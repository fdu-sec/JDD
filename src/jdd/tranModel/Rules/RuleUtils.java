package tranModel.Rules;

import PointToAnalyze.pointer.Pointer;
import config.SootConfig;
import dataflow.DataFlow;
import dataflow.node.SourcesTaintGraph;
import gadgets.collection.markers.DependenceType;
import gadgets.collection.node.CollisionNode;
import gadgets.collection.node.DependenceNode;
import rules.protocol.AbstractProtocolCheckRule;
import tranModel.Taint.Taint;
import tranModel.TransformableNode;
import cfg.Node;
import config.RegularConfig;
import container.BasicDataContainer;
import container.FragmentsContainer;
import container.RulesContainer;
import dataflow.node.MethodDescriptor;
import dataflow.node.SourceNode;
import detetor.SearchGadgetChains;
import gadgets.collection.AnalyzeUtils;
import gadgets.collection.node.ClassNode;
import gadgets.collection.node.GadgetInfoRecord;
import gadgets.unit.Fragment;
import gadgets.unit.InterimFragment;
import util.Pair;
import markers.Stage;
import soot.*;
import soot.jimple.*;
import soot.jimple.internal.JInstanceFieldRef;
import soot.tagkit.Tag;
import structure.taint.TaintSpreadRuleUnit;
import util.ClassRelationshipUtils;
import util.StaticAnalyzeUtils.ClassUtils;
import util.StaticAnalyzeUtils.FieldUtil;
import util.StaticAnalyzeUtils.Parameter;
import util.Utils;

import java.io.IOException;
import java.util.*;

import static container.FragmentsContainer.*;
import static dataflow.DataFlow.findAllUnitAndValueAffected;
import static dataflow.DataFlowAnalysisUtils.recordEqualsFieldInEqualsMtd;
import static dataflow.DataFlowAnalysisUtils.shortPriorityLinkCheck;
import static gadgets.collection.AnalyzeUtils.*;

public class RuleUtils {
    /**
     * 生成并添加污点
     * @param object
     * @param accessPath
     * @param descriptor
     */
    public static void addTaint(Value object, List<SootField> accessPath, MethodDescriptor descriptor){
        if(accessPath.size() > RegularConfig.accessPath_limit) return;
        Taint newTaint = descriptor.getOrCreateTaint(object, new LinkedList<>(accessPath));
        if (BasicDataContainer.openAliasAnalysis)
            addTaintToAllAliases(descriptor, newTaint);
    }

    /**
     * 向descriptor.taints, descriptor.newTaints中添加污点信息, 不进行别名分析
     * 看情况记录fields污点影响关系信息
     * @param descriptor
     * @param taint
     */
    public static void addTaint(MethodDescriptor descriptor, Taint taint){
        Taint.addTaint(taint,descriptor.taints);
        Taint.addTaint(taint, descriptor.newtaints);
//        descriptor.taints.add(taint);
//        descriptor.newtaints.add(taint);
    }

    /**
     * 向descriptor.taints, descriptor.newTaints中添加污点信息, 并进行别名分析
     * 看情况记录fields污点影响关系信息
     * @param descriptor
     * @param taint
     */
    public static void addTaintToAllAliases(MethodDescriptor descriptor, Taint taint){
        if(descriptor.taints.contains(taint)) return;
        Taint.addTaint(taint,descriptor.taints);
        Taint.addTaint(taint, descriptor.newtaints);

        for(Taint tmpTaint : taint.aliases){
            addTaintToAllAliases(descriptor, tmpTaint);
        }
    }



    public static void createAndAddSourceNode(Object source,
                                              Taint taint,
                                              Value taintValue,
                                              MethodDescriptor descriptor){
        HashSet<SourceNode> newSourceNodes;
        if (BasicDataContainer.stage.equals(Stage.IOCD_GENERATING)
                | BasicDataContainer.stage.equals(Stage.IOCD_SUPPLEMENT_INFER))
            newSourceNodes = RuleUtils.createSourceNode(source, taint, taintValue, descriptor);
        else newSourceNodes = createSourceNodeDirectly(source, descriptor);
        for (SourceNode newSourceNode: newSourceNodes) {
            descriptor.sourcesTaintGraph.completeFieldOfParamSourceNde(newSourceNode, taintValue);
            descriptor.sourcesTaintGraph.addTaintedSourceNode(newSourceNode, taint.object);
        }
    }

    public static HashSet<SourceNode> createSourceNode(Object source, Taint taint,
                                              Value taintValue,
                                              MethodDescriptor descriptor){
        HashSet<SourceNode> ret = new HashSet<>();
        if (source instanceof ParameterRef){
            ret.add(new SourceNode(((ParameterRef) source).getIndex(),
                    descriptor.sourcesTaintGraph.entryMethod));
            return ret;
        }
        else if (source instanceof Constant){
            ret.add(new SourceNode((Value) source));
            return ret;
        }

        SootClass fieldOfClass = getClassOfValueByPointer(taintValue, descriptor);

        SootField lastSootField = null, curSootField = null;
        SootClass lastFieldClass = null, curFieldClass = null;

        if (source instanceof SootFieldRef){
            SootFieldRef sootFieldRef = (SootFieldRef) source;
            curSootField = FieldUtil.fromRefToSootField(sootFieldRef);
            curFieldClass = FieldUtil.getSootFieldType(curSootField);
        }
        else if (source instanceof SootField){
            curSootField = ((SootField) source);
            curFieldClass = FieldUtil.getSootFieldType(curSootField);
        }else return ret;

        LinkedList<SootField> newTmpFields = new LinkedList<>(taint.accessPath);
//        sourceNode.field.addAll(taint.accessPath);
        if (!newTmpFields.contains(curSootField))
            newTmpFields.addLast(curSootField);

        SourceNode sourceNode = new SourceNode(newTmpFields, fieldOfClass);
//        descriptor.sourcesTaintGraph.completeFieldOfParamSourceNde(sourceNode, taintValue);
        if (taint.accessPath.isEmpty()) {
            ret.add(sourceNode);
            return ret;
        }

        ret.add(sourceNode);

        if (fieldOfClass != null ){
            boolean refineFlag = false;
            if (FieldUtil.getSootFieldByName(fieldOfClass, sourceNode.field.getLast().getName()) == null)
                refineFlag = true;
            else {
                SootField tmpSootField = FieldUtil.getSootFieldByName(fieldOfClass, sourceNode.field.getFirst().getName());
                if (tmpSootField != null){
                    if (!tmpSootField.equals(sourceNode.field.getFirst()))
                        refineFlag = true;
                }
            }

            if (refineFlag){
                for (SourceNode tmpSourceNode: descriptor.sourcesTaintGraph.matchTaintedSources(taintValue)){
                    if (!tmpSourceNode.isField())
                        continue;
                    if (tmpSourceNode.field.getLast().getType().toString().contains("[]")){
                        SootClass tmpFieldClass = FieldUtil.getSootFieldType(tmpSourceNode.field.getLast());
                        if (tmpFieldClass.equals(sourceNode.classOfField)){
                            LinkedList<SootField> newFieldsPath = new LinkedList<>();
                            newFieldsPath.addAll(tmpSourceNode.field);
                            newFieldsPath.addAll(sourceNode.field);

                            SourceNode newSourceNode = new SourceNode(newFieldsPath, tmpSourceNode.classOfField);
                            newSourceNode.ind = tmpSourceNode.ind;
                            newSourceNode.entryMtd = tmpSourceNode.entryMtd;
                            ret.add(newSourceNode);
                            ret.remove(sourceNode); // TODO: 直接删除
                        }
                    }
                }
            }
        }
        return ret;
    }

    /**
     * 直接创建 SourceNode, 不考虑和已有的 source nodes之间的关联性，也不考虑可能需要的source node修正
     * @param source
     * @param descriptor
     * @return
     */
    public static HashSet<SourceNode> createSourceNodeDirectly(Object source,
                                                               MethodDescriptor descriptor){
        HashSet<SourceNode> ret = new HashSet<>();
        if (source instanceof ParameterRef){
            ret.add(new SourceNode(((ParameterRef) source).getIndex(),
                    descriptor.sourcesTaintGraph.entryMethod));
            return ret;
        }
        else if (source instanceof Constant){
            ret.add(new SourceNode((Value) source));
            return ret;
        }
        SootField curSootField;
        if (source instanceof SootFieldRef){
            SootFieldRef sootFieldRef = (SootFieldRef) source;
            curSootField = FieldUtil.fromRefToSootField(sootFieldRef);
        }
        else if (source instanceof SootField){
            curSootField = ((SootField) source);
        }else return ret;

        SourceNode newSourceNode = SourceNode.createFieldSourceNode(curSootField, null);
        ret.add(newSourceNode);
        return ret;
    }

    /**
     * 1. field a = static method call(..)
     * 2. static method :: new A(field_1, field_2)
     * @param descriptor
     * @param tfNode
     * @return
     */
    public static HashSet<SourceNode> matchSNodeForInvokedAfterAssign(MethodDescriptor descriptor,
                                                                      ValueBox valueBox,
                                                                      TransformableNode tfNode){
        HashMap<Node, ValueBox> sourceMap = new HashMap<>();
        sourceMap.put(tfNode.node, valueBox);
        HashSet<SourceNode> candidates = new HashSet<>();
        // 1. 调用方法构造实例对象并赋值
        for (HashMap.Entry<Node, ValueBox> entryUse: DataFlow.findAllUnitAndValueAffected(sourceMap).entrySet()){
            Node node = entryUse.getKey();
            if (((Stmt) node.unit) instanceof AssignStmt){
                Value left = ((AssignStmt) node.unit).getLeftOp();
                if ( left instanceof JInstanceFieldRef)
                    candidates.addAll(createSourceNodeDirectly(((JInstanceFieldRef)left).getField(), descriptor));
            }
        }

        Type retType = tfNode.getUnitInvokeExpr().getType();
        HashSet<SourceNode> ret = new HashSet<>();
        for (SourceNode sourceNode: candidates){
            if (sourceNode.getType().equals(retType))
                ret.add(sourceNode);
        }

        if (ret.isEmpty()){ // 2. TODO: 初始化实例对象返回

        }
        return ret;
    }
    /**
     * 启发式匹配source node
     * @param descriptor
     * @param valueBox
     * @param tfNode
     * @param callStack
     * @return
     */
    public static HashSet<SourceNode> tryHeuristicSourceMatching(MethodDescriptor descriptor,
                                                                 ValueBox valueBox,
                                                                 TransformableNode tfNode,
                                                                 LinkedList<SootMethod> callStack){
        if (valueBox == null)
            return new HashSet<>();

        SootClass classOfValueType = Utils.toSootClass(valueBox.getValue().getType());
        Pointer pointer = descriptor.pointTable.getPointer(valueBox.getValue());
        SootClass sootClass = descriptor.getCurrentClass();
        if (pointer != null){
            SootClass tmpClassOfType = Utils.toSootClass(pointer.getType());
            if (ClassRelationshipUtils.isSubClassOf(tmpClassOfType, classOfValueType))
                classOfValueType = tmpClassOfType;
        }

        HashSet<SourceNode> candidateRetOfFirstRound = new HashSet<>();
        SootClass clz = getParamSourceNodeClass(descriptor, valueBox.getValue());
        selectSourceNode(clz,sootClass, descriptor, classOfValueType, candidateRetOfFirstRound);

        if (candidateRetOfFirstRound.isEmpty()| candidateRetOfFirstRound.size() == 1)
            return candidateRetOfFirstRound;

        HashSet<SourceNode> candidateRetOfSecondRound = new HashSet<>();
        for (int index = callStack.size()-1; index >= 0; index-- ){
            HashSet<SourceNode> usedFieldSources = getFieldsUsedInMethod(callStack.get(index), true);
            for (SourceNode sourceNode: usedFieldSources){
                if (candidateRetOfFirstRound.contains(sourceNode))
                    candidateRetOfSecondRound.add(sourceNode);
            }
        }

        if (candidateRetOfSecondRound.size() == 1)
            return candidateRetOfSecondRound;
        else if (candidateRetOfSecondRound.isEmpty())
            return candidateRetOfFirstRound;

        HashSet<SourceNode> candidateRetOfThirdRound = new HashSet<>();
        HashMap<Node, ValueBox> mp = new HashMap<>();
        mp.put(tfNode.node, valueBox);
        HashMap<Node, ValueBox> allUnitAndValueAffected = findAllUnitAndValueAffected(mp);
        for (ValueBox affectedValueBox: allUnitAndValueAffected.values()){
            if (affectedValueBox == null)
                continue;
            Value affectedValue = affectedValueBox.getValue();
            if (affectedValue instanceof JInstanceFieldRef){
                SootField tmpSootField = ((JInstanceFieldRef) affectedValue).getField();
                SourceNode tmpSourceNode = SourceNode.createFieldSourceNode(tmpSootField, sootClass);
                if (candidateRetOfFirstRound.contains(tmpSourceNode))
                    candidateRetOfThirdRound.add(tmpSourceNode);
            }
        }

        if (candidateRetOfThirdRound.isEmpty())
            return candidateRetOfSecondRound;

        return candidateRetOfThirdRound;
    }

    public static HashSet<SourceNode> getTaintedFieldSourceNodesWithHeuristic(MethodDescriptor descriptor,
                                                                              ValueBox valueBox,
                                                                              TransformableNode tfNode,
                                                                              LinkedList<SootMethod> callStack){
        HashSet<SourceNode> fieldSourceNodes = descriptor.sourcesTaintGraph.matchTaintedSources(valueBox.getValue());
        if (fieldSourceNodes.isEmpty())
            fieldSourceNodes = tryHeuristicSourceMatching(descriptor, valueBox, tfNode, callStack);
        filterSourcesForHC(fieldSourceNodes, descriptor);
        fieldSourceNodes.removeIf(sn-> !sn.isField());
        return fieldSourceNodes;
    }

    public static void selectSourceNode(SootClass clz, SootClass sootClass,
                                        MethodDescriptor descriptor,
                                        SootClass classOfValueType,
                                        HashSet<SourceNode> candidateRetOfFirstRound) {
        for (SootField sootField: FieldUtil.getAllDeclaredFields(clz != null? clz: descriptor.getCurrentClass())){
            SootClass tmpClassOfFieldType = FieldUtil.getSootFieldType(sootField);
            if (ClassRelationshipUtils.isSubClassOf(classOfValueType, tmpClassOfFieldType)) {
                SourceNode tmpSourceNode = SourceNode.createFieldSourceNode(sootField, sootClass);
                candidateRetOfFirstRound.add(tmpSourceNode);
            }
//            else if (classOfValueType.getName().equals("java.lang.Object")
//                    && sootField.getType().toString().contains("[]")){ // 认为数组中的元素更有可能出现先InputStream中读出, 再存入某个数组类型field中导致一开始难以直接匹配到来源
//                SourceNode tmpSourceNode = SourceNode.createFieldSourceNode(sootField, sootClass);
//                candidateRetOfFirstRound.add(tmpSourceNode);
//            }
            else if (RuleUtils.canContainGenericType(sootField.getType())){
                SourceNode tmpSourceNode = SourceNode.createFieldSourceNode(sootField, sootClass);
                candidateRetOfFirstRound.add(tmpSourceNode);
            }
        }
    }

    public static HashSet<SourceNode> tryHeuristicSourceMatching(Value value, SourceNode sourceNode,
                                                                 MethodDescriptor descriptor,
                                                                 GadgetInfoRecord gadgetInfoRecord){
        HashSet<SourceNode> ret = new HashSet<>();
        SootClass classOfField = sourceNode.classOfField;
        for (SourceNode superSourceNode: descriptor.sourcesTaintGraph.sources2TaintedValues.keySet()){
            if (superSourceNode.getType().toString().contains("[]")
                    & Utils.toSootClass(superSourceNode.getType()).equals(classOfField)){
                LinkedList<SootField> fields = new LinkedList<>(superSourceNode.field);
                fields.addAll(sourceNode.field);
                fields.remove(sourceNode.field.getLast());
                SourceNode newSourceNode = new SourceNode(fields, superSourceNode.classOfField);
                newSourceNode.setClassId(gadgetInfoRecord);
                ret.add(newSourceNode);
            }
        }

        if (ret.isEmpty()
                & classOfField.hasOuterClass()
                & !Utils.endWithNumber(classOfField.getName())){
            if (gadgetInfoRecord.hasClass(classOfField.getOuterClass())) {
                SootClass outerClass = classOfField.getOuterClass();
                for (SootField sootField : outerClass.getFields()) {
                    if (sootField.getType().toString().contains("[]")
                            & Utils.toSootClass(sootField.getType()).equals(classOfField)) {
                        SourceNode superSourceNode = SourceNode.createFieldSourceNode(sootField, outerClass);
                        if (gadgetInfoRecord.fieldsUsedSitesRecords.containsKey(superSourceNode)) {
                            LinkedList<SootField> fields = new LinkedList<>(superSourceNode.field);
                            fields.addAll(sourceNode.field);
                            SourceNode newSourceNode = new SourceNode(fields, superSourceNode.classOfField);
                            newSourceNode.setClassId(gadgetInfoRecord);
                            ret.add(newSourceNode);
                        }
                    }
                }
            }
        }
        return ret;
    }

    public static SootClass getClassOfValueByPointer(Value value, MethodDescriptor descriptor){
        if (value == null)
            return null;
        SootClass sootClass = null;
        Pointer pointer = descriptor.pointTable.getPointer(value);
        if (pointer == null)
            sootClass = Utils.toSootClass(value.getType());
        else sootClass = Utils.toSootClass(pointer.getType());

        return sootClass;
    }


    /**
     * 应用 RulesContainer.ruleDataStructure 中的规则进行污染传播检查
     * @param descriptor
     * @param stmt
     */
    public static void applySpreadRules(MethodDescriptor descriptor, Stmt stmt){
        if (!stmt.containsInvokeExpr()) return;
        InvokeExpr invokeExpr = stmt.getInvokeExpr();
        String methodSig = invokeExpr.getMethod().getSignature();
        for (TaintSpreadRuleUnit taintSpreadRuleUnit : RulesContainer.ruleDataStructure.getTaintSpreadRuleUnits()){
//            if (!taintSpreadRuleUnit.methodSigs.contains(methodSig))
            if (!isMatchedToSpreadRuleUnit(invokeExpr.getMethod(), taintSpreadRuleUnit))
                continue;

            for (Integer hashCode: taintSpreadRuleUnit.taintsConditionRecord.keySet()){
                boolean flag = true;
                for (Integer ind: taintSpreadRuleUnit.taintsConditionRecord.get(hashCode)){
                    Value checkArgValue = getValueByParamIndex(stmt, ind);
                    if (checkArgValue == null){
                        flag = false;
                        break;
                    }
                    if (!Utils.isTainted(checkArgValue, descriptor.taints)){
                        flag = false;
                        break;
                    }
                }
                if (flag){
                    for (Integer ind: taintSpreadRuleUnit.paramsBeTainted.get(hashCode)){
                        Value argValue = getValueByParamIndex(stmt, ind);
                        if (argValue == null)
                            continue;
                        Taint newTaint = descriptor.getOrCreateTaint(argValue, new LinkedList<>());
                        RuleUtils.addTaint(descriptor,newTaint);

                        // 添加污染源
                        if (BasicDataContainer.infosCollect) {
                            boolean hasFieldInfluenceRecord = false;
                            if (taintSpreadRuleUnit.taintInfluenceFieldsRecord != null
                                    && taintSpreadRuleUnit.taintInfluenceFieldsRecord.containsKey(hashCode)
                                    && !taintSpreadRuleUnit.taintInfluenceFieldsRecord.get(hashCode).isEmpty()) {
                                hasFieldInfluenceRecord = true;
                            }

                            HashSet<String> fieldSigs = new HashSet<>();
                            if (hasFieldInfluenceRecord)
                                fieldSigs = taintSpreadRuleUnit.taintInfluenceFieldsRecord.get(hashCode);

                            for (Pair<Integer, Integer> influencePair : taintSpreadRuleUnit.taintInfluenceRecord.get(hashCode)) {
                                Value sourceValue = getValueByParamIndex(stmt, influencePair.getKey());
                                Value taintedValue = getValueByParamIndex(stmt, influencePair.getValue());
                                if (sourceValue == null | taintedValue == null)
                                    continue;

                                if (hasFieldInfluenceRecord) {
                                    for (String fieldSig: fieldSigs) {
                                        if (Scene.v().containsField(fieldSig)) {
                                            SootField sootField = Scene.v().getField(fieldSig);

                                            ValueBox thisValueBox = Parameter.getThisValueBox(stmt);
                                            SootClass sootClass = null;
                                            if (thisValueBox != null) {
                                                Pointer pointer = descriptor.pointTable.getPointer(thisValueBox.getValue());
                                                if (pointer != null)
                                                    sootClass = Utils.toSootClass(pointer.getType());
                                            }
                                            SourceNode sourceNode = SourceNode.createFieldSourceNode(sootField, sootClass);
                                            sourceNode.checkFlag = taintSpreadRuleUnit.serializableCheckFlag;
                                            descriptor.sourcesTaintGraph.addTaintedSourceNode(sourceNode, taintedValue);
                                        }
                                    }
                                }else {
                                    descriptor.sourcesTaintGraph.createAndAddSourceNode(sourceValue, taintedValue,
                                            taintSpreadRuleUnit.needInfluenceCheck, taintSpreadRuleUnit.serializableCheckFlag);
                                }
                            }
                        }
                    }
                }
            }
        }
    }


    public static boolean isMatchedToSpreadRuleUnit(SootMethod sootMethod, TaintSpreadRuleUnit taintSpreadRuleUnit){
        if (taintSpreadRuleUnit.checkLevel == 3)
            return taintSpreadRuleUnit.methodSigs.contains(sootMethod.getSignature());
        if (taintSpreadRuleUnit.checkLevel == 2)
            return taintSpreadRuleUnit.methodSig.equals(sootMethod.getSubSignature());
        if (taintSpreadRuleUnit.checkLevel == 1)
            return taintSpreadRuleUnit.methodSig.equals(sootMethod.getName());
        return false;
    }

    public static SootClass getParamSourceNodeClass(MethodDescriptor descriptor, Value value){
        for (SourceNode sourceNode: descriptor.sourcesTaintGraph.matchTaintedSources(value)){
            if (sourceNode.isParameter() || sourceNode.isFieldOfParameter()) {
                return sourceNode.entryMtd.getDeclaringClass();
            }
        }

        return null;
    }

    /**
     * 根据参数索引返回对应的Value
     * 本项目, -2 -- invokeExpr.getArgCount
     * -1: this
     * -2: return
     * @param stmt
     * @param ind
     * @return
     */
    public static Value getValueByParamIndex(Stmt stmt, Integer ind){
        if (stmt == null | ind == null)
            return null;
        if (!stmt.containsInvokeExpr())
            return null;

        ValueBox thisValueBox = Parameter.getThisValueBox(stmt);
        Value retValue = Parameter.getReturnedValue(stmt);

        InvokeExpr invokeExpr = stmt.getInvokeExpr();

        if (ind == -2 & retValue != null)
            return retValue;
        if (ind == -1 & thisValueBox != null)
            return thisValueBox.getValue();
        if (invokeExpr.getArgCount() > ind & ind >= 0)
            return invokeExpr.getArg(ind);
        return null;
    }

    public static ValueBox getValueBoxByParamIndex(Stmt stmt, Integer ind){
        if (stmt == null | ind == null)
            return null;
        if (!stmt.containsInvokeExpr())
            return null;

        ValueBox thisValueBox = Parameter.getThisValueBox(stmt);
        ValueBox retValueBox = Parameter.getReturnedValueBox(stmt);

        InvokeExpr invokeExpr = stmt.getInvokeExpr();

        if (ind == -2 & retValueBox != null)
            return retValueBox;
        if (ind == -1 & thisValueBox != null)
            return thisValueBox;
        if (invokeExpr.getArgCount() > ind & ind >= 0)
            return invokeExpr.getArgBox(ind);
        return null;
    }

    /**
     * 做一些基本的类型转换, 得到更基础的 local value
     * @param value
     * @return
     */
    public static Value getBaseValue(Value value){
        if (value instanceof ArrayRef)
            value = ((ArrayRef) value).getBase();
        if (value instanceof CastExpr)
            value = ((CastExpr) value).getOp();
        return value;
    }

    /**
     * 根据指令信息提取从InputStream中读出的fields
     * (1) 仅考虑从InputStream中读取的, 直接申明的不考虑
     * @param tfNode
     * @return
     */
    public static Pair<SootFieldRef, Value> getSootFieldRefFromInputStream(MethodDescriptor descriptor, TransformableNode tfNode){
        if (!tfNode.containsInvoke())
            return new Pair<>(null,null);

        SootClass sootClass = null;
        SootFieldRef sootFieldRef = null;
        Value value = null;

        InvokeExpr invokeExpr = tfNode.getUnitInvokeExpr();
        SootMethod invokedMethod = invokeExpr.getMethod();
        String methodSig = invokedMethod.getSignature();


        return new Pair<>(sootFieldRef, value);
    }



    public static HashSet<HashSet<Integer>> linkCheckOfTaints(Fragment preFragment, Fragment sucFragment){
        HashSet<HashSet<Integer>> paramsTaitRequires = new HashSet<>();
        if (sucFragment.connectRequire == null)
            System.out.println("???");
        if (sucFragment.connectRequire.paramsTaitRequire == null)
            System.out.println("???");
        for (HashSet<Integer> condSet: sucFragment.connectRequire.paramsTaitRequire) {
            boolean flag = true;
            for (int paramInd : condSet) {
                if (!preFragment.endToHeadTaints.containsKey(paramInd)) {
                    flag = false;
                    break;
                }
            }
            if (flag) {
                HashSet<Integer> taintReqs = new HashSet<>();
                for (int paramInd: condSet) {
                    taintReqs.addAll(preFragment.endToHeadTaints.get(paramInd).iterator().next());
                }
                paramsTaitRequires.add(taintReqs);
            }
        }

        return paramsTaitRequires;
    }

    public static HashSet<Fragment> deleteHir(HashSet<Fragment> fragments, int threadCount){
        if (fragments.size() < threadCount)
            return new HashSet<>();

        TreeMap<Integer, HashSet<Fragment>> sortedFragmentsMap = sortFragmentsMap(fragments);
        HashSet<Fragment> toSave = new HashSet<>();
        for (Integer priority: sortedFragmentsMap.keySet()){
            if (toSave.size() + sortedFragmentsMap.get(priority).size() >= threadCount)
                break;

            toSave.addAll(sortedFragmentsMap.get(priority));
        }

        HashSet<Fragment> toDelete = new HashSet<>(fragments);
        toDelete.removeAll(toSave);

        return toDelete;
    }

    public static TreeMap<Integer, HashSet<Fragment>> sortFragmentsMap(HashSet<Fragment> fragments){
        TreeMap<Integer, HashSet<Fragment>> sortedFragmentsMap = new TreeMap<>();
        for (Fragment fragment: fragments){
            if (fragment.priority == 1)
                fragment.calPrioritySimply();
            if (!sortedFragmentsMap.containsKey(fragment.priority))
                sortedFragmentsMap.put(fragment.priority,  new HashSet<>());
            sortedFragmentsMap.get(fragment.priority).add(fragment);
        }

        return sortedFragmentsMap;
    }


    public static boolean generateFragmentOrNot(HashSet<SootMethod> sootMethods, String methodSubSig){
        int methodCount = 0;
        for (SootMethod sootMethod: sootMethods){
            if (!sootMethod.getSubSignature().equals(methodSubSig))
                continue;

            methodCount ++;
        }

        return methodCount > BasicDataContainer.methodLimitNum;
    }

    public static boolean isValidEqHCGadgetFragment(Fragment fragment){
        if (fragment.head.getSubSignature().equals(fragment.end.getSubSignature())
                && fragment.head.getSubSignature().equals("boolean equals(java.lang.Object)")){
            if (!FragmentsContainer.isSingleFixedEqualsMethod(fragment.head))
                return false;
        }
        return true;
    }

    public static boolean isEqMethod(SootMethod sootMethod){
        return sootMethod.getSubSignature().equals("boolean equals(java.lang.Object)");
    }

    /**
     * 特定于Gadget chains检测场景的方法调用规则，如果要改成通用检测，请删除
     * @return
     */
    public static boolean invokeContinueCheck(InvokeExpr invokeExpr,
                                      MethodDescriptor descriptor,
                                      Pointer thisPointer){

        if (RuleUtils.isEqMethod(invokeExpr.getMethod())){
            if (!Utils.isTainted(invokeExpr.getArg(0),descriptor.taints))
                return false;
            // 判断调用的类型和入参类型, 需要均为Object类型
            Pointer argPointer = descriptor.pointTable.getPointer(invokeExpr.getArg(0));
            if (thisPointer != null){
                if (!thisPointer.getType().toString().contains("java.lang.Object"))
                    return false;
            }
            if (argPointer != null){
                if (!argPointer.getType().toString().contains("java.lang.Object"))
                    return false;
            }
        }
        return true;
    }

    public static void getTaintedFieldSourcesForHC(GadgetInfoRecord gadgetInfoRecord,
                                                   MethodDescriptor descriptor,
                                                   ClassNode curClassNode, InvokeExpr invokeExpr,
                                                   LinkedList<SootMethod> callStack,
                                                   HashSet<SourceNode> fieldSources){
        if (gadgetInfoRecord.flag || !fieldSources.isEmpty()) return;

        Fragment sucFragment = gadgetInfoRecord.getFragment(callStack);
        if (sucFragment == null || sucFragment.head.equals(gadgetInfoRecord.gadgets.getFirst()))
            return;
        int fragmentIndex = gadgetInfoRecord.fragment.linkedFragments.indexOf(sucFragment.hashCode())-1;
        Fragment curFragment = FragmentsContainer.basicFragmentsMap.get(gadgetInfoRecord.fragment.linkedFragments.get(fragmentIndex));
        if (curFragment == null)
            return;

        if (isEqMethod(curFragment.head)
                && !isEqMethod(sucFragment.head)
                && descriptor.fieldsParamIndexRecord.containsKey(-1)
                && descriptor.fieldsParamIndexRecord.get(-1).size() == 1){
            SourceNode thisSourceNode = descriptor.fieldsParamIndexRecord.get(-1).iterator().next();
            if (thisSourceNode.equals(curClassNode.source)){
                fieldSources.add(curClassNode.source);
            }
        }
        else if (isEqMethod(sucFragment.head)
                && isEqMethod(curFragment.head)){
            fieldSources.add(curClassNode.source);
        } else if (isEqMethod(sucFragment.head)){
            Value argValue = invokeExpr.getArg(0);
            fieldSources.addAll(RuleUtils.getTaintedFieldSourcesViaAF(argValue, gadgetInfoRecord, descriptor));
        }else if (isEqMethod(curFragment.head)
                && !isEqMethod(sucFragment.head)
                && descriptor.fieldsParamIndexRecord.containsKey(0)
                && descriptor.fieldsParamIndexRecord.get(0).size() == 1){
            fieldSources.add(curClassNode.source);
        }
    }

    public static HashSet<SourceNode> getTaintedFieldSources(Value value, MethodDescriptor descriptor){
        HashSet<SourceNode> ret = new HashSet<>();
        if (!Utils.isTainted(value, descriptor.taints))
            return ret;

        for (SourceNode sourceNode: descriptor.sourcesTaintGraph.matchTaintedSources(value)){
            if (sourceNode.isField())
                ret.add(sourceNode);
        }
        return ret;
    }

    /**
     * 在IOCD生成时，对于一些污点传播过于复杂，可能难以准确追踪时，采取的启发式Class-Fields约束推断方法。
     * @param thisValueBox
     * @param invokeExpr
     * @param tfNode
     * @param callStack
     * @param descriptor
     * @param gadgetInfoRecord
     * @return
     */
    public static HashSet<SourceNode> getTaintedFieldSourceNodesViaHeuristic(ValueBox thisValueBox,
                                                                             InvokeExpr invokeExpr,
                                                                             SootClass fieldTypeOfClass,
                                                                             TransformableNode tfNode,
                                                                             LinkedList<SootMethod> callStack,
                                                                             MethodDescriptor descriptor,
                                                                             ClassNode curClassNode,
                                                                             GadgetInfoRecord gadgetInfoRecord){
        HashSet<SourceNode> fieldSources
                = RuleUtils.getTaintedFieldSourcesViaAF(thisValueBox.getValue(), gadgetInfoRecord, descriptor);
        if (fieldSources.isEmpty())
            fieldSources = RuleUtils.tryHeuristicSourceMatching(descriptor, thisValueBox, tfNode, callStack);
        RuleUtils.getTaintedFieldSourcesForHC(gadgetInfoRecord, descriptor, curClassNode, invokeExpr, callStack, fieldSources);
        filterSourceNodes(fieldSources, descriptor, thisValueBox, fieldTypeOfClass);
        if (isEqMethod(descriptor.sootMethod) && isEqMethod(curClassNode.gadgets.getFirst()) && fieldSources.size() == 1){
            SourceNode sourceNode = fieldSources.iterator().next();
            if (!sourceNode.equals(curClassNode.source)
                    && curClassNode.rootClassNode.classId == sourceNode.classId && curClassNode.rootClassNode.source != null
                    && curClassNode.rootClassNode.source.equals(sourceNode, 0)){
                fieldSources.remove(sourceNode);
                fieldSources.add(curClassNode.source);
            }
        }
        return fieldSources;
    }

    public static HashSet<SourceNode> getTaintedFieldSourceNodesViaHeuristic(ValueBox valueBox,
                                                                             TransformableNode tfNode,
                                                                             LinkedList<SootMethod> callStack,
                                                                             MethodDescriptor descriptor,
                                                                             GadgetInfoRecord gadgetInfoRecord){
        if (valueBox == null)   return new HashSet<>();
        Value value = valueBox.getValue();
        HashSet<SourceNode> controllableValues = RuleUtils.getTaintedFieldSources(value, descriptor);
        if (!controllableValues.isEmpty())  return controllableValues;
        controllableValues = RuleUtils.getTaintedFieldSourcesViaAF(value, gadgetInfoRecord, descriptor);
        if (controllableValues.isEmpty()) {
            // 判断选择那个methodDescriptor更为合适
            LinkedHashSet<Node> affectNodes = DataFlow.findAllDefUnitAffectThisValue(tfNode.node, valueBox);
            for (Node node: affectNodes){
                ValueBox thisValueBox = Parameter.getThisValueBox(node);
                if (thisValueBox == null || ((Stmt) node.unit).getInvokeExpr().getArgCount() != 0)   continue;
                HashSet<SourceNode> sourceNodes = descriptor.sourcesTaintGraph.matchTaintedSources(thisValueBox.getValue());
                for (SourceNode sourceNode: sourceNodes){
                    if (!sourceNode.isField()) continue;
                    SootClass clz = sourceNode.classOfField;
                    selectSourceNode(clz, clz, descriptor, Utils.toSootClass(value.getType()), controllableValues);
                }
            }
        }
        return controllableValues;
    }


    public static HashSet<SourceNode> getTaintedFieldSourcesViaAF(Value value,
                                                                  GadgetInfoRecord gadgetInfoRecord,
                                                                  MethodDescriptor descriptor){
        HashSet<SourceNode> ret = new HashSet<>();
        if (!Utils.isTainted(value, descriptor.taints))
            return ret;

        for (SourceNode sourceNode: descriptor.sourcesTaintGraph.matchTaintedSources(value)){
            if (sourceNode.isField())
                ret.add(sourceNode);
        }

        HashSet<SourceNode> toDelete = new HashSet<>();
        HashSet<SourceNode> toAdd = new HashSet<>();
        for (SourceNode sourceNode: ret){
            SootClass classOfSourceNode = sourceNode.classOfField;
            if (!gadgetInfoRecord.hasClass(classOfSourceNode)
                & (ClassRelationshipUtils.isSubClassOf(Utils.toSootClass(sourceNode.getType()), Utils.toSootClass(value.getType()))
                    | sourceNode.getType().toString().equals("java.lang.Object"))){
                toDelete.add(sourceNode);
                toAdd.addAll(tryHeuristicSourceMatching(value,sourceNode, descriptor, gadgetInfoRecord));
            }
        }

        ret.removeAll(toDelete);
        // 顺便删除掉MethodDescriptor中的错误记录
        for (SourceNode sourceNode: toDelete){
            descriptor.sourcesTaintGraph.sources2TaintedValues.get(sourceNode).remove(value);
        }
        for (SourceNode sourceNode: toAdd){
            descriptor.sourcesTaintGraph.addTaintedSourceNode(sourceNode, value);
        }

        ret.addAll(toAdd);
        return ret;
    }

    /**
     * 过滤器: 根据经验总结, 提升静态部分gadget chains检测准确性
     * @param descriptor
     * @param valueBox
     * @return true: 清理
     */
    public static boolean sanitizerArrayElement(MethodDescriptor descriptor, ValueBox valueBox){
        for (SourceNode sourceNode: descriptor.sourcesTaintGraph.matchTaintedSources(valueBox.getValue())){
            if (!sourceNode.isField())
                continue;

            SootField sootField = sourceNode.field.getLast();
            Tag signatureTag = sootField.getTag("SignatureTag");
            if (signatureTag == null)
                continue;

            if (ClassRelationshipUtils.isSubClassOf(
                    sootField.getDeclaringClass(), BasicDataContainer.commonClassMap.get("Map"))) {
                LinkedList<String> extractedTypes = Utils.extractArrayElementType(signatureTag.toString());
                if (extractedTypes.size() >= 2 ) {
                    if (!extractedTypes.getFirst().equals("java/lang/Object") & !extractedTypes.get(1).equals("java/lang/Object"))
                        return true;
                }
            }
        }


        return false;
    }

    public static LinkedList<String> getArrayElementOfSootField(SootField sootField){
        LinkedList<String> extractedTypes = new LinkedList<>();
        Tag signatureTag = sootField.getTag("SignatureTag");
        if (signatureTag == null)
            return extractedTypes;
        extractedTypes = Utils.extractArrayElementType(signatureTag.toString());
        return extractedTypes;
    }


    public static void sanitizerOfConClassNode(ClassNode conClassNode,
                                               TransformableNode tfNode,
                                               MethodDescriptor invokedDescriptor){

        // 1.如果没有被污染, 则删除添加的 ConClassNode
        if (invokedDescriptor.retTainted.isEmpty() & conClassNode != null){
            GadgetInfoRecord gadgetInfoRecord = conClassNode.gadgetInfoRecord;
            ClassNode rootClassNode = conClassNode.rootClassNode;
            rootClassNode.implicitFields.get(conClassNode.source).remove(conClassNode);
            gadgetInfoRecord.implicitClassFieldsGraph.get(conClassNode.sootClass).remove(conClassNode);
        }
    }


    public static HashSet<SourceNode> sanitizerOfTaintAndSource(GadgetInfoRecord gadgetInfoRecord,
                                                                MethodDescriptor descriptor, Taint taint){
        HashSet<SourceNode> ret = new HashSet<>(); // 记录通过检测的 source nodes
        for (SourceNode sourceNode: descriptor.sourcesTaintGraph.matchTaintedSources(taint)){
            if (!sourceNode.isField())
                continue;

            ClassNode tmpClassNode = gadgetInfoRecord.getClassNode(sourceNode.classOfField);
            if (tmpClassNode != null)
                ret.add(sourceNode);
        }

        return ret;
    }



    public static boolean validControllableCollisionType(SourceNode sourceNode, MethodDescriptor descriptor){
        if (!sourceNode.isField())
            return false;

        if (FieldUtil.isTransientType(sourceNode.field.getLast())){
            if (!checkTransientControllableSimply(null, sourceNode.field.getLast(), descriptor))
                return false;
        }

        if (Utils.isBasicType(sourceNode.getType()))
            return true;

        if ( (sourceNode.getType().toString().contains("Entry") | sourceNode.getType().toString().contains("Node"))
                & sourceNode.getType().toString().contains("[]")){
            return true;
        }

        return false;
    }

    /**
     * 检查在 sootClass 中 transient 类型的 field 是否在反序列化的过程中能被攻击者控制
     * (1) 检查 readObject 等方法
     * (2) 此处做简单处理, 仅分析在方法中是否用到该 sootFields? (或者直接把来源在此处就分析出来呢)
     * @param sootClass
     * @param sootField
     * @return
     */
    public static boolean checkTransientControllable(SootClass sootClass, SootField sootField){
        if (FragmentsContainer.protocolCheckRule.entryMethods.isEmpty())
            return false;
        if (sootClass == null)
            sootClass = sootField.getDeclaringClass();

        HashSet<SootMethod> readObjMethods = ClassRelationshipUtils.getMethodsOfClass(sootClass, FragmentsContainer.protocolCheckRule.entryMethods);
        if (readObjMethods.isEmpty())
            return false;

        for (SootMethod sootMethod: readObjMethods){
            HashSet<SourceNode> usedFields = new HashSet<>();
            boolean flag = false; // 记录是否因为调用方法数量超过控制导致检测出的fields数量为0
            SearchGadgetChains.collectFields(sootMethod, usedFields);
            for (SourceNode sourceNode: usedFields){
                if (!sourceNode.isField())
                    continue;
                if (sourceNode.field.getLast().equals(sootField))
                    return true;
            }
        }
        return false;
    }


    public static boolean checkTransientControllableSimply(SootClass sootClass, SootField sootField, MethodDescriptor descriptor){
        if (sootField == null)
            return false; // 如果找不到对应的field, 则认定为错误的
        if (FragmentsContainer.protocolCheckRule.entryMethods.isEmpty())
            return false;
        if (sootClass == null)
            sootClass = sootField.getDeclaringClass();
        if (descriptor != null){
            SootClass curClass = descriptor.getCurrentClass();
            if (ClassRelationshipUtils.isSubClassOf(curClass, sootClass))
                sootClass = curClass;
        }

        HashSet<SootMethod> readObjMethods = new HashSet<>();
        for (SootClass clz: ClassUtils.getAllSupers(sootClass)){
            readObjMethods.addAll(ClassRelationshipUtils.getMethodsOfClass(clz, FragmentsContainer.protocolCheckRule.entryMethods));
        }
        if (readObjMethods.isEmpty())
            return false;
        // 加入一层readObj中的被调函数
        LinkedList<SootMethod> checkMtds = new LinkedList<>(readObjMethods);
        int initMethodCount = readObjMethods.size();
        int count = 0;
        while (!checkMtds.isEmpty()){
            count ++;
            SootMethod sootMethod = checkMtds.pop();
            if (!sootMethod.hasActiveBody())
                continue;

            SootField tmpSootField = null;
            for (Unit unit: sootMethod.retrieveActiveBody().getUnits()){
                Stmt stmt = (Stmt) unit;
                if (stmt instanceof AssignStmt){
                    Value left = ((AssignStmt) stmt).getLeftOp();
                    Value right = ((AssignStmt) stmt).getRightOp();

                    if (left instanceof JInstanceFieldRef) {
                        tmpSootField = ((JInstanceFieldRef) left).getField();
                    }
                    else if (right instanceof JInstanceFieldRef) {
                        tmpSootField = ((JInstanceFieldRef) right).getField();
                    }

                    if (tmpSootField != null){
                        if (tmpSootField.equals(sootField))
                            return true;
                    }
                }
                if (stmt.containsInvokeExpr() && count <= initMethodCount){
                    if (transientCheckForResolve(sootMethod, stmt.getInvokeExpr().getMethod(), sootField)){
                        return true;
                    }
                    checkMtds.add(stmt.getInvokeExpr().getMethod());
                }
            }
        }

        for (SootMethod sootMethod: readObjMethods){
            if (!sootMethod.hasActiveBody())
                continue;

            SootField tmpSootField = null;
            for (Unit unit: sootMethod.retrieveActiveBody().getUnits()){
                Stmt stmt = (Stmt) unit;
                if (stmt instanceof AssignStmt){
                    Value left = ((AssignStmt) stmt).getLeftOp();
                    Value right = ((AssignStmt) stmt).getRightOp();

                    if (left instanceof JInstanceFieldRef) {
                        tmpSootField = ((JInstanceFieldRef) left).getField();
                    }
                    else if (right instanceof JInstanceFieldRef) {
                        tmpSootField = ((JInstanceFieldRef) right).getField();
                    }

                    if (tmpSootField != null){
                        if (tmpSootField.equals(sootField))
                            return true;
                    }
                }
            }
        }
        return false;
    }

    public static boolean needSlzCheck(MethodDescriptor descriptor,
                                       ValueBox valueBox){
        if (valueBox == null)
            return true;

        HashSet<SourceNode> sourceNodes = descriptor.sourcesTaintGraph.matchTaintedSources(valueBox.getValue());
        if (sourceNodes.size() == 1){
            SourceNode sourceNode = sourceNodes.iterator().next();
            if (!sourceNode.checkFlag)
                return false;
        }
        return true;
    }

    // resolve在反序列化实例的时候默认执行(E.g. JDK), 但其是用反射方法返回一个对象, 直接的数据流很难准确推断其赋值对象
    // 因此暂时采用启发式推断的方式
    public static boolean transientCheckForResolve(SootMethod topMtd, SootMethod sootMethod, SootField sootField){
        if (!topMtd.getSubSignature().equals("java.lang.Object readResolve()")
                || sootMethod.getParameterCount() != 2)
            return false;

        Type toTestFieldType = sootField.getType();
        Type v1Type = sootMethod.getParameterType(0);
        Type v2Type = sootMethod.getParameterType(1);

        int typeCode = turnTypeToInt(toTestFieldType) ^ turnTypeToInt(v1Type) ^ turnTypeToInt(v2Type);
        if (typeCode==7 || typeCode == 14)
            return true;

        return false;
    }

    public static int turnTypeToInt(Type type){
        String typeStr = type.toString();
        if (typeStr.equals("java.lang.Object"))
            return 1;
        if (typeStr.equals("java.lang.String"))
            return 2;
        if (typeStr.equals("java.lang.reflect.Method"))
            return 4;
        if (typeStr.equals("java.lang.Class"))
            return 8;
        return -1;
    }

    /**
     * 获取 sootMethod 中使用了的所有fields
     * @param sootMethod
     * @param flag 是否考虑 方法签名中已经记录的源追踪情况
     * @return
     */
    public static HashSet<SourceNode> getFieldsUsedInMethod(SootMethod sootMethod, boolean flag){
        HashSet<SourceNode> ret = new HashSet<>();
        MethodDescriptor descriptor = BasicDataContainer.getOrCreateDescriptor(sootMethod);
        SootClass sootClass = descriptor.getCurrentClass();
        if (flag) {
            for (Value argValue: descriptor.paramIdMapLocalValue.values()){
                for (SourceNode argSourceNode: descriptor.sourcesTaintGraph.matchTaintedSources(argValue)){
                    if (argSourceNode.isField()){
                        ret.add(argSourceNode);
                    }
                }
            }
        }

        SootField tmpSootField = null;
        if (!sootMethod.hasActiveBody())    return ret;
        for (Unit unit: sootMethod.retrieveActiveBody().getUnits()){
            Stmt stmt = (Stmt) unit;
            if (stmt instanceof AssignStmt){
                Value left = ((AssignStmt) stmt).getLeftOp();
                Value right = ((AssignStmt) stmt).getRightOp();

                if (left instanceof JInstanceFieldRef) {
                    tmpSootField = ((JInstanceFieldRef) left).getField();
                    SourceNode tmpSourceNode = SourceNode.createFieldSourceNode(tmpSootField, sootClass);
                    ret.add(tmpSourceNode);
                }
                else if (right instanceof JInstanceFieldRef) {
                    tmpSootField = ((JInstanceFieldRef) right).getField();
                    SourceNode tmpSourceNode = SourceNode.createFieldSourceNode(tmpSootField, sootClass);
                    ret.add(tmpSourceNode);
                }
            }
        }
        return ret;
    }


    public static LinkedList<SootField> getAccessPath(Value baseObj, SootField sootField,
                                                      MethodDescriptor descriptor) {
        LinkedList<SootField> accessField = new LinkedList<>();
        if (descriptor.paramIdMapLocalValue.containsKey(-1)){
            if (descriptor.paramIdMapLocalValue.get(-1).equals(baseObj))
                return accessField;
        }

        SootClass classOfBaseObj = Utils.toSootClass(baseObj.getType());
        for (SourceNode sourceNode: descriptor.sourcesTaintGraph.matchTaintedSources(baseObj)){
            if (!sourceNode.isField())
                continue;
            SootClass classOfFieldType = Utils.toSootClass(sourceNode.getType());
            if (!classOfFieldType.equals(classOfBaseObj))
                continue;

            LinkedList<SootField> tmpFieldAccessPath = new LinkedList<>(sourceNode.field);
            tmpFieldAccessPath.add(sootField);
            return tmpFieldAccessPath;
        }

        return accessField;
    }

    public static HashSet<InterimFragment> markConClassNodesBasedOnInterimFragments(GadgetInfoRecord gadgetInfoRecord,
                                                                    SootMethod invokedMethod,
                                                                    TransformableNode tfNode,
                                                                    MethodDescriptor descriptor){
        HashSet<InterimFragment> ret = new HashSet<>();
        ValueBox thisValueBox = Parameter.getThisValueBox(tfNode.node);
        if (!(tfNode.node.unit instanceof AssignStmt) | thisValueBox == null)
            return ret;

        AssignStmt assignStmt = (AssignStmt) tfNode.node.unit;
        Value retValue = ((AssignStmt) assignStmt).getLeftOp();
        SootClass nextClass = invokedMethod.getDeclaringClass();
        Pair<SourceNode, HashSet<SourceNode>> SourcePair = AnalyzeUtils.matchFieldSourceNode(thisValueBox, descriptor, nextClass);
        SourceNode fieldSourceNode = SourcePair.getKey();
        if (fieldSourceNode == null)
            return ret;

        HashSet<InterimFragment> interimFragments =  FragmentsContainer.getInterimFragment(invokedMethod);
        if (interimFragments.isEmpty()) return ret;
        if (interimFragments.size() > BasicDataContainer.methodLimitNum) {
            ret = (HashSet<InterimFragment>) Utils.getRandomElements(interimFragments, BasicDataContainer.methodLimitNum);
        }

        HashMap<Integer, Pair<InterimFragment, HashSet<SourceNode>>> candidateInterimFragmentsMap = new HashMap<>();
        for (InterimFragment interimFragment: interimFragments){
            if (gadgetInfoRecord.gadgets.contains(interimFragment.head))
                continue;

            if (interimFragment.head.hasActiveBody()){
                if (interimFragment.head.retrieveActiveBody().getUnits().size() > 10)
                    continue;
            }

            if (!interimFragment.taintSourceActions.containsKey(-1))
                continue;
            if (interimFragment.taintSourceActions.get(-1).isEmpty())
                continue;

            HashSet<SourceNode> tmpSourceNodes = new HashSet<>();
            for (SourceNode sourceNode: interimFragment.taintSourceActions.get(-1)){
                if (sourceNode.isConstant())
                    continue;

                if (sourceNode.isParameter()){
                    Value argValue = getValueByParamIndex((Stmt) tfNode.node.unit, sourceNode.ind);
                    if (!Utils.isTainted(argValue, descriptor.taints))
                        continue;

                    for (SourceNode tmpSourceNode: descriptor.sourcesTaintGraph.matchTaintedSources(argValue)){
                        if (!tmpSourceNode.isField())
                            continue;
                        tmpSourceNodes.add(tmpSourceNode);
                    }
                }
                if (sourceNode.isField()){
                    tmpSourceNodes.add(sourceNode);
                }
            }

            if (tmpSourceNodes.isEmpty())
                continue;

            candidateInterimFragmentsMap.put(interimFragment.head.retrieveActiveBody().getUnits().size(),
                    new Pair<>(interimFragment, new HashSet<>(tmpSourceNodes)));
        }

        // 开始创建
        for (Object value: Utils.getSortedElement(candidateInterimFragmentsMap, BasicDataContainer.interimFragmentToConClassLimit)){
            Pair<InterimFragment, HashSet<SourceNode>> pair = (Pair<InterimFragment, HashSet<SourceNode>>) value;
            InterimFragment interimFragment = pair.getKey();
            HashSet<SourceNode> sourceNodes = pair.getValue();

            ret.add(interimFragment);

            for (SourceNode retSourceNode: sourceNodes){
                descriptor.sourcesTaintGraph.addTaintedSourceNode(retSourceNode, retValue);
            }
            gadgetInfoRecord.inImplicitClassFlag = true;
        }

        return ret;
    }

    public static boolean isValidEqualsConnect(Fragment preFragment, Fragment sucFragment){
//        if (!FragmentsContainer.isFixedEqualsMethod(preFragment.head) | needEncapsulateEqualsMethod(preFragment.head))
        if (getMtdNum(sucFragment.gadgets, "boolean equals(java.lang.Object)") >= 2)
            return false;
        if (!RuleUtils.isValidDoubleSingleFixedEqs(preFragment, sucFragment))
            return false;
        // TODO: 1. first.equals -> second.equals -> nextFragment.head;
        // TODO: 2. nextFragment.class -> fixed & <-> second.class
        if (!shortPriorityLinkCheck(preFragment, sucFragment))
            return false;

        return true;
    }

    public static boolean isGeneticType(Type type){
        if (canContainGenericType(type) || isSingleGenericType(type))
            return true;

        return false;
    }
    public static boolean couldSetGenericTypeObj(Type type){
        SootClass typeOfClass = Utils.toSootClass(type);
        if (isGeneticType(type)
                || ClassRelationshipUtils.isSubClassOf(
                typeOfClass, BasicDataContainer.commonClassMap.get("Map"))
                || ClassRelationshipUtils.isSubClassOf(
                typeOfClass, BasicDataContainer.commonClassMap.get("List"))
                || ClassRelationshipUtils.isSubClassOf(typeOfClass, BasicDataContainer.commonClassMap.get("Entry")))
                return true;
        return false;
    }

    public static boolean isInterfaceGenericType(Type type){
        if (!isGeneticType(type))
            return false;
        String typeStr = type.toString();
        if (typeStr.contains("java.lang.Object")
                || typeStr.contains("java.util.Map$Entry"))
            return true;
        return false;
    }

    public static boolean isSingleGenericType(Type type){
        String typeStr = type.toString();
        if ( typeStr.endsWith("$Entry")
                || typeStr.endsWith("$Node")
                || typeStr.equals("java.lang.Object")) {
            return true;
        }

        return false;
    }

    public static boolean canContainGenericType(Type type){
        String typeStr = type.toString();
        if ( typeStr.endsWith("$Entry[]")
                || typeStr.endsWith("$Node[]")
                || typeStr.equals("java.lang.Object[]")) {
            return true;
        }

        return false;
    }

    /**
     * 检查是否存在 hash 碰撞方法, 如果存在则进行连接
     * @param gadgetInfoRecord
     * @return true:
     */
    public static boolean detectAndRecordHashCollision(GadgetInfoRecord gadgetInfoRecord, Fragment fragment){
        if (!fragment.head.getSubSignature().equals("boolean equals(java.lang.Object)"))
            return true;
        if (!FragmentsContainer.isFixedEqualsMethod(fragment.head))
            return true;

        if (gadgetInfoRecord.collisionNode == null){
            gadgetInfoRecord.collisionNode =  new CollisionNode();
        }

        // 记录碰撞的方法
        gadgetInfoRecord.collisionNode.collisionMethod = fragment.head;

        SootMethod hashCodeMtd = getHashCodeMtd(fragment.head.getDeclaringClass());
        // 暂时好像没有不是同一个对象/包装碰撞的, 先如此简单处理
        gadgetInfoRecord.collisionNode.firstHashCodeMtd = hashCodeMtd;
        gadgetInfoRecord.collisionNode.secondHashCodeMtd = hashCodeMtd;

        // 记录相关的fields
        boolean addGadgetFlag = false;
        for (SourceNode sourceNode: FragmentsContainer.fixedHashClass.get(fragment.head.getDeclaringClass())){
            gadgetInfoRecord.collisionNode.first.add(sourceNode);
            gadgetInfoRecord.collisionNode.second.add(sourceNode);
            if (sourceNode.getType().toString().contains("[]"))
                addGadgetFlag = true;
        }

        if (addGadgetFlag){
            int thisEqualMtdIndex = gadgetInfoRecord.gadgets.indexOf(fragment.head);
            SootMethod preMtd = gadgetInfoRecord.gadgets.get(thisEqualMtdIndex-1);
            if (!preMtd.getSubSignature().equals("boolean equals(java.lang.Object)")){
                SootMethod toAddMtd = getEqualsMtd(fragment.head.getDeclaringClass());
                if (!FragmentsContainer.fixedHashClass.containsKey(toAddMtd.getDeclaringClass()))
                    return false;
                if (AnalyzeUtils.getMtdNum(gadgetInfoRecord.gadgets, "boolean equals(java.lang.Object)") > 1)
                    return false;

                gadgetInfoRecord.gadgets.add(thisEqualMtdIndex, toAddMtd);
            }
        }

        return true;
    }

    public static Fragment getEqFragmentByIndex(LinkedList<Fragment> linkedFragments, int index){
        if (index <=0 )
            return null;
        int equalsCount = 0;
        for (Fragment fragment: linkedFragments){
            if (RuleUtils.isEqMethod(fragment.head))
                equalsCount ++;
            if (equalsCount == index)
                return fragment;
        }
        return null;
    }

    /**
     * @param gadgetInfoRecord
     * @param linkedFragments 从source fragment 到最后 sink Fragment 的有序 fragment 拼接序列
     * @return
     */
    public static boolean detectAndRecordHashCollision(GadgetInfoRecord gadgetInfoRecord,
                                                       LinkedList<Fragment> linkedFragments) throws IOException {
        Fragment firstEqualsFragment = null;
                Fragment secondEqualsFragment = null;
        int equalsMtdCount = 0;
        for (Fragment tmpFragment: linkedFragments){
            if (RuleUtils.isEqMethod(tmpFragment.head)){
                if (equalsMtdCount == 0)
                    firstEqualsFragment = tmpFragment;
                if (equalsMtdCount == 1)
                    secondEqualsFragment = tmpFragment;
                equalsMtdCount++;
            }
        }

        // 标记需要哈希碰撞
        if (equalsMtdCount > 0)
            gadgetInfoRecord.hashCollisionFlag = true;

        // 不允许超过2个equals方法的连接 (冗余), 如果第一个不是直接固定的话;
        if (equalsMtdCount >= 2) {
            if (equalsMtdCount == 2
                    && FragmentsContainer.isSingleFixedEqualsMethod(firstEqualsFragment.head)
                    && FragmentsContainer.isFixedEqualsMethod(secondEqualsFragment.head)
                    /*&& RuleUtils.recordCollisionForSingle(linkedFragments, firstEqualsFragment, gadgetInfoRecord)*/){
                recordCollisionForSameMtd(firstEqualsFragment.head, gadgetInfoRecord);
                // 记录单个碰撞的情况
                return true;
            }
            else
                return false;
        }

        // 没有 equals 方法连接的则直接返回
        if (firstEqualsFragment == null)
            return true;
        if (!FragmentsContainer.isFixedEqualsMethod(firstEqualsFragment.head))
            return false;

        // 为第一个 equals 方法生成碰撞信息
        if (FragmentsContainer.isSingleFixedEqualsMethod(firstEqualsFragment.head)
                /*&& !needEncapsulateEqualsMethod(firstEqualsFragment.head)*/) {
            // TODO: 在一些情况下, 可以直接将与该hashCode方法求解相关的fields设置为同一个对象, 从而产生hash碰撞; 在此补充对该种情况的处理
//            if (couldCollisionForSingleEquals(gadgetInfoRecord, linkedFragments, firstEqualsFragment))
//                return true;
//            return RuleUtils.recordCollisionForSingle(linkedFragments, firstEqualsFragment, gadgetInfoRecord);
            if (secondEqualsFragment == null) gadgetInfoRecord.hashCollisionReview = 1;
            return true;
        }

        return false;
    }

    public static void recordCollisionForSameMtd(SootMethod firstEqMtd, GadgetInfoRecord gadgetInfoRecord){
        if (gadgetInfoRecord.collisionNode == null){
            gadgetInfoRecord.collisionNode =  new CollisionNode();
        }
        // 记录碰撞的方法
        gadgetInfoRecord.collisionNode.collisionMethod = firstEqMtd;

        SootMethod hashCodeMtd = getHashCodeMtd(firstEqMtd.getDeclaringClass());
        // 暂时好像没有不是同一个对象/包装碰撞的, 先如此简单处理
        gadgetInfoRecord.collisionNode.firstHashCodeMtd = hashCodeMtd;
        gadgetInfoRecord.collisionNode.secondHashCodeMtd = hashCodeMtd;
        gadgetInfoRecord.collisionNode.first.clear();
        gadgetInfoRecord.collisionNode.second.clear();

        for (SourceNode sourceNode: FragmentsContainer.fixedHashClass.get(firstEqMtd.getDeclaringClass())){
            gadgetInfoRecord.collisionNode.first.add(sourceNode);
            gadgetInfoRecord.collisionNode.second.add(sourceNode);
        }
    }

    public static boolean recordCollisionForSingle(LinkedList<Fragment> linkedFragments,
                                                   Fragment firstEqualsFragment,
                                                   GadgetInfoRecord gadgetInfoRecord) throws IOException {
        if (gadgetInfoRecord.collisionNode == null){
            gadgetInfoRecord.collisionNode =  new CollisionNode();
        }

        gadgetInfoRecord.collisionNode.collisionMethod = firstEqualsFragment.head;
        Fragment nextFragment = RuleUtils.getHashCollisionMethods(linkedFragments, firstEqualsFragment, gadgetInfoRecord);
        // 1. 如果有nextFragment, 即后续的classNode和firstEqMethod对应的类的来源相同，这两个方法对应的classNode碰撞
        // 2. 如果没有, 则两个firstEqMethod对应的类碰撞
        SootMethod hashCodeMtd1 = getHashCodeMtd(firstEqualsFragment.head.getDeclaringClass());
        SootMethod hashCodeMtd2 = nextFragment == null? hashCodeMtd1: getHashCodeMtd(nextFragment.head.getDeclaringClass());
        if (hashCodeMtd2 == null || !AbstractProtocolCheckRule.isSingleHashControllable(hashCodeMtd2))
            return false;
        gadgetInfoRecord.collisionNode.firstHashCodeMtd = hashCodeMtd1;
        gadgetInfoRecord.collisionNode.secondHashCodeMtd = hashCodeMtd2;

        gadgetInfoRecord.collisionNode.flag = true;
        if (!FragmentsContainer.isSingleFixedEqualsMethod(firstEqualsFragment.head))
            gadgetInfoRecord.hashCollisionReview = 0;

        gadgetInfoRecord.collisionNode.first
                = new LinkedList<>(FragmentsContainer.fixedHashClass.get(firstEqualsFragment.head.getDeclaringClass()));
        gadgetInfoRecord.collisionNode.second = gadgetInfoRecord.collisionNode.first;
        return true;
    }


    public static boolean recordCollisionForSingleHC(LinkedList<Fragment> linkedFragments,
                                                   Fragment firstEqualsFragment,
                                                   GadgetInfoRecord gadgetInfoRecord) throws IOException {
        if (getMtdNum(gadgetInfoRecord.gadgets, "boolean equals(java.lang.Object)") == 2) {
            recordCollisionForSameMtd(firstEqualsFragment.head, gadgetInfoRecord); return true;
        }
        if (getMtdNum(gadgetInfoRecord.gadgets, "boolean equals(java.lang.Object)") == 1){
            SootMethod firstMtd = Utils.getMethod(gadgetInfoRecord.gadgets, "boolean equals(java.lang.Object)", 1);
            if (FragmentsContainer.isSingleFixedEqualsMethod(firstMtd) && fixedHashClass.get(firstMtd.getDeclaringClass()).isEmpty()){
                gadgetInfoRecord.collisionNode = new CollisionNode();
                gadgetInfoRecord.collisionNode.type = 1;
                recordCollisionForSameMtd(firstEqualsFragment.head, gadgetInfoRecord); return true;
            }
        }
        if (gadgetInfoRecord.collisionNode == null) gadgetInfoRecord.collisionNode =  new CollisionNode();
        ClassNode firstCNode = gadgetInfoRecord.getClassNode(BasicDataContainer.getOrCreateDescriptor(firstEqualsFragment.head).getCurrentClass());
        if (firstCNode == null) return false;

        Fragment nextFragment = RuleUtils.getHashCollisionMethods(linkedFragments, firstEqualsFragment, gadgetInfoRecord);
        if (nextFragment == null) return recordCaseC(gadgetInfoRecord, firstEqualsFragment);

        // 1. 如果有nextFragment, 即后续的classNode和firstEqMethod对应的类的来源相同，这两个方法对应的classNode碰撞
        // 2. 如果没有, 则两个firstEqMethod对应的类碰撞
        ClassNode secondCNode = gadgetInfoRecord.getClassNode(BasicDataContainer.getOrCreateDescriptor(nextFragment.head).getCurrentClass());
        if (secondCNode == null)    return false;
        // 不同实例的来源一直，则属于Case A
        if (firstCNode.source != null && secondCNode.source != null
                && (firstCNode.source.classOfField.equals(secondCNode.source.classOfField)
                    && firstCNode.source.field.getFirst().equals(secondCNode.source.field.getFirst()))){
            gadgetInfoRecord.collisionNode.type = 1;
            // 记录两个不同实例存放的上层实例对象的hash method
            gadgetInfoRecord.collisionNode.firstHashCodeMtd
                    = gadgetInfoRecord.collisionNode.secondHashCodeMtd
                    = getHashCodeMtd(firstCNode.source.classOfField);

            SootMethod topEqMtd = AnalyzeUtils.getEqualsMtd(firstCNode.source.classOfField);
            gadgetInfoRecord.collisionNode.collisionMethod = topEqMtd;
            if (!FragmentsContainer.isSingleFixedEqualsMethod(topEqMtd))
                return false;
            gadgetInfoRecord.collisionNode.flag = true;
            gadgetInfoRecord.collisionNode.top = new LinkedList<>(FragmentsContainer.fixedHashClass.get(firstCNode.source.classOfField));
        }else { // 否则属于 Case C
            recordCaseC(gadgetInfoRecord, firstEqualsFragment);
        }

        return true;
    }

    public static boolean recordCaseC(GadgetInfoRecord gadgetInfoRecord, Fragment firstEqualsFragment){
        gadgetInfoRecord.collisionNode.collisionMethod = firstEqualsFragment.head;
        gadgetInfoRecord.collisionNode.firstHashCodeMtd
                = gadgetInfoRecord.collisionNode.secondHashCodeMtd
                = getHashCodeMtd(firstEqualsFragment.head.getDeclaringClass());

        gadgetInfoRecord.collisionNode.type = 3;
        if (!FragmentsContainer.isSingleFixedEqualsMethod(firstEqualsFragment.head))
            gadgetInfoRecord.hashCollisionReview = 0;
        gadgetInfoRecord.collisionNode.first
                = new LinkedList<>(FragmentsContainer.fixedHashClass.get(firstEqualsFragment.head.getDeclaringClass()));
        gadgetInfoRecord.collisionNode.second = gadgetInfoRecord.collisionNode.first;

        return true;
    }


    /**
     * 将某个对象的hashCode相关的fields直接设置为相同来完成hash 碰撞
     * 要求后续的类层次结构关系中, 不存在两个不同类实例对象是同一个类实例对象的相同的fields [添加标识, 在后续进行复查]
     * @param gadgetInfoRecord
     * @param linkedFragments
     * @param firstEqualsFragment
     * @return
     */
    public static boolean couldCollisionForSingleEquals(GadgetInfoRecord gadgetInfoRecord,
                                                        LinkedList<Fragment> linkedFragments,
                                                        Fragment firstEqualsFragment){
        if (!FragmentsContainer.classHashCodeFieldsMap.containsKey(firstEqualsFragment.head.getDeclaringClass()))
            return false;

        HashSet<SourceNode> hashCodeSources = FragmentsContainer.classHashCodeFieldsMap.get(firstEqualsFragment.head.getDeclaringClass());
        if (hashCodeSources.size() > 2) // 启发式, 剪枝
            return false;

        int fragmentIndex = linkedFragments.indexOf(firstEqualsFragment);
        Fragment nextFragment = null;
        if (fragmentIndex+1 >= linkedFragments.size()) {
            if (firstEqualsFragment.gadgets.size() == 1)
                return false;
            if (getHashCodeMtd(firstEqualsFragment.gadgets.get(1).getDeclaringClass()) == null)
                return false;
        }
        else {
            nextFragment = linkedFragments.get(fragmentIndex + 1);
            if (getHashCodeMtd(nextFragment.head.getDeclaringClass()) == null)
                return false;
        }

        if (gadgetInfoRecord.collisionNode == null){
            gadgetInfoRecord.collisionNode =  new CollisionNode();
        }

        // 记录碰撞的方法
        gadgetInfoRecord.collisionNode.collisionMethod = firstEqualsFragment.head;

        SootMethod hashCodeMtd = getHashCodeMtd(firstEqualsFragment.head.getDeclaringClass());
        // 暂时好像没有不是同一个对象/包装碰撞的, 先如此简单处理
        gadgetInfoRecord.collisionNode.firstHashCodeMtd = hashCodeMtd;
        gadgetInfoRecord.collisionNode.secondHashCodeMtd = hashCodeMtd;
        gadgetInfoRecord.collisionNode.flag = true;
        gadgetInfoRecord.hashCollisionReview = 0;

        return true;
    }

    /**
     * 属于启发式规则中的一条, 可以去掉;
     * 用于避免出现一些 exploitable 但是没有太大意义的gadget chains
     * @param head
     * @param end
     * @return
     * end.getSubSignature().equals(" boolean equals ( java.lang.Object)")
     *                     & !end.getSubSignature().equals("java.lang.String toString()")
     *                     & !end.getSubSignature().equals("<java.util.Map: boolean containsValue(java.lang.Object)>")
     *                     & !isSinkFlag
     */
    public static boolean isValidEqualsMethod(SootMethod head, SootMethod end, Fragment.FRAGMENT_STATE state){
        if (head.getSubSignature().equals("boolean equals(java.lang.Object)")) {
            if (end.getSubSignature().equals("int hashCode()"))
                return false;
        }else if (end.getSubSignature().equals("boolean equals(java.lang.Object)") & !Fragment.FRAGMENT_STATE.SOURCE.equals(state)){
            if (!head.getSubSignature().equals("boolean equals(java.lang.Object)"))
                return false;
            if (!FragmentsContainer.isFixedEqualsMethod(head))
                return false;
        }

        return true;
    }


    public static boolean isGenericType(MethodDescriptor descriptor, Value value){
        if (!value.getType().toString().contains("[]"))
            return false;
        HashSet<SourceNode> sourceNodes = descriptor.sourcesTaintGraph.matchTaintedSources(value);
        for (SourceNode sourceNode: sourceNodes){
            if (!sourceNode.getType().equals(value.getType()) | !sourceNode.isField())
                continue;
            SootField sootField = sourceNode.field.getLast();
            Tag signatureTag = sootField.getTag("SignatureTag");
            if (signatureTag != null){
                if (signatureTag.toString().contains("[TK;")
                        |signatureTag.toString().contains("[TV;"))
                    return true;
            }
        }
        return false;
    }

    public static boolean heuristicFilterGF(Fragment fragment, int count){
        if (fragment.gadgets.size() > BasicDataContainer.chainLimit
                || count >= RegularConfig.prioritizedGadgetChainLimit)
            return false;

        return true;
    }

    /**
     * 根据经验模型记录一些无效的end方法
     * @param sootMethod
     * @return
     */
    public static boolean isInvalidFragmentEnd(SootMethod sootMethod, boolean isSinkFlag){
        if (isSinkFlag) return false;
        if (SootConfig.ignoreInfo.contains(sootMethod.getSubSignature())
                || SootConfig.ignoreInfo.contains(sootMethod.getSignature())
                || SootConfig.ignoreInfo.contains(sootMethod.getDeclaringClass().getName())
                || hcFilter(sootMethod))
            return true;

        return false;
    }

    public static boolean hcFilter(SootMethod end){
        if ((end.getSubSignature().equals("java.lang.Object getValue()")
                || end.getSubSignature().equals("java.lang.Object getKey()"))
                && ClassRelationshipUtils.isSubClassOf(
                        end.getDeclaringClass(), BasicDataContainer.commonClassMap.get("Entry")))
            return true;
        return false;
    }

    /**
     * 取出 firstEqFragment 之后，即hash碰撞之后调用的方法配对
     * @param linkedFragments
     * @param firsrEqFragment
     * @param gadgetInfoRecord
     * @return
     */
    public static Fragment getHashCollisionMethods(LinkedList<Fragment> linkedFragments,
                                            Fragment firsrEqFragment,
                                            GadgetInfoRecord gadgetInfoRecord){
        SootMethod firstEqMtd = firsrEqFragment.head;
        ClassNode firstEqCNode = gadgetInfoRecord.getClassNode(firstEqMtd.getDeclaringClass());
        if (firstEqCNode == null || linkedFragments.getLast().equals(firsrEqFragment))
            return null;
        SourceNode firstSourceNode = firstEqCNode.source;

        for (Fragment tmpFragment: linkedFragments.subList(linkedFragments.indexOf(firsrEqFragment)+1, linkedFragments.size())){
            ClassNode tmpCNode = gadgetInfoRecord.getClassNode(tmpFragment.getClassForHead());
            if (tmpCNode == null || tmpCNode.source == null)   return null;
            if (tmpCNode.source.equals(firstSourceNode,0)){
                return tmpFragment;
            }
        }
        return null;
    }

    public static boolean satisfyTaintCheck(ValueBox thisValueBox,
                                            MethodDescriptor descriptor,
                                            TransformableNode tfNode,
                                            InvokeExpr invokeExpr){
        if (thisValueBox == null)
            return false;

        if (Utils.isTaintedOrGen(descriptor, thisValueBox.getValue()))
            return true;
        Value thisValue = descriptor.paramIdMapLocalValue.get(-1);
        if (thisValue != null && invokeExpr.getArgs().contains(thisValue))
            return true;

        if (RegularConfig.taintRuleMode.equals("loose")) {
            InvokeExpr invokedExpr = tfNode.getUnitInvokeExpr();
            if (invokedExpr.getMethod().getName().equals("<init>")) {
                for (Value argValue : invokedExpr.getArgs()) {
                    if (Utils.isTainted(argValue, descriptor.taints))
                        return true;
                }
            }
        }
        return false;
    }

    /**
     * 过滤掉冗余的调用方法
     * E.g. 同时存在 a.method, a_superClass.method: 删除掉a_superClass.method
     * 但考虑精细检查所消耗的时候可能比检查更高(因为符合这类情况的可能不是很多）
     * 因此此处暂时仅过滤简单常见的情况
     * @param invokedMethods
     */
    public static void filterInvokedMethods(HashSet<SootMethod> invokedMethods, SootMethod invokedMethod){
        if (invokedMethods.size() <=1
                || invokedMethod.getDeclaringClass().getName().equals("java.lang.Object")
                || invokedMethod.getDeclaringClass().getName().equals("java.lang.Class")) return;
        HashSet<SootMethod> toDelete = new HashSet<>();

        for (SootMethod tmpMtd: invokedMethods){
            if (tmpMtd.getDeclaringClass().getName().equals("java.lang.Object"))
                toDelete.add(tmpMtd);
            else if (tmpMtd.getDeclaringClass().getName().equals("java.lang.Class")
                    && isInitializationMethods(tmpMtd))
                toDelete.add(tmpMtd);
        }
        invokedMethods.removeAll(toDelete);
    }

    public static boolean isInitializationMethods(SootMethod sootMethod){
        return sootMethod.getName().equals("<clinit>")
                || sootMethod.getName().equals("<init>");
    }

    public static boolean isInitMtdTaintSourceRecord(Object affected, Value affect,
                                                     MethodDescriptor descriptor){
        if (!descriptor.sootMethod.getName().equals("<init>"))
            return false;
        HashSet<SourceNode> affectSourceNodes = descriptor.sourcesTaintGraph.matchTaintedSources(affect);
        if (affectSourceNodes.size() != 1 || !isInputStreamSourceNode(affectSourceNodes.iterator().next()))
            return false;
        HashSet<SourceNode> sourceNodes = createSourceNodeDirectly(affected, descriptor);
        for (SourceNode sourceNode: sourceNodes){
            descriptor.sourcesTaintGraph.addTaintedSourceNode(sourceNode, affect);
        }
        return true;
    }

    public static boolean isInputStreamSourceNode(SourceNode sourceNode){
        if ((sourceNode.isParameter() || sourceNode.isFieldOfParameter())
                && sourceNode.getType().toString().contains("InputStream"))
            return true;
        return false;
    }

    public static void supplementDependenceHC(GadgetInfoRecord gadgetInfoRecord){
        HashMap<SootClass, DependenceNode> depRecords = new HashMap<>();
        for (DependenceNode dependenceNode: gadgetInfoRecord.dependenceNodes){
            if (dependenceNode.left.classOfField != null
                    && dependenceNode.right.classOfField != null
                    && dependenceNode.left.classOfField.equals(dependenceNode.right.classOfField)) {
                if (depRecords.containsKey(dependenceNode.left.classOfField))
                    depRecords.replace(dependenceNode.left.classOfField,null);
                else depRecords.put(dependenceNode.left.classOfField, dependenceNode);
            }
        }
        for (SootClass sootClass: depRecords.keySet()) {
            DependenceNode dependenceNode = depRecords.get(sootClass);
            if (dependenceNode == null) continue;
            if (!dependenceNode.type.toString().contains("CLASS")) {
                HashSet<SootField> sootFields = FieldUtil.findFieldsByType(sootClass, "java.lang.Class");
                for (SootField sootField: sootFields){
                    createAndAddDpNode(sootField, true, sootClass, dependenceNode.left, DependenceType.CLASS_METHOD, gadgetInfoRecord,false);
                    createAndAddDpNode(sootField,true, sootClass, dependenceNode.right, DependenceType.CLASS_NAME, gadgetInfoRecord,false);
                }
            } else if (!dependenceNode.type.toString().contains("NAME")) {
                HashSet<SootField> sootFields = FieldUtil.findFieldsByType(sootClass, "java.lang.String");
                for (SootField sootField: sootFields){
                    createAndAddDpNode(sootField, false, sootClass, dependenceNode.left, DependenceType.CLASS_NAME, gadgetInfoRecord,false);
                    createAndAddDpNode(sootField, false, sootClass, dependenceNode.right, DependenceType.METHOD_NAME, gadgetInfoRecord,false);
                }
            } else if (!dependenceNode.type.toString().contains("METHOD")) {
                HashSet<SootField> sootFields = FieldUtil.findFieldsByType(sootClass, "java.lang.reflect.Method");
                for (SootField sootField: sootFields){
                    createAndAddDpNode(sootField, false, sootClass, dependenceNode.left, DependenceType.CLASS_METHOD, gadgetInfoRecord,false);
                    createAndAddDpNode(sootField, true, sootClass, dependenceNode.right, DependenceType.METHOD_NAME, gadgetInfoRecord,false);
                }
            }
        }
    }

    public static void createAndAddDpNode(SootField newField, boolean flag,
                                          SootClass sootClass,
                                          SourceNode sourceNode,
                                          DependenceType dependenceType,
                                          GadgetInfoRecord gadgetInfoRecord,
                                          boolean checkFlag){
        SourceNode newSourceNode = SourceNode.createFieldSourceNode(newField, sootClass);
        DependenceNode dependenceNode = null;
        if (flag)
            dependenceNode = new DependenceNode(newSourceNode, sourceNode, dependenceType);
        else dependenceNode = new DependenceNode(sourceNode, newSourceNode, dependenceType);
        gadgetInfoRecord.addDependenceNode(dependenceNode,checkFlag);
    }

    public static void filterSourceNodes(HashSet<SourceNode> fieldSources,
                                         MethodDescriptor descriptor,
                                         ValueBox thisValueBox,
                                         SootClass fieldTypeOfClass){
        if (thisValueBox == null)   return;
        fieldSources.removeIf(fsn -> !fsn.isField()
/*                || (isGeneticType(fsn.getType()) && !isInterfaceGenericType(fsn.getType()))*/
                || (!couldSetGenericTypeObj(fsn.getType())
                        && !ClassRelationshipUtils.isSubClassOf(fieldTypeOfClass, Utils.toSootClass(fsn.getType()))));
    }
    /**
     * 利用启发式规则取出的sources可能
     */
    public static void filterSourcesForHC(HashSet<SourceNode> fieldSources,
                                          MethodDescriptor descriptor) {
        HashSet<SourceNode> toDelete = new HashSet<>();
        for (SourceNode sourceNode: fieldSources){
            if (sourceNode.isField()
                    && !checkTransientControllableSimply(sourceNode.classOfField, sourceNode.field.getFirst(), descriptor))
                toDelete.add(sourceNode);
        }
        fieldSources.removeAll(toDelete);
    }

    /**
     * 判断某个变量能否被攻击者控制
     * (1) 是否被污染
     * (2) 查找污染源能否可控
     *      (a) fields以外的类型暂时不做细粒度检查
     *      (b) field: 检查是否在序列化和反序列化过程中攻击者可控. E.g. Transient fields
     * @param descriptor
     * @param valueBox
     * @param tfNode
     * @return
     */



    /**
     * 检查要生成的Fragment的end是否能被攻击者控制; (也可以加在 continueCheck 方法里面)
     * @return true: 攻击者可以控制end / 是static method (sinks)
     *         flase: 攻击者无法控制
     */
    public static boolean isEndMtdControllableHC(MethodDescriptor descriptor,
                                               TransformableNode tfNode,
                                               LinkedList<SootMethod> callStack) {
        ValueBox thisValueBox = Parameter.getThisValueBox(tfNode.node);
        if (thisValueBox == null)   return true;
        HashSet<SourceNode> fieldSources
                = RuleUtils.getTaintedFieldSourceNodesWithHeuristic(descriptor, thisValueBox, tfNode, callStack);

        if (fieldSources.size() == 1){
            SourceNode sourceNode = fieldSources.iterator().next();
            SootField sootField =sourceNode.field.getFirst();
            if (FieldUtil.isTransientType(sootField)
                    && !checkTransientControllableSimply(sourceNode.classOfField, sootField, descriptor))
                return false;
//            if (isGeneticType(sourceNode.getType())
//                    && !isInterfaceGenericType(sourceNode.getType()))
//                return false;
        }
        return true;
    }

    public static HashSet<String> basicLinkClz = new HashSet<>(Arrays.asList(
            "java.util.concurrent.ConcurrentHashMap",
            "java.util.HashMap", "java.util.Hashtable"
    ));
    /*
    启发式筛选，基于一些人工经验设定 (如果不需要可以移除该方法，但会多输出一些作用不是那么大的衍生链，建议添加)
     */
    public static boolean heuristicGadgetChainLink(Fragment fragment, Fragment sucFragment){
        if ( Fragment.FRAGMENT_STATE.SOURCE.equals(fragment.state)
                &&(isEqMethod(fragment.end)
                || fragment.end.getSubSignature().equals("java.lang.Object put(java.lang.Object,java.lang.Object)")
                || fragment.end.getSubSignature().equals("java.lang.Object get(java.lang.Object)"))){
            if (fragment.gadgets.size() > 2
                    || !basicLinkClz.contains(fragment.head.getDeclaringClass().getName()))
                return false;
        }else if (fragment.end.getSubSignature().equals("int hashCode()")
                && (!Fragment.FRAGMENT_STATE.SOURCE.equals(fragment.state)
                || !basicLinkClz.contains(fragment.head.getDeclaringClass().getName())))
            return false;
        return true;
    }

    /**
     * 启发式算法筛掉一些意义不大的替换链
     * @param preFragment
     * @param linkableSinkFragments
     * @return
     */
    public static HashSet<Fragment> heuristicEqChainLink(Fragment preFragment, HashSet<Fragment> linkableSinkFragments){
        HashSet<Fragment> ret = new HashSet<>();
        if (isEqMethod(preFragment.end) && BasicDataContainer.hashCollisionModeSelect){
            // 1. 检查sucFragment中有几个equals，如果仅有一个，则必定为case 1/3
            String subEqMethodSig = "boolean equals(java.lang.Object)";
            HashSet<Fragment> tmpLinkableSinkFragments = new HashSet<>(linkableSinkFragments);
            SootMethod eqForHeadClz = getEqualsMtd(preFragment.head.getDeclaringClass());
            boolean isSingleFixedEq = FragmentsContainer.isSingleFixedEqualsMethod(eqForHeadClz);
            while (!tmpLinkableSinkFragments.isEmpty()){
                Fragment sucFragment = tmpLinkableSinkFragments.iterator().next();
                tmpLinkableSinkFragments.remove(sucFragment);
                int eqMtdNum = getMtdNum(sucFragment.gadgets, subEqMethodSig);
                if (eqMtdNum < 2){
                    if (!isSingleFixedEq)   continue;
                    if (!AbstractProtocolCheckRule.isSingleEvenCollisionHc(sucFragment.head)){
                        if (!preFragment.head.getDeclaringClass().equals(sucFragment.head.getDeclaringClass()))
                            continue;
                    }
                    LinkedList<SootMethod> newGadgets = new LinkedList<>(sucFragment.gadgets);
                    newGadgets.addFirst(eqForHeadClz);
                    boolean flag = true;
                    for (Fragment tmpFragment: linkableSinkFragments)
                        if (Utils.listEqual(tmpFragment.gadgets, newGadgets))   {flag = false; break;}
                    if (flag){
                        sucFragment.gadgets = newGadgets;
                        ret.add(sucFragment);
                    }
                }else if (eqMtdNum == 2){
                    SootMethod firstEq = sucFragment.head;
                    SootMethod secondEq = Utils.getMethod(sucFragment.gadgets, subEqMethodSig, 2);
                    if (!AbstractProtocolCheckRule.isSingleEvenCollisionHc(firstEq)){
                        if (!firstEq.getDeclaringClass().equals(secondEq.getDeclaringClass())
                                || !firstEq.getDeclaringClass().equals(preFragment.head.getDeclaringClass()))
                            continue;
                    }
                    ret.add(sucFragment);
                }
            }
        }else ret = linkableSinkFragments;
        return ret;
    }

    public static boolean isValidDoubleSingleFixedEqs(Fragment preFragment, Fragment sucFragment){
        if (!isSingleFixedEqualsMethod(preFragment.head))
            return false;
        if (Fragment.FRAGMENT_STATE.SOURCE.equals(preFragment.state)
                && !basicLinkClz.contains(sucFragment.head.getDeclaringClass().getName()))
            return false;
/*        if (isSingleFixedEqualsMethod(sucFragment.head)){
            for (SourceNode sourceNode: FragmentsContainer.fixedHashClass.get(sucFragment.head.getDeclaringClass())){
                if (canContainGenericType(sourceNode.getType()))
                    return false;
            }
        }else */if (!isFixedEqualsMethod(sucFragment.head))
            return false;
        return true;
    }

    public static void filterOuterSource(HashSet<SourceNode> usedFields, SootClass sootClass) {
        HashSet<SootClass> superClzs = ClassUtils.getAllSupers(sootClass);
        usedFields.removeIf(sn-> sn.classOfField == null || !superClzs.contains(sn.classOfField));
    }

    /**
     * 检查fields的类型是否与要添加的dependence node含义相匹配 (粗粒度筛选)
     * @param dependenceNode
     * @return
     */
    public static boolean isValidFieldsTypeForDpNode(DependenceNode dependenceNode) {
        Type leftType = dependenceNode.left.getType();
        Type rightType = dependenceNode.right.getType();

        if (dependenceNode.type.equals(DependenceType.ARRAY_SIZE)
                || dependenceNode.type.equals(DependenceType.ARRAY_ELEMENT)){
            if (!Utils.isBasicType(leftType))
                return false;
        }
        if (dependenceNode.type.equals(DependenceType.CLASS_NAME)){
            if ((!leftType.toString().contains("java.lang.Class")
                    && !couldSetGenericTypeObj(leftType))
                 || (couldSetGenericTypeObj(rightType)
                    && !rightType.toString().contains("String")
                    && !rightType.toString().contains("string")))
                return false;
        }
        if (dependenceNode.type.equals(DependenceType.METHOD_NAME)){
            if ((!rightType.toString().contains("String")
                    && !rightType.toString().contains("string")
                    && !couldSetGenericTypeObj(rightType))
                    || (!couldSetGenericTypeObj(leftType)
                            && !leftType.toString().contains("java.lang.reflect.Method")))
                return false;
        }
        if (dependenceNode.type.equals(DependenceType.CLASS_METHOD)){
            if ((!leftType.toString().contains("java.lang.Class")
                    && !couldSetGenericTypeObj(leftType))
                  || (!couldSetGenericTypeObj(rightType))
                    && !rightType.toString().contains("java.lang.reflect.Method")){
                return false;
            }
        }
        return true;
    }
}
