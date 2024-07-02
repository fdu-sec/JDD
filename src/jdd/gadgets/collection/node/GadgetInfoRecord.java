package gadgets.collection.node;

import container.FragmentsContainer;
import gadgets.collection.iocd.unit.ConstantRecord;
import gadgets.collection.iocd.unit.MethodRecord;
import gadgets.unit.Fragment;
import gadgets.unit.RecordUtils;
import rules.protocol.AbstractProtocolCheckRule;
import soot.jimple.InvokeExpr;
import tranModel.Rule;
import tranModel.Rules.RuleUtils;
import tranModel.TransformableNode;
import container.BasicDataContainer;
import dataflow.node.MethodDescriptor;
import dataflow.node.SourceNode;
import gadgets.collection.AnalyzeUtils;
import util.Pair;
import markers.SinkType;
import soot.*;
import soot.jimple.IfStmt;
import util.ClassRelationshipUtils;
import util.StaticAnalyzeUtils.ClassUtils;
import util.StaticAnalyzeUtils.FieldUtil;
import util.StaticAnalyzeUtils.Parameter;
import util.Utils;

import java.io.IOException;
import java.util.HashMap;
import java.util.HashSet;
import java.util.LinkedHashMap;
import java.util.LinkedList;

import static dataflow.DataFlowAnalysisUtils.extractUsedFields;
import static gadgets.collection.AnalyzeUtils.getHashCodeMtd;

public class GadgetInfoRecord {
    public final Fragment fragment;
    public boolean flag = false;
    public boolean hashCollisionFlag = false;
    public SootClass rootClass = null; //记录顶级 SootClass
    public ClassNode rootClassNode = null;
    public SootClass curClass = null;
    public SinkType sinkType;
    public LinkedList<SootMethod> gadgets = new LinkedList<>();
    public LinkedList<Fragment> linkedFragments = new LinkedList<>();
    public LinkedHashMap<SootClass, ClassNode> classFieldsGraph = new LinkedHashMap<>();
    public LinkedHashMap<SootMethod, GadgetNode> gadgetNodesMap = new LinkedHashMap<>(); // 方便在输出数据时, 按顺序取出
    public LinkedHashMap<SootClass, HashSet<ClassNode>> implicitClassFieldsGraph = new LinkedHashMap<>();
    public LinkedHashMap<SootClass, LinkedHashMap<SootMethod, GadgetNode>> implicitGadgetNodesMap = new LinkedHashMap<>();
    public HashSet<SinkNode> sinkNodes = new HashSet<>();
    public HashMap<SourceNode, HashSet<Pair<String, Integer>>> fieldsUsedSitesRecords = new HashMap<>();
    public HashMap<SootClass, ConstantRecord> constantRecordHashMap = new HashMap<>();
    public HashSet<DependenceNode> dependenceNodes = new HashSet<>();

    // TODO: 用来记录 动态代理方法跳转 [触发动态代理 Invocation Handler 的方法, 动态代理的 Invocation Handler 方法]
    public LinkedHashMap<SootMethod, SootMethod> dynamicProxyInvokeRecord = new LinkedHashMap<>();

    public CollisionNode collisionNode = null;

    public boolean inImplicitClassFlag = false;
    public int hashCollisionReview = -1; // -1, 0, 1

    public GadgetInfoRecord(Fragment sinkFragment, SinkType sinkType) {
        this.fragment = sinkFragment;
        this.gadgets = sinkFragment.gadgets;
        this.sinkType = sinkType;

        rootClass = gadgets.get(0).getDeclaringClass();
        if (rootClass.hasOuterClass() & Utils.endWithNumber(rootClass.getName()))
            rootClass = rootClass.getOuterClass();
        curClass = rootClass;
    }

    /**
     * 判断是否具有该class对应的Class Node
     * @return
     */
    public boolean hasClass(SootClass sootClass){
        if (classFieldsGraph.containsKey(sootClass))
            return true;
        return implicitClassFieldsGraph.containsKey(sootClass);
    }

    /**
     * 根据当前的 class 取出sootMethod对应的 Gadget Node
     * (1) supplement阶段则从implicitGadgetNodesMap中取
     * (2) 否则, 直接从 classFieldsGraph 中取
     *
     * @param sootMethod
     * @return
     */
    public GadgetNode getGadgetNode(SootMethod sootMethod) {
//        if (classFieldsGraph.get(curClass) == null)
//            System.out.println("???");
        if (classFieldsGraph.containsKey(curClass)) {
            if (classFieldsGraph.get(curClass).gadgetNodes.containsKey(sootMethod))
                return classFieldsGraph.get(curClass).gadgetNodes.get(sootMethod);
            else if (classFieldsGraph.get(curClass).rootClassNode != null){
                if (classFieldsGraph.get(curClass).rootClassNode.sootClass.equals(curClass))
                    return classFieldsGraph.get(curClass).rootClassNode.gadgetNodes.get(sootMethod);
            }
        }

        if (implicitGadgetNodesMap.containsKey(curClass)){
            return implicitGadgetNodesMap.get(curClass).get(sootMethod);
        }
        return null;
    }

    public void updateCurrentClass(MethodDescriptor descriptor,
                                   LinkedList<SootMethod> callStack,
                                   boolean inImplicitClassFlag) {
        SootMethod sootMethod = descriptor.sootMethod;
        // 静态方法不更新
        if (sootMethod.isStatic() | descriptor.tempGeneratedObjs.contains(descriptor.paramIdMapLocalValue.get(-1)))
            return;

        if (Utils.isSubList(callStack, gadgets)) {
            updateCurrentClass(Utils.getRealClass(sootMethod));
            return;
        }

        if (inImplicitClassFlag) {
            updateCurrentClass(Utils.getRealClass(sootMethod));
        }
    }

    public boolean inImplicitClass(LinkedList<SootMethod> callStack, SootMethod sootMethod) {
        ClassNode lastClassNode = getLastClassNode(callStack);
        if (lastClassNode == null)
            return false;
        boolean inImplicitClassFlag = lastClassNode.gadgets.contains(sootMethod) & !sootMethod.isStatic() & !flag;
        return inImplicitClassFlag;
    }

    public void updateCurrentClass(SootClass sootClass) {
        if (sootClass == null)
            return;

        if (sootClass.hasOuterClass() & Utils.endWithNumber(sootClass.getName()))
            sootClass = sootClass.getOuterClass();

        if (!curClass.equals(sootClass))
            curClass = sootClass;
    }

    public ClassNode getClassNode(SootClass sootClass) {
        if (classFieldsGraph.containsKey(sootClass))
            return classFieldsGraph.get(sootClass);

        for (ClassNode classNode : classFieldsGraph.values()) {
            for (SourceNode sourceNode : classNode.implicitFields.keySet()) {
                for (ClassNode implicitClassNode : classNode.implicitFields.get(sourceNode)) {
                    if (implicitClassNode.sootClass.equals(sootClass))
                        return implicitClassNode;
                }
            }
        }
        return null;
    }

    public ClassNode getLastClassNode(LinkedList<SootMethod> callStack) {
        SootClass lastClass = Utils.getRealClass(callStack.getFirst());
        ClassNode lastClassNode = getClassNode((ClassNode) null, lastClass);
        if (lastClassNode == null)
            return null;

        SootClass tmpClass = null;
        ClassNode tmpCFNode = lastClassNode;

        for (int index = 1; index < callStack.size() & tmpCFNode != null; index++) {
            tmpClass = Utils.getRealClass(callStack.get(index));
            if (tmpClass == null) continue;

            if (!tmpClass.equals(lastClass)) {
                tmpCFNode = getClassNode(tmpCFNode, tmpClass);
                if (tmpCFNode != null) {
                    lastClass = tmpClass;
                }
            }
        }
        return tmpCFNode;
    }

    public ClassNode getClassNode(ClassNode rootClassNode, SootClass curClass) {
        if (curClass == null) return null;

        curClass = ClassRelationshipUtils.getOuterClass(curClass);
        if (classFieldsGraph.containsKey(curClass) | rootClassNode == null)
            return classFieldsGraph.get(curClass);

        if (!implicitClassFieldsGraph.containsKey(curClass))
            return null;
        for (ClassNode classNode : implicitClassFieldsGraph.get(curClass)) {
            if (isRootCFNode(classNode, rootClassNode))
                return classNode;

        }
        return null;
    }

    public ClassNode getClassNode(SootClass rootClass, SootClass curClass){
        if (classFieldsGraph.containsKey(curClass) | rootClass == null)
            return classFieldsGraph.get(curClass);
        if (!implicitClassFieldsGraph.containsKey(curClass))
            return null;
        for (ClassNode classNode: implicitClassFieldsGraph.get(curClass)){
            if (classNode.sootClass.equals(rootClass))
                return classNode;
        }
        return null;
    }

    public static boolean isRootCFNode(ClassNode curClassNode, ClassNode rootCFNode) {
        ClassNode tmpRootClassNode = curClassNode.rootClassNode;
        while (tmpRootClassNode.rootClassNode != null) {
            if (tmpRootClassNode.rootClassNode.equals(rootCFNode))
                return true;
            tmpRootClassNode = tmpRootClassNode.rootClassNode;
        }

        return false;
    }


    public void putConditionNode(ConditionNode conditionNode,
                                 GadgetNode gadgetNode,
                                 IfStmt ifStmt) {
        HashMap<IfStmt, GadgetNode> toChange = new HashMap<>();
        boolean toAdd = true;

        HashSet<ClassNode> allClassNodes = new HashSet<>(classFieldsGraph.values());
        allClassNodes.addAll(getAllImplicitClassNodes());

        for (ClassNode classNode : allClassNodes) {
            HashSet<GadgetNode> allGadgetNodes = new HashSet<>(classNode.gadgetNodes.values());
            allGadgetNodes.addAll(classNode.implicitGadgetNodes.values());

            for (GadgetNode recordedGadgetNode : allGadgetNodes) {
                HashSet<IfStmt> allIfStmts = new HashSet<>(recordedGadgetNode.dominatorConditions.keySet());
                allIfStmts.addAll(recordedGadgetNode.implicitConditions.keySet());
                for (IfStmt recordedIfStmt : allIfStmts) {
                    ConditionNode recordedConditionNode = recordedGadgetNode.getConditionNodeByIfStmt(recordedIfStmt);
                    if (recordedConditionNode.controllableValues.size() != conditionNode.controllableValues.size()
                            | recordedConditionNode.conditionValues.size() != conditionNode.conditionValues.size())
                        continue;

                    if (!recordedConditionNode.controllableValues.containsAll(conditionNode.controllableValues)
                            | !recordedConditionNode.conditionValues.containsAll(conditionNode.conditionValues))
                        continue;

                    if (recordedConditionNode.isDominator) {
                        if (!recordedConditionNode.isNotContradictory(conditionNode.comparison))
                            toChange.put(recordedIfStmt, recordedGadgetNode);
                    }
                    toAdd = false;
                }
            }
        }

        if (toAdd) {
            if (conditionNode.isDominator) {
                gadgetNode.dominatorConditions.put(ifStmt, conditionNode);
            } else gadgetNode.implicitConditions.put(ifStmt, conditionNode);
            gadgetNode.allConditions.put(ifStmt, conditionNode); // 同步记录到 allConditions中
        }

        for (IfStmt toChangeIfStmt : toChange.keySet()) {
            GadgetNode toChangeGadgetNode = toChange.get(toChangeIfStmt);
            ConditionNode toChangeConditionNode = toChangeGadgetNode.dominatorConditions.get(toChangeIfStmt);
            toChangeGadgetNode.dominatorConditions.remove(toChangeIfStmt, toChangeConditionNode);
            toChangeConditionNode.isDominator = false;
            toChangeGadgetNode.implicitConditions.put(toChangeIfStmt, toChangeConditionNode);
        }
    }

    public HashSet<ClassNode> getAllImplicitClassNodes() {
        HashSet<ClassNode> allImplicitClassNodes = new HashSet<>();
        for (SootClass sootClass : implicitClassFieldsGraph.keySet())
            allImplicitClassNodes.addAll(implicitClassFieldsGraph.get(sootClass));

        return allImplicitClassNodes;
    }

    public HashSet<GadgetNode> getAllGadgetNodes() {
        HashSet<GadgetNode> ret = new HashSet<>();
        for (ClassNode classNode: classFieldsGraph.values()){
            ret.addAll(classNode.gadgetNodes.values());
            ret.addAll(classNode.implicitGadgetNodes.values());
        }
        for (ClassNode classNode: getAllImplicitClassNodes()){
            ret.addAll(classNode.implicitGadgetNodes.values());
        }
        return ret;
    }

    public void addDependenceNode(DependenceNode dependenceNode, boolean flag) {
        if (!RuleUtils.isValidFieldsTypeForDpNode(dependenceNode))
            return;
        // if flag == false, 则意味着不确定是否需要添加；此时如果已有fields相同但是dependence type 不同的节点，则不添加
        for (DependenceNode recordedDPNode : this.dependenceNodes) {
            if (recordedDPNode.equals(dependenceNode))
                return;
            if (!flag && recordedDPNode.left.equals(dependenceNode.left)
                    && recordedDPNode.right.equals(dependenceNode.right))
                return;
        }

        dependenceNodes.add(dependenceNode);
    }



    public void addSinkNode(SinkNode sinkNode) {
        for (SinkNode tmpSinkNode : sinkNodes) {
            if (tmpSinkNode.equals(sinkNode))
                return;
        }

        sinkNodes.add(sinkNode);
    }

    public void recordUsedFields(TransformableNode tfNode, MethodDescriptor descriptor) {
        HashMap<SourceNode, HashSet<Pair<String, Integer>>> ret = extractUsedFields(tfNode, descriptor);
        for (SourceNode sourceNode : ret.keySet()) {
            if (!fieldsUsedSitesRecords.containsKey(sourceNode))
                fieldsUsedSitesRecords.put(sourceNode, new HashSet<>());

            fieldsUsedSitesRecords.get(sourceNode).addAll(ret.get(sourceNode));
        }
    }

    public void recordConstantsInMethod(){

    }

    public void recordConstantsOfFields(){

    }

    public void recordForward(TransformableNode tfNode, MethodDescriptor descriptor){
        // 记录fields的使用信息
        recordUsedFields(tfNode, descriptor);
        // 记录方法/class中出现过的常量信息

    }

    /**
     * 创建新的 ClassNode, 并建立和已有 ClassNode 之间的关系
     *
     * @param tfNode
     * @param invokedDescriptor
     * @param descriptor
     */
    public ClassNode createNewClassNode(TransformableNode tfNode,
                                        MethodDescriptor invokedDescriptor,
                                        MethodDescriptor descriptor,
                                        LinkedList<SootMethod> callStack) {
        if (!tfNode.containsInvoke()) return null;

        HashSet<SourceNode> fieldSources = new HashSet<>();
        ValueBox thisValueBox = Parameter.getThisValueBox(tfNode.node);
        if (thisValueBox == null) {
            // 如果是调用静态方法返回给某个field，则需要另外处理
            fieldSources = RuleUtils.matchSNodeForInvokedAfterAssign(
                    descriptor, Parameter.getReturnedValueBox(tfNode.node), tfNode);
            if (fieldSources.isEmpty()) return null;
        }
        if (thisValueBox != null && !Utils.isCompleteTainted(thisValueBox.getValue(), descriptor.taints))   return null;

        ClassNode curClassNode = getClassNode(curClass);
        if (curClassNode == null)
            return null;

        SootClass tmpFieldTypeOfClass = AnalyzeUtils.getActualFieldClassFollowsCallStack(descriptor.sootMethod, gadgets);
        SootClass fieldTypeOfClass = tmpFieldTypeOfClass == null ?
                invokedDescriptor.sootMethod.getDeclaringClass() : tmpFieldTypeOfClass;

        SootClass actualClass = null;
        SourceNode fieldSourceNode = null;
        InvokeExpr invokeExpr = tfNode.getUnitInvokeExpr();
        boolean flag = false;
        HashSet<SourceNode> valuesOfObjectType = new HashSet<>();

        if (fieldSources.isEmpty()) fieldSources = RuleUtils.getTaintedFieldSourceNodesViaHeuristic(
                    thisValueBox, invokeExpr, fieldTypeOfClass, tfNode, callStack, descriptor, curClassNode,this
            );
        for (SourceNode tmpFieldSourceNode : fieldSources) {
            SootClass tmpSourceFieldTypeOfClass = Utils.toSootClass(tmpFieldSourceNode.getType());
            if (tmpSourceFieldTypeOfClass == null)
                continue;

            if (tmpSourceFieldTypeOfClass.equals(fieldTypeOfClass)) {
                flag = true;
                actualClass = fieldTypeOfClass;
                fieldSourceNode = tmpFieldSourceNode;
                break;
            }
            if (ClassUtils.getAllSupers(fieldTypeOfClass).contains(tmpSourceFieldTypeOfClass)
                    & !tmpSourceFieldTypeOfClass.getName().contains("java.lang.Object")
                    & !fieldTypeOfClass.getName().contains("java.lang.Object")) {
                flag = true;
                actualClass = fieldTypeOfClass;
                fieldSourceNode = tmpFieldSourceNode;
                break;
            }
            if (RuleUtils.couldSetGenericTypeObj(tmpFieldSourceNode.getType())) {
                valuesOfObjectType.add(tmpFieldSourceNode);
                actualClass = fieldTypeOfClass;
                fieldSourceNode = tmpFieldSourceNode;
            }
        }

        if (actualClass == null)
            return null;

        HashSet<SourceNode> toDelete = new HashSet<>();
        if (valuesOfObjectType.size() > 1) {
            for (SourceNode tmpSourceNode : valuesOfObjectType) {
                if (tmpSourceNode.getType().toString().contains("[]")
                        & fieldSourceNode.getType().toString().equals("java.lang.Object")
                        & !hasClass(fieldSourceNode.field.getLast().getDeclaringClass())) {
                    toDelete.add(fieldSourceNode);
                    fieldSourceNode = tmpSourceNode;
                }else if (fieldSourceNode.getType().toString().contains("[]")
                        & tmpSourceNode.getType().toString().equals("java.lang.Object")
                        & hasClass(fieldSourceNode.classOfField)){
                    toDelete.add(tmpSourceNode);
                }
            }
        }
        valuesOfObjectType.removeAll(toDelete);


        // 对 equals这种特殊情况进行污点补充
        if (!this.flag
                && descriptor.sootMethod.getSubSignature().equals("boolean equals(java.lang.Object)")
                && (!invokedDescriptor.fieldsParamIndexRecord.containsKey(0)
                || (invokedDescriptor.fieldsParamIndexRecord.containsKey(0)
                && invokedDescriptor.fieldsParamIndexRecord.get(0).isEmpty()))){
            HashSet<SourceNode> fieldSourceNodes = new HashSet<>();
            fieldSourceNodes.add(fieldSourceNode);
            invokedDescriptor.fieldsParamIndexRecord.put(0, fieldSourceNodes);
        }

        if ((flag || valuesOfObjectType.size() > 0) && !this.flag) {
            if (classFieldDepDuplicateRecord(this.curClass, actualClass)) {
                if (!classFieldsGraph.containsKey(actualClass)
                        && !curClassNode.fields.containsKey(fieldSourceNode)) {
                    ClassNode recordedFieldClassNode = getClassNode(actualClass);
                    curClassNode.fields.put(fieldSourceNode, new HashSet<>());
                    curClassNode.fields.get(fieldSourceNode).add(recordedFieldClassNode);
                    return recordedFieldClassNode;
                }
                if (RuleUtils.isEqMethod(invokedDescriptor.sootMethod)){
                    ClassNode nextClassNode = new ClassNode(curClassNode, invokedDescriptor.sootMethod, actualClass, fieldSourceNode, this, valuesOfObjectType);

                    if (!curClassNode.fields.containsKey(fieldSourceNode))
                        curClassNode.fields.put(fieldSourceNode, new HashSet<>());
                    curClassNode.fields.get(fieldSourceNode).add(nextClassNode);
                    nextClassNode.flag = true;
                    classFieldsGraph.put(actualClass, nextClassNode);
                    invokedDescriptor.visited = false;
                    nextClassNode.classId = curClassNode.classId + 1;
                    return nextClassNode;
                }
                return null;
            }

            if (actualClass.hasOuterClass() & Utils.endWithNumber(actualClass.getName()))
                actualClass = actualClass.getOuterClass();
            // 判断调用子类的父类方法的情况
            if (!curClass.isConcrete() && ClassRelationshipUtils.isSubClassOf(actualClass, curClass)
                    && !curClass.getName().equals("java.lang.Object")){
                SootClass fieldClass = Utils.toSootClass(fieldSourceNode.getType());
                if (fieldSourceNode.equals(curClassNode.source)
                        && !fieldClass.getName().contains("[]")
                        && !ClassRelationshipUtils.isSubClassOf(fieldClass, BasicDataContainer.commonClassMap.get("Map"))
                        && !ClassRelationshipUtils.isSubClassOf(fieldClass, BasicDataContainer.commonClassMap.get("List"))){
                    this.classFieldsGraph.remove(curClass);
                    this.classFieldsGraph.put(actualClass, curClassNode);
                    curClass = actualClass;
                    curClassNode.sootClass = curClass;
                    return null;
                }
            }
            SourceNode tmpSourceNode = FieldUtil.seletectPrioritySourceNode(fieldSources, fieldTypeOfClass);
            fieldSourceNode = tmpSourceNode!=null? tmpSourceNode: fieldSourceNode;
            ClassNode nextClassNode = new ClassNode(curClassNode, invokedDescriptor.sootMethod, actualClass, fieldSourceNode, this, valuesOfObjectType);
            // thinking[Fix]: 如果在前继的类层次结构中，已经有相同的类示例对象，则补充id计数的更新
            if (classFieldsGraph.containsKey(nextClassNode.sootClass)){
                nextClassNode.classId = classFieldsGraph.get(nextClassNode.sootClass).classId+1;}
            if (!curClassNode.fields.containsKey(fieldSourceNode))
                curClassNode.fields.put(fieldSourceNode, new HashSet<>());
            curClassNode.fields.get(fieldSourceNode).add(nextClassNode);
            nextClassNode.flag = true;
            classFieldsGraph.put(actualClass, nextClassNode);

            return nextClassNode;
        }
        return null;
    }

    /**
     * 获取callStack对应的fragment, 如果当前的方法调用序列偏离了gadget chain, 则返回最近的fragment
     * @param callStack
     * @return
     */
    public Fragment getFragment(LinkedList<SootMethod> callStack) {
        int countIndex = 0;
        for (Integer hashCode: this.fragment.linkedFragments){
            Fragment basicFragment = FragmentsContainer.basicFragmentsMap.get(hashCode);
            for (SootMethod tmpMtd: basicFragment.gadgets){
                if (tmpMtd.equals(callStack.get(countIndex)))
                    countIndex++;
                else return basicFragment;
                if (callStack.size() <= countIndex)
                    return basicFragment;
            }
        }
        return null;
    }

    public boolean classFieldDepDuplicateRecord(SootClass classFrom, SootClass classTo) {
        if (classFrom.equals(classTo))
            return true;

        if (classFieldsGraph.containsKey(classTo)) {
            ClassNode classNodeTo = classFieldsGraph.get(classTo);
            if (classNodeTo.rootClassNode != null) {
                if (classNodeTo.rootClassNode.sootClass.equals(classFrom))
                    return true;
            }
        } else {
            SootClass connectedToClass = ClassRelationshipUtils.getOuterClass(classTo);
            if (connectedToClass != null) {
                if (classFieldsGraph.containsKey(connectedToClass))
                    return true;
            }
        }
        return false;
    }

    public ClassNode createConClassNodes(TransformableNode tfNode, SootMethod preMethod,
                                    MethodDescriptor descriptor, MethodDescriptor invokedDescriptor) {
        if (preMethod == null | !tfNode.containsInvoke())
            return null;

        SootClass currentClass = descriptor.getCurrentClass();
        if (currentClass == null)   return null; // 如果当前是静态方法，则不记录conField

        MethodDescriptor preDescriptor = BasicDataContainer.getOrCreateDescriptor(preMethod);
        SootClass preClass = preDescriptor.getCurrentClass();

        // 1. 检查是否为某个 field 调用的方法
        ValueBox thisValueBox = Parameter.getThisValueBox(tfNode.node);
        SootMethod invokedMethod = invokedDescriptor.sootMethod;
        SootClass nextClass = invokedMethod.getDeclaringClass();
        Pair<SourceNode, HashSet<SourceNode>> pair = AnalyzeUtils.matchFieldSourceNode(thisValueBox, descriptor, nextClass);
        if (pair == null)   return null;
        SourceNode fieldSourceNode = pair.getKey();
        if (fieldSourceNode == null)  return null;

        ClassNode currentClassNode = AnalyzeUtils.getClassNode(preClass,currentClass, fieldSourceNode, this);
        if (currentClassNode == null) return null;

        SootClass tmpFieldClassOfType = Utils.toSootClass(fieldSourceNode.getType());
        if (ClassRelationshipUtils.isSubClassOf(tmpFieldClassOfType, nextClass))
            nextClass = tmpFieldClassOfType;

        // 检查欲添加的 ClassFieldsNode 是否重复
        if (isDuplicationClassNode(currentClass, nextClass))  return null;

        ClassNode nextClassNode = new ClassNode(currentClassNode, invokedMethod, nextClass, fieldSourceNode, this, pair.getValue());
        nextClassNode.flag = false;

        if (!currentClassNode.implicitFields.containsKey(fieldSourceNode)){
            currentClassNode.implicitFields.put(fieldSourceNode, new HashSet<>());
        }
        currentClassNode.implicitFields.get(fieldSourceNode).add(nextClassNode);

        if (!implicitClassFieldsGraph.containsKey(nextClass))
            implicitClassFieldsGraph.put(nextClass, new HashSet<>());
        implicitClassFieldsGraph.get(nextClass).add(nextClassNode);

        return nextClassNode;
    }

    private boolean isDuplicationClassNode(SootClass currentClass, SootClass nextClass) {
        if (currentClass.equals(nextClass))
            return true;
        if (classFieldsGraph.containsKey(nextClass))
            return true;
        if (!implicitClassFieldsGraph.containsKey(nextClass))
            return false;
        for (ClassNode implicitClassNode: implicitClassFieldsGraph.get(nextClass)){
            if (implicitClassNode.rootClassNode.sootClass.equals(currentClass))
                return true;
        }
        return false;
    }


    public void createAddGadgetNodeToClassNode(SootMethod invokedMethod, SootClass sootClass) {
        if (!invokedMethod.isStatic()){
            if (!ClassRelationshipUtils.isSubClassOf(sootClass, invokedMethod.getDeclaringClass()))
                return;
        }

        ClassNode classNode = getClassNode(sootClass);
        if (classNode != null){
            GadgetNode newGadgetNode = new GadgetNode(invokedMethod, sootClass);
            classNode.addGadgetNode(newGadgetNode);
        }
    }
}