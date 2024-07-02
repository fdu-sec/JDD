package gadgets.collection.iocd;

import cfg.Node;
import config.RegularConfig;
import container.BasicDataContainer;
import dataflow.node.SourceNode;
import gadgets.collection.iocd.unit.*;
import gadgets.collection.iocd.unit.instrument.IfStmtInstRecord;
import gadgets.collection.iocd.unit.instrument.Instruments;
import gadgets.collection.iocd.unit.instrument.MethodInstRecord;
import gadgets.collection.iocd.unit.instrument.SinkInstRecord;
import gadgets.collection.node.*;
import util.Pair;
import lombok.extern.slf4j.Slf4j;
import gadgets.collection.markers.Comparison;
import markers.SinkType;
import rules.sinks.*;
import soot.*;
import soot.jimple.IfStmt;
import util.ClassRelationshipUtils;
import util.StaticAnalyzeUtils.FieldUtil;
import util.StaticAnalyzeUtils.Parameter;

import java.io.FileWriter;
import java.io.IOException;
import java.util.*;

import static gadgets.collection.AnalyzeUtils.*;
import static util.DataSaveLoadUtil.toGJson;

@Slf4j
public class TransformerUtils {
    public static void exportGadgetRecordJson(GadgetInfoRecord gadgetInfoRecord, String dir) throws Exception {
        IOCD outputRecord = transformGadgetRecord(gadgetInfoRecord);
        int hasCode = gadgetInfoRecord.hashCode();
        outputRecord.hashCode = hasCode;
        String outputJson = toGJson(outputRecord);

        String fileName = dir + hasCode + ".json";
        try{
            FileWriter out = new FileWriter(fileName, false);
            out.write(outputJson);
            out.flush();
        } catch (IOException e){
            log.error("Could not write result to " + fileName + "!");
            e.printStackTrace();
        }

    }

    public static IOCD transformGadgetRecord(GadgetInfoRecord gadgetInfoRecord) {
        IOCD iocd = new IOCD();

        iocd.sinkType = gadgetInfoRecord.sinkType.toString();
        iocd.protocol = RegularConfig.protocol;
        iocd.needSerialize = BasicDataContainer.needSerializable;
        iocd.hashCollisionFlag = gadgetInfoRecord.hashCollisionFlag;
        recordSpecificInfosForJsonProtocol(gadgetInfoRecord, iocd);

        LinkedList<Pair<Integer,String>> callStack = new LinkedList<>();
        for (SootMethod gadget: gadgetInfoRecord.gadgets)
            callStack.add(new Pair<>(gadget.getSignature().hashCode(), gadget.getSignature()));
        iocd.gadgetCallStack = callStack;

        LinkedList<ClassRecord> tmpClassRecords = new LinkedList<>();
        HashSet<ClassRecord> conClassRecords = new HashSet<>();
        iocd.gadgetClasses = tmpClassRecords;
        iocd.conClassNodes = conClassRecords;

        SootClass rootClass = gadgetInfoRecord.rootClass;
        LinkedHashMap<SootClass, ClassNode> tmpClassNodesMap = gadgetInfoRecord.classFieldsGraph;
        ClassNode rootClassNode = tmpClassNodesMap.get(rootClass);

        ClassNode tmpRootClassNode = rootClassNode;
        while (tmpRootClassNode.rootClassNode != null){
            rootClassNode = tmpRootClassNode.rootClassNode;
            tmpRootClassNode = rootClassNode;
        }

        // 通过队列迭代算法处理从rootClass开始的一系列类节点
        Queue<ClassNode> classNodesQueue = new LinkedList<>();
        HashMap<ClassNode, FieldRecord> visited = new HashMap<>();
        classNodesQueue.add(rootClassNode);
        visited.put(rootClassNode, null);

        while (!classNodesQueue.isEmpty()) {
            ClassNode tmpClassNode = classNodesQueue.poll();

            ClassRecord cRecord = new ClassRecord();
            cRecord.id = tmpClassNode.classId;
            if (tmpClassNode.isProxy) {
                cRecord.isProxy = tmpClassNode.isProxy;
                cRecord.triggerMethod = tmpClassNode.triggerMethod.getName();
            }

            String tmpClassName = tmpClassNode.sootClass.getName(); // 该node所属对象
            cRecord.className = tmpClassName;
            if(tmpClassNode.rootClassNode == null){
                cRecord.setSourceRecord(null);
            }
            else {
//                Pair<String, String> tmpPredecessorRecord = new Pair<>(
//                        tmpClassNode.source.classOfField.getName(),
//                        tmpClassNode.source.field.getLast().getSignature()
//                );

                cRecord.setSourceRecord(makeSourceNodeRecord(tmpClassNode.source));
                for (SourceNode candidateSourceNode: tmpClassNode.candidateSources){
                    cRecord.getCandidateSources().add(makeSourceNodeRecord(candidateSourceNode));
                }

//                cRecord.setPredClassId(tmpClassNode.source.classId);

                if (tmpClassNode.caller != null) {
                    cRecord.setPredecessorMethod(makeInitMethodRecord(tmpClassNode.caller));
                }
            }

            LinkedList<MethodRecord> tmpMRs = new LinkedList<>();
            LinkedList<SootMethod> currentCallStack = tmpClassNode.gadgets;
            LinkedList<ConditionRecord> tmpAllConditions = new LinkedList<>();
            for (SootMethod sootMethod: currentCallStack){
                GadgetNode gadgetNode = gadgetInfoRecord.gadgetNodesMap.get(sootMethod);
                MethodRecord tmpMR = makeInitMethodRecord(gadgetNode);
                tmpMRs.add(tmpMR);

                HashMap<IfStmt, ConditionNode> tmpDominatorCNs = gadgetNode.dominatorConditions;
                HashMap<IfStmt, ConditionNode> tmpImplicitCNs = gadgetNode.implicitConditions;
                for (ConditionNode conditionNode: tmpDominatorCNs.values()){
                    ConditionRecord conditionRecord = makeInitConditionRecord(conditionNode, tmpMR, true);
                    if ((conditionRecord.conditionValue.isEmpty() && conditionRecord.conditionName.isEmpty())
                            && ((conditionRecord.type & ConditionNode.UNCONTROLLABLE) == 0))
                        continue;
                    tmpAllConditions.add(conditionRecord);
                }

                for (ConditionNode conditionNode: tmpImplicitCNs.values()){
                    ConditionRecord conditionRecord = makeInitConditionRecord(conditionNode, tmpMR, false);
                    if ((conditionRecord.conditionValue.isEmpty() && conditionRecord.conditionName.isEmpty())
                            && ((conditionRecord.type & ConditionNode.UNCONTROLLABLE) == 0))
                        continue;
                    tmpAllConditions.add(conditionRecord);
                }
            }
            cRecord.usedMethods = tmpMRs;
            cRecord.allConditions = tmpAllConditions;

            LinkedList<FieldRecord> tmpFieldRecord = new LinkedList<>();
            HashMap<SourceNode, HashSet<ClassNode>> tmpField = tmpClassNode.fields;
            for (SourceNode fieldSourceNode: tmpField.keySet()){
                HashSet<ClassNode> nextClassNodes = tmpClassNode.fields.get(fieldSourceNode);
                FieldRecord sourceToNextClassNode = makeInitFieldRecord(fieldSourceNode);

                tmpFieldRecord.add(sourceToNextClassNode);

                for (ClassNode nextClassNode: nextClassNodes) {
                    if (!visited.containsKey(nextClassNode) && nextClassNode != null) {
                        classNodesQueue.add(nextClassNode);
                        visited.put(nextClassNode, sourceToNextClassNode);
                    }
                }
            }
            cRecord.fields = tmpFieldRecord;

            ArrayList<FieldRecord> tmpConFieldRecord = new ArrayList<>();
            HashMap<SourceNode, HashSet<ClassNode>> tmpConField = tmpClassNode.implicitFields;
            for (SourceNode fieldSourceNode: tmpConField.keySet()) {
                HashSet<ClassNode> conNextClassNodes = tmpClassNode.implicitFields.get(fieldSourceNode);
                for (ClassNode conNextClassNode : conNextClassNodes) {
                    FieldRecord sourceToNextClassNode = makeInitFieldRecord(fieldSourceNode);
                    if (sourceToNextClassNode != null) {
                        sourceToNextClassNode.setFieldType(conNextClassNode.sootClass.getName());

                        tmpConFieldRecord.add(sourceToNextClassNode);

                        if (!visited.containsKey(conNextClassNode) && conNextClassNode != null) {
                            classNodesQueue.add(conNextClassNode);
                            visited.put(conNextClassNode, sourceToNextClassNode);
                        }
                    }
                }
            }
            cRecord.conFields = tmpConFieldRecord;

            cRecord.isProxy = tmpClassNode.isProxy;
            if (cRecord.isProxy){
//                cRecord.addProxyInterface.add(tmpClassNode.invocationHandlerClassNode);
            }

            if (!tmpClassNode.flag){
                cRecord.flag = false;
                conClassRecords.add(cRecord);
            }
            else {
                tmpClassRecords.add(cRecord);
            }
        }

        LinkedHashMap<Integer, Boolean> conditionsOrder = new LinkedHashMap<>();
        for (SootMethod gadget: gadgetInfoRecord.gadgets){
            if (gadgetInfoRecord.gadgets.getLast().equals(gadget))
                continue;
            GadgetNode gadgetNode = gadgetInfoRecord.gadgetNodesMap.get(gadget);
            if (gadgetNode == null)
                continue;
            if (gadgetNode.allConditions.isEmpty())
                continue;

            MethodRecord methodRecord = makeInitMethodRecord(gadgetNode);
            for (IfStmt ifStmt: gadgetNode.allConditions.keySet()){
                ConditionNode conditionNode = gadgetNode.allConditions.get(ifStmt);
                ConditionRecord conditionRecord = makeInitConditionRecord(conditionNode, methodRecord, conditionNode.isDominator);
                if ((conditionRecord.conditionValue.isEmpty() && conditionRecord.conditionName.isEmpty())
                        && ((conditionRecord.type & ConditionNode.UNCONTROLLABLE) == 0))
                    continue;

                conditionsOrder.put(ifStmt.hashCode(), conditionNode.isDominator);
            }
        }
        iocd.conditionsRecords = conditionsOrder;

        HashSet<DependenceNode> dependenceNodes = gadgetInfoRecord.dependenceNodes;
        HashSet<DependenceRecord> dependenceRecords = new HashSet<>();
        for (DependenceNode dependenceNode: dependenceNodes) {
            DependenceRecord tmpDependenceRecord = makeInitDependenceRecord(dependenceNode);
            dependenceRecords.add(tmpDependenceRecord);
        }
        iocd.dependenceRecords = dependenceRecords;

        if (gadgetInfoRecord.collisionNode != null)
            iocd.hashCollisionRecord = makeInitHashCollisionRecord(gadgetInfoRecord.collisionNode);

        for (SourceNode sourceNode: gadgetInfoRecord.fieldsUsedSitesRecords.keySet()){
            for (Pair<String, Integer> usedSite : gadgetInfoRecord.fieldsUsedSitesRecords.get(sourceNode)){
                UsedSiteRecord usedSiteRecord = makeInitUsedSiteRecord(iocd, usedSite);
                FieldRecord fieldRecord = makeInitFieldRecord(sourceNode);
                if (fieldRecord != null) {
                    usedSiteRecord.usedFields.add(fieldRecord);
                }
            }
        }

        for (ClassNode implicitClassNode: gadgetInfoRecord.getAllImplicitClassNodes()){
            for (SootMethod sootMethod: implicitClassNode.implicitGadgetNodes.keySet()){
                GadgetNode gadgetNode = implicitClassNode.implicitGadgetNodes.get(sootMethod);
                MethodRecord methodRecord = makeInitMethodRecord(gadgetNode);
                for (ConditionNode conditionNode: gadgetNode.implicitConditions.values()){
                    ConditionRecord tmpConditionRecord = makeInitConditionRecord(conditionNode, methodRecord, false);
                    iocd.supplementConditions.add(tmpConditionRecord);
                }
            }
        }

        HashSet<SinkNode> sinkNodes = gadgetInfoRecord.sinkNodes;
        LinkedList<SinkRecord> tmpSinkRecords = new LinkedList<>();
        for (SinkNode sinkNode: sinkNodes){
            SinkRecord sinkRecord = makeInitSinkRecord(sinkNode);
            tmpSinkRecords.add(sinkRecord);
        }
        iocd.sinkRecords = tmpSinkRecords;

        return iocd;
    }


    public static SourceRecord makeSourceNodeRecord(SourceNode sourceNode){
        LinkedList<String> fieldSigs = new LinkedList<>();
        if (!sourceNode.field.isEmpty()){
            for (SootField sootField : sourceNode.field)
                fieldSigs.add(sootField.getSignature());
        }

        SourceRecord sourceRecord = new SourceRecord(
                new Pair<>(sourceNode.classOfField.getName(),
                        sourceNode.field.getLast().getSignature()),
                fieldSigs);

        return sourceRecord;
    }

    public static UsedSiteRecord makeInitUsedSiteRecord(IOCD iocd,
                                              Pair<String, Integer> usedSite){
        for (UsedSiteRecord usedSiteRecord : iocd.usedFieldsRecords){
            if (usedSiteRecord.inClassName.equals(usedSite.getKey()) & usedSiteRecord.site.equals(usedSite.getValue()))
                return usedSiteRecord;
        }
        UsedSiteRecord newUsedSiteRecord = new UsedSiteRecord();
        newUsedSiteRecord.inClassName = usedSite.getKey();
        newUsedSiteRecord.site = usedSite.getValue();
        iocd.usedFieldsRecords.add(newUsedSiteRecord);
        return newUsedSiteRecord;
    }

    public static CollisionRecord makeInitHashCollisionRecord(CollisionNode collisionNode){
        CollisionRecord collisionRecord = new CollisionRecord();
        collisionRecord.type = collisionNode.type;
        collisionRecord.collisionMethodRecord = makeInitMethodRecord(collisionNode.collisionMethod);
        if (collisionNode.firstHashCodeMtd != null)
            collisionRecord.firstHashCodeMtd = makeInitMethodRecord(collisionNode.firstHashCodeMtd);
        if (collisionNode.secondHashCodeMtd != null)
            collisionRecord.secondHashCodeMtd = makeInitMethodRecord(collisionNode.secondHashCodeMtd);

        for (SourceNode sourceNode: collisionNode.first){
            FieldRecord tmpFieldRecord = makeInitFieldRecord(sourceNode);
            if (tmpFieldRecord != null)
                collisionRecord.first.add(tmpFieldRecord);
        }

        for (SourceNode sourceNode: collisionNode.second){
            FieldRecord tmpFieldRecord = makeInitFieldRecord(sourceNode);
            if (tmpFieldRecord != null)
                collisionRecord.second.add(tmpFieldRecord);
        }

        for (SourceNode sourceNode: collisionNode.top){
            FieldRecord tmpFieldRecord = makeInitFieldRecord(sourceNode);
            if (tmpFieldRecord != null)
                collisionRecord.top.add(tmpFieldRecord);
        }

        return collisionRecord;
    }

    public static DependenceRecord makeInitDependenceRecord(DependenceNode dependenceNode){
        DependenceRecord dependenceRecord = new DependenceRecord();
        dependenceRecord.type = dependenceNode.type;
        if (dependenceNode.methodName != null)
            dependenceRecord.methodName = dependenceNode.methodName;

        dependenceRecord.leftRecordF = makeInitFieldRecord(dependenceNode.left);
        dependenceRecord.rightRecordF = makeInitFieldRecord(dependenceNode.right);

        return dependenceRecord;
    }

    public static SinkRecord makeInitSinkRecord(SinkNode sinkNode){
        SinkRecord sinkRecord = new SinkRecord();
        sinkRecord.sinkClassName = sinkNode.sootClass.getName();
        sinkRecord.sinkMethod = makeInitMethodRecord(sinkNode.node.sootMethod);
        sinkRecord.jimpleUnitInfo = sinkNode.node.unit.toString();
        if (sinkNode.sinkType.equals(SinkType.FILE))
            makeInitFileSinkRecord(sinkNode,sinkRecord);
        else if (sinkNode.sinkType.equals(SinkType.INVOKE))
            makeInitInvokeSinkRecord(sinkNode,sinkRecord);
        else makeInitSimpleSinkRecord(sinkNode, sinkRecord);

        return sinkRecord;
    }

    public static SinkRecord makeInitSimpleSinkRecord(SinkNode sinkNode, SinkRecord sinkRecord){
        for (Integer paramInd: sinkNode.controllableSinkValues.keySet()) {
            for (SourceNode sourceNode : sinkNode.controllableSinkValues.get(paramInd)) {
                FieldRecord tmpFieldRecord = makeInitFieldRecord(sourceNode);
                if (tmpFieldRecord != null) {
                    Pair<Integer, FieldRecord> pair = new Pair<>(paramInd, tmpFieldRecord);
                    sinkRecord.sinkField.add(pair);
                }
            }
        }

        return sinkRecord;
    }

    public static SinkRecord makeInitInvokeSinkRecord(SinkNode sinkNode, SinkRecord sinkRecord){
        int elementCount = 0;
        if (sinkNode.sinkObject != null){
            FieldRecord tmpFieldRecord = makeInitFieldRecord(sinkNode.sinkObject);
            if (tmpFieldRecord != null) {
                elementCount ++;
                sinkRecord.sinkClassBelongToF = tmpFieldRecord;
            }
        }

        if (sinkNode.sinkMethod != null){
            FieldRecord tmpFieldRecord = makeInitFieldRecord(sinkNode.sinkMethod);
            if (tmpFieldRecord != null) {
                elementCount ++;
                sinkRecord.sinkMethodF = tmpFieldRecord;
            }
        }

        if (sinkNode.sinkMethodName != null){
            FieldRecord tmpFieldRecord = makeInitFieldRecord(sinkNode.sinkMethodName);
            if (tmpFieldRecord != null) {
                elementCount ++;
                sinkRecord.sinkMethodNameF = tmpFieldRecord;
            }
        }

        if ( elementCount != 2)
            return null;
        return sinkRecord;
    }

    public static SinkRecord makeInitFileSinkRecord(SinkNode sinkNode, SinkRecord sinkRecord){
        int elementCount = 0;
        if (!sinkNode.sinkFilePath.isEmpty()){
            for (SourceNode sourceNode: sinkNode.sinkFilePath){
                FieldRecord tmpFieldRecord = makeInitFieldRecord(sourceNode);
                if (tmpFieldRecord != null){
                    sinkRecord.sinkFilePathF.add(tmpFieldRecord);
                    elementCount = 1;
                }
            }
        }


        if (sinkNode.sinkFileContent != null){
            FieldRecord tmpFieldRecord = makeInitFieldRecord(sinkNode.sinkFileContent);
            if (tmpFieldRecord != null){
                sinkRecord.sinkFileContentF = tmpFieldRecord;
                elementCount ++;
            }
        }

        if (elementCount != 2)
            return null;

        return sinkRecord;
    }

    public static ConditionRecord makeInitConditionRecord(ConditionNode conditionNode,
                                                          MethodRecord methodRecord,
                                                          boolean isBasic){
        ConditionRecord conditionRecord = new ConditionRecord();
        conditionRecord.basic = isBasic;
        conditionRecord.type = conditionNode.type;
        conditionRecord.methodBelongTo = methodRecord;
        IfStmt ifStmt = conditionNode.conditionNode.getIfStmt();
        conditionRecord.ifStmt = ifStmt.toString();
        conditionRecord.hashCode = ifStmt.hashCode();
        conditionRecord.comparator = getComparator(conditionNode.comparison);

        Pair<String,Integer> pair = new Pair<>(conditionNode.conditionNode.context.sootClass.getName(),
                getLineNumberByUnit(conditionNode.conditionNode.node.unit));
        conditionRecord.usedSite = pair;

        LinkedHashMap<String, FieldRecord> conditionNames = new LinkedHashMap<>(); // 变量
        LinkedHashMap<String, String> conditionValues = new LinkedHashMap<>(); // 比较值 (E.g. 常量)
        for (SourceNode sourceNode: conditionNode.controllableValues){
            FieldRecord fieldRecord = makeInitFieldRecord(sourceNode);
            if (fieldRecord != null)
                conditionNames.put(sourceNode.getType().toString(), fieldRecord);
        }

        for (Object value: conditionNode.conditionValues){
            conditionValues.put(getTypeString(value), value.toString());
        }

        conditionRecord.conditionName = conditionNames;
        conditionRecord.conditionValue = conditionValues;

        return conditionRecord;
    }

    public static String getTypeString(Object value){
        if (value instanceof Value)
            return ((Value) value).getType().toString();
        return value.getClass().toString();
    }

    public static FieldRecord makeInitFieldRecord(SourceNode sourceNode){
        if (!sourceNode.isField())
            return null;

        FieldRecord fieldRecord = new FieldRecord();
        fieldRecord.classBelongTo = sourceNode.classOfField.getName();
        fieldRecord.classId = sourceNode.classId;
        fieldRecord.fieldName = sourceNode.field.getFirst().getName();
        fieldRecord.fieldType = sourceNode.field.getFirst().getType().toString();
        fieldRecord.sig = sourceNode.field.getFirst().getSignature();
        fieldRecord.isTransient = FieldUtil.isTransientType(sourceNode.field.getFirst());

        FieldRecord curFieldRecord = fieldRecord;
        if (sourceNode.field.size() > 1) {
            for (int index = 1; index < sourceNode.field.size(); index++) {
                SootField sootField = sourceNode.field.get(index);
                FieldRecord nextFieldRecord = new FieldRecord();
                nextFieldRecord.classBelongTo = sootField.getDeclaringClass().getName();
                nextFieldRecord.fieldName = sootField.getName();
                nextFieldRecord.fieldType = sootField.getType().toString();
                nextFieldRecord.sig = sootField.getSignature();
                nextFieldRecord.isTransient = FieldUtil.isTransientType(sourceNode.field.getFirst());
                curFieldRecord.fields.add(nextFieldRecord);

                curFieldRecord = nextFieldRecord;
            }
        }

        return fieldRecord;
    }

    public static String getComparator(Comparison comparison){
        if (comparison.equals(Comparison.NO_EQUAL_TO))
            return "!=";
        if (comparison.equals(Comparison.EQUAL))
            return "==";
        if (comparison.equals(Comparison.SMALLER))
            return "<";
        if (comparison.equals(Comparison.SMALLER_OR_EQUAL))
            return "<=";
        if (comparison.equals(Comparison.BIGGER))
            return ">";
        if (comparison.equals(Comparison.BIGGER_OR_EQUAL))
            return ">=";
        return null;
    }

    public static MethodRecord makeInitMethodRecord(GadgetNode gadgetNode){
        MethodRecord methodRecord = new MethodRecord();
        methodRecord.methodName = gadgetNode.sootMethod.getName();
        methodRecord.sig = gadgetNode.sootMethod.getSignature();
        methodRecord.classBelongTo = gadgetNode.sootClass.getName();
        return methodRecord;
    }

    public static MethodRecord makeInitMethodRecord(SootMethod sootMethod){
        MethodRecord methodRecord = new MethodRecord();
        methodRecord.classBelongTo = sootMethod.getDeclaringClass().getName();
        methodRecord.methodName = sootMethod.getName();
        methodRecord.sig = sootMethod.getSignature();
        return methodRecord;
    }

    public static void recordSpecificInfosForJsonProtocol(GadgetInfoRecord gadgetInfoRecord, IOCD iocd){
        if (!RegularConfig.protocol.equals("json"))
            return;

        // 记录 entry 方法是否为public的
        SootMethod entryMtd = gadgetInfoRecord.gadgets.getFirst();
        iocd.publicEntry = entryMtd.isPublic();

        if (entryMtd.getName().startsWith("get")){
            iocd.entryType = "getter";
        }else if (ClassRelationshipUtils.isOverWrittenInterfaceMtd(entryMtd)){
            iocd.entryType = "interfaceOver";
        }
    }


    public static void recordIfStmtAndMethodForInst(GadgetInfoRecord gadgetInfoRecord, Instruments instruments){
        HashSet<GadgetNode> allGadgetNodes = gadgetInfoRecord.getAllGadgetNodes();
        for (GadgetNode gadgetNode: allGadgetNodes){
            SootMethod sootMethod = gadgetNode.sootMethod;
            SootClass sootClass = gadgetNode.sootClass;

            HashSet<IfStmtInstRecord> ifStmtInstRecords = instruments.classIfStmtsMap.get(sootClass.getName());
            HashSet<Integer> hashCodesRecord = new HashSet<>();
            if (ifStmtInstRecords != null) {
                for (IfStmtInstRecord ifStmtRecord : ifStmtInstRecords) {
                    hashCodesRecord.add(ifStmtRecord.hashCode);
                }
            }

            HashSet<IfStmtInstRecord> ifStmtRecords = new HashSet<>();

            HashMap<IfStmt, Integer> ifStmtLineNumberMap = getLineNumberOfIfStmts(sootMethod);
            HashMap<IfStmt, Node> ifStmtNodeMap = getIfStmtNodeMap(sootMethod);

            HashMap<IfStmt, ConditionNode> allConditionNodes = new HashMap<>();
            allConditionNodes.putAll(gadgetNode.dominatorConditions);
            allConditionNodes.putAll(gadgetNode.implicitConditions);

            for (IfStmt ifStmt: allConditionNodes.keySet()){
                if (hashCodesRecord.contains(ifStmt.hashCode()))
                    continue;
                IfStmtInstRecord ifStmtRecord = new IfStmtInstRecord();
                ifStmtRecord.setClassName(sootMethod.getDeclaringClass().getName());
                ifStmtRecord.setMethodSubSig(sootMethod.getSubSignature());
                ifStmtRecord.setMethodName(sootMethod.getName());
                ifStmtRecord.setLineNumber(ifStmtLineNumberMap.get(ifStmt));
                ifStmtRecord.setHashCode(ifStmt.hashCode());
                ifStmtRecord.setBasic(false);

                Node node = ifStmtNodeMap.get(ifStmt);
                HashSet<Integer> successes = new HashSet<>();
                for (Node success : node.successorNodes){
                    successes.add(getLineNumberByUnit(success.unit));
                }
                ifStmtRecord.setSuccessor(successes);

                ifStmtRecords.add(ifStmtRecord);
            }

            if (instruments.getClassIfStmtsMap().containsKey(sootClass.getName())){
                instruments.getClassIfStmtsMap().get(sootClass.getName()).addAll(ifStmtRecords);
            }else {
                instruments.getClassIfStmtsMap().put(sootClass.getName(), ifStmtRecords);
            }

            HashSet<MethodInstRecord> methodInstRecords = instruments.getClassMethodsMap().get(sootClass.getName());
            HashSet<String> methodSigs = new HashSet<>();
            if (methodInstRecords != null) {
                for (MethodInstRecord methodInstRecord : methodInstRecords)
                    methodSigs.add(methodInstRecord.sig);
            }
            if (!methodSigs.contains(sootMethod.getSignature())) {
                // 记录 methods 信息
                MethodInstRecord methodInstRecord = new MethodInstRecord();
                methodInstRecord.setClassName(sootClass.getName());
                methodInstRecord.setSubSig(sootMethod.getSubSignature());
                methodInstRecord.setSig(sootMethod.getSignature());
                methodInstRecord.setName(sootMethod.getName());
                methodInstRecord.setHashCode(sootMethod.getSignature().hashCode());

                if (instruments.getClassMethodsMap().containsKey(sootClass.getName())) {
                    instruments.getClassMethodsMap().get(sootClass.getName()).add(methodInstRecord);
                } else {
                    HashSet<MethodInstRecord> toAdd = new HashSet<>();
                    toAdd.add(methodInstRecord);
                    instruments.getClassMethodsMap().put(sootClass.getName(), toAdd);
                }
            }
        }
    }



    public static void exportInstrumentsRecordJson(Instruments instruments, String dir){
        recordSink(instruments);
        String outputJson = toGJson(instruments);
        String fileName = dir + "IfStmtRecord.json";
        try{
            FileWriter out = new FileWriter(fileName, false);
            out.write(outputJson);
            out.flush();
        } catch (IOException e){
            log.error("Could not write result to " + fileName + "!");
            e.printStackTrace();
        }
    }

    public static void recordSink(Instruments instruments){
        // ClassLoader
        for (String methodSig: ClassLoaderCheckRule.newInstanceMethodSigs){
            setSinkInstRecord(methodSig, true, Arrays.asList(-1), instruments);
        }
        for (String methodSig : ClassLoaderCheckRule.classLoaderRiskyMethodSigs.get("ClassLoader.defineClass")){
            setSinkInstRecord(methodSig, false, "byte[]", instruments);
        }
        for (String methodSig : ClassLoaderCheckRule.classLoaderRiskyMethodSigs.get("URLClassLoader.<init>")){
            setSinkInstRecord(methodSig, false, "java.net.URL[]", instruments);
        }
        for (String methodSig : ClassLoaderCheckRule.classLoaderRiskyMethodSigs.get("URLClassLoader.loadClass")){
            setSinkInstRecord(methodSig, false, Arrays.asList(-1), instruments);
        }
        for (String methodSig : ClassLoaderCheckRule.classLoaderRiskyMethodSigs.get("Class.forName")){
            setSinkInstRecord(methodSig, false, "java.lang.ClassLoader", instruments);
        }

        // EXE
        for (String methodSig: ExecCheckRule.riskyMethodSigs){
            if (Scene.v().containsMethod(methodSig)){
                SootMethod sootMethod = Scene.v().getMethod(methodSig);
                setSinkInstRecord(sootMethod,true,Arrays.asList(0),instruments);
            }
        }

        // FileCheck
        for (String methodSig: FileCheckRule.fileSinkSig) {
            setSinkInstRecord(methodSig, true, Arrays.asList(0), instruments);
        }

        // Invoke
        for (String methodSig : InvokeCheckRule.invokeSigs) {
            setSinkInstRecord(methodSig,true,Arrays.asList(-1,0),instruments);
        }

        // LookUp
        for (String methodSig : JNDICheckRule.riskyJNDIMethodsSig){
            SootMethod sootMethod = Scene.v().getMethod(methodSig);
            if (sootMethod == null) {
                log.info("Cannot find soot Method " + methodSig);
                return;
            }

            Integer ind = null;
            if (methodSig.contains("lookup")){
                ind = Parameter.getArgIndexByType(sootMethod,"java.lang.String");
                if (ind == null)
                    ind = Parameter.getArgIndexByType(sootMethod, "javax.naming.Name");
            }
            if (methodSig.contains("getObjectInstance")) {
                ind = Parameter.getArgIndexByType(sootMethod, "java.lang.Object");
            }
            if (ind == null)
                continue;
            setSinkInstRecord(sootMethod, true, Arrays.asList(ind),instruments);
        }

        // Custom
        CustomCheckRule.setSinksInstRecord(instruments);
    }


    public static void setSinkInstRecord(String methodSig, boolean flag, String typeString, Instruments instruments){
        SootMethod sootMethod = Scene.v().getMethod(methodSig);
        if (sootMethod == null) {
            log.info("Cannot find soot Method " + methodSig);
            return;
        }

        setSinkInstRecord(sootMethod,flag,Arrays.asList(Parameter.getArgIndexByType(sootMethod,typeString)),instruments);
    }

    public static void setSinkInstRecord(String methodSig, boolean flag, List<Integer> pollutedParams, Instruments instruments){
        SootMethod sootMethod = Scene.v().getMethod(methodSig);
        if (sootMethod == null) {
            log.info("Cannot find soot Method " + methodSig);
            return;
        }

        setSinkInstRecord(sootMethod, flag, pollutedParams, instruments);
    }

    public static void setSinkInstRecord(SootMethod sootMethod, boolean flag, List<Integer> pollutedParams, Instruments instruments){
        SinkInstRecord sinkInstRecord = new SinkInstRecord();

        MethodInstRecord methodInstRecord = new MethodInstRecord();
        methodInstRecord.setName(sootMethod.getName());
        methodInstRecord.setSubSig(sootMethod.getSubSignature());
        methodInstRecord.setSig(sootMethod.getSignature());
        methodInstRecord.setClassName(sootMethod.getDeclaringClass().getName());
        methodInstRecord.setHashCode(sootMethod.getSignature().hashCode());
        sinkInstRecord.setMethodInstRecord(methodInstRecord);

        for (Integer paramInd: pollutedParams)
            sinkInstRecord.getPollutedParams().add(paramInd);
        sinkInstRecord.setFlag(flag);

        instruments.getSinkRecords().add(sinkInstRecord);
    }
}
