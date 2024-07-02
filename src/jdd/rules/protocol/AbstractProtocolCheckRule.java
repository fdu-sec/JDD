package rules.protocol;

import config.RegularConfig;
import tranModel.Rules.RuleUtils;
import tranModel.Taint.Taint;
import tranModel.Transformable;
import tranModel.TransformableNode;
import container.BasicDataContainer;
import container.FragmentsContainer;
import dataflow.node.MethodDescriptor;
import dataflow.node.SourceNode;
import detetor.SearchGadgetChains;
import detetor.SearchUtils;
import lombok.extern.slf4j.Slf4j;
import markers.SinkType;
import rules.sinks.*;
import soot.*;
import soot.jimple.Stmt;
import util.ClassRelationshipUtils;
import util.StaticAnalyzeUtils.ClassUtils;
import util.StaticAnalyzeUtils.FieldUtil;
import util.StaticAnalyzeUtils.Parameter;
import util.Utils;

import java.io.IOException;
import java.util.*;

import static detetor.SearchUtils.initDealBeforeSearching;
import static gadgets.collection.AnalyzeUtils.getHashCodeMtd;
import static tranModel.Rules.RuleUtils.checkTransientControllableSimply;

@Slf4j
public abstract class AbstractProtocolCheckRule implements ProtocolCheckRule {
    public static HashSet<String> specialSinkClass = new HashSet<>(Arrays.asList("java.io.FileOutputStream"));
    public HashSet<String> entryMethods = new HashSet<>();
    public LinkedHashMap<SinkType, CheckRule> sinkCheckRule = new LinkedHashMap<>();
    public Set<SootClass> candidateClassSet = new HashSet<>();

    public Set<SootMethod> sources = new HashSet<>();
    public Set<SootMethod> fsMtds = new HashSet<>();

    public abstract void init();

    void setSinkCheckRule(){
        if (RegularConfig.sinkRules.contains("classLoad")) {
            ClassLoaderCheckRule classLoaderCheckRule = new ClassLoaderCheckRule();
            sinkCheckRule.put(classLoaderCheckRule.sinkType, classLoaderCheckRule);
        }
        if (RegularConfig.sinkRules.contains("file")) {
            FileCheckRule fileCheckRule = new FileCheckRule();
            sinkCheckRule.put(fileCheckRule.sinkType,fileCheckRule);
        }
        if (RegularConfig.sinkRules.contains("invoke")) {
            InvokeCheckRule invokeCheckRule = new InvokeCheckRule();
            sinkCheckRule.put(invokeCheckRule.sinkType, invokeCheckRule);
        }
        if (RegularConfig.sinkRules.contains("jndi")) {
            JNDICheckRule JNDICheckRule = new JNDICheckRule();
            sinkCheckRule.put(JNDICheckRule.sinkType, JNDICheckRule);
        }
        if (RegularConfig.sinkRules.contains("secondDes")) {
            SecondDesCheckRule secondDesCheckRule = new SecondDesCheckRule();
            sinkCheckRule.put(secondDesCheckRule.sinkType, secondDesCheckRule);
        }
        if (RegularConfig.sinkRules.contains("exec")) {
            ExecCheckRule execCheckRule = new ExecCheckRule();
            sinkCheckRule.put(execCheckRule.sinkType, execCheckRule);
        }
        if (RegularConfig.sinkRules.contains("custom")){
            CustomCheckRule customCheckRule = new CustomCheckRule();
            sinkCheckRule.put(customCheckRule.sinkType,  customCheckRule);
        }
    }

    public CheckRule getCheckRule(SinkType sinkType){
        return sinkCheckRule.get(sinkType);
    }

    public void apply(MethodDescriptor mtdDes,
                      LinkedList<SootMethod> callStack,
                      Transformable transformable) throws IOException{
        if(!((TransformableNode)transformable).containsInvoke()){ return; }
        for(CheckRule checkRule : sinkCheckRule.values()){
            checkRule.apply(mtdDes, callStack, transformable);
        }
    }


    // 获取sources方法
    public abstract HashSet<SootMethod> getSourceMethods();

    public boolean openBPLink(){
        return true;
    }

    // 判断sootMethod是否为source 方法
    public boolean isSource(SootMethod sootMethod){
        return sources.contains(sootMethod) & !fsMtds.contains(sootMethod);
    };
    // 判断是否能用equals触发
    public boolean needEqualsTrigger() {return false;}

    // 在获取entry methods之前，先进行一系列筛选
    // (1) 类筛选
    // (2) 方法筛选 [根据各个协议不同]
    public void doClassCheck(){
        candidateClassSet.addAll(Scene.v().getApplicationClasses());
        candidateClassSet.addAll(Scene.v().getClasses());
        log.info("进行类筛选，筛选前分析类总数为：" + candidateClassSet.size());
        blackListFilter();
        if(BasicDataContainer.needSerializable){ serializationFilter(); }

        log.info("筛选后分析类总数为：" + candidateClassSet.size());
    }

    public void blackListFilter(){
        HashSet<SootClass> toDelete = new HashSet<>();
        for (SootClass sootClass: candidateClassSet){
            if (BasicDataContainer.inBlackList(sootClass))
                toDelete.add(sootClass);
        }
        toDelete.forEach(candidateClassSet::remove);
    }

    void serializationFilter(){
        HashSet<SootClass> subClasses = ClassUtils.getAllSubs(Utils.toSootClass("java.io.Serializable"));
        List<SootClass> classToRemove = new ArrayList<>();
        for(SootClass clazz : candidateClassSet){
            if(AbstractProtocolCheckRule.specialSinkClass.contains(clazz.getName())){
                continue;
            }
            if (BasicDataContainer.needSerializable
                    & !subClasses.contains(clazz)
                    & candidateClassSet.contains(clazz)){
                classToRemove.add(clazz);
            }
        }
        classToRemove.forEach(candidateClassSet::remove);

    }

    public void filterFixedEqualsMethods() throws IOException {
        SearchUtils.setDetectSchemeOn(); // 设置开始检测的 flag
        SootMethod equalMtd = Scene.v().getMethod("<java.lang.Object: boolean equals(java.lang.Object)>");
        HashSet<SootMethod> sourceMethods = ClassRelationshipUtils.getAllSubMethods(
                equalMtd
        );

        // TODO:
        HashSet<SootMethod> toDelete = new HashSet<>();
        for (SootMethod sootMethod: sourceMethods){
            if (!this.candidateClassSet.contains(sootMethod.getDeclaringClass()))
                toDelete.add(sootMethod);
        }

        sourceMethods.removeAll(toDelete);

        // 将其添加到 Source 中
        FragmentsContainer.sources.addAll(sourceMethods);

        for (SootMethod mtd: sourceMethods){
            if (!RuleUtils.isEqMethod(mtd))
                continue;
            SootMethod hashCodeMtd = getHashCodeMtd(mtd.getDeclaringClass());
            if (hashCodeMtd == null)
                continue;
            recordFixedEqMethod(mtd, hashCodeMtd);
        }
    }

    public static void recordFixedEqMethod(SootMethod mtd, SootMethod hashCodeMtd) throws IOException {
        if (mtd.isStatic()
                || Utils.isBasicType(mtd.getDeclaringClass().getName()))
            return;
        SootClass clz = hashCodeMtd.getDeclaringClass();
        HashSet<SourceNode> usedFields = new HashSet<>();
        boolean flag = false; // 记录是否因为调用方法数量超过控制导致检测出的fields数量为0

        LinkedList<SootMethod> callStack = new LinkedList<>(Arrays.asList(hashCodeMtd));
        MethodDescriptor descriptor = initDealBeforeSearching(hashCodeMtd, null);
        flag = SearchGadgetChains.isValidFixedHashCode(true, hashCodeMtd, usedFields,callStack);
        // 记录所有的情况, 避免重复检测
        FragmentsContainer.classHashCodeFieldsMap.put(clz, usedFields);
        RuleUtils.filterOuterSource(usedFields, descriptor.getCurrentClass());
        if (usedFields.isEmpty() & !callStack.contains(null)) {
            FragmentsContainer.fixedHashClass.put(clz, new HashSet<>());
            FragmentsContainer.singleHashFixedClass.add(clz);
        }
        else if (!usedFields.isEmpty() & usedFields.size() <= 4){
            boolean addFlag = true;
            HashSet<SourceNode> tmpToDelete = new HashSet<>();

            if (flag) {
                boolean tmpFlag = true;
                int count = 0, otherCount = 0;
                for (SourceNode sourceNode: usedFields){
                    if (Utils.isBasicType(sourceNode.getType()))
                        continue;
//                        if (!sourceNode.getType().toString().equals("java.lang.Object")
//                                && !sourceNode.getType().toString().equals("java.lang.Object[]"))
                    if (RuleUtils.isSingleGenericType(sourceNode.getType()))
                        count = count + 1;
                    else if (!RuleUtils.isGeneticType(sourceNode.getType())) {
                        tmpFlag = false;
                        otherCount ++;
                        break;
                    }
                    else continue;
                }

                if (count == 0
                        && usedFields.size() == 1
                        && (Utils.isBasicType(usedFields.iterator().next().getType()))){
                    FragmentsContainer.singleHashFixedClass.add(clz);
                    FragmentsContainer.fixedHashClass.put(clz, new HashSet<>(usedFields));
                    return;
                }
                else if (tmpFlag & count % 2 == 0) {
                    FragmentsContainer.singleHashFixedClass.add(clz);
                    FragmentsContainer.fixedHashClass.put(clz, new HashSet<>(usedFields));
                    return;
                }else if (count % 2 == 1 && otherCount == 0) {
                    FragmentsContainer.fixedHashClass.put(clz, new HashSet<>(usedFields));
                }else return;
            }

            for (SourceNode sourceNode: usedFields){
                if (!sourceNode.isField()){
                    addFlag = false;
                    break;
                }
                if (!RuleUtils.validControllableCollisionType(sourceNode, descriptor)){
                    addFlag = false;
                    break;
                }
                if (!ClassRelationshipUtils.isSubClassOf(mtd.getDeclaringClass(), sourceNode.classOfField))
                    tmpToDelete.add(sourceNode);
            }

            if (addFlag) {
                usedFields.removeAll(tmpToDelete);
                FragmentsContainer.fixedHashClass.put(clz, new HashSet<>(usedFields));
            }
        }
        BasicDataContainer.resetState();
    }

    public static boolean isSingleEvenCollisionHc(SootMethod mtd){
        if (!FragmentsContainer.isSingleFixedEqualsMethod(mtd))
            return false;
        int count = 0;
        for (SourceNode sourceNode: FragmentsContainer.fixedHashClass.get(mtd.getDeclaringClass())){
            String typeStr = sourceNode.getType().toString();
            String typeStrTop = sourceNode.getType(0).toString();
            if (typeStr.endsWith("$Entry[]")
                    || typeStr.endsWith("$Node[]")
                    || typeStrTop.endsWith("$Entry[]")
                    || typeStrTop.endsWith("$Node[]"))
                return false;
            if (RuleUtils.isSingleGenericType(sourceNode.getType()))    count++;
        }
        return count > 1;
    }

    public static boolean isSingleHashControllable(SootMethod mtd) throws IOException {
        SootClass clz = mtd.getDeclaringClass();
        if (!FragmentsContainer.classHashCodeFieldsMap.containsKey(clz)){
            SootMethod hashCodeMtd = getHashCodeMtd(clz);
            recordFixedEqMethod(mtd, hashCodeMtd);
        }

        return FragmentsContainer.singleHashFixedClass.contains(clz);
    }

    /**
     * 提取方法返回值相关的fields和调用了 hashCode 方法的fields
     * @param descriptor
     * @return
     */
    public static HashSet<SourceNode> extractFieldsViaHashCode(MethodDescriptor descriptor){
        boolean addFlag = true;
        HashSet<SourceNode> ret = new HashSet<>();
        for (Taint taint: descriptor.retTainted){
            for (SourceNode sourceNode: descriptor.sourcesTaintGraph.matchTaintedSources(taint)){
                if (!sourceNode.isField())
                    continue;
                if (!Utils.isBasicType(sourceNode.getType())
                        | sourceNode.getType().toString().contains("[]")) {
                    ret.add(sourceNode);
                }
            }
        }

        if (!descriptor.sootMethod.hasActiveBody())
            return ret;

        for (Unit unit: descriptor.sootMethod.retrieveActiveBody().getUnits()){
            Stmt stmt = (Stmt) unit;
            if (!stmt.containsInvokeExpr())
                continue;
            SootMethod invokedMtd = ((Stmt) unit).getInvokeExpr().getMethod();
            if (invokedMtd.getSubSignature().equals("int hashCode()")){
                ValueBox thisValueBox = Parameter.getThisValueBox(stmt);
                if (thisValueBox != null){
                    for (SourceNode sourceNode: RuleUtils.getTaintedFieldSources(thisValueBox.getValue(), descriptor)) {
                        if (!sourceNode.isField())
                            continue;
                        if (FieldUtil.isTransientType(sourceNode.field.getLast())){
                            // 应该改成sourceNode.classOf
                            if (checkTransientControllableSimply(descriptor.getCurrentClass(), sourceNode.field.getLast(), descriptor)){
                                return null;
                            }
                        }
                        if (sourceNode.classOfField.equals(descriptor.getCurrentClass()))
                            ret.add(sourceNode);
                    }
                }
            }
        }
        return ret;
    }
}
