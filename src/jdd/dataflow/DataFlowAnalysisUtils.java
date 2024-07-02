package dataflow;

import PointToAnalyze.pointer.Pointer;
import config.RegularConfig;
import soot.jimple.IfStmt;
import tranModel.Rules.RuleUtils;
import tranModel.Taint.Taint;
import tranModel.TransformableNode;
import cfg.CFG;
import container.BasicDataContainer;
import container.FieldsContainer;
import container.FragmentsContainer;
import dataflow.node.SourceNode;
import dataflow.node.MethodDescriptor;
import dataflow.node.UndeterminedFieldNode;
import dataflow.node.paramResult.MethodResult;
import dataflow.node.paramResult.TaintAndLinger;
import gadgets.collection.AnalyzeUtils;
import gadgets.collection.node.ClassNode;
import gadgets.collection.node.GadgetInfoRecord;
import gadgets.collection.node.GadgetNode;
import gadgets.unit.Fragment;
import gadgets.unit.InterimFragment;
import util.Pair;
import lombok.extern.slf4j.Slf4j;
import markers.Stage;
import soot.*;
import soot.jimple.AssignStmt;
import soot.jimple.InvokeExpr;
import soot.jimple.Stmt;
import util.ClassRelationshipUtils;
import util.StaticAnalyzeUtils.ClassUtils;
import util.StaticAnalyzeUtils.FieldUtil;
import util.StaticAnalyzeUtils.InvokeStmtUtil;
import util.StaticAnalyzeUtils.Parameter;
import util.Utils;

import javax.xml.transform.Source;
import java.io.IOException;
import java.util.*;

import static gadgets.collection.AnalyzeUtils.*;
import static tranModel.Rules.RuleUtils.*;
import static util.ClassRelationshipUtils.isDynamicMethod;

@Slf4j
public class DataFlowAnalysisUtils {

    public static MethodDescriptor flowInvokedMethod(MethodDescriptor callerDescriptor, SootMethod callee,
                                         HashMap<Integer, Pointer> inputCallFrame,
                                         LinkedList<SootMethod> callStack, TransformableNode tfNode){
        if (!DataFlowAnalysisUtils.continueFollowInvokeMtd(callStack,callee, tfNode))  return null;
        InvokeExpr currentInvokeExpr = tfNode.getUnitInvokeExpr();
        // 调用下个方法时，传入必要的信息
        MethodDescriptor calleeDescriptor = DataFlowAnalysisUtils.afferentInfosToInvokedMtd(callerDescriptor,currentInvokeExpr,
                callee,inputCallFrame,tfNode);

        callStack.add(callee);
        return calleeDescriptor;
    }

    public static void outInvokedMethod(MethodDescriptor calleeDescriptor,
                                        MethodDescriptor callerDescriptor,
                                        TransformableNode tfNode,
                                        LinkedList<SootMethod> callStack){
        callStack.remove(calleeDescriptor.sootMethod);
        DataFlowAnalysisUtils.updateAfterInvoke(callerDescriptor, calleeDescriptor, tfNode);
    }

    public static void outInvokedMethod(MethodDescriptor calleeDescriptor,
                                        MethodDescriptor callerDescriptor,
                                        TransformableNode tfNode,
                                        ClassNode conClassNode,
                                        GadgetInfoRecord gadgetInfoRecord,
                                        LinkedList<SootMethod> callStack){
        callStack.remove(calleeDescriptor.sootMethod);
        DataFlowAnalysisUtils.updateAfterInvoke(callerDescriptor, calleeDescriptor, conClassNode, gadgetInfoRecord, tfNode);
    }


    public static MethodDescriptor getMethodDescriptor(SootMethod sootMethod){
        // 如果不是具体的方法，比如抽象方法那就不作处理
        if (!sootMethod.isConcrete())   return null;

        MethodDescriptor descriptor = BasicDataContainer.getOrCreateDescriptor(sootMethod);

        descriptor.flushStates();
        // 根据专家经验判断是否需要进行检测
        if (descriptor.needDetect()) {
            if(descriptor.cfg == null){
                CFG cfg = new CFG(sootMethod, true);
                cfg.buildCFG();
                descriptor.cfg = cfg;
            }
            descriptor.paramIdMapLocalValue = Parameter.getParametersLocalValues(descriptor.cfg);
            return descriptor;
        }
        return null;
    }

    public static SootMethod getMethodDescriptor(MethodDescriptor descriptor){
        if (!descriptor.sootMethod.isConcrete())   return null;
        descriptor.flushStates();
        // 根据专家经验判断是否需要进行检测
        if (descriptor.needDetect()) {
            if(descriptor.cfg == null){
                CFG cfg = new CFG(descriptor.sootMethod, true);
                cfg.buildCFG();
                descriptor.cfg = cfg;
            }
            descriptor.paramIdMapLocalValue = Parameter.getParametersLocalValues(descriptor.cfg);
            return descriptor.sootMethod;
        }
        return null;
    }

    /**
     * 初始化方法的参数和对应的local values之间的关系
     * @param descriptor
     */
    public static void initLocalValueFormMethod(MethodDescriptor descriptor){
        if(descriptor.cfg == null){
            CFG cfg = new CFG(descriptor.sootMethod, true);
            cfg.buildCFG();
            descriptor.cfg = cfg;
        }
        descriptor.paramIdMapLocalValue = Parameter.getParametersLocalValues(descriptor.cfg);
    }

    public static void updateInterInfos(MethodDescriptor descriptor){
        // 将当前方法的局部变量的指向信息存储于pointTable中以备后续分析
//        descriptor.paramIdMapLocalValue = Parameter.getParametersLocalValues(descriptor.cfg);
        for(Integer ind : descriptor.paramIdMapLocalValue.keySet()){
            if (descriptor.paramValInfo.containsKey(ind)) {
                Value localVal = descriptor.paramIdMapLocalValue.get(ind);
                Pointer pointer = descriptor.paramValInfo.get(ind);
                if (pointer == null)
                    continue;
                descriptor.pointTable.setPointer(localVal, pointer);
            }
        }


        for(Integer ind : descriptor.paramIdMapLocalValue.keySet()){
            if(!descriptor.inputParamMapTaints.containsKey(ind)){

                if (!descriptor.sootMethod.getSubSignature().equals("java.lang.Object run()")
                        | !descriptor.sootMethod.getDeclaringClass().isInnerClass()
                        | ind != -1)
                    continue;
                for (int indTmp: descriptor.inputParamMapTaints.keySet()){
                    for (Taint tmpTaint : descriptor.inputParamMapTaints.get(indTmp)){
                        if (tmpTaint.object.getType().toString().equals(descriptor.sootMethod.getDeclaringClass().getName())){
                            // 添加this污染
                            if (tmpTaint.accessPath.isEmpty()){
                                LinkedList<SootField> accessPath = new LinkedList<>(tmpTaint.accessPath);
                                Taint taintInLocal = descriptor.getOrCreateTaint(descriptor.paramIdMapLocalValue.get(-1), accessPath);
                                Taint.addTaint(taintInLocal, descriptor.taints);
                            }
                        }
                    }
                }
                continue;
            }
            Value localVal = descriptor.paramIdMapLocalValue.get(ind);
            // inputParamMapTaints是在获取entry的过程中处理了的形参污点
            for(Taint taint : descriptor.inputParamMapTaints.get(ind)){
                LinkedList<SootField> accessPath = new LinkedList<>(taint.accessPath);
                Taint taintInLocal = descriptor.getOrCreateTaint(localVal, accessPath);
                Taint.addTaint(taintInLocal, descriptor.taints);
            }

            // 更新入参对应的fields信息
            if (BasicDataContainer.infosCollect){
                if (descriptor.fieldsParamIndexRecord.containsKey(ind)){
                    for (SourceNode sourceNode : descriptor.fieldsParamIndexRecord.get(ind)){
                        descriptor.sourcesTaintGraph.addTaintedSourceNode(sourceNode,descriptor.paramIdMapLocalValue.get(ind));
                    }
                }
            }
        }
    }

    /**
     * 在分析完方法的所有指令后, 更新信息: 存储分析结果, 减少上下文敏感的分析负担 (减少重复分析)
     * @param descriptor
     */
    public static void updateAfterAnalysisMtd(MethodDescriptor descriptor) {
        // 生成 Interim Fragment
        if (BasicDataContainer.stage.equals(Stage.FRAGMENT_SEARCHING))
            FragmentsContainer.generateInterimFragment(descriptor);

        for(int ind : descriptor.paramIdMapLocalValue.keySet()){
            Value localVal = descriptor.paramIdMapLocalValue.get(ind);
            List<Taint> newTaints = descriptor.getAllNewTaintsAboutThisValue(localVal);
            if (!newTaints.isEmpty()){
                descriptor.paramBeTainted.put(ind, newTaints);
            }
        }

        int inputTaint = 0;
        for (Integer ind: descriptor.inputParamMapTaints.keySet()){
            if (!descriptor.inputParamMapTaints.get(ind).isEmpty())
                inputTaint |= (1 << (ind + 1));
        }

        // fields污染关系和参数之间的关联性 计数
        for (Integer ind = descriptor.inputParamMapTaints.size();
             ind < descriptor.inputParamMapTaints.size() + descriptor.fieldsParamIndexRecord.size(); ind++){
            if (descriptor.fieldsParamIndexRecord.containsKey(ind - descriptor.inputParamMapTaints.size()))
                if (!descriptor.fieldsParamIndexRecord.get(ind - descriptor.inputParamMapTaints.size()).isEmpty())
                    inputTaint |= (1 <<(ind+1));
        }

        TaintAndLinger new_TaintAndLinger = new TaintAndLinger(inputTaint);

        if (BasicDataContainer.infosCollect)
            descriptor.memorize.put(new_TaintAndLinger, new MethodResult(descriptor.paramBeTainted, descriptor.retTainted,
                    descriptor.pointTable, descriptor.sourcesTaintGraph));
        else
            descriptor.memorize.put(new_TaintAndLinger, new MethodResult(descriptor.paramBeTainted,descriptor.retTainted));
    }


    public static void updateAfterInvoke(MethodDescriptor descriptor,
                                         MethodDescriptor invokedDescriptor,
                                         TransformableNode tfNode) {
        if (!tfNode.containsInvoke())   return;
        InvokeExpr invokeExpr = tfNode.getUnitInvokeExpr();

        for(int ind : invokedDescriptor.paramBeTainted.keySet()){
            if(ind == -1){  // TODO: 添加针对 <init> 的处理
                ValueBox thisValueBox = Parameter.getThisValueBox(tfNode.node);
                if(thisValueBox != null){
                    for(Taint taint : invokedDescriptor.paramBeTainted.get(ind)){
                        filterAndAddTaints(descriptor, invokedDescriptor,
                                descriptor.getOrCreateTaint(RuleUtils.getBaseValue(thisValueBox.getValue()), taint.accessPath),
                                taint);
                    }
                }
            } else {
                ValueBox argBox = invokeExpr.getArgBox(ind);
                for(Taint taint : invokedDescriptor.paramBeTainted.get(ind)){
                    filterAndAddTaints(descriptor, invokedDescriptor,
                            descriptor.getOrCreateTaint(RuleUtils.getBaseValue(argBox.getValue()), taint.accessPath),
                            taint);
                }
            }
        }

        if(!invokedDescriptor.retTainted.isEmpty()){
            ValueBox retValueBox = Parameter.getReturnedValueBox(tfNode.node);

            if (retValueBox != null) {
                for (Taint taint : invokedDescriptor.retTainted) {
                    filterAndAddTaints(descriptor, invokedDescriptor,
                            descriptor.getOrCreateTaint(RuleUtils.getBaseValue(retValueBox.getValue()), taint.accessPath),
                            taint);
                }
            }
        }
    }

    public static void updateAfterInvoke(MethodDescriptor descriptor,
                                         MethodDescriptor invokedDescriptor,
                                         ClassNode conClassNode,
                                         GadgetInfoRecord gadgetInfoRecord,
                                         TransformableNode tfNode) {
        if (!tfNode.containsInvoke())   return;
        InvokeExpr invokeExpr = tfNode.getUnitInvokeExpr();

        // 1. conClassNode清理检查
        if (BasicDataContainer.stage.equals(Stage.IOCD_GENERATING)
                | BasicDataContainer.stage.equals(Stage.IOCD_SUPPLEMENT_INFER)){
            sanitizerOfConClassNode(conClassNode, tfNode, invokedDescriptor);
        }

        // 方法调用分析结束
        // 从 call frame 中更新本地变量
        // 先暂存，最终再更新到本地，因为这个循环可能执行多次！（cha无法确定调用的方法具体是哪个）
        // taint传播
        for(int ind : invokedDescriptor.paramBeTainted.keySet()){
            if(ind == -1){  // TODO: 添加针对 <init> 的处理
                ValueBox thisValueBox = Parameter.getThisValueBox(tfNode.node);
                if(thisValueBox != null){
                    for(Taint taint : invokedDescriptor.paramBeTainted.get(ind)){
                        filterAndAddTaints(descriptor, invokedDescriptor,
                                descriptor.getOrCreateTaint(RuleUtils.getBaseValue(thisValueBox.getValue()), taint.accessPath),
                                taint, gadgetInfoRecord);
                    }
                }
            } else {
                ValueBox argBox = invokeExpr.getArgBox(ind);
                for(Taint taint : invokedDescriptor.paramBeTainted.get(ind)){
                    filterAndAddTaints(descriptor, invokedDescriptor,
                            descriptor.getOrCreateTaint(RuleUtils.getBaseValue(argBox.getValue()), taint.accessPath),
                            taint, gadgetInfoRecord);
                }
            }
        }

        if(!invokedDescriptor.retTainted.isEmpty()){
            ValueBox retValueBox = Parameter.getReturnedValueBox(tfNode.node);

            if (retValueBox != null) {
                for (Taint taint : invokedDescriptor.retTainted) {
                    filterAndAddTaints(descriptor, invokedDescriptor,
                            descriptor.getOrCreateTaint(RuleUtils.getBaseValue(retValueBox.getValue()), taint.accessPath),
                            taint, gadgetInfoRecord);
                }
            } // TODO: 对于返回值的污染对象, E.g. Entry.getKey(), 不在主干ClassNodeChains上的, 扩展source的fields记录
        }
    }

    /**
     * 对要添加的污点进行筛选, 对通过筛选的污点记录以下信息: Taint, 指针信息, 污染源信息
     * 筛选准则:
     * (1) 污染源在检测的class chain范围内
     * @param descriptor
     * @param invokedDescriptor
     */

    public static void filterAndAddTaints(MethodDescriptor descriptor,
                                          MethodDescriptor invokedDescriptor,
                                          Taint taintTo, Taint taintFrom){
        // 1. 污点信息添加
        descriptor.taints.add(taintTo);
        descriptor.newtaints.add(taintTo);
        // 2. 指针分析
        descriptor.pointTable.setPointer(taintTo, invokedDescriptor.pointTable.getPointer(taintFrom));
        // 3. 污点来源记录
        if (BasicDataContainer.infosCollect){
            for (SourceNode sourceNode: invokedDescriptor.sourcesTaintGraph.getSourceNodesByTaint(taintFrom)){
                descriptor.sourcesTaintGraph.addTaintedSourceNode(sourceNode, taintTo.object);
            }
        }
    }

    /**
     * 用在 IOCD 构建的信息推断阶段, 对污点进行筛选
     * @param descriptor
     * @param invokedDescriptor
     * @param taintTo
     * @param taintFrom
     * @param gadgetInfoRecord
     */
    public static void filterAndAddTaints(MethodDescriptor descriptor,
                                          MethodDescriptor invokedDescriptor,
                                          Taint taintTo, Taint taintFrom,
                                          GadgetInfoRecord gadgetInfoRecord){
        HashSet<SourceNode> validSourcesMap = new HashSet<>();
        if (BasicDataContainer.stage.equals(Stage.IOCD_GENERATING)
                | BasicDataContainer.stage.equals(Stage.IOCD_SUPPLEMENT_INFER)){
            validSourcesMap = sanitizerOfTaintAndSource(gadgetInfoRecord, invokedDescriptor, taintFrom);
        }

        descriptor.taints.add(taintTo);
        descriptor.newtaints.add(taintTo);
        descriptor.pointTable.setPointer(taintTo, invokedDescriptor.pointTable.getPointer(taintFrom));
         if (BasicDataContainer.infosCollect){
            for (SourceNode sourceNode: validSourcesMap){
                descriptor.sourcesTaintGraph.addTaintedSourceNode(sourceNode, taintTo.object);
                // 检查是否有与 taint spread 规则矛盾的污点变量, 如果有则修正
                for (SourceNode recordedSourceNode: descriptor.sourcesTaintGraph.matchTaintedSources(taintTo)){
                    if (recordedSourceNode.equals(sourceNode))
                        continue;
                    if (recordedSourceNode.isField()
                            && sourceNode.isField()
                            && (gadgetInfoRecord.classFieldsGraph.containsKey(recordedSourceNode.classOfField)
                                && gadgetInfoRecord.classFieldsGraph.containsKey(sourceNode.classOfField))
                            && !recordedSourceNode.classOfField.equals(sourceNode.classOfField)){
                        descriptor.sourcesTaintGraph.sources2TaintedValues.get(recordedSourceNode).remove(taintTo.object);
                    }
                }
            }
        }
    }


    public static MethodDescriptor afferentInfosToInvokedMtd(MethodDescriptor descriptor, InvokeExpr currentInvokeExpr,
                                                       SootMethod invokedMethod, HashMap<Integer, Pointer> inputCallFrame,
                                                       TransformableNode tfNode) {
        MethodDescriptor invokedDescriptor = BasicDataContainer.getOrCreateDescriptor(invokedMethod);
        // Step1: 指针信息传递
        invokedDescriptor.paramValInfo = inputCallFrame;
        // 在一次分析内entryMethod相同, 直接继承
        invokedDescriptor.sourcesTaintGraph.entryMethod = descriptor.sourcesTaintGraph.entryMethod;
//        if (BasicDataContainer.stage.equals(Stage.FRAGMENT_SEARCHING_SINGLE) && BasicDataContainer.openDynamicProxyDetect){
//            // 解析到调用到下一个方法的条件约束信息
//            parseInvokeConditions(tfNode, descriptor, invokedDescriptor);
//        }
        // Step2: 污点传播记录
        ValueBox thisValueBox = Parameter.getThisValueBox(tfNode.node);
        List<Taint> thisTaintRecords = new LinkedList<>();
        if (thisValueBox == null & !tfNode.needInputTaintedParamFlush){
            thisTaintRecords = invokedDescriptor.inputParamMapTaints.get(-1);
        }
        // 已存储信息刷新
        invokedDescriptor.inputParamMapTaints = new HashMap<>();
        invokedDescriptor.fieldsParamIndexRecord = new HashMap<>();
        if (tfNode.needInputTaintedParamFlush)
            invokedDescriptor.sourcesTaintGraph.sourcesInfluenceRecord = descriptor.sourcesTaintGraph.sourcesInfluenceRecord;

        if (!tfNode.needInputTaintedParamFlush & thisTaintRecords != null){
            invokedDescriptor.inputParamMapTaints.put(-1,thisTaintRecords);
            if (BasicDataContainer.infosCollect) {
                HashSet<SourceNode> sourceNodes = new HashSet<>();
                for (Taint taint: thisTaintRecords){
                    sourceNodes.addAll(descriptor.sourcesTaintGraph.getSourceNodesByTaint(taint));
                }
                invokedDescriptor.fieldsParamIndexRecord.put(-1, sourceNodes);
            }
        }else if (thisValueBox != null){
            invokedDescriptor.inputParamMapTaints.put(-1, descriptor.getAllTaintsAboutThisValue(thisValueBox.getValue()));
            if (BasicDataContainer.infosCollect){
                invokedDescriptor.fieldsParamIndexRecord.put(-1, descriptor.sourcesTaintGraph.matchTaintedSources(thisValueBox.getValue()));
            }
        }

        for (int i = 0; i < currentInvokeExpr.getArgCount(); i++){
            Value argValue = currentInvokeExpr.getArg(i);
            // TODO: 细化, 考虑fields敏感的匹配? field敏感一般在污点传递过程中通过a=field.field产生, 因此此处暂时不处理
            invokedDescriptor.inputParamMapTaints.put(i, descriptor.getAllTaintsAboutThisValue(argValue));

            if (BasicDataContainer.infosCollect){
                HashSet<SourceNode> sourceNodes = descriptor.sourcesTaintGraph.matchTaintedSources(argValue);
                invokedDescriptor.fieldsParamIndexRecord.put(i, sourceNodes);
            }
        }

        if (thisValueBox != null) {
            initLocalValueFormMethod(invokedDescriptor);
            Value invokedThisValue = invokedDescriptor.paramIdMapLocalValue.get(-1);
            if (invokedThisValue != null) {
                if (descriptor.tempGeneratedObjs.contains(thisValueBox.getValue())){
                    invokedDescriptor.tempGeneratedObjs.add(invokedThisValue);
                }
            }
        }

        return invokedDescriptor;
    }

    /**
     * 判断是否要继续检查该invokedMethod
     * @param callStack
     * @param invokedMethod
     * @return
     */
    public static boolean continueFollowInvokeMtd(LinkedList<SootMethod> callStack,
                                            SootMethod invokedMethod,
                                                  TransformableNode tfNode) {
        if (BasicDataContainer.inBlackList(invokedMethod))  return false;
        if (callStack.contains(invokedMethod)
                & !(BasicDataContainer.stage.equals(Stage.IOCD_GENERATING)
                    & invokedMethod.getSubSignature().equals("boolean equals(java.lang.Object)"))
                | (!BasicDataContainer.stage.equals(Stage.IOCD_GENERATING) & AnalyzeUtils.getMtdNum(callStack, "boolean equals(java.lang.Object)") >= 2)
                | (BasicDataContainer.stage.equals(Stage.IOCD_GENERATING) & AnalyzeUtils.getMtdNum(callStack, "boolean equals(java.lang.Object)") > 2)
        )
            return false;
        ValueBox thisValueBox = Parameter.getThisValueBox(tfNode.node); // TODO: collectFields 可能存放 null
        if (BasicDataContainer.stage.equals(Stage.FRAGMENT_SEARCHING)
                | BasicDataContainer.stage.equals(Stage.IOCD_GENERATING)
                | BasicDataContainer.stage.equals(Stage.IOCD_SUPPLEMENT_INFER))
            if (AnalyzeUtils.isTmpGeneratedObj(thisValueBox, BasicDataContainer.getOrCreateDescriptor(callStack.getLast()))
                    | callStack.getFirst().getSubSignature().equals("void writeObject(java.io.ObjectOutputStream)"))
                return true;
//        if (serializableIntercept(invokedMethod, tfNode, callStack)) return false;
        return true;
    }

    /**
     * 进行 Serializable 继承情况检测
     * @param invokedMethod
     * @param tfNode: 当前语句
     * @return RuleUtils.checkTransientControllableSimply(tfNode.context.sootClass, getMethodDescriptor(tfNode.method).getField(tfNode.node,thisValueBox))
     */
    public static boolean serializableIntercept(MethodDescriptor descriptor,
                                                SootMethod invokedMethod,
                                                TransformableNode tfNode,
                                                LinkedList<SootMethod> callStack) {
        if (!serializableIntercept(descriptor, invokedMethod, tfNode))
            return false;

        if (callStack.size() <= BasicDataContainer.serializableInterceptLen/*&& Utils.inList(callStack, BasicDataContainer.tmpOffSerializableMtds)*/
                && !FragmentsContainer.protocolCheckRule.candidateClassSet.contains(callStack.getLast().getDeclaringClass()))
//                && !ClassRelationshipUtils.isSubClassOf(callStack.getFirst().getDeclaringClass(),BasicDataContainer.commonClassMap.get("Serializable")))
            return false;

        return true;
    }

    public static boolean serializableIntercept(MethodDescriptor descriptor,
                                                SootMethod invokedMethod,
                                                TransformableNode tfNode){
        if (!BasicDataContainer.needSerializable || invokedMethod.isStatic())
            return false;

        SootClass invokedMtdClass = invokedMethod.getDeclaringClass();
//        if (ClassRelationshipUtils.isSubClassOf(invokedMtdClass,BasicDataContainer.commonClassMap.get("Serializable")))
        if (FragmentsContainer.protocolCheckRule.candidateClassSet.contains(invokedMtdClass))
            return false;

        // Fix: 补充检查逻辑--如果在对象初始化构建过程中能主动创建的对象，则无需进行serializableIntercept检查
        if (!RuleUtils.needSlzCheck(descriptor, Parameter.getThisValueBox(tfNode.node)))
            return false;
        SootField sootField = descriptor.getField(tfNode.node, Parameter.getThisValueBox(tfNode.node));
        if (RuleUtils.checkTransientControllableSimply(tfNode.context.sootClass, sootField, descriptor)) {
//            BasicDataContainer.tmpOffSerializableMtds.add(descriptor.sootMethod);
            return false;
        }
        return true;
    }

    public static HashSet<SootMethod> generateFragmentsOrInvokedMethods(MethodDescriptor descriptor,
                                                                        TransformableNode tfNode,
                                                                 HashMap<Integer, Pointer> inputCallFrame,
                                                                 LinkedList<SootMethod> callStack){
        InvokeExpr invokeExpr = tfNode.getUnitInvokeExpr();
        String invokedMethodSubSig = invokeExpr.getMethod().getSubSignature();
        SootClass expectClass = getInvokedMethodClassByPointerAnalysis(inputCallFrame);
        HashSet<SootMethod> invokedMethods = new HashSet<>();

        if (expectClass != null) {
            if (expectClass.isConcrete() & !expectClass.getName().equals("java.lang.Object")) {
                HashSet<SootMethod> possibleMethods = tfNode.invokeMethods(descriptor);
                invokedMethods = InvokeStmtUtil.findExactMethodFromCHAMethods(possibleMethods, expectClass, tfNode);
                if (invokedMethods.isEmpty() && tfNode.getUnitInvokeExpr().getMethod() != null){
                    invokedMethods.add(tfNode.getUnitInvokeExpr().getMethod());
                }
                if (possibleMethods.size() > 1 && !RuleUtils.isInvalidFragmentEnd(invokeExpr.getMethod(), false)){ // 检查是否存在sub->super方法的情况
                    // candidate sub class -> super mtd -> sub.method
                    FragmentsContainer.searchMtdForSubClass(tfNode.method ,possibleMethods);
                }
            } else {
                SootMethod expectMethod = null;
                invokedMethods = getInvokedMethods(inputCallFrame, tfNode, descriptor);
                for (SootClass superClazz: ClassUtils.getAllSupers(expectClass)){
                    SootMethod tmpInvokedMethod = superClazz.getMethodUnsafe(invokedMethodSubSig);
                    if (tmpInvokedMethod != null ){
                        expectMethod = tmpInvokedMethod;
                        break;
                    }
                }

                if (!invokedMethods.isEmpty()){
                    if (!RuleUtils.generateFragmentOrNot(invokedMethods, invokedMethodSubSig))
                        return invokedMethods;
                    else {
                        Pointer pointer = inputCallFrame.get(-1);
                        if (pointer.getExtraTypes().isEmpty()) { // 判断一下, 节省存储空间
                            if (expectMethod != null)
                                FragmentsContainer.generateFragments(descriptor, callStack, expectMethod, tfNode, null, false);
                        }
                        else
                            FragmentsContainer.generateFragments(descriptor, callStack, expectMethod, tfNode, invokedMethods,false);
                        invokedMethods.clear();
                    }
                }

            }
        }else { // 如果没有指针信息, 则跟进tfNode进行判断
            SootMethod invokedMethod = invokeExpr.getMethod();
            invokedMethods = tfNode.invokeMethods(descriptor);
            if (!isDynamicMethod(invokedMethod)
                    || invokedMethods.size() <= BasicDataContainer.stackLenLimitNum){

            }else {
                FragmentsContainer.generateFragments(descriptor, callStack, invokedMethod, tfNode, null,false);
                invokedMethods.clear();
            }
        }

        // TODO: 在此处进行serializable的检查更为合适 (在generate fragments之前)
        if (BasicDataContainer.needSerializable) {
            ValueBox thisValueBox = Parameter.getThisValueBox(tfNode.node);
            if (thisValueBox != null
                    && !BasicDataContainer.getOrCreateDescriptor(tfNode.method).tempGeneratedObjs.contains(thisValueBox.getValue())) {
                HashSet<SootMethod> toDelete = new HashSet<>();
                for (SootMethod invokedMethod : invokedMethods) {
                    if (serializableIntercept(descriptor, invokedMethod, tfNode, callStack))
                        toDelete.add(invokedMethod);
                }

                invokedMethods.removeAll(toDelete);
            }
        }
        filterInvokedMethods(invokedMethods, tfNode.getUnitInvokeExpr().getMethod()); // 如果当前方法不是Object, 则不必取出Object.init
        if (invokedMethods.size() > BasicDataContainer.stackLenLimitNum)
            invokedMethods.clear();

        return invokedMethods;
    }

    public static HashSet<SootMethod> getInvokedMethods(TransformableNode tfNode,
                                                        HashMap<Integer, Pointer> inputCallFrame,
                                                        LinkedList<SootMethod> callStack,
                                                        GadgetInfoRecord gadgetInfoRecord){
        HashSet<SootMethod> ret = new HashSet<>();
        SootMethod invokedMethod = tfNode.getUnitInvokeExpr().getMethod();
        SootMethod next = getNextMethod(callStack, gadgetInfoRecord.gadgets);

        boolean blackFlag = BasicDataContainer.blackList.contains(tfNode.getUnitInvokeExpr().getMethodRef().getSignature());

        if (next != null) {
            boolean isSub2SuperFlag = false;
            if (next.getSubSignature().equals(invokedMethod.getSubSignature())) {
                MethodDescriptor descriptor = BasicDataContainer.getOrCreateDescriptor(callStack.getLast());
                if (ClassRelationshipUtils.isAbsSuperCallee(descriptor.sootMethod, invokedMethod, next)) {
                    Pointer pointer = new Pointer(next.getDeclaringClass().getType());
                    descriptor.paramValInfo.put(-1, pointer);
                    descriptor.pointTable.setPointer(descriptor.paramIdMapLocalValue.get(-1), pointer);
                    isSub2SuperFlag = true;
                    if (inputCallFrame.containsKey(-1)) inputCallFrame.replace(-1, pointer);
                    else inputCallFrame.put(-1, pointer);
                }
                if (!isDynamicMethod(invokedMethod) && !isSub2SuperFlag)
                    ret.add(invokedMethod);
                else {
                    HashSet<SootMethod> invokedPointerMtd = getInvokedMethods(inputCallFrame, tfNode, descriptor);
                    if (!invokedPointerMtd.contains(next)) {
                        ret.addAll(invokedPointerMtd);
                    }else
                        ret.add(next);
                }
            }
        }
        if (ret.isEmpty()) {
            SootClass expectedClass = getInvokedMethodClassByPointerAnalysis(inputCallFrame);
            boolean flag = true;
            if (expectedClass != null){
                if (expectedClass.isConcrete() || expectedClass.getName().equals("java.lang.Object"))
                    flag = false;
            }
            if (isDynamicMethod(invokedMethod) & flag){
                MethodDescriptor descriptor = BasicDataContainer.getOrCreateDescriptor(callStack.getLast());
                for (InterimFragment interimFragment:
                        RuleUtils.markConClassNodesBasedOnInterimFragments(gadgetInfoRecord, invokedMethod, tfNode, descriptor)){
                    ret.add(interimFragment.head);
                }
            }else {
                ret = getInvokedMethods(inputCallFrame, tfNode, BasicDataContainer.getOrCreateDescriptor(tfNode.method));
            }
        }

        // 如果当前方法不是Object, 则不必取出Object.init
        filterInvokedMethods(ret, tfNode.getUnitInvokeExpr().getMethod());
        if (ret.size() > BasicDataContainer.methodLimitNum / 2) {
            ret.clear();
        }

        if (next == null && blackFlag) // 黑名单中的抽象方法，如果不在gadget chains系列中不继续跟进，防止扰乱五点传播规则，E.g. 生成错误的污染关系
            ret.clear();

        return ret;
    }

    /**
     * 根据指针分析获取调用方法所属的实际类
     * @param inputCallFrame
     * @return
     */
    public static SootClass getInvokedMethodClassByPointerAnalysis(HashMap<Integer, Pointer> inputCallFrame){
        // Spark 尝试查找具体的实现(基于指针分析)
        if (inputCallFrame.containsKey(-1)){
            Pointer pointer = inputCallFrame.get(-1);
            Type type = pointer.getType();
            return Utils.toSootClass(type);
        }
        return null;
    }

    /**
     * 根据指令和指针信息获取可能被调用的方法
     * 利用 Pointer.extraTypes 添加多类型筛选分析, E.g. 强制转换提示了多种类型约束
     * @param tfNode
     * @return
     */
    public static HashSet<SootMethod> getInvokedMethods(TransformableNode tfNode, MethodDescriptor descriptor){
        SootMethod invokedMethodViaNode = null;

        HashMap<Integer, Pointer> inputCallFrame = getMethodBaseParamInfo(tfNode, descriptor);
        HashSet<SootMethod> invokedMethodViaPointer = getInvokedMethods(inputCallFrame, tfNode, descriptor);

        HashSet<SootMethod> toDelete = new HashSet<>(); // 拒绝自己调用自己, 就算存在也会在后续的检查中被删除

        for (SootMethod tmpInvokedMethod: invokedMethodViaPointer){
            if (tmpInvokedMethod.equals(descriptor.sootMethod)) {
                toDelete.add(tmpInvokedMethod);
                invokedMethodViaNode = tfNode.getUnitInvokeExpr().getMethod(); // 这种情况下直接通过从Unit中获取被调方法
            }
        }
        invokedMethodViaPointer.removeAll(toDelete);
        if (invokedMethodViaNode != null)
            invokedMethodViaPointer.add(invokedMethodViaNode);
        return invokedMethodViaPointer;
    }

    public static HashSet<SootMethod> getInvokedMethods(HashMap<Integer, Pointer> inputCallFrame,
                                                        TransformableNode tfNode, MethodDescriptor descriptor){
        Pointer pointer = inputCallFrame.get(-1);

        return getInvokedMethods(pointer, tfNode, descriptor);
    }

    public static HashSet<SootMethod> getInvokedMethods(Pointer pointer, TransformableNode tfNode, MethodDescriptor descriptor){
        HashSet<SootMethod> methods = tfNode.invokeMethods(descriptor);
        if (methods.isEmpty()){
            SootMethod addSM = Scene.v().getMethod(tfNode.getUnitInvokeExpr().getMethod().getSignature());
            if (addSM.isConcrete())
                methods.add(addSM);
            else {
                methods.addAll(ClassRelationshipUtils.getAllSubMethods(addSM));
            }
        }

        if (pointer != null){
            if (pointer.getExtraTypes().isEmpty()) {
                SootClass expectClass = Utils.toSootClass(pointer.getType());
                if (!expectClass.getName().equals("java.lang.Object"))
                    return InvokeStmtUtil.findExactMethodFromCHAMethods(methods, expectClass, tfNode);
            }else {
                HashSet<SootClass> typeConstraint = new HashSet<>();
                typeConstraint.add(Utils.toSootClass(pointer.getType()));
                for (Type extractType : pointer.getExtraTypes()) {
                    typeConstraint.add(Utils.toSootClass(extractType));
                }

                methods = InvokeStmtUtil.findExactMethodFromCHAMethods(methods, typeConstraint, tfNode);
            }
        }
        return methods;
    }

    /**
     * 给定一个包含了方法调用的Unit, 进行污点分析判断是否需要继续分析
     * (1) 非静态方法, this必须污染
     * (2) 静态方法, 入参至少有一个被污染
     * @param tfNode
     * @param descriptor
     * @return
     */
    public static boolean continueCheck(TransformableNode tfNode, MethodDescriptor descriptor) {
        ValueBox thisBox = Parameter.getThisValueBox(tfNode.node);
        InvokeExpr currentInvokeExpr = tfNode.getUnitInvokeExpr();
        SootClass sootClass = currentInvokeExpr.getMethod().getDeclaringClass();

        if (sootClass.hasOuterClass() & Utils.endWithNumber(sootClass.getName()))
            sootClass = sootClass.getOuterClass();
        //  TODO: 补上黑名单的, 在加入完污点模型后 [注意, 对于抽象方法, 考虑可能作为source, 因此此处不能直接拦截]
        if (Utils.isBasicType(sootClass.getName()))
            return false;

        SootMethod invokedMethod = currentInvokeExpr.getMethod();
        if (BasicDataContainer.blackList.contains(currentInvokeExpr.getMethodRef().getSignature())
                && invokedMethod.isConcrete())
            return false;
        // 已经检测到 sink method 后就不再跟进, 避免出现不必要的sink方法调用部分不同的 Sink Fragments
        if (FragmentsContainer.isSinkMethod(invokedMethod))
            return false;
        if (thisBox != null && Utils.isTaintedInnerClzMethodCall(descriptor, thisBox.getValue(), currentInvokeExpr)){
            return true;
        }
        // 1. 如果是非static方法, 则this必须要被污染
        // 如果this 被污染，则一定继续跟进
        if(RuleUtils.satisfyTaintCheck(thisBox, descriptor, tfNode, currentInvokeExpr)){
            if (!(BasicDataContainer.stage.equals(Stage.OFF) | BasicDataContainer.stage.equals(Stage.IOCD_SUPPLEMENT_INFER))
                    & !thisBox.getValue().equals(descriptor.paramIdMapLocalValue.get(-1))) {
//                SootField sootField = descriptor.getField(tfNode.node, thisBox);
                SourceNode sourceNodeOfField = descriptor.getFieldSourceNode(tfNode.node, thisBox);
                if (sourceNodeOfField != null) {
                    SootField sootField = sourceNodeOfField.field.getFirst();
                    if (FieldUtil.isTransientType(sootField)) { // TODO: 该field可能不是属于当前类，可能是上一层的类传过来的
                        if (!checkTransientControllableSimply(sourceNodeOfField.classOfField, sootField, descriptor))
                            return false;
                    }
                }
            }
            // 如果是equals方法，则入参必须污染，否则没啥意义
            Pointer thisPointer = descriptor.pointTable.getPointer(thisBox.getValue());
            if (!RuleUtils.invokeContinueCheck(currentInvokeExpr, descriptor, thisPointer))
                return false;

            else if (thisPointer != null){
                if (Utils.isBasicType(thisPointer.getType()))
                    return false;
            }
            return true;
        }

        // TODO: 简单剪枝，如果 this 未被污染 且 非静态方法，则不跟进
        if (currentInvokeExpr.getMethod().isStatic()
                || AnalyzeUtils.isTmpGeneratedObj(thisBox, descriptor)){
            for(int i = 0; i < currentInvokeExpr.getArgCount(); i++){
                Value argValue = currentInvokeExpr.getArg(i);
                if(Utils.isTainted(argValue, descriptor.taints)){
                    return true;
                }
            }
        }
        return false;
    }

    /** Thinking: 检查直接父类还是所有父类为好？
     * 检查invoked method 和已有的方法调用序列中的方法是否具有相同的接口，如果有则不继续跟紧 (最短优先准则)
     * E.g. invokedMethod, method 继承了相同的方法
     * (1) invoked method 是 method继承方法的父类方法 --> invoked method具有强大的方法调用权限
     * Thinking: 检查的时候要注意筛选的是具有相同方法定义的父类/接口方法, 而非所有的父类/接口类
     * 因为是在一个Fragment中的重复检查，所以无需考虑复杂的 equals 嵌套情况
     * @param invokedMethod
     * @param callStack
     * @return
     */
    public static boolean isDupInvokedMethodInFragment(SootMethod invokedMethod, LinkedList<SootMethod> callStack){
        LinkedHashSet<SootMethod> invokedSuperMethods = ClassRelationshipUtils.getAllSuperMethods(invokedMethod, false);
        if (callStack.getLast().equals(invokedMethod))  return true;
        HashSet<SootClass> invokedDirectionClasses = ClassRelationshipUtils.getDirectSuperClzWithMtd(invokedMethod.getDeclaringClass(), invokedMethod.getSubSignature(), false);
        for (SootMethod sootMethod: callStack){
            if (sootMethod.equals(invokedMethod))
                continue;

            LinkedHashSet<SootMethod> superMethods = ClassRelationshipUtils.getAllSuperMethods(sootMethod, false);
            superMethods.retainAll(invokedSuperMethods);
            if (superMethods.isEmpty())
                continue;

            // 如果有交集，则检查是否为thinking中的特殊情况
            HashSet<SootClass> directionClasses = ClassRelationshipUtils.getDirectSuperClzWithMtd(sootMethod.getDeclaringClass(), sootMethod.getSubSignature(), false);
            if (directionClasses.containsAll(invokedDirectionClasses) && directionClasses.size() > invokedDirectionClasses.size())
                continue;
            return true;
        }

        return false;
    }

    /**
     * 根据方法调用的Unit, 提取上文的指针信息
     * (1) 调用的
     */
    public static HashMap<Integer, Pointer> getMethodBaseParamInfo(TransformableNode tfNode, MethodDescriptor descriptor) {
        Stmt stmt = (Stmt) tfNode.node.unit;
        InvokeExpr currentInvokeExpr = stmt.getInvokeExpr();

        // 记录指针信息
        // Step1: 记录this指针信息
        HashMap<Integer, Pointer> inputCallFrame = new HashMap<>();
        ValueBox thisBox = Parameter.getThisValueBox(tfNode.node);
        if (thisBox != null){
            Value thisValue = thisBox.getValue();
            Pointer pointer = descriptor.pointTable.getPointer(thisValue);
            if (pointer != null)
                inputCallFrame.put(-1, pointer);
        }

        // Step2: 记录参数指针信息
        for (int i = 0; i < currentInvokeExpr.getArgCount(); i++){
            Value argValue = currentInvokeExpr.getArg(i);
            Pointer pointer = descriptor.pointTable.getPointer(argValue);
            if (pointer != null)
                inputCallFrame.put(i,pointer);
        }

        return inputCallFrame;
    }

    public static void recordEqualsFieldInEqualsMtd(TransformableNode tfNode,
                                                    MethodDescriptor descriptor) {

        if (!FragmentsContainer.protocolCheckRule.needEqualsTrigger()) return;
        if (!FragmentsContainer.protocolCheckRule.fsMtds.contains(descriptor.sootMethod)) return;

        SootMethod invokedMtd = tfNode.getUnitInvokeExpr().getMethod();
        if (!invokedMtd.getSubSignature().equals("boolean equals(java.lang.Object)"))
            return;
        ValueBox thisValueBox = Parameter.getThisValueBox(tfNode.node);
        if (thisValueBox != null){
            SootField sootField = descriptor.getField(tfNode.node, thisValueBox);
            // TODO: 补充Size/Map中元素类型为泛化类型/Object类型的情况
            if (sootField != null & thisValueBox.getValue().getType().toString().equals("java.lang.Object")) {
                descriptor.equalsField = sootField; // 记录调用下一个equals方法的field
            }
        }
    }

    /**
     * 利用污点传播模型进行污点分析, Sink分析
     * @param tfNode
     * @param descriptor
     * @param callStack
     * @return
     * @throws IOException
     */
    public static boolean checkTransformable(TransformableNode tfNode, MethodDescriptor descriptor, LinkedList<SootMethod> callStack) throws IOException {
        tfNode.forward(descriptor);
        if (!tfNode.exec | !tfNode.containsInvoke())
            return false;
        if (BasicDataContainer.stage.equals(Stage.FRAGMENT_SEARCHING) || BasicDataContainer.stage.equals(Stage.FRAGMENT_SEARCHING_SINGLE))
            tfNode.forwardCheck(descriptor, callStack);
        return true;
    }



    public static HashMap<SourceNode, HashSet<Pair<String, Integer>>>
    extractUsedFields(TransformableNode tfNode, MethodDescriptor descriptor) {
        HashMap<SourceNode, HashSet<Pair<String,Integer>>> ret = new HashMap<>();
        Stmt stmt = (Stmt) tfNode.node.unit;

        if (stmt instanceof AssignStmt){
            for (ValueBox valueBox : stmt.getUseAndDefBoxes()){
                DataFlowAnalysisUtils.addSootFieldRefToMap(tfNode, valueBox, descriptor, ret);
            }
        }else if (stmt.containsInvokeExpr()){
            InvokeExpr invokeExpr = stmt.getInvokeExpr();
            ValueBox thisValueBox = Parameter.getThisValueBox(tfNode.node);
            if (thisValueBox != null){
                DataFlowAnalysisUtils.addSootFieldRefToMap(tfNode, thisValueBox, descriptor, ret);
            }
            for (int ind = 0; ind < invokeExpr.getArgCount(); ind++) {
                DataFlowAnalysisUtils.addSootFieldRefToMap(tfNode, invokeExpr.getArgBox(ind), descriptor,ret);
            }
        }

        return ret;
    }



    public static void addSootFieldRefToMap(TransformableNode tfNode,
                                            ValueBox valueBox,
                                            MethodDescriptor descriptor,
                                            HashMap<SourceNode, HashSet<Pair<String, Integer>>> ret) {
        if (valueBox == null) return ;

        for (SourceNode source: descriptor.sourcesTaintGraph.matchTaintedSources(valueBox.getValue())){
            if (source.isField()){
                if (!ret.containsKey(source))
                    ret.put(source, new HashSet<>());
                ret.get(source).add(getUsedSite(tfNode));
            }
        }

        if (!ret.isEmpty()) return;

        SootField tmpField = descriptor.getFieldDirectly(tfNode.node, valueBox);
        if (tmpField != null){
            LinkedList<SootField> fields = new LinkedList<>();
            fields.add(tmpField);
            SourceNode sourceNode = new SourceNode(fields, descriptor.getCurrentClass());
            if (!ret.containsKey(sourceNode))
                ret.put(sourceNode, new HashSet<>());
            ret.get(sourceNode).add(getUsedSite(tfNode));
        }
    }


    public static boolean shortPriorityLinkCheck(Fragment preFragment, Fragment sucFragment){
        // 1. 先检查要拼接的抽象方法是否存在重复
        if (isDuplicate(preFragment,sucFragment))
            return false;
        // 2. 其他规则


        return true;
    }


    public static void flushSinkFragmentsBasedOnPriority(Fragment testFragment,
                                                         HashSet<Fragment> recordedFragments,
                                                         HashSet<Fragment> newSinkFragments){
        HashSet<Fragment> toDelete = new HashSet<>();
        boolean addFlag = true; // 简单的短链优先原则，筛选掉一些冗余的chains
        if (!RuleUtils.heuristicFilterGF(testFragment, 0))
            return;
        for (Fragment recordedFragment: newSinkFragments){
            // 启发式判断
            int heuristicPriority = isHeuristicPriority(testFragment, recordedFragment);
            if (heuristicPriority == 1)
                toDelete.add(recordedFragment);
            else if (heuristicPriority == -1)
                addFlag = false;
        }

        recordedFragments.removeAll(toDelete);
        FragmentsContainer.sinkFragments.removeAll(toDelete);
        if (addFlag) {
            recordedFragments.add(testFragment);
            newSinkFragments.add(testFragment);
            FragmentsContainer.sinkFragments.add(testFragment);
            testFragment.calPrioritySimply();

            // 当数量达到一定程度后，进行一个启发式的筛选，过滤掉优先级底的chains
            if (newSinkFragments.size() > RegularConfig.prioritizedGadgetChainLimit * 5) {
                HashSet<Fragment> toDeleteHir = deleteHir(newSinkFragments, RegularConfig.prioritizedGadgetChainLimit * 5);
                newSinkFragments.removeAll(toDeleteHir);
                FragmentsContainer.sinkFragments.removeAll(toDeleteHir);
                recordedFragments.removeAll(toDeleteHir);
            }
        }
    }

    public static void calculatePriority(HashSet<Fragment> newSinkFragments, HashSet<Fragment> allBasicFragments){
        // 先建立基础 basic fragments 索引 Map
        HashMap<Integer, Fragment> allBasicFragmentsMap = new HashMap<>();
//        for (Fragment fragment: allBasicFragments) {
//            allBasicFragmentsMap.put(fragment.hashCode(), fragment);
//        }

        allBasicFragmentsMap = FragmentsContainer.basicFragmentsMap;

        HashSet<Integer> calculatedFragments = new HashSet<>();
        HashMap<Integer, Float> basicFragmentsPriorityRecord = new HashMap<>();
        for (Integer hashCode: allBasicFragmentsMap.keySet()){
            if (calculatedFragments.contains(hashCode))
                continue;
            Fragment basicFragment = allBasicFragmentsMap.get(hashCode);
            calculatePriorityForBasicFragments(basicFragment, basicFragmentsPriorityRecord,
                    allBasicFragmentsMap, calculatedFragments);
        }

        for (Fragment newSinkFragment: newSinkFragments) {
            calculatePriority(newSinkFragment, basicFragmentsPriorityRecord, allBasicFragmentsMap);
        }

        FragmentsContainer.sinkFragments.size();
    }

    public static void calculatePriorityForBasicFragments(Fragment fragment,
                                                             HashMap<Integer, Float> basicFragmentsPriorityRecord,
                                                             HashMap<Integer, Fragment> allBasicFragmentsMap,
                                                             HashSet<Integer> calculatedFragments){
        // 查找 basic Fragments 中与该 fragment 具有相同 head-end 的
        HashSet<Integer> matchedFragments = new HashSet<>();
        matchedFragments.add(fragment.hashCode());
        int maxFragmentLen = fragment.gadgets.size();
        for (Integer hashCode: allBasicFragmentsMap.keySet()){
            Fragment basicFragment = allBasicFragmentsMap.get(hashCode);
            if ((Utils.hashSameElement(basicFragment.connectRequire.preLinkableMethods, fragment.connectRequire.preLinkableMethods)
                    | (basicFragment.state.equals(Fragment.FRAGMENT_STATE.SOURCE) & fragment.state.equals(Fragment.FRAGMENT_STATE.SOURCE)))
                    & ClassRelationshipUtils.hasSameSuperMethod(basicFragment.end, fragment.end)) {
                if (basicFragment.gadgets.size() > maxFragmentLen)
                    maxFragmentLen = basicFragment.gadgets.size();
                matchedFragments.add(hashCode);
            }
        }

        for (Integer hashCode: matchedFragments){ // TODO: 对以 equals作为head的fragment(恒定)加入与hashCode相关fields的分数评估
            Fragment basicFragment = allBasicFragmentsMap.get(hashCode);
            float lenMark = 10 * ((float) basicFragment.gadgets.size() / maxFragmentLen);
            int jdkBasicGadgetNum = 0;
            for (SootMethod gadget: basicFragment.gadgets){
                if (Utils.isJdkInnerMethod(gadget))
                    jdkBasicGadgetNum ++;
            }
            float jdkBasicMark = 2 - (float) jdkBasicGadgetNum /basicFragment.gadgets.size();
            float mark = lenMark + basicFragment.gadgets.size() * jdkBasicMark;
            if (basicFragment.state.equals(Fragment.FRAGMENT_STATE.SOURCE))
                mark = mark * 3;
            basicFragmentsPriorityRecord.put(hashCode, mark);
            calculatedFragments.add(hashCode);
        }
    }

    public static void calculatePriority(Fragment fragment,
                                         HashMap<Integer, Float> basicFragmentsPriorityRecord,
                                         HashMap<Integer, Fragment> allBasicFragmentsMap){
        int lenMark = fragment.linkedFragments.size() * 3;
        int mark = lenMark;
        for (int index = 0; index < fragment.linkedFragments.size(); index++) {
            Integer hashCode = fragment.linkedFragments.get(index);
            mark += basicFragmentsPriorityRecord.get(hashCode);
        }

        fragment.priority = mark;
    }

    /**
     * 匹配存在相同片段的 Fragments
     * (1)
     * @param fragment
     * @param allFragments
     * @return
     */
    public static HashSet<Fragment> getFragmentsWithSameFragment(Fragment fragment, HashSet<Fragment> allFragments){
        HashSet<Fragment> ret = new HashSet<>();
        for (Fragment tmpFragment: allFragments){
            if (Utils.hashSameElement(tmpFragment.linkedFragments, fragment.linkedFragments)){
                ret.add(tmpFragment);
            }
        }
        return ret;
    }

    public static LinkedList<Fragment> getLinkedFragments(Fragment fragment, HashMap<Integer, Fragment> allSinkFragmentsMap){
        LinkedList<Fragment> linkedFragment = new LinkedList<>();
        for (Integer hashCode: fragment.linkedFragments){
            if (!allSinkFragmentsMap.containsKey(hashCode)) // 匹配出现问题, 暂停匹配
                return null;
            linkedFragment.add(allSinkFragmentsMap.get(hashCode));
        }
        return linkedFragment;
    }

    /**
     * 判断Fragments拼接是否存在重复 (接口, 具体方法)
     * @param preFragment
     * @param sucFragment
     * @return true: 存在重复
     */
    public static boolean isDuplicate(Fragment preFragment, Fragment sucFragment){
        // 1. 检查方法是否重复
        if (Utils.hashSameElement(preFragment.connectRequire.preLinkableMethods, sucFragment.linkedDynamicMethods))
            return true;

        int equalsMtdCount = 0;
        for (SootMethod tmpMtd: preFragment.gadgets){
            if (sucFragment.gadgets.contains(tmpMtd))
                return true;
        }

        if (equalsMtdCount >= 3)
            return true;

        HashSet<SootMethod> superMethodsPre = new HashSet<>();
        HashSet<SootMethod> superMethodsSuc = new HashSet<>();
        // 2. 检查接口是否重复
        if (preFragment.endInvokableMethods == null){
            SootMethod headOfSucFragment = sucFragment.head;
            superMethodsPre = ClassRelationshipUtils.getAllSuperMethods(headOfSucFragment, true);
            for (SootMethod gadget: preFragment.gadgets){
                if (!gadget.getSubSignature().equals(headOfSucFragment.getSubSignature())
                        ||RuleUtils.isEqMethod(gadget))  continue;
                superMethodsSuc = ClassRelationshipUtils.getAllSuperMethods(gadget, true);
                superMethodsSuc.retainAll(superMethodsPre);
                if (!superMethodsSuc.isEmpty())
                    return true;
            }
        }
        for (SootMethod linkedDynamicMethodPre: preFragment.linkedDynamicMethods){
            superMethodsPre = ClassRelationshipUtils.getAllSuperMethods(linkedDynamicMethodPre, true);
            for (SootMethod linkedDynamicMethodSuc: sucFragment.linkedDynamicMethods){
                superMethodsSuc = ClassRelationshipUtils.getAllSuperMethods(linkedDynamicMethodSuc, true);
                superMethodsSuc.retainAll(superMethodsPre);
                if (!superMethodsSuc.isEmpty())
                    return true;
            }
        }

        return false;
    }

    /**
     * 应用启发式规则比较两个Sink Fragments哪个优先级高，若需要严格保证输出结果的完备性，建议关掉该步骤
     * (1) 比如中间多一个 fragments 被认为优先级更低
     * (2) 具有相同可调用方法的head, end, 栈长度过大的被认为优先级更低;
     * @param testedSinkFragment
     * @param recordedSinkFragment
     * @return testedSinkFragment 是否具有比 recordedSinkFragment 更高的优先级
     * 1: testedSinkFragment 优先级高 (删除 recordedSinkFragment)
     * 0: 差不多, 无需操作
     * -1: recordedSinkFragment 优先级高 (删除 testedSinkFragment)
     */
    public static int isHeuristicPriority(Fragment testedSinkFragment, Fragment recordedSinkFragment){
        if (testedSinkFragment.linkedDynamicMethods.isEmpty() || recordedSinkFragment.linkedDynamicMethods.isEmpty())
            return 0;
        if (Utils.listEqual(testedSinkFragment.getGadgets(), recordedSinkFragment.getGadgets()))    return -1;
        if (testedSinkFragment.linkedDynamicMethods.getFirst().equals(recordedSinkFragment.linkedDynamicMethods.getFirst())
                && testedSinkFragment.linkedDynamicMethods.getLast().equals(recordedSinkFragment.linkedDynamicMethods.getLast())) {
            if (testedSinkFragment.linkedDynamicMethods.containsAll(recordedSinkFragment.linkedDynamicMethods)
                    && testedSinkFragment.linkedDynamicMethods.size() > recordedSinkFragment.linkedDynamicMethods.size() + 2)
                return -1;
            else if (recordedSinkFragment.linkedDynamicMethods.containsAll(testedSinkFragment.linkedDynamicMethods)
                    && recordedSinkFragment.linkedDynamicMethods.size() > testedSinkFragment.linkedDynamicMethods.size() + 2)
                return 1;
            return 0;
        }
        return 0;
    }


    public static void inferExtraInfosOfGadgetChain(LinkedList<SootMethod> callStack,
                                                    GadgetInfoRecord gadgetInfoRecord,
                                                    MethodDescriptor descriptor,
                                                    TransformableNode tfNode,
                                                    boolean inConClassFlag) throws IOException {
        if (Utils.isSubList(callStack,gadgetInfoRecord.gadgets)){
            tfNode.forwardInferCheck(descriptor,gadgetInfoRecord);
        }else if (inConClassFlag
                | (ClassRelationshipUtils.isGetterMethod(descriptor.sootMethod)
                & descriptor.sootMethod.getDeclaringClass().equals(gadgetInfoRecord.curClass))
                | Utils.getCallStacksDeviation(callStack, gadgetInfoRecord.gadgets)
                    <= BasicDataContainer.stackDeviationLimit-1){
            tfNode.forwardExtraInferCheck(descriptor, gadgetInfoRecord);
        }
    }


    public static void inferInfosOnGadgetChain(GadgetInfoRecord gadgetInfoRecord,
                                               LinkedList<SootMethod> callStack,
                                               TransformableNode tfNode,
                                               MethodDescriptor invokedDescriptor,
                                               MethodDescriptor descriptor){
        ClassNode nextClassNode = gadgetInfoRecord.createNewClassNode(tfNode, invokedDescriptor, descriptor, callStack);

        if (nextClassNode == null) {
            ClassNode curClassNode = gadgetInfoRecord.getClassNode(gadgetInfoRecord.curClass);
            if (curClassNode == null)
                return;
            curClassNode.createAndAddGadgetNode(invokedDescriptor);
        }else {
            nextClassNode.createAndAddGadgetNode(invokedDescriptor);
        }


        GadgetNode gadgetNode = gadgetInfoRecord.getGadgetNode(descriptor.sootMethod);
        if (gadgetNode == null)
            return;
        gadgetNode.recordDominatorConditions(tfNode, gadgetInfoRecord, descriptor);

        invokedDescriptor.visited = false; // 确保一定进入跟踪
    }


    public static ClassNode inferInfosOutOfGadgetChain(GadgetInfoRecord gadgetInfoRecord,
                                                  LinkedList<SootMethod> callStack,
                                                  TransformableNode tfNode,
                                                  MethodDescriptor invokedDescriptor,
                                                  MethodDescriptor descriptor) throws IOException {
        if (invokedDescriptor.sootMethod.isStatic()){
            tfNode.forwardExtraInferCheck(descriptor, gadgetInfoRecord);
            gadgetInfoRecord.createAddGadgetNodeToClassNode(invokedDescriptor.sootMethod, gadgetInfoRecord.curClass);
            return null;
        }
        if (callStack.size() > BasicDataContainer.stackDeviationLimit){
            tfNode.forwardExtraInferCheck(descriptor, gadgetInfoRecord);
        }

        ClassNode conClassNode = createConClassNodeAndAddGadget(callStack, descriptor, invokedDescriptor, gadgetInfoRecord, tfNode);

        return conClassNode;
    }

    public static ClassNode createConClassNodeAndAddGadget(LinkedList<SootMethod> callStack,
                                                           MethodDescriptor descriptor,
                                                           MethodDescriptor invokedDescriptor,
                                                           GadgetInfoRecord gadgetInfoRecord,
                                                           TransformableNode tfNode){
        SootMethod preMethod = AnalyzeUtils.getPreMethod(callStack, descriptor.sootMethod);
        ClassNode conClassNode = gadgetInfoRecord.createConClassNodes(tfNode, preMethod, descriptor, invokedDescriptor);
        if (conClassNode == null)
            return null;

        SootClass invokedClass = invokedDescriptor.getCurrentClass();
        GadgetNode newGadgetNode = new GadgetNode(invokedDescriptor.sootMethod,
                invokedClass == null? invokedDescriptor.sootMethod.getDeclaringClass() : invokedClass);
        conClassNode.addGadgetNode(newGadgetNode);
        invokedDescriptor.visited = false;
        return conClassNode;
    }

    public static boolean continueInferSupplementInfos(SootMethod invokedMethod,
                                                       GadgetInfoRecord gadgetInfoRecord){
        SootClass classOfInvokedMethod = ClassRelationshipUtils.getOuterClass(invokedMethod.getDeclaringClass());
        if (invokedMethod.isStatic()){
            return true;
        }
        if (classOfInvokedMethod != null){
            ClassNode tmpClassNode = gadgetInfoRecord.getClassNode(classOfInvokedMethod);
            if (tmpClassNode == null)
                return false;
        }
        return true;
    }
}
