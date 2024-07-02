package detetor;

import PointToAnalyze.pointer.Pointer;
import config.ConfigUtil;
import config.InitConfig;
import config.RegularConfig;
import config.SootConfig;
import container.BasicDataContainer;
import container.FragmentsContainer;
import dataflow.DataFlowAnalysisUtils;
import dataflow.DataflowDetect;
import dataflow.node.MethodDescriptor;
import dataflow.node.SourceNode;
import dataflow.node.UndeterminedFieldNode;
import fj.P;
import gadgets.collection.iocd.unit.instrument.Instruments;
import gadgets.collection.node.ClassNode;
import gadgets.collection.node.GadgetInfoRecord;
import gadgets.unit.Fragment;
import lombok.extern.slf4j.Slf4j;
import markers.SinkType;
import markers.Stage;
import soot.*;
import soot.jimple.AddExpr;
import soot.jimple.Expr;
import soot.jimple.XorExpr;
import tranModel.Rule;
import tranModel.Rules.RuleUtils;
import tranModel.TranUtil;
import tranModel.TransformableNode;
import util.DataSaveLoadUtil;
import util.Pair;
import util.StaticAnalyzeUtils.Parameter;
import util.TimeOutTask;
import util.Utils;

import java.io.File;
import java.io.FileWriter;
import java.io.IOException;
import java.util.*;

import static dataflow.DataFlowAnalysisUtils.flushSinkFragmentsBasedOnPriority;
import static detetor.SearchUtils.*;
import static gadgets.collection.iocd.TransformerUtils.*;
import static util.ClassRelationshipUtils.isProxyMethod;

@Slf4j
public class SearchGadgetChains {
    public static int timeThread = 15;
    public static DataflowDetect dataflowDetect = new DataflowDetect();

    public static void detect() throws Exception {
        // 1. 初始化
        InitConfig.initAllConfig();

        // 2. Gadget Fragment的搜索
        log.info("[ Fragments Searching]");
        searchGadgetFragments();

        // 3. Gadget Fragment的拼接
        log.info("[ Fragments Linking]");
        linkFragments();

        // 生成IOCD信息
        System.out.println("[ IOCD Generating ]");
        buildIOCD();

        // 分析结束提示
//        analysisFinalSignal();
    }

    public static void analysisFinalSignal() throws IOException {
        String filePath = "/home/cbf/dvd-evaluation/evaluation" + File.separator + "detect-fin";
        try {
            FileWriter out = new FileWriter(filePath, false);
            out.write("detect-fin");
            out.flush();
        } catch (IOException e) {
            log.error("Could not write result to " + filePath + "!");
            e.printStackTrace();
        }
    }


    public static void searchGadgetFragments() {
        setDetectSchemeOn(); // 设置开始检测的 flag
        while (!FragmentsContainer.sources.isEmpty()) {
            SootMethod headMtd = FragmentsContainer.sources.iterator().next();
            FragmentsContainer.sources.remove(headMtd);
            FragmentsContainer.searched.add(headMtd);
            searchFragment(headMtd, null);

            if (FragmentsContainer.superMtdSources.containsKey(headMtd)) { // 考虑
                while (!FragmentsContainer.superMtdSources.get(headMtd).isEmpty()) {
                    SootClass thisClz = FragmentsContainer.superMtdSources.get(headMtd).iterator().next();
                    FragmentsContainer.superMtdSources.get(headMtd).remove(thisClz);
                    FragmentsContainer.searched.add(headMtd);
                    searchFragment(headMtd, thisClz);
                }
            }
        }
        setDetectSchemeOff();
    }

    public static boolean collectFields(SootMethod sootMethod, HashSet<SourceNode> usedFields) {
        // 生成初始方法的污点信息
        MethodDescriptor descriptor = initDealBeforeSearching(sootMethod, null);
        LinkedList<SootMethod> callStack = new LinkedList<>();
        callStack.add(sootMethod);

        // 展开数据流嗖嗖
        try {
            new TimeOutTask() {
                @Override
                protected void task() throws IOException {
                    log.info("搜索方法中相关的fields" + sootMethod.getSignature());
                    dataflowDetect.collectFields(sootMethod, usedFields, callStack);
                }

                @Override
                protected void timeoutHandler() {
                    log.error("分析方法" + sootMethod.getName() + "时超时"
                            + "位于类" + sootMethod.getDeclaringClass() + "位于类" + sootMethod.getDeclaringClass());
                }
            }.run(180);
        } catch (Exception e) {
            e.printStackTrace();
            descriptor.isEntry = false;
            return false;
        }

        return !callStack.contains(null);
    }


    public static boolean isValidFixedHashCode(boolean flag, SootMethod sootMethod,
                                               HashSet<SourceNode> usedFields,
                                               LinkedList<SootMethod> callStack) throws IOException {
        MethodDescriptor descriptor = DataFlowAnalysisUtils.getMethodDescriptor(sootMethod);
        if (descriptor == null) return flag;

        // 更新调用该method的方法到该方法的信息, ;过程间分析
        HashSet<Value> hashCodeValues = new HashSet<>();

        DataFlowAnalysisUtils.updateInterInfos(descriptor);
        List<TransformableNode> topologicalOrder = TranUtil.getTopologicalOrderedTNodesFromCFG(descriptor.cfg);
        for (TransformableNode tfNode : topologicalOrder) {
            HashMap<SourceNode, HashSet<Pair<String, Integer>>> ret = DataFlowAnalysisUtils.extractUsedFields(tfNode, descriptor);
            // 记录被使用的fields
            for (SourceNode sourceNode : ret.keySet()) {
                if (sourceNode.classOfField.equals(descriptor.getCurrentClass()))
                    usedFields.add(sourceNode);
            }
        }

        for (TransformableNode tfNode : topologicalOrder) {
            // 记录被调用了hashCode()方法, 计算hashCode的fields对应的local values
            if (tfNode.containsInvoke()) {
                SootMethod invokedMethod = tfNode.getUnitInvokeExpr().getMethod();

                if (invokedMethod.getSubSignature().equals("int hashCode()")) {
                    ValueBox valueBox = Parameter.getThisValueBox(tfNode.node);
                    if (valueBox != null) {
                        Pointer thisPointer = descriptor.pointTable.getPointer(valueBox.getValue());
                        if (thisPointer != null && thisPointer.getType().toString().equals("java.lang.Class")) continue;
                    }
                    Value retValue = Parameter.getReturnedValue(tfNode.node);
                    hashCodeValues.add(retValue);
                }
            }

            for (ValueBox valueBox : tfNode.node.unit.getUseAndDefBoxes()) {
                if (valueBox == null)
                    continue;
                if (!hashCodeValues.contains(valueBox.getValue()))
                    continue;

                if (valueBox.getValue() instanceof Expr) {
                    if (!(valueBox.getValue() instanceof XorExpr
                            | valueBox.getValue() instanceof AddExpr)) {
                        flag = false;
                    }
                }
            }

            DataFlowAnalysisUtils.checkTransformable(tfNode, descriptor, callStack);

            if (tfNode.containsInvoke() & callStack.size() <= BasicDataContainer.stackLenLimitForFieldsCollection) {
                if (DataFlowAnalysisUtils.continueCheck(tfNode, descriptor)) {
                    HashMap<Integer, Pointer> inputCallFrame = DataFlowAnalysisUtils.getMethodBaseParamInfo(tfNode, descriptor);
                    HashSet<SootMethod> invokedMethods = DataFlowAnalysisUtils.getInvokedMethods(tfNode, descriptor);
                    if (invokedMethods.size() > 10) {
                        callStack.add(null);
                        return flag;
                    }

                    for (SootMethod invokedMethod : invokedMethods) {
                        MethodDescriptor invokedDescriptor = DataFlowAnalysisUtils.flowInvokedMethod(descriptor, invokedMethod, inputCallFrame, callStack, tfNode);
                        if (invokedDescriptor == null | sootMethod.equals(invokedMethod)) {
                            callStack.add(null);
                            return flag;
                        }
                        flag = isValidFixedHashCode(flag, invokedMethod, usedFields, callStack);
                        DataFlowAnalysisUtils.outInvokedMethod(invokedDescriptor, descriptor, tfNode, callStack);
                    }
                } else {
                    callStack.add(null);
                }
            }
        }

        DataFlowAnalysisUtils.updateAfterAnalysisMtd(descriptor);
        return flag;
    }


    /**
     * 构建以sootMethod作为entry的 fields-taints Graph
     *
     * @param sootMethod
     */
    public static void constructFieldsTaintGraph(SootMethod sootMethod) {
        BasicDataContainer.stage = Stage.TAINT_FIELDS_GRAPH_BUILD;
        MethodDescriptor descriptor = initDealBeforeSearching(sootMethod, null);
        LinkedList<SootMethod> callStack = new LinkedList<>();
        HashSet<UndeterminedFieldNode> undeterminedFieldNodes = new HashSet<>();
        try {
            new TimeOutTask() {
                @Override
                protected void task() throws IOException {
                    log.info("搜索方法中相关的fields" + sootMethod.getSignature());
                    dataflowDetect.constructFieldsTaintGraph(sootMethod, callStack, undeterminedFieldNodes);
                }

                @Override
                protected void timeoutHandler() {
                    log.error("分析方法" + sootMethod.getName() + "时超时"
                            + "位于类" + sootMethod.getDeclaringClass() + "位于类" + sootMethod.getDeclaringClass());
                }
            }.run(180);
        } catch (Exception e) {
            e.printStackTrace();
            descriptor.isEntry = false;
            return;
        }
    }


    /**
     * 对 startMtd 作为起始方法, 搜索并记录 Fragment 信息
     * (1) 搜索过程中检测到的其他动态方法
     * (2) 入参与动态方法调用参数之间的映射关系
     * (3) 生成的Fragment的相关信息: Fragment类型,
     *
     * @param headMtd
     */
    public static void searchFragment(SootMethod headMtd, SootClass thisClass) {
        if (FragmentsContainer.isSinkMethod(headMtd) || RuleUtils.isInvalidFragmentEnd(headMtd, false))
            return;
        BasicDataContainer.stage = Stage.FRAGMENT_SEARCHING;

        MethodDescriptor descriptor = initDealBeforeSearching(headMtd, thisClass);

        LinkedList<SootMethod> callStack = new LinkedList<>();
        callStack.add(headMtd);

        // 展开数据流嗖嗖
        try {
            new TimeOutTask() {
                @Override
                protected void task() throws IOException {
                    log.info("处理方法" + headMtd.getSignature());
                    dataflowDetect.detectFragment(descriptor, callStack);
                }

                @Override
                protected void timeoutHandler() {
                    log.error("分析方法" + headMtd.getName() + "时超时"
                            + "位于类" + headMtd.getDeclaringClass() + "位于类" + headMtd.getDeclaringClass());
                }
            }.run(timeThread);
        } catch (Exception e) {
            e.printStackTrace();
            descriptor.isEntry = false;
            return;
        }

        descriptor.isEntry = false;
    }

    /**
     * 进行 Fragments 的拼接
     * TODO 未迁移的功能: 拼接后更细粒度的污点检查 & 无用fragments的
     */
    public static void linkFragments() {
        if (!FragmentsContainer.protocolCheckRule.openBPLink()) {
            FragmentsContainer.gadgetFragments = FragmentsContainer.sinkFragments;
            FragmentsContainer.sortSinkFragments();
            return;
        }


        BasicDataContainer.stage = Stage.FRAGMENT_LINKING;

        LinkedHashSet<Fragment> newSinkFragments = new LinkedHashSet<>();
        HashSet<Fragment> freeStateFragments = new HashSet<>(
                FragmentsContainer.stateFragmentsMap.get(Fragment.FRAGMENT_STATE.FREE_STATE)
        );
        LinkedHashSet<Fragment> allSinkFragments = new LinkedHashSet<>(FragmentsContainer.sinkFragments);
        HashSet<SootMethod> dynamicMethods = new HashSet<>();
        HashSet<SootMethod> dynamicMethodsNext = new HashSet<>();
        for (Fragment sinkFragment : allSinkFragments) {
            dynamicMethods.addAll(sinkFragment.connectRequire.preLinkableMethods);
        }
        int linkCount = 0;

        // 迭代
        while (!dynamicMethods.isEmpty() && linkCount <= BasicDataContainer.linkTimeLimit) {
            newSinkFragments.clear();
            HashSet<Fragment> toDelete = new HashSet<>();
            for (Fragment freeStateFragment : freeStateFragments) {
                if (!dynamicMethods.contains(freeStateFragment.end))
                    continue;

                HashSet<Fragment> addSinkFragments = dataflowDetect.linkFreeStateFragments(freeStateFragment);
                if (!addSinkFragments.isEmpty()) toDelete.add(freeStateFragment);
                for (Fragment newSinkFragment : addSinkFragments) { // TODO: 增加开关，选择是否要开启启发式选择
                    flushSinkFragmentsBasedOnPriority(newSinkFragment, allSinkFragments, newSinkFragments);

                    HashSet<SootMethod> newDynamicMtds = new HashSet<>(newSinkFragment.connectRequire.preLinkableMethods);
                    newDynamicMtds.removeAll(dynamicMethods);
                    if (!newDynamicMtds.isEmpty()) {
                        dynamicMethodsNext.addAll(newDynamicMtds);
                        dynamicMethods.addAll(newDynamicMtds);
                    }
                }
            }
            // 在获取所有的新增 Sink Fragments 后, 将全局的sinkFragments更新为本轮新增的,
            // 并将这些Fragments从Free-State Fragments中删除
            FragmentsContainer.sinkFragments = new HashSet<>(newSinkFragments);
            if (newSinkFragments.isEmpty() || dynamicMethodsNext.isEmpty()) {
                break;
            }
            dynamicMethods = new HashSet<>(dynamicMethodsNext);

            if (RegularConfig.linkMode.equals("strict")) {
                for (Fragment freeStateFragment : toDelete) {
                    HashSet<Fragment> addSinkFragments = dataflowDetect.linkFreeStateFragments(freeStateFragment);
                    for (Fragment newSinkFragment : addSinkFragments) { // TODO: 增加开关，选择是否要开启启发式选择
                        flushSinkFragmentsBasedOnPriority(newSinkFragment, allSinkFragments, newSinkFragments);
                    }
                }
                FragmentsContainer.sinkFragments = new HashSet<>(newSinkFragments);
            }
            freeStateFragments.removeAll(toDelete);

//            // 如果还没退出, 则计算和评估 Fragments 的优先级\
//            DataFlowAnalysisUtils.calculatePriority(newSinkFragments, allSinkFragments);
        }
        FragmentsContainer.sinkFragments = allSinkFragments;

        newSinkFragments.clear();
        for (Fragment sourceFragment : FragmentsContainer.stateFragmentsMap.get(Fragment.FRAGMENT_STATE.SOURCE)) {
            if (!RuleUtils.heuristicGadgetChainLink(sourceFragment, null))
                continue;
            HashSet<Fragment> addSinkFragments = dataflowDetect.linkSourceFragments(sourceFragment);
            for (Fragment fragment : addSinkFragments) {
                flushSinkFragmentsBasedOnPriority(fragment, newSinkFragments, newSinkFragments);
            }

            FragmentsContainer.gadgetFragments = newSinkFragments;
        }

        FragmentsContainer.sortSinkFragments();
        log.info("Gadget chains总数 = " + FragmentsContainer.gadgetFragments.size());
    }

    /**
     * 对检测出的 gadget Fragments 收集信息, 生成 IOCD
     */
    public static void buildIOCD() throws Exception {
        BasicDataContainer.stage = Stage.IOCD_GENERATING;

        setDetectSchemeOn();
        int count = 0, detectedCount = 0;

        Instruments instruments = new Instruments();
        // 先检查结果的目标存储目录是否存在，如果不存在则创建
        String targetResultsPath = RegularConfig.outputDir + File.separator + "gadgets" + File.separator + RegularConfig.outPutDirName + File.separator;
        DataSaveLoadUtil.createDir(targetResultsPath);

        for (HashSet<Fragment> sinkFragments : FragmentsContainer.sortedSinkFragmentsMap.values()) {
            for (Fragment sinkFragment : sinkFragments) {
                if (!RuleUtils.heuristicFilterGF(sinkFragment, detectedCount))
                    continue;
                detectedCount++;
                DataSaveLoadUtil.recordCallStackToFile(sinkFragment.gadgets, sinkFragment.sinkType,
                        RegularConfig.outputDir + "/gadgets/interInfos/" + sinkFragment.sinkType.toString() + "SinkFragments.txt",
                        true);

                GadgetInfoRecord gadgetInfoRecord = FragmentsContainer.generateInitGadgetInfoRecord(sinkFragment);

                if (gadgetInfoRecord != null) {
                    inferGadgetsInfos(gadgetInfoRecord);
                    if (gadgetInfoRecord.flag)
                        count++;
                    try {
                        constructIOCDAndSave(gadgetInfoRecord, instruments);
                    } catch (Throwable throwable) {
                        throwable.printStackTrace();
                    }
                } else if (gadgetInfoRecord == null) {
                    System.out.println("[Pass Gadget Chain Collection]");
                }
            }
        }

        log.info("IOCD验证后, Gadget chains总数 = " + count);

        // 最后输出插桩信息
        exportInstrumentsRecordJson(instruments, RegularConfig.outputDir + File.separator + "gadgets" + File.separator + RegularConfig.outPutDirName + File.separator);
    }

    public static void inferGadgetsInfos(GadgetInfoRecord gadgetInfoRecord) {
        SootMethod sourceGadget = gadgetInfoRecord.gadgets.getFirst();
        MethodDescriptor descriptor = initDealBeforeInferring(gadgetInfoRecord);

        LinkedList<SootMethod> callStack = new LinkedList<>();
        callStack.add(sourceGadget);

        try {
            new TimeOutTask() {
                @Override
                protected void task() throws IOException {
                    log.info("处理方法" + sourceGadget.getSignature());
                    dataflowDetect.inferGadgetInfosOfWholeLife(sourceGadget, gadgetInfoRecord, callStack);
                }

                @Override
                protected void timeoutHandler() {
                    log.error("分析方法" + sourceGadget.getName() + "时超时"
                            + "位于类" + sourceGadget.getDeclaringClass() + "位于类" + sourceGadget.getDeclaringClass());
                }
            }.run(60 * 2);
        } catch (Throwable e) {
            e.printStackTrace();
            descriptor.isEntry = false;
            return;
        }
    }

    public static void constructIOCDAndSave(GadgetInfoRecord gadgetInfoRecord, Instruments instruments) throws Exception {
        if (!gadgetInfoRecord.flag)
            return;
        if (gadgetInfoRecord.hashCollisionReview == 1) {
            if (!RuleUtils.recordCollisionForSingleHC(gadgetInfoRecord.linkedFragments,
                    RuleUtils.getEqFragmentByIndex(gadgetInfoRecord.linkedFragments, 1), gadgetInfoRecord))
                return;
        }
        if (gadgetInfoRecord.hashCollisionReview == 0) {
            HashSet<SootField> rootFieldsRecord = new HashSet<>();
            for (ClassNode classNode : gadgetInfoRecord.classFieldsGraph.values()) {
                if (classNode.source == null)
                    continue;
                if (!classNode.source.isField())
                    continue;

                if (!rootFieldsRecord.contains(classNode.source.field.getFirst()))
                    rootFieldsRecord.add(classNode.source.field.getFirst());
                else {
                    gadgetInfoRecord.flag = false;
                    return;
                }
            }
        }

        String dir = RegularConfig.outputDir + "/gadgets" + File.separator + RegularConfig.outPutDirName + File.separator;
        exportGadgetRecordJson(gadgetInfoRecord, dir);
        recordIfStmtAndMethodForInst(gadgetInfoRecord, instruments);
    }

}