package gadgets.collection.rule;

import rules.sinks.CustomCheckRule;
import rules.sinks.FileCheckRule;
import soot.jimple.Stmt;
import tranModel.Rules.RuleUtils;
import tranModel.Transformable;
import tranModel.TransformableNode;
import container.FragmentsContainer;
import dataflow.node.MethodDescriptor;
import dataflow.node.SourceNode;
import gadgets.collection.node.GadgetInfoRecord;
import gadgets.collection.node.SinkNode;
import lombok.extern.slf4j.Slf4j;
import markers.SinkType;
import rules.sinks.CheckRule;
import rules.sinks.JNDICheckRule;
import soot.*;
import soot.jimple.InvokeExpr;
import util.StaticAnalyzeUtils.Parameter;
import util.Utils;

import java.io.IOException;
import java.util.HashSet;
import java.util.LinkedHashSet;
import java.util.LinkedList;

@Slf4j
public class SinkCheck implements InferRule{
    @Override
    public void apply(MethodDescriptor descriptor,
                      GadgetInfoRecord gadgetInfosRecord,
                      Transformable transformable) throws IOException {
        TransformableNode tfNode = (TransformableNode) transformable;
        if (!tfNode.containsInvoke())
            return;
        if (!gadgetInfosRecord.gadgets.contains(descriptor.sootMethod))
            return;

        CheckRule checkRule = FragmentsContainer.protocolCheckRule.getCheckRule(gadgetInfosRecord.sinkType);
        if (!checkRule.checkRisky(descriptor, tfNode))
            return;

        switch (gadgetInfosRecord.sinkType){
            case JNDI:
                applyJNDI(descriptor, gadgetInfosRecord, tfNode);
                break;
            case LOAD_CLASS:
                applyLoadClass(descriptor, gadgetInfosRecord, tfNode);
                break;
            case EXEC:
                applyExec(descriptor, gadgetInfosRecord, tfNode);
                break;
            case FILE:
                applyWriteFile(descriptor, gadgetInfosRecord, tfNode);
                break;
            case INVOKE:
                applyInvoke(descriptor, gadgetInfosRecord, tfNode);
                break;
            case SECOND_DES:
                applySecodDes(descriptor, gadgetInfosRecord, tfNode); break;
            case CUSTOM:
                applyCusToms(descriptor, gadgetInfosRecord, tfNode); break;
        }
    }

    private void applyCusToms(MethodDescriptor descriptor, GadgetInfoRecord gadgetInfosRecord, TransformableNode tfNode) {
        InvokeExpr invokeExpr = tfNode.getUnitInvokeExpr();
        SinkNode sinkNode = new SinkNode(tfNode.node, descriptor.getCurrentClass(), gadgetInfosRecord.sinkType);
        ValueBox valueBox = null;
        String methodSig = invokeExpr.getMethod().getSignature();

        for (String cumMark: CustomCheckRule.customRulesMap.keySet()){
            if (CustomCheckRule.customRulesMap.get(cumMark).contains(methodSig)){
                LinkedHashSet<Integer> controllableParams = CustomCheckRule.getControllableParams(cumMark, methodSig);
                for (Integer parmInd: controllableParams){
                    ValueBox tmpValueBox = RuleUtils.getValueBoxByParamIndex((Stmt) tfNode.node.unit, parmInd);
//                    Value tmpValue = RuleUtils.getValueByParamIndex((Stmt) tfNode.node.unit, parmInd);
                    HashSet<SourceNode> controllableValues = RuleUtils.getTaintedFieldSourceNodesViaHeuristic(
                            tmpValueBox, tfNode, new LinkedList<>(gadgetInfosRecord.gadgets.subList(0,gadgetInfosRecord.gadgets.size()-1)), descriptor, gadgetInfosRecord);
                    if (controllableValues.isEmpty()) {
                        return;
                    }
                    RuleUtils.tryHeuristicSourceMatching(descriptor, RuleUtils.getValueBoxByParamIndex((Stmt) tfNode.node.unit, parmInd), tfNode,gadgetInfosRecord.gadgets);
                    sinkNode.controllableSinkValues.put(parmInd, controllableValues);
                }

                if (cumMark.equals("fastjson") && !sinkNode.controllableSinkValues.isEmpty()){
                    sinkNode.sinkType = SinkType.INVOKE;
                    sinkNode.sinkObject = sinkNode.controllableSinkValues.get(1).iterator().next();
                    sinkNode.sinkMethod = sinkNode.controllableSinkValues.get(1).iterator().next(); // 由对象所具有的fields决定，攻击者无法完全控制调用的方法
                }
            }
        }
        if (!sinkNode.controllableSinkValues.isEmpty()){
            gadgetInfosRecord.flag = true;
            gadgetInfosRecord.addSinkNode(sinkNode);

            log.info("[Custom] SootMethod: "+tfNode.method);
            log.info("[Custom] TransformableNode: "+tfNode);
            log.info("[Custom] controlledValue : "+sinkNode.controllableSinkValues);
        }
    }

    public static void applyJNDI(MethodDescriptor descriptor,
                                   GadgetInfoRecord gadgetInfoRecord,
                                   TransformableNode tfNode) {
        InvokeExpr invokeExpr = tfNode.getUnitInvokeExpr();
        SinkNode sinkNode = new SinkNode(tfNode.node, descriptor.getCurrentClass(), gadgetInfoRecord.sinkType);
        ValueBox valueBox = null;
        Integer paramIndex = null;
        String methodSig = invokeExpr.getMethod().getSignature();
        if (JNDICheckRule.riskyJNDIMethodsSig.contains(methodSig)){
            valueBox = invokeExpr.getArgBox(0);
            paramIndex = 0;
        }
        else if (JNDICheckRule.riskySPIMethodSig.contains(methodSig)){
            valueBox = invokeExpr.getArgBox(1);
            paramIndex = 1;
        }
        else if (JNDICheckRule.riskyConnectInputMethodSig.contains(methodSig)){
            valueBox = Parameter.getThisValueBox(tfNode.node);
            paramIndex = -1;
        }else if (JNDICheckRule.riskyNDSMethodSig.contains(methodSig)){
            valueBox = Parameter.getArgByType(invokeExpr, "java.lang.String");
            paramIndex = Parameter.getArgIndexByValue(invokeExpr, tfNode, valueBox.getValue());
        }else if (JNDICheckRule.remoteLinkMethodsSig.contains(methodSig)){
            valueBox = Parameter.getThisValueBox(tfNode.node);
            paramIndex = -1;
        }

        if (valueBox != null && paramIndex != null) {
            sinkNode.controllableSinkValues.put(paramIndex,
                    RuleUtils.getTaintedFieldSources(valueBox.getValue(), descriptor));
        }

        if (sinkNode.controllableSinkValues.containsKey(paramIndex)
                && !sinkNode.controllableSinkValues.get(paramIndex).isEmpty()){
            gadgetInfoRecord.flag = true;

            ValueBox thisValueBox = Parameter.getThisValueBox(tfNode.node);
            if (paramIndex != -1 && thisValueBox != null
                    && Utils.isTainted(thisValueBox.getValue(), descriptor.taints)){
                HashSet<SourceNode> thisSources = RuleUtils.getTaintedFieldSources(thisValueBox.getValue(), descriptor);
                sinkNode.controllableSinkValues.put(-1, thisSources);
            }
            gadgetInfoRecord.addSinkNode(sinkNode);

            log.info("[JNDI] SootMethod: "+tfNode.method);
            log.info("[JNDI] TransformableNode: "+tfNode);
            log.info("[JNDI] controlledValue : "+sinkNode.controllableSinkValues);
        }
    }

    public static void applyLoadClass(MethodDescriptor descriptor,
                                      GadgetInfoRecord gadgetInfoRecord,
                                      TransformableNode tfNode){
        InvokeExpr invokeExpr = tfNode.getUnitInvokeExpr();

        SinkNode sinkNode = new SinkNode(tfNode.node, descriptor.getCurrentClass(), gadgetInfoRecord.sinkType);
        ValueBox testArg = Parameter.getArgByType(invokeExpr,"byte[]");
        if (testArg != null){
            sinkNode.controllableSinkValues.put(invokeExpr.getArgs().indexOf(testArg.getValue()),
                    RuleUtils.getTaintedFieldSourcesViaAF(testArg.getValue(), gadgetInfoRecord, descriptor));
        }

        if (!sinkNode.controllableSinkValues.isEmpty()) {
            gadgetInfoRecord.flag = true;
            gadgetInfoRecord.addSinkNode(sinkNode);

            log.info("[ClassLoad] SootMethod: "+tfNode.method);
            log.info("[ClassLoad] TransformableNode: "+tfNode);
            log.info("[ClassLoad] controlledValue : "+sinkNode.controllableSinkValues);
        }
    }

    public static void applyInvoke(MethodDescriptor descriptor,
                                   GadgetInfoRecord gadgetInfoRecord,
                                   TransformableNode tfNode){

        InvokeExpr invokeExpr = tfNode.getUnitInvokeExpr();

        // 解析 invoke 方法名应该设置在哪个对象
        HashSet<SinkNode> sinkNodes = new HashSet<>();

        ValueBox methodValueBox = Parameter.getThisValueBox(tfNode.node);
        if (methodValueBox != null){
            HashSet<SourceNode> sinkMethodSources = RuleUtils.getTaintedFieldSourcesViaAF(methodValueBox.getValue(),gadgetInfoRecord, descriptor);
            for (SourceNode sinkSourceNode: sinkMethodSources){
                if (!Utils.isBasicType(sinkSourceNode.getType())) {
                    SinkNode sinkNode = new SinkNode(tfNode.node, descriptor.getCurrentClass(), gadgetInfoRecord.sinkType);
                    sinkNodes.add(sinkNode);
                    sinkNode.sinkMethod = sinkSourceNode;
                }else if (sinkSourceNode.getType().toString().equals("java.lang.String")){
                    SinkNode sinkNode = new SinkNode(tfNode.node, descriptor.getCurrentClass(), gadgetInfoRecord.sinkType);
                    sinkNodes.add(sinkNode);
                    sinkNode.sinkMethodName = sinkSourceNode;
                }
            }
        }

        // 解析 invoke 方法所属的类对象
        Value objValue = invokeExpr.getArg(0);
        HashSet<SourceNode> sinkObjectSources = RuleUtils.getTaintedFieldSourcesViaAF(objValue,gadgetInfoRecord, descriptor);

        HashSet<SinkNode> tmpSinkNodes = new HashSet<>(sinkNodes);
        sinkNodes.clear();
        for (SinkNode tmpSinkNode: tmpSinkNodes){
            for (SourceNode objSourceNode: sinkObjectSources){
                SinkNode newSinkNode = new SinkNode(tmpSinkNode.node, tmpSinkNode.sootClass, tmpSinkNode.sinkType);
                newSinkNode.sinkMethodName = tmpSinkNode.sinkMethodName;
                newSinkNode.sinkMethod = tmpSinkNode.sinkMethod;
                newSinkNode.sinkObject = objSourceNode;
                sinkNodes.add(newSinkNode);
            }
        }

        for (SinkNode sinkNode: sinkNodes) {
            if (sinkNode.sinkObject == null)
                continue;
            if (sinkNode.sinkMethod == null & sinkNode.sinkMethodName == null)
                continue;

            gadgetInfoRecord.flag = true;
            gadgetInfoRecord.addSinkNode(sinkNode);

            log.info("[Invoke] SootMethod: "+tfNode.method);
            log.info("[Invoke] TransformableNode: "+tfNode);
            log.info("[Invoke] sinkClassBelongTo : "+sinkNode.sinkObject);
            log.info("[Invoke] sinkMethodName : "+sinkNode.sinkMethodName);
            log.info("[Invoke] sinkMethod : "+sinkNode.sinkMethod);
        }
    }


    public static void applyExec(MethodDescriptor descriptor,
                                 GadgetInfoRecord gadgetInfoRecord,
                                 TransformableNode tfNode){
        InvokeExpr invokeExpr = tfNode.getUnitInvokeExpr();

        SinkNode sinkNode = new SinkNode(tfNode.node,descriptor.getCurrentClass(),gadgetInfoRecord.sinkType);
        ValueBox testArg = invokeExpr.getArgBox(0);
        sinkNode.controllableSinkValues.put(0,
                RuleUtils.getTaintedFieldSourcesViaAF(testArg.getValue(),gadgetInfoRecord, descriptor));

        if (sinkNode.controllableSinkValues.containsKey(0)
                && !sinkNode.controllableSinkValues.get(0).isEmpty()) {
            gadgetInfoRecord.flag = true;
            gadgetInfoRecord.addSinkNode(sinkNode);

            log.info("[EXEC] SootMethod: " + tfNode.method);
            log.info("[EXEC] TransformableNode: " + tfNode);
            log.info("[EXEC] controlledValue : " + sinkNode.controllableSinkValues);
        }
    }

    public static void applyWriteFile(MethodDescriptor descriptor,
                                      GadgetInfoRecord gadgetInfoRecord,
                                      TransformableNode tfNode){
        InvokeExpr currentInvokeExpr = tfNode.getUnitInvokeExpr();

        Value contentValue = currentInvokeExpr.getArg(0);
        ValueBox thisValueBox = Parameter.getThisValueBox(tfNode.node);
        if (thisValueBox == null)   return;

        if (!Utils.isTainted(thisValueBox.getValue(), descriptor.taints))
            return;
        HashSet<SinkNode> sinkNodes = new HashSet<>();
        HashSet<SourceNode> sinkFileContentsSourceNodes = RuleUtils.getTaintedFieldSourcesViaAF(contentValue, gadgetInfoRecord, descriptor);
        for (SourceNode fileContentSourceNode: sinkFileContentsSourceNodes){
            if (!Utils.isBasicType(fileContentSourceNode.getType())) {
                SinkNode sinkNode = new SinkNode(tfNode.node, descriptor.getCurrentClass(), SinkType.FILE);
                sinkNode.sinkFileContent = fileContentSourceNode;
                sinkNodes.add(sinkNode);
            }
        }

        HashSet<SourceNode> sinkFilePathSourceNodes = RuleUtils.getTaintedFieldSourcesViaAF(thisValueBox.getValue(), gadgetInfoRecord, descriptor);
        for (SinkNode sinkNode : sinkNodes) {
            for (SourceNode pathSourceNode : sinkFilePathSourceNodes) {
                if (pathSourceNode.getType().toString().equals("java.lang.String")
                        || pathSourceNode.getType().toString().equals("java.lang.Object")
                        || FileCheckRule.fileClassNames.contains(pathSourceNode.getType().toString())) {
                    sinkNode.sinkFilePath.add(pathSourceNode);
                }
            }
        }

        for (SinkNode sinkNode : sinkNodes){
            if (sinkNode.sinkFileContent == null | sinkNode.sinkFilePath.isEmpty())
                continue;
            gadgetInfoRecord.flag = true;
            gadgetInfoRecord.addSinkNode(sinkNode);

            log.info("[FILE] SootMethod: "+tfNode.method);
            log.info("[FILE] TransformableNode: "+tfNode);
            log.info("[FILE] sinkFileContent : "+sinkNode.sinkFileContent);
            log.info("[FILE] sinkFilePath : "+sinkNode.sinkFilePath);
        }
    }


    public static void applySecodDes(MethodDescriptor descriptor,
                                     GadgetInfoRecord gadgetInfosRecord,
                                     TransformableNode transformableNode){
        SinkNode sinkNode = new SinkNode(transformableNode.node,descriptor.getCurrentClass(),gadgetInfosRecord.sinkType);
        ValueBox thisValue = Parameter.getThisValueBox(transformableNode.node);
        if (thisValue != null){
            HashSet<SourceNode> sourceNodes = RuleUtils.getTaintedFieldSourcesViaAF(thisValue.getValue(), gadgetInfosRecord, descriptor);
            for (SourceNode sourceNode: sourceNodes){
                if (sourceNode.getType().toString().equals("byte[]")) {
                    if (!sinkNode.controllableSinkValues.containsKey(-1))
                        sinkNode.controllableSinkValues.put(-1, new HashSet<>());
                    sinkNode.controllableSinkValues.get(-1).add(sourceNode);
                }
            }
        }

        if (!sinkNode.controllableSinkValues.containsKey(-1)
                && !sinkNode.controllableSinkValues.get(-1).isEmpty()) {
            gadgetInfosRecord.flag = true;
            gadgetInfosRecord.addSinkNode(sinkNode);

            log.info("[SECODDES] SootMethod: " + transformableNode.method);
            log.info("[SECODDES] TransformableNode: " + transformableNode);
            log.info("[SECODDES] controlledValue : " + sinkNode.controllableSinkValues);
        }
    }

}
