package rules.sinks;

import PointToAnalyze.pointer.Pointer;
import config.RegularConfig;
import container.FragmentsContainer;
import dataflow.node.MethodDescriptor;
import gadgets.collection.iocd.unit.instrument.Instruments;
import gadgets.unit.RecordUtils;
import markers.SinkType;
import soot.Scene;
import soot.SootMethod;
import soot.Value;
import soot.ValueBox;
import soot.jimple.InvokeExpr;
import tranModel.Rules.RuleUtils;
import tranModel.Transformable;
import tranModel.TransformableNode;
import util.DataSaveLoadUtil;
import util.Pair;
import util.StaticAnalyzeUtils.Parameter;
import util.Utils;

import java.io.IOException;
import java.util.*;

import static dataflow.DataFlowAnalysisUtils.isDupInvokedMethodInFragment;
import static gadgets.collection.iocd.TransformerUtils.setSinkInstRecord;
import static rules.sinks.InvokeCheckRule.isBasicValidTypeForInvokeObj;

public class CustomCheckRule extends AbstractCheckRule{
    public static HashMap<String, HashSet<String>> customRulesMap = new HashMap<>();

    public static void init(){
        // Groovy
        customRulesMap.put("groovy", new HashSet<>());
        customRulesMap.get("groovy").add("<groovy.lang.Closure: java.lang.Object call()>");
        customRulesMap.get("groovy").add("<groovy.lang.Closure: java.lang.Object call(java.lang.Object[])>");
        customRulesMap.get("groovy").add("<groovy.lang.Closure: java.lang.Object call(java.lang.Object)>");

        // Bsh
        customRulesMap.put("Bsh", new HashSet<>());
        customRulesMap.get("Bsh").add("<bsh.BshMethod: java.lang.Object invoke(java.lang.Object[],bsh.Interpreter,bsh.CallStack,bsh.SimpleNode)>");
        customRulesMap.get("Bsh").add("<bsh.BshMethod: java.lang.Object invoke(java.lang.Object[],bsh.Interpreter,bsh.CallStack,bsh.SimpleNode,boolean)>");
        // Myface
        customRulesMap.put("Myface", new HashSet<>());
        customRulesMap.get("Myface").add("<javax.el.ValueExpression: java.lang.Object getValue(javax.el.ELContext)>");

        // checkClojure
        customRulesMap.put("checkClojure", new HashSet<>());
        customRulesMap.get("checkClojure").add("<clojure.main$eval_opt: java.lang.Object invokeStatic(java.lang.Object)>");

        // fastjson
        customRulesMap.put("fastjson", new HashSet<>());
        for (SootMethod mtd: Scene.v().getMethodNumberer()){
            if (mtd.getName().equals("write")
                    && mtd.getDeclaringClass().getName().contains("Object")
                    && mtd.getSignature().contains("fastjson")
                    && mtd.getParameterCount()>1
                    && mtd.getParameterType(1).toString().equals("java.lang.Object")){
                customRulesMap.get("fastjson").add(mtd.getSignature());
            }
        }
    }

    public CustomCheckRule(){
        sinkType = SinkType.CUSTOM;
    }

    @Override
    public boolean checkRisky(MethodDescriptor descriptor, TransformableNode tfNode){
        boolean risky = false;
        for (String cumMark : customRulesMap.keySet()){
            switch (cumMark){
                case "groovy":
                    if (checkRiskyForGroovy(cumMark, descriptor, tfNode)) {
                        risky = true;
                        break;
                    }
                case "Bsh":
                    if (checkRiskyForBsh(cumMark, descriptor, tfNode)) {
                        risky = true;
                        break;
                    }
                case "Myface":
                    if (checkRiskyForMyface(cumMark, descriptor, tfNode)){
                        risky = true;
                        break;
                    }
                case "checkClojure":
                    if (checkRiskyForClojure(cumMark, descriptor, tfNode)){
                        risky = true;
                        break;
                    }
                case "fastjson":
                    if (checkRiskyForJsonWrite(cumMark, descriptor, tfNode)){
                        risky = true; break;
                    }
            }
        }


        return risky;
    }

    private boolean checkRiskyForJsonWrite(String cumMark, MethodDescriptor descriptor, TransformableNode tfNode) {
        boolean risky = false;
        InvokeExpr invokeExpr = tfNode.getUnitInvokeExpr();
        SootMethod sootMethod = invokeExpr.getMethod();

        if (customRulesMap.get(cumMark).contains(sootMethod.getSignature())){
            Value objValue = invokeExpr.getArg(1);
            risky = Utils.isTainted(objValue, descriptor.taints);

            Pointer pointer = descriptor.pointTable.getPointer(objValue);
            String typeStr = "";
            if (pointer != null){
                if(pointer.getType() != null) { typeStr = pointer.getType().toString(); }
                else { typeStr = objValue.getType().toString(); }
                if(!isBasicValidTypeForInvokeObj(typeStr) && !typeStr.equals("java.lang.Class") && !RuleUtils.isGenericType(descriptor, objValue)) { return false; }
            }

            if (risky){
                HashSet<Value> taintedArgs = new HashSet<>();
                taintedArgs.add(objValue);
                risky = RecordUtils.recordTaintedArgs(descriptor, taintedArgs, sinkType, tfNode);
            }
        }
        return risky;
    }

    private boolean checkRiskyForClojure(String cumMark, MethodDescriptor descriptor, TransformableNode tfNode) {
        boolean risky = false;
        InvokeExpr invokeExpr = tfNode.getUnitInvokeExpr();
        SootMethod sootMethod = invokeExpr.getMethod();
        String methodSig = sootMethod.getSignature();

        if (customRulesMap.get(cumMark).contains(methodSig)){
            ValueBox thisValueBox = Parameter.getThisValueBox(tfNode.node);
            if (thisValueBox == null)
                return false;

            Value arg0 = invokeExpr.getArg(0);
            risky = Utils.isTainted(thisValueBox.getValue(), descriptor.taints)
                    && Utils.isTainted(arg0, descriptor.taints);

            if (risky){
                HashSet<Value> taintedArgs = new HashSet<>();
                taintedArgs.add(thisValueBox.getValue());
                taintedArgs.add(arg0);
//                sinkType = SinkType.CUSTOM_Clojure;
                risky = RecordUtils.recordTaintedArgs(descriptor, taintedArgs, sinkType, tfNode);
            }
        }
        return risky;
    }

    private boolean checkRiskyForMyface(String cumMark, MethodDescriptor descriptor, TransformableNode tfNode) {
        boolean risky = false;
        InvokeExpr invokeExpr = tfNode.getUnitInvokeExpr();
        SootMethod sootMethod = invokeExpr.getMethod();
        String methodSig = sootMethod.getSignature();

        if (customRulesMap.get(cumMark).contains(methodSig)){
            ValueBox thisValueBox = Parameter.getThisValueBox(tfNode.node);
            if (thisValueBox == null)
                return false;

            risky = Utils.isTainted(thisValueBox.getValue(), descriptor.taints);

            if (risky){
//                sinkType = SinkType.CUSTOM_MyFace;
                risky = RecordUtils.recordTaintedArgs(descriptor, thisValueBox.getValue(), sinkType, tfNode);
            }
        }
        return risky;
    }

    public boolean checkRiskyForBsh(String cumMark, MethodDescriptor descriptor, TransformableNode tfNode){
        boolean risky = false;
        InvokeExpr invokeExpr = tfNode.getUnitInvokeExpr();
        SootMethod sootMethod = invokeExpr.getMethod();
        String methodSig = sootMethod.getSignature();

        if (customRulesMap.get(cumMark).contains(methodSig)){
            if (methodSig.contains("bsh.BshMethod")) {
                ValueBox thisValueBox = Parameter.getThisValueBox(tfNode.node);
                if (thisValueBox == null)
                    return false;

                risky = Utils.isTainted(thisValueBox.getValue(), descriptor.taints) && Utils.isTainted(thisValueBox.getValue(), descriptor.taints);
                RecordUtils.recordTaintedArgs(descriptor, thisValueBox.getValue(), sinkType, tfNode);
            }else if (methodSig.contains("bsh.Reflect:")){
                Value argValue_0 = invokeExpr.getArg(0);
                Value argValue_1 = invokeExpr.getArg(1);

                if (argValue_0 == null || argValue_1 == null)
                    return false;

                HashSet<Value> taintedValues = new HashSet<>();
                taintedValues.add(argValue_0);
                taintedValues.add(argValue_1);

                risky = Utils.isTainted(argValue_0, descriptor.taints) && Utils.isTainted(argValue_1, descriptor.taints);
                if (risky) {
                    risky = RecordUtils.recordTaintedArgs(descriptor, taintedValues, sinkType, tfNode);
                }
            }
        }
        return risky;
    }
    public boolean checkRiskyForGroovy(String cumMark, MethodDescriptor descriptor, TransformableNode tfNode){
        boolean risky = false;
        InvokeExpr invokeExpr = tfNode.getUnitInvokeExpr();
        SootMethod sootMethod = invokeExpr.getMethod();
        String methodSig = sootMethod.getSignature();

        if (customRulesMap.get(cumMark).contains(methodSig)){
            ValueBox thisValueBox = Parameter.getThisValueBox(tfNode.node);
            if (thisValueBox != null) {
                risky = Utils.isTainted(thisValueBox.getValue(), descriptor.taints);
                Pointer pointer = descriptor.pointTable.getPointer(thisValueBox.getValue());
                if (pointer != null & risky){
                    if (!pointer.getType().toString().equals("groovy.lang.Closure")
                            & !pointer.getType().toString().equals("org.codehaus.groovy.runtime.MethodClosure"))
                        risky = false;
                }
                if (risky) {
//                    sinkType = SinkType.CUSTOM_Groovy;
                    risky = RecordUtils.recordTaintedArgs(descriptor, thisValueBox.getValue(), sinkType, tfNode);
                }
            }
        }

        return risky;
    }

    public void apply(MethodDescriptor descriptor, LinkedList<SootMethod> callStack, Transformable transformable) throws IOException {
        TransformableNode tfNode = (TransformableNode) transformable;
        if (!tfNode.containsInvoke())   return;

        SootMethod currentInvokedMethod = tfNode.getUnitInvokeExpr().getMethod();
        if (checkRisky(descriptor,tfNode) && !isDupInvokedMethodInFragment(currentInvokedMethod, callStack)){
            callStack.add(currentInvokedMethod);
            if (!super.checkGadgetDuplication(callStack, sinkType)){
                FragmentsContainer.updateSinkFragment(callStack,sinkType, tfNode, descriptor);
                DataSaveLoadUtil.recordCallStackToFile(callStack, sinkType,
                        RegularConfig.outputDir + "/gadgets/interInfos/" +"GadgetChains.txt",
                        true);
            }
            callStack.remove(currentInvokedMethod);
        }
    }

    public static LinkedHashSet<Integer> getControllableParams(String cumMark, String methodSig){
        LinkedHashSet<Integer> controllableParams = new LinkedHashSet<>();
        switch (cumMark){
            case "groovy":
                controllableParams.add(-1);
                break;

            case "Bsh":
                if (methodSig.contains("bsh.BshMethod")) {
                    controllableParams.add(-1);
                    controllableParams.add(0);
                }else if (methodSig.contains("bsh.Reflect:")){
                    controllableParams.add(0);
                    controllableParams.add(1);
                }
                break;
            case "Myface":
                controllableParams.add(-1);
                break;

            case "checkClojure":
               controllableParams.add(0);
               controllableParams.add(-1);
               break;

            case "fastjson":
                controllableParams.add(1);
                break;
        }

        return controllableParams;
    }

    @Override
    public boolean isSinkMethod(SootMethod mtd) {
        String methodSig = mtd.getSignature();
        for (String cumMark: customRulesMap.keySet()){
            if (customRulesMap.get(cumMark).contains(methodSig))
                return true;
        }

        return false;
    }

    public static void setSinksInstRecord(Instruments instruments){
        if (customRulesMap.containsKey("groovy")){
            for (String methodSig: customRulesMap.get("groovy")){
                try {
                    if (!Scene.v().containsMethod(methodSig))
                        continue;
                    SootMethod sootMethod = Scene.v().getMethod(methodSig);
                    if (sootMethod == null)
                        continue;

                    setSinkInstRecord(sootMethod, true, Arrays.asList(-1),instruments);
                } catch (Exception e) {
                    continue;
                }

            }
        }

        if (customRulesMap.containsKey("fastjson")){
            for (String methodSig: customRulesMap.get("fastjson")){
                try {
                    if (!Scene.v().containsMethod(methodSig))
                        continue;
                    SootMethod sootMethod = Scene.v().getMethod(methodSig);
                    if (sootMethod == null)
                        continue;

                    setSinkInstRecord(sootMethod, true, Arrays.asList(1),instruments);
                } catch (Exception e) {
                    continue;
                }

            }
        }

        if (customRulesMap.containsKey("Myface")){
            for (String methodSig: customRulesMap.get("Myface")){
                try {
                    if (!Scene.v().containsMethod(methodSig))
                        continue;

                    SootMethod sootMethod = Scene.v().getMethod(methodSig);
                    if (sootMethod == null)
                        continue;

                    setSinkInstRecord(sootMethod, true, Arrays.asList(-1,0),instruments);
                }catch (Exception e){
                    continue;
                }
            }
        }

        if (customRulesMap.containsKey("Myface")){
            for (String methodSig: customRulesMap.get("Myface")){
                try {
                    if (!Scene.v().containsMethod(methodSig))
                        continue;

                    SootMethod sootMethod = Scene.v().getMethod(methodSig);
                    if (sootMethod == null)
                        continue;

                    setSinkInstRecord(sootMethod, true, Arrays.asList(-1,0),instruments);
                }catch (Exception e){
                    continue;
                }
            }
        }

        if (customRulesMap.containsKey("Bsh")){
            for (String methodSig: customRulesMap.get("Bsh")){
                try {
                    if (!Scene.v().containsMethod(methodSig))
                        continue;

                    SootMethod sootMethod = Scene.v().getMethod(methodSig);
                    if (sootMethod == null)
                        continue;
                    if (methodSig.contains("bsh.BshMethod")) {
                        setSinkInstRecord(sootMethod, true, Arrays.asList(-1,0), instruments);
                    }else if (methodSig.contains("bsh.Reflect:")){
                        setSinkInstRecord(sootMethod, true, Arrays.asList(0,1), instruments);
                    }
                }catch (Exception e){
                    continue;
                }
            }
        }
    }
}
