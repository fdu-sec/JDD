package rules.sinks;

import tranModel.Transformable;
import tranModel.TransformableNode;
import config.RegularConfig;
import container.FragmentsContainer;
import dataflow.node.MethodDescriptor;
import gadgets.unit.RecordUtils;
import markers.SinkType;
import soot.SootMethod;
import soot.Value;
import soot.jimple.InvokeExpr;
import util.ClassRelationshipUtils;
import util.DataSaveLoadUtil;
import util.StaticAnalyzeUtils.MethodUtil;
import util.StaticAnalyzeUtils.Parameter;
import util.Utils;

import java.io.IOException;
import java.util.HashMap;
import java.util.HashSet;
import java.util.LinkedList;

public class ExecCheckRule extends AbstractCheckRule {
    public static HashSet<String> riskyMethodSigs = new HashSet<>();

    public static boolean isValidType(Value value){
        String typeString = value.getType().toString();
        if (typeString.contains("java.lang.String") )
            return true;
        return false;
    }

    public ExecCheckRule(){
        sinkType = SinkType.EXEC;
    }


    public static void init() {
        riskyMethodSigs.addAll(
                Utils.toStringSet
                        (ClassRelationshipUtils.getMethodsByName(Utils.toSootClass("java.lang.Runtime"), "exec")));
        riskyMethodSigs.addAll(
                Utils.toStringSet(
                        ClassRelationshipUtils.getMethodsByName(Utils.toSootClass("java.lang.ProcessBuilder"), "<init>")));
        riskyMethodSigs.addAll(
                Utils.toStringSet(
                        ClassRelationshipUtils.getMethodsByName(Utils.toSootClass("java.lang.ProcessBuilder"), "<init>")));

        HashSet<SootMethod> possibleSinks = MethodUtil.getMethodBySig("execCmd",3);
        possibleSinks.addAll(MethodUtil.getMethodBySig("exec", 3));
        // 为避免误报，根据人工经验简单添加一些筛选策略
        possibleSinks.removeIf(mtd-> mtd.getParameterCount()!=1
                || Parameter.getArgByType(mtd, "java.lang.String") == null);
        riskyMethodSigs.addAll(Utils.toStringSet(possibleSinks));
    }


    @Override
    public void apply(MethodDescriptor descriptor, LinkedList<SootMethod> callStack, Transformable transformable) throws IOException {
        TransformableNode tfNode = (TransformableNode) transformable;
        if (!tfNode.containsInvoke())   return;

        SootMethod currentInvokedMethod = tfNode.getUnitInvokeExpr().getMethod();
        if (checkRisky(descriptor,tfNode)){
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

    @Override
    public boolean checkRisky(MethodDescriptor descriptor, TransformableNode tfNode){
        boolean risky = false;
        InvokeExpr invokeExpr = tfNode.getUnitInvokeExpr();
        SootMethod sootMethod = invokeExpr.getMethod();

        if (riskyMethodSigs.contains(sootMethod.getSignature())){
            Value arg = invokeExpr.getArg(0);
            risky = Utils.isTainted(arg, descriptor.taints);

            if (risky ){
                RecordUtils.recordTaintedArgs(descriptor, arg, sinkType, tfNode);
            }
        }

        return risky;
    }

    @Override
    public boolean isSinkMethod(SootMethod mtd) {
        return riskyMethodSigs.contains(mtd.getSignature());
    }

}
