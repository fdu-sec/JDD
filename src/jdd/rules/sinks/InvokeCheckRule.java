package rules.sinks;

import PointToAnalyze.pointer.Pointer;
import container.FieldsContainer;
import tranModel.Rules.RuleUtils;
import tranModel.Transformable;
import tranModel.TransformableNode;

import config.RegularConfig;
import container.FragmentsContainer;
import dataflow.node.MethodDescriptor;
import gadgets.unit.RecordUtils;
import lombok.extern.slf4j.Slf4j;
import markers.SinkType;
import soot.SootMethod;
import soot.Value;
import soot.ValueBox;
import soot.jimple.InvokeExpr;
import util.DataSaveLoadUtil;
import util.StaticAnalyzeUtils.FieldUtil;
import util.StaticAnalyzeUtils.Parameter;
import util.Utils;

import java.io.IOException;
import java.util.*;

@Slf4j
public class InvokeCheckRule extends AbstractCheckRule {
    public static List<String> invokeSigs =
            Arrays.asList(
                    "<java.lang.reflect.Method: java.lang.Object invoke(java.lang.Object,java.lang.Object[])>",
                    "<sun.reflect.misc.MethodUtil: java.lang.Object invoke(java.lang.reflect.Method,java.lang.Object,java.lang.Object[])>"
            );


    public static boolean methodTaintCheck = true;  // 标记是否检测method污染

    public InvokeCheckRule(){
        sinkType = SinkType.INVOKE;
    }

    public static void init(){}

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
        SootMethod currentMtd = invokeExpr.getMethod();
        String currentMtdSig = currentMtd.getSignature();
        HashSet<Value> taintedArgs = new HashSet<>();

        if (invokeSigs.contains(currentMtdSig)){
            ValueBox thisValue = Parameter.getThisValueBox(tfNode.node);
            if (thisValue != null){
                Value thisVal = thisValue.getValue();
                taintedArgs.add(thisVal);
                // 如果method没有被污染，那就直接返回false
                // TODO:  粗筛
                if((!Utils.isTainted(thisVal, descriptor.taints))
                        && methodTaintCheck) { return false; }

                Value arg = invokeExpr.getArg(0);
                taintedArgs.add(arg);
                Pointer pointer = descriptor.pointTable.getPointer(arg);
                String typeStr = "";
                if(pointer != null) {
                    if(pointer.getType() != null) { typeStr = pointer.getType().toString(); }
                    else { typeStr = arg.getType().toString(); }
                    if(!isBasicValidTypeForInvokeObj(typeStr) && !typeStr.equals("java.lang.Class") && !RuleUtils.isGenericType(descriptor, arg)) { return false; }
                }
                risky = Utils.isTainted(arg, descriptor.taints);

                Value arg1 = invokeExpr.getArg(1);
                pointer = descriptor.pointTable.getPointer(arg1);
                typeStr = "";
                if (pointer != null){
                    if(pointer.getType() != null) { typeStr = pointer.getType().toString(); }
                    else { typeStr = arg1.getType().toString(); }
                    if (!isBasicValidTypeForInvokeObj(typeStr) && !typeStr.contains("null") & !arg1.getType().toString().equals("java.lang.Object[]")/* && !Utils.isBasicType(typeStr)*/)   {return false;}
                }

                // 检查是否为static field


            }else {
                Value mtdValue = invokeExpr.getArg(0);
                Value objValue = invokeExpr.getArg(1);
                Value paramsValue = invokeExpr.getArg(2);
                taintedArgs.add(mtdValue);
                taintedArgs.add(objValue);

                if (Utils.isTainted(mtdValue, descriptor.taints)
                        & Utils.isTainted(objValue, descriptor.taints)){
                    Pointer pointer = descriptor.pointTable.getPointer(objValue);
                    String typeStr = "";
                    if(pointer != null) {
                        if(pointer.getType() != null) { typeStr = pointer.getType().toString(); }
                        else { typeStr = objValue.getType().toString(); }
                        if(!typeStr.equals("java.lang.Object") && !typeStr.equals("java.lang.Class")) { return false; }
                    }

                    pointer = descriptor.pointTable.getPointer(paramsValue);
                    typeStr = "";
                    if (pointer != null){
                        if(pointer.getType() != null) { typeStr = pointer.getType().toString(); }
                        else { typeStr = paramsValue.getType().toString(); }
                        if (!isBasicValidTypeForInvokeObj(typeStr) && !typeStr.contains("null")/* && !Utils.isBasicType(typeStr)*/)   {return false;}
                    }
                    risky = true;
                }
            }
        }

        if (risky ){
            risky = RecordUtils.recordTaintedArgs(descriptor, taintedArgs, sinkType, tfNode);
        }

        return risky;
    }

    @Override
    public boolean isSinkMethod(SootMethod mtd) {
        return invokeSigs.contains(mtd.getSignature());
    }

    public static boolean isBasicValidTypeForInvokeObj(String typeStr){
        if (typeStr.contains("java.lang.Object"))
            return true;
        if (typeStr.contains("java.io.Serializable"))
            return true;
        return false;
    }
}
