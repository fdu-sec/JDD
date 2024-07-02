package rules.sinks;

import tranModel.Transformable;
import tranModel.TransformableNode;
import cfg.Node;
import config.RegularConfig;
import container.FragmentsContainer;
import dataflow.node.MethodDescriptor;
import gadgets.unit.RecordUtils;
import markers.SinkType;
import soot.SootMethod;
import soot.Value;
import soot.ValueBox;
import soot.jimple.InvokeExpr;
import util.ClassRelationshipUtils;
import util.DataSaveLoadUtil;
import util.StaticAnalyzeUtils.Parameter;
import util.Utils;


import java.io.IOException;
import java.util.*;

/**
 * 通过ClassLoader加载恶意类导致RCE攻击检测
 * (1) ClassLoader.defineClass : Class clazz = ClassLoader.defineClass -> clazz.newInstance
 * (2) URLClassLoader : URLClassLoader urlClassLoader = URLClassLoader(new URL[], ...)
 *                   -> Class clazz = Class.forName(String name, boolean initialize, *ClassLoader loader) / urlClassLoader.loadClass(String name)
 *                   -> clazz.newInstance()
 */
public class ClassLoaderCheckRule extends AbstractCheckRule {

    public static LinkedHashMap<String,HashSet<String>> classLoaderRiskyMethodSigs = new LinkedHashMap<>();

    public static List<String> newInstanceMethodSigs = Arrays.asList(
            "<java.lang.Class: java.lang.Object newInstance()>",
            "<java.lang.reflect.Constructor: java.lang.Object newInstance(java.lang.Object[])>");
    public static HashSet<LinkedList<SootMethod>> callStacksRecord = new HashSet<>();

    public ClassLoaderCheckRule(){
        sinkType = SinkType.LOAD_CLASS;
    }

    public static void init() {
        callStacksRecord.clear();
        classLoaderRiskyMethodSigs.put("ClassLoader.defineClass", ClassRelationshipUtils.getAllSubMethodSigs(Arrays.asList("java.lang.ClassLoader"),"(defineClass)"));
        /** 进行一次参数筛选，否则会在verify时遗漏 */
        HashSet<String> toDelete = new HashSet<>();
        for (String methodSig : classLoaderRiskyMethodSigs.get("ClassLoader.defineClass")){
            if (!methodSig.contains("byte[]"))
                toDelete.add(methodSig);
        }
        for (String methodSig: toDelete){
            classLoaderRiskyMethodSigs.get("ClassLoader.defineClass").remove(methodSig);
        }
        classLoaderRiskyMethodSigs.put("URLClassLoader.<init>", ClassRelationshipUtils.getAllSubMethodSigs(Arrays.asList("java.net.URLClassLoader"),"(<init>)"));
        classLoaderRiskyMethodSigs.put("URLClassLoader.loadClass",ClassRelationshipUtils.getAllSubMethodSigs(Arrays.asList("java.net.URLClassLoader"),"(loadClass)"));
        classLoaderRiskyMethodSigs.put("Class.forName",ClassRelationshipUtils.getAllSubMethodSigs(Arrays.asList("java.lang.Class"),"(forName)"));

    }

    @Override
    public void apply(MethodDescriptor descriptor, LinkedList<SootMethod> callStack, Transformable transformable) throws IOException {
        TransformableNode tfNode = (TransformableNode) transformable;
        if (!tfNode.containsInvoke())   return;
        super.isClassLoadGadget = true;

        if (checkRisky(descriptor,tfNode)){
            SootMethod currentInvokedMethod = tfNode.getUnitInvokeExpr().getMethod();
            callStack.add(currentInvokedMethod);
            if (!super.checkGadgetDuplication(callStack, sinkType)){
                FragmentsContainer.updateSinkFragment(callStack,sinkType, tfNode, descriptor);
//                DataSaveLoadUtil.recordCallStackToFile(callStack, sinkType,
//                        RegularConfig.outputDir + "/gadgets/interInfos/" + sinkType.toString() + "SinkFragments.txt",
//                        true);
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
        InvokeExpr currentInvokeExpr = tfNode.getUnitInvokeExpr();
        String currentMethodSig = currentInvokeExpr.getMethod().getSignature();
        Node currentCFGNode = tfNode.node;

        ValueBox testArg = null;
        if (classLoaderRiskyMethodSigs.get("ClassLoader.defineClass")
                .contains(currentMethodSig)){
            // 要创建的类的内容需要可控
            testArg = Parameter.getArgByType(currentInvokeExpr,"byte[]");

            if (testArg != null){
                risky = descriptor.addTaint(testArg.getValue(), Parameter.getReturnedValueBox(currentCFGNode));
            }
            if (risky){ // 记录污点来源, 在生成Sink Fragments时填充必要的信息
                RecordUtils.recordTaintedArgs(descriptor, testArg.getValue(), sinkType, tfNode);
            }
        }
        else if (classLoaderRiskyMethodSigs.get("URLClassLoader.<init>").contains(currentMethodSig)){
            testArg = Parameter.getArgByType(currentInvokeExpr,"java.net.URL[]");

            if (testArg != null){
                risky = descriptor.addTaint(testArg.getValue(), Parameter.getThisValueBox(currentCFGNode));
            }
            if (risky){ // 记录污点来源, 在生成Sink Fragments时填充必要的信息
                RecordUtils.recordTaintedArgs(descriptor, testArg.getValue(), sinkType, tfNode);
            }
        }
        else if (classLoaderRiskyMethodSigs.get("URLClassLoader.loadClass").contains(currentMethodSig)){
            testArg = Parameter.getThisValueBox(currentCFGNode);
            if (testArg != null){
                risky = descriptor.addTaint(testArg.getValue(), Parameter.getReturnedValueBox(currentCFGNode));
            }
            if (risky){ // 记录污点来源, 在生成Sink Fragments时填充必要的信息
                RecordUtils.recordTaintedArgs(descriptor, testArg.getValue(), sinkType, tfNode);
            }

        }
        else if (classLoaderRiskyMethodSigs.get("Class.forName").contains(currentMethodSig)){
            testArg = Parameter.getArgByType(currentInvokeExpr,"java.lang.ClassLoader");

            if (testArg != null){
                System.out.println(currentInvokeExpr.getArg(1));
                risky = descriptor.addTaint(testArg.getValue(), Parameter.getReturnedValueBox(currentCFGNode));
                risky  = Utils.isTainted(currentInvokeExpr.getArg(0), descriptor.taints)
                        & risky & currentInvokeExpr.getArg(1).toString().equals("true");
            }
            if (risky){
                HashSet<Value> taintedValues = new HashSet<>();
                taintedValues.add(testArg.getValue());
                taintedValues.add(currentInvokeExpr.getArg(0));
                RecordUtils.recordTaintedArgs(descriptor, taintedValues, sinkType, tfNode);
            }
        }

        return risky;
    }

    @Override
    public boolean isSinkMethod(SootMethod mtd) {
        String methodSig = mtd.getSignature();
        for (String key: classLoaderRiskyMethodSigs.keySet()){
            if (classLoaderRiskyMethodSigs.get(key).contains(methodSig))
                return true;
        }
        return false;
    }
}
