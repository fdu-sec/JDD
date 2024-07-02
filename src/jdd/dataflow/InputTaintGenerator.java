package dataflow;

import PointToAnalyze.pointer.Pointer;
import soot.SootClass;
import tranModel.Taint.Taint;
import container.BasicDataContainer;
import dataflow.node.MethodDescriptor;
import soot.SootField;
import soot.SootMethod;

import java.util.*;

public class InputTaintGenerator {

    public void generateTaints(SootMethod method){
        MethodDescriptor descriptor = BasicDataContainer.getOrCreateDescriptor(method);

        if (BasicDataContainer.gadgetParamsGenerate & !method.getName().equals("<init>")){
            LinkedList<SootField> accessPath = new LinkedList<>();
            taintParam(-1, descriptor, accessPath);
        }

        for(int ind = 0; ind < method.getParameterCount(); ind++) {

//            if (ind == 1 & descriptor.isProxyMethodEntry)   continue;
            // gadget方法入口形式参数的污染
            if (BasicDataContainer.gadgetParamsGenerate && BasicDataContainer.isEntryPolluteSelect){
                LinkedList<SootField> accessPath = new LinkedList<>();
                taintParam(ind, descriptor, accessPath);
            }

        }
    }

    public void generateTaints(MethodDescriptor descriptor, SootClass thisClz){
        if (BasicDataContainer.gadgetParamsGenerate & !descriptor.sootMethod.getName().equals("<init>")){
            LinkedList<SootField> accessPath = new LinkedList<>();
            taintParam(-1, descriptor, accessPath);
        }
        if (thisClz != null){
            Pointer thisPointer = new Pointer(thisClz.getType());
            descriptor.paramValInfo.put(-1, thisPointer);
        }

        for(int ind = 0; ind < descriptor.sootMethod.getParameterCount(); ind++) {
//            if (ind == 1 & descriptor.isProxyMethodEntry)   continue;
            // gadget方法入口形式参数的污染
            if (BasicDataContainer.gadgetParamsGenerate){
                LinkedList<SootField> accessPath = new LinkedList<>();
                taintParam(ind, descriptor, accessPath);
            }

        }
    }

    private void taintParam(int index, MethodDescriptor descriptor, LinkedList<SootField> accessPath){
        LinkedList<Taint> taintForThisParam = new LinkedList<>();
        taintForThisParam.add(descriptor.getOrCreateTaint(null, accessPath));
        descriptor.inputParamMapTaints.put(index, taintForThisParam);
    }
}
