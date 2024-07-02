package dataflow.node;

import tranModel.Taint.Taint;
import util.Pair;
import soot.SootClass;
import soot.SootFieldRef;
import soot.SootMethod;
import soot.Value;

import java.util.HashMap;
import java.util.LinkedHashMap;


public class UndeterminedFieldNode {
    LinkedHashMap<Value, Pair<SootMethod, SootClass>> undeterminedLocalValues = new LinkedHashMap<>();
    HashMap<Value, Pair<SootMethod, Value>> interValueRela = new HashMap<>();


    public void updateSourceOfFields(Taint taint,
                                     MethodDescriptor descriptor,
                                     SootFieldRef sootFieldRef){
        for (Taint ailasTaint: taint.aliases){
            // 仅记录accessPath.isEmpty()的, 因为在field graph构建时不考虑fields之间污染的情况, 而别名为field可能属于fields之间影响
            if (!ailasTaint.accessPath.isEmpty())
                continue;

            for (Value value: undeterminedLocalValues.keySet()){
                if (!value.equals(ailasTaint.object))
                    continue;
                Pair<SootMethod, SootClass> pair = undeterminedLocalValues.get(value);
                if (!descriptor.sootMethod.equals(pair.getKey()))
                    continue;
                if (!descriptor.getCurrentClass().equals(pair.getValue()))
                    continue;


            }
        }
    }
}
