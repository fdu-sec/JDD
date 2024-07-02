package PointToAnalyze.pointer;

import tranModel.Taint.Taint;
import dataflow.node.MethodDescriptor;
import markers.RelationShip;
import soot.Value;
import util.ClassRelationshipUtils;
import util.Utils;

import java.util.ArrayList;
import java.util.HashMap;
import java.util.List;

public class PointTable {
    MethodDescriptor descriptor;
    private HashMap<Value, Pointer> map = new HashMap<>();
    private HashMap<Taint, Pointer> taintMap = new HashMap<>();

    public PointTable(MethodDescriptor descriptor){
        this.descriptor = descriptor;
    }

    public boolean contains(Value value){
        return map.containsKey(value);
    }

    public boolean contains(Taint taint){
        if (taint.accessPath.isEmpty())
            return contains(taint.object);
        return taintMap.containsKey(taint);
    }

    public Pointer get(Taint taint) {
        if (taint.accessPath.isEmpty())
            return map.get(taint.object);
        return taintMap.get(taint);
    }


    public void setPointer(Value to, Pointer pointer){
        if (pointer == null)
            return;
        if (pointer.getType() == null)
            return;
        if (map.containsKey(to)){
            Pointer recordedPointer = map.get(to);
            RelationShip relationShip = ClassRelationshipUtils.getExtentRelationshipAmongClasses(
                    Utils.toSootClass(recordedPointer.getType()),
                    Utils.toSootClass(pointer.getType())
                    );
            if (relationShip.equals(RelationShip.SUB))
                return;
            else if (!relationShip.equals(RelationShip.SUPER)
                    & !relationShip.equals(RelationShip.EQUAL)){
                recordedPointer.addExtraType(pointer.getType());
                recordedPointer.addExtraTypes(pointer.getExtraTypes());
                return;
            }
        }
        map.put(to, pointer);
    }

    public void setPointer(Taint to, Pointer pointer){
        if (pointer == null)
            return;
        if (pointer.getType() == null)
            return;
        if (to.accessPath.isEmpty()) {
            setPointer(to.object, pointer);
            return;
        }
        if (taintMap.containsKey(to)){
            Pointer recordedPointer = taintMap.get(to);
            RelationShip relationShip = ClassRelationshipUtils.getExtentRelationshipAmongClasses(
                    Utils.toSootClass(recordedPointer.getType()),
                    Utils.toSootClass(pointer.getType())
            );
            if (relationShip.equals(RelationShip.SUB)
                    | relationShip.equals(RelationShip.NONE)
                    | relationShip.equals(RelationShip.HAS_SAME_SUPER))
                return;
            else if (relationShip.equals(RelationShip.HAS_SAME_SUB)
                    | relationShip.equals(RelationShip.HAS_SAME_SUPER_AND_SUB)){
                recordedPointer.addExtraType(pointer.getType());
                recordedPointer.addExtraTypes(pointer.getExtraTypes());
            }
        }
        taintMap.put(to, pointer);
    }

    public boolean setPointer(Value from, Value to){
        if(!contains(from)) return false;
        Pointer toObj = getPointer(from);
        setPointer(to, toObj);
        return true;
    }

    public boolean setPointer(Taint from, Taint to){
        if(!contains(from)) return false;
        Pointer toObj = get(from);
        setPointer(to, toObj);
        return true;
    }

    public Pointer getPointer(Value value){
        return map.get(value);
    }

    public Pointer getPointer(Taint taint){
        if (taintMap.containsKey(taint))
            return taintMap.get(taint);
        return new Pointer(taint.getType());
    }
}
