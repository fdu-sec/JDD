package PointToAnalyze.pointer;

import lombok.Getter;
import lombok.Setter;
import markers.RelationShip;
import soot.RefType;
import soot.SootClass;
import soot.Type;
import soot.Value;
import util.ClassRelationshipUtils;
import util.Utils;

import java.util.HashSet;

@Getter
@Setter
public class Pointer {
    private Type type;
    private HashSet<Type> extraTypes = new HashSet<>();
    private RefType refType;

    public Pointer(Type type) {
        this.type = type;
    }

    public Pointer(Type type, RefType refType){
        this.type = type;
        this.refType = refType;
    }

    public Pointer copy(){
        Pointer pointer = new Pointer(null);
        pointer.type = type;
        return pointer;
    }

    public static Pointer createPointer(Value value){
        return new Pointer(value.getType());
    }

    public void addExtraTypes(HashSet<Type> types){
        for (Type extraType: types)
            addExtraType(extraType);
    }

    public void addExtraType(Type type){
        SootClass addClassOfType = Utils.toSootClass(type);
        HashSet<Type> toDelete = new HashSet<>();
        boolean flag = true;
        HashSet<Type> checkTypes = new HashSet<>(extraTypes);
        checkTypes.add(getType());
        for (Type recordedType: checkTypes){
            SootClass recordedClassOfType = Utils.toSootClass(recordedType);
            RelationShip relationShip = ClassRelationshipUtils.getExtentRelationshipAmongClasses(recordedClassOfType, addClassOfType);
            if (relationShip.equals(RelationShip.SUPER))
                toDelete.add(recordedType);
            else if (!relationShip.equals(RelationShip.HAS_SAME_SUB)){
                flag = false;
                break;
            }
        }
        extraTypes.removeAll(toDelete);
        if (flag)
            extraTypes.add(type);
    }
}
