package dataflow.node;


import gadgets.collection.node.ClassNode;
import gadgets.collection.node.GadgetInfoRecord;
import soot.*;
import soot.jimple.Constant;
import util.ClassRelationshipUtils;
import util.StaticAnalyzeUtils.FieldUtil;

import java.util.LinkedList;

public class SourceNode {
    public Integer ind = null;
    public SootMethod entryMtd = null;
    public SootClass classOfField = null;
    public int classId = 0;
    public LinkedList<SootField> field = new LinkedList<>();
    public Value constant = null;
    public boolean checkFlag = true;

    public SourceNode(Integer ind, SootMethod entryMtd){
        this.ind = ind;
        this.entryMtd = entryMtd;
    }

    public SourceNode(LinkedList<SootField> field, SootClass classOfField){
        assert !field.isEmpty();
        this.field = field;
        this.classOfField = classOfField;

        if (classOfField != null){
            SootField firstField = field.getFirst();
            if (ClassRelationshipUtils.isSubClassOf(classOfField,
                    firstField.getDeclaringClass())){
                this.classOfField = classOfField;
            }else this.classOfField = firstField.getDeclaringClass();
        }
        else {
            this.classOfField = field.getFirst().getDeclaringClass();
        }
    }

    public SourceNode(LinkedList<SootField> field, SootClass classOfField, int ind, SootMethod entryMtd){
        assert !field.isEmpty();
        this.field = field;
        this.classOfField = classOfField;

        if (classOfField != null){
            SootField firstField = field.getFirst();
            if (ClassRelationshipUtils.isSubClassOf(classOfField,
                    firstField.getDeclaringClass())){
                this.classOfField = classOfField;
            }else this.classOfField = firstField.getDeclaringClass();
        }
        else {
            this.classOfField = field.getFirst().getDeclaringClass();
        }

        this.ind = ind;
        this.entryMtd = entryMtd;
    }

    public SourceNode(Value constant){
        assert constant instanceof Constant;
        this.constant = constant;
    }

    public boolean equals(Object obj){
        if (!(obj instanceof SourceNode))
            return false;
        SourceNode sourceNode = (SourceNode) obj;

        if (sourceNode.isFieldOfParameter()){
            if (!this.isFieldOfParameter())
                return false;
            return ind.equals(sourceNode.ind) & entryMtd.equals(sourceNode.entryMtd)
                    & field.equals(sourceNode.field);
        }
        if (ind != null)
            return ind.equals(sourceNode.ind) & entryMtd.equals(sourceNode.entryMtd);
        if (constant != null)
            return constant.equals(sourceNode.constant);
        if (field.size() != sourceNode.field.size())
            return false;
        for (int index = 0; index < field.size(); index++){
            if (!field.get(index).equals(sourceNode.field.get(index)))
                return false;
        }
        return true;
    }

    public boolean equals(Object obj, int accessPathIndex){
        if (!(obj instanceof SourceNode))
            return false;
        SourceNode sourceNode = (SourceNode) obj;

        if (sourceNode.isFieldOfParameter()){
            if (!this.isFieldOfParameter())
                return false;
            return ind.equals(sourceNode.ind) & entryMtd.equals(sourceNode.entryMtd)
                    & field.equals(sourceNode.field);
        }
        if (ind != null)
            return ind.equals(sourceNode.ind) & entryMtd.equals(sourceNode.entryMtd);
        if (constant != null)
            return constant.equals(sourceNode.constant);
        if (accessPathIndex < field.size() && accessPathIndex < sourceNode.field.size()){
            return field.get(accessPathIndex).equals(sourceNode.field.get(accessPathIndex));
        }

        if (field.size() != sourceNode.field.size())
            return false;
        for (int index = 0; index < field.size(); index++){
            if (!field.get(index).equals(sourceNode.field.get(index)))
                return false;
        }
        return true;
    }

    public int hashCode(){
        if (isField())
            return field.hashCode()^7 + classOfField.hashCode()^13;
        if (isConstant())
            return constant.hashCode()^11;
        if (isParameter())
            return ind.hashCode()^13 + entryMtd.hashCode()^7;
        if (isFieldOfParameter()){
            return field.hashCode()^7 + classOfField.hashCode()^13 + ind.hashCode()^3 + entryMtd.hashCode()*17;
        }
        return -1;
    }

    public static SourceNode createFieldSourceNode(SootField sootField, SootClass sootClass){
        LinkedList<SootField> fields = new LinkedList<>();
        fields.add(sootField);
        return new SourceNode(fields, sootClass);
    }

    public void setClassId(GadgetInfoRecord gadgetInfoRecord){
        if (isConstant())
            return;
        else if (isField()){
            ClassNode classNode = gadgetInfoRecord.getClassNode(classOfField);
            if (classNode != null)
                classId = classNode.classId;
        }
        else if (isParameter()){
            ClassNode classNode = gadgetInfoRecord.getClassNode(entryMtd.getDeclaringClass());
            if (classNode != null)
                classId = classNode.classId;
        }
    }


    public boolean isField(){
        return isFieldOfParameter() | !field.isEmpty() & ind == null & constant == null;
    }
    public boolean isParameter(){
        return field.isEmpty() & ind != null & entryMtd != null & constant == null;
    }

    public boolean isFieldOfParameter(){
        return !field.isEmpty() & ind != null & entryMtd != null & constant == null;
    }


    public boolean isConstant(){
        return field.isEmpty() & ind == null & constant != null;
    }

    public Type getType(){
        if (isField())
            return field.getLast().getType();
        if (isParameter())
            return entryMtd.getParameterType(ind);
        if (isFieldOfParameter())
            return field.getLast().getType();
        return constant.getType();
    }

    public Type getType(int index){
        if (field.size() > index && isField())   return field.get(index).getType();
        return getType();
    }

    public String toString(){
        if (isField()){
            return field.getLast().getSignature();
        }
        else if (isConstant())
            return constant.toString();
        else if (isParameter())
            return entryMtd.getSignature()+"  [ " + ind + " ]";
        else if (isFieldOfParameter())
            return field.getLast().getSignature() +"  [ " + ind + " ]";
        return "Invalid Type [NULL]";
    }
}
