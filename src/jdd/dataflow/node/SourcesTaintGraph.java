package dataflow.node;

import config.RegularConfig;
import tranModel.Rules.RuleUtils;
import tranModel.Taint.Taint;
import tranModel.TransformableNode;
import soot.*;
import soot.jimple.Constant;
import soot.jimple.FieldRef;
import soot.jimple.ParameterRef;
import util.StaticAnalyzeUtils.FieldUtil;
import util.Utils;

import java.util.HashMap;
import java.util.HashSet;
import java.util.LinkedList;

public class SourcesTaintGraph {
    public HashMap<SourceNode, HashSet<Value>> sources2TaintedValues = new HashMap<>();
    public HashMap<SourceNode, SourceNode> sourcesInfluenceRecord = new HashMap<>();

    public SootMethod entryMethod;

    public MethodDescriptor descriptor;

    public HashMap<ValueBox, TransformableNode> sourceUnFound = new HashMap<>();

    public void addTaintedSourceNode(SourceNode sourceNode, Value value){
        if (sourceNode == null)
            return;
        // 1. 考虑fields之间的影响关系, 查找影响源
        sourceNode = searchOriginalSourceNode(sourceNode, new LinkedList<>());

        // 2. 记录 value <-> 影响源field的关系, 注意检查value是否在之前已经有对应记录, 避免出现多个相同的value键值
        SourceNode inSourceNode = getRecordedKey(sourceNode);; // 用于记录已经存在的与key等价的键值
        // 如果已经有记录, 则加入该field能影响的local value; 否则先创建, 再加入
        if (inSourceNode != null){
            sources2TaintedValues.get(inSourceNode).add(value);
        }else {
            sources2TaintedValues.put(sourceNode, new HashSet<>());
            sources2TaintedValues.get(sourceNode).add(value);
        }
    }

    public void addTaintedSourceNode(Value affected, Value affect){
        for (SourceNode sourceNode: matchTaintedSources(affect))
            addTaintedSourceNode(sourceNode,affected);
    }

    private SourceNode getRecordedKey(SourceNode key) {
        for (SourceNode sourceNode : sources2TaintedValues.keySet()){
            if (sourceNode.equals(key))
                return sourceNode;
        }
        return null;
    }

    private SourceNode searchOriginalSourceNode(SourceNode sourceNode, LinkedList<SourceNode> originalSNs) {
        SourceNode retFieldNode = null;
        if (originalSNs.size() >= RegularConfig.accessPath_limit)
            return originalSNs.getFirst();
        originalSNs.add(sourceNode);
        for (SourceNode fieldNode_tmp: sourcesInfluenceRecord.keySet()){
            if (fieldNode_tmp.equals(sourceNode)) {
                retFieldNode = sourcesInfluenceRecord.get(fieldNode_tmp);
            }
        }
        if (retFieldNode != null)
            return searchOriginalSourceNode(retFieldNode, originalSNs);
        else
            return sourceNode;
    }


    public HashSet<SourceNode> matchTaintedSources(Value value) {
        HashSet<SourceNode> ret = new HashSet<>();
        for (SourceNode sourceNode : sources2TaintedValues.keySet()){
            if (sources2TaintedValues.get(sourceNode).contains(value))
                ret.add(sourceNode);
        }

        if (ret.isEmpty()){
            if (value instanceof FieldRef) {
                LinkedList<SootField> field = new LinkedList<>();
                field.add(((FieldRef) value).getField());
                SourceNode sourceNode = new SourceNode(field, ((FieldRef) value).getFieldRef().declaringClass());
                ret.add(sourceNode);
            }
            else if (value instanceof ParameterRef){
                SourceNode sourceNode = new SourceNode(((ParameterRef) value).getIndex(), entryMethod);
                ret.add(sourceNode);
            }
            else if (value instanceof Constant){
                SourceNode sourceNode = new SourceNode(value);
                ret.add(sourceNode);
            }
        }

        return ret;
    }

    public HashSet<SourceNode> matchTaintedSources(Taint taint){
        HashSet<SourceNode> ret = new HashSet<>();
        boolean fieldPathFlag = !taint.accessPath.isEmpty();
        for (SourceNode sourceNode: sources2TaintedValues.keySet()){
            if (sources2TaintedValues.get(sourceNode).contains(taint.object)){
                if (!fieldPathFlag)
                    ret.add(sourceNode);
                else if (sourceNode.isField()){
                    //  对于taint, 要求fields污染层次比
                    if (sourceNode.field.equals(taint.accessPath))
                        ret.add(sourceNode);
                }
            }
        }

        return ret;
    }

    public HashSet<SourceNode> getSourceNodesByTaint(Taint taint){
        HashSet<SourceNode> ret = new HashSet<>();
        if (taint.accessPath.isEmpty()){
            ret.addAll(matchTaintedSources(taint.object));
        }else {
            for (SourceNode tmpField: matchTaintedSources(taint.object)){
                if (!tmpField.isField())
                    continue;
                SourceNode newSourceNode = new SourceNode(new LinkedList<>(tmpField.field), tmpField.classOfField);
                ret.add(newSourceNode);

                SootField lastSootField = newSourceNode.field.getLast();
                SootClass lastFieldClass = FieldUtil.getSootFieldType(lastSootField);
                for (SootField tmpSootField: taint.accessPath){
                    if (FieldUtil.hasField(lastFieldClass, tmpSootField)) {
                        newSourceNode.field.add(tmpSootField);
                        // 更新最后一个信息
                        lastSootField = tmpSootField;
                        lastFieldClass = FieldUtil.getSootFieldType(lastSootField);
                    }
                    else {
                        ret.remove(newSourceNode);
                        break; // 如果不存在, 则说明该记录存在问题
                    }
                }
            }
        }

        return ret;
    }

    public void completeFieldOfParamSourceNde(SourceNode sourceNode, Value taintObj){
        HashSet<SourceNode> taintObjSourceNodes = matchTaintedSources(taintObj);
        if (taintObjSourceNodes.size() > 1)
            return;
        for (SourceNode tmpSourceNode: taintObjSourceNodes){
            if (tmpSourceNode.isFieldOfParameter()
                    | tmpSourceNode.isParameter()){
                sourceNode.ind = tmpSourceNode.ind;
                sourceNode.entryMtd = tmpSourceNode.entryMtd;
            }
        }
    }

    public void updateSourceUnFound(LinkedList<SootMethod> callStack, MethodDescriptor descriptor){
        if (sourceUnFound.isEmpty())
            return;

        for (ValueBox valueBox: sourceUnFound.keySet()){
            TransformableNode tfNode = sourceUnFound.get(valueBox);
            HashSet<SourceNode> sourceNodes = RuleUtils.tryHeuristicSourceMatching(descriptor, valueBox, tfNode, callStack);
            for (SourceNode sourceNode: sourceNodes){
                descriptor.sourcesTaintGraph.addTaintedSourceNode(sourceNode, valueBox.getValue());
            }
        }

        sourceUnFound.clear();
    }

    public void createAndAddSourceNode(Value sourceValue,
                                       Value taintedValue,
                                       boolean needInfluenceCheck,
                                       boolean needSlzCheck){
        for (SourceNode sourceNode: matchTaintedSources(sourceValue)) {
            sourceNode.checkFlag = needSlzCheck;
            // TODO: 根据类型检测一下, 污染源是否适合传播
            if (needInfluenceCheck)
                if (!couldInfluence(taintedValue.getType(), sourceNode.getType()))
                    continue;
            addTaintedSourceNode(sourceNode, taintedValue);
        }
    }

    public void recordSourceInfluence(Value affected, Value affect){
        HashSet<SourceNode> affectedSourceNodes = matchTaintedSources(affected);
        HashSet<SourceNode> affectSourceNodes = matchTaintedSources(affect);

        for (SourceNode affectedSourceNode: affectedSourceNodes){
            for (SourceNode affectSourceNode: affectSourceNodes){
                recordSourceInfluence(affectedSourceNode,affectSourceNode);
            }
        }
    }

    public void recordSourceInfluence(SourceNode affected, SourceNode affect){
        if (!couldInfluence(affected, affect))
            return;

        // TODO: 由于没有实现路径敏感, 因此可能会引入错误的推断
        HashMap<SourceNode, SourceNode> toDelete = new HashMap<>();
        for (SourceNode recordedAffected: sourcesInfluenceRecord.keySet()){
            if (recordedAffected.equals(affected))
                toDelete.put(recordedAffected, sourcesInfluenceRecord.get(recordedAffected));
            if (recordedAffected.equals(affect) & sourcesInfluenceRecord.get(recordedAffected).equals(affected))
                toDelete.put(recordedAffected, sourcesInfluenceRecord.get(recordedAffected));
        }

        for (SourceNode sourceNode: toDelete.keySet())
            sourcesInfluenceRecord.remove(sourceNode, toDelete.get(sourceNode));

        sourcesInfluenceRecord.put(affected, affect);
    }

    public static boolean couldInfluence(SourceNode affected, SourceNode affect){
        if (affected.equals(affect))
            return false;

        return couldInfluence(affected.getType(),affect.getType());
    }

    public static boolean couldInfluence(Value affected, Value affect){
        if (affected.equals(affect))
            return false;

        return couldInfluence(affected.getType(), affect.getType());
    }

    public static boolean couldInfluence(Type affectedType, Type affectType){
        if (Utils.isBasicType(affectType) & !Utils.isBasicType(affectedType) )
            return false;
        if (Utils.isBasicType(affectType) & Utils.isBasicType(affectedType) & !Utils.isSameType(affectedType,affectType))
            return false;
        return true;
    }
}
