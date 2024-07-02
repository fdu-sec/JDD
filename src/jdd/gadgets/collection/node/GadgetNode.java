package gadgets.collection.node;

import tranModel.TransformableNode;
import container.BasicDataContainer;
import dataflow.node.MethodDescriptor;
import gadgets.collection.AnalyzeUtils;
import soot.SootClass;
import soot.SootMethod;
import soot.jimple.IfStmt;
import soot.jimple.Stmt;

import java.util.HashMap;
import java.util.HashSet;
import java.util.LinkedHashMap;


public class GadgetNode {
    public int deep = 0;
    public SootMethod sootMethod; // 标记方法
    public SootClass sootClass; // 所属类

    public HashMap<TransformableNode, Boolean> conditionPathStrategies = new HashMap<>();

    public LinkedHashMap<IfStmt, ConditionNode> dominatorConditions = new LinkedHashMap<>();

    public LinkedHashMap<IfStmt, ConditionNode> implicitConditions = new LinkedHashMap<>();

    public LinkedHashMap<IfStmt, ConditionNode> allConditions = new LinkedHashMap<>();

    public GadgetNode(SootMethod sootMethod, SootClass sootClass){
        this.sootMethod = sootMethod;
        this.sootClass = sootClass;
    }

    /**
     * 根据 IfStmt 索引 Condition Node
     * @param ifStmt
     * @return
     */
    public ConditionNode getConditionNodeByIfStmt(IfStmt ifStmt){
        if (dominatorConditions.containsKey(ifStmt))
            return dominatorConditions.get(ifStmt);
        return implicitConditions.get(ifStmt);
    }

    public boolean equals(Object object){
        if (!(object instanceof GadgetNode))
            return false;

        GadgetNode gadgetNode = (GadgetNode) object;
        return sootClass.equals(gadgetNode.sootClass) & sootMethod.equals(gadgetNode.sootMethod);
    }

    public int hashCode(){
        return sootClass.hashCode()*13 + sootMethod.hashCode();
    }

    /**
     * 记录tfNode前的必要条件约束
     * @param tfNode
     * @param gadgetInfoRecord
     * @param descriptor
     */
    public void  recordDominatorConditions(TransformableNode tfNode,
                                          GadgetInfoRecord gadgetInfoRecord,
                                          MethodDescriptor descriptor) {
        HashSet<Integer> path_record = tfNode.path_record;
        for (Integer hashCode: path_record){
            if (path_record.contains(-hashCode))
                continue;

            boolean satisfyFlag = hashCode > 0;

            TransformableNode addConditionTfNode = BasicDataContainer.conditionTfNodesMap.get(hashCode>0 ? hashCode:-hashCode);
            IfStmt addIfStmt = addConditionTfNode.getIfStmt();
            if (implicitConditions.containsKey(addIfStmt)){
                implicitConditions.remove(addIfStmt, implicitConditions.get(addIfStmt));
                ConditionNode tmpConditionNode = new ConditionNode(addConditionTfNode, descriptor, satisfyFlag, true);
                gadgetInfoRecord.putConditionNode(tmpConditionNode, this, addIfStmt);
            }else {
                ConditionNode tmpConditionNode = new ConditionNode(addConditionTfNode, descriptor, satisfyFlag, true);
                gadgetInfoRecord.putConditionNode(tmpConditionNode, this, addIfStmt);
            }
        }
    }


    public void markConditionType(){
        changeConditionTypeByTarget();
        changeConditionProperty();
    }

    public void changeConditionProperty(){
        HashMap<IfStmt, ConditionNode> toChange = new HashMap<>();
        for (ConditionNode conditionNode: dominatorConditions.values()){
            if ((conditionNode.type & ConditionNode.OR) == ConditionNode.OR){
                toChange.put(conditionNode.conditionNode.getIfStmt(), conditionNode);
            }
        }

        for (IfStmt ifStmt: toChange.keySet()){
            toChange.get(ifStmt).isDominator = false;
            dominatorConditions.remove(ifStmt, toChange.get(ifStmt));
            implicitConditions.put(ifStmt, toChange.get(ifStmt));
        }
    }

    public void changeConditionTypeByTarget(){
        for (ConditionNode basicCon: dominatorConditions.values()){
            TransformableNode tfNode = basicCon.conditionNode;
            Stmt target = tfNode.getIfStmt().getTarget();
            if (!basicCon.satisfyFlag) //
                target = AnalyzeUtils.getOtherSucStmt(basicCon.conditionNode, target);

            if (tfNode.precursors.size() != 1)  continue;
            TransformableNode preTfNode = tfNode.precursors.iterator().next();
            for (IfStmt allIfStmt : allConditions.keySet()){
                ConditionNode allCondNode = allConditions.get(allIfStmt);
                if (allCondNode.isDominator)    continue;
                if (dominatorConditions.containsKey(allIfStmt)) continue;
                ConditionNode allCon = allConditions.get(allIfStmt);
                if (!allCon.conditionNode.successors.contains(preTfNode)) continue;

                Stmt otherSuc = AnalyzeUtils.getOtherSucStmt(allCon.conditionNode, (Stmt) preTfNode.node.unit);
                if (otherSuc == null)   continue;
                if (otherSuc.equals(target)){
                    basicCon.type = basicCon.type | ConditionNode.OR;
                    break;
                }
            }
        }
    }
}
