package tranModel.Rules;

import tranModel.Rule;
import tranModel.Transformable;
import tranModel.TransformableNode;
import container.BasicDataContainer;
import dataflow.node.MethodDescriptor;
import markers.Stage;
import soot.jimple.IfStmt;
import soot.jimple.Stmt;

import java.util.HashSet;

public class JoinRule implements Rule {
    /**
     * 一般是用来处理控制流汇聚点，合并状态。
     *      1. 在检测到sink点后是否需要继续在当前callstacks路径深入搜索；
     *      2. 信息收集的时候用来收集该语句前面的条件分支信息记录的。
     *  记录的前继节点信息：后续在动态代理模块轻量级的路径敏感
     *      不是常用的路径敏感，而是在到达某个节点后，通过查看前置的条件节点的信息，以推断要执行到该节点所必须满足的条件，并在拼接时进行更细粒度的检测
     * @param transformable
     */
    @Override
    public void apply(Transformable transformable, MethodDescriptor descriptor) {

        if (!BasicDataContainer.openJoinRule)  return;
        TransformableNode tfNode = (TransformableNode) transformable;
        // 如果没有前继节点, 则不需要继续分析
        if (tfNode.precursors.isEmpty()
                || BasicDataContainer.stage.equals(Stage.OFF)
                || BasicDataContainer.stage.equals(Stage.FRAGMENT_LINKING))
            return;

        HashSet<Integer> path_record = new HashSet<>();
        for(TransformableNode precursor : tfNode.precursors){
            if (!precursor.exec){
                tfNode.exec = false;
            }

            path_record.addAll(precursor.path_record);
        }
        tfNode.path_record.addAll(path_record);

//        if (BasicDataContainer.stage.equals(Stage.FRAGMENT_SEARCHING_SINGLE) && BasicDataContainer.openDynamicProxyDetect){
//            recordPath(tfNode);
//        }
    }

    public void recordPath(TransformableNode tfNode){
        Stmt stmt = (Stmt) tfNode.node.unit;

        if (stmt instanceof IfStmt) {
            IfStmt ifStmt = (IfStmt) stmt;
            Stmt target = ifStmt.getTarget();

//            TransformableNode.ifStmtHashMap.put(ifStmt.hashCode(),transformableNode);
            BasicDataContainer.conditionTfNodesMap.put(ifStmt.hashCode(), tfNode);

            for (TransformableNode success: tfNode.successors){
                if (((Stmt)success.node.unit).equals(target) ){
                    if (!tfNode.isCycle)
                        success.path_record.add(ifStmt.hashCode());
                }else {
                    success.path_record.add(-ifStmt.hashCode());
                }
            }
        }
    }
}
