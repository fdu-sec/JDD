package tranModel;

import cfg.CFG;
import cfg.Node;
import lombok.extern.slf4j.Slf4j;
import soot.jimple.IfStmt;

import java.util.HashMap;
import java.util.LinkedHashSet;
import java.util.LinkedList;
import java.util.List;

@Slf4j
public class TranUtil {

    public static int error_cannot_topological_order = 0;
    public static boolean DEBUG = false;

    /**
     * 给定cfg返回一个根据该cfg进行拓扑排序的TransformableNode列表
     * @param cfg
     * @return List<TransformableNode>
     */
    public static List<TransformableNode> getTopologicalOrderedTNodesFromCFG(CFG cfg){

        HashMap<Node, TransformableNode> nodeMapTransformNode = new HashMap<>();
        HashMap<TransformableNode, Integer> transformNodeMapPrecursorSize = new HashMap<>();
        LinkedHashSet<TransformableNode> waiting = new LinkedHashSet<>();
        // Step1: 将cfg中的所有Node封装为TransformableNode
        // Step2: 记录TransformableNode的前继节点数量，作为后续处理循环有环情况时候的入度
        // Step3: 将封装好的TransformableNode填充到waiting中等待处理
        for(Node node : cfg.allNodes.values()){
            // 我重写了TransformableNode 的hash方法，使得同一cfg多次执行获得的拓扑序是一致的
            TransformableNode transformableNode = new TransformableNode(node, cfg.entryPoint);
            transformNodeMapPrecursorSize.put(transformableNode, node.precursorNodes.size());
            nodeMapTransformNode.put(node, transformableNode);
            waiting.add(transformableNode);
        }
//        HashSet<TransformableNode> waiting = new HashSet<>(transformNodeMapPrecursorSize.keySet());
//        List<TransformableNode> waitingList = new LinkedList<>(waiting);
//        Collections.sort(waitingList, );

        List<TransformableNode> ret = new LinkedList<>();
        int topologicalOrderFail = 0;
        boolean cycleFlag = false;
        while(!waiting.isEmpty()){
            int fl = 0;
            for(TransformableNode transformableNode : waiting){
                if(transformNodeMapPrecursorSize.get(transformableNode) == 0){
                    ret.add(transformableNode);
                    waiting.remove(transformableNode);
                    // 更新拓扑排序后的相关信息
                    for(Node node : transformableNode.node.successorNodes){
                        TransformableNode successor = nodeMapTransformNode.get(node);
                        int temp = transformNodeMapPrecursorSize.get(successor);
                        transformNodeMapPrecursorSize.put(successor, temp - 1); // 后继节点未处理前继数量-1

                        transformableNode.successors.add(successor);
                        successor.precursors.add(transformableNode);
                    }
                    fl = 1;

                    // 一般环路是由于循环条件分支导致? 找出环路中的条件分支
                    if (cycleFlag & transformableNode.node.unit instanceof IfStmt) {
                        transformableNode.isCycle = true;
                        cycleFlag = false;
                    }

                    break;
                }
            }
            // 因为套了一层while(!waiting.isEmpty())
            // 所以如果出现环路，transformNodeMapPrecursorSize.get(transformableNode) == 0过不去
            // 进而fl不可能为1，从而进入下面的有环处理中
            if(fl == 0){
                // 找剩下结点中入度最高的：原因：循环中有环，入度最高的最可能是循环的入口
                TransformableNode transformableNode = waiting.iterator().next();
                int maxIn = 0;
                for(TransformableNode t : waiting){
                    if(t.precursors.size() > maxIn){
                        maxIn = t.precursors.size();
                        transformableNode = t;
                    }
                }
                ret.add(transformableNode);
                waiting.remove(transformableNode);
                for(Node node : transformableNode.node.successorNodes){
                    TransformableNode successor = nodeMapTransformNode.get(node);
                    int temp = transformNodeMapPrecursorSize.get(successor);
                    transformNodeMapPrecursorSize.put(successor, temp - 1);

                    transformableNode.successors.add(successor);
                    successor.precursors.add(transformableNode);
                }
                topologicalOrderFail = 1;
                cycleFlag = true;
            }

        }
        if(topologicalOrderFail == 1) error_cannot_topological_order ++;
        return ret;
    }


}
