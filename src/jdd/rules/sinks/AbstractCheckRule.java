package rules.sinks;


import tranModel.Transformable;
import tranModel.TransformableNode;
import container.BasicDataContainer;
import container.FragmentsContainer;
import dataflow.node.MethodDescriptor;
import gadgets.unit.Fragment;
import markers.SinkType;
import markers.Stage;
import soot.SootMethod;
import soot.jimple.InvokeExpr;
import util.Utils;

import java.io.IOException;
import java.util.HashSet;
import java.util.LinkedList;

/**
 * Gadget Sink检测规则的抽象类
 * 用于检查生成Sink Fragment
 */

public abstract class AbstractCheckRule implements CheckRule {
    public SinkType sinkType;
    // 专门为ClassLoader预留的开关，用于重复Gadget比较
    boolean isClassLoadGadget = false;

    /**
     * @param callStack     在进行数据流分析时候的调用栈，我们会在该过程中检测是否当前数据流所在的方法为预设的risky方法
     * @param descriptor    用于描述当前方法的上下文
     * @param transformable 用于标识当前分析的Jimple IR
     */
    public void apply(MethodDescriptor descriptor,
                      LinkedList<SootMethod> callStack,
                      Transformable transformable) throws IOException { }


    public boolean checkRisky(MethodDescriptor descriptor, TransformableNode tfNode){ return false;}

    /**
     * 检查同一 Sink Type 下的 Fragments 中, 是否存在 call stack 重复的
     * @param callStack
     * @param sinkType
     * @return true: 重复; false: 不重复
     */
    protected boolean checkGadgetDuplication(LinkedList<SootMethod> callStack, SinkType sinkType) {
        // 该检查仅在 Fragment 搜索阶段进行
        if (!BasicDataContainer.stage.equals(Stage.FRAGMENT_SEARCHING))
            return false;
        boolean flag = false;
        HashSet<Fragment> toDelete = new HashSet<>();

        for (Fragment fragment: FragmentsContainer.getSinkFragmentsByHead(callStack.getFirst())){
            if (fragment.sinkType.equals(sinkType)){
                if (Utils.listEqual(fragment.getGadgets(), callStack)){
                    flag = true;
                }
                // 一些启发式规则
                else if (Utils.listContains(callStack, fragment.getGadgets())
                        & callStack.size() > fragment.getGadgets().size() + 2){ // 如果call stack包含在fragment.gadgets中, 且gadget数量更少, 则
                    flag = true;
                }else if (Utils.listContains(fragment.getGadgets(),callStack)
                        & fragment.getGadgets().size() > callStack.size() + 2)
                    toDelete.add(fragment);
            }
        }
        for (Fragment fragment: FragmentsContainer.getSinkFragmentByEnd(callStack.getLast())){
            if (fragment.sinkType.equals(sinkType)){
                if (Utils.listEqual(fragment.getGadgets(), callStack)){
                    flag = true;
                } // 启发式的筛选，可以删除
                else if (Utils.isSubRevList(callStack, fragment.getGadgets())
                        && callStack.size() > fragment.getGadgets().size()+BasicDataContainer.heuristicShortChainCutLen){
                    flag = true;
                }else if (Utils.isSubRevList(fragment.getGadgets(), callStack)
                        && fragment.getGadgets().size() < callStack.size()-BasicDataContainer.heuristicShortChainCutLen){
                    toDelete.add(fragment);
                }
            }
        }

        for (Fragment fragment: toDelete){
            FragmentsContainer.stateFragmentsMap.get(Fragment.FRAGMENT_STATE.SINK).remove(fragment);
            FragmentsContainer.typeFragmentsMap.get(fragment.type).remove(fragment);
            FragmentsContainer.sinkFragments.remove(fragment);
        }

        return flag;
    }
}
