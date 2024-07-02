package tranModel;

import container.FragmentsContainer;
import dataflow.node.MethodDescriptor;
import gadgets.collection.node.GadgetInfoRecord;
import gadgets.collection.rule.InferRule;
import soot.SootMethod;

import java.io.IOException;
import java.util.LinkedList;
import java.util.List;

public class Transformable {
    public enum State{
        ORIGIN, TRANSFORMED, TERMINATED
    }

    // 规则容器
    static List<Rule> rules = new LinkedList<>();
    static List<InferRule> inferRules = new LinkedList<>();
    static List<InferRule> extraInferRules = new LinkedList<>();
    public State state = State.ORIGIN;

    // 清除规则
    public static void clearRules(){
        rules = new LinkedList<>();
    }

    public static void clearInferRules(){
        inferRules = new LinkedList<>();
    }

    public static void clearExtraInferRules(){
        extraInferRules = new LinkedList<>();
    }

    // 添加规则
    public static void addRule(Rule rule){
        rules.add(rule);
    }

    public static void addInferRule(InferRule inferRule){
        inferRules.add(inferRule);
    }

    public static void addExtraInferRule(InferRule inferRule){
        extraInferRules.add(inferRule);
    }

    // 用于应用数据流分析过程中的各种规则，比如别名、Point2、污点传播等
    public void forward(MethodDescriptor descriptor){
        state = State.TRANSFORMED;
        for(Rule rule : rules){
            rule.apply(this,descriptor);
        }
    }

    // 用于risky call stack信息的收集
    public void forwardCheck(MethodDescriptor descriptor,
                             LinkedList<SootMethod> callStack) throws IOException {
        FragmentsContainer.protocolCheckRule.apply(descriptor, callStack, this);
    }

    public void forwardInferCheck(MethodDescriptor descriptor,
                                  GadgetInfoRecord gadgetInfoRecord) throws IOException {
        for (InferRule inferRule: inferRules)
            inferRule.apply(descriptor, gadgetInfoRecord, this);
    }

    public void forwardExtraInferCheck(MethodDescriptor descriptor,
                                  GadgetInfoRecord gadgetInfoRecord) throws IOException {
        for (InferRule inferRule: extraInferRules)
            inferRule.apply(descriptor, gadgetInfoRecord, this);
    }

    public void terminate(){
        state = State.TERMINATED;
    }

    public boolean isTerminated(){
        return state.equals(State.TERMINATED);
    }
}
