package container;

import tranModel.Rules.AliasAndPointerRule;
import tranModel.Rules.JoinRule;
import tranModel.Rules.TaintGenerateRule;
import tranModel.Rules.TaintSpreadRule;
import tranModel.Transformable;
import gadgets.collection.node.ConditionUtils;
import gadgets.collection.rule.ConditionCheck;
import gadgets.collection.rule.DependenceCheck;
import gadgets.collection.rule.SinkCheck;
import rules.sinks.*;
import structure.RuleDataStructure;
import util.DataSaveLoadUtil;

import java.io.IOException;

public class RulesContainer {
    public static RuleDataStructure ruleDataStructure = null; // 在初始化之后默认不为null

    public static void reset(){
        ruleDataStructure = null;
    }

    public static void init() throws IOException {
        DataSaveLoadUtil.loadRuleDataStructure();
        // 分配Rules[gadget chains检测]
        loadCheckRules();
        // 加载污点传播的Rules
        loadTransRules();
        loadIOCDInferRules();
        loadBasicConfigOfCheckRules();
    }

    public static void loadCheckRules(){
        ClassLoaderCheckRule.init();
        ExecCheckRule.init();
        FileCheckRule.init();
        InvokeCheckRule.init();
        JNDICheckRule.init();
        SecondDesCheckRule.init();
        CustomCheckRule.init();

//        ConditionNode.init()

    }

    public static void loadTransRules(){
        Transformable.clearRules();
        Transformable.addRule(new JoinRule()); // 这个必须第一个加入
//        TransformableNode.addRule(new PointToRule());
        Transformable.addRule(new TaintSpreadRule());
        Transformable.addRule(new AliasAndPointerRule());
        Transformable.addRule(new TaintGenerateRule());
    }

    public static void loadIOCDInferRules(){
        Transformable.clearInferRules();
        Transformable.addInferRule(new DependenceCheck());
        Transformable.addInferRule(new ConditionCheck());
        Transformable.addInferRule(new SinkCheck());

        Transformable.clearExtraInferRules();
        Transformable.addExtraInferRule(new DependenceCheck());
        Transformable.addExtraInferRule(new ConditionCheck());
    }

    public static void loadBasicConfigOfCheckRules(){
        ConditionUtils.init();
    }
}
