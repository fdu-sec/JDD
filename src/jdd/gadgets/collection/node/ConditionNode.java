package gadgets.collection.node;

import tranModel.TransformableNode;
import cfg.Node;
import dataflow.node.MethodDescriptor;
import dataflow.node.SourceNode;
import gadgets.collection.markers.Comparison;
import soot.Value;
import soot.ValueBox;
import soot.jimple.Constant;
import soot.jimple.IfStmt;

import java.util.HashSet;
import java.util.LinkedList;

import static dataflow.DataFlow.findAllDefUnitAffectThisValue;

public class ConditionNode {
    public LinkedList<SourceNode> controllableValues = new LinkedList<>();
    public LinkedList<Object> conditionValues = new LinkedList<>();
    public Comparison comparison;
    public TransformableNode conditionNode;
    public boolean isDominator = false;
    public boolean satisfyFlag;
    boolean reverse = true;
    boolean deleteLast = false;

    public int type = SINGLE;
    public static int SINGLE = 0; // = and
    public static int OR = 1;
    public static int UNCONTROLLABLE =2;

    public ConditionNode(TransformableNode tfNode, MethodDescriptor descriptor,
                         boolean satisfyFlag, boolean isDominator){
        this.conditionNode = tfNode;
        this.satisfyFlag = satisfyFlag;
        this.isDominator = isDominator;

        Value conditionValue = ((IfStmt) tfNode.node.unit).getCondition();
        parseComparison(conditionValue);
        parseConditionValue(this.conditionNode, conditionValue, descriptor);
    }

    public ConditionNode(TransformableNode tfNode,
                         MethodDescriptor descriptor,
                         boolean isDominator){
        this.conditionNode = tfNode;
        this.satisfyFlag = true;
        this.isDominator = isDominator;
        Value conditionValue = ((IfStmt) tfNode.node.unit).getCondition();
        parseComparison(conditionValue);
        parseConditionValue(this.conditionNode,conditionValue, descriptor);
    }

    public ConditionNode(ConditionNode conditionNode, boolean satisfyFlag, boolean isDominator){
        this.conditionNode = conditionNode.conditionNode;
        this.isDominator = isDominator;
        this.satisfyFlag = satisfyFlag;
        this.controllableValues = conditionNode.controllableValues;
        this.conditionValues = conditionNode.conditionValues;

        if (satisfyFlag != conditionNode.satisfyFlag)
            flipComparison();
    }

    public void parseComparison(Value condition){
        if (condition.toString().contains("==")){
            if (satisfyFlag)
                comparison = Comparison.EQUAL;
            else comparison = Comparison.NO_EQUAL_TO;
        }

        else if (condition.toString().contains("!=")){
            if (satisfyFlag)   comparison = Comparison.NO_EQUAL_TO;
            else comparison = Comparison.EQUAL;
        }

        else if (condition.toString().contains("<=")){
            if (satisfyFlag)   comparison = Comparison.SMALLER_OR_EQUAL;
            else comparison = Comparison.BIGGER;
        }

        else if (condition.toString().contains("<")){
            if (satisfyFlag)   comparison = Comparison.SMALLER;
            else comparison = Comparison.BIGGER_OR_EQUAL;
        }

        else if (condition.toString().contains(">=")){
            if (satisfyFlag)   comparison = Comparison.BIGGER_OR_EQUAL;
            else comparison = Comparison.SMALLER;
        }

        else if (condition.toString().contains(">")){
            if (satisfyFlag)   comparison = Comparison.BIGGER;
            else comparison = Comparison.SMALLER_OR_EQUAL;
        }
    }

    public void flipComparison(){
        switch (comparison){
            case SMALLER_OR_EQUAL:
                comparison = Comparison.BIGGER;
                break;
            case BIGGER_OR_EQUAL:
                comparison = Comparison.SMALLER;
                break;
            case SMALLER:
                comparison = Comparison.BIGGER_OR_EQUAL;
                break;
            case BIGGER:
                comparison = Comparison.SMALLER_OR_EQUAL;
                break;
            case EQUAL:
                comparison = Comparison.NO_EQUAL_TO;
                break;
            case NO_EQUAL_TO:
                comparison = Comparison.EQUAL;
        }
    }

    /**
     * 检测comparison与该condition node 的comparison是否矛盾
     * 不做过于惊喜的判别, 认为 > 和 >= 并不矛盾
     * @param comparison
     * @return
     */
    public boolean isNotContradictory(Comparison comparison){
        if (this.comparison.equals(Comparison.EQUAL))
            return comparison.equals(Comparison.EQUAL);
        if (this.comparison.equals(Comparison.NO_EQUAL_TO))
            return !comparison.equals(Comparison.EQUAL);
        if (this.comparison.equals(Comparison.BIGGER) | this.comparison.equals(Comparison.BIGGER_OR_EQUAL))
            return comparison.equals(Comparison.BIGGER) | comparison.equals(Comparison.BIGGER_OR_EQUAL);
        if (this.comparison.equals(Comparison.SMALLER) | this.comparison.equals(Comparison.SMALLER_OR_EQUAL))
            return comparison.equals(Comparison.SMALLER) | comparison.equals(Comparison.SMALLER_OR_EQUAL);
        return false;
    }

    public void parseConditionValue(TransformableNode tfNode,
                                    Value condition,
                                    MethodDescriptor descriptor){
        for (ValueBox valueBox: condition.getUseBoxes()){
            // 如果是常量，则认为是条件限制变量
            if (valueBox.getValue() instanceof Constant){ // Constant
                if (reverse & !comparison.equals(Comparison.EQUAL) & !comparison.equals(Comparison.NO_EQUAL_TO))
                    flipComparison();
                conditionValues.add(valueBox.getValue());
            }else {
                if (!ConditionUtils.findControllableSourceDirect(this, descriptor,valueBox.getValue())) {
                    // 可能存在一些复杂一些的数据流，查找所有定义语句并进行进一步解析
                    HashSet<Node> sources = findAllDefUnitAffectThisValue(tfNode.node, valueBox);
                    ConditionUtils.parseSources(this, sources, valueBox.getValue(), descriptor);
                }
            }
            reverse = false;
        }

        if (deleteLast)
            conditionValues.remove(conditionValues.size()-1);
    }
}
