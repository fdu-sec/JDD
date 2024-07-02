package util.StaticAnalyzeUtils;

import cfg.Node;
import soot.ValueBox;

import java.util.regex.Pattern;

/**
 * 静态分析基本能力
 */
public class IfStmtUtil {
    public static ValueBox getConditionExprBox(Node node){
        for(ValueBox valueBox : node.unit.getUseBoxes()){
            if(valueBox.toString().contains("ConditionExprBox")) return valueBox;
        }
        return null;
    }

    public static ValueBox tryGetImmediateNum(Node node){
        String pattern = ".*\\(.*[a-zA-Z].*\\).*";
        for(ValueBox valueBox : node.unit.getUseBoxes()){
            if(valueBox.toString().contains("ImmediateBox")) {
                if(Pattern.matches(pattern, valueBox.toString())) continue;
                return valueBox;
            }
        }
        return null;
    }
}
