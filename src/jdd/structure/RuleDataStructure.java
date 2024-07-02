package structure;

import lombok.Getter;
import lombok.Setter;
import structure.taint.TaintSpreadRuleUnit;

import java.util.HashSet;

@Getter
@Setter
public class RuleDataStructure {
    HashSet<TaintSpreadRuleUnit> taintSpreadRuleUnits = new HashSet<>();
}
