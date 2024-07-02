package gadgets.collection.node;

import cfg.Node;
import dataflow.node.MethodDescriptor;
import dataflow.node.SourceNode;
import tranModel.TransformableNode;
import util.Pair;
import gadgets.collection.markers.Comparison;
import soot.SootMethod;
import soot.Type;
import soot.Value;
import soot.ValueBox;
import soot.jimple.*;
import util.ClassRelationshipUtils;
import util.StaticAnalyzeUtils.Parameter;
import util.Utils;

import java.util.HashMap;
import java.util.HashSet;

import static dataflow.DataFlow.findAllDefUnitAffectThisValue;
import static tranModel.Rules.RuleUtils.getValueByParamIndex;

public class ConditionUtils {
    public static HashMap<String, Pair<Integer, Integer>> compareMethodsMapInputArg = new HashMap<>();
    public static HashSet<String> sizeMethods = new HashSet<>();
    public static HashSet<String> mapElementSigs = new HashSet<>();
    public static void init(){
        compareMethodsMapInputArg.put("<java.lang.String: boolean equals(java.lang.Object)>", new Pair<>(-1,0)); // compare-compared
        sizeMethods.addAll(Utils.toStringSet(ClassRelationshipUtils.getAllSubMethodSigs("<java.util.Collection: int size()>")));
        mapElementSigs.addAll(ClassRelationshipUtils.getAllSubMethodSigs("<java.util.Map: java.lang.Object get(java.lang.Object)>"));
        mapElementSigs.addAll(ClassRelationshipUtils.getAllSubMethodSigs("<java.util.Map: boolean containsKey(java.lang.Object)>"));
        mapElementSigs.addAll(ClassRelationshipUtils.getAllSubMethodSigs("<java.util.Map: boolean containsValue(java.lang.Object)>"));
        mapElementSigs.addAll(ClassRelationshipUtils.getAllSubMethodSigs("<java.util.Set: boolean contains(java.lang.Object)>"));
    }

    public static boolean findControllableSourceDirect(ConditionNode conditionNode,
                                                       MethodDescriptor descriptor,
                                                       Value value){
        boolean flag = false;
        for (SourceNode sourceNode: descriptor.sourcesTaintGraph.matchTaintedSources(value)){
            conditionNode.controllableValues.add(sourceNode);
           // 对于array类型的对象, 其中元素==null或是其他条件并不能向上递归到array类型的field == null
            if (!value.getType().toString().contains("[]")
                    & sourceNode.getType().toString().contains("[]"))
                conditionNode.isDominator = false;
            flag = true;
            break;
        }

        return flag;
    }

    public static void parseSources(ConditionNode conditionNode, HashSet<Node> sources,
                                    Value value, MethodDescriptor descriptor) {
        for (Node node: sources){
            if (node.unit instanceof AssignStmt){
                AssignStmt assignStmt = (AssignStmt)node.unit;
                Value left = assignStmt.getLeftOp();
                Value right = assignStmt.getRightOp();
                if (right instanceof Constant){
                    if (conditionNode.reverse)
                        conditionNode.flipComparison();
                    conditionNode.conditionValues.add(right);
                }

                if (right instanceof LengthExpr){
                    Value op = ((LengthExpr)right).getOp();
                    conditionNode.controllableValues.addAll(descriptor.sourcesTaintGraph.matchTaintedSources(op));
                }

                if (right instanceof InvokeExpr){
                    SootMethod invokedMethod = ((InvokeExpr)right).getMethod();
                    if (compareMethodsMapInputArg.containsKey(invokedMethod.getSignature())){
                        Pair<Integer, Integer> inds = compareMethodsMapInputArg.get(invokedMethod.getSignature());
                        // 更新一下比较符号
                        if (invokedMethod.getName().contains("equal")){
                            if (conditionNode.comparison.equals(Comparison.EQUAL))
                                conditionNode.comparison = Comparison.NO_EQUAL_TO;
                            if (conditionNode.comparison.equals(Comparison.NO_EQUAL_TO))
                                conditionNode.comparison = Comparison.EQUAL;
                        }
                        conditionNode.deleteLast = true;

                        Value compareValue = getValueByParamIndex((Stmt) node.unit, inds.getKey());
                        Value comparedValue = getValueByParamIndex((Stmt) node.unit, inds.getValue());
                        if (comparedValue != null & compareValue != null){
                            if (comparedValue instanceof Constant){
                                conditionNode.conditionValues.add(comparedValue);
                            }
                            else
                                conditionNode.controllableValues.addAll(
                                        descriptor.sourcesTaintGraph.matchTaintedSources(comparedValue)
                                );
                            if (compareValue instanceof Constant){
                                conditionNode.conditionValues.add(compareValue);
                            }
                            else
                                conditionNode.controllableValues.addAll(
                                        descriptor.sourcesTaintGraph.matchTaintedSources(compareValue)
                                );
                        }
                    }
                    else if (sizeMethods.contains(invokedMethod.getSignature())){
                        ValueBox thisValueBox = Parameter.getThisValueBox(node);
                        if (thisValueBox != null){
                            Value thisValue = thisValueBox.getValue();
                            if (Utils.isTainted(thisValue, descriptor.taints)){
                                conditionNode.controllableValues.addAll(descriptor.sourcesTaintGraph.matchTaintedSources(thisValue));
                            }
                        }
                    }
                }

                // 对类型表达式的解析处理, E.g. r0 instanceof java.util.Map
                if (right instanceof InstanceOfExpr){
                    conditionNode.flipComparison();
                    conditionNode.deleteLast = true;
                    findControllableSourceDirect(conditionNode, descriptor,((InstanceOfExpr)right).getOp());
                    Type instanceType = ((InstanceOfExpr)right).getCheckType();
                    conditionNode.conditionValues.add(instanceType);
                }
            }
        }
    }
}
