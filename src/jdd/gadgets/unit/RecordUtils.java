package gadgets.unit;

import cfg.Node;
import gadgets.collection.node.ConditionUtils;
import soot.SootMethod;
import soot.ValueBox;
import soot.jimple.AssignStmt;
import soot.jimple.Constant;
import soot.jimple.IfStmt;
import soot.jimple.InvokeExpr;
import tranModel.TranUtil;
import tranModel.TransformableNode;
import dataflow.node.MethodDescriptor;
import dataflow.node.SourceNode;
import markers.SinkType;
import soot.SootField;
import soot.Value;
import util.StaticAnalyzeUtils.FieldUtil;
import util.StaticAnalyzeUtils.Parameter;

import java.util.HashMap;
import java.util.HashSet;
import java.util.LinkedList;
import java.util.List;

import static dataflow.DataFlow.findAllDefUnitAffectThisValue;
import static tranModel.Rules.RuleUtils.checkTransientControllableSimply;

public class RecordUtils {
    public static boolean recordTaintedArgs(MethodDescriptor descriptor,
                                         HashSet<Value> values,
                                         SinkType sinkType,
                                         TransformableNode tfNode){
        boolean risky = true;
        for (Value value: values) {
            risky = recordTaintedArgs(descriptor, value, sinkType, tfNode);
            if (!risky)
                break;
        }
        return risky;
    }

    public static boolean recordTaintedArgs(MethodDescriptor descriptor,
                                         Value value,
                                         SinkType sinkType,
                                         TransformableNode tfNode){
        HashSet<SourceNode> sourceNodes = descriptor.sourcesTaintGraph.matchTaintedSources(value);
        HashSet<SourceNode> paramSources = new HashSet<>();
        for (SourceNode sourceNode: sourceNodes){
            if (sourceNode.isParameter()){
                paramSources.add(sourceNode);
            }else if (sourceNode.isField()){
                SootField sootField = sourceNode.field.getLast();
                if (FieldUtil.isTransientType(sootField)){
                    if (!checkTransientControllableSimply(sourceNode.classOfField, sootField, descriptor)){
                        return false;
                    }
                }
            }
        }

        if (!descriptor.sinkUnitsRecord.containsKey(sinkType))
            descriptor.sinkUnitsRecord.put(sinkType, new HashMap<>());
        descriptor.sinkUnitsRecord.get(sinkType).put(tfNode, paramSources);

        return true;
    }

    public static TransformableNode findTfNodeToNextMtd(MethodDescriptor descriptor,
                                                        LinkedList<SootMethod> callStack){
        int index = callStack.indexOf(descriptor.sootMethod);
        if (callStack.size() < index + 1)
            return null;
        SootMethod nextMtd = callStack.get(index + 1);

        List<TransformableNode> topologicalOrder = TranUtil.getTopologicalOrderedTNodesFromCFG(descriptor.cfg);
        for (TransformableNode tmpTfNode: topologicalOrder){
            if (!tmpTfNode.containsInvoke())
                continue;
            SootMethod tmpNextMtd = tmpTfNode.getUnitInvokeExpr().getMethod();
            if (tmpNextMtd.getSubSignature().equals(nextMtd.getSubSignature()))
                return tmpTfNode;
        }
        return null;
    }

    public static String extractMethodName(TransformableNode tfNode,
                                  MethodDescriptor descriptor) {
        if (!(tfNode.node.unit instanceof IfStmt))
            return null;

        String methodName = "";
        IfStmt ifStmt = (IfStmt) tfNode.node.unit;
        Value condition = ifStmt.getCondition();
        boolean flag = false;
        ValueBox vBox = null;
        ValueBox cstBox = null;

        for (ValueBox valueBox: condition.getUseBoxes()){
            if (!descriptor.sourcesTaintGraph.matchTaintedSources(valueBox.getValue()).isEmpty()){
                flag = true;
            }
            if (valueBox.getValue() instanceof Constant)
                cstBox = valueBox;
            else vBox = valueBox;
        }

        if (flag | vBox == null)
            return null;
        HashSet<Node> sources = findAllDefUnitAffectThisValue(tfNode.node, vBox);
        for (Node node: sources) {
            if (node.unit instanceof AssignStmt) {
                if (((AssignStmt) node.unit).containsInvokeExpr()) {
                    ValueBox thisValueBox = Parameter.getThisValueBox(node);
                    if (thisValueBox == null)   continue;
                    InvokeExpr invokeExpr = ((AssignStmt) node.unit).getInvokeExpr();

                    if (ConditionUtils.compareMethodsMapInputArg.containsKey(invokeExpr.getMethod().getSignature())
                            & !descriptor.sourcesTaintGraph.matchTaintedSources(thisValueBox.getValue()).isEmpty()) {
                        ValueBox argValueBox = Parameter.getArgValueBox(node, 0);
                        if (argValueBox != null)
                            methodName = argValueBox.getValue().toString().replaceAll("\"","");
                    }
                }
            }
        }

        return methodName;
    }

}
