package tranModel.Rules;

import PointToAnalyze.pointer.Pointer;
import soot.*;
import tranModel.Rule;
import tranModel.Taint.Taint;
import tranModel.Transformable;
import tranModel.TransformableNode;
import container.BasicDataContainer;
import dataflow.node.MethodDescriptor;
import dataflow.node.SourceNode;
import lombok.extern.slf4j.Slf4j;
import rules.sinks.FileCheckRule;
import soot.jimple.*;
import soot.jimple.internal.JArrayRef;
import soot.jimple.internal.JInstanceFieldRef;
import soot.jimple.internal.JNewArrayExpr;
import util.ClassRelationshipUtils;
import util.StaticAnalyzeUtils.FieldUtil;
import util.StaticAnalyzeUtils.Parameter;
import util.Utils;

import java.util.*;

@Slf4j
public class TaintSpreadRule implements Rule {
    @Override
    public void apply(Transformable transformable, MethodDescriptor descriptor) {
        TransformableNode transformableNode = (TransformableNode) transformable;
        Stmt stmt = (Stmt) transformableNode.node.unit;

        // 1. Assign
        if (stmt instanceof AssignStmt){
            AssignStmt assignStmt = (AssignStmt) stmt;
            Value left = assignStmt.getLeftOp();
            Value right = assignStmt.getRightOp();

            // (1-1) 如果是Array类型的, 不考虑第几个元素污染
            if (left instanceof JArrayRef)
                left = ((JArrayRef) left).getBase();
            if (right instanceof JArrayRef) {
                right = ((JArrayRef) right).getBase();
            }


            if (Utils.isTainted(left,descriptor.taints) & Utils.isTainted(right,descriptor.taints)){
                descriptor.sourcesTaintGraph.recordSourceInfluence(left, right);
            }


            if (right instanceof JInstanceFieldRef){
                JInstanceFieldRef jInstanceFieldRef = (JInstanceFieldRef) right;
                Value object = jInstanceFieldRef.getBase();
                SootField sootField = jInstanceFieldRef.getField();
                // 匹配所有可能的Taint, 并考虑fields敏感, 为left生成新的污点
                for (Taint taint: descriptor.getAllTaintsAboutThisValue(object)){
                    LinkedList<SootField> tryMatch = taint.match(object,sootField);
                    if (tryMatch != null){
                        Taint newTaint = descriptor.getOrCreateTaint(left,tryMatch);
                        RuleUtils.addTaint(descriptor, newTaint);
                        if (BasicDataContainer.infosCollect){
                            RuleUtils.createAndAddSourceNode(sootField, newTaint, object, descriptor);
                        }
                    }
                }
            }
            else if (left instanceof JInstanceFieldRef){
                JInstanceFieldRef jInstanceFieldRef = (JInstanceFieldRef) left;
                Value object = jInstanceFieldRef.getBase();
                SootField field = jInstanceFieldRef.getField();

                for (Taint taint: descriptor.getAllTaintsAboutThisValue(right)){
                    LinkedList<SootField> accessPath = new LinkedList<>();
                    // 对于一些内部类方法, 会将某个变量传递进去赋给this, 此时不记录fields敏感信息(为了在生成时, 提供生成field.field的条件)
                    if (!field.getName().equals("this$0"))
                        accessPath.add(field);

                    accessPath.addAll(taint.accessPath);
                    Taint newTaint = descriptor.getOrCreateTaint(object,accessPath);
                    RuleUtils.addTaint(descriptor, newTaint);
                    if (BasicDataContainer.infosCollect){
                        if (!RuleUtils.isInitMtdTaintSourceRecord(field, right, descriptor))
                            descriptor.sourcesTaintGraph.recordSourceInfluence(left, right);
                    }
                }
            }
            else if (right instanceof CastExpr){ // 强制类型转换
                Value object = ((CastExpr) right).getOp(); // 取被强制转换的对象, 进行污点匹配

                for (Taint taint: descriptor.getAllTaintsAboutThisValue(object)){
                    Taint newTaint = descriptor.getOrCreateTaint(left, new LinkedList<>(taint.accessPath));
                    RuleUtils.addTaint(descriptor,newTaint);

                    if (BasicDataContainer.infosCollect){
                        descriptor.sourcesTaintGraph.addTaintedSourceNode(left, object);
                    }
                }
            }
//            else if (right instanceof NewArrayExpr){
//                // TODO: 对于 array 类型的是否需要记录size的关联, 如何记录比较合适?
//            }
            else if (right instanceof BinopExpr){
                for (ValueBox opValueBox: ((BinopExpr) right).getUseBoxes()){
                    if (opValueBox == null)
                        continue;
                    for (Taint taint: descriptor.getAllTaintsAboutThisValue(opValueBox.getValue())) {
                        LinkedList<SootField> accessPath = new LinkedList<>(taint.accessPath);
                        Taint newTaint = descriptor.getOrCreateTaint(left, accessPath);
                        RuleUtils.addTaint(descriptor, newTaint);

                        if (BasicDataContainer.infosCollect)
                            descriptor.sourcesTaintGraph.addTaintedSourceNode(left, opValueBox.getValue());
                    }
                }
            }
            else if (right instanceof LengthExpr){
                Value arrayValue = ((LengthExpr) right).getOp();
                for (Taint taint: descriptor.getAllTaintsAboutThisValue(arrayValue)){
                    LinkedList<SootField> accessPath = new LinkedList<>(taint.accessPath);
                    Taint newTaint = descriptor.getOrCreateTaint(left, accessPath);
                    RuleUtils.addTaint(descriptor, newTaint);

                    if (BasicDataContainer.infosCollect){
                        descriptor.sourcesTaintGraph.addTaintedSourceNode(left, right);
                    }
                }
            }
            // 对于常量, 记录源, 不记录为污点
            else if (right instanceof Constant){
                if (BasicDataContainer.infosCollect) {
                    SourceNode newSourceNode = new SourceNode(right);
                    descriptor.sourcesTaintGraph.addTaintedSourceNode(newSourceNode, left);
                }
            }
            // 不记录污点，仅记录来源
            else if (right instanceof JNewArrayExpr){
                Value sizeValue = ((JNewArrayExpr) right).getSize();
                descriptor.sourcesTaintGraph.addTaintedSourceNode(left, sizeValue);
            }
            else {
                // 直接相等的情况
                for (Taint taint: descriptor.getAllTaintsAboutThisValue(right)){
                    LinkedList<SootField> accessPath = new LinkedList<>(taint.accessPath);
                    Taint newTaint = descriptor.getOrCreateTaint(left,accessPath);
                    RuleUtils.addTaint(descriptor, newTaint);

                    if (BasicDataContainer.infosCollect){
                        descriptor.sourcesTaintGraph.addTaintedSourceNode(left, right);
                    }
                }
            }
        }

        // 2. Return, 记录返回的污点
        if (stmt instanceof ReturnStmt){
            for (ValueBox valueBox : stmt.getUseBoxes()) {
                descriptor.retTainted.addAll(descriptor.getAllTaintsAboutThisValue(valueBox.getValue()));
            }
            descriptor.returnStmt = (ReturnStmt) stmt;
        }

        // 3. (a = ) f(taint,...)
        if (stmt.containsInvokeExpr()){
            InvokeExpr invokeExpr = stmt.getInvokeExpr();
            SootMethod invokedMethod = invokeExpr.getMethod();
            RuleUtils.applySpreadRules(descriptor, stmt);
            // 对File的处理
            if (FileCheckRule.fileClassNames.contains(invokedMethod.getDeclaringClass().getName())){
                if (invokeExpr.getMethod().getName().equals("<init>")){
                    ValueBox pathValueBox = Parameter.getArgByType(invokeExpr, "java.lang.String");
                    ValueBox fileValueBox = Parameter.getArgByType(invokeExpr, "java.io.File");
                    ValueBox thisValueBox = Parameter.getThisValueBox(transformableNode.node);
                    if (pathValueBox != null & fileValueBox == null & thisValueBox != null){
                        if (Utils.isTainted(pathValueBox.getValue(), descriptor.taints)){
                            RuleUtils.addTaint(thisValueBox.getValue(), new LinkedList<>(), descriptor);

                            if (BasicDataContainer.infosCollect){
                                descriptor.sourcesTaintGraph.addTaintedSourceNode(thisValueBox.getValue(), pathValueBox.getValue());
                            }
                        }
                    }
                    else if (pathValueBox == null & fileValueBox != null & thisValueBox != null){
                        if (Utils.isTainted(fileValueBox.getValue(), descriptor.taints)){
                            RuleUtils.addTaint(thisValueBox.getValue(), new LinkedList<>(), descriptor);

                            if (BasicDataContainer.infosCollect){
                                descriptor.sourcesTaintGraph.addTaintedSourceNode(thisValueBox.getValue(), fileValueBox.getValue());
                            }
                        }
                    }
                    else if (pathValueBox != null & fileValueBox != null & thisValueBox != null){
                        Value arg0 = invokeExpr.getArg(0);
                        if (Utils.isTainted(arg0, descriptor.taints)
                                & (arg0.equals(pathValueBox.getValue()) | arg0.equals(fileValueBox.getValue()))){
                            RuleUtils.addTaint(thisValueBox.getValue(), new LinkedList<>(), descriptor);

                            if (BasicDataContainer.infosCollect){
                                descriptor.sourcesTaintGraph.addTaintedSourceNode(thisValueBox.getValue(), arg0);
                            }
                        }
                    }
                }
            }

            // 对Map的entrySet()进行特殊处理
            // <java.util.Map: java.util.Set entrySet()>
            if (invokedMethod.getSubSignature().equals("java.util.Set entrySet()")){
                ValueBox thisValueBox = Parameter.getThisValueBox(transformableNode.node);
                Value retValue = Parameter.getReturnedValue(transformableNode.node);
                if (thisValueBox != null & retValue != null){
                    HashSet<SourceNode> taitSourceNodes = descriptor.sourcesTaintGraph.matchTaintedSources(thisValueBox.getValue());
                    if (!taitSourceNodes.isEmpty())
                        descriptor.sourcesTaintGraph.createAndAddSourceNode(thisValueBox.getValue(), retValue, false, true);
                    else {
                        // 启发式匹配
                        SootClass sootClass = null;
                        Pointer pointer = descriptor.pointTable.getPointer(thisValueBox.getValue());
                        if (thisValueBox.getValue().equals(descriptor.paramIdMapLocalValue.get(-1))){
                            sootClass = descriptor.getCurrentClass();
                        }
                        else if (pointer != null){
                            sootClass = Utils.toSootClass(pointer.getType());
                        }else {
                            sootClass = Utils.toSootClass(thisValueBox.getValue().getType());
                        }
                        if (sootClass != null) {
                            for (SootField sootField : FieldUtil.getAllDeclaredFields(sootClass)) {
                                if (!sootField.getType().toString().endsWith("[]"))
                                    continue;

                                SootClass classOfArrayElement = Utils.toSootClass(sootField.getType());
                                if (ClassRelationshipUtils.isSubClassOf(classOfArrayElement, BasicDataContainer.commonClassMap.get("Entry"))){
                                    SourceNode newSourceNode = SourceNode.createFieldSourceNode(sootField, sootClass);
                                    descriptor.sourcesTaintGraph.addTaintedSourceNode(newSourceNode, retValue);
                                    break;
                                }
                            }
                        }
                    }
                }
            }

            // 记录临时创建的对象: 不必检查是否能被序列化, 因为本身即是程序执行过程中自动动态生成的
            if (invokedMethod.getName().equals("getInstance") & invokedMethod.isStatic()){
                Value retValue = Parameter.getReturnedValue(stmt);
                if (retValue != null)
                    descriptor.tempGeneratedObjs.add(retValue);
            }
        }
    }
}
