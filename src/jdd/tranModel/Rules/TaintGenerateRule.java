package tranModel.Rules;

import PointToAnalyze.pointer.Pointer;
import tranModel.Rule;
import tranModel.Taint.Taint;
import tranModel.Transformable;
import tranModel.TransformableNode;
import container.BasicDataContainer;
import container.FieldsContainer;
import dataflow.DataflowDetect;
import dataflow.node.MethodDescriptor;
import dataflow.node.SourceNode;
import lombok.extern.slf4j.Slf4j;
import markers.Stage;
import soot.*;
import soot.jimple.*;
import soot.jimple.internal.JInstanceFieldRef;
import util.ClassRelationshipUtils;
import util.StaticAnalyzeUtils.FieldUtil;
import util.StaticAnalyzeUtils.Parameter;

import java.util.HashSet;
import java.util.LinkedList;

@Slf4j
public class TaintGenerateRule implements Rule {
    public static boolean fieldGenerate = false;

    public HashSet<String> readObjectSigs = new HashSet<>();
    public HashSet<String> getFieldsFromInputSigs = new HashSet<>();

    public TaintGenerateRule(){
        readObjectSigs = ClassRelationshipUtils.getAllSubMethodSigs("<java.io.ObjectInput: java.lang.Object readObject()>");
        getFieldsFromInputSigs.addAll(ClassRelationshipUtils.getAllSubMethodSigs("<java.io.ObjectInputStream$GetField: java.lang.Object get(java.lang.String,java.lang.Object)>"));
        for (String tmpMtdSig: getFieldsFromInputSigs){
            if (!Scene.v().containsMethod(tmpMtdSig))
                continue;
            SootMethod tmpMtd = Scene.v().getMethod(tmpMtdSig);
            SootClass tmpSootClass = tmpMtd.getDeclaringClass();
            for (SootMethod tmpMtdIn: tmpSootClass.getMethods()){
                BasicDataContainer.blackList.add(tmpMtdIn.getSignature());
            }
        }
    }

    /**
     * 将field / ObjectInputStream 作为污点源
     * @param transformable
     * @param descriptor
     */
    @Override
    public void apply(Transformable transformable, MethodDescriptor descriptor) {

        TransformableNode tfNode = (TransformableNode) transformable;

        Unit currentUnit = tfNode.node.unit; // 考虑到有些方法处理的是Stmt的父类Unit，为了避免错误做这步处理
        Stmt currentStmt = (Stmt) currentUnit;

        // 处理赋值语句
        // Step1: 进行框架入口点的检测

        if (currentStmt instanceof AssignStmt) {
            Value left = ((AssignStmt) currentStmt).getLeftOp();
            Value right = ((AssignStmt) currentStmt).getRightOp();

            // 1. 当调用方法时: (a) 跟踪不进去的方法处理; (b) readObject等相关方法的污点处理
            if (currentStmt.containsInvokeExpr()){
                SootMethod invokedMethod = tfNode.getUnitInvokeExpr().getMethod();
//                TODO: (a) 先不处理, 观察一下是否还存在该问题

                boolean generateFlag = false; // 判断是否能生成污点的标识符
                ValueBox thisValueBox = Parameter.getThisValueBox(currentStmt);
                if (thisValueBox != null){
                    for (Taint taint: descriptor.getAllTaintsAboutThisValue(thisValueBox.getValue())){
                        if (taint.accessPath.isEmpty()){
                            generateFlag = true;
                            break;
                        }
                    }
                }

                if (generateFlag){
                    Taint newTaint = descriptor.getOrCreateTaint(left, new LinkedList<>());
                    RuleUtils.addTaint(descriptor, newTaint);

                    // (b-1) 为ObjectInput.readObject()读出的对象
                    // (b-2) ObjectInputStream.GetField.get("fieldName",), 根据第一个参数获得field的名称, 然后取出对应的SootField
                    // 从FieldsContainer中查找(根据全局信息)
                    if (readObjectSigs.contains(invokedMethod.getSignature())) {
                        if (BasicDataContainer.infosCollect) { // TODO: 找不到的话, 尝试根据类型匹配
                            // TODO: 去 FieldsContainer.fieldRefValuesMap 中查找
                            SootField sootField = FieldsContainer.getSootFieldRefByStream(left, descriptor.sootMethod);
                            RuleUtils.createAndAddSourceNode(sootField, newTaint, null, descriptor);
                            if (BasicDataContainer.stage.equals(Stage.IOCD_GENERATING)
                                | BasicDataContainer.stage.equals(Stage.IOCD_SUPPLEMENT_INFER)){
                                descriptor.sourcesTaintGraph.sourceUnFound.put(
                                        ((AssignStmt) currentStmt).getLeftOpBox(), tfNode
                                );
                            }
//                        SourceNode newSourceNode = RuleUtils.createSourceNode(sootField, newTaint);
//                        descriptor.sourcesTaintGraph.addTaintedSourceNode(newSourceNode, left);
                        }
                    }else if (getFieldsFromInputSigs.contains(invokedMethod.getSignature())){
                        SootClass sootClass = descriptor.getCurrentClass();
                        SootField sootField = null;

                        Value fieldNameValue = currentStmt.getInvokeExpr().getArg(0);
                        if (sootClass != null & fieldNameValue instanceof Constant){
                            sootField = FieldUtil.getSootFieldByName(sootClass, fieldNameValue);
                            RuleUtils.createAndAddSourceNode(sootField, newTaint, null, descriptor);
                        }
                    }
                }

            }
            else if (right instanceof FieldRef){
                boolean generateFlag = false;
                if (descriptor.paramIdMapLocalValue.containsKey(-1)){
                    for (Taint taint: descriptor.getAllTaintsAboutThisValue(descriptor.paramIdMapLocalValue.get(-1))){
                        if (taint.accessPath.isEmpty()) {
                            generateFlag = true;
                            break;
                        }
                    }
                }

                if (generateFlag) {
                    if (right instanceof JInstanceFieldRef) {
                        SootField sootField = ((FieldRef) right).getField();
                        Value basedObj = ((JInstanceFieldRef) right).getBase();
                        // 如果 basedObj 不是this，则进行field.field查找
                        LinkedList<SootField> accessPath = new LinkedList<>();
                        if (BasicDataContainer.stage.equals(Stage.IOCD_GENERATING)
                                | BasicDataContainer.stage.equals(Stage.IOCD_SUPPLEMENT_INFER))
                            accessPath = RuleUtils.getAccessPath(basedObj, sootField, descriptor);

                        Taint newTaint = descriptor.getOrCreateTaint(left, accessPath);
                        RuleUtils.addTaint(descriptor, newTaint);

                        Pointer pointer = FieldsContainer.getFieldPointer(sootField, descriptor.getCurrentClass());
                        descriptor.pointTable.setPointer( newTaint, pointer);

                        if (BasicDataContainer.infosCollect) {
                            RuleUtils.createAndAddSourceNode(sootField, newTaint,
                                    ((JInstanceFieldRef) right).getBase(), descriptor);
//                    SourceNode newSourceNode = RuleUtils.createSourceNode(sootField, newTaint);
//                    descriptor.sourcesTaintGraph.addTaintedSourceNode(newSourceNode,left);
                        }
                    }
                    // 3. 其他情况, 包括静态field, 不直接生成污点 (static field在反序列化过程中无法控制)
                    else if (right instanceof StaticFieldRef){
                        SootField sootField = ((StaticFieldRef) right).getField();
                        Value recordedValue = FieldsContainer.getStaticSootFieldInfo(sootField, descriptor.getCurrentClass());
                        if (recordedValue != null){
                            // 静态fields仅记录其为常数的情况, 因为为变量的话, 攻击者也无法控制
                            if (recordedValue instanceof Constant){
                                SourceNode sourceNode = new SourceNode(recordedValue);
//                                sourceNode.constant = recordedValue;
                                descriptor.sourcesTaintGraph.addTaintedSourceNode(sourceNode,left);
                            }
                        }
                    }
                    else {
                        log.info("--- FieldRef in TaintGenerateRule: "+ right);
                    }
                }
            }
        }

        if (BasicDataContainer.infosCollect & descriptor.isEntry){
            if (currentStmt instanceof IdentityStmt){
                IdentityStmt identityStmt = (IdentityStmt) currentStmt;
                Value left = identityStmt.getLeftOp();
                Value right = identityStmt.getRightOp();

                if (right instanceof ParameterRef){
                    int ind = ((ParameterRef) right).getIndex();
                    SourceNode sourceNode = new SourceNode(ind, descriptor.sourcesTaintGraph.entryMethod);
                    descriptor.sourcesTaintGraph.addTaintedSourceNode(sourceNode,left);
                }
            }
        }
    }
}
