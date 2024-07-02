package tranModel.Rules;

import PointToAnalyze.pointer.Pointer;
import soot.*;
import tranModel.Rule;
import tranModel.Taint.Taint;
import tranModel.Transformable;
import tranModel.TransformableNode;
import container.BasicDataContainer;
import container.FieldsContainer;
import dataflow.node.MethodDescriptor;
import soot.jimple.*;
import soot.jimple.internal.JAssignStmt;
import soot.jimple.internal.JIdentityStmt;
import soot.jimple.internal.JInstanceFieldRef;
import util.ClassRelationshipUtils;
import markers.RelationShip;
import util.Utils;

public class AliasAndPointerRule implements Rule {

    @Override
    public void apply(Transformable transformable, MethodDescriptor descriptor) {
        TransformableNode tfNode = (TransformableNode) transformable;

        Stmt stmt = (Stmt) tfNode.node.unit;
        if (stmt instanceof AssignStmt){
            AssignStmt assignStmt = (AssignStmt) stmt;
            Value left = assignStmt.getLeftOp();
            Value right = assignStmt.getRightOp();

            if (right instanceof JInstanceFieldRef){
                // a = taint.field
                JInstanceFieldRef jInstanceFieldRef = (JInstanceFieldRef) right;
                Value object = jInstanceFieldRef.getBase();
                SootField sootField = jInstanceFieldRef.getField();
                // 创建污点(存储在allTaints: 记录所有的“污点”, 其中的污点并并不都是实际被污染的)
                Taint leftTaint = descriptor.getOrCreateTaint(left,null);
                Taint rightTaint = descriptor.getOrCreateTaint(object, Utils.toLinkedList(sootField));

                if (BasicDataContainer.openAliasAnalysis) {
                    leftTaint.aliases.add(rightTaint);
                }

                // 补充别名指针信息
                recordPointer(rightTaint,leftTaint, descriptor);
            }
            else if (right instanceof StaticFieldRef){
                SootField sootField = ((StaticFieldRef) right).getField();
                Pointer pointer = FieldsContainer.getFieldPointer(sootField, descriptor.getCurrentClass());
                if (pointer != null){ // 不为常量的情况, 记录指针信息
                    descriptor.pointTable.setPointer(left, pointer);
                }

                if (BasicDataContainer.openAliasAnalysis){
                    Taint leftTaint = descriptor.getOrCreateTaint(left,null);
                    Taint rightTaint = descriptor.getOrCreateTaint(descriptor.paramIdMapLocalValue.get(-1), Utils.toLinkedList(sootField));
                    leftTaint.aliases.add(rightTaint);
                }

            }
            else if (left instanceof JInstanceFieldRef){
                JInstanceFieldRef jInstanceFieldRef = (JInstanceFieldRef) left;
                Value object = jInstanceFieldRef.getBase();
                SootField sootField = jInstanceFieldRef.getField();

                Taint rightTaint = descriptor.getOrCreateTaint(right,null);
                Taint leftTaint = descriptor.getOrCreateTaint(object,Utils.toLinkedList(sootField));
                if (BasicDataContainer.openAliasAnalysis)
                    leftTaint.aliases.add(rightTaint);

                recordPointer(rightTaint,leftTaint,descriptor);

            }
            else if (left instanceof StaticFieldRef){
                SootField sootField = ((StaticFieldRef) left).getField();
                if (BasicDataContainer.openAliasAnalysis){
                    Taint leftTaint = descriptor.getOrCreateTaint(left,null);
                    Taint rightTaint = descriptor.getOrCreateTaint(descriptor.paramIdMapLocalValue.get(-1), Utils.toLinkedList(sootField));
                    leftTaint.aliases.add(rightTaint);
                }

                Pointer pointer = FieldsContainer.getFieldPointer(sootField, descriptor.getCurrentClass());
                if (pointer != null)
                    descriptor.pointTable.setPointer(left, pointer);
            }

            else if (right instanceof NewExpr){
                RefType refType = ((NewExpr) right).getBaseType();
                Type type = ((NewExpr) right).getType();
                Pointer pointer = new Pointer(type, refType);
                descriptor.pointTable.setPointer(left, pointer);
            }
            // 强制类型转换
            else if (right instanceof CastExpr){
                Value rightValue = ((CastExpr)right).getOp();
                Pointer pointer = new Pointer(((CastExpr)right).getCastType());
                descriptor.pointTable.setPointer(left, pointer);
                // 如果right的类型和强制转换的并不完全兼容，则也加入记录
                if (descriptor.pointTable.contains(rightValue)) {
                    SootClass castClass = Utils.toSootClass(((CastExpr) right).getCastType());
                    Pointer pointerRight = descriptor.pointTable.getPointer(rightValue);
                    SootClass rightValueType = Utils.toSootClass(pointerRight.getType());
                    if (ClassRelationshipUtils.getExtentRelationshipAmongClasses(castClass, rightValueType).equals(RelationShip.HAS_SAME_SUB)){
                        pointer.addExtraType(pointerRight.getType());
                    }
                }

                if (BasicDataContainer.openAliasAnalysis){
                    Taint rightTaint = descriptor.getOrCreateTaint(right,null);
                    Taint leftTaint = descriptor.getOrCreateTaint(left,null);
                    leftTaint.aliases.add(rightTaint);
                }
            }
            else if (stmt.containsInvokeExpr()){
                Pointer pointer = new Pointer( stmt.getInvokeExpr().getMethod().getReturnType());
                descriptor.pointTable.setPointer(left,pointer);
            }
            else {
                if (right instanceof ArrayRef)
                    right = ((ArrayRef) right).getBase();
                if (left instanceof ArrayRef)
                    left = ((ArrayRef) left).getBase();
                recordPointer(right,left,descriptor);
                if (BasicDataContainer.openAliasAnalysis){
                    Taint rightTaint = descriptor.getOrCreateTaint(right,null);
                    Taint leftTaint = descriptor.getOrCreateTaint(left,null);
                    leftTaint.aliases.add(rightTaint);
                }
            }
        }

        if (stmt instanceof JIdentityStmt){
            JIdentityStmt jIdentityStmt = (JIdentityStmt) stmt;
            Value left = jIdentityStmt.getLeftOp();
            Value right = jIdentityStmt.getRightOp();

            recordPointer(right, left, descriptor);

            if (BasicDataContainer.openAliasAnalysis){
                Taint rightTaint = descriptor.getOrCreateTaint(right,null);
                Taint leftTaint = descriptor.getOrCreateTaint(left,null);
                leftTaint.aliases.add(rightTaint);
            }
        }

        if (stmt instanceof JAssignStmt){
        }
        if (stmt instanceof NewExpr){

        }
    }

    public static void recordPointer(Value from, Value to, MethodDescriptor descriptor){
        if (!descriptor.pointTable.setPointer(from, to)){
            Pointer pointer = new Pointer(from.getType());
            descriptor.pointTable.setPointer(to,pointer);
        }
    }

    public static void recordPointer(Taint from, Taint to, MethodDescriptor descriptor){
        if (!descriptor.pointTable.setPointer(from,to)){
            Pointer pointer = new Pointer(from.getType());
            descriptor.pointTable.setPointer(to,pointer);
        }
    }
}
