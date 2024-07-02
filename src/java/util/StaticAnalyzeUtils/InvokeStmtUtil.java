package util.StaticAnalyzeUtils;

import tranModel.TransformableNode;
import cfg.Node;
import soot.*;
import soot.jimple.Stmt;
import util.ClassRelationshipUtils;

import java.util.Arrays;
import java.util.HashSet;
import java.util.Set;

/**
 * 静态分析基本能力
 */
public class InvokeStmtUtil {

    public static ValueBox getObjectValueBox(Unit unit){
        for(ValueBox valueBox : unit.getUseBoxes()){
            if(valueBox.toString().contains("JimpleLocalBox")) return valueBox;
        }
        return null;
    }

    public static ValueBox getArgValueBox(Unit unit, int argIndex){
        if(!((Stmt) unit).containsInvokeExpr()) return null;
        return  ((Stmt) unit).getInvokeExpr().getArgBox(argIndex);
    }

    public static String getDefVariableName(Node node){
        if(node.unit.getDefBoxes().isEmpty()) return null;
        return node.unit.getDefBoxes().get(0).getValue().toString();
    }

    public static HashSet<ValueBox> getAllArgValueBoxes(Unit unit){
        HashSet<ValueBox> ret = new HashSet<>();
        if(!((Stmt) unit).containsInvokeExpr()) return ret;
        for(int ind = 0 ; ind < ((Stmt) unit).getInvokeExpr().getArgCount(); ind++){
            ValueBox vb = ((Stmt) unit).getInvokeExpr().getArgBox(ind);
            ret.add(vb);
        }
        return ret;
    }

    public static int getArgIndexByValueBox(Unit unit, ValueBox valueBox){
        if(!((Stmt) unit).containsInvokeExpr()) return -1;
        for(int ind = 0 ; ind < ((Stmt) unit).getInvokeExpr().getArgCount(); ind++){
            ValueBox vb = ((Stmt) unit).getInvokeExpr().getArgBox(ind);
            if(vb.equals(valueBox)) return ind;
        }
        return -1;
    }

    /**
     * 从众多CHA方法中找到来自这个类型的准确实现, 如果它自己没有实现, 找它的父类;
     * 如果type为非具体方法, 则筛选possibleMethods中所属类为type对应的类的子类的
     */
    public static HashSet<SootMethod> findExactMethodFromCHAMethods(Set<SootMethod> possibleMethods, SootClass expectClass,
                                                     TransformableNode tfNode){
        HashSet<SootMethod> ret = new HashSet<>();
        if(expectClass == null | !tfNode.containsInvoke() | possibleMethods.isEmpty()) return ret;

        String invokedMethodSubSig = tfNode.getUnitInvokeExpr().getMethod().getSubSignature();
        String invokedMethodName = tfNode.getUnitInvokeExpr().getMethod().getName();
        // 1. 获取准确的方法实现 [注意: 一般而言, 应该排除java.lang.Object, 此处默认需要排除的话在调用该方法前就排除, 否则即会筛选出Object类的具体方法]
        if (expectClass.isConcrete()){
            for (SootClass sootClass: ClassUtils.getAllSupers(expectClass)){
                SootMethod tmpInvokedMethod = sootClass.getMethodUnsafe(invokedMethodSubSig);
                if (tmpInvokedMethod != null){
                    ret.add(tmpInvokedMethod);
                    break;
                }
            }
        }
        // 2. 如果type为非具体方法, 则筛选possibleMethods中所属类为type对应的类的子类的
        else {
            ret = ClassRelationshipUtils.getAllSubMethods(expectClass, invokedMethodSubSig);
//            ret.retainAll(possibleMethods);
        }

        // 考虑一次取出了init等相关方法的情况, 即不能直接返回, 需要从possibleMethods中保留这些方法
        for (SootMethod tmpInvokedMethod: possibleMethods){
            if (!tmpInvokedMethod.getSubSignature().equals(invokedMethodSubSig)
                    && !tmpInvokedMethod.getName().equals(invokedMethodName))
                ret.add(tmpInvokedMethod);
        }

        return ret;
    }

    /**
     * 针对多个不存在相互包含关系的 expect class 的处理场景
     * @param possibleMethods
     * @param expectClasses
     * @param tfNode
     * @return
     */
    public static HashSet<SootMethod> findExactMethodFromCHAMethods(Set<SootMethod> possibleMethods,
                                                                    HashSet<SootClass> expectClasses,
                                                                    TransformableNode tfNode){
        HashSet<SootMethod> ret = new HashSet<>();
        if(expectClasses.isEmpty()| !tfNode.containsInvoke() | possibleMethods.isEmpty()) return ret;

        SootMethod invokedMethod = tfNode.getUnitInvokeExpr().getMethod();
        String invokedMethodSubSig = tfNode.getUnitInvokeExpr().getMethod().getSubSignature();
        String invokedMethodName = tfNode.getUnitInvokeExpr().getMethod().getName();

        // 求解约束类型之间的共同子类; 默认在指针信息存储的时候就进行过筛选, 存储下来的类约束信息应当是存在"解"的
        // 先进行类型约束求解, 再进一步求解方法
        HashSet<SootClass> sameSubClasses = ClassUtils.getAllSubs(invokedMethod.getDeclaringClass());
        for (SootClass expectClass: expectClasses){
            if (expectClass.isConcrete()) {
                sameSubClasses.retainAll(Arrays.asList(expectClass));
            }
            else {
                sameSubClasses.retainAll(ClassUtils.getAllSubs(expectClass));
            }
        }
        if (sameSubClasses.isEmpty())
            return ret;

        for (SootClass expectClass: sameSubClasses){
            // 直接取方法, 如果没有, 则查找父类
            SootMethod tmpInvokedMethod = expectClass.getMethodUnsafe(invokedMethodSubSig);
            if (tmpInvokedMethod != null) {
                if (tmpInvokedMethod.isConcrete())
                    ret.add(tmpInvokedMethod);
            }
            else {
                for (SootClass superClass: ClassUtils.getAllSupers(expectClass)){
                    tmpInvokedMethod = superClass.getMethodUnsafe(invokedMethodSubSig);
                    if (tmpInvokedMethod != null){
                        if (tmpInvokedMethod.isConcrete())
                            ret.add(tmpInvokedMethod);
                        break;
                    }
                }
            }
        }

        // 考虑一次取出了init等相关方法的情况, 即不能直接返回, 需要从possibleMethods中保留这些方法
        for (SootMethod tmpInvokedMethod: possibleMethods){
            if (!tmpInvokedMethod.getSubSignature().equals(invokedMethodSubSig)
                    && !tmpInvokedMethod.getName().equals(invokedMethodName))
                ret.add(tmpInvokedMethod);
        }

        return ret;
    }

    public static SootMethod findExactMethodFromCHAMethods(SootMethod possibleMethod, String type){
        SootClass expectClass = Scene.v().getSootClassUnsafe(type);
        if (expectClass == null) return null;
        SootMethod sootMethod = expectClass.getMethodUnsafe(possibleMethod.getSubSignature());
        if (sootMethod != null) return sootMethod;

        for (SootClass sootClass: ClassUtils.getAllSupers(expectClass)){
            SootMethod subMethod = sootClass.getMethodUnsafe(possibleMethod.getSubSignature());
            if (subMethod != null)
                return subMethod;
        }
        return null;
    }

    /**
     * 当sootMethod是接口方法时，查找其所有方法实现
     */
    public static HashSet<SootMethod> findConcreteImplementations(SootMethod sootMethod){
        HashSet<SootMethod> implementations = new HashSet<>();
        if (!sootMethod.getDeclaringClass().isInterface())
            return implementations;

        for (SootClass subClass: ClassUtils.getAllSubs_BFS(sootMethod.getDeclaringClass())){
            SootMethod subMethod = subClass.getMethodUnsafe(sootMethod.getSubSignature());
            if (subMethod != null )
                if (subMethod.isConcrete())
                    implementations.add(subMethod);
        }

        return implementations;
    }
    public static HashSet<SootMethod> findConcreteImplementations(SootClass sootClass, String subSig) {
        HashSet<SootMethod> implementations = new HashSet<>();

        for (SootClass subClass: ClassUtils.getAllSubs_BFS(sootClass)){
            SootMethod subMethod = subClass.getMethodUnsafe(subSig);
            if (subMethod != null & subMethod.isConcrete())
                implementations.add(subClass.getMethodUnsafe(subSig));
        }

        return implementations;
    }
}
