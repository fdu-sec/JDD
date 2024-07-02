package gadgets.collection;

import tranModel.Rules.RuleUtils;
import tranModel.TransformableNode;
import cfg.CFG;
import cfg.Node;
import container.BasicDataContainer;
import dataflow.node.MethodDescriptor;
import dataflow.node.SourceNode;
import gadgets.collection.node.ClassNode;
import gadgets.collection.node.GadgetInfoRecord;
import util.Pair;
import soot.*;
import soot.jimple.IfStmt;
import soot.jimple.Stmt;
import util.ClassRelationshipUtils;
import util.StaticAnalyzeUtils.ClassUtils;
import util.Utils;

import java.util.*;

public class AnalyzeUtils {

    public static SootMethod getNextMethod(LinkedList<SootMethod> callStack, LinkedList<SootMethod> methodStack){
        SootMethod ret = null;
        SootMethod curMtd = callStack.getLast();
        if (Utils.isSubList(callStack, methodStack) & curMtd != null){
            int index = methodStack.indexOf(curMtd);
            if (index + 1 <= callStack.size()){
                if (callStack.size() < methodStack.size())
                    ret = methodStack.get(callStack.size());
            }
            else if (index+1 < methodStack.size()) {
                ret = methodStack.get(index + 1);
            }
        }

        return ret;
    }

    public static SootMethod getNextMethod(LinkedList<SootMethod> callStack, SootMethod sootMethod){
        int index = callStack.indexOf(sootMethod);
        SootMethod next = null;
        if (index+1 < callStack.size()) {
            next = callStack.get(index + 1);
        }
        return next;
    }

    public static SootMethod getPreMethod(LinkedList<SootMethod> callStack, SootMethod curMtd){
        int index = callStack.indexOf(curMtd);
        SootMethod pre = null;
        if (index-1 >= 0){
            pre = callStack.get(index - 1);
        }
        return pre;
    }


    public static SootClass getActualFieldClassFollowsCallStack(SootMethod curMethod, LinkedList<SootMethod> chain) {
        SootMethod next = getNextMethod(chain, curMethod);
        SootMethod nextNext =  getNextMethod(chain, next);
        if (next ==null | nextNext == null)
            return null;

        if (next.isStatic() | nextNext.isStatic())
            return null;

        // 1. 下一个方法的类是前一个方法的类的子类
        if(!ClassUtils.getAllSupers(nextNext.getDeclaringClass()).contains(next.getDeclaringClass()))
            return null;
        // 2. 下下一个方法的类不能有next方法类的该方法
        if (nextNext.getDeclaringClass().getMethodUnsafe(next.getSubSignature()) != null)
            return null;

        return nextNext.getDeclaringClass();

    }

    public static Pair<SourceNode, HashSet<SourceNode>> matchFieldSourceNode(ValueBox valueBox, MethodDescriptor descriptor, SootClass fieldTypeOfClass){
        if (valueBox == null)
            return null;

        Value value = valueBox.getValue();
        SourceNode fieldSourceNode = null;

        HashSet<SourceNode> fieldSources = RuleUtils.getTaintedFieldSources(value, descriptor);
        HashSet<SourceNode> candidates = new HashSet<>();
        for (SourceNode tmpFieldSourceNode : fieldSources) {
            SootClass tmpSourceFieldTypeOfClass = Utils.toSootClass(tmpFieldSourceNode.getType());
            if (tmpSourceFieldTypeOfClass == null)
                continue;

            if (tmpSourceFieldTypeOfClass.equals(fieldTypeOfClass)) {
                fieldSourceNode = tmpFieldSourceNode;
                candidates.add(tmpFieldSourceNode);
                break;
            }

            if (ClassUtils.getAllSupers(fieldTypeOfClass).contains(tmpSourceFieldTypeOfClass)
                    | ClassUtils.getAllSupers(tmpSourceFieldTypeOfClass).contains(fieldTypeOfClass)
                    & !tmpSourceFieldTypeOfClass.getName().contains("java.lang.Object")) {
                fieldSourceNode = tmpFieldSourceNode;
                candidates.add(tmpFieldSourceNode);
                break;
            }

            String tmpTypeString = tmpFieldSourceNode.getType().toString();
            if (tmpTypeString.equals("java.lang.Object")
                    | tmpTypeString.equals("java.lang.Object[]")
                    | ClassRelationshipUtils.isSubClassOf(
                    tmpSourceFieldTypeOfClass, BasicDataContainer.commonClassMap.get("Map"))
                    | ClassRelationshipUtils.isSubClassOf(
                    tmpSourceFieldTypeOfClass, BasicDataContainer.commonClassMap.get("List"))) {
                fieldSourceNode = tmpFieldSourceNode;
                candidates.add(tmpFieldSourceNode);
            }
        }

        return new Pair<>(fieldSourceNode, candidates);
    }

    public static Stmt getOtherSucStmt(TransformableNode tfNode, Stmt target) {
        if (!(tfNode.node.unit instanceof IfStmt))  return null;

        for (TransformableNode sucTfNode : tfNode.successors){
            Stmt tmpStmt = (Stmt) sucTfNode.node.unit;
            if (!tmpStmt.equals(target))
                return tmpStmt;
        }

        return null;
    }


    public static SootClass getClassByPointer(Value value, MethodDescriptor descriptor){
        if (descriptor.pointTable.contains(value))
            return Utils.toSootClass(descriptor.pointTable.getPointer(value).getType());
        return null;
    }


    public static Pair<String, Integer> getUsedSite(TransformableNode tfNode) {
        return new Pair<>(tfNode.context.sootClass.getName(), getLineNumberByUnit(tfNode.node.unit));
    }

    public static Integer getLineNumberByUnit(Unit unit) {
        return unit.getJavaSourceStartLineNumber();
    }



    public static HashMap<IfStmt, Integer> getLineNumberOfIfStmts(SootMethod sootMethod){
        HashMap<IfStmt, Integer> ifStmtHashCodeMap = new HashMap<>();
        List<IfStmt> ifStmts = new ArrayList<>();
        if (!sootMethod.hasActiveBody())
            return ifStmtHashCodeMap;

        for (Unit unit: sootMethod.retrieveActiveBody().getUnits()){
            if (unit instanceof IfStmt)
                ifStmts.add((IfStmt) unit);
        }

        for (IfStmt ifStmt: ifStmts){
            ifStmtHashCodeMap.put(ifStmt, getLineNumberByUnit(ifStmt));
        }

        return ifStmtHashCodeMap;
    }

    public static HashMap<IfStmt, Node> getIfStmtNodeMap(SootMethod sootMethod){
        CFG cfg = new CFG(sootMethod, true);
        cfg.buildCFG();

        HashMap<IfStmt, Node> ret = new HashMap<>();
        for (Node node: cfg.allNodes.values()){
            Unit unit = node.unit;
            if (unit instanceof IfStmt)
                ret.put((IfStmt) unit, node);
        }
        return ret;
    }

    public static boolean isTmpGeneratedObj(ValueBox valueBox, MethodDescriptor descriptor){
        if (valueBox == null)
            return false;

        if (descriptor.tempGeneratedObjs.contains(valueBox.getValue()))
            return true;

        return false;
    }


    public static ClassNode getClassNode(SootClass preClass,
                                         SootClass curClass,
                                         SourceNode sourceNode,
                                         GadgetInfoRecord gadgetInfoRecord){
        ClassNode curClassNode = gadgetInfoRecord.getClassNode(preClass, curClass);
        if (curClassNode == null)
            return null;

        if (!ClassRelationshipUtils.isSubClassOf(curClassNode.sootClass, sourceNode.classOfField)){
            for (SourceNode fieldSourceNode: curClassNode.implicitFields.keySet()){
                for (ClassNode implicitClassNode: curClassNode.implicitFields.get(fieldSourceNode)){
                    if (ClassRelationshipUtils.isSubClassOf(implicitClassNode.sootClass, sourceNode.classOfField)){
                        return implicitClassNode;
                    }
                }
            }
        }

        return curClassNode;
    }

    public static SootMethod getHashCodeMtd(SootClass sootClass){
        SootMethod mtd = sootClass.getMethodUnsafe("int hashCode()");
        if (mtd != null)
            return mtd;

        for (SootClass superClz: ClassUtils.getAllSupers(sootClass)){
            if (superClz.getName().equals("java.lang.Object"))
                continue;
            mtd = superClz.getMethodUnsafe("int hashCode()");
            if (mtd != null) {
                return mtd;
            }
        }
        return null;
    }

    public static SootMethod getEqualsMtd(SootClass sootClass){
        SootMethod mtd = sootClass.getMethodUnsafe("boolean equals(java.lang.Object)");
        if (mtd != null)
            return mtd;

        for (SootClass superClz: ClassUtils.getAllSupers(sootClass)){
            if (superClz.getName().equals("java.lang.Object"))
                continue;
            mtd = superClz.getMethodUnsafe("boolean equals(java.lang.Object)");
            if (mtd != null) {
                return mtd;
            }
        }
        return null;
    }

    public static int getMtdNum(LinkedList<SootMethod> chain, String subMethodSig){
        int count = 0;
        for (SootMethod sootMethod: chain){
            if (sootMethod == null)
                continue;
            if (sootMethod.getSubSignature().equals(subMethodSig))
                count ++;
        }
        return count;
    }
}
