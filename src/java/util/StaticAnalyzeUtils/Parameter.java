package util.StaticAnalyzeUtils;

import cfg.CFG;
import cfg.Node;
import dataflow.DataFlow;
import dataflow.Event;
import lombok.extern.slf4j.Slf4j;
import soot.*;
import soot.jimple.*;
import soot.jimple.internal.JAssignStmt;
import tranModel.Transformable;
import tranModel.TransformableNode;

import java.util.*;

/**
 * 静态分析基本能力
 */
@Slf4j
public class Parameter {

    public static HashMap<Integer, Value> getParametersLocalValues(SootMethod sootMethod){
        CFG cfg = new CFG(sootMethod, true);
        cfg.buildCFG();
        return getParametersLocalValues(cfg);
    }

    /**
     * 获取形参/this和与当前方法内局部变量的对应关系
     * 并将这种关系保留于descriptor.paramIdMapLocalValue
     *  返回值中 -1 : this对应的value
     */
    public static HashMap<Integer, Value> getParametersLocalValues(CFG cfg){
        HashMap<Integer, Value> paramMapValue = new HashMap<>();
        for(Node node : cfg.allNodes.values()){
            Integer paramInd = tryGetParamIdentifiedInUnit(node.unit);
            if(paramInd != null) {
                paramMapValue.put(paramInd, node.unit.getDefBoxes().get(0).getValue());
            }
        }
        return paramMapValue;
    }
    public static HashMap<Integer, List<Event>> getParametersMapTaintedEvent(CFG cfg, SootMethod sootMethod){
        int paramCount = sootMethod.getParameterCount();
        HashMap<Integer, List<Event>> paramMapTaintedEvent = new HashMap<>();
        Node node = cfg.headNode;
        for(int i = 0; i < paramCount + 1; i++){
//            log.info("---------------------------");
//            log.info(node.unit);
            Integer paramInd = tryGetParamIdentifiedInUnit(node.unit);
            if(paramInd == null) {
                if(node.successorNodes.size() == 0) break;
                node = node.successorNodes.iterator().next();
                continue;
            }
            if(paramInd == -1) {
                // "this"
                if(node.successorNodes.size() == 0) break;
                node = node.successorNodes.iterator().next();
                continue;
            }
            // affected
            ArrayList<Event> taintedEvent = new ArrayList<>();
            HashMap<Node, ValueBox> tmp = new HashMap<>();
            tmp.put(node, node.unit.getDefBoxes().get(0));
            for(Map.Entry<Node, ValueBox> entry : DataFlow.findAllUnitAndValueAffected(tmp).entrySet()){
//                log.info(entry.getKey());
//                log.info(entry.getValue());
                Event event = new Event(entry.getKey(), entry.getValue());
                taintedEvent.add(event);
            }
            // 直接引用
//            List<Event> taintedEvent = DataFlow.getValueBoxRefEvents(node.unit.getDefBoxes().get(0), node);
            paramMapTaintedEvent.put(paramInd, taintedEvent);
            if(node.successorNodes.size() == 0) break;
            node = node.successorNodes.iterator().next();
        }
        return paramMapTaintedEvent;
    }

    public static HashMap<Integer, List<Event>> getParametersMapDirectRefEvent(CFG cfg, SootMethod sootMethod){
        HashMap<Integer, List<Event>> paramMapTaintedEvent = new HashMap<>();
        for(Node node : cfg.allNodes.values()){
            Integer paramInd = tryGetParamIdentifiedInUnit(node.unit);
            if(paramInd != null) {
                List<Event> taintedEvent = DataFlow.getValueBoxRefEvents(node.unit.getDefBoxes().get(0), node);
                paramMapTaintedEvent.put(paramInd, taintedEvent);
            }

        }
        return paramMapTaintedEvent;
    }

    /**
     * 给定一个Unit：
     * 1、判断其是是IdentifyStmt
     * 2、判断其DefBox是否来源于方法形参或者this，如果是则返回对应的索引
     * @param unit
     * @return
     */
    public static Integer tryGetParamIdentifiedInUnit(Unit unit){
        /* return:
              -1 : this
         */
        if(unit instanceof IdentityStmt){
            if(unit.getUseBoxes().size() > 0){
                String s = unit.getUseBoxes().get(0).getValue().toString();
                String[] sp = s.split("[@:]");
                if(sp.length >= 3 && sp[1].contains("parameter")){
                    try{
                        return Integer.parseInt(sp[1].substring(sp[1].length() - 1));
                    } catch (Exception e){
                        log.warn("无法获取unit" + unit + "的this/形参对应关系，返回null");
                        return null;
                    }
                }
                else if(sp.length >= 3 && sp[1].contains("this")) return -1;
            }
        }
        return null;
    }

    /**
     * 给定Node，获取unit中指定argIndex的方法参数的ValueBox
     * @param node
     * @param argIndex
     * @return
     */
    public static ValueBox getArgValueBox(Node node, int argIndex){
        Stmt crtStmt = (Stmt) node.unit;
        if(!crtStmt.containsInvokeExpr()) { return null; }
        InvokeExpr crtIE = crtStmt.getInvokeExpr();
        if(crtIE.getArgCount() < argIndex + 1) { return null; }
        return crtIE.getArgBox(argIndex);
    }

    public static HashSet<ValueBox> getAllArgValueBoxes(Node node){
        HashSet<ValueBox> ret = new HashSet<>();
        if(!((Stmt) node.unit).containsInvokeExpr()) return ret;
        for(int ind = 0 ; ind < ((Stmt) node.unit).getInvokeExpr().getArgCount(); ind++){
            ValueBox vb = ((Stmt) node.unit).getInvokeExpr().getArgBox(ind);
            ret.add(vb);
        }
        return ret;
    }

    public static int getArgIndexByValueBox(Node node, ValueBox valueBox){
        if(!((Stmt) node.unit).containsInvokeExpr()) return -1;
        for(int ind = 0 ; ind < ((Stmt) node.unit).getInvokeExpr().getArgCount(); ind++){
            ValueBox vb = ((Stmt) node.unit).getInvokeExpr().getArgBox(ind);
            if(vb.equals(valueBox)) return ind;
        }
        return -1;
    }

    public static Node getParamTransferNode(CFG cfg, SootMethod sootMethod, int index){
        int paramCount = sootMethod.getParameterCount();
        Node node = cfg.headNode;
        for(int i = 0; i < paramCount + 1; i++){
//            log.info("---------------------------");
//            log.info(node.unit);
            Integer paramInd = tryGetParamIdentifiedInUnit(node.unit);
            if(paramInd == null) {
                if(node.successorNodes.size() == 0) break;
                node = node.successorNodes.iterator().next();
                continue;
            }
            if(paramInd == index) {
                return node;
            }

            if(node.successorNodes.size() == 0) break;
            node = node.successorNodes.iterator().next();
        }
        return null;
    }

    // eg. O.method->O
    public static ValueBox getThisValueBox(Node node){
        if (!((Stmt) node.unit).containsInvokeExpr())
            return null;

        InvokeExpr invokeExpr = ((Stmt) node.unit).getInvokeExpr();
        if(invokeExpr instanceof VirtualInvokeExpr || invokeExpr instanceof InterfaceInvokeExpr) {
            InstanceInvokeExpr instanceInvokeExpr = (InstanceInvokeExpr) invokeExpr;
            return instanceInvokeExpr.getBaseBox();
        }
        // hack
        ValueBox thisBox = null;
        HashSet<ValueBox> argBoxes = getAllArgValueBoxes(node);
        for (ValueBox valueBox:invokeExpr.getUseBoxes()){
            if(!argBoxes.contains(valueBox)) thisBox = valueBox;
        }
        return thisBox;
    }

    // eg. O.method->O
    public static ValueBox getThisValueBox(Stmt stmt){
        InvokeExpr invokeExpr = stmt.getInvokeExpr();
        if(invokeExpr instanceof InstanceInvokeExpr) {
            InstanceInvokeExpr instanceInvokeExpr = (InstanceInvokeExpr) invokeExpr;
            return instanceInvokeExpr.getBaseBox();
        }
        return null;
    }

    /**
     * 得到函数调用返回的对象值
     * eg. r1=r0.method -> r1
     * @param node
     * @return 如果提供的Unit是赋值语句那就返回函数调用返回值所赋予的那个Value，否则就返回null
     */
    public static ValueBox getReturnedValueBox(Node node){
        if (node.unit instanceof AssignStmt){
            return ((AssignStmt)node.unit).getLeftOpBox();
        }
        return null;
    }

    public static Value getReturnedValue(Node node){
        if (node.unit instanceof AssignStmt){
            return ((AssignStmt)node.unit).getLeftOp();
        }
        return null;
    }

    public static Value getReturnedValue(Stmt stmt){
        if (stmt instanceof AssignStmt){
            return ((AssignStmt)stmt).getLeftOp();
        }
        return null;
    }

    public static ValueBox getReturnedValueBox(Stmt stmt){
        if (stmt instanceof AssignStmt){
            return ((AssignStmt) stmt).getLeftOpBox();
        }

        return null;
    }

    // 找到某一个static field常量对应的实际值
    public static Value getStaticFieldValue(FieldRef fieldRef){
        SootClass sootClass = fieldRef.getFieldRef().declaringClass();

        if (sootClass.resolvingLevel() < 3) return null;
        SootMethod clint = sootClass.getMethodByNameUnsafe("<clinit>");
        if (clint != null){
            for (Unit unit: clint.retrieveActiveBody().getUnits()){

                if ((Stmt)unit instanceof AssignStmt){
                    AssignStmt assignStmt = (AssignStmt)unit;
                    Value left = assignStmt.getLeftOp();
                    Value right = assignStmt.getRightOp();

                    if (left instanceof FieldRef) { //  检测是否为field，是的话提取对应的值
                        if (((FieldRef) left).toString().equals(fieldRef.toString())) {
                            return right;
                        }
                    }
                }
            }
        }
        return null;
    }

    /**
     * 指定type，获取调用语句invokeExpr中的调用函数中对应的参数ValueBox
     * @param invokeExpr
     * @param type
     * @return 如果没有就返回null
     */
    public static ValueBox getArgByType(InvokeExpr invokeExpr, String type){
        ValueBox testArg = null;
        // 要创建的类的内容需要可控
        for (int ind = 0; ind < invokeExpr.getArgCount(); ind++){
            ValueBox arg = invokeExpr.getArgBox(ind);
            if (arg.getValue().getType().toString().equals(type))
                testArg = arg;
        }

        return testArg;
    }

    public static Integer getArgByType(SootMethod sootMethod, String type){
        Integer testArgIndex = null;
        // 要创建的类的内容需要可控
        for (int ind = 0; ind < sootMethod.getParameterCount(); ind++){
            Type argType = sootMethod.getParameterType(ind);
            if (argType.toString().equals(type))
                testArgIndex = ind;
        }

        return testArgIndex;
    }

    public static Integer getArgIndexByValue(InvokeExpr invokeExpr,
                                             TransformableNode tfNode,
                                             Value argValue){
        if (argValue == null)
            return null;
        ValueBox thisValueBox = Parameter.getThisValueBox(tfNode.node);
        if (thisValueBox != null && thisValueBox.getValue().equals(argValue))
            return -1;

        Value retValue = Parameter.getReturnedValue(tfNode.node);
        if (retValue != null && retValue.equals(argValue))
            return -2;

        for (int ind = 0; ind < invokeExpr.getArgCount(); ind++){
            ValueBox arg = invokeExpr.getArgBox(ind);
            if (arg.getValue().equals(argValue))
                return ind;
        }

        return null;
    }

    public static Integer getArgIndexByType(SootMethod sootMethod, String type){
        for (int ind = 0; ind < sootMethod.getParameterCount(); ind++){
            if (sootMethod.getParameterType(ind).toString().equals(type))
                return ind;
        }
        return null;
    }

    // 解析是第几个参数
    public static Integer getParamIndex(String sig){
        String[] sp = sig.split("[@:]");
        if (sp.length >= 3 && sp[1].contains("parameter")){
            try {
                return Integer.parseInt(sp[1].substring(sp[1].length()-1));
            } catch (NumberFormatException e) {
                throw new RuntimeException(e);
            }
        }else if (sp.length >= 3 && sp[1].contains("this")) return -1;

        return null;
    }
}
