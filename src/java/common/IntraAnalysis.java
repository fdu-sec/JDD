package common;

import util.LogUtil;
import cfg.CFG;
import cfg.Node;
import soot.*;
import soot.jimple.*;
import soot.toolkits.graph.BriefUnitGraph;
import soot.toolkits.graph.UnitGraph;

import java.util.*;

import static util.StringUtil.parseClassNameFromUnit;


public class IntraAnalysis {
    private static final HashMap<SootField,String> fieldMapValue = new HashMap<>();

    /**
     * 批量分析应用时应该重置static类型变量
     */
    public static void reset(){
        fieldMapValue.clear();
    }


    public static boolean isValueDefinedInUnit(Unit unit, Value value) {
        return isValueDefinedInUnit(unit, value.toString());
    }

    public static boolean isValueDefinedInUnit(Unit unit, String valueString) {
        List<String> definedValue = new ArrayList<>();
        for (ValueBox defBox : unit.getDefBoxes())
            definedValue.add(defBox.getValue().toString());
        if (valueString.equals("r0")){
            if (((Stmt)unit).containsFieldRef()
                    && definedValue.contains(((Stmt) unit).getFieldRefBox().getValue().toString())
                    && ((Stmt) unit).getFieldRefBox().getValue().toString().startsWith("r0"))
                return true;
        }
        return definedValue.contains(valueString);
    }

    // 检查某个临时变量是否为类的Field
    public static boolean localIsField(CFG cfg, Unit sourceUnit, Value local){
        Node sourceNode = cfg.getNodeByUnit(sourceUnit);
        List<Node> processedNodes = new ArrayList<>();
        List<Node> waitForProcessNodes = new ArrayList<>(sourceNode.precursorNodes);
        while (!waitForProcessNodes.isEmpty()) {
            Node curNode = waitForProcessNodes.get(0);
            waitForProcessNodes.remove(curNode);
            if (processedNodes.contains(curNode))
                continue;
            processedNodes.add(curNode);
            Unit curUnit = curNode.unit;

            if (curUnit instanceof AssignStmt){
                if (((AssignStmt) curUnit).getLeftOp().toString().equals(local.toString())){
                    return ((AssignStmt) curUnit).getRightOp() instanceof FieldRef;
                }
            }
            waitForProcessNodes.addAll(curNode.precursorNodes);
        }
        return false;
    }


    public static HashSet<Unit> findDirectDefUnits(Body body, Unit sourceUnit, Value sourceValue) {
        UnitGraph unitGraph = new BriefUnitGraph(body);
        return findDirectDefUnits(unitGraph,sourceUnit,sourceValue);
    }

    public static HashSet<Unit> findDirectDefUnits(UnitGraph unitGraph, Unit sourceUnit, Value sourceValue){
        HashSet<Unit> result = new HashSet<>();
        Set<Unit> processedUnit = new HashSet<>();

        Queue<Unit> queue = new LinkedList<>();
        queue.add(sourceUnit);
        while (!queue.isEmpty()) {
            Unit unit = queue.poll();
            processedUnit.add(unit);
            // 自后向前找
            for (Unit pred : unitGraph.getPredsOf(unit)) {
                if (processedUnit.contains(pred))
                    continue;
                if (pred.getDefBoxes().isEmpty() || !isValueDefinedInUnit(pred, sourceValue)) {
                    queue.add(pred);
                } else {
                    result.add(pred);
                }
            }
        }
        return result;
    }


    public static String getValueOfField(SootField sootField){
        if (fieldMapValue.containsKey(sootField)){
            String res = fieldMapValue.get(sootField);
            if (res.equals("null"))
                return null;
            return res;
        }

        SootClass declaringClass = sootField.getDeclaringClass();
        SootMethod clInitMethod = declaringClass.getMethodByNameUnsafe("<clinit>");
        String res=null;
        if (clInitMethod !=null)
            res = getValueOfField(sootField,clInitMethod);
        if (res!=null){
            fieldMapValue.put(sootField,res);
            return res;
        }
        else {
            // 依赖于动态函数返回值，无法处理，E.g., DcTracker-mProvisionActionName
            if (sootField.getSignature().equals("<com.android.internal.telephony.dataconnection.DcTracker: java.lang.String mProvisionActionName>"))
                return "com.android.internal.telephony.PROVISION"+"0";
            for (SootMethod sootMethod:declaringClass.getMethods()){
                if (sootMethod.getName().equals("<init>")){
                    res = getValueOfField(sootField,sootMethod);
                    if (res!=null && !res.equals("null")){
                        fieldMapValue.put(sootField,res);
                        return res;
                    }
                }
            }
            LogUtil.debug("Get null value of field - "+sootField.getSignature());
            fieldMapValue.put(sootField,"null");
            return null;
        }
    }


    private static String getValueOfField(SootField sootField,SootMethod sootMethod){
        Value res = null;
        Unit tgtUnit = null;

        Body body;
        try{
            body = sootMethod.retrieveActiveBody();
        }catch (Exception e){
            e.printStackTrace();
            // System.out.println(("retrieveActiveBody出错，当前方法为" + sootMethod.getName()));
            return null;
        }


        for (Unit unit:body.getUnits()){
            if (unit instanceof AssignStmt && ((Stmt)unit).containsFieldRef()
                    && ((AssignStmt) unit).getFieldRef().getField().equals(sootField)){
                res = ((AssignStmt) unit).getRightOp();
                tgtUnit = unit;
                break;
            }
        }
        if (res != null){
            // 如果是常量，则直接返回，若为变量，则进一步分析
            if (res instanceof Constant)
                return res.toString();
            else{
                for(Unit defUnit: findDirectDefUnits(body,tgtUnit,res)){
                    String vs = getConstantOfDefValue(body,defUnit);
                    if (vs!=null)
                        return vs;
                }
            }
        }
        return null;
    }

    // 为def value寻找可能的常量值
    public static String getConstantOfDefValue(Body body, Unit defUnit){
        if (defUnit instanceof AssignStmt) {
            if (((Stmt)defUnit).containsInvokeExpr()){
                String invokeMethodSig = ((Stmt) defUnit).getInvokeExpr().getMethodRef().getSignature();
                InvokeExpr invokeExpr = ((Stmt) defUnit).getInvokeExpr();
                // 获取 invoke object 的定义信息
                Value invokeObjectValue = invokeExpr.getUseBoxes().get(invokeExpr.getUseBoxes().size()-1).getValue();
                Unit invokeObjectDefUnit = findDirectDefUnits(body,defUnit,invokeObjectValue).iterator().next();
                Value right = ((AssignStmt) invokeObjectDefUnit).getRightOp();
                switch (invokeMethodSig){
                    case "<java.lang.Class: java.lang.String getName()>":
                        if (right instanceof Constant)
                            return parseClassNameFromUnit(right.toString());
                        LogUtil.debug("NUll for class name (1) - "+invokeObjectDefUnit.toString()+" - "+body.getMethod().getSignature());
                        return null;
                    case "<java.lang.Class: java.lang.String getSimpleName()>":
                        if (right instanceof Constant){
                            String className = parseClassNameFromUnit(right.toString());
                            if (className!=null)
                                return className.substring(className.lastIndexOf(".")+1);
                        }
                        LogUtil.debug("NUll for class name (2) - "+invokeObjectDefUnit.toString()+" - "+body.getMethod().getSignature());
                        return null;
                    case "<java.lang.Class: java.lang.Package getPackage()>":
                        if (right instanceof Constant){
                            String className = parseClassNameFromUnit(right.toString());
                            // 直接默认返回package name
                            if (className!=null)
                                return className.substring(0,className.lastIndexOf("."));
                        }else if (right instanceof InvokeExpr){
                            String classGetMethodSig = ((InvokeExpr) right).getMethodRef().getSignature();
                            Value invokeValue = right.getUseBoxes().get(right.getUseBoxes().size()-1).getValue();
                            if (classGetMethodSig.equals("<java.lang.Object: java.lang.Class getClass()>")){
                                if (invokeValue.toString().equals("r0")){
                                    String className = body.getMethod().getDeclaringClass().getName();
                                    return className.substring(0,className.lastIndexOf("."));
                                }
                            }
                        }
                        LogUtil.debug("NUll for class name (3) - "+invokeObjectDefUnit.toString()+" - "+body.getMethod().getSignature());
                        return null;
                    case "<java.lang.Package: java.lang.String getName()>":
                        // 默认该函数调用依赖于 getPackage()
                        return getConstantOfDefValue(body,invokeObjectDefUnit);
                    case "<java.lang.StringBuilder: java.lang.String toString()>":
                        // 这里仅处理顺序的append字符串
                        BriefUnitGraph unitGraph = new BriefUnitGraph(body);
                        Unit curUnit = invokeObjectDefUnit;
                        StringBuilder sb = new StringBuilder();
                        sb.append("\"");
                        while (unitGraph.getSuccsOf(curUnit).size()==1){
                            Unit next = unitGraph.getSuccsOf(curUnit).get(0);
                            if (((Stmt)next).containsInvokeExpr()
                                    && ((Stmt) next).getInvokeExpr().getMethodRef().getSignature().equals("<java.lang.StringBuilder: java.lang.StringBuilder append(java.lang.String)>")
                                    && ((Stmt) next).getInvokeExpr().getUseBoxes().get(((Stmt) next).getInvokeExpr().getUseBoxes().size()-1).getValue().equals(invokeObjectValue)){
                                Value appendValue = ((Stmt) next).getInvokeExpr().getArg(0);
                                if (appendValue instanceof StringConstant){
                                    sb.append(appendValue.toString().replaceAll("\"",""));
                                }else {
                                    Unit ddUnit = findDirectDefUnits(body,next,appendValue).iterator().next();
                                    if (ddUnit instanceof AssignStmt){
                                        String subStr = null;
                                        if (((AssignStmt) ddUnit).containsFieldRef()){
                                            subStr = getValueOfField(((AssignStmt) ddUnit).getFieldRef().getField());
                                        }else if (((AssignStmt) ddUnit).containsInvokeExpr()){
                                            subStr = getConstantOfDefValue(body,ddUnit);
                                        }

                                        if (subStr==null)
                                            sb.append("-null-");
                                        else
                                            sb.append(subStr.replaceAll("\"",""));
                                    }else {
                                        LogUtil.debug("getConstantOfDefValue() - StringBuilder append a non-field and non-constant - "+body.getMethod().getSignature()+" - "+ddUnit.toString());
                                    }
                                }
                            }
                            curUnit=next;
                        }
                        sb.append("\"");
                        return sb.toString();
                    default:
                        LogUtil.debug("getConstantOfDefValue() - Unhandled invokeExpr in <clinit> of "+body.getMethod().getSignature()+" - "+invokeMethodSig);
                }
            }else {
                LogUtil.debug("getConstantOfDefValue() - Not invoke defUnit to define field value - "+defUnit.toString()+" in "+body.getMethod().getSignature());
            }
        }else {
            LogUtil.debug("getConstantOfDefValue() - Not AssignStmt DefUnit - "+defUnit.toString()+" in "+body.getMethod().getSignature());
        }
        return null;
    }


    // 分析函数返回值是否为直接返回一个Field
    public static SootField fetchRetField(SootMethod sootMethod){
        Body body;
        try{
            body = sootMethod.retrieveActiveBody();
        }catch (Exception e){
            //System.out.println(("retrieveActiveBody出错，当前方法为：" + sootMethod.getName()));
            return null;
        }
        BriefUnitGraph briefUnitGraph = new BriefUnitGraph(body);
        for (Unit tailUnit: briefUnitGraph.getTails()){
            if (tailUnit instanceof ReturnStmt){
                Value retValue = ((ReturnStmt) tailUnit).getOp();
                for (Unit defUnit:findDirectDefUnits(briefUnitGraph,tailUnit,retValue)){
                    if (((Stmt)defUnit).containsFieldRef()){
                        return ((Stmt) defUnit).getFieldRef().getField();
                    }
                }
            }
        }
        return null;
    }

    // 分析函数返回值是否为一个常数
    public static HashSet<String> fetchRetConstants(SootMethod sootMethod){
        HashSet<String> constants = new HashSet<>();
        Body body;
        try{
            body = sootMethod.retrieveActiveBody();
        }catch (Exception e){
            return constants;
        }
        BriefUnitGraph briefUnitGraph = new BriefUnitGraph(body);
        for (Unit tailUnit: briefUnitGraph.getTails()){
            if (tailUnit instanceof ReturnStmt){
                Value retValue = ((ReturnStmt) tailUnit).getOp();
                if (retValue instanceof Constant)
                    constants.add(retValue.toString());
            }
        }
        return constants;
    }


    // 获取函数返回值为什么类型
    public static String fetchRetInstanceType(SootMethod sootMethod){
        Body body;
        try{
            body = sootMethod.retrieveActiveBody();
        }catch (Exception e){
            //System.out.println(("retrieveActiveBody出错，当前方法为：" + sootMethod.getName()));
            return null;
        }
        BriefUnitGraph briefUnitGraph = new BriefUnitGraph(body);
        for (Unit tailUnit: briefUnitGraph.getTails()){
            if (tailUnit instanceof ReturnStmt){
                Value retValue = ((ReturnStmt) tailUnit).getOp();
                if (retValue.toString().equals("null"))
                    continue;
                for (Unit defUnit:findDirectDefUnits(briefUnitGraph,tailUnit,retValue)){
                    if (defUnit instanceof AssignStmt){
                        if (((AssignStmt) defUnit).containsFieldRef()){
                            return ((AssignStmt) defUnit).getFieldRef().getField().getType().toString();
                        }else if (((AssignStmt) defUnit).containsInvokeExpr()){
                            return fetchRetInstanceType(((AssignStmt) defUnit).getInvokeExpr().getMethod());
                        }else if (((AssignStmt) defUnit).getRightOp() instanceof NewExpr){
                            return ((NewExpr) ((AssignStmt) defUnit).getRightOp()).getBaseType().toString();
                        }
                    }
                }
            }
        }
        return null;
    }

}



