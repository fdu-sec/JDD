package dataflow;

import cfg.Node;
import cfg.Path;
import soot.Unit;
import soot.Value;
import soot.ValueBox;
import soot.jimple.*;
import util.StringUtil;

import java.util.*;

/**
 * 提供数据流分析功能的工具类
 *
 * @since 2.0
 */
public class DataFlow {



    public static boolean isValueUsedInUnit(Unit unit, Value value) {
        List<String> usedValue = new ArrayList<>();
        for (ValueBox useBox : unit.getUseBoxes()) {
            usedValue.add(useBox.getValue().toString());
        }
        return usedValue.contains(value.toString());
    }

    public static boolean isValueDefinedInUnit(Unit unit, Value value) {
        List<String> definedValue = new ArrayList<>();
        for (ValueBox defBox : unit.getDefBoxes()) {
            definedValue.add(defBox.getValue().toString());
        }
        return definedValue.contains(value.toString());
    }

    public static ValueBox findValueBoxByValue(Unit unit, Value value) {
        for (ValueBox valueBox : unit.getUseAndDefBoxes())
            if (valueBox.getValue().toString().equals(value.toString()))
                return valueBox;
        return null;
    }


    public static void addNewEvent(EventQueue waitForProcessEvent, HashSet<Event> processedEvent, Node node, ValueBox valueBox) {
        Event newEvent = new Event(node, valueBox);
        if (processedEvent.contains(newEvent))
            return;
        waitForProcessEvent.add(newEvent);
    }

    public static void doWithInputAsLeftValueOrRef(Node node, ValueBox valueBox, EventQueue waitForProcessEvent, HashSet<Event> processedEvent, HashMap<Node, ValueBox> result) {
        //处理污染变量为：右值或者是调用语句引用对象的情况即a=b或者a=b.C()的情况
        if (isValueUsedInUnit(node.unit, valueBox.getValue()) && !isValueDefinedInUnit(node.unit, valueBox.getValue())) {
            result.put(node, findValueBoxByValue(node.unit, valueBox.getValue()));
            if (!((Stmt) node.unit).containsInvokeExpr() && node.unit.getDefBoxes().size() != 0) {//如果污染变量为左值不是调用语句
                addNewEvent(waitForProcessEvent, processedEvent, node, node.unit.getDefBoxes().get(0));
            }
            if(((Stmt) node.unit).containsInvokeExpr()&&!node.isExpand){//如果该处语句是调用语句，且没有被展开，我们这里假定只要左值中用到了污染变量，那么该处语句就是被污染的
                if(node.unit.getDefBoxes().size()!=0){
                    addNewEvent(waitForProcessEvent,processedEvent,node,node.unit.getDefBoxes().get(0));
                }
            }


        }
    }


    public static void doWithInputAsParam(Node node, Node beginNode,ValueBox valueBox, EventQueue waitForProcessEvent, HashSet<Event> processedEvent) {
        int index = ((Stmt) node.unit).getInvokeExpr().getArgs().indexOf(valueBox.getValue());//找到使用的变量的索引值
        if (index >= 0) {
            Node paramNode = dnfFind(beginNode, index);//找到感染的参数
            assert paramNode != null;
            addNewEvent(waitForProcessEvent, processedEvent, paramNode, paramNode.unit.getDefBoxes().get(0));
        }
    }

    public static void doWithInputAsRet(Node node, Node succor, ValueBox valueBox, EventQueue waitForProcessEvent, HashSet<Event> processedEvent, HashMap<Node, ValueBox> result) {
        if (((Stmt) node.unit) instanceof ReturnStmt || ((Stmt) node.unit) instanceof RetStmt) {//如果前面是返回值语句
            if (isValueUsedInUnit(node.unit, valueBox.getValue())) {//如果返回值被污染了
                for (Node su : succor.successorNodes) {
                    for (Node pre : su.originPreNode) {
                        if (pre.unit.getDefBoxes().size() != 0) {
                            result.put(pre, findValueBoxByValue(pre.unit, pre.unit.getDefBoxes().get(0).getValue()));
                            addNewEvent(waitForProcessEvent, processedEvent, pre, pre.unit.getDefBoxes().get(0));
                        }
                    }
                }
            }
        }
    }

    public static void doWithInputAsThis(Node node, EventQueue waitForProcessEvent, HashSet<Event> processedEvent, HashMap<Node, ValueBox> result) {
        for (Node succor : node.successorNodes) {
            for (Node pre : succor.originPreNode) {
                addNewEvent(waitForProcessEvent, processedEvent, succor, ((Stmt) pre.unit).getInvokeExpr().getUseBoxes().get(0));
                result.put(pre, ((Stmt) pre.unit).getInvokeExpr().getUseBoxes().get(0));//我们要把污染的对象记录下来
            }
        }
    }


    public static HashMap<Node, ValueBox> findAllUnitAndValueAffected(HashMap<Node, ValueBox> sourceMap) {
        //正向寻找数据传播,找到所有被影响的unit和value
        HashSet<Event> processedEvent = new HashSet<>();
        HashMap<Node, ValueBox> result = new HashMap<>();
        EventQueue waitForProcessEvent = new EventQueue();
        for (Node sourceNode : sourceMap.keySet()) {
            waitForProcessEvent.add(new Event(sourceNode, sourceMap.get(sourceNode)));
        }
        while (!waitForProcessEvent.isEmpty()) {
            Event event = waitForProcessEvent.poll();
            Node node = event.node;
            ValueBox valueBox = event.valueBox;
            if (valueBox == null)   continue;
            processedEvent.add(event);
            for (Node succor : node.successorNodes) {
                if (succor.tag == null) {
                    if (!isValueDefinedInUnit(succor.unit, valueBox.getValue()))
                        addNewEvent(waitForProcessEvent, processedEvent, succor, valueBox);
                    doWithInputAsLeftValueOrRef(succor, valueBox, waitForProcessEvent, processedEvent, result);

                } else if (succor.tag.equals("BEGIN")) {
                    for (Node succorNode : node.originSuccorNode) {
                        if (!isValueDefinedInUnit(succorNode.unit, valueBox.getValue())) {
                            addNewEvent(waitForProcessEvent, processedEvent, succorNode, valueBox);
                        }
                        doWithInputAsLeftValueOrRef(succorNode, valueBox, waitForProcessEvent, processedEvent, result);
                    }
                    if (isValueUsedInUnit(node.unit, valueBox.getValue())) {//如果在其中是错位参数的话
                        doWithInputAsParam(node, succor,valueBox, waitForProcessEvent, processedEvent);
                    }
                } else if (succor.tag.equals("END")) {//如果后继节点是
                    doWithInputAsRet(node, succor, valueBox, waitForProcessEvent, processedEvent, result);
                    if (valueBox.getValue().getUseBoxes().size() != 0 && valueBox.getValue().getUseBoxes().get(0).getValue().toString().contains("r0")) {
                        //如果我们对象的字段被污染了，我们就认为整个对象被污染了
                        doWithInputAsThis(succor, waitForProcessEvent, processedEvent, result);
                    }
                }
            }
        }
        return result;
    }



    public static Node dnfFind(Node beginNode, int index) {
        Queue<Node> queue = new LinkedList<>();
        queue.add(beginNode);
        while (!queue.isEmpty()) {
            Node front = queue.poll();
            if (front.unit != null && ((Stmt) front.unit).toString().contains("@parameter" + index))
                return front;
            for (Node succor : front.successorNodes) {
                if (succor.unit.toString().contains("@param") || succor.unit.toString().contains("@this"))
                    queue.add(succor);
            }
        }
        return null;
    }

    public static Node dnfBackFind(Node node) {
        Queue<Node> queue = new LinkedList<>();
        queue.add(node);
        while (!queue.isEmpty()) {
            Node front = queue.poll();
            if (front.tag!=null&&front.tag.equals("BEGIN"))
                return front;
            queue.addAll(front.precursorNodes);
        }
        return null;
    }

    /**
     * 找到所有影响某个变量的定义语句
     *
     * @param sourceNode  这个变量所在的语句（需要使用这个参数定位变量在cfg中的位置）
     * @param valueBox   变量
     * @return {@link HashSet}&lt;{@link Node}&gt;
     */
    public static LinkedHashSet<Node> findAllDefUnitAffectThisValue(Node sourceNode, ValueBox valueBox) {//反向搜索数据的传播
        HashSet<Event> processedEvent = new HashSet<>();
        EventQueue waitForProcessEvent = new EventQueue();
        waitForProcessEvent.add(new Event(sourceNode, valueBox));
        LinkedHashSet<Node> nodeAffect = new LinkedHashSet<>();
        while (!waitForProcessEvent.isEmpty()) {
            Event event = waitForProcessEvent.poll();
            Node node = event.node;
            ValueBox valuebox = event.valueBox;
            processedEvent.add(event);
            for (Node preNode : node.precursorNodes) {//我们要对所有前驱进行遍历
                if (preNode.tag == null) {//表示前面是一般的语句
                    if (preNode.unit.getDefBoxes().isEmpty() || !isValueDefinedInUnit(preNode.unit, valuebox.getValue())) {
                        //如果前面不是赋值语句或者不是对我们指定变量的赋值语句
                        addNewEvent(waitForProcessEvent, processedEvent, preNode, valuebox);
                    } else if (isValueDefinedInUnit(preNode.unit, valuebox.getValue())) {
                        //如果变量是在该语句中定义的，需要判断情况,共有六种情况
                        //先把我们找到的相关的赋值语句保存下来
                        nodeAffect.add(preNode);
//                        log.info(preNode.unit+": "+valuebox.getValue());
                        //1、是被new出来的
                        Stmt stmt = (Stmt) preNode.unit;
                        if (stmt instanceof AssignStmt && ((AssignStmt) stmt).getRightOp() instanceof NewExpr) {//如果是个赋值语句，并且是new出来的,在这条路径上终止

                            //do nothing
                        } else if (stmt.containsFieldRef()) {//如果含有字段引用
                            //2、如果是属于类的字段
                            if (stmt.getFieldRef().getField().isStatic()) {
//
                            } else {//3、如果是属于实例的,我们要获得该实例,我们不去追究该字段，因为字段他别复杂
                                AssignStmt assignStmt = (AssignStmt) stmt;
                                addNewEvent(waitForProcessEvent, processedEvent, preNode, assignStmt.getRightOp().getUseBoxes().get(0));
                            }
                        } else if (preNode.unit.toString().contains("@this")) {//4、属于该对象，我们应该继续观察该对象
                            Node beginNode = dnfBackFind(preNode);//查询它开始的节点
                            if(beginNode == null) // 到头了
                                continue;
                            for (Node invokeNode : beginNode.precursorNodes) {//我们获得调用语句，然后调查对象
                                ValueBox thisValueBox = ((Stmt) invokeNode.unit).getInvokeExpr().getUseBoxes().get(0);
                                addNewEvent(waitForProcessEvent, processedEvent, invokeNode, thisValueBox);
                            }

                        } else if (preNode.unit.toString().contains("@param")) {//5、属于参数，我们应该关注参数
                            int index = StringUtil.getParameterOrder(((Stmt) preNode.unit).toString());//得到参数序号
                            Node beginNode = dnfBackFind(preNode);
                            if(beginNode == null) // 到头了
                                continue;
                            for (Node invokeNode : beginNode.precursorNodes) {
                                ValueBox paramValueBox = ((Stmt) invokeNode.unit).getInvokeExpr().getUseBoxes().get(index);
                                addNewEvent(waitForProcessEvent, processedEvent, invokeNode, paramValueBox);
                            }
                        } else if (preNode.unit instanceof AssignStmt) { //TODO :报错soot.jimple.internal.JIdentityStmt cannot be cast to soot.jimple.AssignStmt，更新完善修正
                            if (((AssignStmt) preNode.unit).containsInvokeExpr()) {
                                //6、属于返回值，我们要查看返回值
                                if (node.tag != null && node.tag.equals("BEGIN")) {
                                    for (Node originSuccor : preNode.originSuccorNode) {//我们查询原来节点的直接后继
                                        for (Node endNode : originSuccor.precursorNodes) {//原来直接后继的前驱现在是END语句
                                            for (Node pre : endNode.precursorNodes) {
                                                if (pre.unit.toString().contains("null"))//如果返回值是null就不考虑了
                                                    continue;
                                                if ((Stmt) pre.unit instanceof ReturnStmt) {
                                                    ValueBox returnValueBox = ((ReturnStmt) pre.unit).getOpBox();
                                                    addNewEvent(waitForProcessEvent, processedEvent, preNode, returnValueBox);
                                                }
                                            }
                                        }
                                    }
                                }
                            }
                        } else if (stmt instanceof AssignStmt){//7、就是个普通的赋值语句
//                            assert stmt instanceof AssignStmt;
                            AssignStmt assignStmt = (AssignStmt) stmt;
                            addNewEvent(waitForProcessEvent, processedEvent, preNode, assignStmt.getRightOpBox());
                        }
                    }
                } else if (preNode.tag.equals("END")) {
                    //如果是END,说明前面是个调用语句的展开，我们直接去寻找它的原始前驱
                    for (Node originPre : node.originPreNode) {//找到原始前驱
                        if (originPre.unit.getDefBoxes().isEmpty() || !isValueDefinedInUnit(originPre.unit, valuebox.getValue())) {
                            //如果前面这个节点中没有为该变量赋值
                            addNewEvent(waitForProcessEvent, processedEvent, originPre, valuebox);
                        } else if (isValueDefinedInUnit(originPre.unit, valuebox.getValue())) {//如果重新定义了，需要查看返回的是什么？
                            for (Node beginNode : originPre.successorNodes) {//我们应该
                                addNewEvent(waitForProcessEvent, processedEvent, beginNode, originPre.unit.getDefBoxes().get(0));
                            }

                        }
                    }
                }
            }
        }
        return nodeAffect;
    }

    /**
     * 判断一个变量是否依赖另一个变量
     *
     * @param srcNode     污点变量所在的语句（需要使用这个参数定位变量在cfg中的位置）
     * @param srcValueBox 污点变量
     * @param tarNode     目标语句
     * @return boolean  能否被污染
     */
    public boolean isDependencyBetweenValue(Node srcNode, ValueBox srcValueBox, Node tarNode) {//判断数据间的独立性
        HashMap<Node, ValueBox> mp = new HashMap<>();
        mp.put(srcNode, srcValueBox);
        HashMap<Node, ValueBox> allUnitAndValueAffected = findAllUnitAndValueAffected(mp);
        return allUnitAndValueAffected.containsKey(tarNode);
    }

    /**
     * 找到以某个变量作为源头，能够影响的所有变量
     *
     * @param sourceMap 污染源头
     * @return {@link HashMap}&lt;{@link Node}, {@link ValueBox}&gt; 污染传播后的所有污染点
     */
    public static HashMap<Node, ValueBox> findAllUnitAndValueAffectedByPath(Path path, HashMap<Node, ValueBox> sourceMap) {
        //path，一条执行路径
        //sourceMap,路径上的被污染的节点和路径
        //确定给定的数据是如何沿着一条给定的路径传播的
        HashSet<Event> processedEvent = new HashSet<>();
        HashMap<Node, ValueBox> result = new HashMap<>();
        EventQueue waitForProcessEvent = new EventQueue();
        for (Node sourceNode : sourceMap.keySet()) {
            waitForProcessEvent.add(new Event(sourceNode, sourceMap.get(sourceNode)));
        }
        while (!waitForProcessEvent.isEmpty()) {
            Event event = waitForProcessEvent.poll();
            Node node = event.node;
            ValueBox valueBox = event.valueBox;
            processedEvent.add(event);
            //我们需要处理这个节点之后的数据
            for (Node succor : node.successorNodes) {
                if (path.nodes.contains(succor)) {//找出这个路径上的真正后继,后继只有一个
                    if (succor.tag == null) {
                        if (!isValueDefinedInUnit(succor.unit, valueBox.getValue()))
                            addNewEvent(waitForProcessEvent, processedEvent, succor, valueBox);
                        doWithInputAsLeftValueOrRef(succor, valueBox, waitForProcessEvent, processedEvent, result);//判断左值是否受到影响，如果只是普通的左值或者是调用语句中的对象，我们就认为左值会被污染
                    } else if (succor.tag.equals("BEGIN")) {
                        for (Node succorNode : node.originSuccorNode) {//找到原始前驱
                            if (path.nodes.contains(succorNode)) {//找到这个路径上的真正原始后继
                                if (!isValueDefinedInUnit(succorNode.unit, valueBox.getValue()))
                                    addNewEvent(waitForProcessEvent, processedEvent, succorNode, valueBox);
                                doWithInputAsLeftValueOrRef(succorNode, valueBox, waitForProcessEvent, processedEvent, result);
                            }
                        }
                        if (isValueUsedInUnit(node.unit, valueBox.getValue())) {//如果该污染变量在在本语句中被使用
                            doWithInputAsParam(node, succor,valueBox, waitForProcessEvent, processedEvent);
                        }
                    } else if (succor.tag.equals("END")) {
                        if (((Stmt) node.unit) instanceof ReturnStmt || ((Stmt) node.unit) instanceof RetStmt) {//如果前面是返回值语句
                            if (isValueUsedInUnit(node.unit, valueBox.getValue())) {//如果返回值被污染了,我们需要记录这个污染的返回值
                                Node originNode = path.nodes.get(path.nodes.indexOf(succor) + 1);
                                for (Node invokeNode : originNode.originSuccorNode) {
                                    if (path.nodes.contains(invokeNode) && invokeNode.unit.getDefBoxes().size() != 0) {
                                        addNewEvent(waitForProcessEvent, processedEvent, invokeNode,invokeNode.unit.getDefBoxes().get(0));
                                        result.put(invokeNode,invokeNode.unit.getDefBoxes().get(0));
                                    }
                                }
                            }
                            if (valueBox.getValue().getUseBoxes().size() != 0 && valueBox.getValue().getUseBoxes().get(0).getValue().toString().contains("r0")) {//如果语句中的对象的字段被污染了
                                Node originNode = path.nodes.get(path.nodes.indexOf(succor) + 1);
                                for (Node invokeNode : originNode.originSuccorNode) {
                                    if (path.nodes.contains(invokeNode)) {
                                        result.put(invokeNode,((Stmt) invokeNode.unit).getInvokeExpr().getUseBoxes().get(((Stmt) invokeNode.unit).getInvokeExpr().getUseBoxes().size() - 1));
                                        addNewEvent(waitForProcessEvent,processedEvent,originNode,((Stmt) invokeNode.unit).getInvokeExpr().getUseBoxes().get(((Stmt) invokeNode.unit).getInvokeExpr().getUseBoxes().size() - 1));
                                    }
                                }

                            }
                        }
                    }
                }

            }

        }
        return result;
    }

    // 直接引用某个valuebox的语句
    public static List<Node> getValueBoxRefNodes(ValueBox valueBox, Node src){
        List<Node> result = new LinkedList<>();

        Queue<Node> queue = new LinkedList<>();
        HashSet<Node> visitedNodes = new HashSet<>();
        visitedNodes.add(src);
        queue.add(src);

        while (!queue.isEmpty()){
            Node node = queue.poll();
//            log.info(node.unit);
            for(Node successor : node.successorNodes){
                if(!visitedNodes.contains(successor)) {
                    queue.add(successor);
                    visitedNodes.add(successor);
                }
            }

            for(ValueBox usedBox : node.unit.getUseBoxes()){
                if(usedBox.getValue().toString().equals(valueBox.getValue().toString())) {
                    result.add(node);
                    break;
                }
            }
        }
        return result;
    }

    // 直接引用某个valuebox的event
    public static List<Event> getValueBoxRefEvents(ValueBox valueBox, Node src){
        List<Event> result = new LinkedList<>();

        Queue<Node> queue = new LinkedList<>();
        HashSet<Node> visitedNodes = new HashSet<>();
        visitedNodes.add(src);
        queue.add(src);

        while (!queue.isEmpty()){
            Node node = queue.poll();
//            log.info(node.unit);
            for(Node successor : node.successorNodes){
                if(!visitedNodes.contains(successor)) {
                    queue.add(successor);
                    visitedNodes.add(successor);
                }
            }

            for(ValueBox usedBox : node.unit.getUseBoxes()){
                if(usedBox.getValue().toString().equals(valueBox.getValue().toString())) {
                    Event event = new Event(node, usedBox);
                    result.add(event);
                }
            }
        }
        return result;
    }

    // 某个变量的直接定义
    public static List<Node> getDefNodes(ValueBox valueBox, Node src){
        List<Node> result = new LinkedList<>();

        Queue<Node> queue = new LinkedList<>();
        HashSet<Node> visitedNodes = new HashSet<>();
        visitedNodes.add(src);
        queue.add(src);

        while (!queue.isEmpty()){
            Node node = queue.poll();
//            log.info(node.unit);
            for(Node precursor : node.precursorNodes){
                if(!visitedNodes.contains(precursor)) {
                    queue.add(precursor);
                    visitedNodes.add(precursor);
                }
            }

            for(ValueBox defBox : node.unit.getDefBoxes()){
                if(defBox.getValue().toString().equals(valueBox.getValue().toString())) {
                    result.add(node);
                }
            }
        }
        return result;
    }

}
