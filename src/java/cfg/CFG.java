package cfg;

import cg.CG;
import heros.flowfunc.Identity;
import lombok.extern.slf4j.Slf4j;
import soot.*;
import soot.jimple.*;
import soot.jimple.toolkits.callgraph.Edge;
import soot.jimple.toolkits.ide.DefaultJimpleIFDSTabulationProblem;
import soot.toolkits.graph.BriefUnitGraph;
import soot.toolkits.graph.UnitGraph;
import util.Util;

import java.util.*;
import java.util.function.Function;

/**
 * 控制流图（Control Flow Graph）
 *
 * @since 2.0
 */
@Slf4j
public class CFG {

    public Node headNode = null;

    public LinkedHashMap<Unit, Node> allNodes = new LinkedHashMap<>();

    public int maxDepth = 5;

    public HashSet<String> selfDefinedToExpandMethodSet = null;//用户自定定义的应该展开的方法

    public boolean isUseStandardLib = false;

    public SootMethod entryPoint;

    public static int pathCount=0;

    public CG cg=null;

    /**
     * 初始化CFG，详尽的构造器。
     * 不会构建CFG图，构建应使用buildCFG()
     *
     * <br><b>示例</b><br>
     * CFG cfg = new CFG(entryPoint, maxDepth, selfDefinedToExpandMethodSet, isUseStandardLib);<br>
     * cfg.buildCFG();<br>
     *
     * @param entryPoint                   入口方法
     * @param maxDepth                     展开函数的最大深度
     * @param selfDefinedToExpandMethodSet 自定义展开条件
     * @param isUseStandardLib             是否展开标准库
     */
    public CFG(SootMethod entryPoint, int maxDepth, HashSet<String> selfDefinedToExpandMethodSet, boolean isUseStandardLib) {
        this.entryPoint = entryPoint;
        this.maxDepth = maxDepth;
        this.selfDefinedToExpandMethodSet = selfDefinedToExpandMethodSet;
        this.isUseStandardLib = isUseStandardLib;
        if(cg==null){
            log.info("Warning: "+"You haven't set cg for the ICFG, it won't be precise");
        }
    }

    /**
     * 初始化CFG。
     * 不会构建CFG图，构建应使用buildCFG()
     *
     * <br><b>示例</b><br>
     * CFG cfg = new CFG(entryPoint, maxDepth);<br>
     * cfg.buildCFG();<br>
     *
     * @param entryPoint                   入口方法
     * @param maxDepth                     展开函数的最大深度
     */
    public CFG(SootMethod entryPoint, int maxDepth) {
        this.entryPoint = entryPoint;
        this.maxDepth = maxDepth;
    }

    /**
     * 初始化CFG，精简的构造器。
     * 不会构建CFG图，构建应使用buildCFG()<br>
     *
     * <br><b>示例</b><br>
     * CFG cfg = new CFG(entryPoint);<br>
     * cfg.buildCFG();<br>
     *
     * @param entryPoint                   入口方法
     */
    public CFG(SootMethod entryPoint){
        this.entryPoint = entryPoint;
    }

    /**
     * 过程内的，sft use
     *
     * @param sootMethod
     * @param innerProcess
     */
    public CFG(SootMethod sootMethod, boolean innerProcess){
        this.entryPoint = sootMethod;
        if(innerProcess){
            this.selfDefinedToExpandMethodSet = new HashSet<>();
        }
    }

    /**
     * 构建cfg
     *
     * @return {@link Node} 头节点
     */
    public Node buildCFG(){
        buildGraph(entryPoint,new HashSet<>(),0);
        return headNode;
    }

    public void setCG(CG cg){
//        为本ICFG指定cg
        this.cg=cg;
    }

    public HeadAndTail buildGraph(SootMethod sootMethod, Set<String> visit, int depth) {
        if (depth > maxDepth)
            return null;
        Body body;
        try {
            body = sootMethod.retrieveActiveBody();
        }catch (Exception e){
            // ToDo: 匿名内部类的run方法会存在大量无法retrieveActiveBody的情况
            if(!sootMethod.getName().equals("run")) {
            }

            return null;
        }

        if (body != null) {
            UnitGraph unitGraph = new BriefUnitGraph(body);
            for (Unit unit : unitGraph.getBody().getUnits()) {
                allNodes.put(unit, new Node(unit,sootMethod));
                if(headNode == null) headNode = allNodes.get(unit);
            }
            for (Unit unit : unitGraph.getBody().getUnits()) {
                Node node = getNodeByUnit(unit);
                for (Unit preUnit : unitGraph.getPredsOf(unit)) {
                    Node preNode = getNodeByUnit(preUnit);
                    if (!preNode.successorNodes.contains(node)) {

                        // 过程内cfg
                        if (selfDefinedToExpandMethodSet!=null && selfDefinedToExpandMethodSet.isEmpty()){
                            preNode.successorNodes.add(node);
                            node.precursorNodes.add(preNode);
                            continue;
                        }

                        Stmt stmt = (Stmt) preNode.unit;
                        if (stmt.containsInvokeExpr() && (!(stmt instanceof IfStmt)) && (!(stmt instanceof GotoStmt))) {
                            SootMethod method=null;
                            if(cg==null) {
//                                如果没有提前为ICFG构建cg,则on-the-fly构建ICFG,结果是不精确的
                                 method = stmt.getInvokeExpr().getMethod();
                            }else {
//                                soot中使用构建图的方法由于精确读度的问题，也可能会出现误报，这样的情况是我们为预料到的，因此
//                                后面的数据流分析中没有考虑这种情况,为了减少大量的修改，我们默认只取一个方法，但是精确度仍然要
//                                比之前的方法要高很多
                                Iterator<Edge> edgeIterator = Scene.v().getCallGraph().edgesOutOf(preNode.unit);
                                if (edgeIterator.hasNext()){
                                    method=edgeIterator.next().tgt();
                                }
                            }
                            if(method == null) {
                                preNode.successorNodes.add(node);
                                node.precursorNodes.add(preNode);
                                continue;
                            }
                            if (selfDefinedToExpandMethodSet!=null&&!selfDefinedToExpandMethodSet.contains(method.getSignature())) {
                                //如果用户自定义的需要展开的方法集合中不包含该方法
                                preNode.successorNodes.add(node);
                                node.precursorNodes.add(preNode);
                                continue;
                            }
                            if (visit.contains(method.getSignature())) {//如果该方法中含有路径上存在的方法，就说明有环
                                preNode.successorNodes.add(node);
                                node.precursorNodes.add(preNode);
                                continue;
                            }
                            if (!method.isConcrete()) {//如果方法不是具体的
                                preNode.successorNodes.add(node);
                                node.precursorNodes.add(preNode);
                                continue;
                            }
                            if (Util.isStandardLibrary(method.getDeclaringClass().getName())&&isUseStandardLib) {//用于表示安卓的标准库是否要展开
                                preNode.successorNodes.add(node);
                                node.precursorNodes.add(preNode);
                                continue;
                            }
                            Set<String> addVisit = new HashSet<>();
                            addVisit.addAll(visit);
                            addVisit.add(method.getSignature());
                            HeadAndTail headAndTail = buildGraph(method, addVisit, depth + 1);
                            if (headAndTail == null) {
                                preNode.successorNodes.add(node);
                                node.precursorNodes.add(preNode);
                                continue;
                            }

                            preNode.originSuccorNode.add(node);
                            node.originPreNode.add(preNode);

                            Node beginNode = new Node("BEGIN");
                            preNode.successorNodes.add(beginNode);
                            preNode.isExpand=true;//标记该处的方法被展开了
                            beginNode.precursorNodes.add(preNode);
                            for (Node head : headAndTail.headNodes) {
                                beginNode.successorNodes.add(head);
                                head.precursorNodes.add(beginNode);
                            }

                            Node endNode = new Node("END");
                            for (Node tail : headAndTail.tailNodes) {
                                tail.successorNodes.add(endNode);
                                endNode.precursorNodes.add(tail);
                            }

                            endNode.successorNodes.add(node);
                            node.precursorNodes.add(endNode);

                        } else {//如果前驱不是调用方法，它的后继节点就是该节点
                            preNode.successorNodes.add(node);
                            node.precursorNodes.add(preNode);
                        }
                    }
                }
            }
            HeadAndTail headAndTail = new HeadAndTail();//返回展开语句的头和尾
            for (Unit unit : unitGraph.getHeads()) {
                headAndTail.headNodes.add(getNodeByUnit(unit));
//                headNode = getNodeByUnit(unit);//得到整个图的头节点
            }
            for (Unit unit : unitGraph.getTails())
                headAndTail.tailNodes.add(getNodeByUnit(unit));
            return headAndTail;

        } else {
            return null;
        }
    }

    public Node getNodeByUnit(Unit unit) {
        return allNodes.get(unit);
    }

    /**
     * 重置这个cfg图
     */
    public void reset() {
        headNode = null;
        allNodes.clear();
    }

    static class HeadAndTail {
        public HashSet<Node> headNodes = new HashSet<>();
        public HashSet<Node> tailNodes = new HashSet<>();
    }

    /**
     * 找到语句之间的所有路径，为了防止内存溢出，后三个参数用来限制深度优先搜索，我们提供推荐值。
     *
     * @param srcNode       源语句节点
     * @param trgNode       目的语句节点
     * @param maxPathLength 搜索时的最大路径长度，超过此长度的路径不再继续搜索。
     * @param maxPathNum    总的存储的路径上限
     * @param maxTarPathNum 递归查找中递归的路径的上限
     * @return {@link List}&lt;{@link Path}&gt;
     */
    public static List<Path> findAllPathsBetweenUnits(Node srcNode,Node trgNode,int maxPathLength,int maxPathNum,int maxTarPathNum){
        //返回两条语句间的所有路径,CFG是一个DAG
        //我们设置路径的最大长度,当搜索的路径长度大于这个值时，还没有达到目标节点，这条路径就被放弃不再向下寻找
        //我们设置两点间的所有路径数目满足要求和达到最大长度的所有路径数目的最大上限，当我们检索到这么多路径后，我们就不再寻找
        HashMap<Node,List<Path>> node2Path=new HashMap<>();//用于保存节点到目标节点的所有路径
        HashMap<Node,Set<Node>> visitNode=new HashMap<>();
        pathCount=0;//初始化全局变量
        List<Path> result = dnfSearchPath(srcNode, trgNode, maxPathLength, maxPathNum, 0, new HashSet<Node>(), node2Path,visitNode,new HashSet<Node>(), maxTarPathNum);
        return result;
    }

    public static List<Path> dnfSearchPath(Node node,Node trgNode,int maxPathLength,int maxPathNum,int depth,HashSet<Node> visit,HashMap<Node,List<Path>> node2Path,HashMap<Node,Set<Node>> visitNode,HashSet<Node> mark,int maxTarPathNum){
        //深度搜索所有满足条件的路径,我们要保证所有节点只访问一次
        if(pathCount>maxPathNum)//如果检索到的路径超过我们设置的最大上限，我们也放弃继续寻找
            return null;
        if(visit.contains(node)){//防止有环
            pathCount++;
            return null;
        }
        if(depth>=maxPathLength) {//如果该条路径的深度已经达到了我们设置的最大上限还没有找到目标节点，我们就放弃
            pathCount++;
            return null;
        }
        if(node==trgNode){//如果找到了目标节点，就返回
            pathCount++;
            Path path =new Path();
            path.nodes.add(node);
            // log.info("找到目标节点"+node.unit);
            List<Path> result=new ArrayList<>();
            result.add(path);
            node2Path.put(node,result);
            return result;
        }else {//如果没有找到，就需要继续向下查找
            if(node.successorNodes.isEmpty()){//如果该节点没有后继
                pathCount++;
                return null;
            }else {
                HashSet<Node> addVisit = new HashSet<>(visit);
                addVisit.add(node);
                List<Path> result=new ArrayList<>();
                for (Node succor : node.successorNodes) {//从孩子节点找到所有到目标节点的路径
                    int beginSize=result.size();
                    if(mark.contains(succor)&&node2Path.containsKey(succor)) {//如果该节点曾经访问过并且它含有到达目标节点的路径，我们就直接使用它之前保存记录的信息
                        addNode2Path(result,node2Path.get(succor),node);//将现在的节点和他之前的路径结合
                    }else if(!mark.contains(node)){//如果没有访问过该节点，我们就查询他到目标节点的路径
                        List<Path> paths = dnfSearchPath(succor, trgNode, maxPathLength, maxPathNum, depth + 1, addVisit, node2Path,visitNode,mark,maxTarPathNum);
                        if(paths!=null){//如果该子节点到目标节点之间存在路径，就把路径与该机欸但几个并记录下来
                            addNode2Path(result,paths,node);
                        }
                    }
                    int endSize=result.size();
                    if(beginSize!=endSize&&endSize!=0) {//如果从该子节点到目的节点中存在路径
                        //进行内存的一些处理工作
                        Set<Node> father = new HashSet<>();
                        father.add(node);
                        if (!visitNode.containsKey(succor)) {//visitNode用于记录节点的父节点中访问的数目
                            visitNode.put(succor, father);
                        } else {
                            visitNode.get(succor).add(node);
                        }
                        if (visitNode.get(succor).size() == succor.precursorNodes.size()) {//如果所有的父节点都访问过该节点，说明所有父节点都记录了到目标节点的路径，我们就应该删除这些节点保存的路径
                            if (node2Path.get(succor) != null) {
                                node2Path.remove(succor);
                            }
                        }
                    }
                }
                mark.add(node);//标记该节点的路径信息已经查明
                if(result.size()!=0) {//如果该节点到目标节点中有路径，就将得到的路径保存下来
                    // log.info("路径数目为："+result.size());
                    if(result.size()>maxTarPathNum){//如果该节点到目标节点的路径数目大于我们最大的数目，我们就在这些路径中随机选择最大数目的一半
                        List<Path> reducePath=new ArrayList<>();
                        for(int index=0;index<maxTarPathNum/2;index++){
                            reducePath.add(result.get(index));
                        }
                        node2Path.put(node,reducePath);
                        return reducePath;
                    }
                    node2Path.put(node,result);
                    return result;
                }
                // log.info("本节点到目标节点的路径为空");
                return null;
            }
        }
    }

    public static List<Path> addNode2Path(List<Path> result,List<Path> pathList,Node node){//向每条路径的末尾添加指定的节点
        for(Path path:pathList){
            Path newPath=new Path();
            newPath.nodes.add(node);
            newPath.nodes.addAll(path.nodes);
            result.add(newPath);
        }
        return result;
    }

    /**
     * 寻找CFG中所有满足特定要求的语句<br>
     * 可以通过重载filter中的apply函数实现自定义的过滤器
     * <br><b>示例</b>
     * <pre>
     * {@code
     * //下面的例子将使用一个永远接收的过滤器，得到CFG中的所有语句。
     * HashSet<Unit> registerReceiverUnits = cfg.findUnitWithFilter(new Function<Unit, Boolean>(){
     *       @Override
     *       public Boolean apply(Unit unit) {
     *          return true;
     *       }
     * });
     * }
     * </pre>
     *
     * @param filter 过滤器函数
     * @return {@link HashSet}&lt;{@link Unit}&gt;
     */
    public HashSet<Unit> findUnitWithFilter(Function<Unit, Boolean> filter) {
        HashSet<Unit> ret = new HashSet<>();
        for(Unit unit : allNodes.keySet()){
            if(filter.apply(unit))
                ret.add(unit);
        }
        return ret;
    }

    /**
     * 寻找CFG中所有满足特定要求的语句,返回它们所在的node<br>
     * 可以通过重载filter中的apply函数实现自定义的过滤器
     *
     * @param filter 过滤器函数
     * @return {@link HashSet}&lt;{@link Node}&gt;
     */
    public HashSet<Node> findNodeWithFilter(Function<Node, Boolean> filter) {
        HashSet<Node> ret = new HashSet<>();
        for(Node node : allNodes.values()){
            if(filter.apply(node))
                ret.add(node);
        }
        return ret;
    }


    /**
     * 输出一个节点附近的节点，reverse为false时，打印该语句后继的count条语句；reverse为true时打印该语句前驱的count条语句。
     * 输出结果从起始语句到结束语句缩进的空格数递减。
     *
     * @param node    节点
     * @param count   打印的范围
     * @param reverse 选择前驱或后继
     */
    public void printNearbyNodes(Node node, int count, boolean reverse){
        if(count == 0)return;
        String out = String.format("%" + (count + node.toString().length()) + "s\n", node.toString());
        System.out.print(out);
        if(!reverse){
            for(Node node1 : node.successorNodes){
                printNearbyNodes(node1, count - 1, false);
            }
        }
        else{
            for(Node node1 : node.precursorNodes){
                printNearbyNodes(node1, count - 1, true);
            }
        }
    }

    public void printStackTrace(Node node){
        int lev = 0;
        int count = 0;
        Stack<String> stack = new Stack<>();
        while (node.precursorNodes.size() > 0){
            Node preNode = node.precursorNodes.iterator().next();
            if(node.tag != null && node.tag.equals("BEGIN")){
                String unitStr = preNode.unit.toString();
                stack.push(String.format("%" + (lev + unitStr.length()) + "s\n", unitStr));
                if(lev > 0) lev -= 3;
            }
            else if(node.tag != null && node.tag.equals("END")){
                lev += 3;
            }
            node = preNode;
            if(count++ > 200){
                log.info("Out of limit, terminated");
                break;
            }
        }
        while(!stack.empty()){
            log.info(stack.pop());
        }
    }

    /**
     * 获取方法中可以被用户获取的输入，作为正向污点分析的起点
     * （1.参数 2.getIntent()）
     * 需解决的特殊情况：getIntent()函数并不一定在函数开始时初始化，而是在某些callee中初始化;
     * @return
     */
    public HashMap<Node, ValueBox> fetchControlledInputData(){
        HashMap<Node, ValueBox> result = new HashMap<>();
        try {
            Body body = entryPoint.retrieveActiveBody();
            for (Unit unit:body.getUnits()){
                if (unit instanceof IdentityStmt){
                    Value param = ((IdentityStmt) unit).getRightOp();
                    if (param.getType().toString().equals("android.content.Context")) {}
                    else {
                        result.put(getNodeByUnit(unit),((IdentityStmt) unit).getLeftOpBox());
                    }
                }else if (((Stmt)unit).containsInvokeExpr() && unit instanceof AssignStmt){
                    SootMethod invokeMethod = ((Stmt) unit).getInvokeExpr().getMethod();
                    if (invokeMethod.getSubSignature().equals("android.content.Intent getIntent()"))
                        result.put(getNodeByUnit(unit),((AssignStmt) unit).getLeftOpBox());
                }
            }
        }catch (Exception e){
            return result;
        }
        return result;
    }
}
