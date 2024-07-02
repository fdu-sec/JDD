package tranModel;

import PointToAnalyze.pointer.Pointer;
import cfg.CFG;
import cfg.Node;
import container.BasicDataContainer;
import dataflow.node.MethodDescriptor;
import dataflow.node.SourceNode;
import soot.*;
import soot.jimple.IfStmt;
import soot.jimple.InvokeExpr;
import soot.jimple.Stmt;
import soot.jimple.toolkits.callgraph.Edge;
import tranModel.Taint.Taint;
import util.StaticAnalyzeUtils.Parameter;
import util.Utils;

import javax.xml.transform.Source;
import java.util.*;

/**
 * 用于封装cfg.Node
 */
public class TransformableNode extends Transformable{
    public Node node;
    public SootMethod method;
    public HashSet<TransformableNode> successors = new HashSet<>();
    public HashSet<TransformableNode> precursors = new HashSet<>();

    public Context context = new Context();

    public SootMethod addMethod = null;

    public boolean isCycle = false; // 记录是否为循环语句，如果是例如For的循环语句可能会发生条件分支记录的错误问题，是否为循环语句在构建拓扑排序的时候记录

    public int[] ruleFlag = new int[10];
    // 用于标识当前Unit是否是Sink，如果是Sink那就放弃后续的Unit
    // ToDo: 可能会导致后续的sink被漏掉
    public boolean exec = true;
    // 用于路径敏感分析
    public HashSet<Integer> path_record = new HashSet<>();

    public boolean needInputTaintedParamFlush = true;

    public static HashMap<Integer, TransformableNode> ifStmtHashMap = new HashMap<>();


    public TransformableNode(Node node, SootMethod sootMethod){
        this.node = node;
        this.method = sootMethod;
        this.context.method = sootMethod;
        this.context.sootClass = sootMethod.getDeclaringClass();
    }

    public TransformableNode(Node node){
        this.node = node;
    }

    public TransformableNode(){
    }



    public boolean containsInvoke(){
        return ((Stmt) node.unit).containsInvokeExpr();
    }

    public IfStmt getIfStmt(){
        IfStmt ifStmt = null;

        if (((Stmt)this.node.unit) instanceof IfStmt) {
            ifStmt = (IfStmt) this.node.unit;
        }
        return ifStmt;
    }

    /**
     * 用于判断当前这条Jimple方法调用语句存在的对外函数（即多态的情况）有哪些，并：
     * 1、将污点传播到方法调用中去
     * 2、处理soot.jimple.toolkits.callgraph.Edge#tgt()在匿名内部类中的方法链接异常
     * @return
     */
    public HashSet<SootMethod> invokeMethods(MethodDescriptor descriptor){

        HashSet<SootMethod> ret = new HashSet<>();
        if(!containsInvoke()) return ret;
        // 获得出边，没有出边直接返回
        Iterator<Edge> edgeIterator = BasicDataContainer.cg.callGraph.edgesOutOf(node.unit);
        if (edgeIterator == null)
            return ret;

        int index = 0;
        // 对这些引出的方法做处理，使用connectParameters将污点信息进行传递
        while (edgeIterator.hasNext()) {
            index++;
            SootMethod invokeMethod = edgeIterator.next().tgt();
            if (index>1) { connectParameters(invokeMethod, descriptor); }
            ret.add(invokeMethod);
        }
        if (ret.size() == 0 && needConnectParams()) {
            ret = findExactMethod(descriptor);
        }
        return ret;
    }

    @Override
    public String toString(){
        return this.node.unit.toString();
    }

    /**
     * 返回Jimple对应unit的InvokeExpr
     * @return
     */
    public InvokeExpr getUnitInvokeExpr(){
        if (this.containsInvoke()){
            return ((Stmt)node.unit).getInvokeExpr();
        }
        return null;
    }

    @Override
    public int hashCode() {
        return this.node.toString().hashCode();
    }

    public boolean needConnectParams(){
        InvokeExpr invokeExpr = this.getUnitInvokeExpr();
        SootMethod currentMethod = invokeExpr.getMethod();
        SootClass classOfCM = currentMethod.getDeclaringClass();

        if (classOfCM.getName().equals("java.security.AccessController")){
            return true;
        }
        return false;
    }

    public HashSet<SootMethod> findExactMethod(MethodDescriptor descriptor){

        HashSet<SootMethod> res = new HashSet<>();

        InvokeExpr invokeExpr = this.getUnitInvokeExpr();
        SootMethod currentMethod = invokeExpr.getMethod();

        Integer index = null;
        // 判断该方法的参数中是否包含java.security.PrivilegedAction，有就获取其参数位置
        for (int ind=0; ind< currentMethod.getParameterCount(); ind++){
            Type type = currentMethod.getParameterType(ind);
            if (type.toString().equals("java.security.PrivilegedAction")
                    || type.toString().equals("java.security.PrivilegedAction")
                    || type.toString().equals("java.security.PrivilegedExceptionAction")) {
                index = ind;
                break;
            }
        }
        // 获取java.security.PrivilegedAction类（专家经验总结的一系列类）中的所有方法
        // 并拿到里面的run方法，并将其变量进行污染
        if (index != null){
            Value arg = invokeExpr.getArg(index);
            String argTypeName = arg.getType().toString();
            SootClass sootClass = Scene.v().getSootClassUnsafe(argTypeName);
            if (sootClass != null){
                // ToDo:为什么不直接指定特定的方法名？ sootClass.getMethod();
                List<SootMethod> sootMethods = sootClass.getMethods();
                for (SootMethod sootMethod: sootMethods){
                    if (sootMethod.getName().equals("run") ){ //& !sootMethod.getReturnType().toString().equals("java.lang.Object")
                        res.add(sootMethod);
                        connectParameters(sootMethod, descriptor);
                    }
                }
            }
        }

        return res;

    }


    public void connectParameters(SootMethod invokedMethod, MethodDescriptor descriptor){
        if (!needConnectParams())
            return;

        InvokeExpr invokeExpr = this.getUnitInvokeExpr();
        // 因为 proxy 方法不可能被 cg 直接连上 因此无需考虑
        MethodDescriptor invokedDescriptor = BasicDataContainer.getOrCreateDescriptor(invokedMethod);

        if (invokedDescriptor == null)
            return;
        if (invokedDescriptor.cfg == null){
            CFG cfg = new CFG(invokedMethod, true);
            cfg.buildCFG();
            invokedDescriptor.cfg = cfg;
        }

        invokedDescriptor.paramIdMapLocalValue = Parameter.getParametersLocalValues(invokedDescriptor.cfg);

        List<Taint> taintRecords = new LinkedList<>();
        // 遍历被调用方法的每个传入的参数，如果传入的参数等同于已有污点参数，那么就记下这个污点
        for (Value arg: invokeExpr.getArgs()){
            for (Taint taint:descriptor.taints)
                if (taint.object.equals(arg))
                    taintRecords.add(taint);
        }
        // 如果有入参被污染，且与后续调用的方法类型相同，则将其污染
        for (Taint taint: taintRecords){
            if (taint.object.getType().toString().equals(invokedMethod.getDeclaringClass().getName())){
                invokedDescriptor.inputParamMapTaints.put(-1,descriptor.getAllTaintsAboutThisValue(taint.object));
                if (descriptor.pointTable.contains(taint)){
                    invokedDescriptor.paramValInfo.put(-1,descriptor.pointTable.getPointer(taint));
                }
                needInputTaintedParamFlush = false;
            }
        }
    }

    @Override
    public boolean equals(Object obj) {
        if(!(obj instanceof TransformableNode)) return false;
        return this.node.equals(((TransformableNode) obj).node);
    }

    // 去掉有正负值的记录，即提取真正需要相关的路径记录
    public void extractPathRecords(){
        HashSet<Integer> remove = new HashSet<>();
        for (Integer hashCode : path_record){
            if (path_record.contains(-hashCode))
                remove.add(hashCode);
        }
        for (Integer hashCode: remove){
            path_record.remove(hashCode);
            path_record.remove(-hashCode);
        }
    }

}
