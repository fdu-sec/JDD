package cg;
import lombok.extern.slf4j.Slf4j;
import soot.*;
import soot.jimple.spark.SparkTransformer;
import soot.jimple.toolkits.callgraph.*;
import soot.options.Options;
import soot.util.queue.QueueReader;

import java.util.*;
import java.util.function.Function;

/**
 * 调用图（Call Graph）
 *
 * @since 2.0
 */
//@Slf4j
public class CG {

    public List<SootMethod> entryPoints;//入口方法
    public static LinkedList<String> excludeList;
    public CallGraph callGraph;
    public ReachableMethods reachableMethods;
    public TransitiveTargets transitiveTargets;
    public static Filter filter;

    private static boolean enableSpark = false;

    public static void setSpark(boolean b){
        enableSpark = b;
    }

    public CG(List<SootMethod> entryPoint){
        this.entryPoints =entryPoint;
        System.out.println("constructCG");
        this.callGraph=constructCG();
        System.out.println(("constructCG finish"));
        this.reachableMethods=Scene.v().getReachableMethods();
        if(filter==null){
            this.transitiveTargets=new TransitiveTargets(callGraph);
        }else {
            this.transitiveTargets=new TransitiveTargets(callGraph,filter);
        }
    }

    public CG(SootMethod entryPoint){
        this.entryPoints =Collections.singletonList(entryPoint);
        this.callGraph=constructCG();
        this.reachableMethods=Scene.v().getReachableMethods();
        if(filter==null){
            this.transitiveTargets=new TransitiveTargets(callGraph);
        }else {
            this.transitiveTargets=new TransitiveTargets(callGraph,filter);
        }
    }

    public CG(CallGraph callGraph){
        this.callGraph=callGraph;
        this.reachableMethods=Scene.v().getReachableMethods();
        if(filter==null){
            this.transitiveTargets=new TransitiveTargets(callGraph);
        }else {
            this.transitiveTargets=new TransitiveTargets(callGraph,filter);
        }
    }

    public HashSet<SootMethod> edgesOutOf(SootMethod method){
        HashSet<SootMethod> ret = new HashSet<>();
        Iterator<Edge> edgeIterator = callGraph.edgesOutOf(method);
        while (edgeIterator.hasNext()) {
            SootMethod invokeMethod = edgeIterator.next().tgt();
            ret.add(invokeMethod);
        }
        return ret;
    }

    public HashSet<SootMethod> edgesInto(SootMethod method){
        HashSet<SootMethod> ret = new HashSet<>();
        Iterator<Edge> edgeIterator = callGraph.edgesInto(method);
        while (edgeIterator.hasNext()) {
            SootMethod invokeMethod = edgeIterator.next().tgt();
            ret.add(invokeMethod);
        }
        return ret;
    }

    public void setFilter(Filter filter){
//        该Filter用于在查找某指定方法的调用方法时过滤
        CG.filter=filter;
    }

    protected void releaseCallgraph() {
        Scene.v().releaseCallGraph();
        Scene.v().releasePointsToAnalysis();
        Scene.v().releaseReachableMethods();
        G.v().resetSpark();
    }

    private static void enableSparkCallGraph() {
        //Enable Spark
        HashMap<String,String> opt = new HashMap<String,String>();
        opt.put("propagator","worklist");
        opt.put("simple-edges-bidirectional","false");
        opt.put("on-fly-cg","true");
        opt.put("verbose","true");
        opt.put("set-impl","double");
        opt.put("double-set-old","hybrid");
        opt.put("double-set-new","hybrid");
        opt.put("pre_jimplify", "true");
        SparkTransformer.v().transform("",opt);
        PhaseOptions.v().setPhaseOption("cg.spark", "enabled:true");
        PhaseOptions.v().setPhaseOption("cg.spark", "verbose:true");

    }

    private static LinkedList<String> excludeList() {
        if(excludeList==null)
        {
            excludeList = new LinkedList<String> (); // 扩展的基本函数package
            excludeList.add("java.");
            excludeList.add("javax.");
        }
        return excludeList;
    }
    private static void excludeJDKLibrary()
    {
        //exclude jdk classes
        Options.v().set_exclude(excludeList());
        Options.v().set_no_bodies_for_excluded(true);
        Options.v().set_allow_phantom_refs(true);
    }

    private CallGraph constructCG(){
        releaseCallgraph();
        if(enableSpark){
            enableSparkCallGraph();
        }
        excludeJDKLibrary();
        Scene.v().setEntryPoints(this.entryPoints);
        System.out.println(("runpack"));
        PackManager.v().runPacks();
        System.out.println("runpack finish");
        return Scene.v().getCallGraph();
    }

    public List<SootMethod> callerIntoMethod(SootMethod method){
//        获取指定方法的所有的调用者
        List<SootMethod> callerList=new ArrayList<>();
        Iterator<Edge> edgeIterator = callGraph.edgesInto(method);
        while (edgeIterator.hasNext()){
            callerList.add(edgeIterator.next().src());
        }
        return callerList;
    }

    public List<SootMethod> calleeOutOfMethod(SootMethod method){
//        获取指定方法的被调用者
        List<SootMethod> calleeList=new ArrayList<>();
        Iterator<Edge> edgeIterator = callGraph.edgesOutOf(method);
        while (edgeIterator.hasNext()){
            calleeList.add(edgeIterator.next().tgt());
        }
        return calleeList;
    }

    public HashSet<SootMethod> getAllReachableMethodFromEntry(){
//        返回从入口点可达的所有方法
        QueueReader<Edge> listener = callGraph.listener();
        HashSet<SootMethod> allReachableMethod=new HashSet<>();
        while (listener.hasNext()){
            allReachableMethod.add(listener.next().tgt());
        }
        return allReachableMethod;
    }

    // 判断方法是否在CG中
    public boolean isMethodInCG(SootMethod method){
        return reachableMethods.contains(method);
    }

    // 返回指定方法的所有直接或间接调用的方法
    public Iterator<MethodOrMethodContext> getAllMethodsCalledBy(SootMethod method){
        return transitiveTargets.iterator(method);
    }

    public HashSet<SootMethod> findMethodWithFilter(Function<SootMethod, Boolean> filter) {
        HashSet<SootMethod> ret = new HashSet<>();
        for(SootMethod sootMethod : getAllReachableMethodFromEntry()){
            if(filter.apply(sootMethod))
                ret.add(sootMethod);
        }
        return ret;
    }

    public HashSet<SootMethod> getAllReachableMethodsToTarget(SootMethod target){
        HashSet<SootMethod> reachableMethods = new HashSet<>();
        Queue<SootMethod> queue = new LinkedList<>();
        queue.add(target);
        reachableMethods.add(target);
        while (!queue.isEmpty()){
            SootMethod sootMethod = queue.poll();
            for (Iterator<Edge> it = callGraph.edgesInto(sootMethod); it.hasNext(); ) {
                Edge edge = it.next();
                if(!reachableMethods.contains(edge.src())) {
                    reachableMethods.add(edge.src());
                    queue.add(edge.src());
                }
            }
        }
        return reachableMethods;
    }

    public HashSet<String> getAllReachableMethodsSignatureToTarget(SootMethod target){
        HashSet<String> reachableMethods = new HashSet<>();
        Queue<SootMethod> queue = new LinkedList<>();
        queue.add(target);
//        int t = 0;
        reachableMethods.add(target.getSignature());
        while (!queue.isEmpty()){
//            t++;
//            if(t > 200000) break;
            SootMethod sootMethod = queue.poll();
            for (Iterator<Edge> it = callGraph.edgesInto(sootMethod); it.hasNext(); ) {
                Edge edge = it.next();
                if(!reachableMethods.contains(edge.src().getSignature())) {
                    queue.add(edge.src());
                    reachableMethods.add(edge.src().getSignature());
                }
            }
        }
        return reachableMethods;
    }

}
