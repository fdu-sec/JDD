package util.StaticAnalyzeUtils;

import cg.CG;
import soot.SootClass;
import soot.SootMethod;
import soot.jimple.toolkits.callgraph.Edge;
import soot.tagkit.*;

import java.util.*;

/**
 * 静态分析基本能力
 */
public class Method {
    public static List<SootMethod> getCallPath(SootMethod src, SootMethod tgt, CG cg){
        Stack<SootMethod> record = new Stack<>();
        if(dfsCGFromEntry(src, tgt, cg, record, new HashSet<>(), 20)){
            return new LinkedList<>(record);
        }
        else return null;
    }

    private static boolean dfsCGFromEntry(SootMethod sootMethod, SootMethod tgt, CG cg, Stack<SootMethod> record, HashSet<SootMethod> visited, int limit){
//        log.info(sootMethod.getSignature());
        if(sootMethod.equals(tgt)) {
            record.push(tgt);
            return true;
        }
        if(limit == 0) return false;
        visited.add(sootMethod);
        record.push(sootMethod);
        for (Iterator<Edge> it = cg.callGraph.edgesOutOf(sootMethod); it.hasNext(); ) {
            SootMethod invokeMethod = it.next().tgt();
            if(visited.contains(invokeMethod)) continue;
            if(dfsCGFromEntry(invokeMethod, tgt, cg, record, visited, limit - 1)) {
                return true;
            }
        }
        record.pop();
        return false;
    }
    public static List<SootMethod> getCallPathToTgtSet(SootMethod src, HashSet<SootMethod> tgts, CG cg){
        Stack<SootMethod> record = new Stack<>();
        if(dfsCGFromEntryToTgtSet(src, tgts, cg, record, new HashSet<>(), 20)){
            return new LinkedList<>(record);
        }
        else return null;
    }

    private static boolean dfsCGFromEntryToTgtSet(SootMethod sootMethod, HashSet<SootMethod> tgts, CG cg, Stack<SootMethod> record, HashSet<SootMethod> visited, int limit){
        if(tgts.contains(sootMethod)){
            record.push(sootMethod);
            return true;
        }
        if(limit == 0) return false;
        visited.add(sootMethod);
        record.push(sootMethod);
        for (Iterator<Edge> it = cg.callGraph.edgesOutOf(sootMethod); it.hasNext(); ) {
            SootMethod invokeMethod = it.next().tgt();
            if(visited.contains(invokeMethod)) continue;
            if(dfsCGFromEntryToTgtSet(invokeMethod, tgts, cg, record, visited, limit - 1)) {
                return true;
            }
        }
        record.pop();
        return false;
    }

    public static HashSet<AnnotationTag> getClassAnnotations(SootClass sootClass){
        HashSet<AnnotationTag> ret = new HashSet<>();
        if(sootClass.getTags().size()==0){
            return ret;
        }

        VisibilityAnnotationTag visibilityAnnotationTag = (VisibilityAnnotationTag) sootClass.getTag("VisibilityAnnotationTag");
        if (visibilityAnnotationTag !=null){
            ret.addAll(visibilityAnnotationTag.getAnnotations());
        }
        return ret;
    }

    public static HashSet<AnnotationTag> getMethodAnnotations(SootMethod sootMethod){
        HashSet<AnnotationTag> ret = new HashSet<>();
        if(sootMethod.getTags().size()==0){
            return ret;
        }

        VisibilityAnnotationTag visibilityAnnotationTag = (VisibilityAnnotationTag) sootMethod.getTag("VisibilityAnnotationTag");
        if (visibilityAnnotationTag !=null){
            for (AnnotationTag annotationTag:visibilityAnnotationTag.getAnnotations()){
                ret.add(annotationTag);
            }
        }
        return ret;
    }


}
