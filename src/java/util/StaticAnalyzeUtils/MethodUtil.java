package util.StaticAnalyzeUtils;

import soot.Scene;
import soot.SootMethod;

import java.util.HashSet;

public class MethodUtil {
    /**
     * 从全局根据方法签名匹配方法
     * @param methodSig
     * @param level 1: signature, 2: sub signature, 3: method name
     * @return
     */
    public static HashSet<SootMethod> getMethodBySig(String methodSig, int level){
        if (level<=0 || level>3) return null;
        HashSet<SootMethod> ret = new HashSet<>();
        for (SootMethod tmpSootMethod: Scene.v().getMethodNumberer()){
            if (level == 1 && tmpSootMethod.getSignature().equals(methodSig))
                ret.add(tmpSootMethod);
            else if (level == 2 && tmpSootMethod.getSubSignature().equals(methodSig))
                ret.add(tmpSootMethod);
            else if (level == 3 && tmpSootMethod.getName().equals(methodSig))
                ret.add(tmpSootMethod);
        }
        return ret;
    }

    public static HashSet<String> getMethodDiffSig(String methodSig, int level){
        if (level<=0 || level>3) return null;
        HashSet<String> ret = new HashSet<>();
        for (SootMethod tmpSootMethod: Scene.v().getMethodNumberer()){
            if (level == 1 && tmpSootMethod.getSignature().equals(methodSig))
                ret.add(tmpSootMethod.getSignature());
            else if (level == 2 && tmpSootMethod.getSubSignature().equals(methodSig))
                ret.add(tmpSootMethod.getSubSignature());
            else if (level == 3 && tmpSootMethod.getName().equals(methodSig))
                ret.add(tmpSootMethod.getName());
        }
        return ret;
    }
}
