package tranModel;

import soot.SootClass;
import soot.SootMethod;

/**
 * 该类用于记录一个sootMethod和声明他的sootClass
 * 用于TransformableNode中
 */
public class Context {
    public SootMethod method;
    public SootClass sootClass;
}
