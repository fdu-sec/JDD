package DefaultDetector;

import soot.SootMethod;

/**
 * 方法描述类，用于在检测时记录一个方法的检测结果，避免多次检测。
 */
public class DefaultMethodDescriptor implements IMethodDescriptor{

    @Override
    public boolean isCompletelyDescribed() {
        return false;
    }

    @Override
    public void forceSetDescribed() {

    }

    public enum State{
        YES, NO, UNKNOWN
    }

    public SootMethod sootMethod;

    public DefaultMethodDescriptor(SootMethod method){
        this.sootMethod = method;
    }
}
