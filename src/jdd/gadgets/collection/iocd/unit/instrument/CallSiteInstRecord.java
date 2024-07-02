package gadgets.collection.iocd.unit.instrument;

public class CallSiteInstRecord {
    // 调用该方法的方法信息
    public String callerClassName;
    public String callerSubSig;
    public String callerName;

    // call site点信息
    public String calleeClassName;
    public String calleeSubSig;
    public String calleeName;
    public boolean isAbstractOrInterface;
    // 位置
    public int lineNumber;
}
