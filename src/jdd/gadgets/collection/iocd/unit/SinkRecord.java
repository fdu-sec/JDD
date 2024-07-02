package gadgets.collection.iocd.unit;

import lombok.Getter;
import lombok.Setter;
import util.Pair;

import java.util.*;

@Getter
@Setter
public class SinkRecord {

    public String sinkClassName;
    public MethodRecord sinkMethod;
    public String jimpleUnitInfo;
    public HashSet<Pair<Integer, FieldRecord>> sinkField = new HashSet<>();

    public FieldRecord sinkClassBelongToF;
    public FieldRecord sinkMethodNameF;
    public FieldRecord sinkMethodF;
    public FieldRecord sinkProxyInvokeType; //记录是哪个代理，切换调用对象的时候需要更换这个值
    public String trigger = "NONE";  // NONE: 未识别出限制/没有限制 ; getter ; setter
    public LinkedHashSet<FieldRecord> sinkFilePathF = new LinkedHashSet<>();
    public FieldRecord sinkFileContentF;
}
