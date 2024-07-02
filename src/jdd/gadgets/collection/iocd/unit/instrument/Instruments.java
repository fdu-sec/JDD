package gadgets.collection.iocd.unit.instrument;

import lombok.Getter;
import lombok.Setter;

import java.util.HashMap;
import java.util.HashSet;

@Getter
@Setter
public class Instruments {
    // 类名 <-> 存在的IfStmt
    public HashMap<String, HashSet<IfStmtInstRecord>> classIfStmtsMap = new HashMap<>();

//    // call site记录
//    public HashMap<String, HashSet<CallSiteInstRecord>> classCallsitesMap = new HashMap<>();

    // 需要进入的方法插桩
    public HashMap<String, HashSet<MethodInstRecord>> classMethodsMap = new HashMap<>();
    // 判断gadget是否可利用的sink点
    public HashSet<SinkInstRecord> sinkRecords = new HashSet<>();
}
