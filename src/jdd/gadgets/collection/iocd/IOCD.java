package gadgets.collection.iocd;

import gadgets.collection.iocd.unit.*;
import markers.SinkType;
import org.apache.commons.collections4.map.ListOrderedMap;
import util.Pair;

import java.util.*;
import java.util.concurrent.LinkedBlockingQueue;

public class IOCD {
    public int hashCode;
    public boolean hashCollisionFlag = false;
    public String sinkType; // sink类型
    public String protocol; // 记录协议信息
    public boolean needSerialize; // 记录 gadget chain 中是否都继承了序列化接口

    // 为了提高拼接效率, 记录一些反射拼接相关的约束信息
    public boolean publicEntry;
    public String entryType = "none";

    public LinkedList<Pair<Integer, String>> gadgetCallStack; // gadget chains
    public LinkedList<ClassRecord> gadgetClasses = new LinkedList<>(); // 记录类层次结构
    public HashSet<ClassRecord> conClassNodes = new HashSet<>(); // 偏离gadget chains路径的class nodes (不一定准确和必要，按需选用)
    // 对应的Condition hashCode : 是否为必要 Condition
    public LinkedHashMap<Integer,Boolean> conditionsRecords = new LinkedHashMap<>();
    public HashSet<DependenceRecord> dependenceRecords = new HashSet<>(); // 记录依赖关系
    public CollisionRecord hashCollisionRecord; // 记录哈希碰撞信息
    public HashSet<UsedSiteRecord> usedFieldsRecords = new HashSet<>(); // fields使用信息记录
    public HashSet<ConditionRecord> supplementConditions = new HashSet<>(); // 所有非主干的conditions

    public List<SinkRecord> sinkRecords = new ArrayList<>(); // 记录用于构造注入sinks的attack payloads的相关fields

}
