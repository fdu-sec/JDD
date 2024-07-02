package gadgets.collection.iocd.unit;

import dataflow.node.SourceNode;
import util.Pair;
import lombok.Getter;
import lombok.Setter;

import java.util.HashSet;
import java.util.LinkedList;
import java.util.List;

@Getter
@Setter
public class ClassRecord {

    public String className;    //  当前类
    public int id; // 对class Node 进行标识, 当多个同类型实例出现时, 方便处理
    // 记录<前继类 - 前继类下的属性>，如果为null则为第一个class
//    public Pair<String, String> predecessorRecord;
//    public LinkedList<String> preAccessPath = new LinkedList<>();
    public SourceRecord sourceRecord;
    public HashSet<SourceRecord> candidateSources = new HashSet<>();
//    // 从 MethodRecord -> LinkedList<MethodRecord>, 因为可能会出现从其他函数调用回该类
//    public LinkedList<MethodRecord> predecessorMethods = new LinkedList<>();
    public MethodRecord predecessorMethod;
    // field - <被使用的时候在哪个类文件中，在类文件中的行数>
    public HashSet<FieldRecord> usedFields;
    public List<FieldRecord> fields;
    public List<FieldRecord> conFields; // fieldRecord记录
    public LinkedList<ConditionRecord> allConditions;
    public LinkedList<MethodRecord> usedMethods;
    public boolean isProxy;
    public String triggerMethod;
    public HashSet<String> addProxyInterface = new HashSet<>();    // 封装为dynamic proxy instance时继承的类接口 (TODO: 暂时移除了，等测试稳定再重新集成)
    public boolean flag = true;
    public boolean changed = true;
}
