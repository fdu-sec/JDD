package gadgets.collection.node;

import dataflow.node.SourceNode;
import soot.SootMethod;

import java.util.LinkedList;


public class CollisionNode {
    public boolean flag = false; // true代表(2-2)
    public int type = 2;
    public SootMethod firstHashCodeMtd;
    public SootMethod secondHashCodeMtd;
    public SootMethod collisionMethod; // 发生哈希碰撞的方法
    //  Case A(1): E.g. 单个 equals; (Con)HashMap.readObject -> a.equals -> b.mtd, 而可以设置Map中的table中的Nodes: Node_1: key(a),value(b), Node_2: key(b),value(a)
    //  Case B(2): E.g. 两个equals嵌套; HashMap.readObject -> EqM.equals -> a.equals -> b..., 可以设置HashMap.table中的Nodes为两个EqM, EqM中的控制hashCode的fields等价 (之前最常处理的情况)
    //  Case C(3): E.g. 非嵌套的hash碰撞; a.equals -> b... 两个不同的a实例,但是控制hash值的field中设置相同实例b

    // 属于Case A的时候有内容(有top以后就无需再考虑first&second, 因为可以设置为两个一样的实例，交叉赋值 ^ );
    // 而first&second具体指哪个后续对象，根据类层次结构查找，指向该(top)field的
    public LinkedList<SourceNode> top = new LinkedList<>();
    public LinkedList<SourceNode> first = new LinkedList<>(); // first, second对应为用于碰撞的两个实例, e.g. Case A的a和b; Case B 的EqM; Case C的a
    public LinkedList<SourceNode> second = new LinkedList<>();
}
