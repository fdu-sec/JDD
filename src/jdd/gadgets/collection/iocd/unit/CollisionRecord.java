package gadgets.collection.iocd.unit;

import java.util.LinkedList;

public class CollisionRecord {
    public int type;
    public MethodRecord collisionMethodRecord; // 发生碰撞的方法
    public MethodRecord firstHashCodeMtd;
    public MethodRecord secondHashCodeMtd;
    public LinkedList<FieldRecord> top = new LinkedList<>();
    public LinkedList<FieldRecord> first = new LinkedList<>();    // 记录hashCode相关的fields 【第一个元素，前后顺序可调用(变异测试时进行顺序反转测试)】
    public LinkedList<FieldRecord> second = new LinkedList<>(); // 如果存在一个为空则认为是常量
}
