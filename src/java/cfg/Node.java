package cfg;
import lombok.Getter;
import lombok.Setter;
import soot.SootMethod;
import soot.Unit;
import soot.jimple.toolkits.callgraph.Edge;

import java.util.HashSet;
import java.util.Iterator;

@Getter
@Setter
public class Node {
    public Unit unit;
    public HashSet<Node> precursorNodes = new HashSet<>();//保存语句的直接前驱节点
    public HashSet<Node> successorNodes = new HashSet<>();//保存语句的后继
    public String tag;
    public boolean isExpand=false;//如果节点是方法，标记该处的方法是展开了
    public SootMethod sootMethod; // 该Node所属于的SootMethod

    public HashSet<Node> originPreNode=new HashSet<>();//用于保存最初始的前驱节点
    public HashSet<Node> originSuccorNode=new HashSet<>();//用于保存最初始的后继节点

    public Node(Unit unit) {
        this.unit = unit;
    }

    public Node(Unit unit, SootMethod sootMethod){
        this.unit = unit;
        this.sootMethod = sootMethod;
    }

    public Node(String tag) {
        this.tag = tag;
    }

    public String toString(){
        if(this.unit == null) return "<Null Unit>";
        return this.unit.toString();
    }


}
