package cg;

import soot.SootMethod;

import java.util.ArrayList;
import java.util.List;

public class Node {

    public List<Node> preNode;
    public List<Node> postNode;
    public SootMethod sootMethod;


    public Node(SootMethod sootMethod){
        this.sootMethod=sootMethod;
        preNode=new ArrayList<>();
        postNode=new ArrayList<>();
    }
}
