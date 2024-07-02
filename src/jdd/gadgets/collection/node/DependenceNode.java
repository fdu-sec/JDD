package gadgets.collection.node;

import dataflow.node.SourceNode;
import gadgets.collection.markers.DependenceType;


public class DependenceNode {
    public DependenceType type;
    public SourceNode left;
    public SourceNode right;
    public String methodName;

    public DependenceNode(SourceNode left, SourceNode right, DependenceType type){
        this.left = left;
        this.right = right;
        this.type = type;
    }

    public DependenceNode(SourceNode left, SourceNode right, DependenceType type, String methodName){
        this.left = left;
        this.right = right;
        this.type = type;
        this.methodName = methodName;
    }

    public boolean equals(Object object){
        if (!(object instanceof DependenceNode))
            return false;

        DependenceNode dependenceNode = (DependenceNode) object;
        if (!type.equals(dependenceNode.type)
                | !left.equals(dependenceNode.left)
                | !right.equals(dependenceNode.right))
            return false;

        if ((methodName != null & dependenceNode.methodName == null)
                | (methodName == null & dependenceNode.methodName != null))
            return false;

        if (methodName != null)
            if (!methodName.equals(dependenceNode.methodName))
                return false;

        return true;
    }
}
