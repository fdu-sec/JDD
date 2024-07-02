package gadgets.collection.node;

import cfg.Node;
import dataflow.node.SourceNode;
import markers.SinkType;
import soot.SootClass;

import java.util.HashMap;
import java.util.HashSet;
import java.util.LinkedHashSet;

public class SinkNode {
    public SinkType sinkType;
    public SootClass sootClass;
    public Node node;
    public HashMap<Integer, HashSet<SourceNode>> controllableSinkValues = new HashMap<>();
    public SourceNode sinkObject;
    public SourceNode sinkMethodName;
    public SourceNode sinkMethod;

    public LinkedHashSet<SourceNode> sinkFilePath = new LinkedHashSet<>();
    public SourceNode sinkFileContent;

    public SinkNode(Node node, SootClass sootClass, SinkType sinkType){
        this.node = node;
        this.sootClass = sootClass;
        this.sinkType = sinkType;
    }

    public boolean equals(Object object){
        if (!(object instanceof SinkNode))
            return false;

        SinkNode sinkNode = (SinkNode) object;
        if (!sinkType.equals(sinkNode.sinkType)
                || !controllableSinkValues.entrySet().containsAll(sinkNode.controllableSinkValues.entrySet())
                || controllableSinkValues.size() != sinkNode.controllableSinkValues.size()
                || !sootClass.equals(sinkNode.sootClass)
                || !sinkFilePath.containsAll(sinkNode.sinkFilePath)
                || sinkFilePath.size() != sinkNode.sinkFilePath.size())
            return false;

        if ((sinkFileContent == null & sinkNode.sinkFileContent != null) | (sinkFileContent != null & sinkNode.sinkFileContent == null))
            return false;
        else if (sinkFileContent != null & sinkNode.sinkFileContent != null){
            if (!sinkFileContent.equals(sinkNode.sinkFileContent))
                return false;
        }

        if ((sinkObject == null & sinkNode.sinkObject != null) | (sinkObject != null & sinkNode.sinkObject == null))
            return false;
        else if (sinkObject != null & sinkNode.sinkObject != null){
            if (!sinkObject.equals(sinkNode.sinkObject))
                return false;
        }

        if ((sinkMethodName == null & sinkNode.sinkMethodName != null) | (sinkMethodName != null & sinkNode.sinkMethodName == null))
            return false;
        else if (sinkMethodName != null & sinkNode.sinkMethodName != null){
            if (!sinkMethodName.equals(sinkNode.sinkMethodName))
                return false;
        }

        if ((sinkMethod == null & sinkNode.sinkMethod != null) | (sinkMethod != null & sinkNode.sinkMethod == null))
            return false;
        else if (sinkMethod != null & sinkNode.sinkMethod != null){
            if (!sinkMethod.equals(sinkNode.sinkMethod))
                return false;
        }

        return true;
    }
}
