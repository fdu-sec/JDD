package dataflow.node.paramResult;

import PointToAnalyze.pointer.PointTable;
import tranModel.Taint.Taint;
import dataflow.node.SourcesTaintGraph;

import java.util.*;

public class MethodResult {
    public HashMap<Integer, List<Taint>> paramBeTainted = new HashMap<>();
    public HashSet<Taint> retTainted = new HashSet<>();
    public PointTable pointTable = null;
    public SourcesTaintGraph sourcesTaintGraph = null;

    public MethodResult(HashMap<Integer, List<Taint>> paramBeTainted, HashSet<Taint> retTainted){
        this.paramBeTainted = paramBeTainted;
        this.retTainted = retTainted;
    }

    public MethodResult(HashMap<Integer, List<Taint>> paramBeTainted, HashSet<Taint> retTainted,
                        PointTable pointTable, SourcesTaintGraph sourcesTaintGraph){
        this.paramBeTainted = paramBeTainted;
        this.retTainted = retTainted;
        this.pointTable = pointTable;
        this.sourcesTaintGraph = sourcesTaintGraph;
    }
}
