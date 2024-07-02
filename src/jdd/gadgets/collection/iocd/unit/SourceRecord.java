package gadgets.collection.iocd.unit;

import util.Pair;

import java.util.LinkedList;

public class SourceRecord {
    public Pair<String, String> predecessorRecord;
    public LinkedList<String> preAccessPath = new LinkedList<>();

    public SourceRecord(Pair<String,String> predecessorRecord, LinkedList<String> preAccessPath){
        this.predecessorRecord = predecessorRecord;
        this.preAccessPath = preAccessPath;
    }
}
