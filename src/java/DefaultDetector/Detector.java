package DefaultDetector;

import cfg.Node;
import lombok.extern.slf4j.Slf4j;
import soot.Scene;
import soot.SootClass;
import soot.SootMethod;

import java.io.File;
import java.io.FileWriter;
import java.io.IOException;
import java.io.Writer;
import java.util.ArrayList;
import java.util.HashSet;

/**
 * 实现了一些检测器的基础功能，可以选择继承它来复用
 */
@Slf4j
public class Detector {
    public Writer outputWriter, logWriter, errWriter, tempWriter;
    
    protected void init(String outPath){
        try {
            outputWriter = new FileWriter(new File(outPath, "output.txt"));
            logWriter = new FileWriter(new File(outPath, "log.txt"));
            errWriter = new FileWriter(new File(outPath, "error.txt"));
            tempWriter = new FileWriter(new File(outPath, "temp.txt"));
        } catch (IOException e) {
            e.printStackTrace();
        }
    }
    
    protected void finish(){
        try {
            outputWriter.close();
            logWriter.close();
            errWriter.close();
            tempWriter.close();
        } catch (IOException e) {
            e.printStackTrace();
        }
    }

    protected void print(String str) {
        try {
            log.info(str);
            outputWriter.write(str + "\n");
        } catch (IOException e) {
            e.printStackTrace();
        }
    }

    protected void printError(String str){
        try {
            errWriter.write(str + "\n");
        } catch (IOException e) {
            e.printStackTrace();
        }
    }

    protected void printLog(String str){
        try {
            logWriter.write(str + "\n");
        } catch (IOException e) {
            e.printStackTrace();
        }
    }

    protected void printTemp(String str){
        try {
            tempWriter.write(str + "\n");
        } catch (IOException e) {
            e.printStackTrace();
        }
    }

    protected void printOutput(String str){
        try {
            outputWriter.write(str + "\n");
        } catch (IOException e) {
            e.printStackTrace();
        }
    }

    protected HashSet<SootMethod> getMethodByNameFromClass(String className, String methodName){
        HashSet<SootMethod> methods = new HashSet<>();
        SootClass sootClass = Scene.v().getSootClass(className);
        if(sootClass == null) return methods;
        for(SootMethod sootMethod : sootClass.getMethods()){
            if(sootMethod.getName().equals(methodName)) methods.add(sootMethod);
        }
        return methods;
    }

    protected HashSet<SootMethod> getMethodByNameFromClass(String className, ArrayList<String > methodNames){
        HashSet<SootMethod> methods = new HashSet<>();
        SootClass sootClass = Scene.v().getSootClass(className);
        if(sootClass == null) return methods;
        for(SootMethod sootMethod : sootClass.getMethods()){
            if( methodNames.contains(sootMethod.getName()) ) methods.add(sootMethod);
        }
        return methods;
    }

    protected HashSet<Node> getNearbySuccessors(Node node, int lev){
        HashSet<Node> ret = new HashSet<>();
        if(lev == 0) return ret;
        for(Node successor : node.successorNodes){
            ret.add(successor);
            ret.addAll(getNearbySuccessors(successor, lev - 1));
        }
        return ret;
    }

    protected HashSet<Node> getNearbyPrecursors(Node node, int lev){
        HashSet<Node> ret = new HashSet<>();
        if(lev == 0) return ret;
        for(Node precursor : node.precursorNodes){
            ret.add(precursor);
            ret.addAll(getNearbyPrecursors(precursor, lev - 1));
        }
        return ret;
    }
}
