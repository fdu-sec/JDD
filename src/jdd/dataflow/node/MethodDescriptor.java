package dataflow.node;

import DefaultDetector.DefaultMethodDescriptor;
import PointToAnalyze.pointer.PointTable;
import PointToAnalyze.pointer.Pointer;
import tranModel.Taint.Taint;
import tranModel.TransformableNode;
import cfg.CFG;
import cfg.Node;
import dataflow.node.paramResult.MethodResult;
import dataflow.node.paramResult.TaintAndLinger;
import lombok.extern.slf4j.Slf4j;
import markers.SinkType;
import soot.*;
import soot.jimple.AssignStmt;
import soot.jimple.FieldRef;
import soot.jimple.ReturnStmt;
import util.ClassRelationshipUtils;
import util.Utils;

import java.util.*;

import static dataflow.DataFlow.findAllDefUnitAffectThisValue;

@Slf4j
public class MethodDescriptor extends DefaultMethodDescriptor {
    public CFG cfg = null;

    public SootClass currentClass = null;
    public boolean isDynamicEntry = false;
    public boolean isEntry = false;
    public boolean isDynProxyEntry = false;

    // 局部的上下文敏感
    public boolean visited  = false;
    public HashMap<TaintAndLinger, MethodResult> memorize = new HashMap<>();
    public SootField equalsField = null;


    public PointTable pointTable = new PointTable(this);
    public HashMap<Integer, Pointer> paramValInfo = new HashMap<>();

    public HashMap<Integer, Value> paramIdMapLocalValue = new HashMap<>();

    public HashMap<Integer, List<Taint>> paramBeTainted = new HashMap<>();
    public HashMap<Integer, List<Taint>> inputParamMapTaints = new HashMap<>();

    public HashSet<Taint> taints = new HashSet<>();
    public HashSet<Taint> newtaints = new HashSet<>();
    // 维护创建出的所有Taint， 其中的一些可能没有被实际污染（别名分析），实际污染的在taint里
    public HashSet<Taint> allTaints = new HashSet<>();
    // 记录返回值中被污染的对象
    public HashSet<Taint> retTainted = new HashSet<>();
    public ReturnStmt returnStmt = null;

    public HashMap<Integer, HashSet<SourceNode>> fieldsParamIndexRecord = new HashMap<>();
    public SourcesTaintGraph sourcesTaintGraph = new SourcesTaintGraph();

    public HashMap<SinkType, HashMap<TransformableNode, HashSet<SourceNode>>> sinkUnitsRecord = new HashMap<>();

    public HashSet<Value> tempGeneratedObjs = new HashSet<>();


    public MethodDescriptor(SootMethod method) {
        super(method);
        sourcesTaintGraph.descriptor = this;
    }


    public boolean needDetect(){
        if (!visited)
            return true;

        int paramTaint = 0;
        for (Integer ind: inputParamMapTaints.keySet()){    // 污点记录
            if (!inputParamMapTaints.get(ind).isEmpty()){
                paramTaint |= (1 << (ind + 1));
            }
        }

        for (Integer ind = inputParamMapTaints.size(); ind < inputParamMapTaints.size() + fieldsParamIndexRecord.size(); ind++){
            if (fieldsParamIndexRecord.containsKey(ind - inputParamMapTaints.size()))
                if (!fieldsParamIndexRecord.get(ind - inputParamMapTaints.size()).isEmpty())
                    paramTaint |= (1 <<(ind+1));
        }
        TaintAndLinger tmp = new TaintAndLinger(paramTaint);

        if (memorize.containsKey(tmp)){
            paramBeTainted = memorize.get(tmp).paramBeTainted;
            retTainted = memorize.get(tmp).retTainted;
           return false;
        }

        return true;
    }

    public void flushStates(){
        currentClass = null;

        allTaints = new HashSet<>();
        taints = new HashSet<>();
        newtaints = new HashSet<>();

        paramIdMapLocalValue = new HashMap<>();
        paramBeTainted = new HashMap<>();
        retTainted = new HashSet<>();
        pointTable = new PointTable(this);
        sourcesTaintGraph.sources2TaintedValues = new HashMap<>();
        sourcesTaintGraph.sourceUnFound = new HashMap<>();
    }

    /**
     * 返回已有的污点或者新建一个污点：
     * 1、如果object为null，那就直接返回new Taint(null, accessPath);
     * 2、如果object不为null：
     *  a. accessPath为null，那就查看是否存在已有的污点，有就返回没有就新建后返回
     *  b. accessPath不为null，同上
     * accessPath是用于记录一个类中被污染了的field
     * @param object
     * @param accessPath
     * @return
     */
    public Taint getOrCreateTaint(Value object, LinkedList<SootField> accessPath){

        if(object == null){
            return new Taint(null, accessPath);
        }

        if(accessPath == null){
            for(Taint taint : allTaints){
                if(taint.object.equals(object)){
                    if(taint.accessPath.isEmpty()){
                        return taint;
                    }
                }
            }
            Taint taint = new Taint(object);
            Taint.addTaint(taint, allTaints);
            return taint;
        } else{
            for(Taint taint : allTaints){
                if(taint.object.equals(object)){
                    if(Utils.listEqual(accessPath, taint.accessPath)){
                        return taint;
                    }
                }
            }
            Taint taint = new Taint(object, accessPath);
            Taint.addTaint(taint, allTaints);
            return taint;
        }

    }


    public List<Taint> getAllTaintsAboutThisValue(Value object){
        List<Taint> taintsForValue = new LinkedList<>();
        for(Taint taint : this.taints){
            if(taint.object.equals(object)){
                taintsForValue.add(taint);
            }
        }
        return taintsForValue;
    }

    /**
     * 获得所有有关这个Value的新增的taint，排除初始传入的taint
     * 和getAllTaintsAboutThisValue一样, 都是不考虑fields敏感的匹配
     */
    public List<Taint> getAllNewTaintsAboutThisValue(Value object){
        List<Taint> taintsForValue = new LinkedList<>();
        for(Taint taint : this.newtaints){
            if(taint.object.equals(object)){
                taintsForValue.add(taint);
            }
        }
        return taintsForValue;
    }

    /**
     * 1、给定mayTaint判断是否存在与当前的污点列表中，如果在便返回ture不是则返回false
     * 2、给定与mayTaint相关的beAddBox，比如a = b.Fuc(c); 如果c是污点，那么显然污点需要传递到a
     * @param mayTaint
     * @param beAddBox
     * @return
     */
    public boolean addTaint(Value mayTaint, ValueBox beAddBox){
        boolean risky = false;
        for (Taint taint: taints){
            if (taint.object.equals(mayTaint)){
                risky = true;

                if (beAddBox != null){
                    Taint newTaint = getOrCreateTaint(beAddBox.getValue(), new LinkedList<>(taint.accessPath));
                    Taint.addTaint(newTaint,taints);
                }
                break;
            }
        }

        return risky;
    }

    /**
     * 检查污点情况, 进行必要的更新
     * (1) 检查污点是否合法: 是否为 null
     */
    public void flushTaints(){
        HashSet<Taint> toDelete = new HashSet<>();
        for (Taint taint: taints){
            if (taint == null)
                toDelete.add(taint);
        }
        taints.removeAll(toDelete);

        toDelete = new HashSet<>();
        for (Taint taint: allTaints){
            if (taint == null)
                toDelete.add(taint);
        }
        allTaints.removeAll(toDelete);

        toDelete = new HashSet<>();
        for (Taint taint: newtaints){
            if (taint == null)
                toDelete.add(taint);
        }
        newtaints.removeAll(toDelete);
    }

    public SootField getField(Node sourceNode, ValueBox valueBox) {
        if (valueBox == null) return null;
        SourceNode sourceNodeOfField = getFieldSourceNode(sourceNode, valueBox);
        if (sourceNodeOfField != null)
            return sourceNodeOfField.field.getFirst();

        return getFieldDirectly(sourceNode, valueBox);
    }

    public SourceNode getFieldSourceNode(Node sourceNode, ValueBox valueBox){
        HashSet<SourceNode> sources = sourcesTaintGraph.matchTaintedSources(valueBox.getValue());
        for (SourceNode source : sources){
            if (source.isField()){
                SootField sootField = source.field.getLast(); // 默认返回最后一个, 就是最里层的field
                if (valueBox.getValue().getType().toString().equals("java.lang.Object")
                        | (valueBox.getValue().getType().equals(sootField.getType()))
                        | ClassRelationshipUtils.isSubClassOf(
                        Utils.toSootClass(valueBox.getValue().getType()), Utils.toSootClass(sootField.getType()))
                        | (sootField.getType().toString().contains(valueBox.getValue().getType().toString()))){
                    return source;
                }
            }
        }
        return null;
    }

    public SootField getFieldDirectly(Node sourceNode, ValueBox valueBox) {
        if (valueBox == null) return null;
        if (valueBox.getValue() instanceof FieldRef)
            return ((FieldRef) valueBox.getValue()).getField();

        LinkedHashSet<Node> sources = findAllDefUnitAffectThisValue(sourceNode,valueBox);

        Value taint = valueBox.getValue();
        for (Node node: sources){
            if (node.unit instanceof AssignStmt){
                Value left = ((AssignStmt)node.unit).getLeftOp();
                Value right = ((AssignStmt)node.unit).getRightOp();

                if (left.equals(taint)){
                    if (right instanceof FieldRef)
                        return ((FieldRef) right).getField();
                    taint = right;
                }
            }
        }
        return null;
    }

    public SootClass getCurrentClass() {
        if (currentClass != null)
            return currentClass;
        if (paramValInfo.containsKey(-1)){
            Pointer thisPointer = paramValInfo.get(-1);
            SootClass tmpClassOfPointerType = Utils.toSootClass(thisPointer.getType());
            if (ClassRelationshipUtils.isSubClassOf(tmpClassOfPointerType, sootMethod.getDeclaringClass()))
                currentClass = Utils.toSootClass(thisPointer.getType());
            else currentClass = sootMethod.getDeclaringClass();
        }else {
            currentClass = sootMethod.getDeclaringClass();
        }
        return currentClass;
    }
}
