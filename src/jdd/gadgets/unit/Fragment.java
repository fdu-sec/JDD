package gadgets.unit;

import PointToAnalyze.pointer.Pointer;
import dataflow.DataFlowAnalysisUtils;
import soot.SootClass;
import tranModel.Rules.RuleUtils;
import cfg.Node;
import config.RegularConfig;
import container.BasicDataContainer;
import container.FragmentsContainer;
import dataflow.node.MethodDescriptor;
import lombok.Getter;
import lombok.Setter;
import markers.SinkType;
import soot.SootMethod;
import soot.Value;
import soot.ValueBox;
import soot.jimple.InvokeExpr;
import soot.jimple.Stmt;
import tranModel.TransformableNode;
import util.ClassRelationshipUtils;
import util.StaticAnalyzeUtils.Parameter;
import util.Utils;

import java.util.HashMap;
import java.util.HashSet;
import java.util.LinkedList;

import static tranModel.Rules.RuleUtils.sanitizerArrayElement;
import static dataflow.DataFlowAnalysisUtils.shortPriorityLinkCheck;
import static util.ClassRelationshipUtils.isDynamicMethod;
import static util.ClassRelationshipUtils.isValidSuperAbstractOrInterfaceMethod;

/**
 * Fragment数据结构
 */
@Getter
@Setter
public class Fragment {
    boolean flag = true; // 标识该Fragment的合法性, 如果flag==false则移除Fragment
    public enum FRAGMENT_STATE{SOURCE, FREE_STATE, SINK};
    public FRAGMENT_STATE state = null;
    public enum FRAGMENT_TYPE{POLYMORPHISM, DYNAMIC_PROXY, REFLECTION} // 跟进head判断
    public FRAGMENT_TYPE type = null;

    public SinkType sinkType = null;

    public SootMethod head = null; // 起始方法, 记录具体实现

    public SootMethod end = null; // 动态方法调用, 记录的调用方法已经考虑指针分析结果

    public HashSet<SootMethod> endInvokableMethods = null;

    public TransformableNode invokeNode = null;
    public LinkedList<SootMethod> gadgets = new LinkedList<>();

    public HashMap<Integer, HashSet<HashSet<Integer>>> endToHeadTaints = new HashMap<>();

    public ConnectRequire connectRequire = null;

    public int priority = 1;

    public LinkedList<Integer> linkedFragments = new LinkedList<>(); //  顺序记录
    public LinkedList<SootMethod> linkedDynamicMethods = new LinkedList<>();

    private Fragment(Fragment fragment){
        this.flag = fragment.flag;
        this.state = fragment.state;
        this.type = fragment.type;
        this.sinkType = fragment.sinkType;
        this.head = fragment.head;
        this.end = fragment.end;
        this.endInvokableMethods = new HashSet<>(fragment.endInvokableMethods);
        this.invokeNode = fragment.invokeNode;
        this.gadgets = new LinkedList<>(fragment.gadgets);
        this.endToHeadTaints = new HashMap<>(fragment.endToHeadTaints);
        this.connectRequire = fragment.connectRequire;
        this.priority = fragment.priority;
        this.linkedFragments = new LinkedList<>(fragment.linkedFragments);
        this.linkedDynamicMethods = new LinkedList<>(fragment.linkedDynamicMethods);
    }

    public Fragment(MethodDescriptor descriptor, LinkedList<SootMethod> chain,
                    SootMethod invokeMtd, TransformableNode invokeNode,
                    HashSet<SootMethod> endInvokableMethods) {

        gadgets = new LinkedList<>(chain);
        head = chain.get(0);
        this.invokeNode = invokeNode;
        this.end = invokeMtd;
        if (endInvokableMethods != null)
            this.endInvokableMethods = endInvokableMethods;
        init(descriptor);

        if (flag){
            FragmentsContainer.basicFragmentsMap.put(this.hashCode(), this);
        }
    }

    public Fragment(Fragment preFragment, Fragment sucFragment){
        boolean isEqualsConnectFlag = false;
        if (RuleUtils.isEqMethod(preFragment.head)
                && RuleUtils.isEqMethod(sucFragment.head)){
            if (!RuleUtils.isValidEqualsConnect(preFragment,sucFragment)){
                flag = false;
                return;
            }
            isEqualsConnectFlag = true;
        }
        if (!isEqualsConnectFlag) {
            if (!shortPriorityLinkCheck(preFragment, sucFragment)) {
                flag = false;
                return;
            }
        }

        HashSet<HashSet<Integer>> paramsTaitRequires = RuleUtils.linkCheckOfTaints(preFragment, sucFragment);
        if (paramsTaitRequires.isEmpty()){
            flag = false;
            return;
        }else if (paramsTaitRequires.size() == 1
                & preFragment.gadgets.getFirst().getSubSignature().equals("boolean equals(java.lang.Object)")){
            HashSet<Integer> requires = paramsTaitRequires.iterator().next();
            if (requires.isEmpty())
                requires.add(0);
        }

        this.connectRequire = new ConnectRequire(paramsTaitRequires, preFragment.connectRequire.preLinkableMethods);
        this.connectRequire.dynamicProxyLinkCheck = preFragment.connectRequire.dynamicProxyLinkCheck;
        this.connectRequire.reflectionCheck = preFragment.connectRequire.reflectionCheck;


        type = sucFragment.type;
        sinkType = sucFragment.sinkType;


        LinkedList<SootMethod> gadgets = new LinkedList<>(preFragment.gadgets);
        gadgets.addAll(sucFragment.gadgets);
        this.gadgets = gadgets;


        head = preFragment.head;
        end = sucFragment.end;
        invokeNode = sucFragment.invokeNode;
        state = preFragment.state;


        LinkedList<Integer> tmpLinkedFragments = new LinkedList<>(sucFragment.linkedFragments);
        tmpLinkedFragments.addFirst(preFragment.hashCode());
        linkedFragments.addAll(new LinkedList<>(tmpLinkedFragments));

        linkedDynamicMethods.add(preFragment.end);
        linkedDynamicMethods.addAll(sucFragment.linkedDynamicMethods);

        if (flag){
            for (HashSet<Integer> condSet: paramsTaitRequires){
                if (!FragmentsContainer.paramsTaitRequireSinkFragmentsMap.containsKey(condSet))
                    FragmentsContainer.paramsTaitRequireSinkFragmentsMap.put(condSet, new HashSet<>());
                FragmentsContainer.paramsTaitRequireSinkFragmentsMap.get(condSet).add(this);
            }
        }
    }

    private void init(MethodDescriptor descriptor){
        assert head != null & end != null;

        if (!validFragmentCheck())
            return;

        if (FragmentsContainer.protocolCheckRule.isSource(head)){
            state = FRAGMENT_STATE.SOURCE;
        }
        else if (FragmentsContainer.isSinkMethod(end)) {
            state = FRAGMENT_STATE.SINK;
            linkedFragments.add(this.hashCode());
        }

        initForPolymorphism(descriptor);
        recordProxyRequires(descriptor);
    }

    public Fragment copy(Fragment fragment){
        return new Fragment(fragment);
    }

    public void initForPolymorphism(MethodDescriptor descriptor){
        if (!RuleUtils.isValidEqualsMethod(head, end, state)){
            flag = false;
            return;
        }

        HashSet<SootMethod> preLinkableMethods = new HashSet<>();
        if (state == null || FRAGMENT_STATE.SINK.equals(state)) {
            for (SootMethod superMethod : ClassRelationshipUtils.getAllSuperMethods(head, false)) {
                if (!ClassRelationshipUtils.isDynamicMethod(superMethod)) continue;
                preLinkableMethods.add(superMethod);
            }
        }

        HashSet<SootMethod> toDelete = new HashSet<>();
        for (SootMethod mtd1: preLinkableMethods){
            for (SootMethod mtd2: preLinkableMethods){
                if (mtd1.equals(mtd2))
                    continue;
                if (!mtd1.getSubSignature().equals(mtd2.getSubSignature()))
                    continue;

                if (ClassRelationshipUtils.isSubClassOf(mtd1.getDeclaringClass(), mtd2.getDeclaringClass()))
                    toDelete.add(mtd1);
            }
        }
        preLinkableMethods.removeAll(toDelete);

        this.connectRequire = new ConnectRequire(preLinkableMethods);

        if (state == null) {
            if (!connectRequire.preLinkableMethods.isEmpty())
                state = FRAGMENT_STATE.FREE_STATE;
            else {
                flag = false;
                return;
            }
        }

        // 设置 type
        if (state.equals(FRAGMENT_STATE.SOURCE)) {
            if (RegularConfig.protocol.equals("json"))
                type = FRAGMENT_TYPE.REFLECTION;
            else
                type = null;
        }
        else if (BasicDataContainer.commonMtdMap.get("invokeHandler").getSubSignature().equals(head.getSubSignature()))
            type = FRAGMENT_TYPE.DYNAMIC_PROXY; // 包含POLYMORPHISM
        else if (!preLinkableMethods.isEmpty())
            type = FRAGMENT_TYPE.POLYMORPHISM;
        else flag = false;

        if (!flag)
            return;

        if (!state.equals(FRAGMENT_STATE.SINK) & !state.equals(FRAGMENT_STATE.SOURCE)){
            if (gadgets.size() > BasicDataContainer.polyLenLimit){
                flag = false;
                return;
            }
        }
        setTaintsDependence(descriptor, invokeNode.node);
    }

    public void initForDynamicProxy(MethodDescriptor descriptor){

    }

    public SootClass getClassForHead(){
        SootClass headClz = head.getDeclaringClass();
        if (gadgets.size() < 2) return headClz;
        SootClass nextClz = gadgets.get(1).getDeclaringClass();
        if (ClassRelationshipUtils.isSubClassOf(nextClz, headClz)
                && nextClz.getMethodUnsafe(head.getSubSignature()) == null)
            return nextClz;

        return headClz;
    }

    /**
     * 目前采取简化处理的方法: Fragment(Proxy) head->end
     */
    public void recordProxyRequires(MethodDescriptor descriptor){
        if (!ClassRelationshipUtils.isProxyMethod(head))
            return;
        if (!state.equals(FRAGMENT_STATE.SINK)){
            flag = false;
            return;
        }

        extractProxyInfos(descriptor);
    }

    public void extractProxyInfos(MethodDescriptor descriptor){
        TransformableNode nextTfNode = RecordUtils.findTfNodeToNextMtd(descriptor, gadgets);

        HashSet<Integer> path_record = nextTfNode.path_record;
        for (Integer hashCode : path_record){
            if (path_record.contains(-hashCode))
                continue;

            TransformableNode addIfStmt = TransformableNode.ifStmtHashMap.get(hashCode > 0 ? hashCode:-hashCode);
            if (addIfStmt == null)  continue;
            // 必要条件分支hashCode，便于进行后续的分支敏感验证
            connectRequire.condSet.add(hashCode);
//            RecordUtils.extractMethodName(nextTfNode, descriptor);
        }
    }

    public void setTaintsDependence(MethodDescriptor descriptor, Node invokeNode){
//        MethodDescriptor descriptor = BasicDataContainer.getOrCreateDescriptor(this.invokeNode.method);
//        descriptor = BasicDataContainer.getOrCreateDescriptor(gadgets.getLast());
        assert descriptor != null;

        ValueBox thisValueBox = Parameter.getThisValueBox(invokeNode);
        if (thisValueBox != null){
            if (Utils.isTainted(thisValueBox.getValue(), descriptor.taints)) {
                if (sanitizerArrayElement(descriptor, thisValueBox)){
                    flag = false;
                    return;
                }
                HashSet<Integer> conParams = Utils.getEndToHeadTaintsCon(descriptor, thisValueBox.getValue());
                addEndToHeadTaints(-1, conParams);
            }
        }

        InvokeExpr invokeExpr = ((Stmt) invokeNode.unit).getInvokeExpr();
        for (int ind = 0; ind < invokeExpr.getArgCount(); ind++){
            Value argValue = invokeExpr.getArg(ind);
            if (Utils.isTainted(argValue, descriptor.taints)) {
                HashSet<Integer> conParams = Utils.getEndToHeadTaintsCon(descriptor, argValue);
                addEndToHeadTaints(ind, conParams);
            }
        }
    }


    public void addEndToHeadTaints(int ind, HashSet<Integer> conParms){
        if (!endToHeadTaints.containsKey(ind)) {
            endToHeadTaints.put(ind, new HashSet<>());
            endToHeadTaints.get(ind).add(conParms);
            return;
        }

        HashSet<HashSet<Integer>> toDelete = new HashSet<>();
        boolean addFlag = true;
        for (HashSet<Integer> recordedConParams: endToHeadTaints.get(ind)){
            if (recordedConParams.containsAll(conParms) & recordedConParams.size() > conParms.size())
                toDelete.add(recordedConParams);
            else if (conParms.containsAll(recordedConParams))
                addFlag = false;
        }

        endToHeadTaints.get(ind).removeAll(toDelete);
        if (addFlag)
            endToHeadTaints.get(ind).add(conParms);
    }

    public boolean validFragmentCheck(){
        boolean isValid = true;
        if (head.getSubSignature().equals(end.getSubSignature())){
            if (RuleUtils.isEqMethod(end)){
                if (!FragmentsContainer.isSingleFixedEqualsMethod(head))
                    isValid=false;
            }
            else if (endInvokableMethods == null
                    || !isValidSuperAbstractOrInterfaceMethod(head, end)){
                isValid = false;
            }
        }
        if (!isValid){
            this.flag = false;
            return false;
        }

        return true;
    }

    public boolean equals(Object object){
        if (!(object instanceof Fragment))
            return false;

        Fragment fragment = (Fragment) object;
        return gadgets.equals(fragment.gadgets) & end.equals(fragment.end);
    }

    public void calPrioritySimply(){
        priority = linkedFragments.size() + gadgets.size();
    }

}
