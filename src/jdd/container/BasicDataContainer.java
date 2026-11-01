package container;

import tranModel.TransformableNode;
import cg.CG;
import lombok.extern.slf4j.Slf4j;
import config.SootConfig;
import dataflow.node.MethodDescriptor;
import gadgets.unit.Fragment;
import markers.Stage;
import rules.sinks.ClassLoaderCheckRule;
import soot.Scene;
import soot.SootClass;
import soot.SootField;
import soot.SootMethod;
import util.ClassRelationshipUtils;
import util.Utils;

import java.util.*;

/**
 * 存储一些全局可能要用到的基本信息
 */
@Slf4j
public class BasicDataContainer {
    public static CG cg = null;
    public static boolean openDebugMode = false;
    public static boolean needSerializable = true; // 判断是否开启序列化检查
    public static boolean openDynamicProxyDetect = false; // 判断是否开启动态代理检测
    public static boolean isEntryPolluteSelect;
    public static int stackLenLimitNum = 5;
    public static int polyLenLimit = 3;
    /** Seconds a single method's data-flow analysis may take before it is abandoned (TimeOutTask). */
    public static int methodAnalysisTimeout = 180;
    /** The same, for the analysis started from a head / source gadget. */
    public static int headAnalysisTimeout = 30;

    /** Methods whose analysis was cut short by its time budget, in the order the budget was hit. */
    public static final Set<String> analysisTimeouts =
            Collections.synchronizedSet(new LinkedHashSet<String>());

    // Methods and fields of the MozillaRhino1 / MozillaRhino2 chains, resolved once in init(). Each group is
    // all-or-nothing: in a program that does not contain them every field stays null, every rule keyed on them
    // returns the default above, and the analysis of other applications is unchanged.
    public static SootMethod rhinoErrToString, rhinoGetImpl, rhinoFunctionCall, rhinoCallableCall;
    public static SootMethod rhinoNjoGet, rhinoMapGet;
    public static SootMethod rhinoGetProperty, rhinoIdsoGet, rhinoNjmCall, rhinoWrapperUnwrap, rhinoNjoUnwrap;
    public static SootClass rhinoNjo, rhinoGetterSlot;
    public static SootField rhinoSoPrototype, rhinoSoParentScope, rhinoNjoPrototype, rhinoNjoParent;
    public static SootField rhinoSoLastAdded, rhinoGetterSlotGetter;
    /** methods on the call stack / in the fragment: NativeError.toString ... ScriptableObject.getImpl */
    private static final int RHINO_ERR_FRAGMENT_LEN = 7;
    public static int methodLimitNum = 5;
    public static int serializableInterceptLen = 3;
    public static boolean hashCollisionModeSelect = true; //  true: 不考虑 哈希碰撞的Case A类型 (容易产生误报)
    public static int linkTimeLimit = 3;
    public static int chainLimit = 20;
    public static int stackDeviationLimit = 3;
    public static int stackLenLimitForFieldsCollection = 2;
    public static boolean openChainedSinkCheck = false;
    public static int interimFragmentToConClassLimit = 3;
    public static boolean gadgetParamsGenerate = false;
    public static boolean infosCollect = false;

    public static boolean openJoinRule = false;

    public static boolean openAliasAnalysis = true;
    public static boolean openPointerToAnalysis = true;

    public static Stage stage = Stage.OFF;

    public static HashMap<String, HashSet<String>> subClassSearchRecord = new HashMap<>();
    public static HashMap<String, SootClass> commonClassMap = new HashMap<>();
    public static HashMap<String, SootMethod> commonMtdMap = new HashMap<>();
    public static List<String> blackList = SootConfig.getBlackList();

    // 方法的访问权限
    public static List<String> accessPermissions = Arrays.asList("public","protected","private");

    public static HashMap<SootMethod, MethodDescriptor> methodMapDescriptor = new HashMap<>();
    public static HashMap<Integer, TransformableNode> conditionTfNodesMap = new HashMap<>();
    public static int heuristicShortChainCutLen = 0;

    public static void reset(){
        BasicDataContainer.commonMtdMap = new HashMap<>();
        BasicDataContainer.commonClassMap = new HashMap<>();
        BasicDataContainer.subClassSearchRecord = new HashMap<>();

        resetState();

        RulesContainer.reset();
        FragmentsContainer.reset();
    }

    public static void init(){
        commonMtdMap.put("invokeHandler", Scene.v().getMethod("<java.lang.reflect.InvocationHandler: java.lang.Object invoke(java.lang.Object,java.lang.reflect.Method,java.lang.Object[])>"));
        commonClassMap.put("Map", Utils.toSootClass("java.util.Map"));
        commonClassMap.put("List", Utils.toSootClass("java.util.List"));
        commonClassMap.put("Entry", Utils.toSootClass("java.util.Map$Entry"));
        commonClassMap.put("Object", Utils.toSootClass("java.lang.Object"));
        BasicDataContainer.subClassSearchRecord.put("java.util.Map$Entry", ClassRelationshipUtils.getAllSubClasses(Collections.singletonList("java.util.Map$Entry")));
    }

    /**
     * Records that a method's analysis ran out of its time budget.
     * <p>
     * The budget is wall clock, so which methods get cut depends on how loaded the machine is: two runs over the
     * same program can cut different methods, and their results differ with them (a cut analysis leaves whatever
     * partial state it had). Writing the set next to the results lets a comparison of two runs check that both hit
     * the same budget, instead of silently comparing a complete run against a truncated one.
     */
    public static void recordAnalysisTimeout(SootMethod method) {
        if (method == null) return;
        String sig = method.getSignature();
        if (!analysisTimeouts.add(sig)) return;         // already recorded
        try {
            if (config.RegularConfig.outputDir == null) return;
            java.io.File file = new java.io.File(config.RegularConfig.outputDir, "analysisTimeouts.txt");
            if (file.getParentFile() != null) file.getParentFile().mkdirs();
            try (java.io.FileWriter writer = new java.io.FileWriter(file, true)) {
                writer.write(sig + System.lineSeparator());
            }
        } catch (Exception e) {
            log.warn("can not record the analysis timeout of " + sig + ": " + e.getMessage());
        }
    }

    private static SootMethod resolveMtd(String signature) {
        try {
            return Scene.v().containsMethod(signature) ? Scene.v().getMethod(signature) : null;
        } catch (Exception e) {
            return null;
        }
    }

    /**
     * Resolves the methods and fields of the two Rhino chains against the loaded program. Each group is set only if
     * all of its members are found, so a rule is either fully available or not at all.
     */
    public static void initRhinoChainInfos() {
        rhinoErrToString = resolveMtd("<org.mozilla.javascript.NativeError: java.lang.String toString()>");
        rhinoGetImpl = resolveMtd("<org.mozilla.javascript.ScriptableObject: java.lang.Object getImpl(java.lang.String,int,org.mozilla.javascript.Scriptable)>");
        rhinoFunctionCall = resolveMtd("<org.mozilla.javascript.Function: java.lang.Object call(org.mozilla.javascript.Context,org.mozilla.javascript.Scriptable,org.mozilla.javascript.Scriptable,java.lang.Object[])>");
        rhinoCallableCall = resolveMtd("<org.mozilla.javascript.Callable: java.lang.Object call(org.mozilla.javascript.Context,org.mozilla.javascript.Scriptable,org.mozilla.javascript.Scriptable,java.lang.Object[])>");
        boolean lenActive = rhinoErrToString != null && rhinoGetImpl != null && rhinoFunctionCall != null && rhinoCallableCall != null;
        if (!lenActive) rhinoErrToString = rhinoGetImpl = rhinoFunctionCall = rhinoCallableCall = null;
        log.info("rhinoChainInfos: fragment-length / link rules " + (lenActive ? "active" : "skip (not in the analysed program)"));

        rhinoNjo = null; rhinoSoPrototype = null; rhinoSoParentScope = null; rhinoNjoPrototype = null; rhinoNjoParent = null;
        try {
            SootClass so = Scene.v().getSootClassUnsafe("org.mozilla.javascript.ScriptableObject");
            SootClass njo = Scene.v().getSootClassUnsafe("org.mozilla.javascript.NativeJavaObject");
            if (so != null && njo != null) {
                SootField a = so.getFieldByNameUnsafe("prototypeObject"), b = so.getFieldByNameUnsafe("parentScopeObject");
                SootField c = njo.getFieldByNameUnsafe("prototype"), d = njo.getFieldByNameUnsafe("parent");
                if (a != null && b != null && c != null && d != null) {
                    rhinoNjo = njo; rhinoSoPrototype = a; rhinoSoParentScope = b; rhinoNjoPrototype = c; rhinoNjoParent = d;
                }
            }
        } catch (Exception e) {
            rhinoNjo = null;
        }
        log.info("rhinoChainInfos: source remap " + (rhinoNjo != null ? "active" : "skip (not in the analysed program)"));

        rhinoNjoGet = resolveMtd("<org.mozilla.javascript.NativeJavaObject: java.lang.Object get(java.lang.String,org.mozilla.javascript.Scriptable)>");
        rhinoMapGet = resolveMtd("<java.util.Map: java.lang.Object get(java.lang.Object)>");
        if (rhinoNjoGet == null || rhinoMapGet == null) rhinoNjoGet = rhinoMapGet = null;

        rhinoGetProperty = resolveMtd("<org.mozilla.javascript.ScriptableObject: java.lang.Object getProperty(org.mozilla.javascript.Scriptable,java.lang.String)>");
        rhinoIdsoGet = resolveMtd("<org.mozilla.javascript.IdScriptableObject: java.lang.Object get(java.lang.String,org.mozilla.javascript.Scriptable)>");
        rhinoNjmCall = resolveMtd("<org.mozilla.javascript.NativeJavaMethod: java.lang.Object call(org.mozilla.javascript.Context,org.mozilla.javascript.Scriptable,org.mozilla.javascript.Scriptable,java.lang.Object[])>");
        rhinoWrapperUnwrap = resolveMtd("<org.mozilla.javascript.Wrapper: java.lang.Object unwrap()>");
        rhinoNjoUnwrap = resolveMtd("<org.mozilla.javascript.NativeJavaObject: java.lang.Object unwrap()>");
        rhinoGetterSlot = Scene.v().getSootClassUnsafe("org.mozilla.javascript.ScriptableObject$GetterSlot");
        SootClass scriptableObject = Scene.v().getSootClassUnsafe("org.mozilla.javascript.ScriptableObject");
        rhinoSoLastAdded = scriptableObject == null ? null : scriptableObject.getFieldByNameUnsafe("lastAdded");
        rhinoGetterSlotGetter = rhinoGetterSlot == null ? null : rhinoGetterSlot.getFieldByNameUnsafe("getter");
        if (rhinoGetProperty == null || rhinoIdsoGet == null || rhinoNjmCall == null
                || rhinoWrapperUnwrap == null || rhinoNjoUnwrap == null
                || rhinoGetterSlot == null || rhinoSoLastAdded == null || rhinoGetterSlotGetter == null) {
            rhinoGetProperty = null; rhinoIdsoGet = null; rhinoNjmCall = null;
            rhinoWrapperUnwrap = null; rhinoNjoUnwrap = null;
            rhinoGetterSlot = null; rhinoSoLastAdded = null; rhinoGetterSlotGetter = null;
        }
    }

    /**
     * Call-stack depth up to which DataflowDetect.detectFragment follows calls, for the search from callStack's head.
     * The MozillaRhino1 chain needs one fragment of RHINO_ERR_FRAGMENT_LEN methods with head NativeError.toString;
     * every other head keeps stackLenLimitNum.
     */
    public static int stackLenLimitFor(LinkedList<SootMethod> callStack) {
        if (rhinoErrToString != null && !callStack.isEmpty() && callStack.getFirst() == rhinoErrToString)
            return Math.max(stackLenLimitNum, RHINO_ERR_FRAGMENT_LEN);
        return stackLenLimitNum;
    }

    /** Maximal number of methods of a polymorphic (free-state) fragment with this head, see stackLenLimitFor. */
    public static int polyLenLimitFor(SootMethod head) {
        if (rhinoErrToString != null && head == rhinoErrToString)
            return Math.max(polyLenLimit, RHINO_ERR_FRAGMENT_LEN);
        return polyLenLimit;
    }

    public static boolean inBlackList(SootMethod sootMethod){
        if (blackList.isEmpty())
            return false;
        String className = sootMethod.getDeclaringClass().getName();
        if (blackList.contains(className))
            return true;

        for (String black: blackList){
            if (className.startsWith(black))
                return true;
        }

        return false;
    }
    public static boolean inBlackList(SootClass sootClass){
        if (blackList.size() == 0)
            return false;
        String className = sootClass.getName();
        if (blackList.contains(className))
            return true;

        for (String black: blackList){
            if (className.startsWith(black))
                return true;
        }

        return false;
    }

    public static MethodDescriptor getOrCreateDescriptor(SootMethod sootMethod){
        if(methodMapDescriptor.containsKey(sootMethod)){
            return methodMapDescriptor.get(sootMethod);
        }else{
            MethodDescriptor methodDescriptor = new MethodDescriptor(sootMethod);
            methodDescriptor.isDynamicEntry = ClassRelationshipUtils.isDynamicMethod(sootMethod);
            methodMapDescriptor.put(sootMethod, methodDescriptor);
            return methodDescriptor;
        }
    }

    public static void resetMethodDescriptorState(){
        if(!methodMapDescriptor.isEmpty()) { methodMapDescriptor.clear(); }
        else { methodMapDescriptor = new HashMap<>(); }
    }

    public static void resetState(){
        resetMethodDescriptorState();
        ClassLoaderCheckRule.callStacksRecord.clear();
    }

    public static boolean isValidHeadOfObjectMethod(SootMethod sootMethod){
        if (!sootMethod.getDeclaringClass().getName().equals("java.lang.Object"))
            return false;

        if (sootMethod.getSubSignature().equals("java.lang.String toString()")
                | sootMethod.getSubSignature().equals("boolean equals(java.lang.Object)")
                | sootMethod.getSubSignature().equals("int hashCode()"))
            return true;

        return false;
    }
}
