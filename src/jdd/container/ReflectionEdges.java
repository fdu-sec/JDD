package container;

import config.RegularConfig;
import lombok.extern.slf4j.Slf4j;
import org.apache.commons.io.FileUtils;
import soot.Scene;
import soot.SootMethod;
import soot.Unit;
import soot.Value;
import soot.jimple.AssignStmt;
import soot.jimple.InstanceInvokeExpr;
import soot.jimple.InvokeExpr;
import soot.jimple.StaticFieldRef;
import tranModel.TransformableNode;

import java.io.File;
import java.io.IOException;
import java.nio.charset.StandardCharsets;
import java.util.*;

/**
 * Supplementary call edges for reflective calls that Soot's call graph cannot see.
 *
 * Soot has no edge for  adapter.invoke(null, new Object[]{...})  when  adapter  is a java.lang.reflect.Method read from
 * a static field that a static initializer filled with  Class.forName("C").getMethod("m", ...).  This class lets the
 * analysis know such edges from a plain-text table (<configPath>/reflectionEdges), one edge per line:
 *
 *     <declaring.Class: java.lang.reflect.Method staticMethodField> -> <target.Class: ReturnType method(ParamTypes)>
 *
 * An edge applies to a call site  m.invoke(obj, args)  whose receiver  m  is assigned from that static field in the
 * same method. Nothing else is affected: with no table, or with entries whose field/method are not in the analysed
 * program, every query below answers "no edge" and JDD behaves exactly as before.
 *
 * At such a call site the callee set is exactly the edge target(s) (Method.invoke itself is not entered), the callee's
 * parameters take the taint of the packed argument array (conservatively: array tainted => every parameter tainted),
 * and only the return value is mapped back to the caller.
 */
@Slf4j
public class ReflectionEdges {
    private static final String METHOD_INVOKE_SIG =
            "<java.lang.reflect.Method: java.lang.Object invoke(java.lang.Object,java.lang.Object[])>";

    /** raw "field -> method" signature pairs read from the table */
    private static final List<String[]> rawEdges = new ArrayList<>();
    /** resolved: static Method field signature -> target methods; only entries present in the Scene */
    private static final HashMap<String, LinkedHashSet<SootMethod>> edges = new HashMap<>();

    /** (Re)load the table and resolve it against the loaded program. Must run after the classes are loaded. */
    public static void init() {
        rawEdges.clear();
        edges.clear();
        if (RegularConfig.configPath == null) return;
        File file = new File(RegularConfig.configPath + File.separator + "reflectionEdges");
        if (!file.isFile()) return; // no table: feature off

        try {
            for (String line : FileUtils.readLines(file, StandardCharsets.UTF_8)) {
                line = line.trim();
                if (line.isEmpty() || line.startsWith("#")) continue;
                String[] parts = line.split("\\s+->\\s+");
                if (parts.length != 2) {
                    log.warn("reflectionEdges: ignore malformed line: " + line);
                    continue;
                }
                rawEdges.add(new String[]{parts[0].trim(), parts[1].trim()});
            }
        } catch (IOException e) {
            log.warn("reflectionEdges: cannot read " + file + ": " + e.getMessage());
            return;
        }
        resolve();
    }

    private static void resolve() {
        for (String[] raw : rawEdges) {
            try {
                if (!Scene.v().containsField(raw[0]) || !Scene.v().containsMethod(raw[1])) {
                    log.info("reflectionEdges: skip (not in the analysed program): " + raw[0] + " -> " + raw[1]);
                    continue;
                }
                SootMethod target = Scene.v().getMethod(raw[1]);
                if (!target.isConcrete()) continue;
                edges.computeIfAbsent(raw[0], k -> new LinkedHashSet<>()).add(target);
                log.info("reflectionEdges: active: " + raw[0] + " -> " + raw[1]);
            } catch (Exception e) {
                log.warn("reflectionEdges: cannot resolve " + raw[0] + " -> " + raw[1] + ": " + e.getMessage());
            }
        }
    }

    public static boolean isEmpty() {
        return edges.isEmpty();
    }

    /** All edge targets: they are added to the call-graph entry points so Soot builds edges for their bodies. */
    public static LinkedHashSet<SootMethod> allTargets() {
        LinkedHashSet<SootMethod> ret = new LinkedHashSet<>();
        for (LinkedHashSet<SootMethod> targets : edges.values()) ret.addAll(targets);
        return ret;
    }

    /** The table key (static field signature) of the reflective call site, or null if tfNode is not one. */
    private static String edgeKey(TransformableNode tfNode) {
        if (edges.isEmpty() || tfNode == null || !tfNode.containsInvoke()) return null;
        InvokeExpr invokeExpr = tfNode.getUnitInvokeExpr();
        if (!(invokeExpr instanceof InstanceInvokeExpr) || invokeExpr.getArgCount() != 2) return null;
        if (!METHOD_INVOKE_SIG.equals(invokeExpr.getMethod().getSignature())) return null;

        SootMethod owner = tfNode.method;
        if (owner == null || !owner.hasActiveBody()) return null;
        // locals are matched by name: the CFG may work on a copy of the body, names are unique within a body
        String receiver = ((InstanceInvokeExpr) invokeExpr).getBase().toString();
        for (Unit unit : owner.getActiveBody().getUnits()) {
            if (!(unit instanceof AssignStmt)) continue;
            AssignStmt assign = (AssignStmt) unit;
            if (!(assign.getRightOp() instanceof StaticFieldRef)) continue;
            if (!assign.getLeftOp().toString().equals(receiver)) continue;
            String key = ((StaticFieldRef) assign.getRightOp()).getFieldRef().getSignature();
            if (edges.containsKey(key)) return key;
        }
        return null;
    }

    public static boolean isEdgeCallSite(TransformableNode tfNode) {
        return edgeKey(tfNode) != null;
    }

    /** A fresh set of the edge targets of the call site (empty if it is not an edge call site). */
    public static HashSet<SootMethod> targetsOf(TransformableNode tfNode) {
        String key = edgeKey(tfNode);
        return key == null ? new HashSet<>() : new HashSet<>(edges.get(key));
    }

    /** Whether the packed argument array (or the target object) of the call site is tainted. */
    public static boolean argsTainted(TransformableNode tfNode, dataflow.node.MethodDescriptor descriptor) {
        InvokeExpr invokeExpr = tfNode.getUnitInvokeExpr();
        for (Value arg : invokeExpr.getArgs()) {
            if (util.Utils.isTainted(arg, descriptor.taints)) return true;
        }
        return false;
    }
}
