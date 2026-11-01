package container;

import config.RegularConfig;
import lombok.extern.slf4j.Slf4j;
import org.apache.commons.io.FileUtils;
import soot.Scene;
import soot.SootMethod;
import soot.jimple.InvokeExpr;
import soot.jimple.SpecialInvokeExpr;
import tranModel.TransformableNode;
import util.ClassRelationshipUtils;

import java.io.File;
import java.io.IOException;
import java.nio.charset.StandardCharsets;
import java.util.HashSet;

/**
 * Super calls that are followed with their static (invokespecial) target.
 *
 * <configPath>/superCalls lists override methods m (one method signature per line) whose body calls  super.m(...).
 * By default such a call is resolved from the receiver's class, which finds the override itself (or all overrides of
 * an abstract receiver class), and the fragment de-duplication then drops it, so the analysis never enters the super
 * method. For a listed override:
 * - the method named in the invokespecial instruction is added to the candidates of  super.m(...); the candidates
 *   resolved as before (receiver-class resolution, the methods the call graph mixes in such as <clinit>) are all kept,
 *   and the de-duplication decides about them as before, so the candidate set only grows;
 * - that statically bound target is not dropped by the fragment de-duplication (a super call only climbs the class
 *   hierarchy, so it cannot form a cycle; real recursion is still stopped by the call-stack check).
 *
 * The same applies to a listed method's calls of private methods of its own class ( this.p(...) , also invokespecial):
 * they are resolved from the receiver's pointer type as well, and for an abstract subclass as receiver type nothing is
 * found (only the subclasses are searched, not the class declaring p). For those the static target is added the same way.
 *
 * Constructors, static initializers and invokespecial calls in unlisted methods are unchanged. With no table, or entries
 * that are not in the analysed program, nothing changes at all.
 */
@Slf4j
public class SuperCallSites {
    /** signatures of the listed override methods that are in the analysed program */
    private static final HashSet<String> callers = new HashSet<>();

    /** (Re)load the table and resolve it against the loaded program. Must run after the classes are loaded. */
    public static void init() {
        callers.clear();
        if (RegularConfig.configPath == null) return;
        File file = new File(RegularConfig.configPath + File.separator + "superCalls");
        if (!file.isFile()) return; // no table: feature off

        try {
            for (String line : FileUtils.readLines(file, StandardCharsets.UTF_8)) {
                line = line.trim();
                if (line.isEmpty() || line.startsWith("#")) continue;
                try {
                    if (Scene.v().containsMethod(line)) {
                        callers.add(Scene.v().getMethod(line).getSignature());
                        log.info("superCalls: active: " + line);
                    } else {
                        log.info("superCalls: skip (not in the analysed program): " + line);
                    }
                } catch (Exception e) {
                    log.warn("superCalls: cannot resolve " + line + ": " + e.getMessage());
                }
            }
        } catch (IOException e) {
            log.warn("superCalls: cannot read " + file + ": " + e.getMessage());
        }
    }

    public static boolean isEmpty() {
        return callers.isEmpty();
    }

    /** Whether tfNode is  super.m(...)  inside a listed override of m, or a call of a private method of the listed method's class. */
    public static boolean isSuperCall(TransformableNode tfNode) {
        if (callers.isEmpty() || tfNode == null || !tfNode.containsInvoke()) return false;
        InvokeExpr invokeExpr = tfNode.getUnitInvokeExpr();
        if (!(invokeExpr instanceof SpecialInvokeExpr)) return false;
        SootMethod caller = tfNode.method;
        if (caller == null || !callers.contains(caller.getSignature())) return false;

        return isSameObjectEdge(caller, invokeExpr.getMethod());
    }

    /**
     * Whether callee is reached from the listed method caller by a statically bound call on the same object:
     * super.m(...) (same sub-signature, in a super class) or this.p(...) for a private method p of caller's own class.
     * The callee runs on the same object as the caller, so it belongs to the caller's class node in an IOCD.
     */
    public static boolean isSameObjectEdge(SootMethod caller, SootMethod callee) {
        if (callers.isEmpty() || caller == null || callee == null || !callers.contains(caller.getSignature())) return false;
        if (callee.getName().equals("<init>") || callee.getName().equals("<clinit>")) return false;
        if (callee.equals(caller)) return false;
        // this.p(...) for a private method p of the listed method's own class (statically bound as well)
        if (callee.isPrivate() && callee.getDeclaringClass().equals(caller.getDeclaringClass())) return true;
        return callee.getSubSignature().equals(caller.getSubSignature())
                && ClassRelationshipUtils.isSubClassOf(caller.getDeclaringClass(), callee.getDeclaringClass());
    }

    /** Whether invokedMethod is the statically bound target of such a super call (not one of the methods kept with it). */
    public static boolean isSuperCallTarget(TransformableNode tfNode, SootMethod invokedMethod) {
        return isSuperCall(tfNode) && invokedMethod != null && invokedMethod.equals(tfNode.getUnitInvokeExpr().getMethod());
    }
}
