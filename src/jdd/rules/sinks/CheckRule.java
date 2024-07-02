package rules.sinks;

import tranModel.Transformable;
import tranModel.TransformableNode;
import dataflow.node.MethodDescriptor;
import soot.SootMethod;

import java.io.IOException;
import java.util.LinkedList;

/**
 * Gadget Sink检测规则的接口
 */
public interface CheckRule {
    void apply(MethodDescriptor descriptor,
               LinkedList<SootMethod> callStack,
               Transformable transformable) throws IOException;

    boolean checkRisky(MethodDescriptor descriptor, TransformableNode tfNode);

    boolean isSinkMethod(SootMethod mtd);
}
