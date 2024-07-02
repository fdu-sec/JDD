package gadgets.collection.rule;

import tranModel.Transformable;
import dataflow.node.MethodDescriptor;
import gadgets.collection.node.GadgetInfoRecord;

import java.io.IOException;

public interface InferRule {
    void apply(MethodDescriptor descriptor,
               GadgetInfoRecord gadgetInfosRecord,
               Transformable transformable) throws IOException;
}
