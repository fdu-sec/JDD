package tranModel;

import dataflow.node.MethodDescriptor;

public interface Rule {
    void apply(Transformable transformable, MethodDescriptor methodDescriptor);
}
