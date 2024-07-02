package dataflow;

import soot.ValueBox;
import java.util.Objects;
import cfg.Node;
public class Event {

    public Node node;
    public ValueBox valueBox;

    public Event(Node node, ValueBox valueBox){
        this.node=node;
        this.valueBox=valueBox;
    }

    public boolean equals(Event event){
        return this.node==event.node&&this.valueBox==event.valueBox;
    }

    @Override
    public boolean equals(Object obj) {
        if(!(obj instanceof Event))
            return false;
        Event event=(Event) obj;
        return equals(event);
    }

    @Override
    public int hashCode() {
        return Objects.hash(node,valueBox);
    }
}
