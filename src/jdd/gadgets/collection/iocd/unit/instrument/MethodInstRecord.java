package gadgets.collection.iocd.unit.instrument;

import lombok.Getter;
import lombok.Setter;

@Getter
@Setter
public class MethodInstRecord {
    public int hashCode;
    public String className;
    public String subSig;
    public String sig;
    public String name;
}
