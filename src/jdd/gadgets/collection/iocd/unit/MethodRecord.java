package gadgets.collection.iocd.unit;

import lombok.Getter;
import lombok.Setter;

@Getter
@Setter
public class MethodRecord {

    public String classBelongTo;
    public String methodName;
    public String sig;

    public boolean equals(Object object){
        if (!(object instanceof MethodRecord))
            return false;

        MethodRecord methodRecord = (MethodRecord) object;
        return classBelongTo.equals(methodRecord.classBelongTo)
                & methodName.equals(methodRecord.methodName)
                & sig.equals(methodRecord.sig);
    }
}
