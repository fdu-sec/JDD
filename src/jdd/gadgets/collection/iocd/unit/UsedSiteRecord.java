package gadgets.collection.iocd.unit;

import java.util.HashMap;
import java.util.HashSet;

public class UsedSiteRecord {
    public String inClassName;  // 在哪个class文件被用到
    public Integer site;        // 在哪行

    public HashSet<FieldRecord> usedFields = new HashSet<>();
}
