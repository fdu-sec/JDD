package gadgets.collection.iocd.unit.instrument;

import lombok.Getter;
import lombok.Setter;

import java.util.HashSet;

@Getter
@Setter
public class SinkInstRecord {
    public MethodInstRecord methodInstRecord; // 记录sink点方法
    public HashSet<Integer> pollutedParams = new HashSet<>();   //  应该被污染的参数，用于动态检测这些参数是否被污染
    public boolean flag = true;
}
