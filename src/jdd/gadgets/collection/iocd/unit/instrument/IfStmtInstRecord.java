package gadgets.collection.iocd.unit.instrument;

import lombok.Getter;
import lombok.Setter;

import java.util.HashSet;

@Setter
@Getter
public class IfStmtInstRecord {
    public String className;    //  该条件分支所属的类名
    public String methodSubSig; // 该条件分支所属方法sub签名
    public String methodName;
    public Integer lineNumber;  // 在源代码文件中的位置
    public boolean basic = false;       // 是否为 Basic Condition
    public Integer hashCode;    // 用来标记对应哪个 ConditionRecord
    public HashSet<Integer> successor; // 该条件分支的后继
    public Integer basicSuccessor; // 如果是 Basic Condition，会记录后续应该进入的后继语句位置
//    public HashSet<Integer> precursor; // 该条件分支的前继

}
