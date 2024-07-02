package gadgets.collection.iocd.unit;

import util.Pair;
import lombok.Getter;
import lombok.Setter;

import java.util.LinkedHashMap;

@Getter
@Setter
public class ConditionRecord {

    public MethodRecord methodBelongTo;
    public LinkedHashMap<String, FieldRecord> conditionName = new LinkedHashMap<>();    //  可控对象？
    public LinkedHashMap<String, String> conditionValue = new LinkedHashMap<>();   //  值
    public String comparator;
    public String ifStmt;
    public boolean basic = false;
    public int hashCode;
    public Pair<String, Integer> usedSite; // 被使用的位置信息记录
    public int type = SINGLE;


    public static int SINGLE = 0; // = and
    public static int OR = 1;
    public static int UNCONTROLLABLE =2;
}
