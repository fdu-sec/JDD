package config;


import java.util.HashSet;
import java.util.Set;

public class RegularConfig {

    // 配置文件指定
    public static String inputPath;
    public static String outPutDirName;
    public static String outputDir;
    public static String withAllJdk;
    public static String configPath;
    public static int accessPath_limit;
    public static int executionTimeLimit = 60;
    public static int reRunLimitNum = 1;
    // 协议选取
    public static String protocol;
    public static String linkMode;
    // 是否存入mysql
    public static String storeInDataBase;

    public static int intermediary_quantity;

    public static String sootClassPath;
    public static String inputEXPInfosPath;
    public static boolean needSerializable;
    public static String taintRuleMode;
    public static Integer prioritizedGadgetChainLimit;
    public static String derivationType;
    public static HashSet<String> sinkRules = new HashSet<>();
    public static HashSet<String> jsonSourceTypes;
}
