package config;

public enum ConfigurationEnum {

    ACCESS_PATH_LIMIT("accessPath_limit"),
    INTERMEDIARY_QUANTITY("intermediary_quantity"),
    OUT_PUT_DIR_NAME("outPutDirName"),
    CONFIG_PATH("configPath"),
    WITH_ALL_JDK("withAllJdk"),
    OUTPUT_DIR("outputDir"),
    INPUT_PATH("inputPath"),
    STORE_IN_DATABASE("storeInDataBase"),
    PROTOCOL("protocol"),
    JSON_SOURCE_TYPE("jsonSourceType"),
    METHOD_LIMIT_NUM("methodLimitNum"),
    OPEN_DYNAMIC_PROXY("openDynamicProxy"),
    EXECUTION_TIME_LIMIT("executionTimeLimit"),
    RE_RUN_LIMIT_NUM("reRunLimitNum"),
    Heuristic_Short_Chain_Cut_Len("heuristicShortChainCutLen"),
    SERIALIZABLE_INTERCEPTLEN("serializableInterceptLen"),
    DERIVATION_TYPE("derivationType"),
    SINK_RULES("sinkRules"),
    PRIORITIZED_GADGET_CHAIN_LIMIT("prioritizedGadgetChainLimit"),
    LINK_MODE("linkMode"),
    TAINT_RULE_MODE("taintRuleMode"),
    INPUT_EXP_PATH("inputEXPInfosPath"),
    CHAIN_LIMIT("chainLimit"),
    FRAGMENT_LEN_LIMIT("fragmentLenLimit"),

    NEED_SERIALIZABLE("needSerializable");

    private String key = "";
    ConfigurationEnum(String key) { this.key = key; }

    @Override
    public String toString() {
        return key;
    }
}
