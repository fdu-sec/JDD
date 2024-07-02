package gadgets.unit;

import container.BasicDataContainer;
import container.FragmentsContainer;
import soot.SootMethod;

import java.util.HashMap;
import java.util.HashSet;

public class ConnectRequire {
    public HashSet<SootMethod> preLinkableMethods = new HashSet<>(); // Fragment 跳转条件
    public HashSet<HashSet<Integer>> paramsTaitRequire = null; // 污点要求
    public HashSet<Integer> condSet = new HashSet<>();
    
    /** 其他链接条件 */
    // 目前考虑两种: 方法名限制 / 方法所属的类型限制
    public HashMap<String, HashSet<String>> dynamicProxyLinkCheck = new HashMap<>();
    

    // 记录反射拼接的fragment的拼接要求
    // static(1) getter(1)/Interface(2)/any(0) non-parameter(0默认)/String(1)
    public String reflectionCheck = "010";

    public ConnectRequire(HashSet<HashSet<Integer>> paramsTaitRequire, HashSet<SootMethod> preLinkableMethods){
        dynamicProxyLinkCheck.put("MethodNameBlackList", new HashSet<>());
        dynamicProxyLinkCheck.put("MethodNameWhiteList", new HashSet<>());
        dynamicProxyLinkCheck.put("DecClassBlackList", new HashSet<>());
        dynamicProxyLinkCheck.put("DecClassWhiteList", new HashSet<>());
        this.paramsTaitRequire = paramsTaitRequire;
        this.preLinkableMethods = preLinkableMethods;
    }

    public ConnectRequire(HashSet<SootMethod> preLinkableMethods){
        dynamicProxyLinkCheck.put("MethodNameBlackList", new HashSet<>());
        dynamicProxyLinkCheck.put("MethodNameWhiteList", new HashSet<>());
        dynamicProxyLinkCheck.put("DecClassBlackList", new HashSet<>());
        dynamicProxyLinkCheck.put("DecClassWhiteList", new HashSet<>());
        this.preLinkableMethods = preLinkableMethods;
    }
}
