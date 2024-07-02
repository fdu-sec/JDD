package common;

import java.io.File;

public class Constants {

    public static String apkPath=System.getProperty("user.dir")+ File.separator+"app"+File.separator+"auto.apk";
    public static String androidJar = System.getenv("ANDROID_HOME") + File.separator + "platforms";
    public static String outputDir = System.getProperty("user.dir") + File.separator + "sootOutput";

//    public static String apkPath="app"+File.separator+"auto.apk";
//    public static String androidJar = "AndroidHome";
//    public static String outputDir = System.getProperty("user.dir") + File.separator + "sootOutput";

    public static String regex = "(<(java|android)\\.util\\..*(boolean|void) add.*>)|" +
            "(<(java|android)\\.util\\..*(java.lang.Object|void) put.*>)|" +
            "(<android\\.util\\.Sparse.*void (append|put).*>)";


}
