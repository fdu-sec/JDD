package config;

import container.BasicDataContainer;
import container.FieldsContainer;
import container.FragmentsContainer;
import container.RulesContainer;
import lombok.extern.slf4j.Slf4j;
import org.apache.commons.io.FileUtils;
import util.Utils;

import java.io.*;
import java.util.*;
import java.util.jar.JarEntry;
import java.util.jar.JarFile;

@Slf4j
public class ConfigUtil {

    private static Properties configProperties = new Properties();
    // 解压过程中不做处理的文件夹列表
    private static String[] unDecompressDirList = { "META-INF", "OSGI-INF" };
    private static String[] specialDirList = { "/lib/", "WEB-INF/classes/" };
    private static HashSet<String> runtimeSpecialDirList = new HashSet<>();
    private static int classNums = 0;

    // 用于初始化工作，包括目录创建、配置项加载和Soot初始化
    public static void init() throws FileNotFoundException {

        try{
            // 加载配置文件, 读取参数
            initConfig();
            SootConfig.setSoot(RegularConfig.inputPath);
        }catch (FileNotFoundException e){
            log.error("File Not Found: " + e.getMessage());
            e.printStackTrace();
        }catch (IOException e){
            e.printStackTrace();
        }

    }

    public static void initContainer() throws IOException {
        BasicDataContainer.init();
        RulesContainer.init();
        FragmentsContainer.init();
        FieldsContainer.init();
    }

    /**
     * 给定封装了该文件夹dir的File句柄，删除掉该文件夹下所有的空文件夹
     * @param dirFile
     */
    public static void deleteEmptyUnderDir(File dirFile) throws IOException {

        if(!dirFile.isDirectory()){ throw new IllegalArgumentException("Parameter dirFile should be DIRECTORY!"); }
        File[] filesUnderDir = dirFile.listFiles();
        // 长度为零就直接删除掉，因为已经确定是文件夹File
        // 因此不会出现为null的情况
        if(filesUnderDir.length == 0){ return; }
        // 如果长度不为零那就做递归处理
        for(File file : filesUnderDir){
            if(file.isDirectory()){ deleteEmptyUnderDir(file); }
        }
        // 递归返回后再次判断当前目录下的文件
        if(FileUtils.isEmptyDirectory(dirFile)){ FileUtils.deleteDirectory(dirFile);}

    }

    public static List<File> getAllJarFiles(String dir){

        List<File> files = new ArrayList<>();
        File dirFile = new File(dir);
        if(!dirFile.isDirectory()){
            throw new IllegalArgumentException(dir + " is not a directory!");
        }

        File[] tmpFiles = dirFile.listFiles();
        List<File> jarFiles = new ArrayList<>();
        List<File> dirFiles = new ArrayList<>();
        // 获取当前目录下的jar文件
        for(File file : tmpFiles){
            // 对于目录作暂存处理
            if(file.isDirectory()){
                dirFiles.add(file);
                continue;
            }
            String fileName = file.getName();
            if(!fileName.endsWith("jar") && !fileName.endsWith(".war")){ continue; }
            jarFiles.add(file);
        }
        files.addAll(jarFiles);
        // 获取当前目录下的子目录中的jar文件
        for(File dFile : dirFiles){
            List<File> tmpJarFiles = getAllJarFiles(dFile.getAbsolutePath());
            files.addAll(tmpJarFiles);
        }
        return files;
    }


    /**
     * 解压制定目录dir下的所有jar包到outPutDir/tmp/目录下
     * @param dir 格式为/path/to/lib/dir/
     */
    public static void decompressJarFromDir(String dir) throws IOException {

        // 解压dir的所有jar文件到dir/tmp/目录下
        try{
            // 创建临时文件夹
            String tmpDir = "tmp/";
            File tmpDirFile = new File(dir + tmpDir);
            if(tmpDirFile.exists()){
                log.info("有遗留的历史tmp文件夹，使用该tmp文件夹作为分析输入的class path。如果有新的项目要分析请删除该文件夹");
                return;
            }
            tmpDirFile.mkdirs();
            // 获取目录下所有的Jar文件
            List<File> jarFiles = getAllJarFiles(dir);
            for(File jarFile : jarFiles){
                // 进行解压
                JarFile jar = new JarFile(jarFile);
                decompressJar(jar, dir + tmpDir);
            }
            log.info("共解压" + classNums + "个类");
            // 对一些特殊目录做处理，比如WEB-INF/classes，移动到tmp目录下，使得这个文件夹下的类的class path正确
            for(String specialDir : runtimeSpecialDirList){
                File srcDir = new File(specialDir);
                if(FileUtils.isDirectory(srcDir)){
                    File[] filesUnderSpecialDir = srcDir.listFiles();
                    for(File file : filesUnderSpecialDir){
                        String name = file.getName();
                        if(file.isDirectory()){
                            FileUtils.copyDirectoryToDirectory(file, new File(dir + tmpDir));
                            FileUtils.deleteDirectory(file);
                        }else{
                            FileUtils.copyFile(file, new File(dir  + tmpDir + name));
                            FileUtils.delete(file);
                        }
                    }
                }
            }
            // 删除掉解压出的空文件夹
            deleteEmptyUnderDir(tmpDirFile);
        }catch (IOException e){
            e.printStackTrace();
        }
    }

    /**
     *  解压单个jar包的功能函数
     *  @param jarFile 被JarFile对象封装的Jar包
     *  @param outputDir 解压的目录
     */
    public static void decompressJar(JarFile jarFile, String outputDir) throws IOException {

        if(jarFile == null || outputDir == null) {
            throw new IllegalArgumentException("Method parameters should not be null!");
        }
        if(outputDir.equals("")) {
            throw new IllegalArgumentException("Parameter outputDir should not be empty!");
        }

        // 获取jarFile中的每个文件并提取到outputDir下
        Enumeration<JarEntry> entries = jarFile.entries();
        List<String> newJarWarPaths = new ArrayList<>();
        while(entries.hasMoreElements()){

            JarEntry entry = entries.nextElement();
            String entryName = entry.getName();
            String path = outputDir + entryName;
            File newFile = new File(path);
            // 不处理{ META-INF, OSGI-INF }文件夹下的内容
            boolean flag = false;
            for (String ignoreDirName : unDecompressDirList) {
                if(entryName.contains(ignoreDirName)){
                    flag = true;
                    break;
                }
            }
            if(flag){ continue; }
            // 如果是一些包含类的特殊文件夹，那么就记录下来
            for(String specialDir : specialDirList){
                if(path.endsWith(specialDir)){
                    runtimeSpecialDirList.add(path);
                }
            }
            // 如果这个entry是一个文件夹且不存在，那么就新建它
            if(entry.isDirectory()){
                if(!newFile.exists()) { newFile.mkdirs(); }
                continue;
            }
            // 如果是一个文件，那就判断它所处文件夹在不在。而后做解压处理
            // 如果是一个jar/war文件，那么就将其就地解压并记录下等待下一轮的处理
            boolean isJar = false;
            if(entryName.endsWith(".jar") || entryName.endsWith(".war")){
                isJar = true;
                String[] splitedEntryName = entryName.split("/");
                String jarWarFileName = splitedEntryName[splitedEntryName.length - 1];
                path = outputDir + jarWarFileName;
                newJarWarPaths.add(path);
                newFile = new File(path);
            }
            // 如果不是一个class文件，那么没有必要解压它
            if(!entryName.endsWith(".class") && !isJar ) { continue; }
            File newFileParent = newFile.getParentFile();
            if(!newFileParent.exists()) { newFileParent.mkdirs(); }
            InputStream inputStream = jarFile.getInputStream(entry);
            OutputStream outputStream = new BufferedOutputStream(new FileOutputStream(newFile));
            // 解压处理
            byte[] buffer = new byte[2048];
            int bytesNum = 0;
            while((bytesNum = inputStream.read(buffer)) > 0){ outputStream.write(buffer, 0, bytesNum); }
            outputStream.flush();
            outputStream.close();
            inputStream.close();
            classNums++;
        }
        // 处理当前fat jar中被新解压出来的jar/war包
        for(String newJarWarPath : newJarWarPaths){
            JarFile newJarFile = new JarFile(newJarWarPath);
            decompressJar(newJarFile, outputDir);
            // 删除掉这些中间jar包
            FileUtils.delete(new File(newJarWarPath));
        }
    }



    // 判断是否是类Unix系统
    public static  boolean isOnServer(){
        return !System.getProperty("os.name").contains("Windows") & !System.getProperty("os.name").contains("Mac OS X");
    }
    private static String getWorkDir(){ return System.getProperty("user.dir") + "/"; }
    // 判断是否是绝对路径
    private static boolean isAbsolute(String path){
        if(isOnServer()){ return path.startsWith("/"); }
        return path.indexOf(":") > 0 | path.startsWith("/");
    }

    public static void initConfig() throws IOException {
        // 加载配置项并设置jdk依赖类型
        ConfigUtil.loadConfig("config/config.properties");
        RegularConfig.sootClassPath = ConfigUtil.getJdkDependencies(RegularConfig.withAllJdk);

        log.info("[ detect project :" + RegularConfig.inputPath + " ]");
        // 解压inputClassPath下所有的jar/war包
        log.info("解压目录" + RegularConfig.inputPath + "的类信息");
        ConfigUtil.decompressJarFromDir(RegularConfig.inputPath);
        RegularConfig.inputPath = RegularConfig.inputPath + "tmp/";
        log.info("解压完成");
    }

    private static String getPathProperty(String pathKey){

        // 获取当前的程序的运行目录
        String workDir = getWorkDir();
        // 判断是对path进行的配置
        String tmpValue = configProperties.getProperty(pathKey);
        if(Objects.equals(tmpValue, "") || Objects.equals(tmpValue, null)) {
            throw new IllegalArgumentException("Config property " + pathKey + " not found");
        }
        return isAbsolute(tmpValue) ?
                tmpValue :
                workDir + tmpValue;
    }

    /**
     * 用于获取运行程序机子上的jdk依赖，我们默认只使用{ lib/jce.jar, lib/rt.jar, lib/ext/nashron.jar }这几个
     * @param withAllJdk
     * @return jdkDependencies，是一个String。即用File.pathSeparator分隔的依赖的classpath
     */
    public static String getJdkDependencies(String withAllJdk){
        String javaHome = System.getProperty("java.home");
//        String javaHome = "/Library/Java/JavaVirtualMachines/jdk1.7.0_21.jdk/Contents/Home/jre";
        String[] jre;

        if("true".equals(withAllJdk)){
            jre = new String[]{"../lib/dt.jar","../lib/sa-jdi.jar","../lib/tools.jar",
                    "../lib/jconsole.jar","lib/resources.jar","lib/rt.jar","lib/jsse.jar",
                    "lib/jce.jar","lib/charsets.jar","lib/ext/cldrdata.jar","lib/ext/dnsns.jar",
                    "lib/ext/jaccess.jar","lib/ext/localedata.jar","lib/ext/nashorn.jar",
                    "lib/ext/sunec.jar","lib/ext/sunjce_provider.jar","lib/ext/sunpkcs11.jar",
                    "lib/ext/zipfs.jar","lib/management-agent.jar"};
        }else{
            jre = new String[]{"lib/rt.jar","lib/jce.jar", "lib/ext/nashron.jar"};
        }

        StringBuilder tmpJdkDependencies = new StringBuilder();
        for(String cp:jre){
            String path = String.join(File.separator, javaHome, cp);
            File file = new File(path);
            if(file.exists()){
                tmpJdkDependencies.append(path);
                tmpJdkDependencies.append(File.pathSeparator);
            }
        }
        tmpJdkDependencies.deleteCharAt(tmpJdkDependencies.length()-1);

        return tmpJdkDependencies.toString();
    }


    /**
     * 用于从特定的文件路径中获得配置项，默认为config/config.properties
     * @param filePath
     */
    public static void loadConfig(String filePath){
        try{

            if (isOnServer()){
                filePath = "/home/cbf/dvd-evaluation/evaluation/config/config.properties";
            }
            log.info("filePath = "+filePath);
            Reader configReader = new FileReader(filePath);
            configProperties.load(configReader);

            // 加载配置项
            RegularConfig.outputDir = getPathProperty(ConfigurationEnum.OUTPUT_DIR.toString());
            RegularConfig.inputPath = getPathProperty(ConfigurationEnum.INPUT_PATH.toString());
            RegularConfig.configPath = getPathProperty(ConfigurationEnum.CONFIG_PATH.toString());
            RegularConfig.outPutDirName = configProperties.getProperty(ConfigurationEnum.OUT_PUT_DIR_NAME.toString(), "infos");
            RegularConfig.accessPath_limit =
                    Integer.parseInt(configProperties.getProperty(ConfigurationEnum.ACCESS_PATH_LIMIT.toString(), "3"));
            RegularConfig.withAllJdk =
                    configProperties.getProperty(ConfigurationEnum.WITH_ALL_JDK.toString(), "false");
            RegularConfig.intermediary_quantity =
                    Integer.parseInt(configProperties.getProperty(ConfigurationEnum.INTERMEDIARY_QUANTITY.toString(),"2"));
            RegularConfig.protocol = configProperties.getProperty(ConfigurationEnum.PROTOCOL.toString(), "jdk");
            BasicDataContainer.methodLimitNum = Integer.parseInt(configProperties.getProperty(ConfigurationEnum.METHOD_LIMIT_NUM.toString(), "5"));
            RegularConfig.jsonSourceTypes = (HashSet<String>) Utils.toSet(configProperties.getProperty(ConfigurationEnum.JSON_SOURCE_TYPE.toString(), "getter"));
            RegularConfig.storeInDataBase =
                    configProperties.getProperty(ConfigurationEnum.STORE_IN_DATABASE.toString(), "true");
            RegularConfig.prioritizedGadgetChainLimit = Integer.parseInt(configProperties.getProperty(ConfigurationEnum.PRIORITIZED_GADGET_CHAIN_LIMIT.toString(), "-1"));
            RegularConfig.inputEXPInfosPath = getPathProperty(ConfigurationEnum.INPUT_EXP_PATH.toString());
            BasicDataContainer.stackLenLimitNum = Integer.parseInt(configProperties.getProperty(ConfigurationEnum.CHAIN_LIMIT.toString(), "20"));
            BasicDataContainer.stackLenLimitNum = Integer.parseInt(configProperties.getProperty(ConfigurationEnum.FRAGMENT_LEN_LIMIT.toString(), "6"));
            RegularConfig.needSerializable = configProperties.getProperty(ConfigurationEnum.NEED_SERIALIZABLE.toString(), "true").equals("true");
            BasicDataContainer.needSerializable = RegularConfig.needSerializable;
            RegularConfig.linkMode = configProperties.getProperty(ConfigurationEnum.LINK_MODE.toString(), "strict").equals("strict")? "strict":"loose";
            RegularConfig.derivationType = configProperties.getProperty(ConfigurationEnum.DERIVATION_TYPE.toString(),"all");
            RegularConfig.taintRuleMode = configProperties.getProperty(ConfigurationEnum.TAINT_RULE_MODE.toString(), "strict");
            RegularConfig.sinkRules = (HashSet<String>) Utils.toSet(configProperties.getProperty(ConfigurationEnum.SINK_RULES.toString()));
            BasicDataContainer.openDynamicProxyDetect = configProperties.getProperty(ConfigurationEnum.OPEN_DYNAMIC_PROXY.toString(), "false").equals("true");
            RegularConfig.executionTimeLimit = Integer.parseInt(configProperties.getProperty(ConfigurationEnum.EXECUTION_TIME_LIMIT.toString(), "60"));
            RegularConfig.reRunLimitNum = Integer.parseInt(configProperties.getProperty(ConfigurationEnum.RE_RUN_LIMIT_NUM.toString(), "1"));
            BasicDataContainer.heuristicShortChainCutLen = Integer.parseInt(configProperties.getProperty(ConfigurationEnum.Heuristic_Short_Chain_Cut_Len.toString(), "0"));
            BasicDataContainer.serializableInterceptLen = Integer.parseInt(configProperties.getProperty(ConfigurationEnum.SERIALIZABLE_INTERCEPTLEN.toString(), "2"));

        }catch (IOException e){
            throw new IllegalArgumentException("config file not found!");
        }
    }
}
