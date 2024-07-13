package config;

import cg.CG;
import container.BasicDataContainer;
import container.FragmentsContainer;
import lombok.extern.slf4j.Slf4j;
import org.apache.commons.io.FileUtils;
import soot.*;
import soot.options.Options;
import soot.util.Chain;
import util.TimeOutTask;

import java.io.File;
import java.io.FileNotFoundException;
import java.io.IOException;
import java.nio.charset.StandardCharsets;
import java.util.*;

@Slf4j
public class SootConfig {
    public static List<String> ignoreInfo = getIgnoreInfo();
    // 此处将同一个包下无法分析的类合并的阈值设置为10，比如a.b.c.D1-D11会被合并为a.b.c
    public static int loadClassCounter = 0, maxPackageRecordTime = 10;
    public static HashMap<String, Integer> packageRecordTime = new HashMap<>();

    public static void setSoot(String inputClassPath) throws FileNotFoundException {

        G.reset();
        Scene.v().releaseCallGraph();
        Scene.v().releasePointsToAnalysis();
        Scene.v().releaseActiveHierarchy();
        Scene.v().releaseReachableMethods();
        Scene.v().releaseFastHierarchy();
        Scene.v().releaseSideEffectAnalysis();
        Scene.v().releaseClientAccessibilityOracle();
        //remove odd Application Class
        SootConfig.removeAllAppClz();

        Options.v().set_src_prec(Options.src_prec_class);
        Options.v().set_process_dir(Collections.singletonList(((inputClassPath))));
        Options.v().set_allow_phantom_refs(true);
        Options.v().set_whole_program(true);
        Options.v().set_prepend_classpath(true);
        Options.v().set_keep_line_number(true);
        Options.v().set_output_format(Options.output_format_jimple);
//        Options.v().set_output_dir(RegularConfig.outputDir+"/JimpleOutput/framework1");
        Options.v().set_drop_bodies_after_load(false);
        // Options.v().set_no_bodies_for_excluded(true);
        Options.v().setPhaseOption("cg", "all-reachable:true");
        Scene.v().setSootClassPath(Scene.v().getSootClassPath() + File.pathSeparator + RegularConfig.sootClassPath);
        Scene.v().loadDynamicClasses();
        loadTargetClass();
    }


    public static void constructCG(){
        List<SootMethod> tmpMethods = new ArrayList<>(FragmentsContainer.sources);
        BasicDataContainer.cg = new CG(tmpMethods);
    }

    // 去除所有的实现类
    public static void removeAllAppClz() {
        log.info("清除当前所有的Application Class");
        //获取Scene对象
        Scene scene = Scene.v();
        //获取所有的应用类
        Chain<SootClass> appClasses = scene.getApplicationClasses();
        //创建一个临时列表，存储要删除的应用类
        List<SootClass> toRemove = new ArrayList<>();
        //遍历所有的应用类，添加到临时列表中
        for (SootClass appClass : appClasses) {
            toRemove.add(appClass);
        }
        //遍历临时列表，从Scene对象中移除每个应用类
        for (SootClass appClass : toRemove) {
            scene.removeClass(appClass);
        }
    }

    // 向soot中逐个加入需要被分析的类
    public static void loadTargetClass(){
        HashSet hashSet = new HashSet();
        String[] jdkPaths = RegularConfig.sootClassPath.split(":");
        List<String> paths = new ArrayList<>(Arrays.asList(jdkPaths));
        paths.add(RegularConfig.inputPath);
        for(String path : paths){
            for(String cl : SourceLocator.v().getClassesUnder(path)){
                if(checkIgnore(cl)){ continue; }
                try{
                    // 限制load一个类的超时阈值为100秒
                    (new TimeOutTask(){
                        @Override
                        protected void task() {
                            SootClass theClass = Scene.v().loadClassAndSupport(cl);
                            if (!theClass.isPhantom()) {
                                // 这里存在类数量不一致的情况，是因为存在重复的对象
                                theClass.setApplicationClass();
                                hashSet.add(theClass);
                                if(loadClassCounter % 10000 == 0){
                                    log.info("Collected {} classes.", loadClassCounter);
                                }
                                loadClassCounter++;
                            }
                        }
                        @Override
                        protected void timeoutHandler(){
                            log.error("将类" + cl + "导入到soot过程中超时，跳过处理");
                        }
                    }).run(10);

                }catch (Exception e){
                    log.error("加载类" + cl + "过程中出错：" + e.getMessage());
                }
            }
        }
        log.info("共加载：" + hashSet.size() + "个类，App.Size" + Scene.v().getApplicationClasses().size());
    }

    // 用于检查导入的类是否被认为忽略了
    public static boolean checkIgnore(String clazzName){

        for(String ignoreInfoTmp : ignoreInfo){
            if(ignoreInfoTmp.startsWith("#")){ continue; }
            if(clazzName.contains(ignoreInfoTmp)){ return true; }
        }
        return false;

    }

    // 获取外部用户指定的列表中的ignore classes
    private static List<String> getIgnoreInfo() {

        List<String> lines = new LinkedList<>();
        String ignoreListPath = RegularConfig.configPath + File.separator + "ignoreInfo";
        try{
            File ignoreFile = new File(ignoreListPath);
            lines = FileUtils.readLines(ignoreFile, StandardCharsets.UTF_8);
            // 统计出现的包的次数，处理超过阈值的类，并将新的内容写入到文件中
            String packageName;
            List<String> removePackageList = new ArrayList<>();
            for(String l : lines){
                if(l.startsWith("#") || l.equals("")) { continue; }
                packageName = getPackageName(l);
                updatePackageRecordTime(packageName);
            }
            if(maxPackageRecordTime <= 0 ) { maxPackageRecordTime = 10; } // 避免出现异常情况
            if (packageRecordTime == null)
                packageRecordTime = new HashMap<>();
            for(String key : packageRecordTime.keySet()){
                int currentTime = packageRecordTime.get(key);
                if(currentTime > maxPackageRecordTime){
                    removePackageList.add(key);
                    lines.removeIf(line -> line.contains(key));
                    lines.add(key);
                    log.info(key + "包下有超过" + maxPackageRecordTime + "个类无法处理，忽略整个包");
                }
            }
            // 避免java.util.ConcurrentModificationException
            for(String rmPackage : removePackageList){ packageRecordTime.remove(rmPackage); }
            FileUtils.writeLines(new File(ignoreListPath), lines, false);
            // 如果以注释符#开始或者本身是空字符串就删除掉
            lines.removeIf(line -> line.startsWith("#") || line.equals(""));
        }catch (IOException e){
            log.error("Load ignoreInfo from " + ignoreListPath + " failed!");
            System.exit(0);
        }
        return lines;

    }

    public static List<String> getBlackList(){
        List<String> lines = new LinkedList<>();
        String blackListPath = RegularConfig.configPath + File.separator + "testBlackList";
        // RegularConfig.blackListPath
        try{
            File blackListFile = new File(blackListPath);
            lines = FileUtils.readLines(blackListFile, StandardCharsets.UTF_8);
            // 统计出现的包的次数，处理超过阈值的类，并将新的内容写入到文件中
            String packageName;
            List<String> removePackageList = new ArrayList<>();
            for(String l : lines){
                if(l.startsWith("#") || l.equals("")) { continue; }
                packageName = getPackageName(l);
                updatePackageRecordTime(packageName);
            }
            if(maxPackageRecordTime <= 0 ) { maxPackageRecordTime = 10; } // 避免出现异常情况

            if (packageRecordTime == null)
                packageRecordTime = new HashMap<>();
            for(String key : packageRecordTime.keySet()){
                int currentTime = packageRecordTime.get(key);
                if(currentTime > maxPackageRecordTime){
                    removePackageList.add(key);
                    lines.removeIf(line -> line.contains(key));
                    lines.add(key);
                    log.info(key + "包下有超过" + maxPackageRecordTime + "个类无法处理，忽略整个包");
                }
            }
            // 避免java.util.ConcurrentModificationException
            for(String rmPackage : removePackageList){ packageRecordTime.remove(rmPackage); }
            FileUtils.writeLines(new File(blackListPath), lines, false);
            // 如果以注释符#开始或者本身是空字符串就删除掉
            lines.removeIf(line -> line.startsWith("#") || line.equals(""));
        }catch (IOException e){
            log.error("Load ignoreInfo from " + blackListPath + " failed!");
            System.exit(0);
        }
        return lines;
    }

    // 根据实际的情况更新packageRecordTime中的包出现的次数
    public static void updatePackageRecordTime(String packageName){
        if(packageRecordTime == null) { packageRecordTime = new HashMap<>(); }
        if(packageRecordTime.containsKey(packageName)){
            int time = packageRecordTime.get(packageName);
            packageRecordTime.put(packageName, ++time);
        } else {
            packageRecordTime.put(packageName, 1);
        }
    }

    // 工具类，给定一个用.分隔的完整类名，获取其包名
    public static String getPackageName(String className){

        if(className.equals("") || className.startsWith("#")){
            throw new IllegalArgumentException("className非法，当前值为：" + className);
        }
        String[] classNameSplit = className.split("\\.");
        className = className.replace("." + classNameSplit[classNameSplit.length - 1], "");
        return className;
    }
}
