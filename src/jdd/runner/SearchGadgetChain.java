package runner;

import com.google.common.base.Charsets;
import config.RegularConfig;
import config.SootConfig;
import container.BasicDataContainer;
import detetor.SearchGadgetChains;
import lombok.extern.slf4j.Slf4j;
import org.apache.commons.io.FileUtils;
import util.TimeMeasurement;

import java.io.File;
import java.io.IOException;
import java.nio.charset.StandardCharsets;
import java.nio.file.Files;
import java.nio.file.Path;
import java.nio.file.Paths;
import java.util.ArrayList;
import java.util.List;
import java.util.concurrent.*;
import java.util.regex.Matcher;
import java.util.regex.Pattern;

@Slf4j
public class SearchGadgetChain implements Callable<String> {
    public static void main(String[] args) throws InterruptedException {
        String state = "Execute";
        int times = 0;

        TimeMeasurement.begin();
        while(!state.equals("Finished")){
            Thread.sleep(1000);
            log.info("Execute the program for the " + (++times) + "th iteration");
            SearchGadgetChain detector = new SearchGadgetChain();
            FutureTask<String> task = new FutureTask<>(detector);
            Thread detectorThread = (new Thread(task, "Thread-under-supervision"));
            Thread.setDefaultUncaughtExceptionHandler(new DetectorRuntimeExceptionHandler());
            detectorThread.start();
            detectorThread.join();
            try{
                state = task.get();
            } catch (Exception e){
                log.error("Error Report: " + e.getMessage());
                if(times > RegularConfig.executionTimeLimit){ break; }
            }finally {
                BasicDataContainer.reset();
            }
        }
    }

    @Override
    public String call() throws Exception {
        try{
            SearchGadgetChains.detect();
        }catch (Exception e){
            DetectorRuntimeExceptionHandler handler = new DetectorRuntimeExceptionHandler();
            handler.uncaughtException(null, e);
            return e.getMessage();
        }
        return "Finished";
    }
}

@Slf4j
class DetectorRuntimeExceptionHandler implements Thread.UncaughtExceptionHandler {
    @Override
    public void uncaughtException(Thread t, Throwable e) {
        String msg = e.getMessage();
        handleExceptionMsg(msg);
    }

    /**
     * Handle the exception message and get the name of the class that caused the exception
     * @param msg exception message
     * @return unhandled class
     */
    private static String handleExceptionMsg(String msg) {

        String p = "", res;
        if(msg.contains("Failed to apply jb to <")){
            p = "Failed to apply jb to \\<([\\w\\W]*?)\\>";

        }else if(msg.contains("Failed to convert <")){
            p = "Failed to convert \\<([\\w\\W]*?)\\>";
        }
        if(p.equals("")) { throw new IllegalArgumentException("Cannot handle: " + msg); }
        res = getExceptionClassName(p, msg);
        if(SootConfig.checkIgnore(res)) { // Class xxx is already in ingoreInfo, do not add, only delete
            deleteUnhandledClass(res); log.info("Class " + res + " is");
            return null;
        }

        String ignoreListPath = RegularConfig.configPath + File.separator + "ignoreInfo";
        try{
            SootConfig.ignoreInfo.add(res);
            File ignoreFile = new File(ignoreListPath);
            FileUtils.writeStringToFile(ignoreFile, res + "\n", Charsets.UTF_8, true);
            log.info("Unhandled class " + res + " has been written to file");
            log.info("Deleted unhandled class " + res);
            deleteUnhandledClass(res);
        }catch (IOException e){
            log.error("Failed");
        }

        return res;
    }

    /**
     * Remove unparsable classes from the .class folder of the target analysis
     * only add the unhandled class to ignoreInfo file, may not work for jdk > 8.
     * @param res
     */
    public static void deleteUnhandledClass(String res){
        String filePathStr = RegularConfig.inputPath + res.replace(".", "/")+".class";
        Path path = Paths.get(filePathStr);
        try {
            Files.delete(path);
            System.out.println("Class deleted successfully.");
        }catch (IOException e){
            System.err.println("Failed to delete the file: " + e.getMessage());
        }
    }

    /**
     * Get the name of the class that caused the exception
     */
    private static String getExceptionClassName(String p, String msg){

        String res;
        List<String> resList;

        resList = getRegexResultList(p, msg);
        if(resList.isEmpty()) { throw new IllegalArgumentException("Pattern " + p + "无法处理异常信息：" + msg); }
        res = resList.get(0);
        res = res.replace("<", "");
        res = res.replace(">", "");
        String[] tmp;
        tmp = res.split(":");
        res = tmp[0];
        tmp = res.split(" ");
        res = tmp[tmp.length - 1];
        return res;
    }

    /**
     * Given a pattern to match and a str to process, return a list of results that match.
     */
    public static List<String> getRegexResultList(String pattern, String str){

        List<String> list = new ArrayList<>();
        Pattern strPattern = Pattern.compile(pattern);
        Matcher strMatcher = strPattern.matcher(str);
        while (strMatcher.find()){
            list.add(strMatcher.group());
        }
        return list;
    }

}