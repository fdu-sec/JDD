package util;

import cfg.Node;
import com.google.gson.Gson;
import config.RegularConfig;
import container.BasicDataContainer;
import container.RulesContainer;
import gadgets.collection.iocd.IOCD;
import gadgets.collection.iocd.unit.ConditionRecord;
import gadgets.collection.iocd.unit.instrument.IfStmtInstRecord;
import gadgets.collection.iocd.unit.instrument.Instruments;
import gadgets.collection.iocd.unit.instrument.MethodInstRecord;
import gadgets.collection.node.ConditionNode;
import gadgets.collection.node.GadgetInfoRecord;
import gadgets.collection.node.GadgetNode;
import lombok.extern.slf4j.Slf4j;
import markers.SinkType;
import org.apache.commons.io.FileUtils;
import soot.SootClass;
import soot.SootMethod;
import soot.jimple.IfStmt;
import structure.RuleDataStructure;
import structure.taint.TaintSpreadRuleUnit;

import java.io.File;
import java.io.FileNotFoundException;
import java.io.FileWriter;
import java.io.IOException;
import java.nio.file.Files;
import java.nio.file.Path;
import java.nio.file.Paths;
import java.util.HashMap;
import java.util.HashSet;
import java.util.LinkedList;

import static gadgets.collection.AnalyzeUtils.*;
import static gadgets.collection.iocd.TransformerUtils.transformGadgetRecord;

@Slf4j
public class DataSaveLoadUtil {
    /**
     * 工具类，用于将对象进行Json的序列化
     * @param o
     * @return Json序列化后的数据
     */
    public static String toGJson(Object o){
        Gson gson = new Gson();
        return gson.toJson(o);
    }

    public static Object toObject(String json, Class clazzType){
        Gson gson = new Gson();
        return gson.fromJson(json, clazzType);
    }

    // 加载 ruleDataStructure
    public static void loadRuleDataStructure() throws IOException {
        String rulesPath = RegularConfig.configPath + File.separator + "RuleDataStructure.json";
        String jsonContent = FileUtils.readFileToString(new File(rulesPath),"utf-8");

        RulesContainer.ruleDataStructure = (RuleDataStructure) toObject(jsonContent, RuleDataStructure.class);
        // 初始化 Rules
        for (TaintSpreadRuleUnit taintSpreadRuleUnit: RulesContainer.ruleDataStructure.getTaintSpreadRuleUnits()){
            taintSpreadRuleUnit.init();
            BasicDataContainer.blackList.addAll(taintSpreadRuleUnit.methodSigs);
        }
    }

    // 存储更新后的 ruleDataStructure
    public static void saveRuleDataStructure(){
        if (RulesContainer.ruleDataStructure == null)
            return;

        String outPutJson = toGJson(RulesContainer.ruleDataStructure);
        String rulesPath = RegularConfig.configPath + File.separator + "RuleDataStructure.json";
        try{
            FileWriter out = new FileWriter(rulesPath, false);
            out.write(outPutJson);
            out.flush();
        } catch (IOException e){
            log.error("Could not write result to " + rulesPath + "!");
            e.printStackTrace();
        }
    }

    public static void saveTaintSpreadRules(HashSet<TaintSpreadRuleUnit> candidateTaintSpreadRuleUnits){
        assert RulesContainer.ruleDataStructure != null;
        RulesContainer.ruleDataStructure.getTaintSpreadRuleUnits().addAll(candidateTaintSpreadRuleUnits);
    }

    public static void saveTaintSpreadRule(TaintSpreadRuleUnit candidateTaintSpreadRuleUnit){
        assert RulesContainer.ruleDataStructure != null;
        RulesContainer.ruleDataStructure.getTaintSpreadRuleUnits().add(candidateTaintSpreadRuleUnit);
    }

    /**
     * 将 call stack - sink类型信息 记录到输出文件中
     * @param callStack
     * @param sinkType
     */
    public static void recordCallStackToFile(LinkedList<SootMethod> callStack, SinkType sinkType,
                                             String fileName, boolean printFlag) throws IOException {
        SootMethod entryMtd = callStack.get(0);
        FileWriter out = openOrCreateFileWriter(fileName, true);
//                new FileWriter(fileName,true);
        try {
            String first = "["+sinkType+" Gadget] "+entryMtd.getSignature();
            out.write(first);
            out.write("\n");
            if (printFlag)
                System.out.println(first);

            for (int i=1; i<callStack.size();i++) {
                String info ;
                info = " -> "+callStack.get(i).getSignature();;
                out.write(info);
                out.write("\n");

                if (printFlag)
                    System.out.println(info);
            }
            out.write("\n");
            out.flush();
        } catch (FileNotFoundException e) {
            throw new RuntimeException(e);
        } catch (IOException e) {
            throw new RuntimeException(e);
        } finally {
            if (out != null)
                out.close();
        }
    }

    public static boolean fileExistOrNot(String filePath){
        File file = new File(filePath);
        return file.exists();
    }

    public static FileWriter openOrCreateFileWriter(String filePath, boolean appendFlag) throws IOException {
        Path directoryPath = Paths.get(filePath).getParent();
        try {
            if (Files.notExists(directoryPath)) {
                Files.createDirectories(directoryPath);
            }
        }catch (Exception e){e.printStackTrace();}

        if (fileExistOrNot(filePath))
            return new FileWriter(filePath,appendFlag);

        try {
            File file = new File(filePath);
            boolean fileCreated = file.createNewFile();
            if (fileCreated){
                log.info("Created File: "+filePath);
            }else log.info("Failed to create file: "+filePath);

            FileWriter fileWriter = new FileWriter(filePath, appendFlag);
            return fileWriter;
        }catch (Exception e){
            e.printStackTrace();
        }
        return null;
    }

    public static void createDir(String targetDir){
        Path targetPath = Paths.get(targetDir);
        if (!Files.exists(targetPath)){
            try {
                Files.createDirectories(targetPath);
            } catch (IOException e) {
                throw new RuntimeException(e);
            }
        }
    }
}
