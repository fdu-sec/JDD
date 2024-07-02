package util;

import lombok.extern.slf4j.Slf4j;

import java.io.File;
import java.io.IOException;
import java.util.ArrayList;
import java.util.HashMap;
import java.util.HashSet;
import java.util.logging.Logger;


public interface DirTraversal {
    void work(File f) throws Exception;

    Logger logger = Logger.getLogger(DirTraversal.class.getName());

    default void traverse(File dir){
        HashSet<File> toBeAnalyzedFiles = new HashSet<>();
        getAllFiles(dir,toBeAnalyzedFiles);
        for (File f:toBeAnalyzedFiles){
            try {
                work(f);
            } catch (Exception e) {
                logger.warning("[DIRECTORY TRAVERSAL ERROR] " + f + " (This may cause unexpected skipping the file.)");
                e.printStackTrace();
            }
        }
    }

    default void traverseWithCount(File dir){
        HashSet<File> toBeAnalyzedFiles = new HashSet<>();
        getAllFilesWithSuffix(dir,toBeAnalyzedFiles,".apk");
        logger.info("To be analyzed files: "+toBeAnalyzedFiles.size());
        int i=1;
        int sum = toBeAnalyzedFiles.size();
        for (File f:toBeAnalyzedFiles){
            try {
                logger.info("("+i+"/"+sum+") 处理" + f + "...");
                i+=1;
                work(f);
            } catch (Exception e) {
                logger.warning("[DIRECTORY TRAVERSAL ERROR] " + f + " (This may cause unexpected skipping the file.)");
                e.printStackTrace();
            }
        }
    }

    static void getAllFiles(File dir, HashSet<File> toBeAnalyzedFiles){
        File[] files = dir.listFiles();
        assert files != null;
        for(File f : files){
            if(f.isDirectory())
                getAllFiles(f,toBeAnalyzedFiles);
            if(f.isFile()){
                toBeAnalyzedFiles.add(f);
            }
        }
    }

    static void getAllFilesWithSuffix(File dir, HashSet<File> toBeAnalyzedFiles,String suffix){
        File[] files = dir.listFiles();
        assert files != null;
        for(File f : files){
            if(f.isDirectory())
                getAllFilesWithSuffix(f,toBeAnalyzedFiles,suffix);
            if(f.isFile() && f.getName().endsWith(suffix)){
                toBeAnalyzedFiles.add(f);
            }
        }
    }
}
