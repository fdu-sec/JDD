package common;

import soot.Scene;
import soot.SootClass;

import java.util.HashMap;
import java.util.HashSet;
import java.util.Iterator;

public class Memory {

    public static HashMap<SootClass, HashSet<SootClass>> classMapSonClasses = new HashMap<>();
    public static HashMap<SootClass,HashSet<SootClass>> interfaceMapImplementations = new HashMap<>();

    public static void init(){
        classMapSonClasses.clear();
        interfaceMapImplementations.clear();

        for (Iterator<SootClass> iterator = Scene.v().getClasses().snapshotIterator(); iterator.hasNext();){
            SootClass sootClass = iterator.next();
            if (sootClass.hasSuperclass()){
                SootClass fatherClass = sootClass.getSuperclass();
                if (!fatherClass.getName().equals("java.lang.Object")){
                    if (!classMapSonClasses.containsKey(fatherClass))
                        classMapSonClasses.put(fatherClass,new HashSet<>());
                    classMapSonClasses.get(fatherClass).add(sootClass);
                }
            }
            for (SootClass interfaceClass:sootClass.getInterfaces()){
                if (!interfaceMapImplementations.containsKey(interfaceClass))
                    interfaceMapImplementations.put(interfaceClass,new HashSet<>());
                interfaceMapImplementations.get(interfaceClass).add(sootClass);
            }
        }
    }

}
