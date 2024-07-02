package util.StaticAnalyzeUtils;

import lombok.extern.slf4j.Slf4j;
import soot.Scene;
import soot.SootClass;

import java.util.*;

/**
 * 静态分析基本能力
 */
@Slf4j
public class ClassUtils {
    public static HashSet<SootClass> forceGetConcreteClass(SootClass sootClass, int num){
        // BFS search for concrete subclass , return num classes at most
        HashSet<SootClass> concreteClasses = new HashSet<>();
        Queue<SootClass> queue = new LinkedList<>();
        queue.add(sootClass);
        while(!queue.isEmpty() && num > 0){
            SootClass c = queue.poll();
            if(c.isConcrete()) {
                concreteClasses.add(c);
                num--;
            }
            else{
                queue.addAll(Scene.v().getActiveHierarchy().getDirectSubclassesOf(sootClass));
            }
        }
        return concreteClasses;
    }

    public static SootClass forceGetConcreteClassOnlyOne(SootClass sootClass){
        HashSet<SootClass> concreteClasses = forceGetConcreteClass(sootClass, 1);
        if(concreteClasses.size() > 0) return concreteClasses.iterator().next();
        return null;
    }

    public static LinkedHashSet<SootClass> getAllSupers(SootClass sootClass){
        LinkedHashSet<SootClass> res = new LinkedHashSet<>();
        getAllSuperClassAndInterfaces(sootClass, res);
        return res;
    }

    /**
     * 得到所有的父类 & 接口
     */
    private static void getAllSuperClassAndInterfaces(SootClass sootClass, LinkedHashSet<SootClass> result){
        if(result.contains(sootClass)) return;
        if (sootClass.resolvingLevel()<1) return;
        result.add(sootClass);
        if(sootClass.isInterface()) {
            if (!sootClass.hasSuperclass())  return;
            for(SootClass superClass : Scene.v().getActiveHierarchy().getSuperinterfacesOf(sootClass)) {
                getAllSuperClassAndInterfaces(superClass, result);
            }
        }else if (sootClass.hasSuperclass()){
            for(SootClass superClass : Scene.v().getActiveHierarchy().getSuperclassesOf(sootClass)) {
                getAllSuperClassAndInterfaces(superClass, result);
            }
        }
        if (sootClass.getInterfaceCount() > 0){
            for (SootClass interfaceClass : sootClass.getInterfaces()){
                getAllSuperClassAndInterfaces(interfaceClass, result);
            }
        }
    }

    public static HashSet<SootClass> AllInterfaces(SootClass sootClass){
        LinkedHashSet<SootClass> res = new LinkedHashSet<>();
        getAllSuperClassAndInterfaces(sootClass, res);
        return res;
    }

    private static void getAllInterfaces(SootClass sootClass, HashSet<SootClass> result){
        if(result.contains(sootClass)) return;
        result.add(sootClass);
        if(sootClass.isInterface()) {
            for(SootClass superClass : Scene.v().getActiveHierarchy().getSuperinterfacesOf(sootClass)) {
                getAllInterfaces(superClass, result);
            }
        }else {
            for(SootClass superClass : Scene.v().getActiveHierarchy().getSuperinterfacesOf(sootClass)) {
                getAllInterfaces(superClass, result);
            }
        }
    }

    // getAllSubClassAndInterfaces的封装
    public static HashSet<SootClass> getAllSubs(SootClass sootClass){
        HashSet<SootClass> res = new HashSet<>();
        getAllSubClassAndInterfaces(sootClass, res);
        return res;
    }

    /**
     * 查找实现了sootClass的所有子类
     * @param sootClass 目标CLass
     * @param result 保存结果的HashSet
     */
    private static void getAllSubClassAndInterfaces(SootClass sootClass, HashSet<SootClass> result){
        if(result.contains(sootClass)) return;
        if (sootClass.resolvingLevel()<1) return;

        result.add(sootClass); // ToDo: 古怪的写法
        // 如果是接口，那么就获取他的子接口和实现类并且递归处理
        // 如果不是接口，那么就获取当前类的子类并且递归处理
        if(sootClass.isInterface()) {
            for(SootClass superClass : Scene.v().getActiveHierarchy().getSubinterfacesOf(sootClass)) {
                getAllSubClassAndInterfaces(superClass, result);
            }
            for(SootClass superClass : Scene.v().getActiveHierarchy().getImplementersOf(sootClass)) {
                getAllSubClassAndInterfaces(superClass, result);
            }
        } else  {
            try {
                for (SootClass superClass : Scene.v().getActiveHierarchy().getSubclassesOf(sootClass)) {
                    getAllSubClassAndInterfaces(superClass, result);
                }
            }catch (NullPointerException e){
//                log.info(sootClass.getName() + " does not have any sub-classes!");
            }
        }
    }

    /**
     * 广度优先的顺序逐层得到所有父类,大部分情况下（不考虑接口Default方法），他应该是一条链
     * 包含sootClass
     */
    public static LinkedList<SootClass> getAllSupers_BFS(SootClass sootClass){
        LinkedList<SootClass> ret = new LinkedList<>();
        Queue<SootClass> waiting = new LinkedList<>();
        waiting.add(sootClass);
        while(!waiting.isEmpty()){
            SootClass clazz = waiting.poll();
            ret.add(clazz);
            if(!sootClass.isInterface()){
                if(sootClass.hasSuperclass() && !waiting.contains(sootClass.getSuperclass()) && !ret.contains(sootClass.getSuperclass()))
                    waiting.add(sootClass.getSuperclass());
            }else if (sootClass.isInterface()){
                for (SootClass superClass: sootClass.getInterfaces()) {
                    if (waiting.contains(superClass) | ret.contains(superClass))
                        continue;
                    waiting.add(superClass);
                }
            }
        }
        return ret;
    }

    /**
     * 广度优先的顺序逐层得到所有子类
     */
    public static List<SootClass> getAllSubs_BFS(SootClass sootClass){
        List<SootClass> ret = new LinkedList<>();
        Queue<SootClass> waiting = new LinkedList<>();
        waiting.add(sootClass);
        while(!waiting.isEmpty()){
            SootClass clazz = waiting.poll();
            ret.add(clazz);
            if(sootClass.isInterface()) {
                for(SootClass subClass : Scene.v().getActiveHierarchy().getDirectSubinterfacesOf(sootClass)) {
                    if(!waiting.contains(subClass) && !ret.contains(subClass)) waiting.add(subClass);
                }
                for(SootClass subClass : Scene.v().getActiveHierarchy().getDirectImplementersOf(sootClass)) {
                    if(!waiting.contains(subClass) && !ret.contains(subClass)) waiting.add(subClass);
                }
            }
            else  {
                for(SootClass subClass : Scene.v().getActiveHierarchy().getDirectSubclassesOf(sootClass)) {
                    if(!waiting.contains(subClass) && !ret.contains(subClass)) waiting.add(subClass);
                }
            }
        }
        return ret;
    }
}
