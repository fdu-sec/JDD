package util;

import container.BasicDataContainer;
import container.FragmentsContainer;
import markers.RelationShip;
import org.jetbrains.annotations.NotNull;
import soot.Scene;
import soot.SootClass;
import soot.SootMethod;
import util.StaticAnalyzeUtils.ClassUtils;

import java.util.*;
import java.util.regex.Pattern;

public class ClassRelationshipUtils {

    /**
     * 给定的basicTypes列表这样一个类/接口列表，获取它们所有的子类/接口实现类, 包括本身
     * @param basicTypes
     * @return
     */
    public static HashSet<String> getAllSubClasses(List<String> basicTypes){
        HashSet<String> ret = new HashSet<>();
        for (String className: basicTypes){
            SootClass sootClass = Scene.v().getSootClassUnsafe(className);
            if (sootClass != null){
                for (SootClass subClassName: ClassUtils.getAllSubs(sootClass))
                    ret.add(subClassName.getName());
            }
        }

        return ret;
    }

    /**
     * 给定一系列接口类型/抽象类型/普通类型basicTypes，取出所有该类的实现类/子类的
     * 符合包含rule中指定的方法名的方法签名
     * @param basicTypes
     * @param rule
     * @return
     */
    public static HashSet<String> getAllSubMethodSigs(@NotNull List<String> basicTypes, String rule){
        HashSet<String> methodSigs = new HashSet<>();
        for (String className: basicTypes){
            SootClass sootClass = Scene.v().getSootClassUnsafe(className);
            if (sootClass == null)  continue;

            for (SootClass subClass: ClassUtils.getAllSubs(sootClass)){
                for (SootMethod sootMethod: subClass.getMethods()){
                    if (matchRule(sootMethod,rule)){
                        methodSigs.add(sootMethod.getSignature());
                    }
                }
            }
        }
        return methodSigs;
    }

    /**
     * 给定一个SootMethod和一个正则表达式rule判断
     * 判断该方法的名字是否符合正则表达式
     * @param sootMethod
     * @param rule
     * @return
     */
    public static boolean matchRule(SootMethod sootMethod, String rule){
        return Pattern.matches(rule,sootMethod.getName());
    }

    /**
     * 获取methodSig的所有实现方法
     * @param methodSig
     * @return
     */
    public static HashSet<String> getAllSubMethodSigs(String methodSig){
        HashSet<SootMethod> subMethods = new HashSet<>();
        if(!Scene.v().containsMethod(methodSig)) { return new HashSet<>(); }
        SootMethod sootMethod = Scene.v().getMethod(methodSig);
        if (sootMethod == null)  return new HashSet<>();

        return Utils.toMethodSigs(getAllSubMethods(sootMethod));
    }

    public static HashSet<SootMethod> getAllSubMethods(SootMethod sootMethod){
//        HashSet<SootMethod> ret = new HashSet<>();
//        for (SootClass subClass: ClassUtils.getAllSubs(sootMethod.getDeclaringClass())){
//            SootMethod subMethod = subClass.getMethodUnsafe(sootMethod.getSubSignature());
//            if (subMethod != null){
//                ret.add(subMethod);
//            }
//        }
        return getAllSubMethods(sootMethod.getDeclaringClass(), sootMethod.getSubSignature());
    }

    /**
     * 返回sootClass的子类中的methodSubSig方法
     * @param sootClass
     * @param methodSubSig
     * @return
     */
    public static HashSet<SootMethod> getAllSubMethods(SootClass sootClass, String methodSubSig){
        HashSet<SootMethod> ret = new HashSet<>();
        for (SootClass subClass: ClassUtils.getAllSubs(sootClass)){
            SootMethod tmpMethod = subClass.getMethodUnsafe(methodSubSig);
            if (tmpMethod != null)
                ret.add(tmpMethod);
        }
        return ret;
    }

    /**
     * 判断 sootMethod1 和 sootMethod2是否具有相同的父类/接口类方法
     * @param sootMethod1
     * @param sootMethod2
     * @return
     */
    public static boolean hasSameSuperMethod(SootMethod sootMethod1, SootMethod sootMethod2){
        if (sootMethod1.equals(sootMethod2))
            return true;

        HashSet<SootMethod> toDelete = new HashSet<>();
        HashSet<SootMethod> superMethods1 = getAllSuperMethods(sootMethod1, true);
        for (SootMethod sootMethod: superMethods1){
            if (sootMethod.isConcrete())
                toDelete.add(sootMethod);
        }

        HashSet<SootMethod> superMethods2 = getAllSuperMethods(sootMethod2, true);
        for (SootMethod sootMethod: superMethods2){
            if (sootMethod.isConcrete())
                toDelete.add(sootMethod);
        }
        superMethods1.removeAll(toDelete);
        superMethods2.removeAll(toDelete);

        superMethods2.retainAll(superMethods1);
        return !superMethods2.isEmpty();
    }

    /**
     * 判断sootClass是否为superClass的子类 (包括本身)
     * @param sootClass
     * @param superClass
     * @return
     */
    public static boolean isSubClassOf(SootClass sootClass, SootClass superClass){
        if (superClass == null) return false;
        if (Utils.isBasicType(superClass.getName()))    return false; // 认为基本类不可为父类
        if (superClass.getName().equals("java.lang.Object"))    return true;
        String superClassName = superClass.getName();
        if (BasicDataContainer.subClassSearchRecord.containsKey(superClassName))
            return BasicDataContainer.subClassSearchRecord.get(superClassName).contains(sootClass.getName());

        HashSet<String> subClasses = Utils.toClassNames(ClassUtils.getAllSubs(superClass));
        if (superClassName.equals("java.io.Serializable")
                || superClassName.equals("java.lang.reflect.InvocationHandler")
                || superClassName.equals("java.util.List")
                || superClassName.equals("java.util.Collection")
                || superClassName.equals("java.util.Map$Entry")
                || superClassName.equals("java.util.Map")
                || BasicDataContainer.subClassSearchRecord.get("java.util.Map$Entry").contains(superClassName)){
            BasicDataContainer.subClassSearchRecord.put(superClassName, subClasses);
        }
        return subClasses.contains(sootClass.getName());
    }

    /**
     * 获取sootClass1 和 sootClass2之间的关系
     * 0: 没有关系
     * 1: 相同
     * 2: sootClass1 是 sootClass2的子类
     * 3: sootClass2 是 sootClass1的子类
     * 4: sootClass1 和 sootClass 2没有直接关系, 父类相交
     * @param sootClass1
     * @param sootClass2
     * @return
     */
    public static RelationShip getExtentRelationshipAmongClasses(SootClass sootClass1, SootClass sootClass2){
        if (sootClass1.equals(sootClass2))
            return RelationShip.EQUAL;
        if (sootClass1.getName().equals("java.lang.Object"))
            return RelationShip.SUPER;
        if (sootClass2.getName().equals("java.lang.Object"))
            return RelationShip.SUB;

        HashSet<SootClass> superClasses1 = ClassUtils.getAllSupers(sootClass1);
        HashSet<SootClass> superClasses2 = ClassUtils.getAllSupers(sootClass2);
        HashSet<SootClass> subClasses1 = ClassUtils.getAllSubs(sootClass1);
        HashSet<SootClass> subClasses2 = ClassUtils.getAllSubs(sootClass2);

        if (superClasses1.contains(sootClass2))
            return RelationShip.SUB;
        else if (superClasses2.contains(sootClass1))
            return RelationShip.SUPER;
        else {
            superClasses1.retainAll(superClasses2);
            subClasses1.retainAll(subClasses2);
            // 判断是否存在相同的子类, 优先级比是否存在相同的父类高
            if (!subClasses1.isEmpty() & !superClasses1.isEmpty())
                return RelationShip.HAS_SAME_SUPER_AND_SUB;

            if (!subClasses1.isEmpty())
                return RelationShip.HAS_SAME_SUB;

            if (!superClasses1.isEmpty()) {
                return RelationShip.HAS_SAME_SUPER;
            }
            else return RelationShip.NONE;
        }
    }


    /* className对应的类是否为outerClass的内部实现类 */
    public static boolean isOuterClassOf(SootClass sootClass, SootClass outerCLass){
        if (!sootClass.hasOuterClass()) return false;
        return sootClass.getOuterClass().equals(outerCLass);
    }

    /**
     * 查找sootClass的外部类，如果sootClass并非内部类，则返回本身
     */
    public static SootClass getOuterClass(SootClass sootClass){
        if (sootClass == null)
            return null;
        if (sootClass.hasOuterClass() & Utils.endWithNumber(sootClass.getName()))
            return sootClass.getOuterClass();
        return sootClass;
    }




    /**
     * 获取所有的clz的接口/抽象类，可能不包括自己(会根据是否Concrete删除)
     * 删除 java.io.Serializable 接口，防止不必要的重复
     */
    public static HashSet<SootClass> getAllInterfaceAbstractClz(SootClass clz){
        HashSet<SootClass> ret = new HashSet<>();
        if (clz == null)
            return ret;
        LinkedHashSet<SootClass> superClzSet = ClassUtils.getAllSupers(clz);
        if(superClzSet.isEmpty()) { return ret; }
        for(SootClass supClz : superClzSet){
            if(supClz.isConcrete()){ continue; }
            if (supClz.getName().equals("java.io.Serializable")
                    | supClz.getName().contains("java.io.Externalizable")
                    | supClz.getName().contains("java.lang.Cloneable"))    {continue;}
            ret.add(supClz);
        }
        return ret;
    }

    /**
     * 获取 clz 直接extend / implements 的所有类，包括自己
     * @param clz
     * @return
     */
    public static HashSet<SootClass> getAllDirectInterfaceAbstractClz(SootClass clz){
        HashSet<SootClass> res = new HashSet<>();
        Set<SootClass> superClzSet = new HashSet<>();
        if (clz.hasSuperclass())
            superClzSet.add(clz.getSuperclass());
        if (clz.getInterfaceCount()>0){
            superClzSet.addAll(clz.getInterfaces());
        }

        for (SootClass supClz : superClzSet){
            if (supClz.isConcrete())    continue;
            if (supClz.getName().equals("java.io.Serializable")
                    | supClz.getName().contains("java.io.Externalizable")
                    | supClz.getName().contains("java.lang.Cloneable"))    {continue;}
            res.add(supClz);
        }
        res.add(clz);
        return res;
    }

    /**
     * 获取有 subSigMtd 方法的所有父类 (之前默认包含)
     * @param clz
     * @param subSigMtd
     * @param selfFlag 是否包含clz
     * @return
     */
    public static HashSet<SootClass> getDirectSuperClzWithMtd(SootClass clz, String subSigMtd, boolean selfFlag){
        HashSet<SootClass> res = new HashSet<>();
        for (SootClass superClz : getAllDirectInterfaceAbstractClz(clz)){
            if (superClz.equals(clz) & !selfFlag)
                continue;
            if (superClz.getMethodUnsafe(subSigMtd) != null)
                res.add(superClz);
        }
        return res;
    }

    public static HashSet<SootClass> getAllSuperClzWithMtd(SootClass clz, String subSigMtd, boolean selfFlag){
        HashSet<SootClass> res = new HashSet<>();
        for (SootClass superClz : ClassUtils.getAllSupers(clz)){
            if (superClz.equals(clz) & !selfFlag)
                continue;
            if (superClz.getMethodUnsafe(subSigMtd) != null)
                res.add(superClz);
        }
        return res;
    }

    /**
     * 返回sootMethod的所有父类方法
     * @param sootMethod
     * @return
     */
    public static LinkedHashSet<SootMethod> getAllSuperMethods(SootMethod sootMethod, boolean selfFlag){
        String methodSubSig = sootMethod.getSubSignature();
        LinkedHashSet<SootMethod> ret = new LinkedHashSet<>();
        for (SootClass superClass: ClassUtils.getAllSupers(sootMethod.getDeclaringClass())){
            if (!selfFlag & sootMethod.getDeclaringClass().equals(superClass))
                continue;
            SootMethod superMethod = superClass.getMethodUnsafe(methodSubSig);
            if (superMethod != null) {
                ret.add(superMethod);
            }
        }
        return ret;
    }

    /**
     * 获得 sootMethod 的所有父类方法 (之前默认为不包含)
     * @param sootMethod
     * @return
     */
    public static HashSet<SootMethod> getDirectSuperMtdBySubSig(SootMethod sootMethod, boolean selfFlag){
        SootClass clz = sootMethod.getDeclaringClass();
        String subSig = sootMethod.getSubSignature();
        HashSet<SootMethod> res = new HashSet<>();
        for (SootClass superClz : getAllDirectInterfaceAbstractClz(clz)){
            if (superClz.equals(clz) & !selfFlag)
                continue;
            SootMethod superMethod = superClz.getMethodUnsafe(subSig);
            if (superMethod != null)
                res.add(superMethod);
        }
        return res;
    }

    public static HashSet<SootMethod> getAllSuperMtdBySubSig(SootMethod sootMethod, boolean selfFlag){
        SootClass clz = sootMethod.getDeclaringClass();
        String subSig = sootMethod.getSubSignature();
        HashSet<SootMethod> res = new HashSet<>();
        for (SootClass superClz : getAllInterfaceAbstractClz(clz)){
            if (superClz.equals(clz) & !selfFlag)
                continue;
            SootMethod superMethod = superClz.getMethodUnsafe(subSig);
            if (superMethod != null)
                res.add(superMethod);
        }
        SootMethod tmpObjMtd = BasicDataContainer.commonClassMap.get("Object").getMethodUnsafe(subSig);
        if (tmpObjMtd != null)
            if (tmpObjMtd.isConcrete() & !tmpObjMtd.isFinal())
                res.add(tmpObjMtd);

        return res;
    }

    /**
     * 判断是否为 抽象/接口方法
     * @param sootMethod
     * @return
     */
    public static boolean isPolyMethod(SootMethod sootMethod){
        if (sootMethod.isAbstract() | sootMethod.getDeclaringClass().isInterface())
            return true;
        return false;
    }

    /**
     * 判断是否为 动态代理的 InvocationHandler方法
     * @param mtd
     * @return
     */
    public static boolean isProxyMethod(SootMethod mtd){

        if(!BasicDataContainer.openDynamicProxyDetect) { return false; }

        if (!mtd.getSubSignature().equals("java.lang.Object invoke(java.lang.Object,java.lang.reflect.Method,java.lang.Object[])"))
            return false;

        if (isSubClassOf(mtd.getDeclaringClass(),Utils.toSootClass("java.lang.reflect.InvocationHandler")))
            return true;
        return false;
    }

    /**
     * 获取sootMethod的访问权限: public, private, protected
     * @param sootMethod
     * @return
     */
    public static String getAccessPermission(SootMethod sootMethod){
        String accessPermission = sootMethod.getDeclaration().split(" ")[0];
        if (!BasicDataContainer.accessPermissions.contains(accessPermission))
            return "default";
        return accessPermission;
    }

    public static boolean isGetterMethod(SootMethod sootMethod){
        String pattern = "(get)+([^a-z]+.*)+";
        return Pattern.matches(pattern, sootMethod.getName());
    }

    public static boolean isIsMethod(SootMethod sootMethod){
        String pattern = "(is)+([^a-z]+.*)+";
        return Pattern.matches(pattern, sootMethod.getName());
    }

    public static boolean isSetterMethod(SootMethod sootMethod){
        String pattern = "(set)+([^a-z]+.*)+";
        return Pattern.matches(pattern, sootMethod.getName());
    }


    /**
     * 检查sootMethod是否为某个接口类型的重写方法
     * @param sootMethod
     * @return
     */
    public static boolean isOverWrittenInterfaceMtd(SootMethod sootMethod){
        if (!sootMethod.isConcrete())
            return false;
        HashSet<SootClass> superClzs = ClassUtils.getAllSupers(sootMethod.getDeclaringClass());
        String subSignature = sootMethod.getSubSignature();
        for (SootClass superClz: superClzs){
            if (!superClz.isInterface())
                continue;
            if (superClz.getMethodUnsafe(subSignature) != null)
                return true;
        }
        return false;
    }


    /**
     * 根据subSig提取sootClass中的方法
     * @param sootClass
     * @param subSigs
     * @return
     */
    public static HashSet<SootMethod> getMethods(SootClass sootClass, HashSet<String> subSigs){
        HashSet<SootMethod> ret = new HashSet<>();
        for (String subSig: subSigs){
            SootMethod method = sootClass.getMethodUnsafe(subSig);
            if (method != null)
                ret.add(method);
        }
        return ret;
    }

    /**
     * 判断sootMethod是否为动态方法
     * (1) 多态
     * (2) 动态代理
     * 可扩充
     */
    public static boolean isDynamicMethod(SootMethod sootMethod){
        if (FragmentsContainer.dynamicMtds.contains(sootMethod))
            return true;
        if (sootMethod.isAbstract()
                | sootMethod.getDeclaringClass().isInterface()
                | sootMethod.getDeclaringClass().getName().equals("java.lang.Object"))
            return true;
        return false;
    }

    /**
     * 判断superMethod是否为sootMethod的父类接口/抽象方法
     * 启发式: Object类型的完全不允许有重复的父类方法
     * 用于判断Fragment:head<->end的合法性 (end应当为head的可控父类方法, 即具有更高的调用其他方法的权限)
     * @param sootMethod 可以为具体方法
     * @param superMethod 不能为具体方法
     * @return
     */
    public static boolean isValidSuperAbstractOrInterfaceMethod(SootMethod sootMethod, SootMethod superMethod){
        if (superMethod.isConcrete() | superMethod.isNative())
            return false;

        LinkedHashSet<SootMethod> allSuperMethods = getAllSuperMethods(sootMethod, false);
        if (!allSuperMethods.contains(superMethod)
                | allSuperMethods.size() < 2)
            return false;

        int index = 0;
        for (SootMethod superMtd: allSuperMethods){
            if (superMtd.getDeclaringClass().getName().equals("java.lang.Object"))
                return false;
            if (!superMethod.equals(superMtd) & superMtd.isConcrete())
                return false;
            if (superMethod.equals(superMtd) & index > 0)
                return true;
            index ++;
        }

        return false;
    }

    /**
     * 获取 sootClass 中与 methodSubSigs 具有相同 sub sig 的方法
     * @param sootClass
     * @param methodSubSigs
     * @return
     */
    public static HashSet<SootMethod> getMethodsOfClass(SootClass sootClass, HashSet<String> methodSubSigs){
        HashSet<SootMethod> ret = new HashSet<>();
        if (sootClass == null)
            return ret;
        for (String methodSubSig: methodSubSigs){
            SootMethod tmpMethod = sootClass.getMethodUnsafe(methodSubSig);
            if (tmpMethod != null)
                ret.add(tmpMethod);
        }

        return ret;
    }

    /**
     * 取sootClass中与subSig相同子签名的方法, 考虑父类
     * @param sootClass
     * @param subSig
     * @return
     */
    public static SootMethod getMethodOfClassAndSuper(SootClass sootClass, String subSig){
        for (SootClass tmpClass: ClassUtils.getAllSupers(sootClass)){
            SootMethod tmpMethod = tmpClass.getMethodUnsafe(subSig);
            if (tmpMethod != null){
                if (!isDynamicMethod(tmpMethod))
                    return tmpMethod;
            }
        }

        return null;
    }

    /**
     * 判断 caller 是否为 invokedMethod(实际调用方法: next) 所属类的父类方法: caller(父类方法)->子类方法
     * @param caller
     * @param invokedMethod
     * @param next
     * @return
     */
    public static boolean isAbsSuperCallee(SootMethod caller, SootMethod invokedMethod, SootMethod next) {
        if (next == null)
            return false;
        if (next.isStatic())
            return false;
        // 1. 和调用方法subSig相同
        if (!next.getSubSignature().equals(invokedMethod.getSubSignature()))
            return false;
        // 2. 调用方法的类是当前方法所属类的子类
        if (!ClassUtils.getAllSupers(next.getDeclaringClass()).contains(caller.getDeclaringClass()))
            return false;
        // 3. 调用方法没有当前方法
        if (next.getDeclaringClass().getMethodUnsafe(caller.getSubSignature()) != null)
            return false;
        return true;
    }


    /**
     * 判断 sootMethod 是否在 callstack中
     * 包含: 相等 / 和其中某个方法, 是对同一个接口/抽象方法的实现
     * @param callStack
     * @param sootMethod
     * @return
     */
    public static boolean containsInCallStack(LinkedList<SootMethod> callStack, SootMethod sootMethod){
        if (callStack == null)  {return false; }
        String subSig = sootMethod.getSubSignature();
        Set<SootClass> supClzOfMtd = getAllInterfaceAbstractClz(sootMethod.getDeclaringClass());

        for (SootMethod mtd: callStack){
            if (!mtd.getSubSignature().equals(subSig))
                continue;
            SootClass clz = mtd.getDeclaringClass();
            Set<SootClass> supClzs = getAllInterfaceAbstractClz(clz);
            supClzs.retainAll(supClzOfMtd);
            if (supClzs.isEmpty())
                continue;
            return true;
        }
        return false;
    }

    /**
     * 向上查找最顶层的接口/抽象方法
     * @param sootMethod
     * @return
     */
    public static SootMethod getTopSuperMethod(SootMethod sootMethod){
        String methodSubSig = sootMethod.getSubSignature();
        SootMethod ret = null;
        for (SootClass superClass: ClassUtils.getAllSupers(sootMethod.getDeclaringClass())){
            SootMethod superMethod = superClass.getMethodUnsafe(methodSubSig);
            if (superMethod != null) {
                ret = superMethod;
            }
        }
        return ret;
    }

    public static HashSet<SootMethod> getMethodsByName(SootClass sootClass, String methodName) {
        List<SootMethod> ret = sootClass.getMethods();
        ret.removeIf(mtd->!mtd.getName().equals(methodName));
        return new HashSet<>(ret);
    }
}
