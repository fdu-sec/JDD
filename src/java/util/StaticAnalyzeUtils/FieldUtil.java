package util.StaticAnalyzeUtils;

import dataflow.node.SourceNode;
import soot.*;
import soot.jimple.Constant;
import soot.jimple.FieldRef;
import soot.tagkit.Tag;
import util.ClassRelationshipUtils;
import util.Utils;

import java.util.HashSet;
import java.util.LinkedHashSet;

public class FieldUtil {
    /**
     * 解析sootField所属的类型, 返回该类所属的SootClass
     * @param sootField
     * @return
     */
    public static SootClass getSootFieldType(SootField sootField){
        String className = sootField.getType().toString();
        if (className.endsWith("[]"))
            className = className.replaceAll("\\[\\]","");
        return Scene.v().getSootClassUnsafe(className);
    }

    /**
     * 根据 fieldName 取出对应的 sootField
     * @param sootClass
     * @param fieldName
     * @return
     */
    public static SootField getSootFieldByName(SootClass sootClass, String fieldName){
        SootField sootField = sootClass.getFieldByNameUnsafe(fieldName);
        if (sootField != null)
            return sootField;
                                                            // getAllDirectInterfaceAbstractClz
        for (SootClass superClass : ClassUtils.getAllSupers(sootClass)){
            sootField = superClass.getFieldByNameUnsafe(fieldName);
            if (sootField != null)
                return sootField;
        }
        return null;
    }

    public static SootField getSootFieldByName(SootClass sootClass, Value fieldNameValue){
        if (!(fieldNameValue instanceof Constant))
            return null;
        String fieldName = fieldNameValue.toString().replaceAll("\"","");
        return getSootFieldByName(sootClass, fieldName);
    }

    public static SootFieldRef getSootFieldRefByName(SootClass sootClass, Value fieldvalue){
        return getSootFieldRef(sootClass, getSootFieldByName(sootClass,fieldvalue));
    }

    /**
     * 根据 field 当前所属的 SootClass 创建出 SootFieldRef
     */
    public static SootFieldRef getSootFieldRef(SootClass sootClass, SootField sootField){
        if (sootClass == null | sootField == null)
            return null;
        return Scene.v().makeFieldRef(sootClass,sootField.getName(),sootField.getType(),sootField.isStatic());
    }

    public static SootFieldRef getSootFieldRef(SootClass sootClass, Value fieldNameValue){
        SootField sootField = getSootFieldByName(sootClass, fieldNameValue);
        if (sootField != null)
            return getSootFieldRef(sootClass, sootField);
        return null;
    }

    /**
     * 判断 sootField 是否为 transient 类型
     */
    public static boolean isTransientType(SootField sootField){
        return Modifier.isTransient(sootField.getModifiers());
    }

    public static boolean isTransientType(Value value){
        if (!(value instanceof FieldRef))
            return false;
        return isTransientType(((FieldRef) value).getField());
    }

    /**
     * 判断 sootField是否为抽象/接口类型
     * @param sootField
     * @return
     */
    public static boolean isAbstractType(SootField sootField){
        SootClass sootClass = ClassRelationshipUtils.getOuterClass(getSootFieldType(sootField));
        if (sootClass == null)
            return false;
        return sootClass.isAbstract() | sootClass.isInterface();
    }

    public static boolean isGenericType(SootField sootField){
        SootClass sootClass = ClassRelationshipUtils.getOuterClass(getSootFieldType(sootField));
        if (sootClass == null)
            return false;

        if (sootClass.isInterface() | sootClass.isAbstract())
            return true;
        if (sootClass.getName().equals("java.lang.Object") | sootClass.getName().equals("java.lang.Object[]"))
            return true;
//        if (ClassRelationshipUtils.specialClassInfosMap.get("MapClass").contains(sootClass.getName()))
//            return true;
        return false;
    }

    /**
     * 检查sootClass是否包含sootField
     * @param sootClass
     * @param sootField
     * @return
     */
    public static boolean hasField(SootClass sootClass, SootField sootField){
        SootClass declaredClass = sootField.getDeclaringClass();
        return ClassUtils.getAllSupers(sootClass).contains(declaredClass);
    }

    /**
     * 从SootFieldRef得到SootField
     * @param sootFieldRef
     * @return
     */
    public static SootField fromRefToSootField(SootFieldRef sootFieldRef){
        return getSootFieldByName(sootFieldRef.declaringClass(), sootFieldRef.name());
    }


    /**
     * Soot 只能获取当前类申明的field, 因此遍历父类(包含sootClass)
     * @param sootClass
     * @return
     */
    public static LinkedHashSet<SootField> getAllDeclaredFields(SootClass sootClass){
        LinkedHashSet<SootField> ret = new LinkedHashSet<>();
        for (SootClass superClass: ClassUtils.getAllSupers(sootClass)){
            ret.addAll(superClass.getFields());
        }
        return ret;
    }

    /**
     * 返回方法的参数类型, 返回类型签名
     */
    public static String getDeTypeOfCollection(SootField sootField){
        Tag tag = sootField.getTag("SignatureTag");
        if (tag != null)
            return tag.toString();
        return null;
    }

    public static HashSet<SootField> findFieldsByType(SootClass sootClass, String typeStr){
        HashSet<SootField> ret = new HashSet<>();
        for (SootField sootField: getAllDeclaredFields(sootClass)){
            if (sootField.getType().toString().equals(typeStr))
                ret.add(sootField);
        }
        return ret;
    }

    public static SourceNode seletectPrioritySourceNode(HashSet<SourceNode> sourceNodes,
                                                        SootClass fieldTypeOfClass){
        HashSet<String> superClassNames = Utils.toStringSet(ClassUtils.getAllSupers(fieldTypeOfClass));
        superClassNames.forEach(className-> Utils.getLastIndexSubStr(className, "."));
        superClassNames.remove("Object");

        for (SourceNode sourceNode: sourceNodes){
            if (!sourceNode.isField() && !sourceNode.isFieldOfParameter()
                    && (ClassRelationshipUtils.isSubClassOf(Utils.toSootClass(sourceNode.field.getLast().getType()),
                        Utils.toSootClass("java.util.Map"))
                        || ClassRelationshipUtils.isSubClassOf(Utils.toSootClass(sourceNode.field.getLast().getType()),
                            Utils.toSootClass("java.util.Collection"))))  continue;
            String fieldTypeSig = getDeTypeOfCollection(sourceNode.field.getLast());
            if (fieldTypeSig == null)   continue;
            // FieldUtil.getDeTypeOfCollection(valuesOfObjectType.iterator().next().field.getLast())
            if (Utils.isElementContainsSet(superClassNames, fieldTypeSig))
                return sourceNode;
        }
        return null;
    }
}
