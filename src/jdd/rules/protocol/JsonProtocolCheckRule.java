package rules.protocol;

import config.RegularConfig;
import lombok.extern.slf4j.Slf4j;
import rules.sinks.*;
import soot.SootClass;
import soot.SootMethod;
import util.ClassRelationshipUtils;

import java.util.*;

@Slf4j
public class JsonProtocolCheckRule extends AbstractProtocolCheckRule {
    @Override
    public void init() {
        this.setSinkCheckRule();
    }

    @Override
    void setSinkCheckRule() {
        if (RegularConfig.sinkRules.contains("classLoad")) {
            ClassLoaderCheckRule classLoaderCheckRule = new ClassLoaderCheckRule();
            sinkCheckRule.put(classLoaderCheckRule.sinkType, classLoaderCheckRule);
        }
        if (RegularConfig.sinkRules.contains("jndi")) {
            JNDICheckRule JNDICheckRule = new JNDICheckRule();
            sinkCheckRule.put(JNDICheckRule.sinkType, JNDICheckRule);
        }
        if (RegularConfig.sinkRules.contains("exec")) {
            ExecCheckRule execCheckRule = new ExecCheckRule();
            sinkCheckRule.put(execCheckRule.sinkType, execCheckRule);
        }
    }

    @Override
    public HashSet<SootMethod> getSourceMethods() {
        doClassCheck();

        HashSet<SootMethod> sourceMethods = new HashSet<>();
        for (SootClass sootClass: candidateClassSet){
            for (SootMethod sootMethod: sootClass.getMethods()){
                if (isSourceMtd(sootMethod))
                    sourceMethods.add(sootMethod);
            }
        }

        this.sources = sourceMethods;

        return sourceMethods;
    }

    @Override
    public boolean openBPLink(){
        return false;
    }

    /**
     * 根据不同的反射点，采用不同的定制规则
     * @param sootMethod
     * @return
     */
    public boolean isSourceMtd(SootMethod sootMethod){
        if (RegularConfig.jsonSourceTypes.contains("staticCommon")) {
            if (sootMethod.isStatic() && sootMethod.isPublic()
                    && sootMethod.getParameterCount() == 1
                    && sootMethod.getParameterType(0).toString().equals("java.lang.String")) {
                return true;
            }
        }
        if (sootMethod.isStatic() || sootMethod.getParameterCount() > 0
                || !sootMethod.isConcrete() || !sootMethod.isPublic()) // 比较严格的筛选规则，可以看情况自定义修改
            return false;
        if (RegularConfig.jsonSourceTypes.contains("getter")) {
            if (ClassRelationshipUtils.isGetterMethod(sootMethod) && sootMethod.getName().length() >= 4)
                return true;
        }
        if (RegularConfig.jsonSourceTypes.contains("is")){
            if (ClassRelationshipUtils.isIsMethod(sootMethod) && sootMethod.getName().length() >= 4)
                return true;
        }
        if (RegularConfig.jsonSourceTypes.contains("OverWrittenInterfaceMtd")){
            if (ClassRelationshipUtils.isOverWrittenInterfaceMtd(sootMethod) && sootMethod.getName().length() > 4)
                return true;
        }
        if (RegularConfig.jsonSourceTypes.contains("setter")){
            if (ClassRelationshipUtils.isSetterMethod(sootMethod) && sootMethod.getName().length() >= 4)
                return true;
        }
        return false;
    }


}
