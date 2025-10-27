The SpringPartiallyComparableAdvisorHolder gadget chain in `marshalsec` is not the shortest one; 
therefore, it was excluded under JDD’s shortest-chain-first principle. 
However, JDD identified a more optimal alternative, as shown below. 
```
[JNDI Gadget] <java.util.Hashtable: java.lang.Object put(java.lang.Object,java.lang.Object)>
 -> <org.springframework.aop.target.HotSwappableTargetSource: boolean equals(java.lang.Object)>
 -> <javax.sound.sampled.AudioFormat$Encoding: boolean equals(java.lang.Object)>
 -> <org.springframework.aop.aspectj.autoproxy.AspectJAwareAdvisorAutoProxyCreator$PartiallyComparableAdvisorHolder: java.lang.String toString()>
 -> <org.springframework.aop.support.AbstractBeanFactoryPointcutAdvisor: org.aopalliance.aop.Advice getAdvice()>
 -> <org.springframework.jndi.support.SimpleJndiBeanFactory: java.lang.Object getBean(java.lang.String,java.lang.Class)>
 -> <org.springframework.jndi.support.SimpleJndiBeanFactory: java.lang.Object doGetSingleton(java.lang.String,java.lang.Class)>
 -> <org.springframework.jndi.JndiLocatorSupport: java.lang.Object lookup(java.lang.String,java.lang.Class)>
 -> <org.springframework.jndi.JndiTemplate: java.lang.Object lookup(java.lang.String,java.lang.Class)>
```


The corresponding exploit (exp) is also demonstrated in the JDD-POCLearning project under "hessian.payloadGroups.SpringPartiallyComparableAdvisorHolder".