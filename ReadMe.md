## Efficient Detection of Java Deserialization Gadget Chains via Bottom-up Gadget Search and Dataflow-aided Payload Construction
### Publication
Efficient Detection of Java Deserialization Gadget Chains via Bottom-up Gadget Search and Dataflow-aided Payload Construction

B Chen, L Zhang, X Huang, Y Cao, K Lian, Y Zhang, M Yang

IEEE Symposium on Security and Privacy (SP), 2024

### Runtime Environment
JDK 8

Dependencies: See `pom.xml` for specific dependencies

### How to use
1. `git clone https://github.com/BofeiC/JDD.git`

2. run `runner/SearchGadgetChains.main`

## Document


### Configuration item description
- inputPath: test project path
- outputDir: output directory. E.g. IOCDs
- outPutDirName：Name of the folder where IOCDs are stored
- prioritizedGadgetChainLimit: Output N highest prioritized gadget chains
- protocol: currently supports jdk, hessian, json (e.g. jackson, ...).
  - needSerializable: please adjust them together with `protocol`.
    - jdk: needSerializable = true
    - hessian: needSerializable = false or true
    - json: needSerializable = false or true

- sinkRules:
  - available options: classLoad,invoke,jndi,exec,secondDes,custom,file
    - A version that facilitates custom additions and modifications may come online later
    - Some sinks (in custom) that have not been added/tested after refactoring

### Disclaimer
JDD is developed solely for academic research and to advance defensive techniques. It is not intended for unauthorized system attacks.
The developers disclaim any liability for misuse of the software. Please use it responsibly.

The use of JDD for illegal attacks or profit is prohibited.

### Citation
If you use JDD or some of our code logic, or some of the interesting cases found by JDD, please cite our paper as follows:
```
@inproceedings{chen2024efficient,
  title={Efficient Detection of Java Deserialization Gadget Chains via Bottom-up Gadget Search and Dataflow-aided Payload Construction},
  author={Chen, Bofei and Zhang, Lei and Huang, Xinyou and Cao, Yinzhi and Lian, Keke and Zhang, Yuan and Yang, Min},
  booktitle={2024 IEEE Symposium on Security and Privacy (SP)},
  pages={150--150},
  year={2024},
  organization={IEEE Computer Society}
}
```

### Supported Deserialization Protocols
- JDK
- Hessian(e.g. native hessian, sofa-hessian, hessian-lite...)
- Json (use this protocol pattern to detect fragments linked after `Method.invoke`)
- or similar protocols

Some of the fragments detected by JDD can be generalized across different deserialization protocols, e.g., we used JDD to detect a number of exploitable gadget chains in protocols outside the scope of the paper and obtained some new CVEs.

We've recently refactored JDD, resulting in improved performance in some applications. However, some features remain unstable, and we are actively working on fixing them.

### Datasets
- If you need the dataset, please send us an email (bfchen22@m.fudan.edu.cn) with the purpose. Thanks for understanding.

In the email, please include a justification letter (PDF format) on official letterhead. 
The justification letter needs to acknowledge the “JDD” project from Fudan University and clearly state the reason for requesting the dataset. 
Also, confirm that the dataset will not be shared with others without our permission. We emphasize that we will ignore emails that do not follow the above instructions.

### CVEs Assigned
- CVE-2023-29234
- CVE-2023-35839
- CVE-2023-39131
- CVE-2023-48967
- CVE-2024-23636
- CVE-2023-41331
- ...


### A proof-of-concept tool
We also produce a proof-of-concept tool for generating payloads that exploit unsafe Java object deserialization. You can build on this tool to understand payload construction more easily.
This software was created purely for the purpose of academic research and the development of effective defense techniques. It is also forbidden to use it for any illegal attack or profit.
The link is: https://github.com/BofeiC/JDD-PocLearning

### Test Example
The test applications are located in the `testExample` directory. You can change the test application by changing the `inputPath` in the configuration file.

test application example 1: `Groovy`
```
sun.reflect.'annotation'.AnnotationInvocationHandler: void readObject(java.io.ObjectInputStream)
Proxy Map: entrySet()
org.codehaus.groovy.runtime.ConversionHandler: java.lang.Object invoke(java.lang.Object,java.lang.reflect.Method,java.lang.Object[])
org.codehaus.groovy.runtime.ConvertedClosure: java.lang.Object invokeCustom(java.lang.Object,java.lang.reflect.Method,java.lang.Object[])
groovy.lang.Closure: java.lang.Object call(java.lang.Object[])
```
One of unknown gadget chain detected by JDD.
```
java.util.concurrent.ConcurrentHashMap: void readObject(java.io.ObjectInputStream)
groovy.lang.GString: int hashCode()
groovy.lang.GString: java.lang.String toString()
groovy.lang.GString: java.io.Writer writeTo(java.io.Writer)
groovy.lang.Closure: java.lang.Object call()
```
In this application, JDD detected gadget chains that do not require the dynamic proxy feature, which expands the range of protocols that can be attacked. The known gadget chain could only be used in protocols that support dynamic proxies (e.g. JDK, but could not be used in Hessian).


test application example 2: `Vaadin`
Known chain
```
javax.management.BadAttributeValueExpException: void readObject(java.io.ObjectInputStream)
com.vaadin.data.util.PropertysetItem: java.lang.String toString()
com.vaadin.data.util.NestedMethodProperty: java.lang.Object getValue()
java.lang.reflect.Method: java.lang.Object invoke(java.lang.Object,java.lang.Object[])
```
One of unknown gadget chain detected by JDD.
```
java.util.concurrent.ConcurrentHashMap: void readObject(java.io.ObjectInputStream)
java.util.AbstractMap$SimpleEntry: boolean equals(java.lang.Object)
java.util.AbstractMap: boolean access$000(java.lang.Object,java.lang.Object)
java.util.AbstractMap: boolean eq(java.lang.Object,java.lang.Object)
com.sun.org.apache.xpath.internal.objects.XStringForFSB: boolean equals(java.lang.Object)
com.vaadin.data.util.AbstractProperty: java.lang.String toString()
com.vaadin.data.util.LegacyPropertyHelper: java.lang.String legacyPropertyToString(com.vaadin.data.Property)
com.vaadin.data.util.MethodProperty: java.lang.Object getValue()
java.lang.reflect.Method: java.lang.Object invoke(java.lang.Object,java.lang.Object[])
```
