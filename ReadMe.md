## Efficient Detection of Java Deserialization Gadget Chains via Bottom-up Gadget Search and Dataflow-aided Payload Construction
### Publication
Efficient Detection of Java Deserialization Gadget Chains via Bottom-up Gadget Search and Dataflow-aided Payload Construction

B Chen, L Zhang, X Huang, Y Cao, K Lian, Y Zhang, M Yang

IEEE Symposium on Security and Privacy (SP), 2024

### Runtime Environment
JDK 8

Recommended macOS; this project has not been tested on Windows, and feedback indicates that its performance on Windows is unstable.

Dependencies: See `pom.xml` for specific dependencies

### Documents
- [How to use JDD](./document/UsageGuide.md)
- [How to extend JDD](./document/Extend.md)

### Issues
Since the open-source release of JDD, we received some valuable questions and suggestions. Thanks to everyone who shared their thoughts! We’ve compiled and summarized these issues below.
- [Common problems and update logs](./document/Log.md)

Additionally, the current version of JDD still has many areas that could be optimized. We’d love to have experts with program analysis experience join us in further developing JDD. If you have any questions or suggestions, don’t hesitate to reach out directly!

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

We've recently refactored JDD, resulting in improved performance in some applications.

### Supported Dynamic Features
- Polymorphism
- Dynamic proxies (need to switch to dpx branch)
- Reflection

### Datasets (A New Benchmark)
- If you need the dataset, please send us an email (bfchen22@m.fudan.edu.cn) with the purpose. Thanks for understanding.
- You can find the `IOCD` datasets in the `IOCDDatasets` directory.
  The IOCD dataset is an important intermediate component that contains:
  - Gadget chains detected prior to dynamic verification, and 
  - Key constraint information that guide the generation of Injection Objects.
  - *The number of IOCDs is usually smaller than the number of gadget chains shown in DetectedGadgetChains.txt. This is because JDD performs a more precise taint analysis during the IOCD generation process, which eliminates some false positives.*

In the email, please include a justification letter (PDF format) on official letterhead. 
The justification letter needs to acknowledge the “JDD” project from Fudan University and clearly state the reason for requesting the dataset. 
Also, confirm that the dataset will not be shared with others without our permission. We emphasize that we will ignore emails that do not follow the above instructions.



### A proof-of-concept tool
We also produce a proof-of-concept tool for generating payloads that exploit unsafe Java object deserialization. You can build on this tool to understand payload construction more easily.
This software was created purely for the purpose of academic research and the development of effective defense techniques. It is also forbidden to use it for any illegal attack or profit.
The link is: https://github.com/BofeiC/JDD-PocLearning
