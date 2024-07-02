package util;

import java.util.HashSet;
import java.util.Random;
import java.util.Set;

public class Util {
    public static boolean isStandardLibrary(String methodSignature) {//判断是不是标准库的方法
        if (methodSignature.startsWith("java") || methodSignature.startsWith("android") || methodSignature.startsWith("androidx") || methodSignature.startsWith("kotlin"))
            return true;
        return false;
    }

    public static Set<Integer> random(int low,int high,int size){//获取指定范围的指定个数的不同数字
        HashSet<Integer>  set=new HashSet<>();
        Random rand=new Random();
        while (set.size()<size){
            int num = rand.nextInt();
            if(num>=low&&num<high){
                set.add(num);
            }
        }
        return set;
    }
}
