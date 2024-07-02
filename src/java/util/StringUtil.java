package util;

import java.util.*;
import java.util.regex.Matcher;
import java.util.regex.Pattern;

public class StringUtil {


    public static boolean isMatch(String str, String reg) {
        Pattern pattern = Pattern.compile(reg);
        Matcher matcher = pattern.matcher(str);
        return matcher.matches();
    }

    public static boolean isFind(String str,String reg){
        Pattern pattern=Pattern.compile(reg);
        Matcher matcher=pattern.matcher(str);
        return  matcher.find();
    }

    public static int getParameterOrder(String input) {
        String[] str = input.split(":=")[1].split(":");
        Pattern pattern = Pattern.compile("[^0-9]");
        Matcher matcher = pattern.matcher(str[0]);
        return Integer.parseInt(matcher.replaceAll(""));
    }

    public static String insertDot(String str) {
        List<String> insertMark= Arrays.asList(".","$","[","]","(",")");
            StringBuilder stringBuilder=new StringBuilder();
            for(int i=0;i<str.length();i++){
                if(insertMark.contains(str.substring(i,i+1)))//如果是分割符，我们就
                    stringBuilder.append("\\");
                stringBuilder.append(str.substring(i,i+1));
            }
            str=stringBuilder.toString();
        return str;
    }

    /**
     * @classDef: E.g., class "Lcom/android/server/notification/EventConditionProvider;"
     * */
    public static String parseClassNameFromUnit(String classDef){
        if (classDef.contains("\"L")){
            classDef = classDef.substring(classDef.indexOf("\"L")+2,classDef.indexOf(";"));
            classDef = classDef.replaceAll("/",".");
            return classDef;
        }else {
            return null;
        }

    }

    public static String whiteSpaces(int n){
        if(n == 0)return "";
        return String.format("%" + n + "s", "");
    }

    public static boolean containsAnySubstringInCollection(String s, Collection<String> set){
        for(String str : set){
            if(s.contains(str)) return true;
        }
        return false;
    }

    public static boolean containsAnySubstringInCollectionLowercase(String s, Collection<String> set){
        for(String str : set){
            if(s.toLowerCase(Locale.ROOT).contains(str)) return true;
        }
        return false;
    }

    public static boolean substringOfAnyInCollection(String s, Collection<String> set){
        for(String str : set){
            if(str.contains(s)) return true;
        }
        return false;
    }

    public static boolean setEqual(Collection<String> s1, Collection<String> s2){
        for(String object1 : s1){
            if(!s2.contains(object1)) return false;
        }
        for(String object2 : s2){
            if(!s1.contains(object2)) return false;
        }
        return true;
    }

    public static List<String> setSubtract(Collection<String> s1, Collection<String> s2){
        List<String> res = new ArrayList<>();
        for(String object1 : s1){
            if(!s2.contains(object1)) res.add(object1);
        }
        return res;
    }

    // String Util

    public static String formatQuotation(String raw){
        if(raw.length() >= 2 && raw.endsWith("\"") && raw.startsWith("\"")) return raw.substring(1, raw.length() - 1);
        return raw;
    }

    public static String goodTrim(String raw){
        return raw.replaceAll("\\s+", " ").trim();
    }

}
