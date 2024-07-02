package tranModel.Symbol;

import soot.SootMethod;

import java.util.HashMap;
import java.util.List;

public class OverAllSymbolTable {
    HashMap<SootMethod, SymbolTable> methodMapTable = new HashMap<>();

    public boolean containsMethod(SootMethod sootMethod){
        return methodMapTable.containsKey(sootMethod);
    }

    public boolean containsSymbol(SootMethod sootMethod, String symbolName){
        if(!containsMethod(sootMethod)) return false;
        return methodMapTable.get(sootMethod).containsName(symbolName);
    }

    public void addEntry(SootMethod sootMethod, String symbolName, String infoEntry){
        if(!containsMethod(sootMethod)) methodMapTable.put(sootMethod, new SymbolTable());
        SymbolTable symbolTable = methodMapTable.get(sootMethod);
        symbolTable.addEntry(symbolName, infoEntry);
    }

    public List<String> getInfo(SootMethod sootMethod, String symbolName){
        if(!containsMethod(sootMethod)) return null;
        return methodMapTable.get(sootMethod).getInfo(symbolName);
    }

    public boolean containsEntry(SootMethod sootMethod, String symbolName, String infoEntry){
        if(!containsMethod(sootMethod)) return false;
        return methodMapTable.get(sootMethod).containsEntry(symbolName, infoEntry);
    }
}
