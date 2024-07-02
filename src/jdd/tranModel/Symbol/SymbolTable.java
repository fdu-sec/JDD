package tranModel.Symbol;

import java.util.HashMap;
import java.util.LinkedList;
import java.util.List;

public class SymbolTable {
    public HashMap<String, SymbolRecord> nameMapSymbolRecords = new HashMap<>();

    public SymbolRecord get(String name){
        if(!nameMapSymbolRecords.containsKey(name)) return null;
        return nameMapSymbolRecords.get(name);
    }

    public boolean containsName(String name){
        return nameMapSymbolRecords.containsKey(name);
    }

    public void addEntry(String name, String infoEntry){
        if(!containsName(name)) nameMapSymbolRecords.put(name, new SymbolRecord(name));
        SymbolRecord symbolRecord = get(name);
        symbolRecord.addEntry(infoEntry);
    }

    public List<String> getInfo(String name){
        SymbolRecord symbolRecord = get(name);
        if(symbolRecord == null) return new LinkedList<>();
        // hack: 直接将对象本身返回, 我们信任调用者
        return symbolRecord.info;
    }

    public boolean containsEntry(String name, String infoEntry){
        if(!containsName(name)) return false;
        return get(name).containsEntry(infoEntry);
    }
}
