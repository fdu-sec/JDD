package tranModel.Symbol;

import java.util.LinkedList;
import java.util.List;

public class SymbolRecord {
    public String name;
    public List<String> info = new LinkedList<>();

    public SymbolRecord(String name){
        this.name = name;
    }

    public SymbolRecord(String name, String record){
        this.name = name;
        this.info.add(record);
    }

    public boolean containsEntry(String infoEntry){
        for(String s : info){
            if(s.equals(infoEntry)) return true;
        }
        return false;
    }

    public void addEntry(String infoEntry){
        if(containsEntry(infoEntry)) return;
        info.add(infoEntry);
    }
}
