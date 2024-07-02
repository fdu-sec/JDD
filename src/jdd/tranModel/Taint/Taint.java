package tranModel.Taint;

import soot.SootField;
import soot.Type;
import soot.Value;

import java.util.HashSet;
import java.util.LinkedList;

public class Taint{
    public Value object; // 被污染的对象
    public LinkedList<SootField> accessPath = new LinkedList<>(); // a.b -> b.c -> c.d  a.b.c.d->[b,c,d]如果accessPath.size为0，则整个对象被污染
    public HashSet<Taint> aliases = new HashSet<>();

    // 返回null表示不匹配，返回空list表示匹配到object自身的taint
    // 用来查找b.field会带来的污点， b本身会带来的污点很容易找，只需要比较object即可
    public LinkedList<SootField> match(Value object, SootField field){
        if(object.equals(this.object)){
            if(accessPath.isEmpty()) return new LinkedList<>();
            if(accessPath.get(0).equals(field)){ // ToDo: get(0)?
                LinkedList<SootField> subList = new LinkedList<>();
                for(int ind = 1; ind < accessPath.size(); ind++) subList.add(accessPath.get(ind));
                return subList;
            }
        }
        return null;
    }

    // 判断一个taint 是否为本身 / 本身更细划分字段
    public boolean match(Taint taint){
        if (taint.object != this.object) return false;
        if (taint.accessPath.size() < this.accessPath.size())
            return false;

        // TODO: 为什么是 ++ind
        for (Integer ind = 0; ind <this.accessPath.size(); ++ind){
            if (!this.accessPath.get(ind).equals(taint.accessPath.get(ind)))
                return false;
        }

        return true;
    }

    public Taint(Value object, LinkedList<SootField> accessPath){
        this.object = object;
        this.accessPath = accessPath;
    }

    public Taint(Value object){
        this.object = object;
        this.accessPath = new LinkedList<>();
    }

    @Override
    public int hashCode() {
        if(this.object == null || this.accessPath == null) return 123;
        return this.object.hashCode() + this.accessPath.size() * 113;
    }

    @Override
    public boolean equals(Object obj) {
        if(! (obj instanceof Taint)) return false;
        Taint taint = (Taint) obj;
        if((taint.object == null && this.object == null) || (taint.object != null && taint.object.equals(this.object))){
            if(this.accessPath.size() == taint.accessPath.size()){
                for(int ind = 0; ind < this.accessPath.size(); ind++){
                    if(!this.accessPath.get(ind).equals(taint.accessPath.get(ind))) return false;
                }
                return true;
            }
        }
        return false;
    }

    public Type getType(){
        if (object == null)
            return null;
        if (accessPath.isEmpty())
            return object.getType();
        return accessPath.getLast().getType();
    }

    public static void addTaint(Taint taint, HashSet<Taint> set){
        if (taint != null)
            set.add(taint);
    }

    public static void addTaint(HashSet<Taint> taints, HashSet<Taint> set){
        for (Taint taint: taints) {
            if (taint != null)
                set.add(taint);
        }
    }


    @Override
    public String toString(){
        return " [" + object + "  " + accessPath + "] ";
    }
}
