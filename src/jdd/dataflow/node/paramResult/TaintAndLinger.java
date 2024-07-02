package dataflow.node.paramResult;

public class TaintAndLinger {
    int TaintParam;//使用状态压缩

    @Override
    public String toString(){
        String s = Integer.toString(TaintParam) ;
        return s;
    }

    public TaintAndLinger(int TaintParam){
        this.TaintParam = TaintParam;
    }

    @Override
    public boolean equals(Object o){
        TaintAndLinger a = (TaintAndLinger) o;

        return (this.TaintParam == a.TaintParam);
    }

    @Override
    public int hashCode(){
        return Integer.hashCode(TaintParam);
    }
}
