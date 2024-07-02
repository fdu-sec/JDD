package DefaultDetector;

/**
 * 方法描述的接口，特定场景的方法描述可以选择实现该接口
 */
public interface IMethodDescriptor {
    boolean isCompletelyDescribed();
    void forceSetDescribed();

    /**
     * 用来限制调用栈层数
     */
    class BaseStateFlag{
        public int distance;
        public boolean flag;

        public BaseStateFlag(){
            distance = Integer.MAX_VALUE;
            flag = false;
        }

        public boolean isTrue(){
            return flag;
        }

        public void setTrue(){
            flag = true;
        }

        public int getDistance(){
            return distance;
        }

        public boolean updateDistance(BaseStateFlag calleeFlag){
            if(calleeFlag.distance == Integer.MAX_VALUE) return false;
            if(calleeFlag.distance + 1 < this.distance){
                this.distance = calleeFlag.distance + 1;
                return true;
            }
            return false;
        }
    }
}
