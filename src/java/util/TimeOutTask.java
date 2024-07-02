package util;

import lombok.extern.slf4j.Slf4j;

import java.util.ConcurrentModificationException;
import java.util.Random;
import java.util.concurrent.*;

@Slf4j
public abstract class TimeOutTask {
    private ExecutorService executorService= Executors.newFixedThreadPool(Runtime.getRuntime().availableProcessors()*2);

    public void run(int timeoutSeconds) {
        Future<String> future = executorService.submit(new Callable<String>() {
            @Override
            public String call() throws Exception {
                task();
                return  "OK";
            }
        });
        try {
            String result = future.get(timeoutSeconds, TimeUnit.SECONDS);
        } catch (TimeoutException e) {
            future.cancel(true);
            log.error("TimeOutTask: TimeOut");
            timeoutHandler();
        } catch (ExecutionException e){
            log.error("TimeOutTask ExecutionException:" + e.getMessage());
            e.printStackTrace();
        } catch (Exception e){
            e.printStackTrace();
            log.error("TimeOutTask:" + e.getMessage());
        }
        executorService.shutdown();
    }

    protected abstract void task() throws Exception;

    protected void timeoutHandler(){};

}

@Slf4j
class Demo{
    public static void main(String[] args) {
        new TimeOutTask() {
            @Override
            protected void task() {
                try {
                    TimeUnit.SECONDS.sleep(10);
                    log.info("finish");
                } catch (InterruptedException e) {
                    log.info("任务被中断");
                }
            }

            @Override
            protected void timeoutHandler(){
                log.info("回收资源");
            }
        }.run(5);
    }
}

