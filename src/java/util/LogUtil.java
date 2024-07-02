package util;

import lombok.extern.slf4j.Slf4j;

@Slf4j
public class LogUtil {

    public static void debug(String info){
        if (true)
            log.info(info);
    }

    public static void info(String info){
        log.info(info);
    }

}
