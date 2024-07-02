package util;

import lombok.extern.slf4j.Slf4j;

@Slf4j
public class TimeMeasurement {
    private static long startTime;
    private long gadgetStartTime;
    private long gadgetEndTime;
    private String gadgetSignature;

    //private long endTime;
    public static void begin() {
        startTime = System.currentTimeMillis();
    }
    public static void show(String tag) {
        log.info("TIME_MEASURE_TAG"+" "+tag+" : "+
                ( System.currentTimeMillis()- startTime)/(1000*60)+" mins "+
                ( System.currentTimeMillis()- startTime)%(1000*60)/1000+" seconds");
    }
    public static String currentTime(){
        return ( System.currentTimeMillis()- startTime)/(1000*60)+" mins "+
                ( System.currentTimeMillis()- startTime)%(1000*60)/1000+" seconds";
    }
    public void gadgetStart() {
        gadgetStartTime = System.currentTimeMillis();
    }
    public void gadgetStart(String gadgetSignature) {
        this.gadgetSignature = gadgetSignature;
        gadgetStartTime = System.currentTimeMillis();
    }
    public void gadgetEnd() {
        gadgetEndTime = System.currentTimeMillis();
    }
    public String gadgetCount() {
        return ( gadgetEndTime - gadgetStartTime)/(1000*60)+" mins "+
                ( gadgetEndTime - gadgetStartTime)%(1000*60)/1000+" seconds";
    }

}
