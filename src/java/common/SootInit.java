package common;

import soot.G;
import soot.JastAddJ.Opt;
import soot.PackManager;
import soot.Scene;
import soot.options.Options;

import java.io.File;
import java.nio.file.Paths;
import java.util.ArrayList;
import java.util.Collections;

public class SootInit {
    public static void setSoot(String apkPath,String androidJar,String outputDir) {
        G.reset();
        Options.v().set_prepend_classpath(false);
//        Options.v().set_validate(true);
        Options.v().set_allow_phantom_refs(true);
        Options.v().set_whole_program(true);
        Options.v().set_process_multiple_dex(true);
        Options.v().set_include_all(true);

        Options.v().set_android_jars(androidJar);

        Options.v().set_src_prec(Options.src_prec_apk);
        Options.v().set_process_dir(Collections.singletonList(apkPath));
        Options.v().set_output_format(Options.output_format_jimple);
        Options.v().set_output_dir(outputDir);

        Scene.v().loadNecessaryClasses();
    }

}
