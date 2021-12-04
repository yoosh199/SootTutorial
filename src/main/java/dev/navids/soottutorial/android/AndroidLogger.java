package dev.navids.soottutorial.android;

import soot.*;
import soot.jimple.*;

import java.io.File;
import java.util.ArrayList;
import java.util.Arrays;
import java.util.List;
import java.util.Map;


public class AndroidLogger {

    private final static String USER_HOME = System.getProperty("user.home");
    private static String androidJar = USER_HOME + "/Library/Android/sdk/platforms";
    static String androidDemoPath = System.getProperty("user.dir") + File.separator + "demo" + File.separator + "Android";
    static String apkPath = androidDemoPath + File.separator + "/app-debug.apk";
    static String outputPath = androidDemoPath + File.separator + "/Instrumented";


    public static void main(String[] args){
  
        if(System.getenv().containsKey("ANDROID_HOME"))
            androidJar = System.getenv("ANDROID_HOME")+ File.separator+"platforms";
        // Clean the outputPath
        final File[] files = (new File(outputPath)).listFiles();
        if (files != null && files.length > 0) {
            Arrays.asList(files).forEach(File::delete);
        }
        // Initialize Soot
        InstrumentUtil.setupSoot(androidJar, apkPath, outputPath);
      

        // Add a transformation pack in order to add the statement "System.out.println(<content>) at the beginning of each Application method
        PackManager.v().getPack("jtp").add(new Transform("jtp.myLogger", new BodyTransformer() {
            
            protected void internalTransform(Body b, String phaseName, Map<String, String> options) {
         
                if(AndroidUtil.isAndroidMethod(b.getMethod()))
                    return;
                JimpleBody body = (JimpleBody) b;
                UnitPatchingChain units = b.getUnits();
         
                List<Unit> generatedUnits = new ArrayList<>();
                     
                    if(body.getMethod().getSignature().equals("<com.example.paintbrush.Draws: void onCreate(android.os.Bundle)>")){

                    
                        Local MyApplicationLocal = InstrumentUtil.generateNewLocal(body, RefType.v("android.app.Application"));
                        Local counterLocal = InstrumentUtil.generateNewLocal(body, IntType.v());
                        Local globalTreeLocal = InstrumentUtil.generateNewLocal(body, RefType.v("com.example.paintbrush.GlobalTree"));
                        Local viewLocal =InstrumentUtil.generateNewLocal(body, RefType.v("android.view.View"));

                        SootMethod getApplicationMethod = Scene.v().getMethod("<android.app.Activity: android.app.Application getApplication()>");

                        SootMethod getGlobalViewMethod = Scene.v().getMethod("<com.example.paintbrush.GlobalTree: android.view.View getGlobalTreeView()>");
                        SootMethod setContentViewMethod = Scene.v().getMethod("<android.app.Activity: void setContentView(android.view.View)>");

                        VirtualInvokeExpr getApplicationMethodVirtualInvokeExpr = Jimple.v().newVirtualInvokeExpr(body.getLocals().getFirst(),getApplicationMethod.makeRef());

                        generatedUnits.add(Jimple.v().newAssignStmt(MyApplicationLocal, getApplicationMethodVirtualInvokeExpr));

                        CastExpr globalTreeLocalCasting = Jimple.v().newCastExpr(MyApplicationLocal,RefType.v("com.example.paintbrush.GlobalTree"));
                        generatedUnits.add(Jimple.v().newAssignStmt(globalTreeLocal, globalTreeLocalCasting));

                        VirtualInvokeExpr getGlobalViewMethodVirtualInvokeExpr = Jimple.v().newVirtualInvokeExpr(globalTreeLocal,getGlobalViewMethod.makeRef());
                        generatedUnits.add(Jimple.v().newAssignStmt(viewLocal, getGlobalViewMethodVirtualInvokeExpr));

                        VirtualInvokeExpr setContentViewVirtualInvokeExpr = Jimple.v().newVirtualInvokeExpr(body.getLocals().getFirst(),setContentViewMethod.makeRef(),viewLocal);

                        generatedUnits.add(Jimple.v().newInvokeStmt(setContentViewVirtualInvokeExpr));


                        
               
             
                 

                        
                        units.insertBefore(generatedUnits, body.getFirstNonIdentityStmt());
                   
                        b.validate();
                 
                    }
                   
                  
              
                   
   
                
                
            }
        }));
        // Run Soot packs (note that our transformer pack is added to the phase "jtp")
        PackManager.v().runPacks();
        // Write the result of packs in outputPath
        PackManager.v().writeOutput();
    }
}