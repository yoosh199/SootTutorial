package dev.navids.soottutorial.android;

import soot.*;
import soot.jimple.*;

import java.io.File;
import java.util.ArrayList;
import java.util.Arrays;
import java.util.List;
import java.util.Map;

public class AndroidUiDistribution {

        private final static String USER_HOME = System.getProperty("user.home");
        private static String androidJar = USER_HOME + "/Library/Android/sdk/platforms";
        static String androidDemoPath = System.getProperty("user.dir") + File.separator + "demo" + File.separator
                        + "Android";
        // static String apkPath = androidDemoPath + File.separator + "/calc.apk";
        static String apkPath = androidDemoPath + File.separator + "/app-debug.apk";
        static String outputPath = androidDemoPath + File.separator + "/Instrumented";
        static String uiMovedActivity = "NewUIActivity";
        static String applicationName = "ApplicationName";
        static String moveButton = "move_btn";
        static String removeView = "remove_layout"; 

        public static void main(String[] args) {

                if (System.getenv().containsKey("ANDROID_HOME"))
                        androidJar = System.getenv("ANDROID_HOME") + File.separator + "platforms";
                // Clean the outputPath
                final File[] files = (new File(outputPath)).listFiles();
                if (files != null && files.length > 0) {
                        Arrays.asList(files).forEach(File::delete);
                }
                // Initialize Soot
                InstrumentUtil.setupSoot(androidJar, apkPath, outputPath);
                // Add a transformation pack in order to add the statement
                // "System.out.println(<content>) at the beginning of each Application method
                String packageName = AndroidUtil.getPackageName(apkPath);

                addApplicationMethod();

                SootClass injectedClass = createInjectedClickListenerClass(packageName);
                addSootField(injectedClass);
                addDefaultConstructor(injectedClass);
                SootMethod method = addOnClickMethod(injectedClass);
                PackManager.v().getPack("jtp").add(new Transform("jtp.myLogger", new BodyTransformer() {

                        @Override
                        protected void internalTransform(Body b, String phaseName, Map<String, String> options) {
                                if (AndroidUtil.isAndroidMethod(b.getMethod()))
                                        return;
                                JimpleBody body = (JimpleBody) b;
                                UnitPatchingChain units = b.getUnits();

                                List<Unit> generated = new ArrayList<>();
                                // if (body.getMethod().getSignature().equals(
                                // "<com.example.paintbrush.InjectedClickListener: void
                                // onCreate(android.os.Bundle)>")) {
                                // System.out.println(body);

                                // }
                                SootMethod method = b.getMethod();
                                SootClass clazz = method.getDeclaringClass();
                                if (clazz.getName().equals("com.example.paintbrush." + applicationName)) {

                                }

                                List<Unit> generatedUnits1 = new ArrayList<>();

                                // if (body.getMethod().getSignature().equals(
                                // "<com.example.paintbrush." + uiMovedActivity
                                // + ": void onCreate(android.os.Bundle)>")) {

                                // }

                                if (body.getMethod().getSignature().equals(
                                                "<com.example.paintbrush." + uiMovedActivity
                                                                + ": void onCreate(android.os.Bundle)>")) {

                                        Local MyApplicationLocal = InstrumentUtil.generateNewLocal(body,
                                                        RefType.v("android.app.Application"));
                                        Local counterLocal = InstrumentUtil.generateNewLocal(body, IntType.v());
                                        Local globalTreeLocal = InstrumentUtil.generateNewLocal(body,
                                                        RefType.v("com.example.paintbrush." + applicationName));
                                        Local viewLocal = InstrumentUtil.generateNewLocal(body,
                                                        RefType.v("android.view.View"));

                                        SootMethod getApplicationMethod = Scene.v().getMethod(
                                                        "<android.app.Activity: android.app.Application getApplication()>");

                                        SootMethod getGlobalViewMethod = Scene.v().getMethod(
                                                        "<com.example.paintbrush." + applicationName
                                                                        + ": android.view.View getGlobalTreeView()>");
                                        SootMethod setContentViewMethod = Scene.v().getMethod(
                                                        "<android.app.Activity: void setContentView(android.view.View)>");

                                        VirtualInvokeExpr getApplicationMethodVirtualInvokeExpr = Jimple.v()
                                                        .newVirtualInvokeExpr(body.getLocals().getFirst(),
                                                                        getApplicationMethod.makeRef());

                                        generatedUnits1.add(Jimple.v().newAssignStmt(MyApplicationLocal,
                                                        getApplicationMethodVirtualInvokeExpr));

                                        CastExpr globalTreeLocalCasting = Jimple.v().newCastExpr(MyApplicationLocal,
                                                        RefType.v("com.example.paintbrush." + applicationName));
                                        generatedUnits1.add(Jimple.v().newAssignStmt(globalTreeLocal,
                                                        globalTreeLocalCasting));

                                        VirtualInvokeExpr getGlobalViewMethodVirtualInvokeExpr = Jimple.v()
                                                        .newVirtualInvokeExpr(globalTreeLocal,
                                                                        getGlobalViewMethod.makeRef());
                                        generatedUnits1.add(Jimple.v().newAssignStmt(viewLocal,
                                                        getGlobalViewMethodVirtualInvokeExpr));

                                        VirtualInvokeExpr setContentViewVirtualInvokeExpr = Jimple.v()
                                                        .newVirtualInvokeExpr(body.getLocals().getFirst(),
                                                                        setContentViewMethod.makeRef(), viewLocal);

                                        generatedUnits1.add(Jimple.v().newInvokeStmt(setContentViewVirtualInvokeExpr));

                                        units.insertBefore(generatedUnits1, body.getFirstNonIdentityStmt());

                                        b.validate();

                                }

                                if (method.getSignature().equals(
                                                "<com.example.paintbrush.MainActivity: void onCreate(android.os.Bundle)>")) {

                                        Local thisLocal = null;
                                        for (Unit u : units) {
                                                if (u instanceof IdentityStmt) {
                                                        IdentityStmt ids = (IdentityStmt) u;
                                                        if (ids.getRightOp() instanceof ThisRef) {
                                                                thisLocal = (Local) ids.getLeftOp();
                                                                break;
                                                        }
                                                }
                                        }

                                        if (thisLocal == null)
                                                return;

                                        List<Unit> generatedUnits = new ArrayList<>();

                                        // InjectedClickListener333 클래스 가져오기
                                        SootClass injectedClass = Scene.v()
                                                        .getSootClass("com.example.paintbrush.InjectedClickListener");
                                        RefType injectedType = injectedClass.getType();

                                        // local들
                                        Local moveBtnLocal = InstrumentUtil.generateNewLocal(
                                                        body,
                                                        RefType.v("android.widget.Button"));

                                        Local removeLayoutLocal = InstrumentUtil.generateNewLocal(
                                                        body,
                                                        RefType.v("android.view.View"));

                                        Local listenerLocal = InstrumentUtil.generateNewLocal(
                                                        body,
                                                        injectedType);

                                        // 필요한 method ref
                                        SootMethod listenerInitMethod = injectedClass.getMethod(
                                                        "void <init>(android.view.View,android.app.Activity)");

                                        SootMethod setOnClickListenerMethod = Scene.v().getMethod(
                                                        "<android.view.View: void setOnClickListener(android.view.View$OnClickListener)>");

                                        // MainActivity 필드들
                
                                        SootField moveBtnField = Scene.v().getField(
                                                        "<com.example.paintbrush.MainActivity: android.widget.Button "+moveButton+">");

                                        SootField removeLayoutField = Scene.v().getField(
                                                        "<com.example.paintbrush.MainActivity: android.view.View "
                                                                        + removeView + ">");

                                        // 1) moveBtnLocal = this.move_btn
                                        generatedUnits.add(
                                                        Jimple.v().newAssignStmt(
                                                                        moveBtnLocal,
                                                                        Jimple.v().newInstanceFieldRef(
                                                                                        thisLocal,
                                                                                        moveBtnField.makeRef())));

                                        // 2) removeLayoutLocal = this.remove_layout
                                        generatedUnits.add(
                                                        Jimple.v().newAssignStmt(
                                                                        removeLayoutLocal,
                                                                        Jimple.v().newInstanceFieldRef(
                                                                                        thisLocal,
                                                                                        removeLayoutField.makeRef())));

                                        // 3) listenerLocal = new InjectedClickListener
                                        generatedUnits.add(
                                                        Jimple.v().newAssignStmt(
                                                                        listenerLocal,
                                                                        Jimple.v().newNewExpr(injectedType)));

                                        // 4) specialinvoke listenerLocal.<init>(removeLayoutLocal, thisLocal)
                                        generatedUnits.add(
                                                        Jimple.v().newInvokeStmt(
                                                                        Jimple.v().newSpecialInvokeExpr(
                                                                                        listenerLocal,
                                                                                        listenerInitMethod.makeRef(),
                                                                                        removeLayoutLocal,
                                                                                        thisLocal)));

                                        // 5) moveBtnLocal.setOnClickListener(listenerLocal)
                                        generatedUnits.add(
                                                        Jimple.v().newInvokeStmt(
                                                                        Jimple.v().newVirtualInvokeExpr(
                                                                                        moveBtnLocal,
                                                                                        setOnClickListenerMethod
                                                                                                        .makeRef(),
                                                                                        listenerLocal)));

                                        // 삽입 위치: return 직전
                                        Unit insertPoint = null;
                                        for (Unit u : units) {
                                                if (u instanceof ReturnVoidStmt) {
                                                        insertPoint = u;
                                                        break;
                                                }
                                        }

                                        if (insertPoint != null) {
                                                units.insertBefore(generatedUnits, insertPoint);
                                        }

                                        body.validate();
                                        return;
                                }

                        }

                }));

                // Run Soot packs (note that our transformer pack is added to the phase "jtp")
                PackManager.v().runPacks();
                // Write the result of packs in outputPath
                PackManager.v().writeOutput();
        }

        static SootClass createInjectedClickListenerClass(String packageName) {
                String className = packageName + ".InjectedClickListener";
                // System.out.println(className);

                SootClass listenerClass = new SootClass(className, Modifier.PUBLIC);
                listenerClass.setSuperclass(Scene.v().getSootClass("java.lang.Object"));

                // implements android.view.View$OnClickListener
                listenerClass.addInterface(Scene.v().getSootClass("android.view.View$OnClickListener"));

                listenerClass.setApplicationClass();
                // Scene.v().addClass(listenerClass);
                return listenerClass;
        }

        static void addApplicationMethod() {

                // 1. Field 추가
                SootClass globalTreeClass = Scene.v()
                                .getSootClass("com.example.paintbrush." + applicationName);

                SootField globalTreeViewField = new SootField(
                                "globalTreeView",
                                RefType.v("android.view.View"),
                                Modifier.PRIVATE);

                globalTreeClass.addField(globalTreeViewField);

                SootMethod getMethod = new SootMethod(
                                "getGlobalTreeView",
                                new ArrayList<>(),
                                RefType.v("android.view.View"),
                                Modifier.PUBLIC);

                globalTreeClass.addMethod(getMethod);

                // 2. getGlobalTreeView() 생성

                JimpleBody body_application = Jimple.v().newBody(getMethod);
                getMethod.setActiveBody(body_application);

                Local thisLocal = Jimple.v().newLocal("r0", RefType.v(globalTreeClass));
                body_application.getLocals().add(thisLocal);

                UnitPatchingChain units_application = body_application.getUnits();

                units_application.add(Jimple.v().newIdentityStmt(
                                thisLocal,
                                Jimple.v().newThisRef(RefType.v(globalTreeClass))));

                Local fieldLocal = Jimple.v().newLocal("r1", RefType.v("android.view.View"));
                body_application.getLocals().add(fieldLocal);

                units_application.add(Jimple.v().newAssignStmt(
                                fieldLocal,
                                Jimple.v().newInstanceFieldRef(
                                                thisLocal,
                                                globalTreeViewField.makeRef())));

                units_application.add(Jimple.v().newReturnStmt(fieldLocal));

                // 3. setGlobalTreeView(View) 생성
                List<Type> params = new ArrayList<>();
                params.add(RefType.v("android.view.View"));

                SootMethod setMethod = new SootMethod(
                                "setGlobalTreeView",
                                params,
                                VoidType.v(),
                                Modifier.PUBLIC);

                globalTreeClass.addMethod(setMethod);

                JimpleBody body_app2 = Jimple.v().newBody(setMethod);
                setMethod.setActiveBody(body_app2);

                Local thisLocal_app2 = Jimple.v().newLocal("r0", RefType.v(globalTreeClass));
                Local paramLocal = Jimple.v().newLocal("r1", RefType.v("android.view.View"));

                body_app2.getLocals().add(thisLocal_app2);
                body_app2.getLocals().add(paramLocal);

                UnitPatchingChain units_app2 = body_app2.getUnits();

                units_app2.add(Jimple.v().newIdentityStmt(
                                thisLocal_app2,
                                Jimple.v().newThisRef(RefType.v(globalTreeClass))));

                units_app2.add(Jimple.v().newIdentityStmt(
                                paramLocal,
                                Jimple.v().newParameterRef(
                                                RefType.v("android.view.View"),
                                                0)));

                units_app2.add(Jimple.v().newAssignStmt(
                                Jimple.v().newInstanceFieldRef(
                                                thisLocal_app2,
                                                globalTreeViewField.makeRef()),
                                paramLocal));

                units_app2.add(Jimple.v().newReturnVoidStmt());

        }

        static void addSootField(SootClass listenerClass) {
                SootField activityField = new SootField("activity", RefType.v("android.app.Activity"), Modifier.PUBLIC);

                SootField removeLayoutField = new SootField(removeView, RefType.v("android.view.View"),
                                Modifier.PUBLIC);

                listenerClass.addField(activityField);
                listenerClass.addField(removeLayoutField);

        }

        static SootMethod addOnClickMethod(SootClass clazz) {
                List<Type> params = new ArrayList<>();
                params.add(RefType.v("android.view.View"));

                SootMethod onClickMethod = new SootMethod(
                                "onClick",
                                params,
                                VoidType.v(),
                                Modifier.PUBLIC);
                clazz.addMethod(onClickMethod);

                JimpleBody body = Jimple.v().newBody(onClickMethod);
                onClickMethod.setActiveBody(body);

                Local thisLocal = Jimple.v().newLocal("r0", RefType.v(clazz.getName()));
                Local viewParamLocal = Jimple.v().newLocal("r1", RefType.v("android.view.View"));
                Local activityLocal = Jimple.v().newLocal("r2", RefType.v("android.app.Activity"));
                Local appLocal = Jimple.v().newLocal("r3", RefType.v("android.app.Application"));
                Local globalTreeLocal = Jimple.v().newLocal("r4",
                                RefType.v("com.example.paintbrush." + applicationName));
                Local removeLayoutLocal = Jimple.v().newLocal("r5", RefType.v("android.view.View"));
                Local parentLocal = Jimple.v().newLocal("r6", RefType.v("android.view.ViewParent"));
                Local viewGroupLocal = Jimple.v().newLocal("r7", RefType.v("android.view.ViewGroup"));
                Local isViewGroupLocal = Jimple.v().newLocal("r8", IntType.v());
                Local intentLocal = Jimple.v().newLocal("r9", RefType.v("android.content.Intent"));

                body.getLocals().add(thisLocal);
                body.getLocals().add(viewParamLocal);
                body.getLocals().add(activityLocal);
                body.getLocals().add(appLocal);
                body.getLocals().add(globalTreeLocal);
                body.getLocals().add(removeLayoutLocal);
                body.getLocals().add(parentLocal);
                body.getLocals().add(viewGroupLocal);
                body.getLocals().add(isViewGroupLocal);
                body.getLocals().add(intentLocal);

                UnitPatchingChain units = body.getUnits();

                // r0 := @this
                units.add(Jimple.v().newIdentityStmt(
                                thisLocal,
                                Jimple.v().newThisRef(RefType.v(clazz.getName()))));

                // r1 := @parameter0
                units.add(Jimple.v().newIdentityStmt(
                                viewParamLocal,
                                Jimple.v().newParameterRef(RefType.v("android.view.View"), 0)));

                SootField activityField = clazz.getFieldByName("activity");
                SootField removeLayoutField = clazz.getFieldByName(removeView);

                SootMethod getApplicationMethod = Scene.v().getMethod(
                                "<android.app.Activity: android.app.Application getApplication()>");

                SootMethod setGlobalTreeViewMethod = Scene.v().getMethod(
                                "<com.example.paintbrush." + applicationName
                                                + ": void setGlobalTreeView(android.view.View)>");

                SootMethod getParentMethod = Scene.v().getMethod(
                                "<android.view.View: android.view.ViewParent getParent()>");

                SootMethod removeViewMethod = Scene.v().getMethod(
                                "<android.view.ViewGroup: void removeView(android.view.View)>");

                SootMethod intentInitMethod = Scene.v().getMethod(
                                "<android.content.Intent: void <init>(android.content.Context,java.lang.Class)>");

                SootMethod addFlagsMethod = Scene.v().getMethod(
                                "<android.content.Intent: android.content.Intent addFlags(int)>");

                SootMethod startActivityMethod = Scene.v().getMethod(
                                "<android.app.Activity: void startActivity(android.content.Intent)>");

                // r2 = this.activity
                units.add(Jimple.v().newAssignStmt(
                                activityLocal,
                                Jimple.v().newInstanceFieldRef(thisLocal, activityField.makeRef())));

                // r3 = r2.getApplication()
                units.add(Jimple.v().newAssignStmt(
                                appLocal,
                                Jimple.v().newVirtualInvokeExpr(
                                                activityLocal,
                                                getApplicationMethod.makeRef())));

                // r4 = (GlobalTree) r3
                units.add(Jimple.v().newAssignStmt(
                                globalTreeLocal,
                                Jimple.v().newCastExpr(appLocal,
                                                RefType.v("com.example.paintbrush." + applicationName))));

                // r5 = this.remove_layout
                units.add(Jimple.v().newAssignStmt(
                                removeLayoutLocal,
                                Jimple.v().newInstanceFieldRef(thisLocal, removeLayoutField.makeRef())));

                // r4.setGlobalTreeView(r5)
                units.add(Jimple.v().newInvokeStmt(
                                Jimple.v().newVirtualInvokeExpr(
                                                globalTreeLocal,
                                                setGlobalTreeViewMethod.makeRef(),
                                                removeLayoutLocal)));

                // r6 = r5.getParent()
                units.add(Jimple.v().newAssignStmt(
                                parentLocal,
                                Jimple.v().newVirtualInvokeExpr(
                                                removeLayoutLocal,
                                                getParentMethod.makeRef())));

                Unit skipRemove = Jimple.v().newNopStmt();

                // r8 = r6 instanceof android.view.ViewGroup
                units.add(Jimple.v().newAssignStmt(
                                isViewGroupLocal,
                                Jimple.v().newInstanceOfExpr(parentLocal, RefType.v("android.view.ViewGroup"))));

                // if r8 == 0 goto skipRemove
                units.add(Jimple.v().newIfStmt(
                                Jimple.v().newEqExpr(isViewGroupLocal, IntConstant.v(0)),
                                skipRemove));

                // r7 = (ViewGroup) r6
                units.add(Jimple.v().newAssignStmt(
                                viewGroupLocal,
                                Jimple.v().newCastExpr(parentLocal, RefType.v("android.view.ViewGroup"))));

                // r7.removeView(r5)
                units.add(Jimple.v().newInvokeStmt(
                                Jimple.v().newVirtualInvokeExpr(
                                                viewGroupLocal,
                                                removeViewMethod.makeRef(),
                                                removeLayoutLocal)));

                units.add(skipRemove);

                // r9 = new Intent
                units.add(Jimple.v().newAssignStmt(
                                intentLocal,
                                Jimple.v().newNewExpr(RefType.v("android.content.Intent"))));

                // specialinvoke r9.<init>(r2, Draws.class)
                units.add(Jimple.v().newInvokeStmt(
                                Jimple.v().newSpecialInvokeExpr(
                                                intentLocal,
                                                intentInitMethod.makeRef(),
                                                activityLocal,
                                                ClassConstant.v("Lcom/example/paintbrush/" + uiMovedActivity + ";"))));

                // r9 = r9.addFlags(0x18001000)
                units.add(Jimple.v().newAssignStmt(
                                intentLocal,
                                Jimple.v().newVirtualInvokeExpr(
                                                intentLocal,
                                                addFlagsMethod.makeRef(),
                                                IntConstant.v(0x18001000))));

                // r2.startActivity(r9)
                units.add(Jimple.v().newInvokeStmt(
                                Jimple.v().newVirtualInvokeExpr(
                                                activityLocal,
                                                startActivityMethod.makeRef(),
                                                intentLocal)));

                units.add(Jimple.v().newReturnVoidStmt());

                body.validate();
                return onClickMethod;
        }

        static void addDefaultConstructor(SootClass clazz) {

                List<Type> initParams = new ArrayList<>();
                initParams.add(RefType.v("android.view.View"));
                initParams.add(RefType.v("android.app.Activity"));

                SootMethod initMethod = new SootMethod(
                                "<init>",
                                initParams,
                                VoidType.v(),
                                Modifier.PUBLIC);
                clazz.addMethod(initMethod);

                JimpleBody body = Jimple.v().newBody(initMethod);
                initMethod.setActiveBody(body);

                Local thisLocal = Jimple.v().newLocal("r0", RefType.v(clazz.getName()));
                Local removeLayoutLocal = Jimple.v().newLocal("r1", RefType.v("android.view.View"));
                Local activityLocal = Jimple.v().newLocal("r2", RefType.v("android.app.Activity"));

                body.getLocals().add(thisLocal);
                body.getLocals().add(removeLayoutLocal);
                body.getLocals().add(activityLocal);

                UnitPatchingChain units = body.getUnits();

                // r0 := @this
                units.add(Jimple.v().newIdentityStmt(
                                thisLocal,
                                Jimple.v().newThisRef(RefType.v(clazz.getName()))));

                // r1 := @parameter0: android.view.View
                units.add(Jimple.v().newIdentityStmt(
                                removeLayoutLocal,
                                Jimple.v().newParameterRef(RefType.v("android.view.View"), 0)));

                // r2 := @parameter1: android.app.Activity
                units.add(Jimple.v().newIdentityStmt(
                                activityLocal,
                                Jimple.v().newParameterRef(RefType.v("android.app.Activity"), 1)));

                // super()
                SootMethod objectInit = Scene.v().getMethod("<java.lang.Object: void <init>()>");
                units.add(Jimple.v().newInvokeStmt(
                                Jimple.v().newSpecialInvokeExpr(
                                                thisLocal,
                                                objectInit.makeRef())));

                // this.remove_layout = r1
                SootField removeLayoutField = clazz.getFieldByName(removeView);
                units.add(Jimple.v().newAssignStmt(
                                Jimple.v().newInstanceFieldRef(thisLocal, removeLayoutField.makeRef()),
                                removeLayoutLocal));

                // this.activity = r2
                SootField activityField = clazz.getFieldByName("activity");
                units.add(Jimple.v().newAssignStmt(
                                Jimple.v().newInstanceFieldRef(thisLocal, activityField.makeRef()),
                                activityLocal));

                units.add(Jimple.v().newReturnVoidStmt());
        }

}
