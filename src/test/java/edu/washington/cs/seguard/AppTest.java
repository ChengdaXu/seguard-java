package edu.washington.cs.seguard;

import static org.junit.Assert.assertEquals;
import static org.junit.Assert.assertTrue;

import java.io.IOException;
import java.util.*;

import android.util.Base64;
import com.google.common.collect.Sets;
import edu.washington.cs.seguard.core.IFDSDataFlowTransformer;
import edu.washington.cs.seguard.js.JSFlowGraph;
import edu.washington.cs.seguard.pe.AliasRewriter;
import lombok.val;
import org.junit.Test;

import soot.*;

import soot.jimple.InstanceInvokeExpr;
import soot.jimple.Stmt;
import soot.options.Options;

import soot.toolkits.scalar.Pair;
import soot.util.dot.DotGraph;

/**
 * Unit tests.
 */
public class AppTest
{
    @Test
    public void shouldAnswerWithTrue()
    {
        SootClass cls = new SootClass("TestClass");
        SootMethod m = new SootMethod("testMethod", Collections.emptyList(), VoidType.v());
        cls.addMethod(m);
        SootField f = new SootField("testStaticStringField", RefType.v("String"));
        f.setModifiers(Modifier.STATIC);
        cls.addField(f);
    }

    @Test
    public void getStaticStringsTest() {
        soot.G.reset();
        Options.v().set_process_dir(Collections.singletonList("src/test/resources"));
        Options.v().set_soot_classpath("src/test/resources:lib/rt.jar");
        Options.v().set_whole_program(true);
        Options.v().set_allow_phantom_refs(true);
        Options.v().set_no_bodies_for_excluded(true);
        Options.v().set_ignore_resolution_errors(true);
        Scene.v().loadNecessaryClasses();
        SootClass testClass = Scene.v().getSootClass("Test");
        assertEquals(testClass.getMethods().toString(), 4, testClass.getMethods().size());
        assertEquals(testClass.getFields().toString(), 1, testClass.getFields().size());
        PackManager.v().getPack("wjtp").add(new Transform("wjtp.test", new SceneTransformer() {
            @Override
            protected void internalTransform(String s, Map<String, String> map) {
                val strings = Util.getStaticStrings(testClass);
                assertEquals(strings.toString(), 1, strings.size());
            }
        }));
    }

    @Test
    public void testAnalysis() throws IOException {
        SootOptionManager.Manager().buildOptionTest();
        Scene.v().loadNecessaryClasses();
        Scene.v().addBasicClass("dummyMainClass", SootClass.BODIES);
        Scene.v().loadClassAndSupport("dummyMainClass");
        SootClass testClass = Scene.v().getSootClass("dummyMainClass");
        SootMethod method = testClass.getMethodByName("dummyMainMethod");
        method.retrieveActiveBody();
        Scene.v().setEntryPoints(Collections.singletonList(method));
        val config = Config.load("src/test/resources/config.yaml");
        val conditions = new Conditions("SourcesAndSinks.txt", config);
        IFDSDataFlowTransformer transformer = new IFDSDataFlowTransformer(conditions, config);
        System.out.println(method.getActiveBody());
        val rewriter = new AliasRewriter(conditions);
        PackManager.v().getPack("wjtp").add(new Transform("wjtp.aliasrewriter", rewriter));
        PackManager.v().getPack("wjtp").add(new Transform("wjtp.herosifds", transformer));
        PackManager.v().getPack("jtp").add(new Transform("jtp.myTransform", new BodyTransformer() {
            @Override
            protected void internalTransform(Body b, String phaseName, Map<String, String> options) {
                val className = b.getMethod().getDeclaringClass().getName();
                for (Unit u : b.getUnits()) {
                    Stmt s = (Stmt) u;
                    if (s.containsInvokeExpr() && s.getInvokeExpr() instanceof InstanceInvokeExpr) {
                        InstanceInvokeExpr e = (InstanceInvokeExpr) s.getInvokeExpr();
                        if (e.getMethod().getName().equals("println") && className.equals("dummyMainClass")) {
                            boolean equals = false;
                            val constants = "[[other]]";
                            for (Pair result : transformer.getSolver().ifdsResultsAt(u)) {
                                if (result.getO1().equals(e.getArg(0))) {
                                    System.out.println(result.getO2().toString());
                                    val str = result.getO2().toString();
                                    if (str.equals(constants)) {
                                        equals = true;
                                    }
                                }
                            }
                            assertTrue(s.toString(), equals);
                        }
                    }
                }
            }
        }));
        PackManager.v().runPacks();
    }

    static boolean record = false;

    public void compareSetOfStrings(String expectedFile, Set<String> actual) throws IOException {
        if (record) {
            Util.writeLines(expectedFile, actual);
            return;
        }
        val expected = new HashSet<>(Util.readLines(expectedFile));
        val msg = String.format("\nActual: %s\n\nDiff: %s",
                String.join("\n", actual),
                String.join("\n", Sets.symmetricDifference(expected, actual)));
        assertEquals(msg, expected, actual);
    }

    @Test
    public void testJS1() throws IOException {
        val conditions = new Conditions("SourcesAndSinks.txt", Config.load("src/test/resources/config.yaml"));
        val dot = new BetterDot(new DotGraph(""), conditions);
        val cg = JSFlowGraph.addCallGraph(dot, "src/test/resources/example.js");
        JSFlowGraph.addDataFlowGraph(dot, cg);
        compareSetOfStrings("src/test/resources/example.nodes.txt", dot.getNodes());
        compareSetOfStrings("src/test/resources/example.edges.txt", dot.getEdgesWithType());
    }

    @Test
    public void testJS2() throws IOException {
        val conditions = new Conditions("SourcesAndSinks.txt", Config.load("src/test/resources/config.yaml"));
        val dot = new BetterDot(new DotGraph(""), conditions);
        val cg = JSFlowGraph.addCallGraph(dot, "src/test/resources/eventstream.js");
        JSFlowGraph.addDataFlowGraph(dot, cg);
        System.out.println("==================testJS2===============");
        System.out.println(dot.getNodes());
        assertTrue(dot.getNodes().contains("process[env][npm_package_description]"));
        compareSetOfStrings("src/test/resources/eventstream.nodes.txt", dot.getNodes());
        compareSetOfStrings("src/test/resources/eventstream.edges.txt", dot.getEdgesWithType());
    }

    @Test
    public void testJS3() throws IOException {
        val conditions = new Conditions("SourcesAndSinks.txt", Config.load("src/test/resources/config.yaml"));
        val dot = new BetterDot(new DotGraph(""), conditions);
        val cg = JSFlowGraph.addCallGraph(dot, "src/test/resources/example2.js");
        JSFlowGraph.addDataFlowGraph(dot, cg);
        compareSetOfStrings("src/test/resources/example2.nodes.txt", dot.getNodes());
        compareSetOfStrings("src/test/resources/example2.edges.txt", dot.getEdgesWithType());
    }

    @Test
    public void testAndroidAPI() {
        System.out.println(new String(Base64.decode("aHR0cDovL3poZWthcHR5LmNvbQ==", 0)));
    }
}
