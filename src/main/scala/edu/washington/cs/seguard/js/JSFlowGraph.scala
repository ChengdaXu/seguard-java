package edu.washington.cs.seguard.js

import java.io.{BufferedWriter, File, FileWriter}
import java.nio.file.Paths

import com.ibm.wala.cast.ir.ssa.{AstGlobalRead, AstGlobalWrite, AstLexicalRead, AstLexicalWrite, EachElementGetInstruction}
import com.ibm.wala.cast.js.ipa.callgraph.JSCallGraphUtil
import com.ibm.wala.cast.js.ssa.{JavaScriptCheckReference, JavaScriptInvoke, JavaScriptPropertyRead, JavaScriptPropertyWrite, JavaScriptTypeOfInstruction, PrototypeLookup, SetPrototype}
import com.ibm.wala.cast.js.translator.CAstRhinoTranslatorFactory
import com.ibm.wala.cast.js.types.JavaScriptMethods
import com.ibm.wala.examples.analysis.js.JSCallGraphBuilderUtil
import com.ibm.wala.ipa.callgraph.{CGNode, CallGraph}
import com.ibm.wala.ipa.cfg.ExplodedInterproceduralCFG
import com.ibm.wala.ipa.cha.IClassHierarchy
import com.ibm.wala.ssa.{DefUse, SSABinaryOpInstruction, SSAConditionalBranchInstruction, SSAGetInstruction, SSAGotoInstruction, SSAInstruction, SSANewInstruction, SSAPhiInstruction, SSAReturnInstruction, SSAUnaryOpInstruction, SymbolTable}
import edu.washington.cs.seguard.{BetterDot, EdgeType, NodeType}

import scala.collection.mutable
import scala.collection.mutable.HashMap
import scala.jdk.CollectionConverters._

object JSFlowGraph {
  def getMethodName(s: String): Option[String] = {
    if (s.contains(".js@")) {
      None
    } else {
      if (s.contains("/")) {
        Some(s.split('/').last)
      } else {
        Some(s)
      }
    }
  }

  def getMethodName(node: CGNode): Option[String] = {
    getMethodName(node.getMethod.getDeclaringClass.getName.toString)
  }

  private def toFunctionCall(name: String): String = {
    name.stripPrefix("$").stripSuffix("$").replace("$", ".") + "();\n"
  }

  def getAllMethods(jsPath: String, outputPath: String): Unit = {
    val path = Paths.get(jsPath)
    JSCallGraphUtil.setTranslatorFactory(new CAstRhinoTranslatorFactory)
    val cg = JSCallGraphBuilderUtil.makeScriptCG(path.getParent.toString, path.getFileName.toString)
    val cha = cg.getClassHierarchy
    val methods = cha.asScala.filter(!_.getName.toString.contains("prologue.js")).flatMap(_.getAllMethods.asScala).toList
    val lines = methods.map(_.getDeclaringClass.getName.toString.split("/")).filter(_.length > 1).map(xs => toFunctionCall(xs(1)))
    val file = new File(outputPath)
    val bw = new BufferedWriter(new FileWriter(file))
    for (line <- lines) {
      bw.write(line)
    }
    bw.close()
  }

  def addCallGraph(dot: BetterDot, jsPath: String) : CallGraph = {
    val path = Paths.get(jsPath)
    JSCallGraphUtil.setTranslatorFactory(new CAstRhinoTranslatorFactory)
    val cg = JSCallGraphBuilderUtil.makeScriptCG(path.getParent.toString, path.getFileName.toString)
    cg.stream().filter(isApplicationNode)
      .forEach(node => {
        cg.getSuccNodes(node).asScala.filter(isApplicationNode).foreach((succ: CGNode) => {
          val u = getMethodName(node)
          val v = getMethodName(succ)
          if (u.isDefined && v.isDefined) {
            dot.drawNode(u.get, NodeType.METHOD)
            dot.drawNode(v.get, NodeType.METHOD)
            dot.drawEdge(u.get, v.get, EdgeType.CALL)
          }
        })
      })
    cg
  }

  def isApplicationNode(m: CGNode) : Boolean = {
    val className = m.getMethod.getDeclaringClass.getName.toString
    className != "LFakeRoot" && className != "Lprologue.js" && className !="LFunction" &&
      m.getMethod.getReference != JavaScriptMethods.ctorReference
  }

  /**
   * From SSA identifier to abstract node
   * @param defUse
   * @param symbolTable
   * @param i SSA identifier
   * @return
   */
  def getDef(defUse: DefUse, symbolTable: SymbolTable, i: Int): Option[String] = {
    defUse.getDef(i) match {
      case null =>
        if (symbolTable.isConstant(i)) {
          val v = symbolTable.getConstantValue(i)
          if (v == null) {
            None
          } else {
            Some(v.toString)
          }
        } else {
          None
        }
      case other => abstractInstruction(defUse, symbolTable, other)
    }
  }

  /*
  1. What does "__WALA__int3rnal__global" mean?

    point to global context

  -- https://sourceforge.net/p/wala/mailman/message/32491808/
   */
  /**
   * Get abstract node for a [[SSAInstruction]]
   * @param defUse
   * @param symTable
   * @param instruction
   * @return
   */
  def abstractInstruction(defUse: DefUse, symTable: SymbolTable, instruction: SSAInstruction): Option[String] = {
    instruction match {
      case read: AstGlobalRead => {
        var ret = read.getGlobalName
        assert(ret.startsWith("global "))
        ret = ret.stripPrefix("global ")
        if (ret == "__WALA__int3rnal__global" ||
          ret == "Function") { // point to global context
          None
        } else {
          Some(ret)
        }
      }
      case invoke:JavaScriptInvoke => {
        val defs = (0 until invoke.getNumberOfUses).flatMap(i => getDef(defUse, symTable, invoke.getUse(i))).toList
        if (defs.nonEmpty) {
          getMethodName(defs.head).map(_ + "(%s)".format(defs.tail.mkString(", ")))
        } else {
          None
        }
      }
      case binop:SSABinaryOpInstruction => Some(binop.getOperator.toString)
      case uop:SSAUnaryOpInstruction => Some("[uop]" + uop.getOpcode.toString)
      case get:SSAGetInstruction => Some("[get]" + get.getDeclaredField.getName.toString)
      case _:JavaScriptPropertyWrite => None // FIXME: how to retrieve property name?
      case _:JavaScriptPropertyRead => None // FIXME: how to retrieve property name?
      case _:AstGlobalWrite => None
      case _:AstGlobalRead => None
      case _:JavaScriptCheckReference => None
      case _:SSAReturnInstruction => None
      case _:AstLexicalWrite => None
      case _:AstLexicalRead => None
      case _:PrototypeLookup => None
      case _:SSAConditionalBranchInstruction => None
      case _:SSANewInstruction => None
      case _:SSAGotoInstruction => None
      case _:SSAPhiInstruction => None
      case _:EachElementGetInstruction => None
      case _:JavaScriptTypeOfInstruction => None
      case _:SetPrototype => None
      case null => None
      case _ => {
        if (instruction.toString(symTable).contains("putfield")) {
          None
        } else {
          // throw new RuntimeException(instruction.toString + ", " + instruction.getClass.toString)
          println("Unhandled at abstractInstruction: " + instruction.toString(symTable) + ", " + instruction.getClass.toString)
          None
        }
      }
    }
  }

  def getName(u: String, instruction: SSAInstruction, node: CGNode,
              globalVarMap: HashMap[String, HashMap[Int, String]], aliasMap: HashMap[String, HashMap[Int, Int]]): String = {
    var u_complete = u
    val namespace = node.toString  // name of the function where these variables are defined
    if (isApplicationNode(node)) {
      if (!globalVarMap.contains(namespace)) {
        globalVarMap.put(namespace, new HashMap())
      }
      if (instruction.isInstanceOf[AstGlobalRead]) { // global variable
        val key = instruction.getDef();
        if (!globalVarMap(namespace).contains(key)) {
          globalVarMap(namespace).put(key, u_complete)
        }
      } else if (instruction.isInstanceOf[SSAGetInstruction]) {
        val idx = aliasMap(namespace)(instruction.asInstanceOf[SSAGetInstruction].getRef())
        val key = instruction.getDef();
        u_complete = globalVarMap(namespace)(idx) + "[" + instruction.asInstanceOf[SSAGetInstruction].getDeclaredField.getName.toString + "]";
        globalVarMap(namespace).put(key, u_complete)
      }
    }
    u_complete
  }

  def addDataFlowGraph(dot: BetterDot, cg: CallGraph) {
    // IFDS based data-flow analysis
    val icfg = ExplodedInterproceduralCFG.make(cg)
    val dataflow = new IFDSDataFlow(icfg)
    val results = dataflow.analyze()
    val superGraph = dataflow.getSupergraph
    val aliasMap: HashMap[String, HashMap[Int, Int]] = new HashMap();
    val globalVarMap: HashMap[String, HashMap[Int, String]] = new HashMap();

    for (n <- superGraph.getProcedureGraph.asScala) {
      if (isApplicationNode(n)) {
        var localAliasMap: HashMap[Int, Int] = new HashMap()
        println("====== Method " + n + " =======")
        println(n.getIR)
        println("===============================")
        // The IR we used here is in SSA form
        for (instruction <- n.getIR().getInstructions()) {
          if (instruction != null && instruction.isInstanceOf[PrototypeLookup] && !localAliasMap.contains(instruction.getDef(0))) {
            localAliasMap.put(instruction.getDef(0), instruction.getUse(0))
          }
        }
        aliasMap.put(n.toString, localAliasMap);
      }
    }

    /*

    For function calls (i.e., something like "f()"), the fake
      target method is called "do", for constructor calls (i.e.,
      something like "new f()"), the target method is "ctor". Again,
    the actual method to be invoked is passed as an argument (in
      an SSA variable) to the fake target method. It may help to
      print the IR of the function containing such calls (using its
      normal toString method); this will print out quite a bit of
      information about the individual calls.

     -- https://sourceforge.net/p/wala/mailman/message/30369613/
     */

    // For each node in the super graph (Exploded CFG)
    for (node <- superGraph.asScala) {
      if (isApplicationNode(node.getNode)) {
        val symTable = node.getNode.getIR.getSymbolTable
        // Each node corresponds to a _single_ instruction
        val instruction = node.getDelegate.getInstruction
        if (instruction != null) {

          println("======= Instruction of BB " + node.getDelegate.getNumber + " of method " + node.getNode + "==============")
          println(instruction, instruction.toString(symTable))

          // solution is a set of fact nums
          val solution = results.getResult(node)
          val iter = solution.intIterator
          // process each fact at current node
          while (iter.hasNext) {
            val fact = iter.next()
            // fact remapped back to abstract domain: a pair of (dependent: Int, dependencies: Set[Int])
            // each value is an Int due to SSA construction
            val absValues = dataflow.getDomain.getMappedObject(fact)
            println("== Dataflow " + fact + ": " + absValues)
            val to = absValues.fst
            val fromValues = absValues.snd
            for (from <- fromValues.asScala) {
              val defUse = node.getNode.getDU
              val from_raw = getDef(defUse, symTable, from)
              val to_raw = getDef(defUse, symTable, to)
              if (from_raw.isDefined && to_raw.isDefined) {
                if (from_raw.get.contains("exports(f)") || to_raw.get.contains("exports(f)")) {
                  println("here111")
                }
                val fromValue = getName(from_raw.get, defUse.getDef(from), node.getNode, globalVarMap, aliasMap);
                val toValue = getName(to_raw.get, defUse.getDef(to), node.getNode, globalVarMap, aliasMap);
                dot.drawNode(fromValue, NodeType.EXPR)
                dot.drawNode(toValue, NodeType.EXPR)
                dot.drawEdge(fromValue, toValue, EdgeType.DATAFLOW)
              }
            }
          }

          abstractInstruction(node.getNode.getDU, symTable, instruction) match {
            case Some(u) => {
              // DefUse based analysis
              val u_complete = getName(u, instruction, node.getNode, globalVarMap, aliasMap);
              if (u_complete.contains("_compile([get]constructor(), decoded, )")) {
                println("here11111")
              }
              //              if (!globalVarMap.contains(namespace)) {
              //                globalVarMap.put(namespace, new HashMap());
              //              }
              //              if (instruction.isInstanceOf[AstGlobalRead]) { // global variable
              //                val key = instruction.getDef();
              //                globalVarMap(namespace).put(key, u_complete)
              //              } else if (instruction.isInstanceOf[SSAGetInstruction]) {
              //                val idx = aliasMap(namespace)(instruction.asInstanceOf[SSAGetInstruction].getRef())
              //                u_complete = globalVarMap(namespace)(idx) + "[" + instruction.asInstanceOf[SSAGetInstruction].getDeclaredField.getName.toString + "]";
              //                globalVarMap(namespace).put(instruction.getDef(), u_complete)
              //              }
              dot.drawNode(u_complete, NodeType.STMT)
              for (iu <- 0 until instruction.getNumberOfUses) {
                val use = instruction.getUse(iu)
                val defined = node.getNode.getDU.getDef(use)
                if (defined != null) {
                  val defineNode = abstractInstruction(node.getNode.getDU, symTable, defined)
                  if (defineNode.isDefined) {
                    val v = defineNode.get
                    dot.drawNode(v, NodeType.STMT)
                    dot.drawEdge(v, u_complete, EdgeType.DATAFLOW)
                  }
                } else {
                  if (symTable.isConstant(use) && symTable.getConstantValue(use) != null) {
                    var v = symTable.getConstantValue(use).toString
                    if (v.startsWith("L")) {
                      v = getMethodName(v).get
                    }
                    dot.drawNode("[const]" + v, NodeType.CONSTANT)
                    dot.drawEdge(v, u_complete, EdgeType.DATAFLOW)
                  }
                }
              }
            }
            case _ =>
          }
        }
      }
    }
  }
}
