package edu.washington.cs.seguard.js;

import com.ibm.wala.cast.ir.ssa.AstGlobalRead;
import com.ibm.wala.cast.ir.ssa.AstGlobalWrite;
import com.ibm.wala.cast.ir.ssa.AstLexicalWrite;
import com.ibm.wala.cast.ir.ssa.EachElementGetInstruction;
import com.ibm.wala.cast.js.ssa.*;
import com.ibm.wala.classLoader.IClass;
import com.ibm.wala.classLoader.IField;
import com.ibm.wala.dataflow.IFDS.*;
import com.ibm.wala.ipa.callgraph.AnalysisCache;
import com.ibm.wala.ipa.callgraph.CGNode;
import com.ibm.wala.ipa.callgraph.CallGraph;
import com.ibm.wala.ipa.cfg.BasicBlockInContext;
import com.ibm.wala.ipa.cfg.ExplodedInterproceduralCFG;
import com.ibm.wala.ipa.cha.IClassHierarchy;
import com.ibm.wala.ssa.*;
import com.ibm.wala.ssa.analysis.IExplodedBasicBlock;
import com.ibm.wala.util.CancelException;
import com.ibm.wala.util.collections.HashSetFactory;
import com.ibm.wala.util.collections.Pair;
import com.ibm.wala.util.intset.IntSet;
import com.ibm.wala.util.intset.MutableMapping;
import com.ibm.wala.util.intset.MutableSparseIntSet;
import lombok.val;
import scala.Int;

import java.util.*;

public class IFDSDataFlow {
  private final IClassHierarchy cha;
  private final ExplodedInterproceduralCFG icfg;
  private final ISupergraph<BasicBlockInContext<IExplodedBasicBlock>, CGNode> supergraph;
  private final DataFlowDomain domain = new DataFlowDomain();

  public IFDSDataFlow(ExplodedInterproceduralCFG icfg) {
    this.cha = icfg.getCallGraph().getClassHierarchy();
    this.icfg = icfg;
    this.supergraph = ICFGSupergraph.make(icfg.getCallGraph());
  }

  /**
   * Define a Dataflow Domain, which maps an int (SSA variable) to a set of integers (dependency SSA variables)
   */
  @SuppressWarnings("serial")
private class DataFlowDomain extends MutableMapping<Pair<Integer, Set<Integer>>> implements
          TabulationDomain<Pair<Integer, Set<Integer>>, BasicBlockInContext<IExplodedBasicBlock>> {

    @Override
    public boolean hasPriorityOver(PathEdge<BasicBlockInContext<IExplodedBasicBlock>> p1,
                                   PathEdge<BasicBlockInContext<IExplodedBasicBlock>> p2) {
      // don't worry about worklist priorities
      return false;
    }

  }

  private class DataFlowFunctions implements IPartiallyBalancedFlowFunctions<BasicBlockInContext<IExplodedBasicBlock>> {

    private final DataFlowDomain domain;
    // For PrototypeLookup statement like v9 = prototype_values(v29), we would treat v9 as an alias of v29.
    // This aliasMap tracks all aliases
    private final Map<String, Map<Integer, Integer>> aliasMap;
    // This map is used to process ASTGloablWrite instruction. For example, for instruction
    // global:global npm_package_desc = v26, we know that there is dataflow from v26 to
    // npm_package_desc, so this map would record the name of global variables and the most
    // recent variable whose value is assigned to the global variable.
    private final Map<String, Integer> globalVarMap;
    // For every key value pair (int i, Set<Integer> set) -> int idx in domain, we would put a (i, idx) pair
    // in idxMap, so that we can easily find the idx associated with i, and thus get the set of facts easily
//    private final Map<Integer, Integer> idxMap;
    protected DataFlowFunctions(DataFlowDomain domain) {
      this.domain = domain;
      aliasMap = new HashMap();
      globalVarMap = new HashMap<>();
    }

    /**
     * the flow function for flow from a callee to caller where there was no flow from caller to callee; just the identity function
     * 
     * @see ReachingDefsProblem
     */
    @Override
    public IFlowFunction getUnbalancedReturnFlowFunction(BasicBlockInContext<IExplodedBasicBlock> src,
                                                         BasicBlockInContext<IExplodedBasicBlock> dest) {
      return IdentityFlowFunction.identity();
    }

    /**
     * flow function from caller to callee; just the identity function
     */
    @Override
    public IUnaryFlowFunction getCallFlowFunction(BasicBlockInContext<IExplodedBasicBlock> src,
                                                  BasicBlockInContext<IExplodedBasicBlock> dest, BasicBlockInContext<IExplodedBasicBlock> ret) {
      return IdentityFlowFunction.identity();
    }

    /**
     * flow function from call node to return node when there are no targets for the call site; not a case we are expecting
     */
    @Override
    public IUnaryFlowFunction getCallNoneToReturnFlowFunction(BasicBlockInContext<IExplodedBasicBlock> src,
                                                              BasicBlockInContext<IExplodedBasicBlock> dest) {
      // if we're missing callees, just keep what information we have
      return IdentityFlowFunction.identity();
    }

    /**
     * flow function from call node to return node at a call site when callees exist. We kill everything; surviving facts should
     * flow out of the callee
     */
    @Override
    public IUnaryFlowFunction getCallToReturnFlowFunction(BasicBlockInContext<IExplodedBasicBlock> src,
                                                          BasicBlockInContext<IExplodedBasicBlock> dest) {
      return KillEverything.singleton();
    }

    /**
     * flow function for normal intraprocedural edges
     */
    @Override
    public IUnaryFlowFunction getNormalFlowFunction(final BasicBlockInContext<IExplodedBasicBlock> src,
                                                    BasicBlockInContext<IExplodedBasicBlock> dest) {
      return d1 -> {
        val instr = src.getDelegate().getInstruction();
        MutableSparseIntSet result = MutableSparseIntSet.makeEmpty();
        if (instr instanceof AstGlobalRead) {
          val readInstr = (AstGlobalRead) instr;
          if (globalVarMap.containsKey(readInstr.getGlobalName())) {
            val from = globalVarMap.get(readInstr.getGlobalName());
            val to = readInstr.getDef();
            val factNum = domain.add(Pair.make(to, Collections.singleton(from)));
            result.add(factNum);
          }
        } else if (instr == null || instr.getNumberOfUses() < 1 || instr instanceof JavaScriptCheckReference
                || instr instanceof SetPrototype
                || instr instanceof SSAConditionalBranchInstruction || instr instanceof AstLexicalWrite
                || instr instanceof JavaScriptTypeOfInstruction || instr instanceof EachElementGetInstruction) {
          // do nothing
          int a = 1;
        } else if (instr instanceof PrototypeLookup) {
          if (JSFlowGraph.isApplicationNode(src.getNode())) {
            val namespace = src.getNode().toString();
            if (!aliasMap.containsKey(namespace)) {
              aliasMap.put(namespace, new HashMap<>());
            }
            aliasMap.get(namespace).put(instr.getDef(0), instr.getUse(0));
          }
        } else if (instr instanceof SSAGetInstruction) {
          val getInstr = (SSAGetInstruction) instr;
          int from = getInstr.getUse(0);
          val to = getInstr.getDef();
          if (JSFlowGraph.isApplicationNode(src.getNode())) {
            val namespace = src.getNode().toString();
            val localAliasMap = aliasMap.get(namespace);
            from = localAliasMap.getOrDefault(from, from);
          }
          val factNum = domain.add(Pair.make(to, Collections.singleton(from)));
          result.add(factNum);
        } else if (instr instanceof AstGlobalWrite) {
          val writeInstr = (AstGlobalWrite) instr;
          globalVarMap.put(writeInstr.getGlobalName(), writeInstr.getVal());
        } else if (instr instanceof SSAPutInstruction) {
          val putInstr = (SSAPutInstruction) instr;
          if (putInstr.getNumberOfUses() > 1) {
            val from = putInstr.getUse(1);
            val to = putInstr.getUse(0);
            val factNum = domain.add(Pair.make(to, Collections.singleton(from)));
            result.add(factNum);
          }
        } else if (instr instanceof JavaScriptPropertyWrite) {
          val write = (JavaScriptPropertyWrite) instr;
          val from = write.getUse(2);
          val to = write.getObjectRef();
          val factNum = domain.add(Pair.make(to, Collections.singleton(from)));
          result.add(factNum);
        } else if (instr instanceof JavaScriptPropertyRead) {
          val read = (JavaScriptPropertyRead) instr;
          val from = read.getObjectRef();
          val to = read.getDef();
          val factNum = domain.add(Pair.make(to, Collections.singleton(from)));
          result.add(factNum);
        } else if (instr instanceof SSAReturnInstruction) {
          return result; // kill
        } else if (instr instanceof SSABinaryOpInstruction) {
          val from1 = instr.getUse(0);
          val from2 = instr.getUse(1);
          val to = instr.getDef();
          val fromSet = new HashSet<Integer>();
          fromSet.add(from1);
          fromSet.add(from2);
          val factNum = domain.add(Pair.make(to, fromSet));
          result.add(factNum);
        } else if (instr instanceof SSAUnaryOpInstruction) {
          // decode d1 to domain
          // scala union type
          val from1 = instr.getUse(0);
          val to = instr.getDef();
          val fromSet = new HashSet<Integer>();
          fromSet.add(from1);
          val factNum = domain.add(Pair.make(to, fromSet));
          result.add(factNum);
        } else {
//          throw new RuntimeException(instr.toString() + ", " + instr.getClass().toString());
          System.out.println("Unhandled getNormalFlowFunction: " + instr.toString() + ", " + instr.getClass().toString());
        }
        result.add(d1);
        return result;
      };
    }

    /**
     * standard flow function from callee to caller; just identity
     */
    @Override
    public IFlowFunction getReturnFlowFunction(BasicBlockInContext<IExplodedBasicBlock> call,
                                               BasicBlockInContext<IExplodedBasicBlock> src, BasicBlockInContext<IExplodedBasicBlock> dest) {
      return IdentityFlowFunction.identity();
    }

  }

  /**
   * Definition of the reaching definitions tabulation problem. Note that we choose to make the problem a <em>partially</em>
   * balanced tabulation problem, where the solver is seeded with the putstatic instructions themselves. The problem is partially
   * balanced since a definition in a callee used as a seed for the analysis may then reach a caller, yielding a "return" without a
   * corresponding "call." An alternative to this approach, used in the Reps-Horwitz-Sagiv POPL95 paper, would be to "lift" the
   * domain of putstatic instructions with a 0 (bottom) element, have a 0->0 transition in all transfer functions, and then seed the
   * analysis with the path edge (main_entry, 0) -> (main_entry, 0). We choose the partially-balanced approach to avoid pollution of
   * the flow functions.
   * 
   */
  private class ReachingDefsProblem implements
          PartiallyBalancedTabulationProblem<BasicBlockInContext<IExplodedBasicBlock>, CGNode, Pair<Integer, Set<Integer>>> {

    private DataFlowFunctions flowFunctions = new DataFlowFunctions(domain);

    /**
     * path edges corresponding to all putstatic instructions, used as seeds for the analysis
     */
    private Collection<PathEdge<BasicBlockInContext<IExplodedBasicBlock>>> initialSeeds = collectInitialSeeds();

    /**
     * collect the putstatic instructions in the call graph as {@link PathEdge} seeds for the analysis
     */
    private Collection<PathEdge<BasicBlockInContext<IExplodedBasicBlock>>> collectInitialSeeds() {
      Collection<PathEdge<BasicBlockInContext<IExplodedBasicBlock>>> result = HashSetFactory.make();
      for (val cgNode : supergraph.getProcedureGraph()) {
        val fakeEntry = getFakeEntry(cgNode);
        val factNum = domain.add(Pair.make(0, new HashSet<>()));
        icfg.getSuccNodes(fakeEntry).forEachRemaining((succ) -> {
          val entryInstr = fakeEntry.getDelegate().getInstruction();
          val succInstr = succ.getDelegate().getInstruction();
          result.add(PathEdge.createPathEdge(fakeEntry, factNum, succ, factNum));
        });
      }
      return result;
    }

    /**
     * we use the entry block of the CGNode as the fake entry when propagating from callee to caller with unbalanced parens
     */
    @Override
    public BasicBlockInContext<IExplodedBasicBlock> getFakeEntry(BasicBlockInContext<IExplodedBasicBlock> node) {
      final CGNode cgNode = node.getNode();
      return getFakeEntry(cgNode);
    }

    /**
     * we use the entry block of the CGNode as the "fake" entry when propagating from callee to caller with unbalanced parens
     */
    private BasicBlockInContext<IExplodedBasicBlock> getFakeEntry(final CGNode cgNode) {
      BasicBlockInContext<IExplodedBasicBlock>[] entriesForProcedure = supergraph.getEntriesForProcedure(cgNode);
      assert entriesForProcedure.length == 1;
      return entriesForProcedure[0];
    }

    @Override
    public IPartiallyBalancedFlowFunctions<BasicBlockInContext<IExplodedBasicBlock>> getFunctionMap() {
      return flowFunctions;
    }

    @Override
    public TabulationDomain<Pair<Integer, Set<Integer>>, BasicBlockInContext<IExplodedBasicBlock>> getDomain() {
      return domain;
    }

    /**
     * we don't need a merge function; the default unioning of tabulation works fine
     */
    @Override
    public IMergeFunction getMergeFunction() {
      return null;
    }

    @Override
    public ISupergraph<BasicBlockInContext<IExplodedBasicBlock>, CGNode> getSupergraph() {
      return supergraph;
    }

    @Override
    public Collection<PathEdge<BasicBlockInContext<IExplodedBasicBlock>>> initialSeeds() {
      return initialSeeds;
    }

  }

  /**
   * perform the tabulation analysis and return the {@link TabulationResult}
   */
  public TabulationResult<BasicBlockInContext<IExplodedBasicBlock>, CGNode, Pair<Integer, Set<Integer>>> analyze() {
    PartiallyBalancedTabulationSolver<BasicBlockInContext<IExplodedBasicBlock>, CGNode, Pair<Integer, Set<Integer>>> solver = PartiallyBalancedTabulationSolver
        .createPartiallyBalancedTabulationSolver(new ReachingDefsProblem(), null);
    TabulationResult<BasicBlockInContext<IExplodedBasicBlock>, CGNode, Pair<Integer, Set<Integer>>> result = null;
    try {
      result = solver.solve();
    } catch (CancelException e) {
      // this shouldn't happen 
      assert false;
    }
    return result;

  }

  public ISupergraph<BasicBlockInContext<IExplodedBasicBlock>, CGNode> getSupergraph() {
    return supergraph;
  }

  public TabulationDomain<Pair<Integer, Set<Integer>>, BasicBlockInContext<IExplodedBasicBlock>> getDomain() {
    return domain;
  }
}
