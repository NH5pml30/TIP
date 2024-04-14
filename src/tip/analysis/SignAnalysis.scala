package tip.analysis

import tip.ast.{AAssignStmt, AIdentifier, AVarStmt, NoCalls, NoPointers, NoRecords}
import tip.ast.AstNodeData.DeclarationData
import tip.cfg.{CfgNode, CfgStmtNode, InterproceduralProgramCfg, IntraproceduralProgramCfg}
import tip.lattices.SignLattice

object SignAnalysis {

  object Intraprocedural {
    trait TransferImpl extends ValueAnalysisMisc {
      def transferImpl(n: CfgNode, s: statelattice.Element): statelattice.Element = {
        NoPointers.assertContainsNode(n.data)
        NoCalls.assertContainsNode(n.data)
        NoRecords.assertContainsNode(n.data)
        n match {
          case r: CfgStmtNode =>
            r.data match {
              // var declarations
              case varr: AVarStmt => s ++ varr.declIds.map(d => (d, statelattice.sublattice.bottom))

              // assignments
              case AAssignStmt(id: AIdentifier, right, _) => s + ((id, eval(right, s)))

              // all others: like no-ops
              case _ => s
            }
          case _ => s
        }
      }
    }

    /**
      * Intraprocedural analysis that uses the simple fixpoint solver.
      */
    class SimpleSolver(cfg: IntraproceduralProgramCfg)(implicit declData: DeclarationData) extends IntraprocValueAnalysisSimpleSolver(cfg, SignLattice)
      with TransferImpl {
      override def transfer(n: CfgNode, s: statelattice.Element) = super.transferImpl(n, s)
    }

    /**
      * Intraprocedural analysis that uses the worklist solver.
      */
    class WorklistSolver(cfg: IntraproceduralProgramCfg)(implicit declData: DeclarationData) extends IntraprocValueAnalysisWorklistSolver(cfg, SignLattice)
      with TransferImpl {
      override def transfer(n: CfgNode, s: statelattice.Element) = super.transferImpl(n, s)
    }

    /**
      * Intraprocedural analysis that uses the worklist solver with reachability.
      */
    class WorklistSolverWithReachability(cfg: IntraproceduralProgramCfg)(implicit declData: DeclarationData)
        extends IntraprocValueAnalysisWorklistSolverWithReachability(cfg, SignLattice)
          with TransferImpl {
      override def transferUnlifted(n: CfgNode, s: statelattice.Element) = super.transferImpl(n, s)
    }

    /**
      * Intraprocedural analysis that uses the worklist solver with reachability and propagation-style.
      */
    class WorklistSolverWithReachabilityAndPropagation(cfg: IntraproceduralProgramCfg)(implicit declData: DeclarationData)
        extends IntraprocValueAnalysisWorklistSolverWithReachabilityAndPropagation(cfg, SignLattice)
          with TransferImpl {
      override def transferUnlifted(n: CfgNode, s: statelattice.Element) = super.transferImpl(n, s)
    }
  }

  object Interprocedural {

    /**
      * Interprocedural analysis that uses the worklist solver with reachability.
      */
    class WorklistSolverWithReachability(cfg: InterproceduralProgramCfg)(implicit declData: DeclarationData)
        extends InterprocValueAnalysisWorklistSolverWithReachability(cfg, SignLattice)

    /**
      * Interprocedural analysis that uses the worklist solver with reachability and propagation-style.
      */
    class WorklistSolverWithReachabilityAndPropagation(cfg: InterproceduralProgramCfg)(implicit declData: DeclarationData)
        extends InterprocValueAnalysisWorklistSolverWithReachabilityAndPropagation(cfg, SignLattice)

    /**
      * Interprocedural analysis that uses the worklist solver with reachability and propagation-style.
      * with call-string context sensitivity.
      */
    class CallString(cfg: InterproceduralProgramCfg)(implicit declData: DeclarationData) extends CallStringValueAnalysis(cfg, SignLattice)

    /**
      * Interprocedural analysis that uses the worklist solver with reachability and propagation-style.
      * with functional-approach context sensitivity.
      */
    class Functional(cfg: InterproceduralProgramCfg)(implicit declData: DeclarationData) extends FunctionalValueAnalysis(cfg, SignLattice)
  }
}
