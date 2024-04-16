package tip.analysis

import tip.ast._
import tip.lattices._
import tip.ast.AstNodeData.DeclarationData
import tip.solvers._
import tip.cfg._

/**
 * Base class for reaching definitions analysis.
 */
abstract class ReachingDefAnalysis(cfg: IntraproceduralProgramCfg)(implicit declData: DeclarationData) extends FlowSensitiveAnalysis(false) {
  val lattice: MapLattice[CfgNode, PowersetLattice[Either[AAssignStmt, ADeclaration]]] = new MapLattice(new PowersetLattice())

  val domain: Set[CfgNode] = cfg.nodes

  NoPointers.assertContainsProgram(cfg.prog)
  NoRecords.assertContainsProgram(cfg.prog)

  private def toDecl(p: Either[AAssignStmt, ADeclaration]): ADeclaration = {
    p match {
      case Left(AAssignStmt(id: AIdentifier, _, _)) => id
      case Left(_) => ???
      case Right(d: ADeclaration) => d
    }
  }

  def transfer(n: CfgNode, s: lattice.sublattice.Element): lattice.sublattice.Element =
    n match {
      case r: CfgStmtNode =>
        r.data match {
          case varr: AVarStmt => s ++ varr.declIds.map(Right(_))
          case as: AAssignStmt =>
            as.left match {
              case id: AIdentifier => s.filterNot(toDecl(_) == (id: ADeclaration)) + Left(as)
              case _ => ???
            }
          case _ => s
        }
      case _ => s
    }
}

/**
 * Reaching definition analysis that uses the simple fixpoint solver.
 */
class ReachingDefAnalysisSimpleSolver(cfg: IntraproceduralProgramCfg)(implicit declData: DeclarationData)
  extends ReachingDefAnalysis(cfg)
    with SimpleMapLatticeFixpointSolver[CfgNode]
    with ForwardDependencies
