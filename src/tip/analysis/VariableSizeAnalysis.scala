package tip.analysis

import tip.ast.{ACast, AExpr, AInput, Types}
import tip.ast.AstNodeData.DeclarationData
import tip.cfg.{CfgNode, IntraproceduralProgramCfg}
import tip.lattices.{Lattice, LatticeWithOps}
import tip.solvers.FixpointSolvers

object VariableSizeAnalysis {
  case class BitType(isUnsigned: Boolean, bitLength: Int) {
    private def fitsInSigned(checkLength: Int): Boolean = {
      widen() match {
        case Some(bt) => checkLength >= bt
        case _ => false
      }
    }

    private def fitsInUnsigned(checkLength: Int): Boolean = {
      isUnsigned && checkLength >= bitLength;
    }

    private def fitsIn(t: BitType): Boolean = {
      if (t.isUnsigned) fitsInUnsigned(t.bitLength) else fitsInSigned(t.bitLength)
    }

    def widen(): Option[Int] = {
      if (isUnsigned) {
        IntType(false, bitLength + 1).map(_.bitLength)
      } else {
        Some(bitLength)
      }
    }

    def implicitConversion(other: BitType): (Boolean, (Option[Int], Option[Int])) = {
      if (isUnsigned == other.isUnsigned) {
        (isUnsigned, (Some(this.bitLength), Some(other.bitLength)))
      } else {
        (false, (widen(), other.widen()))
      }
    }

    def lub(other: BitType): IntType = {
      implicitConversion(other) match {
        case (iu, (Some(lhs), Some(rhs))) => IntType(iu, math.max(lhs, rhs))
        case _ => IntType()
      }
    }

    def toType(): Option[Types.Value] = {
      Types.values.toStream
        .flatMap(tt => IntType.fromType(tt).flatMap(bt => if (fitsIn(bt)) Some(tt) else None))
        .headOption
    }
  }

  private type IntType = Option[BitType]

  private object IntType {
    private val maxBits = 32;

    def apply(isUnsigned: Boolean, bitLength: Int): IntType =
      if (bitLength <= maxBits) {
        Some(BitType(isUnsigned, bitLength))
      } else {
        IntType()
      }

    def apply(bitLength: Int): IntType = apply(false, bitLength)

    def apply(): IntType = None

    def fromType(t: Types.Value): IntType = {
      import Types._
      t match {
        case BoolT => IntType(true, 1)
        case ByteT => IntType(false, 8)
        case CharT => IntType(true, 16)
        case IntT => IntType(false, 32)
        case BigIntT => IntType()
        case AnyT => ???
      }
    }

    def toType(t: IntType): Types.Value = {
      t.flatMap(bt => bt.toType()).getOrElse(Types.BigIntT)
    }
  }

  /**
   * The bitness lattice.
   */
  object BitnessLattice extends Lattice with LatticeWithOps {
    sealed trait AnyType

    private case class InnerEl(el: IntType) extends AnyType {
      override def toString = el.toString + s" : ${IntType.toType(el)}"
    }

    final case object Top extends AnyType {
      override def toString = s"Top : ${Types.AnyT}"
    }

    final case object Bot extends AnyType {
      override def toString = s"Bot : _|_"
    }

    override type Element = AnyType
    override val bottom: Element = Bot
    override val top: Element = Top

    override def lub(x: AnyType, y: AnyType): AnyType = {
      (x, y) match {
        case (Top, _) => Top
        case (_, Top) => Top
        case (Bot, _) => y
        case (_, Bot) => x
        case (InnerEl(aa), InnerEl(bb)) =>
          InnerEl(aa.flatMap(aaa => bb.flatMap(bbb => aaa lub bbb)))
      }
    }

    def fromType(t: Option[Types.Value]): AnyType = {
      import Types._
      t match {
        case None => Bot
        case Some(AnyT) => Top
        case Some(tt) => InnerEl(IntType.fromType(tt))
      }
    }

    def toType(t: AnyType): Option[Types.Value] = {
      import Types._
      t match {
        case Bot => None
        case Top => Some(AnyT)
        case InnerEl(tt) => Some(IntType.toType(tt))
      }
    }

    def num(i: Int): Element = {
      val l = BigInt(i).bitLength
      InnerEl(if (i >= 0) {
        IntType(true, l)
      } else {
        IntType(false, l + 1)
      })
    }

    private def doOp(c: (Boolean, Int, Int) => Int, a: Element, b: Element): Element = {
      (a, b) match {
        case (Top, _) => Top
        case (_, Top) => Top
        case (Bot, _) => b
        case (_, Bot) => a
        case (InnerEl(Some(aa)), InnerEl(Some(bb))) => // integer
            InnerEl(aa implicitConversion bb match {
              case (isUnsigned, (Some(cea), Some(ceb))) => // bounded integer or bigint
                IntType(isUnsigned, c(isUnsigned, cea, ceb))
              case _ => IntType() // bigint
            })
        case _ => InnerEl(IntType()) // bigint
      }
    }

    def inv(a: Element): Element = {
      a match {
        case Bot => Bot
        case Top => Top
        case InnerEl(Some(aa)) => InnerEl(aa.widen().flatMap(IntType(_)))
        case _ => InnerEl(IntType())
      }
    }

    def plus(a: Element, b: Element): Element = doOp((_, x, y) => (x max y) + 1, a, b)

    def minus(a: Element, b: Element): Element = plus(a, inv(b))

    def times(a: Element, b: Element): Element = doOp((_, x, y) => x + y, a, b)

    def div(a: Element, b: Element): Element = doOp((uns, x, _) => if (uns) x else x + 1, a, b)

    def eqq(a: Element, b: Element): Element = fromType(Some(Types.BoolT))

    def gt(a: Element, b: Element): Element = fromType(Some(Types.BoolT))
  }

  object Intraprocedural {
    trait VariableSizeAnalysisEval extends ValueAnalysisMisc with Dependencies[CfgNode] {
      val valuelattice: BitnessLattice.type

      override def eval(exp: AExpr, env: statelattice.Element)(implicit declData: DeclarationData): valuelattice.Element = {
        exp match {
          case ACast(toType, _, _) => valuelattice.fromType(Some(toType))
          case AInput(_) => valuelattice.fromType(Some(Types.BigIntT))
          case _ => super.eval(exp, env)
        }
      }
    }

    class SimpleSolver(cfg: IntraproceduralProgramCfg)(implicit declData: DeclarationData) extends IntraprocValueAnalysisSimpleSolver(cfg, BitnessLattice)
      with VariableSizeAnalysisEval
  }
}