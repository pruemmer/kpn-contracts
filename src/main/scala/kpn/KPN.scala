


package kpn

import ap.parser._
import IExpression.{ConstantTerm, Sort}
import ap.util.Seqs

/**
 * Syntax for KPNs
 */
object KPN {

  class Channel(val name : String, val sort : Sort) {
    override def toString = name
  }

  /**
   * Individual processes are written in the style of while programs.
   */

  abstract sealed class Prog

  case object Skip                                              extends Prog

  case class  Assign    (v : ConstantTerm, rhs : ITerm)         extends Prog
  case class  Sequence  (left : Prog, right : Prog)             extends Prog
  case class  IfThenElse(cond : IFormula, b1 : Prog, b2 : Prog) extends Prog
  case class  While     (cond : IFormula, body : Prog)          extends Prog

  case class  Assert    (cond : IFormula)                       extends Prog
  case class  Send      (chan : Channel, msg : ITerm)           extends Prog
  case class  Receive   (chan : Channel, v : ConstantTerm)      extends Prog

  def Prog(stmts : Prog*) : Prog =
    if (stmts.isEmpty)
      Skip
    else
      stmts reduceRight (Sequence(_, _))

  def If(cond : IFormula)(branch : Prog*) =
    IfThenElse(cond, Prog(branch : _*), Skip)

  def While(cond : IFormula)(body : Prog*) : Prog =
    While(cond, Prog(body : _*))

  implicit def var2LHS(v : ConstantTerm) = new AnyRef {
    def :=(that : ITerm) = Assign(v, that)
    def <--(chan : Channel) = Receive(chan, v)
  }

  implicit def term2RichTerm(t : ITerm) = new AnyRef {
    def -->(chan : Channel) = Send(chan, t)
  }

  implicit def const2RichTerm(v : ConstantTerm) = new AnyRef {
    def -->(chan : Channel) = Send(chan, v)
  }

  implicit def ite2RichIte(p : IfThenElse) = new AnyRef {
    def Else(branch : Prog*) =
      IfThenElse(p.cond, p.b1, Prog(branch : _*))
  }

  /**
   * Some helper functions
   */

  def constants(p : Prog) : Set[ConstantTerm] = p match {
    case Skip                     => Set()
    case Assign(c, t)             => Set(c) ++ (SymbolCollector constants t)
    case Sequence(p1, p2)         => constants(p1) ++ constants(p2)
    case IfThenElse(cond, p1, p2) => constants(p1) ++ constants(p2) ++
                                     (SymbolCollector constants cond)
    case While(cond, p)           => constants(p) ++
                                     (SymbolCollector constants cond)
    case Assert(cond)             => (SymbolCollector constants cond).toSet
    case Send(_, msg)             => (SymbolCollector constants msg).toSet
    case Receive(_, c)            => Set(c)
  }

  def inChannels(p : Prog) : Set[Channel] = p match {
    case Sequence(p1, p2)         => inChannels(p1) ++ inChannels(p2)
    case IfThenElse(cond, p1, p2) => inChannels(p1) ++ inChannels(p2)
    case While(cond, p)           => inChannels(p)
    case Receive(chan, _)         => Set(chan)
    case _                        => Set()
  }

  def outChannels(p : Prog) : Set[Channel] = p match {
    case Sequence(p1, p2)         => inChannels(p1) ++ inChannels(p2)
    case IfThenElse(cond, p1, p2) => inChannels(p1) ++ inChannels(p2)
    case While(cond, p)           => inChannels(p)
    case Send(chan, _)            => Set(chan)
    case _                        => Set()
  }

  /**
   * Networks
   */

  case class Network(processes : IndexedSeq[Prog]) {
    val processConsts   =
      for (p <- processes) yield constants(p).toSeq.sortBy(_.name)
    val processInChans : IndexedSeq[Seq[Channel]] =
      for (p <- processes) yield inChannels(p).toSeq.sortBy(_.name)
    val processOutChans : IndexedSeq[Seq[Channel]] =
      for (p <- processes) yield outChannels(p).toSeq.sortBy(_.name)

    // Channels have unique writers and readers
    assert((0 until processes.size) forall { i =>
             ((i+1) until processes.size) forall { j =>
               Seqs.disjointSeq(processInChans(i).toSet, processInChans(j)) &&
               Seqs.disjointSeq(processOutChans(i).toSet, processOutChans(j))
             }})

    val allConsts : Seq[ConstantTerm] =
      (for (cs <- processConsts; c <- cs) yield c).distinct
    val allChans : Seq[Channel] =
      (for (cs <- processInChans ++ processOutChans; c <- cs) yield c).distinct
  }

  def Network(processes : Seq[Prog]) : Network = Network(processes.toIndexedSeq)

}


object Main extends App {

  println("hello")

  println(ExampleProg1.procA)
  println(ExampleProg1.procB)

}
