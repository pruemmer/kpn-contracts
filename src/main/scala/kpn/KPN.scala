


package kpn

import ap.parser._
import IExpression.{ConstantTerm, Sort}
import ap.util.Seqs

import lazabs.GlobalParameters
import lazabs.horn.bottomup.SimpleWrapper
import lazabs.horn.Util
import lazabs.horn.bottomup.HornPredAbs.predArgumentSorts

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

  abstract sealed class Prog {
    def constants : Seq[ConstantTerm] =
      progConstants(this).toSeq.sortBy(_.name)
  }

  case object Skip                                              extends Prog

  case class  Assign    (v : ConstantTerm, rhs : ITerm)         extends Prog
  case class  Havoc     (v : ConstantTerm)                      extends Prog
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

  object Havoc {
    def apply(v1 : ConstantTerm, v2 : ConstantTerm, v3 : ConstantTerm*) : Prog =
      Prog(List(Havoc(v1), Havoc(v2)) ++ (for (v <- v3) yield Havoc(v)) : _*)
  }

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

  implicit def int2RichTerm(n : Int) = new AnyRef {
    def -->(chan : Channel) = Send(chan, n)
  }

  implicit def ite2RichIte(p : IfThenElse) = new AnyRef {
    def Else(branch : Prog*) =
      IfThenElse(p.cond, p.b1, Prog(branch : _*))
  }

  /**
   * Some helper functions
   */

  def progConstants(p : Prog) : Set[ConstantTerm] = p match {
    case Skip                     => Set()
    case Assign(c, t)             => Set(c) ++ (SymbolCollector constants t)
    case Havoc(c)                 => Set(c)
    case Sequence(p1, p2)         => progConstants(p1) ++ progConstants(p2)
    case IfThenElse(cond, p1, p2) => progConstants(p1) ++ progConstants(p2) ++
                                     (SymbolCollector constants cond)
    case While(cond, p)           => progConstants(p) ++
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
    case Sequence(p1, p2)         => outChannels(p1) ++ outChannels(p2)
    case IfThenElse(cond, p1, p2) => outChannels(p1) ++ outChannels(p2)
    case While(cond, p)           => outChannels(p)
    case Send(chan, _)            => Set(chan)
    case _                        => Set()
  }

  /**
   * Network nodes.
   */
  abstract sealed class NetworkNode {
    def inChans       : Seq[Channel]
    def internalChans : Seq[Channel]
    def outChans      : Seq[Channel]
    def allChans      : Seq[Channel] = inChans ++ internalChans ++ outChans

    assert(Seqs.disjointSeq(inChans.toSet,  outChans) &&
           Seqs.disjointSeq(inChans.toSet,  internalChans) &&
           Seqs.disjointSeq(outChans.toSet, internalChans))
  }

  /**
   * Atomic network nodes defined by programs.
   */
  case class ProgNode  (prog : Prog)    extends NetworkNode {
    def constants     : Seq[ConstantTerm] = prog.constants
    def inChans       : Seq[Channel]      = inChannels(prog).toSeq.sortBy(_.name)
    def internalChans : Seq[Channel]      = List()
    def outChans      : Seq[Channel]      = outChannels(prog).toSeq.sortBy(_.name)
  }

  /**
   * Compound network nodes defined by sub-networks.
   */
  case class SubnetNode(network : Network) extends NetworkNode {
    def inChans       : Seq[Channel]      = network.inChans
    def internalChans : Seq[Channel]      = network.internalChans
    def outChans      : Seq[Channel]      = network.outChans
  }

  /**
   * Networks, defined by a list of network nodes.
   */
  case class Network(processes : IndexedSeq[NetworkNode]) {
    // Channels have unique writers and readers; internal
    // nodes are not used anywhere else.
    assert((0 until processes.size) forall { i =>
             ((i+1) until processes.size) forall { j =>
               Seqs.disjointSeq(processes(i).inChans.toSet,
                                processes(j).inChans) &&
               Seqs.disjointSeq(processes(i).outChans.toSet,
                                processes(j).outChans)
             }},
           "Channel with multiple readers or multiple writers")
    assert((0 until processes.size) forall { i =>
             ((i+1) until processes.size) forall { j =>
               Seqs.disjointSeq(processes(i).internalChans.toSet,
                                processes(j).allChans) &&
               Seqs.disjointSeq(processes(j).internalChans.toSet,
                                processes(i).allChans)
             }},
           "Internal channel used in illegal context")

    val allChans : Seq[Channel] =
      (for (n <- processes; c <- n.allChans) yield c).distinct
    private val allInChans : Seq[Channel] =
      (for (n <- processes; c <- n.inChans) yield c).distinct
    private val allOutChans : Seq[Channel] =
      (for (n <- processes; c <- n.outChans) yield c).distinct
    val inChans : Seq[Channel] =
      allInChans filterNot allOutChans.toSet
    val outChans : Seq[Channel] =
      allOutChans filterNot allInChans.toSet
    val internalChans : Seq[Channel] =
      allChans filterNot allInChans.toSet filterNot allOutChans.toSet

    def apply(loc : NodeLocator) : NetworkNode =
      locate(loc.path.reverse)

    def childLocators : IndexedSeq[NodeLocator] =
      (for (n <- 0 until processes.size) yield NodeLocator.top.down(n)).toVector

    private def locate(path : List[Int]) : NetworkNode =
      path match {
        case List() =>
          SubnetNode(this)
        case head :: List() =>
          processes(head)
        case head :: tail =>
          processes(head).asInstanceOf[SubnetNode].network.locate(tail)
      }
        
    def nodeLocIterator : Iterator[(NetworkNode, NodeLocator)] =
      nodeLocIteratorHelp(NodeLocator.top)

    def locIterator : Iterator[NodeLocator] =
      nodeLocIterator.map(_._2)

    private def nodeLocIteratorHelp(loc : NodeLocator)
                                  : Iterator[(NetworkNode, NodeLocator)] =
      for ((n, i) <- processes.iterator.zipWithIndex;
           newLoc = loc.down(i);
           sub = (n match {
                    case ProgNode(_) => Iterator.empty
                    case SubnetNode(network) => network.nodeLocIteratorHelp(newLoc)
                  });
           r <- Iterator((n, newLoc)) ++ sub)
      yield r

  }

  def Network(processes : Seq[Prog]) : Network =
    Network(processes.map(ProgNode(_)).toIndexedSeq)

  def Net(nodes : NetworkNode*) : Network =
    Network(nodes.toIndexedSeq)

  implicit def network2node(net : Network) : NetworkNode =
    SubnetNode(net)

  implicit def prog2node(prog : Prog) : NetworkNode =
    ProgNode(prog)

  object NodeLocator {
    def top = NodeLocator(List())
  }

  case class NodeLocator(path : List[Int]) {
    def down(n : Int) = NodeLocator(n :: path)
    def apply(n : Int) = down(n)
    def up = NodeLocator(path.tail)
  }

}


object SolveUtil {

  def solve(name         : String,
            network      : KPN.Network,
            contracts    : Map[Int, Encoder.Summary] = Map(),
            schedule     : Option[Scheduler.Schedule] = None,
            debug        : Boolean = false,
            printSol     : Boolean = false,
            queueEncoder : Encoder.QueueEncoder =
              Encoder.Capacity1QueueEncoder,
            historyEncoder : Encoder.HistoryEncoder =
              Encoder.Capacity1HistoryEncoder) : Unit = {
    val assertions = false

    ap.util.Debug.enableAllAssertions(assertions)
    GlobalParameters.get.assertions = assertions

    println("Analysing KPN " + name)

    println

    val locContracts =
      for ((n, s) <- contracts) yield (KPN.NodeLocator.top.down(n), s)

    val encoder =
      new Encoder(network,
                  defaultQueueEncoder = queueEncoder,
                  defaultHistoryEncoder = historyEncoder,
                  summaries = locContracts,
                  systemSchedule = schedule)

    if (debug)
      for (c <- encoder.allClauses)
        println(c.toPrologString)

    println
    println("Solving ...")

    if (printSol || debug) {
      GlobalParameters.get.log = debug
      SimpleWrapper.solve(encoder.allClauses, debuggingOutput = debug) match {
        case Left(sol) =>
          for ((p, f) <- sol.toSeq.sortBy(_._1.name)) {
            val sorts  = predArgumentSorts(p)
            val consts = (for ((s, n) <- sorts.zipWithIndex)
                          yield IExpression.i(s newConstant ("x" + n))).toList
            val solWithConsts = VariableSubstVisitor(f, (consts, 0))
            println(p.name + ":\t" + PrincessLineariser.asString(solWithConsts))
          }
        case Right(cex) => {
          cex.prettyPrint
          GlobalParameters.get.pngNo = false
          GlobalParameters.get.eogCEX = true
          Util.show(cex map (_._1), "kpn")
        }
      }
    } else {
      GlobalParameters.get.log = false
      if (SimpleWrapper.isSat(encoder.allClauses))
        println("SAFE")
      else
        println("UNSAFE")
    }
  }

}


