/**
 * This file is part of the KPN encoder.
 * Copyright (c) 2021-2024 Philipp Ruemmer. All rights reserved.
 * 
 * Redistribution and use in source and binary forms, with or without
 * modification, are permitted provided that the following conditions are met:
 * 
 * * Redistributions of source code must retain the above copyright notice, this
 *   list of conditions and the following disclaimer.
 * 
 * * Redistributions in binary form must reproduce the above copyright notice,
 *   this list of conditions and the following disclaimer in the documentation
 *   and/or other materials provided with the distribution.
 * 
 * * Neither the name of the authors nor the names of their
 *   contributors may be used to endorse or promote products derived from
 *   this software without specific prior written permission.
 * 
 * THIS SOFTWARE IS PROVIDED BY THE COPYRIGHT HOLDERS AND CONTRIBUTORS
 * "AS IS" AND ANY EXPRESS OR IMPLIED WARRANTIES, INCLUDING, BUT NOT
 * LIMITED TO, THE IMPLIED WARRANTIES OF MERCHANTABILITY AND FITNESS
 * FOR A PARTICULAR PURPOSE ARE DISCLAIMED. IN NO EVENT SHALL THE
 * COPYRIGHT HOLDER OR CONTRIBUTORS BE LIABLE FOR ANY DIRECT,
 * INDIRECT, INCIDENTAL, SPECIAL, EXEMPLARY, OR CONSEQUENTIAL DAMAGES
 * (INCLUDING, BUT NOT LIMITED TO, PROCUREMENT OF SUBSTITUTE GOODS OR
 * SERVICES; LOSS OF USE, DATA, OR PROFITS; OR BUSINESS INTERRUPTION)
 * HOWEVER CAUSED AND ON ANY THEORY OF LIABILITY, WHETHER IN CONTRACT,
 * STRICT LIABILITY, OR TORT (INCLUDING NEGLIGENCE OR OTHERWISE)
 * ARISING IN ANY WAY OUT OF THE USE OF THIS SOFTWARE, EVEN IF ADVISED
 * OF THE POSSIBILITY OF SUCH DAMAGE.
 */

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
      allChans filterNot inChans.toSet filterNot outChans.toSet
    val directInternalChans : Seq[Channel] =
      allInChans filter allOutChans.toSet

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

    /**
     * Iterator over all strict sub-nodes.
     */
    def nodeLocIterator : Iterator[(NetworkNode, NodeLocator)] =
      nodeLocIteratorHelp(NodeLocator.top)

    /**
     * Iterator over locators to all sub-nodes, including the network
     * itself.
     */
    def allNodeLocIterator : Iterator[(NetworkNode, NodeLocator)] =
      Iterator((SubnetNode(this), NodeLocator.top)) ++ nodeLocIterator

    /**
     * Iterator over locators to all strict sub-nodes.
     */
    def locIterator : Iterator[NodeLocator] =
      nodeLocIterator.map(_._2)

    /**
     * Iterator over locators to all sub-nodes, including the network
     * itself.
     */
    def allLocIterator : Iterator[NodeLocator] =
      allNodeLocIterator.map(_._2)

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
    def isTop = path.isEmpty
    def down(n : Int) = NodeLocator(n :: path)
    def apply(n : Int) = down(n)
    def up = NodeLocator(path.tail)
    def ++(that : NodeLocator) = NodeLocator(that.path ::: this.path)
    override def toString() =
      if (path.isEmpty)
        "top"
      else
        path.reverse.mkString("-")
  }

}


object SolveUtil {

  abstract sealed class Result
  case object Safe    extends Result
  case object Unsafe  extends Result
  case object Timeout extends Result

  def solve(name         : String,
            network      : KPN.Network,
            contracts    : Map[Int, Encoder.Summary] = Map(),
            schedule     : Option[Scheduler.Schedule] = None,
            schedules    : Map[KPN.NodeLocator, Scheduler.Schedule] = Map(),
            debug        : Boolean = false,
            printSol     : Boolean = false,
            enableAssert : Boolean = false,
            quiet        : Boolean = false,
            queueEncoder : QueueEncoders.QueueEncoder =
              QueueEncoders.Capacity1QueueEncoder,
            historyEncoder : HistoryEncoders.HistoryEncoder =
              HistoryEncoders.Capacity1HistoryEncoder) : Result = {

    ap.util.Debug.enableAllAssertions(enableAssert)
    GlobalParameters.get.assertions = enableAssert

    if (!quiet) {
      println("Analysing KPN " + name)
      println
    }

    val locContracts =
      for ((n, s) <- contracts) yield (KPN.NodeLocator.top.down(n), s)

    val allSchedules =
      schedule match {
        case Some(s) => schedules + (KPN.NodeLocator.top -> s)
        case None    => schedules
      }

    val encoder =
      new Encoder(network,
                  defaultQueueEncoder = queueEncoder,
                  defaultHistoryEncoder = historyEncoder,
                  summaries = locContracts,
                  schedules = allSchedules)

    if (debug)
      for (c <- encoder.allClauses)
        println(c.toPrologString)

    if (!quiet) {
      println
      println("Solving ...")
    }

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
          Safe
        case Right(cex) => {
          cex.prettyPrint
          GlobalParameters.get.pngNo = false
          GlobalParameters.get.eogCEX = true
          Util.show(cex map (_._1), "kpn")
          Unsafe
        }
      }
    } else {
      GlobalParameters.get.log = false
      if (SimpleWrapper.isSat(encoder.allClauses)) {
        println("SAFE")
        Safe
      } else {
        println("UNSAFE")
        Unsafe
      }
    }
  }

}


