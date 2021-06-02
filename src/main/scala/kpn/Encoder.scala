

package kpn

import ap.parser._
import IExpression.{ConstantTerm, Sort}
import ap.types.MonoSortedPredicate
import ap.theories.ADT

import lazabs.horn.bottomup.HornClauses

object Encoder {
  import IExpression._

  abstract class QueueEncoder {
    def apply(s : Sort) : QueueEncoderInstance
  }

  abstract class QueueEncoderInstance {
    val sort : Sort
    def isEmpty(t : ITerm) : IFormula
  }

  object ListQueueEncoder extends QueueEncoder {
    def apply(s : Sort) = new QueueEncoderInstance {
      val (sort, nil, cons, head, tail, _) =
        ADT.createListType(s.name + "_list", s)
      def isEmpty(t : ITerm) : IFormula = t === nil()
    }
  }

  abstract class HistoryEncoder {
    def apply(s : Sort) : HistoryEncoderInstance
  }

  abstract class HistoryEncoderInstance {
    val sort : Sort
    def isEmpty(t : ITerm) : IFormula
  }

  object ListHistoryEncoder extends HistoryEncoder {
    def apply(s : Sort) = new HistoryEncoderInstance {
      val (sort, nil, cons, head, tail, _) =
        ADT.createListType(s.name + "_list", s)
      def isEmpty(t : ITerm) : IFormula = t === nil()
    }
  }
}


class Encoder(network             : KPN.Network,
              queueEncoders       : Map[KPN.Channel, Encoder.QueueEncoder] = Map(),
              chanHistoryEncoders : Map[KPN.Channel, Encoder.HistoryEncoder] = Map(),
              eventEncoders       : Map[Int, Encoder.HistoryEncoder] = Map()) {

  import KPN._
  import Encoder._
  import IExpression._
  import HornClauses._

  import network.{processes, processConsts, processInChans, processOutChans,
                  allChans}

  // TODO: have per-process ADTs?
  val eventADT = {
    val readEvents =
      for (c <- allChans)
      yield ("send_" + c.name,
             ADT.CtorSignature(List(("value_sent_" + c.name,
                                     ADT.OtherSort(c.sort))),
                               ADT.ADTSort(0)))
    val writeEvents =
      for (c <- allChans)
      yield ("receive_" + c.name,
             ADT.CtorSignature(List(("value_recv_" + c.name,
                                     ADT.OtherSort(c.sort))),
                               ADT.ADTSort(0)))
    val errorEvent =
      ("error", ADT.CtorSignature(List(), ADT.ADTSort(0)))
    new ADT (List("Event"),
             readEvents ++ writeEvents ++ List(errorEvent))
  }

  val Seq(eventSort) = eventADT.sorts

  println(eventADT)

  val channelQueues =
    for (chan <- allChans)
    yield queueEncoders.getOrElse(chan, ListQueueEncoder)(chan.sort)
  val channelHistories =
    for (chan <- allChans)
    yield chanHistoryEncoders.getOrElse(chan, ListHistoryEncoder)(chan.sort)

  val processEventHistories =
    for (n <- 0 until processes.size)
    yield eventEncoders.getOrElse(n, ListHistoryEncoder)(eventSort)
  val processChanHistories =
    for (n <- 0 until processes.size)
    yield (for ((c, h) <- allChans zip channelHistories;
                if processInChans(n) contains c)
           yield h)

  val processSummaries =
    for ((((p, h), cs), n) <-
         (processes zip processEventHistories zip processChanHistories).zipWithIndex)
    yield new MonoSortedPredicate("summary_" + n,
                                  (cs map (_.sort)) ++ List(h.sort, eventSort))

  val globalState =
    new MonoSortedPredicate("state",
                            (channelQueues map (_.sort)) ++
                              (channelHistories map (_.sort)) ++
                              (processEventHistories map (_.sort)))

  def pred2Atom(p : MonoSortedPredicate, prefix : String) : IAtom = {
    val args =
      for ((s, n) <- p.argSorts.zipWithIndex) yield (s newConstant (prefix + n))
    p(args : _*)
  }

  val globalPreState  = pred2Atom(globalState, "e")
  val globalPostState = pred2Atom(globalState, "o")

  val globalClauses = {
    val initClause = globalPreState :- true
    List(initClause)
  }

  for (c <- globalClauses)
    println(c.toPrologString)

}
