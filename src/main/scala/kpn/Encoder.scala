

package kpn

import ap.parser._
import IExpression.{ConstantTerm, Sort}
import ap.types.MonoSortedPredicate
import ap.theories.ADT

import lazabs.horn.bottomup.HornClauses

import scala.collection.immutable.VectorBuilder

object Encoder {
  import IExpression._
  import HornClauses._

  abstract class QueueEncoder {
    def apply(s : Sort) : QueueEncoderInstance
  }

  abstract class QueueEncoderInstance {
    val sort : Sort
    def isEmpty(t : ITerm) : IFormula
    def enqueue(pre : ITerm, el : ITerm, post : ITerm) : IFormula
    def dequeue(pre : ITerm, el : ITerm, post : ITerm) : IFormula
    val axioms : Seq[Clause]
  }

  object ListQueueEncoder extends QueueEncoder {
    def apply(elementSort : Sort) = new QueueEncoderInstance {
      val (sort, nil, cons, head, tail, _) =
        ADT.createListType(elementSort.name + "_list", elementSort)
      val enqueuePred =
        MonoSortedPredicate(elementSort.name + "_enqueue",
                            List(sort, elementSort, sort))

      def isEmpty(t : ITerm) : IFormula = t === nil()

      def enqueue(pre : ITerm, el : ITerm, post : ITerm) : IFormula =
        enqueuePred(pre, el, post)

      def dequeue(pre : ITerm, el : ITerm, post : ITerm) : IFormula =
        pre === cons(el, post)

      val axioms = {
        val pre    = sort newConstant "pre"
        val post   = sort newConstant "post"
        val value1 = elementSort newConstant "value1"
        val value2 = elementSort newConstant "value2"
        List(
          enqueuePred(nil(), value1, cons(value1, nil())) :-
            true,
          enqueuePred(cons(value2, pre), value1, cons(value2, post)) :-
            enqueuePred(pre, value1, post)
        )
      }
    }
  }

  abstract class HistoryEncoder {
    def apply(s : Sort) : HistoryEncoderInstance
  }

  abstract class HistoryEncoderInstance {
    val sort : Sort
    def isEmpty(t : ITerm) : IFormula
    def add(pre : ITerm, el : ITerm, post : ITerm) : IFormula
  }

  object ListHistoryEncoder extends HistoryEncoder {
    def apply(s : Sort) = new HistoryEncoderInstance {
      val (sort, nil, cons, head, tail, _) =
        ADT.createListType(s.name + "_list", s)
      def isEmpty(t : ITerm) : IFormula = t === nil()
      def add(pre : ITerm, el : ITerm, post : ITerm) : IFormula =
        post === cons(el, pre)
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

  val CN = allChans.size
  val PN = processes.size

  // TODO: have per-process ADTs?
  val eventADT = {
    val sendEvents =
      for (c <- allChans)
      yield ("send_" + c.name,
             ADT.CtorSignature(List(("value_sent_" + c.name,
                                     ADT.OtherSort(c.sort))),
                               ADT.ADTSort(0)))
    val recvEvents =
      for (c <- allChans)
      yield ("receive_" + c.name,
             ADT.CtorSignature(List(), ADT.ADTSort(0)))
    val errorEvent =
      ("error", ADT.CtorSignature(List(), ADT.ADTSort(0)))
    new ADT (List("Event"),
             sendEvents ++ recvEvents ++ List(errorEvent))
  }

  val Seq(eventSort) = eventADT.sorts

  val sendEvent  = eventADT.constructors take CN
  val recvEvent  = eventADT.constructors drop CN take CN
  val errorEvent = eventADT.constructors.last

  val channelQueues =
    for (chan <- allChans)
    yield queueEncoders.getOrElse(chan, ListQueueEncoder)(chan.sort)
  val channelHistories =
    for (chan <- allChans)
    yield chanHistoryEncoders.getOrElse(chan, ListHistoryEncoder)(chan.sort)

  val processEventHistories =
    for (n <- 0 until PN)
    yield eventEncoders.getOrElse(n, ListHistoryEncoder)(eventSort)
  val processChanHistories =
    for (n <- 0 until PN)
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

  val stateChanQueueOffset = 0
  val stateChanHistOffset  = CN
  val stateEventHistOffset = 2*CN

  //////////////////////////////////////////////////////////////////////////////
  // Clauses about the global system execution; processes are
  // represented by their summaries

  def pred2Atom(p : MonoSortedPredicate, prefix : String) : IAtom = {
    val args =
      for ((s, n) <- p.argSorts.zipWithIndex) yield (s newConstant (prefix + n))
    p(args : _*)
  }

  val globalClauses = {
    val globalPreState  = pred2Atom(globalState, "e")
    val globalPostState = pred2Atom(globalState, "o")

    val chanQueuePre    = globalPreState.args drop stateChanQueueOffset take CN
    val chanHistPre     = globalPreState.args drop stateChanHistOffset take CN
    val eventHistPre    = globalPreState.args drop stateEventHistOffset take PN
    val chanQueuePost   = globalPostState.args drop stateChanQueueOffset take CN
    val chanHistPost    = globalPostState.args drop stateChanHistOffset take CN
    val eventHistPost   = globalPostState.args drop stateEventHistOffset take PN

    val procChanHist =
      for (pn <- 0 until PN)
      yield (for (c <- processInChans(pn); cn = allChans indexOf c)
             yield chanHistPre(cn))

    val initClause = {
      val queueInits =
        and(for ((t, c) <- chanQueuePost zip channelQueues)
            yield (c isEmpty t))
      val chanHistInits =
        and(for ((t, c) <- chanHistPost zip channelHistories)
            yield (c isEmpty t))
      val procHistInits =
        and(for ((t, p) <- eventHistPost zip processEventHistories)
            yield (p isEmpty t))
      globalPostState :- (queueInits, chanHistInits, procHistInits)
    }

    val recvClauses =
      for ((p, pn) <- processes.zipWithIndex;
           c <- processInChans(pn);
           cn = allChans indexOf c) yield {
        val postArgs =
          globalPreState.args.updated(stateChanQueueOffset + cn, chanQueuePost(cn))
                             .updated(stateChanHistOffset + cn, chanHistPost(cn))
                             .updated(stateEventHistOffset + pn, eventHistPost(pn))
        val value =
          c.sort newConstant "value"
        val event =
          recvEvent(cn)()

        val deq =
          channelQueues(cn).dequeue(chanQueuePre(cn), value, chanQueuePost(cn))
        val chanhistadd =
          channelHistories(cn).add(chanHistPre(cn), value, chanHistPost(cn))
        val eventhistadd =
          processEventHistories(pn).add(eventHistPre(pn), event, eventHistPost(pn))

        globalState(postArgs : _*) :- (globalPreState,
                                       processSummaries(pn)(procChanHist(pn) ++
                                                              List(eventHistPre(pn), event) : _*),
                                       deq, chanhistadd, eventhistadd)
      }

    val sendClauses =
      for ((p, pn) <- processes.zipWithIndex;
           c <- processOutChans(pn);
           cn = allChans indexOf c) yield {
        val postArgs =
          globalPreState.args.updated(stateChanQueueOffset + cn, chanQueuePost(cn))
                             .updated(stateEventHistOffset + pn, eventHistPost(pn))
        val value =
          c.sort newConstant "value"
        val event =
          sendEvent(cn)(value)

        val enc =
          channelQueues(cn).enqueue(chanQueuePre(cn), value, chanQueuePost(cn))
        val eventhistadd =
          processEventHistories(pn).add(eventHistPre(pn), event, eventHistPost(pn))

        globalState(postArgs : _*) :- (globalPreState,
                                       processSummaries(pn)(procChanHist(pn) ++
                                                              List(eventHistPre(pn), event) : _*),
                                       enc, eventhistadd)
      }

    val errorClauses =
      for ((p, pn) <- processes.zipWithIndex) yield {
        false :- (globalPreState,
                  processSummaries(pn)(procChanHist(pn) ++
                                         List(eventHistPre(pn), errorEvent()) : _*))
      }

    List(initClause) ++ recvClauses ++ sendClauses ++ errorClauses
  }

  //////////////////////////////////////////////////////////////////////////////
  // Clauses about the individual processes

  val processClauses = {

    val clauses =
      for ((p, pn) <- processes.zipWithIndex) yield {

        val summary =
          processSummaries(pn)

        val chanHists =
          for (c <- processInChans(pn); cn = allChans indexOf c)
          yield channelHistories(cn)
        val eventHist =
          processEventHistories(pn)
        val consts =
          processConsts(pn)

        val argSorts =
          (chanHists map (_.sort)) ++ List(eventHist.sort) ++ (consts map (Sort sortOf _))

        var cnt = 0
        def newPred = {
          cnt = cnt + 1
          new MonoSortedPredicate("proc_" + pn + "_" + (cnt - 1), argSorts)
        }

        // TODO: use the original constants, for better readibility?
        val preAtom       = pred2Atom(newPred, "e")
        val postAtom      = pred2Atom(newPred, "o")

        val eventOffset   = chanHists.size
        val constsOffset  = chanHists.size + 1

        val chanHistsPre  = preAtom.args take chanHists.size
        val eventHistPre  = preAtom.args(chanHists.size)
        val constsPre     = preAtom.args drop constsOffset
        val chanHistsPost = postAtom.args take chanHists.size
        val eventHistPost = postAtom.args(chanHists.size)
        val constsPost    = postAtom.args drop constsOffset

        val preSubst      = (consts zip constsPre).toMap

        val clauses       = new VectorBuilder[Clause]

        clauses += (preAtom :- (and(for ((h, t) <- chanHists zip chanHistsPre)
                                    yield (h isEmpty t)),
                                eventHist isEmpty eventHistPre,
                                constsPre === 0))

        def toPre(p : Predicate) = p(preAtom.args : _*)

        def translate(p : Prog,
                      prePred : Predicate,
                      postPred : Predicate) : Unit = p match {
          case Skip =>
            clauses += (toPre(postPred) :- toPre(prePred))
          case Sequence(left, right) => {
            val intPred = newPred
            translate(left, prePred, intPred)
            translate(right, intPred, postPred)
          }
          case While(cond, body) => {
            val startPred = newPred
            val guard = ConstantSubstVisitor(cond, preSubst)
            clauses += (toPre(startPred) :- (toPre(prePred), guard))
            clauses += (toPre(postPred) :- (toPre(prePred), ~guard))
            translate(body, startPred, prePred)
          }
          case Assign(v, rhs) => {
            val t        = ConstantSubstVisitor(rhs, preSubst)
            val ind      = consts indexOf v
            val postArgs = preAtom.args.updated(constsOffset + ind, t)
            clauses      += (postPred(postArgs : _*) :- toPre(prePred))
          }
          case Send(c, t) => {
          }
          case Receive(c, v) => {
            val cn          = processInChans(pn) indexOf c
            val event       = recvEvent(cn)()
            val summaryArgs = chanHistsPre ++ List(eventHistPre, event)
            clauses += (summary(summaryArgs : _*) :- toPre(prePred))

            val ind         = consts indexOf v
            val value       = c.sort newConstant "value"
            val chanConstr  = chanHists(cn).add(chanHistsPre(cn), value, chanHistsPost(cn))
            val eventConstr = eventHist.add(eventHistPre, event, eventHistPost)
            val postArgs    = preAtom.args.updated(cn, chanHistsPost(cn))
                                          .updated(eventOffset, eventHistPost)
                                          .updated(constsOffset + ind, i(value))
            clauses += (postPred(postArgs : _*) :- (toPre(prePred), chanConstr, eventConstr))
          }
        }

        translate(p, preAtom.pred, postAtom.pred)

        clauses.result
      }

    clauses.flatten
  }

  val allClauses : Seq[Clause] =
    globalClauses ++ processClauses ++ (channelQueues map (_.axioms)).flatten

}