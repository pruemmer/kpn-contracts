

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

  object Capacity1QueueEncoder extends QueueEncoder {
    def apply(elementSort : Sort) = new QueueEncoderInstance {
      val name = elementSort.name + "_queue1"
      val (sort, record, Seq(queue_size, queue_value)) =
        ADT.createRecordType(name,
                             List((name + "_size", Sort.Integer),
                                  (name + "_value", elementSort)))

      def isEmpty(t : ITerm) : IFormula = queue_size(t) === 0

      def enqueue(pre : ITerm, el : ITerm, post : ITerm) : IFormula =
        (queue_size(post) === queue_size(pre) + 1) &
        ite(queue_size(pre) === 0,
            queue_value(post) === el,
            queue_value(post) === queue_value(pre))

      def dequeue(pre : ITerm, el : ITerm, post : ITerm) : IFormula =
        (queue_size(pre) > 0) &
        (queue_size(post) === queue_size(pre) - 1) &
        (el === queue_value(pre))

      val axioms = List()
    }
  }

  object Capacity2QueueEncoder extends QueueEncoder {
    def apply(elementSort : Sort) = new QueueEncoderInstance {
      val name = elementSort.name + "_queue2"
      val (sort, record, Seq(queue_size, queue_value1, queue_value2)) =
        ADT.createRecordType(name,
                             List((name + "_size", Sort.Integer),
                                  (name + "_value1", elementSort),
                                  (name + "_value2", elementSort)))

      def isEmpty(t : ITerm) : IFormula = queue_size(t) === 0

      def enqueue(pre : ITerm, el : ITerm, post : ITerm) : IFormula =
        (queue_size(post) === queue_size(pre) + 1) &
        ((queue_size(pre) === 0 & queue_value1(post) === el) |
           (queue_size(pre) === 1 &
              queue_value1(post) === queue_value1(pre) &
              queue_value2(post) === el) |
           (queue_size(pre) >= 2 &
              queue_value1(post) === queue_value1(pre) &
              queue_value2(post) === queue_value2(pre)))

      def dequeue(pre : ITerm, el : ITerm, post : ITerm) : IFormula =
        (queue_size(pre) > 0) &
        (queue_size(post) === queue_size(pre) - 1) &
        (el === queue_value1(pre)) &
        (queue_value1(post) === queue_value2(pre))

      val axioms = List()
    }
  }

  abstract class HistoryEncoder {
    def apply(s : Sort) : HistoryEncoderInstance
  }

  abstract class HistoryEncoderInstance {
    val sort : Sort
    def isEmpty(t : ITerm) : IFormula
    def add(pre : ITerm, el : ITerm, post : ITerm) : IFormula
    def last(hist : ITerm) : ITerm
  }

  object ListHistoryEncoder extends HistoryEncoder {
    def apply(s : Sort) = new HistoryEncoderInstance {
      val (sort, nil, cons, head, tail, _) =
        ADT.createListType(s.name + "_list", s)
      def isEmpty(t : ITerm) : IFormula = t === nil()
      def add(pre : ITerm, el : ITerm, post : ITerm) : IFormula =
        post === cons(el, pre)
      def last(hist : ITerm) : ITerm =
        head(hist)
    }
  }

  object Capacity1HistoryEncoder extends HistoryEncoder {
    def apply(elementSort : Sort) = new HistoryEncoderInstance {
      val name = elementSort.name + "_hist1"
      val (sort, record, Seq(hist_empty, hist_value)) =
        ADT.createRecordType(name,
                             List((name + "_empty", Sort.Bool),
                                  (name + "_value", elementSort)))
      def isEmpty(t : ITerm) : IFormula =
        t === record(ADT.BoolADT.True, elementSort.witness.get)
      def add(pre : ITerm, el : ITerm, post : ITerm) : IFormula =
        post === record(ADT.BoolADT.False, el)
      def last(hist : ITerm) : ITerm =
        hist_value(hist)
    }
  }

  object Capacity2HistoryEncoder extends HistoryEncoder {
    def apply(elementSort : Sort) = new HistoryEncoderInstance {
      val name = elementSort.name + "_hist2"
      val (sort, record, Seq(hist_empty, hist_value1, hist_value2)) =
        ADT.createRecordType(name,
                             List((name + "_empty", Sort.Bool),
                                  (name + "_value1", elementSort),
                                  (name + "_value2", elementSort)))
      def isEmpty(t : ITerm) : IFormula =
        t === record(ADT.BoolADT.True, elementSort.witness.get, elementSort.witness.get)
      def add(pre : ITerm, el : ITerm, post : ITerm) : IFormula =
        post === record(ADT.BoolADT.False, el, hist_value1(pre))
      def last(hist : ITerm) : ITerm =
        hist_value1(hist)
    }
  }

  //////////////////////////////////////////////////////////////////////////////

  /**
   * Generic interface to buffer and event histories
   */
  trait History {
    val sort : Sort
    def isEmpty : IFormula
    def last : ITerm
  }

  class HistoryInstance(t : ITerm,
                        encoder : HistoryEncoderInstance) extends History {
    val sort : Sort = encoder.sort
    def isEmpty : IFormula = encoder.isEmpty(t)
    def last : ITerm = encoder.last(t)
  }

  /**
   * Simple API to analyse terms representing events.
   */
  trait EventAPI {
    implicit def toRichTerm(t : ITerm) : RichEventTerm
    def recvEvent(c : KPN.Channel) : ITerm
    def errorEvent                 : ITerm
  }

  trait RichEventTerm {
    def isRecv   (c : KPN.Channel) : IFormula
    def isSend   (c : KPN.Channel) : IFormula
    def send     (c : KPN.Channel) : ITerm
    def valueSent(c : KPN.Channel) : ITerm
    def isError                    : IFormula
  }

  /**
   * A summary is a relation between the input histories, the event
   * history, and an event. The summary also receives an API for the
   * the event ADT as an argument, containing the constructors for
   * send, receive, and error events.
   */
  type Summary = (Map[KPN.Channel, History], History,
                  ITerm, EventAPI) => IFormula

  /////////////////////////////////////////////////////////////////////////////
  // Clauses about the individual processes

  import KPN._
  import Encoder._
  import IExpression._
  import HornClauses._

  def pred2Atom(p : MonoSortedPredicate, prefix : String) : IAtom = {
    val args =
      for ((s, n) <- p.argSorts.zipWithIndex) yield (s newConstant (prefix + n))
    p(args : _*)
  }

  def encodeProg(prog       : Prog,
                 predPrefix : String,
                 summary    : Seq[ITerm] => IFormula,
                 inChans    : Seq[Channel],
                 chanHists  : Seq[HistoryEncoderInstance],
                 eventHist  : HistoryEncoderInstance,
                 eventAPI   : EventAPI) : Seq[Clause] = {
    import eventAPI._

    val consts = prog.constants

    val argSorts =
      (chanHists map (_.sort)) ++
       List(eventHist.sort) ++
       (consts map (Sort sortOf _))

    var cnt = 0
    def newPred = {
      cnt = cnt + 1
      new MonoSortedPredicate(predPrefix + "_" + (cnt - 1), argSorts)
    }

    val eventOffset   = chanHists.size
    val constsOffset  = chanHists.size + 1

    val preAtom       = {
      val p = newPred
      val a = pred2Atom(p, "e")
      newPred((a.args take constsOffset) ++ (consts map i) : _*)
    }
    val postAtom      = pred2Atom(newPred, "o")

    val chanHistsPre  = preAtom.args take chanHists.size
    val eventHistPre  = preAtom.args(chanHists.size)
    val constsPre     = preAtom.args drop constsOffset
    val chanHistsPost = postAtom.args take chanHists.size
    val eventHistPost = postAtom.args(chanHists.size)
    val constsPost    = postAtom.args drop constsOffset

    val clauses       = new VectorBuilder[Clause]

    clauses += (preAtom :- (and(for ((h, t) <- chanHists zip chanHistsPre)
                                yield (h isEmpty t)),
                            eventHist isEmpty eventHistPre,
                            and(for (c <- constsPre)
                                yield (c === Sort.sortOf(c).witness.get))))

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
            val headPred, startPred = newPred
            clauses += (toPre(headPred)  :- toPre(prePred))
            clauses += (toPre(startPred) :- (toPre(headPred), cond))
            clauses += (toPre(postPred)  :- (toPre(headPred), ~cond))
            translate(body, startPred, headPred)
          }

          case IfThenElse(cond, body1, body2) => {
            val thenPred, elsePred = newPred
            clauses += (toPre(thenPred) :- (toPre(prePred), cond))
            clauses += (toPre(elsePred) :- (toPre(prePred), ~cond))
            translate(body1, thenPred, postPred)
            translate(body2, elsePred, postPred)
          }

          case Assign(v, rhs) => {
            val ind      = consts indexOf v
            val postArgs = preAtom.args.updated(constsOffset + ind, rhs)
            clauses      += (postPred(postArgs : _*) :- toPre(prePred))
          }

          case Havoc(v) => {
            val ind      = consts indexOf v
            val fresh    = (Sort sortOf v) newConstant (v.name + "_fresh")
            val postArgs = preAtom.args.updated(constsOffset + ind,
                                                IConstant(fresh))
            clauses      += (postPred(postArgs : _*) :- toPre(prePred))
          }

          case Assert(cond) => {
            val event       = errorEvent
            val summaryArgs = chanHistsPre ++ List(eventHistPre, event)
            clauses += (summary(summaryArgs) :- (toPre(prePred), ~cond))
            clauses += (toPre(postPred) :-(toPre(prePred), cond))
          }

          case Send(c, t) => {
            val event       = t.send(c)
            val summaryArgs = chanHistsPre ++ List(eventHistPre, event)
            clauses += (summary(summaryArgs) :- toPre(prePred))

            val eventConstr = eventHist.add(eventHistPre, event, eventHistPost)
            val postArgs    = preAtom.args.updated(eventOffset, eventHistPost)
            clauses += (postPred(postArgs : _*) :-(toPre(prePred), eventConstr))
          }

          case Receive(c, v) => {
            val pcn         = inChans indexOf c
            val event       = recvEvent(c)
            val summaryArgs = chanHistsPre ++ List(eventHistPre, event)
            clauses += (summary(summaryArgs) :- toPre(prePred))

            val ind         = consts indexOf v
            val value       = c.sort newConstant "value"
            val chanConstr  = chanHists(pcn).add(chanHistsPre(pcn), value,
                                                 chanHistsPost(pcn))
            val eventConstr = eventHist.add(eventHistPre, event, eventHistPost)
            val postArgs    = preAtom.args.updated(pcn, chanHistsPost(pcn))
                                          .updated(eventOffset, eventHistPost)
                                          .updated(constsOffset + ind, i(value))
            clauses += (postPred(postArgs : _*) :-
                          (toPre(prePred), chanConstr, eventConstr))
          }
        }

    translate(prog, preAtom.pred, postAtom.pred)

    clauses.result
  }

}

////////////////////////////////////////////////////////////////////////////////

class Encoder(network               : KPN.Network,
              queueEncoders         : Map[KPN.Channel, Encoder.QueueEncoder] =
                Map(),
              chanHistoryEncoders   : Map[KPN.Channel, Encoder.HistoryEncoder] =
                Map(),
              eventEncoders         : Map[KPN.NodeLocator, Encoder.HistoryEncoder] =
                Map(),
              defaultQueueEncoder   : Encoder.QueueEncoder =
                Encoder.ListQueueEncoder,
              defaultHistoryEncoder : Encoder.HistoryEncoder =
                Encoder.ListHistoryEncoder,
              summaries             : Map[KPN.NodeLocator, Encoder.Summary] =
                Map(),
              systemSchedule        : Option[Scheduler.Schedule] =
                None) {

  import KPN._
  import Encoder._
  import IExpression._
  import HornClauses._
  import Scheduler.{Schedule, RecvEvent, SendEvent, ErrorEvent}

  import network.allChans

  val CN = allChans.size

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

  val eventAPI = new EventAPI {
    implicit def toRichTerm(t : ITerm) = new RichEventTerm {
      def isRecv(c : KPN.Channel) : IFormula =
        eventADT.hasCtor(t, (allChans indexOf c) + CN)
      def isSend(c : KPN.Channel) : IFormula =
        eventADT.hasCtor(t, allChans indexOf c)
      def send(c : KPN.Channel) : ITerm =
        sendEvent(allChans indexOf c)(t)
      def valueSent(c : KPN.Channel) : ITerm =
        eventADT.selectors(allChans indexOf c)(0)(t)
      def isError : IFormula =
        eventADT.hasCtor(t, 2*CN)
    }
    def recvEvent(c : KPN.Channel) : ITerm =
      Encoder.this.recvEvent(allChans indexOf c)()
    def errorEvent : ITerm =
      Encoder.this.errorEvent()
  }

  val channelQueues =
    for (chan <- allChans)
    yield queueEncoders.getOrElse(chan, defaultQueueEncoder)(chan.sort)
  val channelHistories =
    for (chan <- allChans)
    yield chanHistoryEncoders.getOrElse(chan, defaultHistoryEncoder)(chan.sort)

  val processEventHistories =
    (for (n <- network.locIterator)
     yield (n -> eventEncoders.getOrElse(n, defaultHistoryEncoder)(eventSort))).toMap
  val processInChans =
    (for ((n, l) <- network.nodeLocIterator) yield {
       l -> (allChans filter n.inChans.toSet)
     }).toMap
  val processChanHistories =
    (for ((n, l) <- network.nodeLocIterator) yield {
       val hists = for ((c, h) <- allChans zip channelHistories;
                        if n.inChans contains c)
                   yield h
       l -> hists
     }).toMap

  val summaryPreds =
    (for ((n, l) <- network.nodeLocIterator) yield {
       val pred =
         new MonoSortedPredicate("summary_" + l,
                                 (processChanHistories(l) map (_.sort)) ++
                                 List(processEventHistories(l).sort, eventSort))
       l -> pred
     }).toMap

  def instantiateSummary(processId : NodeLocator,
                         chanHistories : Seq[ITerm], eventHistory : ITerm,
                         event : ITerm) : IFormula = {
    assert(summaries contains processId)
    val chans =
      (for (((c, hist), t) <- (processInChans(processId) zip processChanHistories(processId))
                         zip chanHistories)
       yield (c -> new HistoryInstance(t, hist))).toMap
    val evs =
      new HistoryInstance(eventHistory, processEventHistories(processId))
    summaries(processId)(chans, evs, event, eventAPI)
  }

  def summaryFor(processId : NodeLocator, args : Seq[ITerm]) : IFormula =
    if (summaries contains processId) {
      val chanHistories = args take (args.size - 2)
      val eventHistory  = args(args.size - 2)
      val event         = args.last
      instantiateSummary(processId, chanHistories, eventHistory, event)
    } else {
      summaryPreds(processId)(args : _*)
    }

  //////////////////////////////////////////////////////////////////////////////
  // Clauses about the global system execution; processes are
  // represented by their summaries

  val finalSystemSchedule =
    systemSchedule match {
      case Some(s) => s
      case None =>
        Schedule(0,
                 (for (c <- allChans;
                       ev <- List(RecvEvent(c), SendEvent(c)))
                  yield (0, ev, 0)) ++ List((0, ErrorEvent, 0)))
    }

  def subnetClauses(subnetLoc : NodeLocator) : Seq[Clause] = {
    val subnet              = network(subnetLoc).asInstanceOf[SubnetNode].network

    val childLocs           = subnet.childLocators.map(subnetLoc ++ _)
    val PN                  = childLocs.size
    val processes           = childLocs map (network(_))
    val childEventHistories = childLocs map processEventHistories

    val (intChans, intChannelQueues, intChannelHistories) =
      (for (((c, q), h) <- allChans zip channelQueues zip channelHistories;
            if subnet.directInternalChans contains c)
       yield (c, q, h)).unzip3

    val CN = intChans.size

    val globalState =
      new MonoSortedPredicate("state",
                              (intChannelQueues map (_.sort)) ++
                                (intChannelHistories map (_.sort)) ++
                                (childEventHistories map (_.sort)) ++
                                List(Sort.Integer))

    val stateChanQueueOffset           = 0
    val stateChanHistOffset            = CN
    val stateEventHistOffset           = 2*CN
    val stateSystemScheduleStateOffset = globalState.arity - 1

    val globalPreState  = pred2Atom(globalState, "e")
    val globalPostState = pred2Atom(globalState, "o")

    val chanQueuePre    = globalPreState.args drop stateChanQueueOffset take CN
    val chanHistPre     = globalPreState.args drop stateChanHistOffset take CN
    val eventHistPre    = globalPreState.args drop stateEventHistOffset take PN
    val schedStatePre   = globalPreState.args(stateSystemScheduleStateOffset)
    val chanQueuePost   = globalPostState.args drop stateChanQueueOffset take CN
    val chanHistPost    = globalPostState.args drop stateChanHistOffset take CN
    val eventHistPost   = globalPostState.args drop stateEventHistOffset take PN
    val schedStatePost  = globalPostState.args(stateSystemScheduleStateOffset)

    val procChanHistPre =
      for (pn <- 0 until PN)
      yield (for ((c, t) <- intChans zip chanHistPre;
                  if processes(pn).inChans contains c)
             yield t)

    val initClause = {
      val queueInits =
        and(for ((t, c) <- chanQueuePost zip intChannelQueues)
            yield (c isEmpty t))
      val chanHistInits =
        and(for ((t, c) <- chanHistPost zip intChannelHistories)
            yield (c isEmpty t))
      val procHistInits =
        and(for ((t, p) <- eventHistPost zip childEventHistories)
            yield (p isEmpty t))
      val schedInit =
        schedStatePost === finalSystemSchedule.initial
      globalPostState :- (queueInits, chanHistInits, procHistInits, schedInit)
    }
    
    val recvClauses =
      for ((p, pn) <- processes.zipWithIndex;
           c <- processes(pn).inChans;
           cn = intChans indexOf c;
           (schedFrom, RecvEvent(`c`), schedTo) <- finalSystemSchedule.transitions) yield {
        val postArgs =
          globalPreState.args.updated(stateChanQueueOffset + cn, chanQueuePost(cn))
                             .updated(stateChanHistOffset + cn, chanHistPost(cn))
                             .updated(stateEventHistOffset + pn, eventHistPost(pn))
                             .updated(stateSystemScheduleStateOffset, schedStatePost)
        val value =
          c.sort newConstant "value"
        val event =
          recvEvent(cn)()

        val deq =
          intChannelQueues(cn).dequeue(chanQueuePre(cn), value, chanQueuePost(cn))
        val chanhistadd =
          intChannelHistories(cn).add(chanHistPre(cn), value, chanHistPost(cn))
        val eventhistadd =
          childEventHistories(pn).add(eventHistPre(pn), event, eventHistPost(pn))
        val schedConstraints =
          (schedStatePre === schedFrom) & (schedStatePost === schedTo)

        globalState(postArgs : _*) :- (globalPreState,
                                       summaryFor(childLocs(pn),
                                                  procChanHistPre(pn) ++
                                                    List(eventHistPre(pn), event)),
                                       deq, chanhistadd, eventhistadd, schedConstraints)
      }

    val sendClauses =
      for ((p, pn) <- processes.zipWithIndex;
           c <- processes(pn).outChans;
           cn = intChans indexOf c;
           (schedFrom, SendEvent(`c`), schedTo) <- finalSystemSchedule.transitions) yield {
        val postArgs =
          globalPreState.args.updated(stateChanQueueOffset + cn, chanQueuePost(cn))
                             .updated(stateEventHistOffset + pn, eventHistPost(pn))
                             .updated(stateSystemScheduleStateOffset, schedStatePost)
        val value =
          c.sort newConstant "value"
        val event =
          sendEvent(cn)(value)

        val enc =
          intChannelQueues(cn).enqueue(chanQueuePre(cn), value, chanQueuePost(cn))
        val eventhistadd =
          childEventHistories(pn).add(eventHistPre(pn), event, eventHistPost(pn))
        val schedConstraints =
          (schedStatePre === schedFrom) & (schedStatePost === schedTo)

        globalState(postArgs : _*) :- (globalPreState,
                                       summaryFor(childLocs(pn),
                                                  procChanHistPre(pn) ++
                                                    List(eventHistPre(pn), event)),
                                       enc, eventhistadd, schedConstraints)
      }

    val errorClauses =
      for ((p, pn) <- processes.zipWithIndex;
           (schedFrom, ErrorEvent, _) <- finalSystemSchedule.transitions) yield {
        false :- (globalPreState,
                  summaryFor(childLocs(pn),
                             procChanHistPre(pn) ++
                               List(eventHistPre(pn), errorEvent())),
                  schedStatePre === schedFrom)
      }

    List(initClause) ++ recvClauses ++ sendClauses ++ errorClauses
  }

  val globalClauses = subnetClauses(NodeLocator.top)

  //////////////////////////////////////////////////////////////////////////////
  // Clauses about the individual processes

  val processClauses =
    for ((ProgNode(prog), pn) <- network.nodeLocIterator.toList;
         clause <- encodeProg(prog,
                              "proc_" + pn,
                              summaryFor(pn, _),
                              processInChans(pn),
                              processChanHistories(pn),
                              processEventHistories(pn),
                              eventAPI))
    yield clause

  val allClauses : Seq[Clause] =
    globalClauses ++ processClauses ++ (channelQueues map (_.axioms)).flatten

}
