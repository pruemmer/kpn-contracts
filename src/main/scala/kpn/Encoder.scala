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
import ap.types.MonoSortedPredicate
import ap.theories.ADT

import lazabs.horn.bottomup.HornClauses

import scala.collection.immutable.VectorBuilder

object Encoder {
  import IExpression._
  import HornClauses._
  import HistoryEncoders.{History, HistoryEncoderInstance}
  import KPN._

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
              queueEncoders         : Map[KPN.Channel, QueueEncoders.QueueEncoder] =
                Map(),
              chanHistoryEncoders   : Map[KPN.Channel, HistoryEncoders.HistoryEncoder] =
                Map(),
              eventEncoders         : Map[KPN.NodeLocator, HistoryEncoders.HistoryEncoder] =
                Map(),
              defaultQueueEncoder   : QueueEncoders.QueueEncoder =
                QueueEncoders.ListQueueEncoder,
              defaultHistoryEncoder : HistoryEncoders.HistoryEncoder =
                HistoryEncoders.ListHistoryEncoder,
              summaries             : Map[KPN.NodeLocator, Encoder.Summary] =
                Map(),
              systemSchedule        : Option[Scheduler.Schedule] =
                None) {

  import KPN._
  import Encoder._
  import IExpression._
  import HornClauses._
  import Scheduler.{Schedule, RecvEvent, SendEvent, ErrorEvent}
  import HistoryEncoders.HistoryInstance

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
