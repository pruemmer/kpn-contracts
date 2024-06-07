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
import ap.theories.ADT

object TestProg1 {

  import KPN._
  import IExpression._

  val c = Sort.Integer newConstant "c"
  val chanAB = new Channel("chanAB", Sort.Integer)
  val chanBA = new Channel("chanBA", Sort.Integer)

  /**
   * Process 1
   */

  val procA = Prog(
    c := 0,
    c --> chanAB,
    While (true) (
      c <-- chanBA,
      Assert(c >= 0),
      (c + 1) --> chanAB
    )
  )

  /**
   * Process 2
   */

  val procB = Prog(
    While (true) (
      c <-- chanAB,
      (c + 1) --> chanBA
    )
  )

  val network = Network(List(procA, procB))

}

object TestProg2 {

  import KPN._
  import IExpression._

  val c = Sort.Integer newConstant "c"
  val chanAB = new Channel("chanAB", Sort.Integer)
  val chanBA = new Channel("chanBA", Sort.Integer)

  /**
   * Process 1
   */

  val procA = Prog(
    c := 0,
    c --> chanAB,
    c <-- chanBA,
    (c + 1) --> chanAB
  )

  /**
   * Process 2
   */

  val procB = Prog(
    While (true) (
      c <-- chanAB,
      Assert(c >= 0),
      (c + 1) --> chanBA
    )
  )

  val network = Network(List(procA, procB))

}

object TestProg2Unsafe {

  import KPN._
  import IExpression._

  val c = Sort.Integer newConstant "c"
  val chanAB = new Channel("chanAB", Sort.Integer)
  val chanBA = new Channel("chanBA", Sort.Integer)

  /**
   * Process 1
   */

  val procA = Prog(
    c := 0,
    c --> chanAB,
    c <-- chanBA,
    (c - 10) --> chanAB
  )

  /**
   * Process 2
   */

  val procB = Prog(
    While (true) (
      c <-- chanAB,
      Assert(c >= 0),
      (c + 1) --> chanBA
    )
  )

  val network = Network(List(procA, procB))

}


object TestProg3 {

  import KPN._
  import IExpression._

  val c = Sort.Integer newConstant "c"
  val d = Sort.Integer newConstant "d"
  val b = Sort.Integer newConstant "b"
  val chanAB = new Channel("chanAB", Sort.Integer)
  val chanAC = new Channel("chanAC", Sort.Integer)
  val chanBC = new Channel("chanBC", Sort.Integer)
  val ackBA  = new Channel("ackBA", Sort.Bool)
  val ackCA  = new Channel("ackCA", Sort.Bool)

  /**
   * Process A
   */

  val procA = Prog(
    c := 0,
    c --> chanAB,
    c --> chanAC,
    While (true) (
      b <-- ackBA,
      b <-- ackCA,
      c := c + 1,
      c --> chanAB,
      c --> chanAC
    )
  )

  /**
   * Process B
   */

  val procB = Prog(
    While (true) (
      c <-- chanAB,
      c --> chanBC,
      b := ADT.BoolADT.True,
      b --> ackBA
    )
  )

  /**
   * Process C
   */

  val procC = Prog(
    While (true) (
      c <-- chanAC,
      d <-- chanBC,
      Assert(c === d),
      b := ADT.BoolADT.True,
      b --> ackCA
    )
  )

  val network = Network(List(procA, procB, procC))

  import Scheduler.{SendEvent, RecvEvent, ErrorEvent}

  val schedule : Scheduler.Schedule =
    Scheduler.Schedule(0, Vector((0,SendEvent(chanAB),1),
                                 (1,RecvEvent(chanAB),2),
                                 (2,SendEvent(chanAC),3),
                                 (3,RecvEvent(chanAC),4),
                                 (4,SendEvent(chanBC),5),
                                 (5,RecvEvent(chanBC),6),
                                 (6,ErrorEvent,-1),
                                 (6,SendEvent(ackBA),7),
                                 (7,RecvEvent(ackBA),8),
                                 (8,SendEvent(ackCA),9),
                                 (9,RecvEvent(ackCA),10),
                                 (10,SendEvent(chanAB),11),
                                 (11,RecvEvent(chanAB),12),
                                 (12,SendEvent(chanAC),13),
                                 (13,RecvEvent(chanAC),14),
                                 (14,SendEvent(chanBC),15),
                                 (15,RecvEvent(chanBC),16),
                                 (16,ErrorEvent,-1),
                                 (16,SendEvent(ackBA),17),
                                 (17,RecvEvent(ackBA),8)))

}


object TestProg3Unsafe {

  import KPN._
  import IExpression._

  val c = Sort.Integer newConstant "c"
  val d = Sort.Integer newConstant "d"
  val b = Sort.Integer newConstant "b"
  val chanAB = new Channel("chanAB", Sort.Integer)
  val chanAC = new Channel("chanAC", Sort.Integer)
  val chanBC = new Channel("chanBC", Sort.Integer)
  val ackBA  = new Channel("ackBA", Sort.Bool)
  val ackCA  = new Channel("ackCA", Sort.Bool)

  /**
   * Process A
   */

  val procA = Prog(
    c := 0,
    c --> chanAB,
    c --> chanAC,
    While (true) (
      b <-- ackBA,
      b <-- ackCA,
      c := c + 1,
      c --> chanAB,
      c --> chanAC
    )
  )

  /**
   * Process B
   */

  val procB = Prog(
    While (true) (
      c <-- chanAB,
      (c + 1) --> chanBC,
      b := ADT.BoolADT.True,
      b --> ackBA
    )
  )

  /**
   * Process C
   */

  val procC = Prog(
    While (true) (
      c <-- chanAC,
      d <-- chanBC,
      Assert(c === d),
      b := ADT.BoolADT.True,
      b --> ackCA
    )
  )

  val network = Network(List(procA, procB, procC))

}

object TestInputNetwork {

  import KPN._
  import IExpression._

  val c1 = new Channel("c1", Sort.Integer)
  val c2 = new Channel("c2", Sort.Integer)

  val network = Network(List(
    KPNNodes.InputImpl(c1),
    KPNNodes.AbsImpl(c1, c2),
    KPNNodes.AssertImpl(c2, _ >= 0)
  ))

  val schedule : Scheduler.Schedule =
    Scheduler.Schedule(0, List((0, Scheduler.SendEvent(c1), 1),
                             (1, Scheduler.RecvEvent(c1), 2),
                             (2, Scheduler.SendEvent(c2), 3),
                             (3, Scheduler.RecvEvent(c2), 4),
                             (3, Scheduler.RecvEvent(c2), 0),
                             (4, Scheduler.ErrorEvent, 4)))

  SolveUtil.solve("InputVerify", network, schedule = Some(schedule))
}

object TestProgSum {

  import KPN._
  import IExpression._

  val c = Sort.Integer newConstant "c"
  val d = Sort.Integer newConstant "d"
  val in1 = new Channel("in1", Sort.Integer)
  val in2 = new Channel("in2", Sort.Integer)
  val out = new Channel("out", Sort.Integer)

  /**
   * Sum process
   */

  val procSum =
    KPNNodes.AddImpl(in1, in2, out)

  /**
   * Incrementing process, using process Sum to increment the
   * input from out by 1.
   */

  val procInc = Prog(
    0 --> in1,
    1 --> in2,
    While (true) (
      c <-- out,
      Assert(c >= 0),
      c --> in1,
      1 --> in2
    )
  )

  val network = Network(List(procSum, procInc))

  val SumSummary : Encoder.Summary =
    KPNNodes.AddContract(in1, in2, out)

  val IncSummary : Encoder.Summary =
    (hist, eventHist, event, api) => {
      import api._

      ite(eventHist.isEmpty,

          event.isSend(in1) & event.valueSent(in1) >= 0,

          (eventHist.last.isSend(in1) & event.isSend(in2) &
             event.valueSent(in2) === 1) |
          (eventHist.last.isSend(in2) & event.isRecv(out)) |
          (eventHist.last.isRecv(out) & hist(out).last < 0 &
             event.isError) |
          (eventHist.last.isRecv(out) & event.isSend(in1) &
             event.valueSent(in1) >= 0))
    }

  val summaries : Map[Int, Encoder.Summary] =
    Map(0 -> SumSummary, 1 -> IncSummary)

  val schedule : Scheduler.Schedule =
    Scheduler.Schedule(0, List((0, Scheduler.SendEvent(in1), 1),
                               (1, Scheduler.RecvEvent(in1), 2),
                               (2, Scheduler.SendEvent(in2), 3),
                               (3, Scheduler.RecvEvent(in2), 4),
                               (4, Scheduler.SendEvent(out), 5),
                               (5, Scheduler.RecvEvent(out), 0),
                               (0, Scheduler.ErrorEvent, 0)))

}

object TestProgFib {

  import KPN._
  import IExpression._

  val ak = new Channel("ak", Sort.Integer)
  val bk = new Channel("bk", Sort.Integer)
  val ck = new Channel("ck", Sort.Integer)
  val dk = new Channel("dk", Sort.Integer)
  val ek = new Channel("ek", Sort.Integer)
  val fk = new Channel("fk", Sort.Integer)

  def network(n : Int) =
    Network(List(KPNNodes.DelayImpl (0)(ek, fk),
                 KPNNodes.AddImpl   (ck, fk, ak),
                 KPNNodes.DelayImpl (1)(ak, bk),
                 KPNNodes.SplitImpl (bk, ck, dk, ek),
                 KPNNodes.AssertImpl(dk, _ >= n)))

  val summaries : Map[Int, Encoder.Summary] =
    Map(0 -> KPNNodes.DelayContract(0, ek, fk),
        1 -> KPNNodes.AddContract(ck, fk, ak),
        2 -> KPNNodes.DelayContract(1, ak, bk),
        3 -> KPNNodes.SplitContract(bk, ck, dk, ek))

  val schedule : Scheduler.Schedule =
    Scheduler.Schedule(0, List((0, Scheduler.SendEvent(bk), 1),
                               (1, Scheduler.RecvEvent(bk), 2),
                               (2, Scheduler.SendEvent(ck), 3),
                               (3, Scheduler.RecvEvent(ck), 4),
                               (4, Scheduler.SendEvent(dk), 5),
                               (5, Scheduler.RecvEvent(dk), 6),
                               (6, Scheduler.ErrorEvent, 6),
                               (6, Scheduler.SendEvent(fk), 7),
                               (7, Scheduler.RecvEvent(fk), 8),
                               (8, Scheduler.SendEvent(ek), 9),
                               (9, Scheduler.RecvEvent(ek), 10),
                               (10, Scheduler.SendEvent(ak), 11),
                               (11, Scheduler.RecvEvent(ak), 0)))

}

object TestSimpleNested {

  import KPN._
  import IExpression._

  val ak = new Channel("ak", Sort.Integer)
  val bk = new Channel("bk", Sort.Integer)
  val ck = new Channel("ck", Sort.Integer)

  def network(bound : Int) =
    Net(KPNNodes.FiniteSeqImpl(-5)(ak),
        Net(KPNNodes.AbsImpl(ak, bk),
            KPNNodes.AbsImpl(bk, ck)),
        KPNNodes.AssertImpl(ck, _ >= bound))

  import Scheduler.{Schedule, SendEvent, RecvEvent, ErrorEvent}

  val schedules =
    Map(KPN.NodeLocator.top -> Schedule(0, List(
      (0, SendEvent(ak), 1),
      (1, RecvEvent(ak), 2),
      (2, SendEvent(ck), 3),
      (3, RecvEvent(ck), 2),
      (2, ErrorEvent, -1)
    )),
    KPN.NodeLocator.top.down(1) -> Schedule(0, List(
      (0, RecvEvent(ak), 1),
      (1, SendEvent(bk), 2),
      (2, RecvEvent(bk), 3),
      (3, SendEvent(ck), 0)
    )))

}