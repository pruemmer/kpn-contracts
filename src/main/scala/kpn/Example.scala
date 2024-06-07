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

object FibonacciInfer extends App {

  SolveUtil.solve("Fibonacci, inferring contracts, assuming system schedule",
                  ExampleProgFib.network,
                  schedule = Some(ExampleProgFib.schedule),
                  printSol = true)

}

object FibonacciVerify extends App {

  SolveUtil.solve("Fibonacci, verifying contracts, assuming system schedule",
                  ExampleProgFib.network,
                  ExampleProgFib.summaries,
                  schedule = Some(ExampleProgFib.schedule))

}

object ExampleProgFib {

  import KPN._
  import IExpression._

  val ak = new Channel("ak", Sort.Integer)
  val bk = new Channel("bk", Sort.Integer)
  val ck = new Channel("ck", Sort.Integer)
  val dk = new Channel("dk", Sort.Integer)
  val ek = new Channel("ek", Sort.Integer)
  val fk = new Channel("fk", Sort.Integer)

  val network =
    Network(List(KPNNodes.DelayImpl (0)(ek, fk),
                 KPNNodes.AddImpl   (ck, fk, ak),
                 KPNNodes.DelayImpl (1)(ak, bk),
                 KPNNodes.SplitImpl (bk, ck, dk, ek),
                 KPNNodes.AssertImpl(dk, _ >= 0)))

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


object NestedNetworkVerify extends App {

  import KPN._
  import IExpression._

  val ak = new Channel("ak", Sort.Integer)
  val ek = new Channel("ek", Sort.Integer)

  val sum_in = new Channel("sum_in", Sort.Integer)
  val bk = new Channel("bk", Sort.Integer)
  val ck = new Channel("ck", Sort.Integer)
  val dk = new Channel("dk", Sort.Integer)
  val sum_out = new Channel("sum_out", Sort.Integer)

  val network =
    Net(KPNNodes.InputImpl(ak),
        KPNNodes.AbsImpl(ak, sum_in),
        Net(KPNNodes.DelayImpl(0)(bk, ck),
            KPNNodes.AddImpl  (sum_in, ck, dk),
            KPNNodes.SplitImpl(dk, sum_out, bk)),
        KPNNodes.AssertImpl(sum_out, _ >= 0))

  println(network)

  SolveUtil.solve("nested network, verification",
                  network)

}

object SimpleNestedNetworkVerify extends App {

  import KPN._
  import IExpression._

  val ak = new Channel("ak", Sort.Integer)
  val bk = new Channel("bk", Sort.Integer)
  val ck = new Channel("ck", Sort.Integer)

  val network =
    Net(KPNNodes.FiniteSeqImpl(-5)(ak),
        Net(KPNNodes.AbsImpl(ak, bk),
            KPNNodes.AbsImpl(bk, ck)),
        KPNNodes.AssertImpl(ck, _ >= 5))

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

  SolveUtil.solve("nested network, verification",
                  network, schedules = schedules, printSol = true)

}


object SimpleNestedNetworkVerify2 extends App {

  import KPN._
  import IExpression._

  val ak = new Channel("ak", Sort.Integer)
  val bk = new Channel("bk", Sort.Integer)
  val ck = new Channel("ck", Sort.Integer)
  val dk = new Channel("dk", Sort.Integer)

  val network =
    Net(KPNNodes.FiniteSeqImpl(-5)(ak),
        KPNNodes.AbsImpl(ak, bk),
        KPNNodes.AssertImpl(bk, _ >= 1))

  import Scheduler.{Schedule, SendEvent, RecvEvent, ErrorEvent}

  SolveUtil.solve("nested network, verification",
                  network)

}
