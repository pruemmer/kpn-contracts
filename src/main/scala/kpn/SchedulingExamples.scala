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
import kpn.HistoryEncoders.Capacity2HistoryEncoder

object InputScheduling extends App {

  import KPN._
  import IExpression._

  val c1 = new Channel("c1", Sort.Integer)
  val c2 = new Channel("c2", Sort.Integer)

  val network = Network(List(
    KPNNodes.InputImpl(c1),
    KPNNodes.AbsImpl(c1, c2),
    KPNNodes.AssertImpl(c2, _ >= 0)
  ))

  /*
  println(Scheduler.progEpsSchedule(network.processes(0)).toSchedule)
  new Scheduler.GuardAnalysis(Scheduler.progEpsSchedule(network.processes(0)).toSchedule)
  println(Scheduler.progEpsSchedule(network.processes(2)))
  new Scheduler.GuardAnalysis(Scheduler.progEpsSchedule(network.processes(2)).toSchedule)
*/
}

object NetworkScheduling extends App {

  import KPN._
  import IExpression._

  val ak = new Channel("ak", Sort.Integer)
  val bk = new Channel("bk", Sort.Integer)
  val ck = new Channel("ck", Sort.Integer)
  val dk = new Channel("dk", Sort.Integer)
  val ek = new Channel("ek", Sort.Integer)
  val fk = new Channel("fk", Sort.Integer)
  val out = new Channel("out", Sort.Integer)

  val network =
    Network(List(KPNNodes.DelayImpl (0, ek, fk),
                 KPNNodes.AddImpl   (ck, fk, ak),
                 KPNNodes.DelayImpl (1, ak, bk),
                 KPNNodes.SplitImpl (bk, ck, dk, ek, out),
                 KPNNodes.AssertWin2Impl(dk, (x0, x1) => x0 <= x1)
                 //KPNNodes.AssertImpl(dk, _ >= 0)
                 ))

  val schedules =
    for (p <- network.processes)
    yield Scheduler.nodeEpsSchedule(p).toSchedule

  val scheduler = new Scheduler.NetworkScheduler(schedules)

  SolveUtil.solve("Fibonacci, inferring contracts, assuming system schedule",
                  network,
                  historyEncoder = Capacity2HistoryEncoder,
                  schedule = Some(scheduler.result))

}
