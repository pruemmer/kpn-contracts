package kpn

import ap.parser._
import kpn.Encoder.Capacity2HistoryEncoder

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

  println(Scheduler.progEpsSchedule(network.processes(0)).toSchedule)
  new Scheduler.GuardAnalysis(Scheduler.progEpsSchedule(network.processes(0)).toSchedule)
  println(Scheduler.progEpsSchedule(network.processes(2)))
  new Scheduler.GuardAnalysis(Scheduler.progEpsSchedule(network.processes(2)).toSchedule)

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
    yield Scheduler.progEpsSchedule(p).toSchedule

  val scheduler = new Scheduler.NetworkScheduler(schedules)

  SolveUtil.solve("Fibonacci, inferring contracts, assuming system schedule",
                  network,
                  historyEncoder = Capacity2HistoryEncoder,
                  schedule = Some(scheduler.result))

}