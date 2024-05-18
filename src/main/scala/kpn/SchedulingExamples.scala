package kpn

import ap.parser._

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