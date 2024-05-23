

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

object ScheduleExample extends App {

  import Scheduler._

  println(progEpsSchedule(ExampleProg2Unsafe.procA).toSchedule)
  println(progEpsSchedule(ExampleProg2Unsafe.procB).toSchedule)
  println(progEpsSchedule(ExampleProgSum.procInc).toSchedule)

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
    Network(List(KPNNodes.DelayImpl (0, ek, fk),
                 KPNNodes.AddImpl   (ck, fk, ak),
                 KPNNodes.DelayImpl (1, ak, bk),
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
        Net(KPNNodes.DelayImpl(0, bk, ck),
            KPNNodes.AddImpl  (sum_in, ck, dk),
            KPNNodes.SplitImpl(dk, sum_out, bk)),
        KPNNodes.AssertImpl(sum_out, _ >= 0))

  println(network)

  SolveUtil.solve("nested network, verification",
                  network)

}
