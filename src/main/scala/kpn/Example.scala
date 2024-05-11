

package kpn

import ap.parser._
import ap.theories.ADT

object ExampleProg1 {

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

object ExampleProg2 {

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

object ExampleProg2Unsafe {

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


object ExampleProg3 {

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

}


object ExampleProg3Unsafe {

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

object InputVerify extends App {

  import KPN._
  import IExpression._

  val c1 = new Channel("c1", Sort.Integer)
  val c2 = new Channel("c2", Sort.Integer)

  val network = Network(List(
    KPNNodes.InputImpl(c1),
    KPNNodes.AbsImpl(c1, c2),
    KPNNodes.AssertImpl(c2, _ >= 0)
  ))

  val schedule : Encoder.Schedule =
    Encoder.Schedule(0, List((0, Encoder.SendEvent(c1), 1),
                             (1, Encoder.RecvEvent(c1), 2),
                             (2, Encoder.SendEvent(c2), 3),
                             (3, Encoder.RecvEvent(c2), 4),
                             (3, Encoder.RecvEvent(c2), 0),
                             (4, Encoder.ErrorEvent, 4)))

  SolveUtil.solve("InputVerify", network, schedule = Some(schedule))
}

object AddIncVerify extends App {

  SolveUtil.solve("IncAdd, verifying summaries",
                  ExampleProgSum.network,
                  ExampleProgSum.summaries)

}

object AddIncVerifySched extends App {

  SolveUtil.solve("IncAdd, verifying summaries, assuming system schedule",
                  ExampleProgSum.network,
                  ExampleProgSum.summaries,
                  Some(ExampleProgSum.schedule))

}

object AddIncInfer extends App {

  SolveUtil.solve("IncAdd, inferring summaries",
                  ExampleProgSum.network)

}

object AddIncInferSched extends App {

  SolveUtil.solve("IncAdd, inferring summaries, assuming system schedule",
                  ExampleProgSum.network,
                  schedule = Some(ExampleProgSum.schedule),
                  printSol = true)

}

object ExampleProgSum {

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

  val schedule : Encoder.Schedule =
    Encoder.Schedule(0, List((0, Encoder.SendEvent(in1), 1),
                             (1, Encoder.RecvEvent(in1), 2),
                             (2, Encoder.SendEvent(in2), 3),
                             (3, Encoder.RecvEvent(in2), 4),
                             (4, Encoder.SendEvent(out), 5),
                             (5, Encoder.RecvEvent(out), 0),
                             (0, Encoder.ErrorEvent, 0)))

}


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
                  schedule = Some(ExampleProgFib.schedule),
                  printSol = true)

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

  val schedule : Encoder.Schedule =
    Encoder.Schedule(0, List((0, Encoder.SendEvent(bk), 1),
                             (1, Encoder.RecvEvent(bk), 2),
                             (2, Encoder.SendEvent(ck), 3),
                             (3, Encoder.RecvEvent(ck), 4),
                             (4, Encoder.SendEvent(dk), 5),
                             (5, Encoder.RecvEvent(dk), 6),
                             (6, Encoder.ErrorEvent, 6),
                             (6, Encoder.SendEvent(fk), 7),
                             (7, Encoder.RecvEvent(fk), 8),
                             (8, Encoder.SendEvent(ek), 9),
                             (9, Encoder.RecvEvent(ek), 10),
                             (10, Encoder.SendEvent(ak), 11),
                             (11, Encoder.RecvEvent(ak), 0)))

}
