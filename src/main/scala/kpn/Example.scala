

package kpn

import ap.parser._
import ap.theories.ADT

object Nodes {

  import KPN._
  import IExpression._

  def AddImpl(in1 : Channel, in2 : Channel, out : Channel) = {
    val c = Sort.Integer newConstant "c"
    val d = Sort.Integer newConstant "d"

    Prog(
      While (true) (
        c <-- in1,
        d <-- in2,
        (c + d) --> out
      )
    )
  }

  def AddContract(in1 : Channel, in2 : Channel,
                  out : Channel) : Encoder.Summary = {
    (hist, eventHist, event, api) => {
      import api._

      ite(eventHist.isEmpty,

          event.isRecv(in1),

          (eventHist.last.isSend(out) & event.isRecv(in1)) |
          (eventHist.last.isRecv(in1) & event.isRecv(in2)) |
          (eventHist.last.isRecv(in2) & event.isSend(out) &
             event.sentValue(out) === hist(in1).last + hist(in2).last))
    }
  }

  def DelayImpl(init : ITerm, in : Channel, out : Channel,
                sort : Sort = Sort.Integer) = {
    val c = sort newConstant "c"

    Prog(
      init --> out,
      While (true) (
        c <-- in,
        c --> out
      )
    )
  }

  def DelayContract(init : ITerm, in : Channel, out : Channel,
                    sort : Sort = Sort.Integer) : Encoder.Summary = {
    (hist, eventHist, event, api) => {
      import api._

      ite(eventHist.isEmpty,

          event.isSend(out) & (event.sentValue(out) === init),

          (eventHist.last.isSend(out) & event.isRecv(in)) |
          (eventHist.last.isRecv(in)  & event.isSend(out) &
             event.sentValue(out) >= hist(in).last))
    }
  }

  def SplitImpl(sort : Sort, in : Channel, outs : Channel*) = {
    val c = sort newConstant "c"
    Prog(
      While (true) (
        (List(c <-- in) ++
           (for (out <- outs) yield (c --> out))) : _*
      )
    )
  }

  def AssertImpl(in : Channel, prop : ITerm => IFormula,
                 sort : Sort = Sort.Integer) = {
    val c = sort newConstant "c"

    Prog(
      While (true) (
        c <-- in,
        Assert(prop(c))
      )
    )
  }

}

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


object AddIncVerify extends App {

  SolveUtil.solve("IncAdd, verifying summaries",
                  ExampleProgSum.network,
                  ExampleProgSum.summaries)

}

object AddIncInfer extends App {

  SolveUtil.solve("IncAdd, inferring summaries",
                  ExampleProgSum.network)

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
    Nodes.AddImpl(in1, in2, out)

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
    Nodes.AddContract(in1, in2, out)

  val IncSummary : Encoder.Summary =
    (hist, eventHist, event, api) => {
      import api._

      ite(eventHist.isEmpty,

          event.isSend(in1) & event.sentValue(in1) >= 0,

          (eventHist.last.isSend(in1) & event.isSend(in2) &
             event.sentValue(in2) === 1) |
          (eventHist.last.isSend(in2) & event.isRecv(out)) |
          (eventHist.last.isRecv(out) & hist(out).last < 0 &
             event.isError) |
          (eventHist.last.isRecv(out) & event.isSend(in1) &
             event.sentValue(in1) >= 0))
    }

  val summaries : Map[Int, Encoder.Summary] =
    Map(0 -> SumSummary, 1 -> IncSummary)

}


object FibonacciInfer extends App {

  SolveUtil.solve("Fibonacci, inferring contracts",
                  ExampleProgFib.network)

}

object FibonacciVerify extends App {

  SolveUtil.solve("Fibonacci, verifying contracts",
                  ExampleProgFib.network,
                  ExampleProgFib.summaries,
                  debug = true,
                  queueEncoder = Encoder.Capacity2QueueEncoder)

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
    Network(List(Nodes.DelayImpl (0, ek, fk),
                 Nodes.AddImpl   (ck, fk, ak),
                 Nodes.DelayImpl (1, ak, bk),
                 Nodes.SplitImpl (Sort.Integer, bk, ck, dk, ek),
                 Nodes.AssertImpl(dk, x => x >= 0)))

  val summaries : Map[Int, Encoder.Summary] =
    Map(0 -> Nodes.DelayContract(0, ek, fk),
        1 -> Nodes.AddContract(ck, fk, ak),
        2 -> Nodes.DelayContract(1, ak, bk))

}
