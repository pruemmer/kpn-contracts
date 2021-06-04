

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
