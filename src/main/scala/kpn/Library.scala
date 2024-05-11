package kpn

import ap.parser._
import ap.theories.ADT

object KPNNodes {

  import KPN._
  import IExpression._

  /**
    * Node representing inputs to the network of type <code>sort</code>.
    */
  def InputImpl(out : Channel) = {
    val c = out.sort newConstant "c"

    Prog(
        While (true) (
            Havoc(c),
            c --> out
        )
    )
  }

  def AbsImpl(in : Channel, out : Channel) = {
    require(in.sort == Sort.Integer && out.sort == Sort.Integer)
    val c = Sort.Integer newConstant "c"

    Prog(
        While (true) (
            c <-- in,
            ite(c >= 0, c, 0) --> out
        )
    )
  }

  def AddImpl(in1 : Channel, in2 : Channel, out : Channel) = {
    require(in1.sort == Sort.Integer &&
            in2.sort == Sort.Integer &&
            out.sort == Sort.Integer)
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
             event.valueSent(out) === hist(in1).last + hist(in2).last))
    }
  }

  def DelayImpl(init : ITerm, in : Channel, out : Channel) = {
    require(in.sort == out.sort)
    val c = in.sort newConstant "c"

    Prog(
      init --> out,
      While (true) (
        c <-- in,
        c --> out
      )
    )
  }

  def DelayContract(init : ITerm, in : Channel, out : Channel) : Encoder.Summary = {
    (hist, eventHist, event, api) => {
      import api._

      ite(eventHist.isEmpty,

          event.isSend(out) & (event.valueSent(out) === init),

          (eventHist.last.isSend(out) & event.isRecv(in)) |
          (eventHist.last.isRecv(in)  & event.isSend(out) &
             event.valueSent(out) >= hist(in).last))
    }
  }

  def SplitImpl(in : Channel, outs : Channel*) = {
    require(outs.map(_.sort).toSet subsetOf Set(in.sort))
    val c = in.sort newConstant "c"

    Prog(
      While (true) (
        (List(c <-- in) ++
           (for (out <- outs) yield (c --> out))) : _*
      )
    )
  }

  def SplitContract(in : Channel, outs : Channel*) : Encoder.Summary =
    (hist, eventHist, event, api) => {
      import api._

      ite(eventHist.isEmpty,
          event.isRecv(in),
          (eventHist.last.isRecv(in) & event.isSend(outs.head) &
             (event.valueSent(outs.head) === hist(in).last)) |
          (eventHist.last.isSend(outs.last) & event.isRecv(in)) |
            or(for (Seq(c, d) <- outs sliding 2)
               yield (eventHist.last.isSend(c) & event.isSend(d) &
                        (event.valueSent(d) === hist(in).last))))
    }

  def AssertImpl(in : Channel, prop : ITerm => IFormula) = {
    val c = in.sort newConstant "c"

    Prog(
      While (true) (
        c <-- in,
        Assert(prop(c))
      )
    )
  }

}