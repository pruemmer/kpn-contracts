

package kpn

import ap.parser._
import IExpression.{ConstantTerm, Sort}
import ap.theories.ADT

object Encoder {

  abstract class QueueEncoder {
    def apply(s : Sort) : QueueEncoderInstance
  }

  abstract class QueueEncoderInstance {
    val sort : Sort
  }

  object ListQueueEncoder {
    def apply(s : Sort) = new QueueEncoderInstance {
      val (sort, nil, cons, head, tail, _) =
        ADT.createListType(s.name + "_list", s)
    }
  }

  abstract class HistoryEncoder {
    def apply(s : Sort) : HistoryEncoderInstance
  }

  abstract class HistoryEncoderInstance {
    val sort : Sort
  }

  object ListHistoryEncoder {
    def apply(s : Sort) = new HistoryEncoderInstance {
      val (sort, nil, cons, head, tail, _) =
        ADT.createListType(s.name + "_list", s)
    }
  }
}


class Encoder(network             : KPN.Network,
              queueEncoders       : Map[KPN.Channel, Encoder.QueueEncoder],
              chanHistoryEncoders : Map[KPN.Channel, Encoder.HistoryEncoder],
              eventEncoders       : Map[Int, Encoder.HistoryEncoder]) {

  import KPN._
  import Encoder._

  import network.{processes, processConsts, processInChans, processOutChans,
                  allChans}

  val channelQueues =
    for (chan <- allChans)
    yield queueEncoders.getOrElse(chan, ListQueueEncoder(chan.sort))
  val channelHistories =
    for (chan <- allChans)
    yield chanHistoryEncoders.getOrElse(chan, ListHistoryEncoder(chan.sort))

}
