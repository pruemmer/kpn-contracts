

package kpn

import ap.util.Seqs

import scala.collection.mutable.{LinkedHashSet, ArrayBuffer,
                                 HashSet => MHashSet, HashMap => MHashMap,
                                Stack}

object Scheduler {

  import KPN._

  sealed abstract class ScheduleEvent
  case object ErrorEvent extends ScheduleEvent

  abstract class ChannelEvent(c : KPN.Channel) extends ScheduleEvent
  case class     RecvEvent(_c : KPN.Channel) extends ChannelEvent(_c)
  case class     SendEvent(_c : KPN.Channel) extends ChannelEvent(_c)

  object Schedule {
    type Transition = (Int, ScheduleEvent, Int)
  }

  /**
   * Class to represent schedules of the overall system, represented
   * as an automaton over the events on the channels.
   */
  case class Schedule(initial : Int, transitions : Seq[Schedule.Transition]) {
    import Schedule._

    lazy val states : Set[Int] = {
      (Iterator(initial) ++
       (for ((s1, _, s2) <- transitions.iterator;
             s <- Iterator(s1, s2)) yield s)).toSet
    }

    def outgoingTransitions(state : Int) : Seq[Transition] =
      for (t@(`state`, _, _) <- transitions) yield t

    def hasErrorTransition(state : Int) =
      outgoingTransitions(state).exists {
        case (_, ErrorEvent, _) => true
        case _                  => false
      }

    lazy val recvChannels : Seq[Channel] =
      (for ((_, RecvEvent(ch), _) <- transitions) yield ch).distinct
    lazy val sendChannels : Seq[Channel] =
      (for ((_, SendEvent(ch), _) <- transitions) yield ch).distinct
  }

  /**
   * Finite-state automata representing communication behaviours.
   */
  case class EpsSchedule(initial : Int,
                         transitions : Seq[(Int, Option[ScheduleEvent], Int)],
                         accepting : Set[Int]) {
    lazy val states : Set[Int] = {
      (Iterator(initial) ++ accepting.iterator ++
       (for ((s1, _, s2) <- transitions.iterator;
             s <- Iterator(s1, s2)) yield s)).toSet
    }

    private def makeStatesDisjoint(that : EpsSchedule) : EpsSchedule =
      if (Seqs.disjoint(this.states, that.states)) {
        that
      } else {
        val thisMax = this.states.max
        val thatMin = that.states.min

        def mapState(s : Int) = thisMax - thatMin + s + 1

        EpsSchedule(mapState(that.initial),
                    for ((s1, e, s2) <- that.transitions)
                    yield (mapState(s1), e, mapState(s2)),
                    that.accepting map mapState)
      }

    def ++(that : EpsSchedule) : EpsSchedule = {
      val newThat = this.makeStatesDisjoint(that)
      EpsSchedule(this.initial,
                  this.transitions ++
                    (for (s <- this.accepting) yield (s, None, newThat.initial)) ++
                    newThat.transitions,
                  newThat.accepting)
    }

    def * : EpsSchedule =
      EpsSchedule(initial,
                  transitions ++
                    (for (s <- accepting) yield (s, None, initial)),
                  accepting)

    def union(that : EpsSchedule) : EpsSchedule = {
      val newThat = this.makeStatesDisjoint(that)
      val newInitial = (this.states.max max newThat.states.max) + 1
      EpsSchedule(newInitial,
                  List((newInitial, None, this.initial),
                       (newInitial, None, newThat.initial)) ++
                  this.transitions ++ that.transitions,
                  this.accepting ++ newThat.accepting)
    }

    private def epsClosure(s : Int) : Seq[Int] = {
      val res = new LinkedHashSet[Int]
      var todo : List[Int] = List(s)

      while (!todo.isEmpty) {
        val next = todo.head
        todo = todo.tail
        if (res add next)
          for ((`next`, None, t) <- transitions)
            todo = t :: todo
      }

      res.toSeq
    }

    def toSchedule : Schedule = {
      val newTransitions   = new ArrayBuffer[(Int, ScheduleEvent, Int)]
      var todo : List[Int] = List(initial)
      val statesDone       = new MHashSet[Int]

      while (!todo.isEmpty) {
        val next = todo.head
        todo = todo.tail

        if (statesDone add next) {
          for (s1 <- epsClosure(next);
               (`s1`, Some(ev), s2) <- transitions) {
            newTransitions += ((next, ev, s2))
            todo = s2 :: todo
          }
        }
      }

      Schedule(initial, newTransitions.toSeq)
    }
  }

  /**
   * Compute a finite-state abstraction of the possible communication
   * behaviour of a program.
   */
  def progEpsSchedule(p : Prog) : EpsSchedule = p match {
    case Skip | _ : Assign | _ : Havoc =>
      EpsSchedule(0, List(), Set(0))
    case Sequence(p1, p2) =>
      progEpsSchedule(p1) ++ progEpsSchedule(p2)
    case IfThenElse(_, b1, b2) =>
      progEpsSchedule(b1) union progEpsSchedule(b2)
    case While(_, body) =>
      progEpsSchedule(body).*
    case _ : Assert =>
      EpsSchedule(0, List((0, None, 1), (0, Some(ErrorEvent), 2)), Set(1))
    case Send(ch, _) =>
      EpsSchedule(0, List((0, Some(SendEvent(ch)), 1)), Set(1))
    case Receive(ch, _) =>
      EpsSchedule(0, List((0, Some(RecvEvent(ch)), 1)), Set(1))
  }

  def nodeEpsSchedule(n : NetworkNode) : EpsSchedule = n match {
    case ProgNode(prog) => progEpsSchedule(prog)
  }

  /**
   * Class to infer receive operations that have to be performed in individual
   * states of a schedule before any output or error can possibly occur.
   */
  class GuardAnalysis(schedule : Schedule) {
    import GuardAnalysis._
    import Schedule.Transition

    private val state2RecvSet = new MHashMap[Int, RecvSet]
    private val transition2RecvSet = new MHashMap[Schedule.Transition, RecvSet]

    for ((state, ErrorEvent | _ : SendEvent, _) <- schedule.transitions)
      state2RecvSet.put(state, EmptyRecvSet)

    private var cont = true
    while (cont) {
      cont = false

      for (t@(fromS, RecvEvent(ch), toS) <- schedule.transitions;
           toRS <- state2RecvSet get toS)
        transition2RecvSet.put(t, add(toRS, Map(ch -> 1)))

      for (state <- schedule.states) {
        val readSets =
          for (t <- schedule.outgoingTransitions(state);
               rs <- transition2RecvSet get t)
          yield rs
        if (!readSets.isEmpty) {
          val newRS = readSets.reduceLeft(min(_, _))
          val oldRS = state2RecvSet.getOrElse(state, newRS)
          val newRS2 = min(newRS, oldRS)
          (state2RecvSet get state) match {
            case Some(`newRS2`) =>
              // nothing
            case _ => {
              state2RecvSet.put(state, newRS2)
              cont = true
            }
          }
        }
      }
    }

    /**
     * Number of receives from channels that a schedule will
     * perform at least, from the given state, before an error or
     * any output can occur. Result None indicates
     * that no errors or outputs can be reached altogether.
     */
    def necessaryRecvsFromState(s : Int) : Option[RecvSet] =
      state2RecvSet.get(s)

    /**
     * Number of receives from channels that a schedule will
     * perform at least, when starting with the given transition,
     * before an error or any output can occur. Result None indicates
     * that no errors or outputs can be reached altogether.
     */
    def necessaryRecvsFromTransition(t : Transition) : Option[RecvSet] =
      transition2RecvSet.get(t)
  }
  
  object GuardAnalysis {
    type RecvSet = Map[Channel, Int]

    private val EmptyRecvSet : RecvSet = Map()

    private def add(a : RecvSet, b : RecvSet) : RecvSet =
      (for (ch <- (a.keySet ++ b.keySet).iterator)
       yield (ch -> (a.getOrElse(ch, 0) + b.getOrElse(ch, 0)))).toMap

    private def min(a : RecvSet, b : RecvSet) : RecvSet =
      (for (ch <- (a.keySet & b.keySet).iterator)
       yield (ch -> (a.getOrElse(ch, 0) min b.getOrElse(ch, 0)))).toMap
  }

  /**
   * Given execution schedules of the processes in a network, derive
   * a schedule for the network as a whole.
   */
  class NetworkScheduler(processSchedules : IndexedSeq[Schedule]) {

    val N = processSchedules.size

    private val recvChannels =
      (for (s <- processSchedules; ch <- s.recvChannels) yield ch).toSet
    private val sendChannels =
      (for (s <- processSchedules; ch <- s.sendChannels) yield ch).toSet

    val internalChannels = recvChannels & sendChannels
    val inChannels       = recvChannels -- internalChannels
    val outChannels      = sendChannels -- internalChannels

    val allChannels =
      (for (sched <- processSchedules;
            ch <- sched.recvChannels ++ sched.sendChannels)
       yield ch).distinct

    private object ScheduleState {
      sealed abstract class ProcRank(val r : Int, val factor : Int)
      case class RecvFeasible    (_factor : Int) extends ProcRank(0, _factor)
      case class SendRecvFeasible(_factor : Int) extends ProcRank(1, _factor)
      case class SendToEmpty     (_factor : Int) extends ProcRank(2, _factor)
      case class OtherRank       (_factor : Int) extends ProcRank(3, _factor)
/*
      implicit object ProcOrdering extends Ordering[ProcRank] {
        def compare(r1 : ProcRank, r2 : ProcRank) : Int =
          Seqs.lexCombineInts(r1.r compare r2.r, r1.factor compare r2.factor)
      }
*/
    }

    private case class ScheduleState(processStates : IndexedSeq[Int],
                                     channelSize   : Map[Channel, Int]) {
      import ScheduleState._

      def performTransition(n : Int, toState : Int,
                            ev : ScheduleEvent) : ScheduleState = {
        val newChannelSize =
          ev match {
            case RecvEvent(ch) if channelSize contains ch =>
              channelSize + (ch -> (channelSize(ch) - 1))
            case SendEvent(ch) if channelSize contains ch =>
              channelSize + (ch -> (channelSize(ch) + 1))
            case _ =>
              channelSize
          }
        ScheduleState(processStates.updated(n, toState), newChannelSize)
      }

      def posChannelSize(ch : Channel) =
        !internalChannels(ch) || channelSize(ch) > 0

      def emptyChannel(ch : Channel) =
        !internalChannels(ch) || channelSize(ch) == 0

      def outgoingTransitions(n : Int) =
        processSchedules(n).outgoingTransitions(processStates(n))

      lazy val hasErrorTransition =
        (0 until N).exists(n => outgoingTransitions(n).exists {
          case (_, ErrorEvent, _) => true
          case _                  => false
        })

      def procScore(n : Int) : ProcRank = {
        val outgoing = outgoingTransitions(n)
        val events   = outgoing.map(_._2)

        val sendChannels = (for (SendEvent(ch) <- events) yield ch).distinct
        val recvChannels = (for (RecvEvent(ch) <- events) yield ch).distinct

        val sendToEmpty  = sendChannels.forall(ch => emptyChannel(ch))
        val recvFeasible = recvChannels.forall(ch => posChannelSize(ch))

        (!sendChannels.isEmpty, sendToEmpty,
         !recvChannels.isEmpty, recvFeasible) match {
          case (false, _,    true,  true) => RecvFeasible(outgoing.size)
          case (true,  true, true,  true) => SendRecvFeasible(outgoing.size)
          case (true,  true, false, _)    => SendToEmpty(outgoing.size)
          case _                          => OtherRank(outgoing.size)
        }
      }

      def recommendedFiring : Set[Int] = {
        val ranks = (0 until N).map(procScore(_)).toVector
        ranks.indexWhere(_.isInstanceOf[RecvFeasible]) match {
          case -1 =>
          case n  => return Set(n)
        }
        ranks.indexWhere(_.isInstanceOf[SendToEmpty]) match {
          case -1 =>
          case n  => return Set(n)
        }
        (0 until N).toSet
      }

      def nextStates(firingSchedules : Set[Int])
                   : Seq[(ScheduleEvent, ScheduleState, Boolean)] = {
        for ((state, n) <- processStates.zipWithIndex;
             if firingSchedules contains n;
             (_, ev, toState) <- processSchedules(n).outgoingTransitions(state);
             if (ev match {
                   case RecvEvent(ch) => posChannelSize(ch)
                   case ErrorEvent    => false
                   case _             => true
                 }))
          yield (ev,
                 performTransition(n, toState, ev),
                 processSchedules(n).hasErrorTransition(toState))
        }
    }

    private val stateIndexes = new MHashMap[ScheduleState, Int]

    private val initialState =
      ScheduleState(processSchedules.map(_.initial),
                    internalChannels.map(_ -> 0).toMap)

    private val errorStateIdx = -1

    private def indexOf(s : ScheduleState) : Int =
      stateIndexes.getOrElseUpdate(s, stateIndexes.size)
    indexOf(initialState)

    private val networkTransitions = new ArrayBuffer[Schedule.Transition]

    private val statesTodo = new Stack[ScheduleState]
    statesTodo.push(initialState)

    if (initialState.hasErrorTransition)
      networkTransitions += ((indexOf(initialState), ErrorEvent, errorStateIdx))

    while (!statesTodo.isEmpty) {
      val state = statesTodo.pop

      for ((ev, newState, et) <- state.nextStates(state.recommendedFiring)) {
        if (!(stateIndexes contains newState))
          statesTodo.push(newState)
        networkTransitions += ((indexOf(state), ev, indexOf(newState)))
        if (et)
          networkTransitions += ((indexOf(newState), ErrorEvent, errorStateIdx))
      }
    }

    val result =
      Schedule(indexOf(initialState), networkTransitions.toVector)

  }

}
