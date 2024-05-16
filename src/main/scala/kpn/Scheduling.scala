

package kpn

import ap.util.Seqs

import scala.collection.mutable.{LinkedHashSet, ArrayBuffer, HashSet => MHashSet}

object Scheduler {

  import KPN._
  import Encoder.{Event, ErrorEvent, RecvEvent, SendEvent, Schedule}

  /**
   * Finite-state automata representing communication behaviours.
   */
  case class EpsSchedule(initial : Int,
                         transitions : Seq[(Int, Option[Event], Int)],
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
      val newTransitions   = new ArrayBuffer[(Int, Event, Int)]
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

}
