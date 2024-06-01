/**
 * This file is part of the KPN encoder.
 * Copyright (c) 2021-2024 Philipp Ruemmer. All rights reserved.
 * 
 * Redistribution and use in source and binary forms, with or without
 * modification, are permitted provided that the following conditions are met:
 * 
 * * Redistributions of source code must retain the above copyright notice, this
 *   list of conditions and the following disclaimer.
 * 
 * * Redistributions in binary form must reproduce the above copyright notice,
 *   this list of conditions and the following disclaimer in the documentation
 *   and/or other materials provided with the distribution.
 * 
 * * Neither the name of the authors nor the names of their
 *   contributors may be used to endorse or promote products derived from
 *   this software without specific prior written permission.
 * 
 * THIS SOFTWARE IS PROVIDED BY THE COPYRIGHT HOLDERS AND CONTRIBUTORS
 * "AS IS" AND ANY EXPRESS OR IMPLIED WARRANTIES, INCLUDING, BUT NOT
 * LIMITED TO, THE IMPLIED WARRANTIES OF MERCHANTABILITY AND FITNESS
 * FOR A PARTICULAR PURPOSE ARE DISCLAIMED. IN NO EVENT SHALL THE
 * COPYRIGHT HOLDER OR CONTRIBUTORS BE LIABLE FOR ANY DIRECT,
 * INDIRECT, INCIDENTAL, SPECIAL, EXEMPLARY, OR CONSEQUENTIAL DAMAGES
 * (INCLUDING, BUT NOT LIMITED TO, PROCUREMENT OF SUBSTITUTE GOODS OR
 * SERVICES; LOSS OF USE, DATA, OR PROFITS; OR BUSINESS INTERRUPTION)
 * HOWEVER CAUSED AND ON ANY THEORY OF LIABILITY, WHETHER IN CONTRACT,
 * STRICT LIABILITY, OR TORT (INCLUDING NEGLIGENCE OR OTHERWISE)
 * ARISING IN ANY WAY OUT OF THE USE OF THIS SOFTWARE, EVEN IF ADVISED
 * OF THE POSSIBILITY OF SUCH DAMAGE.
 */

package kpn

import ap.parser._
import IExpression.{ConstantTerm, Sort}
import ap.types.MonoSortedPredicate
import ap.theories.ADT

import lazabs.horn.bottomup.HornClauses

object QueueEncoders {
  import IExpression._
  import HornClauses._

  abstract class QueueEncoder {
    def apply(s : Sort) : QueueEncoderInstance
  }

  abstract class QueueEncoderInstance {
    val sort : Sort
    def isEmpty(t : ITerm) : IFormula
    def enqueue(pre : ITerm, el : ITerm, post : ITerm) : IFormula
    def dequeue(pre : ITerm, el : ITerm, post : ITerm) : IFormula
    val axioms : Seq[Clause]
  }

  object ListQueueEncoder extends QueueEncoder {
    def apply(elementSort : Sort) = new QueueEncoderInstance {
      val (sort, nil, cons, head, tail, _) =
        ADT.createListType(elementSort.name + "_list", elementSort)
      val enqueuePred =
        MonoSortedPredicate(elementSort.name + "_enqueue",
                            List(sort, elementSort, sort))

      def isEmpty(t : ITerm) : IFormula = t === nil()

      def enqueue(pre : ITerm, el : ITerm, post : ITerm) : IFormula =
        enqueuePred(pre, el, post)

      def dequeue(pre : ITerm, el : ITerm, post : ITerm) : IFormula =
        pre === cons(el, post)

      val axioms = {
        val pre    = sort newConstant "pre"
        val post   = sort newConstant "post"
        val value1 = elementSort newConstant "value1"
        val value2 = elementSort newConstant "value2"
        List(
          enqueuePred(nil(), value1, cons(value1, nil())) :-
            true,
          enqueuePred(cons(value2, pre), value1, cons(value2, post)) :-
            enqueuePred(pre, value1, post)
        )
      }
    }
  }

  object Capacity1QueueEncoder extends QueueEncoder {
    def apply(elementSort : Sort) = new QueueEncoderInstance {
      val name = elementSort.name + "_queue1"
      val (sort, record, Seq(queue_size, queue_value)) =
        ADT.createRecordType(name,
                             List((name + "_size", Sort.Integer),
                                  (name + "_value", elementSort)))

      def isEmpty(t : ITerm) : IFormula = queue_size(t) === 0

      def enqueue(pre : ITerm, el : ITerm, post : ITerm) : IFormula =
        (queue_size(post) === queue_size(pre) + 1) &
        ite(queue_size(pre) === 0,
            queue_value(post) === el,
            queue_value(post) === queue_value(pre))

      def dequeue(pre : ITerm, el : ITerm, post : ITerm) : IFormula =
        (queue_size(pre) > 0) &
        (queue_size(post) === queue_size(pre) - 1) &
        (el === queue_value(pre))

      val axioms = List()
    }
  }

  object Capacity2QueueEncoder extends QueueEncoder {
    def apply(elementSort : Sort) = new QueueEncoderInstance {
      val name = elementSort.name + "_queue2"
      val (sort, record, Seq(queue_size, queue_value1, queue_value2)) =
        ADT.createRecordType(name,
                             List((name + "_size", Sort.Integer),
                                  (name + "_value1", elementSort),
                                  (name + "_value2", elementSort)))

      def isEmpty(t : ITerm) : IFormula = queue_size(t) === 0

      def enqueue(pre : ITerm, el : ITerm, post : ITerm) : IFormula =
        (queue_size(post) === queue_size(pre) + 1) &
        ((queue_size(pre) === 0 & queue_value1(post) === el) |
           (queue_size(pre) === 1 &
              queue_value1(post) === queue_value1(pre) &
              queue_value2(post) === el) |
           (queue_size(pre) >= 2 &
              queue_value1(post) === queue_value1(pre) &
              queue_value2(post) === queue_value2(pre)))

      def dequeue(pre : ITerm, el : ITerm, post : ITerm) : IFormula =
        (queue_size(pre) > 0) &
        (queue_size(post) === queue_size(pre) - 1) &
        (el === queue_value1(pre)) &
        (queue_value1(post) === queue_value2(pre))

      val axioms = List()
    }
  }

}
