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

import scala.collection.immutable.VectorBuilder

object HistoryEncoders {
  import IExpression._
  import HornClauses._

  abstract class HistoryEncoder {
    def apply(s : Sort) : HistoryEncoderInstance
  }

  abstract class HistoryEncoderInstance {
    val sort : Sort
    def isEmpty(t : ITerm) : IFormula
    def add(pre : ITerm, el : ITerm, post : ITerm) : IFormula
    def last(hist : ITerm) : ITerm
  }

  object ListHistoryEncoder extends HistoryEncoder {
    def apply(s : Sort) = new HistoryEncoderInstance {
      val (sort, nil, cons, head, tail, _) =
        ADT.createListType(s.name + "_list", s)
      def isEmpty(t : ITerm) : IFormula = t === nil()
      def add(pre : ITerm, el : ITerm, post : ITerm) : IFormula =
        post === cons(el, pre)
      def last(hist : ITerm) : ITerm =
        head(hist)
    }
  }

  object Capacity1HistoryEncoder extends HistoryEncoder {
    def apply(elementSort : Sort) = new HistoryEncoderInstance {
      val name = elementSort.name + "_hist1"
      val (sort, record, Seq(hist_empty, hist_value)) =
        ADT.createRecordType(name,
                             List((name + "_empty", Sort.Bool),
                                  (name + "_value", elementSort)))
      def isEmpty(t : ITerm) : IFormula =
        t === record(ADT.BoolADT.True, elementSort.witness.get)
      def add(pre : ITerm, el : ITerm, post : ITerm) : IFormula =
        post === record(ADT.BoolADT.False, el)
      def last(hist : ITerm) : ITerm =
        hist_value(hist)
    }
  }

  object Capacity2HistoryEncoder extends HistoryEncoder {
    def apply(elementSort : Sort) = new HistoryEncoderInstance {
      val name = elementSort.name + "_hist2"
      val (sort, record, Seq(hist_empty, hist_value1, hist_value2)) =
        ADT.createRecordType(name,
                             List((name + "_empty", Sort.Bool),
                                  (name + "_value1", elementSort),
                                  (name + "_value2", elementSort)))
      def isEmpty(t : ITerm) : IFormula =
        t === record(ADT.BoolADT.True, elementSort.witness.get, elementSort.witness.get)
      def add(pre : ITerm, el : ITerm, post : ITerm) : IFormula =
        post === record(ADT.BoolADT.False, el, hist_value1(pre))
      def last(hist : ITerm) : ITerm =
        hist_value1(hist)
    }
  }


  //////////////////////////////////////////////////////////////////////////////

  /**
   * Generic interface to buffer and event histories
   */
  trait History {
    val sort : Sort
    def isEmpty : IFormula
    def last : ITerm
  }

  class HistoryInstance(t : ITerm,
                        encoder : HistoryEncoderInstance) extends History {
    val sort : Sort = encoder.sort
    def isEmpty : IFormula = encoder.isEmpty(t)
    def last : ITerm = encoder.last(t)
  }
}
