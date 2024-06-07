/**
 * This file is part of the KPN encoder.
 * Copyright (c) 2024 Philipp Ruemmer. All rights reserved.
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
import ap.types.Sort

import scala.collection.mutable.{ArrayBuffer, LinkedHashSet,
                                 HashMap => MHashMap}

object KPNode {

}

abstract class KPNode {
  protected class C(val sort : Sort) {
    override def toString() : String = "Connector[" + sort + "]"
  }

  private class Subnode(val name      : String,
                        val outputs   : Seq[C],
                        inputFuns     : Seq[() => C],
                        toNetworkNode : (Seq[KPN.Channel]) => KPN.NetworkNode) {
    lazy val inputs : Seq[C] = for (inp <- inputFuns) yield inp()

    def toNetworkNode(outputChannels : Map[C, KPN.Channel],
                      inputChannels : Map[C, Iterator[KPN.Channel]]) : KPN.NetworkNode = {
      val inputChans =
        for (c <- inputs) yield inputChannels(c).next
      toNetworkNode(outputs.map(outputChannels) ++ inputChans)
    }

    override def toString() : String = name
  }

  private val subnodes = new ArrayBuffer[Subnode]

  protected def const(value : ITerm) : C = {
    val out = new C(Sort sortOf value)
    subnodes +=
      new Subnode("const[" + value + "]",
                  List(out), List(),
                  chans => KPNNodes.ConstImpl(value)(chans(0)))
    out
  }

  protected def delay(init : ITerm)(op : => C) : C = {
    val out = new C(Sort sortOf init)
    subnodes +=
      new Subnode("delay[" + init + "]",
                  List(out), List(() => op),
                  chans => KPNNodes.DelayImpl(init)(chans(1), chans(0)))
    out
  }

  protected def add(op1 : => C, op2 : => C) : C = {
    val out = new C(Sort.Integer)
    subnodes +=
      new Subnode("add",
                  List(out), List(() => op1, () => op2),
                  chans => KPNNodes.AddImpl(chans(1), chans(2), chans(0)))
    out
  }

  protected def ensure(f : ITerm => IFormula)(op : => C) : Unit = {
    subnodes +=
      new Subnode("ensure",
                  List(), List(() => op),
                  chans => KPNNodes.AssertImpl(chans(0), f))
  }

  lazy val network : KPN.Network = {
    val connectors = new LinkedHashSet[C]
    val readers    = new MHashMap[C, List[Subnode]]

    var i = 0
    while (i < subnodes.size) {
      val node = subnodes(i)
      connectors ++= node.outputs
      connectors ++= node.inputs
      for (c <- node.inputs)
        readers.put(c, node :: readers.getOrElse(c, List()))
      i = i + 1
    }

    val outputChannels =
      (for ((c, n) <- connectors.iterator.zipWithIndex)
       yield (c -> new KPN.Channel("out" + n, c.sort))).toMap

    val networkNodes = new ArrayBuffer[KPN.NetworkNode]

    val inputChannels =
      (for ((c, n) <- connectors.iterator.zipWithIndex;
            outChan = outputChannels(c))
       yield c -> (readers(c) match {
                     case List(_) =>
                       Iterator(outChan)
                     case rdrs => {
                       val inChans =
                         for (i <- 0 until rdrs.size)
                         yield new KPN.Channel("in" + n + "-" + i, c.sort)
                       networkNodes += KPNNodes.SplitImpl(outChan, inChans :_*)
                       inChans.iterator
                     }
                   })).toMap

    for (n <- subnodes)
      networkNodes += n.toNetworkNode(outputChannels, inputChannels)

    new KPN.Network(networkNodes.toIndexedSeq)
  }

}

