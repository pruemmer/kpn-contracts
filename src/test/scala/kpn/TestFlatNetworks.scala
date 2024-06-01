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
import ap.theories.ADT

import org.scalacheck.{Arbitrary, Gen, Properties}
import org.scalacheck.Prop._

object TestFlatNetworks extends Properties("TestFlatNetworks") {

  ap.util.Debug.enableAllAssertions(true)

  property("TestProg1") = {
    SolveUtil.solve("TestProg1",
                    TestProg1.network,
                    enableAssert = true,
                    quiet = true) == SolveUtil.Safe
  }

  property("TestProg2Safe") = {
    SolveUtil.solve("TestProg2Safe",
                    TestProg2.network,
                    enableAssert = true,
                    quiet = true) == SolveUtil.Safe
  }

  property("TestProg2Unsafe") = {
    SolveUtil.solve("TestProg2Unsafe",
                    TestProg2Unsafe.network,
                    enableAssert = true,
                    quiet = true) == SolveUtil.Unsafe
  }


  property("TestProg3Safe") = {
    SolveUtil.solve("TestProg3Safe",
                    TestProg3.network,
                    schedule = Some(TestProg3.schedule),
                    enableAssert = true,
                    quiet = true) == SolveUtil.Safe
  }


  property("TestProg3Unsafe") = {
    SolveUtil.solve("TestProg3Unsafe",
                    TestProg3Unsafe.network,
                    enableAssert = true,
                    quiet = true) == SolveUtil.Unsafe
  }

  property("InputNetworkSafe") = {
    SolveUtil.solve("InputNetworkSafe",
                    TestInputNetwork.network,
                    schedule = Some(TestInputNetwork.schedule),
                    enableAssert = true,
                    quiet = true) == SolveUtil.Safe
  }

  property("AddIncVerify") = {
    SolveUtil.solve("IncAdd, verifying summaries",
                    TestProgSum.network,
                    TestProgSum.summaries,
                    enableAssert = true,
                    quiet = true) == SolveUtil.Safe
  }

  property("AddIncVerifySched") = {
    SolveUtil.solve("IncAdd, verifying summaries, assuming system schedule",
                    TestProgSum.network,
                    TestProgSum.summaries,
                    schedule = Some(TestProgSum.schedule),
                    enableAssert = true,
                    quiet = true) == SolveUtil.Safe
  }

  property("AddIncInfer") = {
    SolveUtil.solve("IncAdd, inferring summaries",
                    TestProgSum.network,
                    enableAssert = true,
                    quiet = true) == SolveUtil.Safe
  }

  property("AddIncInferSched") = {
    SolveUtil.solve("IncAdd, inferring summaries, assuming system schedule",
                    TestProgSum.network,
                    schedule = Some(TestProgSum.schedule),
                    enableAssert = true,
                    quiet = true) == SolveUtil.Safe
  }

  property("FibonacciInferSafe") = {
    SolveUtil.solve("Fibonacci, inferring contracts, assuming system schedule",
                    TestProgFib.network(0),
                    schedule = Some(TestProgFib.schedule),
                    enableAssert = true,
                    quiet = true) == SolveUtil.Safe
  }

  property("FibonacciVerifySafe") = {
    SolveUtil.solve("Fibonacci, verifying contracts, assuming system schedule",
                    TestProgFib.network(0),
                    TestProgFib.summaries,
                    schedule = Some(TestProgFib.schedule),
                    enableAssert = true,
                    quiet = true) == SolveUtil.Safe
  }

  property("FibonacciInferUnsafe") = {
    SolveUtil.solve("Fibonacci unsafe, inferring contracts, assuming system schedule",
                    TestProgFib.network(2),
                    schedule = Some(TestProgFib.schedule),
                    enableAssert = true,
                    quiet = true) == SolveUtil.Unsafe
  }

  property("FibonacciVerifyUnsafe") = {
    SolveUtil.solve("Fibonacci unsafe, verifying contracts, assuming system schedule",
                    TestProgFib.network(2),
                    TestProgFib.summaries,
                    schedule = Some(TestProgFib.schedule),
                    enableAssert = true,
                    quiet = true) == SolveUtil.Unsafe
  }

}
