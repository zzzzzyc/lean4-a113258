/-
Copyright 2026 The Formal Conjectures Authors.
Copyright 2026 zzzzzyc / zhang yichuan
SPDX-License-Identifier: Apache-2.0

Licensed under the Apache License, Version 2.0 (the "License");
you may not use this file except in compliance with the License.
You may obtain a copy of the License at

    https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software
distributed under the License is distributed on an "AS IS" BASIS,
WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
See the License for the specific language governing permissions and
limitations under the License.

Adapted from FormalConjectures/OEIS/113258.lean. See NOTICE for attribution.
Modified: use recursive factorial and finite sums, and add IsPerfectPower.
-/

/-
  OEIS A113258, matching google-deepmind/formal-conjectures
  FormalConjectures/OEIS/113258.lean

  a(n) = ∑_{i = 1}^n (i!) ^ {(n-i+1)!}
       = ∑_{i = 0}^{n-1} (i+1)! ^ (n-i)!
-/

namespace LeanA113258

def fact : Nat → Nat
  | 0 => 1
  | n + 1 => fact n * (n + 1)

def sumRange (n : Nat) (f : Nat → Nat) : Nat :=
  match n with
  | 0 => 0
  | n + 1 => sumRange n f + f n

/-- Same formula as `FormalConjectures.OeisA113258.a`. -/
def a (n : Nat) : Nat :=
  sumRange n fun i => fact (i + 1) ^ fact (n - i)

def IsPerfectPower (n : Nat) : Prop :=
  ∃ b e : Nat, 1 < b ∧ 1 < e ∧ n = b ^ e

@[simp] theorem fact_zero : fact 0 = 1 := rfl
@[simp] theorem fact_succ (n : Nat) : fact (n + 1) = fact n * (n + 1) := rfl
@[simp] theorem a_zero : a 0 = 0 := rfl

theorem sumRange_zero (f : Nat → Nat) : sumRange 0 f = 0 := rfl

theorem sumRange_succ (n : Nat) (f : Nat → Nat) :
    sumRange (n + 1) f = sumRange n f + f n := rfl

end LeanA113258
