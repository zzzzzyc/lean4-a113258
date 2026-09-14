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
Modified: restate the question using IsPerfectPower and add reduction lemmas.
-/

import LeanA113258.Defs
import LeanA113258.Compute
import LeanA113258.Squares

namespace LeanA113258

/--
  Official open question, unchanged
  (`FormalConjectures/OEIS/113258.lean`):

  `∃ n > 4, ∃ b > 1, ∃ e > 1, a n = b ^ e`

  Equivalent target: `∀ n, 4 < n → ¬ IsPerfectPower (a n)`.
-/
def officialConjecture : Prop :=
  ∃ n, 4 < n ∧ IsPerfectPower (a n)

theorem a5_closes_one_case : ¬ IsPerfectPower (a 5) :=
  a_5_not_perfect_power

theorem a6_closes_one_case : ¬ IsPerfectPower (a 6) :=
  a_6_not_perfect_power

/-- `n ≥ 7`: any perfect-power witness must use an odd exponent
    coprime to `(n-1)!` (hence `e ≥ n`). That Diophantine case is open
    without Mathlib / Baker-type bounds; `officialConjecture_false`
    is therefore not declared. -/
theorem perfect_power_remaining_case {n : Nat} (hn : 7 ≤ n)
    (h : IsPerfectPower (a n)) :
    ∃ b e, 1 < b ∧ 1 < e ∧ a n = b ^ e ∧
      Nat.gcd e (fact (n - 1)) = 1 ∧ n ≤ e ∧ ¬ 2 ∣ e := by
  obtain ⟨b, e, hb, he, hab, hcop⟩ := perfect_power_imp_coprime hn h
  refine ⟨b, e, hb, he, hab, hcop,
    coprime_exp_ge (by omega) he hcop, ?_⟩
  intro h2
  exact not_even_exp hn he h2 ⟨b, hb, hab⟩

end LeanA113258
