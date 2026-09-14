import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Data.Nat.Choose.Cast
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Tactic.NormNum

/-!
Laurent (2008), Lemma 3, proved by completing squares instead of minimizing
on a simplex. This is a component of the interpolation-determinant argument,
not a proof of the two-logarithm lower bound.
-/

namespace LeanA113258.LaurentCore

open scoped BigOperators

/-- The homogeneous quadratic estimate for a sequence with at least two entries.
The upper restriction `μ ≤ 1` in Laurent's statement is not needed here. -/
theorem quadratic_estimate {m : ℕ} (x : Fin (m + 2) → ℝ) {μ N : ℝ}
    (hμ : (1 / 3 : ℝ) ≤ μ) (hN : 0 ≤ N)
    (hx : ∀ i, 0 ≤ x i) (hsum : ∑ i, x i = N) :
    (1 + 2 * μ - μ ^ 2) / 2 * N ^ 2 ≤
      (∑ i, (x i) ^ 2) + 2 * μ * N * ∑ i, (i.val : ℝ) * x i := by
  have htail :
      (1 + μ) * N * (∑ i : Fin m, x i.succ.succ) ≤
        (∑ i : Fin m, (x i.succ.succ) ^ 2) +
          2 * μ * N * ∑ i : Fin m, ((i.val : ℝ) + 2) * x i.succ.succ := by
    simp only [Finset.mul_sum, ← Finset.sum_add_distrib]
    apply Finset.sum_le_sum
    intro i _
    have hi : 0 ≤ (i.val : ℝ) := Nat.cast_nonneg _
    have hw : 0 ≤ 2 * μ * ((i.val : ℝ) + 2) - (1 + μ) := by
      nlinarith [mul_nonneg (show 0 ≤ μ by linarith) hi]
    have hp := mul_nonneg (mul_nonneg hN hw) (hx i.succ.succ)
    nlinarith [sq_nonneg (x i.succ.succ)]
  simp only [Fin.sum_univ_succ, Fin.val_zero, Fin.val_succ, Nat.cast_add,
    Nat.cast_one, Nat.cast_zero, zero_mul, one_mul, zero_add] at hsum ⊢
  have h0 := sq_nonneg (2 * x 0 - (1 + μ) * N)
  have h1 := sq_nonneg (2 * x (Fin.succ 0) - (1 - μ) * N)
  have htail' :
      (∑ i : Fin m, ((i.val : ℝ) + 1 + 1) * x i.succ.succ) =
        ∑ i : Fin m, ((i.val : ℝ) + 2) * x i.succ.succ := by
    apply Finset.sum_congr rfl
    intro i _
    ring
  rw [htail']
  have hmass := congrArg (fun t : ℝ => (1 + μ) * N * t) hsum
  nlinarith [hmass]

#print axioms quadratic_estimate

/-- Include the empty and one-entry sequences. -/
theorem quadratic_estimate_all {ℓ : ℕ} (x : Fin ℓ → ℝ) {μ N : ℝ}
    (hμ : (1 / 3 : ℝ) ≤ μ) (hN : 0 ≤ N)
    (hx : ∀ i, 0 ≤ x i) (hsum : ∑ i, x i = N) :
    (1 + 2 * μ - μ ^ 2) / 2 * N ^ 2 ≤
      (∑ i, (x i) ^ 2) + 2 * μ * N * ∑ i, (i.val : ℝ) * x i := by
  rcases ℓ with _ | ℓ
  · have hzero : N = 0 := by simpa using hsum.symm
    simp [hzero]
  rcases ℓ with _ | ℓ
  · change (1 + 2 * μ - μ ^ 2) / 2 * N ^ 2 ≤
      (∑ i : Fin 1, (x i) ^ 2) + 2 * μ * N * ∑ i : Fin 1, (i.val : ℝ) * x i
    change (∑ i : Fin 1, x i) = N at hsum
    simp only [Fin.sum_univ_one, Fin.val_zero, Nat.cast_zero, zero_mul,
      mul_zero, add_zero] at hsum ⊢
    rw [hsum]
    nlinarith [sq_nonneg ((1 - μ) * N)]
  · exact quadratic_estimate x hμ hN hx hsum

/-- Laurent (2008), Lemma 3, with zero multiplicities allowed.
The original positive-multiplicity case follows immediately. -/
theorem laurent_lemma_three {ℓ N : ℕ} (ν : Fin ℓ → ℕ)
    (hsum : ∑ i, ν i = N) {μ : ℝ} (hμ : (1 / 3 : ℝ) ≤ μ) :
    (((1 + 2 * μ - μ ^ 2) / 2) * (N : ℝ) ^ 2 - (N : ℝ)) / 2 ≤
      (∑ i, ((ν i).choose 2 : ℝ)) +
        μ * (N : ℝ) * ∑ i, (i.val : ℝ) * (ν i : ℝ) := by
  have hsumR : ∑ i, (ν i : ℝ) = (N : ℝ) := by exact_mod_cast hsum
  have hq := quadratic_estimate_all (fun i => (ν i : ℝ)) hμ
    (Nat.cast_nonneg N) (fun i => Nat.cast_nonneg (ν i)) hsumR
  have hc : (∑ i, ((ν i).choose 2 : ℝ)) =
      ((∑ i, (ν i : ℝ) ^ 2) - (N : ℝ)) / 2 := by
    calc
      (∑ i, ((ν i).choose 2 : ℝ)) =
          ∑ i, (((ν i : ℝ) ^ 2 - (ν i : ℝ)) / 2) := by
        apply Finset.sum_congr rfl
        intro i _
        rw [Nat.cast_choose_two]
        ring
      _ = ((∑ i, (ν i : ℝ) ^ 2) - (N : ℝ)) / 2 := by
        simp only [div_eq_mul_inv, ← Finset.sum_mul, Finset.sum_sub_distrib, hsumR]
  rw [hc]
  linarith

#print axioms laurent_lemma_three

end LeanA113258.LaurentCore
