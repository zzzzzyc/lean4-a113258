import LaurentInterpolationRank
import Mathlib.Algebra.Polynomial.Sequence

namespace LeanA113258.LaurentCore

open scoped BigOperators
open Polynomial Matrix

noncomputable def binomialSequence (R : Type*) [Field R] [CharZero R] : Polynomial.Sequence R where
  elems' k := ((k.factorial : R)⁻¹) • descPochhammer R k
  degree_eq' k := by
    rw [smul_eq_C_mul, degree_C_mul (inv_ne_zero (Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero k))),
      degree_eq_natDegree (monic_descPochhammer R k).ne_zero, descPochhammer_natDegree]

theorem binomialSequence_eval_nat (R : Type*) [Field R] [CharZero R] (k n : ℕ) :
    (binomialSequence R k).eval (n : R) = (n.choose k : R) := by
  change (((k.factorial : R)⁻¹) • descPochhammer R k).eval (n : R) = _
  rw [smul_eq_C_mul, eval_mul, eval_C, Nat.cast_choose_eq_descPochhammer_div]
  ring

/-- A nonzero minor of the binomial interpolation matrix used in Laurent's
arithmetic argument. Its additive coordinates are natural numbers. -/
theorem exists_nonzero_binomial_interpolation_minor {R Γ κ : Type*}
    [Field R] [CharZero R] [Fintype Γ] [DecidableEq Γ] [Fintype κ]
    {K L : ℕ} (x : Γ → ℕ) (y : Γ → R)
    (x₁ y₁ : Fin L → R) (x₂ y₂ : κ → R) (e : Fin L → κ → Γ)
    (hx : ∀ i t, (x (e i t) : R) = x₁ i + x₂ t)
    (hy : ∀ i t, y (e i t) = y₁ i * y₂ t)
    (hy₁ : Function.Injective y₁) (hx₂ : Function.Injective x₂)
    (hy₂ : ∀ t, y₂ t ≠ 0) (hcard : (K - 1) * L < Fintype.card κ) :
    ∃ f : (Fin K × Fin L) → Γ, Function.Injective f ∧
      (Matrix.of fun i j : Fin K × Fin L =>
        ((x (f j)).choose i.1.val : R) * y (f j) ^ i.2.val).det ≠ 0 := by
  have hw : LinearIndependent R (fun i : Fin K => binomialSequence R i.val) :=
    (binomialSequence R).linearIndependent.comp Fin.val Fin.val_injective
  have hdeg (i : Fin K) : (binomialSequence R i.val).natDegree ≤ K - 1 := by
    rw [(binomialSequence R).natDegree_eq]
    omega
  simpa only [binomialSequence_eval_nat] using
    exists_nonzero_polynomial_interpolation_minor (fun i : Fin K => binomialSequence R i.val)
      hw hdeg (fun t => (x t : R)) y x₁ y₁ x₂ y₂ e hx hy hy₁ hx₂ hy₂ hcard

end LeanA113258.LaurentCore
