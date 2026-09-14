import LaurentZeroEstimate
import LaurentMinor

/-! Construct a nonzero interpolation minor from the proved zero estimate. -/

namespace LeanA113258.LaurentCore

open scoped BigOperators
open Polynomial Matrix

/-- The interpolation rank criterion is unchanged when powers of the additive
coordinate are replaced by any independent family of bounded-degree polynomials. -/
theorem exists_nonzero_polynomial_interpolation_minor {R Γ κ ι : Type*}
    [Field R] [Fintype Γ] [DecidableEq Γ] [Fintype κ]
    [Fintype ι] [DecidableEq ι]
    {L d : ℕ} (w : ι → R[X]) (hw : LinearIndependent R w)
    (hwdeg : ∀ i, (w i).natDegree ≤ d) (x y : Γ → R)
    (x₁ y₁ : Fin L → R) (x₂ y₂ : κ → R) (e : Fin L → κ → Γ)
    (hx : ∀ i t, x (e i t) = x₁ i + x₂ t)
    (hy : ∀ i t, y (e i t) = y₁ i * y₂ t)
    (hy₁ : Function.Injective y₁) (hx₂ : Function.Injective x₂)
    (hy₂ : ∀ t, y₂ t ≠ 0) (hcard : d * L < Fintype.card κ) :
    ∃ f : (ι × Fin L) → Γ, Function.Injective f ∧
      (Matrix.of fun i j : ι × Fin L =>
        (w i.1).eval (x (f j)) * y (f j) ^ i.2.val).det ≠ 0 := by
  classical
  let A : Matrix (ι × Fin L) Γ R := Matrix.of fun i j => (w i.1).eval (x j) * y j ^ i.2.val
  apply exists_nonzero_minor_of_row_test A
  intro u hu
  let p : Fin L → R[X] := fun j => ∑ k : ι, u (k, j) • w k
  have hdeg (j : Fin L) : (p j).natDegree ≤ d := by
    apply natDegree_sum_le_of_forall_le
    intro k _
    exact (natDegree_smul_le _ _).trans (hwdeg k)
  have hpval (j : Fin L) (v : R) : (p j).eval v = ∑ k : ι, u (k, j) * (w k).eval v := by
    simp only [p, eval_finsetSum, smul_eq_C_mul, eval_mul, eval_C]
  have hpzero : ∀ j, p j = 0 :=
    additive_multiplicative_zero_estimate p hdeg x₁ y₁ x₂ y₂ hy₁ hx₂ hy₂ hcard (by
      intro i t
      have hh := hu (e i t)
      simp only [A, Matrix.of_apply, hx, hy, Fintype.sum_prod_type] at hh
      simp only [hpval, Finset.sum_mul]
      rw [Finset.sum_comm]
      simpa only [mul_assoc] using hh)
  funext i
  exact Fintype.linearIndependent_iff.mp hw (fun k => u (k, i.2)) (hpzero i.2) i.1

theorem exists_nonzero_monomial_interpolation_minor {R Γ κ : Type*}
    [Field R] [Fintype Γ] [DecidableEq Γ] [Fintype κ]
    {K L : ℕ} (x y : Γ → R)
    (x₁ y₁ : Fin L → R) (x₂ y₂ : κ → R) (e : Fin L → κ → Γ)
    (hx : ∀ i t, x (e i t) = x₁ i + x₂ t)
    (hy : ∀ i t, y (e i t) = y₁ i * y₂ t)
    (hy₁ : Function.Injective y₁) (hx₂ : Function.Injective x₂)
    (hy₂ : ∀ t, y₂ t ≠ 0) (hcard : (K - 1) * L < Fintype.card κ) :
    ∃ f : (Fin K × Fin L) → Γ, Function.Injective f ∧
      (Matrix.of fun i j : Fin K × Fin L =>
        x (f j) ^ i.1.val * y (f j) ^ i.2.val).det ≠ 0 := by
  classical
  let A : Matrix (Fin K × Fin L) Γ R := Matrix.of fun i j => x j ^ i.1.val * y j ^ i.2.val
  apply exists_nonzero_minor_of_row_test A
  intro u hu
  let p : Fin L → R[X] := fun j => ∑ k : Fin K, monomial k.val (u (k, j))
  have hdeg (j : Fin L) : (p j).natDegree ≤ K - 1 := by
    apply natDegree_sum_le_of_forall_le
    intro k _
    exact (natDegree_monomial_le (m := k.val) (u (k, j))).trans (by omega)
  have hpval (j : Fin L) (v : R) : (p j).eval v = ∑ k : Fin K, u (k, j) * v ^ k.val := by
    simp only [p, eval_finsetSum, eval_monomial]
  have hpzero : ∀ j, p j = 0 :=
    additive_multiplicative_zero_estimate p hdeg x₁ y₁ x₂ y₂ hy₁ hx₂ hy₂ hcard (by
      intro i t
      have hh := hu (e i t)
      simp only [A, Matrix.of_apply, hx, hy, Fintype.sum_prod_type] at hh
      simp only [hpval, Finset.sum_mul]
      rw [Finset.sum_comm]
      simpa only [mul_assoc] using hh)
  funext i
  have hcoeff := congrArg (fun q : R[X] => q.coeff i.1.val) (hpzero i.2)
  have hpcoeff : (p i.2).coeff i.1.val = u i := by
    simp only [p, finsetSum_coeff, coeff_monomial]
    rw [Finset.sum_eq_single i.1]
    · simp
    · intro j _ hji
      rw [if_neg (fun he => hji (Fin.ext he))]
    · simp
  simpa only [hpcoeff, coeff_zero, Pi.zero_apply] using hcoeff

end LeanA113258.LaurentCore
