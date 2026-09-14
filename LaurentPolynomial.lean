import LaurentMultiplicity
import Mathlib.Algebra.Polynomial.Div

/-!
A finite polynomial version of the interpolation-determinant vanishing bound.
This proves genuine divisibility, not an assumed analytic order statement.
The analytic passage to exponential series remains separate.
-/

namespace LeanA113258.LaurentCore

open scoped BigOperators
open Polynomial

theorem determinant_sum_rows {ι κ R : Type*} [Fintype ι] [DecidableEq ι]
    [Fintype κ] [CommRing R] (A : ι → κ → ι → R) :
    (Matrix.of fun i j => ∑ k, A i k j).det =
      ∑ f : ι → κ, (Matrix.of fun i j => A i (f i) j).det := by
  classical
  have hrows : (Matrix.of fun i j => ∑ k, A i k j) = (fun i => ∑ k, A i k) := by
    ext i j
    simp only [Matrix.of_apply, Finset.sum_apply]
  rw [hrows]
  exact (Matrix.detRowAlternating : (ι → R) [⋀^ι]→ₗ[R] R).toMultilinearMap.map_sum A

theorem determinant_X_rows {ι R : Type*} [Fintype ι] [DecidableEq ι]
    [CommRing R] (d : ι → ℕ) (A : Matrix ι ι R) :
    (Matrix.of fun i j => (X : R[X]) ^ d i * C (A i j)).det =
      X ^ (∑ i, d i) * C A.det := by
  have h := Matrix.det_mul_column (fun i => (X : R[X]) ^ d i)
    (A.map (C : R →+* R[X]))
  have hmap : (A.map (C : R →+* R[X])).det = C A.det :=
    (RingHom.map_det C A).symm
  rw [Finset.prod_pow_eq_pow_sum, hmap] at h
  exact h

/-- Finite bivariate interpolation, restricted to the weighted curve `(X, X^w)`.
The row coefficients and column evaluation points are arbitrary. -/
noncomputable def interpolationPolynomial {ι R : Type*} [Fintype ι] [DecidableEq ι]
    [CommRing R] (H L w : ℕ) (a : ι → (Fin H × Fin L) → R) (z s : ι → R) : R[X] :=
  (Matrix.of fun i j => ∑ u : Fin H × Fin L,
    (X : R[X]) ^ (u.1.val + w * u.2.val) *
      C (a i u * (z j ^ u.1.val * s j ^ u.2.val))).det

/-- Every term of degree below `d` vanishes in the interpolation determinant.
This is the finite algebraic part of the analytic multiplicity argument. -/
theorem X_pow_dvd_interpolationPolynomial {ι R : Type*}
    [Fintype ι] [DecidableEq ι] [CommRing R]
    (H L w d : ℕ) (a : ι → (Fin H × Fin L) → R) (z s : ι → R)
    {μ : ℝ} (hμ : (1 / 3 : ℝ) ≤ μ)
    (hw : μ * (Fintype.card ι : ℝ) ≤ (w : ℝ))
    (hd : (d : ℝ) ≤
      (((1 + 2 * μ - μ ^ 2) / 2) * (Fintype.card ι : ℝ) ^ 2 -
        (Fintype.card ι : ℝ)) / 2) :
    (X : R[X]) ^ d ∣ interpolationPolynomial H L w a z s := by
  classical
  unfold interpolationPolynomial
  rw [determinant_sum_rows]
  apply Finset.dvd_sum
  intro f _
  let D : ℕ := ∑ i, ((f i).1.val + w * (f i).2.val)
  let A : Matrix ι ι R := Matrix.of fun i j =>
    a i (f i) * (z j ^ (f i).1.val * s j ^ (f i).2.val)
  change (X : R[X]) ^ d ∣
    (Matrix.of fun i j => X ^ ((f i).1.val + w * (f i).2.val) * C (A i j)).det
  rw [determinant_X_rows]
  by_cases hA : A.det = 0
  · simp [hA]
  have hinjNat := scaled_monomial_det_labels_injective
    (fun i => (f i).2.val) (fun i => (f i).1.val) z s (fun i => a i (f i)) hA
  have hinj : Function.Injective (fun i => ((f i).2, (f i).1.val)) := by
    intro i j hij
    apply hinjNat
    have hc : (f i).2 = (f j).2 := congrArg (fun t : Fin L × ℕ => t.1) hij
    have hh : (f i).1.val = (f j).1.val := congrArg (fun t : Fin L × ℕ => t.2) hij
    exact Prod.ext (congrArg Fin.val hc) hh
  have hbound := weighted_degree_of_injective_pairs
    (fun i => (f i).2) (fun i => (f i).1.val) hinj hμ
  have hcpos : (0 : ℝ) ≤ ∑ i, ((f i).2.val : ℝ) :=
    Finset.sum_nonneg fun _ _ => Nat.cast_nonneg _
  have hcast : (D : ℝ) = (∑ i, ((f i).1.val : ℝ)) +
      (w : ℝ) * ∑ i, ((f i).2.val : ℝ) := by
    simp only [D, Nat.cast_sum, Nat.cast_add, Nat.cast_mul,
      Finset.sum_add_distrib, Finset.mul_sum]
  have hdegree : d ≤ D := by
    have hw' := mul_le_mul_of_nonneg_right hw hcpos
    have hreal : (d : ℝ) ≤ (D : ℝ) := by linarith
    exact_mod_cast hreal
  exact dvd_mul_of_dvd_left (pow_dvd_pow X hdegree) _

/-- The divisibility statement expressed as exact zero coefficients. -/
theorem interpolationPolynomial_coeff_eq_zero {ι R : Type*}
    [Fintype ι] [DecidableEq ι] [CommRing R]
    (H L w d : ℕ) (a : ι → (Fin H × Fin L) → R) (z s : ι → R)
    {μ : ℝ} (hμ : (1 / 3 : ℝ) ≤ μ)
    (hw : μ * (Fintype.card ι : ℝ) ≤ (w : ℝ))
    (hd : (d : ℝ) ≤
      (((1 + 2 * μ - μ ^ 2) / 2) * (Fintype.card ι : ℝ) ^ 2 -
        (Fintype.card ι : ℝ)) / 2) {k : ℕ} (hk : k < d) :
    (interpolationPolynomial H L w a z s).coeff k = 0 :=
  (Polynomial.X_pow_dvd_iff.mp
    (X_pow_dvd_interpolationPolynomial H L w d a z s hμ hw hd)) k hk

#print axioms determinant_sum_rows
#print axioms X_pow_dvd_interpolationPolynomial
#print axioms interpolationPolynomial_coeff_eq_zero

end LeanA113258.LaurentCore
