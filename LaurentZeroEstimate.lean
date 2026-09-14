import LaurentPolynomialDeterminant
import Mathlib.LinearAlgebra.Vandermonde
import Mathlib.Algebra.Polynomial.Roots

/-! The zero estimate for translations in the additive times multiplicative
group, proved with a polynomial determinant and a Vandermonde determinant. -/

namespace LeanA113258.LaurentCore

open scoped BigOperators
open Polynomial Matrix

theorem translated_polynomial_determinant {R : Type*} [CommRing R] [IsDomain R]
    {L : ℕ} (p : Fin L → R[X]) (x y : Fin L → R)
    (hp : ∀ j, p j ≠ 0) (hy : Function.Injective y) :
    let A : Matrix (Fin L) (Fin L) R[X] := Matrix.of fun i j =>
      (p j).comp (X + C (x i)) * C (y i ^ j.val)
    A.det ≠ 0 ∧ A.det.natDegree ≤ ∑ j, (p j).natDegree := by
  classical
  dsimp only
  let A : Matrix (Fin L) (Fin L) R[X] := Matrix.of fun i j =>
    (p j).comp (X + C (x i)) * C (y i ^ j.val)
  have hd (i j : Fin L) : (A i j).natDegree ≤ (p j).natDegree := by
    dsimp [A]
    apply (natDegree_mul_C_le ((p j).comp (X + C (x i))) (y i ^ j.val)).trans_eq
    calc
      _ = (p j).natDegree * (X + C (x i) : R[X]).natDegree := natDegree_comp
      _ = (p j).natDegree * 1 := congrArg (fun d => (p j).natDegree * d) (natDegree_X_add_C (x i))
      _ = _ := Nat.mul_one _
  have hc (i j : Fin L) : (A i j).coeff (p j).natDegree =
      (p j).leadingCoeff * y i ^ j.val := by
    dsimp [A]
    rw [coeff_mul_C]
    have hh := coeff_comp_degree_mul_degree (p := p j) (q := X + C (x i)) (by simp)
    simpa using congrArg (fun r : R => r * y i ^ j.val) hh
  have hcoeff : A.det.coeff (∑ j, (p j).natDegree) =
      (∏ j, (p j).leadingCoeff) * (Matrix.vandermonde y).det := by
    rw [coeff_det_sum_column_bounds A (fun j => (p j).natDegree) hd]
    simp_rw [hc]
    simpa only [Matrix.vandermonde_apply, mul_comm] using
      Matrix.det_mul_row (fun j => (p j).leadingCoeff) (Matrix.vandermonde y)
  refine ⟨?_, natDegree_det_le_sum_column_bounds A (fun j => (p j).natDegree) hd⟩
  intro hzero
  have hnz : (∏ j, (p j).leadingCoeff) * (Matrix.vandermonde y).det ≠ 0 :=
    mul_ne_zero (Finset.prod_ne_zero_iff.mpr fun j _ => leadingCoeff_ne_zero.mpr (hp j))
      (Matrix.det_vandermonde_ne_zero_iff.mpr hy)
  apply hnz
  rw [← hcoeff, hzero, coeff_zero]

/-- A polynomial of bidegrees at most `(d, L-1)` cannot vanish on all sums
of these two sets in `G_a × G_m`, unless all its coefficients vanish. -/
theorem additive_multiplicative_zero_estimate {R κ : Type*}
    [CommRing R] [IsDomain R] [Fintype κ]
    {L d : ℕ} (p : Fin L → R[X])
    (hpdeg : ∀ j, (p j).natDegree ≤ d)
    (x₁ y₁ : Fin L → R) (x₂ y₂ : κ → R)
    (hy₁ : Function.Injective y₁) (hx₂ : Function.Injective x₂)
    (hy₂ : ∀ t, y₂ t ≠ 0) (hcard : d * L < Fintype.card κ)
    (hvanish : ∀ i t, ∑ j : Fin L,
      (p j).eval (x₁ i + x₂ t) * (y₁ i * y₂ t) ^ j.val = 0) :
    ∀ j, p j = 0 := by
  classical
  by_contra hnot
  push Not at hnot
  obtain ⟨j₀, hj₀⟩ := hnot
  let q : Fin L → R[X] := fun j => if p j = 0 then 1 else p j
  have hq (j : Fin L) : q j ≠ 0 := by
    dsimp [q]
    split_ifs with h <;> simp_all
  have hqdeg (j : Fin L) : (q j).natDegree ≤ d := by
    dsimp [q]
    split_ifs with h
    · simp
    · exact hpdeg j
  let A : Matrix (Fin L) (Fin L) R[X] := Matrix.of fun i j =>
    (q j).comp (X + C (x₁ i)) * C (y₁ i ^ j.val)
  let D : R[X] := A.det
  obtain ⟨hD, hDdeg⟩ := translated_polynomial_determinant q x₁ y₁ hq hy₁
  change D ≠ 0 at hD
  change D.natDegree ≤ ∑ j, (q j).natDegree at hDdeg
  have hdeg : D.natDegree ≤ d * L := by
    apply hDdeg.trans
    calc
      (∑ j, (q j).natDegree) ≤ ∑ _ : Fin L, d := Finset.sum_le_sum (fun j _ => hqdeg j)
      _ = _ := by simp [Nat.mul_comm]
  have heval (t : κ) : D.eval (x₂ t) = 0 := by
    let M : Matrix (Fin L) (Fin L) R := Matrix.of fun i j => (A i j).eval (x₂ t)
    let v : Fin L → R := fun j => if p j = 0 then 0 else y₂ t ^ j.val
    have hv : v ≠ 0 := by
      intro hzero
      have hh := congrFun hzero j₀
      have hpow : y₂ t ^ j₀.val ≠ 0 := pow_ne_zero _ (hy₂ t)
      apply hpow
      simpa only [v, hj₀, if_false, Pi.zero_apply] using hh
    have hMv : M *ᵥ v = 0 := by
      funext i
      change (∑ j, M i j * v j) = 0
      rw [← hvanish i t]
      apply Finset.sum_congr rfl
      intro j _
      dsimp [M, A, v, q]
      by_cases hpj : p j = 0
      · simp [hpj]
      · simp only [hpj, if_false, eval_mul, eval_comp, eval_add, eval_X, eval_C, mul_pow]
        rw [add_comm (x₂ t) (x₁ i)]
        ring
    have hmap : D.eval (x₂ t) = M.det := by
      exact RingHom.map_det (Polynomial.evalRingHom (x₂ t)) A
    rw [hmap]
    by_contra hM
    exact hv (Matrix.eq_zero_of_mulVec_eq_zero hM hMv)
  exact hD (Polynomial.eq_zero_of_natDegree_lt_card_of_eval_eq_zero D hx₂ heval (hdeg.trans_lt hcard))

end LeanA113258.LaurentCore
