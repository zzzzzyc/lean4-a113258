import LaurentBinomialRank
import Mathlib.LinearAlgebra.Matrix.Kronecker

/-! The exact determinant change from binomial rows to centered power rows. -/

namespace LeanA113258.LaurentCore

open scoped BigOperators
open Polynomial Matrix Kronecker

theorem polynomial_interpolation_determinant {R : Type*} [CommRing R]
    {K L : ℕ} (p : Fin K → R[X]) (hp : ∀ k, (p k).natDegree ≤ k.val)
    (x y : (Fin K × Fin L) → R) :
    (Matrix.of fun i j : Fin K × Fin L => (p i.1).eval (x j) * y j ^ i.2.val).det =
      (∏ k : Fin K, (p k).coeff k.val) ^ L *
        (Matrix.of fun i j : Fin K × Fin L => x j ^ i.1.val * y j ^ i.2.val).det := by
  classical
  let C₀ : Matrix (Fin K) (Fin K) R := Matrix.of fun k h => (p k).coeff h.val
  let M : Matrix (Fin K × Fin L) (Fin K × Fin L) R := Matrix.of fun i j =>
    x j ^ i.1.val * y j ^ i.2.val
  have hcoeff : C₀.det = ∏ k : Fin K, (p k).coeff k.val := by
    rw [← Matrix.det_transpose]
    exact Matrix.det_of_isUpperTriangular (Matrix.matrixOfPolynomials_blockTriangular p hp)
  have heval (k : Fin K) (v : R) : (p k).eval v = ∑ h : Fin K, (p k).coeff h.val * v ^ h.val := by
    rw [eval_eq_sum_range' ((hp k).trans_lt k.isLt)]
    exact (Fin.sum_univ_eq_sum_range (fun h => (p k).coeff h * v ^ h) K).symm
  have hmat : (Matrix.of fun i j : Fin K × Fin L => (p i.1).eval (x j) * y j ^ i.2.val) =
      (C₀ ⊗ₖ (1 : Matrix (Fin L) (Fin L) R)) * M := by
    ext i j
    rcases i with ⟨ki, li⟩
    rw [Matrix.mul_apply]
    simp only [Fintype.sum_prod_type, Matrix.kronecker_apply, Matrix.one_apply,
      C₀, M, Matrix.of_apply, mul_ite, mul_one, mul_zero, ite_mul, zero_mul,
      Finset.sum_ite_eq, Finset.mem_univ, if_true]
    rw [heval, Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro h _
    ring
  rw [hmat, Matrix.det_mul, Matrix.det_kronecker, hcoeff, Matrix.det_one]
  simp only [Fintype.card_fin, one_pow, mul_one, M]

theorem equal_leading_coefficients_interpolation_det {R : Type*} [CommRing R]
    {K L : ℕ} (p q : Fin K → R[X])
    (hp : ∀ k, (p k).natDegree ≤ k.val) (hq : ∀ k, (q k).natDegree ≤ k.val)
    (hpq : ∀ k, (p k).coeff k.val = (q k).coeff k.val)
    (x y : (Fin K × Fin L) → R) :
    (Matrix.of fun i j : Fin K × Fin L => (p i.1).eval (x j) * y j ^ i.2.val).det =
      (Matrix.of fun i j : Fin K × Fin L => (q i.1).eval (x j) * y j ^ i.2.val).det := by
  rw [polynomial_interpolation_determinant p hp, polynomial_interpolation_determinant q hq]
  simp_rw [hpq]

theorem binomial_interpolation_det_eq_centered {R : Type*} [Field R] [CharZero R]
    {K L : ℕ} (x : (Fin K × Fin L) → ℕ) (y : (Fin K × Fin L) → R) (ζ : R) :
    (Matrix.of fun i j : Fin K × Fin L =>
      ((x j).choose i.1.val : R) * y j ^ i.2.val).det =
      (Matrix.of fun i j : Fin K × Fin L =>
        (((x j : R) - ζ) ^ i.1.val / (i.1.val.factorial : R)) * y j ^ i.2.val).det := by
  let p : Fin K → R[X] := fun k => binomialSequence R k.val
  let q : Fin K → R[X] := fun k => (k.val.factorial : R)⁻¹ • (X - C ζ) ^ k.val
  have hp (k : Fin K) : (p k).natDegree ≤ k.val :=
    le_of_eq ((binomialSequence R).natDegree_eq k.val)
  have hpowdeg (k : Fin K) : ((X - C ζ : R[X]) ^ k.val).natDegree = k.val := by
    rw [natDegree_pow, natDegree_X_sub_C, mul_one]
  have hq (k : Fin K) : (q k).natDegree ≤ k.val := by
    exact (natDegree_smul_le _ _).trans_eq (hpowdeg k)
  have hpq (k : Fin K) : (p k).coeff k.val = (q k).coeff k.val := by
    have hpc : (descPochhammer R k.val).coeff k.val = 1 := by
      have hh : (descPochhammer R k.val).coeff (descPochhammer R k.val).natDegree = 1 := by
        rw [coeff_natDegree]
        exact (monic_descPochhammer R k.val).leadingCoeff
      simpa only [descPochhammer_natDegree] using hh
    have hqc : ((X - C ζ : R[X]) ^ k.val).coeff k.val = 1 := by
      have hh : ((X - C ζ : R[X]) ^ k.val).coeff ((X - C ζ : R[X]) ^ k.val).natDegree = 1 := by
        rw [coeff_natDegree]
        exact ((monic_X_sub_C ζ).pow k.val).leadingCoeff
      simpa only [hpowdeg] using hh
    change (((k.val.factorial : R)⁻¹) • descPochhammer R k.val).coeff k.val =
      (((k.val.factorial : R)⁻¹) • (X - C ζ) ^ k.val).coeff k.val
    rw [coeff_smul, coeff_smul, hpc, hqc]
  have hh := equal_leading_coefficients_interpolation_det p q hp hq hpq (fun j => (x j : R)) y
  simpa only [p, q, binomialSequence_eval_nat, smul_eq_C_mul, eval_mul, eval_C,
    eval_pow, eval_sub, eval_X, div_eq_mul_inv, mul_comm] using hh

end LeanA113258.LaurentCore
