import LaurentBasisChange
import LaurentAnalyticEstimate
import LaurentIntegerDeterminant

/-! Exact identities identifying the integer determinant with the exponential
determinant; bounds are not substituted for these identities. -/

namespace LeanA113258.LaurentCore

open scoped BigOperators
open Polynomial Matrix

theorem sum_fin_cast_complex (n : ℕ) :
    (∑ i : Fin n, (i.val : ℂ)) = (n : ℂ) * ((n : ℂ) - 1) / 2 := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Fin.sum_univ_castSucc]
    simp only [Fin.val_castSucc, Fin.val_last, ih, Nat.cast_add, Nat.cast_one]
    ring

theorem sum_centered_second_index (K L : ℕ) :
    (∑ i : Fin K × Fin L, ((i.2.val : ℂ) - ((L : ℂ) - 1) / 2)) = 0 := by
  rw [Fintype.sum_prod_type]
  have hh : (∑ i : Fin L, ((i.val : ℂ) - ((L : ℂ) - 1) / 2)) = 0 := by
    rw [Finset.sum_sub_distrib, sum_fin_cast_complex]
    simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    ring
  simp only [hh, Finset.sum_const_zero]

theorem binomial_exponential_centering {K L : ℕ}
    (x : (Fin K × Fin L) → ℕ) (y z s : (Fin K × Fin L) → ℂ)
    (u c η A δ : ℂ)
    (hx : ∀ j, (x j : ℂ) - u * η = u * z j)
    (hy : ∀ j, y j = Complex.exp (A * (z j + η) + δ * s j))
    (hc : (∑ i : Fin K × Fin L, ((i.2.val : ℂ) - c)) = 0) :
    (Matrix.of fun i j : Fin K × Fin L =>
      ((x j).choose i.1.val : ℂ) * y j ^ i.2.val).det =
      Complex.exp (c * ∑ j, (A * (z j + η) + δ * s j)) *
        (Matrix.of fun i j : Fin K × Fin L =>
          (u ^ i.1.val / (i.1.val.factorial : ℂ)) * z j ^ i.1.val *
            Complex.exp (((i.2.val : ℂ) - c) * A * z j) *
              Complex.exp (((i.2.val : ℂ) - c) * δ * s j)).det := by
  classical
  let row : (Fin K × Fin L) → ℂ := fun i => Complex.exp (((i.2.val : ℂ) - c) * A * η)
  let col : (Fin K × Fin L) → ℂ := fun j => Complex.exp (c * (A * (z j + η) + δ * s j))
  let M : Matrix (Fin K × Fin L) (Fin K × Fin L) ℂ := Matrix.of fun i j =>
    (u ^ i.1.val / (i.1.val.factorial : ℂ)) * z j ^ i.1.val *
      Complex.exp (((i.2.val : ℂ) - c) * A * z j) *
        Complex.exp (((i.2.val : ℂ) - c) * δ * s j)
  rw [binomial_interpolation_det_eq_centered x y (u * η)]
  have hmat : (Matrix.of fun i j : Fin K × Fin L =>
      (((x j : ℂ) - u * η) ^ i.1.val / (i.1.val.factorial : ℂ)) * y j ^ i.2.val) =
      (Matrix.of fun i j => row i * (col j * M i j)) := by
    ext i j
    have he : y j ^ i.2.val = row i * col j *
        Complex.exp (((i.2.val : ℂ) - c) * A * z j) *
          Complex.exp (((i.2.val : ℂ) - c) * δ * s j) := by
      rw [hy, ← Complex.exp_nat_mul]
      dsimp [row, col]
      rw [← Complex.exp_add, ← Complex.exp_add, ← Complex.exp_add]
      congr 1
      ring
    simp only [Matrix.of_apply, hx, mul_pow, he, M]
    ring
  rw [hmat]
  have hrows : (Matrix.of fun i j => row i * (col j * M i j)).det =
      (∏ i, row i) * (Matrix.of fun i j => col j * M i j).det :=
    Matrix.det_mul_column row (Matrix.of fun i j => col j * M i j)
  rw [hrows]
  have hcol : (Matrix.of fun i j => col j * M i j).det = (∏ j, col j) * M.det :=
    Matrix.det_mul_row col M
  rw [hcol]
  have hrow : (∏ i, row i) = 1 := by
    dsimp [row]
    rw [← Complex.exp_sum, ← Finset.sum_mul, ← Finset.sum_mul, hc]
    simp
  have hcols : (∏ j, col j) = Complex.exp (c * ∑ j, (A * (z j + η) + δ * s j)) := by
    dsimp [col]
    rw [← Complex.exp_sum, ← Finset.mul_sum]
  rw [hrow, one_mul, hcols]

end LeanA113258.LaurentCore
