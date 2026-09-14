import LaurentPolynomial
import Mathlib.LinearAlgebra.Matrix.ToLin
import Mathlib.LinearAlgebra.Basis.VectorSpace

/-! Extract an actual nonzero maximal minor from the coefficient test for
row independence. No determinant is assumed nonzero in the premise. -/

namespace LeanA113258.LaurentCore

open scoped BigOperators
open Matrix

theorem exists_nonzero_minor_of_row_test {ι κ R : Type*}
    [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ] [Field R]
    (A : Matrix ι κ R)
    (hA : ∀ u : ι → R, (∀ j, ∑ i, u i * A i j = 0) → u = 0) :
    ∃ f : ι → κ, Function.Injective f ∧ (A.submatrix id f).det ≠ 0 := by
  classical
  let F : (ι → R) →ₗ[R] (κ → R) := Matrix.toLin' A.transpose
  have hinj : Function.Injective F := by
    intro u v huv
    have huv0 : F (u - v) = 0 := by rw [map_sub, huv, sub_self]
    have hh : u - v = 0 := hA (u - v) (by
      intro j
      have he := congrFun huv0 j
      simpa only [F, Matrix.toLin'_apply, Matrix.mulVec, dotProduct,
        Matrix.transpose_apply, mul_comm, Pi.zero_apply] using he)
    exact sub_eq_zero.mp hh
  obtain ⟨G, hGF⟩ := F.exists_leftInverse_of_injective (LinearMap.ker_eq_bot.mpr hinj)
  let B : Matrix ι κ R := LinearMap.toMatrix' G
  have hBA : B * A.transpose = 1 := by
    have hh := congrArg LinearMap.toMatrix' hGF
    simpa only [LinearMap.toMatrix'_comp, F, LinearMap.toMatrix'_toLin',
      LinearMap.toMatrix'_id, B] using hh
  have hsum : (∑ f : ι → κ, (Matrix.of fun i j => B i (f i) * A j (f i)).det) ≠ 0 := by
    have he := determinant_sum_rows (fun (i : ι) (k : κ) (j : ι) => B i k * A j k)
    change (B * A.transpose).det = ∑ f : ι → κ,
      (Matrix.of fun i j => B i (f i) * A j (f i)).det at he
    rw [← he, hBA, Matrix.det_one]
    exact one_ne_zero
  obtain ⟨f, _, hf⟩ := Finset.exists_ne_zero_of_sum_ne_zero hsum
  have hminor : (A.submatrix id f).det ≠ 0 := by
    intro hzero
    apply hf
    have he := Matrix.det_mul_column (fun i => B i (f i)) (A.submatrix id f).transpose
    simpa only [Matrix.det_transpose, hzero, mul_zero, Matrix.transpose_apply,
      Matrix.submatrix_apply, id_eq] using he
  refine ⟨f, ?_, hminor⟩
  intro i j hij
  by_contra hne
  apply hminor
  rw [← Matrix.det_transpose]
  apply Matrix.det_zero_of_row_eq hne
  funext k
  change A k (f i) = A k (f j)
  rw [hij]

end LeanA113258.LaurentCore
