import LaurentPolynomial
import Mathlib.Algebra.Polynomial.BigOperators

/-! Degree and highest coefficient of a polynomial determinant with
different degree bounds in different columns. -/

namespace LeanA113258.LaurentCore

open scoped BigOperators
open Polynomial

theorem coeff_prod_sum_of_natDegree_le {ι R : Type*} [CommSemiring R]
    (S : Finset ι) (p : ι → R[X]) (d : ι → ℕ)
    (hd : ∀ i ∈ S, (p i).natDegree ≤ d i) :
    (∏ i ∈ S, p i).coeff (∑ i ∈ S, d i) = ∏ i ∈ S, (p i).coeff (d i) := by
  classical
  induction S using Finset.induction_on with
  | empty => simp
  | @insert i S hi ih =>
    rw [Finset.prod_insert hi, Finset.sum_insert hi, Finset.prod_insert hi,
      coeff_mul_add_eq_of_natDegree_le (hd i (Finset.mem_insert_self i S))
        ((natDegree_prod_le S p).trans
          (Finset.sum_le_sum fun j hj => hd j (Finset.mem_insert_of_mem hj))),
      ih (fun j hj => hd j (Finset.mem_insert_of_mem hj))]

theorem natDegree_det_le_sum_column_bounds {ι R : Type*}
    [Fintype ι] [DecidableEq ι] [CommRing R]
    (A : Matrix ι ι R[X]) (d : ι → ℕ)
    (hd : ∀ i j, (A i j).natDegree ≤ d j) :
    A.det.natDegree ≤ ∑ j, d j := by
  classical
  rw [Matrix.det_apply]
  apply natDegree_sum_le_of_forall_le
  intro σ _
  have hs : (Equiv.Perm.sign σ • ∏ i, A (σ i) i).natDegree ≤
      (∏ i, A (σ i) i).natDegree := by
    rcases Int.units_eq_one_or (Equiv.Perm.sign σ) with h | h
    · simp [h]
    · simp [h, Units.neg_smul]
  exact hs.trans ((natDegree_prod_le _ _).trans (Finset.sum_le_sum fun i _ => hd (σ i) i))

theorem coeff_det_sum_column_bounds {ι R : Type*}
    [Fintype ι] [DecidableEq ι] [CommRing R]
    (A : Matrix ι ι R[X]) (d : ι → ℕ)
    (hd : ∀ i j, (A i j).natDegree ≤ d j) :
    A.det.coeff (∑ j, d j) = (Matrix.of fun i j => (A i j).coeff (d j)).det := by
  classical
  rw [Matrix.det_apply, finsetSum_coeff, Matrix.det_apply]
  apply Finset.sum_congr rfl
  intro σ _
  rw [coeff_smul, coeff_prod_sum_of_natDegree_le _ _ d (fun i _ => hd (σ i) i)]
  rfl

end LeanA113258.LaurentCore
