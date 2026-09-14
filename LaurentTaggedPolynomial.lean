import LaurentSchwarz

/-! Polynomial multiplicity with the second exponent fixed in each row.
This is the exact multiplicity used for the individual terms in Laurent's
Lemma 4; it does not round the real weight in Lemma 3 to an integer. -/

namespace LeanA113258.LaurentCore

open scoped BigOperators
open Polynomial

theorem sum_choose_fiber_le_sum {ι κ : Type*} [Fintype ι] [Fintype κ]
    [DecidableEq κ] (c : ι → κ) (h : ι → ℕ)
    (hinj : Function.Injective (fun i => (c i, h i))) :
    (∑ v, (Fintype.card {i // c i = v}).choose 2) ≤ ∑ i, h i := by
  classical
  calc
    _ ≤ ∑ v, ∑ i : {i // c i = v}, h i := by
      apply Finset.sum_le_sum
      intro v _
      apply choose_card_le_sum_injective
      intro i j hij
      apply Subtype.ext
      exact hinj (Prod.ext (i.property.trans j.property.symm) hij)
    _ = _ := Fintype.sum_fiberwise c h

theorem X_pow_dvd_taggedPolynomial {ι R : Type*}
    [Fintype ι] [DecidableEq ι] [CommRing R]
    {L : ℕ} (p : ι → R[X]) (c : ι → Fin L) (z s : ι → R) :
    (X : R[X]) ^ (∑ v, (Fintype.card {i // c i = v}).choose 2) ∣
      (Matrix.of fun i j =>
        (p i).comp (C (z j) * X) * C (s j ^ (c i).val)).det := by
  classical
  let H := (Finset.univ.sup fun i => (p i).natDegree) + 1
  have hH (i : ι) : (p i).natDegree < H :=
    Nat.lt_succ_of_le (Finset.le_sup (f := fun i => (p i).natDegree) (Finset.mem_univ i))
  have hexpand (i j : ι) :
      (p i).comp (C (z j) * X) * C (s j ^ (c i).val) =
      ∑ h : Fin H, X ^ h.val * C ((p i).coeff h.val *
        (z j ^ h.val * s j ^ (c i).val)) := by
    conv_lhs => rw [(p i).as_sum_range_C_mul_X_pow' (hH i)]
    simp only [Polynomial.sum_comp, Polynomial.mul_comp, Polynomial.C_comp,
      Polynomial.pow_comp, Polynomial.X_comp, mul_pow, Finset.sum_mul]
    rw [show (∑ h : Fin H, (X : R[X]) ^ h.val * C ((p i).coeff h.val *
        (z j ^ h.val * s j ^ (c i).val))) =
        ∑ h ∈ Finset.range H, X ^ h * C ((p i).coeff h *
          (z j ^ h * s j ^ (c i).val)) from
      Fin.sum_univ_eq_sum_range (fun h => X ^ h * C ((p i).coeff h *
        (z j ^ h * s j ^ (c i).val))) H]
    apply Finset.sum_congr rfl
    intro h _
    simp only [C_mul, C_pow]
    ring
  simp_rw [hexpand]
  rw [determinant_sum_rows]
  apply Finset.dvd_sum
  intro f _
  let A : Matrix ι ι R := Matrix.of fun i j =>
    (p i).coeff (f i).val * (z j ^ (f i).val * s j ^ (c i).val)
  change X ^ _ ∣ (Matrix.of fun i j => X ^ (f i).val * C (A i j)).det
  rw [determinant_X_rows]
  by_cases hA : A.det = 0
  · simp [hA]
  have hinj := scaled_monomial_det_labels_injective
    (fun i => (c i).val) (fun i => (f i).val) z s
    (fun i => (p i).coeff (f i).val) hA
  have hinj' : Function.Injective (fun i => (c i, (f i).val)) := by
    intro i j hij
    apply hinj
    have hc : c i = c j := congrArg (fun t : Fin L × ℕ => t.1) hij
    have hh : (f i).val = (f j).val := congrArg (fun t : Fin L × ℕ => t.2) hij
    exact Prod.ext (congrArg Fin.val hc) hh
  exact dvd_mul_of_dvd_left
    (pow_dvd_pow X (sum_choose_fiber_le_sum c (fun i => (f i).val) hinj')) _

end LeanA113258.LaurentCore
