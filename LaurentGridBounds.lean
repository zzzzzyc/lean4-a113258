import LaurentCombinatorial

/-! Coordinate-sum bounds for distinct points in a rectangular integer grid.
These supply the combinatorics in the sharp arithmetic and analytic bounds. -/

namespace LeanA113258.LaurentCore

open scoped BigOperators

theorem bounded_occupancy_moment {R : ℕ} (ν : Fin R → ℝ) {S : ℝ}
    (hν : ∀ i, 0 ≤ ν i) (hcap : ∀ i, ν i ≤ S) :
    (∑ i, ν i) ^ 2 ≤ S * (∑ i, ν i) + 2 * S * ∑ i, (i.val : ℝ) * ν i := by
  induction R with
  | zero => simp
  | succ R ih =>
    have hprev := ih (fun i => ν i.castSucc) (fun i => hν i.castSucc) (fun i => hcap i.castSucc)
    have hsum : (∑ i : Fin R, ν i.castSucc) ≤ (R : ℝ) * S := by
      calc
        _ ≤ ∑ _ : Fin R, S := Finset.sum_le_sum fun i _ => hcap i.castSucc
        _ = _ := by simp
    have hcross := mul_le_mul_of_nonneg_right hsum (hν (Fin.last R))
    have hsq := mul_le_mul_of_nonneg_right (hcap (Fin.last R)) (hν (Fin.last R))
    rw [Fin.sum_univ_castSucc ν, Fin.sum_univ_castSucc (fun i : Fin (R + 1) => (i.val : ℝ) * ν i)]
    simp only [Fin.val_castSucc, Fin.val_last]
    nlinarith

theorem grid_coordinate_moment {ι : Type*} [Fintype ι] {R S : ℕ}
    (r : ι → Fin R) (s : ι → Fin S)
    (hinj : Function.Injective (fun i => (r i, s i))) :
    (Fintype.card ι : ℝ) ^ 2 ≤
      (S : ℝ) * Fintype.card ι + 2 * S * ∑ i, ((r i).val : ℝ) := by
  classical
  let ν : Fin R → ℝ := fun v => Fintype.card {i // r i = v}
  have hν (v : Fin R) : 0 ≤ ν v := Nat.cast_nonneg _
  have hcap (v : Fin R) : ν v ≤ (S : ℝ) := by
    have hi : Function.Injective (fun i : {i // r i = v} => s i.val) := by
      intro i j he
      apply Subtype.ext
      exact hinj (Prod.ext (i.property.trans j.property.symm) he)
    have hh := Fintype.card_le_of_injective _ hi
    simp only [Fintype.card_fin] at hh
    change (Fintype.card {i // r i = v} : ℝ) ≤ (S : ℝ)
    exact_mod_cast hh
  have hsum : (∑ v, ν v) = (Fintype.card ι : ℝ) := by
    simpa [ν] using Fintype.sum_fiberwise r (fun _ => (1 : ℝ))
  have hmoment : (∑ v, (v.val : ℝ) * ν v) = ∑ i, ((r i).val : ℝ) := by
    simpa [ν, mul_comm] using Fintype.sum_fiberwise' r (fun v => (v.val : ℝ))
  simpa only [hsum, hmoment] using bounded_occupancy_moment ν hν hcap

theorem grid_coordinate_difference {ι : Type*} [Fintype ι] {R S : ℕ}
    (r₁ r₂ : ι → Fin R) (s₁ s₂ : ι → Fin S)
    (h₁ : Function.Injective (fun i => (r₁ i, s₁ i)))
    (h₂ : Function.Injective (fun i => (r₂ i, s₂ i))) :
    (S : ℝ) * ((∑ i, ((r₁ i).val : ℝ)) - ∑ i, ((r₂ i).val : ℝ)) ≤
      S * R * Fintype.card ι - (Fintype.card ι : ℝ) ^ 2 := by
  have hrev : Function.Injective (fun i => ((r₁ i).rev, s₁ i)) := by
    intro i j he
    apply h₁
    simpa only [Fin.rev_rev] using congrArg (fun p : Fin R × Fin S => (p.1.rev, p.2)) he
  have hlow := grid_coordinate_moment r₂ s₂ h₂
  have hupp := grid_coordinate_moment (fun i => (r₁ i).rev) s₁ hrev
  have hv (i : ι) : (((r₁ i).rev).val : ℝ) = (R : ℝ) - 1 - (r₁ i).val := by
    have hh : (r₁ i).rev.val + 1 + (r₁ i).val = R := by
      simp only [Fin.val_rev]
      omega
    have hh' : (((r₁ i).rev).val : ℝ) + 1 + (r₁ i).val = (R : ℝ) := by exact_mod_cast hh
    linarith
  simp_rw [hv] at hupp
  rw [Finset.sum_sub_distrib] at hupp
  simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul] at hupp
  nlinarith

end LeanA113258.LaurentCore
