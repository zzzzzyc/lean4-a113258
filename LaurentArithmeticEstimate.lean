import LaurentCorrelation
import LaurentIntegerDeterminant

/-! The arithmetic lower bound, including the sharp correlation term. -/

namespace LeanA113258.LaurentCore

open scoped BigOperators

theorem laurent_grid_correlation_permuted {K L R S : ℕ} (hR : 0 < R) (hS : 0 < S)
    (r : Fin K × Fin L → Fin R) (s : Fin K × Fin L → Fin S)
    (hinj : Function.Injective (fun i => (r i, s i))) (σ : Equiv.Perm (Fin K × Fin L)) :
    |∑ i : Fin K × Fin L, (((σ i).2.val : ℝ) - ((L : ℝ) - 1) / 2) * (r i).val| ≤
      (1 / 4 - (K : ℝ) * L / (12 * R * S)) * L * R * (K * L) / 2 := by
  have hh := laurent_grid_correlation hR hS (r ∘ σ.symm) (s ∘ σ.symm) (hinj.comp σ.symm.injective)
  have he := Equiv.sum_comp σ (fun i => ((i.2.val : ℝ) - ((L : ℝ) - 1) / 2) * (r (σ.symm i)).val)
  simp only [Equiv.symm_apply_apply] at he
  rw [he]
  exact hh

theorem grid_exponent_lower_of_correlation {K L R : ℕ}
    (r : Fin K × Fin L → Fin R) (σ : Equiv.Perm (Fin K × Fin L)) {G : ℝ}
    (hcorr : |∑ i, (((σ i).2.val : ℝ) - ((L : ℝ) - 1) / 2) * (r i).val| ≤ G) :
    ((L : ℝ) - 1) / 2 * (∑ i, ((r i).val : ℝ)) - G ≤
      ((∑ i, (σ i).2.val * (r i).val : ℕ) : ℝ) := by
  have he : (∑ i, (((σ i).2.val : ℝ) - ((L : ℝ) - 1) / 2) * (r i).val) =
      ((∑ i, (σ i).2.val * (r i).val : ℕ) : ℝ) - ((L : ℝ) - 1) / 2 * ∑ i, ((r i).val : ℝ) := by
    push_cast
    simp_rw [sub_mul]
    rw [Finset.sum_sub_distrib, Finset.mul_sum]
  have hh := (abs_le.mp hcorr).1
  rw [he] at hh
  linarith

theorem laurent_integer_determinant_lower_bound {K L R S : ℕ}
    (hR : 0 < R) (hS : 0 < S)
    (r : Fin K × Fin L → Fin R) (s : Fin K × Fin L → Fin S)
    (hinj : Function.Injective (fun i => (r i, s i)))
    (a b u v : ℕ) (ha : 0 < a) (hb : 0 < b)
    (hdet : (binomialIntegerMatrix (fun i : Fin K × Fin L => i.1.val) (fun i => i.2.val)
      (fun i => (r i).val) (fun i => (s i).val) a b u v).det ≠ 0) :
    let g := (1 / 4 - (K : ℝ) * L / (12 * R * S))
    let M₁ := ((L : ℝ) - 1) / 2 * (∑ i, ((r i).val : ℝ))
    let M₂ := ((L : ℝ) - 1) / 2 * (∑ i, ((s i).val : ℝ))
    (M₁ - g * L * R * (K * L) / 2) * Real.log a +
      (M₂ - g * L * S * (K * L) / 2) * Real.log b ≤
      Real.log |((binomialIntegerMatrix (fun i : Fin K × Fin L => i.1.val) (fun i => i.2.val)
        (fun i => (r i).val) (fun i => (s i).val) a b u v).det : ℝ)| := by
  classical
  dsimp only
  obtain ⟨σ₁, _, hmin₁⟩ := Finset.exists_min_image Finset.univ
    (fun σ : Equiv.Perm (Fin K × Fin L) => ∑ i, (σ i).2.val * (r i).val) Finset.univ_nonempty
  obtain ⟨σ₂, _, hmin₂⟩ := Finset.exists_min_image Finset.univ
    (fun σ : Equiv.Perm (Fin K × Fin L) => ∑ i, (σ i).2.val * (s i).val) Finset.univ_nonempty
  have hh := log_binomial_determinant_lower_bound
    (fun i : Fin K × Fin L => i.1.val) (fun i => i.2.val)
    (fun i => (r i).val) (fun i => (s i).val) a b u v
    (∑ i, (σ₁ i).2.val * (r i).val) (∑ i, (σ₂ i).2.val * (s i).val)
    ha hb hdet (fun σ => hmin₁ σ (Finset.mem_univ _)) (fun σ => hmin₂ σ (Finset.mem_univ _))
  have h₁ := grid_exponent_lower_of_correlation r σ₁
    (laurent_grid_correlation_permuted hR hS r s hinj σ₁)
  have hinj' : Function.Injective (fun i => (s i, r i)) := by
    intro i j he
    exact hinj (congrArg Prod.swap he)
  have h₂ := grid_exponent_lower_of_correlation s σ₂
    (laurent_grid_correlation_permuted hS hR s r hinj' σ₂)
  have he : (12 : ℝ) * S * R = 12 * R * S := by ring
  rw [he] at h₂
  have hloga : 0 ≤ Real.log (a : ℝ) := Real.log_nonneg (by exact_mod_cast ha)
  have hlogb : 0 ≤ Real.log (b : ℝ) := Real.log_nonneg (by exact_mod_cast hb)
  exact (add_le_add (mul_le_mul_of_nonneg_right h₁ hloga)
    (mul_le_mul_of_nonneg_right h₂ hlogb)).trans hh

end LeanA113258.LaurentCore
