import LaurentArithmeticEstimate
import LaurentAnalyticEstimate

/-! Boundary product bounds for the unperturbed exponential determinant. -/

namespace LeanA113258.LaurentCore

open scoped BigOperators
open Complex

theorem real_exponential_product_bound {ι : Type*} [Fintype ι]
    (k : ι → ℕ) (a : ι → ℂ) (α z : ι → ℝ) (σ : Equiv.Perm ι)
    {ρ Z C : ℝ} (hρ : 0 ≤ ρ) (hZ : 0 ≤ Z)
    (hz : ∀ j, |z j| ≤ Z) (hcorr : |∑ i, α i * z (σ i)| ≤ C)
    (t : ℂ) (ht : ‖t‖ ≤ ρ) :
    (∏ i, ‖a i * (t * (z (σ i) : ℂ)) ^ k i *
      Complex.exp ((α i : ℂ) * (t * (z (σ i) : ℂ)))‖) ≤
      (∏ i, ‖a i‖) * (ρ * Z) ^ (∑ i, k i) * Real.exp (ρ * C) := by
  classical
  have hbase (i : ι) : ‖t * (z (σ i) : ℂ)‖ ≤ ρ * Z := by
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs]
    exact mul_le_mul ht (hz _) (abs_nonneg _) hρ
  have he (i : ι) : (((α i : ℂ) * (t * (z (σ i) : ℂ))).re) = t.re * (α i * z (σ i)) := by
    simp only [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, mul_zero, sub_zero, zero_mul]
    ring
  have hprod : (∏ i, ‖a i * (t * (z (σ i) : ℂ)) ^ k i *
        Complex.exp ((α i : ℂ) * (t * (z (σ i) : ℂ)))‖) ≤
      ∏ i, (‖a i‖ * (ρ * Z) ^ k i * Real.exp (t.re * (α i * z (σ i)))) := by
    apply Finset.prod_le_prod
    · intro i _
      exact norm_nonneg _
    · intro i _
      rw [norm_mul, norm_mul, norm_pow, Complex.norm_exp, he]
      exact mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (norm_nonneg _) (hbase i) _) (norm_nonneg _))
        (Real.exp_pos _).le
  rw [Finset.prod_mul_distrib, Finset.prod_mul_distrib,
    Finset.prod_pow_eq_pow_sum, ← Real.exp_sum, ← Finset.mul_sum] at hprod
  have hre : |t.re| ≤ ρ := (Complex.abs_re_le_norm t).trans ht
  have hexp : t.re * (∑ i, α i * z (σ i)) ≤ ρ * C := by
    calc
      _ ≤ |t.re * (∑ i, α i * z (σ i))| := le_abs_self _
      _ = |t.re| * |∑ i, α i * z (σ i)| := abs_mul _ _
      _ ≤ _ := mul_le_mul hre hcorr (abs_nonneg _) hρ
  exact hprod.trans (mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr hexp) (by positivity))

theorem centered_grid_coordinate_bound {R S : ℕ}
    (r : Fin R) (s : Fin S) {β : ℝ} (hβ : 0 ≤ β) :
    |(r.val : ℝ) + β * s.val - (((R : ℝ) - 1) + β * ((S : ℝ) - 1)) / 2| ≤
      (((R : ℝ) - 1) + β * ((S : ℝ) - 1)) / 2 := by
  have hr : (r.val : ℝ) ≤ (R : ℝ) - 1 := by
    have hh : r.val + 1 ≤ R := r.isLt
    have hh' : (r.val : ℝ) + 1 ≤ R := by exact_mod_cast hh
    linarith
  have hs : (s.val : ℝ) ≤ (S : ℝ) - 1 := by
    have hh : s.val + 1 ≤ S := s.isLt
    have hh' : (s.val : ℝ) + 1 ≤ S := by exact_mod_cast hh
    linarith
  have hbs := mul_le_mul_of_nonneg_left hs hβ
  have hbs₀ := mul_nonneg hβ (Nat.cast_nonneg s.val : (0 : ℝ) ≤ s.val)
  apply abs_le.mpr
  constructor <;> nlinarith [(Nat.cast_nonneg r.val : (0 : ℝ) ≤ r.val)]

theorem centered_grid_correlation_bound {K L R S : ℕ} (hR : 0 < R) (hS : 0 < S)
    (r : Fin K × Fin L → Fin R) (s : Fin K × Fin L → Fin S)
    (hinj : Function.Injective (fun i => (r i, s i))) (σ : Equiv.Perm (Fin K × Fin L))
    {A β η : ℝ} (hA : 0 ≤ A) (hβ : 0 ≤ β) :
    |∑ i : Fin K × Fin L, (((i.2.val : ℝ) - ((L : ℝ) - 1) / 2) * A) *
      ((r (σ i)).val + β * (s (σ i)).val - η)| ≤
      A * ((1 / 4 - (K : ℝ) * L / (12 * R * S)) * L * R * (K * L) / 2 +
        β * ((1 / 4 - (K : ℝ) * L / (12 * R * S)) * L * S * (K * L) / 2)) := by
  have h₁ := laurent_grid_correlation hR hS (r ∘ σ) (s ∘ σ) (hinj.comp σ.injective)
  have hinj' : Function.Injective (fun i => (s i, r i)) := by
    intro i j he
    exact hinj (congrArg Prod.swap he)
  have h₂ := laurent_grid_correlation hS hR (s ∘ σ) (r ∘ σ) (hinj'.comp σ.injective)
  have hden : (12 : ℝ) * S * R = 12 * R * S := by ring
  rw [hden] at h₂
  have he : (∑ i : Fin K × Fin L, (((i.2.val : ℝ) - ((L : ℝ) - 1) / 2) * A) *
        ((r (σ i)).val + β * (s (σ i)).val - η)) =
      A * ((∑ i, ((i.2.val : ℝ) - ((L : ℝ) - 1) / 2) * (r (σ i)).val) +
        β * (∑ i, ((i.2.val : ℝ) - ((L : ℝ) - 1) / 2) * (s (σ i)).val)) := by
    calc
      _ = A * ((∑ i, ((i.2.val : ℝ) - ((L : ℝ) - 1) / 2) * (r (σ i)).val) +
          β * (∑ i, ((i.2.val : ℝ) - ((L : ℝ) - 1) / 2) * (s (σ i)).val)) -
          (∑ i : Fin K × Fin L, ((i.2.val : ℝ) - ((L : ℝ) - 1) / 2)) * (A * η) := by
        simp only [Finset.mul_sum, Finset.sum_mul, ← Finset.sum_add_distrib, ← Finset.sum_sub_distrib]
        apply Finset.sum_congr rfl
        intro i _
        ring
      _ = _ := by rw [sum_centered_second_index_real]; ring
  rw [he, abs_mul, abs_of_nonneg hA]
  apply mul_le_mul_of_nonneg_left _ hA
  refine (abs_add_le _ _).trans ?_
  rw [abs_mul, abs_of_nonneg hβ]
  exact add_le_add h₁ (mul_le_mul_of_nonneg_left h₂ hβ)

end LeanA113258.LaurentCore
