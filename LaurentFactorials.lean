import LaurentCombinatorial

/-! Elementary effective logarithmic bounds for factorials and their products. -/

namespace LeanA113258.LaurentCore

open scoped BigOperators

theorem consecutive_log_bounds (n : ℕ) (hn : 0 < n) :
    (n : ℝ) * (Real.log ((n : ℝ) + 1) - Real.log n) ≤ 1 ∧
      1 ≤ ((n : ℝ) + 1) * (Real.log ((n : ℝ) + 1) - Real.log n) := by
  have hn' : (0 : ℝ) < n := by exact_mod_cast hn
  have hr : 0 < ((n : ℝ) + 1) / n := div_pos (by positivity) hn'
  have hu := Real.log_le_sub_one_of_pos hr
  have hl := Real.one_sub_inv_le_log_of_pos hr
  rw [Real.log_div (by positivity) (ne_of_gt hn')] at hu hl
  have hu' := mul_le_mul_of_nonneg_left hu hn'.le
  have hl' := mul_le_mul_of_nonneg_left hl (by positivity : (0 : ℝ) ≤ (n : ℝ) + 1)
  have he₁ : (n : ℝ) * (((n : ℝ) + 1) / n - 1) = 1 := by field_simp; ring
  have he₂ : ((n : ℝ) + 1) * (1 - (((n : ℝ) + 1) / n)⁻¹) = 1 := by field_simp; ring
  rw [he₁] at hu'
  rw [he₂] at hl'
  exact ⟨hu', hl'⟩

theorem log_factorial_effective (n : ℕ) (hn : 0 < n) :
    (n : ℝ) * Real.log n - n + 1 ≤ Real.log (n.factorial : ℝ) ∧
      Real.log (n.factorial : ℝ) ≤ ((n : ℝ) + 1) * Real.log n - n + 1 := by
  induction n, hn using Nat.le_induction with
  | base => norm_num
  | succ n hn ih =>
    have hd := consecutive_log_bounds n hn
    have he : Real.log ((n + 1).factorial : ℝ) = Real.log ((n : ℝ) + 1) + Real.log (n.factorial : ℝ) := by
      rw [Nat.factorial_succ, Nat.cast_mul, Real.log_mul (by positivity) (by positivity)]
      push_cast
      rfl
    rw [he]
    push_cast
    constructor <;> nlinarith [ih.1, ih.2, hd.1, hd.2]

theorem log_superfactorial_lower (K : ℕ) (hK : 0 < K) :
    (K : ℝ) * (K - 1) / 2 * Real.log K - 3 * K * (K - 1) / 4 ≤
      ∑ k : Fin K, Real.log (k.val.factorial : ℝ) := by
  induction K, hK using Nat.le_induction with
  | base => norm_num [Fin.sum_univ_one]
  | succ K hK ih =>
    rw [Fin.sum_univ_castSucc]
    simp only [Fin.val_castSucc, Fin.val_last, Nat.cast_add, Nat.cast_one]
    have hf := (log_factorial_effective K hK).1
    have hd := (consecutive_log_bounds K hK).1
    have hm := mul_le_mul_of_nonneg_left hd (by positivity : (0 : ℝ) ≤ ((K : ℝ) + 1) / 2)
    nlinarith [ih, hf, hm]

theorem sum_first_index_real (K L : ℕ) :
    ((∑ i : Fin K × Fin L, i.1.val : ℕ) : ℝ) = (K : ℝ) * L * (K - 1) / 2 := by
  have hs (n : ℕ) : (∑ k : Fin n, (k.val : ℝ)) = (n : ℝ) * (n - 1) / 2 := by
    induction n with
    | zero => simp
    | succ n ih =>
      rw [Fin.sum_univ_castSucc]
      simp only [Fin.val_castSucc, Fin.val_last, ih, Nat.cast_add, Nat.cast_one]
      ring
  push_cast
  rw [Fintype.sum_prod_type]
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  rw [← Finset.mul_sum, hs]
  ring

theorem log_polynomial_factor_bound (K L : ℕ) (hK : 0 < K)
    {u ρ η : ℝ} (hu : 0 < u) (hρ : 0 < ρ) (hη : 0 < η) :
    Real.log ((∏ i : Fin K × Fin L, (u ^ i.1.val / (i.1.val.factorial : ℝ))) *
      (ρ * η) ^ (∑ i : Fin K × Fin L, i.1.val)) ≤
      (K : ℝ) * L * (K - 1) / 2 * (Real.log ρ + Real.log (u * η / K) + 3 / 2) := by
  have hK' : (0 : ℝ) < K := by exact_mod_cast hK
  have hprod : (0 : ℝ) < ∏ i : Fin K × Fin L, (u ^ i.1.val / (i.1.val.factorial : ℝ)) := by
    exact Finset.prod_pos (fun i _ => div_pos (pow_pos hu _) (by positivity))
  rw [Real.log_mul (ne_of_gt hprod) (by positivity),
    Real.log_prod (fun i _ => (div_pos (pow_pos hu _) (by positivity)).ne'), Real.log_pow]
  have hi (i : Fin K × Fin L) : Real.log (u ^ i.1.val / (i.1.val.factorial : ℝ)) =
      (i.1.val : ℝ) * Real.log u - Real.log (i.1.val.factorial : ℝ) := by
    rw [Real.log_div (by positivity) (by positivity), Real.log_pow]
  simp_rw [hi]
  rw [Finset.sum_sub_distrib, ← Finset.sum_mul]
  have hs := sum_first_index_real K L
  push_cast at hs
  rw [hs, sum_first_index_real, Real.log_mul (ne_of_gt hρ) (ne_of_gt hη)]
  have hf : (∑ i : Fin K × Fin L, Real.log (i.1.val.factorial : ℝ)) =
      (L : ℝ) * ∑ k : Fin K, Real.log (k.val.factorial : ℝ) := by
    rw [Fintype.sum_prod_type]
    simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    rw [Finset.mul_sum]
  rw [hf, Real.log_div (by positivity) (ne_of_gt hK'),
    Real.log_mul (ne_of_gt hu) (ne_of_gt hη)]
  have hh := mul_le_mul_of_nonneg_left (log_superfactorial_lower K hK)
    (Nat.cast_nonneg L : (0 : ℝ) ≤ L)
  nlinarith

end LeanA113258.LaurentCore
