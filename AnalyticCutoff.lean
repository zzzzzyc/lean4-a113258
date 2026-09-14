import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

/-!
Explicit real inequalities used to specialize Laurent's published estimate.
This file does not assume or assert that estimate itself.
-/

namespace LeanA113258.AnalyticCutoff

noncomputable def H (x : ℝ) : ℝ := max (Real.log ((5 / 2 : ℝ) * x) + 19 / 50) 10

theorem log_8750_bound : Real.log (8750 : ℝ) + 19 / 50 < 10 := by
  have he := Real.sum_le_exp_of_nonneg (x := (481 / 50 : ℝ)) (by norm_num) 14
  norm_num [Finset.sum_range_succ] at he
  have h : Real.log (8750 : ℝ) < 481 / 50 := by
    apply (Real.log_lt_iff_lt_exp (by norm_num)).2
    linarith
  linarith

theorem H_ge_ten (x : ℝ) : 10 ≤ H x := le_max_right _ _

theorem H_at_cutoff : H 3500 = 10 := by
  unfold H
  norm_num only [show (5 / 2 : ℝ) * 3500 = 8750 by norm_num]
  exact max_eq_right (le_of_lt log_8750_bound)

theorem H_below_cutoff {x : ℝ} (hx : 0 < x) (hcut : x ≤ 3500) : H x = 10 := by
  have hlog : Real.log ((5 / 2 : ℝ) * x) ≤ Real.log 8750 := by
    apply Real.log_le_log (by positivity)
    linarith
  exact max_eq_right (by linarith [log_8750_bound])

/-- A square-root comparison avoids any argument about piecewise derivatives. -/
theorem H_sq_above_cutoff {x : ℝ} (hx : 3500 ≤ x) : 35 * (H x) ^ 2 ≤ x := by
  let t : ℝ := Real.sqrt (x / 3500)
  have ht : 1 ≤ t := Real.one_le_sqrt.mpr (by linarith)
  have htpos : 0 < t := by linarith
  have hs : t ^ 2 = x / 3500 := Real.sq_sqrt (by linarith)
  have hxt : x = 3500 * t ^ 2 := by nlinarith
  have hlog : Real.log ((5 / 2 : ℝ) * x) = Real.log 8750 + 2 * Real.log t := by
    have harg : (5 / 2 : ℝ) * x = 8750 * t ^ 2 := by rw [hxt]; ring
    rw [harg, Real.log_mul (by norm_num) (pow_ne_zero 2 (ne_of_gt htpos)), Real.log_pow]
    norm_num
  have hlt : Real.log ((5 / 2 : ℝ) * x) + 19 / 50 ≤ 10 * t := by
    rw [hlog]
    linarith [log_8750_bound, Real.log_le_sub_one_of_pos htpos]
  have hh : H x ≤ 10 * t := max_le hlt (by linarith)
  have hhpos := H_ge_ten x
  have hprod : 0 ≤ (10 * t - H x) * (10 * t + H x) :=
    mul_nonneg (by linarith) (by linarith)
  nlinarith

theorem exponent_lt_3500 {e : ℝ} (hbound : e < 35 * (H e) ^ 2) : e < 3500 := by
  by_contra h
  have := H_sq_above_cutoff (le_of_not_gt h)
  linarith

/-- The elementary factorial ratio bound, stated over the reals. -/
theorem ratio_le {n B : ℝ} (hn : 12 ≤ n) (hB : 9 ≤ B) :
    (n - 1 + 1 / B) / (n - 4) ≤ 25 / 18 := by
  have hBpos : 0 < B := by linarith
  have hinv : 1 / B ≤ (1 / 9 : ℝ) := (div_le_div_iff₀ hBpos (by norm_num)).2 (by linarith)
  apply (div_le_iff₀ (by linarith : 0 < n - 4)).2
  linarith

theorem exponent_bound_from_ratio {n B e : ℝ} (hn : 12 ≤ n) (hB : 9 ≤ B)
    (hbound : e < (126 / 5 : ℝ) * (H e) ^ 2 * ((n - 1 + 1 / B) / (n - 4))) :
    e < 3500 := by
  apply exponent_lt_3500
  have hr := mul_le_mul_of_nonneg_left (ratio_le hn hB)
    (show 0 ≤ (126 / 5 : ℝ) * (H e) ^ 2 by positivity)
  nlinarith

theorem index_lt_2524 {n B e : ℝ} (hn : 12 ≤ n) (hB : 9 ≤ B) (hne : n ≤ e)
    (hbound : e < (126 / 5 : ℝ) * (H e) ^ 2 * ((n - 1 + 1 / B) / (n - 4))) :
    n < 2524 := by
  have hepos : 0 < e := by linarith
  have he := exponent_bound_from_ratio hn hB hbound
  rw [H_below_cutoff hepos (le_of_lt he)] at hbound
  norm_num at hbound
  have hbound' : e * (n - 4) < 2520 * (n - 1 + 1 / B) := by
    apply (lt_div_iff₀ (by linarith : 0 < n - 4)).1
    simpa only [mul_div_assoc, one_div] using hbound
  have hBpos : 0 < B := by linarith
  have hinv : 1 / B ≤ (1 / 9 : ℝ) := (div_le_div_iff₀ hBpos (by norm_num)).2 (by linarith)
  by_contra h
  have hnlarge : 2524 ≤ n := le_of_not_gt h
  have hp : 0 ≤ n * (n - 2524) := mul_nonneg (by linarith) (by linarith)
  have hq : 0 ≤ (e - n) * (n - 4) := mul_nonneg (by linarith) (by linarith)
  nlinarith

#print axioms log_8750_bound
#print axioms H_at_cutoff
#print axioms exponent_lt_3500
#print axioms exponent_bound_from_ratio
#print axioms index_lt_2524

end LeanA113258.AnalyticCutoff
