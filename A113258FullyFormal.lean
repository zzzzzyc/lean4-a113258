import LaurentCoprimeLowerBound
import FiniteCover

/-! A113258 closed using the fully proved coprime interpolation bound.
The finite certificates retain the explicitly authorized native computation. -/

namespace LeanA113258

open AnalyticCutoff NearPowerAnalysis

theorem remaining_ratio_fully_formal {n b e : ℕ}
    (hn : 12 ≤ n) (hb : 209 ≤ b)
    (hg : Nat.gcd e (fact (n - 1)) = 1) (hab : a n = b ^ e) :
    (e : ℝ) < (126 / 5 : ℝ) * (H (e : ℝ)) ^ 2 *
      (((n : ℝ) - 1 + 1 / (fact (n - 2) : ℝ)) / ((n : ℝ) - 4)) := by
  have hn' : (12 : ℝ) ≤ n := by exact_mod_cast hn
  have hBpos : (0 : ℝ) < (fact (n - 2) : ℝ) := by exact_mod_cast fact_pos (n - 2)
  by_cases hesmall : e < 2520
  · have he' : (e : ℝ) < 2520 := by exact_mod_cast hesmall
    have hH := H_ge_ten (e : ℝ)
    have hratio : (1 : ℝ) < ((n : ℝ) - 1 + 1 / (fact (n - 2) : ℝ)) / ((n : ℝ) - 4) := by
      apply (lt_div_iff₀ (by linarith : (0 : ℝ) < (n : ℝ) - 4)).mpr
      have hh : (0 : ℝ) < 1 / (fact (n - 2) : ℝ) := by positivity
      linarith
    have hh := mul_lt_mul_of_pos_left hratio (by positivity : (0 : ℝ) < (126 / 5) * (H (e : ℝ)) ^ 2)
    nlinarith
  have helarge : 2520 ≤ e := by omega
  have hepos : (0 : ℝ) < e := by exact_mod_cast (show 0 < e by omega)
  have hHsq : 25 * (H (e : ℝ)) ^ 2 ≤ (e : ℝ) := by
    by_cases hecut : (e : ℝ) ≤ 3500
    · rw [H_below_cutoff hepos hecut]
      have hh : (2520 : ℝ) ≤ e := by exact_mod_cast helarge
      norm_num
      linarith
    · have hh := H_sq_above_cutoff (le_of_not_ge hecut)
      nlinarith [sq_nonneg (H (e : ℝ))]
  have hodd := base_odd_of_a_eq_pow (by omega : 1 ≤ n) (by omega : 0 < e) hab
  have hb3' : (3 : ℝ) ≤ (b : ℝ) := by exact_mod_cast (show 3 ≤ b by omega)
  have hbpos : (0 : ℝ) < (b : ℝ) := by linarith
  have hblog : (4 : ℝ) ≤ Real.log (b : ℝ) := by
    have hh := Real.log_le_log (by norm_num : (0 : ℝ) < 81)
      (show (81 : ℝ) ≤ b by exact_mod_cast (show 81 ≤ b by omega))
    have heq : (81 : ℝ) = 3 ^ 4 := by norm_num
    rw [heq, Real.log_pow] at hh
    norm_num only [Nat.cast_ofNat] at hh
    linarith [Real.log_three_gt_d9]
  have hδpos : (0 : ℝ) < (delta n : ℝ) := by exact_mod_cast delta_pos (by omega : 2 ≤ n)
  have hK := fact_pos (n - 1)
  have hB := fact_pos (n - 2)
  have hpow : (b : ℝ) ^ e = (2 : ℝ) ^ fact (n - 1) + (delta n : ℝ) := by
    have hnat : b ^ e = 2 ^ fact (n - 1) + delta n := by
      rw [← hab]
      exact a_eq_main_add_delta (by omega)
    exact_mod_cast hnat
  have hδ : (delta n : ℝ) < (2 : ℝ) ^ (3 * fact (n - 2)) := by
    exact_mod_cast delta_lt_two_pow_three_B (by omega : 7 ≤ n)
  have hupper : (b : ℝ) ^ e < (2 : ℝ) ^ (fact (n - 1) + 1) := by
    have hnat := a_lt_two_pow_succ (by omega : 7 ≤ n)
    rw [hab] at hnat
    exact_mod_cast hnat
  have hMK : 3 * fact (n - 2) < fact (n - 1) := by
    rw [fact_pred_eq (by omega)]
    exact Nat.mul_lt_mul_of_pos_right (by omega) hB
  have hform := linearForm_pos hbpos hδpos hpow
  have hL := LaurentCore.two_log_lower_bound_large_coprime hb hodd hg
    (H_ge_ten (e : ℝ)) hblog hHsq (le_max_left _ _) hform
  have hratio := ratio_bound_of_log_lower hb3' (by omega) hMK hδpos hpow hδ hupper hL
  have hK' : (fact (n - 1) : ℝ) = ((n : ℝ) - 1) * (fact (n - 2) : ℝ) := by
    rw [fact_pred_eq (by omega)]
    push_cast [Nat.cast_sub (by omega : 1 ≤ n)]
    rfl
  push_cast at hratio
  rw [hK', real_factorial_ratio (by linarith : (4 : ℝ) < (n : ℝ)) hBpos] at hratio
  exact hratio

theorem officialConjecture_false : ¬ officialConjecture := by
  intro h
  obtain ⟨n, b, e, hn, hb, _h210, hne, _h7, hg, hab, _rest⟩ :=
    officialConjecture_iff_remaining_uniform.mp h
  have hratio := remaining_ratio_fully_formal hn hb hg hab
  have hn' : (12 : ℝ) ≤ n := by exact_mod_cast hn
  have hne' : (n : ℝ) ≤ e := by exact_mod_cast hne
  have hB : (9 : ℝ) ≤ (fact (n - 2) : ℝ) := by
    have hf := fact_le_of_le (by omega : 4 ≤ n - 2)
    rw [fact_four] at hf
    have hh : 9 ≤ fact (n - 2) := by omega
    exact_mod_cast hh
  have heBound := exponent_bound_from_ratio hn' hB hratio
  have hnBound := index_lt_2524 hn' hB hne' hratio
  have heNat : e < 3500 := by exact_mod_cast heBound
  have hnNat : n < 2524 := by exact_mod_cast hnBound
  have hepos : (0 : ℝ) < e := by exact_mod_cast (show 0 < e by omega)
  rw [H_below_cutoff hepos heBound.le] at hratio
  norm_num at hratio
  have hmul : (e : ℝ) * ((n : ℝ) - 4) < 2520 * ((n : ℝ) - 1 + 1 / (fact (n - 2) : ℝ)) := by
    apply (lt_div_iff₀ (by linarith : (0 : ℝ) < (n : ℝ) - 4)).mp
    simpa only [mul_div_assoc, one_div] using hratio
  have hBp : (0 : ℝ) < (fact (n - 2) : ℝ) := by linarith
  have hinv : 1 / (fact (n - 2) : ℝ) ≤ (1 / 9 : ℝ) :=
    (div_le_div_iff₀ hBp (by norm_num)).mpr (by linarith)
  have hreal : (9 : ℝ) * e * ((n : ℝ) - 4) < 22680 * ((n : ℝ) - 1) + 2520 := by nlinarith
  have hcast : ((9 * e * (n - 4) : ℕ) : ℝ) < ((22680 * (n - 1) + 2520 : ℕ) : ℝ) := by
    push_cast [Nat.cast_sub (by omega : 4 ≤ n), Nat.cast_sub (by omega : 1 ≤ n)]
    exact hreal
  have hcut : 9 * e * (n - 4) < 22680 * (n - 1) + 2520 := by exact_mod_cast hcast
  exact CoverChecker.finite_cut_cover n b e hn (by omega) (by omega) hne heNat hg hcut hab

theorem not_perfect_power_gt_four {n : ℕ} (hn : 4 < n) : ¬ IsPerfectPower (a n) := by
  intro hp
  exact officialConjecture_false ⟨n, hn, hp⟩

#print axioms remaining_ratio_fully_formal
#print axioms officialConjecture_false

end LeanA113258
