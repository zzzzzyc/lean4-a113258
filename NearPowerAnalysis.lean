import AnalyticCutoff

namespace LeanA113258.NearPowerAnalysis

open AnalyticCutoff

theorem log_two_lower : (2 / 3 : ℝ) < Real.log 2 := by
  have h := Real.lt_log_one_add_of_pos (x := (1 : ℝ)) (by norm_num)
  norm_num at h
  exact h

theorem log_two_upper : Real.log (2 : ℝ) < 1 := by
  have := Real.log_lt_sub_one_of_pos (x := (2 : ℝ)) (by norm_num) (by norm_num)
  linarith

theorem log_base_gt_one {b : ℝ} (hb : 3 ≤ b) : 1 < Real.log b := by
  have hthree : (1 : ℝ) < Real.log 3 := by
    have h := Real.lt_log_one_add_of_pos (x := (2 : ℝ)) (by norm_num)
    norm_num at h
    exact h
  exact lt_of_lt_of_le hthree (Real.log_le_log (by norm_num) hb)

noncomputable def linearForm (b : ℝ) (e K : ℕ) : ℝ :=
  (e : ℝ) * Real.log b - (K : ℝ) * Real.log 2

theorem linearForm_eq_log_gap {b d : ℝ} {e K : ℕ} (hb : 0 < b) (hd : 0 < d)
    (hpow : b ^ e = (2 : ℝ) ^ K + d) :
    linearForm b e K = Real.log (1 + d / (2 : ℝ) ^ K) := by
  have htwo : (2 : ℝ) ^ K ≠ 0 := ne_of_gt (by positivity : 0 < (2 : ℝ) ^ K)
  have hfactor : b ^ e = (2 : ℝ) ^ K * (1 + d / (2 : ℝ) ^ K) := by
    rw [hpow]
    field_simp
  have hlog := congrArg Real.log hfactor
  rw [Real.log_mul htwo (ne_of_gt (by positivity : 0 < 1 + d / (2 : ℝ) ^ K)),
    Real.log_pow, Real.log_pow] at hlog
  unfold linearForm
  linarith

theorem linearForm_pos {b d : ℝ} {e K : ℕ} (hb : 0 < b) (hd : 0 < d)
    (hpow : b ^ e = (2 : ℝ) ^ K + d) : 0 < linearForm b e K := by
  rw [linearForm_eq_log_gap hb hd hpow]
  apply Real.log_pos
  have : 0 < d / (2 : ℝ) ^ K := by positivity
  linarith

theorem log_linearForm_upper {b d : ℝ} {e K M : ℕ} (hb : 0 < b) (hd : 0 < d)
    (hpow : b ^ e = (2 : ℝ) ^ K + d) (hdelta : d < (2 : ℝ) ^ M) :
    Real.log (linearForm b e K) < ((M : ℝ) - (K : ℝ)) * Real.log 2 := by
  have hK : 0 < (2 : ℝ) ^ K := by positivity
  have hq : 0 < d / (2 : ℝ) ^ K := div_pos hd hK
  have hsmall : linearForm b e K < d / (2 : ℝ) ^ K := by
    rw [linearForm_eq_log_gap hb hd hpow]
    have := Real.log_lt_sub_one_of_pos (x := 1 + d / (2 : ℝ) ^ K)
      (by linarith) (by linarith)
    linarith
  have hfrac : d / (2 : ℝ) ^ K < (2 : ℝ) ^ M / (2 : ℝ) ^ K :=
    div_lt_div_of_pos_right hdelta hK
  have hlog := Real.log_lt_log (linearForm_pos hb hd hpow) (hsmall.trans hfrac)
  rw [Real.log_div (by positivity) (ne_of_gt hK), Real.log_pow, Real.log_pow] at hlog
  convert hlog using 1 <;> ring

theorem base_log_upper {b : ℝ} {e K : ℕ} (hb : 0 < b) (he : 0 < e)
    (hpow : b ^ e < (2 : ℝ) ^ (K + 1)) :
    Real.log b < ((K : ℝ) + 1) * Real.log 2 / (e : ℝ) := by
  have hlog := Real.log_lt_log (by positivity : 0 < b ^ e) hpow
  rw [Real.log_pow, Real.log_pow] at hlog
  apply (lt_div_iff₀ (by exact_mod_cast he : 0 < (e : ℝ))).2
  push_cast at hlog
  nlinarith

theorem normalized_coefficient_lt {b : ℝ} {e K : ℕ} (hb : 3 ≤ b) (hK : 0 < K)
    (hform : 0 < linearForm b e K) :
    (K : ℝ) / Real.log b + (e : ℝ) < (5 / 2 : ℝ) * (e : ℝ) := by
  have hlogb := log_base_gt_one hb
  have hKpos : 0 < (K : ℝ) := by exact_mod_cast hK
  have hstrict : (2 / 3 : ℝ) * (K : ℝ) < (e : ℝ) * Real.log b := by
    have hm := mul_lt_mul_of_pos_right log_two_lower hKpos
    unfold linearForm at hform
    nlinarith
  have hdiv : (K : ℝ) / Real.log b < (3 / 2 : ℝ) * (e : ℝ) := by
    apply (div_lt_iff₀ (by linarith : 0 < Real.log b)).2
    nlinarith
  linarith

/-- Transport the exact normalized logarithm used by Laurent to `H e`.
The lower bound is an explicit premise, not an axiom or an established theorem here. -/
theorem weaken_laurent_lower {b : ℝ} {e K : ℕ} (hb : 3 ≤ b) (hK : 0 < K)
    (he : 0 < e) (hform : 0 < linearForm b e K)
    (hL : -(126 / 5 : ℝ) *
      (max (Real.log ((K : ℝ) / Real.log b + (e : ℝ)) + 19 / 50) 10) ^ 2 * Real.log b
      ≤ Real.log (linearForm b e K)) :
    -(126 / 5 : ℝ) * (H (e : ℝ)) ^ 2 * Real.log b ≤ Real.log (linearForm b e K) := by
  have hb' := log_base_gt_one hb
  have he' : 0 < (e : ℝ) := by exact_mod_cast he
  have hK' : 0 < (K : ℝ) := by exact_mod_cast hK
  let S := max (Real.log ((K : ℝ) / Real.log b + (e : ℝ)) + 19 / 50) 10
  have hS : 10 ≤ S := le_max_right _ _
  have hlog := Real.log_le_log
    (show 0 < (K : ℝ) / Real.log b + (e : ℝ) by positivity)
    (le_of_lt (normalized_coefficient_lt hb hK hform))
  have hSH : S ≤ H (e : ℝ) := max_le_max (by linarith) (le_refl _)
  have hH := H_ge_ten (e : ℝ)
  have hsq : S ^ 2 ≤ (H (e : ℝ)) ^ 2 := by
    nlinarith [mul_nonneg (sub_nonneg.mpr hSH) (show 0 ≤ H (e : ℝ) + S by linarith)]
  have hm := mul_le_mul_of_nonneg_right hsq (show 0 ≤ Real.log b by linarith)
  change -(126 / 5 : ℝ) * S ^ 2 * Real.log b ≤ _ at hL
  nlinarith

/-- Complete elementary deduction from a logarithmic lower bound to an exponent bound. -/
theorem ratio_bound_of_log_lower {b d : ℝ} {e K M : ℕ}
    (hb : 3 ≤ b) (he : 0 < e) (hMK : M < K) (hd : 0 < d)
    (hpow : b ^ e = (2 : ℝ) ^ K + d) (hdelta : d < (2 : ℝ) ^ M)
    (hu : b ^ e < (2 : ℝ) ^ (K + 1))
    (hL : -(126 / 5 : ℝ) * (H (e : ℝ)) ^ 2 * Real.log b ≤ Real.log (linearForm b e K)) :
    (e : ℝ) < (126 / 5 : ℝ) * (H (e : ℝ)) ^ 2 * (((K : ℝ) + 1) / ((K : ℝ) - (M : ℝ))) := by
  have hbpos : 0 < b := by linarith
  have hl2 : 0 < Real.log (2 : ℝ) := by linarith [log_two_lower]
  have he' : 0 < (e : ℝ) := by exact_mod_cast he
  have hMK' : (M : ℝ) < (K : ℝ) := by exact_mod_cast hMK
  have hlogU := log_linearForm_upper hbpos hd hpow hdelta
  have hblog := (lt_div_iff₀ he').mp (base_log_upper hbpos he hu)
  let T : ℝ := (126 / 5 : ℝ) * (H (e : ℝ)) ^ 2
  have hT : 0 < T := by
    have := H_ge_ten (e : ℝ)
    dsimp [T]
    positivity
  have hlow : ((K : ℝ) - (M : ℝ)) * Real.log 2 < T * Real.log b := by
    dsimp [T]
    linarith
  have hleft := mul_lt_mul_of_pos_left hlow he'
  have hright := mul_lt_mul_of_pos_left hblog hT
  have hcombined : ((e : ℝ) * ((K : ℝ) - (M : ℝ))) * Real.log 2 <
      (T * ((K : ℝ) + 1)) * Real.log 2 := by nlinarith
  have hcancel := (mul_lt_mul_iff_left₀ hl2).mp hcombined
  have hdiv := (lt_div_iff₀ (show 0 < (K : ℝ) - (M : ℝ) by linarith)).mpr hcancel
  simpa only [T, mul_div_assoc] using hdiv

#print axioms log_linearForm_upper
#print axioms base_log_upper
#print axioms normalized_coefficient_lt
#print axioms weaken_laurent_lower
#print axioms ratio_bound_of_log_lower

end LeanA113258.NearPowerAnalysis
