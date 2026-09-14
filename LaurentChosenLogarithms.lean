import LaurentChosenParameters

namespace LeanA113258.LaurentCore

theorem chosen_factorial_error_bound (N : ℕ) (hN : 0 < N) {H B : ℝ}
    (hH : 10 ≤ H) (hB : 4 ≤ B) (hNup : (N : ℝ) ≤ 32 * H ^ 2 * B) :
    2 * (Real.log (N.factorial : ℝ) + N) / N ≤ 4 * H + 2 * B + 4 := by
  have hN' : (0 : ℝ) < N := by exact_mod_cast hN
  have hH' : 0 < H := by linarith
  have hB' : 0 < B := by linarith
  have hnlog : Real.log (N : ℝ) ≤ 2 * H + B + 1 := by
    have hh := Real.log_le_log hN' hNup
    rw [Real.log_mul (by positivity) (by positivity),
      Real.log_mul (by positivity) (by positivity), Real.log_pow] at hh
    norm_num only [Nat.cast_ofNat] at hh
    have h32 : Real.log (32 : ℝ) ≤ 4 := by
      have he : (32 : ℝ) = 2 ^ 5 := by norm_num
      rw [he, Real.log_pow]
      norm_num only [Nat.cast_ofNat]
      linarith [Real.log_two_lt_d9]
    nlinarith [Real.log_le_sub_one_of_pos hH', Real.log_le_sub_one_of_pos hB']
  have hf := (log_factorial_effective N hN).2
  have hn1 := Real.log_le_sub_one_of_pos hN'
  have hh : Real.log (N.factorial : ℝ) + N ≤ N * (Real.log (N : ℝ) + 1) := by nlinarith
  have hm := mul_le_mul_of_nonneg_left hnlog hN'.le
  apply (div_le_iff₀ hN').mpr
  nlinarith

theorem chosen_coordinate_ratio_bound {H B J L β : ℝ}
    (hH : 10 ≤ H) (hB : 4 ≤ B) (hJ : 5 * H * B ≤ J)
    (hL₀ : 11 / 5 * H ≤ L) (hL₁ : L ≤ 11 / 5 * H + 1)
    (hβ : β ≤ 3 / 2 * B) :
    (J + L - 1 + (2 * L - 1) * β) / (4 * J) ≤ 5 / 8 := by
  have hH₀ : 0 < H := by linarith
  have hB₀ : 0 < B := by linarith
  have hJ₀ : 0 < J := lt_of_lt_of_le (by positivity) hJ
  have hLu : L ≤ 23 / 10 * H := by linarith
  have hLpos : 0 < L := by linarith
  have hm := mul_le_mul_of_nonneg_right hLu (by linarith : 0 ≤ 1 + 3 * B)
  have hcross := mul_nonneg hH₀.le (show 0 ≤ B - 4 by linarith)
  have hratio : L * (1 + 3 * B) ≤ 3 / 2 * J := by nlinarith
  have hb := mul_le_mul_of_nonneg_left hβ (by linarith : 0 ≤ 2 * L - 1)
  apply (div_le_iff₀ (by positivity : 0 < 4 * J)).mpr
  nlinarith

theorem chosen_parameter_log_bound {H B J L e v : ℝ}
    (hH : 10 ≤ H) (hB : 4 ≤ B) (hJ : 5 * H * B ≤ J)
    (hL₀ : 11 / 5 * H ≤ L) (hL₁ : L ≤ 11 / 5 * H + 1)
    (he : 0 < e) (hv : 0 ≤ v) (hβ : v / e ≤ 3 / 2 * B)
    (hHlog : Real.log ((5 / 2 : ℝ) * e) + 19 / 50 ≤ H) :
    Real.log (((J + L - 1) * e + (2 * L - 1) * v) / (4 * J)) + 3 / 2 ≤ H - 1 / 5 := by
  have hH₀ : 0 < H := by linarith
  have hB₀ : 0 < B := by linarith
  have hJ₀ : 0 < J := lt_of_lt_of_le (by positivity) hJ
  have hLpos : 1 < L := by linarith
  have hE : 0 < ((J + L - 1) * e + (2 * L - 1) * v) / (4 * J) := by
    apply div_pos _ (by positivity)
    have hh := mul_nonneg (show 0 ≤ 2 * L - 1 by linarith) hv
    have hh' := mul_pos (show 0 < J + L - 1 by linarith) he
    linarith
  have hratio := chosen_coordinate_ratio_bound hH hB hJ hL₀ hL₁ hβ
  have hh := mul_le_mul_of_nonneg_right hratio he.le
  have hid : (J + L - 1 + (2 * L - 1) * (v / e)) / (4 * J) * e =
      ((J + L - 1) * e + (2 * L - 1) * v) / (4 * J) := by field_simp
  rw [hid] at hh
  have hlog := Real.log_le_log hE hh
  have heq : (5 / 8 : ℝ) * e = ((5 / 2 : ℝ) * e) / 4 := by ring
  rw [heq, Real.log_div (x := (5 / 2 : ℝ) * e) (y := 4) (by positivity) (by norm_num)] at hlog
  have h4 : Real.log (4 : ℝ) = 2 * Real.log 2 := by
    have heq : (4 : ℝ) = 2 ^ 2 := by norm_num
    rw [heq, Real.log_pow]
    norm_num
  rw [h4] at hlog
  linarith [Real.log_two_gt_d9]

end LeanA113258.LaurentCore
