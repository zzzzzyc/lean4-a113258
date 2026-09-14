import LaurentChosenLogarithms

namespace LeanA113258.LaurentCore

theorem chosen_dimensions_bounds {H B : ℝ} (hH : 10 ≤ H) (hB : 4 ≤ B) :
    let J := ⌈5 * H * B⌉₊
    let L := ⌈11 / 5 * H⌉₊
    0 < J ∧ 0 < L ∧ 5 * H * B ≤ J ∧ (J : ℝ) ≤ 5 * H * B + 1 ∧
      11 / 5 * H ≤ L ∧ (L : ℝ) ≤ 11 / 5 * H + 1 ∧
        ((2 * J * L : ℕ) : ℝ) ≤ 30 * H ^ 2 * B ∧ (L : ℝ) ^ 2 ≤ 6 * H ^ 2 := by
  dsimp only
  have hH₀ : 0 < H := by linarith
  have hB₀ : 0 < B := by linarith
  have hJ : 5 * H * B ≤ (⌈5 * H * B⌉₊ : ℝ) := Nat.le_ceil _
  have hJu : (⌈5 * H * B⌉₊ : ℝ) ≤ 5 * H * B + 1 := (Nat.ceil_lt_add_one (by positivity)).le
  have hL : 11 / 5 * H ≤ (⌈11 / 5 * H⌉₊ : ℝ) := Nat.le_ceil _
  have hLu : (⌈11 / 5 * H⌉₊ : ℝ) ≤ 11 / 5 * H + 1 := (Nat.ceil_lt_add_one (by positivity)).le
  have hJpos : 0 < ⌈5 * H * B⌉₊ := Nat.one_le_ceil_iff.mpr (by positivity)
  have hLpos : 0 < ⌈11 / 5 * H⌉₊ := Nat.one_le_ceil_iff.mpr (by positivity)
  refine ⟨hJpos, hLpos, hJ, hJu, hL, hLu, ?_, ?_⟩
  · have hHB : 40 ≤ H * B := by nlinarith [mul_nonneg (show 0 ≤ H - 10 by linarith) (show 0 ≤ B - 4 by linarith)]
    have hJ' : (⌈5 * H * B⌉₊ : ℝ) ≤ 51 / 10 * H * B := by linarith
    have hL' : (⌈11 / 5 * H⌉₊ : ℝ) ≤ 23 / 10 * H := by linarith
    have hh := mul_le_mul hJ' hL' (Nat.cast_nonneg _) (by positivity)
    push_cast
    nlinarith [hh, mul_pos (sq_pos_of_pos hH₀) hB₀]
  · have hL' : (⌈11 / 5 * H⌉₊ : ℝ) ≤ 23 / 10 * H := by linarith
    have hh := mul_self_le_mul_self (Nat.cast_nonneg _) hL'
    nlinarith [sq_nonneg H]

theorem chosen_additive_width {H B : ℝ} {e v : ℕ}
    (hH : 10 ≤ H) (hB : 4 ≤ B) (he : 25 * H ^ 2 ≤ (e : ℝ))
    (hform : (e : ℝ) * B - (v : ℝ) * Real.log 2 < 1) :
    ⌈5 * H * B⌉₊ + 1 ≤ v := by
  have hH₀ : 0 < H := by linarith
  have hB₀ : 0 < B := by linarith
  have heH : 250 * H ≤ (e : ℝ) := by nlinarith [mul_nonneg hH₀.le (show 0 ≤ H - 10 by linarith)]
  have hlog : Real.log (2 : ℝ) ≤ 1 := by linarith [Real.log_two_lt_d9]
  have hv := mul_le_mul_of_nonneg_left hlog (Nat.cast_nonneg v : (0 : ℝ) ≤ v)
  have hJu := (chosen_dimensions_bounds hH hB).2.2.2.1
  have hh := mul_le_mul_of_nonneg_right heH hB₀.le
  have hHB : 40 ≤ H * B := by nlinarith [mul_nonneg (show 0 ≤ H - 10 by linarith) (show 0 ≤ B - 4 by linarith)]
  have hreal : (⌈5 * H * B⌉₊ : ℝ) + 1 ≤ (v : ℝ) := by nlinarith
  exact_mod_cast hreal

theorem chosen_error_exponent_bound {H B : ℝ} (hH : 10 ≤ H) (hB : 4 ≤ B) :
    (1 / 2 : ℝ) * ((2 * ⌈5 * H * B⌉₊ * ⌈11 / 5 * H⌉₊ : ℕ) : ℝ) * Real.log 5 ≤
      (126 / 5 : ℝ) * H ^ 2 * B := by
  have hd := (chosen_dimensions_bounds hH hB).2.2.2.2.2.2.1
  have hlog : Real.log (5 : ℝ) ≤ 161 / 100 := by linarith [Real.log_five_lt_d9]
  have hlog₀ : 0 ≤ Real.log (5 : ℝ) := Real.log_nonneg (by norm_num)
  have hh := mul_le_mul hd hlog hlog₀ (by positivity)
  have hpos : 0 ≤ H ^ 2 * B := mul_nonneg (sq_nonneg _) (by linarith)
  nlinarith

end LeanA113258.LaurentCore
