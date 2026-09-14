import LaurentParameterConstraint
import LaurentGridInjectivity
import Mathlib.Analysis.Complex.ExponentialBounds

/-! A rectangular parameter choice tailored to the A113258 remaining window:
rho = 5, mu = 1/2, L = ceil(11 H/5), J = ceil(5 H log b), K = 2 J. -/

namespace LeanA113258.LaurentCore

theorem chosen_parameter_height_bound {H B J L A : ℝ}
    (hH : 10 ≤ H) (hB : 4 ≤ B) (hJ : 5 * H * B ≤ J)
    (hL₀ : 11 / 5 * H ≤ L) (hL₁ : L ≤ 11 / 5 * H + 1)
    (hA : A ≤ 7 / 10) :
    (1 / 4 - J / (12 * (J + L))) * L * 6 * ((J + L) * A + 2 * L * B) ≤
      7 / 10 * J * L + 119 / 50 * B * L ^ 2 := by
  have hH₀ : 0 < H := by linarith
  have hB₀ : 0 < B := by linarith
  have hJ₀ : 0 < J := lt_of_lt_of_le (by positivity) hJ
  have hLpos : 0 < L := by linarith
  have hsum : J + L ≠ 0 := by positivity
  have hLu : L ≤ 23 / 10 * H := by linarith
  have hfrac : B * L / (J + L) ≤ 23 / 50 := by
    apply (div_le_iff₀ (by positivity : 0 < J + L)).mpr
    have hh := mul_le_mul_of_nonneg_left hLu hB₀.le
    nlinarith
  have he : (1 / 4 - J / (12 * (J + L))) * L * 6 * ((J + L) * A + 2 * L * B) =
      A * J * L + (3 / 2 * A + 2 * B + B * L / (J + L)) * L ^ 2 := by
    field_simp
    ring
  rw [he]
  have hc : 3 / 2 * A + 2 * B + B * L / (J + L) ≤ 119 / 50 * B := by linarith
  have hh := add_le_add (mul_le_mul_of_nonneg_right hA (mul_pos hJ₀ hLpos).le)
    (mul_le_mul_of_nonneg_right hc (sq_nonneg L))
  nlinarith

theorem chosen_parameter_polynomial_margin {H B J L : ℝ}
    (hH : 10 ≤ H) (hB : 4 ≤ B) (hJ : 5 * H * B ≤ J)
    (hL₀ : 11 / 5 * H ≤ L) (hL₁ : L ≤ 11 / 5 * H + 1) :
    3 / 2 * H * B ≤ J * (21 / 10 * L - 2 * H - 14 / 5) - 119 / 50 * B * L ^ 2 := by
  let t := L - 11 / 5 * H
  have ht₀ : 0 ≤ t := sub_nonneg.mpr hL₀
  have ht₁ : t ≤ 1 := by dsimp [t]; linarith
  have ht₂ : t ^ 2 ≤ 1 := by nlinarith
  have hHt : 0 ≤ H * t := mul_nonneg (by linarith) ht₀
  have hHs : 0 ≤ H * (H - 10) := mul_nonneg (by linarith) (by linarith)
  have hm : 3 / 2 * H ≤ 5 * H * (21 / 10 * L - 2 * H - 14 / 5) - 119 / 50 * L ^ 2 := by
    have he : L = 11 / 5 * H + t := by dsimp [t]; ring
    rw [he]
    nlinarith [ht₂, hHt, hHs]
  have hb := mul_le_mul_of_nonneg_right hm (by linarith : 0 ≤ B)
  have hj := mul_le_mul_of_nonneg_right hJ (by linarith : 0 ≤ 21 / 10 * L - 2 * H - 14 / 5)
  nlinarith [hb, hj]

theorem chosen_parameter_strict_margin {H B J L A : ℝ}
    (hH : 10 ≤ H) (hB : 4 ≤ B) (hJ : 5 * H * B ≤ J)
    (hL₀ : 11 / 5 * H ≤ L) (hL₁ : L ≤ 11 / 5 * H + 1)
    (hA : A ≤ 7 / 10) :
    (4 * H + 2 * B + 4) + (2 * J - 1) * (H - 1 / 5) +
        (1 / 4 - J / (12 * (J + L))) * L * 6 * ((J + L) * A + 2 * L * B) <
      2 * J * (7 / 8 * L - 1) * Real.log 5 := by
  have hH₀ : 0 < H := by linarith
  have hB₀ : 0 < B := by linarith
  have hJ₀ : 0 < J := lt_of_lt_of_le (by positivity) hJ
  have hcoef : 0 ≤ 2 * J * (7 / 8 * L - 1) := mul_nonneg (by positivity) (by linarith)
  have hlog : (8 / 5 : ℝ) ≤ Real.log 5 := by linarith [Real.log_five_gt_d9]
  have hl := mul_le_mul_of_nonneg_left hlog hcoef
  have hheight := chosen_parameter_height_bound hH hB hJ hL₀ hL₁ hA
  have hmargin := chosen_parameter_polynomial_margin hH hB hJ hL₀ hL₁
  have hcross : 0 ≤ (H - 10) * (B - 4) := mul_nonneg (by linarith) (by linarith)
  have herr : 4 * H + 2 * B + 4 < 3 / 2 * H * B := by nlinarith
  nlinarith [hl, hheight, hmargin]

end LeanA113258.LaurentCore
