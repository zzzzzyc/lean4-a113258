import LaurentChosenDimensions

/-! Effective two-logarithm lower bound in the large coprime range needed by
the A113258 proof. Every determinant and parameter estimate is proved here. -/

namespace LeanA113258.LaurentCore

set_option maxHeartbeats 2000000 in
theorem two_log_lower_bound_large_coprime {b e v : ℕ} {H : ℝ}
    (hb : 209 ≤ b) (hodd : b % 2 = 1) (hcop : e.Coprime v)
    (hH : 10 ≤ H) (hB : 4 ≤ Real.log (b : ℝ))
    (he : 25 * H ^ 2 ≤ (e : ℝ))
    (hHlog : Real.log ((5 / 2 : ℝ) * e) + 19 / 50 ≤ H)
    (hform : 0 < (e : ℝ) * Real.log (b : ℝ) - (v : ℝ) * Real.log 2) :
    -(126 / 5 : ℝ) * H ^ 2 * Real.log (b : ℝ) ≤
      Real.log ((e : ℝ) * Real.log (b : ℝ) - (v : ℝ) * Real.log 2) := by
  classical
  let B := Real.log (b : ℝ)
  let A := Real.log (2 : ℝ)
  let Λ := (e : ℝ) * B - (v : ℝ) * A
  let J := ⌈5 * H * B⌉₊
  let L := ⌈11 / 5 * H⌉₊
  let K := 2 * J
  let R := J + L
  let S := 2 * L
  let η := (((R : ℝ) - 1) + (v : ℝ) / e * ((S : ℝ) - 1)) / 2
  have he' : (0 : ℝ) < e := lt_of_lt_of_le (by nlinarith) he
  have heNat : 0 < e := by exact_mod_cast he'
  have hΛ : 0 < Λ := hform
  have hA : 0 < A := Real.log_pos (by norm_num)
  have hAlo : (2 / 3 : ℝ) ≤ A := by dsimp [A]; linarith [Real.log_two_gt_d9]
  have hAup : A ≤ 7 / 10 := by dsimp [A]; linarith [Real.log_two_lt_d9]
  obtain ⟨hJ, hL, hJlo, hJup, hLlo, hLup, hNup, hLsq⟩ := chosen_dimensions_bounds hH hB
  change 0 < J at hJ
  change 0 < L at hL
  change 5 * H * B ≤ (J : ℝ) at hJlo
  change (J : ℝ) ≤ 5 * H * B + 1 at hJup
  change 11 / 5 * H ≤ (L : ℝ) at hLlo
  change (L : ℝ) ≤ 11 / 5 * H + 1 at hLup
  change ((K * L : ℕ) : ℝ) ≤ 30 * H ^ 2 * B at hNup
  change (L : ℝ) ^ 2 ≤ 6 * H ^ 2 at hLsq
  by_contra hbad
  have hlog : Real.log Λ < -(126 / 5 : ℝ) * H ^ 2 * B := lt_of_not_ge hbad
  have hΛ₁ : Λ < 1 := by
    have hneg : Real.log Λ < 0 := by nlinarith [sq_nonneg H]
    have hh := Real.exp_lt_exp.mpr hneg
    simpa only [Real.exp_log hΛ, Real.exp_zero] using hh
  have hwidth : J + 1 ≤ v := chosen_additive_width hH hB he hΛ₁
  have hnotdiv : ¬2 ∣ b := by
    intro hd
    have hh := Nat.mod_eq_zero_of_dvd hd
    omega
  have hy := prime_power_rectangle_injective (R := L) (S := 1) Nat.prime_two (by omega : 1 < b) hnotdiv
  have hx := additive_rectangle_injective_of_small_width (S := 2 * L) hcop hwidth
  have hcard : (K - 1) * L < (J + 1) * (2 * L) := by
    have hh := Nat.mul_lt_mul_of_pos_right (show K - 1 < 2 * (J + 1) by dsimp [K]; omega) hL
    nlinarith
  have hm := exists_nonzero_integer_rectangle_minor (K := K) (L := L)
    (R₁ := L) (R₂ := J + 1) (S₁ := 1) (S₂ := 2 * L)
    2 b e v (by norm_num) (by omega) (by simp) hcard hy hx
  have hr : L + (J + 1) - 1 = R := by dsimp [R]; omega
  have hs : 1 + 2 * L - 1 = S := by dsimp [S]; omega
  rw [hr, hs] at hm
  obtain ⟨r, s, hinj, hdet⟩ := hm
  have hR : 0 < R := by dsimp [R]; omega
  have hS : 0 < S := by dsimp [S]; omega
  have hK : 0 < K := by dsimp [K]; omega
  have hβ₀ : (0 : ℝ) ≤ (v : ℝ) / e := by positivity
  have hβ : (v : ℝ) / e ≤ 3 / 2 * B := by
    have hh : (v : ℝ) / e * A < B := by
      rw [div_mul_eq_mul_div]
      apply (div_lt_iff₀ he').mpr
      change 0 < (e : ℝ) * B - (v : ℝ) * A at hΛ
      nlinarith
    have hh' := mul_le_mul_of_nonneg_left hAlo hβ₀
    nlinarith
  have hη : 0 < η := by
    have hR' : (1 : ℝ) < R := by exact_mod_cast (show 1 < R by dsimp [R]; omega)
    have hS' : (1 : ℝ) ≤ S := by exact_mod_cast hS
    have hh := mul_nonneg hβ₀ (sub_nonneg.mpr hS')
    dsimp [η]
    linarith
  have hδeq : B - (v : ℝ) / e * A = Λ / e := by dsimp [Λ]; field_simp
  have hδ : 0 ≤ B - (v : ℝ) / e * A := by rw [hδeq]; positivity
  have hpower : Λ ≤ (5 : ℝ) ^ (-(1 / 2 : ℝ) * (K * L : ℕ)) := by
    have hc := chosen_error_exponent_bound hH hB
    change (1 / 2 : ℝ) * ((K * L : ℕ) : ℝ) * Real.log 5 ≤ (126 / 5 : ℝ) * H ^ 2 * B at hc
    rw [Real.rpow_def_of_pos (by norm_num : (0 : ℝ) < 5)]
    have hh := Real.exp_le_exp.mpr (show Real.log Λ ≤ Real.log 5 * (-(1 / 2 : ℝ) * (K * L : ℕ)) by nlinarith)
    rwa [Real.exp_log hΛ] at hh
  have hsmall : (L : ℝ) * S * |B - (v : ℝ) / e * A| / 2 ≤
      (5 : ℝ) ^ (-(1 / 2 : ℝ) * (K * L : ℕ)) := by
    have hLs : (L : ℝ) ^ 2 ≤ (e : ℝ) := by nlinarith [sq_nonneg H]
    have hm := mul_le_mul_of_nonneg_right hLs (div_pos hΛ he').le
    have hid : (L : ℝ) * S * |B - (v : ℝ) / e * A| / 2 = (L : ℝ) ^ 2 * (Λ / e) := by
      rw [abs_of_nonneg hδ, hδeq]
      dsimp [S]
      push_cast
      ring
    rw [hid]
    have heq : (e : ℝ) * (Λ / e) = Λ := by field_simp
    rw [heq] at hm
    exact hm.trans hpower
  have hconstraint := integer_determinant_parameter_constraint hK hL hR hS r s hinj
    2 b e v (by norm_num) (by omega) heNat (μ := 1 / 2) (ρ := 5) (by norm_num) (by norm_num)
    hη hδ hsmall hdet
  have herr := chosen_factorial_error_bound (K * L) (Nat.mul_pos hK hL) hH hB
    (hNup.trans (by nlinarith [mul_nonneg (sq_nonneg H) (show 0 ≤ B by linarith)]))
  have hψ := chosen_parameter_log_bound hH hB hJlo hLlo hLup he' (Nat.cast_nonneg v) hβ hHlog
  have hmargin := chosen_parameter_strict_margin hH hB hJlo hLlo hLup hAup
  have hcoord : (((R : ℝ) - 1) * e + ((S : ℝ) - 1) * v) / (2 * K) =
      (((J : ℝ) + L - 1) * e + (2 * L - 1) * v) / (4 * J) := by
    dsimp [R, S, K]
    push_cast
    ring
  rw [hcoord] at hconstraint
  have hg : (1 / 4 - (K : ℝ) * L / (12 * R * S)) = 1 / 4 - (J : ℝ) / (12 * (J + L)) := by
    have hJ' : (J : ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hJ)
    have hL' : (L : ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hL)
    dsimp [R, S, K]
    push_cast
    field_simp
  rw [hg] at hconstraint
  have hψmul := mul_le_mul_of_nonneg_left hψ (show 0 ≤ (K : ℝ) - 1 by
    have hh : (1 : ℝ) ≤ K := by exact_mod_cast hK
    linarith)
  dsimp [R, S, K] at hconstraint hψmul
  push_cast at hconstraint hψmul
  norm_num at hconstraint
  dsimp [A, B] at hmargin hψmul
  dsimp [B, K] at herr
  push_cast at herr
  nlinarith [hconstraint, hψmul, herr, hmargin]

end LeanA113258.LaurentCore
