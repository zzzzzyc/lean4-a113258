import LaurentDeterminantUpper

/-! Comparison of the independently proved arithmetic and analytic bounds. -/

namespace LeanA113258.LaurentCore

open scoped BigOperators

theorem integer_determinant_log_comparison {K L R S : ℕ}
    (hR : 0 < R) (hS : 0 < S)
    (r : Fin K × Fin L → Fin R) (s : Fin K × Fin L → Fin S)
    (hinj : Function.Injective (fun i => (r i, s i)))
    (a b u v : ℕ) (ha : 0 < a) (hb : 0 < b) (hu : 0 < u)
    {μ ρ : ℝ} (hμ : (1 / 3 : ℝ) ≤ μ) (hρ : 1 < ρ)
    (hη : 0 < (((R : ℝ) - 1) + (v : ℝ) / u * ((S : ℝ) - 1)) / 2)
    (hsmall : (L : ℝ) * S * |Real.log (b : ℝ) - (v : ℝ) / u * Real.log (a : ℝ)| / 2 ≤
      ρ ^ (-μ * (K * L : ℕ)))
    (hdet : (binomialIntegerMatrix (fun i : Fin K × Fin L => i.1.val) (fun i => i.2.val)
      (fun i => (r i).val) (fun i => (s i).val) a b u v).det ≠ 0) :
    let A := Real.log (a : ℝ)
    let B := Real.log (b : ℝ)
    let β := (v : ℝ) / u
    let η := (((R : ℝ) - 1) + β * ((S : ℝ) - 1)) / 2
    let g := 1 / 4 - (K : ℝ) * L / (12 * R * S)
    let G₁ := g * L * R * (K * L) / 2
    let G₂ := g * L * S * (K * L) / 2
    let P := (∏ i : Fin K × Fin L, ((u : ℝ) ^ i.1.val / (i.1.val.factorial : ℝ))) *
      (ρ * η) ^ (∑ i : Fin K × Fin L, i.1.val)
    ((((1 + 2 * μ - μ ^ 2) / 2) * (K * L : ℕ) ^ 2 - (K * L : ℕ)) / 2) * Real.log ρ ≤
      Real.log ((K * L).factorial : ℝ) + Real.log P + (K * L : ℕ) +
        ρ * (A * (G₁ + β * G₂)) + G₁ * A + G₂ * B := by
  classical
  dsimp only
  let A := Real.log (a : ℝ)
  let B := Real.log (b : ℝ)
  let β := (v : ℝ) / u
  let η := (((R : ℝ) - 1) + β * ((S : ℝ) - 1)) / 2
  let g := 1 / 4 - (K : ℝ) * L / (12 * R * S)
  let G₁ := g * L * R * (K * L) / 2
  let G₂ := g * L * S * (K * L) / 2
  let M₁ := ((L : ℝ) - 1) / 2 * (∑ j, ((r j).val : ℝ))
  let M₂ := ((L : ℝ) - 1) / 2 * (∑ j, ((s j).val : ℝ))
  let M := M₁ * A + M₂ * B
  let C := A * (G₁ + β * G₂)
  let P := (∏ i : Fin K × Fin L, ((u : ℝ) ^ i.1.val / (i.1.val.factorial : ℝ))) *
    (ρ * η) ^ (∑ i : Fin K × Fin L, i.1.val)
  let N := K * L
  let d := (((1 + 2 * μ - μ ^ 2) / 2) * (N : ℝ) ^ 2 - N) / 2
  let D := binomialIntegerMatrix (fun i : Fin K × Fin L => i.1.val) (fun i => i.2.val)
    (fun i => (r i).val) (fun i => (s i).val) a b u v
  have hρ₀ : 0 < ρ := lt_trans zero_lt_one hρ
  have hu' : (0 : ℝ) < u := by exact_mod_cast hu
  have hP : 0 < P := by
    apply mul_pos
    · exact Finset.prod_pos (fun i _ => div_pos (pow_pos hu' _) (by positivity))
    · exact pow_pos (mul_pos hρ₀ hη) _
  have hD : (0 : ℝ) < |(D.det : ℝ)| := abs_pos.mpr (by exact_mod_cast hdet)
  have hlow := laurent_integer_determinant_lower_bound hR hS r s hinj a b u v ha hb hdet
  change (M₁ - G₁) * A + (M₂ - G₂) * B ≤ Real.log |(D.det : ℝ)| at hlow
  have hupp := integer_determinant_norm_upper hR hS r s hinj a b u v ha hb hu hμ hρ hsmall
  have heM : ((L : ℝ) - 1) / 2 * ((∑ j, ((r j).val : ℝ)) * A + (∑ j, ((s j).val : ℝ)) * B) = M := by
    dsimp [M, M₁, M₂]
    ring
  change |(D.det : ℝ)| ≤ Real.exp (((L : ℝ) - 1) / 2 *
    ((∑ j, ((r j).val : ℝ)) * A + (∑ j, ((s j).val : ℝ)) * B)) *
      (N.factorial * (P * Real.exp (ρ * C))) * ρ ^ (-d) * Real.exp (N : ℝ) at hupp
  rw [heM] at hupp
  have hlog := Real.log_le_log hD hupp
  have he : Real.log (Real.exp M * (N.factorial * (P * Real.exp (ρ * C))) *
      ρ ^ (-d) * Real.exp (N : ℝ)) =
      M + Real.log (N.factorial : ℝ) + Real.log P + ρ * C - d * Real.log ρ + N := by
    rw [Real.log_mul (by positivity) (by positivity),
      Real.log_mul (by positivity) (by positivity),
      Real.log_mul (by positivity) (by positivity),
      Real.log_mul (by positivity) (by positivity),
      Real.log_mul (by positivity) (by positivity),
      Real.log_exp, Real.log_exp, Real.log_exp, Real.log_rpow hρ₀]
    ring
  rw [he] at hlog
  change d * Real.log ρ ≤ Real.log (N.factorial : ℝ) + Real.log P + N + ρ * C + G₁ * A + G₂ * B
  dsimp only [M] at hlog
  linarith

end LeanA113258.LaurentCore
