import LaurentRealCentering

/-! The analytic upper bound for the actual integer interpolation determinant. -/

namespace LeanA113258.LaurentCore

open scoped BigOperators
open Metric

theorem centered_index_abs_le (L : ℕ) (l : Fin L) :
    |(l.val : ℝ) - ((L : ℝ) - 1) / 2| ≤ (L : ℝ) / 2 := by
  have hl : (l.val : ℝ) + 1 ≤ L := by exact_mod_cast l.isLt
  have h₀ : (0 : ℝ) ≤ l.val := Nat.cast_nonneg _
  exact abs_le.mpr ⟨by linarith, by linarith⟩

theorem integer_determinant_norm_upper {K L R S : ℕ}
    (hR : 0 < R) (hS : 0 < S)
    (r : Fin K × Fin L → Fin R) (s : Fin K × Fin L → Fin S)
    (hinj : Function.Injective (fun i => (r i, s i)))
    (a b u v : ℕ) (ha : 0 < a) (hb : 0 < b) (hu : 0 < u)
    {μ ρ : ℝ} (hμ : (1 / 3 : ℝ) ≤ μ) (hρ : 1 < ρ)
    (hsmall : (L : ℝ) * S * |Real.log (b : ℝ) - (v : ℝ) / u * Real.log (a : ℝ)| / 2 ≤
      ρ ^ (-μ * (K * L : ℕ))) :
    let A := Real.log (a : ℝ)
    let B := Real.log (b : ℝ)
    let β := (v : ℝ) / u
    let η := (((R : ℝ) - 1) + β * ((S : ℝ) - 1)) / 2
    let g := 1 / 4 - (K : ℝ) * L / (12 * R * S)
    let G₁ := g * L * R * (K * L) / 2
    let G₂ := g * L * S * (K * L) / 2
    let M := ((L : ℝ) - 1) / 2 * ((∑ j, ((r j).val : ℝ)) * A + (∑ j, ((s j).val : ℝ)) * B)
    let P := (∏ i : Fin K × Fin L, ((u : ℝ) ^ i.1.val / (i.1.val.factorial : ℝ))) *
      (ρ * η) ^ (∑ i : Fin K × Fin L, i.1.val)
    |((binomialIntegerMatrix (fun i : Fin K × Fin L => i.1.val) (fun i => i.2.val)
      (fun i => (r i).val) (fun i => (s i).val) a b u v).det : ℝ)| ≤
      Real.exp M * ((K * L).factorial * (P * Real.exp (ρ * (A * (G₁ + β * G₂))))) *
        ρ ^ (-((((1 + 2 * μ - μ ^ 2) / 2) * (K * L : ℕ) ^ 2 - (K * L : ℕ)) / 2)) *
          Real.exp (K * L : ℕ) := by
  classical
  dsimp only
  let A := Real.log (a : ℝ)
  let B := Real.log (b : ℝ)
  let β := (v : ℝ) / u
  let η := (((R : ℝ) - 1) + β * ((S : ℝ) - 1)) / 2
  let c := ((L : ℝ) - 1) / 2
  let δ := B - β * A
  let z : Fin K × Fin L → ℝ := fun j => ((r j).val : ℝ) + β * (s j).val - η
  let α : Fin K × Fin L → ℝ := fun i => ((i.2.val : ℝ) - c) * A
  let a₀ : Fin K × Fin L → ℂ := fun i => (u : ℂ) ^ i.1.val / (i.1.val.factorial : ℂ)
  let C := A * ((1 / 4 - (K : ℝ) * L / (12 * R * S)) * L * R * (K * L) / 2 +
    β * ((1 / 4 - (K : ℝ) * L / (12 * R * S)) * L * S * (K * L) / 2))
  let P := (∏ i : Fin K × Fin L, ((u : ℝ) ^ i.1.val / (i.1.val.factorial : ℝ))) *
    (ρ * η) ^ (∑ i : Fin K × Fin L, i.1.val)
  let U := P * Real.exp (ρ * C)
  let ε := (L : ℝ) * S * |δ| / 2
  have hρ₀ : 0 ≤ ρ := (lt_trans zero_lt_one hρ).le
  have hβ : 0 ≤ β := by dsimp [β]; positivity
  have hA : 0 ≤ A := Real.log_nonneg (by exact_mod_cast ha)
  have hη : 0 ≤ η := by
    have hR' : (1 : ℝ) ≤ R := by exact_mod_cast hR
    have hS' : (1 : ℝ) ≤ S := by exact_mod_cast hS
    exact div_nonneg (add_nonneg (sub_nonneg.mpr hR') (mul_nonneg hβ (sub_nonneg.mpr hS'))) (by norm_num)
  have hnorm (i : Fin K × Fin L) : ‖a₀ i‖ = (u : ℝ) ^ i.1.val / (i.1.val.factorial : ℝ) := by
    simp only [a₀, norm_div, norm_pow, Complex.norm_natCast]
  have hP : 0 ≤ P := by dsimp [P]; positivity
  have hU : 0 ≤ U := mul_nonneg hP (Real.exp_pos _).le
  have hε : 0 ≤ ε := by dsimp [ε]; positivity
  have hz (j) : |z j| ≤ η := centered_grid_coordinate_bound (r j) (s j) hβ
  have hprod (t : ℂ) (ht : t ∈ ball (0 : ℂ) ρ) (σ : Equiv.Perm (Fin K × Fin L)) :
      (∏ i, ‖a₀ i * (t * (z (σ i) : ℂ)) ^ i.1.val *
        Complex.exp ((α i : ℂ) * (t * (z (σ i) : ℂ)))‖) ≤ U := by
    have ht' : ‖t‖ ≤ ρ := (by simpa only [mem_ball, dist_zero_right] using ht : ‖t‖ < ρ).le
    have hcorr := centered_grid_correlation_bound hR hS r s hinj σ (η := η) hA hβ
    have hh := real_exponential_product_bound (fun i : Fin K × Fin L => i.1.val) a₀ α z σ
      hρ₀ hη hz hcorr t ht'
    simpa only [hnorm] using hh
  have hpert (i j : Fin K × Fin L) :
      ‖((((i.2.val : ℝ) - c) * δ : ℝ) : ℂ) * ((s j).val : ℂ)‖ ≤ ε := by
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, Complex.norm_natCast, abs_mul]
    have hl := centered_index_abs_le L i.2
    have hs : ((s j).val : ℝ) ≤ S := by exact_mod_cast (s j).isLt.le
    have hh := mul_le_mul (mul_le_mul_of_nonneg_right hl (abs_nonneg δ)) hs
      (Nat.cast_nonneg _) (mul_nonneg (by positivity) (abs_nonneg δ))
    dsimp [ε]
    nlinarith [hh]
  have hw : ε ≤ ρ ^ (-μ * (Fintype.card (Fin K × Fin L) : ℝ)) := by
    simpa only [Fintype.card_prod, Fintype.card_fin] using hsmall
  have hh := exponential_interpolation_bound (fun i : Fin K × Fin L => i.1.val)
    a₀ (fun i => (α i : ℂ)) (fun i => ((((i.2.val : ℝ) - c) * δ : ℝ) : ℂ))
    (fun j => (z j : ℂ)) (fun j => ((s j).val : ℂ)) hμ hρ hU hε hw hpert hprod
  have hc := integer_determinant_real_centering (fun i => (r i).val) (fun i => (s i).val)
    a b u v ha hb hu η
  rw [hc]
  have hbnd := mul_le_mul_of_nonneg_left hh (Real.exp_pos
    (c * ((∑ j, ((r j).val : ℝ)) * A + (∑ j, ((s j).val : ℝ)) * B))).le
  simpa only [Fintype.card_prod, Fintype.card_fin, a₀, α, z, c, δ, A, B, β, η, U, P, C,
    mul_assoc] using hbnd

end LeanA113258.LaurentCore
