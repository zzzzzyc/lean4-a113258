import LaurentDeterminantComparison
import LaurentFactorials

/-! An explicit parameter constraint, with the factorial normalizations
estimated by elementary logarithmic inequalities. -/

namespace LeanA113258.LaurentCore

open scoped BigOperators

theorem integer_determinant_parameter_constraint {K L R S : ℕ}
    (hK : 0 < K) (hL : 0 < L) (hR : 0 < R) (hS : 0 < S)
    (r : Fin K × Fin L → Fin R) (s : Fin K × Fin L → Fin S)
    (hinj : Function.Injective (fun i => (r i, s i)))
    (a b u v : ℕ) (ha : 0 < a) (hb : 0 < b) (hu : 0 < u)
    {μ ρ : ℝ} (hμ : (1 / 3 : ℝ) ≤ μ) (hρ : 1 < ρ)
    (hη : 0 < (((R : ℝ) - 1) + (v : ℝ) / u * ((S : ℝ) - 1)) / 2)
    (hδ : 0 ≤ Real.log (b : ℝ) - (v : ℝ) / u * Real.log (a : ℝ))
    (hsmall : (L : ℝ) * S * |Real.log (b : ℝ) - (v : ℝ) / u * Real.log (a : ℝ)| / 2 ≤
      ρ ^ (-μ * (K * L : ℕ)))
    (hdet : (binomialIntegerMatrix (fun i : Fin K × Fin L => i.1.val) (fun i => i.2.val)
      (fun i => (r i).val) (fun i => (s i).val) a b u v).det ≠ 0) :
    (K : ℝ) * (((1 + 2 * μ - μ ^ 2) / 2) * L - 1) * Real.log ρ ≤
      2 * (Real.log ((K * L).factorial : ℝ) + (K * L : ℕ)) / (K * L : ℕ) +
        ((K : ℝ) - 1) * (Real.log ((((R : ℝ) - 1) * u + ((S : ℝ) - 1) * v) / (2 * K)) + 3 / 2) +
          (1 / 4 - (K : ℝ) * L / (12 * R * S)) * L * (ρ + 1) *
            (R * Real.log (a : ℝ) + S * Real.log (b : ℝ)) := by
  classical
  let A := Real.log (a : ℝ)
  let B := Real.log (b : ℝ)
  let β := (v : ℝ) / u
  let η := (((R : ℝ) - 1) + β * ((S : ℝ) - 1)) / 2
  let g := 1 / 4 - (K : ℝ) * L / (12 * R * S)
  let G₁ := g * L * R * (K * L) / 2
  let G₂ := g * L * S * (K * L) / 2
  let N := (K : ℝ) * L
  let d := (((1 + 2 * μ - μ ^ 2) / 2) * N ^ 2 - N) / 2
  let F := Real.log ((K * L).factorial : ℝ)
  let P := (∏ i : Fin K × Fin L, ((u : ℝ) ^ i.1.val / (i.1.val.factorial : ℝ))) *
    (ρ * η) ^ (∑ i : Fin K × Fin L, i.1.val)
  let ψ := Real.log ((((R : ℝ) - 1) * u + ((S : ℝ) - 1) * v) / (2 * K)) + 3 / 2
  have hK' : (0 : ℝ) < K := by exact_mod_cast hK
  have hL' : (0 : ℝ) < L := by exact_mod_cast hL
  have hR' : (0 : ℝ) < R := by exact_mod_cast hR
  have hS' : (0 : ℝ) < S := by exact_mod_cast hS
  have hu' : (0 : ℝ) < u := by exact_mod_cast hu
  have hρ' : 0 < ρ := lt_trans zero_lt_one hρ
  have hN : 0 < N := mul_pos hK' hL'
  have hcard : (K : ℝ) * L ≤ (R : ℝ) * S := by
    have hh := Fintype.card_le_of_injective _ hinj
    simp only [Fintype.card_prod, Fintype.card_fin] at hh
    exact_mod_cast hh
  have hg : 0 ≤ g := by
    have he : g * (12 * R * S) = 3 * (R : ℝ) * S - K * L := by dsimp [g]; field_simp; ring
    have hd : (0 : ℝ) < 12 * R * S := by positivity
    have hm : 0 ≤ g * (12 * R * S) := by nlinarith
    exact nonneg_of_mul_nonneg_left hm hd
  have hG₂ : 0 ≤ G₂ := by dsimp [G₂]; positivity
  have hC : A * (G₁ + β * G₂) ≤ G₁ * A + G₂ * B := by
    have hh := mul_nonneg hδ hG₂
    change 0 ≤ (B - β * A) * G₂ at hh
    nlinarith
  have hp := log_polynomial_factor_bound K L hK hu' hρ' hη
  have he : (u : ℝ) * η / K = (((R : ℝ) - 1) * u + ((S : ℝ) - 1) * v) / (2 * K) := by
    dsimp [η, β]
    field_simp
  rw [he] at hp
  simp only [add_assoc] at hp
  change Real.log P ≤ (K : ℝ) * L * (K - 1) / 2 * (Real.log ρ + ψ) at hp
  have hh := integer_determinant_log_comparison hR hS r s hinj a b u v ha hb hu hμ hρ hη hsmall hdet
  dsimp only at hh
  push_cast at hh
  change d * Real.log ρ ≤ F + Real.log P + N + ρ * (A * (G₁ + β * G₂)) + G₁ * A + G₂ * B at hh
  have hc := mul_le_mul_of_nonneg_left hC hρ'.le
  have hbnd : d * Real.log ρ ≤ F + N * (K - 1) / 2 * (Real.log ρ + ψ) + N +
      (ρ + 1) * (G₁ * A + G₂ * B) := by dsimp [N] at *; nlinarith [hp, hc]
  push_cast
  change (K : ℝ) * (((1 + 2 * μ - μ ^ 2) / 2) * L - 1) * Real.log ρ ≤
    2 * (F + N) / N + (K - 1) * ψ + g * L * (ρ + 1) * (R * A + S * B)
  apply (mul_le_mul_iff_right₀ (div_pos hN (by norm_num : (0 : ℝ) < 2))).mp
  have heq : N / 2 * (2 * (F + N) / N + (K - 1) * ψ + g * L * (ρ + 1) * (R * A + S * B)) =
      F + N + N * (K - 1) / 2 * ψ + (ρ + 1) * (G₁ * A + G₂ * B) := by
    dsimp [G₁, G₂, N]
    field_simp
  rw [heq]
  have heq' : N / 2 * ((K : ℝ) * (((1 + 2 * μ - μ ^ 2) / 2) * L - 1) * Real.log ρ) =
      d * Real.log ρ - N * (K - 1) / 2 * Real.log ρ := by dsimp [d, N]; ring
  rw [heq']
  nlinarith [hbnd]

end LeanA113258.LaurentCore
