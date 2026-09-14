import LaurentPolynomial
import Mathlib.Analysis.Complex.Schwarz
import Mathlib.Analysis.Calculus.Deriv.Polynomial

/-!
Connect polynomial divisibility to the precise Schwarz factor `ρ ^ (-d)`.
The boundary estimate is explicit input. Neither the exponential-series limit
nor Laurent's parameter estimates are claimed in this file.
-/

namespace LeanA113258.LaurentCore

open scoped Topology
open Filter Set Metric Polynomial Asymptotics

theorem schwarz_of_power_factor (f g : ℂ → ℂ) (d : ℕ) {ρ M : ℝ}
    (hρ : 1 < ρ) (hf : DifferentiableOn ℂ f (ball 0 ρ))
    (hg : ContinuousAt g 0) (hfactor : ∀ z, f z = z ^ d * g z)
    (hbound : ∀ z ∈ ball 0 ρ, ‖f z‖ ≤ M) : ‖f 1‖ ≤ M / ρ ^ d := by
  have h1 : (1 : ℂ) ∈ ball 0 ρ := by simpa using hρ
  cases d with
  | zero => simpa using hbound 1 h1
  | succ n =>
    have hzero : f 0 = 0 := by simpa using hfactor 0
    have hgO : g =O[𝓝 (0 : ℂ)] (fun _ => (1 : ℂ)) := hg.tendsto.isBigO_one ℂ
    have hlo : (fun z : ℂ => f z - f 0) =o[𝓝 0] (fun z => ‖z - 0‖ ^ n) := by
      have hh := (Asymptotics.isLittleO_pow_pow (𝕜 := ℂ) (Nat.lt_succ_self n)).mul_isBigO hgO
      simpa only [hzero, sub_zero, hfactor, mul_one, norm_pow] using hh.norm_right
    have hm : MapsTo f (ball 0 ρ) (closedBall (f 0) M) := by
      intro z hz
      simpa only [mem_closedBall, hzero, dist_zero_right] using hbound z hz
    have h := Complex.dist_le_mul_div_pow_of_mapsTo_ball_of_isLittleO hf hm hlo h1
    simpa only [hzero, dist_zero_right, norm_one, one_div, inv_pow,
      div_eq_mul_inv, one_mul] using h

theorem polynomial_schwarz_of_X_pow_dvd (p : ℂ[X]) (d : ℕ) {ρ M : ℝ}
    (hρ : 1 < ρ) (hdiv : X ^ d ∣ p)
    (hbound : ∀ z ∈ ball 0 ρ, ‖p.eval z‖ ≤ M) : ‖p.eval 1‖ ≤ M / ρ ^ d := by
  obtain ⟨q, hq⟩ := hdiv
  apply schwarz_of_power_factor (fun z => p.eval z) (fun z => q.eval z) d hρ
    p.differentiableOn q.differentiable.continuous.continuousAt ?_ hbound
  intro z
  simp [hq]

/-- The finite interpolation determinant now has a proved analytic upper bound,
conditional only on a boundary bound and the explicit numerical inequalities. -/
theorem interpolationPolynomial_schwarz {ι : Type*} [Fintype ι] [DecidableEq ι]
    (H L w d : ℕ) (a : ι → (Fin H × Fin L) → ℂ) (z s : ι → ℂ)
    {μ ρ M : ℝ} (hμ : (1 / 3 : ℝ) ≤ μ)
    (hw : μ * (Fintype.card ι : ℝ) ≤ (w : ℝ))
    (hd : (d : ℝ) ≤
      (((1 + 2 * μ - μ ^ 2) / 2) * (Fintype.card ι : ℝ) ^ 2 -
        (Fintype.card ι : ℝ)) / 2)
    (hρ : 1 < ρ)
    (hbound : ∀ t ∈ ball 0 ρ, ‖(interpolationPolynomial H L w a z s).eval t‖ ≤ M) :
    ‖(interpolationPolynomial H L w a z s).eval 1‖ ≤ M / ρ ^ d :=
  polynomial_schwarz_of_X_pow_dvd _ d hρ
    (X_pow_dvd_interpolationPolynomial H L w d a z s hμ hw hd) hbound

#print axioms schwarz_of_power_factor
#print axioms interpolationPolynomial_schwarz

end LeanA113258.LaurentCore
