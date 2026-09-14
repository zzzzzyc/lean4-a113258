import LaurentExponential
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Topology.Instances.Matrix

/-! Analytic bounds for Laurent's exponential interpolation determinant. -/

namespace LeanA113258.LaurentCore

open scoped BigOperators Topology
open Filter Set Metric

theorem norm_det_le_factorial_mul {ι : Type*} [Fintype ι] [DecidableEq ι]
    (A : Matrix ι ι ℂ) {M : ℝ}
    (hM : ∀ σ : Equiv.Perm ι, (∏ i, ‖A i (σ i)‖) ≤ M) :
    ‖A.det‖ ≤ (Fintype.card ι).factorial * M := by
  rw [← Matrix.det_transpose, Matrix.det_apply]
  calc
    _ ≤ ∑ σ : Equiv.Perm ι, ‖Equiv.Perm.sign σ • ∏ i, A.transpose (σ i) i‖ :=
      norm_sum_le _ _
    _ = ∑ σ : Equiv.Perm ι, ∏ i, ‖A i (σ i)‖ := by
      simp only [norm_units_zsmul, norm_prod, Matrix.transpose_apply]
    _ ≤ ∑ _ : Equiv.Perm ι, M := Finset.sum_le_sum (fun σ _ => hM σ)
    _ = _ := by simp [Fintype.card_perm]

/-- Laurent's Lemma 4 with an explicit bound for the unperturbed products. -/
theorem tagged_exponential_term_bound {ι : Type*} [Fintype ι] [DecidableEq ι]
    {L : ℕ} (k : ι → ℕ) (c : ι → Fin L) (a α β z s : ι → ℂ)
    {ρ U δ : ℝ} (hρ : 1 < ρ) (hδ : 0 ≤ δ)
    (hsmall : ∀ i j, ‖β i * s j‖ ≤ δ)
    (hprod : ∀ t ∈ ball (0 : ℂ) ρ, ∀ σ : Equiv.Perm ι,
      (∏ i, ‖a i * (t * z (σ i)) ^ k i *
        Complex.exp (α i * (t * z (σ i)))‖) ≤ U) :
    ‖(Matrix.of fun i j =>
      (a i * z j ^ k i * Complex.exp (α i * z j)) *
        ((β i * s j) ^ (c i).val / ((c i).val.factorial : ℂ))).det‖ ≤
      ((Fintype.card ι).factorial * U *
        (δ ^ (∑ i, (c i).val) / ∏ i, ((c i).val.factorial : ℝ))) /
          ρ ^ (∑ v, (Fintype.card {i // c i = v}).choose 2) := by
  classical
  let a' : ι → ℂ := fun i => a i * β i ^ (c i).val / ((c i).val.factorial : ℂ)
  let F : ℂ → Matrix ι ι ℂ := fun t => Matrix.of fun i j =>
    a' i * (t * z j) ^ k i * Complex.exp (α i * (t * z j)) * s j ^ (c i).val
  have hentry (t : ℂ) (i j : ι) : F t i j =
      (a i * (t * z j) ^ k i * Complex.exp (α i * (t * z j))) *
        ((β i * s j) ^ (c i).val / ((c i).val.factorial : ℂ)) := by
    dsimp [F, a']
    rw [mul_pow]
    ring
  have hbound (t : ℂ) (ht : t ∈ ball 0 ρ) : ‖(F t).det‖ ≤
      (Fintype.card ι).factorial * U *
        (δ ^ (∑ i, (c i).val) / ∏ i, ((c i).val.factorial : ℝ)) := by
    have hh := norm_det_le_factorial_mul (F t) (M := U *
      (δ ^ (∑ i, (c i).val) / ∏ i, ((c i).val.factorial : ℝ))) (by
      intro σ
      calc
        _ ≤ ∏ i, (‖a i * (t * z (σ i)) ^ k i *
            Complex.exp (α i * (t * z (σ i)))‖ *
              (δ ^ (c i).val / ((c i).val.factorial : ℝ))) := by
          apply Finset.prod_le_prod (fun i _ => norm_nonneg _)
          intro i _
          rw [hentry, norm_mul, norm_div, norm_pow, Complex.norm_natCast]
          exact mul_le_mul_of_nonneg_left
            (div_le_div_of_nonneg_right (pow_le_pow_left₀ (norm_nonneg _) (hsmall i (σ i)) _)
              (Nat.cast_nonneg _)) (norm_nonneg _)
        _ = (∏ i, ‖a i * (t * z (σ i)) ^ k i *
            Complex.exp (α i * (t * z (σ i)))‖) *
              (δ ^ (∑ i, (c i).val) / ∏ i, ((c i).val.factorial : ℝ)) := by
          rw [Finset.prod_mul_distrib, Finset.prod_div_distrib,
            Finset.prod_pow_eq_pow_sum]
        _ ≤ _ := mul_le_mul_of_nonneg_right (hprod t ht σ)
          (div_nonneg (pow_nonneg hδ _) (Finset.prod_nonneg fun _ _ => Nat.cast_nonneg _)))
    simpa only [mul_assoc] using hh
  have hh := tagged_exponential_schwarz k c a' α z s hρ hbound
  have hmat : (Matrix.of fun i j =>
      a' i * z j ^ k i * Complex.exp (α i * z j) * s j ^ (c i).val) =
      (Matrix.of fun i j => (a i * z j ^ k i * Complex.exp (α i * z j)) *
        ((β i * s j) ^ (c i).val / ((c i).val.factorial : ℂ))) := by
    ext i j
    simpa only [F, Matrix.of_apply, one_mul] using hentry 1 i j
  rwa [hmat] at hh

theorem fiber_multiplicity_weight_bound {ι : Type*} [Fintype ι]
    {L : ℕ} (c : ι → Fin L) {μ : ℝ} (hμ : (1 / 3 : ℝ) ≤ μ) :
    (((1 + 2 * μ - μ ^ 2) / 2) * (Fintype.card ι : ℝ) ^ 2 -
      (Fintype.card ι : ℝ)) / 2 ≤
      ((∑ v, (Fintype.card {i // c i = v}).choose 2 : ℕ) : ℝ) +
        μ * (Fintype.card ι : ℝ) * ((∑ i, (c i).val : ℕ) : ℝ) := by
  classical
  let ν : Fin L → ℕ := fun v => Fintype.card {i // c i = v}
  have htotal : ∑ v, ν v = Fintype.card ι := by
    simpa [ν] using Fintype.sum_fiberwise c (fun _ => (1 : ℕ))
  have hw : ∑ v, (v.val : ℝ) * (ν v : ℝ) = ∑ i, ((c i).val : ℝ) := by
    simpa [ν, mul_comm] using Fintype.sum_fiberwise' c (fun v => (v.val : ℝ))
  have hh := laurent_lemma_three ν htotal hμ
  rw [hw] at hh
  simpa only [ν, Nat.cast_sum] using hh

/-- A direct bound for every exponent tuple. Zero multiplicities are allowed,
so no sorting of the distinct exponents is needed. -/
theorem interpolation_weight_bound {ι : Type*} [Fintype ι]
    {L : ℕ} (c : ι → Fin L) {μ ρ δ : ℝ}
    (hμ : (1 / 3 : ℝ) ≤ μ) (hρ : 1 < ρ) (hδ : 0 ≤ δ)
    (hsmall : δ ≤ ρ ^ (-μ * (Fintype.card ι : ℝ))) :
    δ ^ (∑ i, (c i).val) / ρ ^ (∑ v, (Fintype.card {i // c i = v}).choose 2) ≤
      ρ ^ (-((((1 + 2 * μ - μ ^ 2) / 2) * (Fintype.card ι : ℝ) ^ 2 -
        (Fintype.card ι : ℝ)) / 2)) := by
  classical
  let S : ℕ := ∑ i, (c i).val
  let m : ℕ := ∑ v, (Fintype.card {i // c i = v}).choose 2
  have hp : 0 < ρ := lt_trans zero_lt_one hρ
  have hh := fiber_multiplicity_weight_bound c hμ
  change _ ≤ (m : ℝ) + μ * (Fintype.card ι : ℝ) * (S : ℝ) at hh
  calc
    δ ^ S / ρ ^ m ≤ (ρ ^ (-μ * (Fintype.card ι : ℝ))) ^ S / ρ ^ m :=
      div_le_div_of_nonneg_right (pow_le_pow_left₀ hδ hsmall S) (pow_nonneg hp.le m)
    _ = ρ ^ ((-μ * (Fintype.card ι : ℝ)) * (S : ℝ) - (m : ℝ)) := by
      have hpow : (ρ ^ (-μ * (Fintype.card ι : ℝ))) ^ S =
          ρ ^ ((-μ * (Fintype.card ι : ℝ)) * (S : ℝ)) := by
        simpa only [Real.rpow_natCast] using
          (Real.rpow_mul hp.le (-μ * (Fintype.card ι : ℝ)) (S : ℝ)).symm
      rw [hpow, Real.rpow_sub hp, Real.rpow_natCast]
    _ ≤ _ := Real.rpow_le_rpow_of_exponent_le hρ.le (by linarith)

theorem sum_inverse_factorials_le_exp_card {ι : Type*} [Fintype ι] [DecidableEq ι] (T : ℕ) :
    (∑ c : ι → Fin T, (∏ i, ((c i).val.factorial : ℝ))⁻¹) ≤
      Real.exp (Fintype.card ι) := by
  classical
  have heq : (∑ c : ι → Fin T, (∏ i, ((c i).val.factorial : ℝ))⁻¹) =
      (∑ h : Fin T, (h.val.factorial : ℝ)⁻¹) ^ Fintype.card ι := by
    simp only [← Finset.prod_inv_distrib]
    simpa only [Finset.prod_const, Finset.card_univ] using
      (Fintype.prod_sum (fun (_i : ι) (h : Fin T) => (h.val.factorial : ℝ)⁻¹)).symm
  rw [heq]
  have hsum : (∑ h : Fin T, (h.val.factorial : ℝ)⁻¹) ≤ Real.exp 1 := by
    have heq' : (∑ h : Fin T, (h.val.factorial : ℝ)⁻¹) =
        ∑ h ∈ Finset.range T, (h.factorial : ℝ)⁻¹ :=
      Fin.sum_univ_eq_sum_range (fun h => (h.factorial : ℝ)⁻¹) T
    rw [heq']
    simpa only [one_pow, one_div] using Real.sum_le_exp_of_nonneg (by norm_num : (0 : ℝ) ≤ 1) T
  have hh := pow_le_pow_left₀ (Finset.sum_nonneg fun _ _ => by positivity) hsum (Fintype.card ι)
  simpa only [Real.exp_one_pow] using hh

theorem exponential_interpolation_truncation_bound {ι : Type*}
    [Fintype ι] [DecidableEq ι] (T : ℕ)
    (k : ι → ℕ) (a α β z s : ι → ℂ) {μ ρ U δ : ℝ}
    (hμ : (1 / 3 : ℝ) ≤ μ) (hρ : 1 < ρ) (hU : 0 ≤ U) (hδ : 0 ≤ δ)
    (hweight : δ ≤ ρ ^ (-μ * (Fintype.card ι : ℝ)))
    (hsmall : ∀ i j, ‖β i * s j‖ ≤ δ)
    (hprod : ∀ t ∈ ball (0 : ℂ) ρ, ∀ σ : Equiv.Perm ι,
      (∏ i, ‖a i * (t * z (σ i)) ^ k i *
        Complex.exp (α i * (t * z (σ i)))‖) ≤ U) :
    ‖(Matrix.of fun i j =>
      (a i * z j ^ k i * Complex.exp (α i * z j)) *
        (∑ h : Fin T, (β i * s j) ^ h.val / (h.val.factorial : ℂ))).det‖ ≤
      ((Fintype.card ι).factorial * U) *
        ρ ^ (-((((1 + 2 * μ - μ ^ 2) / 2) * (Fintype.card ι : ℝ) ^ 2 -
          (Fintype.card ι : ℝ)) / 2)) * Real.exp (Fintype.card ι) := by
  classical
  let C : ℝ := (Fintype.card ι).factorial * U
  let W : ℝ := ρ ^ (-((((1 + 2 * μ - μ ^ 2) / 2) * (Fintype.card ι : ℝ) ^ 2 -
    (Fintype.card ι : ℝ)) / 2))
  have hC : 0 ≤ C := mul_nonneg (Nat.cast_nonneg _) hU
  have hW : 0 ≤ W := Real.rpow_nonneg (le_of_lt (lt_trans zero_lt_one hρ)) _
  simp_rw [Finset.mul_sum]
  rw [determinant_sum_rows]
  have hterm (c : ι → Fin T) :
      ‖(Matrix.of fun i j =>
        (a i * z j ^ k i * Complex.exp (α i * z j)) *
          ((β i * s j) ^ (c i).val / ((c i).val.factorial : ℂ))).det‖ ≤
      (C * W) * (∏ i, ((c i).val.factorial : ℝ))⁻¹ := by
    have hh := tagged_exponential_term_bound k c a α β z s hρ hδ hsmall hprod
    have hw := interpolation_weight_bound c hμ hρ hδ hweight
    let Q : ℝ := ∏ i, ((c i).val.factorial : ℝ)
    have hQ : 0 ≤ Q⁻¹ := by dsimp [Q]; positivity
    calc
      _ ≤ (C * (δ ^ (∑ i, (c i).val) /
          ρ ^ (∑ v, (Fintype.card {i // c i = v}).choose 2))) * Q⁻¹ := by
        convert hh using 1
        dsimp [C, Q]
        ring
      _ ≤ _ := mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hw hC) hQ
  calc
    _ ≤ ∑ c : ι → Fin T, ‖(Matrix.of fun i j =>
        (a i * z j ^ k i * Complex.exp (α i * z j)) *
          ((β i * s j) ^ (c i).val / ((c i).val.factorial : ℂ))).det‖ := norm_sum_le _ _
    _ ≤ ∑ c : ι → Fin T, (C * W) * (∏ i, ((c i).val.factorial : ℝ))⁻¹ :=
      Finset.sum_le_sum (fun c _ => hterm c)
    _ = (C * W) * ∑ c : ι → Fin T, (∏ i, ((c i).val.factorial : ℝ))⁻¹ :=
      (Finset.mul_sum _ _ _).symm
    _ ≤ _ := mul_le_mul_of_nonneg_left (sum_inverse_factorials_le_exp_card T) (mul_nonneg hC hW)

theorem tendsto_exponential_fin_sum (x : ℂ) :
    Tendsto (fun T : ℕ => ∑ h : Fin T, x ^ h.val / (h.val.factorial : ℂ))
      atTop (𝓝 (Complex.exp x)) := by
  have hh := (Complex.exp' x).tendsto_limit
  have heq (T : ℕ) : (∑ h : Fin T, x ^ h.val / (h.val.factorial : ℂ)) =
      ∑ h ∈ Finset.range T, x ^ h / (h.factorial : ℂ) :=
    Fin.sum_univ_eq_sum_range (fun h => x ^ h / (h.factorial : ℂ)) T
  simp only [heq]
  simpa only [Complex.exp', Complex.exp_def] using hh

/-- A complete analytic interpolation estimate. The factorial-series sum is
bounded directly by `exp N`, using the zero-allowing combinatorial lemma.
The bound `U` for the unperturbed products is explicit input. -/
theorem exponential_interpolation_bound {ι : Type*}
    [Fintype ι] [DecidableEq ι]
    (k : ι → ℕ) (a α β z s : ι → ℂ) {μ ρ U δ : ℝ}
    (hμ : (1 / 3 : ℝ) ≤ μ) (hρ : 1 < ρ) (hU : 0 ≤ U) (hδ : 0 ≤ δ)
    (hweight : δ ≤ ρ ^ (-μ * (Fintype.card ι : ℝ)))
    (hsmall : ∀ i j, ‖β i * s j‖ ≤ δ)
    (hprod : ∀ t ∈ ball (0 : ℂ) ρ, ∀ σ : Equiv.Perm ι,
      (∏ i, ‖a i * (t * z (σ i)) ^ k i *
        Complex.exp (α i * (t * z (σ i)))‖) ≤ U) :
    ‖(Matrix.of fun i j =>
      (a i * z j ^ k i * Complex.exp (α i * z j)) *
        Complex.exp (β i * s j)).det‖ ≤
      ((Fintype.card ι).factorial * U) *
        ρ ^ (-((((1 + 2 * μ - μ ^ 2) / 2) * (Fintype.card ι : ℝ) ^ 2 -
          (Fintype.card ι : ℝ)) / 2)) * Real.exp (Fintype.card ι) := by
  classical
  let A : Matrix ι ι ℂ := Matrix.of fun i j =>
    (a i * z j ^ k i * Complex.exp (α i * z j)) * Complex.exp (β i * s j)
  let B : ℕ → Matrix ι ι ℂ := fun T => Matrix.of fun i j =>
    (a i * z j ^ k i * Complex.exp (α i * z j)) *
      (∑ h : Fin T, (β i * s j) ^ h.val / (h.val.factorial : ℂ))
  have hmatrix : Tendsto B atTop (𝓝 A) := by
    apply tendsto_pi_nhds.mpr
    intro i
    apply tendsto_pi_nhds.mpr
    intro j
    exact tendsto_const_nhds.mul (tendsto_exponential_fin_sum (β i * s j))
  have hdet := ((continuous_id.matrix_det :
    Continuous (fun M : Matrix ι ι ℂ => M.det)).tendsto A).comp hmatrix
  exact le_of_tendsto hdet.norm (Eventually.of_forall fun T =>
    exponential_interpolation_truncation_bound T k a α β z s hμ hρ hU hδ hweight hsmall hprod)

end LeanA113258.LaurentCore
