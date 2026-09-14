import LaurentTaggedPolynomial
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Analysis.SpecialFunctions.ExpDeriv

/-! Transfer the exact polynomial multiplicity to exponential functions using
Taylor remainders. All orders are proved, rather than supplied as hypotheses. -/

namespace LeanA113258.LaurentCore

open scoped BigOperators Topology
open Polynomial Asymptotics Filter Set Metric

theorem finset_prod_sub_isBigO {ι : Type*} (S : Finset ι)
    (f g : ι → ℂ → ℂ) (v : ℂ → ℂ)
    (hf : ∀ i ∈ S, ContinuousAt (f i) 0)
    (hg : ∀ i ∈ S, ContinuousAt (g i) 0)
    (hfg : ∀ i ∈ S, (fun t => f i t - g i t) =O[𝓝 0] v) :
    (fun t => (∏ i ∈ S, f i t) - ∏ i ∈ S, g i t) =O[𝓝 0] v := by
  classical
  induction S using Finset.induction_on with
  | empty => simpa using (isBigO_zero v (𝓝 (0 : ℂ)))
  | @insert i S hi ih =>
    have hfS : ContinuousAt (fun t => ∏ j ∈ S, f j t) 0 := by
      exact tendsto_finsetProd S (fun j hj => (hf j (Finset.mem_insert_of_mem hj)).tendsto)
    have hgi := hg i (Finset.mem_insert_self i S)
    have hrest := ih (fun j hj => hf j (Finset.mem_insert_of_mem hj))
      (fun j hj => hg j (Finset.mem_insert_of_mem hj))
      (fun j hj => hfg j (Finset.mem_insert_of_mem hj))
    have hfirst := (hfg i (Finset.mem_insert_self i S)).mul
      (hfS.tendsto.isBigO_one ℂ)
    have hsecond := (hgi.tendsto.isBigO_one ℂ).mul hrest
    have hsum := (hfirst.congr_right (fun t => mul_one (v t))).add
      (hsecond.congr_right (fun t => one_mul (v t)))
    apply hsum.congr_left
    intro t
    simp only [Finset.prod_insert hi]
    ring

theorem determinant_sub_isBigO {ι : Type*} [Fintype ι] [DecidableEq ι]
    (A B : ℂ → Matrix ι ι ℂ) (v : ℂ → ℂ)
    (hA : ∀ i j, ContinuousAt (fun t => A t i j) 0)
    (hB : ∀ i j, ContinuousAt (fun t => B t i j) 0)
    (hAB : ∀ i j, (fun t => A t i j - B t i j) =O[𝓝 0] v) :
    (fun t => (A t).det - (B t).det) =O[𝓝 0] v := by
  classical
  simp only [Matrix.det_apply, ← Finset.sum_sub_distrib]
  have hs := IsBigO.sum (s := Finset.univ) (A := fun σ : Equiv.Perm ι =>
    fun t => Equiv.Perm.sign σ • (∏ i, A t (σ i) i) -
      Equiv.Perm.sign σ • (∏ i, B t (σ i) i)) (g := v) (l := 𝓝 (0 : ℂ)) (by
    intro σ _
    have hh := finset_prod_sub_isBigO Finset.univ
      (fun i t => A t (σ i) i) (fun i t => B t (σ i) i) v
      (fun i _ => hA (σ i) i) (fun i _ => hB (σ i) i) (fun i _ => hAB (σ i) i)
    simpa only [← mul_sub, Units.smul_def, zsmul_eq_mul] using
      hh.const_mul_left ((Equiv.Perm.sign σ : ℤ) : ℂ))
  exact hs.congr_left (fun t => Finset.sum_apply t Finset.univ _)

noncomputable def exponentialTaylor (n : ℕ) (a : ℂ) : ℂ[X] :=
  ∑ h ∈ Finset.range n, C (a ^ h / (h.factorial : ℂ)) * X ^ h

theorem exponentialTaylor_eval (n : ℕ) (a t : ℂ) :
    (exponentialTaylor n a).eval t =
      ∑ h ∈ Finset.range n, (a * t) ^ h / (h.factorial : ℂ) := by
  simp only [exponentialTaylor, eval_finsetSum, eval_mul, eval_C, eval_pow, eval_X]
  apply Finset.sum_congr rfl
  intro h _
  rw [mul_pow]
  ring

theorem exponentialTaylor_remainder (n : ℕ) (a : ℂ) :
    (fun t => Complex.exp (a * t) - (exponentialTaylor n a).eval t)
      =O[𝓝 0] (fun t => t ^ n) := by
  have ht : Tendsto (fun t : ℂ => a * t) (𝓝 0) (𝓝 0) := by
    simpa using tendsto_const_nhds.mul (tendsto_id : Tendsto (id : ℂ → ℂ) (𝓝 0) (𝓝 0))
  have hh := (Complex.exp_sub_sum_range_isBigO_pow n).comp_tendsto ht
  have hh' : (fun t => Complex.exp (a * t) - (exponentialTaylor n a).eval t)
      =O[𝓝 0] (fun t => a ^ n * t ^ n) := by
    simpa only [Function.comp_def, exponentialTaylor_eval, mul_pow] using hh
  exact hh'.of_const_mul_right

theorem polynomial_eval_isBigO_of_X_pow_dvd (p : ℂ[X]) (d : ℕ)
    (hp : X ^ d ∣ p) : (fun t => p.eval t) =O[𝓝 0] (fun t => t ^ d) := by
  obtain ⟨q, hq⟩ := hp
  have hh := (isBigO_refl (fun t : ℂ => t ^ d) (𝓝 0)).mul
    (q.differentiable.continuous.continuousAt.tendsto.isBigO_one ℂ)
  simpa only [hq, eval_mul, eval_pow, eval_X, mul_one] using hh

/-- Exact multiplicity for the exponential determinant appearing in each
Taylor term of Laurent's interpolation determinant. -/
theorem tagged_exponential_isBigO {ι : Type*} [Fintype ι] [DecidableEq ι]
    {L : ℕ} (k : ι → ℕ) (c : ι → Fin L) (a α z s : ι → ℂ) :
    (fun t => (Matrix.of fun i j =>
      a i * (t * z j) ^ k i * Complex.exp (α i * (t * z j)) * s j ^ (c i).val).det)
      =O[𝓝 0] (fun t => t ^ (∑ v, (Fintype.card {i // c i = v}).choose 2)) := by
  classical
  let d := ∑ v, (Fintype.card {i // c i = v}).choose 2
  let p : ι → ℂ[X] := fun i => C (a i) * X ^ k i * exponentialTaylor d (α i)
  let P : ℂ[X] := (Matrix.of fun i j =>
    (p i).comp (C (z j) * X) * C (s j ^ (c i).val)).det
  let A : ℂ → Matrix ι ι ℂ := fun t => Matrix.of fun i j =>
    a i * (t * z j) ^ k i * Complex.exp (α i * (t * z j)) * s j ^ (c i).val
  let B : ℂ → Matrix ι ι ℂ := fun t => Matrix.of fun i j =>
    (p i).eval (z j * t) * s j ^ (c i).val
  have hA (i j : ι) : ContinuousAt (fun t => A t i j) 0 := by
    dsimp [A]
    fun_prop
  have hB (i j : ι) : ContinuousAt (fun t => B t i j) 0 := by
    dsimp [B]
    exact (((p i).differentiable.continuous.continuousAt.comp
      (continuousAt_const.mul continuousAt_id)).mul continuousAt_const)
  have hAB (i j : ι) : (fun t => A t i j - B t i j) =O[𝓝 0] (fun t => t ^ d) := by
    have hpre : ContinuousAt (fun t : ℂ => a i * (t * z j) ^ k i * s j ^ (c i).val) 0 := by
      fun_prop
    have hh := (hpre.tendsto.isBigO_one ℂ).mul (exponentialTaylor_remainder d (α i * z j))
    apply (hh.congr_right (fun t => one_mul (t ^ d))).congr_left
    intro t
    dsimp [A, B, p]
    simp only [eval_mul, eval_C, eval_pow, eval_X, exponentialTaylor_eval]
    have he : α i * z j * t = α i * (t * z j) := by ring
    have he' : α i * (z j * t) = α i * (t * z j) := by ring
    rw [he, he', mul_comm (z j) t]
    ring
  have hdet := determinant_sub_isBigO A B (fun t => t ^ d) hA hB hAB
  have hPeval (t : ℂ) : P.eval t = (B t).det := by
    have hh := RingHom.map_det (Polynomial.evalRingHom t)
      (Matrix.of fun i j => (p i).comp (C (z j) * X) * C (s j ^ (c i).val))
    change P.eval t = (Matrix.of fun i j =>
      ((p i).comp (C (z j) * X) * C (s j ^ (c i).val)).eval t).det at hh
    simpa only [eval_mul, eval_comp, eval_C, eval_X, B] using hh
  have hP : (fun t => P.eval t) =O[𝓝 0] (fun t => t ^ d) :=
    polynomial_eval_isBigO_of_X_pow_dvd P d (X_pow_dvd_taggedPolynomial p c z s)
  have hBdet := hP.congr_left hPeval
  exact hdet.congr_of_sub.mpr hBdet

theorem schwarz_of_isBigO_power (f : ℂ → ℂ) (d : ℕ) {ρ M : ℝ}
    (hρ : 1 < ρ) (hf : DifferentiableOn ℂ f (ball 0 ρ))
    (ho : f =O[𝓝 0] (fun t => t ^ d))
    (hbound : ∀ t ∈ ball 0 ρ, ‖f t‖ ≤ M) : ‖f 1‖ ≤ M / ρ ^ d := by
  have h1 : (1 : ℂ) ∈ ball 0 ρ := by simpa using hρ
  cases d with
  | zero => simpa using hbound 1 h1
  | succ n =>
    have hzero : f 0 = 0 := by
      obtain ⟨C, hC⟩ := ho.isBigOWith
      have hh := hC.bound.self_of_nhds
      simpa only [zero_pow (Nat.succ_ne_zero n), norm_zero, mul_zero,
        norm_le_zero_iff] using hh
    have hlo : (fun t : ℂ => f t - f 0) =o[𝓝 0] (fun t => ‖t - 0‖ ^ n) := by
      simpa only [hzero, sub_zero, norm_pow] using
        (ho.trans_isLittleO (Asymptotics.isLittleO_pow_pow (𝕜 := ℂ) (Nat.lt_succ_self n))).norm_right
    have hm : MapsTo f (ball 0 ρ) (closedBall (f 0) M) := by
      intro t ht
      simpa only [mem_closedBall, hzero, dist_zero_right] using hbound t ht
    have hh := Complex.dist_le_mul_div_pow_of_mapsTo_ball_of_isLittleO hf hm hlo h1
    simpa only [hzero, dist_zero_right, norm_one, one_div, inv_pow,
      div_eq_mul_inv, one_mul] using hh

/-- The Schwarz factor in Laurent's Lemma 4, for actual exponential functions.
Only the boundary estimate is an input; the zero's multiplicity is proved. -/
theorem tagged_exponential_schwarz {ι : Type*} [Fintype ι] [DecidableEq ι]
    {L : ℕ} (k : ι → ℕ) (c : ι → Fin L) (a α z s : ι → ℂ)
    {ρ M : ℝ} (hρ : 1 < ρ)
    (hbound : ∀ t ∈ ball (0 : ℂ) ρ,
      ‖(Matrix.of fun i j =>
        a i * (t * z j) ^ k i * Complex.exp (α i * (t * z j)) * s j ^ (c i).val).det‖ ≤ M) :
    ‖(Matrix.of fun i j =>
      a i * z j ^ k i * Complex.exp (α i * z j) * s j ^ (c i).val).det‖ ≤
      M / ρ ^ (∑ v, (Fintype.card {i // c i = v}).choose 2) := by
  have hf : Differentiable ℂ (fun t => (Matrix.of fun i j =>
      a i * (t * z j) ^ k i * Complex.exp (α i * (t * z j)) * s j ^ (c i).val).det) := by
    simp only [Matrix.det_apply, Matrix.of_apply, Units.smul_def, zsmul_eq_mul]
    fun_prop
  simpa only [one_mul] using schwarz_of_isBigO_power _ _ hρ hf.differentiableOn
    (tagged_exponential_isBigO k c a α z s) hbound

end LeanA113258.LaurentCore
