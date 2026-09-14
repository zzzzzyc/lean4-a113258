import LaurentCentering
import LaurentProductEstimate

/-! Specialization of the centering identity to positive integer bases and
their real logarithms. -/

namespace LeanA113258.LaurentCore

open scoped BigOperators

theorem integer_powers_eq_exp_real_logs (a b r s : ℕ) (ha : 0 < a) (hb : 0 < b) :
    (a : ℂ) ^ r * (b : ℂ) ^ s =
      Complex.exp (((r : ℝ) * Real.log a + (s : ℝ) * Real.log b : ℝ) : ℂ) := by
  have ha' : (0 : ℝ) < a := by exact_mod_cast ha
  have hb' : (0 : ℝ) < b := by exact_mod_cast hb
  rw [← Complex.ofReal_exp, Real.exp_add, Real.exp_nat_mul, Real.exp_nat_mul,
    Real.exp_log ha', Real.exp_log hb']
  push_cast
  rfl

theorem integer_determinant_real_centering {K L : ℕ}
    (r s : Fin K × Fin L → ℕ) (a b u v : ℕ)
    (ha : 0 < a) (hb : 0 < b) (hu : 0 < u) (η : ℝ) :
    let c := ((L : ℝ) - 1) / 2
    let A := Real.log (a : ℝ)
    let B := Real.log (b : ℝ)
    let β := (v : ℝ) / u
    let δ := B - β * A
    let z := fun j => (r j : ℝ) + β * s j - η
    |((binomialIntegerMatrix (fun i : Fin K × Fin L => i.1.val) (fun i => i.2.val)
      r s a b u v).det : ℝ)| =
      Real.exp (c * ((∑ j, (r j : ℝ)) * A + (∑ j, (s j : ℝ)) * B)) *
        ‖(Matrix.of fun i j : Fin K × Fin L =>
          ((u : ℂ) ^ i.1.val / (i.1.val.factorial : ℂ)) * (z j : ℂ) ^ i.1.val *
            Complex.exp (((((i.2.val : ℝ) - c) * A : ℝ) : ℂ) * (z j : ℂ)) *
              Complex.exp (((((i.2.val : ℝ) - c) * δ : ℝ) : ℂ) * (s j : ℂ))).det‖ := by
  classical
  dsimp only
  let A := Real.log (a : ℝ)
  let B := Real.log (b : ℝ)
  let β := (v : ℝ) / u
  let c := ((L : ℝ) - 1) / 2
  let δ := B - β * A
  let z : Fin K × Fin L → ℝ := fun j => (r j : ℝ) + β * s j - η
  let x : Fin K × Fin L → ℕ := fun j => r j * u + s j * v
  let y : Fin K × Fin L → ℂ := fun j => (a : ℂ) ^ r j * (b : ℂ) ^ s j
  have hu' : (u : ℂ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hu)
  have hx (j) : (x j : ℂ) - (u : ℂ) * (η : ℂ) = (u : ℂ) * (z j : ℂ) := by
    dsimp [x, z, β]
    push_cast
    field_simp
  have harg (j : Fin K × Fin L) :
      (A : ℂ) * ((z j : ℂ) + (η : ℂ)) + (δ : ℂ) * (s j : ℂ) =
      (((r j : ℝ) * A + (s j : ℝ) * B : ℝ) : ℂ) := by
    dsimp [z, δ]
    push_cast
    ring
  have hy (j) : y j = Complex.exp ((A : ℂ) * ((z j : ℂ) + (η : ℂ)) + (δ : ℂ) * (s j : ℂ)) := by
    rw [harg]
    exact integer_powers_eq_exp_real_logs a b (r j) (s j) ha hb
  have hc : (∑ i : Fin K × Fin L, ((i.2.val : ℂ) - (c : ℂ))) = 0 := by
    simpa only [c, Complex.ofReal_div, Complex.ofReal_sub, Complex.ofReal_natCast,
      Complex.ofReal_one, Complex.ofReal_ofNat] using sum_centered_second_index K L
  have hh := binomial_exponential_centering x y (fun j => (z j : ℂ))
    (fun j => (s j : ℂ)) (u : ℂ) (c : ℂ) (η : ℂ) (A : ℂ) (δ : ℂ) hx hy hc
  let D := binomialIntegerMatrix (fun i : Fin K × Fin L => i.1.val) (fun i => i.2.val) r s a b u v
  have hcast : (D.det : ℂ) =
      (Matrix.of fun i j : Fin K × Fin L => ((x j).choose i.1.val : ℂ) * y j ^ i.2.val).det := by
    have he := (Int.castRingHom ℂ).map_det D
    change (D.det : ℂ) = (D.map (fun n : ℤ => (n : ℂ))).det at he
    rw [he]
    congr 1
    ext i j
    simp only [D, binomialIntegerMatrix, Matrix.map_apply, Matrix.of_apply,
      Int.cast_mul, Int.cast_pow, Int.cast_natCast, x, y, mul_pow, pow_mul]
    ring
  have hexp : (c : ℂ) * (∑ j, ((A : ℂ) * ((z j : ℂ) + (η : ℂ)) + (δ : ℂ) * (s j : ℂ))) =
      ((c * ((∑ j, (r j : ℝ)) * A + (∑ j, (s j : ℝ)) * B) : ℝ) : ℂ) := by
    simp_rw [harg]
    push_cast
    rw [Finset.sum_add_distrib, Finset.sum_mul, Finset.sum_mul]
  rw [hexp] at hh
  have hn := congrArg norm (hcast.trans hh)
  rw [Complex.norm_intCast, norm_mul, Complex.norm_exp, Complex.ofReal_re] at hn
  convert hn using 1
  congr 2
  congr 1
  ext i j
  dsimp [A, B, β, c, δ, z]
  push_cast
  rfl

end LeanA113258.LaurentCore
