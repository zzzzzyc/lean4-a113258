import LaurentMultiplicity

/-!
Arithmetic determinant bounds for the rational-integer case. These use
integrality and common divisors, avoiding algebraic-number heights.
The required nonzero minor must still be constructed separately.
-/

namespace LeanA113258.LaurentCore

open scoped BigOperators

theorem integer_common_divisor_lower_bound {D m : ℤ}
    (hm : 0 < m) (hD : D ≠ 0) (hdiv : m ∣ D) : (m : ℝ) ≤ |(D : ℝ)| := by
  obtain ⟨k, hk⟩ := hdiv
  have hk0 : k ≠ 0 := by
    intro hz
    apply hD
    simp [hk, hz]
  have hkabs : (1 : ℤ) ≤ |k| := by
    have := abs_pos.mpr hk0
    omega
  have hkR : (1 : ℝ) ≤ |(k : ℝ)| := by exact_mod_cast hkabs
  have hmR : (0 : ℝ) < (m : ℝ) := by exact_mod_cast hm
  rw [hk, Int.cast_mul, abs_mul, abs_of_pos hmR]
  nlinarith

theorem common_divisor_of_determinant_terms {ι : Type*} [Fintype ι] [DecidableEq ι]
    (A : Matrix ι ι ℤ) (m : ℤ)
    (hterms : ∀ σ : Equiv.Perm ι, m ∣ ∏ i, A (σ i) i) : m ∣ A.det := by
  rw [Matrix.det_apply']
  apply Finset.dvd_sum
  intro σ _
  exact dvd_mul_of_dvd_right (hterms σ) _

/-- The real determinant of an integer matrix is the cast of its integer determinant. -/
theorem real_integer_determinant_lower_bound {ι : Type*} [Fintype ι] [DecidableEq ι]
    (A : Matrix ι ι ℤ) {m : ℤ} (hm : 0 < m) (hA : A.det ≠ 0)
    (hdiv : m ∣ A.det) : (m : ℝ) ≤ |(A.map (fun x => (x : ℝ))).det| := by
  rw [← Int.cast_det]
  exact integer_common_divisor_lower_bound hm hA hdiv

theorem real_integer_determinant_log_lower_bound {ι : Type*}
    [Fintype ι] [DecidableEq ι] (A : Matrix ι ι ℤ) {m : ℤ}
    (hm : 0 < m) (hA : A.det ≠ 0) (hdiv : m ∣ A.det) :
    Real.log (m : ℝ) ≤ Real.log |(A.map (fun x => (x : ℝ))).det| := by
  apply Real.log_le_log (by exact_mod_cast hm)
  exact real_integer_determinant_lower_bound A hm hA hdiv

theorem integer_determinant_contradiction {ι : Type*} [Fintype ι] [DecidableEq ι]
    (A : Matrix ι ι ℤ) {m : ℤ} (hm : 0 < m) (hA : A.det ≠ 0)
    (hdiv : m ∣ A.det) (hupper : |(A.map (fun x => (x : ℝ))).det| < (m : ℝ)) :
    False :=
  (not_lt_of_ge (real_integer_determinant_lower_bound A hm hA hdiv)) hupper

#print axioms common_divisor_of_determinant_terms
#print axioms real_integer_determinant_log_lower_bound
#print axioms integer_determinant_contradiction

end LeanA113258.LaurentCore
