import LaurentArithmetic

/-! The common power divisor in the rational-integer specialization of
Laurent's arithmetic lower bound. -/

namespace LeanA113258.LaurentCore

open scoped BigOperators

def binomialIntegerMatrix {ι : Type*} (k l r s : ι → ℕ) (a b u v : ℕ) : Matrix ι ι ℤ :=
  Matrix.of fun i j => ((r j * u + s j * v).choose (k i) : ℤ) *
    (a : ℤ) ^ (l i * r j) * (b : ℤ) ^ (l i * s j)

theorem common_power_divisor_binomial_determinant {ι : Type*}
    [Fintype ι] [DecidableEq ι] (k l r s : ι → ℕ) (a b u v m₁ m₂ : ℕ)
    (h₁ : ∀ σ : Equiv.Perm ι, m₁ ≤ ∑ i, l (σ i) * r i)
    (h₂ : ∀ σ : Equiv.Perm ι, m₂ ≤ ∑ i, l (σ i) * s i) :
    (a : ℤ) ^ m₁ * (b : ℤ) ^ m₂ ∣ (binomialIntegerMatrix k l r s a b u v).det := by
  classical
  apply common_divisor_of_determinant_terms
  intro σ
  simp only [binomialIntegerMatrix, Matrix.of_apply, Finset.prod_mul_distrib,
    Finset.prod_pow_eq_pow_sum]
  have hh : (a : ℤ) ^ m₁ * (b : ℤ) ^ m₂ ∣
      (a : ℤ) ^ (∑ i, l (σ i) * r i) * (b : ℤ) ^ (∑ i, l (σ i) * s i) :=
    mul_dvd_mul (pow_dvd_pow (a : ℤ) (h₁ σ)) (pow_dvd_pow (b : ℤ) (h₂ σ))
  rw [mul_assoc]
  exact dvd_mul_of_dvd_right hh _

theorem log_binomial_determinant_lower_bound {ι : Type*}
    [Fintype ι] [DecidableEq ι] (k l r s : ι → ℕ) (a b u v m₁ m₂ : ℕ)
    (ha : 0 < a) (hb : 0 < b)
    (hdet : (binomialIntegerMatrix k l r s a b u v).det ≠ 0)
    (h₁ : ∀ σ : Equiv.Perm ι, m₁ ≤ ∑ i, l (σ i) * r i)
    (h₂ : ∀ σ : Equiv.Perm ι, m₂ ≤ ∑ i, l (σ i) * s i) :
    (m₁ : ℝ) * Real.log (a : ℝ) + (m₂ : ℝ) * Real.log (b : ℝ) ≤
      Real.log |((binomialIntegerMatrix k l r s a b u v).det : ℝ)| := by
  have hapos : (0 : ℤ) < a := by exact_mod_cast ha
  have hbpos : (0 : ℤ) < b := by exact_mod_cast hb
  have hm : (0 : ℤ) < (a : ℤ) ^ m₁ * (b : ℤ) ^ m₂ :=
    mul_pos (pow_pos hapos _) (pow_pos hbpos _)
  have hh := integer_common_divisor_lower_bound hm hdet
    (common_power_divisor_binomial_determinant k l r s a b u v m₁ m₂ h₁ h₂)
  have haposR : (0 : ℝ) < a := by exact_mod_cast ha
  have hbposR : (0 : ℝ) < b := by exact_mod_cast hb
  have hlog := Real.log_le_log (show (0 : ℝ) < ((a : ℤ) ^ m₁ * (b : ℤ) ^ m₂ : ℤ) by
    exact_mod_cast hm) hh
  simpa only [Int.cast_mul, Int.cast_pow, Int.cast_natCast,
    Real.log_mul (ne_of_gt (pow_pos haposR _)) (ne_of_gt (pow_pos hbposR _)), Real.log_pow] using hlog

end LeanA113258.LaurentCore
