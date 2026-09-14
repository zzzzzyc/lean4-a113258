import LaurentGridBounds
import Mathlib.Algebra.BigOperators.Field

/-! Discrete layer identities used in the rectangular-grid correlation bound. -/

namespace LeanA113258.LaurentCore

open scoped BigOperators

theorem sum_prefixes (u : ℕ → ℝ) (h : ℕ) :
    (∑ j ∈ Finset.range (h + 1), ∑ q ∈ Finset.range j, u q) =
      ∑ q ∈ Finset.range h, ((h : ℝ) - q) * u q := by
  induction h with
  | zero => simp
  | succ h ih =>
    rw [Finset.sum_range_succ, ih, Finset.sum_range_succ,
      Finset.sum_range_succ]
    simp only [Nat.cast_add, Nat.cast_one]
    have hs : (∑ q ∈ Finset.range h, (((h : ℝ) + 1) - q) * u q) =
        (∑ q ∈ Finset.range h, ((h : ℝ) - q) * u q) + ∑ q ∈ Finset.range h, u q := by
      rw [← Finset.sum_add_distrib]
      apply Finset.sum_congr rfl
      intro q _
      ring
    rw [hs]
    ring

theorem centered_layers_odd (t : ℕ → ℝ) (h : ℕ) :
    (∑ l ∈ Finset.range (2 * h + 1), ((l : ℝ) - h) * t l) =
      ∑ j ∈ Finset.range (h + 1), ∑ q ∈ Finset.range j, (t (2 * h - q) - t q) := by
  rw [sum_prefixes]
  have hsplit : 2 * h + 1 = h + (h + 1) := by omega
  rw [hsplit, Finset.sum_range_add]
  have href := Finset.sum_range_reflect
    (fun l => (((h + l : ℕ) : ℝ) - h) * t (h + l)) (h + 1)
  rw [← href, Finset.sum_range_succ]
  simp only [Nat.add_sub_cancel, Nat.sub_self, sub_self, zero_mul, add_zero]
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro q hq
  have hqh : q ≤ h := by have := Finset.mem_range.mp hq; omega
  have he : h + (h - q) = 2 * h - q := by omega
  have hv : (((h + (h - q) : ℕ) : ℝ) - h) = (h : ℝ) - q := by
    rw [Nat.cast_add, Nat.cast_sub hqh]
    ring
  rw [hv, he]
  ring

theorem centered_layers_even (t : ℕ → ℝ) (h : ℕ) :
    (∑ l ∈ Finset.range (2 * h), ((l : ℝ) - ((2 * h : ℕ) - 1 : ℝ) / 2) * t l) =
      (∑ j ∈ Finset.range h, ∑ q ∈ Finset.range j, (t (2 * h - 1 - q) - t q)) +
        (∑ q ∈ Finset.range h, (t (2 * h - 1 - q) - t q)) / 2 := by
  cases h with
  | zero => simp
  | succ h =>
    have hpre := sum_prefixes (fun q => t (2 * (h + 1) - 1 - q) - t q) h
    rw [hpre]
    have hsplit : 2 * (h + 1) = (h + 1) + (h + 1) := by omega
    rw [hsplit, Finset.sum_range_add]
    have href := Finset.sum_range_reflect
      (fun l => ((((h + 1) + l : ℕ) : ℝ) - (((h + 1) + (h + 1) : ℕ) - 1 : ℝ) / 2) *
        t ((h + 1) + l)) (h + 1)
    rw [← href]
    have hp : (∑ q ∈ Finset.range h, ((h : ℝ) - q) * (t ((h + 1) + (h + 1) - 1 - q) - t q)) =
        ∑ q ∈ Finset.range (h + 1), ((h : ℝ) - q) * (t ((h + 1) + (h + 1) - 1 - q) - t q) := by
      rw [Finset.sum_range_succ]
      simp
    rw [hp, Finset.sum_div, ← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro q hq
    have hqh : q ≤ h := by have := Finset.mem_range.mp hq; omega
    have he : (h + 1) + (h + 1 - 1 - q) = (h + 1) + (h + 1) - 1 - q := by omega
    rw [he]
    have hn : 1 ≤ (h + 1) + (h + 1) := by omega
    have hnq : q ≤ (h + 1) + (h + 1) - 1 := by omega
    push_cast [Nat.cast_sub hnq, Nat.cast_sub hn]
    ring

theorem sum_quadratic_layers (A B : ℝ) (h : ℕ) :
    (∑ j ∈ Finset.range (h + 1), (A * j - B * (j : ℝ) ^ 2)) =
      A * h * (h + 1) / 2 - B * h * (h + 1) * (2 * h + 1) / 6 := by
  induction h with
  | zero => simp
  | succ h ih =>
    rw [Finset.sum_range_succ, ih]
    push_cast
    ring

theorem sum_quadratic_half_layers (A B : ℝ) (h : ℕ) :
    (∑ j ∈ Finset.range h, (A * j - B * (j : ℝ) ^ 2)) +
        (A * h - B * (h : ℝ) ^ 2) / 2 =
      A * (h : ℝ) ^ 2 / 2 - B * (2 * (h : ℝ) ^ 3 + h) / 6 := by
  have hh := sum_quadratic_layers A B h
  rw [Finset.sum_range_succ] at hh
  linarith

theorem centered_sum_bound_odd (t : ℕ → ℝ) (h : ℕ) {A B S : ℝ}
    (hB : 0 ≤ B) (hAB : B * (2 * h + 1) ≤ A)
    (hp : ∀ j ≤ h, S * (∑ q ∈ Finset.range j, (t (2 * h - q) - t q)) ≤
      A * j - B * (j : ℝ) ^ 2) :
    S * (∑ l ∈ Finset.range (2 * h + 1), ((l : ℝ) - h) * t l) ≤
      A * (2 * h + 1) ^ 2 / 8 - B * (2 * h + 1) ^ 3 / 24 := by
  rw [centered_layers_odd, Finset.mul_sum]
  have hh : (∑ j ∈ Finset.range (h + 1), S * ∑ q ∈ Finset.range j,
        (t (2 * h - q) - t q)) ≤
      ∑ j ∈ Finset.range (h + 1), (A * j - B * (j : ℝ) ^ 2) := by
    apply Finset.sum_le_sum
    intro j hj
    exact hp j (by have := Finset.mem_range.mp hj; omega)
  rw [sum_quadratic_layers] at hh
  have hbn : 0 ≤ B * (2 * (h : ℝ) + 1) := mul_nonneg hB (by positivity)
  nlinarith

theorem centered_sum_bound_even (t : ℕ → ℝ) (h : ℕ) {A B S : ℝ}
    (hB : 0 ≤ B)
    (hp : ∀ j ≤ h, S * (∑ q ∈ Finset.range j, (t (2 * h - 1 - q) - t q)) ≤
      A * j - B * (j : ℝ) ^ 2) :
    S * (∑ l ∈ Finset.range (2 * h), ((l : ℝ) - ((2 * h : ℕ) - 1 : ℝ) / 2) * t l) ≤
      A * (2 * h) ^ 2 / 8 - B * (2 * h) ^ 3 / 24 := by
  rw [centered_layers_even, mul_add, mul_div_assoc, Finset.mul_sum]
  have hh : (∑ j ∈ Finset.range h, S * ∑ q ∈ Finset.range j,
        (t (2 * h - 1 - q) - t q)) ≤
      ∑ j ∈ Finset.range h, (A * j - B * (j : ℝ) ^ 2) := by
    apply Finset.sum_le_sum
    intro j hj
    exact hp j (by have := Finset.mem_range.mp hj; omega)
  have hh' := add_le_add hh (div_le_div_of_nonneg_right (hp h le_rfl) (by norm_num : (0 : ℝ) ≤ 2))
  rw [sum_quadratic_half_layers] at hh'
  have hbn : 0 ≤ B * (h : ℝ) := mul_nonneg hB (Nat.cast_nonneg _)
  nlinarith

end LeanA113258.LaurentCore
