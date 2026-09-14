import NearPowerAnalysis
import LeanA113258.BakerCond

/-!
The sequence-specific specialization of Laurent's Corollary 2.
`LaurentIntegerTwoLogLowerBound` is the precise remaining external theorem.
All results in this file explicitly take it as a premise.
-/

namespace LeanA113258

open AnalyticCutoff NearPowerAnalysis

/-- The rational-integer case of Laurent (2008), Corollary 2, m=10.
This is a proposition to prove, not an axiom declaration. -/
def LaurentIntegerTwoLogLowerBound : Prop :=
  ∀ b e K : ℕ, 3 ≤ b → b % 2 = 1 → 0 < e → 0 < K →
    0 < linearForm (b : ℝ) e K →
    -(126 / 5 : ℝ) *
      (max (Real.log ((K : ℝ) / Real.log (b : ℝ) + (e : ℝ)) + 19 / 50) 10) ^ 2 *
        Real.log (b : ℝ) ≤ Real.log (linearForm (b : ℝ) e K)

theorem real_factorial_ratio {n B : ℝ} (hn : 4 < n) (hB : 0 < B) :
    ((n - 1) * B + 1) / ((n - 1) * B - 3 * B) =
      (n - 1 + 1 / B) / (n - 4) := by
  have hden : (n - 1) * B - 3 * B = (n - 4) * B := by ring
  rw [hden]
  field_simp [ne_of_gt hB, ne_of_gt (sub_pos.mpr hn)]

theorem remaining_ratio_from_laurent (hLaurent : LaurentIntegerTwoLogLowerBound)
    {n b e : ℕ} (hn : 12 ≤ n) (hb : 1 < b) (he : 1 < e) (hab : a n = b ^ e) :
    (e : ℝ) < (126 / 5 : ℝ) * (H (e : ℝ)) ^ 2 *
      (((n : ℝ) - 1 + 1 / (fact (n - 2) : ℝ)) / ((n : ℝ) - 4)) := by
  have hodd := base_odd_of_a_eq_pow (by omega : 1 ≤ n) (by omega : 0 < e) hab
  have hb3 : 3 ≤ b := by omega
  have hb3' : (3 : ℝ) ≤ (b : ℝ) := by exact_mod_cast hb3
  have hbpos : (0 : ℝ) < (b : ℝ) := by linarith
  have hδpos : (0 : ℝ) < (delta n : ℝ) := by exact_mod_cast delta_pos (by omega : 2 ≤ n)
  have hK := fact_pos (n - 1)
  have hB := fact_pos (n - 2)
  have hpow : (b : ℝ) ^ e = (2 : ℝ) ^ fact (n - 1) + (delta n : ℝ) := by
    have hnat : b ^ e = 2 ^ fact (n - 1) + delta n := by
      rw [← hab]
      exact a_eq_main_add_delta (by omega)
    exact_mod_cast hnat
  have hδ : (delta n : ℝ) < (2 : ℝ) ^ (3 * fact (n - 2)) := by
    exact_mod_cast delta_lt_two_pow_three_B (by omega : 7 ≤ n)
  have hupper : (b : ℝ) ^ e < (2 : ℝ) ^ (fact (n - 1) + 1) := by
    have hnat := a_lt_two_pow_succ (by omega : 7 ≤ n)
    rw [hab] at hnat
    exact_mod_cast hnat
  have hMK : 3 * fact (n - 2) < fact (n - 1) := by
    rw [fact_pred_eq (by omega)]
    exact Nat.mul_lt_mul_of_pos_right (by omega) hB
  have hform := linearForm_pos hbpos hδpos hpow
  have hL := hLaurent b e (fact (n - 1)) hb3 hodd (by omega) hK hform
  have hL' := weaken_laurent_lower hb3' hK (by omega) hform hL
  have hratio := ratio_bound_of_log_lower hb3' (by omega) hMK hδpos hpow hδ hupper hL'
  have hn' : (12 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
  have hB' : (0 : ℝ) < (fact (n - 2) : ℝ) := by exact_mod_cast hB
  have hK' : (fact (n - 1) : ℝ) = ((n : ℝ) - 1) * (fact (n - 2) : ℝ) := by
    rw [fact_pred_eq (by omega)]
    push_cast [Nat.cast_sub (by omega : 1 ≤ n)]
    rfl
  push_cast at hratio
  rw [hK', real_factorial_ratio (by linarith : (4 : ℝ) < (n : ℝ)) hB'] at hratio
  exact hratio

theorem remaining_finite_from_laurent (hLaurent : LaurentIntegerTwoLogLowerBound)
    {n b e : ℕ} (hn : 12 ≤ n) (hb : 1 < b) (he : 1 < e)
    (hg : Nat.gcd e (fact (n - 1)) = 1) (hab : a n = b ^ e) :
    n ≤ 2523 ∧ n ≤ e ∧ e < 3500 := by
  have hratio := remaining_ratio_from_laurent hLaurent hn hb he hab
  have hn' : (12 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
  have hB : (9 : ℝ) ≤ (fact (n - 2) : ℝ) := by
    have hf := fact_le_of_le (by omega : 4 ≤ n - 2)
    rw [fact_four] at hf
    have : 9 ≤ fact (n - 2) := by omega
    exact_mod_cast this
  have hne := coprime_exp_ge (by omega : 2 ≤ n) he hg
  have hne' : (n : ℝ) ≤ (e : ℝ) := by exact_mod_cast hne
  have heBound := exponent_bound_from_ratio hn' hB hratio
  have hnBound := index_lt_2524 hn' hB hne' hratio
  have heNat : e < 3500 := by exact_mod_cast heBound
  have hnNat : n < 2524 := by exact_mod_cast hnBound
  exact ⟨by omega, hne, heNat⟩

/-- A fully integral necessary condition, suitable for a finite certificate checker. -/
theorem remaining_integer_cut_from_laurent (hLaurent : LaurentIntegerTwoLogLowerBound)
    {n b e : ℕ} (hn : 12 ≤ n) (hb : 1 < b) (he : 1 < e) (hab : a n = b ^ e) :
    9 * e * (n - 4) < 22680 * (n - 1) + 2520 := by
  have hratio := remaining_ratio_from_laurent hLaurent hn hb he hab
  have hn' : (12 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
  have hB : (9 : ℝ) ≤ (fact (n - 2) : ℝ) := by
    have hf := fact_le_of_le (by omega : 4 ≤ n - 2)
    rw [fact_four] at hf
    have : 9 ≤ fact (n - 2) := by omega
    exact_mod_cast this
  have hepos : (0 : ℝ) < (e : ℝ) := by exact_mod_cast (show 0 < e by omega)
  have heCut := exponent_bound_from_ratio hn' hB hratio
  rw [H_below_cutoff hepos (le_of_lt heCut)] at hratio
  norm_num at hratio
  have hmul : (e : ℝ) * ((n : ℝ) - 4) < 2520 * ((n : ℝ) - 1 + 1 / (fact (n - 2) : ℝ)) := by
    apply (lt_div_iff₀ (by linarith : (0 : ℝ) < (n : ℝ) - 4)).1
    simpa only [mul_div_assoc, one_div] using hratio
  have hBp : (0 : ℝ) < (fact (n - 2) : ℝ) := by linarith
  have hinv : 1 / (fact (n - 2) : ℝ) ≤ (1 / 9 : ℝ) :=
    (div_le_div_iff₀ hBp (by norm_num)).2 (by linarith)
  have hreal : (9 : ℝ) * (e : ℝ) * ((n : ℝ) - 4) < 22680 * ((n : ℝ) - 1) + 2520 := by
    nlinarith
  have hcast : ((9 * e * (n - 4) : ℕ) : ℝ) < ((22680 * (n - 1) + 2520 : ℕ) : ℝ) := by
    push_cast [Nat.cast_sub (by omega : 4 ≤ n), Nat.cast_sub (by omega : 1 ≤ n)]
    exact hreal
  exact_mod_cast hcast

#print axioms remaining_ratio_from_laurent
#print axioms remaining_finite_from_laurent
#print axioms remaining_integer_cut_from_laurent

end LeanA113258
