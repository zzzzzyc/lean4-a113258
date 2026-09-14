import LeanA113258.Remaining

namespace LeanA113258

/-!
  Factorial polarization of `a n` as global `Nat` identities
  (not congruences):

    `a n = 2^K + 6^B + ρ`

  with `K = (n-1)!`, `B = (n-2)!`, and `0 < ρ < 2^B` for `n ≥ 7`.
-/

theorem fact_K_eq_mul_B {n : Nat} (hn : 2 ≤ n) :
    fact (n - 1) = (n - 1) * fact (n - 2) :=
  fact_pred_eq hn

theorem two_pow_K_eq {n : Nat} (hn : 2 ≤ n) :
    2 ^ fact (n - 1) = 2 ^ fact (n - 2) * 2 ^ ((n - 2) * fact (n - 2)) := by
  simpa [term_one, mainTerm] using term_one_decomp hn

theorem sixB_eq {n : Nat} (hn : 3 ≤ n) :
    6 ^ fact (n - 2) = 2 ^ fact (n - 2) * 3 ^ fact (n - 2) := by
  simpa [term, fact_three] using term_two_decomp hn

theorem a_eq_twoK_add_sixB_add_rho {n : Nat} (hn : 3 ≤ n) :
    a n = 2 ^ fact (n - 1) + 6 ^ fact (n - 2) + rho n := by
  have h := a_eq_twoB_mul_plus_rho hn
  unfold midFactor at h
  rw [Nat.mul_add, ← two_pow_K_eq (by omega), ← sixB_eq hn] at h
  exact h

theorem delta_eq_sixB_add_rho {n : Nat} (hn : 3 ≤ n) :
    delta n = 6 ^ fact (n - 2) + rho n := by
  have ha := a_eq_main_add_delta (by omega : 2 ≤ n)
  have hp := a_eq_twoK_add_sixB_add_rho hn
  simp [mainTerm] at ha
  omega

theorem sixB_lt_half {n : Nat} (hn : 7 ≤ n) :
    6 ^ fact (n - 2) < 2 ^ (fact (n - 1) / 2) := by
  have h := n_six_pow_lt_half hn
  have hle : 6 ^ fact (n - 2) ≤ n * 6 ^ fact (n - 2) :=
    Nat.le_mul_of_pos_left _ (by omega : 0 < n)
  exact Nat.lt_of_le_of_lt hle h

theorem rho_lt_sixB {n : Nat} (hn : 7 ≤ n) :
    rho n < 6 ^ fact (n - 2) :=
  Nat.lt_trans (rho_lt_twoB hn)
    (Nat.pow_lt_pow_left (by decide : (2 : Nat) < 6)
      (Nat.ne_of_gt (fact_pos (n - 2))))

theorem polarized {n : Nat} (hn : 7 ≤ n) :
    a n = 2 ^ fact (n - 1) + 6 ^ fact (n - 2) + rho n ∧
      0 < rho n ∧
      rho n < 2 ^ fact (n - 2) ∧
      6 ^ fact (n - 2) < 2 ^ (fact (n - 1) / 2) :=
  ⟨a_eq_twoK_add_sixB_add_rho (by omega),
    rho_pos (by omega), rho_lt_twoB hn, sixB_lt_half hn⟩

end LeanA113258
