import LeanA113258.Remaining
import LeanA113258.PrimeCertificates

namespace LeanA113258

set_option maxRecDepth 30000
set_option maxHeartbeats 8000000

theorem a_7_not_perfect_power : ¬ IsPerfectPower (a 7) := by
  apply a_not_perfect_power_of_mod_certificate (p := 13) (by decide)
  · apply primeCert_of_trial (t := 3) (by decide) (by decide); decide
  · decide +kernel
  · decide +kernel

/-- A divisor of a fixed factorial divides every later factorial. -/
theorem dvd_fact_from {d k n : Nat} (hk : d ∣ fact k) (hn : k ≤ n) :
    d ∣ fact n := by
  refine le_induction (fun n => d ∣ fact n) hn hk ?_
  intro m _ hm
  rw [fact_succ]
  exact Nat.dvd_mul_right_of_dvd hm (m + 1)

/-- Once a modular power is idempotent, every positive multiple of that
    exponent has the same residue. -/
theorem pow_multiple_mod {b d m r k : Nat} (hk : 0 < k)
    (hseed : b ^ d % m = r) (hidem : r * r % m = r) :
    b ^ (d * k) % m = r := by
  cases k with
  | zero => omega
  | succ k =>
    induction k with
    | zero => simpa using hseed
    | succ k ih =>
      rw [Nat.mul_succ, Nat.pow_add, Nat.mul_mod, ih (by omega), hseed, hidem]

theorem pow_fact_mod_from {b d m r k n : Nat}
    (_hd : 0 < d) (hdiv : d ∣ fact k) (hn : k ≤ n)
    (hseed : b ^ d % m = r) (hidem : r * r % m = r) :
    b ^ fact n % m = r := by
  obtain ⟨t, ht⟩ := dvd_fact_from hdiv hn
  have hpos := fact_pos n
  have htpos : 0 < t := by
    cases t with
    | zero => simp at ht; omega
    | succ t => omega
  rw [ht]
  exact pow_multiple_mod htpos hseed hidem

theorem term_mod210_zero {n i : Nat} (hi : 6 ≤ i) : term n i % 210 = 0 := by
  have hd : 210 ∣ fact (i + 1) := dvd_fact_from (k := 7) (by decide) (by omega)
  have he : fact (n - i) = (fact (n - i) - 1) + 1 := by have := fact_pos (n - i); omega
  have hp : 210 ∣ fact (i + 1) ^ fact (n - i) := by
    rw [he, Nat.pow_succ']
    exact Nat.dvd_mul_right_of_dvd hd _
  exact Nat.mod_eq_zero_of_dvd hp

theorem sumRange_mod_eq_initial {f : Nat → Nat} {m k n : Nat} (hn : k ≤ n)
    (ht : ∀ i, k ≤ i → f i % m = 0) :
    sumRange n f % m = sumRange k f % m := by
  refine le_induction (fun n => sumRange n f % m = sumRange k f % m) hn rfl ?_
  intro j hj ih
  rw [sumRange_succ, Nat.add_mod, ht j hj, Nat.add_zero, Nat.mod_mod, ih]

/-- Every term from n=7 onward is -1 modulo 210. -/
theorem a_mod210 {n : Nat} (hn : 7 ≤ n) : a n % 210 = 209 := by
  have h0 : term n 0 % 210 = 1 := by simp [term]
  have h1 : term n 1 % 210 = 106 := by
    simp only [term]
    exact pow_fact_mod_from (d := 12) (k := 4) (by decide) (by decide)
      (by omega) (by decide) (by decide)
  have h2 : term n 2 % 210 = 36 := by
    simp only [term]
    exact pow_fact_mod_from (d := 12) (k := 4) (by decide) (by decide)
      (by omega) (by decide) (by decide)
  have h3 : term n 3 % 210 = 36 := by
    simp only [term]
    exact pow_fact_mod_from (d := 12) (k := 4) (by decide) (by decide)
      (by omega) (by decide) (by decide)
  have h4 : term n 4 % 210 = 120 := by
    simp only [term]
    exact pow_fact_mod_from (d := 1) (k := 0) (by decide) (by decide)
      (by omega) (by decide) (by decide)
  have h5 : term n 5 % 210 = 120 := by
    simp only [term]
    exact pow_fact_mod_from (d := 2) (k := 2) (by decide) (by decide)
      (by omega) (by decide) (by decide)
  have ha : a n % 210 = sumRange 6 (term n) % 210 :=
    sumRange_mod_eq_initial (by omega) (fun _ hi => term_mod210_zero hi)
  rw [ha]
  simp only [sumRange_succ, sumRange_zero]
  omega

theorem pow_period_mod {b m d : Nat} (h : b ^ (d + 1) % m = b % m)
    (k : Nat) : b ^ (k + d + 1) % m = b ^ (k + 1) % m := by
  rw [Nat.add_assoc, Nat.pow_add, Nat.mul_mod, h, ← Nat.mul_mod, ← Nat.pow_succ]

theorem pow_reduce_mod {b m d : Nat} (h : b ^ (d + 1) % m = b % m)
    {e : Nat} (he : 0 < e) :
    b ^ e % m = b ^ ((e - 1) % d + 1) % m := by
  have step (k r : Nat) : b ^ (d * k + r + 1) % m = b ^ (r + 1) % m := by
    induction k with
    | zero => simp
    | succ k ih =>
      have hsplit : d * (k + 1) + r + 1 = (d * k + r) + d + 1 := by
        rw [Nat.mul_succ]; omega
      rw [hsplit, pow_period_mod h, ih]
  have hdecomp := Nat.mod_add_div (e - 1) d
  have heq : e = d * ((e - 1) / d) + (e - 1) % d + 1 := by omega
  calc
    b ^ e % m = b ^ (d * ((e - 1) / d) + (e - 1) % d + 1) % m :=
      congrArg (fun t : Nat => b ^ t % m) heq
    _ = b ^ ((e - 1) % d + 1) % m := step _ _

theorem mod210_period_table : ∀ r : Fin 210, r.val ^ 13 % 210 = r.val := by
  decide

theorem mod210_root_table : ∀ r : Fin 210, ∀ s : Fin 12,
    (s.val + 1) % 2 ≠ 0 → (s.val + 1) % 3 ≠ 0 →
    r.val ^ (s.val + 1) % 210 = 209 → r.val = 209 := by
  decide

/-- Raising to an exponent prime to 6 cannot produce -1 modulo 210
    unless the base was already -1. -/
theorem base_mod210_of_pow {b e : Nat} (he : 0 < e)
    (h2 : e % 2 ≠ 0) (h3 : e % 3 ≠ 0) (hpow : b ^ e % 210 = 209) :
    b % 210 = 209 := by
  have hperiod : b ^ (12 + 1) % 210 = b % 210 := by
    rw [Nat.pow_mod]
    exact mod210_period_table ⟨b % 210, Nat.mod_lt _ (by decide)⟩
  have hr := pow_reduce_mod hperiod he
  have hsmall : (b % 210) ^ ((e - 1) % 12 + 1) % 210 = 209 := by
    rw [← Nat.pow_mod, ← hr, hpow]
  apply mod210_root_table ⟨b % 210, Nat.mod_lt _ (by decide)⟩
      ⟨(e - 1) % 12, Nat.mod_lt _ (by decide)⟩ _ _ hsmall
  · dsimp
    omega
  · dsimp
    omega

theorem perfect_power_base_mod210 {n b e : Nat} (hn : 7 ≤ n)
    (hb : 1 < b) (he : 1 < e) (hab : a n = b ^ e) : b % 210 = 209 := by
  have hg : Nat.gcd e (fact (n - 1)) = 1 := by
    have hpos : 0 < Nat.gcd e (fact (n - 1)) :=
      Nat.gcd_pos_of_pos_right e (fact_pos (n - 1))
    by_cases h : Nat.gcd e (fact (n - 1)) = 1
    · exact h
    · exact (not_eth_power_of_pos_gcd hn he (by omega) ⟨b, hb, hab⟩).elim
  have h2 : e % 2 ≠ 0 := by
    intro h
    have hd : 2 ∣ Nat.gcd e (fact (n - 1)) := Nat.dvd_gcd
      (Nat.dvd_of_mod_eq_zero h) (dvd_fact_of_le (by decide) (by omega))
    rw [hg] at hd
    have := Nat.le_of_dvd (by decide : 0 < 1) hd
    omega
  have h3 : e % 3 ≠ 0 := by
    intro h
    have hd : 3 ∣ Nat.gcd e (fact (n - 1)) := Nat.dvd_gcd
      (Nat.dvd_of_mod_eq_zero h) (dvd_fact_of_le (by decide) (by omega))
    rw [hg] at hd
    have := Nat.le_of_dvd (by decide : 0 < 1) hd
    omega
  exact base_mod210_of_pow (by omega) h2 h3 (hab ▸ a_mod210 hn)

theorem perfect_power_base_ge209 {n b e : Nat} (hn : 7 ≤ n)
    (hb : 1 < b) (he : 1 < e) (hab : a n = b ^ e) : 209 ≤ b := by
  have hm := perfect_power_base_mod210 hn hb he hab
  have := Nat.mod_le b 210
  omega

/-- The new base restriction reduces the exponent bound from about 2K/3
    to K/7, where K=(n-1)!. -/
theorem perfect_power_exp_bound {n b e : Nat} (hn : 7 ≤ n)
    (hb : 1 < b) (he : 1 < e) (hab : a n = b ^ e) :
    7 * e ≤ fact (n - 1) := by
  have hbase := perfect_power_base_ge209 hn hb he hab
  have hpow : 2 ^ (7 * e) ≤ b ^ e := by
    rw [Nat.pow_mul]
    exact Nat.pow_le_pow_left (by omega) e
  have hlt : 2 ^ (7 * e) < 2 ^ (fact (n - 1) + 1) :=
    Nat.lt_of_le_of_lt (hab ▸ hpow) (a_lt_two_pow_succ hn)
  have := (Nat.pow_lt_pow_iff_right (by decide : 1 < 2)).mp hlt
  omega

theorem not_perfect_power_of_coprime_certificate {n : Nat} (hn : 7 ≤ n)
    (hc : checkCoprimeFrom (a n) n (fact (n - 1) / 7 + 1 - n)
      (fact (n - 1)) = true) : ¬ IsPerfectPower (a n) := by
  intro hp
  obtain ⟨b, e, hb, he, hg, hab⟩ := perfect_power_remaining hn hp
  have he' : 1 < e := by omega
  have hb' : 1 < b := by omega
  have hbound := perfect_power_exp_bound hn hb' he' hab
  have hgap := checkCoprimeFrom_spec (a n) n (fact (n - 1) / 7 + 1 - n)
    (fact (n - 1)) hc e he (by omega) hg
  exact not_eq_pow_of_rootGapDyadic hgap hab

theorem a_8_not_perfect_power : ¬ IsPerfectPower (a 8) := by
  apply a_not_perfect_power_of_mod_certificate (p := 733) (by decide)
  · apply primeCert_of_trial (t := 27) (by decide) (by decide); decide
  · decide +kernel
  · decide +kernel

theorem a_9_not_perfect_power : ¬ IsPerfectPower (a 9) := by
  apply a_not_perfect_power_of_mod_certificate (p := 113) (by decide)
  · apply primeCert_of_trial (t := 10) (by decide) (by decide); decide
  · decide +kernel
  · decide +kernel

theorem not_perfect_power_five_through_eleven {n : Nat} (hn : 5 ≤ n) (hn' : n ≤ 11) :
    ¬ IsPerfectPower (a n) := by
  have : n = 5 ∨ n = 6 ∨ n = 7 ∨ n = 8 ∨ n = 9 ∨ n = 10 ∨ n = 11 := by omega
  rcases this with h | h | h | h | h | h | h
  · subst n
    apply a_not_perfect_power_of_mod_certificate (p := 23) (by decide)
    · apply primeCert_of_trial (t := 4) (by decide) (by decide); decide
    · decide +kernel
    · decide +kernel
  · subst n
    apply a_not_perfect_power_of_mod_certificate (p := 661) (by decide)
    · apply primeCert_of_trial (t := 25) (by decide) (by decide); decide
    · decide +kernel
    · decide +kernel
  · subst n; exact a_7_not_perfect_power
  · subst n; exact a_8_not_perfect_power
  · subst n; exact a_9_not_perfect_power
  · subst n; exact a_10_not_perfect_power
  · subst n; exact a_11_not_perfect_power

/-- This is a reduction of the open question, not its resolution. -/
theorem officialConjecture_iff_remaining_mod210 :
    officialConjecture ↔ ∃ n b e : Nat,
      12 ≤ n ∧ 209 ≤ b ∧ b % 210 = 209 ∧ n ≤ e ∧
      7 * e ≤ fact (n - 1) ∧ Nat.gcd e (fact (n - 1)) = 1 ∧ a n = b ^ e := by
  constructor
  · rintro ⟨n, hn, hp⟩
    have hn12 : 12 ≤ n := by
      by_cases h : n ≤ 11
      · exact (not_perfect_power_five_through_eleven (by omega) h hp).elim
      · omega
    obtain ⟨b, e, hb, he, hg, hab⟩ := perfect_power_remaining (by omega) hp
    exact ⟨n, b, e, hn12,
      perfect_power_base_ge209 (by omega) (by omega) (by omega) hab,
      perfect_power_base_mod210 (by omega) (by omega) (by omega) hab,
      he, perfect_power_exp_bound (by omega) (by omega) (by omega) hab, hg, hab⟩
  · rintro ⟨n, b, e, hn, hb, _, he, _, _, hab⟩
    exact ⟨n, by omega, b, e, by omega, by omega, hab⟩

end LeanA113258
