import LeanA113258.FermatCong
import LeanA113258.TwoAdic
import LeanA113258.CoprimeLarge
import LeanA113258.ProofProgress

namespace LeanA113258

/-!
  Uniform remaining-window package.

  Everything below holds for **every** `n` in the stated range. None of it
  proves `not_eth_power_of_coprime_large`, and this file does **not**
  declare `officialConjecture_false`.
-/

/-- Small certified primes used by the uniform Fermat congruence. -/
theorem primeCert_three : primeCert 3 := by
  apply primeCert_of_trial (t := 1) (by decide) (by decide); decide

theorem primeCert_five : primeCert 5 := by
  apply primeCert_of_trial (t := 2) (by decide) (by decide); decide

theorem primeCert_seven : primeCert 7 := by
  apply primeCert_of_trial (t := 2) (by decide) (by decide); decide

/-- For every `n ≥ 3`, `a n ≡ -1 (mod 3)`. -/
theorem a_mod_three {n : Nat} (hn : 3 ≤ n) : a n % 3 = 2 :=
  a_mod_prime (n := n) (p := 3) (by decide) primeCert_three (by omega)

/-- For every `n ≥ 7`, `a n ≡ -1 (mod 5)`. -/
theorem a_mod_five {n : Nat} (hn : 7 ≤ n) : a n % 5 = 4 :=
  a_mod_prime (n := n) (p := 5) (by decide) primeCert_five (by omega)

/-- For every `n ≥ 11`, `a n ≡ -1 (mod 7)`. -/
theorem a_mod_seven {n : Nat} (hn : 11 ≤ n) : a n % 7 = 6 :=
  a_mod_prime (n := n) (p := 7) (by decide) primeCert_seven (by omega)

/--
If `a n = b ^ e` sits in the remaining coprime-large window, then the
base is odd, the exponent is odd, `v₂(b-1)=v₂(n!)`, the base is `-1`
modulo every certified prime with `2p-3 ≤ n`, and `b` lies in a unique
odd class inside a dyadic slot strictly below `2^{(n-2)!}`.
-/
theorem remaining_uniform
    {n b e : Nat} (hn : 7 ≤ n) (hb : 3 ≤ b) (he : n ≤ e)
    (hg : Nat.gcd e (fact (n - 1)) = 1)
    (hab : a n = b ^ e) :
    b % 2 = 1 ∧
      e % 2 = 1 ∧
      val2 (b - 1) = val2 (fact n) ∧
      (∀ p, 1 < p → primeCert p → 2 * p - 3 ≤ n → b % p = p - 1) ∧
      (let q := fact (n - 1) / e; 2 ^ q < b ∧ b < 2 ^ (q + 1)) ∧
      b < 2 ^ fact (n - 2) ∧
      b ^ e % 2 ^ fact (n - 2) = rho n := by
  have hw := remaining_window hn hb he hg hab
  have hbodd := hw.1
  have heodd := hw.2.1
  have hval : val2 (b - 1) = val2 (fact n) :=
    val2_base_sub_one_of_pow (by omega) heodd hbodd hab
  have hfermat :
      ∀ p, 1 < p → primeCert p → 2 * p - 3 ≤ n → b % p = p - 1 := by
    intro p hp hc hpn
    exact remaining_base_mod_prime hn hp hc hpn (by omega) (by omega) hg hab
  exact ⟨hbodd, heodd, hval, hfermat, hw.2.2.1, hw.2.2.2.1, hw.2.2.2.2⟩

/-- Strengthened reduction of the open question; still not a solution. -/
theorem officialConjecture_iff_remaining_uniform :
    officialConjecture ↔ ∃ n b e : Nat,
      12 ≤ n ∧ 209 ≤ b ∧ b % 210 = 209 ∧ n ≤ e ∧
      7 * e ≤ fact (n - 1) ∧ Nat.gcd e (fact (n - 1)) = 1 ∧
      a n = b ^ e ∧
      b % 2 = 1 ∧ e % 2 = 1 ∧
      val2 (b - 1) = val2 (fact n) ∧
      (∀ p, 1 < p → primeCert p → 2 * p - 3 ≤ n → b % p = p - 1) ∧
      (let q := fact (n - 1) / e; 2 ^ q < b ∧ b < 2 ^ (q + 1)) ∧
      b < 2 ^ fact (n - 2) := by
  constructor
  · intro h
    obtain ⟨n, b, e, hn, hb, h210, he, h7, hg, hab⟩ :=
      officialConjecture_iff_remaining_mod210.mp h
    have hu := remaining_uniform (n := n) (b := b) (e := e)
      (by omega) (by omega) he hg hab
    exact ⟨n, b, e, hn, hb, h210, he, h7, hg, hab,
      hu.1, hu.2.1, hu.2.2.1, hu.2.2.2.1, hu.2.2.2.2.1, hu.2.2.2.2.2.1⟩
  · rintro ⟨n, b, e, hn, hb, h210, he, h7, hg, hab, _hodd, _heodd, _hv, _hf, _hd, _hlt⟩
    exact officialConjecture_iff_remaining_mod210.mpr
      ⟨n, b, e, hn, hb, h210, he, h7, hg, hab⟩

end LeanA113258
