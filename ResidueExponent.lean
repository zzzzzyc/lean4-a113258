import LeanA113258.Fermat

namespace LeanA113258

/-!
  A modular certificate excludes an exponent when the target is itself a
  perfect power: raising the target to `t` would give a Fermat exponent.
-/

theorem not_pow_of_powModCert_ne_one {N p e t : Nat}
    (hp : 1 < p) (hc : primeCert p) (he : 0 < e)
    (heq : p - 1 = e * t) (hN : N % p ≠ 0)
    (hcert : powModCert (N % p) t p ≠ 1) :
    ∀ b : Nat, N ≠ b ^ e := by
  intro b hpow
  have hb : b % p ≠ 0 := by
    intro hb0
    apply hN
    rw [hpow, Nat.pow_mod, hb0, Nat.zero_pow he, Nat.zero_mod]
  have hforced : powModCert (N % p) t p = 1 := by
    calc
      powModCert (N % p) t p = (N % p) ^ t % p := powModCert_eq _ _ _
      _ = N ^ t % p := (Nat.pow_mod _ _ _).symm
      _ = (b ^ e) ^ t % p := by rw [hpow]
      _ = b ^ (e * t) % p := by rw [Nat.pow_mul]
      _ = b ^ (p - 1) % p := by rw [← heq]
      _ = 1 := fermat_coprime hp hc hb
  exact hcert hforced

/-- The same modular-power certificate, expressed using `aModCert`. -/
theorem a_not_pow_of_mod_certificate {n p e t : Nat}
    (hp : 1 < p) (hc : primeCert p) (he : 0 < e)
    (heq : p - 1 = e * t)
    (hN : aModCert n p ≠ 0)
    (hcert : powModCert (aModCert n p) t p ≠ 1) :
    ∀ b : Nat, a n ≠ b ^ e := by
  apply not_pow_of_powModCert_ne_one hp hc he heq
  · simpa only [aModCert_eq] using hN
  · simpa only [aModCert_eq] using hcert

#print axioms not_pow_of_powModCert_ne_one
#print axioms a_not_pow_of_mod_certificate

end LeanA113258
