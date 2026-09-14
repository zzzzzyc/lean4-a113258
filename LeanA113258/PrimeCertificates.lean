import LeanA113258.Remaining

namespace LeanA113258

set_option maxRecDepth 100000
set_option maxHeartbeats 8000000

/-- Binary modular exponentiation; no huge integer power is constructed. -/
def powModCert (b e m : Nat) : Nat :=
  if he : e = 0 then 1 % m
  else
    let r := powModCert b (e / 2) m
    if e % 2 = 0 then r * r % m else (r * r % m) * (b % m) % m
termination_by e
decreasing_by omega

theorem powModCert_eq (b e m : Nat) : powModCert b e m = b ^ e % m := by
  induction e using Nat.strongRecOn with
  | ind e ih =>
    rw [powModCert]
    by_cases he : e = 0
    · simp [he]
    · simp only [he, ↓reduceDIte]
      rw [ih (e / 2) (by omega)]
      by_cases hpar : e % 2 = 0
      · rw [if_pos hpar, ← Nat.mul_mod, ← Nat.pow_add]
        have heq : e / 2 + e / 2 = e := by omega
        rw [heq]
      · rw [if_neg hpar, ← Nat.mul_mod (b ^ (e / 2)) (b ^ (e / 2)) m,
          ← Nat.mul_mod, ← Nat.pow_add,
          ← Nat.pow_succ]
        have heq : e / 2 + e / 2 + 1 = e := by omega
        change b ^ (e / 2 + e / 2 + 1) % m = b ^ e % m
        rw [heq]

def aModCert (n m : Nat) : Nat :=
  sumRange n (fun i => powModCert (fact (i + 1)) (fact (n - i)) m) % m

theorem sumRange_mod_terms (n m : Nat) (f : Nat → Nat) :
    sumRange n (fun i => f i % m) % m = sumRange n f % m := by
  induction n with
  | zero => rfl
  | succ n ih =>
    simp only [sumRange_succ]
    rw [Nat.add_mod, Nat.mod_mod, ih, ← Nat.add_mod]

theorem aModCert_eq (n m : Nat) : aModCert n m = a n % m := by
  unfold aModCert
  simp only [powModCert_eq]
  exact sumRange_mod_terms n m _

/-- A finite primality certificate: every nonzero residue modulo p is coprime to p. -/
def primeCert (p : Nat) : Prop :=
  ∀ r : Fin p, r.val ≠ 0 → Nat.gcd r.val p = 1

/-- Trial division only up to sqrt(p), with a proof of its sufficiency. -/
theorem primeCert_of_trial {p t : Nat} (hp : 1 < p)
    (hbound : p < (t + 1) * (t + 1))
    (htrial : ∀ d : Fin (t + 1), 2 ≤ d.val → p % d.val ≠ 0) : primeCert p := by
  intro r hr
  let g := Nat.gcd r.val p
  have hgpos : 0 < g := Nat.gcd_pos_of_pos_right r.val (by omega)
  have hgr : g ≤ r.val := Nat.gcd_le_left p (by omega)
  have hgp : g ∣ p := Nat.gcd_dvd_right r.val p
  by_cases hg1 : g = 1
  · exact hg1
  · have hg2 : 2 ≤ g := by omega
    obtain ⟨k, hk⟩ := hgp
    have hk2 : 2 ≤ k := by
      cases k with
      | zero => simp at hk; omega
      | succ k => cases k with
        | zero => simp at hk; have := r.isLt; omega
        | succ k => omega
    have hkle : k ≤ t ∨ g ≤ t := by
      by_cases hk' : k ≤ t
      · exact Or.inl hk'
      · right
        by_cases hg' : g ≤ t
        · exact hg'
        · have hmul : (t + 1) * (t + 1) ≤ g * k :=
            Nat.mul_le_mul (by omega) (by omega)
          omega
    cases hkle with
    | inl hkt =>
      have hd : k ∣ p := ⟨g, by rw [hk, Nat.mul_comm]⟩
      exact (htrial ⟨k, by omega⟩ hk2 (Nat.mod_eq_zero_of_dvd hd)).elim
    | inr hgt =>
      have hd : g ∣ p := ⟨k, hk⟩
      exact (htrial ⟨g, by omega⟩ hg2 (Nat.mod_eq_zero_of_dvd hd)).elim

theorem prime_dvd_base_of_dvd_pow {p b e : Nat} (hp : 1 < p)
    (hc : primeCert p) (hd : p ∣ b ^ e) : p ∣ b := by
  by_cases hz : b % p = 0
  · exact Nat.dvd_of_mod_eq_zero hz
  · have hg : Nat.gcd b p = 1 := by
      rw [Nat.gcd_comm, Nat.gcd_rec]
      exact hc ⟨b % p, Nat.mod_lt _ (by omega)⟩ hz
    have hpow : Nat.gcd (b ^ e) p = 1 := Nat.gcd_pow_left_of_gcd_eq_one hg
    have hpd : p ∣ Nat.gcd (b ^ e) p := Nat.dvd_gcd hd (Nat.dvd_refl p)
    rw [hpow] at hpd
    have := Nat.le_of_dvd (by decide : 0 < 1) hpd
    omega

/-- A prime occurring to exponent exactly one rules out every perfect power. -/
theorem not_perfect_power_of_prime_square {N p : Nat} (hp : 1 < p)
    (hc : primeCert p) (hd : N % p = 0) (hnd : N % (p * p) ≠ 0) :
    ¬ IsPerfectPower N := by
  rintro ⟨b, e, _, he, hN⟩
  have hpdiv : p ∣ b ^ e := hN ▸ Nat.dvd_of_mod_eq_zero hd
  obtain ⟨t, ht⟩ := prime_dvd_base_of_dvd_pow hp hc hpdiv
  have heq : e = 2 + (e - 2) := by omega
  have hdiv : p * p ∣ b ^ e := by
    rw [ht, Nat.mul_pow, heq, Nat.pow_add, Nat.pow_two]
    exact Nat.dvd_mul_right_of_dvd (Nat.dvd_mul_right (p * p) _) _
  have hz : N % (p * p) = 0 := hN ▸ Nat.mod_eq_zero_of_dvd hdiv
  exact hnd hz

theorem a_not_perfect_power_of_mod_certificate {n p : Nat} (hp : 1 < p)
    (hc : primeCert p) (hd : aModCert n p = 0)
    (hnd : aModCert n (p * p) ≠ 0) : ¬ IsPerfectPower (a n) := by
  apply not_perfect_power_of_prime_square hp hc
  · simpa only [aModCert_eq] using hd
  · simpa only [aModCert_eq] using hnd

theorem a_10_not_perfect_power : ¬ IsPerfectPower (a 10) := by
  apply a_not_perfect_power_of_mod_certificate (p := 11069) (by decide)
  · apply primeCert_of_trial (t := 105) (by decide) (by decide); decide
  · decide +kernel
  · decide +kernel

theorem a_11_not_perfect_power : ¬ IsPerfectPower (a 11) := by
  apply a_not_perfect_power_of_mod_certificate (p := 4583) (by decide)
  · apply primeCert_of_trial (t := 67) (by decide) (by decide); decide
  · decide +kernel
  · decide +kernel

end LeanA113258
