import FastModTable
import Mathlib.NumberTheory.PowModTotient

namespace LeanA113258

set_option maxRecDepth 100000
set_option maxHeartbeats 8000000

/-! Fast certificate evaluation modulo a prime square. -/

def powModSquareResidue (base exponent index p : Nat) : Nat :=
  if base % p = 0 then
    if index = 1 then base else 0
  else
    powModCert base exponent (p * p)

def aModSquareTableAux (n p : Nat) (baseTable expTable : Array Nat) : Nat :=
  sumRange n (fun i =>
    powModSquareResidue baseTable[i + 1]! expTable[n - i]! (n - i) p) % (p * p)

def aModSquareTable (n p : Nat) : Nat :=
  let baseTable := factModTable n (p * p)
  let expTable := factModTable n (p * (p - 1))
  aModSquareTableAux n p baseTable expTable

theorem totient_prime_square {p : Nat} (hp : p.Prime) :
    Nat.totient (p * p) = p * (p - 1) := by
  calc
    Nat.totient (p * p) = Nat.totient (p ^ (1 + 1)) := by simp [pow_succ]
    _ = p ^ 1 * (p - 1) := Nat.totient_prime_pow_succ hp 1
    _ = p * (p - 1) := by simp

theorem pow_mod_square_residue_spec {p base exponent index originalBase : Nat}
    (hp : p.Prime)
    (hindexPos : 0 < index)
    (hbase : base = originalBase % (p * p))
    (hexponent : exponent = fact index % (p * (p - 1)))
    (hbaseMod : base % p = originalBase % p) :
    powModSquareResidue base exponent index p =
      originalBase ^ fact index % (p * p) := by
  by_cases hnonunit : base % p = 0
  · by_cases hlast : index = 1
    · simp only [powModSquareResidue, if_pos hnonunit, if_pos hlast]
      rw [hbase, hlast]
      simp [fact]
    · have hindex : 2 ≤ index := by omega
      have hexpge : 2 ≤ fact index := by
        have hmono : fact 2 ≤ fact index := fact_le_of_le hindex
        norm_num [fact] at hmono ⊢
        exact le_trans (by decide) hmono
      have hdivBase : p ∣ originalBase := by
        apply Nat.dvd_of_mod_eq_zero
        rw [← hbaseMod]
        exact hnonunit
      have hpp : p * p ∣ originalBase ^ fact index := by
        obtain ⟨c, hc⟩ := hdivBase
        rw [hc, Nat.mul_pow]
        have hpower : p * p ∣ p ^ fact index := by
          simpa [pow_two] using (Nat.pow_dvd_pow p hexpge)
        exact dvd_trans hpower (dvd_mul_right _ _)
      have hzero : originalBase ^ fact index % (p * p) = 0 :=
        Nat.mod_eq_zero_of_dvd hpp
      simp [powModSquareResidue, hnonunit, hlast, hzero]
  · have hnotdvd : ¬ p ∣ originalBase := by
      intro h
      have hz : originalBase % p = 0 := Nat.mod_eq_zero_of_dvd h
      rw [← hbaseMod] at hz
      exact hnonunit hz
    have hcop : originalBase.Coprime (p * p) := by
      simpa [pow_two] using hp.coprime_pow_of_not_dvd (m := 2) hnotdvd
    have hmod := Nat.pow_totient_mod (n := p * p) (k := fact index)
        (by have := hp.two_le; nlinarith) hcop
    rw [totient_prime_square hp] at hmod
    calc
      powModSquareResidue base exponent index p =
          powModCert base exponent (p * p) := by
            simp [powModSquareResidue, hnonunit]
      _ = base ^ exponent % (p * p) := powModCert_eq _ _ _
      _ = originalBase ^ (fact index % (p * (p - 1))) % (p * p) := by
        rw [hbase, hexponent]
        exact (Nat.pow_mod _ _ _).symm
      _ = originalBase ^ fact index % (p * p) := hmod.symm

theorem aModSquareTableAux_eq {n p : Nat} (hp : p.Prime)
    {baseTable expTable : Array Nat}
    (hbase : ∀ k, k ≤ n → baseTable[k]! = fact k % (p * p))
    (hexp : ∀ k, k ≤ n → expTable[k]! = fact k % (p * (p - 1))) :
    aModSquareTableAux n p baseTable expTable = a n % (p * p) := by
  have hterms : ∀ i, i < n →
      powModSquareResidue baseTable[i + 1]! expTable[n - i]! (n - i) p =
        fact (i + 1) ^ fact (n - i) % (p * p) := by
    intro i hi
    have hb := hbase (i + 1) (by omega)
    have he := hexp (n - i) (Nat.sub_le _ _)
    have hm : baseTable[i + 1]! % p = fact (i + 1) % p := by
      rw [hb]
      exact Nat.mod_mod_of_dvd _ ⟨p, by ring⟩
    have hindex : 0 < n - i := by omega
    exact pow_mod_square_residue_spec hp hindex hb he hm
  calc
    aModSquareTableAux n p baseTable expTable =
        sumRange n (fun i => fact (i + 1) ^ fact (n - i) % (p * p)) % (p * p) := by
          unfold aModSquareTableAux
          congr 1
          apply sumRange_congr
          exact hterms
    _ = sumRange n (fun i => fact (i + 1) ^ fact (n - i)) % (p * p) :=
      sumRange_mod_terms n (p * p) _
    _ = a n % (p * p) := rfl

theorem aModSquareTable_eq {n p : Nat} (hp : p.Prime) :
    aModSquareTable n p = a n % (p * p) := by
  unfold aModSquareTable
  apply aModSquareTableAux_eq hp
  · intro k hk
    exact factModTable_getBang hk
  · intro k hk
    exact factModTable_getBang hk

theorem primeCert_of_natPrime {p : Nat} (hp : p.Prime) : primeCert p := by
  intro r hr
  have hcop : p.Coprime r.val := Nat.coprime_of_lt_prime hr r.isLt hp
  exact (Nat.coprime_iff_gcd_eq_one.mp (Nat.coprime_comm.mp hcop))

theorem a_not_perfect_power_of_square_table_certificate {n p residue : Nat}
    (hp : p.Prime) (hres : aModSquareTable n p = residue)
    (hdiv : p ∣ residue) (hnonzero : residue ≠ 0) :
    ¬ IsPerfectPower (a n) := by
  have hpgt : 1 < p := hp.one_lt
  have hsqdiv : p ∣ p * p := ⟨p, by ring⟩
  have hmodp : a n % p = 0 := by
    calc
      a n % p = (a n % (p * p)) % p := (Nat.mod_mod_of_dvd (a n) hsqdiv).symm
      _ = residue % p := by rw [← aModSquareTable_eq hp, hres]
      _ = 0 := Nat.mod_eq_zero_of_dvd hdiv
  have hmodp2 : a n % (p * p) ≠ 0 := by
    rw [← aModSquareTable_eq hp, hres]
    exact hnonzero
  exact not_perfect_power_of_prime_square hpgt (primeCert_of_natPrime hp) hmodp hmodp2

/-- Boolean row check for `(n, p, a(n) mod p^2)` factor certificates. -/
def factorCoverCheck (row : Nat × Nat × Nat) : Bool :=
  let n := row.1
  let p := row.2.1
  let residue := row.2.2
  (decide p.Prime && decide (aModSquareTable n p = residue)) &&
    (decide (p ∣ residue) && decide (residue ≠ 0))

theorem factorCoverCheck_sound {row : Nat × Nat × Nat}
    (h : factorCoverCheck row = true) :
    ¬ IsPerfectPower (a row.1) := by
  rcases row with ⟨n, p, residue⟩
  simp only [factorCoverCheck, Bool.and_eq_true] at h
  rcases h with ⟨⟨hp, hres⟩, ⟨hdiv, hnonzero⟩⟩
  exact a_not_perfect_power_of_square_table_certificate
    (of_decide_eq_true hp) (of_decide_eq_true hres)
    (of_decide_eq_true hdiv) (of_decide_eq_true hnonzero)

#print axioms pow_mod_square_residue_spec
#print axioms aModSquareTable_eq
#print axioms a_not_perfect_power_of_square_table_certificate
#print axioms factorCoverCheck_sound

end LeanA113258
