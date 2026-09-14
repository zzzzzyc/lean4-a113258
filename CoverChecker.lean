import ResidueExponent
import FastModTable

namespace LeanA113258.CoverChecker

structure ModCertRow where
  n : Nat
  e : Nat
  k : Nat
  p : Nat
  residue : Nat
  result : Nat
  deriving DecidableEq, Repr

/-- Payload for a block with one shared modulus p and one shared prime proof. -/
structure ModCertPayload where
  n : Nat
  e : Nat
  k : Nat
  residue : Nat
  result : Nat
  deriving DecidableEq, Repr

/-- A certificate row paired with its shared, pre-proved primality witness. -/
structure CertifiedModCertRow where
  row : ModCertRow
  prime : primeCert row.p

def payloadRow (p : Nat) (d : ModCertPayload) : ModCertRow :=
  ⟨d.n, d.e, d.k, p, d.residue, d.result⟩

/-- The finite Boolean checker for a modular non-perfect-power row. -/
def rowCheck (r : ModCertRow) : Bool :=
  decide (0 < r.e ∧ 1 < r.p ∧ r.p - 1 = r.e * (2 * r.k) ∧
    r.residue ≠ 0 ∧ powModCert r.residue (2 * r.k) r.p = r.result ∧
    r.result ≠ 1 ∧ aModPrimeTable r.n r.p = r.residue)

def payloadCheck (p : Nat) (d : ModCertPayload) : Bool :=
  rowCheck (payloadRow p d)

/-- A checked row soundly excludes the advertised exponent. -/
theorem row_sound (r : ModCertRow) (hc : rowCheck r = true)
    (hp : primeCert r.p) : ∀ b : Nat, a r.n ≠ b ^ r.e := by
  have hdata := of_decide_eq_true hc
  rcases hdata with ⟨he, hp_gt, hp_factor, hres_ne, hpow, hpow_ne, htable⟩
  have hcert : aModCert r.n r.p = r.residue := by
    calc
      aModCert r.n r.p = a r.n % r.p := aModCert_eq r.n r.p
      _ = aModPrimeTable r.n r.p := (aModPrimeTable_eq hp_gt hp).symm
      _ = r.residue := htable
  apply a_not_pow_of_mod_certificate hp_gt hp he hp_factor
  · rw [hcert]
    exact hres_ne
  · rw [hcert, hpow]
    exact hpow_ne

/-- Soundness for a row stored under a shared modulus/prime certificate. -/
theorem payload_sound (p : Nat) (d : ModCertPayload)
    (hc : payloadCheck p d = true) (hp : primeCert p) :
    ∀ b : Nat, a d.n ≠ b ^ d.e := by
  exact row_sound (payloadRow p d) hc hp

theorem certified_row_sound (r : CertifiedModCertRow)
    (hc : rowCheck r.row = true) :
    ∀ b : Nat, a r.row.n ≠ b ^ r.row.e :=
  row_sound r.row hc r.prime

#print axioms row_sound
#print axioms payload_sound
#print axioms certified_row_sound

end LeanA113258.CoverChecker
