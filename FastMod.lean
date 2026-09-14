import LeanA113258.FermatCong

namespace LeanA113258

/-! Fast factorial residues and prime-modulus exponent reduction. -/

/-- Factorial modulo `m`, keeping every recursive intermediate reduced. -/
def factMod : Nat → Nat → Nat
  | 0, m => 1 % m
  | n + 1, m => factMod n m * ((n + 1) % m) % m

theorem factMod_eq (n m : Nat) : factMod n m = fact n % m := by
  induction n with
  | zero => simp [factMod, fact]
  | succ n ih =>
    calc
      factMod (n + 1) m = (factMod n m * ((n + 1) % m)) % m := rfl
      _ = (fact n % m * ((n + 1) % m)) % m := by rw [ih]
      _ = (fact n * (n + 1)) % m := by
        exact (Nat.mul_mod _ _ _).symm
      _ = fact (n + 1) % m := by rw [fact_succ]

/-- Fermat's theorem makes the exponent periodic modulo `p - 1`. -/
theorem pow_mod_eq_pow_mod_reduced {p b e : Nat}
    (hp : 1 < p) (hc : primeCert p) (hb : b % p ≠ 0) :
    b ^ e % p = b ^ (e % (p - 1)) % p := by
  have hpm : 0 < p - 1 := by omega
  have hdecomp : e = (p - 1) * (e / (p - 1)) + e % (p - 1) := by
    exact (Nat.div_add_mod e (p - 1)).symm
  rw [hdecomp, Nat.pow_add, Nat.mul_mod,
    pow_mod_one_of_mul hp hc hb]
  simp

/-- A modular power whose base and exponent have already been reduced. -/
def powModResidue (base exponent p : Nat) : Nat :=
  if base = 0 then 0 else powModCert base exponent p

theorem powModResidue_eq {b e p : Nat}
    (hp : 1 < p) (hc : primeCert p) (he : 0 < e) :
    powModResidue (b % p) (e % (p - 1)) p = b ^ e % p := by
  by_cases hb : b % p = 0
  · simp [powModResidue, hb, Nat.pow_mod, Nat.zero_pow he, Nat.zero_mod]
  · simp only [powModResidue, hb]
    calc
      powModCert (b % p) (e % (p - 1)) p =
          (b % p) ^ (e % (p - 1)) % p := powModCert_eq _ _ _
      _ = b ^ (e % (p - 1)) % p := (Nat.pow_mod _ _ _).symm
      _ = b ^ e % p := (pow_mod_eq_pow_mod_reduced hp hc hb).symm

/-- A certificate evaluator for `a n` that uses only small modular exponents. -/
def aModPrimeReduced (n p : Nat) : Nat :=
  sumRange n (fun i =>
    powModResidue (factMod (i + 1) p) (factMod (n - i) (p - 1)) p) % p

theorem aModPrimeReduced_eq {n p : Nat}
    (hp : 1 < p) (hc : primeCert p) :
    aModPrimeReduced n p = a n % p := by
  have hterms : ∀ i,
      powModResidue (factMod (i + 1) p) (factMod (n - i) (p - 1)) p =
        (fact (i + 1) ^ fact (n - i)) % p := by
    intro i
    rw [factMod_eq (i + 1) p, factMod_eq (n - i) (p - 1)]
    exact powModResidue_eq hp hc (fact_pos (n - i))
  calc
    aModPrimeReduced n p =
        sumRange n (fun i =>
          powModResidue (factMod (i + 1) p) (factMod (n - i) (p - 1)) p) % p := rfl
    _ = sumRange n (fun i => (fact (i + 1) ^ fact (n - i)) % p) % p := by
      congr 1
      apply congrArg (sumRange n)
      funext i
      exact hterms i
    _ = sumRange n (fun i => fact (i + 1) ^ fact (n - i)) % p :=
      sumRange_mod_terms n p _
    _ = a n % p := rfl

#print axioms factMod_eq
#print axioms pow_mod_eq_pow_mod_reduced
#print axioms powModResidue_eq
#print axioms aModPrimeReduced_eq

end LeanA113258
