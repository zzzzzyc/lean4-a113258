import LeanA113258.PrimeCertificates

namespace LeanA113258

/-!
  Uniform modular arithmetic for every `n`.
  If `p` is certified prime and `2 * p - 3 ≤ n`, then `a n ≡ -1 (mod p)`.
-/

def binom : Nat → Nat → Nat
  | _, 0 => 1
  | 0, _ + 1 => 0
  | n + 1, k + 1 => binom n k + binom n (k + 1)

theorem binom_zero (n : Nat) : binom n 0 = 1 := by
  cases n <;> rfl

theorem binom_succ_succ (n k : Nat) :
    binom (n + 1) (k + 1) = binom n k + binom n (k + 1) := rfl

theorem binom_eq_zero_of_lt : ∀ n k, n < k → binom n k = 0
  | 0, 0, h => by omega
  | 0, k + 1, _ => rfl
  | n + 1, 0, h => by omega
  | n + 1, k + 1, h => by
    rw [binom_succ_succ, binom_eq_zero_of_lt n k (by omega),
      binom_eq_zero_of_lt n (k + 1) (by omega)]

theorem binom_self : ∀ n, binom n n = 1
  | 0 => rfl
  | n + 1 => by
    rw [binom_succ_succ, binom_self n, binom_eq_zero_of_lt n (n + 1) (by omega)]

theorem binom_mul_fact : ∀ n k, k ≤ n →
    binom n k * fact k * fact (n - k) = fact n
  | 0, 0, _ => rfl
  | 0, k + 1, h => by omega
  | n + 1, 0, _ => by
    simp [binom_zero, fact_zero]
  | n + 1, k + 1, h => by
    have hk : k ≤ n := by omega
    cases Nat.lt_or_eq_of_le h with
    | inr heq =>
      have hk' : k = n := by omega
      subst hk'
      simp [Nat.sub_self, fact_zero, binom_self]
    | inl hlt =>
      have hk2 : k + 1 ≤ n := by omega
      have ih1 := binom_mul_fact n k hk
      have ih2 := binom_mul_fact n (k + 1) hk2
      have hs : n + 1 - (k + 1) = n - k := by omega
      have h1 :
          binom n k * fact (k + 1) * fact (n - k) = (k + 1) * fact n := by
        have hf : fact (k + 1) = fact k * (k + 1) := fact_succ k
        have rearr :
            binom n k * (fact k * (k + 1)) * fact (n - k) =
              (binom n k * fact k * fact (n - k)) * (k + 1) := by
          have hL : binom n k * (fact k * (k + 1)) =
              (binom n k * fact k) * (k + 1) := by
            rw [← Nat.mul_assoc]
          rw [hL, Nat.mul_assoc, Nat.mul_comm (k + 1), ← Nat.mul_assoc]
        rw [hf, rearr, ih1, Nat.mul_comm]
      have h2 :
          binom n (k + 1) * fact (k + 1) * fact (n - k) = (n - k) * fact n := by
        have hdecomp : fact (n - k) = fact (n - (k + 1)) * (n - k) := by
          have : n - k = n - (k + 1) + 1 := by omega
          rw [this, fact_succ, Nat.mul_comm]
        calc
          binom n (k + 1) * fact (k + 1) * fact (n - k)
              = binom n (k + 1) * fact (k + 1) * (fact (n - (k + 1)) * (n - k)) := by
                rw [hdecomp]
          _ = (binom n (k + 1) * fact (k + 1) * fact (n - (k + 1))) * (n - k) := by
                simp [Nat.mul_assoc]
          _ = fact n * (n - k) := by rw [ih2]
          _ = (n - k) * fact n := Nat.mul_comm _ _
      have hsum :
          (binom n k + binom n (k + 1)) * fact (k + 1) * fact (n - k) =
            fact (n + 1) := by
        rw [Nat.add_mul, Nat.add_mul, h1, h2]
        have : (k + 1) * fact n + (n - k) * fact n = (n + 1) * fact n := by
          rw [← Nat.add_mul]
          have : k + 1 + (n - k) = n + 1 := by omega
          rw [this]
        rw [this, fact_succ, Nat.mul_comm]
      simpa [binom_succ_succ, hs] using hsum

theorem sumRange_mul_left (n c : Nat) (f : Nat → Nat) :
    c * sumRange n f = sumRange n fun i => c * f i := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [sumRange_succ, sumRange_succ, Nat.mul_add, ih]

theorem sumRange_eq_of {n : Nat} {f g : Nat → Nat}
    (h : ∀ i, i < n → f i = g i) : sumRange n f = sumRange n g := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [sumRange_succ, sumRange_succ,
      ih (fun i hi => h i (Nat.lt_succ_of_le (Nat.le_of_lt hi))),
      h n (Nat.lt_succ_self n)]

theorem sumRange_tail (n : Nat) (f : Nat → Nat) :
    sumRange (n + 1) f = f 0 + sumRange n fun i => f (i + 1) := by
  induction n with
  | zero => simp [sumRange_succ, sumRange_zero]
  | succ n ih =>
    rw [sumRange_succ, ih, sumRange_succ, Nat.add_assoc]

theorem sumRange_add' (n : Nat) (f g : Nat → Nat) :
    sumRange n (fun i => f i + g i) = sumRange n f + sumRange n g := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [sumRange_succ, sumRange_succ, sumRange_succ, ih]
    omega

/-- `(x + 1) ^ n = Σ_{k = 0}^{n} C(n,k) x ^ k`. -/
theorem binomial_add_one (x : Nat) : ∀ n,
    (x + 1) ^ n = sumRange (n + 1) fun k => binom n k * x ^ k
  | 0 => by
    simp [sumRange_succ, sumRange_zero, binom_zero]
  | n + 1 => by
    have ih := binomial_add_one x n
    have hpow : (x + 1) ^ (n + 1) = (x + 1) * (x + 1) ^ n := by
      rw [Nat.pow_succ, Nat.mul_comm]
    rw [hpow, ih, Nat.add_mul, Nat.one_mul, sumRange_mul_left]
    have hx :
        sumRange (n + 1) (fun k => x * (binom n k * x ^ k)) =
          sumRange (n + 1) (fun k => binom n k * x ^ (k + 1)) :=
      sumRange_eq_of fun k _ => by
        calc
          x * (binom n k * x ^ k)
              = x * binom n k * x ^ k := by rw [← Nat.mul_assoc]
          _ = binom n k * x * x ^ k := by rw [Nat.mul_comm x]
          _ = binom n k * (x * x ^ k) := Nat.mul_assoc _ _ _
          _ = binom n k * (x ^ k * x) := by rw [Nat.mul_comm x]
          _ = binom n k * x ^ (k + 1) := by rw [Nat.pow_succ]
    rw [hx]
    have hRHS :
        sumRange (n + 2) (fun k => binom (n + 1) k * x ^ k) =
          1 + sumRange (n + 1) fun i => binom (n + 1) (i + 1) * x ^ (i + 1) := by
      rw [sumRange_tail]
      simp [binom_zero]
    have hpas :
        sumRange (n + 1) (fun i => binom (n + 1) (i + 1) * x ^ (i + 1)) =
          sumRange (n + 1) fun i =>
            (binom n i + binom n (i + 1)) * x ^ (i + 1) :=
      sumRange_eq_of fun i _ => by rw [binom_succ_succ]
    have hsplit :
        sumRange (n + 1) (fun i =>
            (binom n i + binom n (i + 1)) * x ^ (i + 1)) =
          sumRange (n + 1) (fun i => binom n i * x ^ (i + 1)) +
            sumRange (n + 1) (fun i => binom n (i + 1) * x ^ (i + 1)) := by
      rw [sumRange_eq_of (fun i _ => Nat.add_mul _ _ _), sumRange_add']
    have hf2 :
        sumRange (n + 1) (fun i => binom n (i + 1) * x ^ (i + 1)) =
          sumRange n fun i => binom n (i + 1) * x ^ (i + 1) := by
      rw [sumRange_succ, binom_eq_zero_of_lt n (n + 1) (by omega)]
      simp
    have horig :
        sumRange (n + 1) (fun k => binom n k * x ^ k) =
          1 + sumRange n fun i => binom n (i + 1) * x ^ (i + 1) := by
      rw [sumRange_tail]
      simp [binom_zero]
    calc
      sumRange (n + 1) (fun k => binom n k * x ^ (k + 1)) +
          sumRange (n + 1) (fun k => binom n k * x ^ k) =
          sumRange (n + 1) (fun k => binom n k * x ^ (k + 1)) +
            (1 + sumRange n fun i => binom n (i + 1) * x ^ (i + 1)) := by
            rw [horig]
      _ = 1 + (sumRange (n + 1) (fun k => binom n k * x ^ (k + 1)) +
            sumRange n fun i => binom n (i + 1) * x ^ (i + 1)) := by
            omega
      _ = 1 + (sumRange (n + 1) (fun i => binom n i * x ^ (i + 1)) +
            sumRange (n + 1) fun i => binom n (i + 1) * x ^ (i + 1)) := by
            rw [hf2]
      _ = 1 + sumRange (n + 1) fun i =>
            (binom n i + binom n (i + 1)) * x ^ (i + 1) := by
            rw [← hsplit]
      _ = 1 + sumRange (n + 1) fun i =>
            binom (n + 1) (i + 1) * x ^ (i + 1) := by
            rw [hpas]
      _ = sumRange (n + 2) fun k => binom (n + 1) k * x ^ k := by
            rw [hRHS]

/-! ### Interior binomial coefficients vanish modulo a prime -/

theorem fact_gcd_prime {p n : Nat} (_hp : 1 < p) (hc : primeCert p)
    (hn : n < p) : Nat.gcd (fact n) p = 1 := by
  induction n with
  | zero => simp
  | succ n ih =>
    have hcop : Nat.Coprime (n + 1) p :=
      hc ⟨n + 1, hn⟩ (Nat.succ_ne_zero n)
    rw [fact_succ]
    exact (Nat.coprime_mul_iff_left.2
      ⟨ih (Nat.lt_of_succ_lt hn), hcop⟩)

theorem prime_dvd_binom {p k : Nat} (hp : 1 < p) (hc : primeCert p)
    (hk0 : 0 < k) (hkp : k < p) : p ∣ binom p k := by
  have hmul := binom_mul_fact p k (Nat.le_of_lt hkp)
  have hfact : p ∣ fact p := by
    cases p with
    | zero => omega
    | succ p =>
      rw [fact_succ]
      exact Nat.dvd_mul_left (p + 1) (fact p)
  have hL : p ∣ binom p k * fact k * fact (p - k) := hmul ▸ hfact
  have hg1 : Nat.gcd (fact k) p = 1 := fact_gcd_prime hp hc hkp
  have hg2 : Nat.gcd (fact (p - k)) p = 1 := fact_gcd_prime hp hc (by omega)
  have h1 : p ∣ binom p k * fact k :=
    (show Nat.Coprime p (fact (p - k)) from by
        simpa [Nat.Coprime, Nat.gcd_comm] using hg2).dvd_of_dvd_mul_right
      (by simpa [Nat.mul_assoc] using hL)
  exact (show Nat.Coprime p (fact k) from by
      simpa [Nat.Coprime, Nat.gcd_comm] using hg1).dvd_of_dvd_mul_right h1

theorem sumRange_mod_zero {n m : Nat} {f : Nat → Nat}
    (h : ∀ i, i < n → f i % m = 0) : sumRange n f % m = 0 := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [sumRange_succ, Nat.add_mod, h n (Nat.lt_succ_self n),
      ih (fun i hi => h i (Nat.lt_succ_of_le (Nat.le_of_lt hi)))]
    simp

/-- Fermat: `(x + 1) ^ p ≡ x ^ p + 1 (mod p)`. -/
theorem fermat_succ_pow {p x : Nat} (hp : 1 < p) (hc : primeCert p) :
    (x + 1) ^ p % p = (x ^ p + 1) % p := by
  have hbin := binomial_add_one x p
  have h0 : binom p 0 * x ^ 0 = 1 := by simp [binom_zero]
  have hmid :
      sumRange (p - 1) (fun i => binom p (i + 1) * x ^ (i + 1)) % p = 0 := by
    refine sumRange_mod_zero (fun i hi => ?_)
    have hk0 : 0 < i + 1 := Nat.succ_pos _
    have hkp : i + 1 < p := by omega
    exact Nat.mod_eq_zero_of_dvd
      (Nat.dvd_mul_right_of_dvd (prime_dvd_binom hp hc hk0 hkp) _)
  have htail :
      sumRange (p + 1) (fun k => binom p k * x ^ k) =
        1 + (sumRange (p - 1) (fun i => binom p (i + 1) * x ^ (i + 1)) +
          x ^ p) := by
    have hsplit : p = Nat.succ (p - 1) := by omega
    rw [sumRange_tail, h0, hsplit, sumRange_succ]
    have hp' : p - 1 + 1 = p := by omega
    simp [hp', binom_self]
  rw [hbin, htail]
  have h1 : 1 % p = 1 := Nat.mod_eq_of_lt hp
  let mid := sumRange (p - 1) (fun i => binom p (i + 1) * x ^ (i + 1))
  have hA :
      (1 + (mid + x ^ p)) % p = (1 % p + (mid + x ^ p) % p) % p :=
    Nat.add_mod _ _ _
  have hB : (mid + x ^ p) % p = (mid % p + x ^ p % p) % p := Nat.add_mod _ _ _
  have hC : (1 + (mid + x ^ p)) % p = (1 + (0 + x ^ p % p) % p) % p := by
    rw [hA, h1, hB, hmid]
  have hD : (1 + (0 + x ^ p % p) % p) % p = (1 + x ^ p % p) % p := by
    rw [Nat.zero_add, Nat.mod_mod]
  have hE : (1 + x ^ p % p) % p = (x ^ p + 1) % p := by
    calc
      (1 + x ^ p % p) % p
          = (1 % p + (x ^ p % p) % p) % p := Nat.add_mod _ _ _
      _ = (1 % p + x ^ p % p) % p := by rw [Nat.mod_mod]
      _ = (x ^ p % p + 1 % p) % p := by rw [Nat.add_comm]
      _ = (x ^ p + 1) % p := (Nat.add_mod _ _ _).symm
  exact hC.trans (hD.trans hE)

/-- Fermat's little theorem in the form `a ^ p ≡ a (mod p)`. -/
theorem fermat_pow {p a : Nat} (hp : 1 < p) (hc : primeCert p) :
    a ^ p % p = a % p := by
  induction a with
  | zero =>
    have : 0 < p := by omega
    rw [Nat.zero_pow this]
  | succ a ih =>
    have h := fermat_succ_pow (x := a) hp hc
    have h1 : 1 % p = 1 := Nat.mod_eq_of_lt hp
    calc
      (a + 1) ^ p % p = (a ^ p + 1) % p := h
      _ = (a ^ p % p + 1 % p) % p := Nat.add_mod _ _ _
      _ = (a % p + 1) % p := by rw [ih, h1]
      _ = (a + 1) % p := by
            have hadd := Nat.add_mod a 1 p
            rw [hadd, h1]

theorem fermat_coprime {p a : Nat} (hp : 1 < p) (hc : primeCert p)
    (ha : a % p ≠ 0) : a ^ (p - 1) % p = 1 := by
  have hppos : 0 < p := by omega
  have hpow := fermat_pow (a := a) hp hc
  have hp' : p - 1 + 1 = p := by omega
  have hdecomp : a ^ p = a ^ (p - 1) * a := by
    calc
      a ^ p = a ^ (p - 1 + 1) := by rw [hp']
      _ = a ^ (p - 1) * a := Nat.pow_succ _ _
  have hmul : (a ^ (p - 1) * a) % p = a % p := by
    rw [← hdecomp, hpow]
  let r := a ^ (p - 1) % p
  let s := a % p
  have hs0 : s ≠ 0 := ha
  have hslt : s < p := Nat.mod_lt _ hppos
  have hrs : (r * s) % p = s := by
    have : (a ^ (p - 1) % p * (a % p)) % p = a % p := by
      rw [← Nat.mul_mod, hmul]
    simpa [r, s] using this
  have rne : r ≠ 0 := by
    intro h0
    have hzs : (0 * s) % p = s := by simpa [h0] using hrs
    have : s = 0 := by
      simpa [Nat.zero_mul, Nat.zero_mod] using hzs.symm
    exact hs0 this
  have _hrpos : 1 ≤ r := by omega
  have _hle : s ≤ r * s := Nat.le_mul_of_pos_left s (by omega)
  have hsub : p ∣ r * s - s :=
    Nat.dvd_of_mod_eq_zero
      (Nat.sub_mod_eq_zero_of_mod_eq (by rw [hrs, Nat.mod_eq_of_lt hslt]))
  have hfac : r * s - s = (r - 1) * s := by
    have hr' : r - 1 + 1 = r := by omega
    calc
      r * s - s = (r - 1 + 1) * s - s := by rw [hr']
      _ = ((r - 1) * s + s) - s := by rw [Nat.add_one_mul]
      _ = (r - 1) * s := Nat.add_sub_cancel _ _
  have hdvd : p ∣ (r - 1) * s := by
    rw [← hfac]; exact hsub
  have hcop : Nat.Coprime s p :=
    hc ⟨s, hslt⟩ hs0
  have : p ∣ r - 1 :=
    hcop.symm.dvd_of_dvd_mul_right hdvd
  have hrlt : r < p := Nat.mod_lt _ hppos
  have hzero : r - 1 = 0 :=
    Nat.eq_zero_of_dvd_of_lt this (by omega)
  omega

end LeanA113258
