import LeanA113258.Fermat

namespace LeanA113258

/-!
  Uniform congruences: if `p` is a certified prime and `2 * p - 3 ≤ n`,
  then `a n ≡ -1 (mod p)`. In the remaining coprime-large window the
  perfect-power base is likewise `≡ -1 (mod p)`.
-/

/-! ### Powers congruent to 1 via Fermat -/

theorem pow_mod_one_of_mul {p a k : Nat} (hp : 1 < p) (hc : primeCert p)
    (ha : a % p ≠ 0) : a ^ ((p - 1) * k) % p = 1 := by
  induction k with
  | zero =>
    rw [Nat.mul_zero, Nat.pow_zero]
    exact Nat.mod_eq_of_lt hp
  | succ k ih =>
    rw [Nat.mul_succ, Nat.pow_add, Nat.mul_mod, ih, fermat_coprime hp hc ha]
    simp [Nat.mod_eq_of_lt hp]

theorem pow_mod_one_of_dvd {p a e : Nat} (hp : 1 < p) (hc : primeCert p)
    (ha : a % p ≠ 0) (hd : p - 1 ∣ e) : a ^ e % p = 1 := by
  obtain ⟨k, hk⟩ := hd
  rw [hk]
  exact pow_mod_one_of_mul hp hc ha

/-! ### Factorials and terms modulo a prime -/

theorem fact_mod_prime_ne {p k : Nat} (hp : 1 < p) (hc : primeCert p)
    (hk : k < p) : fact k % p ≠ 0 := by
  intro hz
  have hd : p ∣ fact k := Nat.dvd_of_mod_eq_zero hz
  have hg := fact_gcd_prime hp hc hk
  have hpd : p ∣ Nat.gcd (fact k) p := Nat.dvd_gcd hd (Nat.dvd_refl p)
  rw [hg] at hpd
  have : p ≤ 1 := Nat.le_of_dvd (by decide : 0 < 1) hpd
  omega

theorem term_mod_prime_one {n i p : Nat} (hp : 1 < p) (hc : primeCert p)
    (hi : i + 1 < p) (hexp : p - 1 ≤ n - i) : term n i % p = 1 := by
  unfold term
  refine pow_mod_one_of_dvd hp hc ?ha ?hd
  · exact fact_mod_prime_ne hp hc hi
  · exact dvd_fact_of_le (by omega) hexp

theorem term_mod_prime_zero {n i p : Nat} (hp : 1 < p) (hpi : p ≤ i + 1) :
    term n i % p = 0 := by
  unfold term
  have hd : p ∣ fact (i + 1) := dvd_fact_of_le (by omega) hpi
  have hpos : 0 < fact (n - i) := fact_pos _
  have hsucc : fact (n - i) = fact (n - i) - 1 + 1 := by omega
  have hpow : p ∣ fact (i + 1) ^ fact (n - i) := by
    rw [hsucc, Nat.pow_succ, Nat.mul_comm]
    exact Nat.dvd_mul_right_of_dvd hd _
  exact Nat.mod_eq_zero_of_dvd hpow

/-! ### Splitting `sumRange` -/

theorem sumRange_split {k n : Nat} (f : Nat → Nat) (hk : k ≤ n) :
    sumRange n f = sumRange k f + sumRange (n - k) (fun i => f (k + i)) := by
  refine le_induction
      (fun n => sumRange n f = sumRange k f + sumRange (n - k) (fun i => f (k + i)))
      hk ?base ?step
  · simp [Nat.sub_self, sumRange_zero]
  · intro n hn ih
    rw [sumRange_succ, ih]
    have hnk : n + 1 - k = n - k + 1 := by omega
    rw [hnk, sumRange_succ]
    have : k + (n - k) = n := by omega
    rw [this]
    omega

theorem sumRange_const_one (n : Nat) : sumRange n (fun _ => 1) = n := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [sumRange_succ, ih]

theorem sumRange_mod_one {n m : Nat} {f : Nat → Nat}
    (h : ∀ i, i < n → f i % m = 1 % m) :
    sumRange n f % m = n % m := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [sumRange_succ, Nat.add_mod, ih (fun i hi => h i (Nat.lt_succ_of_le (Nat.le_of_lt hi))),
      h n (Nat.lt_succ_self n)]
    exact (Nat.add_mod n 1 m).symm

/-! ### Uniform theorem: `a n ≡ -1 (mod p)` -/

theorem a_eq_sum_term (n : Nat) : a n = sumRange n (term n) := rfl

theorem a_mod_prime {n p : Nat} (hp : 1 < p) (hc : primeCert p)
    (hn : 2 * p - 3 ≤ n) : a n % p = p - 1 := by
  have hpn : p - 1 ≤ n := by omega
  have hsplit := sumRange_split (term n) hpn
  have hhead : ∀ i, i < p - 1 → term n i % p = 1 := by
    intro i hi
    have hi1 : i + 1 < p := by omega
    have hexp : p - 1 ≤ n - i := by omega
    exact term_mod_prime_one hp hc hi1 hexp
  have hhead' : ∀ i, i < p - 1 → term n i % p = 1 % p := by
    intro i hi
    rw [Nat.mod_eq_of_lt hp]
    exact hhead i hi
  have hsum1 : sumRange (p - 1) (term n) % p = p - 1 := by
    have h1 : (p - 1) % p = p - 1 := Nat.mod_eq_of_lt (by omega)
    have hmod := sumRange_mod_one (n := p - 1) (m := p) (f := term n) hhead'
    rw [h1] at hmod
    exact hmod
  have htail :
      sumRange (n - (p - 1)) (fun i => term n (p - 1 + i)) % p = 0 := by
    refine sumRange_mod_zero (fun i _hi => ?_)
    have : p ≤ p - 1 + i + 1 := by omega
    exact term_mod_prime_zero (n := n) (i := p - 1 + i) hp this
  rw [a_eq_sum_term, hsplit, Nat.add_mod, hsum1, htail]
  simp [Nat.mod_eq_of_lt (by omega : p - 1 < p)]

/-! ### Coprimality of `e` with `p - 1` -/

theorem gcd_e_pred_prime {n e p : Nat}
    (hg : Nat.gcd e (fact (n - 1)) = 1) (hle : p - 1 ≤ n - 1) (_hp : 1 < p) :
    Nat.gcd e (p - 1) = 1 := by
  have hd : p - 1 ∣ fact (n - 1) := dvd_fact_of_le (by omega) hle
  have hdiv : Nat.gcd e (p - 1) ∣ Nat.gcd e (fact (n - 1)) :=
    Nat.gcd_dvd_gcd_of_dvd_right e hd
  rw [hg] at hdiv
  exact Nat.eq_one_of_dvd_one hdiv

/-! ### Modular inverse via Bézout (Init integers, no Mathlib) -/

private theorem int_sub_add_cancel_left (x y : Int) : x - (x + y) = -y := by
  rw [Int.sub_eq_add_neg, Int.neg_add, ← Int.add_assoc, Int.add_right_neg, Int.zero_add]

private theorem bezout_step (s t a q r : Int) :
    (t - s * q) * a + s * (a * q + r) = s * r + t * a := by
  have h1 : (t - s * q) * a = t * a - (s * q) * a := Int.sub_mul t (s * q) a
  have h2 : s * (a * q + r) = s * (a * q) + s * r := Int.mul_add s _ _
  have h3 : s * (a * q) = (s * q) * a := by
    rw [Int.mul_comm a q, ← Int.mul_assoc]
  rw [h1, h2, h3, ← Int.add_assoc, Int.sub_add_cancel, Int.add_comm]

theorem bezout (a m : Nat) :
    ∃ s t : Int, s * (a : Int) + t * (m : Int) = (Nat.gcd a m : Int) := by
  induction a, m using Nat.gcd.induction with
  | H0 n =>
    refine ⟨0, 1, ?_⟩
    simp
  | H1 a m ha ih =>
    obtain ⟨s, t, h⟩ := ih
    refine ⟨t - s * (↑(m / a) : Int), s, ?_⟩
    have hrec : Nat.gcd a m = Nat.gcd (m % a) a := Nat.gcd_rec a m
    have hdiv : (m : Int) = ↑a * ↑(m / a) + ↑(m % a) := by
      have hnat := Nat.div_add_mod m a
      calc
        (m : Int) = ↑(a * (m / a) + m % a) := by rw [hnat]
        _ = ↑(a * (m / a)) + ↑(m % a) := Int.natCast_add _ _
        _ = ↑a * ↑(m / a) + ↑(m % a) := by rw [Int.natCast_mul]
    have hid :
        (t - s * ↑(m / a)) * ↑a + s * ↑m =
          s * ↑(m % a) + t * ↑a := by
      rw [hdiv]
      exact bezout_step s t (↑a) (↑(m / a)) (↑(m % a))
    rw [hid, h, hrec]

theorem exists_mul_mod_gcd (a m : Nat) (hm : 0 < m) :
    ∃ k, a * k % m = Nat.gcd a m % m := by
  obtain ⟨s, t, hst⟩ := bezout a m
  have hsub : s * ↑a - ↑(Nat.gcd a m) = -(t * ↑m) := by
    rw [← hst]
    exact int_sub_add_cancel_left _ _
  have hcong : (s * ↑a) % (m : Int) = (↑(Nat.gcd a m) : Int) % ↑m := by
    refine (Int.emod_eq_emod_iff_emod_sub_eq_zero (m := s * ↑a)
      (n := (m : Int)) (k := ↑(Nat.gcd a m))).2 ?_
    have hdvd : (m : Int) ∣ (s * ↑a - ↑(Nat.gcd a m)) :=
      ⟨-t, by
        rw [hsub, Int.mul_comm t, Int.neg_mul_eq_mul_neg]⟩
    exact Int.emod_eq_zero_of_dvd hdvd
  have hmne : (m : Int) ≠ 0 := Int.natCast_ne_zero.mpr (Nat.ne_of_gt hm)
  have hs0 : 0 ≤ s % (m : Int) := Int.emod_nonneg s hmne
  let k := (s % (m : Int)).toNat
  have hk : (k : Int) = s % ↑m := Int.toNat_of_nonneg hs0
  refine ⟨k, ?_⟩
  apply Int.natCast_inj.mp
  rw [Int.natCast_emod, Int.natCast_emod, Int.natCast_mul, hk]
  have hmul : (↑a * (s % ↑m)) % (m : Int) = (s * ↑a) % ↑m := by
    rw [Int.mul_comm, Int.mul_emod, Int.mul_emod s ↑a, Int.emod_emod]
  exact hmul.trans hcong

theorem exists_mul_mod_one {a m : Nat} (hm : 1 < m) (h : Nat.gcd a m = 1) :
    ∃ k, a * k % m = 1 := by
  obtain ⟨k, hk⟩ := exists_mul_mod_gcd a m (by omega)
  rw [h, Nat.mod_eq_of_lt hm] at hk
  exact ⟨k, hk⟩

theorem odd_inv_of_coprime_even {e m inv : Nat}
    (he : e % 2 = 1) (hm2 : m % 2 = 0) (_hg : Nat.gcd e m = 1)
    (hinv : e * inv % m = 1) : inv % 2 = 1 := by
  have hde : e * inv = e * inv / m * m + 1 := by
    have h := Nat.div_add_mod (e * inv) m
    rw [hinv, Nat.mul_comm m] at h
    exact h.symm
  have hodd : (e * inv) % 2 = 1 := by
    rw [hde, Nat.add_mod, Nat.mul_mod, hm2]
    simp
  have : (e * inv) % 2 = (e % 2 * (inv % 2)) % 2 := Nat.mul_mod e inv 2
  rw [this, he, Nat.one_mul, Nat.mod_mod] at hodd
  exact hodd

/-- `(p - 1) ^ 2 ≡ 1 (mod p)`. -/
theorem pred_mul_pred_mod {p : Nat} (hp : 1 < p) :
    (p - 1) * (p - 1) % p = 1 := by
  let n := p - 2
  have hn : p - 1 = n + 1 := by omega
  have hp' : p = n + 2 := by omega
  have h : (n + 1) * (n + 1) = (n + 2) * n + 1 := by
    have h1 : (n + 1) * (n + 1) = n * n + n + n + 1 := by
      rw [Nat.add_one_mul, Nat.mul_add, Nat.mul_one]
      omega
    have h2 : (n + 2) * n = n * n + n + n := by
      rw [Nat.add_mul, Nat.two_mul]
      omega
    omega
  have h' : (p - 1) * (p - 1) = p * (p - 2) + 1 := by
    rw [hn, hp']
    exact h
  rw [h', Nat.add_mod, Nat.mul_mod_right, Nat.zero_add, Nat.mod_mod,
    Nat.mod_eq_of_lt hp]

theorem pow_neg_one_odd {p k : Nat} (hp : 1 < p) (h : k % 2 = 1) :
    (p - 1) ^ k % p = p - 1 := by
  have hk : k = 2 * (k / 2) + 1 := by omega
  rw [hk, Nat.pow_add, Nat.pow_mul, Nat.pow_one, Nat.mul_mod]
  have hsq : ((p - 1) ^ 2) % p = 1 := by
    rw [Nat.pow_two]
    exact pred_mul_pred_mod hp
  have hpow : ((p - 1) ^ 2) ^ (k / 2) % p = 1 := by
    rw [Nat.pow_mod, hsq, one_pow, Nat.mod_eq_of_lt hp]
  rw [hpow, Nat.mod_eq_of_lt (by omega : p - 1 < p)]
  simp [Nat.mod_eq_of_lt (by omega : p - 1 < p)]

/-! ### Remaining-case lift: the base is `-1` modulo `p` -/

theorem e_odd_of_coprime_fact_ge7 {n e : Nat} (hn : 7 ≤ n)
    (hg : Nat.gcd e (fact (n - 1)) = 1) : e % 2 = 1 := by
  have h2 : 2 ∣ fact (n - 1) := two_dvd_fact (by omega : 2 ≤ n - 1)
  have hne : e % 2 ≠ 0 := by
    intro hz
    have he : 2 ∣ e := Nat.dvd_of_mod_eq_zero hz
    have hg2 : 2 ∣ Nat.gcd e (fact (n - 1)) := Nat.dvd_gcd he h2
    rw [hg] at hg2
    have : 2 ≤ 1 := Nat.le_of_dvd (by decide : 0 < 1) hg2
    omega
  omega

theorem pow_mod_eq_zero_of {p b e : Nat} (_hp : 0 < p) (hb : b % p = 0)
    (he : 0 < e) : b ^ e % p = 0 := by
  rw [Nat.pow_mod, hb, Nat.zero_pow he, Nat.zero_mod]

theorem remaining_base_mod_prime
    {n b e p : Nat} (hn : 7 ≤ n) (hp : 1 < p) (hc : primeCert p)
    (hpn : 2 * p - 3 ≤ n)
    (_hb : 1 < b) (he : 1 < e)
    (hg : Nat.gcd e (fact (n - 1)) = 1)
    (hab : a n = b ^ e) :
    b % p = p - 1 := by
  have hamod : a n % p = p - 1 := a_mod_prime hp hc hpn
  have hbe : b ^ e % p = p - 1 := by
    rw [← hab]
    exact hamod
  have hb0 : b % p ≠ 0 := by
    intro hz
    have : b ^ e % p = 0 :=
      pow_mod_eq_zero_of (by omega) hz (by omega)
    have : p - 1 = 0 := by omega
    omega
  by_cases hp2 : p = 2
  · subst hp2
    cases Nat.mod_two_eq_zero_or_one b with
    | inl h0 => exact (hb0 h0).elim
    | inr h1 => exact h1
  · have hpgt : 2 < p := by omega
    have hpm : 1 < p - 1 := by omega
    have hcop : Nat.gcd e (p - 1) = 1 :=
      gcd_e_pred_prime hg (by omega) hp
    obtain ⟨inv, hinv⟩ := exists_mul_mod_one (a := e) (m := p - 1) hpm hcop
    have heodd : e % 2 = 1 := e_odd_of_coprime_fact_ge7 hn hg
    have hm2 : (p - 1) % 2 = 0 := by
      have hne : p % 2 ≠ 0 := by
        intro hz
        have hd : 2 ∣ p := Nat.dvd_of_mod_eq_zero hz
        have h2lt : 2 < p := hpgt
        have hcop2 : Nat.gcd (2 : Nat) p = 1 :=
          hc ⟨2, h2lt⟩ (by decide : (2 : Nat) ≠ 0)
        have hg2 : Nat.gcd 2 p = 2 := Nat.gcd_eq_left hd
        omega
      have : p % 2 = 1 := by omega
      omega
    have hiodd : inv % 2 = 1 :=
      odd_inv_of_coprime_even heodd hm2 hcop hinv
    have hdecomp : e * inv = (p - 1) * (e * inv / (p - 1)) + 1 := by
      have h := Nat.div_add_mod (e * inv) (p - 1)
      rw [hinv] at h
      exact h.symm
    have hpowb : b ^ (e * inv) % p = b % p := by
      rw [hdecomp, Nat.pow_add, Nat.pow_one, Nat.mul_mod,
        pow_mod_one_of_mul hp hc hb0]
      simp
    have hpowbe : b ^ (e * inv) % p = (p - 1) ^ inv % p := by
      have hmul : (b ^ e) ^ inv = b ^ (e * inv) := (Nat.pow_mul b e inv).symm
      calc
        b ^ (e * inv) % p = (b ^ e) ^ inv % p := by rw [hmul]
        _ = (b ^ e % p) ^ inv % p := Nat.pow_mod _ _ _
        _ = (p - 1) ^ inv % p := by rw [hbe]
    have hneg : (p - 1) ^ inv % p = p - 1 := pow_neg_one_odd hp hiodd
    calc
      b % p = b ^ (e * inv) % p := hpowb.symm
      _ = (p - 1) ^ inv % p := hpowbe
      _ = p - 1 := hneg

end LeanA113258
