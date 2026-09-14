import LeanA113258.Remaining

namespace LeanA113258

/-!
  Uniform facts (all `n ≥ 7`) about the remaining coprime-large exponent window.

  Proved here, with no `sorry`:
  * the odd base of a remaining representation lies in a dyadic interval
    `2^q < b < 2^{q+1}` with `q = (n-1)! / e`
  * that interval sits strictly below `2^{(n-2)!}` when `e ≥ n`
  * odd `e`-th powers are injective on odd residues modulo `2^B`
  * hence at most one odd candidate class modulo `2^{(n-2)!}`
  * a packaged description of the remaining hole

  Not proved (and not claimed):
  * `not_eth_power_of_coprime_large`
  * `officialConjecture_false`

  Uniqueness of the odd residue class together with the dyadic interval does
  **not** finish the remaining case: the unique candidate might still exist.
-/

/-! ### Helpers -/

theorem coprime_not_dvd {e K : Nat} (he : 1 < e) (hg : Nat.gcd e K = 1) :
    ¬ e ∣ K := by
  intro hdvd
  have : Nat.gcd e K = e := gcd_eq_left_of_dvd hdvd
  omega

private theorem sumRange_congr {n : Nat} {f g : Nat → Nat}
    (h : ∀ i, i < n → f i = g i) : sumRange n f = sumRange n g := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [sumRange_succ, sumRange_succ, ih fun i hi => h i (Nat.lt_succ_of_le (Nat.le_of_lt hi)),
      h n (Nat.lt_succ_self n)]

private theorem sumRange_mul_left (n c : Nat) (f : Nat → Nat) :
    sumRange n (fun i => c * f i) = c * sumRange n f := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [sumRange_succ, sumRange_succ, ih, Nat.mul_add]

theorem dvd_natAbsDiff_of_mod_eq {a b m : Nat}
    (h : a % m = b % m) : m ∣ natAbsDiff a b := by
  unfold natAbsDiff
  by_cases hlt : a < b
  · rw [if_pos hlt]
    exact Nat.dvd_of_mod_eq_zero (Nat.sub_mod_eq_zero_of_mod_eq h.symm)
  · rw [if_neg hlt]
    exact Nat.dvd_of_mod_eq_zero (Nat.sub_mod_eq_zero_of_mod_eq h)

theorem mod_eq_of_dvd_natAbsDiff {a b m : Nat}
    (h : m ∣ natAbsDiff a b) : a % m = b % m := by
  unfold natAbsDiff at h
  by_cases hlt : a < b
  · rw [if_pos hlt] at h
    obtain ⟨k, hk⟩ := h
    have hb : b = a + m * k := by
      have : b = a + (b - a) := (Nat.add_sub_of_le (Nat.le_of_lt hlt)).symm
      rw [this, hk]
    rw [hb, Nat.add_mul_mod_self_left]
  · rw [if_neg hlt] at h
    have hle : b ≤ a := Nat.le_of_not_lt hlt
    obtain ⟨k, hk⟩ := h
    have ha : a = b + m * k := by
      have : a = b + (a - b) := (Nat.add_sub_of_le hle).symm
      rw [this, hk]
    rw [ha, Nat.add_mul_mod_self_left]

/-! ### Binary interval for the remaining base -/

theorem remaining_base_dyadic
    {n b e : Nat} (hn : 7 ≤ n) (hb : 2 ≤ b) (he : 1 < e)
    (hg : Nat.gcd e (fact (n - 1)) = 1)
    (hab : a n = b ^ e) :
    let q := fact (n - 1) / e
    2 ^ q < b ∧ b < 2 ^ (q + 1) := by
  have _ := hb
  let K := fact (n - 1)
  let q := K / e
  let r := K % e
  have he0 : 0 < e := Nat.zero_lt_of_lt he
  have hndvd : ¬ e ∣ K := coprime_not_dvd he hg
  have hr0 : 0 < r := by
    have : r ≠ 0 := by
      intro hz
      have : e ∣ K := (Nat.dvd_iff_mod_eq_zero.2 hz)
      exact hndvd this
    omega
  have hrlt : r < e := Nat.mod_lt K he0
  have hK : K = q * e + r := by
    have hdiv := Nat.div_add_mod K e
    rw [Nat.mul_comm] at hdiv
    exact hdiv.symm
  have ⟨hKlt, hKsucc⟩ := a_mem_two_pow_interval hn
  rw [hab] at hKlt hKsucc
  have hene : e ≠ 0 := Nat.ne_of_gt he0
  have hlower : 2 ^ q < b := by
    have hge : 2 ^ (q * e + 1) ≤ 2 ^ (q * e + r) :=
      Nat.pow_le_pow_right (by decide : (0 : Nat) < 2) (by omega : q * e + 1 ≤ q * e + r)
    have hKexp : 2 ^ K = 2 ^ (q * e + r) := congrArg (fun t => 2 ^ t) hK
    have hchain : (2 ^ q) ^ e < b ^ e := by
      have hpow : 2 ^ (q * e + 1) = 2 * (2 ^ q) ^ e := by
        rw [Nat.pow_succ', Nat.pow_mul]
      have hpos : 0 < (2 ^ q) ^ e := Nat.pow_pos (Nat.two_pow_pos _)
      have hgt : (2 ^ q) ^ e < 2 * (2 ^ q) ^ e := by
        have : 1 * (2 ^ q) ^ e < 2 * (2 ^ q) ^ e :=
          Nat.mul_lt_mul_of_pos_right (by decide : (1 : Nat) < 2) hpos
        simpa using this
      have : (2 ^ q) ^ e < 2 ^ (q * e + 1) := by
        rw [hpow]
        exact hgt
      have hle' : 2 ^ (q * e + 1) ≤ 2 ^ K := by
        rw [hKexp]
        exact hge
      exact Nat.lt_trans this (Nat.lt_of_le_of_lt hle' hKlt)
    exact (Nat.pow_lt_pow_iff_left hene).1 hchain
  have hupper : b < 2 ^ (q + 1) := by
    have hre : r + 1 ≤ e := Nat.succ_le_of_lt hrlt
    have hle : q * e + r + 1 ≤ q * e + e := by omega
    have hK1 : K + 1 = q * e + r + 1 := by omega
    have hpowR : 2 ^ (q * e + e) = (2 ^ (q + 1)) ^ e := by
      have : q * e + e = (q + 1) * e := by
        rw [Nat.add_mul, Nat.one_mul]
      rw [this, Nat.pow_mul]
    have hle2 : 2 ^ (q * e + r + 1) ≤ (2 ^ (q + 1)) ^ e := by
      have : 2 ^ (q * e + r + 1) ≤ 2 ^ (q * e + e) :=
        Nat.pow_le_pow_right (by decide : (0 : Nat) < 2) hle
      rw [← hpowR]
      exact this
    have hlt : b ^ e < (2 ^ (q + 1)) ^ e := by
      have : b ^ e < 2 ^ (K + 1) := hKsucc
      have hKpow : 2 ^ (K + 1) = 2 ^ (q * e + r + 1) := congrArg (fun t => 2 ^ t) hK1
      rw [hKpow] at this
      exact Nat.lt_of_lt_of_le this hle2
    exact (Nat.pow_lt_pow_iff_left hene).1 hlt
  exact ⟨hlower, hupper⟩

theorem remaining_base_lt_twoB
    {n b e : Nat} (hn : 7 ≤ n) (hb : 2 ≤ b) (he : n ≤ e)
    (hg : Nat.gcd e (fact (n - 1)) = 1)
    (hab : a n = b ^ e) :
    b < 2 ^ fact (n - 2) := by
  have he1 : 1 < e := by omega
  have ⟨_, hupper⟩ := remaining_base_dyadic hn hb he1 hg hab
  let q := fact (n - 1) / e
  have hqn : fact (n - 1) / e ≤ fact (n - 1) / n :=
    div_le_div_of_ge_right (by omega : 0 < n) he
  have hltB : fact (n - 1) / n < fact (n - 2) := by
    have hK : fact (n - 1) = (n - 1) * fact (n - 2) := fact_pred_eq (by omega)
    rw [hK, Nat.div_lt_iff_lt_mul (by omega : 0 < n)]
    have hBpos : 0 < fact (n - 2) := fact_pos _
    have : (n - 1) * fact (n - 2) < n * fact (n - 2) :=
      Nat.mul_lt_mul_of_pos_right (by omega : n - 1 < n) hBpos
    simpa [Nat.mul_comm] using this
  have hqB : q + 1 ≤ fact (n - 2) := by
    have : q ≤ fact (n - 1) / n := hqn
    omega
  have hpow : 2 ^ (q + 1) ≤ 2 ^ fact (n - 2) :=
    Nat.pow_le_pow_right (by decide : (0 : Nat) < 2) hqB
  exact Nat.lt_of_lt_of_le hupper hpow

/-! ### Odd eth-powers are injective on odd residues modulo `2^B` -/

theorem pow_succ_sub_pow_succ {x y k : Nat} (hle : y ≤ x) :
    x ^ (k + 1) - y ^ (k + 1) =
      x * (x ^ k - y ^ k) + (x - y) * y ^ k := by
  have hyk : y ^ k ≤ x ^ k := Nat.pow_le_pow_left hle k
  have hxkyk : x * y ^ k ≤ x * x ^ k := Nat.mul_le_mul_left x hyk
  have hyyk : y * y ^ k ≤ x * y ^ k := Nat.mul_le_mul_right (y ^ k) hle
  have h1 : x * (x ^ k - y ^ k) = x * x ^ k - x * y ^ k :=
    Nat.mul_sub_left_distrib x _ _
  have h2 : (x - y) * y ^ k = x * y ^ k - y * y ^ k :=
    Nat.mul_sub_right_distrib x y (y ^ k)
  have hsum :
      (x * x ^ k - x * y ^ k) + (x * y ^ k - y * y ^ k) =
        x * x ^ k - y * y ^ k := by
    rw [← Nat.add_sub_assoc hyyk (x * x ^ k - x * y ^ k),
      Nat.sub_add_cancel hxkyk]
  rw [Nat.pow_succ', Nat.pow_succ', h1, h2, hsum]

theorem mixed_pow_sum_succ {x y k : Nat} (_hk : 1 ≤ k) :
    sumRange (k + 1) (fun i => x ^ (k - i) * y ^ i) =
      x * sumRange k (fun i => x ^ (k - 1 - i) * y ^ i) + y ^ k := by
  rw [sumRange_succ]
  have hlast : x ^ (k - k) * y ^ k = y ^ k := by simp
  rw [hlast]
  have hfun : ∀ i, i < k →
      x ^ (k - i) * y ^ i = x * (x ^ (k - 1 - i) * y ^ i) := by
    intro i hi
    have hidx : k - i = (k - 1 - i) + 1 := by omega
    rw [hidx, Nat.pow_succ, Nat.mul_comm (x ^ (k - 1 - i)), Nat.mul_assoc]
  have hsum := sumRange_congr hfun
  rw [hsum, sumRange_mul_left]

theorem pow_sub_pow {x y n : Nat} (hle : y ≤ x) (hn : 1 ≤ n) :
    x ^ n - y ^ n =
      (x - y) * sumRange n (fun i => x ^ (n - 1 - i) * y ^ i) := by
  refine le_induction
      (fun n => x ^ n - y ^ n =
        (x - y) * sumRange n (fun i => x ^ (n - 1 - i) * y ^ i))
      hn ?base ?step
  · simp [sumRange_succ, sumRange_zero]
  · intro k hk ih
    have hdecomp := pow_succ_sub_pow_succ (x := x) (y := y) (k := k) hle
    have hS := mixed_pow_sum_succ (x := x) (y := y) (k := k) hk
    have hidx :
        sumRange (k + 1) (fun i => x ^ (k + 1 - 1 - i) * y ^ i) =
          sumRange (k + 1) (fun i => x ^ (k - i) * y ^ i) :=
      sumRange_congr fun i _ => by
        have : k + 1 - 1 - i = k - i := by omega
        rw [this]
    rw [hdecomp, ih, hidx, hS]
    have hx :
        x * ((x - y) * sumRange k (fun i => x ^ (k - 1 - i) * y ^ i)) =
          (x - y) * (x * sumRange k (fun i => x ^ (k - 1 - i) * y ^ i)) := by
      rw [← Nat.mul_assoc, Nat.mul_comm x (x - y), Nat.mul_assoc]
    rw [hx, ← Nat.mul_add]

theorem odd_mixed_term {x y i j : Nat} (hx : x % 2 = 1) (hy : y % 2 = 1) :
    (x ^ i * y ^ j) % 2 = 1 :=
  odd_mul_odd (odd_pow hx) (odd_pow hy)

theorem odd_pow_diff_factor_odd {x y e : Nat}
    (he : e % 2 = 1) (hx : x % 2 = 1) (hy : y % 2 = 1) :
    sumRange e (fun i => x ^ (e - 1 - i) * y ^ i) % 2 = 1 := by
  have hterms : ∀ i, i < e →
      (x ^ (e - 1 - i) * y ^ i) % 2 = 1 := fun i _ =>
    odd_mixed_term (i := e - 1 - i) (j := i) hx hy
  have hsum := sumRange_mod2_of_all_odd hterms
  omega

theorem odd_pow_mod_two_pow_inj
    {B e x y : Nat} (hB : 1 ≤ B) (he : e % 2 = 1)
    (hx : x % 2 = 1) (hy : y % 2 = 1)
    (h : x ^ e % 2 ^ B = y ^ e % 2 ^ B) :
    x % 2 ^ B = y % 2 ^ B := by
  have he1 : 1 ≤ e := by
    have : e ≠ 0 := by
      intro hz
      subst hz
      simp at he
    omega
  have hSodd := odd_pow_diff_factor_odd (x := x) (y := y) (e := e) he hx hy
  have hcop : Nat.Coprime (sumRange e (fun i => x ^ (e - 1 - i) * y ^ i)) (2 ^ B) :=
    (coprime_odd_two hSodd).pow_right B
  have hdvdPow : 2 ^ B ∣ natAbsDiff (x ^ e) (y ^ e) :=
    dvd_natAbsDiff_of_mod_eq h
  have hdiff : 2 ^ B ∣ natAbsDiff x y := by
    cases Nat.le_total y x with
    | inl hle =>
      have hpowle : y ^ e ≤ x ^ e := Nat.pow_le_pow_left hle e
      have hnat : natAbsDiff (x ^ e) (y ^ e) = x ^ e - y ^ e := by
        unfold natAbsDiff
        rw [if_neg (Nat.not_lt_of_le hpowle)]
      have hfac := pow_sub_pow (x := x) (y := y) hle he1
      have : 2 ^ B ∣ (x - y) * sumRange e (fun i => x ^ (e - 1 - i) * y ^ i) := by
        rw [← hfac, ← hnat]
        exact hdvdPow
      have hxydvd : 2 ^ B ∣ x - y :=
        hcop.symm.dvd_of_dvd_mul_left (by
          rw [Nat.mul_comm]
          exact this)
      unfold natAbsDiff
      rw [if_neg (Nat.not_lt_of_le hle)]
      exact hxydvd
    | inr hle =>
      have hpowle : x ^ e ≤ y ^ e := Nat.pow_le_pow_left hle e
      have hnat : natAbsDiff (x ^ e) (y ^ e) = y ^ e - x ^ e := by
        unfold natAbsDiff
        by_cases hlt : x ^ e < y ^ e
        · rw [if_pos hlt]
        · have heq : x ^ e = y ^ e := Nat.le_antisymm hpowle (Nat.le_of_not_lt hlt)
          rw [if_neg hlt, heq, Nat.sub_self]
      have hfac := pow_sub_pow (x := y) (y := x) hle he1
      have : 2 ^ B ∣ (y - x) * sumRange e (fun i => y ^ (e - 1 - i) * x ^ i) := by
        have hS' :
            natAbsDiff (x ^ e) (y ^ e) =
              (y - x) * sumRange e (fun i => y ^ (e - 1 - i) * x ^ i) := by
          rw [hnat, hfac]
        rw [← hS']
        exact hdvdPow
      have hSodd' := odd_pow_diff_factor_odd (x := y) (y := x) (e := e) he hy hx
      have hcop' :
          Nat.Coprime (sumRange e (fun i => y ^ (e - 1 - i) * x ^ i)) (2 ^ B) :=
        (coprime_odd_two hSodd').pow_right B
      have hyxdvd : 2 ^ B ∣ y - x :=
        hcop'.symm.dvd_of_dvd_mul_left (by
          rw [Nat.mul_comm]
          exact this)
      unfold natAbsDiff
      by_cases hlt : x < y
      · rw [if_pos hlt]
        exact hyxdvd
      · have heq : x = y := Nat.le_antisymm hle (Nat.le_of_not_lt hlt)
        simp [heq]
  have _ := hB
  exact mod_eq_of_dvd_natAbsDiff hdiff

/-! ### At most one odd candidate modulo `2^B` -/

theorem a_mod_twoB {n : Nat} (hn : 7 ≤ n) :
    a n % 2 ^ fact (n - 2) = rho n := by
  obtain ⟨hsplit, _, hlt⟩ := a_twoB_split hn
  rw [hsplit, Nat.mul_add_mod, Nat.mod_eq_of_lt hlt]

theorem remaining_at_most_one_odd_base_mod
    {n b c e : Nat} (hn : 7 ≤ n) (he : e % 2 = 1)
    (hb : b % 2 = 1) (hc : c % 2 = 1)
    (hbe : a n = b ^ e) (hce : a n = c ^ e) :
    b % 2 ^ fact (n - 2) = c % 2 ^ fact (n - 2) := by
  have hB : 1 ≤ fact (n - 2) := Nat.succ_le_of_lt (fact_pos _)
  have hbmod : b ^ e % 2 ^ fact (n - 2) = rho n := by
    rw [← hbe]
    exact a_mod_twoB hn
  have hcmod : c ^ e % 2 ^ fact (n - 2) = rho n := by
    rw [← hce]
    exact a_mod_twoB hn
  have hpow : b ^ e % 2 ^ fact (n - 2) = c ^ e % 2 ^ fact (n - 2) := by
    rw [hbmod, hcmod]
  exact odd_pow_mod_two_pow_inj hB he hb hc hpow

/-! ### Packaged remaining window -/

theorem e_odd_of_coprime_fact {n e : Nat} (hn : 3 ≤ n)
    (hg : Nat.gcd e (fact (n - 1)) = 1) : e % 2 = 1 := by
  cases Nat.mod_two_eq_zero_or_one e with
  | inr hodd => exact hodd
  | inl heven =>
    have h2e : 2 ∣ e := Nat.dvd_of_mod_eq_zero heven
    have h2K : 2 ∣ fact (n - 1) := two_dvd_fact (by omega : 2 ≤ n - 1)
    have hnot : ¬ Nat.Coprime e (fact (n - 1)) :=
      Nat.not_coprime_of_dvd_of_dvd (by decide : (1 : Nat) < 2) h2e h2K
    exact (hnot hg).elim

theorem remaining_window
    {n b e : Nat} (hn : 7 ≤ n) (hb : 3 ≤ b) (he : n ≤ e)
    (hg : Nat.gcd e (fact (n - 1)) = 1)
    (hab : a n = b ^ e) :
    b % 2 = 1 ∧
      e % 2 = 1 ∧
      (let q := fact (n - 1) / e; 2 ^ q < b ∧ b < 2 ^ (q + 1)) ∧
      b < 2 ^ fact (n - 2) ∧
      b ^ e % 2 ^ fact (n - 2) = rho n := by
  have hb2 : 2 ≤ b := by omega
  have he1 : 1 < e := by omega
  have he0 : 0 < e := by omega
  have hbodd := base_odd_of_a_eq_pow (n := n) (by omega : 1 ≤ n) he0 hab
  have heodd := e_odd_of_coprime_fact (n := n) (by omega : 3 ≤ n) hg
  have hdy := remaining_base_dyadic hn hb2 he1 hg hab
  have hltB := remaining_base_lt_twoB hn hb2 he hg hab
  have hmod : b ^ e % 2 ^ fact (n - 2) = rho n := by
    rw [← hab]
    exact a_mod_twoB hn
  exact ⟨hbodd, heodd, hdy, hltB, hmod⟩

end LeanA113258
