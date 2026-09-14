import LeanA113258.Remaining

namespace LeanA113258

/-!
  Uniform 2-adic valuation facts (no per-`n` certificates).
-/

def val2 (n : Nat) : Nat :=
  if h : n = 0 then 0
  else if n % 2 = 0 then val2 (n / 2) + 1 else 0
termination_by n
decreasing_by
  have : 0 < n := by omega
  exact Nat.div_lt_self this (by decide)

def oddPart (n : Nat) : Nat := n / 2 ^ val2 n

def val2Fact : Nat → Nat
  | 0 => 0
  | n + 1 => val2Fact n + val2 (n + 1)

/-! ### Basic unfolding lemmas -/

theorem val2_zero : val2 0 = 0 := by
  unfold val2
  simp

theorem val2_odd {n : Nat} (h : n % 2 = 1) : val2 n = 0 := by
  have hne : n ≠ 0 := by omega
  conv => lhs; unfold val2
  rw [dif_neg hne, if_neg]
  omega

theorem val2_even {n : Nat} (hn : 0 < n) (he : n % 2 = 0) :
    val2 n = val2 (n / 2) + 1 := by
  have hne : n ≠ 0 := Nat.ne_of_gt hn
  conv => lhs; unfold val2
  rw [dif_neg hne, if_pos he]

theorem val2_one : val2 1 = 0 := val2_odd (by decide)

theorem val2_two : val2 2 = 1 := by
  rw [val2_even (by decide : (0 : Nat) < 2) (by decide)]
  simp [val2_one]

theorem val2_pos_of_even {n : Nat} (hn : 0 < n) (he : n % 2 = 0) :
    1 ≤ val2 n := by
  rw [val2_even hn he]
  omega

/-! ### Powers of two -/

theorem val2_two_pow (s : Nat) : val2 (2 ^ s) = s := by
  induction s with
  | zero => simp [val2_one]
  | succ s ih =>
    have hpos : 0 < 2 ^ (s + 1) := Nat.two_pow_pos _
    have heven : (2 ^ (s + 1)) % 2 = 0 := by
      rw [Nat.pow_succ']
      exact Nat.mul_mod_right 2 _
    have hdiv : 2 ^ (s + 1) / 2 = 2 ^ s := by
      rw [Nat.pow_succ']
      exact Nat.mul_div_right _ (by decide)
    rw [val2_even hpos heven, hdiv, ih]

/-! ### Multiplication by an odd factor -/

theorem val2_mul_odd {a b : Nat} (hb : b % 2 = 1) : val2 (a * b) = val2 a := by
  refine Nat.strongRecOn a fun a ih => ?_
  by_cases ha0 : a = 0
  · simp [ha0, val2_zero]
  · have hapos : 0 < a := by omega
    have hbpos : 0 < b := by omega
    cases Nat.mod_two_eq_zero_or_one a with
    | inl heven =>
      have habeven : (a * b) % 2 = 0 := by
        rw [Nat.mul_mod, heven]
        simp
      have habpos : 0 < a * b := Nat.mul_pos hapos hbpos
      have h2 : 2 ∣ a := Nat.dvd_of_mod_eq_zero heven
      have hdiv : (a * b) / 2 = (a / 2) * b := by
        have : a * b = 2 * ((a / 2) * b) := by
          calc
            a * b = (2 * (a / 2)) * b := by rw [Nat.mul_div_cancel' h2]
            _ = 2 * ((a / 2) * b) := by rw [Nat.mul_assoc]
        rw [this, Nat.mul_div_right _ (by decide)]
      rw [val2_even habpos habeven, hdiv, val2_even hapos heven]
      exact congrArg (· + 1) (ih (a / 2) (Nat.div_lt_self hapos (by decide)))
    | inr hodd =>
      have habodd : (a * b) % 2 = 1 := odd_mul_odd hodd hb
      rw [val2_odd hodd, val2_odd habodd]

/-! ### Canonical factorization `n = 2^{val2 n} * oddPart n` -/

theorem two_pow_val2_dvd (n : Nat) : 2 ^ val2 n ∣ n := by
  refine Nat.strongRecOn n fun n ih => ?_
  by_cases h0 : n = 0
  · subst h0
    exact Nat.dvd_zero _
  · have hpos : 0 < n := by omega
    cases Nat.mod_two_eq_zero_or_one n with
    | inl heven =>
      have h2 : 2 ∣ n := Nat.dvd_of_mod_eq_zero heven
      have hhalf : 2 ^ val2 (n / 2) ∣ n / 2 :=
        ih (n / 2) (Nat.div_lt_self hpos (by decide))
      have hgoal : 2 * 2 ^ val2 (n / 2) ∣ 2 * (n / 2) :=
        Nat.mul_dvd_mul_left 2 hhalf
      rw [val2_even hpos heven, Nat.pow_succ']
      simpa [Nat.mul_div_cancel' h2] using hgoal
    | inr hodd =>
      rw [val2_odd hodd]
      exact Nat.one_dvd n

theorem eq_two_pow_oddPart {n : Nat} (_hn : 0 < n) :
    n = 2 ^ val2 n * oddPart n :=
  (Nat.mul_div_cancel' (two_pow_val2_dvd n)).symm

theorem oddPart_pos {n : Nat} (hn : 0 < n) : 0 < oddPart n := by
  have h := eq_two_pow_oddPart hn
  cases Nat.eq_zero_or_pos (oddPart n) with
  | inl h0 =>
    rw [h0, Nat.mul_zero] at h
    omega
  | inr h => exact h

theorem oddPart_odd {n : Nat} (hn : 0 < n) : oddPart n % 2 = 1 := by
  revert hn
  refine Nat.strongRecOn n fun n ih hn => ?_
  cases Nat.mod_two_eq_zero_or_one n with
  | inl heven =>
    have h2 : 2 ∣ n := Nat.dvd_of_mod_eq_zero heven
    have hhalf : 0 < n / 2 := Nat.div_pos (Nat.le_of_dvd hn h2) (by decide)
    have hoddPart : oddPart n = oddPart (n / 2) := by
      unfold oddPart
      rw [val2_even hn heven, Nat.pow_succ']
      exact (Nat.div_div_eq_div_mul n 2 (2 ^ val2 (n / 2))).symm
    rw [hoddPart]
    exact ih (n / 2) (Nat.div_lt_self hn (by decide)) hhalf
  | inr hodd =>
    unfold oddPart
    rw [val2_odd hodd]
    simpa using hodd

/-! ### Uniqueness of the 2-adic exponent -/

theorem val2_unique {n s y : Nat} (hn : 0 < n) (h : n = 2 ^ s * y)
    (hy : y % 2 = 1) : s = val2 n := by
  induction s generalizing n with
  | zero =>
    have : n % 2 = 1 := by simpa [h] using hy
    rw [val2_odd this]
  | succ s ih =>
    have hypos : 0 < y := by omega
    have hn2 : n = 2 * (2 ^ s * y) := by
      rw [h, Nat.pow_succ', Nat.mul_assoc]
    have heven : n % 2 = 0 := by
      rw [hn2]
      exact Nat.mul_mod_right 2 _
    have hdiv : n / 2 = 2 ^ s * y := by
      rw [hn2, Nat.mul_div_right _ (by decide)]
    have hhalf : 0 < n / 2 := by
      have : 0 < 2 ^ s := Nat.two_pow_pos _
      exact hdiv ▸ Nat.mul_pos this hypos
    have hs : s = val2 (n / 2) := ih hhalf hdiv
    rw [val2_even hn heven, hs]

/-! ### `val2` of a product and of a power -/

theorem val2_mul {x y : Nat} (hx : 0 < x) (hy : 0 < y) :
    val2 (x * y) = val2 x + val2 y := by
  revert hx
  refine Nat.strongRecOn x fun x ih hx => ?_
  cases Nat.mod_two_eq_zero_or_one x with
  | inl heven =>
    have h2 : 2 ∣ x := Nat.dvd_of_mod_eq_zero heven
    have heven' : (x * y) % 2 = 0 := by
      rw [Nat.mul_mod, heven]
      simp
    have hxypos : 0 < x * y := Nat.mul_pos hx hy
    have hdiv : (x * y) / 2 = (x / 2) * y := by
      have : x * y = 2 * ((x / 2) * y) := by
        calc
          x * y = (2 * (x / 2)) * y := by rw [Nat.mul_div_cancel' h2]
          _ = 2 * ((x / 2) * y) := by rw [Nat.mul_assoc]
      rw [this, Nat.mul_div_right _ (by decide)]
    have hx2 : 0 < x / 2 := Nat.div_pos (Nat.le_of_dvd hx h2) (by decide)
    rw [val2_even hxypos heven', hdiv, val2_even hx heven,
      ih (x / 2) (Nat.div_lt_self hx (by decide)) hx2]
    omega
  | inr hodd =>
    rw [val2_odd hodd, Nat.zero_add, Nat.mul_comm]
    exact val2_mul_odd hodd

theorem val2_pow {a e : Nat} (he : 0 < e) : val2 (a ^ e) = e * val2 a := by
  by_cases ha : a = 0
  · subst ha
    simp [Nat.zero_pow he, val2_zero]
  · have hapos : 0 < a := by omega
    revert he
    induction e with
    | zero => intro he; omega
    | succ e ih =>
      intro he
      have hpowpos : 0 < a ^ e := Nat.pow_pos hapos
      rw [Nat.pow_succ, val2_mul hpowpos hapos]
      cases Nat.eq_zero_or_pos e with
      | inl h0 =>
        subst h0
        simp [val2_one]
      | inr hpos =>
        rw [ih hpos]
        exact (Nat.succ_mul e (val2 a)).symm

/-! ### Geometric sums and `x^e - 1` -/

theorem odd_geomSum {x e : Nat} (hx : x % 2 = 1) (he : e % 2 = 1) :
    geomSum x e % 2 = 1 := by
  have := geomSum_mod2_of_odd (e := e) hx
  omega

theorem val2_odd_pow_sub_one {x e : Nat} (hx : x % 2 = 1) (he : e % 2 = 1)
    (hx1 : 1 ≤ x) : val2 (x ^ e - 1) = val2 (x - 1) := by
  have hfac := pow_sub_one_eq_mul_geomSum (n := e) hx1
  have hgs := odd_geomSum hx he
  rw [hfac, val2_mul_odd hgs]

/-! ### Factorial valuation -/

theorem val2Fact_succ (n : Nat) : val2Fact (n + 1) = val2Fact n + val2 (n + 1) :=
  rfl

theorem val2_fact (n : Nat) : val2 (fact n) = val2Fact n := by
  induction n with
  | zero =>
    simp [fact, val2Fact, val2_one]
  | succ n ih =>
    rw [fact_succ, val2Fact_succ, val2_mul (fact_pos n) (Nat.succ_pos n), ih]

theorem val2Fact_succ_ge (m : Nat) : val2Fact m ≤ val2Fact (m + 1) := by
  rw [val2Fact_succ]
  omega

theorem val2Fact_mono {m k : Nat} (h : m ≤ k) : val2Fact m ≤ val2Fact k := by
  refine le_induction (fun k => val2Fact m ≤ val2Fact k) h ?base ?step
  · exact Nat.le_refl _
  · intro n _hn ih
    exact Nat.le_trans ih (val2Fact_succ_ge n)

/-! ### Recursive Legendre formula and bounds -/

theorem val2Fact_div2 (n : Nat) : val2Fact n = n / 2 + val2Fact (n / 2) := by
  induction n with
  | zero => simp [val2Fact]
  | succ n ih =>
    rw [val2Fact_succ, ih]
    cases Nat.mod_two_eq_zero_or_one n with
    | inl heven =>
      have hdiv : (n + 1) / 2 = n / 2 := by omega
      have hodd : (n + 1) % 2 = 1 := by omega
      rw [val2_odd hodd, hdiv, Nat.add_zero]
    | inr hodd =>
      have heven : (n + 1) % 2 = 0 := by omega
      have hn1 : 0 < n + 1 := Nat.succ_pos _
      have hhalf : (n + 1) / 2 = n / 2 + 1 := by omega
      have hval : val2 (n + 1) = val2 ((n + 1) / 2) + 1 :=
        val2_even hn1 heven
      rw [hval, hhalf, val2Fact_succ]
      omega

theorem val2Fact_le (n : Nat) : val2Fact n ≤ n := by
  refine Nat.strongRecOn n fun n ih => ?_
  rw [val2Fact_div2]
  by_cases h0 : n = 0
  · simp [h0, val2Fact]
  · have hlt : n / 2 < n := Nat.div_lt_self (by omega) (by decide)
    have : val2Fact (n / 2) ≤ n / 2 := ih (n / 2) hlt
    omega

theorem val2Fact_le_pred {n : Nat} (hn : 1 ≤ n) : val2Fact n ≤ n - 1 := by
  revert hn
  refine Nat.strongRecOn n fun n ih hn => ?_
  rw [val2Fact_div2]
  cases n with
  | zero => omega
  | succ n =>
    cases Nat.eq_zero_or_pos ((n + 1) / 2) with
    | inl hz =>
      have : n = 0 := by omega
      subst this
      simp [val2Fact]
    | inr hpos =>
      have hlt : (n + 1) / 2 < n + 1 :=
        Nat.div_lt_self (Nat.succ_pos _) (by decide)
      have := ih ((n + 1) / 2) hlt (Nat.succ_le_of_lt hpos)
      omega

theorem val2Fact_ge_half (m : Nat) : m / 2 ≤ val2Fact m := by
  induction m with
  | zero => simp [val2Fact]
  | succ m ih =>
    rw [val2Fact_succ]
    cases Nat.mod_two_eq_zero_or_one m with
    | inl heven =>
      have : (m + 1) / 2 = m / 2 := by omega
      omega
    | inr hodd =>
      have heven : (m + 1) % 2 = 0 := by omega
      have hpos : 0 < m + 1 := Nat.succ_pos _
      have hval : 1 ≤ val2 (m + 1) := val2_pos_of_even hpos heven
      have : (m + 1) / 2 = m / 2 + 1 := by omega
      omega

theorem val2_le_half (n : Nat) : val2 n ≤ n / 2 := by
  refine Nat.strongRecOn n fun n ih => ?_
  by_cases h0 : n = 0
  · simp [h0, val2_zero]
  · cases Nat.mod_two_eq_zero_or_one n with
    | inr hodd =>
      rw [val2_odd hodd]
      omega
    | inl heven =>
      have hpos : 0 < n := by omega
      rw [val2_even hpos heven]
      have hlt : n / 2 < n := Nat.div_lt_self hpos (by decide)
      have ih' : val2 (n / 2) ≤ (n / 2) / 2 := ih (n / 2) hlt
      have hcases : n = 2 ∨ 4 ≤ n := by omega
      cases hcases with
      | inl h2 =>
        subst h2
        simp [val2_one]
      | inr h4 =>
        have : val2 (n / 2) + 1 ≤ (n / 2) / 2 + 1 := Nat.add_le_add_right ih' 1
        have : (n / 2) / 2 + 1 ≤ n / 2 := by
          have : 2 ≤ n / 2 := by omega
          omega
        omega

theorem val2Fact_one : val2Fact 1 = 0 := by
  change val2Fact 0 + val2 1 = 0
  simp [val2Fact, val2_one]

theorem val2Fact_two : val2Fact 2 = 1 := by
  change val2Fact 1 + val2 2 = 1
  simp [val2Fact_one, val2_two]

theorem val2Fact_three : val2Fact 3 = 1 := by
  change val2Fact 2 + val2 3 = 1
  simp [val2Fact_two, val2_odd]

theorem val2Fact_four : val2Fact 4 = 3 := by
  have h4 : val2 4 = 2 := by
    rw [val2_even (by decide : (0 : Nat) < 4) (by decide), val2_two]
  change val2Fact 3 + val2 4 = 3
  rw [val2Fact_three, h4]

theorem val2Fact_seven : val2Fact 7 = 4 := by
  have h5 : val2Fact 5 = 3 := by
    rw [val2Fact_succ, val2Fact_four, val2_odd (by decide)]
  have h6 : val2Fact 6 = 4 := by
    have h6v : val2 6 = 1 := by
      rw [val2_even (by decide : (0 : Nat) < 6) (by decide),
        val2_odd (by decide : (3 : Nat) % 2 = 1)]
    rw [val2Fact_succ, h5, h6v]
  rw [val2Fact_succ, h6, val2_odd (by decide)]

theorem val2Fact_ge_three {m : Nat} (hm : 4 ≤ m) : 3 ≤ val2Fact m := by
  refine le_induction (fun m => 3 ≤ val2Fact m) hm ?base ?step
  · exact Nat.le_of_eq val2Fact_four.symm
  · intro k _hk ih
    exact Nat.le_trans ih (val2Fact_succ_ge k)

/-! ### `val2 (fact (n-1)) > val2 n` for `n ≥ 5` -/

theorem two_pow_dvd_of_le_val2 {n k : Nat} (hn : 0 < n) (h : k ≤ val2 n) :
    2 ^ k ∣ n := by
  have hsplit : val2 n = k + (val2 n - k) := (Nat.add_sub_of_le h).symm
  have hpow : 2 ^ val2 n = 2 ^ k * 2 ^ (val2 n - k) := by
    conv => lhs; rw [hsplit]
    rw [Nat.pow_add]
  refine ⟨2 ^ (val2 n - k) * oddPart n, ?_⟩
  calc
    n = 2 ^ val2 n * oddPart n := eq_two_pow_oddPart hn
    _ = (2 ^ k * 2 ^ (val2 n - k)) * oddPart n := by rw [hpow]
    _ = 2 ^ k * (2 ^ (val2 n - k) * oddPart n) := by rw [Nat.mul_assoc]

theorem val2_dvd {d m : Nat} (h : d ∣ m) (hm : 0 < m) : val2 d ≤ val2 m := by
  obtain ⟨k, hk⟩ := h
  have hdpos : 0 < d := by
    cases Nat.eq_zero_or_pos d with
    | inl hd =>
      subst hd
      simp at hk
      omega
    | inr h => exact h
  have hkpos : 0 < k := by
    cases Nat.eq_zero_or_pos k with
    | inl hk0 =>
      subst hk0
      rw [Nat.mul_zero] at hk
      omega
    | inr h => exact h
  rw [hk, val2_mul hdpos hkpos]
  omega

theorem val2_two_pow_le_of_dvd {k m : Nat} (h : 2 ^ k ∣ m) (hm : 0 < m) :
    k ≤ val2 m := by
  have := val2_dvd h hm
  rwa [val2_two_pow] at this

theorem odd_ge_three {y : Nat} (hy : y % 2 = 1) (h1 : y ≠ 1) : 3 ≤ y := by
  omega

theorem two_pow_succ_eq (v : Nat) : 2 ^ (v + 1) = 2 * 2 ^ v := by
  rw [Nat.pow_succ']

theorem two_pow_pred_div {v : Nat} (hv : 1 ≤ v) :
    (2 ^ v - 1) / 2 = 2 ^ (v - 1) - 1 := by
  have hv' : v = v - 1 + 1 := by omega
  have hpow : 2 ^ v = 2 * 2 ^ (v - 1) := by
    conv => lhs; rw [hv', Nat.pow_succ']
  have hge : 1 ≤ 2 ^ (v - 1) := Nat.one_le_two_pow
  have heq : 2 ^ v - 1 = 2 * (2 ^ (v - 1) - 1) + 1 := by
    have hsub : 2 * 2 ^ (v - 1) - 2 = 2 * (2 ^ (v - 1) - 1) := by
      rw [Nat.mul_sub_left_distrib, Nat.mul_one]
    have : 2 * 2 ^ (v - 1) - 1 = 2 * 2 ^ (v - 1) - 2 + 1 := by omega
    calc
      2 ^ v - 1 = 2 * 2 ^ (v - 1) - 1 := by rw [hpow]
      _ = 2 * 2 ^ (v - 1) - 2 + 1 := this
      _ = 2 * (2 ^ (v - 1) - 1) + 1 := by rw [hsub]
  rw [heq]
  exact Nat.mul_add_div (by decide : (0 : Nat) < 2) (2 ^ (v - 1) - 1) 1

theorem two_pow_pred_gt {v : Nat} (hv : 4 ≤ v) : v < 2 ^ (v - 1) - 1 := by
  refine le_induction (fun v => v < 2 ^ (v - 1) - 1) hv ?base ?step
  · decide
  · intro k hk ih
    have hk' : k = k - 1 + 1 := by omega
    have hpow : 2 ^ k = 2 * 2 ^ (k - 1) := by
      conv => lhs; rw [hk', Nat.pow_succ']
    have h2 : 1 ≤ 2 ^ (k - 1) := Nat.one_le_two_pow
    have : k + 1 < 2 ^ k - 1 := by
      have : k + 1 < 2 ^ (k - 1) := by omega
      have : 2 ^ (k - 1) ≤ 2 * 2 ^ (k - 1) - 1 := by omega
      omega
    simpa [hpow] using this

theorem val2Fact_pred_gt_val2 {n : Nat} (hn : 5 ≤ n) :
    val2 n < val2Fact (n - 1) := by
  have hge3 : 3 ≤ val2Fact (n - 1) := val2Fact_ge_three (by omega)
  cases Nat.lt_or_ge (val2 n) 3 with
  | inl hlt =>
    omega
  | inr hv3 =>
    have hnpos : 0 < n := by omega
    have h8 : 2 ^ 3 ∣ n := two_pow_dvd_of_le_val2 hnpos hv3
    have hn8 : 8 ≤ n := Nat.le_of_dvd hnpos (by simpa using h8)
    have hdecomp := eq_two_pow_oddPart hnpos
    by_cases hpow : oddPart n = 1
    · have n_eq : n = 2 ^ val2 n := by
        calc
          n = 2 ^ val2 n * oddPart n := hdecomp
          _ = 2 ^ val2 n * 1 := by rw [hpow]
          _ = 2 ^ val2 n := by rw [Nat.mul_one]
      have hcases : val2 n = 3 ∨ 4 ≤ val2 n := by omega
      cases hcases with
      | inl hv3' =>
        have n8 : n = 8 := by
          calc
            n = 2 ^ val2 n := n_eq
            _ = 2 ^ 3 := by rw [hv3']
            _ = 8 := rfl
        subst n8
        have h8v : val2 8 = 3 := by
          simpa using val2_two_pow 3
        simp [h8v, val2Fact_seven]
      | inr hv4 =>
        have hv1 : 1 ≤ val2 n := by omega
        have hhalf : (n - 1) / 2 ≤ val2Fact (n - 1) := val2Fact_ge_half _
        have hdiv : (n - 1) / 2 = 2 ^ (val2 n - 1) - 1 := by
          have : n - 1 = 2 ^ val2 n - 1 := by
            conv => lhs; rw [n_eq]
          rw [this]
          exact two_pow_pred_div hv1
        have hgt : val2 n < 2 ^ (val2 n - 1) - 1 := two_pow_pred_gt hv4
        omega
    · have hy : 3 ≤ oddPart n := odd_ge_three (oddPart_odd hnpos) hpow
      have hnmul : 3 * 2 ^ val2 n ≤ n := by
        calc
          3 * 2 ^ val2 n ≤ oddPart n * 2 ^ val2 n :=
            Nat.mul_le_mul_right _ hy
          _ = n := by
            rw [Nat.mul_comm]
            exact hdecomp.symm
      have hle : 2 ^ (val2 n + 1) ≤ n - 1 := by
        have h2v : 1 ≤ 2 ^ val2 n := Nat.one_le_two_pow
        have : 2 * 2 ^ val2 n ≤ 3 * 2 ^ val2 n - 1 := by omega
        have : 3 * 2 ^ val2 n - 1 ≤ n - 1 := by omega
        rw [two_pow_succ_eq]
        omega
      have hdvd : 2 ^ (val2 n + 1) ∣ fact (n - 1) :=
        dvd_fact_of_le (Nat.two_pow_pos _) hle
      have : val2 n + 1 ≤ val2 (fact (n - 1)) :=
        val2_two_pow_le_of_dvd hdvd (fact_pos _)
      rw [val2_fact] at this
      omega

/-! ### Valuation of a sum -/

theorem val2_add_of_lt {x y : Nat} (h : val2 x < val2 y) (hx : 0 < x) :
    val2 (x + y) = val2 x := by
  have hypos : 0 < y := by
    cases Nat.eq_zero_or_pos y with
    | inl hy =>
      subst hy
      rw [val2_zero] at h
      omega
    | inr hy => exact hy
  have hxeq := eq_two_pow_oddPart hx
  have hyeq := eq_two_pow_oddPart hypos
  have hle : val2 x ≤ val2 y := Nat.le_of_lt h
  have hy' : y = 2 ^ val2 x * (2 ^ (val2 y - val2 x) * oddPart y) := by
    have hsum : val2 y = val2 x + (val2 y - val2 x) := (Nat.add_sub_of_le hle).symm
    have hpow : 2 ^ val2 y = 2 ^ val2 x * 2 ^ (val2 y - val2 x) := by
      conv => lhs; rw [hsum]
      rw [Nat.pow_add]
    calc
      y = 2 ^ val2 y * oddPart y := hyeq
      _ = (2 ^ val2 x * 2 ^ (val2 y - val2 x)) * oddPart y := by rw [hpow]
      _ = 2 ^ val2 x * (2 ^ (val2 y - val2 x) * oddPart y) := by rw [Nat.mul_assoc]
  have hsum :
      x + y = 2 ^ val2 x * (oddPart x + 2 ^ (val2 y - val2 x) * oddPart y) := by
    have hxadd :
        x + y =
          2 ^ val2 x * oddPart x +
            2 ^ val2 x * (2 ^ (val2 y - val2 x) * oddPart y) :=
      (congrArg (fun t => t + y) hxeq).trans
        (congrArg (fun t => 2 ^ val2 x * oddPart x + t) hy')
    rw [← Nat.mul_add] at hxadd
    exact hxadd
  have hst : 1 ≤ val2 y - val2 x := by omega
  have heven : (2 ^ (val2 y - val2 x) * oddPart y) % 2 = 0 := by
    have : (2 ^ (val2 y - val2 x)) % 2 = 0 := two_pow_mod_two hst
    rw [Nat.mul_mod, this, Nat.zero_mul]
  have hodd :
      (oddPart x + 2 ^ (val2 y - val2 x) * oddPart y) % 2 = 1 := by
    have hxodd : oddPart x % 2 = 1 := oddPart_odd hx
    omega
  have hpos : 0 < x + y := Nat.add_pos_left hx y
  exact (val2_unique hpos hsum hodd).symm

theorem val2_add_of_lt_or_zero {x y : Nat} (hx : 0 < x)
    (h : y = 0 ∨ val2 x < val2 y) : val2 (x + y) = val2 x := by
  cases h with
  | inl hy => simp [hy]
  | inr hlt => exact val2_add_of_lt hlt hx

theorem val2_add_gt {x y s : Nat}
    (hx : x = 0 ∨ s < val2 x) (hy : y = 0 ∨ s < val2 y) :
    x + y = 0 ∨ s < val2 (x + y) := by
  cases hx with
  | inl hx0 =>
    subst hx0
    simpa using hy
  | inr hxlt =>
    cases hy with
    | inl hy0 =>
      subst hy0
      simpa using Or.inr hxlt
    | inr hylt =>
      have hxpos : 0 < x := by
        cases Nat.eq_zero_or_pos x with
        | inl hx0 =>
          subst hx0
          rw [val2_zero] at hxlt
          omega
        | inr h => exact h
      have hypos : 0 < y := by
        cases Nat.eq_zero_or_pos y with
        | inl hy0 =>
          subst hy0
          rw [val2_zero] at hylt
          omega
        | inr h => exact h
      right
      cases Nat.lt_or_ge (val2 x) (val2 y) with
      | inl hlt =>
        have : val2 (x + y) = val2 x := val2_add_of_lt hlt hxpos
        omega
      | inr hge =>
        cases Nat.eq_or_lt_of_le hge with
        | inl heq =>
          have hxeq := eq_two_pow_oddPart hxpos
          have hyeq := eq_two_pow_oddPart hypos
          have hsum : x + y = 2 ^ val2 x * (oddPart x + oddPart y) := by
            have hyeq' : y = 2 ^ val2 x * oddPart y := by
              rw [heq] at hyeq
              exact hyeq
            have hxadd :
                x + y = 2 ^ val2 x * oddPart x + 2 ^ val2 x * oddPart y :=
              (congrArg (fun t => t + y) hxeq).trans
                (congrArg (fun t => 2 ^ val2 x * oddPart x + t) hyeq')
            rw [← Nat.mul_add] at hxadd
            exact hxadd
          have hsumeven : (oddPart x + oddPart y) % 2 = 0 := by
            have hxodd : oddPart x % 2 = 1 := oddPart_odd hxpos
            have hyodd : oddPart y % 2 = 1 := oddPart_odd hypos
            omega
          have hsumpos : 0 < oddPart x + oddPart y :=
            Nat.add_pos_left (oddPart_pos hxpos) _
          have hval : 1 ≤ val2 (oddPart x + oddPart y) :=
            val2_pos_of_even hsumpos hsumeven
          have : val2 (x + y) = val2 x + val2 (oddPart x + oddPart y) := by
            rw [hsum, val2_mul (Nat.two_pow_pos _) hsumpos, val2_two_pow]
          omega
        | inr hgt =>
          have : val2 (x + y) = val2 y := by
            rw [Nat.add_comm]
            exact val2_add_of_lt hgt hypos
          omega

theorem val2_sum_gt {n s : Nat} {f : Nat → Nat}
    (h : ∀ i, i < n → f i = 0 ∨ s < val2 (f i)) :
    sumRange n f = 0 ∨ s < val2 (sumRange n f) := by
  induction n with
  | zero =>
    left
    rfl
  | succ n ih =>
    have ih' := ih fun i hi => h i (Nat.lt_succ_of_le (Nat.le_of_lt hi))
    have ht := h n (Nat.lt_succ_self n)
    rw [sumRange_succ]
    exact val2_add_gt ih' ht

theorem val2_sum_unique_min {n k : Nat} {f : Nat → Nat}
    (hk : k < n) (hpos : 0 < f k)
    (hmin : ∀ i, i < n → i ≠ k → f i = 0 ∨ val2 (f k) < val2 (f i)) :
    val2 (sumRange n f) = val2 (f k) := by
  have hsplit :
      sumRange n f = f k + sumRange n (fun i => if i = k then 0 else f i) := by
    have h1 :
        sumRange n f =
          sumRange n (fun i =>
            (if i = k then f k else 0) + (if i = k then 0 else f i)) := by
      congr
      funext i
      by_cases h : i = k <;> simp [h]
    rw [h1, sumRange_add, sumRange_indicator_at hk]
  rw [hsplit]
  have hrest :
      sumRange n (fun i => if i = k then 0 else f i) = 0 ∨
        val2 (f k) < val2 (sumRange n (fun i => if i = k then 0 else f i)) := by
    refine val2_sum_gt fun i hi => ?_
    by_cases hik : i = k
    · subst hik
      left
      simp
    · simp [hik]
      exact hmin i hi hik
  exact val2_add_of_lt_or_zero hpos hrest

/-! ### Tail of `sumRange` and `a n - 1` -/

private theorem sumRange_tail (n : Nat) (f : Nat → Nat) :
    sumRange (n + 1) f = f 0 + sumRange n fun i => f (i + 1) := by
  induction n with
  | zero => simp [sumRange_succ, sumRange_zero]
  | succ n ih =>
    rw [sumRange_succ, ih, sumRange_succ, Nat.add_assoc]

theorem term_zero (n : Nat) : term n 0 = 1 := by
  rw [term, Nat.sub_zero, fact_one]
  exact one_pow _

theorem term_last {n : Nat} (hn : 1 ≤ n) : term n (n - 1) = fact n := by
  have h1 : n - (n - 1) = 1 := by omega
  have h2 : n - 1 + 1 = n := by omega
  rw [term, h1, fact_one, Nat.pow_one, h2]

theorem term_val2 (n i : Nat) :
    val2 (term n i) = fact (n - i) * val2Fact (i + 1) := by
  rw [term, val2_pow (fact_pos (n - i)), val2_fact]

theorem n_lt_fact_pred {n : Nat} (hn : 5 ≤ n) : n < fact (n - 1) := by
  refine le_induction (fun n => n < fact (n - 1)) hn ?base ?step
  · decide
  · intro k hk _ih
    have hrec : fact k = fact (k - 1) * k :=
      (fact_sub_one (by omega : 1 ≤ k)).symm
    have h24 : 24 ≤ fact (k - 1) := by
      have : 4 ≤ k - 1 := by omega
      simpa [fact_four] using fact_le_of_le this
    have hle : 24 * k ≤ fact (k - 1) * k := by
      rw [Nat.mul_comm (fact (k - 1)), Nat.mul_comm 24]
      exact Nat.mul_le_mul_left k h24
    have hlt : k + 1 < 24 * k := by omega
    exact hrec ▸ Nat.lt_of_lt_of_le hlt hle

theorem n_lt_fact_sub_two {n : Nat} (hn : 5 ≤ n) : n < fact (n - 2) := by
  refine le_induction (fun n => n < fact (n - 2)) hn ?base ?step
  · decide
  · intro k hk _ih
    have hrec : fact (k - 1) = fact (k - 2) * (k - 1) := by
      have : k - 1 - 1 = k - 2 := by omega
      rw [← fact_sub_one (n := k - 1) (by omega), this]
    have h6 : 6 ≤ fact (k - 2) := by
      have : 3 ≤ k - 2 := by omega
      simpa [fact_three] using fact_le_of_le this
    have hle : 6 * (k - 1) ≤ fact (k - 2) * (k - 1) := by
      rw [Nat.mul_comm (fact (k - 2)), Nat.mul_comm 6]
      exact Nat.mul_le_mul_left (k - 1) h6
    have hlt : k + 1 < 6 * (k - 1) := by omega
    exact hrec ▸ Nat.lt_of_lt_of_le hlt hle

theorem five_half_gt_self {n : Nat} (hn : 6 ≤ n) :
    n < 5 * ((n - 2) / 2) := by
  refine le_induction (fun n => n < 5 * ((n - 2) / 2)) hn ?base ?step
  · decide
  · intro k hk ih
    have : (k + 1 - 2) / 2 = (k - 1) / 2 := by omega
    have hstep :
        (k - 1) / 2 = (k - 2) / 2 ∨ (k - 1) / 2 = (k - 2) / 2 + 1 := by omega
    omega

theorem half_add_le_self (n : Nat) : (n - 1) / 2 + n / 2 ≤ n := by omega

theorem val2Fact_n_eq {n : Nat} (hn : 1 ≤ n) :
    val2Fact n = val2Fact (n - 1) + val2 n := by
  have : n = n - 1 + 1 := by omega
  rw [this, val2Fact_succ]
  simp

theorem val2Fact_eq_add2 {n : Nat} (hn : 2 ≤ n) :
    val2Fact n = val2Fact (n - 2) + val2 (n - 1) + val2 n := by
  have hn1 : 1 ≤ n := by omega
  have hn2 : n - 1 = n - 2 + 1 := by omega
  rw [val2Fact_n_eq hn1, hn2, val2Fact_succ]

theorem val2Fact_eq_add3 {n : Nat} (hn : 3 ≤ n) :
    val2Fact n = val2Fact (n - 3) + val2 (n - 2) + val2 (n - 1) + val2 n := by
  have hn2 : 2 ≤ n := by omega
  have h : n - 2 = n - 3 + 1 := by omega
  rw [val2Fact_eq_add2 hn2, h, val2Fact_succ]

theorem val2Fact_lt_six_mul {n : Nat} (hn : 6 ≤ n) :
    val2Fact n < 6 * val2Fact (n - 2) := by
  have hdecomp := val2Fact_eq_add2 (by omega : 2 ≤ n)
  have hR : val2 (n - 1) + val2 n ≤ (n - 1) / 2 + n / 2 :=
    Nat.add_le_add (val2_le_half (n - 1)) (val2_le_half n)
  have hL : 5 * ((n - 2) / 2) ≤ 5 * val2Fact (n - 2) :=
    Nat.mul_le_mul_left 5 (val2Fact_ge_half (n - 2))
  have hlt : (n - 1) / 2 + n / 2 < 5 * ((n - 2) / 2) :=
    Nat.lt_of_le_of_lt (half_add_le_self n) (five_half_gt_self hn)
  omega

theorem three_halves_le (n : Nat) :
    (n - 2) / 2 + (n - 1) / 2 + n / 2 ≤ 3 * n / 2 := by omega

theorem three_n_lt_23_half {n : Nat} (hn : 7 ≤ n) :
    3 * n < 23 * ((n - 3) / 2) := by
  refine le_induction (fun n => 3 * n < 23 * ((n - 3) / 2)) hn ?base ?step
  · decide
  · intro k hk ih
    have : (k + 1 - 3) / 2 = (k - 2) / 2 := by omega
    have : (k - 2) / 2 = (k - 3) / 2 ∨ (k - 2) / 2 = (k - 3) / 2 + 1 := by
      omega
    omega

theorem val2Fact_lt_24_mul {n : Nat} (hn : 7 ≤ n) :
    val2Fact n < 24 * val2Fact (n - 3) := by
  have hdecomp := val2Fact_eq_add3 (by omega : 3 ≤ n)
  have hR :
      val2 (n - 2) + val2 (n - 1) + val2 n ≤
        (n - 2) / 2 + (n - 1) / 2 + n / 2 :=
    Nat.add_le_add (Nat.add_le_add (val2_le_half (n - 2))
      (val2_le_half (n - 1))) (val2_le_half n)
  have hL : 23 * ((n - 3) / 2) ≤ 23 * val2Fact (n - 3) :=
    Nat.mul_le_mul_left 23 (val2Fact_ge_half (n - 3))
  have hsum : (n - 2) / 2 + (n - 1) / 2 + n / 2 ≤ 3 * n := by omega
  have h23 := three_n_lt_23_half hn
  omega

theorem n_lt_120_mul_half {n : Nat} (hn : 8 ≤ n) :
    n < 120 * ((n - 4) / 2) := by
  refine le_induction (fun n => n < 120 * ((n - 4) / 2)) hn ?base ?step
  · decide
  · intro k _hk _ih
    have : (k + 1 - 4) / 2 = (k - 3) / 2 := by omega
    have : (k - 3) / 2 = (k - 4) / 2 ∨ (k - 3) / 2 = (k - 4) / 2 + 1 := by
      omega
    omega

theorem n_lt_720_mul_half {n : Nat} (hn : 9 ≤ n) :
    n < 720 * ((n - 5) / 2) := by
  refine le_induction (fun n => n < 720 * ((n - 5) / 2)) hn ?base ?step
  · decide
  · intro k _hk _ih
    have : (k + 1 - 5) / 2 = (k - 4) / 2 := by omega
    have : (k - 4) / 2 = (k - 5) / 2 ∨ (k - 4) / 2 = (k - 5) / 2 + 1 := by
      omega
    omega

theorem n_lt_5040_mul_half {n : Nat} (hn : 10 ≤ n) :
    n < 5040 * ((n - 6) / 2) := by
  refine le_induction (fun n => n < 5040 * ((n - 6) / 2)) hn ?base ?step
  · decide
  · intro k _hk _ih
    have : (k + 1 - 6) / 2 = (k - 5) / 2 := by omega
    have : (k - 5) / 2 = (k - 6) / 2 ∨ (k - 5) / 2 = (k - 6) / 2 + 1 := by
      omega
    omega

theorem n_lt_40320_mul_half {n : Nat} (hn : 11 ≤ n) :
    n < 40320 * ((n - 7) / 2) := by
  refine le_induction (fun n => n < 40320 * ((n - 7) / 2)) hn ?base ?step
  · decide
  · intro k _hk _ih
    have : (k + 1 - 7) / 2 = (k - 6) / 2 := by omega
    have : (k - 6) / 2 = (k - 7) / 2 ∨ (k - 6) / 2 = (k - 7) / 2 + 1 := by
      omega
    omega

theorem fact_seven : fact 7 = 5040 := by
  rw [fact_succ, fact_six]

theorem fact_eight : fact 8 = 40320 := by
  rw [fact_succ, fact_seven]

theorem fact_nine : fact 9 = 362880 := by
  rw [fact_succ, fact_eight]

theorem sq_le_fact {m : Nat} (hm : 4 ≤ m) : m * m ≤ fact m := by
  refine le_induction (fun m => m * m ≤ fact m) hm ?base ?step
  · decide
  · intro k hk ih
    have hk2 : 2 ≤ k := by omega
    have hkk : k + 1 ≤ k * k := by
      have h2k : 2 * k ≤ k * k := by
        have := Nat.mul_le_mul_left k hk2
        rwa [Nat.mul_comm k 2] at this
      have : 2 * k = k + k := Nat.two_mul k
      omega
    have hbound : (k + 1) * (k + 1) ≤ k * k * (k + 1) :=
      Nat.mul_le_mul_right (k + 1) hkk
    have hmul : k * k * (k + 1) ≤ fact (k + 1) := by
      rw [fact_succ]
      exact Nat.mul_le_mul_right (k + 1) ih
    exact Nat.le_trans hbound hmul

theorem n_lt_half_sq {n : Nat} (hn : 12 ≤ n) :
    n < (n / 2) * (n / 2) := by
  refine le_induction (fun n => n < (n / 2) * (n / 2)) hn ?base ?step
  · decide
  · intro k hk _ih
    have h6 : 6 ≤ k / 2 := by omega
    have hcases : (k + 1) / 2 = k / 2 ∨ (k + 1) / 2 = k / 2 + 1 := by omega
    cases hcases with
    | inl hsame =>
      rw [hsame]
      have hmul : 6 * (k / 2) ≤ (k / 2) * (k / 2) :=
        Nat.mul_le_mul_right (k / 2) h6
      have hlt : k + 1 < 6 * (k / 2) := by
        have : 12 ≤ k := hk
        omega
      exact Nat.lt_of_lt_of_le hlt hmul
    | inr hsucc =>
      rw [hsucc]
      have hmul : 6 * (k / 2 + 1) ≤ (k / 2 + 1) * (k / 2 + 1) :=
        Nat.mul_le_mul_right (k / 2 + 1) (Nat.le_trans h6 (Nat.le_succ _))
      have hlt : k + 1 < 6 * (k / 2 + 1) := by
        have : 12 ≤ k := hk
        omega
      exact Nat.lt_of_lt_of_le hlt hmul

theorem n_lt_362880_half {n : Nat} (hn : 19 ≤ n) :
    n < 362880 * ((n / 2 + 2) / 2) := by
  refine le_induction
      (fun n => n < 362880 * ((n / 2 + 2) / 2)) hn ?base ?step
  · decide
  · intro k _hk _ih
    have : (k + 1) / 2 + 2 = k / 2 + 2 ∨
        (k + 1) / 2 + 2 = k / 2 + 3 := by omega
    have : ((k + 1) / 2 + 2) / 2 =
        (k / 2 + 2) / 2 ∨
        ((k + 1) / 2 + 2) / 2 = (k / 2 + 2) / 2 + 1 := by omega
    omega


theorem fact_ge_seven {k : Nat} (h : 7 ≤ k) : 5040 ≤ fact k := by
  simpa [fact_seven] using fact_le_of_le h

theorem val2Fact_pos_of_two {m : Nat} (h : 2 ≤ m) : 1 ≤ val2Fact m := by
  have : val2Fact 2 ≤ val2Fact m := val2Fact_mono h
  simpa [val2Fact_two] using this

theorem val2_term_gt_fact {n i : Nat} (hn : 5 ≤ n) (hi : 1 ≤ i)
    (hin : i ≤ n - 2) : val2Fact n < val2 (term n i) := by
  have hv : val2 (term n i) = fact (n - i) * val2Fact (i + 1) :=
    term_val2 n i
  have hkey : val2 n < val2Fact (n - 1) := val2Fact_pred_gt_val2 hn
  have hleF : val2Fact n ≤ n - 1 := val2Fact_le_pred (by omega)
  have hcases : n - i = 2 ∨ n - i = 3 ∨ 4 ≤ n - i := by omega
  rcases hcases with hk2 | h3 | h4
  · have hi' : i + 1 = n - 1 := by omega
    have hf : val2Fact n = val2Fact (n - 1) + val2 n :=
      val2Fact_n_eq (by omega)
    have hdouble :
        val2Fact (n - 1) + val2Fact (n - 1) = 2 * val2Fact (n - 1) :=
      (Nat.two_mul _).symm
    have hlt : val2Fact (n - 1) + val2 n < 2 * val2Fact (n - 1) := by
      rw [← hdouble]
      exact Nat.add_lt_add_left hkey _
    rw [hv, hk2, fact_two, hi', hf]
    exact hlt
  · have hi' : i + 1 = n - 2 := by omega
    have hn6 : n = 5 ∨ 6 ≤ n := by omega
    cases hn6 with
    | inl h5 =>
      subst h5
      have hi2 : i = 2 := by omega
      subst hi2
      have hval5 : val2Fact 5 = 3 := by
        rw [val2Fact_succ, val2Fact_four, val2_odd (by decide)]
      rw [hv, hval5, fact_three, val2Fact_three]
      decide
    | inr h6 =>
      rw [hv, h3, fact_three, hi']
      exact val2Fact_lt_six_mul h6
  · have hcases' : i = 1 ∨ i = 2 ∨ 3 ≤ i := by omega
    rcases hcases' with hi1 | hi2 | hi3
    · subst hi1
      rw [hv, val2Fact_two, Nat.mul_one]
      exact Nat.lt_of_le_of_lt hleF (Nat.lt_of_le_of_lt (Nat.sub_le n 1) (n_lt_fact_pred hn))
    · subst hi2
      rw [hv, val2Fact_three, Nat.mul_one]
      exact Nat.lt_of_le_of_lt hleF (Nat.lt_of_le_of_lt (Nat.sub_le n 1) (n_lt_fact_sub_two hn))
    · have hn7 : 7 ≤ n := by omega
      rw [hv]
      have hge1 : 1 ≤ val2Fact (i + 1) := val2Fact_pos_of_two (by omega)
      have hsplit : i = n - 4 ∨ i ≤ n - 5 := by omega
      cases hsplit with
      | inl heq =>
        have hni : n - i = 4 := by omega
        have hi' : i + 1 = n - 3 := by omega
        rw [hni, hi', fact_four]
        exact val2Fact_lt_24_mul hn7
      | inr hle =>
        have hsplit' : i = n - 5 ∨ i ≤ n - 6 := by omega
        cases hsplit' with
        | inl heq =>
          have hni : n - i = 5 := by omega
          have hi' : i + 1 = n - 4 := by omega
          rw [hni, hi', fact_five]
          have hn8 : 8 ≤ n := by omega
          have hlt : n < 120 * val2Fact (n - 4) :=
            Nat.lt_of_lt_of_le (n_lt_120_mul_half hn8)
              (Nat.mul_le_mul_left 120 (val2Fact_ge_half (n - 4)))
          exact Nat.lt_of_le_of_lt hleF (Nat.lt_of_le_of_lt (Nat.sub_le n 1) hlt)
        | inr h6 =>
          have hsplit'' : i = n - 6 ∨ i ≤ n - 7 := by omega
          cases hsplit'' with
          | inl heq =>
            have hni : n - i = 6 := by omega
            have hi' : i + 1 = n - 5 := by omega
            rw [hni, hi', fact_six]
            have hn9 : 9 ≤ n := by omega
            have hlt : n < 720 * val2Fact (n - 5) :=
              Nat.lt_of_lt_of_le (n_lt_720_mul_half hn9)
                (Nat.mul_le_mul_left 720 (val2Fact_ge_half (n - 5)))
            exact Nat.lt_of_le_of_lt hleF (Nat.lt_of_le_of_lt (Nat.sub_le n 1) hlt)
          | inr h7 =>
            have hk7 : 7 ≤ n - i := by omega
            have hsplit7 : i = n - 7 ∨ i ≤ n - 8 := by omega
            cases hsplit7 with
            | inl heq =>
              have hni : n - i = 7 := by omega
              have hi' : i + 1 = n - 6 := by omega
              rw [hni, hi', fact_seven]
              have hn10 : 10 ≤ n := by omega
              have hlt : n < 5040 * val2Fact (n - 6) :=
                Nat.lt_of_lt_of_le (n_lt_5040_mul_half hn10)
                  (Nat.mul_le_mul_left 5040 (val2Fact_ge_half (n - 6)))
              exact Nat.lt_of_le_of_lt hleF (Nat.lt_of_le_of_lt (Nat.sub_le n 1) hlt)
            | inr h8 =>
              have hk8 : 8 ≤ n - i := by omega
              have hsplit8 : n - i = 8 ∨ 9 ≤ n - i := by omega
              cases hsplit8 with
              | inl heq8 =>
                have hi' : i + 1 = n - 7 := by omega
                rw [heq8, hi', fact_eight]
                have hn11 : 11 ≤ n := by omega
                have hlt : n < 40320 * val2Fact (n - 7) :=
                  Nat.lt_of_lt_of_le (n_lt_40320_mul_half hn11)
                    (Nat.mul_le_mul_left 40320 (val2Fact_ge_half (n - 7)))
                exact Nat.lt_of_le_of_lt hleF
                  (Nat.lt_of_le_of_lt (Nat.sub_le n 1) hlt)
              | inr h9 =>
                have hn12 : 12 ≤ n := by omega
                have hf9 : 362880 ≤ fact (n - i) := by
                  simpa [fact_nine] using fact_le_of_le h9
                have hspliti : i ≤ n / 2 ∨ n / 2 + 1 ≤ i := by omega
                cases hspliti with
                | inl hile =>
                  have hhalf : n / 2 ≤ n - i := by omega
                  have h4 : 4 ≤ n / 2 := by omega
                  have hfact : (n / 2) * (n / 2) ≤ fact (n - i) :=
                    Nat.le_trans (sq_le_fact h4) (fact_le_of_le hhalf)
                  have hltn : n < fact (n - i) :=
                    Nat.lt_of_lt_of_le (n_lt_half_sq hn12) hfact
                  have hprod : n < fact (n - i) * val2Fact (i + 1) := by
                    have : fact (n - i) * 1 ≤
                        fact (n - i) * val2Fact (i + 1) :=
                      Nat.mul_le_mul_left _ hge1
                    omega
                  exact Nat.lt_of_le_of_lt hleF
                    (Nat.lt_of_le_of_lt (Nat.sub_le n 1) hprod)
                | inr hige =>
                  have hn19 : 19 ≤ n := by
                    have : n / 2 + 1 ≤ n - 9 := Nat.le_trans hige (by omega)
                    omega
                  have hle_i : n / 2 + 2 ≤ i + 1 := by omega
                  have hdiv : (n / 2 + 2) / 2 ≤ (i + 1) / 2 :=
                    Nat.div_le_div_right hle_i
                  have hlt : n < 362880 * val2Fact (i + 1) := by
                    have h1 := n_lt_362880_half hn19
                    have h2 : 362880 * ((n / 2 + 2) / 2) ≤
                        362880 * ((i + 1) / 2) :=
                      Nat.mul_le_mul_left 362880 hdiv
                    have h3 : 362880 * ((i + 1) / 2) ≤
                        362880 * val2Fact (i + 1) :=
                      Nat.mul_le_mul_left 362880 (val2Fact_ge_half (i + 1))
                    omega
                  have h4 : 362880 * val2Fact (i + 1) ≤
                      fact (n - i) * val2Fact (i + 1) :=
                    Nat.mul_le_mul_right _ hf9
                  exact Nat.lt_of_le_of_lt hleF
                    (Nat.lt_of_le_of_lt (Nat.sub_le n 1)
                      (Nat.lt_of_lt_of_le hlt h4))

theorem a_eq_one_add_tail {n : Nat} (hn : 1 ≤ n) :
    a n = 1 + sumRange (n - 1) (fun i => term n (i + 1)) := by
  have ha : a n = sumRange n (term n) := rfl
  have hn' : n = n - 1 + 1 := by omega
  rw [ha, hn', sumRange_tail, term_zero]
  simp

theorem a_sub_one {n : Nat} (hn : 1 ≤ n) :
    a n - 1 = sumRange (n - 1) (fun i => term n (i + 1)) := by
  have h := a_eq_one_add_tail hn
  omega

theorem val2_a_sub_one {n : Nat} (hn : 5 ≤ n) :
    val2 (a n - 1) = val2 (fact n) := by
  have hn1 : 1 ≤ n := by omega
  have hsum := a_sub_one hn1
  have hlast : term n (n - 1) = fact n := term_last hn1
  have hk : n - 2 < n - 1 := by omega
  have hidx : n - 2 + 1 = n - 1 := by omega
  have hpos : 0 < term n (n - 1) := by
    rw [hlast]
    exact fact_pos n
  have hpos' : 0 < (fun i => term n (i + 1)) (n - 2) := by
    simpa [hidx] using hpos
  have hmin :
      ∀ i, i < n - 1 → i ≠ n - 2 →
        (fun j => term n (j + 1)) i = 0 ∨
          val2 ((fun j => term n (j + 1)) (n - 2)) <
            val2 ((fun j => term n (j + 1)) i) := by
    intro i hi hik
    right
    have hi1 : 1 ≤ i + 1 := by omega
    have hin : i + 1 ≤ n - 2 := by omega
    have hgt : val2Fact n < val2 (term n (i + 1)) :=
      val2_term_gt_fact hn hi1 hin
    have : val2 (term n (n - 1)) = val2Fact n := by
      rw [hlast, val2_fact]
    simpa [hidx] using (show val2 (term n (n - 1)) < val2 (term n (i + 1)) by
      omega)
  have huniq :
      val2 (sumRange (n - 1) (fun i => term n (i + 1))) =
        val2 ((fun i => term n (i + 1)) (n - 2)) :=
    val2_sum_unique_min hk hpos' hmin
  rw [hsum, huniq]
  simp only []
  rw [hidx, hlast, val2_fact]

theorem val2_base_sub_one_of_pow {n b e : Nat} (hn : 5 ≤ n)
    (he : e % 2 = 1) (hb : b % 2 = 1) (hab : a n = b ^ e) :
    val2 (b - 1) = val2 (fact n) := by
  have hx1 : 1 ≤ b := by omega
  have ha : val2 (a n - 1) = val2 (fact n) := val2_a_sub_one hn
  rw [hab] at ha
  have := val2_odd_pow_sub_one hb he hx1
  omega

end LeanA113258
