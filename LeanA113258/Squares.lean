import LeanA113258.Defs

namespace LeanA113258

/-!
  For `n ≥ 3`, `(n-1)!` is even, so `2^{(n-1)!}` is already a square
  (and an `e`-th power whenever `e ∣ (n-1)!`).
  Remainder `δ = a n - 2^{(n-1)!}` is positive; for `n ≥ 7` it is
  smaller than the next-square gap, and also smaller than the
  `(b+1)^e - b^e` gap when `e ∣ (n-1)!`.

  Not being a square is weaker than not being a perfect power.
  The remaining case is `gcd(e, (n-1)!) = 1` (hence `e ≥ n`).
-/

def mainTerm (n : Nat) : Nat := 2 ^ fact (n - 1)

def term (n i : Nat) : Nat := fact (i + 1) ^ fact (n - i)

def rest (n i : Nat) : Nat := if i = 1 then 0 else term n i

def delta (n : Nat) : Nat := sumRange n (rest n)

/-- Exponent in `n * 3^{(n-2)!} < 2^{…}` after cancelling `2^{(n-2)!}`. -/
def halfGapExp (n : Nat) : Nat := (n - 3) * fact (n - 2) / 2

theorem le_induction (P : Nat → Prop) {m n : Nat} (hn : m ≤ n) (base : P m)
    (step : ∀ k, m ≤ k → P k → P (k + 1)) : P n := by
  induction n with
  | zero =>
    have hm : m = 0 := Nat.eq_zero_of_le_zero hn
    exact hm ▸ base
  | succ n ih =>
    cases Nat.eq_or_lt_of_le hn with
    | inl he => exact he ▸ base
    | inr hlt =>
      exact step n (Nat.le_of_lt_succ hlt) (ih (Nat.le_of_lt_succ hlt))

theorem fact_pos (n : Nat) : 0 < fact n := by
  induction n with
  | zero => decide
  | succ n ih => exact Nat.mul_pos ih (Nat.succ_pos n)

theorem fact_one : fact 1 = 1 := rfl
theorem fact_two : fact 2 = 2 := rfl
theorem fact_three : fact 3 = 6 := rfl
theorem fact_four : fact 4 = 24 := rfl
theorem fact_five : fact 5 = 120 := rfl
theorem fact_six : fact 6 = 720 := rfl

theorem fact_le_of_le {m n : Nat} (h : m ≤ n) : fact m ≤ fact n := by
  induction n with
  | zero => simp [Nat.eq_zero_of_le_zero h]
  | succ n ih =>
    cases Nat.eq_or_lt_of_le h with
    | inl he => simp [he]
    | inr hlt =>
      refine Nat.le_trans (ih (Nat.le_of_lt_succ hlt)) ?_
      rw [fact_succ]
      exact Nat.le_mul_of_pos_right _ (Nat.succ_pos n)

theorem two_dvd_fact {k : Nat} (h : 2 ≤ k) : 2 ∣ fact k := by
  refine le_induction (fun k => 2 ∣ fact k) h ?base ?step
  · exact ⟨1, rfl⟩
  · intro n _hn ih
    rw [fact_succ]
    exact Nat.dvd_mul_right_of_dvd ih (n + 1)

theorem dvd_fact_of_le {k n : Nat} (hk : 0 < k) (hkn : k ≤ n) : k ∣ fact n := by
  induction n with
  | zero =>
    have : k = 0 := Nat.eq_zero_of_le_zero hkn
    omega
  | succ n ih =>
    cases Nat.eq_or_lt_of_le hkn with
    | inl he =>
      subst he
      rw [fact_succ]
      exact Nat.dvd_mul_left (n + 1) (fact n)
    | inr hlt =>
      rw [fact_succ]
      exact Nat.dvd_mul_right_of_dvd (ih (Nat.le_of_lt_succ hlt)) (n + 1)

theorem fact_sub_one {n : Nat} (hn : 1 ≤ n) : fact (n - 1) * n = fact n := by
  cases n with
  | zero => omega
  | succ n => rw [Nat.add_one_sub_one, fact_succ, Nat.mul_comm]

theorem fact_pred_eq {n : Nat} (hn : 2 ≤ n) :
    fact (n - 1) = (n - 1) * fact (n - 2) := by
  have h1 : 1 ≤ n - 1 := by omega
  have : n - 1 - 1 = n - 2 := by omega
  rw [← fact_sub_one h1, this, Nat.mul_comm]

theorem two_pow_even_is_square {k : Nat} (h : 2 ∣ k) :
    ∃ s : Nat, 2 ^ k = s ^ 2 := by
  obtain ⟨t, ht⟩ := h
  refine ⟨2 ^ t, ?_⟩
  calc
    2 ^ k = 2 ^ (2 * t) := by rw [ht, Nat.mul_comm]
    _ = 2 ^ (t + t) := by rw [Nat.two_mul]
    _ = 2 ^ t * 2 ^ t := Nat.pow_add 2 t t
    _ = (2 ^ t) ^ 2 := (Nat.pow_two (2 ^ t)).symm

theorem term_one (n : Nat) : term n 1 = mainTerm n := by
  simp [term, mainTerm, fact_two]

theorem term_eq_split (n i : Nat) :
    term n i = (if i = 1 then mainTerm n else 0) + rest n i := by
  unfold rest
  by_cases h : i = 1
  · simp [h, term_one]
  · simp [h]

theorem sumRange_add (n : Nat) (f g : Nat → Nat) :
    sumRange n (fun i => f i + g i) = sumRange n f + sumRange n g := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [sumRange_succ, sumRange_succ, sumRange_succ, ih]
    omega

theorem sumRange_indicator_one {n c : Nat} (hn : 2 ≤ n) :
    sumRange n (fun i => if i = 1 then c else 0) = c := by
  refine le_induction (fun n => sumRange n (fun i => if i = 1 then c else 0) = c) hn ?base ?step
  · simp [sumRange_succ, sumRange_zero]
  · intro k _hk ih
    rw [sumRange_succ, ih]
    have : k ≠ 1 := by omega
    simp [this]

theorem a_eq_main_add_delta {n : Nat} (hn : 2 ≤ n) :
    a n = mainTerm n + delta n := by
  have : a n = sumRange n (term n) := rfl
  rw [this]
  have hfun : term n = fun i => (if i = 1 then mainTerm n else 0) + rest n i := by
    funext i
    exact term_eq_split n i
  rw [hfun, sumRange_add, sumRange_indicator_one hn]
  rfl

theorem one_pow (k : Nat) : (1 : Nat) ^ k = 1 := by
  induction k with
  | zero => rfl
  | succ k ih => rw [Nat.pow_succ, ih]

theorem twentyfour_le_six_pow {n : Nat} (hn : 4 ≤ n) :     24 ≤ 6 ^ (n - 2) := by
  refine le_induction (fun n => 24 ≤ 6 ^ (n - 2)) hn ?base ?step
  · decide
  · intro k _hk ih
    have : 6 ^ (k + 1 - 2) = 6 ^ (k - 2) * 6 := by
      have : k + 1 - 2 = k - 2 + 1 := by omega
      rw [this, Nat.pow_succ]
    rw [this]
    exact Nat.le_trans ih (Nat.le_mul_of_pos_right _ (by decide))

theorem succ_le_six_double_gap {n : Nat} (hn : 5 ≤ n) :
    n + 1 ≤ 6 ^ (2 * n - 4) := by
  refine le_induction (fun n => n + 1 ≤ 6 ^ (2 * n - 4)) hn ?base ?step
  · decide
  · intro k _hk ih
    have hpow : 6 ^ (2 * (k + 1) - 4) = 6 ^ (2 * k - 4) * 36 := by
      have : 2 * (k + 1) - 4 = 2 * k - 4 + 2 := by omega
      rw [this, Nat.pow_add]
    rw [hpow]
    have h36 : k + 2 ≤ (k + 1) * 36 := by omega
    exact Nat.le_trans h36 (Nat.mul_le_mul_right 36 ih)

theorem fact_le_six_prod {n : Nat} (hn : 5 ≤ n) :
    fact n ≤ 6 ^ ((n - 2) * (n - 3)) := by
  refine le_induction (fun n => fact n ≤ 6 ^ ((n - 2) * (n - 3))) hn ?base ?step
  · decide
  · intro k hk ih
    rw [fact_succ]
    have hgoal : (k + 1 - 2) * (k + 1 - 3) = (k - 2) * (k - 3) + (2 * k - 4) := by
      have h1 : k + 1 - 2 = k - 1 := by omega
      have h2 : k + 1 - 3 = k - 2 := by omega
      have h3 : 2 * k - 4 = 2 * (k - 2) := by omega
      have h4 : k - 1 = k - 3 + 2 := by omega
      rw [h1, h2, h3, h4, Nat.add_mul, Nat.mul_comm (k - 3)]
    have hpow :
        6 ^ ((k + 1 - 2) * (k + 1 - 3)) =
          6 ^ ((k - 2) * (k - 3)) * 6 ^ (2 * k - 4) := by
      rw [hgoal, Nat.pow_add]
    rw [hpow]
    exact Nat.mul_le_mul ih (succ_le_six_double_gap hk)

theorem fact_sub_two_decomp {n : Nat} (hn : 5 ≤ n) :
    fact (n - 2) = (n - 2) * (n - 3) * fact (n - 4) := by
  have h1 : fact (n - 2) = (n - 2) * fact (n - 3) :=
    fact_pred_eq (n := n - 1) (by omega)
  have h2 : fact (n - 3) = (n - 3) * fact (n - 4) :=
    fact_pred_eq (n := n - 2) (by omega)
  rw [h1, h2, Nat.mul_assoc]

theorem term_le_six_pow {n i : Nat} (hn : 7 ≤ n) (hi : i < n) (hne : i ≠ 1) :
    term n i ≤ 6 ^ fact (n - 2) := by
  unfold term
  have hi' : i = 0 ∨ 2 ≤ i := by omega
  cases hi' with
  | inl h0 =>
    subst h0
    rw [fact_one, one_pow]
    exact Nat.one_le_pow (fact (n - 2)) 6 (by decide)
  | inr _hi2 =>
    have hcases : i = 2 ∨ i = 3 ∨ 4 ≤ i := by omega
    rcases hcases with h2 | h3 | h4
    · subst h2
      rw [fact_three]
      exact Nat.le_refl _
    · subst h3
      rw [fact_four]
      have hrec : fact (n - 2) = (n - 2) * fact (n - 3) :=
        fact_pred_eq (n := n - 1) (by omega)
      have hle : 24 ≤ 6 ^ (n - 2) := twentyfour_le_six_pow (by omega)
      have h1 : 24 ^ fact (n - 3) ≤ (6 ^ (n - 2)) ^ fact (n - 3) :=
        Nat.pow_le_pow_left hle _
      have hpow : (6 ^ (n - 2)) ^ fact (n - 3) = 6 ^ fact (n - 2) := by
        rw [hrec]
        exact (Nat.pow_mul 6 (n - 2) (fact (n - 3))).symm
      exact hpow ▸ h1
    · have hbase : fact (i + 1) ≤ fact n := fact_le_of_le (Nat.succ_le_of_lt hi)
      have hexp : fact (n - i) ≤ fact (n - 4) := fact_le_of_le (by omega)
      have h1 : fact (i + 1) ^ fact (n - i) ≤ fact n ^ fact (n - i) :=
        Nat.pow_le_pow_left hbase _
      have h2 : fact n ^ fact (n - i) ≤ fact n ^ fact (n - 4) :=
        Nat.pow_le_pow_right (fact_pos n) hexp
      have h12 : fact (i + 1) ^ fact (n - i) ≤ fact n ^ fact (n - 4) :=
        Nat.le_trans h1 h2
      have hprod : fact n ≤ 6 ^ ((n - 2) * (n - 3)) := fact_le_six_prod (by omega)
      have h3 :
          fact n ^ fact (n - 4) ≤ (6 ^ ((n - 2) * (n - 3))) ^ fact (n - 4) :=
        Nat.pow_le_pow_left hprod _
      have hde : fact (n - 2) = (n - 2) * (n - 3) * fact (n - 4) :=
        fact_sub_two_decomp (by omega)
      have h4 : (6 ^ ((n - 2) * (n - 3))) ^ fact (n - 4) = 6 ^ fact (n - 2) := by
        rw [← Nat.pow_mul, hde, Nat.mul_assoc]
      exact Nat.le_trans h12 (h4 ▸ h3)

theorem rest_le_six_pow {n i : Nat} (hn : 7 ≤ n) (hi : i < n) :
    rest n i ≤ 6 ^ fact (n - 2) := by
  unfold rest
  by_cases h : i = 1
  · simp [h]
  · simp [h]
    exact term_le_six_pow hn hi h

theorem sumRange_le_const {n c : Nat} {f : Nat → Nat}
    (h : ∀ i, i < n → f i ≤ c) : sumRange n f ≤ n * c := by
  induction n with
  | zero => simp [sumRange]
  | succ n ih =>
    rw [sumRange_succ, Nat.succ_mul]
    exact Nat.add_le_add
      (ih fun i hi => h i (Nat.lt_succ_of_le (Nat.le_of_lt hi)))
      (h n (Nat.lt_succ_self n))

theorem delta_le_n_six_pow {n : Nat} (hn : 7 ≤ n) :
    delta n ≤ n * 6 ^ fact (n - 2) :=
  sumRange_le_const fun i hi => rest_le_six_pow hn hi

theorem rest_zero (n : Nat) : rest n 0 = 1 := by
  simp [rest, term, fact_one, one_pow]

theorem sumRange_ge_first {n : Nat} (f : Nat → Nat) (hn : 1 ≤ n) :
    f 0 ≤ sumRange n f := by
  refine le_induction (fun n => f 0 ≤ sumRange n f) hn ?base ?step
  · simp [sumRange_succ, sumRange_zero]
  · intro k _hk ih
    rw [sumRange_succ]
    exact Nat.le_trans ih (Nat.le_add_right _ _)

theorem delta_pos {n : Nat} (hn : 2 ≤ n) : 0 < delta n := by
  have : 1 ≤ delta n := by
    simpa [delta, rest_zero] using sumRange_ge_first (rest n) (by omega)
  omega

theorem two_mul_halfGapExp {n : Nat} (hn : 4 ≤ n) :
    2 * halfGapExp n = (n - 3) * fact (n - 2) := by
  have hdvd : 2 ∣ (n - 3) * fact (n - 2) :=
    Nat.dvd_mul_left_of_dvd (two_dvd_fact (by omega)) (n - 3)
  simpa [halfGapExp] using Nat.mul_div_cancel' hdvd

theorem half_main_exp {n : Nat} (hn : 4 ≤ n) :
    fact (n - 1) / 2 = fact (n - 2) + halfGapExp n := by
  have hrec : fact (n - 1) = (n - 1) * fact (n - 2) := fact_pred_eq (by omega)
  have hhalf := two_mul_halfGapExp hn
  have hsum : (n - 1) * fact (n - 2) = 2 * fact (n - 2) + (n - 3) * fact (n - 2) := by
    have : n - 1 = 2 + (n - 3) := by omega
    rw [this, Nat.add_mul]
  have : fact (n - 1) = 2 * (fact (n - 2) + halfGapExp n) := by
    rw [hrec, hsum, ← hhalf, Nat.mul_add]
  have hdiv := congrArg (fun z => z / 2) this
  have hcancel : 2 * (fact (n - 2) + halfGapExp n) / 2 =
      fact (n - 2) + halfGapExp n :=
    Nat.mul_div_cancel_left _ (by decide : (0 : Nat) < 2)
  rw [← hcancel, ← hdiv]

theorem seed7 : 7 * 3 ^ 120 < 2 ^ 240 := by native_decide

theorem halfGapExp_seven : halfGapExp 7 = 240 := by
  simp [halfGapExp, fact_five]

theorem succ_le_self_pow {n : Nat} (hn : 3 ≤ n) : n + 1 ≤ n ^ (n - 1) := by
  have hsq : n + 1 ≤ n * n := by
    have : 2 * n ≤ n * n := Nat.mul_le_mul_right n (by omega)
    have : n + n ≤ n * n := by
      rw [Nat.two_mul] at this
      exact this
    omega
  have hpow : n * n ≤ n ^ (n - 1) := by
    have : n ^ 2 ≤ n ^ (n - 1) :=
      Nat.pow_le_pow_of_le (by omega : 1 < n) (by omega : 2 ≤ n - 1)
    simpa [Nat.pow_two] using this
  exact Nat.le_trans hsq hpow

theorem halfGapExp_succ {n : Nat} (hn : 7 ≤ n) :
    halfGapExp (n + 1) =
      halfGapExp n * (n - 1) + (n - 1) * fact (n - 2) / 2 := by
  have hL : 2 * halfGapExp (n + 1) = (n - 2) * fact (n - 1) := by
    simpa using two_mul_halfGapExp (n := n + 1) (by omega)
  have hrec : fact (n - 1) = (n - 1) * fact (n - 2) := fact_pred_eq (by omega)
  have hd : 2 ∣ (n - 1) * fact (n - 2) :=
    Nat.dvd_mul_left_of_dvd (two_dvd_fact (by omega)) (n - 1)
  have hdiv : 2 * ((n - 1) * fact (n - 2) / 2) = (n - 1) * fact (n - 2) :=
    Nat.mul_div_cancel' hd
  have hh : 2 * halfGapExp n = (n - 3) * fact (n - 2) :=
    two_mul_halfGapExp (by omega)
  have hR :
      2 * (halfGapExp n * (n - 1) + (n - 1) * fact (n - 2) / 2) =
        (n - 2) * fact (n - 1) := by
    calc
      2 * (halfGapExp n * (n - 1) + (n - 1) * fact (n - 2) / 2)
          = 2 * (halfGapExp n * (n - 1)) +
              2 * ((n - 1) * fact (n - 2) / 2) := by
            rw [Nat.mul_add]
      _ = (2 * halfGapExp n) * (n - 1) + (n - 1) * fact (n - 2) := by
            rw [Nat.mul_assoc, hdiv]
      _ = (n - 3) * fact (n - 2) * (n - 1) + (n - 1) * fact (n - 2) := by
            rw [hh]
      _ = (n - 1) * fact (n - 2) * (n - 3) + (n - 1) * fact (n - 2) := by
            have hcomm : (n - 3) * fact (n - 2) * (n - 1) =
                (n - 1) * fact (n - 2) * (n - 3) := by
              rw [Nat.mul_assoc, Nat.mul_comm (fact (n - 2)), Nat.mul_assoc,
                Nat.mul_comm (n - 3), Nat.mul_assoc]
            rw [hcomm]
      _ = (n - 1) * fact (n - 2) * (n - 3 + 1) := by
            have hadd :=
              Nat.mul_add ((n - 1) * fact (n - 2)) (n - 3) 1
            rw [Nat.mul_one] at hadd
            exact hadd.symm
      _ = (n - 1) * fact (n - 2) * (n - 2) := by
            have : n - 3 + 1 = n - 2 := by omega
            rw [this]
      _ = (n - 2) * fact (n - 1) := by
            rw [hrec, Nat.mul_comm (n - 1), Nat.mul_assoc,
              Nat.mul_comm (n - 1), Nat.mul_left_comm]
  exact Nat.eq_of_mul_eq_mul_left (by decide : (0 : Nat) < 2) (hL.trans hR.symm)

theorem log_compare_succ {n : Nat} (hn : 7 ≤ n)
    (ih : n * 3 ^ fact (n - 2) < 2 ^ halfGapExp n) :
    (n + 1) * 3 ^ fact (n - 1) < 2 ^ halfGapExp (n + 1) := by
  have hm : fact (n - 1) = (n - 1) * fact (n - 2) := fact_pred_eq (by omega)
  have hpow :
      (n * 3 ^ fact (n - 2)) ^ (n - 1) < (2 ^ halfGapExp n) ^ (n - 1) :=
    Nat.pow_lt_pow_left ih (by omega)
  have ihp : n ^ (n - 1) * 3 ^ fact (n - 1) < 2 ^ (halfGapExp n * (n - 1)) := by
    have hL : (n * 3 ^ fact (n - 2)) ^ (n - 1) =
        n ^ (n - 1) * 3 ^ fact (n - 1) := by
      rw [Nat.mul_pow, ← Nat.pow_mul, Nat.mul_comm (fact (n - 2)), hm]
    have hR : (2 ^ halfGapExp n) ^ (n - 1) = 2 ^ (halfGapExp n * (n - 1)) :=
      (Nat.pow_mul _ _ _).symm
    rw [← hL, ← hR]
    exact hpow
  have hsucc := halfGapExp_succ hn
  have hextra : 0 < 2 ^ ((n - 1) * fact (n - 2) / 2) := Nat.two_pow_pos _
  have hn1 : n + 1 ≤ n ^ (n - 1) := succ_le_self_pow (by omega)
  have h2decomp :
      2 ^ halfGapExp (n + 1) =
        2 ^ (halfGapExp n * (n - 1)) * 2 ^ ((n - 1) * fact (n - 2) / 2) := by
    rw [hsucc, Nat.pow_add]
  have hmul :
      (n + 1) * (n ^ (n - 1) * 3 ^ fact (n - 1)) <
        (n + 1) * 2 ^ (halfGapExp n * (n - 1)) :=
    Nat.mul_lt_mul_of_pos_left ihp (by omega)
  have hbound :
      (n + 1) * 2 ^ (halfGapExp n * (n - 1)) ≤
        n ^ (n - 1) * 2 ^ halfGapExp (n + 1) := by
    rw [h2decomp]
    calc
      (n + 1) * 2 ^ (halfGapExp n * (n - 1))
          ≤ n ^ (n - 1) * 2 ^ (halfGapExp n * (n - 1)) :=
            Nat.mul_le_mul_right _ hn1
      _ ≤ n ^ (n - 1) * 2 ^ (halfGapExp n * (n - 1)) *
            2 ^ ((n - 1) * fact (n - 2) / 2) :=
            Nat.le_mul_of_pos_right _ hextra
      _ = n ^ (n - 1) * (2 ^ (halfGapExp n * (n - 1)) *
            2 ^ ((n - 1) * fact (n - 2) / 2)) := by
            rw [Nat.mul_assoc]
  have hchain :
      (n + 1) * (n ^ (n - 1) * 3 ^ fact (n - 1)) <
        n ^ (n - 1) * 2 ^ halfGapExp (n + 1) :=
    Nat.lt_of_lt_of_le hmul hbound
  have hrearr :
      (n + 1) * (n ^ (n - 1) * 3 ^ fact (n - 1)) =
        n ^ (n - 1) * ((n + 1) * 3 ^ fact (n - 1)) := by
    calc
      (n + 1) * (n ^ (n - 1) * 3 ^ fact (n - 1))
          = ((n + 1) * n ^ (n - 1)) * 3 ^ fact (n - 1) := by
            rw [← Nat.mul_assoc]
      _ = (n ^ (n - 1) * (n + 1)) * 3 ^ fact (n - 1) := by
            rw [Nat.mul_comm (n + 1)]
      _ = n ^ (n - 1) * ((n + 1) * 3 ^ fact (n - 1)) := by
            rw [Nat.mul_assoc]
  rw [hrearr] at hchain
  exact Nat.lt_of_mul_lt_mul_left hchain

set_option maxHeartbeats 2000000

theorem log_compare {n : Nat} (hn : 7 ≤ n) :
    n * 3 ^ fact (n - 2) < 2 ^ halfGapExp n := by
  refine le_induction (fun n => n * 3 ^ fact (n - 2) < 2 ^ halfGapExp n) hn ?base ?step
  · simpa [halfGapExp_seven, fact_five] using seed7
  · intro k hk ih
    exact log_compare_succ hk ih

theorem six_pow_eq_two_three (m : Nat) : (6 : Nat) ^ m = 2 ^ m * 3 ^ m := by
  have : (6 : Nat) = 2 * 3 := rfl
  rw [this, Nat.mul_pow]

theorem n_six_pow_lt_half {n : Nat} (hn : 7 ≤ n) :
    n * 6 ^ fact (n - 2) < 2 ^ (fact (n - 1) / 2) := by
  have hlog := log_compare hn
  have hsix : 6 ^ fact (n - 2) = 2 ^ fact (n - 2) * 3 ^ fact (n - 2) :=
    six_pow_eq_two_three _
  have hsum := half_main_exp (by omega : 4 ≤ n)
  have hdecomp :
      2 ^ (fact (n - 1) / 2) = 2 ^ fact (n - 2) * 2 ^ halfGapExp n := by
    rw [hsum, Nat.pow_add]
  rw [hsix, hdecomp]
  have hrearr :
      n * (2 ^ fact (n - 2) * 3 ^ fact (n - 2)) =
        2 ^ fact (n - 2) * (n * 3 ^ fact (n - 2)) :=
    Nat.mul_left_comm n _ _
  rw [hrearr]
  exact Nat.mul_lt_mul_of_pos_left hlog (Nat.two_pow_pos _)

theorem delta_lt_half_pow {n : Nat} (hn : 7 ≤ n) :
    delta n < 2 ^ (fact (n - 1) / 2) :=
  Nat.lt_of_le_of_lt (delta_le_n_six_pow hn) (n_six_pow_lt_half hn)

theorem main_is_square {n : Nat} (hn : 3 ≤ n) :
    ∃ s : Nat, mainTerm n = s ^ 2 ∧ s = 2 ^ (fact (n - 1) / 2) := by
  have he : 2 ∣ fact (n - 1) := two_dvd_fact (by omega)
  refine ⟨2 ^ (fact (n - 1) / 2), ?_, rfl⟩
  have hK : fact (n - 1) = fact (n - 1) / 2 + fact (n - 1) / 2 := by
    have := Nat.mul_div_cancel' he
    rw [Nat.two_mul] at this
    exact this.symm
  unfold mainTerm
  have hpow : 2 ^ fact (n - 1) =
      2 ^ (fact (n - 1) / 2 + fact (n - 1) / 2) :=
    congrArg (fun t => 2 ^ t) hK
  rw [hpow, Nat.pow_add, Nat.pow_two]

theorem not_eq_square_of_between {m s : Nat}
    (h1 : s ^ 2 < m) (h2 : m < (s + 1) ^ 2) : ¬ ∃ t, m = t ^ 2 := by
  rintro ⟨t, ht⟩
  cases Nat.lt_or_ge t (s + 1) with
  | inl hlt =>
    have : t ^ 2 ≤ s ^ 2 := Nat.pow_le_pow_left (Nat.le_of_lt_succ hlt) 2
    exact Nat.lt_irrefl _ (ht ▸ Nat.lt_of_le_of_lt this h1)
  | inr hge =>
    have : (s + 1) ^ 2 ≤ t ^ 2 := Nat.pow_le_pow_left hge 2
    exact Nat.lt_irrefl _ (ht ▸ Nat.lt_of_lt_of_le h2 this)

/-- `a n` lies strictly between consecutive squares when `n ≥ 7`. -/
theorem not_square {n : Nat} (hn : 7 ≤ n) : ¬ ∃ t, a n = t ^ 2 := by
  obtain ⟨s, hs, hsdef⟩ := main_is_square (n := n) (by omega)
  have hn2 : 2 ≤ n := by omega
  have ha := a_eq_main_add_delta hn2
  have hpos := delta_pos hn2
  have hlt := delta_lt_half_pow hn
  have hmain_lt : s ^ 2 < a n := by
    rw [← hs, ha]
    omega
  have hnext : a n < (s + 1) ^ 2 := by
    have hexp : (s + 1) ^ 2 = s ^ 2 + 2 * s + 1 := by
      simp [Nat.pow_two, Nat.mul_add, Nat.add_mul, Nat.add_assoc]
      omega
    have hs2 : 2 * s = 2 ^ (fact (n - 1) / 2 + 1) := by
      rw [hsdef, Nat.pow_succ']
    rw [hexp, ← hs, ha, hs2]
    have : 2 ^ (fact (n - 1) / 2) < 2 ^ (fact (n - 1) / 2 + 1) :=
      Nat.pow_lt_pow_succ (by decide)
    omega
  exact not_eq_square_of_between hmain_lt hnext

/-! ### `e`-th power gap when `e ∣ (n-1)!` -/

theorem add_one_pow_ge {b e : Nat} (he : 1 ≤ e) :
    b ^ e + e * b ^ (e - 1) ≤ (b + 1) ^ e := by
  refine le_induction (fun e => b ^ e + e * b ^ (e - 1) ≤ (b + 1) ^ e) he ?base ?step
  · simp
  · intro k hk ih
    have hmul :
        (b + 1) * (b ^ k + k * b ^ (k - 1)) ≤ (b + 1) ^ (k + 1) := by
      have : (b + 1) * (b + 1) ^ k = (b + 1) ^ (k + 1) := by
        rw [Nat.mul_comm, Nat.pow_succ]
      rw [← this]
      exact Nat.mul_le_mul_left _ ih
    refine Nat.le_trans ?_ hmul
    have hb : (b + 1) * b ^ k = b ^ (k + 1) + b ^ k := by
      rw [Nat.add_mul, Nat.one_mul, Nat.pow_succ, Nat.mul_comm]
    have hbpow : b * b ^ (k - 1) = b ^ k := by
      have : k = k - 1 + 1 := by omega
      calc
        b * b ^ (k - 1) = b ^ (k - 1 + 1) := by
          rw [Nat.mul_comm, ← Nat.pow_succ]
        _ = b ^ k := by rw [← this]
    have hrest : (b + 1) * (k * b ^ (k - 1)) = k * b ^ k + k * b ^ (k - 1) := by
      rw [Nat.add_mul, Nat.one_mul, Nat.mul_left_comm b, hbpow]
    rw [Nat.mul_add, hb, hrest]
    have : b ^ (k + 1) + (k + 1) * b ^ k ≤
        b ^ (k + 1) + b ^ k + (k * b ^ k + k * b ^ (k - 1)) := by
      have : (k + 1) * b ^ k = k * b ^ k + b ^ k := by rw [Nat.add_mul, Nat.one_mul]
      rw [this]
      omega
    exact this

theorem two_pow_of_dvd_exp {k e : Nat} (_he : 0 < e) (hd : e ∣ k) :
    2 ^ k = (2 ^ (k / e)) ^ e := by
  calc
    2 ^ k = 2 ^ (k / e * e) := by rw [Nat.div_mul_cancel hd]
    _ = (2 ^ (k / e)) ^ e := Nat.pow_mul _ _ _

theorem not_eq_pow_of_between {m b e : Nat} (_he : 0 < e)
    (h1 : b ^ e < m) (h2 : m < (b + 1) ^ e) : ¬ ∃ t, m = t ^ e := by
  rintro ⟨t, ht⟩
  cases Nat.lt_or_ge t (b + 1) with
  | inl hlt =>
    have : t ^ e ≤ b ^ e := Nat.pow_le_pow_left (Nat.le_of_lt_succ hlt) e
    exact Nat.lt_irrefl _ (ht ▸ Nat.lt_of_le_of_lt this h1)
  | inr hge =>
    have : (b + 1) ^ e ≤ t ^ e := Nat.pow_le_pow_left hge e
    exact Nat.lt_irrefl _ (ht ▸ Nat.lt_of_lt_of_le h2 this)

theorem div_le_div_of_ge_right {a b c : Nat} (hb : 0 < b) (hbc : b ≤ c) :
    a / c ≤ a / b := by
  have : (a / c) * b ≤ a :=
    Nat.le_trans (Nat.mul_le_mul_left (a / c) hbc) (Nat.div_mul_le_self a c)
  exact (Nat.le_div_iff_mul_le hb).2 this

theorem dvd_exp_le {n e : Nat} (hn : 7 ≤ n) (he : 1 < e)
    (hd : e ∣ fact (n - 1)) : e ≤ fact (n - 1) :=
  Nat.le_of_dvd (fact_pos _) hd

/-- If `e ∣ (n-1)!` and `n ≥ 7`, then `a n` is not an `e`-th power. -/
theorem not_eth_power_of_dvd {n e : Nat} (hn : 7 ≤ n) (he : 1 < e)
    (hdvd : e ∣ fact (n - 1)) : ¬ ∃ b, 1 < b ∧ a n = b ^ e := by
  intro ⟨b, _hb, hab⟩
  have hK : 2 ^ fact (n - 1) = (2 ^ (fact (n - 1) / e)) ^ e :=
    two_pow_of_dvd_exp (Nat.zero_lt_of_lt he) hdvd
  have hn2 : 2 ≤ n := by omega
  have ha := a_eq_main_add_delta hn2
  have hmain : mainTerm n = 2 ^ fact (n - 1) := rfl
  have hpos := delta_pos hn2
  have hdelta := delta_lt_half_pow hn
  have hbase : (2 ^ (fact (n - 1) / e)) ^ e < a n := by
    rw [← hK, ← hmain, ha]
    omega
  have hge : fact (n - 1) / 2 ≤ (fact (n - 1) / e) * (e - 1) := by
    have h2 : e ≤ 2 * (e - 1) := by omega
    have hmul :
        e * (fact (n - 1) / e) ≤ (2 * (e - 1)) * (fact (n - 1) / e) :=
      Nat.mul_le_mul_right _ h2
    have : fact (n - 1) ≤ 2 * ((fact (n - 1) / e) * (e - 1)) := by
      calc
        fact (n - 1) = e * (fact (n - 1) / e) :=
          (Nat.mul_div_cancel' hdvd).symm
        _ ≤ (2 * (e - 1)) * (fact (n - 1) / e) := hmul
        _ = 2 * ((e - 1) * (fact (n - 1) / e)) := Nat.mul_assoc _ _ _
        _ = 2 * ((fact (n - 1) / e) * (e - 1)) := by rw [Nat.mul_comm (e - 1)]
    exact Nat.div_le_of_le_mul this
  have hb0pow : (2 ^ (fact (n - 1) / e)) ^ (e - 1) =
      2 ^ ((fact (n - 1) / e) * (e - 1)) :=
    (Nat.pow_mul _ _ _).symm
  have hpowge : 2 ^ (fact (n - 1) / 2) ≤ (2 ^ (fact (n - 1) / e)) ^ (e - 1) := by
    rw [hb0pow]
    exact Nat.pow_le_pow_of_le (by decide : 1 < 2) hge
  have hbig : 2 ^ (fact (n - 1) / 2) ≤ e * (2 ^ (fact (n - 1) / e)) ^ (e - 1) :=
    Nat.le_trans hpowge (Nat.le_mul_of_pos_left _ (by omega))
  have hlt_next : a n < (2 ^ (fact (n - 1) / e) + 1) ^ e := by
    have : a n = (2 ^ (fact (n - 1) / e)) ^ e + delta n := by
      rw [ha, hmain, hK]
    rw [this]
    have h1 :
        (2 ^ (fact (n - 1) / e)) ^ e + delta n <
          (2 ^ (fact (n - 1) / e)) ^ e +
            e * (2 ^ (fact (n - 1) / e)) ^ (e - 1) :=
      Nat.add_lt_add_left (Nat.lt_of_lt_of_le hdelta hbig) _
    have h2 :
        (2 ^ (fact (n - 1) / e)) ^ e +
            e * (2 ^ (fact (n - 1) / e)) ^ (e - 1) ≤
          (2 ^ (fact (n - 1) / e) + 1) ^ e :=
      add_one_pow_ge (Nat.succ_le_of_lt (show 0 < e from Nat.zero_lt_of_lt he))
    exact Nat.lt_of_lt_of_le h1 h2
  exact not_eq_pow_of_between (Nat.zero_lt_of_lt he) hbase hlt_next ⟨b, hab⟩

theorem gcd_eq_left_of_dvd {a b : Nat} (h : a ∣ b) : Nat.gcd a b = a :=
  Nat.dvd_antisymm (Nat.gcd_dvd_left a b) (Nat.dvd_gcd (Nat.dvd_refl a) h)

theorem not_eth_power_of_pos_gcd {n e : Nat} (hn : 7 ≤ n) (he : 1 < e)
    (hd : 1 < Nat.gcd e (fact (n - 1))) :
    ¬ ∃ b, 1 < b ∧ a n = b ^ e := by
  intro ⟨b, hb, hab⟩
  let d := Nat.gcd e (fact (n - 1))
  have hde : d ∣ e := Nat.gcd_dvd_left _ _
  have hdK : d ∣ fact (n - 1) := Nat.gcd_dvd_right _ _
  obtain ⟨t, ht⟩ := hde
  have hb' : 1 < b ^ t := by
    cases t with
    | zero =>
      have : e = 0 := by simpa using ht
      omega
    | succ t =>
      have hpos : 0 < b ^ t := Nat.pow_pos (Nat.zero_lt_of_lt hb)
      have : b ≤ b * b ^ t := Nat.le_mul_of_pos_right _ hpos
      have : 1 < b * b ^ t := Nat.lt_of_lt_of_le hb this
      simpa [Nat.pow_succ'] using this
  have : a n = (b ^ t) ^ d := by
    rw [hab, ht, Nat.mul_comm, Nat.pow_mul]
  exact not_eth_power_of_dvd hn (by omega : 1 < d) hdK ⟨b ^ t, hb', this⟩

/-- Any perfect-power exponent for `a n` (`n ≥ 7`) must be coprime to `(n-1)!`. -/
theorem perfect_power_imp_coprime {n : Nat} (hn : 7 ≤ n)
    (h : IsPerfectPower (a n)) :
    ∃ b e, 1 < b ∧ 1 < e ∧ a n = b ^ e ∧ Nat.gcd e (fact (n - 1)) = 1 := by
  obtain ⟨b, e, hb, he, hab⟩ := h
  refine ⟨b, e, hb, he, hab, ?_⟩
  cases Nat.eq_or_lt_of_le (Nat.succ_le_of_lt
      (Nat.gcd_pos_of_pos_left (fact (n - 1)) (Nat.zero_lt_of_lt he))) with
  | inl h1 => exact h1.symm
  | inr hgt =>
    exact (not_eth_power_of_pos_gcd hn he hgt ⟨b, hb, hab⟩).elim

theorem coprime_exp_ge {n e : Nat} (hn : 2 ≤ n) (he : 1 < e)
    (h : Nat.gcd e (fact (n - 1)) = 1) : n ≤ e := by
  cases Nat.lt_or_ge e n with
  | inl hlt =>
    have : e ≤ n - 1 := by omega
    have hdvd : e ∣ fact (n - 1) := dvd_fact_of_le (by omega) this
    have : Nat.gcd e (fact (n - 1)) = e := gcd_eq_left_of_dvd hdvd
    omega
  | inr hge => exact hge

/-- Even exponents reduce to `not_square`. -/
theorem not_even_exp {n e : Nat} (hn : 7 ≤ n) (he : 1 < e) (h2 : 2 ∣ e) :
    ¬ ∃ b, 1 < b ∧ a n = b ^ e := by
  intro ⟨b, hb, hab⟩
  obtain ⟨t, ht⟩ := h2
  have : a n = (b ^ t) ^ 2 := by
    rw [hab, ht, Nat.mul_comm, Nat.pow_mul]
  exact not_square hn ⟨b ^ t, this⟩

end LeanA113258
