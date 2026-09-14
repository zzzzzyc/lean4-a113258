import LeanA113258.Squares
import LeanA113258.Compute
import LeanA113258.Conjecture
import LeanA113258.Gaps

namespace LeanA113258

/-!
  Remaining work after the `e ∣ (n-1)!` / positive-gcd / even-exponent cases.

  Proved here:
  * `a n` is odd (`n ≥ 1`), so any base with `a n = b ^ e` is odd
  * `a n ≠ 2 ^ e` (`n ≥ 2`, `e > 1`)
  * `n ≥ 7` and `IsPerfectPower (a n)` reduce to a coprime large-exponent
    representation with base `≥ 3`
  * the integer splitting
      `a n = 2^{B} * (2^{B(n-2)} + 3^{B}) + ρ` with `B = (n-2)!` and `0 < ρ < 2^{B}`
  * `a n ≠ 2^K + 1` (since `δ ≥ 1 + 6^{(n-2)!}`)
  * partial coprime-large exclusions: even bases; `e ≥ K+1`;
    and `3^e > 2^{K+1}` when `2(K+1)+3 ≤ 3e`

  Not proved (no `sorry`):
  * `not_eth_power_of_coprime_large` — if `3 ≤ b`, `n ≤ e`,
    `Nat.gcd e (fact (n-1)) = 1`, then `a n ≠ b ^ e`.
    The remaining odd-base window is `n ≤ e < 2(K+1)/3` roughly,
    where `0 < b^e - 2^K < 2^{K/2}` is not yet ruled out.
    Do **not** declare `officialConjecture_false` until this is closed.
-/

/-! ### Oddness and not a power of two -/

theorem term_even {n i : Nat} (hi : 1 ≤ i) (_hin : i < n) : 2 ∣ term n i := by
  unfold term
  exact two_dvd_pow_of (two_dvd_fact (by omega : 2 ≤ i + 1)) (fact_pos (n - i))

theorem sumRange_odd_head {n : Nat} {f : Nat → Nat} (hn : 1 ≤ n)
    (h0 : f 0 % 2 = 1)
    (ht : ∀ i, 1 ≤ i → i < n → f i % 2 = 0) :
    sumRange n f % 2 = 1 := by
  refine le_induction
      (fun n => (∀ i, 1 ≤ i → i < n → f i % 2 = 0) → sumRange n f % 2 = 1)
      hn ?base ?step ht
  · intro _
    simp [sumRange_succ, sumRange_zero, h0]
  · intro k hk ih ht'
    rw [sumRange_succ]
    have hsum : sumRange k f % 2 = 1 :=
      ih fun i hi1 hi2 => ht' i hi1 (Nat.lt_trans hi2 (Nat.lt_succ_self k))
    have hfk : f k % 2 = 0 := ht' k hk (Nat.lt_succ_self k)
    omega

theorem a_odd {n : Nat} (hn : 1 ≤ n) : a n % 2 = 1 := by
  have h0 : term n 0 % 2 = 1 := by
    simp [term, fact_one, one_pow]
  have ht : ∀ i, 1 ≤ i → i < n → term n i % 2 = 0 := by
    intro i hi1 hi2
    exact Nat.mod_eq_zero_of_dvd (term_even hi1 hi2)
  exact sumRange_odd_head hn h0 ht

theorem two_pow_even {e : Nat} (he : 1 ≤ e) : (2 ^ e) % 2 = 0 := by
  cases e with
  | zero => omega
  | succ e =>
    rw [Nat.pow_succ']
    exact Nat.mul_mod_right 2 _

/-- `a n` is odd, while `2^e` is even for `e ≥ 1`. -/
theorem not_power_of_two {n e : Nat} (hn : 2 ≤ n) (he : 1 < e) :
    a n ≠ 2 ^ e := by
  intro h
  have hodd := a_odd (n := n) (by omega)
  have heven := two_pow_even (e := e) (by omega)
  rw [h] at hodd
  omega

theorem two_pow_K_lt_a {n : Nat} (hn : 2 ≤ n) :
    2 ^ fact (n - 1) < a n := by
  have ha := a_eq_main_add_delta hn
  have hδ := delta_pos hn
  simpa [mainTerm] using (show mainTerm n < a n by
    rw [ha]; omega)

/-- For `n ≥ 7`, `2^K < a n < 2^{K+1}` with `K = (n-1)!`. -/
theorem a_lt_two_pow_succ {n : Nat} (hn : 7 ≤ n) :
    a n < 2 ^ (fact (n - 1) + 1) := by
  have ha := a_eq_main_add_delta (by omega : 2 ≤ n)
  have hδ := delta_lt_half_pow hn
  have hhalf : 2 ^ (fact (n - 1) / 2) ≤ 2 ^ fact (n - 1) :=
    Nat.pow_le_pow_right (by decide) (Nat.div_le_self _ _)
  have hδK : delta n < 2 ^ fact (n - 1) := Nat.lt_of_lt_of_le hδ hhalf
  have hsum : a n < 2 ^ fact (n - 1) + 2 ^ fact (n - 1) := by
    rw [ha]; simp [mainTerm]; omega
  have hdouble : 2 ^ fact (n - 1) + 2 ^ fact (n - 1) =
      2 ^ (fact (n - 1) + 1) := by
    rw [← Nat.two_mul, Nat.pow_succ']
  exact hdouble ▸ hsum

theorem a_mem_two_pow_interval {n : Nat} (hn : 7 ≤ n) :
    2 ^ fact (n - 1) < a n ∧ a n < 2 ^ (fact (n - 1) + 1) :=
  ⟨two_pow_K_lt_a (by omega), a_lt_two_pow_succ hn⟩

/-! ### Reduction of `IsPerfectPower` for `n ≥ 7` -/

theorem perfect_power_remaining {n : Nat} (hn : 7 ≤ n)
    (h : IsPerfectPower (a n)) :
    ∃ b e, 3 ≤ b ∧ n ≤ e ∧ Nat.gcd e (fact (n - 1)) = 1 ∧ a n = b ^ e := by
  obtain ⟨b, e, hb, he, hab, hg⟩ := perfect_power_imp_coprime hn h
  refine ⟨b, e, ?_, coprime_exp_ge (by omega) he hg, hg, hab⟩
  have hb2 : 2 ≤ b := Nat.succ_le_of_lt hb
  cases Nat.eq_or_lt_of_le hb2 with
  | inl h2 =>
    subst h2
    exact (not_power_of_two (by omega) he hab).elim
  | inr hlt => exact hlt

/-- Closing `n ≥ 7` is exactly ruling out the remaining coprime large exponents. -/
theorem not_perfect_power_of_no_remaining {n : Nat} (hn : 7 ≤ n)
    (h : ∀ b e, 3 ≤ b → n ≤ e → Nat.gcd e (fact (n - 1)) = 1 → a n ≠ b ^ e) :
    ¬ IsPerfectPower (a n) := by
  intro hp
  obtain ⟨b, e, hb, he, hg, hab⟩ := perfect_power_remaining hn hp
  exact h b e hb he hg hab

/-! ### Coprime-large setup and partial exclusions -/

/-- `a n` odd forces any perfect-power base to be odd. -/
theorem base_odd_of_a_eq_pow {n b e : Nat} (hn : 1 ≤ n) (he : 0 < e)
    (h : a n = b ^ e) : b % 2 = 1 := by
  have hodd := a_odd (n := n) hn
  rw [h] at hodd
  cases Nat.mod_two_eq_zero_or_one b with
  | inr hodd' => exact hodd'
  | inl heven =>
    have : (b ^ e) % 2 = 0 :=
      Nat.mod_eq_zero_of_dvd (two_dvd_pow_of (Nat.dvd_of_mod_eq_zero heven) he)
    omega

theorem not_eth_power_of_even_base {n b e : Nat} (hn : 1 ≤ n) (he : 0 < e)
    (hbeven : b % 2 = 0) : a n ≠ b ^ e := by
  intro h
  have := base_odd_of_a_eq_pow hn he h
  omega

theorem two_pow_K_not_eth {n e : Nat} (he : 1 < e)
    (hg : Nat.gcd e (fact (n - 1)) = 1) (x : Nat) :
    2 ^ fact (n - 1) ≠ x ^ e :=
  two_pow_not_eth_of_coprime he hg x

theorem sumRange_ge_two {n : Nat} (f : Nat → Nat) (hn : 3 ≤ n) :
    f 0 + f 2 ≤ sumRange n f := by
  have hle : sumRange 3 f ≤ sumRange n f :=
    sumRange_le_sumRange_of_le (by omega) f
  have h3 : sumRange 3 f = f 0 + f 1 + f 2 := by
    simp [sumRange_succ, sumRange_zero]
  omega

theorem delta_ge_one_add_term_two {n : Nat} (hn : 3 ≤ n) :
    1 + term n 2 ≤ delta n := by
  have hsum : rest n 0 + rest n 2 ≤ sumRange n (rest n) :=
    sumRange_ge_two (rest n) hn
  have h0 : rest n 0 = 1 := rest_zero n
  have h2 : rest n 2 = term n 2 := by simp [rest]
  simpa [delta, h0, h2] using hsum

theorem term_two_ge_six {n : Nat} (hn : 3 ≤ n) : 6 ≤ term n 2 := by
  simp [term, fact_three]
  exact Nat.le_self_pow (Nat.ne_of_gt (fact_pos (n - 2))) 6

/-- `δ ≥ 1 + 6^{(n-2)!} ≥ 7`, so `a n` is never `2^K + 1`. -/
theorem a_ne_two_pow_add_one {n : Nat} (hn : 3 ≤ n) :
    a n ≠ 2 ^ fact (n - 1) + 1 := by
  have ha := a_eq_main_add_delta (by omega : 2 ≤ n)
  have hδ := delta_ge_one_add_term_two hn
  have ht := term_two_ge_six hn
  intro h
  have : delta n = 1 := by
    simp [mainTerm] at ha
    omega
  omega

/-- Package A: if `a n = b ^ e` with the remaining coprime-large hypotheses,
    then `b` is odd and `0 < b^e - 2^K < 2^{K/2}`, in particular `≠ 1`. -/
theorem coprime_large_setup {n b e : Nat} (hn : 7 ≤ n) (_hb : 3 ≤ b)
    (_he : n ≤ e) (_hg : Nat.gcd e (fact (n - 1)) = 1)
    (hab : a n = b ^ e) :
    b % 2 = 1 ∧
      2 ^ fact (n - 1) < b ^ e ∧
      b ^ e - 2 ^ fact (n - 1) < 2 ^ (fact (n - 1) / 2) ∧
      b ^ e ≠ 2 ^ fact (n - 1) + 1 := by
  have hn1 : 1 ≤ n := by omega
  have he0 : 0 < e := by omega
  have hbodd := base_odd_of_a_eq_pow hn1 he0 hab
  have ha := a_eq_main_add_delta (by omega : 2 ≤ n)
  have hpos := delta_pos (by omega : 2 ≤ n)
  have hδ := delta_lt_half_pow hn
  have hKlt : 2 ^ fact (n - 1) < b ^ e := by
    rw [← hab]
    simpa [mainTerm] using (show mainTerm n < a n by rw [ha]; omega)
  have hgap : b ^ e - 2 ^ fact (n - 1) < 2 ^ (fact (n - 1) / 2) := by
    have : a n - mainTerm n = delta n := by
      rw [ha]; omega
    simpa [hab, mainTerm] using (show a n - mainTerm n < 2 ^ (fact (n - 1) / 2) by
      rw [this]; exact hδ)
  exact ⟨hbodd, hKlt, hgap, by
    intro h1
    exact a_ne_two_pow_add_one (by omega) (hab.trans h1)⟩

/-- No `e`-th power sits in `(2^K, 2^{K+1})` once `e ≥ K+1`. -/
theorem not_eth_power_of_exp_ge_succ_K {n b e : Nat} (hn : 7 ≤ n)
    (hb : 2 ≤ b) (he : fact (n - 1) + 1 ≤ e) : a n ≠ b ^ e := by
  intro h
  have ⟨_, h2⟩ := a_mem_two_pow_interval hn
  rw [h] at h2
  have h2e : 2 ^ e ≤ b ^ e := Nat.pow_le_pow_left hb e
  have hKe : 2 ^ (fact (n - 1) + 1) ≤ 2 ^ e :=
    Nat.pow_le_pow_right (by decide : (0 : Nat) < 2) he
  exact Nat.lt_irrefl _ (Nat.lt_of_lt_of_le h2 (Nat.le_trans hKe h2e))

/-- If `3^e` already exceeds `2^{K+1}`, no base `≥ 3` can lie in the dyadic window. -/
theorem not_eth_power_of_three_pow_overflow {n b e : Nat} (hn : 7 ≤ n)
    (hb : 3 ≤ b) (h : 2 * (fact (n - 1) + 1) + 3 ≤ 3 * e) :
    a n ≠ b ^ e := by
  intro hab
  have ⟨_, hlt⟩ := a_mem_two_pow_interval hn
  have hK : 720 ≤ fact (n - 1) := by
    have : 6 ≤ n - 1 := by omega
    simpa [fact_six] using fact_le_of_le this
  have he : 3 ≤ e := by
    have : 2 * (720 + 1) + 3 ≤ 2 * (fact (n - 1) + 1) + 3 := by omega
    have : 1445 ≤ 3 * e := Nat.le_trans this h
    omega
  have h3 : 2 ^ (fact (n - 1) + 1) < 3 ^ e :=
    three_pow_gt_two_pow_succ he h
  have hb3 : 3 ^ e ≤ b ^ e := Nat.pow_le_pow_left hb e
  exact Nat.lt_irrefl _ (Nat.lt_of_lt_of_le hlt (Nat.le_trans (Nat.le_of_lt h3) (hab ▸ hb3)))

/-!
  Remaining hole (unproved, no `sorry`):

  ```
  theorem not_eth_power_of_coprime_large
      {n b e : Nat} (hn : 7 ≤ n) (hb : 3 ≤ b) (he : n ≤ e)
      (hg : Nat.gcd e (fact (n - 1)) = 1) : a n ≠ b ^ e
  ```

  Closed fragments: even bases; `t = 0`; `t = 1`; `e ≥ K+1`;
  `2(K+1)+3 ≤ 3e` (so `3^e > 2^{K+1}`). The leftover is odd `b ≥ 3` with
  `n ≤ e` and `3e < 2(K+1)+3`, where the gap `b^e - 2^K` is odd and
  `≥ 3` but not yet shown `≥ 2^{K/2}`.

  With the full lemma, `not_perfect_power_of_no_remaining` plus `a 5` / `a 6`
  would yield `¬ officialConjecture`.
-/

theorem officialConjecture_false_of
    (h : ∀ n, 7 ≤ n → ¬ IsPerfectPower (a n)) :
    ¬ officialConjecture := by
  rintro ⟨n, hn, hp⟩
  have : n = 5 ∨ n = 6 ∨ 7 ≤ n := by omega
  rcases this with h5 | h6 | h7
  · subst h5; exact a5_closes_one_case hp
  · subst h6; exact a_6_not_perfect_power hp
  · exact h n h7 hp

/-! ### Splitting `a n = 2^{B}(2^{B(n-2)}+3^{B})+ρ` -/

def midFactor (n : Nat) : Nat :=
  2 ^ ((n - 2) * fact (n - 2)) + 3 ^ fact (n - 2)

def rhoTerm (n i : Nat) : Nat := if i = 1 ∨ i = 2 then 0 else term n i

def rho (n : Nat) : Nat := sumRange n (rhoTerm n)

theorem term_one_decomp {n : Nat} (hn : 2 ≤ n) :
    term n 1 = 2 ^ fact (n - 2) * 2 ^ ((n - 2) * fact (n - 2)) := by
  rw [term_one, mainTerm]
  have hK : fact (n - 1) = (n - 1) * fact (n - 2) := fact_pred_eq hn
  have hsum : n - 1 = 1 + (n - 2) := by omega
  rw [hK, hsum, Nat.add_mul, Nat.one_mul, Nat.pow_add]

theorem term_two_decomp {n : Nat} (_hn : 3 ≤ n) :
    term n 2 = 2 ^ fact (n - 2) * 3 ^ fact (n - 2) := by
  simp [term, fact_three]
  exact six_pow_eq_two_three _

theorem term_split_rho (n i : Nat) :
    term n i =
      (if i = 1 then term n 1 else 0) +
      (if i = 2 then term n 2 else 0) +
      rhoTerm n i := by
  unfold rhoTerm
  by_cases h1 : i = 1
  · simp [h1]
  · by_cases h2 : i = 2
    · simp [h1, h2]
    · simp [h1, h2]

theorem sumRange_add3 (n : Nat) (f g h : Nat → Nat) :
    sumRange n (fun i => f i + g i + h i) =
      sumRange n f + sumRange n g + sumRange n h := by
  have : (fun i => f i + g i + h i) = fun i => (f i + g i) + h i := rfl
  rw [this, sumRange_add, sumRange_add]

theorem sumRange_zero_of {n : Nat} {f : Nat → Nat}
    (h : ∀ i, i < n → f i = 0) : sumRange n f = 0 := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [sumRange_succ, h n (Nat.lt_succ_self n),
      ih fun i hi => h i (Nat.lt_succ_of_le (Nat.le_of_lt hi))]

theorem sumRange_indicator_at {n k c : Nat} (hk : k < n) :
    sumRange n (fun i => if i = k then c else 0) = c := by
  refine le_induction (fun n => sumRange n (fun i => if i = k then c else 0) = c)
    (Nat.succ_le_of_lt hk) ?base ?step
  · rw [sumRange_succ]
    have hz : sumRange k (fun i => if i = k then c else 0) = 0 :=
      sumRange_zero_of fun i hi => by
        have : i ≠ k := Nat.ne_of_lt hi
        simp [this]
    simp [hz]
  · intro m hm ih
    rw [sumRange_succ, ih]
    have : m ≠ k := by omega
    simp [this]

theorem rhoTerm_zero (n : Nat) : rhoTerm n 0 = 1 := by
  simp [rhoTerm, term, fact_one, one_pow]

theorem rho_pos {n : Nat} (hn : 1 ≤ n) : 0 < rho n := by
  have : 1 ≤ rho n := by
    simpa [rho, rhoTerm_zero] using sumRange_ge_first (rhoTerm n) hn
  omega

theorem a_eq_twoB_mul_plus_rho {n : Nat} (hn : 3 ≤ n) :
    a n = 2 ^ fact (n - 2) * midFactor n + rho n := by
  have hfun : term n = fun i =>
      (if i = 1 then term n 1 else 0) +
      (if i = 2 then term n 2 else 0) +
      rhoTerm n i := by
    funext i
    exact term_split_rho n i
  have ha : a n = sumRange n (term n) := rfl
  rw [ha, hfun, sumRange_add3]
  have h1 : sumRange n (fun i => if i = 1 then term n 1 else 0) = term n 1 :=
    sumRange_indicator_one (by omega)
  have h2 : sumRange n (fun i => if i = 2 then term n 2 else 0) = term n 2 :=
    sumRange_indicator_at (by omega : (2 : Nat) < n)
  rw [h1, h2, term_one_decomp (by omega), term_two_decomp hn, ← Nat.mul_add]
  rfl

/-! ### `ρ < 2^{(n-2)!}` for `n ≥ 7` -/

theorem two_mul_pow_lt_of_base {a b e : Nat} (he : 0 < e) (h : 2 * a < b) :
    2 * a ^ e < b ^ e := by
  have h2 : 2 ≤ 2 ^ e := Nat.le_self_pow (Nat.ne_of_gt he) 2
  have hle : 2 * a ^ e ≤ (2 * a) ^ e := by
    calc
      2 * a ^ e ≤ 2 ^ e * a ^ e := Nat.mul_le_mul_right (a ^ e) h2
      _ = (2 * a) ^ e := (Nat.mul_pow 2 a e).symm
  have hlt : (2 * a) ^ e < b ^ e := Nat.pow_lt_pow_left h (Nat.ne_of_gt he)
  exact Nat.lt_of_le_of_lt hle hlt

theorem n_le_four_pow_sub3 {n : Nat} (hn : 7 ≤ n) : n ≤ 4 ^ (n - 3) := by
  refine le_induction (fun n => n ≤ 4 ^ (n - 3)) hn ?base ?step
  · decide
  · intro k _hk ih
    have hpow : 4 ^ (k + 1 - 3) = 4 * 4 ^ (k - 3) := by
      have : k + 1 - 3 = k - 3 + 1 := by omega
      rw [this, Nat.pow_succ']
    rw [hpow]
    have : k + 1 ≤ 4 * k := by omega
    exact Nat.le_trans this (Nat.mul_le_mul_left 4 ih)

theorem two_n_sq (n : Nat) : (2 * n) * (2 * n) = 4 * n * n := by
  calc
    (2 * n) * (2 * n) = 2 * (n * (2 * n)) := by rw [Nat.mul_assoc]
    _ = 2 * (n * 2 * n) := by rw [Nat.mul_assoc]
    _ = 2 * (2 * n * n) := by rw [Nat.mul_comm n 2]
    _ = (2 * (2 * n)) * n := by rw [← Nat.mul_assoc]
    _ = (2 * 2 * n) * n := by rw [← Nat.mul_assoc]
    _ = 4 * n * n := rfl

theorem succ_sq_le_k_four {n : Nat} (hn : 7 ≤ n) :
    (n + 1) * (n + 1) ≤ n * 4 ^ (n - 2) := by
  have h2 : n + 1 ≤ 2 * n := by omega
  have hsq : (n + 1) * (n + 1) ≤ (2 * n) * (2 * n) := Nat.mul_le_mul h2 h2
  have hn4 : n ≤ 4 ^ (n - 3) := n_le_four_pow_sub3 hn
  have h4n : 4 * n ≤ 4 ^ (n - 2) := by
    have hmul : 4 * n ≤ 4 * 4 ^ (n - 3) := Nat.mul_le_mul_left 4 hn4
    have hpow : 4 * 4 ^ (n - 3) = 4 ^ (n - 2) := by
      have : n - 2 = n - 3 + 1 := by omega
      rw [this, Nat.pow_succ, Nat.mul_comm]
    exact hpow ▸ hmul
  have htail : 4 * n * n ≤ n * 4 ^ (n - 2) := by
    rw [Nat.mul_comm n]
    exact Nat.mul_le_mul_right n h4n
  rw [two_n_sq] at hsq
  exact Nat.le_trans hsq htail

theorem four_n_fact_le {n : Nat} (hn : 7 ≤ n) :
    4 * n * fact n ≤ 2 ^ ((n - 2) * (n - 3)) := by
  refine le_induction (fun n => 4 * n * fact n ≤ 2 ^ ((n - 2) * (n - 3)))
    hn ?base ?step
  · decide
  · intro k hk ih
    have h1 : k + 1 - 2 = k - 1 := by omega
    have h2 : k + 1 - 3 = k - 2 := by omega
    have hsplit : (k - 1) * (k - 2) = (k - 2) * (k - 3) + 2 * (k - 2) := by
      have : k - 1 = k - 3 + 2 := by omega
      rw [this, Nat.add_mul, Nat.mul_comm (k - 3)]
    have h4pow : 2 ^ (2 * (k - 2)) = 4 ^ (k - 2) := by
      rw [Nat.pow_mul]
    have hpow : 2 ^ ((k + 1 - 2) * (k + 1 - 3)) =
        2 ^ ((k - 2) * (k - 3)) * 4 ^ (k - 2) := by
      rw [h1, h2, hsplit, Nat.pow_add, h4pow]
    have hL : 4 * (k + 1) * fact (k + 1) =
        4 * ((k + 1) * (k + 1) * fact k) := by
      rw [fact_succ]
      calc
        4 * (k + 1) * (fact k * (k + 1))
            = (4 * (k + 1)) * (fact k * (k + 1)) := rfl
        _ = (4 * (k + 1)) * fact k * (k + 1) := by rw [← Nat.mul_assoc]
        _ = (4 * (k + 1)) * (k + 1) * fact k := by
              rw [Nat.mul_right_comm (4 * (k + 1))]
        _ = 4 * ((k + 1) * (k + 1) * fact k) := by
              rw [Nat.mul_assoc 4 (k + 1), Nat.mul_assoc 4]
    have hsq := succ_sq_le_k_four hk
    have hmul : (k + 1) * (k + 1) * fact k ≤ k * 4 ^ (k - 2) * fact k :=
      Nat.mul_le_mul_right _ hsq
    have hL2 : 4 * ((k + 1) * (k + 1) * fact k) ≤
        4 * (k * 4 ^ (k - 2) * fact k) :=
      Nat.mul_le_mul_left 4 hmul
    have hrearr : 4 * (k * 4 ^ (k - 2) * fact k) =
        4 * k * fact k * 4 ^ (k - 2) := by
      have hinner : k * 4 ^ (k - 2) * fact k = k * (fact k * 4 ^ (k - 2)) := by
        rw [Nat.mul_assoc, Nat.mul_comm (4 ^ (k - 2))]
      calc
        4 * (k * 4 ^ (k - 2) * fact k)
            = 4 * (k * (fact k * 4 ^ (k - 2))) := by rw [hinner]
        _ = (4 * k) * (fact k * 4 ^ (k - 2)) := by rw [Nat.mul_assoc]
        _ = (4 * k) * fact k * 4 ^ (k - 2) := by rw [← Nat.mul_assoc]
    rw [hpow, hL]
    refine Nat.le_trans hL2 ?_
    rw [hrearr]
    exact Nat.mul_le_mul_right _ ih

theorem term_ge_four_le {n i : Nat} (hn : 7 ≤ n) (hi : 4 ≤ i) (hin : i < n) :
    term n i ≤ fact n ^ fact (n - 4) := by
  unfold term
  have hbase : fact (i + 1) ≤ fact n := fact_le_of_le (Nat.succ_le_of_lt hin)
  have hexp : fact (n - i) ≤ fact (n - 4) := fact_le_of_le (by omega)
  have h1 : fact (i + 1) ^ fact (n - i) ≤ fact n ^ fact (n - i) :=
    Nat.pow_le_pow_left hbase _
  have h2 : fact n ^ fact (n - i) ≤ fact n ^ fact (n - 4) :=
    Nat.pow_le_pow_right (fact_pos n) hexp
  exact Nat.le_trans h1 h2

theorem two_n_fact_pow_lt_twoB {n : Nat} (hn : 7 ≤ n) :
    2 * n * fact n ^ fact (n - 4) < 2 ^ fact (n - 2) := by
  have hFpos : 0 < fact (n - 4) := fact_pos _
  have hle : 4 * n * fact n ≤ 2 ^ ((n - 2) * (n - 3)) := four_n_fact_le hn
  have hde : fact (n - 2) = (n - 2) * (n - 3) * fact (n - 4) :=
    fact_sub_two_decomp (by omega)
  have hpow : (2 ^ ((n - 2) * (n - 3))) ^ fact (n - 4) = 2 ^ fact (n - 2) := by
    rw [← Nat.pow_mul, hde, Nat.mul_assoc]
  have hmid : 4 * n * fact n ^ fact (n - 4) ≤
      (4 * n * fact n) ^ fact (n - 4) := by
    have h4n : 4 * n ≤ (4 * n) ^ fact (n - 4) :=
      Nat.le_self_pow (Nat.ne_of_gt hFpos) (4 * n)
    calc
      4 * n * fact n ^ fact (n - 4)
          ≤ (4 * n) ^ fact (n - 4) * fact n ^ fact (n - 4) :=
            Nat.mul_le_mul_right _ h4n
      _ = (4 * n * fact n) ^ fact (n - 4) := (Nat.mul_pow _ _ _).symm
  have hlt : 2 * n * fact n ^ fact (n - 4) <
      4 * n * fact n ^ fact (n - 4) := by
    have hpos : 0 < fact n ^ fact (n - 4) := Nat.pow_pos (fact_pos n)
    have : 2 * n < 4 * n := by omega
    exact Nat.mul_lt_mul_of_pos_right this hpos
  have hfinal : (4 * n * fact n) ^ fact (n - 4) ≤ 2 ^ fact (n - 2) := by
    have := Nat.pow_le_pow_left hle (fact (n - 4))
    exact hpow ▸ this
  exact Nat.lt_of_lt_of_le (Nat.lt_of_lt_of_le hlt hmid) hfinal

set_option maxHeartbeats 2000000

theorem two_mul_twentyfour_pow_lt_seven : 2 * 24 ^ 24 < 2 ^ 120 := by
  native_decide

theorem fortyeight_lt_two_pow {n : Nat} (hn : 8 ≤ n) : 48 < 2 ^ (n - 2) := by
  refine le_induction (fun n => 48 < 2 ^ (n - 2)) hn ?base ?step
  · decide
  · intro k _hk ih
    have hpow : 2 ^ (k + 1 - 2) = 2 * 2 ^ (k - 2) := by
      have : k + 1 - 2 = k - 2 + 1 := by omega
      rw [this, Nat.pow_succ']
    rw [hpow]
    omega

theorem two_mul_term_three_lt_twoB {n : Nat} (hn : 7 ≤ n) :
    2 * term n 3 < 2 ^ fact (n - 2) := by
  have ht : term n 3 = 24 ^ fact (n - 3) := by
    simp [term, fact_four]
  have hexp : fact (n - 2) = (n - 2) * fact (n - 3) :=
    fact_pred_eq (n := n - 1) (by omega)
  have hR : (2 ^ (n - 2)) ^ fact (n - 3) = 2 ^ fact (n - 2) := by
    rw [hexp]
    exact (Nat.pow_mul 2 (n - 2) (fact (n - 3))).symm
  rw [ht]
  have hcases : n = 7 ∨ 8 ≤ n := by omega
  cases hcases with
  | inl h7 =>
    subst h7
    simpa [fact_four, fact_five] using two_mul_twentyfour_pow_lt_seven
  | inr h8 =>
    have hbase : 2 * 24 < 2 ^ (n - 2) := fortyeight_lt_two_pow h8
    have := two_mul_pow_lt_of_base (fact_pos (n - 3)) hbase
    exact hR ▸ this

theorem two_pow_eq_two_mul_pred {k : Nat} (hk : 1 ≤ k) :
    2 ^ k = 2 * 2 ^ (k - 1) := by
  have h : k = k - 1 + 1 := by omega
  have : 2 ^ k = 2 ^ (k - 1 + 1) := congrArg (fun t => 2 ^ t) h
  rw [this, Nat.pow_succ']

theorem term_three_lt_half {n : Nat} (hn : 7 ≤ n) :
    term n 3 < 2 ^ (fact (n - 2) - 1) := by
  have h2 := two_mul_term_three_lt_twoB hn
  have hB : 1 ≤ fact (n - 2) := Nat.succ_le_of_lt (fact_pos _)
  rw [two_pow_eq_two_mul_pred hB] at h2
  exact Nat.lt_of_mul_lt_mul_left h2

def rhoTail (n i : Nat) : Nat := if 4 ≤ i then term n i else 0

theorem rhoTerm_split (n i : Nat) :
    rhoTerm n i =
      (if i = 0 then 1 else 0) +
      (if i = 3 then term n 3 else 0) +
      rhoTail n i := by
  unfold rhoTerm rhoTail
  have hcases : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ 4 ≤ i := by omega
  rcases hcases with h0 | h1 | h2 | h3 | h4
  · subst h0; simp [term]
  · subst h1; simp
  · subst h2; simp
  · subst h3; simp
  · have : ¬ (i = 1 ∨ i = 2) := by omega
    have : i ≠ 0 := by omega
    have : i ≠ 3 := by omega
    simp [‹¬ (i = 1 ∨ i = 2)›, ‹i ≠ 0›, ‹i ≠ 3›, h4]

theorem rho_tail_ge_four {n : Nat} (hn : 7 ≤ n) :
    sumRange n (rhoTail n) ≤ n * fact n ^ fact (n - 4) := by
  refine sumRange_le_const fun i hi => ?_
  unfold rhoTail
  by_cases h4 : 4 ≤ i
  · simp [h4]
    exact term_ge_four_le hn h4 hi
  · simp [h4]

theorem rho_eq_one_add_three_add_tail {n : Nat} (hn : 7 ≤ n) :
    rho n = 1 + term n 3 + sumRange n (rhoTail n) := by
  have hfun : rhoTerm n = fun i =>
      (if i = 0 then 1 else 0) +
      (if i = 3 then term n 3 else 0) +
      rhoTail n i := by
    funext i
    exact rhoTerm_split n i
  rw [rho, hfun, sumRange_add3]
  have h0 : sumRange n (fun i => if i = 0 then 1 else 0) = 1 :=
    sumRange_indicator_at (by omega : (0 : Nat) < n)
  have h3 : sumRange n (fun i => if i = 3 then term n 3 else 0) = term n 3 :=
    sumRange_indicator_at (by omega : (3 : Nat) < n)
  rw [h0, h3]

theorem le_sub_one_of_lt {a b : Nat} (h : a < b) : a ≤ b - 1 := by omega

theorem add_sub_one {x : Nat} (hx : 1 ≤ x) : 1 + (x - 1) = x := by
  rw [Nat.add_comm, Nat.sub_add_cancel hx]

theorem add_sub_one_right {x : Nat} (hx : 1 ≤ x) : x + (x - 1) = 2 * x - 1 := by
  rw [← Nat.add_sub_assoc hx, Nat.two_mul]

theorem rho_lt_twoB {n : Nat} (hn : 7 ≤ n) :
    rho n < 2 ^ fact (n - 2) := by
  have hB : 1 ≤ fact (n - 2) := Nat.succ_le_of_lt (fact_pos _)
  have hhalf := two_pow_eq_two_mul_pred hB
  have h3 := term_three_lt_half hn
  have htail0 := rho_tail_ge_four hn
  have h2n := two_n_fact_pow_lt_twoB hn
  have hx : 1 ≤ 2 ^ (fact (n - 2) - 1) := Nat.one_le_two_pow
  have htail : sumRange n (rhoTail n) < 2 ^ (fact (n - 2) - 1) := by
    have hassoc : 2 * n * fact n ^ fact (n - 4) =
        2 * (n * fact n ^ fact (n - 4)) := by rw [Nat.mul_assoc]
    have : n * fact n ^ fact (n - 4) < 2 ^ (fact (n - 2) - 1) := by
      rw [hhalf, hassoc] at h2n
      exact Nat.lt_of_mul_lt_mul_left (a := 2) h2n
    exact Nat.lt_of_le_of_lt htail0 this
  have hr := rho_eq_one_add_three_add_tail hn
  have h3' : term n 3 ≤ 2 ^ (fact (n - 2) - 1) - 1 := le_sub_one_of_lt h3
  have htail' : sumRange n (rhoTail n) ≤ 2 ^ (fact (n - 2) - 1) - 1 :=
    le_sub_one_of_lt htail
  have hsum : 1 + term n 3 + sumRange n (rhoTail n) ≤
      1 + (2 ^ (fact (n - 2) - 1) - 1) + (2 ^ (fact (n - 2) - 1) - 1) :=
    Nat.add_le_add (Nat.add_le_add_left h3' 1) htail'
  have hsimp : 1 + (2 ^ (fact (n - 2) - 1) - 1) + (2 ^ (fact (n - 2) - 1) - 1) =
      2 ^ fact (n - 2) - 1 := by
    rw [add_sub_one hx, add_sub_one_right hx, ← hhalf]
  have hlt' : 2 ^ fact (n - 2) - 1 < 2 ^ fact (n - 2) := by
    have : 0 < 2 ^ fact (n - 2) := Nat.two_pow_pos _
    omega
  have hle : rho n ≤ 2 ^ fact (n - 2) - 1 := by
    rw [hr]
    exact Nat.le_trans hsum (Nat.le_of_eq hsimp)
  exact Nat.lt_of_le_of_lt hle hlt'

/-- Package of the integer splitting used as a clue for the remaining hole. -/
theorem a_twoB_split {n : Nat} (hn : 7 ≤ n) :
    a n = 2 ^ fact (n - 2) * midFactor n + rho n ∧
      0 < rho n ∧ rho n < 2 ^ fact (n - 2) :=
  ⟨a_eq_twoB_mul_plus_rho (by omega), rho_pos (by omega), rho_lt_twoB hn⟩

end LeanA113258
