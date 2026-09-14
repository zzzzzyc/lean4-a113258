import LeanA113258.Squares

namespace LeanA113258

/-!
  Elementary comparisons used by `Remaining`.

  Kept compiling (no `sorry`):
  * parity / 2-adic splitting of a positive integer
  * `2^K` is not an `e`-th power when `gcd(e, K) = 1` and `e > 1`
  * `3^e` overshoots `2^{K+1}` once `2(K+1)+3 ≤ 3e`

  Catalan-type gap lemmas that previously lived here were unfinished and
  broke the build; they are not imported by any theorem that claims the
  official conjecture.
-/

/-! ### Parity -/

theorem odd_mul_odd {x y : Nat} (hx : x % 2 = 1) (hy : y % 2 = 1) :
    (x * y) % 2 = 1 := by
  rw [Nat.mul_mod, hx, hy]

theorem odd_pow {x e : Nat} (hx : x % 2 = 1) : (x ^ e) % 2 = 1 := by
  induction e with
  | zero => simp
  | succ e ih =>
    rw [Nat.pow_succ]
    exact odd_mul_odd ih hx

theorem two_pow_mod_two {K : Nat} (hK : 1 ≤ K) : (2 ^ K) % 2 = 0 := by
  cases K with
  | zero => omega
  | succ K =>
    rw [Nat.pow_succ']
    exact Nat.mul_mod_right 2 _

theorem odd_ne_two_pow {y m : Nat} (hy : y % 2 = 1) (hm : 1 ≤ m) :
    y ≠ 2 ^ m := by
  intro h
  have := two_pow_mod_two hm
  omega

theorem odd_pow_ne_two_pow {y e m : Nat} (hy : y % 2 = 1) (hm : 1 ≤ m) :
    y ^ e ≠ 2 ^ m := by
  intro h
  have := odd_pow (e := e) hy
  have := two_pow_mod_two hm
  omega

theorem two_dvd_pow_of {m e : Nat} (h : 2 ∣ m) (he : 0 < e) : 2 ∣ m ^ e := by
  cases e with
  | zero => omega
  | succ e =>
    rw [Nat.pow_succ, Nat.mul_comm]
    exact Nat.dvd_mul_right_of_dvd h (m ^ e)

/-! ### Odd divisors of powers of two -/

theorem coprime_odd_two {t : Nat} (h : t % 2 = 1) : Nat.Coprime t 2 := by
  have hpos : 0 < Nat.gcd t 2 := Nat.gcd_pos_of_pos_right t (by decide)
  have hle : Nat.gcd t 2 ≤ 2 := Nat.le_of_dvd (by decide) (Nat.gcd_dvd_right t 2)
  have hcases : Nat.gcd t 2 = 1 ∨ Nat.gcd t 2 = 2 := by omega
  cases hcases with
  | inl h1 => exact h1
  | inr h2 =>
    have : 2 ∣ t := h2 ▸ Nat.gcd_dvd_left t 2
    have : t % 2 = 0 := Nat.mod_eq_zero_of_dvd this
    omega

theorem odd_dvd_two_pow {t k : Nat} (hodd : t % 2 = 1) (h : t ∣ 2 ^ k) :
    t = 1 := by
  induction k generalizing t with
  | zero =>
    exact Nat.eq_one_of_dvd_one (by simpa using h)
  | succ k ih =>
    have ht2 : Nat.Coprime t 2 := coprime_odd_two hodd
    have : t ∣ 2 ^ k :=
      ht2.dvd_of_dvd_mul_left (by simpa [Nat.pow_succ'] using h)
    exact ih hodd this

/-! ### Factor `n = 2^s * y` with `y` odd -/

theorem exists_val2 (a : Nat) (ha : 0 < a) :
    ∃ s y, a = 2 ^ s * y ∧ y % 2 = 1 := by
  revert ha
  refine Nat.strongRecOn a fun a ih ha => ?_
  cases Nat.mod_two_eq_zero_or_one a with
  | inl heven =>
    have h2 : 2 ∣ a := Nat.dvd_of_mod_eq_zero heven
    have hge : 2 ≤ a := Nat.le_of_dvd ha h2
    have hhalf : 0 < a / 2 := Nat.div_pos hge (by decide)
    have hlt : a / 2 < a := Nat.div_lt_self ha (by decide)
    obtain ⟨s, y, hs, hy⟩ := ih (a / 2) hlt hhalf
    refine ⟨s + 1, y, ?_, hy⟩
    calc
      a = 2 * (a / 2) := (Nat.mul_div_cancel' h2).symm
      _ = 2 * (2 ^ s * y) := by rw [hs]
      _ = 2 ^ (s + 1) * y := by
        rw [Nat.pow_succ', Nat.mul_assoc]
  | inr hodd =>
    refine ⟨0, a, ?_, hodd⟩
    simp

theorem eq_two_pow_of_mul_odd {s y K : Nat} (hy : y % 2 = 1)
    (h : 2 ^ s * y = 2 ^ K) : y = 1 ∧ s = K := by
  have hy1 : y = 1 := by
    have : y ∣ 2 ^ K := ⟨2 ^ s, by rw [← h, Nat.mul_comm]⟩
    exact odd_dvd_two_pow hy this
  subst hy1
  have hs : 2 ^ s = 2 ^ K := by simpa using h
  exact ⟨rfl, (Nat.pow_right_inj (by decide : 1 < 2)).mp hs⟩

/-- If `x ^ e = 2 ^ K` with `e > 0`, then `x` is a power of two and `e` divides `K`. -/
theorem two_pow_eq_pow_imp {x e K : Nat} (he : 0 < e) (h : x ^ e = 2 ^ K) :
    ∃ t, x = 2 ^ t ∧ t * e = K := by
  have hxpos : 0 < x := by
    cases x with
    | zero =>
      have : 0 < 2 ^ K := Nat.two_pow_pos _
      cases e with
      | zero => omega
      | succ _ =>
        simp at h
        omega
    | succ _ => exact Nat.succ_pos _
  obtain ⟨s, y, hx, hy⟩ := exists_val2 x hxpos
  have hmul : 2 ^ (s * e) * y ^ e = 2 ^ K := by
    calc
      2 ^ (s * e) * y ^ e = (2 ^ s) ^ e * y ^ e := by rw [Nat.pow_mul]
      _ = (2 ^ s * y) ^ e := (Nat.mul_pow (2 ^ s) y e).symm
      _ = x ^ e := by rw [hx]
      _ = 2 ^ K := h
  have hye : (y ^ e) % 2 = 1 := odd_pow hy
  obtain ⟨hy1e, hse⟩ := eq_two_pow_of_mul_odd hye hmul
  have hy1 : y = 1 := by
    rcases (Nat.pow_eq_one (a := y) (n := e)).mp hy1e with hy | he0
    · exact hy
    · omega
  refine ⟨s, ?_, hse⟩
  rw [hx, hy1, Nat.mul_one]

theorem two_pow_not_eth_of_coprime {e K : Nat} (he : 1 < e)
    (hg : Nat.gcd e K = 1) (x : Nat) : 2 ^ K ≠ x ^ e := by
  intro h
  obtain ⟨t, _hx, hte⟩ := two_pow_eq_pow_imp (by omega : 0 < e) h.symm
  have hdvd : e ∣ K := ⟨t, by rw [← hte, Nat.mul_comm]⟩
  have : Nat.gcd e K = e := gcd_eq_left_of_dvd hdvd
  omega

theorem sumRange_le_sumRange_of_le {m n : Nat} (h : m ≤ n) (f : Nat → Nat) :
    sumRange m f ≤ sumRange n f := by
  refine le_induction (fun n => sumRange m f ≤ sumRange n f) h ?base ?step
  · exact Nat.le_refl _
  · intro k _hk ih
    rw [sumRange_succ]
    exact Nat.le_trans ih (Nat.le_add_right _ _)

/-! ### `3^e` overshoots `2^{K+1}` for large `e` (uses only `8 < 9`) -/

theorem three_pow_even_gt {t : Nat} (ht : 1 ≤ t) :
    2 ^ (3 * t) < 3 ^ (2 * t) := by
  have h : (2 ^ 3) ^ t < (3 ^ 2) ^ t :=
    Nat.pow_lt_pow_left (by decide : (8 : Nat) < 9) (Nat.ne_of_gt ht)
  rw [← Nat.pow_mul, ← Nat.pow_mul] at h
  exact h

theorem three_pow_gt_two_pow_of_large_even {e K : Nat}
    (heven : e % 2 = 0) (he : 2 * (K + 1) ≤ 3 * e) (he2 : 2 ≤ e) :
    2 ^ (K + 1) < 3 ^ e := by
  have hdvd : 2 ∣ e := Nat.dvd_of_mod_eq_zero heven
  have hsplit : e = 2 * (e / 2) := (Nat.mul_div_cancel' hdvd).symm
  have ht : 1 ≤ e / 2 := by omega
  have h3 : 2 ^ (3 * (e / 2)) < 3 ^ e := by
    have h := three_pow_even_gt ht
    have hr : 2 * (e / 2) = e := hsplit.symm
    rw [hr] at h
    exact h
  have hle : K + 1 ≤ 3 * (e / 2) := by
    have hx : 2 * (K + 1) ≤ 3 * (2 * (e / 2)) := by
      rw [← hsplit]
      exact he
    have hassoc : 3 * (2 * (e / 2)) = 2 * (3 * (e / 2)) := by
      calc
        3 * (2 * (e / 2)) = (3 * 2) * (e / 2) := (Nat.mul_assoc 3 2 (e / 2)).symm
        _ = (2 * 3) * (e / 2) := by rw [Nat.mul_comm (3 : Nat) 2]
        _ = 2 * (3 * (e / 2)) := Nat.mul_assoc 2 3 (e / 2)
    have : 2 * (K + 1) ≤ 2 * (3 * (e / 2)) := by
      rw [← hassoc]
      exact hx
    exact Nat.le_of_mul_le_mul_left this (by decide : (0 : Nat) < 2)
  have hle' : 2 ^ (K + 1) ≤ 2 ^ (3 * (e / 2)) :=
    Nat.pow_le_pow_right (by decide : (0 : Nat) < 2) hle
  exact Nat.lt_of_le_of_lt hle' h3

theorem three_pow_gt_two_pow_of_large_odd {e K : Nat}
    (hodd : e % 2 = 1) (he : 2 * (K + 1) + 3 ≤ 3 * e) (he3 : 3 ≤ e) :
    2 ^ (K + 1) < 3 ^ e := by
  have heq : e = 2 * (e / 2) + 1 := by
    have := Nat.div_add_mod e 2
    omega
  have ht : 1 ≤ e / 2 := by omega
  have hmul : 3 * e = 6 * (e / 2) + 3 := by
    have h := congrArg (fun t => 3 * t) heq
    calc
      3 * e = 3 * (2 * (e / 2) + 1) := h
      _ = 3 * (2 * (e / 2)) + 3 := by rw [Nat.mul_add, Nat.mul_one]
      _ = 6 * (e / 2) + 3 := by
        have : 3 * (2 * (e / 2)) = 6 * (e / 2) := by
          rw [← Nat.mul_assoc]
        rw [this]
  have hle : K + 1 ≤ 3 * (e / 2) := by
    have : 2 * (K + 1) + 3 ≤ 6 * (e / 2) + 3 := by
      rw [← hmul]
      exact he
    omega
  have hlt : 2 ^ (3 * (e / 2)) < 3 ^ (2 * (e / 2)) := three_pow_even_gt ht
  have hle' : 2 ^ (K + 1) ≤ 2 ^ (3 * (e / 2)) :=
    Nat.pow_le_pow_right (by decide : (0 : Nat) < 2) hle
  have hmid : 2 ^ (K + 1) < 3 ^ (2 * (e / 2)) := Nat.lt_of_le_of_lt hle' hlt
  have hlast : 3 ^ (2 * (e / 2)) < 3 ^ (2 * (e / 2) + 1) :=
    Nat.pow_lt_pow_succ (by decide : (1 : Nat) < 3)
  have hr : 2 * (e / 2) + 1 = e := heq.symm
  rw [hr] at hlast
  exact Nat.lt_trans hmid hlast

theorem three_pow_gt_two_pow_succ {e K : Nat} (he : 3 ≤ e)
    (h : 2 * (K + 1) + 3 ≤ 3 * e) : 2 ^ (K + 1) < 3 ^ e := by
  cases Nat.mod_two_eq_zero_or_one e with
  | inl heven =>
    have : 2 * (K + 1) ≤ 3 * e := by omega
    exact three_pow_gt_two_pow_of_large_even heven this (by omega)
  | inr hodd =>
    exact three_pow_gt_two_pow_of_large_odd hodd h he

/-! ### Geometric sum: `(x-1) * geomSum + 1 = x^n` (`x ≥ 1`) -/

def geomSum (x n : Nat) : Nat := sumRange n (fun i => x ^ i)

theorem geomSum_succ (x n : Nat) :
    geomSum x (n + 1) = geomSum x n + x ^ n := rfl

theorem geomSum_one (x : Nat) : geomSum x 1 = 1 := by
  simp [geomSum, sumRange_succ, sumRange_zero]

theorem geomSum_two (x : Nat) : geomSum x 2 = 1 + x := by
  simp [geomSum, sumRange_succ, sumRange_zero]

theorem geomSum_eval {x n : Nat} (hx : 1 ≤ x) :
    (x - 1) * geomSum x n + 1 = x ^ n := by
  induction n with
  | zero => simp [geomSum, sumRange]
  | succ n ih =>
    rw [geomSum_succ, Nat.mul_add, Nat.add_right_comm, ih, Nat.pow_succ]
    have hdistrib : x ^ n + (x - 1) * x ^ n = x * x ^ n := by
      calc
        x ^ n + (x - 1) * x ^ n
            = 1 * x ^ n + (x - 1) * x ^ n := by rw [Nat.one_mul]
        _ = (1 + (x - 1)) * x ^ n := (Nat.add_mul 1 (x - 1) (x ^ n)).symm
        _ = (x - 1 + 1) * x ^ n := by rw [Nat.add_comm]
        _ = x * x ^ n := by rw [Nat.sub_add_cancel hx]
    rw [hdistrib, Nat.mul_comm]

theorem pow_sub_one_eq_mul_geomSum {x n : Nat} (hx : 1 ≤ x) :
    x ^ n - 1 = (x - 1) * geomSum x n := by
  have h := geomSum_eval (n := n) hx
  have : 1 ≤ x ^ n := Nat.one_le_pow n x (by omega)
  omega

theorem geomSum_ge_succ {x e : Nat} (he : 2 ≤ e) :
    1 + x ≤ geomSum x e :=
  Nat.le_trans (Nat.le_of_eq (geomSum_two x).symm)
    (sumRange_le_sumRange_of_le he _)

theorem sumRange_mod2_of_all_odd {n : Nat} {f : Nat → Nat}
    (h : ∀ i, i < n → f i % 2 = 1) :
    sumRange n f % 2 = n % 2 := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [sumRange_succ, Nat.add_mod,
      ih fun i hi => h i (Nat.lt_succ_of_le (Nat.le_of_lt hi)),
      h n (Nat.lt_succ_self n)]
    omega

theorem geomSum_mod2_of_odd {x e : Nat} (hx : x % 2 = 1) :
    geomSum x e % 2 = e % 2 :=
  sumRange_mod2_of_all_odd fun _ _ => odd_pow hx

/-- Odd base, odd exponent `≥ 3`: `x^e - 1` is never a power of two. -/
theorem odd_pow_sub_one_ne_two_pow {x e K : Nat}
    (hx : 3 ≤ x) (hxodd : x % 2 = 1) (he : 3 ≤ e) (heodd : e % 2 = 1) :
    x ^ e - 1 ≠ 2 ^ K := by
  intro h
  have hx1 : 1 ≤ x := by omega
  have hfac := pow_sub_one_eq_mul_geomSum (n := e) hx1
  have hdiv : geomSum x e ∣ 2 ^ K := by
    rw [← h, hfac]
    exact Nat.dvd_mul_left _ _
  have hgsodd : geomSum x e % 2 = 1 := by
    have := geomSum_mod2_of_odd (e := e) hxodd
    omega
  have hg1 : geomSum x e = 1 := odd_dvd_two_pow hgsodd hdiv
  have hge : 1 + x ≤ geomSum x e := geomSum_ge_succ (by omega)
  omega

/-- `x^e = 2^K + 1` is impossible for odd `x ≥ 3` and odd `e ≥ 3`. -/
theorem pow_eq_two_pow_add_one_of_odd_odd {x e K : Nat}
    (hx : 3 ≤ x) (hxodd : x % 2 = 1) (he : 3 ≤ e) (heodd : e % 2 = 1) :
    x ^ e ≠ 2 ^ K + 1 := by
  intro h
  have hx1 : 1 ≤ x := by omega
  have hpow : 1 ≤ x ^ e := Nat.one_le_pow e x (by omega)
  have : x ^ e - 1 = 2 ^ K := by omega
  exact odd_pow_sub_one_ne_two_pow hx hxodd he heodd this

/-- Even `x`: `x^e` is even, so `x^e - 1` is odd and cannot equal `2^K` (`K ≥ 1`). -/
theorem even_pow_sub_one_ne_two_pow {x e K : Nat}
    (heven : x % 2 = 0) (he : 1 ≤ e) (hK : 1 ≤ K) :
    x ^ e ≠ 2 ^ K + 1 := by
  intro h
  have hpe : (x ^ e) % 2 = 0 :=
    Nat.mod_eq_zero_of_dvd (two_dvd_pow_of (Nat.dvd_of_mod_eq_zero heven) (by omega))
  have hK0 : (2 ^ K) % 2 = 0 := two_pow_mod_two hK
  omega

theorem two_pow_mod4 {K : Nat} (hK : 2 ≤ K) : (2 ^ K) % 4 = 0 := by
  have : 2 ^ 2 ∣ 2 ^ K := Nat.pow_dvd_pow 2 hK
  exact Nat.mod_eq_zero_of_dvd this

theorem odd_mod4 {z : Nat} (hz : z % 2 = 1) : z % 4 = 1 ∨ z % 4 = 3 := by
  omega

theorem odd_sq_add_one_mod4 {z : Nat} (hz : z % 2 = 1) :
    (z ^ 2 + 1) % 4 = 2 := by
  have hz4 := odd_mod4 hz
  have hpow : z ^ 2 % 4 = (z % 4) ^ 2 % 4 := Nat.pow_mod z 2 4
  have hsq : z ^ 2 % 4 = 1 := by
    rcases hz4 with h | h <;> rw [hpow, h]
  omega

/-- Even exponent: `x^e + 1 = z^2 + 1 ≡ 2 (mod 4)` if `x` is odd, not a power of 4. -/
theorem two_pow_sub_pow_ne_one_of_even_exp {x e K : Nat}
    (hxodd : x % 2 = 1) (heven : e % 2 = 0) (he : 2 ≤ e) (hK : 2 ≤ K) :
    2 ^ K ≠ x ^ e + 1 := by
  intro h
  have hdvd : 2 ∣ e := Nat.dvd_of_mod_eq_zero heven
  have hsplit : e = 2 * (e / 2) := (Nat.mul_div_cancel' hdvd).symm
  have hzpow : x ^ e = (x ^ (e / 2)) ^ 2 := by
    have hmul : (x ^ (e / 2)) ^ 2 = x ^ ((e / 2) * 2) :=
      (Nat.pow_mul x (e / 2) 2).symm
    have hcomm : (e / 2) * 2 = 2 * (e / 2) := Nat.mul_comm _ _
    rw [hmul, hcomm, ← hsplit]
  have hzodd : (x ^ (e / 2)) % 2 = 1 := odd_pow hxodd
  have h4 : ((x ^ (e / 2)) ^ 2 + 1) % 4 = 2 := odd_sq_add_one_mod4 hzodd
  have h0 : (2 ^ K) % 4 = 0 := two_pow_mod4 hK
  have : (2 ^ K) % 4 = ((x ^ (e / 2)) ^ 2 + 1) % 4 := by
    rw [h, hzpow]
  omega

/-- Even `x`: `x^e + 1` is odd, so cannot equal `2^K` (`K ≥ 1`). -/
theorem two_pow_sub_even_pow_ne_one {x e K : Nat}
    (heven : x % 2 = 0) (he : 1 ≤ e) (hK : 1 ≤ K) :
    2 ^ K ≠ x ^ e + 1 := by
  intro h
  have hpe : (x ^ e) % 2 = 0 :=
    Nat.mod_eq_zero_of_dvd (two_dvd_pow_of (Nat.dvd_of_mod_eq_zero heven) (by omega))
  have hK0 : (2 ^ K) % 2 = 0 := two_pow_mod_two hK
  omega

/-! ### `|2^a - 2^b|` -/

def natAbsDiff (a b : Nat) : Nat := if a < b then b - a else a - b

theorem two_pow_lt_iff {a b : Nat} : 2 ^ a < 2 ^ b ↔ a < b :=
  Nat.pow_lt_pow_iff_right (by decide : 1 < 2)

theorem two_pow_split {a b : Nat} (h : a ≤ b) :
    2 ^ b = 2 ^ a * 2 ^ (b - a) := by
  rw [← Nat.pow_add, Nat.add_comm, Nat.sub_add_cancel h]

theorem two_pow_eq_two_mul_pred' {k : Nat} (hk : 1 ≤ k) :
    2 ^ k = 2 * 2 ^ (k - 1) := by
  have h : k = k - 1 + 1 := by omega
  have : 2 ^ k = 2 ^ (k - 1 + 1) := congrArg (fun t => 2 ^ t) h
  rw [this, Nat.pow_succ']

theorem two_pow_sub_ge_half_max {a b : Nat} (h : a < b) :
    2 ^ (b - 1) ≤ 2 ^ b - 2 ^ a := by
  have hb : 1 ≤ b := by omega
  have ha : a ≤ b - 1 := by omega
  have hle : 2 ^ a ≤ 2 ^ (b - 1) :=
    Nat.pow_le_pow_right (by decide : (0 : Nat) < 2) ha
  have hsplit := two_pow_eq_two_mul_pred' hb
  omega

/-- Case B.1: if `t ≠ K` and `K ≥ 2` then `|2^t - 2^K| ≥ 2^{K/2}`. -/
theorem abs_two_pow_diff_ge_half {t K : Nat} (hne : t ≠ K) (hK : 2 ≤ K) :
    2 ^ (K / 2) ≤ natAbsDiff (2 ^ t) (2 ^ K) := by
  unfold natAbsDiff
  have hhalf : 2 ^ (K / 2) ≤ 2 ^ (K - 1) :=
    Nat.pow_le_pow_right (by decide : (0 : Nat) < 2) (by omega)
  cases Nat.lt_trichotomy t K with
  | inl hlt =>
    rw [if_pos (two_pow_lt_iff.mpr hlt)]
    exact Nat.le_trans hhalf (two_pow_sub_ge_half_max hlt)
  | inr hrest =>
    cases hrest with
    | inl heq => exact (hne heq).elim
    | inr hgt =>
      have hnot : ¬ 2 ^ t < 2 ^ K := fun h =>
        Nat.lt_asymm hgt (two_pow_lt_iff.mp h)
      rw [if_neg hnot]
      have h1 : 2 ^ (t - 1) ≤ 2 ^ t - 2 ^ K := two_pow_sub_ge_half_max hgt
      have h2 : 2 ^ K ≤ 2 ^ (t - 1) :=
        Nat.pow_le_pow_right (by decide : (0 : Nat) < 2) (by omega)
      have h3 : 2 ^ (K / 2) ≤ 2 ^ K :=
        Nat.pow_le_pow_right (by decide : (0 : Nat) < 2) (Nat.div_le_self _ _)
      exact Nat.le_trans h3 (Nat.le_trans h2 h1)

theorem pow_two_base_gap {t e K : Nat} (hne : t * e ≠ K) (hK : 2 ≤ K) :
    2 ^ (K / 2) ≤ natAbsDiff (2 ^ (t * e)) (2 ^ K) :=
  abs_two_pow_diff_ge_half hne hK

theorem se_eq_K_imp_dvd {s e K : Nat} (h : s * e = K) : e ∣ K :=
  ⟨s, by rw [← h, Nat.mul_comm]⟩

theorem even_base_se_ne_of_coprime {s e K : Nat} (he : 1 < e)
    (hg : Nat.gcd e K = 1) : s * e ≠ K := by
  intro h
  have : e ∣ K := se_eq_K_imp_dvd h
  have : Nat.gcd e K = e := gcd_eq_left_of_dvd this
  omega

end LeanA113258
