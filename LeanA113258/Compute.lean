import LeanA113258.Defs

namespace LeanA113258

/-! Concrete values from the official file / OEIS. -/

theorem a_1 : a 1 = 1 := rfl
theorem a_2 : a 2 = 3 := rfl
theorem a_3 : a 3 = 11 := rfl
theorem a_4 : a 4 = 125 := by native_decide
theorem a_4_is_perfect_power : IsPerfectPower (a 4) :=
  ⟨5, 3, by native_decide, by native_decide, by native_decide⟩

theorem a_5_val : a 5 = 16824569 := by native_decide
theorem a_6_val : a 6 = 1329227995784915877642188398793079569 := by native_decide

/-- Integer `e`-th root via binary search. Fuel `n.log2 + 8` is enough to
halve `[1, n]` down to a singleton. -/
def natNthRoot.go (n e lo hi fuel : Nat) : Nat :=
  match fuel with
  | 0 => lo
  | fuel + 1 =>
    if lo ≥ hi then lo
    else
      let mid := (lo + hi + 1) / 2
      if mid ^ e ≤ n then natNthRoot.go n e mid hi fuel
      else natNthRoot.go n e lo (mid - 1) fuel

def natNthRoot (n e : Nat) : Nat :=
  if e = 0 then 0
  else natNthRoot.go n e 1 n (n.log2 + 8)

/-- `true` iff the floor `e`-th root strictly sandwiches `n`. -/
def rootGap (n e : Nat) : Bool :=
  decide (natNthRoot n e ^ e < n ∧ n < (natNthRoot n e + 1) ^ e)

/-- Check `rootGap n e` for `e = start, start+1, …, start+remaining-1`. -/
def checkFrom (n start remaining : Nat) : Bool :=
  match remaining with
  | 0 => true
  | remaining + 1 => rootGap n start && checkFrom n (start + 1) remaining

theorem rootGap_true {n e : Nat} (h : rootGap n e = true) :
    natNthRoot n e ^ e < n ∧ n < (natNthRoot n e + 1) ^ e := by
  unfold rootGap at h
  exact of_decide_eq_true h

theorem checkFrom_spec (n start remaining : Nat)
    (h : checkFrom n start remaining = true) :
    ∀ e, start ≤ e → e < start + remaining → rootGap n e = true := by
  induction remaining generalizing start with
  | zero =>
    intro e hle hlt
    exact absurd hle (Nat.not_le_of_gt hlt)
  | succ remaining ih =>
    simp [checkFrom] at h
    obtain ⟨hhere, hrest⟩ := h
    intro e hle hlt
    cases Nat.eq_or_lt_of_le hle with
    | inl heq =>
      subst heq
      exact hhere
    | inr hlt' =>
      exact ih (start + 1) hrest e (Nat.succ_le_of_lt hlt') (by omega)

/-- Search `[1, hi]` instead of `[1, n]`. The gap `r^e < n < (r+1)^e` is the
    certificate; `hi` only speeds up the search. -/
def natNthRootHi (n e hi : Nat) : Nat :=
  if e = 0 then 0
  else natNthRoot.go n e 1 hi (hi.log2 + 8)

def rootGapHi (n e hi : Nat) : Bool :=
  decide (natNthRootHi n e hi ^ e < n ∧ n < (natNthRootHi n e hi + 1) ^ e)

/-- Upper bound `2^{K/e + 1}` is enough once `n < 2^{K+1}`. -/
def rootGapDyadic (n e K : Nat) : Bool :=
  rootGapHi n e (2 ^ (K / e + 1))

/-- Like `checkFrom`, but skip exponents not coprime to `K`. -/
def checkCoprimeFrom (n start remaining K : Nat) : Bool :=
  match remaining with
  | 0 => true
  | remaining + 1 =>
      (if Nat.gcd start K = 1 then rootGapDyadic n start K else true) &&
        checkCoprimeFrom n (start + 1) remaining K

theorem rootGapHi_true {n e hi : Nat} (h : rootGapHi n e hi = true) :
    natNthRootHi n e hi ^ e < n ∧ n < (natNthRootHi n e hi + 1) ^ e := by
  unfold rootGapHi at h
  exact of_decide_eq_true h

theorem not_eq_pow_of_rootGapHi {n b e hi : Nat} (h : rootGapHi n e hi = true) :
    n ≠ b ^ e := by
  obtain ⟨hlt, hgt⟩ := rootGapHi_true h
  intro hab
  cases Nat.lt_or_ge b (natNthRootHi n e hi + 1) with
  | inl hb_lt =>
    have : b ^ e ≤ natNthRootHi n e hi ^ e :=
      Nat.pow_le_pow_left (Nat.le_of_lt_succ hb_lt) e
    have : n ≤ natNthRootHi n e hi ^ e := hab ▸ this
    exact Nat.lt_irrefl n (Nat.lt_of_le_of_lt this hlt)
  | inr hb_ge =>
    have : (natNthRootHi n e hi + 1) ^ e ≤ b ^ e := Nat.pow_le_pow_left hb_ge e
    have : (natNthRootHi n e hi + 1) ^ e ≤ n := hab ▸ this
    exact Nat.lt_irrefl n (Nat.lt_of_lt_of_le hgt this)

theorem not_eq_pow_of_rootGapDyadic {n b e K : Nat}
    (h : rootGapDyadic n e K = true) : n ≠ b ^ e :=
  not_eq_pow_of_rootGapHi h

theorem checkCoprimeFrom_spec (n start remaining K : Nat)
    (h : checkCoprimeFrom n start remaining K = true) :
    ∀ e, start ≤ e → e < start + remaining → Nat.gcd e K = 1 →
      rootGapDyadic n e K = true := by
  induction remaining generalizing start with
  | zero =>
    intro e hle hlt
    exact absurd hle (Nat.not_le_of_gt hlt)
  | succ remaining ih =>
    simp [checkCoprimeFrom] at h
    obtain ⟨hhere, hrest⟩ := h
    intro e hle hlt hg
    cases Nat.eq_or_lt_of_le hle with
    | inl heq =>
      subst heq
      cases hhere with
      | inl hne => exact (hne hg).elim
      | inr hgap => exact hgap
    | inr hlt' =>
      exact ih (start + 1) hrest e (Nat.succ_le_of_lt hlt') (by omega) hg

theorem pow2_le_of_base {b e : Nat} (hb : 1 < b) : 2 ^ e ≤ b ^ e :=
  Nat.pow_le_pow_left (Nat.succ_le_of_lt hb) e

theorem exp_le_of_lt_pow2 {n e eMax : Nat}
    (hbound : n < 2 ^ (eMax + 1)) (hle : 2 ^ e ≤ n) : e ≤ eMax := by
  have hlt : 2 ^ e < 2 ^ (eMax + 1) := Nat.lt_of_le_of_lt hle hbound
  exact Nat.lt_succ_iff.mp ((Nat.pow_lt_pow_iff_right (by decide : 1 < 2)).mp hlt)

/-- If `2^(eMax+1) > n` and every exponent `2..eMax` has a strict root gap,
then `n` is not a perfect power. -/
theorem not_perfect_power_of_gaps (n eMax : Nat)
    (hbound : n < 2 ^ (eMax + 1))
    (hcheck : checkFrom n 2 (eMax - 1) = true)
    (heMax : 1 < eMax) :
    ¬ IsPerfectPower n := by
  rintro ⟨b, e, hb, he, hn⟩
  have h2e : 2 ^ e ≤ n := hn ▸ pow2_le_of_base hb
  have he_le : e ≤ eMax := exp_le_of_lt_pow2 hbound h2e
  have he2 : 2 ≤ e := Nat.succ_le_of_lt he
  have hg : rootGap n e = true :=
    checkFrom_spec n 2 (eMax - 1) hcheck e he2 (by omega)
  obtain ⟨hlt, hgt⟩ := rootGap_true hg
  cases Nat.lt_or_ge b (natNthRoot n e + 1) with
  | inl hb_lt =>
    have : b ^ e ≤ natNthRoot n e ^ e :=
      Nat.pow_le_pow_left (Nat.le_of_lt_succ hb_lt) e
    have : n ≤ natNthRoot n e ^ e := hn ▸ this
    exact Nat.lt_irrefl n (Nat.lt_of_le_of_lt this hlt)
  | inr hb_ge =>
    have : (natNthRoot n e + 1) ^ e ≤ b ^ e := Nat.pow_le_pow_left hb_ge e
    have : (natNthRoot n e + 1) ^ e ≤ n := hn ▸ this
    exact Nat.lt_irrefl n (Nat.lt_of_lt_of_le hgt this)

set_option maxHeartbeats 4000000

theorem a_5_not_perfect_power : ¬ IsPerfectPower (a 5) := by
  rw [a_5_val]
  refine not_perfect_power_of_gaps 16824569 24 ?bound ?check (by decide)
  · native_decide
  · native_decide

theorem a_6_not_perfect_power : ¬ IsPerfectPower (a 6) := by
  rw [a_6_val]
  refine not_perfect_power_of_gaps 1329227995784915877642188398793079569 120 ?bound ?check
      (by decide)
  · native_decide
  · native_decide

set_option maxHeartbeats 8000000

/-- Remaining coprime exponents for `n = 7`: `7 ≤ e ≤ 481` (`475` values). -/
theorem a7_coprime_gaps : checkCoprimeFrom (a 7) 7 475 720 = true := by
  native_decide

end LeanA113258
