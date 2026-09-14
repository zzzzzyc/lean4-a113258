import LeanA113258.ProofProgress
import LeanA113258.CoprimeLarge
import LeanA113258.Polarization

namespace LeanA113258

/-!
  Conditional Baker / linear-form lower bounds for the remaining coprime-large
  window. Every `def … : Prop` below is a hypothesis; this file does not judge
  whether any instance is true, and it does not declare `officialConjecture_false`.
-/

/-- 假设（其真假不在本仓库判定）：任何超过 2^K 的 e 次幂，超出量至少是 2^K / 2^(L b e K)。
    这是 Λ ≥ 2^(−L) 的整数化。不要试图证明任何非平凡实例。 -/
def PowGapLowerBound (L : Nat → Nat → Nat → Nat) : Prop :=
  ∀ b e K : Nat, 3 ≤ b → 2 ≤ e → 2 ^ K < b ^ e →
    2 ^ K ≤ (b ^ e - 2 ^ K) * 2 ^ L b e K

theorem gap_ge_of_bound {L : Nat → Nat → Nat → Nat} (hL : PowGapLowerBound L)
    {b e K : Nat} (hb : 3 ≤ b) (he : 2 ≤ e) (hlt : 2 ^ K < b ^ e)
    (hsmall : 2 * L b e K ≤ K) :
    2 ^ (K / 2) ≤ b ^ e - 2 ^ K := by
  have hgap := hL b e K hb he hlt
  have hLle : L b e K ≤ K / 2 :=
    (Nat.le_div_iff_mul_le (by decide : (0 : Nat) < 2)).2 (by
      rw [Nat.mul_comm]
      exact hsmall)
  have hsum : K / 2 + L b e K ≤ K := by
    have hhalf : K / 2 * 2 ≤ K := Nat.div_mul_le_self K 2
    have hhalf' : 2 * (K / 2) ≤ K := by
      rw [Nat.mul_comm]
      exact hhalf
    omega
  have hpow : 2 ^ (K / 2) * 2 ^ L b e K ≤ 2 ^ K := by
    rw [← Nat.pow_add]
    exact Nat.pow_le_pow_right (by decide : (0 : Nat) < 2) hsum
  have hmul : 2 ^ (K / 2) * 2 ^ L b e K ≤ (b ^ e - 2 ^ K) * 2 ^ L b e K :=
    Nat.le_trans hpow hgap
  exact Nat.le_of_mul_le_mul_right hmul (Nat.two_pow_pos _)

theorem not_eth_power_of_gap_bound {L : Nat → Nat → Nat → Nat} (hL : PowGapLowerBound L)
    {n b e : Nat} (hn : 7 ≤ n) (hb : 3 ≤ b) (he : n ≤ e)
    (hg : Nat.gcd e (fact (n - 1)) = 1)
    (hsmall : 2 * L b e (fact (n - 1)) ≤ fact (n - 1)) : a n ≠ b ^ e := by
  intro hab
  have hsetup := coprime_large_setup hn hb he hg hab
  have hlt := hsetup.2.1
  have hgap := hsetup.2.2.1
  have he2 : 2 ≤ e := by omega
  have hge := gap_ge_of_bound hL hb he2 hlt hsmall
  omega

theorem six_pow_add_two_pow_lt {B : Nat} (hB : 2 ≤ B) : 6 ^ B + 2 ^ B < 8 ^ B := by
  refine le_induction (fun B => 6 ^ B + 2 ^ B < 8 ^ B) hB ?base ?step
  · decide
  · intro k _hk ih
    have hL : 6 ^ (k + 1) + 2 ^ (k + 1) = 6 * 6 ^ k + 2 * 2 ^ k := by
      rw [Nat.pow_succ', Nat.pow_succ']
    have hle : 6 * 6 ^ k + 2 * 2 ^ k ≤ 6 * 6 ^ k + 6 * 2 ^ k :=
      Nat.add_le_add_left
        (Nat.mul_le_mul_right (2 ^ k) (by decide : (2 : Nat) ≤ 6)) _
    have hdist : 6 * 6 ^ k + 6 * 2 ^ k = 6 * (6 ^ k + 2 ^ k) :=
      (Nat.mul_add 6 _ _).symm
    have hmid : 6 * (6 ^ k + 2 ^ k) < 6 * 8 ^ k :=
      Nat.mul_lt_mul_of_pos_left ih (by decide : (0 : Nat) < 6)
    have h8 : 6 * 8 ^ k ≤ 8 ^ (k + 1) := by
      rw [Nat.pow_succ']
      exact Nat.mul_le_mul_right (8 ^ k) (by decide : (6 : Nat) ≤ 8)
    rw [hL]
    exact Nat.lt_of_le_of_lt hle (hdist ▸ Nat.lt_of_lt_of_le hmid h8)

theorem delta_lt_two_pow_three_B {n : Nat} (hn : 7 ≤ n) :
    delta n < 2 ^ (3 * fact (n - 2)) := by
  have hδ := delta_eq_sixB_add_rho (by omega : 3 ≤ n)
  have hρ := rho_lt_twoB hn
  have hB2 : 2 ≤ fact (n - 2) := by
    have : fact 2 ≤ fact (n - 2) := fact_le_of_le (by omega)
    simpa [fact_two] using this
  have hlt := six_pow_add_two_pow_lt hB2
  have h8 : 8 ^ fact (n - 2) = 2 ^ (3 * fact (n - 2)) := by
    have h8eq : (8 : Nat) = 2 ^ 3 := by decide
    rw [h8eq, Nat.pow_mul]
  have hsum : 6 ^ fact (n - 2) + rho n <
      6 ^ fact (n - 2) + 2 ^ fact (n - 2) := by omega
  have hlt8 : 6 ^ fact (n - 2) + rho n < 8 ^ fact (n - 2) :=
    Nat.lt_trans hsum hlt
  rw [hδ, ← h8]
  exact hlt8

theorem not_eth_power_of_gap_bound' {L : Nat → Nat → Nat → Nat} (hL : PowGapLowerBound L)
    {n b e : Nat} (hn : 7 ≤ n) (hb : 3 ≤ b) (he : n ≤ e)
    (hg : Nat.gcd e (fact (n - 1)) = 1)
    (hsmall : L b e (fact (n - 1)) + 3 * fact (n - 2) ≤ fact (n - 1)) :
    a n ≠ b ^ e := by
  intro hab
  have hsetup := coprime_large_setup hn hb he hg hab
  have hlt := hsetup.2.1
  have he2 : 2 ≤ e := by omega
  have hbound := hL b e (fact (n - 1)) hb he2 hlt
  have ha := a_eq_main_add_delta (by omega : 2 ≤ n)
  have hgap : b ^ e - 2 ^ fact (n - 1) = delta n := by
    simp [mainTerm] at ha
    omega
  have hδlt := delta_lt_two_pow_three_B hn
  have hgaplt : b ^ e - 2 ^ fact (n - 1) < 2 ^ (3 * fact (n - 2)) := by
    rw [hgap]
    exact hδlt
  have hmul :
      (b ^ e - 2 ^ fact (n - 1)) * 2 ^ L b e (fact (n - 1))
        < 2 ^ (3 * fact (n - 2)) * 2 ^ L b e (fact (n - 1)) :=
    Nat.mul_lt_mul_of_pos_right hgaplt (Nat.two_pow_pos _)
  have hpow :
      2 ^ (3 * fact (n - 2)) * 2 ^ L b e (fact (n - 1))
        = 2 ^ (3 * fact (n - 2) + L b e (fact (n - 1))) :=
    (Nat.pow_add 2 _ _).symm
  have hsmall' :
      3 * fact (n - 2) + L b e (fact (n - 1)) ≤ fact (n - 1) := by
    rw [Nat.add_comm]
    exact hsmall
  have hleK :
      2 ^ (3 * fact (n - 2) + L b e (fact (n - 1)))
        ≤ 2 ^ fact (n - 1) :=
    Nat.pow_le_pow_right (by decide : (0 : Nat) < 2) hsmall'
  have hstrict :
      (b ^ e - 2 ^ fact (n - 1)) * 2 ^ L b e (fact (n - 1))
        < 2 ^ fact (n - 1) := by
    rw [hpow] at hmul
    exact Nat.lt_of_lt_of_le hmul hleK
  exact Nat.lt_irrefl _ (Nat.lt_of_le_of_lt hbound hstrict)

/-- 假设（其真假不在本仓库判定）：Baker–Wüstholz 形损失指数。不是定理。 -/
def BakerHyp (C : Nat) : Prop :=
  PowGapLowerBound fun b _e K => C * (Nat.log2 b + 1) * (Nat.log2 K + 1)

theorem remaining_log2_base_le {n b e : Nat} (hn : 7 ≤ n) (hb : 2 ≤ b) (he : 1 < e)
    (hg : Nat.gcd e (fact (n - 1)) = 1) (hab : a n = b ^ e) :
    Nat.log2 b ≤ fact (n - 1) / e := by
  have hb0 : b ≠ 0 := by omega
  have hdy := remaining_base_dyadic hn hb he hg hab
  have hlt : Nat.log2 b < fact (n - 1) / e + 1 :=
    (Nat.log2_lt hb0).2 hdy.2
  omega

theorem not_eth_power_of_bakerHyp {C : Nat} (hC : BakerHyp C)
    {n b e : Nat} (hn : 7 ≤ n) (hb : 3 ≤ b) (he : n ≤ e)
    (hg : Nat.gcd e (fact (n - 1)) = 1)
    (hsmall : 4 * C * (Nat.log2 (fact (n - 1)) + 1) ≤ e) : a n ≠ b ^ e := by
  intro hab
  by_cases hbig : fact (n - 1) + 1 ≤ e
  · exact not_eth_power_of_exp_ge_succ_K hn (by omega : 2 ≤ b) hbig hab
  · have he0 : 0 < e := by omega
    have hq1 : 1 ≤ fact (n - 1) / e :=
      (Nat.le_div_iff_mul_le he0).2 (by omega)
    have hlog :=
      remaining_log2_base_le hn (by omega : 2 ≤ b) (by omega : 1 < e) hg hab
    have hle1 : Nat.log2 b + 1 ≤ fact (n - 1) / e + 1 :=
      Nat.add_le_add_right hlog 1
    let M := C * (Nat.log2 (fact (n - 1)) + 1)
    have h4M : 4 * M ≤ e := by
      have hassoc : 4 * M = 4 * C * (Nat.log2 (fact (n - 1)) + 1) :=
        (Nat.mul_assoc 4 C (Nat.log2 (fact (n - 1)) + 1)).symm
      rwa [hassoc]
    have h1 :
        C * (Nat.log2 b + 1) * (Nat.log2 (fact (n - 1)) + 1)
          ≤ C * (fact (n - 1) / e + 1) * (Nat.log2 (fact (n - 1)) + 1) :=
      Nat.mul_le_mul_right (Nat.log2 (fact (n - 1)) + 1)
        (Nat.mul_le_mul_left C hle1)
    have four_mul_eq (x y : Nat) : 4 * x * y = 2 * (2 * x * y) := by
      have hx : 4 * x = 2 * (2 * x) := by
        have : (4 : Nat) = 2 * 2 := rfl
        rw [this]
        exact Nat.mul_assoc 2 2 x
      calc
        4 * x * y = (4 * x) * y := rfl
        _ = (2 * (2 * x)) * y := by rw [hx]
        _ = 2 * ((2 * x) * y) := Nat.mul_assoc 2 (2 * x) y
        _ = 2 * (2 * x * y) := rfl
    have h2M : 2 * M * (fact (n - 1) / e + 1) ≤ fact (n - 1) := by
      have h4 : 4 * M * (fact (n - 1) / e + 1) ≤ e * (fact (n - 1) / e + 1) :=
        Nat.mul_le_mul_right (fact (n - 1) / e + 1) h4M
      have hqe : e * (fact (n - 1) / e) ≤ fact (n - 1) := by
        rw [Nat.mul_comm]
        exact Nat.div_mul_le_self _ _
      have hsum : e * (fact (n - 1) / e + 1) = e * (fact (n - 1) / e) + e := by
        rw [Nat.mul_add, Nat.mul_one]
      have he_le : e ≤ e * (fact (n - 1) / e) :=
        Nat.le_mul_of_pos_right e hq1
      have h2qe : e * (fact (n - 1) / e + 1) ≤ 2 * (e * (fact (n - 1) / e)) := by
        rw [hsum, Nat.two_mul]
        exact Nat.add_le_add_left he_le _
      have h4le2K : 4 * M * (fact (n - 1) / e + 1) ≤ 2 * fact (n - 1) :=
        Nat.le_trans (Nat.le_trans h4 h2qe) (Nat.mul_le_mul_left 2 hqe)
      have hre := four_mul_eq M (fact (n - 1) / e + 1)
      have hpos2 : (0 : Nat) < 2 := by decide
      have : 2 * (2 * M * (fact (n - 1) / e + 1)) ≤ 2 * fact (n - 1) := by
        rwa [← hre]
      exact Nat.le_of_mul_le_mul_left this hpos2
    have hside :
        2 * (C * (Nat.log2 b + 1) * (Nat.log2 (fact (n - 1)) + 1))
          ≤ fact (n - 1) := by
      have h2 :
          2 * (C * (Nat.log2 b + 1) * (Nat.log2 (fact (n - 1)) + 1))
            ≤ 2 * (C * (fact (n - 1) / e + 1) * (Nat.log2 (fact (n - 1)) + 1)) :=
        Nat.mul_le_mul_left 2 h1
      have hr :
          C * (fact (n - 1) / e + 1) * (Nat.log2 (fact (n - 1)) + 1)
            = M * (fact (n - 1) / e + 1) :=
        Nat.mul_right_comm C (fact (n - 1) / e + 1)
          (Nat.log2 (fact (n - 1)) + 1)
      have hassoc : 2 * (M * (fact (n - 1) / e + 1))
          = 2 * M * (fact (n - 1) / e + 1) :=
        (Nat.mul_assoc 2 M (fact (n - 1) / e + 1)).symm
      calc
        2 * (C * (Nat.log2 b + 1) * (Nat.log2 (fact (n - 1)) + 1))
            ≤ 2 * (C * (fact (n - 1) / e + 1) * (Nat.log2 (fact (n - 1)) + 1)) :=
              h2
        _ = 2 * (M * (fact (n - 1) / e + 1)) := by rw [hr]
        _ = 2 * M * (fact (n - 1) / e + 1) := hassoc
        _ ≤ fact (n - 1) := h2M
    exact not_eth_power_of_gap_bound hC hn hb he hg hside hab

theorem officialConjecture_false_of_bakerHyp_and_small
    {C : Nat} (hC : BakerHyp C)
    (hsmallAll : ∀ n b e, 12 ≤ n → 3 ≤ b → n ≤ e →
      e < 4 * C * (Nat.log2 (fact (n - 1)) + 1) →
      Nat.gcd e (fact (n - 1)) = 1 → a n ≠ b ^ e) :
    ¬ officialConjecture := by
  intro h
  obtain ⟨n, b, e, hn, hb, _, he, _, hg, hab⟩ :=
    officialConjecture_iff_remaining_mod210.mp h
  have hn7 : 7 ≤ n := by omega
  have hb3 : 3 ≤ b := by omega
  by_cases hlt : e < 4 * C * (Nat.log2 (fact (n - 1)) + 1)
  · exact hsmallAll n b e hn hb3 he hlt hg hab
  · have hge : 4 * C * (Nat.log2 (fact (n - 1)) + 1) ≤ e := by omega
    exact not_eth_power_of_bakerHyp hC hn7 hb3 he hg hge hab

/-- 假设（其真假不在本仓库判定）：两对数 LMN 形。不是定理。 -/
def TwoLogHyp (C c0 M0 : Nat) : Prop :=
  PowGapLowerBound fun b e _K => (C * (Nat.log2 e + c0) ^ 2 + M0) * (Nat.log2 b + 1)

theorem not_eth_power_of_twoLogHyp {C c0 M0 : Nat} (hC : TwoLogHyp C c0 M0)
    {n b e : Nat} (hn : 7 ≤ n) (hb : 3 ≤ b) (he : n ≤ e)
    (hg : Nat.gcd e (fact (n - 1)) = 1)
    (hsmall : 4 * (C * (Nat.log2 e + c0) ^ 2 + M0) ≤ e) : a n ≠ b ^ e := by
  intro hab
  by_cases hbig : fact (n - 1) + 1 ≤ e
  · exact not_eth_power_of_exp_ge_succ_K hn (by omega : 2 ≤ b) hbig hab
  · have he0 : 0 < e := by omega
    have hq1 : 1 ≤ fact (n - 1) / e :=
      (Nat.le_div_iff_mul_le he0).2 (by omega)
    have hlog :=
      remaining_log2_base_le hn (by omega : 2 ≤ b) (by omega : 1 < e) hg hab
    have hle1 : Nat.log2 b + 1 ≤ fact (n - 1) / e + 1 :=
      Nat.add_le_add_right hlog 1
    let M := C * (Nat.log2 e + c0) ^ 2 + M0
    have h1 : M * (Nat.log2 b + 1) ≤ M * (fact (n - 1) / e + 1) :=
      Nat.mul_le_mul_left M hle1
    have four_mul_eq (x y : Nat) : 4 * x * y = 2 * (2 * x * y) := by
      have hx : 4 * x = 2 * (2 * x) := by
        have : (4 : Nat) = 2 * 2 := rfl
        rw [this]
        exact Nat.mul_assoc 2 2 x
      calc
        4 * x * y = (4 * x) * y := rfl
        _ = (2 * (2 * x)) * y := by rw [hx]
        _ = 2 * ((2 * x) * y) := Nat.mul_assoc 2 (2 * x) y
        _ = 2 * (2 * x * y) := rfl
    have h2M : 2 * M * (fact (n - 1) / e + 1) ≤ fact (n - 1) := by
      have h4 : 4 * M * (fact (n - 1) / e + 1) ≤ e * (fact (n - 1) / e + 1) :=
        Nat.mul_le_mul_right (fact (n - 1) / e + 1) hsmall
      have hqe : e * (fact (n - 1) / e) ≤ fact (n - 1) := by
        rw [Nat.mul_comm]
        exact Nat.div_mul_le_self _ _
      have hsum : e * (fact (n - 1) / e + 1) = e * (fact (n - 1) / e) + e := by
        rw [Nat.mul_add, Nat.mul_one]
      have he_le : e ≤ e * (fact (n - 1) / e) :=
        Nat.le_mul_of_pos_right e hq1
      have h2qe : e * (fact (n - 1) / e + 1) ≤ 2 * (e * (fact (n - 1) / e)) := by
        rw [hsum, Nat.two_mul]
        exact Nat.add_le_add_left he_le _
      have h4le2K : 4 * M * (fact (n - 1) / e + 1) ≤ 2 * fact (n - 1) :=
        Nat.le_trans (Nat.le_trans h4 h2qe) (Nat.mul_le_mul_left 2 hqe)
      have hre := four_mul_eq M (fact (n - 1) / e + 1)
      have hpos2 : (0 : Nat) < 2 := by decide
      have : 2 * (2 * M * (fact (n - 1) / e + 1)) ≤ 2 * fact (n - 1) := by
        rwa [← hre]
      exact Nat.le_of_mul_le_mul_left this hpos2
    have hside : 2 * (M * (Nat.log2 b + 1)) ≤ fact (n - 1) := by
      have h2 : 2 * (M * (Nat.log2 b + 1))
          ≤ 2 * (M * (fact (n - 1) / e + 1)) :=
        Nat.mul_le_mul_left 2 h1
      have hassoc : 2 * (M * (fact (n - 1) / e + 1))
          = 2 * M * (fact (n - 1) / e + 1) :=
        (Nat.mul_assoc 2 M (fact (n - 1) / e + 1)).symm
      calc
        2 * (M * (Nat.log2 b + 1))
            ≤ 2 * (M * (fact (n - 1) / e + 1)) := h2
        _ = 2 * M * (fact (n - 1) / e + 1) := hassoc
        _ ≤ fact (n - 1) := h2M
    exact not_eth_power_of_gap_bound hC hn hb he hg hside hab

/-- 假设（其真假不在本仓库判定）：Lang–Waldschmidt linear-log conjectural shape, not a theorem. -/
def LangWaldschmidtHyp (c1 c2 : Nat) : Prop :=
  PowGapLowerBound fun b e K =>
    c1 * (Nat.log2 b + 1) + c2 * (Nat.log2 e + Nat.log2 K + 1)

theorem not_eth_power_of_langWaldschmidtHyp {c1 c2 : Nat}
    (hC : LangWaldschmidtHyp c1 c2)
    {n b e : Nat} (hn : 7 ≤ n) (hb : 3 ≤ b) (he : n ≤ e)
    (hg : Nat.gcd e (fact (n - 1)) = 1)
    (hsmall :
      c1 * (Nat.log2 b + 1) + c2 * (Nat.log2 e + Nat.log2 (fact (n - 1)) + 1)
        + 3 * fact (n - 2) ≤ fact (n - 1)) :
    a n ≠ b ^ e :=
  not_eth_power_of_gap_bound' hC hn hb he hg hsmall

end LeanA113258
