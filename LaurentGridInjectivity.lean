import LaurentRectangleRank
import Mathlib.Data.Nat.Factorization.Basic

/-! Multiplicative grid injectivity and the elementary noncollision case for
additive coordinates. -/

namespace LeanA113258.LaurentCore

theorem prime_power_product_injective {p b : ℕ} (hp : p.Prime) (hb : 1 < b)
    (hpb : ¬p ∣ b) : Function.Injective (fun i : ℕ × ℕ => p ^ i.1 * b ^ i.2) := by
  have hp₀ : p ≠ 0 := hp.ne_zero
  have hb₀ : b ≠ 0 := by omega
  have hf (r s : ℕ) : (p ^ r * b ^ s).factorization p = r := by
    rw [Nat.factorization_mul (pow_ne_zero _ hp₀) (pow_ne_zero _ hb₀), Finsupp.add_apply,
      Nat.factorization_pow_self hp, Nat.factorization_pow]
    simp only [Finsupp.smul_apply, smul_eq_mul, Nat.factorization_eq_zero_of_not_dvd hpb,
      mul_zero, add_zero]
  intro i j he
  have hr : i.1 = j.1 := by
    have hh := congrArg (fun n : ℕ => n.factorization p) he
    simpa only [hf] using hh
  have hs : b ^ i.2 = b ^ j.2 := Nat.eq_of_mul_eq_mul_left (pow_pos hp.pos _)
    (by simpa only [hr] using he)
  exact Prod.ext hr (pow_right_injective₀ (by omega : 0 < b) (by omega : b ≠ 1) hs)

theorem prime_power_rectangle_injective {p b R S : ℕ} (hp : p.Prime) (hb : 1 < b)
    (hpb : ¬p ∣ b) :
    Function.Injective (fun i : Fin R × Fin S => p ^ i.1.val * b ^ i.2.val) := by
  intro i j he
  have hh := prime_power_product_injective hp hb hpb (a₁ := (i.1.val, i.2.val))
    (a₂ := (j.1.val, j.2.val)) he
  exact Prod.ext (Fin.ext (congrArg Prod.fst hh)) (Fin.ext (congrArg Prod.snd hh))

theorem additive_rectangle_injective_of_small_width {R S u v : ℕ}
    (hcop : u.Coprime v) (hR : R ≤ v) :
    Function.Injective (fun i : Fin R × Fin S => i.1.val * u + i.2.val * v) := by
  intro i j he
  have hrmod : i.1.val * u % v = j.1.val * u % v := by
    have hh := congrArg (fun n => n % v) he
    simpa only [Nat.add_mul_mod_self_right] using hh
  have hr : i.1.val = j.1.val := by
    have hi : i.1.val < v := lt_of_lt_of_le i.1.isLt hR
    have hj : j.1.val < v := lt_of_lt_of_le j.1.isLt hR
    have hh := Nat.ModEq.cancel_right_of_coprime hcop.symm hrmod
    simpa only [Nat.ModEq, Nat.mod_eq_of_lt hi, Nat.mod_eq_of_lt hj] using hh
  have hs : i.2.val = j.2.val := by
    have hv : 0 < v := lt_of_le_of_lt (Nat.zero_le _) (lt_of_lt_of_le i.1.isLt hR)
    exact Nat.eq_of_mul_eq_mul_right hv (Nat.add_left_cancel (by simpa only [hr] using he))
  exact Prod.ext (Fin.ext hr) (Fin.ext hs)

end LeanA113258.LaurentCore
