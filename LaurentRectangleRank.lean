import LaurentBinomialRank
import LaurentIntegerDeterminant

/-! The nonzero integer minor on a sum of two rectangular grids. -/

namespace LeanA113258.LaurentCore

open scoped BigOperators

theorem exists_nonzero_integer_rectangle_minor {K L R₁ R₂ S₁ S₂ : ℕ}
    (a b u v : ℕ) (ha : 0 < a) (hb : 0 < b)
    (hcard₁ : L ≤ R₁ * S₁) (hcard₂ : (K - 1) * L < R₂ * S₂)
    (hy₁ : Function.Injective (fun i : Fin R₁ × Fin S₁ => a ^ i.1.val * b ^ i.2.val))
    (hx₂ : Function.Injective (fun i : Fin R₂ × Fin S₂ => i.1.val * u + i.2.val * v)) :
    ∃ r : Fin K × Fin L → Fin (R₁ + R₂ - 1),
      ∃ s : Fin K × Fin L → Fin (S₁ + S₂ - 1),
        Function.Injective (fun i => (r i, s i)) ∧
          (binomialIntegerMatrix (fun i : Fin K × Fin L => i.1.val) (fun i => i.2.val)
            (fun i => (r i).val) (fun i => (s i).val) a b u v).det ≠ 0 := by
  classical
  let Γ := Fin (R₁ + R₂ - 1) × Fin (S₁ + S₂ - 1)
  let Γ₁ := Fin R₁ × Fin S₁
  let Γ₂ := Fin R₂ × Fin S₂
  let e₁ : Fin L ↪ Γ₁ := Classical.choice (Function.Embedding.nonempty_of_card_le (by
    simpa only [Γ₁, Fintype.card_fin, Fintype.card_prod] using hcard₁))
  let x : Γ → ℕ := fun j => j.1.val * u + j.2.val * v
  let y : Γ → ℚ := fun j => (a : ℚ) ^ j.1.val * (b : ℚ) ^ j.2.val
  let x₁ : Fin L → ℚ := fun i => ((e₁ i).1.val * u + (e₁ i).2.val * v : ℕ)
  let y₁ : Fin L → ℚ := fun i => (a : ℚ) ^ (e₁ i).1.val * (b : ℚ) ^ (e₁ i).2.val
  let x₂ : Γ₂ → ℚ := fun j => (j.1.val * u + j.2.val * v : ℕ)
  let y₂ : Γ₂ → ℚ := fun j => (a : ℚ) ^ j.1.val * (b : ℚ) ^ j.2.val
  let e : Fin L → Γ₂ → Γ := fun i j =>
    (⟨(e₁ i).1.val + j.1.val, by have := (e₁ i).1.isLt; have := j.1.isLt; omega⟩,
     ⟨(e₁ i).2.val + j.2.val, by have := (e₁ i).2.isLt; have := j.2.isLt; omega⟩)
  have hxe (i j) : (x (e i j) : ℚ) = x₁ i + x₂ j := by
    dsimp [x, e, x₁, x₂]
    push_cast
    ring
  have hye (i j) : y (e i j) = y₁ i * y₂ j := by
    dsimp [y, e, y₁, y₂]
    rw [pow_add, pow_add]
    ring
  have hyi : Function.Injective y₁ := by
    intro i j he
    apply e₁.injective
    apply hy₁
    dsimp [y₁] at he
    exact_mod_cast he
  have hxi : Function.Injective x₂ := by
    intro i j he
    apply hx₂
    dsimp [x₂] at he
    exact_mod_cast he
  have hyz (j) : y₂ j ≠ 0 := by
    dsimp [y₂]
    exact mul_ne_zero (pow_ne_zero _ (by exact_mod_cast (Nat.ne_of_gt ha)))
      (pow_ne_zero _ (by exact_mod_cast (Nat.ne_of_gt hb)))
  obtain ⟨f, hf, hd⟩ := exists_nonzero_binomial_interpolation_minor x y x₁ y₁ x₂ y₂ e
    hxe hye hyi hxi hyz (by simpa only [Γ₂, Fintype.card_prod, Fintype.card_fin] using hcard₂)
  refine ⟨fun i => (f i).1, fun i => (f i).2, hf, ?_⟩
  let D := binomialIntegerMatrix (fun i : Fin K × Fin L => i.1.val) (fun i => i.2.val)
    (fun i => (f i).1.val) (fun i => (f i).2.val) a b u v
  have he : (D.det : ℚ) = (Matrix.of fun i j : Fin K × Fin L =>
      ((x (f j)).choose i.1.val : ℚ) * y (f j) ^ i.2.val).det := by
    have hm := (Int.castRingHom ℚ).map_det D
    change (D.det : ℚ) = (D.map (fun n : ℤ => (n : ℚ))).det at hm
    rw [hm]
    congr 1
    ext i j
    simp only [D, binomialIntegerMatrix, Matrix.map_apply, Matrix.of_apply,
      Int.cast_mul, Int.cast_pow, Int.cast_natCast, x, y, mul_pow, pow_mul]
    ring
  intro hz
  apply hd
  rw [← he]
  change D.det = 0 at hz
  rw [hz, Int.cast_zero]

end LeanA113258.LaurentCore
