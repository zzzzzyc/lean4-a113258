import LaurentLayers

/-! The sharp rectangular-grid correlation estimate used on both sides of the
interpolation determinant comparison. -/

namespace LeanA113258.LaurentCore

open scoped BigOperators

theorem grid_layer_difference {K L R S : ℕ}
    (r : Fin K × Fin L → Fin R) (s : Fin K × Fin L → Fin S)
    (hinj : Function.Injective (fun i => (r i, s i)))
    (t : ℕ → ℝ) (ht : ∀ l : Fin L, t l.val = ∑ k, ((r (k, l)).val : ℝ))
    (j : ℕ) (hj : j ≤ L) :
    (S : ℝ) * (∑ q ∈ Finset.range j, (t (L - 1 - q) - t q)) ≤
      S * R * K * j - (K : ℝ) ^ 2 * (j : ℝ) ^ 2 := by
  let f₁ : Fin K × Fin j → Fin K × Fin L := fun i => (i.1, (Fin.castLE hj i.2).rev)
  let f₂ : Fin K × Fin j → Fin K × Fin L := fun i => (i.1, Fin.castLE hj i.2)
  have hf₁ : Function.Injective f₁ := by
    intro i i' he
    apply Prod.ext
    · exact congrArg (fun p : Fin K × Fin L => p.1) he
    · apply Fin.ext
      have he' : (Fin.castLE hj i.2).rev = (Fin.castLE hj i'.2).rev := congrArg Prod.snd he
      have he'' := @Fin.rev_injective L _ _ he'
      exact congrArg (fun q : Fin L => q.val) he''
  have hf₂ : Function.Injective f₂ := by
    intro i i' he
    apply Prod.ext
    · exact congrArg (fun p : Fin K × Fin L => p.1) he
    · exact Fin.ext (congrArg (fun p => p.2.val) he)
  have hh := grid_coordinate_difference (r ∘ f₁) (r ∘ f₂) (s ∘ f₁) (s ∘ f₂)
    (hinj.comp hf₁) (hinj.comp hf₂)
  have htop : (∑ i : Fin K × Fin j, ((r (f₁ i)).val : ℝ)) =
      ∑ q ∈ Finset.range j, t (L - 1 - q) := by
    rw [Fintype.sum_prod_type, Finset.sum_comm,
      ← Fin.sum_univ_eq_sum_range (fun q => t (L - 1 - q)) j]
    apply Finset.sum_congr rfl
    intro q _
    simpa only [f₁, Fin.val_rev, Fin.val_castLE, Nat.sub_sub, Nat.add_comm]
      using (ht (Fin.castLE hj q).rev).symm
  have hbot : (∑ i : Fin K × Fin j, ((r (f₂ i)).val : ℝ)) =
      ∑ q ∈ Finset.range j, t q := by
    rw [Fintype.sum_prod_type, Finset.sum_comm,
      ← Fin.sum_univ_eq_sum_range t j]
    apply Finset.sum_congr rfl
    intro q _
    exact (ht (Fin.castLE hj q)).symm
  simp only [Function.comp_apply, htop, hbot, Fintype.card_prod, Fintype.card_fin,
    Nat.cast_mul] at hh
  rw [Finset.sum_sub_distrib]
  nlinarith [hh]

theorem sharp_grid_correlation_le {K L R S : ℕ}
    (r : Fin K × Fin L → Fin R) (s : Fin K × Fin L → Fin S)
    (hinj : Function.Injective (fun i => (r i, s i))) :
    (S : ℝ) * (∑ i : Fin K × Fin L,
      ((i.2.val : ℝ) - ((L : ℝ) - 1) / 2) * (r i).val) ≤
      S * R * K * (L : ℝ) ^ 2 / 8 - (K : ℝ) ^ 2 * (L : ℝ) ^ 3 / 24 := by
  classical
  let t : ℕ → ℝ := fun l => if hl : l < L then ∑ k, ((r (k, ⟨l, hl⟩)).val : ℝ) else 0
  have ht (l : Fin L) : t l.val = ∑ k, ((r (k, l)).val : ℝ) := by
    simp only [t, dif_pos l.isLt]
  have hcard : (K : ℝ) * L ≤ (R : ℝ) * S := by
    have hh := Fintype.card_le_of_injective _ hinj
    simp only [Fintype.card_prod, Fintype.card_fin] at hh
    exact_mod_cast hh
  have hsum : (∑ i : Fin K × Fin L,
        ((i.2.val : ℝ) - ((L : ℝ) - 1) / 2) * (r i).val) =
      ∑ l ∈ Finset.range L, ((l : ℝ) - ((L : ℝ) - 1) / 2) * t l := by
    rw [Fintype.sum_prod_type, Finset.sum_comm,
      ← Fin.sum_univ_eq_sum_range (fun l => ((l : ℝ) - ((L : ℝ) - 1) / 2) * t l) L]
    apply Finset.sum_congr rfl
    intro l _
    rw [ht, Finset.mul_sum]
  rw [hsum]
  have hp := grid_layer_difference r s hinj t ht
  have hpar : L = 2 * (L / 2) ∨ L = 2 * (L / 2) + 1 := by omega
  rcases hpar with he | ho
  · have hh := centered_sum_bound_even t (L / 2) (A := (S : ℝ) * R * K)
      (B := (K : ℝ) ^ 2) (S := (S : ℝ)) (sq_nonneg _) (fun j hj => by
        have h := hp j (by omega)
        rw [he] at h
        exact h)
    rw [he]
    convert hh using 1
    push_cast
    ring
  · have hab : (K : ℝ) ^ 2 * (2 * (L / 2 : ℕ) + 1) ≤ (S : ℝ) * R * K := by
      have hh := mul_le_mul_of_nonneg_left hcard (Nat.cast_nonneg K : (0 : ℝ) ≤ K)
      have he' : (L : ℝ) = 2 * (L / 2 : ℕ) + 1 := by exact_mod_cast ho
      nlinarith [hh]
    have hh := centered_sum_bound_odd t (L / 2) (A := (S : ℝ) * R * K)
      (B := (K : ℝ) ^ 2) (S := (S : ℝ)) (sq_nonneg _) hab (fun j hj => by
        have h := hp j (by omega)
        rw [ho] at h
        simpa only [Nat.add_sub_cancel] using h)
    rw [ho]
    push_cast
    have hc : ((2 * (L / 2 : ℕ) + 1 : ℝ) - 1) / 2 = (L / 2 : ℕ) := by ring
    rw [hc]
    exact hh

theorem sum_centered_second_index_real (K L : ℕ) :
    (∑ i : Fin K × Fin L, ((i.2.val : ℝ) - ((L : ℝ) - 1) / 2)) = 0 := by
  have hs (n : ℕ) : (∑ l : Fin n, (l.val : ℝ)) = (n : ℝ) * (n - 1) / 2 := by
    induction n with
    | zero => simp
    | succ n ih =>
      rw [Fin.sum_univ_castSucc]
      simp only [Fin.val_castSucc, Fin.val_last, ih, Nat.cast_add, Nat.cast_one]
      ring
  rw [Fintype.sum_prod_type]
  have hh : (∑ i : Fin L, ((i.val : ℝ) - ((L : ℝ) - 1) / 2)) = 0 := by
    rw [Finset.sum_sub_distrib, hs]
    simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    ring
  simp only [hh, Finset.sum_const_zero]

theorem sharp_grid_correlation_abs {K L R S : ℕ}
    (r : Fin K × Fin L → Fin R) (s : Fin K × Fin L → Fin S)
    (hinj : Function.Injective (fun i => (r i, s i))) :
    (S : ℝ) * |∑ i : Fin K × Fin L,
      ((i.2.val : ℝ) - ((L : ℝ) - 1) / 2) * (r i).val| ≤
      S * R * K * (L : ℝ) ^ 2 / 8 - (K : ℝ) ^ 2 * (L : ℝ) ^ 3 / 24 := by
  have hpos := sharp_grid_correlation_le r s hinj
  have hrev : Function.Injective (fun i => ((r i).rev, s i)) := by
    intro i j he
    apply hinj
    simpa only [Fin.rev_rev] using congrArg (fun p : Fin R × Fin S => (p.1.rev, p.2)) he
  have hneg := sharp_grid_correlation_le (fun i => (r i).rev) s hrev
  have hv (i : Fin K × Fin L) : (((r i).rev).val : ℝ) = (R : ℝ) - 1 - (r i).val := by
    have hh : (r i).rev.val + 1 + (r i).val = R := by
      simp only [Fin.val_rev]
      omega
    have hh' : (((r i).rev).val : ℝ) + 1 + (r i).val = (R : ℝ) := by exact_mod_cast hh
    linarith
  have he : (∑ i : Fin K × Fin L,
      ((i.2.val : ℝ) - ((L : ℝ) - 1) / 2) * ((r i).rev).val) =
      -(∑ i : Fin K × Fin L, ((i.2.val : ℝ) - ((L : ℝ) - 1) / 2) * (r i).val) := by
    calc
      _ = ∑ i : Fin K × Fin L, (((i.2.val : ℝ) - ((L : ℝ) - 1) / 2) * (R - 1) -
          ((i.2.val : ℝ) - ((L : ℝ) - 1) / 2) * (r i).val) := by
        apply Finset.sum_congr rfl
        intro i _
        rw [hv]
        ring
      _ = _ := by
        rw [Finset.sum_sub_distrib, ← Finset.sum_mul, sum_centered_second_index_real]
        ring
  rw [he, mul_neg] at hneg
  have hh := abs_le.mpr ⟨neg_le.mp hneg, hpos⟩
  simpa only [abs_mul, abs_of_nonneg (Nat.cast_nonneg S : (0 : ℝ) ≤ S)] using hh

theorem laurent_grid_correlation {K L R S : ℕ} (hR : 0 < R) (hS : 0 < S)
    (r : Fin K × Fin L → Fin R) (s : Fin K × Fin L → Fin S)
    (hinj : Function.Injective (fun i => (r i, s i))) :
    |∑ i : Fin K × Fin L, ((i.2.val : ℝ) - ((L : ℝ) - 1) / 2) * (r i).val| ≤
      (1 / 4 - (K : ℝ) * L / (12 * R * S)) * L * R * (K * L) / 2 := by
  have hR' : (R : ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hR)
  have hS' : (S : ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hS)
  have he : (S : ℝ) * ((1 / 4 - (K : ℝ) * L / (12 * R * S)) * L * R * (K * L) / 2) =
      S * R * K * (L : ℝ) ^ 2 / 8 - (K : ℝ) ^ 2 * (L : ℝ) ^ 3 / 24 := by
    field_simp
    ring
  apply (mul_le_mul_iff_right₀ (by exact_mod_cast hS : (0 : ℝ) < S)).mp
  rw [he]
  exact sharp_grid_correlation_abs r s hinj

end LeanA113258.LaurentCore
