import LaurentCombinatorial
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic

/-!
Finite combinatorics behind the vanishing-order argument in Laurent (2008),
Lemma 4. These theorems do not assert the analytic determinant estimate.
-/

namespace LeanA113258.LaurentCore

open scoped BigOperators

/-- Distinct nonnegative integers have sum at least `0 + ... + (n - 1)`. -/
theorem choose_le_sum_injective_fin {n : ℕ} (f : Fin n → ℕ)
    (hf : Function.Injective f) : n.choose 2 ≤ ∑ i, f i := by
  induction n with
  | zero => simp
  | succ n ih =>
    have hm : ∃ j, n ≤ f j := by
      by_contra h
      have hlt : ∀ j, f j < n := by simpa using h
      let g : Fin (n + 1) → Fin n := fun j => ⟨f j, hlt j⟩
      have hg : Function.Injective g := by
        intro i j hij
        exact hf (congrArg Fin.val hij)
      have hc := Fintype.card_le_of_injective g hg
      simp only [Fintype.card_fin] at hc
      omega
    obtain ⟨j, hj⟩ := hm
    have hrest := ih (fun i => f (j.succAbove i))
      (hf.comp Fin.succAbove_right_injective)
    rw [Fin.sum_univ_succAbove f j, Nat.choose_succ_succ, Nat.choose_one_right]
    exact Nat.add_le_add hj hrest

theorem choose_card_le_sum_injective {ι : Type*} [Fintype ι]
    (f : ι → ℕ) (hf : Function.Injective f) :
    (Fintype.card ι).choose 2 ≤ ∑ i, f i := by
  let e : Fin (Fintype.card ι) ≃ ι := (Fintype.equivFin ι).symm
  have h := choose_le_sum_injective_fin (fun i => f (e i)) (hf.comp e.injective)
  simpa only [Equiv.sum_comp] using h

/-- A nonzero monomial determinant cannot repeat its exponent pair in two rows. -/
theorem monomial_det_labels_injective {ι R : Type*} [Fintype ι] [DecidableEq ι]
    [CommRing R] (c h : ι → ℕ) (z s : ι → R)
    (hdet : (Matrix.of fun i j => z j ^ h i * s j ^ c i).det ≠ 0) :
    Function.Injective (fun i => (c i, h i)) := by
  intro i j heq
  by_contra hij
  apply hdet
  apply Matrix.det_zero_of_row_eq hij
  funext k
  have hc := congrArg Prod.fst heq
  have hh := congrArg Prod.snd heq
  change c i = c j at hc
  change h i = h j at hh
  change z k ^ h i * s k ^ c i = z k ^ h j * s k ^ c j
  rw [hc, hh]

/-- Row coefficients do not affect the necessary distinctness of exponent pairs. -/
theorem scaled_monomial_det_labels_injective {ι R : Type*}
    [Fintype ι] [DecidableEq ι] [CommRing R] (c h : ι → ℕ) (z s a : ι → R)
    (hdet : (Matrix.of fun i j => a i * (z j ^ h i * s j ^ c i)).det ≠ 0) :
    Function.Injective (fun i => (c i, h i)) := by
  apply monomial_det_labels_injective c h z s
  intro hz
  apply hdet
  exact (Matrix.det_mul_column a (Matrix.of fun i j => z j ^ h i * s j ^ c i)).trans
    (by rw [hz, mul_zero])

/-- Counting distinct exponent pairs gives the weighted degree used by the
interpolation determinant estimate. No series or analytic assumptions occur here. -/
theorem weighted_degree_of_injective_pairs {ι : Type*} [Fintype ι]
    {ℓ : ℕ} (c : ι → Fin ℓ) (h : ι → ℕ)
    (hinj : Function.Injective (fun i => (c i, h i)))
    {μ : ℝ} (hμ : (1 / 3 : ℝ) ≤ μ) :
    (((1 + 2 * μ - μ ^ 2) / 2) * (Fintype.card ι : ℝ) ^ 2 -
        (Fintype.card ι : ℝ)) / 2 ≤
      (∑ i, (h i : ℝ)) + μ * (Fintype.card ι : ℝ) * ∑ i, ((c i).val : ℝ) := by
  classical
  let ν : Fin ℓ → ℕ := fun k => Fintype.card {i // c i = k}
  have htotal : ∑ k, ν k = Fintype.card ι := by
    simpa [ν] using Fintype.sum_fiberwise c (fun _ => (1 : ℕ))
  have hchoose : ∑ k, (ν k).choose 2 ≤ ∑ i, h i := by
    calc
      (∑ k, (ν k).choose 2) ≤ ∑ k, ∑ i : {i // c i = k}, h i := by
        apply Finset.sum_le_sum
        intro k _
        apply choose_card_le_sum_injective
        intro i j heq
        apply Subtype.ext
        apply hinj
        exact Prod.ext (i.property.trans j.property.symm) heq
      _ = ∑ i, h i := Fintype.sum_fiberwise c h
  have hw : ∑ k, (k.val : ℝ) * (ν k : ℝ) = ∑ i, ((c i).val : ℝ) := by
    simpa [ν, mul_comm] using Fintype.sum_fiberwise' c (fun k => (k.val : ℝ))
  have hL := laurent_lemma_three ν htotal hμ
  rw [hw] at hL
  have hchooseR : (∑ k, ((ν k).choose 2 : ℝ)) ≤ ∑ i, (h i : ℝ) := by
    exact_mod_cast hchoose
  linarith

#print axioms choose_card_le_sum_injective
#print axioms scaled_monomial_det_labels_injective
#print axioms weighted_degree_of_injective_pairs

end LeanA113258.LaurentCore
