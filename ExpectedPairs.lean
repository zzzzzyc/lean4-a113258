import FiniteReduction
import FactorCover

namespace LeanA113258

/-- Indices requiring an exponent certificate after the proved elementary filters. -/
def expectedIndices (e : ℕ) : List ℕ :=
  (List.range (min 2524 (e.minFac + 1))).filter (fun n =>
    decide (12 ≤ n ∧ n ≤ e ∧ 9 * e * (n - 4) < 22680 * (n - 1) + 2520 ∧
      n ∉ factorCoverCertifiedN))

/-- The complete residual domain, in exponent/index order. -/
def expectedPairs : List (ℕ × ℕ) :=
  (List.range 3500).flatMap (fun e => (expectedIndices e).map (fun n => (n, e)))

/-- Every remaining hypothetical power occurs in the enumerated domain.
This is a symbolic proof; it does not rely on an unchecked enumeration. -/
theorem expectedPairs_mem {n e : ℕ}
    (hn : 12 ≤ n) (hnmax : n ≤ 2523) (hne : n ≤ e) (he : e < 3500)
    (hg : Nat.gcd e (fact (n - 1)) = 1)
    (hcut : 9 * e * (n - 4) < 22680 * (n - 1) + 2520)
    (hnot : n ∉ factorCoverCertifiedN) : (n, e) ∈ expectedPairs := by
  have hmf : n ≤ e.minFac := index_le_exponent_divisor
    (Nat.minFac_prime (by omega : e ≠ 1)).one_lt (Nat.minFac_dvd e) hg
  have hnrange : n < min 2524 (e.minFac + 1) := by omega
  have hmem : n ∈ expectedIndices e := by
    apply List.mem_filter.mpr
    exact ⟨List.mem_range.mpr hnrange, by simp only [decide_eq_true_eq]; exact ⟨hn, hne, hcut, hnot⟩⟩
  apply List.mem_flatMap.mpr
  refine ⟨e, List.mem_range.mpr he, ?_⟩
  exact List.mem_map.mpr ⟨n, hmem, rfl⟩

#print axioms expectedPairs_mem

end LeanA113258
