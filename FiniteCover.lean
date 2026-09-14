import FiniteReduction
import ExpectedPairs
import FactorCover
import ModularCover

namespace LeanA113258.CoverChecker

open LeanA113258

set_option maxRecDepth 100000
set_option maxHeartbeats 8000000

/-- The generated row-key sequence is exactly the symbolic candidate domain. -/
theorem modularCoverKeys_eq_expected :
    modularCoverRows.map (fun r => (r.n, r.e)) = expectedPairs := by
  native_decide

/-- Every admissible uncovered pair has a modular certificate row. -/
theorem modularCover_covers {n e : Nat}
    (hn : 12 ≤ n) (hnmax : n ≤ 2523) (hne : n ≤ e) (he : e < 3500)
    (hg : Nat.gcd e (fact (n - 1)) = 1)
    (hcut : 9 * e * (n - 4) < 22680 * (n - 1) + 2520)
    (hnot : n ∉ factorCoverCertifiedN) :
    ∃ r, r ∈ modularCoverRows ∧ r.n = n ∧ r.e = e := by
  have hpair : (n, e) ∈ expectedPairs :=
    expectedPairs_mem hn hnmax hne he hg hcut hnot
  rw [← modularCoverKeys_eq_expected] at hpair
  obtain ⟨r, hr, heq⟩ := List.mem_map.mp hpair
  exact ⟨r, hr, congrArg Prod.fst heq, congrArg Prod.snd heq⟩

/-- Close the finite range from factor certificates and modular rows. -/
theorem finite_cut_cover : FiniteCutCover := by
  intro n b e hn hnmax hb hne he hg hcut hab
  by_cases hfactor : n ∈ factorCoverCertifiedN
  · have hpp : IsPerfectPower (a n) := ⟨b, e, hb, by omega, hab⟩
    exact (factorCoverAllSound hfactor hpp).elim
  · obtain ⟨r, hr, hrn, hre⟩ :=
      modularCover_covers hn hnmax hne he hg hcut hfactor
    have hrow := modularCoverAllSound hr b
    rw [hrn, hre] at hrow
    exact hrow hab

#print axioms modularCoverKeys_eq_expected
#print axioms finite_cut_cover

end LeanA113258.CoverChecker
