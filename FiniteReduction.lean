import SequenceCutoff
import LeanA113258.Uniform

namespace LeanA113258

/-- Any nontrivial divisor of an admissible exponent bounds the index below it.
No minimality or primality claim about the divisor is required. -/
theorem index_le_exponent_divisor {n e d : ℕ} (hd : 1 < d) (hde : d ∣ e)
    (hg : Nat.gcd e (fact (n - 1)) = 1) : n ≤ d := by
  by_contra h
  have hdf : d ∣ fact (n - 1) := dvd_fact_of_le (by omega) (by omega)
  have hdiv := Nat.dvd_gcd hde hdf
  rw [hg] at hdiv
  have := Nat.le_of_dvd (by decide : 0 < 1) hdiv
  omega

/-- Exact finite coverage interface; the base is unrestricted apart from `b>1`. -/
def FiniteCutCover : Prop :=
  ∀ n b e : ℕ, 12 ≤ n → n ≤ 2523 → 1 < b → n ≤ e → e < 3500 →
    Nat.gcd e (fact (n - 1)) = 1 →
    9 * e * (n - 4) < 22680 * (n - 1) + 2520 → a n ≠ b ^ e

/-- This closing implication contains no admitted inputs. -/
theorem officialConjecture_false_of_laurent_and_cover
    (hLaurent : LaurentIntegerTwoLogLowerBound) (hCover : FiniteCutCover) :
    ¬ officialConjecture := by
  intro h
  obtain ⟨n, b, e, hn, hb, _h210, he, _h7, hg, hab, _rest⟩ :=
    officialConjecture_iff_remaining_uniform.mp h
  have hb' : 1 < b := by omega
  have he' : 1 < e := by omega
  have hbounds := remaining_finite_from_laurent hLaurent hn hb' he' hg hab
  have hcut := remaining_integer_cut_from_laurent hLaurent hn hb' he' hab
  exact hCover n b e hn hbounds.1 hb' he hbounds.2.2 hg hcut hab

#print axioms index_le_exponent_divisor
#print axioms officialConjecture_false_of_laurent_and_cover

end LeanA113258
