import FactorCoverBatch001
import FactorCoverBatch002
import FactorCoverBatch003
import FactorCoverBatch004
import FactorCoverBatch005
import FactorCoverBatch006
import FactorCoverBatch007
import FactorCoverBatch008
import FactorCoverBatch009
import FactorCoverBatch010

namespace LeanA113258

/-- All generated `(n,p,a(n) mod p^2)` factor certificates. -/
def factorCoverRows : List (Nat × Nat × Nat) :=
  FactorCoverBatch001Rows ++
  FactorCoverBatch002Rows ++
  FactorCoverBatch003Rows ++
  FactorCoverBatch004Rows ++
  FactorCoverBatch005Rows ++
  FactorCoverBatch006Rows ++
  FactorCoverBatch007Rows ++
  FactorCoverBatch008Rows ++
  FactorCoverBatch009Rows ++
  FactorCoverBatch010Rows

/-- n-values with generated valuation-one certificates. -/
def factorCoverCertifiedN : List Nat := factorCoverRows.map Prod.fst

theorem factorCoverRowsChecked : factorCoverRows.all factorCoverCheck = true := by
  simp [factorCoverRows, FactorCoverBatch001Checked, FactorCoverBatch002Checked, FactorCoverBatch003Checked, FactorCoverBatch004Checked, FactorCoverBatch005Checked, FactorCoverBatch006Checked, FactorCoverBatch007Checked, FactorCoverBatch008Checked, FactorCoverBatch009Checked, FactorCoverBatch010Checked]

theorem factorCoverCheck_of_mem {rows : List (Nat × Nat × Nat)}
    (hall : rows.all factorCoverCheck = true) {row : Nat × Nat × Nat}
    (hrow : row ∈ rows) : factorCoverCheck row = true := by
  induction rows with
  | nil => simp at hrow
  | cons head tail ih =>
    simp only [List.all_cons, Bool.and_eq_true] at hall
    rcases List.mem_cons.mp hrow with heq | hmem
    · simpa [heq] using hall.1
    · exact ih hall.2 hmem

theorem factorCoverAllSound {n : Nat} (hn : n ∈ factorCoverCertifiedN) :
    ¬ IsPerfectPower (a n) := by
  rcases List.mem_map.mp hn with ⟨row, hrow, heq⟩
  rw [← heq]
  exact factorCoverCheck_sound (factorCoverCheck_of_mem factorCoverRowsChecked hrow)

end LeanA113258
