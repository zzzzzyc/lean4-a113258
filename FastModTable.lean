import FastMod

namespace LeanA113258

/-! Linear-time prefix tables for factorial residues. -/

/-- One incremental factorial-residue update. -/
def factModStep (m acc k : Nat) : Nat := acc * ((k + 1) % m) % m

theorem foldl_factMod_range (n m : Nat) :
    List.foldl (factModStep m) (1 % m) (List.range n) = factMod n m := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [List.range_succ, List.foldl_append]
    simp [factModStep, factMod, ih]

/-- The table entry at index `k` is `k! mod m`, for `0 ≤ k ≤ n`. -/
def factModTable (n m : Nat) : Array Nat :=
  (List.scanl (factModStep m) (1 % m) (List.range n)).toArray

theorem factModTable_size (n m : Nat) : (factModTable n m).size = n + 1 := by
  simp [factModTable]

theorem factModTable_get {n m k : Nat} (hk : k ≤ n) :
    (factModTable n m)[k]'(by rw [factModTable_size]; omega) = fact k % m := by
  unfold factModTable
  have hscan :
      k < (List.scanl (factModStep m) (1 % m) (List.range n)).length := by
    simp only [List.length_scanl, List.length_range]
    omega
  have harray :
      k < (List.scanl (factModStep m) (1 % m) (List.range n)).toArray.size := by
    simpa only [List.size_toArray] using hscan
  rw [List.getElem_toArray harray, List.getElem_scanl hscan,
    List.take_range, Nat.min_eq_left hk, foldl_factMod_range, factMod_eq]

theorem factModTable_getBang {n m k : Nat} (hk : k ≤ n) :
    (factModTable n m)[k]! = fact k % m := by
  have hbound : k < (factModTable n m).size := by
    rw [factModTable_size]
    omega
  rw [getElem!_pos (factModTable n m) k hbound]
  exact factModTable_get hk

/-- Table-based summand evaluation, with the tables shared by all terms. -/
def aModPrimeTableAux (n p : Nat) (baseTable expTable : Array Nat) : Nat :=
  sumRange n (fun i =>
    powModResidue (baseTable[i + 1]!) (expTable[n - i]!) p) % p

theorem sumRange_congr {n : Nat} {f g : Nat → Nat}
    (h : ∀ i, i < n → f i = g i) : sumRange n f = sumRange n g := by
  induction n with
  | zero => rfl
  | succ n ih =>
    have hprefix : sumRange n f = sumRange n g :=
      ih (fun i hi => h i (Nat.lt_succ_of_lt hi))
    rw [sumRange_succ, sumRange_succ, hprefix, h n (Nat.lt_succ_self n)]

theorem aModPrimeTableAux_eq {n p : Nat}
    (hp : 1 < p) (hc : primeCert p)
    {baseTable expTable : Array Nat}
    (hbase : ∀ k, k ≤ n → baseTable[k]! = fact k % p)
    (hexp : ∀ k, k ≤ n → expTable[k]! = fact k % (p - 1)) :
    aModPrimeTableAux n p baseTable expTable = a n % p := by
  have hterms : ∀ i, i < n →
      powModResidue (baseTable[i + 1]!) (expTable[n - i]!) p =
        (fact (i + 1) ^ fact (n - i)) % p := by
    intro i hi
    have hbasei : baseTable[i + 1]! = fact (i + 1) % p :=
      hbase (i + 1) (by omega)
    have hexpi : expTable[n - i]! = fact (n - i) % (p - 1) :=
      hexp (n - i) (Nat.sub_le _ _)
    rw [hbasei, hexpi]
    exact powModResidue_eq hp hc (fact_pos (n - i))
  calc
    aModPrimeTableAux n p baseTable expTable =
        sumRange n (fun i =>
          powModResidue (baseTable[i + 1]!) (expTable[n - i]!) p) % p := rfl
    _ = sumRange n (fun i => (fact (i + 1) ^ fact (n - i)) % p) % p := by
      rw [sumRange_congr hterms]
    _ = sumRange n (fun i => fact (i + 1) ^ fact (n - i)) % p :=
      sumRange_mod_terms n p _
    _ = a n % p := rfl

/-- `a(n) mod p`, computed from two O(n) factorial tables. -/
def aModPrimeTable (n p : Nat) : Nat :=
  let baseTable := factModTable n p
  let expTable := factModTable n (p - 1)
  aModPrimeTableAux n p baseTable expTable

theorem aModPrimeTable_eq {n p : Nat}
    (hp : 1 < p) (hc : primeCert p) :
    aModPrimeTable n p = a n % p := by
  unfold aModPrimeTable
  apply aModPrimeTableAux_eq hp hc
  · intro k hk
    exact factModTable_getBang hk
  · intro k hk
    exact factModTable_getBang hk

theorem aModPrimeTable_eq_reduced {n p : Nat}
    (hp : 1 < p) (hc : primeCert p) :
    aModPrimeTable n p = aModPrimeReduced n p := by
  rw [aModPrimeTable_eq hp hc, aModPrimeReduced_eq hp hc]

/-! A kernel-friendly table evaluator. Unlike `Array.get!`, the list streams
are consumed once from left to right, so reduction does not repeatedly scan
the backing list for each table lookup. -/

/-- The factorial residues `0!, 1!, ..., n!` modulo `m`, produced in one pass. -/
def factModStream (n m : Nat) : List Nat :=
  List.scanl (factModStep m) (1 % m) (List.range n)

theorem factModStream_size (n m : Nat) : (factModStream n m).length = n + 1 := by
  simp [factModStream]

theorem factModStream_get {n m k : Nat} (hk : k ≤ n) :
    (factModStream n m)[k]'(by rw [factModStream_size]; omega) = fact k % m := by
  unfold factModStream
  have hscan : k < (List.scanl (factModStep m) (1 % m) (List.range n)).length := by
    simp only [List.length_scanl, List.length_range]
    omega
  rw [List.getElem_scanl hscan, List.take_range, Nat.min_eq_left hk,
    foldl_factMod_range, factMod_eq]

theorem factModStream_tail_size (n m : Nat) :
    ((factModStream n m).drop 1).length = n := by
  rw [List.length_drop, factModStream_size]
  omega

theorem factModStream_base_get {n m i : Nat} (hi : i < n) :
    ((factModStream n m).drop 1)[i]'(by rw [factModStream_tail_size]; exact hi) =
      fact (i + 1) % m := by
  rw [List.getElem_drop]
  have hidx : 1 + i = i + 1 := by omega
  simpa only [hidx] using factModStream_get (n := n) (m := m) (k := i + 1) (by omega)

theorem factModStream_exp_get {n m i : Nat} (hi : i < n) :
    (((factModStream n m).drop 1).reverse)[i]'
      (by rw [List.length_reverse, factModStream_tail_size]; exact hi) =
      fact (n - i) % m := by
  have hlen : ((factModStream n m).drop 1).length = n := factModStream_tail_size n m
  have hrev := List.getElem_reverse (l := (factModStream n m).drop 1) (i := i)
    (by rw [List.length_reverse, hlen]; exact hi)
  have hrev' : (((factModStream n m).drop 1).reverse)[i]'
      (by rw [List.length_reverse, hlen]; exact hi) =
      ((factModStream n m).drop 1)[n - 1 - i]'(by rw [hlen]; omega) := by
    simpa only [hlen] using hrev
  rw [hrev', List.getElem_drop]
  have hidx : 1 + (n - 1 - i) = n - i := by omega
  simpa only [hidx] using factModStream_get (n := n) (m := m) (k := n - i) (by omega)

theorem factModStream_zip_terms {n p : Nat} :
    List.zipWith (fun b e => powModResidue b e p)
      ((factModStream n p).drop 1)
      (((factModStream n (p - 1)).drop 1).reverse) =
    List.map (fun i => powModResidue (fact (i + 1) % p) (fact (n - i) % (p - 1)) p)
      (List.range n) := by
  apply List.ext_getElem
  · simp only [List.length_zipWith, List.length_reverse, factModStream_tail_size,
      Nat.min_self, List.length_map, List.length_range]
  · intro i hi1 hi2
    rw [List.getElem_zipWith, List.getElem_map, List.getElem_range]
    have hi : i < n := by
      simpa only [List.length_zipWith, List.length_reverse, factModStream_tail_size,
        Nat.min_self] using hi1
    rw [factModStream_base_get (n := n) (m := p) (i := i) hi]
    rw [factModStream_exp_get (n := n) (m := p - 1) (i := i) hi]

/-- Modular evaluation consuming both factorial-residue streams exactly once. -/
def aModPrimeStream (n p : Nat) : Nat :=
  let bases := (factModStream n p).drop 1
  let exps := ((factModStream n (p - 1)).drop 1).reverse
  (List.foldl (fun acc term => acc + term) 0
    (List.zipWith (fun b e => powModResidue b e p) bases exps)) % p

theorem sumRange_eq_foldl_range (n : Nat) (f : Nat → Nat) :
    sumRange n f = List.foldl (fun acc i => acc + f i) 0 (List.range n) := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [sumRange_succ, List.range_succ, List.foldl_append]
    simp [ih]

theorem aModPrimeStream_eq_reduced (n p : Nat) :
    aModPrimeStream n p = aModPrimeReduced n p := by
  unfold aModPrimeStream aModPrimeReduced
  dsimp only
  rw [factModStream_zip_terms, List.foldl_map]
  rw [← sumRange_eq_foldl_range]
  congr 1
  apply congrArg (sumRange n)
  funext i
  simp only [factMod_eq]

theorem aModPrimeStream_eq {n p : Nat} (hp : 1 < p) (hc : primeCert p) :
    aModPrimeStream n p = a n % p := by
  rw [aModPrimeStream_eq_reduced, aModPrimeReduced_eq hp hc]

#print axioms foldl_factMod_range
#print axioms factModTable_get
#print axioms factModTable_getBang
#print axioms aModPrimeTableAux_eq
#print axioms aModPrimeTable_eq
#print axioms aModPrimeTable_eq_reduced
#print axioms factModStream_get
#print axioms factModStream_zip_terms
#print axioms aModPrimeStream_eq_reduced
#print axioms aModPrimeStream_eq

end LeanA113258
