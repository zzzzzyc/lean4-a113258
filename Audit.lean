import A113258Closure

example : ¬ LeanA113258.officialConjecture :=
  LeanA113258.officialConjecture_false

example (n : Nat) (hn : 4 < n) :
    ¬ LeanA113258.IsPerfectPower (LeanA113258.a n) :=
  LeanA113258.not_perfect_power_gt_four hn

#print axioms LeanA113258.LaurentCore.two_log_lower_bound_large_coprime
#print axioms LeanA113258.remaining_ratio_fully_formal
#print axioms LeanA113258.officialConjecture_false
#print axioms LeanA113258.not_perfect_power_gt_four
