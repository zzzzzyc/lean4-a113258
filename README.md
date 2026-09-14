# A113258: No Perfect Powers for n > 4

Author: **zzzzzyc / zhang yichuan**

Consider the factorial-power sum sequence

$$
a(n)=\sum_{i=1}^{n}(i!)^{(n-i+1)!}.
$$

This project proves that, for every natural number $n>4$, there are no natural numbers $b>1$ and $e>1$ such that $a(n)=b^e$.

The main theorem is `LeanA113258.not_perfect_power_gt_four`. The negation of the original existence statement is `LeanA113258.officialConjecture_false`.

## Build and audit

The project uses Lean **4.33.1**. The file `lake-manifest.json` pins Mathlib to commit `0df444a360eaa60ab8c11dca51a86af692955474`.

```sh
lake exe cache get
lake build
lake env lean Audit.lean
```

The last command checks the types of the final theorems and prints the axiom dependencies of the analytic lower bound, the reduction from the infinite range, and the main theorems.

## Proof outline

Elementary number theory reduces any putative counterexample to parameters satisfying $n\ge12$, $b\ge209$, and $e\ge n$, with $b$ odd and $\gcd(e,(n-1)!)=1$. Set $V=(n-1)!$ and $F=(n-2)!$. Then

$$
a(n)=2^V+\delta_n,\qquad 0<\delta_n<2^{3F}.
$$

If $a(n)=b^e$, the linear form in two logarithms $\Lambda=e\log b-V\log2$ is a very small positive number. Using interpolation determinants, the project proves an explicit lower bound under the required large-exponent and coprimality conditions. Combining this with the upper bound on the remainder shows that all remaining candidates satisfy

$$
12\le n\le2523,\qquad n\le e<3500,\qquad
9e(n-4)<22680(n-1)+2520.
$$

Prime-factor and modular-arithmetic certificates cover this finite range and exclude every candidate. The exclusion rules, coverage of the candidates, and final reduction are all proved in Lean.

## Trust assumptions

- The analytic lower bound and the reduction from the infinite range depend only on the three standard axioms `propext`, `Classical.choice`, and `Quot.sound`.
- The main theorems additionally use **119 `native_decide` computational dependencies**: 10 batches of prime-factor certificates, 108 batches of modular-arithmetic certificates, and one coverage-list check. These computations additionally trust the Lean compiler. The number 119 counts computational dependencies, not candidates.
- The final proof does not depend on `sorryAx` or an unproved Laurent assumption. The formalization establishes the special two-logarithm lower bound needed for this problem.

## Source files

- `A113258Closure.lean`: entry point for the final results.
- `A113258FullyFormal.lean`: connects the analytic reduction to the finite certificates.
- `LaurentCoprimeLowerBound.lean` and its dependencies: proof of the two-logarithm lower bound.
- `LeanA113258/`: sequence definitions and elementary number theory.
- `N12Cover/`, `FactorCoverBatch*.lean`, and the checker modules: finite certificates embedded in Lean and their verification.
- `Audit.lean`: checks the final theorem statements and their axiom dependencies.

## References

- [OEIS A113258](https://oeis.org/A113258).
- [Problem statement in Formal Conjectures](https://github.com/google-deepmind/formal-conjectures/blob/main/FormalConjectures/OEIS/113258.lean).
- Michel Laurent, *Linear forms in two logarithms and interpolation determinants II*, Acta Arithmetica 133(4), 2008, 325–348. [DOI 10.4064/aa133-4-3](https://doi.org/10.4064/aa133-4-3).

## License

Copyright 2026 zzzzzyc / zhang yichuan

The project's source code, certificates, and original documentation are licensed under the **Apache License 2.0**. See [LICENSE](LICENSE) for the full text and [NOTICE](NOTICE) for upstream attribution, dependency licenses, and references. Third-party materials remain subject to their respective licenses.
