# A113258: Certificate Specification and Verification / 证书格式与验证

[中文说明](#中文说明) · [English version](#english-version) · [Computational examples / 计算示例](#computational-examples--计算示例)

This technical supplement specifies the finite certificates, their mathematical justification,
and the coverage argument used in *Perfect powers in the OEIS sequence A113258*.
The description refers to proof-source commit
[`8f84e18b47c99512321d136dcb7887415b30de1f`](https://github.com/zzzzzyc/lean4-a113258/tree/8f84e18b47c99512321d136dcb7887415b30de1f).
本说明为《OEIS 数列 A113258 中的完全幂》的配套技术文档，给出有限证书的格式、数学依据与覆盖性论证。
所述实现及证书数据均对应上述固定版本；证书数据以 Lean 源文件形式保存于仓库中。

## 中文说明

### 1. 有限验证的范围

数列定义为

$$a(n)=\sum_{i=1}^{n}(i!)^{(n-i+1)!}.$$

主定理断言：当 $n>4$ 时，不存在整数 $b>1$、$e>1$ 使 $a(n)=b^e$。
下标 $5\le n\le11$ 由单独列出的证书处理。初等归约与对数下界表明，其余可能的反例必须满足

$$12\le n\le2523,\qquad n\le e<3500,$$
$$\gcd(e,(n-1)!)=1,\qquad 9e(n-4)<22680(n-1)+2520.$$

有限验证据此排除满足上述必要条件的候选数对。两类证书均通过模运算验证，
不涉及 $a(n)$ 完整整数值的计算。

### 2. 素因子重数为一的证书

素因子证书由三元组 `(n, p, s)` 表示。其验证条件为：

- $p$ 是素数；
- $s=a(n)\bmod p^2$；
- $s\ne0$ 且 $p\mid s$。

于是 $p\mid a(n)$，但 $p^2\nmid a(n)$。如果 $a(n)=b^e$ 且 $e>1$，
由 $p\mid b^e$ 得 $p\mid b$，进而 $p^2\mid b^e$，矛盾。
因此，该证书排除固定下标 $n$ 处的所有指数 $e>1$。

例如，`FactorCoverBatch001.lean` 包含证书

```lean
(13, 83, 6640)
```

其中 $83^2=6889$，且

$$a(13)\equiv6640=80\cdot83\pmod{6889}.$$

由 $0<6640<6889$ 及 $83\mid6640$，上述判据可知 $a(13)$ 不是完全幂。
证书集合共含 1,134 个三元组，排除 1,134 个不同下标。

### 3. 固定指数的模排除证书

模证书由六元组 `(n, e, k, p, r, t)` 及 $p$ 的素性证明构成。
其验证条件为

$$p-1=2ke,\qquad r=a(n)\bmod p,\qquad r\ne0,$$
$$t=r^{2k}\bmod p,\qquad t\ne1.$$

如果 $a(n)=b^e$，则 $r\ne0$ 保证 $p\nmid b$。费马小定理给出

$$r^{2k}\equiv b^{2ke}=b^{p-1}\equiv1\pmod p,$$

与 $t\ne1$ 矛盾。因此，该证书排除固定数对 $(n,e)$ 对应的等式 $a(n)=b^e$。
此判据不要求 $e$ 为素数。

例如，`N12Cover/Block001.lean` 的首条证书为

```lean
⟨⟨12, 13, 2, 53, 33, 46⟩, LeanA113258.Generated.PrimeCerts.primeCert_53⟩
```

该证书满足 $52=2\cdot2\cdot13$、$a(12)\equiv33\pmod{53}$，且
$33^4\equiv46\not\equiv1\pmod{53}$，因此 $a(12)$ 不是十三次幂。
该下标处其他候选指数的排除由相应证书与覆盖性定理保证。

### 4. 候选域与覆盖性证明

记 $\mathcal F$ 为第一类证书已排除的下标集合。由指数互素条件，$e$ 的每个素因子都不小于 $n$。
以 $\operatorname{minFac}(e)$ 表示 $e$ 的最小素因子，定义剩余候选域

$$\begin{aligned}
\mathcal E=\{(n,e):\;&12\le n\le2523,\ n\le e<3500,\ n\le\operatorname{minFac}(e),\\
&9e(n-4)<22680(n-1)+2520,\ n\notin\mathcal F\}.
\end{aligned}$$

覆盖性论证包括以下三个步骤：

1. `ExpectedPairs.lean` 中的 `expectedPairs_mem` 是符号证明：任何满足归约条件、尚未被第一类证书排除的反例，其数对都属于枚举列表 `expectedPairs`。
2. `FiniteCover.lean` 中的 `modularCoverKeys_eq_expected` 通过计算验证模证书的有序键列表与 `expectedPairs` 相等。
3. `modularCover_covers` 证明每个候选数对均有对应证书；`finite_cut_cover` 结合检查器可靠性定理完成有限范围的排除。

证书搜索与证书验证在论证中相互分离。候选域的包含性由符号证明建立，
证书键的完整性由列表相等性验证保证，集合 $\mathcal F$ 中各下标的排除则由素因子证书验证保证。
搜索程序的正确性不作为最终定理的前提。

模证书集合共含 215,122 条记录，涉及 1,376 个下标、726 个指数和 843 个素数模数。
指数中包含 484 个素数与 242 个合数；合数指数对应 366 条证书。
最大素数模数为 115,499。

$12\le n\le2523$ 共含 2,512 个下标，而两类证书涉及的下标数之和为
$1134+1376=2510$，且这两个下标集合互不相交。对于未出现于两类证书中的下标 $2522$、$2523$，
上述整数不等式分别将指数限制为 $\{2522,2523\}$ 和 $\{2523\}$。
由于 $2522$ 与 $2523$ 分别有素因子 $2$ 与 $3$，这些指数均不满足互素条件。
因此，两处剩余候选域均为空。

### 5. 阶乘幂的模计算

检查器通过递推表计算阶乘余数。模素数 $p$ 时，与 $p$ 互素的底数可按模 $p-1$ 约化指数；
底数被 $p$ 整除时，由于原指数为正，对应项的余数为零。
模 $p^2$ 时，互素底数的指数可按模 $p(p-1)$ 约化；非互素底数分两种情形处理：
指数为 $1!=1$ 时保留底数余数，指数至少为 $2!$ 时该项模 $p^2$ 为零。
因而，指数约化仅用于满足相应互素条件的项。
上述计算与数列定义的一致性已在 Lean 中证明。

### 6. 公理依赖与验证范围

检查规则的可靠性、数学归约和枚举包含性有形式化证明。
最终两个定理各自依赖三个标准公理 `propext`、`Classical.choice`、`Quot.sound`，
以及 119 个由 `native_decide` 生成的计算公理：10 个素因子批次、108 个模证书分块、1 个覆盖列表相等性。
有限计算通过编译执行完成，其信任范围包含 Lean 编译器和运行时；这些计算结果并非全部由逻辑内核逐步归约得到。

论文附录另行记录了独立 C／Python 检查的范围与结果。
本说明所附 Python 程序仅复算第 2、3 节的两条示例证书。
完整证书集合的形式化验证可按下文的 Lean 构建及审计命令复现。

## English version

### 1. Scope of the finite verification

For the sequence $a(n)=\sum_{i=1}^{n}(i!)^{(n-i+1)!}$, the theorem excludes
$a(n)=b^e$ with $n>4$ and $b,e>1$. Indices $5\le n\le11$ are handled by separate certificates.
The mathematical reduction bounds every remaining counterexample by
$12\le n\le2523$, $n\le e<3500$, $\gcd(e,(n-1)!)=1$, and
$9e(n-4)<22680(n-1)+2520$. Certificates discharge this finite domain.

### 2. Certificates of prime multiplicity one

A factor certificate is a triple `(n, p, s)` specifying a prime $p$ and the exact residue
$s=a(n)\bmod p^2$, with $s\ne0$ and $p\mid s$.
Thus $p$ divides $a(n)$ exactly once. In a power $b^e$ with $e>1$, a prime
dividing the base would occur at least twice. The row therefore excludes all such powers at $n$.

For example, the certificate `(13, 83, 6640)` in `FactorCoverBatch001.lean` states
$a(13)\equiv6640=80\cdot83\pmod{83^2}$, with $83^2=6889$.
There are 1,134 factor rows, for 1,134 different indices.

### 3. Modular exclusion for a fixed exponent

A modular certificate consists of a tuple `(n, e, k, p, r, t)` and a primality witness for $p$.
The checker verifies $p-1=2ke$, $r=a(n)\bmod p\ne0$, and
$t=r^{2k}\bmod p\ne1$.
If $a(n)=b^e$, Fermat's theorem would instead give
$r^{2k}\equiv b^{p-1}\equiv1\pmod p$, a contradiction.
No primality assumption on $e$ is needed.

For example, `(12, 13, 2, 53, 33, 46)` in `N12Cover/Block001.lean` excludes thirteenth powers at index 12:
$52=4\cdot13$, $a(12)\equiv33\pmod{53}$, and $33^4\equiv46\pmod{53}$.
The remaining candidate exponents are excluded by the corresponding certificates and the coverage theorem.

### 4. Candidate domain and coverage

After removing the indices certified by factor rows, `expectedPairs` enumerates
the bounded domain using $n\le\operatorname{minFac}(e)$ and the strict integer inequality.
`expectedPairs_mem` symbolically proves that every remaining hypothetical counterexample
belongs to this list. A separate computation checks equality of the certificate-key list
and `expectedPairs`. The coverage theorem then retrieves a checked row for each possible pair.
The correctness of the search program is not a premise of the final theorem.

The final list has 215,122 rows, covering 1,376 indices and using 843 prime moduli
(maximum 115,499). It retains 726 distinct exponents: 484 prime and 242 composite;
366 rows have composite exponents.
The two indices absent from both certificate classes are 2522 and 2523.
The integer inequality restricts their exponents to $\{2522,2523\}$ and $\{2523\}$, respectively.
Since $2522$ and $2523$ have prime factors $2$ and $3$, respectively, all these exponents violate
the coprimality condition. Both remaining candidate domains are therefore empty.

### 5. Modular evaluation of factorial powers

Fast evaluation uses factorial residue tables. Exponent reduction modulo $p-1$
or $p(p-1)$ is applied only to bases coprime to the modulus. Nonunits are handled
separately, including the exponent-one case modulo $p^2$.
The agreement of these computations with the defining sum is proved in Lean.

### 6. Axiom dependencies and verification scope

Each final theorem depends on the three standard axioms `propext`, `Classical.choice`, and `Quot.sound`,
and on 119 compiled-computation axioms:
10 factor batches, 108 modular blocks, and one coverage equality.
`native_decide` adds trust in the Lean compiler and runtime.
The finite computations are evaluated by compiled execution rather than entirely by kernel reduction.
The paper's appendix separately records the scope and results of independent C/Python checks.
The Python program below verifies the two example certificates in Sections 2 and 3;
the complete formal verification can be reproduced using the Lean commands below.

## Computational examples / 计算示例

The following Python 3 program uses only the standard library. It evaluates the defining sum
modulo the specified moduli, retaining the original factorial exponents.
以下 Python 3 程序仅使用标准库，直接按数列定义计算指定模数下的余数，并保留原始阶乘指数。

```python
from math import factorial, isqrt

def prime(p):
    return p >= 2 and all(p % d for d in range(2, isqrt(p) + 1))

def a_mod(n, modulus):
    return sum(pow(factorial(i), factorial(n - i + 1), modulus)
               for i in range(1, n + 1)) % modulus

assert prime(83)
s = a_mod(13, 83**2)
assert s == 6640 and s != 0 and s % 83 == 0
print("factor row: a(13) mod 83^2 =", s)

assert prime(53) and 53 - 1 == 2 * 2 * 13
r = a_mod(12, 53)
t = pow(r, 4, 53)
assert r == 33 and r != 0 and t == 46 and t != 1
print("modular row: a(12) mod 53 =", r, "; r^4 mod 53 =", t)
```

Expected output / 预期输出：

```text
factor row: a(13) mod 83^2 = 6640
modular row: a(12) mod 53 = 33 ; r^4 mod 53 = 46
```

## Reproducing the Lean verification / Lean 验证的复现

Use a checkout of the fixed commit linked at the top, with the toolchain selected by
`lean-toolchain` (Lean 4.33.1) and the dependencies recorded in `lake-manifest.json`.
在文首所链接的固定版本仓库根目录运行：

```sh
lake exe cache get
lake build
lake env lean Audit.lean
```

`Audit.lean` checks the exported theorem types and reports their axiom dependencies.
The recorded 181-module rebuild took 1530.4 seconds with sequential module compilation
and reused pinned external dependency caches. This timing refers to the recorded build configuration.
Peak memory was not recorded. 该次构建未记录峰值内存。

## Source map / 源码入口

All links below are pinned to the same proof snapshot. 以下链接均固定到同一证明版本。

- [Factor row checks and their soundness / 素因子检查与可靠性](https://github.com/zzzzzyc/lean4-a113258/blob/8f84e18b47c99512321d136dcb7887415b30de1f/PrimeSquareMod.lean)
- [Factor example / 素因子示例](https://github.com/zzzzzyc/lean4-a113258/blob/8f84e18b47c99512321d136dcb7887415b30de1f/FactorCoverBatch001.lean)
- [Modular row fields, checker and soundness / 模证书字段、检查与可靠性](https://github.com/zzzzzyc/lean4-a113258/blob/8f84e18b47c99512321d136dcb7887415b30de1f/CoverChecker.lean)
- [Modular example / 模证书示例](https://github.com/zzzzzyc/lean4-a113258/blob/8f84e18b47c99512321d136dcb7887415b30de1f/N12Cover/Block001.lean)
- [Symbolic inclusion in the enumerated domain / 归约条件到枚举域的符号证明](https://github.com/zzzzzyc/lean4-a113258/blob/8f84e18b47c99512321d136dcb7887415b30de1f/ExpectedPairs.lean)
- [Coverage equality and finite closure / 覆盖相等性与有限范围的证明](https://github.com/zzzzzyc/lean4-a113258/blob/8f84e18b47c99512321d136dcb7887415b30de1f/FiniteCover.lean)
- [Final theorem audit / 最终命题审计](https://github.com/zzzzzyc/lean4-a113258/blob/8f84e18b47c99512321d136dcb7887415b30de1f/Audit.lean)

### Mathematical development / 数学论证的入口

- [Small indices / 小下标](https://github.com/zzzzzyc/lean4-a113258/blob/8f84e18b47c99512321d136dcb7887415b30de1f/LeanA113258/ProofProgress.lean): `not_perfect_power_five_through_eleven`.
- [Primality and basic modular certificates / 素性与基本模证书](https://github.com/zzzzzyc/lean4-a113258/blob/8f84e18b47c99512321d136dcb7887415b30de1f/LeanA113258/PrimeCertificates.lean): `primeCert_of_trial`.
- [Elementary remainder estimate / 初等余项界](https://github.com/zzzzzyc/lean4-a113258/blob/8f84e18b47c99512321d136dcb7887415b30de1f/LeanA113258/BakerCond.lean): `delta_lt_two_pow_three_B`.
- [Nonzero integer minor / 非零整数子式](https://github.com/zzzzzyc/lean4-a113258/blob/8f84e18b47c99512321d136dcb7887415b30de1f/LaurentRectangleRank.lean): `exists_nonzero_integer_rectangle_minor`.
- [Determinant comparison / 行列式比较](https://github.com/zzzzzyc/lean4-a113258/blob/8f84e18b47c99512321d136dcb7887415b30de1f/LaurentParameterConstraint.lean): `integer_determinant_parameter_constraint`.
- [Specialized logarithmic bound / 专门化对数下界](https://github.com/zzzzzyc/lean4-a113258/blob/8f84e18b47c99512321d136dcb7887415b30de1f/LaurentCoprimeLowerBound.lean): `two_log_lower_bound_large_coprime`.
- [Effective cutoff / 有效截断](https://github.com/zzzzzyc/lean4-a113258/blob/8f84e18b47c99512321d136dcb7887415b30de1f/AnalyticCutoff.lean).
- [Final connection / 最终衔接](https://github.com/zzzzzyc/lean4-a113258/blob/8f84e18b47c99512321d136dcb7887415b30de1f/A113258FullyFormal.lean): `remaining_ratio_fully_formal`.

Copyright 2026 YiChuan Zhang. Licensed under Apache-2.0; see [LICENSE](LICENSE).
