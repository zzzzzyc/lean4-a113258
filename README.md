# A113258 的 Lean 证明

作者：**zzzzzyc / zhang yichuan**

定义阶乘幂和序列

$$
a(n)=\sum_{i=1}^{n}(i!)^{(n-i+1)!}.
$$

本项目证明：对所有自然数 $n>4$，不存在自然数 $b>1$、$e>1$ 使 $a(n)=b^e$。

主定理为 `LeanA113258.not_perfect_power_gt_four`，存在性命题的否定为 `LeanA113258.officialConjecture_false`。

## 构建与审计

使用 Lean **4.33.1**。`lake-manifest.json` 锁定 Mathlib 提交 `0df444a360eaa60ab8c11dca51a86af692955474`。

```sh
lake exe cache get
lake build
lake env lean Audit.lean
```

最后一条命令核对最终定理的类型，并打印解析下界、无限范围归约和主定理的公理依赖。

## 证明概要

初等数论先将潜在反例归约到 $n\ge12$、$b\ge209$、$e\ge n$，其中 $b$ 为奇数且 $\gcd(e,(n-1)!)=1$。令 $V=(n-1)!$、$F=(n-2)!$，则

$$
a(n)=2^V+\delta_n,\qquad 0<\delta_n<2^{3F}.
$$

若 $a(n)=b^e$，两对数线性形式 $\Lambda=e\log b-V\log2$ 是一个极小的正数。项目通过插值行列式方法，在所需的大指数、互质条件下证明显式下界。结合余项上界，得到所有潜在反例都满足

$$
12\le n\le2523,\qquad n\le e<3500,\qquad
9e(n-4)<22680(n-1)+2520.
$$

素因子证书与模运算证书覆盖这个有限范围，排除全部候选。相应的排除规则、候选覆盖性和最终归约均在 Lean 中证明。

## 信任范围

- 解析下界与无限范围归约仅依赖 `propext`、`Classical.choice`、`Quot.sound` 三个标准公理。
- 主定理额外使用 **119 个 `native_decide` 计算依赖**：10 批素因子证书、108 批模运算证书，以及 1 项覆盖列表检查。验证额外信任 Lean 编译器；119 是计算依赖数，并非候选数。
- 最终证明不依赖 `sorryAx` 或未证明的 Laurent 假设。这里形式化的是原题所需的特殊两对数下界。

## 源码入口

- `A113258Closure.lean`：最终结果入口。
- `A113258FullyFormal.lean`：连接解析归约与有限证书。
- `LaurentCoprimeLowerBound.lean` 及其依赖：两对数下界的证明。
- `LeanA113258/`：序列定义与初等数论。
- `N12Cover/`、`FactorCoverBatch*.lean` 及检查模块：嵌入 Lean 的有限证书及其验证。
- `Audit.lean`：最终定理与公理依赖审计。

## 来源

- [OEIS A113258](https://oeis.org/A113258)。
- [Formal Conjectures 中的题目陈述](https://github.com/google-deepmind/formal-conjectures/blob/main/FormalConjectures/OEIS/113258.lean)。
- Michel Laurent, *Linear forms in two logarithms and interpolation determinants II*, Acta Arithmetica 133(4), 2008, 325–348. [DOI 10.4064/aa133-4-3](https://doi.org/10.4064/aa133-4-3)。

## 许可证

Copyright 2026 zzzzzyc / zhang yichuan

本项目的源码、证书和原创文档采用 **Apache License 2.0**，许可全文见根目录 `LICENSE`。上游署名、依赖许可和文献来源见根目录 `NOTICE`；第三方材料仍遵循各自的许可。
