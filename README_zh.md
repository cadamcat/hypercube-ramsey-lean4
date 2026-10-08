[English](README.md) | [简体中文](README_zh.md)

# 超立方体 Ramsey 数具有线性阶：Lean 4 形式化

存在绝对常数 `C > 0`，使得对每个 `n ≥ 0`，`n` 维超立方体的 Ramsey 数不超过 `C · 2^n`：对顶点数至少为 `C · 2^n` 的完全图，其边的任意红蓝二着色都包含该超立方体的单色副本。

- **作者：** Yao Xu ([@cadamcat](https://github.com/cadamcat))；见[作者与署名说明](AUTHORS.md)。
- **数学结果：** OpenAI，[*The hypercube Ramsey number has linear order*](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/The-hypercube-Ramsey-number-has-linear-order-September-23-2026/paper.pdf)，定理 1.1。
- 借助 AI 辅助开发（Claude Code、Codex 和 Antigravity）；所有证明均经 Lean 4 内核验证。

## 主要结果

本仓库证明了 Google DeepMind 的 Formal Conjectures 在提交 `9d259649abe0b02d7a25f7589b872db679b35e21` 中给出的 Erdős 第 181 题陈述（[181.lean](https://github.com/google-deepmind/formal-conjectures/blob/9d259649abe0b02d7a25f7589b872db679b35e21/FormalConjectures/ErdosProblems/181.lean)）：

```lean
namespace Erdos181

open SimpleGraph

theorem erdos_181 :
    ∃ C > (0 : ℝ), ∀ n : ℕ,
      (diagonalGraphRamsey (hypercube n) : ℝ) ≤ C * 2 ^ n
```

`hypercube n` 是 `Fin n → Bool` 上的图，两个向量恰有一个坐标不同时相邻。`graphRamsey G H` 是满足下述条件的顶点数 `M` 所成集合的 `sInf`：对 `Fin M` 上的每个图 `C`，`C` 包含 `G` 的副本，或 `C` 的补图包含 `H` 的副本；`diagonalGraphRamsey G` 即 `graphRamsey G G`。包含关系是 Mathlib 的 `IsContained`，即单射同态，因此单色副本不必是诱导子图，这与论文一致。对超立方体而言，这个集合非空且不含 `0`，所以其 `sInf` 就是满足条件的最小正整数，上界不会因集合为空而平凡成立：[Bridge.lean](HypercubeRamsey/Bridge.lean) 证明 `diagonalGraphRamsey (hypercube n)` 等于 OpenAI 的 `ramseyNumber (cube n)`（对正整数顶点数取下确界），[TargetProbes.lean](Audit/TargetProbes.lean) 检查了 `2 ^ n ≤ diagonalGraphRamsey (hypercube n)`。

[Challenge.lean](Challenge.lean) 包含这一陈述及其所用的定义（从 Formal Conjectures 复制），只导入 Mathlib。[HypercubeRamsey/Main.lean](HypercubeRamsey/Main.lean) 证明了同名、同陈述的定理，所用定义是 [HypercubeRamsey/FormalConjectures.lean](HypercubeRamsey/FormalConjectures.lean) 中的一份相同副本。[Challenge.json](Challenge.json) 配置 Comparator 比较这两个模块。陈述的检查方法以及与 Formal Conjectures 原文件的差异见[验证说明](docs/verification.md)。

## 证明的组织

形式证明遵循论文。OpenAI 的 Lean 库提供超立方体图、其 Ramsey 数、有限 Ramsey 界，以及论文的引理 2.1：若 `R(Q_n) / 2^n` 无界，则存在一列在两个等大顶点集之间的红蓝着色，跨越两侧的边中没有单色超立方体。本仓库形式化了论文的其余部分，即证明这样的序列不存在。

| 路径 | 内容 |
| --- | --- |
| `HypercubeRamsey/Bridge.lean` | `hypercube n` 就是 OpenAI 的 `cube n`，且 `diagonalGraphRamsey` 在其上与 OpenAI 的 `ramseyNumber` 相等 |
| `HypercubeRamsey/Framework/`、`HypercubeRamsey/Assembly.lean` | 反例序列、两侧顶点上的概率分布、阶段（stage）、补丁（patch）与差异（discrepancy）界 |
| `HypercubeRamsey/S03/` 至 `HypercubeRamsey/S18/` | 论文第 3 至 18 节 |
| `HypercubeRamsey/PartC/` | 第 12 至 18 节共用的定义与常数 |
| `HypercubeRamsey/Tools/` | 一般性引理：二项式与集中不等式估计、鞅、超立方体几何 |
| `HypercubeRamsey/Interface.lean` | 推论 7.2、10.2、11.4 与第 12 至 18 节的论证合起来排除反例序列 |
| `HypercubeRamsey/Main.lean` | `Erdos181.erdos_181` |
| `Audit/TargetProbes.lean`、`Audit/IndependentRestatement.lean` | 对目标定义的内核检查探针，以及用初等语言重述的定理 1.1 及其与目标等价的证明 |

## 构建与验证

环境要求：Git、Python 3 和 [elan](https://github.com/leanprover/elan)，并确保 `lake` 已加入 `PATH`。在全新检出的仓库根目录运行：

```sh
lake update
scripts/apply-oai-patches.sh
lake exe cache get
lake build
```

OpenAI 的 `lake update` hook 在解析依赖并写入 `lake-manifest.json` 之后会报错退出，错误信息以 `iut: Lake resolved an unexpected checkout at …` 开头。随后运行补丁脚本：它把 OpenAI 的 Lean 4.34.1 兼容补丁应用到已获取的依赖包上，再次运行 `lake update` 后也可重新运行。

检查陈述与公理：

```sh
LEAN_NUM_THREADS=4 ./scripts/verify.sh
```

脚本构建 `HypercubeRamsey.Main`，检查复制的定义以及 `Erdos181.erdos_181` 经 Lean 精化（elaboration）后的陈述与 `Challenge.lean` 一致，并检查该定理只依赖 `propext`、`Classical.choice` 和 `Quot.sound`。全部检查通过时退出状态为 0；证明仍依赖 `sorryAx` 时为 2；其他失败为 1。`./scripts/replay.sh` 在全新的 Lean 内核环境中重放该定理所在模块及其导入的全部模块。各项检查和 Comparator 配置见[验证说明](docs/verification.md)。

## 固定依赖

- Lean `v4.34.1`，由 [lean-toolchain](lean-toolchain) 选定。
- [Mathlib](https://github.com/leanprover-community/mathlib4)，提交 `d13f23b723b8a846827a245b89c10fc7d3f11612`。
- OpenAI 的 [`openai/math`](https://github.com/openai/math/tree/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean)，提交 `adc7f1241b42e322a6451854ab7e4b4c146bf78a`。
- 其余依赖由 OpenAI 的库固定版本，具体版本见 [lake-manifest.json](lake-manifest.json)。

## 数学参考文献

- OpenAI，[*The hypercube Ramsey number has linear order*](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/The-hypercube-Ramsey-number-has-linear-order-September-23-2026/paper.pdf)，2026 年 9 月 23 日。
- S. A. Burr 和 P. Erdős，[On the magnitude of generalized Ramsey numbers for graphs](https://www.renyi.hu/~p_erdos/1975-26.pdf)，载于 *Infinite and Finite Sets*, Vol. I，Colloquia Mathematica Societatis János Bolyai 10，North-Holland，1975，215–240。其第 7 节提出超立方体的 Ramsey 数是否为线性的问题。
- [Erdős 第 181 题](https://www.erdosproblems.com/181)。

## 许可证

Apache-2.0；见 [LICENSE](LICENSE)、[NOTICE](NOTICE) 和[第三方来源与署名说明](THIRD_PARTY.md)。
