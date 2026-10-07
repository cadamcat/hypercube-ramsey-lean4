[English](README.md) | [简体中文](README_zh.md)

# 超立方体 Ramsey 数具有线性阶

本仓库形式化了如下定理：存在与 `n` 无关的常数 `C > 0`，使每个 `n` 维超立方体的对角 Ramsey 数不超过 `C · 2^n`，其中 `n` 遍历自然数并包括零。这是 OpenAI 论文 *The hypercube Ramsey number has linear order* 的结果，解决了 Burr–Erdős 超立方体 Ramsey 猜想。本仓库形式化该结果，不主张新的数学成果。

- **作者：** Yao Xu ([@cadamcat](https://github.com/cadamcat))；作者与署名说明见 [AUTHORS.md](AUTHORS.md)。
- 借助 AI 辅助开发（Claude Code 和 Codex）；所有证明均经 Lean 4 内核验证。

## 形式化陈述

目标是 Formal Conjectures 在提交 `9d259649abe0b02d7a25f7589b872db679b35e21` 中的 `Erdos181.erdos_181`：

```lean
∃ C > (0 : ℝ), ∀ n : ℕ,
  (diagonalGraphRamsey (hypercube n) : ℝ) ≤ C * 2 ^ n
```

`hypercube n` 的顶点是 `n` 位布尔向量，两点当且仅当恰有一个坐标不同而相邻。Ramsey 数中的单色副本是单射图同态，不要求保诱导子图，这与论文一致。挑战将 `graphRamsey` 定义为 `sInf`；证明中的桥接定理将其与 OpenAI 定义的最小正整数 Ramsey 数识别。目标陈述及其定义副本见 [Challenge.lean](Challenge.lean)；证明入口见 [HypercubeRamsey/Main.lean](HypercubeRamsey/Main.lean)。[Challenge.json](Challenge.json) 配置 Comparator 比较两处陈述。

## 构建与验证

环境要求：Git、Python 3 和 [elan](https://github.com/leanprover/elan)，并确保 `lake` 已加入 `PATH`。全新检出后，请运行：

```sh
lake update
scripts/apply-oai-patches.sh
lake exe cache get
lake build
```

发布配置将 OpenAI 库固定到 Git 提交。`lake update` 解析依赖并写入 `lake-manifest.json` 后，可能因 `iut: Lake resolved an unexpected checkout at …` 信息而以非零状态退出。随后运行补丁脚本；它会应用 Lean 4.34.1 兼容补丁，再次运行 `lake update` 后也可安全地重跑。

若要构建定理并检查其公理依赖，请运行：

```sh
LEAN_NUM_THREADS=4 ./scripts/verify.sh
```

脚本会用 Lean 内核构建证明模块与挑战模块，并检查 `Erdos181.erdos_181` 仅依赖 `propext`、`Classical.choice` 和 `Quot.sound`。

## 固定依赖

- Lean `v4.34.1`，由 [lean-toolchain](lean-toolchain) 选定。
- [Mathlib](https://github.com/leanprover-community/mathlib4)，提交 `d13f23b723b8a846827a245b89c10fc7d3f11612`。
- OpenAI 的 [`openai/math`](https://github.com/openai/math/tree/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean)，提交 `adc7f1241b42e322a6451854ab7e4b4c146bf78a`。
- 其余固定依赖及其版本见 [lake-manifest.json](lake-manifest.json)。

Formal Conjectures 的原始陈述见[第 181 题](https://github.com/google-deepmind/formal-conjectures/blob/9d259649abe0b02d7a25f7589b872db679b35e21/FormalConjectures/ErdosProblems/181.lean)。数学结果出自 OpenAI 的论文 [*The hypercube Ramsey number has linear order*](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/The-hypercube-Ramsey-number-has-linear-order-September-23-2026/paper.pdf)。第三方来源见 [THIRD_PARTY.md](THIRD_PARTY.md)，项目许可证见 [LICENSE](LICENSE)。
