# Authors and attribution

Yao Xu ([@cadamcat](https://github.com/cadamcat)) is the author. He planned the formalization, set its acceptance criteria, and made the publication decision.

The mathematical result is OpenAI's [*The hypercube Ramsey number has linear order*](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/The-hypercube-Ramsey-number-has-linear-order-September-23-2026/paper.pdf), which resolves the Burr–Erdős hypercube Ramsey conjecture. This repository formalizes that result and claims no new mathematics.

Claude Opus 5.5 in Claude Code coordinated the work and reviewed statements. GPT-6 Luna in Codex wrote most of the Lean proofs. GPT-6.1 Sol in Codex checked statements for counterexamples, designed statement repairs, and proved the hardest steps. All proofs are checked by the Lean kernel.

The project uses Mathlib and OpenAI's `openai/math` library. Their sources and licenses, along with the Formal Conjectures definitions included in the repository, are listed in [THIRD_PARTY.md](THIRD_PARTY.md).
