# Authors and attribution

Yao Xu ([@cadamcat](https://github.com/cadamcat)) is the author and maintainer of this formalization project.

The mathematical theorem was proved by OpenAI, in the paper [*The hypercube Ramsey number has linear order*](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/The-hypercube-Ramsey-number-has-linear-order-September-23-2026/paper.pdf). It answers a question of Burr and Erdős (Erdős problem 181). This repository formalizes the theorem; it does not claim a new mathematical solution. The formal proof follows the paper and takes the cube, its Ramsey number, finite Ramsey bounds and the paper's counterexample-sequence lemma from OpenAI's Lean library.

The author planned, dispatched and reviewed the work. Formalization and review used Claude Opus 5.5 in Claude Code, GPT-6 Luna and GPT-6.1 Sol in Codex, and Gemini 3.8 Flash in Antigravity. The resulting proofs and their dependencies were checked by the Lean kernel.

The project uses Mathlib, OpenAI's `openai/math` library and the packages it pins, and definitions copied from Google DeepMind's Formal Conjectures. Their authors and licenses are credited in [THIRD_PARTY.md](THIRD_PARTY.md) and [NOTICE](NOTICE).
