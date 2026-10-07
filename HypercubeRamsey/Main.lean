import HypercubeRamsey.Interface

/-!
# The target

Formal Conjectures' `Erdos181.erdos_181`, over the definitions copied in `HypercubeRamsey/FormalConjectures.lean`.
`scripts/check_target.py types` compares this statement with `Challenge.lean`.
-/

namespace Erdos181

open SimpleGraph

theorem erdos_181 :
    ∃ C > (0 : ℝ), ∀ n : ℕ,
      (diagonalGraphRamsey (hypercube n) : ℝ) ≤ C * 2 ^ n :=
  HypercubeRamsey.erdos_181_of_linear HypercubeRamsey.linear_bound

end Erdos181
