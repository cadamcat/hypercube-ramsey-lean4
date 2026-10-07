import HypercubeRamsey.Bridge
import HypercubeRamsey.Framework.Basic

/-!
# Top-level assembly

The target follows once no bad sequence exists.
-/

namespace HypercubeRamsey

open SimpleGraph

theorem erdos_181_of_no_badSeq (h : BadSeq → False) :
    ∃ C > (0 : ℝ), ∀ n : ℕ, (diagonalGraphRamsey (hypercube n) : ℝ) ≤ C * 2 ^ n := sorry

end HypercubeRamsey
