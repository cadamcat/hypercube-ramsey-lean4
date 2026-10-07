import HypercubeRamsey.Bridge
import HypercubeRamsey.Framework.Basic

/-!
# Top-level assembly

The target follows once no bad sequence exists.
-/

namespace HypercubeRamsey

open SimpleGraph
open OAI.HypercubeRamsey

theorem erdos_181_of_no_badSeq (h : BadSeq → False) :
    ∃ C > (0 : ℝ), ∀ n : ℕ, (diagonalGraphRamsey (hypercube n) : ℝ) ≤ C * 2 ^ n := by
  by_contra htarget
  have hnot : ¬ ∃ C : ℝ, 0 < C ∧
      ∀ n : ℕ, (ramseyNumber (cube n) : ℝ) ≤ C * (2 : ℝ) ^ n := by
    intro hlinear
    exact htarget (erdos_181_of_linear hlinear)
  obtain ⟨S⟩ := badSeq_of_not_linear hnot
  exact h S

end HypercubeRamsey
