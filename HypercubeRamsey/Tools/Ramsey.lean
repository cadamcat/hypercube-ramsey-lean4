import Mathlib
import HypercubeRamsey.Tools.Ramsey_p_tools_binom

/-!
# Binomial Ramsey bound

Finite graph Ramsey with the binomial upper bound needed when one clique parameter grows subexponentially.
-/

namespace HypercubeRamsey

/-- X-RamseyBinom: a graph with at least `choose (s+t-2) (s-1)` vertices contains an `s`-clique or a
`t`-independent set. -/
theorem xRamseyBinom {V : Type*} [Fintype V] (G : SimpleGraph V) (s t : ℕ)
    (hs : 1 ≤ s) (ht : 1 ≤ t)
    (hcard : Nat.choose (s + t - 2) (s - 1) ≤ Fintype.card V) :
    (∃ C : Finset V, C.card = s ∧
      ∀ u ∈ C, ∀ v ∈ C, u ≠ v → G.Adj u v) ∨
    (∃ I : Finset V, I.card = t ∧
      ∀ u ∈ I, ∀ v ∈ I, u ≠ v → ¬ G.Adj u v) := by
  exact xRamseyBinom_p_tools_binom G s t hs ht hcard

end HypercubeRamsey
