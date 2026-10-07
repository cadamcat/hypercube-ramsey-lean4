import Mathlib

/-!
# Greedy colouring of finite graphs

X-GreedyColour: the standard finite greedy argument uses at most `Δ` previously coloured neighbours at each
vertex, so one of `Δ+1` colours is available.
-/

namespace HypercubeRamsey

/-- X-GreedyColour: a finite graph of maximum degree at most `Δ` has a proper colouring with `Δ+1` colours. -/
theorem xGreedyColour {V : Type*} [Fintype V] (G : SimpleGraph V) [DecidableRel G.Adj] (Δ : ℕ)
    (hdegree : ∀ v, (Finset.univ.filter (fun u => G.Adj v u)).card ≤ Δ) :
    ∃ colour : V → Fin (Δ + 1),
      ∀ u v, G.Adj u v → colour u ≠ colour v := by
  classical
  sorry

end HypercubeRamsey
