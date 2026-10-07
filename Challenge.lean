/-
The target of this formalization: Formal Conjectures `Erdos181.erdos_181`
(`FormalConjectures/ErdosProblems/181.lean`, commit 9d259649abe0b02d7a25f7589b872db679b35e21),
with the definitions it uses copied verbatim from `FormalConjecturesForMathlib` at that commit.
Only the module-system wrappers are dropped, and the deprecated import `Mathlib.Data.Real.Basic` is
replaced by its new path `Mathlib.Basic.Real.Basic`.
The two FC definition files are merged into one block, and FC's other `Ramsey.lean` declarations and its
`EdgeColouring` import are omitted. This file imports Mathlib alone and is not imported
by the proof; `HypercubeRamsey/Main.lean` proves the same statement over the identical definitions
in `HypercubeRamsey/FormalConjectures.lean`, and `scripts/check_target.py` compares the two.
-/
import Mathlib.Combinatorics.SimpleGraph.Basic
import Mathlib.Combinatorics.SimpleGraph.Copy
import Mathlib.Data.Fintype.Pi
import Mathlib.Basic.Real.Basic
import Mathlib.Data.Set.Card
import Mathlib.Order.Lattice.Nat

-- BEGIN FORMAL CONJECTURES DEFINITIONS
namespace SimpleGraph

open scoped Finset

/-- `hypercube n` is the `n`-dimensional hypercube graph `Qₙ`: the vertices are the `n`-bit
vectors, and two vertices are adjacent when they differ in exactly one coordinate. -/
def hypercube (n : ℕ) : SimpleGraph (Fin n → Bool) where
  Adj u v := #{i | u i ≠ v i} = 1
  symm.symm _ _ := by simp [eq_comm]
  loopless.irrefl _ := by simp

@[simp]
theorem hypercube_adj {n : ℕ} {u v : Fin n → Bool} :
    (hypercube n).Adj u v ↔ #{i | u i ≠ v i} = 1 := Iff.rfl

/--
The two-color Ramsey number `graphRamsey G H` is the minimum number of vertices `n`
such that every 2-coloring of the edges of the complete graph on `n` vertices contains
a copy of `G` in the first color or a copy of `H` in the second color.

A 2-coloring of the complete graph on `Fin n` is represented by a graph `C` (the edges of the
first color) and its complement `Cᶜ` (the edges of the second color).
-/
noncomputable def graphRamsey {α β : Type*} [Fintype α] [Fintype β]
    (G : SimpleGraph α) (H : SimpleGraph β) : ℕ :=
  sInf { n : ℕ | ∀ (C : SimpleGraph (Fin n)), G.IsContained C ∨ H.IsContained Cᶜ }

/-- The diagonal graph Ramsey number `R(G, G)`. -/
noncomputable def diagonalGraphRamsey {α : Type*} [Fintype α] (G : SimpleGraph α) : ℕ :=
  graphRamsey G G

end SimpleGraph
-- END FORMAL CONJECTURES DEFINITIONS

namespace Erdos181

open SimpleGraph

/--
Let $Q_n$ be the $n$-dimensional hypercube graph (so that $Q_n$ has $2^n$ vertices and
$n2^{n-1}$ edges). Prove that $$R(Q_n) \ll 2^n.$$
-/
theorem erdos_181 :
    ∃ C > (0 : ℝ), ∀ n : ℕ,
      (diagonalGraphRamsey (hypercube n) : ℝ) ≤ C * 2 ^ n := by
  sorry

end Erdos181
