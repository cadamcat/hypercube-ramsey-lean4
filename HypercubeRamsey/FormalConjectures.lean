/-
Definitions copied verbatim from Formal Conjectures (Apache-2.0), commit
9d259649abe0b02d7a25f7589b872db679b35e21:
- `FormalConjecturesForMathlib/Combinatorics/SimpleGraph/Hypercube.lean` (`hypercube`, `hypercube_adj`);
- `FormalConjecturesForMathlib/Combinatorics/SimpleGraph/Ramsey.lean` (`graphRamsey`, `diagonalGraphRamsey`).
Only the module-system wrappers (`module`, `public import`, `@[expose] public section`) are dropped, and
the deprecated import `Mathlib.Data.Real.Basic` is replaced by its new path `Mathlib.Basic.Real.Basic`.
The two FC definition files are merged into one block, and FC's other `Ramsey.lean` declarations and its
`EdgeColouring` import are omitted.
This file and `Challenge.lean` carry the same definitions; `scripts/check_target.py` compares them.
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
