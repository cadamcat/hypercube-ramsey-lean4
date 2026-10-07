import HypercubeRamsey.Bridge

/-!
# Probes of the target's definitions (statement fidelity)

Kernel-checked evaluations of the Formal Conjectures definitions on small cases.
-/

open SimpleGraph

-- Q_2 is the 4-cycle 00-01-11-10: neighbours differ in one bit, antipodes do not.
example : (hypercube 2).Adj ![false, false] ![false, true] := by rw [hypercube_adj]; decide
example : ¬ (hypercube 2).Adj ![false, false] ![true, true] := by rw [hypercube_adj]; decide
example : ¬ (hypercube 2).Adj ![true, false] ![true, false] := by rw [hypercube_adj]; decide

-- Q_n has 2^n vertices.
example (n : ℕ) : Fintype.card (Fin n → Bool) = 2 ^ n := by simp

-- R(Q_0) = 1: the one-vertex graph needs one vertex, so the bound forces C ≥ 1.
example : diagonalGraphRamsey (hypercube 0) = 1 := by
  rw [HypercubeRamsey.diagonalGraphRamsey_hypercube]
  exact OAI.HypercubeRamsey.ramseyNumber_cube_zero

-- The Ramsey set is nonempty and its infimum is at least the order, so the target is not vacuous:
-- R(Q_n) ≥ 2^n for every n.
example (n : ℕ) : 2 ^ n ≤ diagonalGraphRamsey (hypercube n) := by
  rw [HypercubeRamsey.diagonalGraphRamsey_hypercube]
  exact (OAI.HypercubeRamsey.elementary_cube_bounds n).1
