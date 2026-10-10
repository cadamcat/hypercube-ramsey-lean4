import HypercubeRamsey.Main
import HypercubeRamsey.Bridge

/-!
# Non-vacuity audit for `Erdos181.erdos_181`

Checks that the theorem is not vacuous: its constant can be applied at concrete `n`, the
definitions take the intended values on small inputs, the bound is not trivially true, and the
theorem implies the colouring form for every `N ≥ C·2^n`. Any admissible constant is at least 1, and
`2^n ≤ R(Q_n)`, so the bound is tight up to the constant.
-/

namespace NonVacuity

open SimpleGraph

/-- The constant from the main theorem applies at concrete `n = 0, 1, 2`. -/
theorem witness_applies_at_concrete :
    ∃ C : ℝ, 0 < C ∧ (diagonalGraphRamsey (hypercube 0) : ℝ) ≤ C * 2 ^ (0 : ℕ) ∧
      (diagonalGraphRamsey (hypercube 1) : ℝ) ≤ C * 2 ^ (1 : ℕ) ∧
      (diagonalGraphRamsey (hypercube 2) : ℝ) ≤ C * 2 ^ (2 : ℕ) := by
  obtain ⟨C, hC, hb⟩ := Erdos181.erdos_181
  exact ⟨C, hC, hb 0, hb 1, hb 2⟩

/-- `Q_n` has `2^n` vertices. -/
theorem hypercube_vertex_card (n : ℕ) : Fintype.card (Fin n → Bool) = 2 ^ n := by
  simp

/-- Adjacency in `Q_2` is the 4-cycle on its four vertices. -/
theorem hypercube_adj_Q2 :
    (hypercube 2).Adj ![false, false] ![false, true] ∧
      ¬ (hypercube 2).Adj ![false, false] ![true, true] ∧
      ¬ (hypercube 2).Adj ![true, false] ![true, false] := by
  refine ⟨?_, ?_, ?_⟩
  · rw [hypercube_adj]; decide
  · rw [hypercube_adj]; decide
  · rw [hypercube_adj]; decide

/-- `Q_0` has a single vertex and no loops. -/
theorem hypercube_Q0_no_loops (u v : Fin 0 → Bool) : ¬ (hypercube 0).Adj u v := by
  rw [hypercube_adj]
  have hempty : ({i : Fin 0 | u i ≠ v i} : Finset (Fin 0)) = ∅ := by simp
  rw [hempty]
  decide

/-- `R(Q_0) = 1`, so the `sInf ∅ = 0` and `M = 0` cases do not arise. -/
theorem ramsey_zero_eq_one : diagonalGraphRamsey (hypercube 0) = 1 := by
  rw [HypercubeRamsey.diagonalGraphRamsey_hypercube]
  exact OAI.HypercubeRamsey.ramseyNumber_cube_zero

/-- `0` is never a Ramsey size (no map from a nonempty vertex type into `Fin 0`). -/
theorem zero_not_mem_ramsey (n : ℕ) :
    (0 : ℕ) ∉ {m : ℕ | ∀ G : SimpleGraph (Fin m),
      (hypercube n).IsContained G ∨ (hypercube n).IsContained Gᶜ} := by
  intro h
  rcases h ⊥ with hG | hG <;> obtain ⟨f⟩ := hG <;> exact (f (fun _ => false)).elim0

/-- The Ramsey number is at least the order (`2^n ≤ R(Q_n)`). -/
theorem ramsey_lower_bound (n : ℕ) :
    2 ^ n ≤ diagonalGraphRamsey (hypercube n) := by
  rw [HypercubeRamsey.diagonalGraphRamsey_hypercube]
  exact (OAI.HypercubeRamsey.elementary_cube_bounds n).1

/-- The Ramsey number is positive, so the `sInf` is not the trivial `0`. -/
theorem ramsey_pos (n : ℕ) : 0 < diagonalGraphRamsey (hypercube n) := by
  have hlow := ramsey_lower_bound n
  have hpos : 0 < 2 ^ n := Nat.two_pow_pos n
  omega

/-- `R(Q_n)` belongs to its own Ramsey set (the set is nonempty). -/
theorem ramsey_mem (n : ℕ) :
    diagonalGraphRamsey (hypercube n) ∈ {m : ℕ |
      ∀ G : SimpleGraph (Fin m),
        (hypercube n).IsContained G ∨ (hypercube n).IsContained Gᶜ} := by
  rw [HypercubeRamsey.diagonalGraphRamsey_hypercube, HypercubeRamsey.hypercube_eq_cube]
  exact (OAI.HypercubeRamsey.ramseyNumber_spec _).2

/-- The Ramsey set for `Q_n` is nonempty (excludes `sInf ∅ = 0`). -/
theorem ramsey_set_nonempty (n : ℕ) :
    {m : ℕ | ∀ G : SimpleGraph (Fin m),
      (hypercube n).IsContained G ∨ (hypercube n).IsContained Gᶜ}.Nonempty :=
  ⟨_, ramsey_mem n⟩

/-- The bound `C * 2 ^ n` is positive for every `n` when `C > 0`. -/
theorem bound_pos (C : ℝ) (hC : 0 < C) (n : ℕ) : 0 < C * (2 : ℝ) ^ n := by
  positivity

/-- The Ramsey property is monotone in the host size. -/
theorem ramsey_monotone (n M N : ℕ)
    (hM : M ∈ {m : ℕ | ∀ G : SimpleGraph (Fin m),
      (hypercube n).IsContained G ∨ (hypercube n).IsContained Gᶜ})
    (hMN : M ≤ N) :
    N ∈ {m : ℕ | ∀ G : SimpleGraph (Fin m),
      (hypercube n).IsContained G ∨ (hypercube n).IsContained Gᶜ} := by
  intro G
  let e : Fin M ↪ Fin N := Fin.castLEEmb hMN
  have hG := hM (G.comap e)
  rcases hG with h | h
  · obtain ⟨f⟩ := h
    left
    refine ⟨⟨⟨fun v => e (f v), fun {u v} huv => ?_⟩, fun a b hab => ?_⟩⟩
    · have h1 := f.toHom.map_adj huv
      simpa using h1
    · exact f.injective (e.injective hab)
  · obtain ⟨f⟩ := h
    right
    refine ⟨⟨⟨fun v => e (f v), fun {u v} huv => ?_⟩, fun a b hab => ?_⟩⟩
    · have h1 := f.toHom.map_adj huv
      rw [compl_adj] at h1
      rw [compl_adj]
      obtain ⟨hne, hnadj⟩ := h1
      exact ⟨e.injective.ne hne, hnadj⟩
    · exact f.injective (e.injective hab)

/-- The main theorem implies the plain colouring form for every `N ≥ C·2^n`. -/
theorem colouring_form :
    ∃ C > (0 : ℝ), ∀ (n N : ℕ), C * (2 : ℝ) ^ n ≤ (N : ℝ) →
      ∀ G : SimpleGraph (Fin N),
        (hypercube n).IsContained G ∨ (hypercube n).IsContained Gᶜ := by
  obtain ⟨C, hC, hb⟩ := Erdos181.erdos_181
  refine ⟨C, hC, fun n N hN G => ?_⟩
  have hle : diagonalGraphRamsey (hypercube n) ≤ N := by
    have h1 : (diagonalGraphRamsey (hypercube n) : ℝ) ≤ C * (2 : ℝ) ^ n := hb n
    have h2 : (diagonalGraphRamsey (hypercube n) : ℝ) ≤ (N : ℝ) := le_trans h1 hN
    exact_mod_cast h2
  exact ramsey_monotone n _ _ (ramsey_mem n) hle G

/-- Any constant satisfying the bound is necessarily at least 1. -/
theorem constant_ge_one (C : ℝ)
    (hb : ∀ n : ℕ, (diagonalGraphRamsey (hypercube n) : ℝ) ≤ C * (2 : ℝ) ^ n) :
    1 ≤ C := by
  have h0 := hb 0
  rw [ramsey_zero_eq_one] at h0
  simpa using h0

/-- The witness from the main theorem is at least 1. -/
theorem witness_ge_one : ∃ C > (0 : ℝ),
    (∀ n : ℕ, (diagonalGraphRamsey (hypercube n) : ℝ) ≤ C * (2 : ℝ) ^ n) ∧ 1 ≤ C := by
  obtain ⟨C, hC, hb⟩ := Erdos181.erdos_181
  exact ⟨C, hC, hb, constant_ge_one C hb⟩

#print axioms witness_applies_at_concrete
#print axioms hypercube_vertex_card
#print axioms hypercube_adj_Q2
#print axioms hypercube_Q0_no_loops
#print axioms ramsey_zero_eq_one
#print axioms zero_not_mem_ramsey
#print axioms ramsey_lower_bound
#print axioms ramsey_pos
#print axioms ramsey_mem
#print axioms ramsey_set_nonempty
#print axioms bound_pos
#print axioms ramsey_monotone
#print axioms colouring_form
#print axioms constant_ge_one
#print axioms witness_ge_one

end NonVacuity
