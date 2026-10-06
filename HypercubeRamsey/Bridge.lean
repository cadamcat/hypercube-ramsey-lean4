import HypercubeRamsey.FormalConjectures
import OAI.Combinatorics.Ramsey.Hypercube

/-!
# Bridge from the Formal Conjectures target to OpenAI's vocabulary

`SimpleGraph.hypercube n` is OpenAI's `cube n`, and `diagonalGraphRamsey` agrees with OpenAI's
`ramseyNumber` on it. So a linear bound on `ramseyNumber (cube n)` gives `Erdos181.erdos_181`.
-/

namespace HypercubeRamsey

open SimpleGraph OAI.HypercubeRamsey

theorem hypercube_eq_cube (n : ℕ) : hypercube n = cube n := by
  ext u v
  rfl

theorem diagonalGraphRamsey_hypercube (n : ℕ) :
    diagonalGraphRamsey (hypercube n) = ramseyNumber (cube n) := by
  rw [hypercube_eq_cube]
  unfold diagonalGraphRamsey graphRamsey ramseyNumber
  congr 1
  ext M
  show (∀ C : SimpleGraph (Fin M), Nonempty ((cube n).Copy C) ∨ Nonempty ((cube n).Copy Cᶜ)) ↔
    0 < M ∧ RamseyProperty (cube n) M
  constructor
  · intro h
    refine ⟨Nat.pos_of_ne_zero ?_, h⟩
    rintro rfl
    rcases h ⊥ with h | h
    · obtain ⟨f⟩ := h
      exact (f (fun _ => false)).elim0
    · obtain ⟨f⟩ := h
      exact (f (fun _ => false)).elim0
  · exact fun h => h.2

/-- The target follows from a linear bound in OpenAI's vocabulary. -/
theorem erdos_181_of_linear
    (h : ∃ C : ℝ, 0 < C ∧ ∀ n : ℕ, (ramseyNumber (cube n) : ℝ) ≤ C * (2 : ℝ) ^ n) :
    ∃ C > (0 : ℝ), ∀ n : ℕ, (diagonalGraphRamsey (hypercube n) : ℝ) ≤ C * 2 ^ n := by
  obtain ⟨C, hC, hb⟩ := h
  exact ⟨C, hC, fun n => by rw [diagonalGraphRamsey_hypercube]; exact hb n⟩

end HypercubeRamsey
