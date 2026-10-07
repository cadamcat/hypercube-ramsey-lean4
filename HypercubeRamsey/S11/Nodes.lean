import HypercubeRamsey.S11.Needs

/-!
Section 11's two interfaces to the stage-level assembly. The embedding node is the frozen one-shot boundary for
the slice, compatibility, outer-moment, avoidance, injection, and Hall construction in PART-B.md §3.11.
-/

namespace HypercubeRamsey.S11

open HypercubeRamsey

/-- P11.1-sel (11:12–32): select the discrepancy window and the shallow linear-bias menu. -/
theorem linear_jump_selection (T : Stage) (hT : StabilizedOn T FamB)
    (hNoHdag : ¬ HdagLtOne T.swap) (hZero : HLdagZero T)
    (δ : ℚ) (hδ : 0 < δ) (hδ1 : δ < 1) :
    ∃ x₀ : ℚ, 0 < x₀ ∧ x₀ < 1 ∧
      DiscAt T (pw ((1 : ℝ) - (δ : ℝ) / 16)) (pw x₀)
        (fun n => n ^ (-(19 : ℝ) / 20)) ∧
      AvL T ((1 / 100 : ℚ) : ℝ) ((1 / 100 : ℚ) : ℝ) ((1 / 200 : ℚ) : ℝ) := by
  classical
  let y : ℚ := 1 - δ / 16
  have hy : 0 < y := by
    dsimp [y]
    linarith
  have hy1 : y < 1 := by
    dsimp [y]
    linarith
  obtain ⟨x₀, hx₀, hx₀1, hUnavailable⟩ :
      ∃ x₀ : ℚ, 0 < x₀ ∧ x₀ < 1 ∧ ¬ AvP T.swap x₀ y (19 / 20 : ℚ) := by
    by_contra hNoWitness
    apply hNoHdag
    refine ⟨(19 / 20 : ℚ), by norm_num, ?_⟩
    intro x hx hx1
    refine ⟨y, hy, hy1, ?_⟩
    by_contra hNotAvailable
    exact hNoWitness ⟨x, hx, hx1, hNotAvailable⟩
  have hTswap : StabilizedOn T.swap FamB := hT.swap FamB_swap
  have hDiscSwap₀ :=
    _root_.HypercubeRamsey.discAt_of_not_AvP hTswap hx₀ hy (by norm_num) hUnavailable
  have hy_cast : (y : ℝ) = (1 : ℝ) - (δ : ℝ) / 16 := by
    dsimp [y]
    push_cast
    ring
  have hDiscSwap :
      DiscAt T.swap (pw (x₀ : ℝ)) (pw ((y : ℝ)))
        (fun n => n ^ (-(19 : ℝ) / 20)) := by
    have hErr : -((19 / 20 : ℚ) : ℝ) = -(19 : ℝ) / 20 := by norm_num
    simpa only [hErr] using hDiscSwap₀
  have hDisc :
      DiscAt T (pw ((1 : ℝ) - (δ : ℝ) / 16)) (pw (x₀ : ℝ))
        (fun n => n ^ (-(19 : ℝ) / 20)) := by
    have h := (DiscAt.swap_iff T (pw (x₀ : ℝ)) (pw (y : ℝ))
      (fun n => n ^ (-(19 : ℝ) / 20))).mp hDiscSwap
    simpa only [hy_cast] using h
  have hAvailQ : AvL T (1 / 100 : ℚ) (1 / 100 : ℚ) (1 / 200 : ℚ) :=
    hZero (1 / 100 : ℚ) (1 / 100 : ℚ) (1 / 200 : ℚ)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have hAvail :
      AvL T ((1 / 100 : ℚ) : ℝ) ((1 / 100 : ℚ) : ℝ) ((1 / 200 : ℚ) : ℝ) := by
    simpa using hAvailQ
  exact ⟨x₀, hx₀, hx₀1, hDisc, hAvail⟩

/-- P11.1c (11:9–394): the complete one-shot cube embedding for the linear-budget jump.

The proof lane for this node expands the P11.1-menu, P11.1a/b, L11.2, L11.3, and P11.1d1–d3 contracts;
the Ramsey-binomial estimate is requested in `Needs.lean` as X-RamseyBinom.
-/
theorem linear_jump_embedding_core (δ x₀ h₀ : ℚ) (κ : ℝ)
    (hδ : 0 < δ) (hδ1 : (δ : ℝ) < 1 / 20000)
    (hx₀ : 0 < x₀) (hx₀1 : x₀ < 1)
    (hh₀ : 0 < h₀) (hh₀1 : h₀ < 1 / 100) (hκ : 0 < κ) :
    ∃ n₀ : ℕ, ∃ C₀ : ℝ, ∀ n N (E : Fin N → Fin N → Prop) (X Y : Finset (Fin N)),
      LargeAt n₀ C₀ n N →
      DiscOne E X Y ((n : ℝ) ^ ((1 : ℝ) - (δ : ℝ) / 16))
        ((n : ℝ) ^ (x₀ : ℝ)) ((n : ℝ) ^ (-(19 : ℝ) / 20)) →
      (∀ (G : Colour) A B, A ⊆ X → B ⊆ Y →
        (A, B) ∉ PCluster G ((1 / 100 : ℚ) : ℝ) (δ : ℝ) n N E) →
      (∀ (G : Colour) A B, A ⊆ Y → B ⊆ X →
        (A, B) ∉ PCluster G ((1 / 100 : ℚ) : ℝ) (δ : ℝ) n N (transposeRel E)) →
      AvailableAt κ
        (PBias (pw ((1 / 100 : ℚ) : ℝ)) (lw ((1 / 100 : ℚ) : ℝ)) (h₀ : ℝ)).toPatch
        n N E X Y →
      CubeAt n N E := by
  sorry

end HypercubeRamsey.S11
