import HypercubeRamsey.S10.Split_opus_s10_tagged_sol_s10_d2_tilt

namespace HypercubeRamsey.Lane_sol_s10_d2

open Classical OAI.HypercubeRamsey HypercubeRamsey.S10 Filter
open scoped BigOperators

theorem forall_list_indices {I : Type*} [DecidableEq I] (L : Finset I) (f : I → Prop) :
    (∀ b : Fin L.card, f (L.equivFin.symm b).1) ↔ ∀ c ∈ L, f c := by
  constructor
  · intro h c hc
    simpa using h (L.equivFin ⟨c, hc⟩)
  · intro h b
    exact h _ (L.equivFin.symm b).2

/-- Enumeration of a finite ID set preserves its common hit set. -/
theorem hitSet_equivFin {I : Type*} [DecidableEq I] {N k : ℕ}
    (E : Fin N → Fin N → Prop) (G : Colour) (L : Finset I) (W : I → Fin k → Fin N) :
    fixedListHitSet E G (fun b : Fin L.card => W (L.equivFin.symm b).1) =
      Finset.univ.filter (fun y => ∀ c ∈ L, ∀ i, Hits E G (W c i) y) := by
  classical
  ext y
  simp only [fixedListHitSet, Finset.mem_filter, Finset.mem_univ, true_and]
  exact forall_list_indices L (fun c => ∀ i : Fin k, Hits E G (W c i) y)

/-- Enumeration preserves deletion of one tuple ID. -/
theorem hitSetWithout_equivFin {I : Type*} [DecidableEq I] {N k : ℕ}
    (E : Fin N → Fin N → Prop) (G : Colour) (L : Finset I) (W : I → Fin k → Fin N)
    (d : Fin L.card) :
    fixedListHitSetWithout E G (fun b : Fin L.card => W (L.equivFin.symm b).1) d =
      Finset.univ.filter (fun y => ∀ c ∈ L, c ≠ (L.equivFin.symm d).1 →
        ∀ i, Hits E G (W c i) y) := by
  classical
  have heq (b : Fin L.card) : (L.equivFin.symm b).1 = (L.equivFin.symm d).1 ↔ b = d := by
    constructor
    · intro h
      exact L.equivFin.symm.injective (Subtype.ext h)
    · intro h
      rw [h]
  ext y
  simp only [fixedListHitSetWithout, Finset.mem_filter, Finset.mem_univ, true_and]
  constructor
  · intro h c hc hcd i
    let b := L.equivFin ⟨c, hc⟩
    have hb : b ≠ d := by
      intro hbd
      apply hcd
      have hval := congrArg (fun b : Fin L.card => (L.equivFin.symm b).1) hbd
      simpa [b] using hval
    simpa [b] using h b hb i
  · intro h b hbd i
    exact h _ (L.equivFin.symm b).2 (fun hc => hbd ((heq b).mp hc)) i

end HypercubeRamsey.Lane_sol_s10_d2
