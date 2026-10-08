import HypercubeRamsey.S10.Split_opus_s10_tagged_sol_s10_d2

namespace HypercubeRamsey.Lane_sol_s10_d2

open Classical OAI.HypercubeRamsey HypercubeRamsey.S10 Filter
open scoped BigOperators

/-- Deleting IDs marked by a finite family loses at most the sum of its sizes. -/
theorem eligible_card_bound {I Q A : Type*} [DecidableEq I] [DecidableEq Q] [DecidableEq A]
    (B : Finset I) (Qs : Finset Q) (F : Q → Finset A) (tag : I → A)
    (hinj : Function.Injective tag) :
    B.card ≤ (B.filter fun i => ∀ q ∈ Qs, tag i ∉ F q).card + ∑ q ∈ Qs, (F q).card := by
  classical
  let E := B.filter fun i => ∀ q ∈ Qs, tag i ∉ F q
  let Bad := B.filter fun i => ¬ ∀ q ∈ Qs, tag i ∉ F q
  have hmap : ∀ i ∈ Bad, tag i ∈ Qs.biUnion F := by
    intro i hi
    have hb := (Finset.mem_filter.mp hi).2
    simp only [not_forall, Classical.not_imp, not_not] at hb
    obtain ⟨q, hq, hf⟩ := hb
    exact Finset.mem_biUnion.mpr ⟨q, hq, hf⟩
  have hbad : Bad.card ≤ ∑ q ∈ Qs, (F q).card := by
    calc
      Bad.card ≤ (Qs.biUnion F).card := Finset.card_le_card_of_injOn tag hmap hinj.injOn
      _ ≤ _ := Finset.card_biUnion_le
  have heq : B.card = E.card + Bad.card := by
    exact (Finset.card_filter_add_card_filter_not (s := B)
      (p := fun i => ∀ q ∈ Qs, tag i ∉ F q)).symm
  rw [heq]
  exact Nat.add_le_add_left hbad _

end HypercubeRamsey.Lane_sol_s10_d2
