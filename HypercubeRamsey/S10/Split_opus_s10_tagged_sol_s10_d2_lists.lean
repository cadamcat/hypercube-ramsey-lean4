import HypercubeRamsey.S10.Split_opus_s10_tagged_sol_s10_d2

namespace HypercubeRamsey.Lane_sol_s10_d2

open Classical OAI.HypercubeRamsey HypercubeRamsey.S10 Filter
open scoped BigOperators

/-- Bounded-size lists from a candidate set have the padded-tuple count bound. -/
theorem bounded_family_card {I : Type*} [Fintype I] [DecidableEq I]
    (C : Finset I) (F : Finset (Finset I)) (R : ℕ)
    (hsub : ∀ L ∈ F, L ⊆ C) (hsize : ∀ L ∈ F, L.card ≤ R) :
    F.card ≤ (C.card + 1) ^ R := by
  classical
  let code (L : Finset I) : Finset {i // i ∈ C} := C.attach.filter fun i => i.1 ∈ L
  have himage (L : Finset I) (hL : L ∈ F) : (code L).image Subtype.val = L := by
    ext i
    constructor
    · intro hi
      obtain ⟨j, hj, he⟩ := Finset.mem_image.mp hi
      have hji := (Finset.mem_filter.mp hj).2
      simpa [he] using hji
    · intro hi
      apply Finset.mem_image.mpr
      refine ⟨⟨i, hsub L hL hi⟩, ?_, rfl⟩
      exact Finset.mem_filter.mpr ⟨Finset.mem_attach _ _, hi⟩
  have hc (L : Finset I) : (code L).card ≤ L.card := by
    apply Finset.card_le_card_of_injOn Subtype.val
    · intro i hi
      exact (Finset.mem_filter.mp hi).2
    · exact Subtype.val_injective.injOn
  let Target : Finset (Finset {i // i ∈ C}) := Finset.univ.filter fun L => L.card ≤ R
  have hm : ∀ L ∈ F, code L ∈ Target := by
    intro L hL
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, (hc L).trans (hsize L hL)⟩
  have hi : (F : Set (Finset I)).InjOn code := by
    intro L hL L' hL' he
    have he' := congrArg (fun K : Finset {i // i ∈ C} => K.image Subtype.val) he
    rwa [himage L hL, himage L' hL'] at he'
  calc
    F.card ≤ Target.card := Finset.card_le_card_of_injOn code hm hi
    _ ≤ (C.card + 1) ^ R := p10_1kCandidateListFamily_card_le C R

/-- Enumerate an arbitrary finite menu before applying the disjoint-failure bound. -/
theorem finite_family_disjoint_bad_probability {I : Type*} [Fintype I] [DecidableEq I]
    {N k : ℕ} (μ : I → Law N) (Menu : Finset (Finset I)) (n : ℕ)
    (failed : Finset I → (I → Fin k → Fin N) → Prop)
    (hdep : ∀ L ∈ Menu, ∀ W W', (∀ id ∈ L, W id = W' id) → (failed L W ↔ failed L W'))
    (ε : ℝ) (hε : 0 ≤ ε)
    (hprob : ∀ L ∈ Menu, (p10_1kIdTupleArrayLaw μ).pr (failed L) ≤ ε) :
    (p10_1kIdTupleArrayLaw μ).pr (fun W => ∃ f : Fin n → Finset I,
      (∀ i, f i ∈ Menu) ∧ (∀ i j, i ≠ j → Disjoint (f i) (f j)) ∧ ∀ i, failed (f i) W) ≤
      (Menu.card : ℝ) ^ n * ε ^ n := by
  classical
  let S : Fin Menu.card → Finset I := fun i => (Menu.equivFin.symm i).1
  have hb := disjoint_failure_union_bound μ n Menu.card S (fun i => failed (S i))
    (fun i => hdep (S i) (Menu.equivFin.symm i).2) ε hε
    (fun i => hprob (S i) (Menu.equivFin.symm i).2)
  apply le_trans _ hb
  apply p10_1k_FinProb_pr_mono
  rintro W ⟨f, hmem, hd, hf⟩
  let choose : Fin n → Fin Menu.card := fun i => Menu.equivFin ⟨f i, hmem i⟩
  have he (i : Fin n) : S (choose i) = f i := by simp [S, choose]
  refine ⟨choose, ?_, ?_⟩
  · intro i j hij
    simpa only [he] using hd i j hij
  · intro i
    simpa only [he] using hf i

end HypercubeRamsey.Lane_sol_s10_d2
