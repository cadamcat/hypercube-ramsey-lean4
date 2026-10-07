import HypercubeRamsey.S16.Comparisons_q_s16_comp2

namespace HypercubeRamsey.S18.Lane_sol_d18l_row

open Classical
open S16
open scoped BigOperators

/-- A test of injectively selected coordinates has the selected product law. -/
theorem pi_injection_expect {I J Ω : Type*} [Fintype I] [DecidableEq I]
    [Fintype J] [DecidableEq J] [Fintype Ω]
    (law : I → FinLaw Ω) (f : J → I) (hf : Function.Injective f)
    (Φ : (J → Ω) → ℝ) :
    (FinLaw.pi law).E (fun ω => Φ (fun j => ω (f j))) =
      (FinLaw.pi (fun j => law (f j))).E Φ := by
  let S := Finset.univ.image f
  let f' : J → {i : I // i ∈ S} := fun j =>
    ⟨f j, Finset.mem_image.mpr ⟨j, Finset.mem_univ _, rfl⟩⟩
  have hbij : Function.Bijective f' := by
    constructor
    · intro a b h
      exact hf (congrArg Subtype.val h)
    · intro i
      obtain ⟨j, _, hj⟩ := Finset.mem_image.mp i.2
      exact ⟨j, Subtype.ext hj⟩
  let e := Equiv.ofBijective f' hbij
  let eval : ({i : I // i ∈ S} → Ω) ≃ (J → Ω) :=
    Equiv.arrowCongr e.symm (Equiv.refl Ω)
  let test (ω : {i : I // i ∈ S} → Ω) := Φ (eval ω)
  have hproject := Lane_q_s16_comp2.pi_subtype_expect law S test
  change (FinLaw.pi law).E (fun ω => test (fun i => ω i.1)) = _
  rw [hproject]
  unfold FinLaw.E FinLaw.pi
  rw [← Equiv.sum_comp eval.symm]
  apply Finset.sum_congr rfl
  intro ω _
  have hprod : (∏ i : {i : I // i ∈ S}, (law i.1).w (eval.symm ω i)) =
      ∏ j : J, (law (f j)).w (ω j) := by
    rw [← Equiv.prod_comp e]
    simp [eval, e, f']
  dsimp only
  rw [hprod]
  simp only [test, Equiv.apply_symm_apply]

end HypercubeRamsey.S18.Lane_sol_d18l_row
