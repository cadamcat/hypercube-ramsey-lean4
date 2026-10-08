import HypercubeRamsey.Framework.FinProbLemmas
import HypercubeRamsey.S10.Split_opus_s10_tagged_sol_s10_d56

namespace HypercubeRamsey.Lane_sol_s10_d56

open Classical
open scoped BigOperators

/-- Reindexing independent coordinates preserves their product expectation. -/
theorem pi_equiv_expect {ι κ Ω : Type*}
    [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ] [Fintype Ω]
    (e : ι ≃ κ) (P : ι → FinProb Ω) (f : (κ → Ω) → ℝ) :
    (FinProb.pi P).expect (fun ω => f (fun k => ω (e.symm k))) =
      (FinProb.pi (fun k => P (e.symm k))).expect f := by
  classical
  let ef : (κ → Ω) ≃ (ι → Ω) :=
    { toFun := fun ω i => ω (e i)
      invFun := fun ω k => ω (e.symm k)
      left_inv := by intro ω; funext k; simp
      right_inv := by intro ω; funext i; simp }
  unfold FinProb.expect FinProb.pi
  rw [← Equiv.sum_comp ef]
  apply Finset.sum_congr rfl
  intro ω hω
  change (∏ i, (P i).w (ω (e i))) * f (fun k => ω (e (e.symm k))) =
    (∏ k, (P (e.symm k)).w (ω k)) * f ω
  have hprod : (∏ i, (P i).w (ω (e i))) =
      ∏ k, (P (e.symm k)).w (ω k) := by
    apply Fintype.prod_equiv e
    intro i
    simp
  simp [hprod]

/-- Distinct queried slices have exactly their independent product marginal. -/
theorem pi_injective_expect {ι κ Ω : Type*}
    [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ] [Fintype Ω]
    (P : ι → FinProb Ω) (e : κ → ι) (he : Function.Injective e)
    (f : (κ → Ω) → ℝ) :
    (FinProb.pi P).expect (fun ω => f (fun k => ω (e k))) =
      (FinProb.pi (fun k => P (e k))).expect f := by
  classical
  let S : Finset ι := Finset.univ.image e
  let eS : κ ≃ {i // i ∈ S} := Equiv.ofBijective
    (fun k => ⟨e k, Finset.mem_image.mpr ⟨k, Finset.mem_univ k, rfl⟩⟩)
    ⟨by intro a b hab; exact he (congrArg Subtype.val hab), by
      intro i
      obtain ⟨k, hk, heq⟩ := Finset.mem_image.mp i.2
      exact ⟨k, Subtype.ext heq⟩⟩
  have hm := FinProb.pi_marginal_expect P S
    (fun ω : {i // i ∈ S} → Ω => f (fun k => ω (eS k)))
  have hr := pi_equiv_expect eS.symm (fun i : {i // i ∈ S} => P i.1) f
  exact hm.trans hr

/-- Events at distinct queried coordinates factor even if the rest of the field is unused. -/
theorem pi_injective_pr_all {ι κ Ω : Type*}
    [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ] [Fintype Ω]
    (P : ι → FinProb Ω) (e : κ → ι) (he : Function.Injective e)
    (F : κ → Ω → Prop) :
    (FinProb.pi P).pr (fun ω => ∀ k, F k (ω (e k))) = ∏ k, (P (e k)).pr (F k) := by
  classical
  have hpr (k : κ) : (P (e k)).pr (F k) =
      (P (e k)).expect (fun a => if F k a then (1 : ℝ) else 0) := by
    unfold FinProb.pr FinProb.expect
    apply Finset.sum_congr rfl
    intro a ha
    split_ifs with h <;> simp [h]
  have hind (ω : κ → Ω) :
      (if ∀ k, F k (ω k) then (1 : ℝ) else 0) =
        ∏ k, if F k (ω k) then (1 : ℝ) else 0 := by
    by_cases h : ∀ k, F k (ω k)
    · simp [h]
    · obtain ⟨k, hk⟩ := not_forall.mp h
      rw [ite_eq_right h]
      symm
      exact Finset.prod_eq_zero (Finset.mem_univ k) (ite_eq_right hk)
  have hstart : (FinProb.pi P).pr (fun ω => ∀ k, F k (ω (e k))) =
      (FinProb.pi P).expect (fun ω => if ∀ k, F k (ω (e k)) then (1 : ℝ) else 0) := by
    unfold FinProb.pr FinProb.expect
    apply Finset.sum_congr rfl
    intro ω hω
    split_ifs with h <;> simp [h]
  rw [hstart, pi_injective_expect P e he
    (fun ω : κ → Ω => if ∀ k, F k (ω k) then (1 : ℝ) else 0)]
  simp_rw [hind]
  rw [pi_expect_product (fun k => P (e k))
    (fun k a => if F k a then (1 : ℝ) else 0)]
  simp_rw [← hpr]


/-- Projecting one coordinate of a product field gives its original marginal law. -/
theorem pi_expect_eval {ι Ω : Type*} [Fintype ι] [DecidableEq ι] [Fintype Ω]
    (P : ι → FinProb Ω) (i : ι) (f : Ω → ℝ) :
    (FinProb.pi P).expect (fun ω => f (ω i)) = (P i).expect f := by
  classical
  have he : Function.Injective (fun _ : Unit => i) := fun _ _ _ => Subsingleton.elim _ _
  rw [pi_injective_expect P (fun _ : Unit => i) he (fun ω => f (ω ()))]
  let e : Ω ≃ (Unit → Ω) :=
    { toFun := fun x _ => x
      invFun := fun ω => ω ()
      left_inv := fun _ => rfl
      right_inv := by intro ω; funext u; cases u; rfl }
  unfold FinProb.expect
  rw [← Equiv.sum_comp e]
  apply Finset.sum_congr rfl
  intro x hx
  change (∏ _ : Unit, (P i).w x) * f x = (P i).w x * f x
  simp

end HypercubeRamsey.Lane_sol_s10_d56
