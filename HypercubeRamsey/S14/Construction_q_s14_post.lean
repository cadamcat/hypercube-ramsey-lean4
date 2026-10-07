import HypercubeRamsey.Framework.FinProb
import HypercubeRamsey.PartC.Core

/-!
Finite product reindexing lemmas for the Section 14 posterior calculations.
-/

namespace HypercubeRamsey.Lane_q_s14_post

open scoped BigOperators

theorem sum_pi_splitAt {ι : Type*} [Fintype ι] [DecidableEq ι]
    {α : ι → Type*} [∀ i, Fintype (α i)]
    (P : ∀ i, α i → ℝ) (i₀ : ι) (f : (∀ i, α i) → ℝ) :
    (∑ w, (∏ i, P i (w i)) * f w) =
      ∑ a : α i₀, P i₀ a *
        ∑ r : ∀ i : {j // j ≠ i₀}, α i,
          (∏ i : {j // j ≠ i₀}, P i.1 (r i)) *
            f ((Equiv.piSplitAt i₀ α).symm (a, r)) := by
  classical
  let e := Equiv.piSplitAt i₀ α
  have hprod (a : α i₀) (r : ∀ i : {j // j ≠ i₀}, α i) :
      (∏ i, P i ((e.symm (a, r)) i)) =
        P i₀ a * ∏ i : {j // j ≠ i₀}, P i.1 (r i) := by
    letI : Fintype {j : ι // j = i₀} :=
      Fintype.subtype (Finset.univ.filter fun j : ι => j = i₀) (by intro j; simp)
    letI : Fintype {j : ι // ¬ j = i₀} :=
      Fintype.subtype (Finset.univ.filter fun j : ι => ¬ j = i₀) (by intro j; simp)
    calc
      _ = (∏ i : {j // j = i₀}, P i.1 ((e.symm (a, r)) i.1)) *
          ∏ i : {j // ¬ j = i₀}, P i.1 ((e.symm (a, r)) i.1) :=
            (Fintype.prod_subtype_mul_prod_subtype (fun i : ι => i = i₀)
              (fun i => P i ((e.symm (a, r)) i))).symm
      _ = P i₀ a * ∏ i : {j // j ≠ i₀}, P i.1 (r i) := by
          have hone :
              (∏ i : {j // j = i₀}, P i.1 ((e.symm (a, r)) i.1)) = P i₀ a := by
            rw [Fintype.prod_subsingleton _ ⟨i₀, rfl⟩]
            simp [e, Equiv.piSplitAt]
          have hrest :
              (∏ i : {j // ¬ j = i₀}, P i.1 ((e.symm (a, r)) i.1)) =
                ∏ i : {j // j ≠ i₀}, P i.1 (r i) := by
            apply Finset.prod_congr rfl
            intro i hi
            simp [e, Equiv.piSplitAt, Equiv.symm, i.2]
          rw [hone, hrest]
  calc
    _ = ∑ w, (∏ i, P i (w i)) * f w := rfl
    _ = ∑ z : α i₀ × (∀ i : {j // j ≠ i₀}, α i),
        (∏ i, P i ((e.symm z) i)) * f (e.symm z) :=
          (Equiv.sum_comp e.symm (fun w => (∏ i, P i (w i)) * f w)).symm
    _ = ∑ z : α i₀ × (∀ i : {j // j ≠ i₀}, α i),
        (P i₀ z.1 * ∏ i : {j // j ≠ i₀}, P i.1 (z.2 i)) * f (e.symm z) := by
          apply Finset.sum_congr rfl
          intro z hz
          rcases z with ⟨a, r⟩
          rw [hprod]
    _ = ∑ a : α i₀, ∑ r : ∀ i : {j // j ≠ i₀}, α i,
        (P i₀ a * ∏ i : {j // j ≠ i₀}, P i.1 (r i)) * f (e.symm (a, r)) :=
          Fintype.sum_prod_type _
    _ = ∑ a : α i₀, P i₀ a *
        ∑ r : ∀ i : {j // j ≠ i₀}, α i,
          (∏ i : {j // j ≠ i₀}, P i.1 (r i)) * f (e.symm (a, r)) := by
          apply Finset.sum_congr rfl
          intro a ha
          rw [Finset.mul_sum]
          apply Finset.sum_congr rfl
          intro r hr
          ring

theorem expect_comp_eq_sum_pr {α β : Type*} [Fintype α] [Fintype β]
    (P : FinLaw α) (f : α → β) (g : β → ℝ) :
    P.E (fun a => g (f a)) = ∑ b, P.pr (fun a => f a = b) * g b := by
  classical
  unfold FinLaw.E FinLaw.pr
  calc
    _ = ∑ a, ∑ b, (if f a = b then P.w a * g b else 0) := by
      apply Finset.sum_congr rfl
      intro a ha
      simp
    _ = ∑ b, ∑ a, (if f a = b then P.w a * g b else 0) := Finset.sum_comm
    _ = ∑ b, (∑ a, if f a = b then P.w a else 0) * g b := by
      apply Finset.sum_congr rfl
      intro b hb
      rw [Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro a ha
      split_ifs <;> simp [*]

theorem sum_pr_eq_one {α β : Type*} [Fintype α] [Fintype β]
    (P : FinLaw α) (f : α → β) :
    ∑ b, P.pr (fun a => f a = b) = 1 := by
  classical
  unfold FinLaw.pr
  rw [Finset.sum_comm]
  calc
    _ = ∑ a, P.w a := by
      apply Finset.sum_congr rfl
      intro a ha
      simp
    _ = 1 := P.sum_one

end HypercubeRamsey.Lane_q_s14_post
