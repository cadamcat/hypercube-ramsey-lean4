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

theorem sum_diagonal_eq_base {α : Type*} [Fintype α]
    (P : FinProb α) (g : α → α → ℝ)
    (hg : ∀ a a' b, g a b = g a' b) :
    (∑ a, P.w a * g a a) =
      ∑ b, P.w b * ∑ a, P.w a * g b a := by
  classical
  have hconst (a : α) : ∑ b, P.w b * g a a = g a a := by
    calc
      _ = (∑ b, P.w b) * g a a := by rw [← Finset.sum_mul]
      _ = g a a := by rw [P.sum_eq_one]; ring
  calc
    _ = ∑ a, P.w a * ∑ b, P.w b * g a a := by
      apply Finset.sum_congr rfl
      intro a ha
      rw [hconst]
    _ = ∑ a, P.w a * ∑ b, P.w b * g b a := by
      apply Finset.sum_congr rfl
      intro a ha
      congr 1
      apply Finset.sum_congr rfl
      intro b hb
      rw [hg b a a]
    _ = ∑ b, P.w b * ∑ a, P.w a * g b a := by
      calc
        _ = ∑ a, ∑ b, P.w a * (P.w b * g b a) := by
          apply Finset.sum_congr rfl
          intro a ha
          rw [Finset.mul_sum]
        _ = ∑ b, ∑ a, P.w b * (P.w a * g b a) := by
          rw [Finset.sum_comm]
          apply Finset.sum_congr rfl
          intro b hb
          apply Finset.sum_congr rfl
          intro a ha
          ring
        _ = ∑ b, P.w b * ∑ a, P.w a * g b a := by
          apply Finset.sum_congr rfl
          intro b hb
          rw [Finset.mul_sum]

theorem expect_bind {α β : Type*} [Fintype α] [Fintype β]
    (P : FinLaw α) (K : α → FinLaw β) (f : α × β → ℝ) :
    (FinLaw.bind P K).E f = P.E (fun a => (K a).E (fun b => f (a, b))) := by
  classical
  unfold FinLaw.E FinLaw.bind
  rw [Fintype.sum_prod_type]
  apply Finset.sum_congr rfl
  intro a ha
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro b hb
  ring

theorem finLaw_nonempty {α : Type*} [Fintype α] (P : FinLaw α) : Nonempty α := by
  classical
  by_contra h
  letI : IsEmpty α := ⟨fun a => h ⟨a⟩⟩
  have hsum := P.sum_one
  simp at hsum

theorem expect_swap {α β : Type*} [Fintype α] [Fintype β]
    (P : FinLaw α) (Q : FinLaw β) (f : α → β → ℝ) :
    P.E (fun a => Q.E (fun b => f a b)) =
      Q.E (fun b => P.E (fun a => f a b)) := by
  classical
  unfold FinLaw.E
  calc
    _ = ∑ a, ∑ b, P.w a * (Q.w b * f a b) := by
      apply Finset.sum_congr rfl
      intro a ha
      rw [Finset.mul_sum]
    _ = ∑ b, ∑ a, Q.w b * (P.w a * f a b) := by
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro b hb
      apply Finset.sum_congr rfl
      intro a ha
      ring
    _ = ∑ b, Q.w b * ∑ a, P.w a * f a b := by
      apply Finset.sum_congr rfl
      intro b hb
      rw [Finset.mul_sum]

end HypercubeRamsey.Lane_q_s14_post
