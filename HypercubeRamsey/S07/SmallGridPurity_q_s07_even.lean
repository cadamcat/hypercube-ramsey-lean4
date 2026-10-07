import HypercubeRamsey.S07.Support
import HypercubeRamsey.S07.Experiment

set_option maxHeartbeats 1000000

namespace HypercubeRamsey.S07

open Classical
open OAI.HypercubeRamsey
open scoped BigOperators

theorem bind_pr_eq {α β : Type*} [Fintype α] [Fintype β]
    (P : FinProb α) (K : α → FinProb β) (A : α → β → Prop) :
    (FinProb.bind P K).pr (fun ab => A ab.1 ab.2) =
      ∑ a, P.w a * (K a).pr (A a) := by
  classical
  simp only [FinProb.pr, FinProb.bind, Fintype.sum_prod_type]
  apply Finset.sum_congr rfl
  intro a ha
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro b hb
  by_cases h : A a b <;> simp [h] <;> ring

theorem pr_const {α : Type*} [Fintype α] (P : FinProb α) (A : Prop) :
    P.pr (fun _ => A) = if A then 1 else 0 := by
  classical
  by_cases h : A
  · simp [FinProb.pr, h, P.sum_eq_one]
  · simp [FinProb.pr, h]

theorem pr_as_weight_sum {α : Type*} [Fintype α] (P : FinProb α) (A : α → Prop) :
    P.pr A = ∑ x, P.w x * (if A x then 1 else 0) := by
  classical
  unfold FinProb.pr
  apply Finset.sum_congr rfl
  intro x hx
  by_cases h : A x <;> simp [h]

theorem condOr_weight_support {α : Type*} [Fintype α]
    (P : FinProb α) (A : α → Prop) (hA : 0 < P.pr A) {x : α}
    (hx : (condOr P A).w x ≠ 0) : A x := by
  classical
  simp only [condOr, dif_pos hA, FinProb.cond] at hx
  by_contra hnot
  simp [hnot] at hx

theorem condOr_pr_not {α : Type*} [Fintype α]
    (P : FinProb α) (A : α → Prop) (hA : 0 < P.pr A) :
    (condOr P A).pr (fun x => ¬ A x) = 0 := by
  classical
  unfold FinProb.pr
  apply Finset.sum_eq_zero
  intro x hx
  by_cases h : A x
  · simp [h]
  · simp [condOr, hA, h, FinProb.cond]

theorem pr_mono {α : Type*} [Fintype α] (P : FinProb α) {A B : α → Prop}
    (hAB : ∀ x, A x → B x) : P.pr A ≤ P.pr B := by
  classical
  unfold FinProb.pr
  apply Finset.sum_le_sum
  intro x hx
  by_cases hA : A x
  · have hB := hAB x hA
    simp [hA, hB]
  · by_cases hB : B x
    · simp [hA, hB, P.nonneg x]
    · simp [hA, hB]

theorem pr_compl {α : Type*} [Fintype α] (P : FinProb α) (A : α → Prop) :
    P.pr A + P.pr (fun x => ¬ A x) = 1 := by
  classical
  letI : DecidablePred A := fun x => Classical.propDecidable (A x)
  letI : DecidablePred (fun x => ¬ A x) := fun x => Classical.propDecidable (¬ A x)
  rw [pr_as_weight_sum P A, pr_as_weight_sum P (fun x => ¬ A x)]
  rw [← Finset.sum_add_distrib]
  calc
    (∑ x, ((P.w x * (if A x then 1 else 0)) +
      P.w x * (if ¬ A x then 1 else 0))) =
        ∑ x, P.w x := by
      apply Finset.sum_congr rfl
      intro x hx
      by_cases h : A x <;> simp [h]
    _ = 1 := P.sum_eq_one


end HypercubeRamsey.S07
