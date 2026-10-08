import HypercubeRamsey.Framework.FinProbLemmas
import HypercubeRamsey.S10.Split_opus_s10_tagged_sol_s10_d56

namespace HypercubeRamsey.Lane_sol_s10_d56

open Classical
open scoped BigOperators

/-- Integrate independent data and selection fields in their sampling order. -/
theorem prod_expect {α β : Type*} [Fintype α] [Fintype β]
    (P : FinProb α) (Q : FinProb β) (f : α → β → ℝ) :
    (P.prod Q).expect (fun ω => f ω.1 ω.2) = P.expect (fun a => Q.expect (f a)) := by
  change (FinProb.bind P (fun _ => Q)).expect (fun ω => f ω.1 ω.2) = _
  exact FinProb.bind_expect P (fun _ => Q) f

/-- Enumerating a realized list replaces its selection event by a tuple-independent weight. -/
theorem conditional_choice_expect_le {α β γ : Type*}
    [Fintype α] [Fintype β] [DecidableEq γ]
    (P : FinProb α) (Q : FinProb β) (F : Finset γ)
    (choice : α → β → γ) (gate : α → β → Prop) (row : α → γ → ℝ)
    (weight : γ → ℝ)
    (hrow : ∀ a, ∀ c ∈ F, 0 ≤ row a c)
    (hsupport : ∀ a b, gate a b → choice a b ∈ F)
    (hweight : ∀ a, ∀ c ∈ F, Q.pr (fun b => gate a b ∧ choice a b = c) ≤ weight c) :
    (P.prod Q).expect (fun ω => if gate ω.1 ω.2 then row ω.1 (choice ω.1 ω.2) else 0) ≤
      ∑ c ∈ F, weight c * P.expect (fun a => row a c) := by
  classical
  have hpoint (a : α) (b : β) :
      (if gate a b then row a (choice a b) else 0) =
        ∑ c ∈ F, if gate a b ∧ choice a b = c then row a c else 0 := by
    by_cases hg : gate a b
    · rw [ite_eq_left hg]
      symm
      rw [Finset.sum_eq_single (choice a b)]
      · simp [hg]
      · intro c hc hne
        simp [Ne.symm hne]
      · intro hn
        exact False.elim (hn (hsupport a b hg))
    · simp [hg]
  have hcond (a : α) :
      Q.expect (fun b => if gate a b then row a (choice a b) else 0) ≤
        ∑ c ∈ F, weight c * row a c := by
    calc
      _ = ∑ c ∈ F, Q.pr (fun b => gate a b ∧ choice a b = c) * row a c := by
        simp_rw [hpoint]
        unfold FinProb.expect FinProb.pr
        simp_rw [Finset.mul_sum]
        rw [Finset.sum_comm]
        apply Finset.sum_congr rfl
        intro c hc
        rw [Finset.sum_mul]
        apply Finset.sum_congr rfl
        intro b hb
        by_cases h : gate a b ∧ choice a b = c <;> simp [h]
      _ ≤ _ := Finset.sum_le_sum fun c hc =>
        mul_le_mul_of_nonneg_right (hweight a c hc) (hrow a c hc)
  rw [prod_expect P Q (fun a b => if gate a b then row a (choice a b) else 0)]
  apply (FinProb.expect_mono P hcond).trans_eq
  unfold FinProb.expect
  simp_rw [Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro c hc
  apply Finset.sum_congr rfl
  intro a ha
  ring

end HypercubeRamsey.Lane_sol_s10_d56
