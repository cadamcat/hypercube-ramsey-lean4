import HypercubeRamsey.S05.Centres_sol_s05_k1

namespace HypercubeRamsey.Lane_sol_s05_k1

open Classical
open scoped BigOperators

noncomputable section
set_option maxHeartbeats 400000

variable {I : Type*} [Fintype I] [DecidableEq I]
variable {A B : I → Type*} [∀ i, Fintype (A i)] [∀ i, Fintype (B i)]

theorem pi_prod_expect_mul (P : ∀ i, FinProb (A i)) (Q : ∀ i, FinProb (B i))
    (f : (∀ i, A i) → ℝ) (g : (∀ i, B i) → ℝ) :
    (FinProb.pi (fun i => (P i).prod (Q i))).expect
      (fun ω => f (fun i => (ω i).1) * g (fun i => (ω i).2)) =
        (FinProb.pi P).expect f * (FinProb.pi Q).expect g := by
  let e : (∀ i, A i × B i) ≃ ((∀ i, A i) × (∀ i, B i)) :=
    { toFun := fun ω => (fun i => (ω i).1, fun i => (ω i).2)
      invFun := fun ω i => (ω.1 i, ω.2 i)
      left_inv := by intro ω; funext i; exact Prod.eta (ω i)
      right_inv := by intro ω; rcases ω with ⟨a, b⟩; rfl }
  change (∑ ω : (∀ i, A i × B i), (∏ i, (P i).w (ω i).1 * (Q i).w (ω i).2) *
    (f (fun i => (ω i).1) * g (fun i => (ω i).2))) = _
  rw [← Equiv.sum_comp e.symm]
  rw [Fintype.sum_prod_type]
  calc
    _ = ∑ a, ∑ b, ((∏ i, (P i).w (a i)) * f a) * ((∏ i, (Q i).w (b i)) * g b) := by
      apply Finset.sum_congr rfl
      intro a _
      apply Finset.sum_congr rfl
      intro b _
      change (∏ i, (P i).w (a i) * (Q i).w (b i)) * (f a * g b) = _
      rw [Finset.prod_mul_distrib]
      ring
    _ = _ := by
      unfold FinProb.expect FinProb.pi
      rw [Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro a _
      rw [Finset.mul_sum]

theorem pi_prod_expect_snd (P : ∀ i, FinProb (A i)) (Q : ∀ i, FinProb (B i))
    (g : (∀ i, B i) → ℝ) :
    (FinProb.pi (fun i => (P i).prod (Q i))).expect (fun ω => g (fun i => (ω i).2)) =
      (FinProb.pi Q).expect g := by
  simpa only [one_mul, FinProb.expect_const] using pi_prod_expect_mul P Q (fun _ => 1) g

theorem pi_prod_pr_and (P : ∀ i, FinProb (A i)) (Q : ∀ i, FinProb (B i))
    (F : (∀ i, A i) → Prop) (G : (∀ i, B i) → Prop) :
    (FinProb.pi (fun i => (P i).prod (Q i))).pr
      (fun ω => F (fun i => (ω i).1) ∧ G (fun i => (ω i).2)) =
        (FinProb.pi P).pr F * (FinProb.pi Q).pr G := by
  have h := pi_prod_expect_mul P Q (fun a => if F a then 1 else 0) (fun b => if G b then 1 else 0)
  unfold FinProb.expect at h
  unfold FinProb.pr
  convert h using 1
  · apply Finset.sum_congr rfl
    intro ω _
    by_cases hf : F (fun i => (ω i).1) <;> by_cases hg : G (fun i => (ω i).2) <;> simp [hf, hg]
  · congr 1
    · apply Finset.sum_congr rfl
      intro ω _
      by_cases hf : F ω <;> simp [hf]
    · apply Finset.sum_congr rfl
      intro ω _
      by_cases hg : G ω <;> simp [hg]

theorem pi_cylinder_pr (P : ∀ i, FinProb (A i)) (s : Finset I) (a : ∀ i, A i) :
    (FinProb.pi P).pr (fun ω => ∀ i ∈ s, ω i = a i) = ∏ i ∈ s, (P i).w (a i) := by
  let a' := fun i : {i // i ∈ s} => a i.1
  have hm := FinProb.pi_marginal P s a'
  calc
    _ = (FinProb.map (FinProb.pi P) (fun ω (i : {i // i ∈ s}) => ω i.1)).w a' := by
      unfold FinProb.pr FinProb.map
      apply Finset.sum_congr rfl
      intro ω _
      have he : (∀ i ∈ s, ω i = a i) ↔ (fun i : {i // i ∈ s} => ω i.1) = a' := by
        constructor
        · intro h
          exact funext fun i => h i.1 i.2
        · intro h i hi
          exact congrFun h ⟨i, hi⟩
      by_cases hc : ∀ i ∈ s, ω i = a i
      · have heq := he.mp hc
        split_ifs <;> first | rfl | contradiction
      · have hn := mt he.mpr hc
        split_ifs <;> first | rfl | contradiction
    _ = (FinProb.pi (fun i : {i // i ∈ s} => P i.1)).w a' := hm
    _ = _ := by
      change (∏ i : {i // i ∈ s}, (P i.1).w (a i.1)) = _
      exact Finset.prod_coe_sort s (fun i => (P i).w (a i))

end
end HypercubeRamsey.Lane_sol_s05_k1
