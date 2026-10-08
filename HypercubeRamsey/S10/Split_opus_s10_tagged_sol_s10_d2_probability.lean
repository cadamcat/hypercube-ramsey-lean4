import HypercubeRamsey.S10.Split_opus_s10_tagged_sol_s10_d2

namespace HypercubeRamsey.Lane_sol_s10_d2

open Classical OAI.HypercubeRamsey HypercubeRamsey.S10 Filter
open scoped BigOperators

/-- Finite product expectations can be integrated in either coordinate. -/
theorem prod_expect {α β : Type*} [Fintype α] [Fintype β]
    (P : FinProb α) (Q : FinProb β) (f : α × β → ℝ) :
    (P.prod Q).expect f = P.expect (fun a => Q.expect (fun b => f (a, b))) := by
  unfold FinProb.expect FinProb.prod
  rw [Fintype.sum_prod_type]
  simp_rw [Finset.mul_sum, mul_assoc]

/-- Probability is the expectation of its indicator. -/
theorem pr_indicator {α : Type*} [Fintype α] (P : FinProb α) (A : α → Prop) :
    P.pr A = P.expect (fun a => if A a then 1 else 0) := by
  classical
  unfold FinProb.pr FinProb.expect
  apply Finset.sum_congr rfl
  intro a _
  by_cases h : A a <;> simp [h]

/-- Group an independent field indexed by pairs into independent fields on slices. -/
theorem pi_curry_expect {α β Ω : Type*} [Fintype α] [Fintype β] [Fintype Ω]
    [DecidableEq α] [DecidableEq β]
    (P : α × β → FinProb Ω) (f : (α → β → Ω) → ℝ) :
    (FinProb.pi P).expect (fun ω => f (fun a b => ω (a, b))) =
      (FinProb.pi (fun a => FinProb.pi (fun b => P (a, b)))).expect f := by
  classical
  let e : (α × β → Ω) ≃ (α → β → Ω) :=
    { toFun := fun ω a b => ω (a, b)
      invFun := fun ω ab => ω ab.1 ab.2
      left_inv := fun ω => by funext ab; cases ab; rfl
      right_inv := fun ω => by funext a b; rfl }
  unfold FinProb.expect
  apply Fintype.sum_equiv e
  intro ω
  change (∏ ab, (P ab).w (ω ab)) * f (e ω) =
    (∏ a, ∏ b, (P (a, b)).w (ω (a, b))) * f (e ω)
  rw [Fintype.prod_prod_type]

/-- The marginal at one coordinate is its original law. -/
theorem pi_coordinate_expect {α Ω : Type*} [Fintype α] [Fintype Ω]
    [DecidableEq α] (P : α → FinProb Ω) (a₀ : α) (f : Ω → ℝ) :
    (FinProb.pi P).expect (fun ω => f (ω a₀)) = (P a₀).expect f := by
  classical
  let S : Finset α := {a₀}
  let I := {a // a ∈ S}
  let i₀ : I := ⟨a₀, by simp [S]⟩
  letI : Unique I :=
    { default := i₀
      uniq := fun i => Subtype.ext (Finset.mem_singleton.mp i.2) }
  let e : (I → Ω) ≃ Ω :=
    { toFun := fun ω => ω i₀
      invFun := fun x _ => x
      left_inv := fun ω => by
        funext i
        have hi : i = i₀ := Subsingleton.elim _ _
        rw [hi]
      right_inv := fun _ => rfl }
  have hm := FinProb.pi_marginal_expect P S (fun ω => f (ω i₀))
  change (FinProb.pi P).expect (fun ω => f (ω a₀)) = _ at hm
  rw [hm]
  unfold FinProb.expect
  apply Fintype.sum_equiv e
  intro ω
  change (∏ i : I, (P i.1).w (ω i)) * f (ω i₀) = (P a₀).w (ω i₀) * f (ω i₀)
  simp only [Fintype.prod_unique]
  rfl

/-- The coordinate marginal statement for events. -/
theorem pi_coordinate_pr {α Ω : Type*} [Fintype α] [Fintype Ω]
    [DecidableEq α] (P : α → FinProb Ω) (a₀ : α) (A : Ω → Prop) :
    (FinProb.pi P).pr (fun ω => A (ω a₀)) = (P a₀).pr A := by
  rw [pr_indicator, pr_indicator]
  exact pi_coordinate_expect P a₀ (fun ω => if A ω then (1 : ℝ) else 0)

/-- Reconstruct a field from one coordinate and its complement. -/
def insertField {α Ω : Type*} [DecidableEq α] (a₀ : α) (x : Ω)
    (rest : {a : α // a ≠ a₀} → Ω) : α → Ω :=
  fun a => if h : a = a₀ then x else rest ⟨a, h⟩

/-- Separate one coordinate from the rest of an independent field. -/
theorem pi_split_coordinate_expect {α Ω : Type*} [Fintype α] [Fintype Ω]
    [DecidableEq α] (P : α → FinProb Ω) (a₀ : α) (f : (α → Ω) → ℝ) :
    (FinProb.pi P).expect f = (P a₀).expect (fun x =>
      (FinProb.pi (fun i : {a : α // a ≠ a₀} => P i.1)).expect
        (fun rest => f (insertField a₀ x rest))) := by
  classical
  let e : (α → Ω) ≃ Ω × ({a : α // a ≠ a₀} → Ω) :=
    { toFun := fun ω => (ω a₀, fun i => ω i.1)
      invFun := fun xr => insertField a₀ xr.1 xr.2
      left_inv := fun ω => by
        funext a
        by_cases h : a = a₀ <;> simp [insertField, h]
      right_inv := fun xr => by
        apply Prod.ext
        · simp [insertField]
        · funext i
          simp [insertField, i.2] }
  letI : Unique {a : α // a = a₀} :=
    { default := ⟨a₀, rfl⟩
      uniq := fun i => Subtype.ext i.2 }
  have hweight (ω : α → Ω) :
      (FinProb.pi P).w ω = (P a₀).w (ω a₀) *
        (FinProb.pi (fun i : {a : α // a ≠ a₀} => P i.1)).w (fun i => ω i.1) := by
    change (∏ a, (P a).w (ω a)) = (P a₀).w (ω a₀) *
      ∏ i : {a : α // a ≠ a₀}, (P i.1).w (ω i.1)
    rw [← Fintype.prod_subtype_mul_prod_subtype (fun a : α => a = a₀)
      (fun a => (P a).w (ω a))]
    simp only [Fintype.prod_unique]
    rfl
  unfold FinProb.expect
  simp_rw [Finset.mul_sum]
  let g : Ω × ({a : α // a ≠ a₀} → Ω) → ℝ := fun xr =>
    (P a₀).w xr.1 * ((FinProb.pi (fun i : {a : α // a ≠ a₀} => P i.1)).w xr.2 *
      f (insertField a₀ xr.1 xr.2))
  change (∑ ω, (FinProb.pi P).w ω * f ω) = ∑ x, ∑ rest, g (x, rest)
  rw [← Fintype.sum_prod_type]
  apply Fintype.sum_equiv e
  intro ω
  have he : insertField a₀ (ω a₀) (fun i => ω i.1) = ω := e.left_inv ω
  change (FinProb.pi P).w ω * f ω = (P a₀).w (ω a₀) *
    ((FinProb.pi (fun i : {a : α // a ≠ a₀} => P i.1)).w (fun i => ω i.1) *
      f (insertField a₀ (ω a₀) (fun i => ω i.1)))
  rw [he, hweight]
  ring

/-- Integrate an event in the second coordinate of a product law. -/
theorem prod_pr_expect {α β : Type*} [Fintype α] [Fintype β]
    (P : FinProb α) (Q : FinProb β) (F : α → β → Prop) :
    (P.prod Q).pr (fun ab => F ab.1 ab.2) = P.expect (fun a => Q.pr (F a)) := by
  classical
  rw [pr_indicator, prod_expect]
  apply congrArg P.expect
  funext a
  exact (pr_indicator Q (F a)).symm

/-- Independent coordinates can be integrated in either order. -/
theorem expect_swap {α β : Type*} [Fintype α] [Fintype β]
    (P : FinProb α) (Q : FinProb β) (f : α → β → ℝ) :
    P.expect (fun a => Q.expect (f a)) = Q.expect (fun b => P.expect (fun a => f a b)) := by
  unfold FinProb.expect
  simp_rw [Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro b _
  apply Finset.sum_congr rfl
  intro a _
  ring

/-- A uniform conditional bound survives averaging over an independent variable. -/
theorem prod_pr_le_of_uniform {α β : Type*} [Fintype α] [Fintype β]
    (P : FinProb α) (Q : FinProb β) (F : α → β → Prop) (ε : ℝ)
    (h : ∀ a, Q.pr (F a) ≤ ε) : (P.prod Q).pr (fun ab => F ab.1 ab.2) ≤ ε := by
  rw [prod_pr_expect]
  exact (FinProb.expect_mono P h).trans_eq (FinProb.expect_const P ε)

end HypercubeRamsey.Lane_sol_s10_d2
