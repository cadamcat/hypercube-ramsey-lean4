import HypercubeRamsey.Framework.FinProbLemmas
import HypercubeRamsey.S03.Height.Device

/-!
# opus-s10-d7a: finite-law helpers for the predictive-failure bound d7a

Generic facts about `FinProb.pi`: probabilities as expectations, the expectation of a
coordinatewise product, the fibrewise regrouping of a product over a finite family of
roles by their groups, and the probability of an event read through a subset of
coordinates.
-/

namespace HypercubeRamsey.Lane_opus_s10_d7a

open HypercubeRamsey
open scoped BigOperators

theorem pr_eq_expect_ite {Ω : Type*} [Fintype Ω] (P : FinProb Ω) (A : Ω → Prop)
    [DecidablePred A] : P.pr A = P.expect (fun x => if A x then (1 : ℝ) else 0) := by
  unfold FinProb.pr FinProb.expect
  refine Finset.sum_congr rfl fun x _ => ?_
  by_cases hx : A x <;> simp [hx]

theorem pi_expect_prod_eq {ι : Type*} [Fintype ι] [DecidableEq ι] {Ω : Type*} [Fintype Ω]
    (P : ι → FinProb Ω) (F : ι → Ω → ℝ) :
    (FinProb.pi P).expect (fun C => ∏ q, F q (C q)) = ∏ q, (P q).expect (F q) := by
  show ∑ C : ι → Ω, (∏ q, (P q).w (C q)) * ∏ q, F q (C q) =
    ∏ q, ∑ x, (P q).w x * F q x
  rw [Fintype.prod_sum]
  refine Finset.sum_congr rfl fun C _ => ?_
  rw [Finset.prod_mul_distrib]

/-- Regroup a product over roles `S` by their groups `g b ∈ T`, and integrate an
independent cluster per group. -/
theorem pi_expect_prod_fiber {ι κ : Type*} [Fintype ι] [DecidableEq ι] {Ω : Type*}
    [Fintype Ω] (P : ι → FinProb Ω) (S : Finset κ) (g : κ → ι) (T : Finset ι)
    (hST : ∀ b ∈ S, g b ∈ T) (f : κ → Ω → ℝ) :
    (FinProb.pi P).expect (fun C => ∏ b ∈ S, f b (C (g b))) =
      ∏ q ∈ T, (P q).expect (fun x => ∏ b ∈ S.filter (fun b => g b = q), f b x) := by
  let F : ι → Ω → ℝ := fun q x =>
    if q ∈ T then ∏ b ∈ S.filter (fun b => g b = q), f b x else 1
  have h1 : ∀ C : ι → Ω, ∏ b ∈ S, f b (C (g b)) = ∏ q, F q (C q) := by
    intro C
    calc
      ∏ b ∈ S, f b (C (g b)) =
          ∏ q ∈ T, ∏ b ∈ S.filter (fun b => g b = q), f b (C (g b)) :=
        (Finset.prod_fiberwise_of_maps_to hST _).symm
      _ = ∏ q ∈ T, ∏ b ∈ S.filter (fun b => g b = q), f b (C q) := by
        refine Finset.prod_congr rfl fun q _ => Finset.prod_congr rfl fun b hb => ?_
        rw [(Finset.mem_filter.mp hb).2]
      _ = ∏ q, F q (C q) := by
        show _ = ∏ q, (if q ∈ T then ∏ b ∈ S.filter (fun b => g b = q), f b (C q) else 1)
        rw [Finset.prod_ite_mem, Finset.univ_inter]
  have hF : ∀ q, (P q).expect (F q) =
      if q ∈ T then (P q).expect (fun x => ∏ b ∈ S.filter (fun b => g b = q), f b x)
      else 1 := by
    intro q
    by_cases hq : q ∈ T
    · simp only [F, if_pos hq]
    · simp only [F, if_neg hq]
      exact FinProb.expect_const (P q) 1
  calc
    (FinProb.pi P).expect (fun C => ∏ b ∈ S, f b (C (g b))) =
        (FinProb.pi P).expect (fun C => ∏ q, F q (C q)) := by
      unfold FinProb.expect
      exact Finset.sum_congr rfl fun C _ =>
        congrArg (fun x => (FinProb.pi P).w C * x) (h1 C)
    _ = ∏ q, (P q).expect (F q) := pi_expect_prod_eq P F
    _ = ∏ q, (if q ∈ T then
          (P q).expect (fun x => ∏ b ∈ S.filter (fun b => g b = q), f b x) else 1) :=
      Finset.prod_congr rfl fun q _ => hF q
    _ = ∏ q ∈ T, (P q).expect (fun x => ∏ b ∈ S.filter (fun b => g b = q), f b x) := by
      rw [Finset.prod_ite_mem, Finset.univ_inter]

/-- The probability of an event read through the coordinates in `s` only, under a
product law, is its probability under the product over `s`. -/
theorem pi_pr_restrict {ι : Type*} [Fintype ι] [DecidableEq ι] {Ω : Type*} [Fintype Ω]
    (P : ι → FinProb Ω) (s : Finset ι) (ω₀ : ι → Ω) (A : ({i // i ∈ s} → Ω) → Prop) :
    (FinProb.pi P).pr (fun ω => A (fun i => ω i.1)) =
      (FinProb.pi (fun i : {i // i ∈ s} => P i.1)).pr A := by
  classical
  rw [pr_eq_expect_ite, pr_eq_expect_ite]
  have hdep : FinProb.DependsOn
      (fun ω : ι → Ω => if A (fun i => ω i.1) then (1 : ℝ) else 0) s := by
    intro ω ω' hag
    have hω : (fun i : {i // i ∈ s} => ω i.1) = (fun i => ω' i.1) :=
      funext fun i => hag i.1 i.2
    simp only [hω]
  have hres : ∀ a : {i // i ∈ s} → Ω,
      (fun i : {i // i ∈ s} =>
        ((Equiv.piEquivPiSubtypeProd (fun i => i ∈ s) (fun _ => Ω)).symm
          (a, fun i => ω₀ i.1)) i.1) = a := by
    intro a
    funext i
    simp only [Equiv.piEquivPiSubtypeProd_symm_apply, dif_pos i.2]
  rw [FinProb.pi_expect_depends P s _ ω₀ hdep]
  simp only [hres]

theorem prod_expect_eq {α β : Type*} [Fintype α] [Fintype β] (P : FinProb α)
    (Q : FinProb β) (F : α × β → ℝ) :
    (FinProb.prod P Q).expect F = P.expect (fun x => Q.expect (fun y => F (x, y))) := by
  unfold FinProb.expect
  rw [Fintype.sum_prod_type]
  refine Finset.sum_congr rfl fun x _ => ?_
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun y _ => ?_
  show P.w x * Q.w y * F (x, y) = P.w x * (Q.w y * F (x, y))
  ring

/-- Finite union bound for `FinProb.pr`. -/
theorem pr_le_sum_pr {Ω ι : Type*} [Fintype Ω] [Fintype ι] (P : FinProb Ω)
    (A : Ω → Prop) (B : ι → Ω → Prop) (hAB : ∀ ω, A ω → ∃ i, B i ω) :
    P.pr A ≤ ∑ i, P.pr (B i) := by
  classical
  unfold FinProb.pr
  rw [Finset.sum_comm]
  refine Finset.sum_le_sum fun ω _ => ?_
  have hnn : ∀ j, 0 ≤ (if B j ω then P.w ω else 0) := fun j => by
    split_ifs
    · exact P.nonneg ω
    · exact le_rfl
  by_cases hA : A ω
  · obtain ⟨i, hi⟩ := hAB ω hA
    rw [if_pos hA]
    calc
      P.w ω = (if B i ω then P.w ω else 0) := (if_pos hi).symm
      _ ≤ ∑ j, (if B j ω then P.w ω else 0) :=
        Finset.single_le_sum (f := fun j => if B j ω then P.w ω else 0)
          (fun j _ => hnn j) (Finset.mem_univ i)
  · rw [if_neg hA]
    exact Finset.sum_nonneg fun j _ => hnn j

end HypercubeRamsey.Lane_opus_s10_d7a
