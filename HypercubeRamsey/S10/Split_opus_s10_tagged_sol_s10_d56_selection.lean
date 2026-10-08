import HypercubeRamsey.S10.Split_opus_s10_tagged_sol_s10_d56_weights
import HypercubeRamsey.S10.Split_opus_s10_tagged_sol_s10_d56_independence
import HypercubeRamsey.S10.Split_opus_s10_tagged_sol_s10_d56_enumeration

namespace HypercubeRamsey.Lane_sol_s10_d56

open Classical HypercubeRamsey.S10 OAI.HypercubeRamsey
open scoped BigOperators

/-- The two global independent fields are a product of independent per-slice experiments. -/
theorem global_act_tie_expect (n m : ℕ) (δ : ℝ)
    (F : ((P10_1kSpecialSliceWord m → (p10_1kHeightParams n m δ).Loc → Bool) ×
      (P10_1kSpecialSliceWord m → (p10_1kHeightParams n m δ).Ties)) → ℝ) :
    ((p10_1kGlobalActivationLaw n m δ).prod (p10_1kGlobalTieLaw n m δ)).expect
      (fun ω => F ((fun z loc => ω.1 (z, loc)), (fun z loc => ω.2 (z, loc)))) =
    (FinProb.pi (fun _ : P10_1kSpecialSliceWord m =>
      (p10_1kHeightParams n m δ).actLaw.prod (p10_1kHeightParams n m δ).tieLaw)).expect
        (fun ω => F ((fun z => (ω z).1), (fun z => (ω z).2))) := by
  classical
  let p := p10_1kHeightParams n m δ
  let Z := P10_1kSpecialSliceWord m
  let pa := FinProb.bernoulli ((p.n : ℝ) ^ p.b₀ / p.lam)
  let pt : FinProb p.TiePerm := FinProb.uniformAll ⟨1⟩
  have ht (A : P10_1kProspectiveId n m δ → Bool) :
      (p10_1kGlobalTieLaw n m δ).expect
        (fun T => F ((fun z loc => A (z, loc)), (fun z loc => T (z, loc)))) =
      (FinProb.pi (fun _ : Z => p.tieLaw)).expect
        (fun T => F ((fun z loc => A (z, loc)), T)) :=
    pi_curry_expect (fun (_ : Z) (_ : p.Loc) => pt)
      (fun T => F ((fun z loc => A (z, loc)), T))
  have ha : (p10_1kGlobalActivationLaw n m δ).expect (fun A =>
      (FinProb.pi (fun _ : Z => p.tieLaw)).expect
        (fun T => F ((fun z loc => A (z, loc)), T))) =
      (FinProb.pi (fun _ : Z => p.actLaw)).expect (fun A =>
        (FinProb.pi (fun _ : Z => p.tieLaw)).expect (fun T => F (A, T))) :=
    pi_curry_expect (fun (_ : Z) (_ : p.Loc) => pa)
      (fun A => (FinProb.pi (fun _ : Z => p.tieLaw)).expect (fun T => F (A, T)))
  rw [prod_expect (p10_1kGlobalActivationLaw n m δ) (p10_1kGlobalTieLaw n m δ)
    (fun A T => F ((fun z loc => A (z, loc)), (fun z loc => T (z, loc))))]
  simp_rw [ht]
  rw [ha]
  rw [← prod_expect (FinProb.pi (fun _ : Z => p.actLaw)) (FinProb.pi (fun _ : Z => p.tieLaw))
    (fun A T => F (A, T))]
  exact pi_pair_expect (fun _ : Z => p.actLaw) (fun _ : Z => p.tieLaw) F

private theorem pr_eq_expect_indicator {Ω : Type*} [Fintype Ω] (P : FinProb Ω)
    (F : Ω → Prop) : P.pr F = P.expect (fun ω => if F ω then (1 : ℝ) else 0) := by
  classical
  unfold FinProb.pr FinProb.expect
  apply Finset.sum_congr rfl
  intro ω hω
  by_cases h : F ω <;> simp [h]

/-- Selections in distinct slices have independent activation/tie marginals. -/
theorem global_act_tie_pr_queries (n m : ℕ) (δ : ℝ) {r : ℕ}
    (e : Fin r → P10_1kSpecialSliceWord m) (he : Function.Injective e)
    (F : Fin r → ((p10_1kHeightParams n m δ).Loc → Bool) ×
      (p10_1kHeightParams n m δ).Ties → Prop) :
    ((p10_1kGlobalActivationLaw n m δ).prod (p10_1kGlobalTieLaw n m δ)).pr
      (fun ω => ∀ i, F i ((fun loc => ω.1 (e i, loc)), (fun loc => ω.2 (e i, loc)))) =
        ∏ i, ((p10_1kHeightParams n m δ).actLaw.prod
          (p10_1kHeightParams n m δ).tieLaw).pr (F i) := by
  classical
  rw [pr_eq_expect_indicator]
  rw [global_act_tie_expect n m δ (fun AT =>
    @ite ℝ (∀ i, F i (AT.1 (e i), AT.2 (e i)))
      (Classical.propDecidable _) 1 0)]
  rw [← pr_eq_expect_indicator
    (FinProb.pi (fun _ : P10_1kSpecialSliceWord m =>
      (p10_1kHeightParams n m δ).actLaw.prod (p10_1kHeightParams n m δ).tieLaw))
    (fun ω => ∀ i, F i (ω (e i)))]
  exact pi_injective_pr_all (fun _ : P10_1kSpecialSliceWord m =>
    (p10_1kHeightParams n m δ).actLaw.prod (p10_1kHeightParams n m δ).tieLaw) e he F


/-- Fixed eligibility in distinct slices is dominated by the product of position-only caps. -/
theorem global_selection_probability_le (n m : ℕ) (δ : ℝ) {r : ℕ}
    (e : Fin r → P10_1kSpecialSliceWord m) (he : Function.Injective e)
    (Sites : P10_1kSpecialSliceWord m → (p10_1kHeightParams n m δ).Sites)
    (v : P10_1kSpecialSliceWord m → CubeVertex (p10_1kHeightParams n m δ).d)
    (P : P10_1kProspectiveId n m δ → Bool)
    (E : P10_1kSpecialSliceWord m → (p10_1kHeightParams n m δ).EligMap)
    (center : Fin r → (p10_1kHeightParams n m δ).Loc) :
    let p := p10_1kHeightParams n m δ
    ((p10_1kGlobalActivationLaw n m δ).prod (p10_1kGlobalTieLaw n m δ)).pr
      (fun ω => ∀ i,
        (∀ j, (99 / 100 : ℝ) * p.lam ≤ ((E (e i) (v (e i)) j).card : ℝ)) ∧
        p.Legal (fun loc => P (e i, loc)) (E (e i))
          (p.domBall (Sites (e i)) (v (e i)) p.Rlong) ∧
        p.selection (Sites (e i)) (fun loc => P (e i, loc))
          (fun loc => ω.1 (e i, loc)) (E (e i)) (fun loc => ω.2 (e i, loc)) (v (e i)) =
            some (center i)) ≤
    ∏ i, selectionCap p (Sites (e i)) (v (e i)) (center i) (fun loc => P (e i, loc)) := by
  classical
  dsimp only
  let p := p10_1kHeightParams n m δ
  let F : Fin r → (p.Loc → Bool) × p.Ties → Prop := fun i ω =>
    (∀ j, (99 / 100 : ℝ) * p.lam ≤ ((E (e i) (v (e i)) j).card : ℝ)) ∧
    p.Legal (fun loc => P (e i, loc)) (E (e i))
      (p.domBall (Sites (e i)) (v (e i)) p.Rlong) ∧
    p.selection (Sites (e i)) (fun loc => P (e i, loc)) ω.1 (E (e i)) ω.2 (v (e i)) =
      some (center i)
  change ((p10_1kGlobalActivationLaw n m δ).prod (p10_1kGlobalTieLaw n m δ)).pr
    (fun ω => ∀ i, F i ((fun loc => ω.1 (e i, loc)), (fun loc => ω.2 (e i, loc)))) ≤ _
  rw [global_act_tie_pr_queries n m δ e he F]
  apply Finset.prod_le_prod₀
  · intro i hi
    unfold FinProb.pr
    apply Finset.sum_nonneg
    intro ω hω
    split_ifs
    · exact (p.actLaw.prod p.tieLaw).nonneg ω
    · exact le_rfl
  · intro i hi
    exact selection_probability_le_cap p (Sites (e i)) (v (e i)) (center i)
      (fun loc => P (e i, loc)) (E (e i))

end HypercubeRamsey.Lane_sol_s10_d56
