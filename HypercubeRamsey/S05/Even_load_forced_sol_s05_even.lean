import HypercubeRamsey.S05.Even_load_selection_sol_s05_even

namespace HypercubeRamsey.Lane_sol_s05_even
open Classical OAI.HypercubeRamsey
open scoped BigOperators
noncomputable section
set_option maxHeartbeats 400000

/-- Integrate the second component of a finite product event. -/
theorem prod_probability_expect {A B : Type*} [Fintype A] [Fintype B]
    (P : FinProb A) (Q : FinProb B) (s : A → B → Prop) :
    (P.prod Q).pr (fun ab => s ab.1 ab.2) = P.expect (fun a => Q.pr (s a)) := by
  unfold FinProb.pr FinProb.expect FinProb.prod
  rw [Fintype.sum_prod_type]
  apply Finset.sum_congr rfl
  intro a _
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro b _
  by_cases hs : s a b <;> simp [hs]

theorem expect_constant {A : Type*} [Fintype A] (P : FinProb A) (c : ℝ) :
    P.expect (fun _ => c) = c := by
  unfold FinProb.expect
  rw [← Finset.sum_mul, P.sum_eq_one, one_mul]

theorem probability_drop_independent {A B T : Type*} [Fintype A] [Fintype B] [Fintype T]
    (P : FinProb A) (Q : FinProb B) (R : FinProb T) (s : A → B → Prop) :
    (P.prod (Q.prod R)).pr (fun abt => s abt.1 abt.2.1) = (P.prod Q).pr (fun ab => s ab.1 ab.2) := by
  rw [prod_probability_expect P (Q.prod R) (fun a bt => s a bt.1),
    prod_probability_expect P Q s]
  congr 1
  funext a
  rw [prod_probability_expect Q R (fun b _ => s a b)]
  have heq (b : B) : R.pr (fun _ => s a b) = if s a b then (1 : ℝ) else 0 := by
    unfold FinProb.pr
    by_cases h : s a b
    · simp only [if_pos h]
      exact R.sum_eq_one
    · simp [h]
  simp_rw [heq]
  unfold FinProb.expect FinProb.pr
  apply Finset.sum_congr rfl
  intro b _
  by_cases h : s a b <;> simp [h]

theorem joint_forced_presence_probability {I A : Type*} [Fintype I] [DecidableEq I] [Fintype A]
    (q : ℝ) (l : I) (Q : FinProb A) (s : (I → Bool) → A → Prop)
    (hs : ∀ P a, s P a → P l = true) :
    ((FinProb.pi (fun _ : I => FinProb.bernoulli q)).prod Q).pr (fun ω => s ω.1 ω.2) =
      max 0 (min q 1) * ((forcedPresenceLaw q l).prod Q).pr (fun ω => s ω.1 ω.2) := by
  rw [prod_probability_expect, prod_probability_expect]
  have heq (P : I → Bool) : Q.pr (s P) = if P l then Q.pr (s P) else 0 := by
    cases hP : P l
    · unfold FinProb.pr
      have hempty : ∀ a, ¬ s P a := fun a ha => by have hh := hs P a ha; simp [hP] at hh
      simp [hempty]
    · simp
  calc
    _ = (FinProb.pi (fun _ : I => FinProb.bernoulli q)).expect
        (fun P => if P l then Q.pr (s P) else 0) := by
      congr 1
      exact funext heq
    _ = _ := forced_presence_expect q l (fun P => Q.pr (s P))

theorem raw_zero_level_selection (p : HDParams) (hlam : 0 < p.lam)
    (Esel : (p.Loc → Bool) → p.EligMap) (Sites : p.Sites) (v : CubeVertex p.d) (hv : v ∈ Sites)
    (l : p.Loc) (hl0 : l.2.val = 0)
    (hshape : ∀ P j l, l ∈ Esel P v j → P l = true ∧ l.2 = j ∧ _root_.hammingDist l.1 v ≤ p.r) :
    (p.posLaw.prod (p.actLaw.prod p.tieLaw)).pr (fun ω =>
      p.Legal ω.1 (Esel ω.1) (p.domBall Sites v p.Rlong) ∧
        p.selection Sites ω.1 ω.2.1 (Esel ω.1) ω.2.2 v = some l) ≤
      max 0 (min (p.lam / (p.V : ℝ)) 1) * (3 / p.lam) := by
  rw [prod_probability_expect p.posLaw (p.actLaw.prod p.tieLaw)
    (fun P ω => p.Legal P (Esel P) (p.domBall Sites v p.Rlong) ∧
      p.selection Sites P ω.1 (Esel P) ω.2 v = some l)]
  have hbound (P : p.Loc → Bool) :
      (p.actLaw.prod p.tieLaw).pr (fun ω =>
        p.Legal P (Esel P) (p.domBall Sites v p.Rlong) ∧
          p.selection Sites P ω.1 (Esel P) ω.2 v = some l) ≤
        if P l then (3 / p.lam) else 0 := by
    cases hP : P l
    · have hz : (p.actLaw.prod p.tieLaw).pr (fun ω =>
          p.Legal P (Esel P) (p.domBall Sites v p.Rlong) ∧
            p.selection Sites P ω.1 (Esel P) ω.2 v = some l) = 0 := by
        unfold FinProb.pr
        apply Finset.sum_eq_zero
        intro ω _
        apply if_neg
        intro hs
        have hp := (selection_some_shape p Sites P ω.1 (Esel P) ω.2 v l (hshape P) hs.2).1
        simp [hP] at hp
      simp [hz]
    · simp only [hP, if_true]
      exact level_zero_selection_bound p hlam P (Esel P) Sites v hv l hl0 (fun j l hl => (hshape P j l hl).2.1)
  calc
    _ ≤ p.posLaw.expect (fun P => if P l then (3 / p.lam) else 0) := by
      unfold FinProb.expect
      apply Finset.sum_le_sum
      intro P _
      exact mul_le_mul_of_nonneg_left (hbound P) (p.posLaw.nonneg P)
    _ = _ := by
      unfold HDParams.posLaw
      rw [forced_presence_expect, expect_constant]

/-- The positive-level selection estimate is an intersection estimate under forced presence. -/
theorem raw_positive_level_selection (p : HDParams)
    (Esel : (p.Loc → Bool) → p.EligMap) (Sites : p.Sites) (v : CubeVertex p.d) (l : p.Loc)
    (hlpos : 0 < l.2.val)
    (hshape : ∀ P j l, l ∈ Esel P v j → P l = true ∧ l.2 = j ∧ _root_.hammingDist l.1 v ≤ p.r)
    (ε : ℝ)
    (hpositive : ((p.posLawForced (some l)).prod p.actLaw).pr (fun ω =>
      p.Legal ω.1 (Esel ω.1) (p.domBall Sites v p.Rlong) ∧
        0 < p.height Sites ω.1 ω.2 (Esel ω.1) p.Rlong v) ≤ ε) :
    (p.posLaw.prod (p.actLaw.prod p.tieLaw)).pr (fun ω =>
      p.Legal ω.1 (Esel ω.1) (p.domBall Sites v p.Rlong) ∧
        p.selection Sites ω.1 ω.2.1 (Esel ω.1) ω.2.2 v = some l) ≤
      max 0 (min (p.lam / (p.V : ℝ)) 1) * ε := by
  let s := fun (P : p.Loc → Bool) (ω : (p.Loc → Bool) × p.Ties) =>
    p.Legal P (Esel P) (p.domBall Sites v p.Rlong) ∧ p.selection Sites P ω.1 (Esel P) ω.2 v = some l
  have hs (P) (ω) (h : s P ω) : P l = true :=
    (selection_some_shape p Sites P ω.1 (Esel P) ω.2 v l (hshape P) h.2).1
  have hforced : forcedPresenceLaw (p.lam / (p.V : ℝ)) l = p.posLawForced (some l) := by
    unfold forcedPresenceLaw HDParams.posLawForced
    congr 1
    funext i
    simp [eq_comm]
  change (p.posLaw.prod (p.actLaw.prod p.tieLaw)).pr (fun ω => s ω.1 ω.2) ≤ _
  unfold HDParams.posLaw
  rw [joint_forced_presence_probability _ l _ s hs, hforced]
  apply mul_le_mul_of_nonneg_left _ (le_max_left _ _)
  have hmono := probability_mono ((p.posLawForced (some l)).prod (p.actLaw.prod p.tieLaw))
    (fun ω => s ω.1 ω.2)
    (fun ω => p.Legal ω.1 (Esel ω.1) (p.domBall Sites v p.Rlong) ∧
      0 < p.height Sites ω.1 ω.2.1 (Esel ω.1) p.Rlong v) (by
        intro ω h
        refine ⟨h.1, ?_⟩
        have hh := selection_level_eq_height p Sites ω.1 ω.2.1 (Esel ω.1) ω.2.2 v l
          (fun j l hl => (hshape ω.1 j l hl).2.1) h.2
        exact hh ▸ hlpos)
  rw [probability_drop_independent (p.posLawForced (some l)) p.actLaw p.tieLaw
    (fun P A => p.Legal P (Esel P) (p.domBall Sites v p.Rlong) ∧
      0 < p.height Sites P A (Esel P) p.Rlong v)] at hmono
  exact hmono.trans hpositive

end
end HypercubeRamsey.Lane_sol_s05_even
