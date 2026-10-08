import HypercubeRamsey.S05.Even_test_sol_s05_even

namespace HypercubeRamsey.Lane_sol_s05_even

open Classical
open scoped BigOperators
noncomputable section
set_option maxHeartbeats 400000

theorem clock_gated_resampling_bound {Ω Z I O : Type*}
    [Fintype Ω] [Fintype Z] [Fintype I] [DecidableEq I] [Fintype O]
    (S : Finset I) [DecidableEq (S → O)] (o₀ : O)
    (raw : FinProb Ω) (π : FinProb Z) (J : Ω → FinProb (I → O))
    (replace : Ω → Z → Ω)
    (hresample : ∀ f : Ω → ℝ, raw.expect (fun ω => π.expect (fun z => f (replace ω z))) = raw.expect f)
    (hreplace : ∀ ω z z', replace (replace ω z) z' = replace ω z')
    (row : Ω → I → O → ℝ) (hrow : ∀ ω i o, 0 ≤ row ω i o)
    (gate : Ω → (S → O) → Prop) (enter select : Ω → Prop)
    (F : Ω → (S → O) → ℝ)
    (hF : ∀ ω d, F ω d = if gate ω d then ∏ i ∈ S, row ω i (extendOutputs S o₀ d i) else 0)
    (Q : Ω → FinProb (S → O)) (hQ : ∀ ω z, Q (replace ω z) = Q ω)
    (hcompare : ∀ ω, enter ω → ∀ d,
      (FinProb.map (J ω) (fun a (i : S) => a i.1)).w d ≤ 2 * ∏ i ∈ S, row ω i (extendOutputs S o₀ d i))
    (hgate : ∀ ω, enter ω → select ω → ∀ a, (J ω).w a ≠ 0 → gate ω (fun i : S => a i.1))
    (ε : ℝ) (hε : 0 < ε) :
    let m := fun ω d => ∑ z, π.w z * F (replace ω z) d
    (FinProb.bind raw J).pr (fun a => enter a.1 ∧ select a.1 ∧
      ¬ (0 < m a.1 (fun i : S => a.2 i.1) ∧
        ε * (Q a.1).w (fun i : S => a.2 i.1) ≤ m a.1 (fun i : S => a.2 i.1))) ≤ 2 * ε := by
  dsimp only
  let m := fun ω d => ∑ z, π.w z * F (replace ω z) d
  let bad := fun ω d => ¬ (0 < m ω d ∧ ε * (Q ω).w d ≤ m ω d)
  let failMass := fun ω => ∑ d, if bad ω d then F ω d else 0
  have hF0 (ω : Ω) (d : S → O) : 0 ≤ F ω d := by
    rw [hF]
    split_ifs
    · exact Finset.prod_nonneg fun i _ => hrow ω i _
    · rfl
  have hfail0 (ω : Ω) : 0 ≤ failMass ω := by
    apply Finset.sum_nonneg
    intro d _
    split_ifs
    · exact hF0 ω d
    · rfl
  have hbound : raw.expect failMass ≤ ε :=
    gated_resampling_bound raw π replace hresample hreplace F hF0 Q hQ ε hε
  have hpoint (ω : Ω) :
      (∑ a : I → O, if enter ω ∧ select ω ∧ bad ω (fun i : S => a i.1) then (J ω).w a else 0) ≤
        2 * failMass ω := by
    by_cases he : enter ω
    · let g := fun d : S → O => if bad ω d ∧ gate ω d then (1 : ℝ) else 0
      have hfirst :
          (∑ a : I → O, if enter ω ∧ select ω ∧ bad ω (fun i : S => a i.1) then (J ω).w a else 0) ≤
            (J ω).expect (fun a => g (fun i : S => a i.1)) := by
        unfold FinProb.expect
        apply Finset.sum_le_sum
        intro a _
        by_cases ha : enter ω ∧ select ω ∧ bad ω (fun i : S => a i.1)
        · rw [if_pos ha]
          by_cases hw : (J ω).w a = 0
          · simp [hw]
          · have hg := hgate ω he ha.2.1 a hw
            simp [g, ha.2.2, hg]
        · rw [if_neg ha]
          apply mul_nonneg ((J ω).nonneg a)
          dsimp [g]
          split_ifs <;> norm_num
      have hsecond : (FinProb.map (J ω) (fun a (i : S) => a i.1)).expect g ≤ 2 * failMass ω := by
        unfold FinProb.expect failMass
        rw [Finset.mul_sum]
        apply Finset.sum_le_sum
        intro d _
        by_cases hb : bad ω d
        · by_cases hg : gate ω d
          · simpa only [g, hb, hg, true_and, if_true, mul_one, hF, if_pos hg] using hcompare ω he d
          · simp [g, hb, hg, hF]
        · simp [g, hb]
      exact hfirst.trans ((FinProb.map_expect (J ω) (fun a (i : S) => a i.1) g).symm.le.trans hsecond)
    · simp only [he, false_and, if_false, Finset.sum_const_zero]
      exact mul_nonneg (by norm_num) (hfail0 ω)
  have hpr : (FinProb.bind raw J).pr (fun a => enter a.1 ∧ select a.1 ∧
      bad a.1 (fun i : S => a.2 i.1)) =
      raw.expect (fun ω => ∑ a : I → O,
        if enter ω ∧ select ω ∧ bad ω (fun i : S => a i.1) then (J ω).w a else 0) := by
    unfold FinProb.pr FinProb.expect
    rw [Fintype.sum_prod_type]
    apply Finset.sum_congr rfl
    intro ω _
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro a _
    split_ifs <;> simp [FinProb.bind]
  change (FinProb.bind raw J).pr (fun a => enter a.1 ∧ select a.1 ∧ bad a.1 (fun i : S => a.2 i.1)) ≤ 2 * ε
  rw [hpr]
  calc
    _ ≤ raw.expect (fun ω => 2 * failMass ω) := FinProb.expect_mono raw hpoint
    _ = 2 * raw.expect failMass := FinProb.expect_smul raw 2 failMass
    _ ≤ 2 * ε := mul_le_mul_of_nonneg_left hbound (by norm_num)

end
end HypercubeRamsey.Lane_sol_s05_even
