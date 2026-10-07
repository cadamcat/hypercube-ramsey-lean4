import HypercubeRamsey.S05.History_sol_s05_1f_high

namespace HypercubeRamsey.Lane_sol_s05_1f
open Classical OAI.HypercubeRamsey
open scoped BigOperators
noncomputable section
set_option maxHeartbeats 400000
set_option synthInstance.maxSize 1024
variable {γ K' χ : ℝ} {n N : ℕ} {E : Fin N → Fin N → Prop} {G : Colour}
variable (X : Setup5 γ K' χ n N E G)

/-- Split off the denominator exceptions and integrate the remaining high
feasibility failure under its concrete posterior. -/
theorem high_raw_bound_of_posterior_tail (H : X.KeyHist) (r : X.AbsRecord)
    (hr : X.RecOccurs r) (hh : r.1.isRight) (ε : ℝ) (hε : 0 ≤ ε)
    (htail : ∀ a : X.ArraysOn (Fin (X.p.T n)),
      Real.exp (-(X.p.delta * X.p.s n)) ≤ X.step3MassOn H r a none →
      (∀ c ∈ X.refsOn H r a,
        Real.exp (-(X.p.delta * X.refLen c.2.1 c.2.2 * colLen5 (X.p.s n) r.1)) *
          X.step3MassOn H r a (some c) ≤ X.step3MassOn H r a none) →
      ∀ hm : 0 < X.step3MassOn H r a none,
        (posteriorLaw X H r a none hm).pr (fun θ =>
          ¬ (X.HighCapped (X.withCol H r.1 θ) r a ∧
            X.HighPriceFeasible (X.withCol H r.1 θ) r a)) ≤ ε) :
    (∑ θ : Fin (colLen5 (X.p.s n) r.1) → Fin N,
      (∏ h, (X.prior H.1 r.1).w (θ h)) * X.step3Rate (X.withCol H r.1 θ) r) ≤
      (∑ θ : Fin (colLen5 (X.p.s n) r.1) → Fin N,
        (∏ h, (X.prior H.1 r.1).w (θ h)) *
          (X.recArrayLaw (X.withCol H r.1 θ)).pr
            (denominatorFail X (X.withCol H r.1 θ) r)) + ε := by
  classical
  let F := fun θ a => X.step3FailOn (X.withCol H r.1 θ) r a ∧
    ¬ denominatorFail X (X.withCol H r.1 θ) r a
  have harrays := recordArrays_eq_observed X r hr
  have hF (θ) : FinProb.DependsOn (fun a => @ite ℝ (F θ a) (Classical.propDecidable _) 1 0) r.2.1 := by
    intro a b hab
    have hfull := Lane_sol_s05_h5l.step3Fail_array_depends X (X.withCol H r.1 θ) r a b
      (by simpa only [harrays] using hab)
    have hden := denominatorFail_arrays_congr X (X.withCol H r.1 θ) r hr a b hab
    have he : F θ a ↔ F θ b := by simp only [F, hfull, hden]
    by_cases hfa : F θ a
    · simp only [if_pos hfa, if_pos (he.mp hfa)]
    · have hfb : ¬ F θ b := fun h => hfa (he.mpr h)
      simp only [if_neg hfa, if_neg hfb]
  have htarget (θ) : (X.withCol H r.1 θ).2 r.1 = θ := by simp [Setup5.withCol]
  have hcol : colLen5 (X.p.s n) r.1 = X.p.s n := by cases h : r.1 <;> simp_all [colLen5]
  obtain ⟨key, hkey⟩ : ∃ key : CoarseKey5 n, r.1 = .inr key := by
    cases h : r.1 with
    | inl k => simp [h] at hh
    | inr k => exact ⟨k, rfl⟩
  have hFtail (a) (hm : 0 < X.step3MassOn H r a none) :
      (posteriorLaw X H r a none hm).pr (fun θ => F θ a) ≤ ε := by
    let P := posteriorLaw X H r a none hm
    by_cases hdata : X.step3MassOn H r a none < Real.exp (-(X.p.delta * X.p.s n)) ∨
      ∃ c ∈ X.refsOn H r a,
        X.step3MassOn H r a none <
          Real.exp (-(X.p.delta * X.refLen c.2.1 c.2.2 * colLen5 (X.p.s n) r.1)) *
            X.step3MassOn H r a (some c)
    · have hno (θ) : ¬ F θ a := by
        rintro ⟨hf, hn⟩
        apply hn
        refine ⟨hf.1, ?_⟩
        simpa only [Lane_sol_s05_hist1b.step3MassOn_withCol, refsOn_withCol_high X H r hh a θ]
          using hdata
      have hz : P.pr (fun θ => F θ a) = 0 := by simp [FinProb.pr, hno]
      exact hz ▸ hε
    · have hlo : Real.exp (-(X.p.delta * X.p.s n)) ≤ X.step3MassOn H r a none :=
        le_of_not_gt (fun h => hdata (Or.inl h))
      have hrats (c) (hc : c ∈ X.refsOn H r a) :
          Real.exp (-(X.p.delta * X.refLen c.2.1 c.2.2 * colLen5 (X.p.s n) r.1)) *
            X.step3MassOn H r a (some c) ≤ X.step3MassOn H r a none :=
        le_of_not_gt (fun h => hdata (Or.inr ⟨c, hc, h⟩))
      apply le_trans _ (htail a hlo hrats hm)
      unfold FinProb.pr
      apply Finset.sum_le_sum
      intro θ _
      by_cases hf : F θ a
      · have hbad : ¬ (X.HighCapped (X.withCol H r.1 θ) r a ∧
            X.HighPriceFeasible (X.withCol H r.1 θ) r a) := by
          rcases hf.1.2 with hlow | hrat | hprice
          · have hlo : X.step3MassOn (X.withCol H r.1 θ) r a none <
                Real.exp (-(X.p.delta * X.p.s n)) := by
              conv at hlow => rhs; rw [hkey]
              exact hlow
            exact False.elim (hf.2 ⟨hf.1.1, Or.inl hlo⟩)
          · exact False.elim (hf.2 ⟨hf.1.1, Or.inr hrat⟩)
          · exact hprice.2
        simp only [if_pos hf, if_pos hbad]; exact le_rfl
      · simp only [if_neg hf]
        split_ifs <;> first | exact le_rfl | exact P.nonneg θ
  have hcond := step3_conditional_tail X H r hr F ε hε hF hFtail
  have hbound (θ) : X.step3Rate (X.withCol H r.1 θ) r ≤
      (X.recArrayLaw (X.withCol H r.1 θ)).pr (denominatorFail X (X.withCol H r.1 θ) r) +
        (X.recArrayLaw (X.withCol H r.1 θ)).pr (fun a => X.candGateOn H r a θ ∧ F θ a) := by
    let P := X.recArrayLaw (X.withCol H r.1 θ)
    apply le_trans _ (P.pr_union _ _)
    unfold Setup5.step3Rate FinProb.pr
    apply Finset.sum_le_sum
    intro a _
    by_cases hf : X.step3FailOn (X.withCol H r.1 θ) r a
    · have ho : denominatorFail X (X.withCol H r.1 θ) r a ∨ X.candGateOn H r a θ ∧ F θ a := by
        by_cases hd : denominatorFail X (X.withCol H r.1 θ) r a
        · exact Or.inl hd
        · exact Or.inr ⟨(Lane_sol_s05_hist1b.candGateOn_withCol X H r a θ θ).mp
            (by simpa only [htarget] using hf.1), hf, hd⟩
      simp only [if_pos hf, if_pos ho]; exact le_rfl
    · simp only [if_neg hf]; split_ifs <;> simp [P.nonneg a]
  calc
    _ ≤ ∑ θ, (∏ h, (X.prior H.1 r.1).w (θ h)) *
        ((X.recArrayLaw (X.withCol H r.1 θ)).pr (denominatorFail X (X.withCol H r.1 θ) r) +
          (X.recArrayLaw (X.withCol H r.1 θ)).pr (fun a => X.candGateOn H r a θ ∧ F θ a)) :=
      Finset.sum_le_sum fun θ _ => mul_le_mul_of_nonneg_left (hbound θ)
        (Finset.prod_nonneg fun h _ => (X.prior H.1 r.1).nonneg _)
    _ = _ := by simp only [mul_add, Finset.sum_add_distrib]
    _ ≤ _ := add_le_add le_rfl hcond

end
end HypercubeRamsey.Lane_sol_s05_1f
