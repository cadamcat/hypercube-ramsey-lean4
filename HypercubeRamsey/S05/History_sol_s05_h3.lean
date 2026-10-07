import HypercubeRamsey.S05.History_q_s05_h23
import HypercubeRamsey.S05.History_sol_s05_h5l_lll

namespace HypercubeRamsey.Lane_sol_s05_h23

open Classical OAI.HypercubeRamsey Lane_q_s05_h23
open scoped BigOperators
noncomputable section
set_option maxHeartbeats 400000
set_option maxRecDepth 4096
set_option synthInstance.maxSize 1024

variable {γ K' χ : ℝ} {n N : ℕ} {E : Fin N → Fin N → Prop} {G : Colour}

abbrev highRawLaw (X : Setup5 γ K' χ n N E G) (b : X.Base) : FinProb (HiddenHigh5 X) :=
  FinProb.pi fun i => FinProb.pi fun _ => X.prior b (.inr i)

abbrev lowRawLaw (X : Setup5 γ K' χ n N E G) (b : X.Base) : FinProb (HiddenLow5 X) :=
  FinProb.pi fun k => FinProb.pi fun _ => X.prior b (.inl k)

theorem hidden_split_weight (X : Setup5 γ K' χ n N E G) (b : X.Base)
    (lo : HiddenLow5 X) (hi : HiddenHigh5 X) :
    (X.hiddenLaw b).w ((hiddenSplitEquiv5 X).symm (lo, hi)) =
      (lowRawLaw X b).w lo * (highRawLaw X b).w hi := by
  change (∏ ℓ : X.Key, ∏ h : Fin (colLen5 (X.p.s n) ℓ),
    (X.prior b ℓ).w ((hiddenSplitEquiv5 X).symm (lo, hi) ℓ h)) = _
  rw [Fintype.prod_sum_type]
  rfl

theorem hidden_split_expect (X : Setup5 γ K' χ n N E G) (b : X.Base)
    (f : X.Hidden → ℝ) :
    (X.hiddenLaw b).expect f = (lowRawLaw X b).expect (fun lo =>
      (highRawLaw X b).expect (fun hi => f ((hiddenSplitEquiv5 X).symm (lo, hi)))) := by
  classical
  unfold FinProb.expect
  rw [← (hiddenSplitEquiv5 X).symm.sum_comp]
  simp only [Fintype.sum_prod_type, hidden_split_weight, mul_assoc, Finset.mul_sum]

theorem hidden_split_pr (X : Setup5 γ K' χ n N E G) (b : X.Base)
    (A : X.Hidden → Prop) :
    (X.hiddenLaw b).pr A = (highRawLaw X b).expect (fun hi =>
      (lowRawLaw X b).pr (fun lo => A ((hiddenSplitEquiv5 X).symm (lo, hi)))) := by
  classical
  rw [pr_indicator5, hidden_split_expect]
  unfold FinProb.expect FinProb.pr
  simp only [mul_ite, mul_one, mul_zero, Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro hi _
  apply Finset.sum_congr rfl
  intro lo _
  split_ifs <;> ring

theorem low_shift_weight (X : Setup5 γ K' χ n N E G) (b : X.Base)
    (t : CubeVertex (X.p.m n)) (lo : HiddenLow5 X) :
    (lowRawLaw X b).w (hiddenLowShift5 X t lo) = (lowRawLaw X b).w lo := by
  change (∏ k : LowKey5 X, ∏ h : Fin 1,
    (X.prior b (.inl k)).w (lo (signShiftLowKey5 X t k) h)) = _
  have heq (k : LowKey5 X) : X.prior b (.inl k) =
      X.prior b (.inl (signShiftLowKey5 X t k)) := by
    exact prior_irrel_sign5 X b _ _ rfl rfl
  calc
    _ = ∏ k : LowKey5 X, ∏ h : Fin 1,
        (X.prior b (.inl (signShiftLowKey5 X t k))).w (lo (signShiftLowKey5 X t k) h) := by
      apply Finset.prod_congr rfl
      intro k _
      rw [heq k]
    _ = _ := (signShiftLowKey5 X t).prod_comp
      (fun k : LowKey5 X => ∏ h : Fin 1, (X.prior b (.inl k)).w (lo k h))

theorem low_shift_pr (X : Setup5 γ K' χ n N E G) (b : X.Base)
    (t : CubeVertex (X.p.m n)) (A : HiddenLow5 X → Prop) :
    (lowRawLaw X b).pr (fun lo => A (hiddenLowShift5 X t lo)) =
      (lowRawLaw X b).pr A := by
  classical
  unfold FinProb.pr
  have h := (hiddenLowShift5 X t).sum_comp
    (fun lo => if A lo then (lowRawLaw X b).w lo else 0)
  simpa only [low_shift_weight] using h

theorem blockMass_split_low_irrel (X : Setup5 γ K' χ n N E G) (b : X.Base)
    (hi : HiddenHigh5 X) (lo lo' : HiddenLow5 X) (K : X.Ty) (S : Finset X.Key)
    (hhigh : ∀ ℓ ∈ S, ∃ i, ℓ = .inr i) :
    X.blockMass (b, (hiddenSplitEquiv5 X).symm (lo, hi)) K S =
      X.blockMass (b, (hiddenSplitEquiv5 X).symm (lo', hi)) K S := by
  unfold Setup5.blockMass
  apply Finset.sum_congr rfl
  intro z _
  unfold Setup5.blockWeight
  congr 1
  apply Finset.prod_congr rfl
  intro ℓ hℓ
  obtain ⟨i, rfl⟩ := hhigh ℓ hℓ
  rfl

theorem step2Fail_split_low_irrel (X : Setup5 γ K' χ n N E G) (b : X.Base)
    (hi : HiddenHigh5 X) (lo lo' : HiddenLow5 X) (K : X.Ty)
    (hhigh : ∀ ℓ ∈ K.2.1, ∃ i, ℓ = .inr i) :
    X.step2Fail (b, (hiddenSplitEquiv5 X).symm (lo, hi)) K ↔
      X.step2Fail (b, (hiddenSplitEquiv5 X).symm (lo', hi)) K := by
  have hfull := blockMass_split_low_irrel X b hi lo lo' K K.2.1 hhigh
  have hdel (ℓ : X.Key) := blockMass_split_low_irrel X b hi lo lo' K (K.2.1.erase ℓ)
    (fun k hk => hhigh k (Finset.mem_erase.mp hk).2)
  simp only [Setup5.step2Fail, hfull, hdel]

theorem hidden_pr_highOnly (X : Setup5 γ K' χ n N E G) (b : X.Base)
    (A : X.Hidden → Prop)
    (hA : ∀ hi lo lo', A ((hiddenSplitEquiv5 X).symm (lo, hi)) ↔
      A ((hiddenSplitEquiv5 X).symm (lo', hi))) :
    (X.hiddenLaw b).pr A = (highRawLaw X b).pr
      (fun hi => A ((hiddenSplitEquiv5 X).symm ((fun _ _ => X.y₀), hi))) := by
  classical
  rw [hidden_split_pr, pr_indicator5]
  congr 1
  funext hi
  have he : (fun lo => A ((hiddenSplitEquiv5 X).symm (lo, hi))) =
      (fun _ : HiddenLow5 X => A ((hiddenSplitEquiv5 X).symm ((fun _ _ => X.y₀), hi))) := by
    funext lo
    exact propext (hA hi lo _)
  rw [he, pr_indicator5]
  exact FinProb.expect_const _ _

theorem highOnly_step2_probability (X : Setup5 γ K' χ n N E G) (b : X.Base)
    (K : X.Ty) (hhigh : ∀ ℓ ∈ K.2.1, ∃ i, ℓ = .inr i) :
    (X.hiddenLaw b).pr (fun U => X.step2Fail (b, U) K) =
      (highRawLaw X b).pr (fun hi =>
        X.step2Fail (b, (hiddenSplitEquiv5 X).symm ((fun _ _ => X.y₀), hi)) K) :=
  hidden_pr_highOnly X b _ (fun hi lo lo' => step2Fail_split_low_irrel X b hi lo lo' K hhigh)

theorem step2_high_alarm_bound (X : Setup5 γ K' χ n N E G) (b : X.Base)
    (K : X.Ty) (ε : ℝ) (hε : 0 < ε)
    (hraw : (X.hiddenLaw b).pr (fun U => X.step2Fail (b, U) K) ≤ ε ^ 2) :
    (highRawLaw X b).pr (fun hi => ε < (lowRawLaw X b).pr
      (fun lo => X.step2Fail (b, (hiddenSplitEquiv5 X).symm (lo, hi)) K)) ≤ ε := by
  rw [hidden_split_pr] at hraw
  have hMarkov := (highRawLaw X b).markov
    (fun hi => (lowRawLaw X b).pr (fun lo =>
      X.step2Fail (b, (hiddenSplitEquiv5 X).symm (lo, hi)) K)) ε
      (fun hi => pr_nonneg5 _ _) hε
  let F := fun hi => (lowRawLaw X b).pr (fun lo =>
    X.step2Fail (b, (hiddenSplitEquiv5 X).symm (lo, hi)) K)
  have hm : (highRawLaw X b).pr (fun hi => ε < F hi) ≤
      (highRawLaw X b).pr (fun hi => ε ≤ F hi) := pr_mono5 _ (fun _ h => h.le)
  apply (hm.trans hMarkov).trans
  apply (div_le_iff₀ hε).2
  nlinarith [hraw]


theorem high_step3_mean_bound (X : Setup5 γ K' χ n N E G) (b : X.Base)
    (r : X.AbsRecord) (i : CoarseKey5 n) (ε : ℝ)
    (hraw : ∀ hi : HiddenHigh5 X, ∀ lo : HiddenLow5 X,
      (FinProb.pi fun _ : Fin (X.p.s n) => X.prior b (.inr i)).expect (fun θ =>
        X.step3Rate (X.withCol (b, (hiddenSplitEquiv5 X).symm (lo, hi)) (.inr i) θ) r) ≤ ε) :
    (highRawLaw X b).expect (fun hi => (lowRawLaw X b).expect (fun lo =>
      X.step3Rate (b, (hiddenSplitEquiv5 X).symm (lo, hi)) r)) ≤ ε := by
  classical
  have hupdate (hi : HiddenHigh5 X) (lo : HiddenLow5 X) (θ : Fin (X.p.s n) → Fin N) :
      X.withCol (b, (hiddenSplitEquiv5 X).symm (lo, hi)) (.inr i) θ =
        (b, (hiddenSplitEquiv5 X).symm (lo, Function.update hi i θ)) := by
    apply Prod.ext
    · rfl
    funext ℓ
    cases ℓ with
    | inl k =>
      change Function.update ((hiddenSplitEquiv5 X).symm (lo, hi)) (.inr i) θ (.inl k) = lo k
      exact Function.update_of_ne (by simp : (Sum.inl k : X.Key) ≠ Sum.inr i) _ _
    | inr j =>
      by_cases he : j = i
      · subst j
        change Function.update ((hiddenSplitEquiv5 X).symm (lo, hi)) (.inr i) θ (.inr i) =
          Function.update hi i θ i
        exact (Function.update_self (.inr i) θ ((hiddenSplitEquiv5 X).symm (lo, hi))).trans
          (Function.update_self i θ hi).symm
      · change Function.update ((hiddenSplitEquiv5 X).symm (lo, hi)) (.inr i) θ (.inr j) =
          Function.update hi i θ j
        exact (Function.update_of_ne (Sum.inr_injective.ne he) θ
          ((hiddenSplitEquiv5 X).symm (lo, hi))).trans (Function.update_of_ne he θ hi).symm
  have hmean (lo : HiddenLow5 X) : (highRawLaw X b).expect (fun hi =>
      X.step3Rate (b, (hiddenSplitEquiv5 X).symm (lo, hi)) r) ≤ ε := by
    apply Lane_sol_s05_h5l.pi_expect_update_bound
      (fun i : CoarseKey5 n => FinProb.pi fun _ : Fin (X.p.s n) => X.prior b (.inr i))
      i _ ε (fun _ _ => X.y₀)
    intro hi
    have h := hraw hi lo
    convert h using 1
    congr 1
    funext θ
    exact congrArg (fun H => X.step3Rate H r) (hupdate hi lo θ).symm
  have hswap :
      (highRawLaw X b).expect (fun hi => (lowRawLaw X b).expect (fun lo =>
        X.step3Rate (b, (hiddenSplitEquiv5 X).symm (lo, hi)) r)) =
      (lowRawLaw X b).expect (fun lo => (highRawLaw X b).expect (fun hi =>
        X.step3Rate (b, (hiddenSplitEquiv5 X).symm (lo, hi)) r)) := by
    unfold FinProb.expect
    simp only [Finset.mul_sum]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro lo _
    apply Finset.sum_congr rfl
    intro hi _
    ring
  rw [hswap]
  calc
    _ ≤ (lowRawLaw X b).expect (fun _ => ε) := FinProb.expect_mono _ hmean
    _ = ε := FinProb.expect_const _ _


theorem hidden_split_signShift (X : Setup5 γ K' χ n N E G)
    (t : CubeVertex (X.p.m n)) (lo : HiddenLow5 X) (hi : HiddenHigh5 X) :
    hiddenSignShift5 X t ((hiddenSplitEquiv5 X).symm (lo, hi)) =
      (hiddenSplitEquiv5 X).symm (hiddenLowShift5 X t lo, hi) := by
  simp only [hiddenSignShift5, Equiv.trans_apply, Equiv.apply_symm_apply,
    Equiv.prodCongr_apply, Prod.map_apply, Equiv.refl_apply]

theorem step2_lowPr_signShift (X : Setup5 γ K' χ n N E G) (b : X.Base)
    (hi : HiddenHigh5 X) (t : CubeVertex (X.p.m n)) (K : X.Ty)
    {j : Fin (X.p.J n + 1)} (hlevel : K.2.2 = some j) :
    (lowRawLaw X b).pr (fun lo =>
      X.step2Fail (b, (hiddenSplitEquiv5 X).symm (lo, hi)) (signShiftType5 X t K)) =
      (lowRawLaw X b).pr (fun lo =>
        X.step2Fail (b, (hiddenSplitEquiv5 X).symm (lo, hi)) K) := by
  classical
  calc
    _ = (lowRawLaw X b).pr (fun lo =>
        X.step2Fail (b, (hiddenSplitEquiv5 X).symm (hiddenLowShift5 X t lo, hi))
          (signShiftType5 X t K)) := (low_shift_pr X b t _).symm
    _ = _ := by
      apply pr_congr5
      intro lo
      have h := step2Fail_signShiftLow5 X (b, (hiddenSplitEquiv5 X).symm (lo, hi)) t K hlevel
      simpa only [signShiftHistory5, hidden_split_signShift] using h

theorem opt_lowPr_signShift (X : Setup5 γ K' χ n N E G) (b : X.Base)
    (hi : HiddenHigh5 X) (t t₀ : CubeVertex (X.p.m n)) (K : X.Ty)
    (hlevel : K.2.2 = none) (hhigh : ∀ ℓ ∈ K.2.1, ∃ i, ℓ = .inr i) :
    (lowRawLaw X b).pr (fun lo =>
      X.optFail (b, (hiddenSplitEquiv5 X).symm (lo, hi)) K (shiftSignVector5 t t₀)) =
      (lowRawLaw X b).pr (fun lo =>
        X.optFail (b, (hiddenSplitEquiv5 X).symm (lo, hi)) K t₀) := by
  classical
  calc
    _ = (lowRawLaw X b).pr (fun lo =>
        X.optFail (b, (hiddenSplitEquiv5 X).symm (hiddenLowShift5 X t lo, hi)) K
          (shiftSignVector5 t t₀)) := (low_shift_pr X b t _).symm
    _ = _ := by
      apply pr_congr5
      intro lo
      have h := optFail_signShiftHigh5 X (b, (hiddenSplitEquiv5 X).symm (lo, hi)) t t₀ K hlevel hhigh
      simpa only [signShiftHistory5, hidden_split_signShift,
        signShiftType5_eq_of_highKeys X t K hhigh] using h


end
end HypercubeRamsey.Lane_sol_s05_h23
