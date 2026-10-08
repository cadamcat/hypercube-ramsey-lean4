import HypercubeRamsey.S05.History_sol_s05_h3_alarms

namespace HypercubeRamsey.Lane_sol_s05_h23

open Classical OAI.HypercubeRamsey Lane_q_s05_h23
open Lane_sol_s05_hist1b Lane_sol_s05_h5l
open scoped BigOperators Topology
noncomputable section
set_option maxHeartbeats 400000
set_option maxRecDepth 4096
set_option synthInstance.maxSize 1024

variable {γ K' χ : ℝ} {n N : ℕ} {E : Fin N → Fin N → Prop} {G : Colour}


 theorem signShiftType_halfDelta (X : Setup5 γ K' χ n N E G)
    (t : CubeVertex (X.p.m n)) (K : X.Ty) :
    signShiftType5 (halfDeltaSetup X) t K = signShiftType5 X t K := by
  classical
  have hk (k : X.Key) : signShiftKey5 (halfDeltaSetup X) t k = signShiftKey5 X t k := by
    cases k <;> rfl
  apply Prod.ext
  · rfl
  apply Prod.ext
  · ext k
    change k ∈ K.2.1.image (signShiftKey5 (halfDeltaSetup X) t) ↔
      k ∈ K.2.1.image (signShiftKey5 X t)
    constructor
    · intro h
      obtain ⟨ℓ, hℓ, he⟩ := Finset.mem_image.mp h
      exact Finset.mem_image.mpr ⟨ℓ, hℓ, (hk ℓ).symm.trans he⟩
    · intro h
      obtain ⟨ℓ, hℓ, he⟩ := Finset.mem_image.mp h
      exact Finset.mem_image.mpr ⟨ℓ, hℓ, (hk ℓ).trans he⟩
  · rfl


 def stage3PatternBad (X : Setup5 γ K' χ n N E G) (b : X.Base)
    (q : CoarseKey5 n) (i : Stage2GroupAlarm5 (halfDeltaSetup X) q) (hi : HiddenHigh5 X) : Prop :=
  match i with
  | .lowStep2 _ p => step2HighBad X b p.1 hi
  | .highStep2 p => step2HighBad X b p.1 hi
  | .highOptional p => optHighBad X b p.1.1 hi
  | _ => False

 def stage3PatternBudget (X : Setup5 γ K' χ n N E G) (q : CoarseKey5 n)
    (i : Stage2GroupAlarm5 (halfDeltaSetup X) q) : ℝ :=
  stage2GroupAlarmBudget5 (halfDeltaSetup X) q i

private theorem exp_half_gap (δ L : ℝ) :
    Real.exp (-((δ / 2) * L) / 4) = Real.exp (-(δ * L) / 8) := by
  congr 1
  ring

 theorem stage3Pattern_pr (X : Setup5 γ K' χ n N E G) (b : X.Base) (cH : ℝ)
    (hraw : Stage3RawBounds X b cH) (q : CoarseKey5 n)
    (i : Stage2GroupAlarm5 (halfDeltaSetup X) q) :
    (highRawLaw X b).pr (stage3PatternBad X b q i) ≤ stage3PatternBudget X q i := by
  classical
  have hz : (highRawLaw X b).pr (fun _ => False) = 0 := by unfold FinProb.pr; simp
  cases i with
  | lowStep1 j p ℓ =>
    change (highRawLaw X b).pr (fun _ => False) ≤ Real.exp _
    rw [hz]
    exact (Real.exp_pos _).le
  | highStep1 p ℓ =>
    change (highRawLaw X b).pr (fun _ => False) ≤ Real.exp _
    rw [hz]
    exact (Real.exp_pos _).le
  | lowCap j h =>
    change (highRawLaw X b).pr (fun _ => False) ≤ Real.exp _
    rw [hz]
    exact (Real.exp_pos _).le
  | highCap h =>
    change (highRawLaw X b).pr (fun _ => False) ≤ Real.exp _
    rw [hz]
    exact (Real.exp_pos _).le
  | lowStep2 j p =>
    rcases p.2.2.2.2 with ⟨x, hx, hK⟩
    let K₀ : X.Ty := X.g.evenType (X.p.J n) x
    let t := X.g.sign x
    let Kc : X.Ty := p.1
    have hK' : Kc = signShiftType5 X t K₀ := by
      exact hK.trans (signShiftType_halfDelta X t K₀)
    have hj : K₀.2.2 = some j := by
      have h := p.2.2.2.1
      change Kc.2.2 = some j at h
      rw [hK', signShiftType5_level] at h
      exact h
    have hc : (X.hiddenLaw b).pr (fun U => X.step2Fail (b, U) Kc) ≤
        ((Kc.2.1.card : ℝ) + 1) * Real.exp (-(X.p.delta * (X.p.q0 * X.p.typeSegs n Kc)) / 4) := by
      calc
        _ = (X.hiddenLaw b).pr (fun U => X.step2Fail (b, U) K₀) := by
          rw [hK']
          exact step2FailPr_signShiftLowSimple5 X b t K₀ hj
        _ ≤ ((K₀.2.1.card : ℝ) + 1) * Real.exp (-(X.p.delta * (X.p.q0 * X.p.typeSegs n K₀)) / 4) :=
          hraw.step2 K₀ ⟨x, hx, rfl⟩
        _ = _ := by
          rw [hK']
          have hcard := signShiftType5_keys_card X t K₀
          have hseg := signShiftType5_segs X t K₀
          rw [hcard, hseg]
    change (highRawLaw X b).pr (step2HighBad X b p.1) ≤
      ((p.1.2.1.card : ℝ) + 1) * Real.exp (-((X.p.delta / 2) * (X.p.q0 * X.p.typeSegs n p.1)) / 4)
    rw [exp_half_gap]
    exact step2HighBad_pr X b Kc hc
  | highStep2 p =>
    rcases p.2.2.2.2 with ⟨x, hx, hK⟩
    have hType : X.TypeOccurs p.1 := ⟨x, hx, hK.symm⟩
    change (highRawLaw X b).pr (step2HighBad X b p.1) ≤
      ((p.1.2.1.card : ℝ) + 1) * Real.exp (-((X.p.delta / 2) * (X.p.q0 * X.p.typeSegs n p.1)) / 4)
    rw [exp_half_gap]
    exact step2HighBad_pr X b p.1 (hraw.step2 p.1 hType)
  | highOptional p =>
    rcases p.1.2.2.2.2 with ⟨x, hx, hK⟩
    rcases p.2 with ⟨t, ho⟩
    have ho' : X.OptOccurs p.1.1 t := ho
    have hType : X.TypeOccurs p.1.1 := ⟨x, hx, hK.symm⟩
    have hn : p.1.1.2.2 = none := p.1.2.2.2.1
    have hh := typeOccurs_highKeys5 X p.1.1 hType hn
    let Kc : X.Ty := p.1.1
    let t' : CubeVertex (X.p.m n) := t
    have hp : (X.hiddenLaw b).pr (fun U => X.optFail (b, U) Kc default) =
        (X.hiddenLaw b).pr (fun U => X.optFail (b, U) Kc t') := by
      have h := optFailPr_signShiftHighSimple5 X b t' t' Kc hn hh
      rw [signShiftType5_eq_of_highKeys X t' Kc hh, shiftSignVector_self5 t'] at h
      exact h
    change (highRawLaw X b).pr (optHighBad X b p.1.1) ≤
      Real.exp (-((X.p.delta / 2) * (X.p.q0 * X.p.uStarSeg n)) / 4)
    rw [exp_half_gap]
    apply optHighBad_pr
    rw [hp]
    exact hraw.optional p.1.1 t ho'

 theorem stage3Pattern_budget_sum (X : Setup5 γ K' χ n N E G) (q : CoarseKey5 n)
    (hm : 1 ≤ X.p.m n) (hK1 : 16 / X.p.delta ≤ X.p.K1) :
    (∑ i : Stage2GroupAlarm5 (halfDeltaSetup X) q, stage3PatternBudget X q i) ≤
      stage2GroupBudgetVanishing5 (halfDelta X.p) n := by
  let Y := halfDeltaSetup X
  have hmY : 1 ≤ Y.p.m n := hm
  have hJ := J_le_m_h23 Y.p n hmY
  have hk := halfDelta_K1 X.p hK1
  calc
    _ = ∑ a : Stage2GroupAlarmFlat5 Y q, stage2GroupAlarmFlatBudget5 Y q a :=
      stage2GroupAlarmBudget_sum_eq_flat5 Y q
    _ ≤ stage2GroupBudgetBound5 Y stage2CoarseCountBase5 :=
      stage2GroupAlarmFlatBudget_sum_le5 Y q hmY hJ hk
    _ ≤ _ := stage2GroupBudgetBound_le_vanishing5 Y hmY hJ hk

 theorem step2Fail_hidden_ext (X : Setup5 γ K' χ n N E G) (H H' : X.KeyHist) (K : X.Ty)
    (hb : H.1 = H'.1) (hc : ∀ ℓ ∈ K.2.1, H.2 ℓ = H'.2 ℓ) :
    X.step2Fail H K ↔ X.step2Fail H' K := by
  have hf := X.blockMass_ext5 H H' K K.2.1 hb hc
  have hd (ℓ : X.Key) := X.blockMass_ext5 H H' K (K.2.1.erase ℓ) hb
    (fun k hk => hc k (Finset.mem_of_mem_erase hk))
  simp only [Setup5.step2Fail, hb, hf, hd]

 theorem optFail_hidden_ext (X : Setup5 γ K' χ n N E G) (H H' : X.KeyHist) (K : X.Ty)
    (t : CubeVertex (X.p.m n)) (hb : H.1 = H'.1)
    (hc : ∀ ℓ ∈ insert (X.optKeyOf K t) K.2.1, H.2 ℓ = H'.2 ℓ) :
    X.optFail H K t ↔ X.optFail H' K t := by
  have hf := X.blockMass_ext5 H H' K (insert (X.optKeyOf K t) K.2.1) hb hc
  have hd := X.blockMass_ext5 H H' K K.2.1 hb
    (fun k hk => hc k (Finset.mem_insert_of_mem hk))
  simp only [Setup5.optFail, hb, hf, hd]

 theorem step2HighBad_depends (X : Setup5 γ K' χ n N E G) (b : X.Base)
    (q : CoarseKey5 n) (K : X.Ty) (hkeys : ∀ ℓ ∈ K.2.1, ℓ.coarse ∈ highGroupScope q) :
    FinProb.DependsOn (step2HighBad X b K) (highGroupScope q) := by
  classical
  intro hi hi' h
  have he (lo : HiddenLow5 X) :
      X.step2Fail (b, (hiddenSplitEquiv5 X).symm (lo, hi)) K ↔
        X.step2Fail (b, (hiddenSplitEquiv5 X).symm (lo, hi')) K := by
    refine step2Fail_hidden_ext X (b, (hiddenSplitEquiv5 X).symm (lo, hi))
      (b, (hiddenSplitEquiv5 X).symm (lo, hi')) K rfl ?_
    intro ℓ hℓ
    cases ℓ with
    | inl k => rfl
    | inr i => exact h i (hkeys (.inr i) hℓ)
  have hp := pr_congr5 (lowRawLaw X b) _ _ he
  unfold step2HighBad
  split_ifs
  · exact propext (he (fun _ _ => X.y₀))
  · rw [hp]

 theorem optHighBad_depends (X : Setup5 γ K' χ n N E G) (b : X.Base)
    (q : CoarseKey5 n) (K : X.Ty)
    (hkeys : ∀ ℓ ∈ insert (X.optKeyOf K default) K.2.1, ℓ.coarse ∈ highGroupScope q) :
    FinProb.DependsOn (optHighBad X b K) (highGroupScope q) := by
  intro hi hi' h
  have he (lo : HiddenLow5 X) :
      X.optFail (b, (hiddenSplitEquiv5 X).symm (lo, hi)) K default ↔
        X.optFail (b, (hiddenSplitEquiv5 X).symm (lo, hi')) K default := by
    refine optFail_hidden_ext X (b, (hiddenSplitEquiv5 X).symm (lo, hi))
      (b, (hiddenSplitEquiv5 X).symm (lo, hi')) K default rfl ?_
    intro ℓ hℓ
    cases ℓ with
    | inl k => rfl
    | inr i => exact h i (hkeys (.inr i) hℓ)
  have hp := pr_congr5 (lowRawLaw X b) _ _ he
  unfold optHighBad
  rw [hp]

 theorem near_key_in_highScope {n : ℕ} (q i : CoarseKey5 n)
    (hi : i ∈ nearCoarseKeys5 q.1) : i ∈ highGroupScope q := by
  have h := nearBinVectors_coord_dist5 q.1 i.1 (Finset.mem_product.mp hi).1
  exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, fun a => (h a).trans (by norm_num : 1 ≤ 2)⟩

 theorem stage3Pattern_depends (X : Setup5 γ K' χ n N E G) (b : X.Base)
    (q : CoarseKey5 n) (i : Stage2GroupAlarm5 (halfDeltaSetup X) q) :
    FinProb.DependsOn (stage3PatternBad X b q i) (highGroupScope q) := by
  classical
  cases i with
  | lowStep1 j p ℓ => exact fun _ _ _ => rfl
  | highStep1 p ℓ => exact fun _ _ _ => rfl
  | lowCap j h => exact fun _ _ _ => rfl
  | highCap h => exact fun _ _ _ => rfl
  | lowStep2 j p =>
    apply step2HighBad_depends
    intro ℓ hℓ
    apply near_key_in_highScope
    exact stage2LowPatternAt_gateKeys_coarse5 (halfDeltaSetup X) q j p ℓ (Finset.mem_union.mpr (Or.inl hℓ))
  | highStep2 p =>
    apply step2HighBad_depends
    intro ℓ hℓ
    apply near_key_in_highScope
    exact stage2HighPatternAt_gateKeys_coarse5 (halfDeltaSetup X) q p ℓ (Finset.mem_union.mpr (Or.inl hℓ))
  | highOptional p =>
    apply optHighBad_depends
    intro ℓ hℓ
    rcases Finset.mem_insert.mp hℓ with ht | hs
    · subst ℓ
      have he : (X.optKeyOf p.1.1 default).coarse = q := by
        change p.1.1.1 = q
        exact p.1.2.2.1
      rw [he]
      exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, coarseNear_refl 2 q⟩
    · apply near_key_in_highScope
      exact stage2HighPatternAt_gateKeys_coarse5 (halfDeltaSetup X) q p.1 ℓ (Finset.mem_union.mpr (Or.inl hs))

end
end HypercubeRamsey.Lane_sol_s05_h23
