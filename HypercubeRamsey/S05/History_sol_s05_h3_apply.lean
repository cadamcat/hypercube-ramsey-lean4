import HypercubeRamsey.S05.History_sol_s05_h3_groups

namespace HypercubeRamsey.Lane_sol_s05_h23

open Classical Filter OAI.HypercubeRamsey Lane_q_s05_h23
open Lane_sol_s05_hist1b Lane_sol_s05_h5l
open scoped BigOperators Topology
noncomputable section
set_option maxHeartbeats 400000
set_option maxRecDepth 4096
set_option synthInstance.maxSize 1024

variable {γ K' χ : ℝ} {n N : ℕ} {E : Fin N → Fin N → Prop} {G : Colour}

 theorem onlyHighKeys_signShift (X : Setup5 γ K' χ n N E G)
    (t : CubeVertex (X.p.m n)) (K : X.Ty) :
    onlyHighKeys X (signShiftType5 X t K) ↔ onlyHighKeys X K := by
  constructor
  · intro h ℓ hℓ
    obtain ⟨i, hi⟩ := h (signShiftKey5 X t ℓ) (Finset.mem_image.mpr ⟨ℓ, hℓ, rfl⟩)
    exact ⟨i, (signShiftKey5 X t).injective hi⟩
  · intro h ℓ hℓ
    obtain ⟨k, hk, rfl⟩ := Finset.mem_image.mp hℓ
    obtain ⟨i, rfl⟩ := h k hk
    exact ⟨i, rfl⟩

 theorem step2HighBad_signShift (X : Setup5 γ K' χ n N E G) (b : X.Base)
    (hi : HiddenHigh5 X) (t : CubeVertex (X.p.m n)) (K : X.Ty)
    {j : Fin (X.p.J n + 1)} (hj : K.2.2 = some j) :
    step2HighBad X b (signShiftType5 X t K) hi ↔ step2HighBad X b K hi := by
  classical
  by_cases hh : onlyHighKeys X K
  · rw [signShiftType5_eq_of_highKeys X t K hh]
  · have hn : ¬ onlyHighKeys X (signShiftType5 X t K) :=
      fun h => hh ((onlyHighKeys_signShift X t K).mp h)
    unfold step2HighBad
    simp only [hh, hn, ite_false, signShiftType5_keys_card, signShiftType5_segs]
    rw [step2_lowPr_signShift X b hi t K hj]

 theorem stage3Patterns_good_step2 (X : Setup5 γ K' χ n N E G) (b : X.Base)
    (hi : HiddenHigh5 X)
    (hg : ∀ q (i : Stage2GroupAlarm5 (halfDeltaSetup X) q), ¬ stage3PatternBad X b q i hi) :
    ∀ K, X.TypeOccurs K → ¬ step2HighBad X b K hi := by
  intro K hK
  obtain ⟨x, hx, rfl⟩ := hK
  let K₀ : X.Ty := X.g.evenType (X.p.J n) x
  let t := X.g.sign x
  by_cases hl : X.g.severity x ≤ X.p.J n
  · obtain ⟨j, p, hp⟩ := stage2LowPatternAt_of_role5 (halfDeltaSetup X) x hx hl
    let Kc : X.Ty := p.1
    have hc : Kc = signShiftType5 X t K₀ := hp.trans (signShiftType_halfDelta X t K₀)
    have hj : K₀.2.2 = some j := by
      have h : Kc.2.2 = some j := p.2.2.2.1
      rw [hc, signShiftType5_level] at h
      exact h
    have hf := hg (X.g.key x) (.lowStep2 j p)
    change ¬ step2HighBad X b Kc hi at hf
    have hn : ¬ step2HighBad X b (signShiftType5 X t K₀) hi := by rw [← hc]; exact hf
    exact fun h => hn ((step2HighBad_signShift X b hi t K₀ hj).mpr h)
  · obtain ⟨p, hp⟩ := stage2HighPatternAt_of_role5 (halfDeltaSetup X) x hx hl
    have hc : (p.1 : X.Ty) = K₀ := hp
    have hf := hg (X.g.key x) (.highStep2 p)
    change ¬ step2HighBad X b p.1 hi at hf
    rw [hc] at hf
    exact hf

 theorem stage3Patterns_good_optional (X : Setup5 γ K' χ n N E G) (b : X.Base)
    (hi : HiddenHigh5 X)
    (hg : ∀ q (i : Stage2GroupAlarm5 (halfDeltaSetup X) q), ¬ stage3PatternBad X b q i hi) :
    ∀ K t, X.OptOccurs K t → (lowRawLaw X b).pr
      (fun lo => X.optFail (b, (hiddenSplitEquiv5 X).symm (lo, hi)) K t) ≤
        Real.exp (-(X.p.delta * (X.p.q0 * X.p.uStarSeg n)) / 8) := by
  intro K t hOpt
  obtain ⟨x, hx, hK, hOptKey⟩ := hOpt
  have ho : X.OptOccurs K t := ⟨x, hx, hK, hOptKey⟩
  have hn : K.2.2 = none := optOccurs_high5 X K t ho
  have hh := typeOccurs_highKeys5 X K ⟨x, hx, hK⟩ hn
  have hl : ¬ X.g.severity x ≤ X.p.J n := by
    intro h
    have he := hn
    rw [← hK] at he
    simp [ChunkGeometry5.evenType, h] at he
  obtain ⟨p, hp⟩ := stage2HighPatternAt_of_role5 (halfDeltaSetup X) x hx hl
  have hc : (p.1 : X.Ty) = K := hp.trans hK
  have hpOpt : ∃ t, (halfDeltaSetup X).OptOccurs p.1 t := by
    refine ⟨t, ?_⟩
    change X.OptOccurs p.1 t
    rw [hc]
    exact ho
  have hf := hg (X.g.key x) (.highOptional ⟨p, hpOpt⟩)
  change ¬ optHighBad X b p.1 hi at hf
  have hpraw : (lowRawLaw X b).pr
      (fun lo => X.optFail (b, (hiddenSplitEquiv5 X).symm (lo, hi)) K default) =
      (lowRawLaw X b).pr (fun lo => X.optFail (b, (hiddenSplitEquiv5 X).symm (lo, hi)) K t) := by
    have h := opt_lowPr_signShift X b hi t t K hn hh
    rw [shiftSignVector_self5 t] at h
    exact h
  rw [hc] at hf
  unfold optHighBad at hf
  rw [hpraw] at hf
  exact le_of_not_gt hf

 theorem stage3Groups_good_records (X : Setup5 γ K' χ n N E G) (b : X.Base)
    (cH : ℝ) (hi : HiddenHigh5 X) (hg : ∀ q, ¬ stage3GroupBad X b cH q hi) :
    ∀ r, X.RecOccurs r → (∃ q, r.1 = .inr q) →
      highRecordMean X b r hi ≤ Real.exp (-(cH * X.p.s n) / 2) := by
  intro r hr hright
  obtain ⟨q, hkey⟩ := hright
  obtain ⟨t, r', he⟩ := normalizedHighRecordAt_exists X q r hr hkey
  have hn : ¬ (Real.exp (-(cH * X.p.s n) / 2) < highRecordMean X b r'.1 hi) :=
    fun h => hg q (Or.inr ⟨r', h⟩)
  have hm := occurring_high_mask_none X r hr q hkey
  have hf : highRecordMean X b r'.1 hi = highRecordMean X b r hi := by
    rw [he]
    exact step3_lowExpect_signShift X b hi t r q hkey hm
  rw [hf] at hn
  exact le_of_not_gt hn

 def stage3Request (cH : Pre15 → ℝ) : ParamReq5 where
  Kcap := fun _ => 0
  Kpp := fun _ => 0
  Kh := fun _ => 0
  K1 := fun x => 16 / x.1.2.2.2.1
  K2 := fun _ => 0
  KD := fun _ => 0
  Ks := fun x => 2 * ((signatureConstant : ℝ) + 204) / cH x.1.1.1
  KB := fun _ => 0
  alpha := fun _ => 1
  alpha_pos := by intro x; norm_num

 theorem stage3Law_exists (X : Setup5 γ K' χ n N E G) (b : X.Base) (cH : ℝ)
    (hcH : 0 < cH) (hraw : Stage3RawBounds X b cH)
    (hm : 2 ≤ X.p.m n) (hD : signatureConstant ≤ X.p.m n)
    (hTm : X.p.T n ≤ X.p.m n) (hTJ : X.p.T n ≤ X.p.J n) (hJ : 1 ≤ X.p.J n)
    (hK1 : 16 / X.p.delta ≤ X.p.K1)
    (hKs : 2 * ((signatureConstant : ℝ) + 204) / cH ≤ X.p.Ks)
    (hhalf : highGroupBudget X.p n < 1 / 2)
    (hdeg : (coarseCountBound 4 : ℝ) * highGroupBudget X.p n ≤ 1 / 4) :
    ∃ ν : FinProb (HiddenHigh5 X),
      (∀ hi, ν.w hi ≠ 0 → ∀ K, X.TypeOccurs K → onlyHighKeys X K → ∀ lo : HiddenLow5 X,
        ¬ X.step2Fail (b, (hiddenSplitEquiv5 X).symm (lo, hi)) K) ∧
      (∀ hi, ν.w hi ≠ 0 → ∀ K, X.TypeOccurs K → ¬ onlyHighKeys X K →
        (lowRawLaw X b).pr (fun lo => X.step2Fail (b, (hiddenSplitEquiv5 X).symm (lo, hi)) K) ≤
          ((K.2.1.card : ℝ) + 1) * Real.exp (-(X.p.delta * (X.p.q0 * X.p.typeSegs n K)) / 8)) ∧
      (∀ hi, ν.w hi ≠ 0 → ∀ K t, X.OptOccurs K t →
        (lowRawLaw X b).pr (fun lo => X.optFail (b, (hiddenSplitEquiv5 X).symm (lo, hi)) K t) ≤
          Real.exp (-(X.p.delta * (X.p.q0 * X.p.uStarSeg n)) / 8)) ∧
      (∀ hi, ν.w hi ≠ 0 → ∀ r, X.RecOccurs r → (∃ q, r.1 = .inr q) →
        highRecordMean X b r hi ≤ Real.exp (-(cH * X.p.s n) / 2)) ∧
      (∀ hi, ν.w hi ≠ 0 → ∀ q h, (X.prior b (.inr q)).w (hi q h) ≠ 0) := by
  obtain ⟨ν, hgood, hsupp⟩ := highGroup_avoidance X b cH hcH hraw hm hD hTm hTJ hJ hK1 hKs hhalf hdeg
  have hg (hi) (hhi : ν.w hi ≠ 0) (q) (i : Stage2GroupAlarm5 (halfDeltaSetup X) q) :
      ¬ stage3PatternBad X b q i hi := fun h => hgood hi hhi q (Or.inl ⟨i, h⟩)
  refine ⟨ν, ?_, ?_, ?_, ?_, hsupp⟩
  · intro hi hhi K hK hh lo
    have hf := stage3Patterns_good_step2 X b hi (hg hi hhi) K hK
    unfold step2HighBad at hf
    rw [if_pos hh] at hf
    exact fun h => hf ((step2Fail_split_low_irrel X b hi lo (fun _ _ => X.y₀) K hh).mp h)
  · intro hi hhi K hK hn
    have hf := stage3Patterns_good_step2 X b hi (hg hi hhi) K hK
    unfold step2HighBad at hf
    rw [if_neg hn] at hf
    exact le_of_not_gt hf
  · intro hi hhi
    exact stage3Patterns_good_optional X b hi (hg hi hhi)
  · intro hi hhi
    exact stage3Groups_good_records X b cH hi (hgood hi hhi)

end
end HypercubeRamsey.Lane_sol_s05_h23
