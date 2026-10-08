import HypercubeRamsey.S05.History_sol_s05_h3_scopes

namespace HypercubeRamsey.Lane_sol_s05_h23

open Classical OAI.HypercubeRamsey Lane_q_s05_h23
open Lane_sol_s05_hist1b Lane_sol_s05_h5l
open scoped BigOperators Topology
noncomputable section
set_option maxHeartbeats 400000
set_option maxRecDepth 4096
set_option synthInstance.maxSize 1024

variable {γ K' χ : ℝ} {n N : ℕ} {E : Fin N → Fin N → Prop} {G : Colour}

 def onlyHighKeys (X : Setup5 γ K' χ n N E G) (K : X.Ty) : Prop :=
  ∀ ℓ ∈ K.2.1, ∃ i : CoarseKey5 n, ℓ = .inr i

 def step2HighBad (X : Setup5 γ K' χ n N E G) (b : X.Base) (K : X.Ty)
    (hi : HiddenHigh5 X) : Prop := by
  classical
  exact if onlyHighKeys X K then
    X.step2Fail (b, (hiddenSplitEquiv5 X).symm ((fun _ _ => X.y₀), hi)) K
  else ((K.2.1.card : ℝ) + 1) * Real.exp (-(X.p.delta * (X.p.q0 * X.p.typeSegs n K)) / 8) <
    (lowRawLaw X b).pr (fun lo => X.step2Fail (b, (hiddenSplitEquiv5 X).symm (lo, hi)) K)

 def optHighBad (X : Setup5 γ K' χ n N E G) (b : X.Base) (K : X.Ty)
    (hi : HiddenHigh5 X) : Prop :=
  Real.exp (-(X.p.delta * (X.p.q0 * X.p.uStarSeg n)) / 8) <
    (lowRawLaw X b).pr (fun lo => X.optFail (b, (hiddenSplitEquiv5 X).symm (lo, hi)) K default)

structure Stage3RawBounds (X : Setup5 γ K' χ n N E G) (b : X.Base) (cH : ℝ) : Prop where
  step2 : ∀ K, X.TypeOccurs K → (X.hiddenLaw b).pr (fun U => X.step2Fail (b, U) K) ≤
    ((K.2.1.card : ℝ) + 1) * Real.exp (-(X.p.delta * (X.p.q0 * X.p.typeSegs n K)) / 4)
  optional : ∀ K t, X.OptOccurs K t → (X.hiddenLaw b).pr (fun U => X.optFail (b, U) K t) ≤
    Real.exp (-(X.p.delta * (X.p.q0 * X.p.uStarSeg n)) / 4)
  record : ∀ r, X.RecOccurs r → ∀ q : CoarseKey5 n, r.1 = .inr q →
    (highRawLaw X b).expect (highRecordMean X b r) ≤ Real.exp (-(cH * X.p.s n))

private theorem strict_markov_coeff {Ω : Type*} [Fintype Ω] (P : FinProb Ω)
    (f : Ω → ℝ) (A e : ℝ) (hf : ∀ ω, 0 ≤ f ω) (hA : 1 ≤ A) (he : 0 < e)
    (hmean : P.expect f ≤ A * e ^ 2) : P.pr (fun ω => A * e < f ω) ≤ A * e := by
  have hA0 : 0 < A := by linarith
  have ht : 0 < A * e := mul_pos hA0 he
  have hp := P.markov f (A * e) hf ht
  have hm : P.pr (fun ω => A * e < f ω) ≤ P.pr (fun ω => A * e ≤ f ω) :=
    pr_mono5 P (fun _ h => h.le)
  have hdiv : P.expect f / (A * e) ≤ e := by
    apply (div_le_iff₀ ht).2
    nlinarith [hmean]
  exact (hm.trans hp).trans (hdiv.trans (le_mul_of_one_le_left he.le hA))

 theorem step2HighBad_pr (X : Setup5 γ K' χ n N E G) (b : X.Base) (K : X.Ty)
    (hraw : (X.hiddenLaw b).pr (fun U => X.step2Fail (b, U) K) ≤
      ((K.2.1.card : ℝ) + 1) * Real.exp (-(X.p.delta * (X.p.q0 * X.p.typeSegs n K)) / 4)) :
    (highRawLaw X b).pr (step2HighBad X b K) ≤
      ((K.2.1.card : ℝ) + 1) * Real.exp (-(X.p.delta * (X.p.q0 * X.p.typeSegs n K)) / 8) := by
  classical
  let A : ℝ := (K.2.1.card : ℝ) + 1
  let e : ℝ := Real.exp (-(X.p.delta * (X.p.q0 * X.p.typeSegs n K)) / 8)
  have he : 0 < e := Real.exp_pos _
  have hA : 1 ≤ A := by
    dsimp [A]
    have hcard : (0 : ℝ) ≤ K.2.1.card := Nat.cast_nonneg _
    linarith
  have he2 : e ^ 2 = Real.exp (-(X.p.delta * (X.p.q0 * X.p.typeSegs n K)) / 4) := by
    dsimp [e]
    rw [pow_two, ← Real.exp_add]
    congr 1
    ring
  change (highRawLaw X b).pr (step2HighBad X b K) ≤ A * e
  unfold step2HighBad
  by_cases hh : onlyHighKeys X K
  · have hpr := highOnly_step2_probability X b K hh
    have he1 : e ≤ 1 := by
      apply Real.exp_le_one_iff.mpr
      have hδ := X.p.hdelta.1
      have hL : (0 : ℝ) ≤ X.p.q0 * X.p.typeSegs n K :=
        mul_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _)
      nlinarith [mul_nonneg hδ.le hL]
    simp only [hh, ite_true]
    rw [← hpr]
    calc
      _ ≤ A * e ^ 2 := by simpa only [A, he2] using hraw
      _ ≤ A * e := mul_le_mul_of_nonneg_left (by nlinarith [he, he1]) (by linarith)
  · have hm : (highRawLaw X b).expect (fun hi => (lowRawLaw X b).pr
        (fun lo => X.step2Fail (b, (hiddenSplitEquiv5 X).symm (lo, hi)) K)) ≤ A * e ^ 2 := by
      rw [← hidden_split_pr X b (fun U => X.step2Fail (b, U) K)]
      simpa only [A, he2] using hraw
    have h := strict_markov_coeff (highRawLaw X b)
      (fun hi => (lowRawLaw X b).pr (fun lo =>
        X.step2Fail (b, (hiddenSplitEquiv5 X).symm (lo, hi)) K)) A e
      (fun _ => pr_nonneg5 _ _) hA he hm
    simp only [hh, ite_false]
    exact h

 theorem optHighBad_pr (X : Setup5 γ K' χ n N E G) (b : X.Base) (K : X.Ty)
    (hraw : (X.hiddenLaw b).pr (fun U => X.optFail (b, U) K default) ≤
      Real.exp (-(X.p.delta * (X.p.q0 * X.p.uStarSeg n)) / 4)) :
    (highRawLaw X b).pr (optHighBad X b K) ≤
      Real.exp (-(X.p.delta * (X.p.q0 * X.p.uStarSeg n)) / 8) := by
  let e := Real.exp (-(X.p.delta * (X.p.q0 * X.p.uStarSeg n)) / 8)
  have he : 0 < e := Real.exp_pos _
  have he2 : e ^ 2 = Real.exp (-(X.p.delta * (X.p.q0 * X.p.uStarSeg n)) / 4) := by
    dsimp [e]
    rw [pow_two, ← Real.exp_add]
    congr 1
    ring
  have hm : (highRawLaw X b).expect (fun hi => (lowRawLaw X b).pr
      (fun lo => X.optFail (b, (hiddenSplitEquiv5 X).symm (lo, hi)) K default)) ≤ 1 * e ^ 2 := by
    rw [← hidden_split_pr X b (fun U => X.optFail (b, U) K default)]
    simpa only [one_mul, he2] using hraw
  have h := strict_markov_coeff (highRawLaw X b)
    (fun hi => (lowRawLaw X b).pr (fun lo =>
      X.optFail (b, (hiddenSplitEquiv5 X).symm (lo, hi)) K default)) 1 e
    (fun _ => pr_nonneg5 _ _) le_rfl he hm
  unfold optHighBad
  simpa only [one_mul, e] using h

 theorem highRecordMean_nonneg (X : Setup5 γ K' χ n N E G) (b : X.Base)
    (r : X.AbsRecord) (hi : HiddenHigh5 X) : 0 ≤ highRecordMean X b r hi := by
  unfold highRecordMean FinProb.expect
  apply Finset.sum_nonneg
  intro lo _
  exact mul_nonneg ((lowRawLaw X b).nonneg lo) (pr_nonneg5 _ _)

 theorem highRecord_bad_pr (X : Setup5 γ K' χ n N E G) (b : X.Base) (cH : ℝ)
    (hraw : Stage3RawBounds X b cH) (q : CoarseKey5 n) (r : NormalizedHighRecordAt X q) :
    (highRawLaw X b).pr (fun hi => Real.exp (-(cH * X.p.s n) / 2) < highRecordMean X b r.1 hi) ≤
      Real.exp (-(cH * X.p.s n) / 2) := by
  obtain ⟨r₀, t, hr₀, hkey, heq⟩ := r.2.2
  have hm := occurring_high_mask_none X r₀ hr₀ q hkey
  have hf : highRecordMean X b r.1 = highRecordMean X b r₀ := by
    funext hi
    rw [heq]
    exact step3_lowExpect_signShift X b hi t r₀ q hkey hm
  let e := Real.exp (-(cH * X.p.s n) / 2)
  have he : 0 < e := Real.exp_pos _
  have he2 : e ^ 2 = Real.exp (-(cH * X.p.s n)) := by
    dsimp [e]
    rw [pow_two, ← Real.exp_add]
    congr 1
    ring
  have hmean : (highRawLaw X b).expect (highRecordMean X b r.1) ≤ 1 * e ^ 2 := by
    rw [hf, one_mul, he2]
    exact hraw.record r₀ hr₀ q hkey
  have h := strict_markov_coeff (highRawLaw X b) (highRecordMean X b r.1) 1 e
    (highRecordMean_nonneg X b r.1) le_rfl he hmean
  simpa only [one_mul, e] using h

end
end HypercubeRamsey.Lane_sol_s05_h23
