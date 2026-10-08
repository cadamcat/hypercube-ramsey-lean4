import HypercubeRamsey.S05.History_sol_s05_h3_records

namespace HypercubeRamsey.Lane_sol_s05_h23

open Classical OAI.HypercubeRamsey Lane_q_s05_h23
open scoped BigOperators
noncomputable section
set_option maxHeartbeats 400000
set_option maxRecDepth 4096
set_option synthInstance.maxSize 1024

variable {γ K' χ : ℝ} {n N : ℕ} {E : Fin N → Fin N → Prop} {G : Colour}


theorem shiftHighRecord_key (X : Setup5 γ K' χ n N E G)
    (t : CubeVertex (X.p.m n)) (r : X.AbsRecord) :
    (shiftHighRecord X t r).1 = r.1 := rfl

section Covariance

variable (X : Setup5 γ K' χ n N E G) (H : X.KeyHist)
    (t : CubeVertex (X.p.m n)) (r : X.AbsRecord) (j : CoarseKey5 n)
    (hkey : r.1 = .inr j) (hmask : r.2.2.2 = none)
    (a : X.ArraysOn (Fin (X.p.T n)))

include hkey hmask in
 theorem step3MassOn_high_signShift
    (ex : Option (Fin (X.p.T n) × X.Ty × Finset (Fin X.blockBound))) :
    X.step3MassOn (signShiftHistory5 X t H) (shiftHighRecord X t r)
      (arraysSignPerm X t a) (ex.map (refSignMap X t)) = X.step3MassOn H r a ex := by
  unfold Setup5.step3MassOn
  apply Finset.sum_congr rfl
  intro θ _
  have hg := propext (candGateOn_high_signShift X H t r j hkey hmask a θ)
  rw [hg, obsLikOn_high_signShift X H t r j hkey a θ ex]
  rfl

include hkey hmask in
 theorem step3PostOn_high_signShift
    (ex : Option (Fin (X.p.T n) × X.Ty × Finset (Fin X.blockBound)))
    (θ : Fin (colLen5 (X.p.s n) r.1) → Fin N) :
    X.step3PostOn (signShiftHistory5 X t H) (shiftHighRecord X t r)
      (arraysSignPerm X t a) (ex.map (refSignMap X t)) θ = X.step3PostOn H r a ex θ := by
  unfold Setup5.step3PostOn
  have hg := propext (candGateOn_high_signShift X H t r j hkey hmask a θ)
  rw [hg, obsLikOn_high_signShift X H t r j hkey a θ ex,
    step3MassOn_high_signShift X H t r j hkey hmask a ex]
  rfl

include hkey in
 theorem high_column_signShift :
    (signShiftHistory5 X t H).2 (shiftHighRecord X t r).1 = H.2 r.1 := by
  rcases r with ⟨ℓ, data⟩
  change ℓ = .inr j at hkey
  subst ℓ
  rfl

include hkey hmask in
 theorem highSource_high_signShift (h : Fin (colLen5 (X.p.s n) r.1)) :
    X.highSource (signShiftHistory5 X t H) (shiftHighRecord X t r)
      (arraysSignPerm X t a) h = X.highSource H r a h := by
  have hp : X.step3PostOn (signShiftHistory5 X t H) (shiftHighRecord X t r)
      (arraysSignPerm X t a) none = X.step3PostOn H r a none := by
    funext θ
    exact step3PostOn_high_signShift X H t r j hkey hmask a none θ
  unfold Setup5.highSource
  rw [hp, high_column_signShift X H t r j hkey]
  rfl

include hkey hmask in
 theorem highDeleted_high_signShift
    (c : Fin (X.p.T n) × X.Ty × Finset (Fin X.blockBound))
    (h : Fin (colLen5 (X.p.s n) r.1)) :
    X.highDeleted (signShiftHistory5 X t H) (shiftHighRecord X t r)
      (arraysSignPerm X t a) (refSignMap X t c) h = X.highDeleted H r a c h := by
  have hp : X.step3PostOn (signShiftHistory5 X t H) (shiftHighRecord X t r)
      (arraysSignPerm X t a) (some (refSignMap X t c)) = X.step3PostOn H r a (some c) := by
    funext θ
    exact step3PostOn_high_signShift X H t r j hkey hmask a (some c) θ
  unfold Setup5.highDeleted
  rw [hp, high_column_signShift X H t r j hkey]
  rfl

include hkey hmask in
 theorem HighCapped_high_signShift :
    X.HighCapped (signShiftHistory5 X t H) (shiftHighRecord X t r)
      (arraysSignPerm X t a) ↔ X.HighCapped H r a := by
  constructor
  · rintro ⟨R, hc, hs⟩
    refine ⟨R, hc, ?_⟩
    intro h y hy
    have hh := hs h y hy
    rw [highSource_high_signShift X H t r j hkey hmask a h] at hh
    exact hh
  · rintro ⟨R, hc, hs⟩
    refine ⟨R, hc, ?_⟩
    intro h y hy
    rw [highSource_high_signShift X H t r j hkey hmask a h]
    exact hs h y hy

end Covariance

private theorem price_feasibility_reindex {A B Z : Type*} [Fintype A] [Fintype B]
    (e : A ≃ B) (good : Z → Prop) (good' : Z → Prop)
    (cost : Z → A → ℝ) (cost' : Z → B → ℝ) (bound : A → ℝ) (bound' : B → ℝ)
    (hg : ∀ z, good' z ↔ good z)
    (hc : ∀ z c, cost' z (e c) = cost z c)
    (hb : ∀ c, bound' (e c) = bound c) :
    (∀ p : B → ℝ, (∀ c, 0 ≤ p c) → (∑ c, p c = 1) →
      ∃ z, good' z ∧ ∑ c, p c * cost' z c ≤ ∑ c, p c * bound' c) ↔
    (∀ p : A → ℝ, (∀ c, 0 ≤ p c) → (∑ c, p c = 1) →
      ∃ z, good z ∧ ∑ c, p c * cost z c ≤ ∑ c, p c * bound c) := by
  classical
  constructor
  · intro h p hp hsum
    let q : B → ℝ := fun c => p (e.symm c)
    have hq : ∑ c, q c = 1 := by
      rw [← e.sum_comp (fun c => q c)]
      simpa only [q, Equiv.symm_apply_apply] using hsum
    obtain ⟨z, hz, hcost⟩ := h q (fun c => hp (e.symm c)) hq
    refine ⟨z, (hg z).mp hz, ?_⟩
    have heq : (∑ c, q c * cost' z c) = ∑ c, p c * cost z c := by
      rw [← e.sum_comp (fun c => q c * cost' z c)]
      simp only [q, Equiv.symm_apply_apply, hc]
    have heq' : (∑ c, q c * bound' c) = ∑ c, p c * bound c := by
      rw [← e.sum_comp (fun c => q c * bound' c)]
      simp only [q, Equiv.symm_apply_apply, hb]
    simpa only [heq, heq'] using hcost
  · intro h p hp hsum
    let q : A → ℝ := fun c => p (e c)
    have hq : ∑ c, q c = 1 := by
      rw [show (∑ c, q c) = ∑ c, p c from e.sum_comp p]
      exact hsum
    obtain ⟨z, hz, hcost⟩ := h q (fun c => hp (e c)) hq
    refine ⟨z, (hg z).mpr hz, ?_⟩
    have heq : (∑ c, q c * cost z c) = ∑ c, p c * cost' z c := by
      rw [← e.sum_comp (fun c => p c * cost' z c)]
      simp only [q, hc]
    have heq' : (∑ c, q c * bound c) = ∑ c, p c * bound' c := by
      rw [← e.sum_comp (fun c => p c * bound' c)]
      simp only [q, hb]
    simpa only [heq, heq'] using hcost

noncomputable def refSignEquiv (X : Setup5 γ K' χ n N E G) (H : X.KeyHist)
    (t : CubeVertex (X.p.m n)) (r : X.AbsRecord) (a : X.ArraysOn (Fin (X.p.T n))) :
    {c // c ∈ X.refsOn H r a} ≃
      {c // c ∈ X.refsOn (signShiftHistory5 X t H) (shiftHighRecord X t r)
        (arraysSignPerm X t a)} :=
  Equiv.ofBijective
    (fun c => ⟨refSignMap X t c.1, by
      rw [refsOn_signShift]
      exact Finset.mem_image.mpr ⟨c.1, c.2, rfl⟩⟩)
    ⟨by
      intro c d h
      apply Subtype.ext
      exact refSignMap_injective X t (congrArg Subtype.val h), by
      intro c
      have hc : c.1 ∈ (X.refsOn H r a).image (refSignMap X t) := by
        simpa only [refsOn_signShift] using c.2
      obtain ⟨d, hd, he⟩ := Finset.mem_image.mp hc
      exact ⟨⟨d, hd⟩, Subtype.ext he⟩⟩

theorem refSignEquiv_apply (X : Setup5 γ K' χ n N E G) (H : X.KeyHist)
    (t : CubeVertex (X.p.m n)) (r : X.AbsRecord) (a : X.ArraysOn (Fin (X.p.T n)))
    (c : {c // c ∈ X.refsOn H r a}) :
    (refSignEquiv X H t r a c).1 = refSignMap X t c.1 := rfl

theorem refLen_signShift (X : Setup5 γ K' χ n N E G)
    (t : CubeVertex (X.p.m n)) (c : Fin (X.p.T n) × X.Ty × Finset (Fin X.blockBound)) :
    X.refLen (refSignMap X t c).2.1 (refSignMap X t c).2.2 = X.refLen c.2.1 c.2.2 := rfl

section Prices

variable (X : Setup5 γ K' χ n N E G) (H : X.KeyHist)
    (t : CubeVertex (X.p.m n)) (r : X.AbsRecord) (j : CoarseKey5 n)
    (hkey : r.1 = .inr j) (hmask : r.2.2.2 = none)
    (a : X.ArraysOn (Fin (X.p.T n)))

include hkey hmask in
 theorem highDeletionCost_high_signShift
    (R : FinProb (Fin (colLen5 (X.p.s n) r.1) × Fin N))
    (c : {c // c ∈ X.refsOn H r a}) (h : Fin (colLen5 (X.p.s n) r.1)) (y : Fin N) :
    highDeletionCost5 R (fun d h' => X.highDeleted (signShiftHistory5 X t H)
      (shiftHighRecord X t r) (arraysSignPerm X t a) d.1 h')
      (refSignEquiv X H t r a c) h y =
        highDeletionCost5 R (fun d h' => X.highDeleted H r a d.1 h') c h y := by
  have hd : X.highDeleted (signShiftHistory5 X t H) (shiftHighRecord X t r)
      (arraysSignPerm X t a) (refSignEquiv X H t r a c).1 h = X.highDeleted H r a c.1 h := by
    change X.highDeleted (signShiftHistory5 X t H) (shiftHighRecord X t r)
      (arraysSignPerm X t a) (refSignMap X t c.1) h = X.highDeleted H r a c.1 h
    exact highDeleted_high_signShift X H t r j hkey hmask a c.1 h
  exact congrArg (fun Q : Law N => max 0 (Real.log
    (R.w (h, y) / (Q.w y / (colLen5 (X.p.s n) r.1 : ℝ))))) hd

include hkey hmask in
 theorem HighPriceFeasible_high_signShift :
    X.HighPriceFeasible (signShiftHistory5 X t H) (shiftHighRecord X t r)
      (arraysSignPerm X t a) ↔ X.HighPriceFeasible H r a := by
  let e := refSignEquiv X H t r a
  let cap := fun R : FinProb (Fin (colLen5 (X.p.s n) r.1) × Fin N) =>
    ∀ h y, R.w (h, y) ≤ 2 * Real.exp (X.p.DH n) / ((colLen5 (X.p.s n) r.1 : ℝ) * N)
  let good := fun R : FinProb (Fin (colLen5 (X.p.s n) r.1) × Fin N) =>
    cap R ∧ ∀ h y, R.w (h, y) ≠ 0 → (X.highSource H r a h).w y ≠ 0
  let good' := fun R : FinProb (Fin (colLen5 (X.p.s n) r.1) × Fin N) =>
    cap R ∧ ∀ h y, R.w (h, y) ≠ 0 →
      (X.highSource (signShiftHistory5 X t H) (shiftHighRecord X t r)
        (arraysSignPerm X t a) h).w y ≠ 0
  let cost := fun (R : FinProb (Fin (colLen5 (X.p.s n) r.1) × Fin N)) (c : {c // c ∈ X.refsOn H r a}) =>
    ∑ h, ∑ y, R.w (h, y) *
      highDeletionCost5 R (fun d h' => X.highDeleted H r a d.1 h') c h y
  let cost' := fun (R : FinProb (Fin (colLen5 (X.p.s n) r.1) × Fin N))
      (c : {c // c ∈ X.refsOn (signShiftHistory5 X t H) (shiftHighRecord X t r)
        (arraysSignPerm X t a)}) =>
    ∑ h, ∑ y, R.w (h, y) * highDeletionCost5 R (fun d h' =>
      X.highDeleted (signShiftHistory5 X t H) (shiftHighRecord X t r)
        (arraysSignPerm X t a) d.1 h') c h y
  let bound := fun c : {c // c ∈ X.refsOn H r a} =>
    X.p.a 4 * (X.refLen c.1.2.1 c.1.2.2 : ℝ)
  let bound' := fun
      c : {c // c ∈ X.refsOn (signShiftHistory5 X t H) (shiftHighRecord X t r)
        (arraysSignPerm X t a)} => X.p.a 4 * (X.refLen c.1.2.1 c.1.2.2 : ℝ)
  have hg : ∀ R, good' R ↔ good R := by
    intro R
    simp only [good, good', highSource_high_signShift X H t r j hkey hmask a]
  have hc : ∀ R c, cost' R (e c) = cost R c := by
    intro R c
    dsimp only [cost', cost, e]
    simp only [highDeletionCost_high_signShift X H t r j hkey hmask a]
  have hb : ∀ c, bound' (e c) = bound c := by
    intro c
    dsimp only [bound', bound, e]
    rw [refSignEquiv_apply, refLen_signShift]
  have h := price_feasibility_reindex e good good' cost cost' bound bound' hg hc hb
  unfold Setup5.HighPriceFeasible
  change
    (∀ price : {c // c ∈ X.refsOn (signShiftHistory5 X t H) (shiftHighRecord X t r)
        (arraysSignPerm X t a)} → ℝ,
      (∀ c, 0 ≤ price c) → (∑ c, price c = 1) →
      ∃ R, cap R ∧ (∀ h y, R.w (h, y) ≠ 0 →
        (X.highSource (signShiftHistory5 X t H) (shiftHighRecord X t r)
          (arraysSignPerm X t a) h).w y ≠ 0) ∧
        ∑ c, price c * cost' R c ≤ ∑ c, price c * bound' c) ↔
    (∀ price : {c // c ∈ X.refsOn H r a} → ℝ,
      (∀ c, 0 ≤ price c) → (∑ c, price c = 1) →
      ∃ R, cap R ∧ (∀ h y, R.w (h, y) ≠ 0 → (X.highSource H r a h).w y ≠ 0) ∧
        ∑ c, price c * cost R c ≤ ∑ c, price c * bound c)
  simpa only [good, good', and_assoc] using h

end Prices

section FailureRates

variable (X : Setup5 γ K' χ n N E G) (H : X.KeyHist)
    (t : CubeVertex (X.p.m n)) (r : X.AbsRecord) (j : CoarseKey5 n)
    (hkey : r.1 = .inr j) (hmask : r.2.2.2 = none)
    (a : X.ArraysOn (Fin (X.p.T n)))

include hkey hmask in
 theorem step3FailOn_high_signShift :
    X.step3FailOn (signShiftHistory5 X t H) (shiftHighRecord X t r)
      (arraysSignPerm X t a) ↔ X.step3FailOn H r a := by
  have ht : (signShiftHistory5 X t H).2 r.1 = H.2 r.1 :=
    high_column_signShift X H t r j hkey
  have hg := candGateOn_high_signShift X H t r j hkey hmask a (H.2 r.1)
  have hm : X.step3MassOn (signShiftHistory5 X t H) (shiftHighRecord X t r)
      (arraysSignPerm X t a) none = X.step3MassOn H r a none :=
    step3MassOn_high_signShift X H t r j hkey hmask a none
  have hd (c : Fin (X.p.T n) × X.Ty × Finset (Fin X.blockBound)) :
      X.step3MassOn (signShiftHistory5 X t H) (shiftHighRecord X t r)
        (arraysSignPerm X t a) (some (refSignMap X t c)) = X.step3MassOn H r a (some c) :=
    step3MassOn_high_signShift X H t r j hkey hmask a (some c)
  have href :
      (∃ c ∈ X.refsOn (signShiftHistory5 X t H) (shiftHighRecord X t r)
        (arraysSignPerm X t a), X.step3MassOn H r a none <
          Real.exp (-(X.p.delta * X.refLen c.2.1 c.2.2 * colLen5 (X.p.s n) r.1)) *
            X.step3MassOn (signShiftHistory5 X t H) (shiftHighRecord X t r)
              (arraysSignPerm X t a) (some c)) ↔
      (∃ c ∈ X.refsOn H r a, X.step3MassOn H r a none <
        Real.exp (-(X.p.delta * X.refLen c.2.1 c.2.2 * colLen5 (X.p.s n) r.1)) *
          X.step3MassOn H r a (some c)) := by
    rw [refsOn_signShift]
    simp only [Finset.exists_mem_image, refLen_signShift, hd]
  have hc := HighCapped_high_signShift X H t r j hkey hmask a
  have hp := HighPriceFeasible_high_signShift X H t r j hkey hmask a
  simp only [Setup5.step3FailOn, shiftHighRecord_key, ht, hg, hm, href, hc, hp]

include hkey hmask in
 theorem step3Rate_high_signShift :
    X.step3Rate (signShiftHistory5 X t H) (shiftHighRecord X t r) = X.step3Rate H r := by
  classical
  unfold Setup5.step3Rate FinProb.pr
  rw [← (arraysSignPerm X t).sum_comp]
  apply Finset.sum_congr rfl
  intro a _
  simp only [step3FailOn_high_signShift X H t r j hkey hmask a,
    recArrayLaw_signShift_weight]

end FailureRates

theorem low_shift_expect (X : Setup5 γ K' χ n N E G) (b : X.Base)
    (t : CubeVertex (X.p.m n)) (f : HiddenLow5 X → ℝ) :
    (lowRawLaw X b).expect (fun lo => f (hiddenLowShift5 X t lo)) =
      (lowRawLaw X b).expect f := by
  unfold FinProb.expect
  have h := (hiddenLowShift5 X t).sum_comp
    (fun lo => (lowRawLaw X b).w lo * f lo)
  simpa only [low_shift_weight] using h

theorem step3_lowExpect_signShift (X : Setup5 γ K' χ n N E G) (b : X.Base)
    (hi : HiddenHigh5 X) (t : CubeVertex (X.p.m n)) (r : X.AbsRecord) (j : CoarseKey5 n)
    (hkey : r.1 = .inr j) (hmask : r.2.2.2 = none) :
    (lowRawLaw X b).expect (fun lo =>
      X.step3Rate (b, (hiddenSplitEquiv5 X).symm (lo, hi)) (shiftHighRecord X t r)) =
    (lowRawLaw X b).expect (fun lo =>
      X.step3Rate (b, (hiddenSplitEquiv5 X).symm (lo, hi)) r) := by
  calc
    _ = (lowRawLaw X b).expect (fun lo =>
      X.step3Rate (b, (hiddenSplitEquiv5 X).symm (hiddenLowShift5 X t lo, hi))
        (shiftHighRecord X t r)) :=
      (low_shift_expect X b t (fun lo =>
        X.step3Rate (b, (hiddenSplitEquiv5 X).symm (lo, hi)) (shiftHighRecord X t r))).symm
    _ = _ := by
      apply congrArg (lowRawLaw X b).expect
      funext lo
      have h := step3Rate_high_signShift X (b, (hiddenSplitEquiv5 X).symm (lo, hi))
        t r j hkey hmask
      simpa only [signShiftHistory5, hidden_split_signShift] using h

end
end HypercubeRamsey.Lane_sol_s05_h23
