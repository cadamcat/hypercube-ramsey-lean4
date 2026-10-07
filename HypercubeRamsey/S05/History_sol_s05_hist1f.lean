import HypercubeRamsey.S05.History_sol_s05_hist1b

namespace HypercubeRamsey.Lane_sol_s05_hist1b

open Classical OAI.HypercubeRamsey
open scoped BigOperators
noncomputable section
set_option synthInstance.maxSize 1024

variable {γ K' χ : ℝ} {n N : ℕ} {E : Fin N → Fin N → Prop} {G : Colour}
variable (X : Setup5 γ K' χ n N E G)

theorem withCol_withCol (H : X.KeyHist) (ℓ : X.Key)
    (θ θ' : Fin (colLen5 (X.p.s n) ℓ) → Fin N) :
    X.withCol (X.withCol H ℓ θ) ℓ θ' = X.withCol H ℓ θ' := by
  simp [Setup5.withCol, Function.update_idem]

theorem blockWeight_withCol_eq_of_not_mem (H : X.KeyHist) (K : X.Ty) (S : Finset X.Key)
    (ℓ : X.Key) (θ : Fin (colLen5 (X.p.s n) ℓ) → Fin N) (hℓ : ℓ ∉ S) (z : X.Block K) :
    X.blockWeight (X.withCol H ℓ θ) K S z = X.blockWeight H K S z := by
  unfold Setup5.blockWeight Setup5.withCol
  congr 1
  apply Finset.prod_congr rfl
  intro k hk
  change X.colLik H.1 K k z (Function.update H.2 ℓ θ k) = X.colLik H.1 K k z (H.2 k)
  rw [Function.update_of_ne (show k ≠ ℓ from fun heq => hℓ (heq ▸ hk))]

theorem blockLawOn_withCol_eq_of_not_mem (H : X.KeyHist) (K : X.Ty) (S : Finset X.Key)
    (ℓ : X.Key) (θ : Fin (colLen5 (X.p.s n) ℓ) → Fin N) (hℓ : ℓ ∉ S) :
    X.blockLawOn (X.withCol H ℓ θ) K S = X.blockLawOn H K S := by
  unfold Setup5.blockLawOn
  congr 1
  funext z
  exact blockWeight_withCol_eq_of_not_mem X H K S ℓ θ hℓ z

theorem blockMass_withCol_eq_of_not_mem (H : X.KeyHist) (K : X.Ty) (S : Finset X.Key)
    (ℓ : X.Key) (θ : Fin (colLen5 (X.p.s n) ℓ) → Fin N) (hℓ : ℓ ∉ S) :
    X.blockMass (X.withCol H ℓ θ) K S = X.blockMass H K S := by
  simp only [Setup5.blockMass,
    blockWeight_withCol_eq_of_not_mem X H K S ℓ θ hℓ]

theorem blockLawDel_withCol (H : X.KeyHist) (K : X.Ty) (ℓ : X.Key)
    (θ : Fin (colLen5 (X.p.s n) ℓ) → Fin N) :
    X.blockLawDel (X.withCol H ℓ θ) K ℓ = X.blockLawDel H K ℓ := by
  exact blockLawOn_withCol_eq_of_not_mem X H K (K.2.1.erase ℓ) ℓ θ
    (by simp)

/-- The candidate ratio gate gives absolute continuity of the candidate block law. -/
theorem blockLaw_candidate_support (H : X.KeyHist) (K : X.Ty) (ℓ : X.Key)
    (θ : Fin (colLen5 (X.p.s n) ℓ) → Fin N) (hℓ : ℓ ∈ K.2.1)
    (hd : 0 < X.blockMass H K (K.2.1.erase ℓ))
    (hr : Real.exp (-(X.p.delta * (X.p.q0 * X.p.typeSegs n K)) * colLen5 (X.p.s n) ℓ) *
      X.blockMass H K (K.2.1.erase ℓ) ≤ X.blockMass (X.withCol H ℓ θ) K K.2.1)
    (z : X.Block K) (hz : (X.blockLawDel H K ℓ).w z = 0) :
    (X.blockLaw (X.withCol H ℓ θ) K).w z = 0 := by
  have hf : 0 < X.blockMass (X.withCol H ℓ θ) K K.2.1 :=
    lt_of_lt_of_le (mul_pos (Real.exp_pos _) hd) hr
  have hdw := Lane_q_s05_hist1b.normalize5_weight_eq_div_of_nonneg
    (X.blockWeight H K (K.2.1.erase ℓ)) (X.fallbackBlock K) z
    (Lane_q_s05_hist1b.blockWeight_nonneg X H K (K.2.1.erase ℓ)) hd
  change (normalize5 (X.blockWeight H K (K.2.1.erase ℓ)) (X.fallbackBlock K)).w z = 0 at hz
  rw [hdw] at hz
  have hzero : X.blockWeight H K (K.2.1.erase ℓ) z = 0 :=
    (div_eq_zero_iff.mp hz).resolve_right (ne_of_gt hd)
  have hle := Lane_q_s05_hist1b.blockWeight_withCol_le X H K ℓ z θ hℓ
  rw [hzero, mul_zero] at hle
  have hfzero := le_antisymm hle (Lane_q_s05_hist1b.blockWeight_nonneg X (X.withCol H ℓ θ) K K.2.1 z)
  change (normalize5 (X.blockWeight (X.withCol H ℓ θ) K K.2.1) (X.fallbackBlock K)).w z = 0
  rw [Lane_q_s05_hist1b.normalize5_weight_eq_div_of_nonneg _ _ _
    (Lane_q_s05_hist1b.blockWeight_nonneg X (X.withCol H ℓ θ) K K.2.1) hf, hfzero, zero_div]

theorem blockLaw_candidate_recompose (H : X.KeyHist) (K : X.Ty) (ℓ : X.Key)
    (θ : Fin (colLen5 (X.p.s n) ℓ) → Fin N) (hℓ : ℓ ∈ K.2.1)
    (hd : 0 < X.blockMass H K (K.2.1.erase ℓ))
    (hr : Real.exp (-(X.p.delta * (X.p.q0 * X.p.typeSegs n K)) * colLen5 (X.p.s n) ℓ) *
      X.blockMass H K (K.2.1.erase ℓ) ≤ X.blockMass (X.withCol H ℓ θ) K K.2.1) (z : X.Block K) :
    (X.blockLaw (X.withCol H ℓ θ) K).w z = (X.blockLawDel H K ℓ).w z *
      ratio5 ((X.blockLaw (X.withCol H ℓ θ) K).w z) ((X.blockLawDel H K ℓ).w z) := by
  exact (Lane_q_s05_hist1b.posterior_density_recompose5 _ _
    (fun z hz => blockLaw_candidate_support X H K ℓ θ hℓ hd hr z hz) z).symm

theorem candGateOn_withCol {Id : Type} (H : X.KeyHist) (r : X.RecordOn Id)
    (a : X.ArraysOn Id) (θ θ' : Fin (colLen5 (X.p.s n) r.1) → Fin N) :
    X.candGateOn (X.withCol H r.1 θ') r a θ ↔ X.candGateOn H r a θ := by
  have hm (K : X.Ty) := blockMass_withCol_eq_of_not_mem X H K (K.2.1.erase r.1)
    r.1 θ' (by simp)
  simp only [Setup5.candGateOn, withCol_withCol, hm]

theorem obsLikOn_withCol {Id : Type} (H : X.KeyHist) (r : X.RecordOn Id)
    (a : X.ArraysOn Id) (θ θ' : Fin (colLen5 (X.p.s n) r.1) → Fin N)
    (excl : Option (Id × X.Ty × Finset (Fin X.blockBound))) :
    X.obsLikOn (X.withCol H r.1 θ') r a θ excl = X.obsLikOn H r a θ excl := by
  simp only [Setup5.obsLikOn, withCol_withCol, blockLawDel_withCol]

theorem step3MassOn_withCol {Id : Type} (H : X.KeyHist) (r : X.RecordOn Id)
    (a : X.ArraysOn Id) (θ' : Fin (colLen5 (X.p.s n) r.1) → Fin N)
    (excl : Option (Id × X.Ty × Finset (Fin X.blockBound))) :
    X.step3MassOn (X.withCol H r.1 θ') r a excl = X.step3MassOn H r a excl := by
  simp only [Setup5.step3MassOn, candGateOn_withCol, obsLikOn_withCol]
  rfl

/-- The separately stored low mask belongs to one of the observed arrays. -/
theorem record_mask_mem {Id : Type} (r : X.RecordOn Id) (y : OddRole5 n)
    (μ : X.St.Site → Id) (hr : X.RecordFrom r y μ)
    (c : Id × X.Ty) (M : Finset (Fin X.blockBound)) (hc : r.2.2.2 = some (c.1, c.2, M)) :
    c ∈ r.2.1 := by
  obtain ⟨_, hobs, _, hm⟩ := hr
  rw [hc] at hm
  obtain ⟨_, a, ha, hK, _, hi, _⟩ := hm
  rw [hobs]
  apply Finset.mem_image.mpr
  refine ⟨a, ha, ?_⟩
  exact Prod.ext hi.symm hK.symm

theorem record_ref_mem {Id : Type} (r : X.RecordOn Id) (y : OddRole5 n)
    (μ : X.St.Site → Id) (hr : X.RecordFrom r y μ)
    (c : Id × X.Ty × Option X.Key) (hc : c ∈ r.2.2.1) : (c.1, c.2.1) ∈ r.2.1 := by
  obtain ⟨_, hobs, href, _⟩ := hr
  rw [href] at hc
  obtain ⟨a, ha, heq⟩ := Finset.mem_image.mp hc
  rw [hobs]
  exact Finset.mem_image.mpr ⟨a, (Finset.mem_filter.mp ha).1,
    congrArg (fun e : Id × X.Ty × Option X.Key => (e.1, e.2.1)) heq⟩

theorem candGateOn_arrays_congr {Id : Type} (H : X.KeyHist)
    (r : X.RecordOn Id) (a b : X.ArraysOn Id)
    (hmask : ∀ c M, r.2.2.2 = some (c.1, c.2, M) → c ∈ r.2.1)
    (hab : ∀ c ∈ r.2.1, a c = b c) (θ : Fin (colLen5 (X.p.s n) r.1) → Fin N) :
    X.candGateOn H r a θ ↔ X.candGateOn H r b θ := by
  have hhit (c : Id × X.Ty) (M : Finset (Fin X.blockBound))
      (hc : r.2.2.2 = some (c.1, c.2, M)) (y : Fin N) : X.hitSet a c y = X.hitSet b c y := by
    unfold Setup5.hitSet
    rw [hab c (hmask c M hc)]
  unfold Setup5.candGateOn
  constructor
  · rintro ⟨hd, hm⟩
    refine ⟨hd, ?_⟩
    intro c M hc h
    rw [← hhit c M hc]
    exact hm c M hc h
  · rintro ⟨hd, hm⟩
    refine ⟨hd, ?_⟩
    intro c M hc h
    rw [hhit c M hc]
    exact hm c M hc h

theorem obsLikOn_arrays_congr {Id : Type} (H : X.KeyHist) (r : X.RecordOn Id)
    (a b : X.ArraysOn Id) (hab : ∀ c ∈ r.2.1, a c = b c)
    (θ : Fin (colLen5 (X.p.s n) r.1) → Fin N)
    (excl : Option (Id × X.Ty × Finset (Fin X.blockBound))) :
    X.obsLikOn H r a θ excl = X.obsLikOn H r b θ excl := by
  unfold Setup5.obsLikOn
  apply Finset.prod_congr rfl
  intro c hc
  rw [hab c (Finset.mem_filter.mp hc).1]

theorem step3MassOn_arrays_congr {Id : Type} (H : X.KeyHist)
    (r : X.RecordOn Id) (a b : X.ArraysOn Id)
    (hmask : ∀ c M, r.2.2.2 = some (c.1, c.2, M) → c ∈ r.2.1)
    (hab : ∀ c ∈ r.2.1, a c = b c)
    (excl : Option (Id × X.Ty × Finset (Fin X.blockBound))) :
    X.step3MassOn H r a excl = X.step3MassOn H r b excl := by
  unfold Setup5.step3MassOn
  apply Finset.sum_congr rfl
  intro θ _
  rw [candGateOn_arrays_congr X H r a b hmask hab θ,
    obsLikOn_arrays_congr X H r a b hab θ excl]

/-- Product reference arrays, deleting the target at every type that uses it. -/
def step3Reference (H : X.KeyHist) (r : X.AbsRecord) : FinProb (X.ArraysOn (Fin (X.p.T n))) :=
  FinProb.pi fun c => FinProb.pi fun _ =>
    if r.1 ∈ c.2.2.1 then X.blockLawDel H c.2 r.1 else X.blockLaw H c.2

/-- The part of the candidate gate that uses only history normalizers. -/
def step3DenGate (H : X.KeyHist) (r : X.AbsRecord)
    (θ : Fin (colLen5 (X.p.s n) r.1) → Fin N) : Prop :=
  ∀ c ∈ r.2.1, r.1 ∈ c.2.2.1 →
    0 < X.blockMass H c.2 (c.2.2.1.erase r.1) ∧
      Real.exp (-(X.p.delta * (X.p.q0 * X.p.typeSegs n c.2)) * colLen5 (X.p.s n) r.1) *
        X.blockMass H c.2 (c.2.2.1.erase r.1) ≤ X.blockMass (X.withCol H r.1 θ) c.2 c.2.2.1

theorem array_candidate_recompose (H : X.KeyHist) (r : X.AbsRecord)
    (θ : Fin (colLen5 (X.p.s n) r.1) → Fin N) (hd : step3DenGate X H r θ)
    (c : Fin (X.p.T n) × X.Ty) (hc : c ∈ r.2.1) (a : X.Array c.2) :
    (FinProb.pi fun _ => X.blockLaw (X.withCol H r.1 θ) c.2).w a =
      (FinProb.pi fun _ => if r.1 ∈ c.2.2.1 then X.blockLawDel H c.2 r.1 else X.blockLaw H c.2).w a *
      (if r.1 ∈ c.2.2.1 then ∏ i, ratio5
        ((X.blockLaw (X.withCol H r.1 θ) c.2).w (a i)) ((X.blockLawDel H c.2 r.1).w (a i)) else 1) := by
  by_cases hℓ : r.1 ∈ c.2.2.1
  · simp only [hℓ, ite_true, FinProb.pi]
    rw [← Finset.prod_mul_distrib]
    apply Finset.prod_congr rfl
    intro i _
    exact blockLaw_candidate_recompose X H c.2 r.1 θ hℓ (hd c hc hℓ).1 (hd c hc hℓ).2 (a i)
  · simp only [hℓ, ite_false, mul_one]
    have heq : X.blockLaw (X.withCol H r.1 θ) c.2 = X.blockLaw H c.2 :=
      blockLawOn_withCol_eq_of_not_mem X H c.2 c.2.2.1 r.1 θ hℓ
    rw [heq]

theorem obsLikOn_none_prod (H : X.KeyHist) (r : X.AbsRecord)
    (a : X.ArraysOn (Fin (X.p.T n))) (θ : Fin (colLen5 (X.p.s n) r.1) → Fin N) :
    X.obsLikOn H r a θ none = ∏ c ∈ r.2.1,
      if r.1 ∈ c.2.2.1 then ∏ i, ratio5
        ((X.blockLaw (X.withCol H r.1 θ) c.2).w (a c i)) ((X.blockLawDel H c.2 r.1).w (a c i)) else 1 := by
  simp [Setup5.obsLikOn, Setup5.InRef, Finset.prod_filter]

/-- Marginalize unobserved arrays before changing the observed-array densities. -/
theorem gated_array_pr (H : X.KeyHist) (r : X.AbsRecord)
    (θ : Fin (colLen5 (X.p.s n) r.1) → Fin N)
    (hmask : ∀ c M, r.2.2.2 = some (c.1, c.2, M) → c ∈ r.2.1)
    (F : X.ArraysOn (Fin (X.p.T n)) → Prop)
    (hF : FinProb.DependsOn (fun a => if F a then (1 : ℝ) else 0) r.2.1) :
    (X.recArrayLaw (X.withCol H r.1 θ)).pr (fun a => X.candGateOn H r a θ ∧ F a) =
      (step3Reference X H r).expect (fun a =>
        if X.candGateOn H r a θ ∧ F a then X.obsLikOn H r a θ none else 0) := by
  by_cases hd : step3DenGate X H r θ
  · let L (c : Fin (X.p.T n) × X.Ty) (a : X.Array c.2) :=
      if r.1 ∈ c.2.2.1 then ∏ i, ratio5
        ((X.blockLaw (X.withCol H r.1 θ) c.2).w (a i)) ((X.blockLawDel H c.2 r.1).w (a i)) else 1
    have hA : FinProb.DependsOn
        (fun a => if X.candGateOn H r a θ ∧ F a then (1 : ℝ) else 0) r.2.1 := by
      intro a b hab
      have hgate := candGateOn_arrays_congr X H r a b hmask hab θ
      have hf := hF a b hab
      by_cases hg : X.candGateOn H r a θ
      · have hgb := hgate.mp hg
        simpa only [hg, hgb, true_and] using hf
      · have hgb : ¬ X.candGateOn H r b θ := fun hb => hg (hgate.mpr hb)
        simp [hg, hgb]
    have heq := pi_change_weights
      (fun c : Fin (X.p.T n) × X.Ty => FinProb.pi fun _ => X.blockLaw (X.withCol H r.1 θ) c.2)
      (fun c : Fin (X.p.T n) × X.Ty => FinProb.pi fun _ =>
        if r.1 ∈ c.2.2.1 then X.blockLawDel H c.2 r.1 else X.blockLaw H c.2)
      r.2.1 L (fun a => if X.candGateOn H r a θ ∧ F a then 1 else 0)
      (fun _ _ _ _ => X.y₀) hA
      (fun c hc a => array_candidate_recompose X H r θ hd c hc a)
    have hlik (a : X.ArraysOn (Fin (X.p.T n))) :
        (∏ c ∈ r.2.1, L c (a c)) = X.obsLikOn H r a θ none :=
      (obsLikOn_none_prod X H r a θ).symm
    calc
      _ = (FinProb.pi fun c : Fin (X.p.T n) × X.Ty =>
            FinProb.pi fun _ => X.blockLaw (X.withCol H r.1 θ) c.2).expect
          (fun a => if X.candGateOn H r a θ ∧ F a then 1 else 0) := by
        unfold Setup5.recArrayLaw FinProb.pr FinProb.expect
        apply Finset.sum_congr rfl
        intro a _
        by_cases ha : X.candGateOn H r a θ ∧ F a <;> simp [ha]
      _ = _ := heq
      _ = _ := by
        unfold FinProb.expect step3Reference
        apply Finset.sum_congr rfl
        intro a _
        dsimp only
        rw [hlik]
        by_cases ha : X.candGateOn H r a θ ∧ F a <;> simp [ha]
  · have hgate (a : X.ArraysOn (Fin (X.p.T n))) : ¬ X.candGateOn H r a θ := fun h => hd h.1
    simp [hgate, FinProb.pr, FinProb.expect]

/-- The lower-denominator exception at one record costs its threshold in the raw
target-and-array experiment. No successful-history conditioning is used. -/
theorem step3_lower_tail (H : X.KeyHist) (r : X.AbsRecord) (hr : X.RecOccurs r)
    (ε : ℝ) (hε : 0 ≤ ε) :
    (∑ θ : Fin (colLen5 (X.p.s n) r.1) → Fin N,
      (∏ h, (X.prior H.1 r.1).w (θ h)) *
        (X.recArrayLaw (X.withCol H r.1 θ)).pr (fun a =>
          X.candGateOn (X.withCol H r.1 θ) r a θ ∧
            X.step3MassOn (X.withCol H r.1 θ) r a none < ε)) ≤ ε := by
  obtain ⟨y, μ, hrecord⟩ := hr
  have hmask := record_mask_mem X r y μ hrecord
  let P := FinProb.pi fun _ : Fin (colLen5 (X.p.s n) r.1) => X.prior H.1 r.1
  let Q := step3Reference X H r
  let L := fun θ a => if X.candGateOn H r a θ then X.obsLikOn H r a θ none else 0
  have hmass (a : X.ArraysOn (Fin (X.p.T n))) :
      X.step3MassOn H r a none = ∑ θ, P.w θ * L θ a := by
    unfold Setup5.step3MassOn
    apply Finset.sum_congr rfl
    intro θ _
    dsimp [P, L, FinProb.pi]
    by_cases hg : X.candGateOn H r a θ <;> simp [hg]
  have hbound := Lane_q_s05_hist1b.finite_subdensity_lower_bad5 P Q L (fun _ => True)
    (fun a => X.step3MassOn H r a none) ε (fun a => by simpa only [ite_true] using hmass a) hε
  have hdep : FinProb.DependsOn
      (fun a => if X.step3MassOn H r a none < ε then (1 : ℝ) else 0) r.2.1 := by
    intro a b hab
    dsimp only
    rw [step3MassOn_arrays_congr X H r a b hmask hab]
  have heq : (∑ θ : Fin (colLen5 (X.p.s n) r.1) → Fin N,
      (∏ h, (X.prior H.1 r.1).w (θ h)) *
        (X.recArrayLaw (X.withCol H r.1 θ)).pr (fun a =>
          X.candGateOn (X.withCol H r.1 θ) r a θ ∧
            X.step3MassOn (X.withCol H r.1 θ) r a none < ε)) =
      ∑ θ, ∑ a, if X.step3MassOn H r a none < ε then P.w θ * Q.w a * L θ a else 0 := by
    apply Finset.sum_congr rfl
    intro θ _
    simp only [candGateOn_withCol, step3MassOn_withCol]
    rw [gated_array_pr X H r θ hmask (fun a => X.step3MassOn H r a none < ε) hdep]
    unfold FinProb.expect
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro a _
    dsimp [P, Q, L, FinProb.pi]
    by_cases hg : X.candGateOn H r a θ <;>
      by_cases hm : X.step3MassOn H r a none < ε <;> simp [hg, hm] <;> ring
  rw [heq]
  simpa only [true_and] using hbound

end
end HypercubeRamsey.Lane_sol_s05_hist1b
