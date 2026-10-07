import HypercubeRamsey.S05.Centres_sol_s05_centres_scales

namespace HypercubeRamsey.Lane_sol_s05_centres

open Classical OAI.HypercubeRamsey
open scoped BigOperators
set_option maxHeartbeats 400000
set_option synthInstance.maxSize 4096
noncomputable section

variable {γ K' χ : ℝ} {n N : ℕ} {E : Fin N → Fin N → Prop} {G : Colour}
variable (X : Setup5 γ K' χ n N E G)

theorem priorRep_block_hits (H : X.KeyHist) (K : X.Ty) (ℓ : X.Key) (z : X.Block K)
    (y : Fin N) (hb : X.baseLaw.w H.1 ≠ 0) (hz : X.blockBase H.1 K z ≠ 0)
    (hc : K.1.1 ∈ binList5 ℓ.coarse)
    (hp : X.p.typeSegs n K ≤ X.p.uSeg n (ℓ.level + 1))
    (hy : (X.priorRep H.1 ℓ K.1.1 z).w y ≠ 0) : X.BlockHits K z y := by
  have hraw := Lane_q_s05_hist1b.priorRep_raw_nonzero5 X H K ℓ z hb hz hc y hy
  cases hbd : ℓ.coarse.2 with
  | false =>
    have hbin : K.1.1 = ℓ.coarse.1 := by simpa [binList5, hbd] using hc
    have hprior : (X.P.prior.partner H.1.1 ℓ.coarse.1).w y ≠ 0 := by
      have hr := hraw
      simp only [Setup5.colWeight, hbd, Bool.false_eq_true, if_false] at hr
      exact (mul_ne_zero_iff.mp hr).1
    have hparent : H.1.1 ∈ X.P.lab0 := by
      by_contra h
      have hr := Lane_q_s05_hist1b.base_parent_supported X H.1 hb
      exact hr (X.P.lab0_atom _ h)
    have hmem : y ∈ X.P.prior.partnerSet H.1.1 ℓ.coarse.1 := by
      by_contra h
      exact hprior (X.P.prior.partner_support _ _ _ h)
    have hpair := X.partner_related H.1.1 hparent ℓ.coarse.1 y hmem
    intro s i
    have hseg := Lane_q_s05_hist1b.posterior_interior_segment_nonzero5
      X H K ℓ z y hp hc hbd hraw s
    rw [Setup5.segLaw, if_pos hpair] at hseg
    exact (X.S.segment_hits _ _ _ hpair hseg i).2
  | true =>
    have hr := hraw
    simp only [Setup5.colWeight, hbd, if_true] at hr
    have hp0 : X.P.prior.parent.w y ≠ 0 := (mul_ne_zero_iff.mp hr).1
    have hparent : y ∈ X.P.lab0 := by
      by_contra h
      exact hp0 (X.P.lab0_atom _ h)
    have hprior : (X.P.prior.partner y K.1.1).w (H.1.2.1 K.1.1) ≠ 0 := by
      have hf := Finset.prod_ne_zero_iff.mp (mul_ne_zero_iff.mp hr).2 K.1.1 hc
      exact (mul_ne_zero_iff.mp hf).1
    have hmem : H.1.2.1 K.1.1 ∈ X.P.prior.partnerSet y K.1.1 := by
      by_contra h
      exact hprior (X.P.prior.partner_support _ _ _ h)
    have hpair := X.partner_related y hparent K.1.1 (H.1.2.1 K.1.1) hmem
    intro s i
    have hseg := Lane_q_s05_hist1b.posterior_boundary_segment_nonzero5
      X H K ℓ z y hp hc hbd hraw s
    rw [Setup5.segLaw, if_pos hpair] at hseg
    exact (X.S.segment_hits _ _ _ hpair hseg i).1

theorem blockWeight_col_hits (H : X.KeyHist) (K : X.Ty) (ℓ : X.Key)
    (z : X.Block K) (θ : Fin (colLen5 (X.p.s n) ℓ) → Fin N)
    (hb : X.baseLaw.w H.1 ≠ 0) (hz : X.blockBase H.1 K z ≠ 0)
    (hc : K.1.1 ∈ binList5 ℓ.coarse)
    (hp : X.p.typeSegs n K ≤ X.p.uSeg n (ℓ.level + 1)) (hℓ : ℓ ∈ K.2.1)
    (hw : X.blockWeight (X.withCol H ℓ θ) K K.2.1 z ≠ 0)
    (h : Fin (colLen5 (X.p.s n) ℓ)) : X.BlockHits K z (θ h) := by
  have hpw := (mul_ne_zero_iff.mp hw).2
  have hlik := Finset.prod_ne_zero_iff.mp hpw ℓ hℓ
  have hcoord : ratio5 ((X.priorRep H.1 ℓ K.1.1 z).w (θ h))
      ((X.priorDel H.1 ℓ K.1.1 (X.p.typeSegs n K)).w (θ h)) ≠ 0 := by
    have hl : (X.withCol H ℓ θ).2 ℓ = θ := by simp [Setup5.withCol]
    simpa [Setup5.colLik, hl, Setup5.withCol] using (Finset.prod_ne_zero_iff.mp hlik h (Finset.mem_univ _))
  have hrep : (X.priorRep H.1 ℓ K.1.1 z).w (θ h) ≠ 0 := by
    intro he
    apply hcoord
    simp [ratio5, he]
  exact priorRep_block_hits X H K ℓ z (θ h) hb hz hc hp hrep

theorem normalize_support {A : Type*} [Fintype A] [DecidableEq A]
    (f : A → ℝ) (a₀ a : A) (hs : 0 < ∑ x, f x) (ha : (normalize5 f a₀).w a ≠ 0) :
    f a ≠ 0 := by
  have hmax : 0 < ∑ x, max 0 (f x) :=
    hs.trans_le (Finset.sum_le_sum fun x _ => le_max_right _ _)
  have hw : (normalize5 f a₀).w a = max 0 (f a) / ∑ x, max 0 (f x) := by
    simp [normalize5, hmax]
  intro hzero
  apply ha
  simp [hw, hzero]

theorem condCoord_witness {s : ℕ} (P : (Fin s → Fin N) → ℝ)
    (hP : ∀ θ, 0 ≤ P θ) (θ₀ : Fin s → Fin N) (ht : 0 < P θ₀)
    (h : Fin s) (x : Fin N) (hx : (X.condCoord P θ₀ h).w x ≠ 0) :
    ∃ θ, P θ ≠ 0 ∧ (∀ j, j < h → θ j = θ₀ j) ∧ θ h = x := by
  let f : Fin N → ℝ := fun y => ∑ θ : Fin s → Fin N,
    if (∀ j, j < h → θ j = θ₀ j) ∧ θ h = y then P θ else 0
  have hf : ∀ y, 0 ≤ f y := by
    intro y
    exact Finset.sum_nonneg fun θ _ => by split_ifs <;> first | exact hP θ | exact le_rfl
  have hft : 0 < f (θ₀ h) := by
    have hh : P θ₀ ≤ f (θ₀ h) := by
      calc
        _ = (if (∀ j, j < h → θ₀ j = θ₀ j) ∧ θ₀ h = θ₀ h then P θ₀ else 0) := by simp
        _ ≤ f (θ₀ h) := Finset.single_le_sum
          (f := fun θ : Fin s → Fin N =>
            if (∀ j, j < h → θ j = θ₀ j) ∧ θ h = θ₀ h then P θ else 0)
          (fun θ _ => by split_ifs <;> first | exact hP θ | exact le_rfl) (Finset.mem_univ θ₀)
    exact ht.trans_le hh
  have hsum : 0 < ∑ y, f y := hft.trans_le
    (Finset.single_le_sum (fun y _ => hf y) (Finset.mem_univ _))
  have hx' : (normalize5 f X.y₀).w x ≠ 0 := hx
  have hfne := normalize_support f X.y₀ x hsum hx'
  by_contra hnone
  apply hfne
  apply Finset.sum_eq_zero
  intro θ _
  by_cases hg : (∀ j, j < h → θ j = θ₀ j) ∧ θ h = x
  · simp only [if_pos hg]
    by_contra hp
    exact hnone ⟨θ, hp, hg.1, hg.2⟩
  · simp [hg]

theorem step3Post_nonneg {Id : Type} (H : X.KeyHist) (r : X.RecordOn Id)
    (a : X.ArraysOn Id) (θ : Fin (colLen5 (X.p.s n) r.1) → Fin N) :
    0 ≤ X.step3PostOn H r a none θ := by
  unfold Setup5.step3PostOn
  apply div_nonneg
  · apply mul_nonneg
    · apply mul_nonneg
      · exact Finset.prod_nonneg fun h _ => (X.prior H.1 r.1).nonneg (θ h)
      · split_ifs <;> norm_num
    · exact Lane_sol_s05_hist1b.obsLikOn_nonneg X H r a θ none
  · exact Lane_sol_s05_hist1b.step3MassOn_nonneg X H r a none

theorem step3Post_candidate_block {Id : Type} (H : X.KeyHist) (r : X.RecordOn Id)
    (a : X.ArraysOn Id) (θ : Fin (colLen5 (X.p.s n) r.1) → Fin N)
    (ht : X.step3PostOn H r a none θ ≠ 0) (c : Id × X.Ty) (hc : c ∈ r.2.1)
    (hℓ : r.1 ∈ c.2.2.1) (i : Fin (X.p.typeBlocks n c.2)) :
    X.blockWeight (X.withCol H r.1 θ) c.2 c.2.2.1 (a c i) ≠ 0 := by
  have hnum := (div_ne_zero_iff.mp ht).1
  have hg : X.candGateOn H r a θ := by
    by_contra hg
    simp [hg] at hnum
  have hlik := (mul_ne_zero_iff.mp hnum).2
  have hfactor := Finset.prod_ne_zero_iff.mp hlik c (Finset.mem_filter.mpr ⟨hc, hℓ⟩)
  have hi := Finset.prod_ne_zero_iff.mp hfactor i (Finset.mem_univ _)
  have hnone : ¬ X.InRef (none : Option (Id × X.Ty × Finset (Fin X.blockBound))) c i := by
    simp [Setup5.InRef]
  simp only [if_neg hnone] at hi
  have hb : (X.blockLaw (X.withCol H r.1 θ) c.2).w (a c i) ≠ 0 := by
    intro hb
    apply hi
    simp [ratio5, hb]
  have hm : 0 < X.blockMass (X.withCol H r.1 θ) c.2 c.2.2.1 :=
    (mul_pos (Real.exp_pos _) (hg.1 c hc hℓ).1).trans_le (hg.1 c hc hℓ).2
  exact normalize_support (X.blockWeight (X.withCol H r.1 θ) c.2 c.2.2.1)
    (X.fallbackBlock c.2) (a c i) hm hb

theorem high_source_block_hits {Id : Type} (H : X.KeyHist) (r : X.RecordOn Id)
    (a : X.ArraysOn Id) (hbase : X.baseLaw.w H.1 ≠ 0)
    (hpath : 0 < X.step3PostOn H r a none (H.2 r.1))
    (c : Id × X.Ty) (hc : c ∈ r.2.1) (hℓ : r.1 ∈ c.2.2.1)
    (hcover : c.2.1.1 ∈ binList5 r.1.coarse)
    (hprefix : X.p.typeSegs n c.2 ≤ X.p.uSeg n (r.1.level + 1))
    (i : Fin (X.p.typeBlocks n c.2))
    (hblock : X.blockWeight H c.2 c.2.2.1 (a c i) ≠ 0)
    (h : Fin (colLen5 (X.p.s n) r.1)) (x : Fin N)
    (hx : (X.highSource H r a h).w x ≠ 0) : X.BlockHits c.2 (a c i) x := by
  obtain ⟨θ, hθ, _, hcoord⟩ := condCoord_witness X
    (X.step3PostOn H r a none) (step3Post_nonneg X H r a) (H.2 r.1) hpath h x hx
  have hcandidate := step3Post_candidate_block X H r a θ hθ c hc hℓ i
  have hb : X.blockBase H.1 c.2 (a c i) ≠ 0 :=
    (mul_ne_zero_iff.mp (mul_ne_zero_iff.mp hblock).1).1
  have hh := blockWeight_col_hits X H c.2 r.1 (a c i) θ hbase hb hcover hprefix hℓ hcandidate h
  simpa [hcoord] using hh

end
end HypercubeRamsey.Lane_sol_s05_centres
