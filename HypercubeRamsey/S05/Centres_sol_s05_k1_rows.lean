import HypercubeRamsey.S05.Centres_sol_s05_k1
import HypercubeRamsey.S05.History_sol_s05_1f

namespace HypercubeRamsey.Lane_sol_s05_k1

open Classical OAI.HypercubeRamsey
open scoped BigOperators

noncomputable section
set_option maxHeartbeats 400000
set_option synthInstance.maxSize 4096

variable {γ K' χ : ℝ} {n N : ℕ} {E : Fin N → Fin N → Prop} {G : Colour}
variable (X : Setup5 γ K' χ n N E G)

/-- The high neighbors of a low interface also share one quotient state.
Both inward 13/11 flips preserve the merged fine-count data. -/
theorem low_high_state_unique {m J : ℕ} (g : ChunkGeometry5 n m) (St : CubeStates5 g J)
    (x a b : CubeVertex n) (hax : (cube n).Adj a x) (hbx : (cube n).Adj b x)
    (hx : g.severity x ≤ J) (ha : J < g.severity a) (hb : J < g.severity b) :
    St.stateOf a = St.stateOf b := by
  have hfa := Lane_sol_s05_h5l.high_low_neighbor g J a x hax ha hx
  have hfb := Lane_sol_s05_h5l.high_low_neighbor g J b x hbx hb hx
  obtain ⟨i, hix⟩ := Lane_sol_s05_h5l.adjacent_flip a x hax
  obtain ⟨j, hjx⟩ := Lane_sol_s05_h5l.adjacent_flip b x hbx
  obtain ⟨k, hik, hi0, hi1⟩ := Lane_sol_s05_1f.severity_drop_fringe g a i
    (by rw [← hix]; exact hx.trans_lt ha)
  obtain ⟨l, hjl, hj0, hj1⟩ := Lane_sol_s05_1f.severity_drop_fringe g b j
    (by rw [← hjx]; exact hx.trans_lt hb)
  have hresA (c : Fin n) (hc : c ∈ g.residual) : x c = a c := by
    have hci : c ≠ i := fun he =>
      Finset.disjoint_left.mp (g.chunks_disjoint.2.2.2.2 k) hik (he ▸ hc)
    rw [hix, flipVertex5, Function.update_of_ne hci]
  have hresB (c : Fin n) (hc : c ∈ g.residual) : x c = b c := by
    have hcj : c ≠ j := fun he =>
      Finset.disjoint_left.mp (g.chunks_disjoint.2.2.2.2 l) hjl (he ▸ hc)
    rw [hjx, flipVertex5, Function.update_of_ne hcj]
  have hcoA (t : Fin coarseChunkCount5) : g.coarseCount a t = g.coarseCount x t := by
    have hbits := Lane_sol_s05_h5l.fine_flip_agree_coarse g a i k hik
    rw [← hix] at hbits
    unfold ChunkGeometry5.coarseCount
    apply congrArg Finset.card
    apply Finset.filter_congr
    intro c hc
    have hc' : c ∈ g.coarseCoords := Finset.mem_biUnion.mpr ⟨t, Finset.mem_univ _, hc⟩
    rw [hbits c hc']
  have hcoB (t : Fin coarseChunkCount5) : g.coarseCount b t = g.coarseCount x t := by
    have hbits := Lane_sol_s05_h5l.fine_flip_agree_coarse g b j l hjl
    rw [← hjx] at hbits
    unfold ChunkGeometry5.coarseCount
    apply congrArg Finset.card
    apply Finset.filter_congr
    intro c hc
    have hc' : c ∈ g.coarseCoords := Finset.mem_biUnion.mpr ⟨t, Finset.mem_univ _, hc⟩
    rw [hbits c hc']
  have hfineA (t : Fin m) : mergedFineCount5 g.fineLength (g.fineCount a t) =
      mergedFineCount5 g.fineLength (g.fineCount x t) := by
    have h := Lane_sol_s05_hist1b.fine_flip_outward_merged g a k i hik hi0 hi1 t
    rw [← hix] at h
    exact h.symm
  have hfineB (t : Fin m) : mergedFineCount5 g.fineLength (g.fineCount b t) =
      mergedFineCount5 g.fineLength (g.fineCount x t) := by
    have h := Lane_sol_s05_hist1b.fine_flip_outward_merged g b l j hjl hj0 hj1 t
    rw [← hjx] at h
    exact h.symm
  exact St.data_determine_state a b
    (fun c hc => (hresA c hc).symm.trans (hresB c hc))
    (fun t => (hcoA t).trans (hcoB t).symm)
    (fun t => (hfineA t).trans (hfineB t).symm) (hfa.1.trans hfb.1.symm)

/-- The candidate ratio gate alone gives the block comparison; it does not
require the candidate history to pass the global Step 2 tests. -/
theorem blockLaw_candidate_le (H : X.KeyHist) (K : X.Ty) (ℓ : X.Key)
    (θ : Fin (colLen5 (X.p.s n) ℓ) → Fin N) (hℓ : ℓ ∈ K.2.1)
    (hd : 0 < X.blockMass H K (K.2.1.erase ℓ))
    (hr : Real.exp (-(X.p.delta * (X.p.q0 * X.p.typeSegs n K)) * colLen5 (X.p.s n) ℓ) *
      X.blockMass H K (K.2.1.erase ℓ) ≤ X.blockMass (X.withCol H ℓ θ) K K.2.1)
    (z : X.Block K) :
    (X.blockLaw (X.withCol H ℓ θ) K).w z ≤
      Real.exp (X.p.a 2 * (X.p.q0 * X.p.typeSegs n K) * colLen5 (X.p.s n) ℓ) *
        (X.blockLawDel H K ℓ).w z := by
  let x : ℝ := (X.p.q0 * X.p.typeSegs n K : ℕ) * colLen5 (X.p.s n) ℓ
  let D := X.blockMass H K (K.2.1.erase ℓ)
  let M := X.blockMass (X.withCol H ℓ θ) K K.2.1
  let w := X.blockWeight (X.withCol H ℓ θ) K K.2.1 z
  let v := X.blockWeight H K (K.2.1.erase ℓ) z
  have hD : 0 < D := hd
  have hden : Real.exp (-X.p.delta * x) * D ≤ M := by
    simpa only [D, M, x, Nat.cast_mul, mul_assoc, neg_mul] using hr
  have hM : 0 < M := (mul_pos (Real.exp_pos _) hD).trans_le hden
  have hweight : w ≤ Real.exp (X.p.a 1 * x) * v := by
    simpa only [w, v, x, Nat.cast_mul, mul_assoc] using
      Lane_q_s05_hist1b.blockWeight_withCol_le X H K ℓ z θ hℓ
  have hv : 0 ≤ v := Lane_q_s05_hist1b.blockWeight_nonneg X _ _ _ _
  have hgap : X.p.a 1 + X.p.delta ≤ X.p.a 2 := by
    have hδ := X.p.hdelta_a (1 : Fin 9) (2 : Fin 9) (by decide)
    have ha := X.p.ha_order (1 : Fin 9) (2 : Fin 9) (by decide)
    linarith
  have hx : 0 ≤ x := by dsimp [x]; positivity
  have hrate : Real.exp ((X.p.a 1 + X.p.delta) * x) ≤ Real.exp (X.p.a 2 * x) :=
    Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_right hgap hx)
  have hcancel : Real.exp ((X.p.a 1 + X.p.delta) * x) * (v / D) *
      (Real.exp (-X.p.delta * x) * D) = Real.exp (X.p.a 1 * x) * v := by
    calc
      _ = Real.exp ((X.p.a 1 + X.p.delta) * x) * Real.exp (-X.p.delta * x) * v := by
        field_simp [hD.ne']
      _ = _ := by rw [← Real.exp_add]; congr 1; ring
  have hmiddle : Real.exp (X.p.a 1 * x) * v ≤ Real.exp (X.p.a 2 * x) * (v / D) * M := by
    rw [← hcancel]
    calc
      _ ≤ Real.exp (X.p.a 2 * x) * (v / D) * (Real.exp (-X.p.delta * x) * D) :=
        mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_right hrate (div_nonneg hv hD.le)) (by positivity)
      _ ≤ _ := mul_le_mul_of_nonneg_left hden (by positivity)
  have hnorm : w / M ≤ Real.exp (X.p.a 2 * x) * (v / D) :=
    (div_le_iff₀ hM).mpr (hweight.trans hmiddle)
  have hrep : (X.blockLaw (X.withCol H ℓ θ) K).w z = w / M := by
    simpa only [Setup5.blockLaw, Setup5.blockLawOn, Setup5.blockMass, w, M] using
      Lane_q_s05_hist1b.normalize5_weight_eq_div_of_nonneg
        (X.blockWeight (X.withCol H ℓ θ) K K.2.1) (X.fallbackBlock K) z
        (Lane_q_s05_hist1b.blockWeight_nonneg X _ _ _) hM
  have hdel : (X.blockLawDel H K ℓ).w z = v / D := by
    simpa only [Setup5.blockLawDel, Setup5.blockLawOn, Setup5.blockMass, v, D] using
      Lane_q_s05_hist1b.normalize5_weight_eq_div_of_nonneg
        (X.blockWeight H K (K.2.1.erase ℓ)) (X.fallbackBlock K) z
        (Lane_q_s05_hist1b.blockWeight_nonneg X _ _ _) hD
  simpa only [hrep, hdel, x, Nat.cast_mul, mul_assoc] using hnorm

theorem blockRatio_candidate_le (H : X.KeyHist) (K : X.Ty) (ℓ : X.Key)
    (θ : Fin (colLen5 (X.p.s n) ℓ) → Fin N) (hℓ : ℓ ∈ K.2.1)
    (hd : 0 < X.blockMass H K (K.2.1.erase ℓ))
    (hr : Real.exp (-(X.p.delta * (X.p.q0 * X.p.typeSegs n K)) * colLen5 (X.p.s n) ℓ) *
      X.blockMass H K (K.2.1.erase ℓ) ≤ X.blockMass (X.withCol H ℓ θ) K K.2.1)
    (z : X.Block K) :
    ratio5 ((X.blockLaw (X.withCol H ℓ θ) K).w z) ((X.blockLawDel H K ℓ).w z) ≤
      Real.exp (X.p.a 2 * (X.p.q0 * X.p.typeSegs n K) * colLen5 (X.p.s n) ℓ) :=
  Lane_q_s05_hist1b.ratio5_le_of_mul_le (FinProb.nonneg _ _) (FinProb.nonneg _ _)
    (Real.exp_nonneg _) (blockLaw_candidate_le X H K ℓ θ hℓ hd hr z)

/-- The observed entry count contributing to the low target likelihood.
Target-independent high pools contribute no entries. -/
def observationLength {Id : Type} (r : X.RecordOn Id) : ℕ :=
  ∑ c ∈ r.2.1.filter (fun c => r.1 ∈ c.2.2.1),
    X.p.typeBlocks n c.2 * (X.p.q0 * X.p.typeSegs n c.2)

theorem obsLikOn_le_exp {Id : Type} (H : X.KeyHist) (r : X.RecordOn Id) (a : X.ArraysOn Id)
    (θ : Fin (colLen5 (X.p.s n) r.1) → Fin N) (hg : X.candGateOn H r a θ) :
    X.obsLikOn H r a θ none ≤
      Real.exp (X.p.a 2 * observationLength X r * colLen5 (X.p.s n) r.1) := by
  have hnone (c : Id × X.Ty) (i : Fin (X.p.typeBlocks n c.2)) :
      ¬ X.InRef (none : Option (Id × X.Ty × Finset (Fin X.blockBound))) c i := by
    simp [Setup5.InRef]
  unfold Setup5.obsLikOn
  simp only [hnone, ite_false]
  calc
    _ ≤ ∏ c ∈ r.2.1.filter (fun c => r.1 ∈ c.2.2.1),
        Real.exp (X.p.a 2 * (X.p.typeBlocks n c.2 * (X.p.q0 * X.p.typeSegs n c.2) : ℕ) *
          colLen5 (X.p.s n) r.1) := by
      apply Finset.prod_le_prod₀
      · intro c hc
        exact Finset.prod_nonneg fun i _ =>
          Lane_q_s05_hist1b.ratio5_nonneg (FinProb.nonneg _ _) (FinProb.nonneg _ _)
      · intro c hc
        obtain ⟨hobs, hℓ⟩ := Finset.mem_filter.mp hc
        have hb := hg.1 c hobs hℓ
        calc
          _ ≤ ∏ _i : Fin (X.p.typeBlocks n c.2),
              Real.exp (X.p.a 2 * (X.p.q0 * X.p.typeSegs n c.2) * colLen5 (X.p.s n) r.1) :=
            Finset.prod_le_prod₀
              (fun i _ => Lane_q_s05_hist1b.ratio5_nonneg (FinProb.nonneg _ _) (FinProb.nonneg _ _))
              (fun i _ => blockRatio_candidate_le X H c.2 r.1 θ hℓ hb.1 hb.2 (a c i))
          _ = _ := by
            simp only [Finset.prod_const, Finset.card_univ, Fintype.card_fin]
            rw [← Real.exp_nat_mul]
            congr 1
            push_cast
            ring
    _ = _ := by
      rw [← Real.exp_sum]
      congr 1
      simp only [observationLength, Nat.cast_sum]
      simp_rw [Finset.mul_sum, Finset.sum_mul]

theorem low_key_length (ℓ : X.Key) (hℓ : ℓ.isLeft) : colLen5 (X.p.s n) ℓ = 1 := by
  cases ℓ with
  | inl k => rfl
  | inr k => simp at hℓ

theorem mask_legit_of_gate {Id : Type} (H : X.KeyHist) (r : X.RecordOn Id) (a : X.ArraysOn Id)
    (hl : r.1.isLeft) (hg : X.candGateOn H r a (H.2 r.1))
    (c : Id × X.Ty) (M : Finset (Fin X.blockBound)) (hm : r.2.2.2 = some (c.1, c.2, M))
    (hhigh : c.2.2.2 = none) : X.LegitRef c.2 M := by
  let i : Fin (colLen5 (X.p.s n) r.1) := ⟨0, by rw [low_key_length X r.1 hl]; decide⟩
  obtain ⟨hcard, hmask⟩ := hg.2 c M hm i
  simp only [Setup5.LegitRef, hhigh]
  rw [← hmask]
  exact ⟨by rw [Lane_sol_s05_1f.firstK_card, Nat.min_eq_left hcard],
    (Finset.filter_subset _ _).trans (Finset.filter_subset _ _)⟩

theorem lowPost_gate {Id : Type} (H : X.KeyHist) (r : X.RecordOn Id) (a : X.ArraysOn Id)
    (x : Fin N) (hx : X.step3PostOn H r a none (fun _ => x) ≠ 0) :
    X.candGateOn H r a (fun _ => x) := by
  by_contra hg
  apply hx
  simp only [Setup5.step3PostOn, hg, ite_false, mul_zero, zero_mul, zero_div]

theorem lowPost_observed_hits {Id : Type} (H : X.KeyHist) (r : X.RecordOn Id) (a : X.ArraysOn Id)
    (hl : r.1.isLeft) (hbase : X.baseLaw.w H.1 ≠ 0)
    (c : Id × X.Ty) (hc : c ∈ r.2.1) (hℓ : r.1 ∈ c.2.2.1)
    (hcover : c.2.1.1 ∈ binList5 r.1.coarse)
    (hprefix : X.p.typeSegs n c.2 ≤ X.p.uSeg n (r.1.level + 1))
    (i : Fin (X.p.typeBlocks n c.2)) (hraw : X.blockWeight H c.2 c.2.2.1 (a c i) ≠ 0)
    (x : Fin N) (hx : X.step3PostOn H r a none (fun _ => x) ≠ 0) :
    X.BlockHits c.2 (a c i) x := by
  have hcandidate := Lane_sol_s05_centres.step3Post_candidate_block X H r a (fun _ => x) hx c hc hℓ i
  have hb : X.blockBase H.1 c.2 (a c i) ≠ 0 :=
    (mul_ne_zero_iff.mp (mul_ne_zero_iff.mp hraw).1).1
  let j : Fin (colLen5 (X.p.s n) r.1) := ⟨0, by rw [low_key_length X r.1 hl]; decide⟩
  exact Lane_sol_s05_centres.blockWeight_col_hits X H c.2 r.1 (a c i) (fun _ => x)
    hbase hb hcover hprefix hℓ hcandidate j

theorem lowPost_mask_hits {Id : Type} (H : X.KeyHist) (r : X.RecordOn Id) (a : X.ArraysOn Id)
    (hl : r.1.isLeft) (c : Id × X.Ty) (M : Finset (Fin X.blockBound))
    (hm : r.2.2.2 = some (c.1, c.2, M)) (x : Fin N)
    (hx : X.step3PostOn H r a none (fun _ => x) ≠ 0)
    (j : Fin X.blockBound) (hj : j ∈ M) (i : Fin (X.p.typeBlocks n c.2))
    (hji : X.blockIdx c.2 j = some i) : X.BlockHits c.2 (a c i) x := by
  have hg := lowPost_gate X H r a x hx
  let h : Fin (colLen5 (X.p.s n) r.1) := ⟨0, by rw [low_key_length X r.1 hl]; decide⟩
  have hmask := (hg.2 c M hm h).2
  have hjhit : j ∈ X.hitSet a c x := by
    rw [← hmask] at hj
    exact (Finset.mem_filter.mp hj).1
  obtain ⟨i', hi', hh⟩ := (Finset.mem_filter.mp hjhit).2
  have hii : i' = i := Option.some.inj (hi'.symm.trans hji)
  exact hii ▸ hh

theorem blockIndices_card_le (K : X.Ty) (M : Finset (Fin X.blockBound)) :
    (Finset.univ.filter (fun i : Fin (X.p.typeBlocks n K) =>
      ∃ j ∈ M, X.blockIdx K j = some i)).card ≤ M.card := by
  let S := Finset.univ.filter (fun i : Fin (X.p.typeBlocks n K) =>
    ∃ j ∈ M, X.blockIdx K j = some i)
  let f := Fin.castLE (Lane_sol_s05_hist1b.typeBlocks_le_blockBound X K)
  have hf : Function.Injective f := by
    intro i j h
    exact Fin.ext (congrArg (fun t : Fin X.blockBound => t.val) h)
  have hsub : S.image f ⊆ M := by
    intro t ht
    obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp ht
    obtain ⟨j, hj, hji⟩ := (Finset.mem_filter.mp hi).2
    have hv : j.val = i.val := by
      unfold Setup5.blockIdx at hji
      split_ifs at hji with h
      exact congrArg Fin.val (Option.some.inj hji)
    have he : f i = j := Fin.ext hv.symm
    exact he.symm ▸ hj
  exact (Finset.card_image_of_injective S hf).symm.le.trans (Finset.card_le_card hsub)

theorem deletedEntrySum_le {Id : Type} (r : X.RecordOn Id)
    (c : Id × X.Ty × Finset (Fin X.blockBound)) :
    (∑ d ∈ r.2.1.filter (fun d => r.1 ∈ d.2.2.1), ∑ i : Fin (X.p.typeBlocks n d.2),
      if X.InRef (some c) d i then ((X.p.q0 * X.p.typeSegs n d.2 : ℕ) : ℝ) else 0) ≤
        (X.refLen c.2.1 c.2.2 : ℝ) := by
  let S := r.2.1.filter (fun d => r.1 ∈ d.2.2.1)
  let d₀ := (c.1, c.2.1)
  have hzero (d : Id × X.Ty) (hd : d ≠ d₀) :
      (∑ i : Fin (X.p.typeBlocks n d.2),
        if X.InRef (some c) d i then ((X.p.q0 * X.p.typeSegs n d.2 : ℕ) : ℝ) else 0) = 0 := by
    apply Finset.sum_eq_zero
    intro i _
    have hn : ¬ X.InRef (some c) d i := by
      rintro ⟨e, he, hde, _⟩
      have hec : c = e := Option.some.inj he
      subst e
      exact hd hde
    simp only [hn, ite_false, Nat.cast_zero]
  have hsum : (∑ d ∈ S, ∑ i : Fin (X.p.typeBlocks n d.2),
      if X.InRef (some c) d i then ((X.p.q0 * X.p.typeSegs n d.2 : ℕ) : ℝ) else 0) ≤
      (∑ i : Fin (X.p.typeBlocks n c.2.1),
        if X.InRef (some c) d₀ i then ((X.p.q0 * X.p.typeSegs n c.2.1 : ℕ) : ℝ) else 0) := by
    by_cases hd₀ : d₀ ∈ S
    · rw [Finset.sum_eq_single d₀ (fun d _ hd => hzero d hd) (fun hd => (hd hd₀).elim)]
    · have hz : (∑ d ∈ S, ∑ i : Fin (X.p.typeBlocks n d.2),
          if X.InRef (some c) d i then ((X.p.q0 * X.p.typeSegs n d.2 : ℕ) : ℝ) else 0) = 0 :=
        Finset.sum_eq_zero fun d hd => hzero d (fun he => hd₀ (he ▸ hd))
      rw [hz]
      exact Finset.sum_nonneg fun i _ => by split_ifs <;> positivity
  refine hsum.trans ?_
  have hpred (i : Fin (X.p.typeBlocks n c.2.1)) :
      X.InRef (some c) d₀ i ↔ ∃ j ∈ c.2.2, X.blockIdx c.2.1 j = some i := by
    simp [Setup5.InRef, d₀]
  simp_rw [hpred]
  rw [← Finset.sum_filter]
  simp only [Finset.sum_const, nsmul_eq_mul]
  have hc := Nat.cast_le (α := ℝ).mpr (blockIndices_card_le X c.2.1 c.2.2)
  exact (mul_le_mul_of_nonneg_right hc (Nat.cast_nonneg _)).trans_eq (by
    simp only [Setup5.refLen, Nat.cast_mul])

theorem obsLikOn_delete_le {Id : Type} (H : X.KeyHist) (r : X.RecordOn Id) (a : X.ArraysOn Id)
    (c : Id × X.Ty × Finset (Fin X.blockBound))
    (θ : Fin (colLen5 (X.p.s n) r.1) → Fin N) (hg : X.candGateOn H r a θ) :
    X.obsLikOn H r a θ none ≤
      Real.exp (X.p.a 2 * X.refLen c.2.1 c.2.2 * colLen5 (X.p.s n) r.1) *
        X.obsLikOn H r a θ (some c) := by
  let S := r.2.1.filter (fun d => r.1 ∈ d.2.2.1)
  let L (d : Id × X.Ty) (i : Fin (X.p.typeBlocks n d.2)) :=
    ratio5 ((X.blockLaw (X.withCol H r.1 θ) d.2).w (a d i)) ((X.blockLawDel H d.2 r.1).w (a d i))
  let u (d : Id × X.Ty) (i : Fin (X.p.typeBlocks n d.2)) : ℝ :=
    if X.InRef (some c) d i then (X.p.q0 * X.p.typeSegs n d.2 : ℕ) else 0
  have hpoint (d : Id × X.Ty) (hd : d ∈ S) (i : Fin (X.p.typeBlocks n d.2)) :
      L d i ≤ Real.exp (X.p.a 2 * u d i * colLen5 (X.p.s n) r.1) *
        (if X.InRef (some c) d i then 1 else L d i) := by
    by_cases hi : X.InRef (some c) d i
    · simp only [u, hi, ite_true, mul_one]
      obtain ⟨hobs, hℓ⟩ := Finset.mem_filter.mp hd
      simpa only [L, Nat.cast_mul] using
        blockRatio_candidate_le X H d.2 r.1 θ hℓ (hg.1 d hobs hℓ).1 (hg.1 d hobs hℓ).2 (a d i)
    · simp only [u, hi, ite_false, mul_zero, zero_mul, Real.exp_zero, one_mul]
      exact le_rfl
  have hprod : (∏ d ∈ S, ∏ i, L d i) ≤
      (∏ d ∈ S, ∏ i, Real.exp (X.p.a 2 * u d i * colLen5 (X.p.s n) r.1)) *
        (∏ d ∈ S, ∏ i, if X.InRef (some c) d i then 1 else L d i) := by
    rw [← Finset.prod_mul_distrib]
    apply Finset.prod_le_prod₀
    · intro d _
      exact Finset.prod_nonneg fun i _ => Lane_q_s05_hist1b.ratio5_nonneg (FinProb.nonneg _ _) (FinProb.nonneg _ _)
    · intro d hd
      rw [← Finset.prod_mul_distrib]
      exact Finset.prod_le_prod₀
        (fun i _ => Lane_q_s05_hist1b.ratio5_nonneg (FinProb.nonneg _ _) (FinProb.nonneg _ _))
        (fun i _ => hpoint d hd i)
  have hexp : (∏ d ∈ S, ∏ i, Real.exp (X.p.a 2 * u d i * colLen5 (X.p.s n) r.1)) =
      Real.exp (X.p.a 2 * (∑ d ∈ S, ∑ i, u d i) * colLen5 (X.p.s n) r.1) := by
    simp_rw [← Real.exp_sum]
    congr 1
    simp_rw [Finset.mul_sum, Finset.sum_mul]
  have ha2 : 0 ≤ X.p.a 2 := by
    have horder := X.p.ha_order (0 : Fin 9) (2 : Fin 9) (by decide)
    rw [X.p.ha0] at horder
    linarith
  have hlen : (∑ d ∈ S, ∑ i, u d i) ≤ (X.refLen c.2.1 c.2.2 : ℝ) := deletedEntrySum_le X r c
  have he : Real.exp (X.p.a 2 * (∑ d ∈ S, ∑ i, u d i) * colLen5 (X.p.s n) r.1) ≤
      Real.exp (X.p.a 2 * X.refLen c.2.1 c.2.2 * colLen5 (X.p.s n) r.1) := by
    apply Real.exp_le_exp.mpr
    exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hlen ha2) (Nat.cast_nonneg _)
  rw [hexp] at hprod
  have hnone (d : Id × X.Ty) (i : Fin (X.p.typeBlocks n d.2)) :
      ¬ X.InRef (none : Option (Id × X.Ty × Finset (Fin X.blockBound))) d i := by
    simp [Setup5.InRef]
  have hfull : X.obsLikOn H r a θ none = ∏ d ∈ S, ∏ i, L d i := by
    simp only [Setup5.obsLikOn, hnone, ite_false, S, L]
  have hdel : X.obsLikOn H r a θ (some c) =
      ∏ d ∈ S, ∏ i, if X.InRef (some c) d i then 1 else L d i := rfl
  rw [hfull, hdel]
  exact hprod.trans (mul_le_mul_of_nonneg_right he
    (by rw [← hdel]; exact Lane_sol_s05_hist1b.obsLikOn_nonneg X H r a θ (some c)))

/-- The low Step 3 lower test bounds every posterior atom, including
candidate values different from the realized target. -/
theorem lowPost_cap {Id : Type} (H : X.KeyHist) (r : X.RecordOn Id) (a : X.ArraysOn Id)
    (hl : r.1.isLeft) (hlower : Real.exp (-(X.p.delta * X.p.kPrime n r.1.level)) ≤
      X.step3MassOn H r a none)
    (B : ℝ) (hprior : ∀ x, (N : ℝ) * (X.prior H.1 r.1).w x ≤ Real.exp B) (x : Fin N) :
    (N : ℝ) * X.step3PostOn H r a none (fun _ => x) ≤
      Real.exp (B + X.p.delta * X.p.kPrime n r.1.level + X.p.a 2 * observationLength X r) := by
  have hlen := low_key_length X r.1 hl
  have hM : 0 < X.step3MassOn H r a none := (Real.exp_pos _).trans_le hlower
  by_cases hg : X.candGateOn H r a (fun _ => x)
  · have hlik : X.obsLikOn H r a (fun _ => x) none ≤
        Real.exp (X.p.a 2 * observationLength X r) := by
      simpa only [hlen, Nat.cast_one, mul_one] using obsLikOn_le_exp X H r a (fun _ => x) hg
    have hpr : (∏ h : Fin (colLen5 (X.p.s n) r.1), (X.prior H.1 r.1).w x) =
        (X.prior H.1 r.1).w x := by simp [hlen]
    simp only [Setup5.step3PostOn, hpr, hg, ite_true, mul_one]
    rw [← mul_div_assoc]
    apply (div_le_iff₀ hM).mpr
    have hnum : (N : ℝ) * ((X.prior H.1 r.1).w x * X.obsLikOn H r a (fun _ => x) none) ≤
        Real.exp B * Real.exp (X.p.a 2 * observationLength X r) := by
      rw [← mul_assoc]
      exact mul_le_mul (hprior x) hlik
        (Lane_sol_s05_hist1b.obsLikOn_nonneg X H r a _ none) (Real.exp_nonneg _)
    calc
      _ ≤ _ := hnum
      _ = Real.exp (B + X.p.delta * X.p.kPrime n r.1.level + X.p.a 2 * observationLength X r) *
          Real.exp (-(X.p.delta * X.p.kPrime n r.1.level)) := by
        rw [← Real.exp_add, ← Real.exp_add]
        congr 1
        ring
      _ ≤ _ := mul_le_mul_of_nonneg_left hlower (Real.exp_nonneg _)
  · simp only [Setup5.step3PostOn, hg, ite_false, mul_zero, zero_mul, zero_div]
    exact Real.exp_nonneg _

theorem step3Mass_lower_of_pass {Id : Type} [DecidableEq Id]
    (H : X.KeyHist) (r : X.RecordOn Id) (a : X.ArraysOn Id)
    (hg : X.candGateOn H r a (H.2 r.1)) (hpass : ¬ X.step3FailOn H r a) :
    (match r.1 with
      | .inl k => Real.exp (-(X.p.delta * X.p.kPrime n k.2.2.val))
      | .inr _ => Real.exp (-(X.p.delta * X.p.s n))) ≤ X.step3MassOn H r a none := by
  by_contra h
  exact hpass ⟨hg, Or.inl (lt_of_not_ge h)⟩

theorem step3Mass_delete_lower_of_pass {Id : Type} [DecidableEq Id]
    (H : X.KeyHist) (r : X.RecordOn Id) (a : X.ArraysOn Id)
    (hg : X.candGateOn H r a (H.2 r.1)) (hpass : ¬ X.step3FailOn H r a)
    (c : Id × X.Ty × Finset (Fin X.blockBound)) (hc : c ∈ X.refsOn H r a) :
    Real.exp (-(X.p.delta * X.refLen c.2.1 c.2.2 * colLen5 (X.p.s n) r.1)) *
      X.step3MassOn H r a (some c) ≤ X.step3MassOn H r a none := by
  by_contra h
  exact hpass ⟨hg, Or.inr (Or.inl ⟨c, hc, lt_of_not_ge h⟩)⟩

theorem normalized_dominance {A : Type*} [Fintype A] (p q : A → ℝ) (C D : ℝ)
    (hp : ∀ x, 0 ≤ p x) (hq : ∀ x, 0 ≤ q x) (hC : 0 ≤ C) (hD : 0 < D)
    (hdom : ∀ x, p x ≤ C * q x) (hM : 0 < ∑ x, p x)
    (hden : D * (∑ x, q x) ≤ ∑ x, p x) (x : A) :
    p x / (∑ z, p z) ≤ (C / D) * (q x / ∑ z, q z) := by
  have hsum : (∑ z, p z) ≤ C * (∑ z, q z) := by
    simpa only [Finset.mul_sum] using Finset.sum_le_sum (fun z _ => hdom z)
  have hQ : 0 < ∑ z, q z := by
    by_contra h
    have hQ0 : (∑ z, q z) = 0 := le_antisymm (le_of_not_gt h) (Finset.sum_nonneg fun z _ => hq z)
    rw [hQ0, mul_zero] at hsum
    exact (not_le_of_gt hM) hsum
  calc
    _ ≤ (C * q x) / (∑ z, p z) := div_le_div_of_nonneg_right (hdom x) hM.le
    _ ≤ (C * q x) / (D * ∑ z, q z) :=
      div_le_div_of_nonneg_left (mul_nonneg hC (hq x)) (mul_pos hD hQ) hden
    _ = _ := by field_simp

theorem step3Post_delete_of_likelihood {Id : Type} (H : X.KeyHist) (r : X.RecordOn Id)
    (a : X.ArraysOn Id) (c : Id × X.Ty × Finset (Fin X.blockBound))
    (hM : 0 < X.step3MassOn H r a none)
    (hden : Real.exp (-(X.p.delta * X.refLen c.2.1 c.2.2 * colLen5 (X.p.s n) r.1)) *
      X.step3MassOn H r a (some c) ≤ X.step3MassOn H r a none)
    (hlik : ∀ θ, X.candGateOn H r a θ → X.obsLikOn H r a θ none ≤
      Real.exp (X.p.a 2 * X.refLen c.2.1 c.2.2 * colLen5 (X.p.s n) r.1) *
        X.obsLikOn H r a θ (some c))
    (θ : Fin (colLen5 (X.p.s n) r.1) → Fin N) :
    X.step3PostOn H r a none θ ≤
      Real.exp ((X.p.a 2 + X.p.delta) * X.refLen c.2.1 c.2.2 * colLen5 (X.p.s n) r.1) *
        X.step3PostOn H r a (some c) θ := by
  let p := fun θ : Fin (colLen5 (X.p.s n) r.1) → Fin N =>
    (∏ h, (X.prior H.1 r.1).w (θ h)) * (if X.candGateOn H r a θ then 1 else 0) *
      X.obsLikOn H r a θ none
  let q := fun θ : Fin (colLen5 (X.p.s n) r.1) → Fin N =>
    (∏ h, (X.prior H.1 r.1).w (θ h)) * (if X.candGateOn H r a θ then 1 else 0) *
      X.obsLikOn H r a θ (some c)
  have hnn (excl : Option (Id × X.Ty × Finset (Fin X.blockBound))) (θ') :
      0 ≤ (∏ h, (X.prior H.1 r.1).w (θ' h)) * (if X.candGateOn H r a θ' then 1 else 0) *
        X.obsLikOn H r a θ' excl := by
    apply mul_nonneg
    · apply mul_nonneg (Finset.prod_nonneg fun h _ => (X.prior H.1 r.1).nonneg (θ' h))
      split_ifs <;> norm_num
    · exact Lane_sol_s05_hist1b.obsLikOn_nonneg X H r a θ' excl
  have hdom (θ') : p θ' ≤
      Real.exp (X.p.a 2 * X.refLen c.2.1 c.2.2 * colLen5 (X.p.s n) r.1) * q θ' := by
    by_cases hg : X.candGateOn H r a θ'
    · dsimp only [p, q]
      rw [ite_eq_left hg]
      simp only [mul_one]
      have hp := mul_le_mul_of_nonneg_left (hlik θ' hg)
        (Finset.prod_nonneg (s := Finset.univ) fun h _ => (X.prior H.1 r.1).nonneg (θ' h))
      simpa only [mul_left_comm] using hp
    · simp only [p, q, hg, ite_false, mul_zero, zero_mul]
      exact le_rfl
  have h := normalized_dominance p q
    (Real.exp (X.p.a 2 * X.refLen c.2.1 c.2.2 * colLen5 (X.p.s n) r.1))
    (Real.exp (-(X.p.delta * X.refLen c.2.1 c.2.2 * colLen5 (X.p.s n) r.1)))
    (hnn none) (hnn (some c)) (Real.exp_nonneg _) (Real.exp_pos _) hdom hM hden θ
  have hfactor : Real.exp (X.p.a 2 * X.refLen c.2.1 c.2.2 * colLen5 (X.p.s n) r.1) /
      Real.exp (-(X.p.delta * X.refLen c.2.1 c.2.2 * colLen5 (X.p.s n) r.1)) =
        Real.exp ((X.p.a 2 + X.p.delta) * X.refLen c.2.1 c.2.2 * colLen5 (X.p.s n) r.1) := by
    rw [← Real.exp_sub]
    congr 1
    ring
  rw [hfactor] at h
  exact h

theorem lowPost_delete {Id : Type} [DecidableEq Id] (H : X.KeyHist) (r : X.RecordOn Id)
    (a : X.ArraysOn Id) (hl : r.1.isLeft) (hM : 0 < X.step3MassOn H r a none)
    (hg : X.candGateOn H r a (H.2 r.1)) (hpass : ¬ X.step3FailOn H r a)
    (c : Id × X.Ty × Finset (Fin X.blockBound)) (hc : c ∈ X.refsOn H r a) (x : Fin N) :
    X.step3PostOn H r a none (fun _ => x) ≤
      Real.exp ((X.p.a 2 + X.p.delta) * X.refLen c.2.1 c.2.2) *
        X.step3PostOn H r a (some c) (fun _ => x) := by
  have h := step3Post_delete_of_likelihood X H r a c hM
    (step3Mass_delete_lower_of_pass X H r a hg hpass c hc)
    (fun θ hθ => obsLikOn_delete_le X H r a c θ hθ) (fun _ => x)
  simpa only [low_key_length X r.1 hl, Nat.cast_one, mul_one] using h

section Proxy

variable {Data : Type*} [Fintype Data] {Id : Type} [DecidableEq Id]
variable (T : SelectionExperiment5 (Fin N) Data) (H : X.KeyHist) (r : X.RecordOn Id)
variable (a : X.ArraysOn Id) (d : Data)
variable (hbase : ∀ x, T.baseRow d x = X.step3PostOn H r a none (fun _ => x))

include hbase

theorem lowProxy_le_post (x : Fin N) :
    T.proxyRow (Real.exp (-(X.p.delta * X.p.kPrime n r.1.level))) d x ≤
      Real.exp (X.p.delta * X.p.kPrime n r.1.level) *
        X.step3PostOn H r a none (fun _ => x) := by
  have hε : Real.exp (-(X.p.delta * X.p.kPrime n r.1.level)) ≤ 1 :=
    Real.exp_le_one_iff.mpr (neg_nonpos.mpr (mul_nonneg X.p.hdelta.1.le (Nat.cast_nonneg _)))
  have h := L5_1k_row_comparison T _ (Real.exp_pos _) hε d x
  rw [hbase x] at h
  simpa only [Real.exp_neg, inv_inv] using h

theorem lowProxy_support (x : Fin N)
    (hx : T.proxyRow (Real.exp (-(X.p.delta * X.p.kPrime n r.1.level))) d x ≠ 0) :
    X.step3PostOn H r a none (fun _ => x) ≠ 0 := by
  intro hp
  have h := lowProxy_le_post X T H r a d hbase x
  rw [hp, mul_zero] at h
  exact hx (le_antisymm h (Lane_sol_s05_centres.selection_proxy_nonneg T _ d x))

theorem lowProxy_delete (hl : r.1.isLeft) (hM : 0 < X.step3MassOn H r a none)
    (hg : X.candGateOn H r a (H.2 r.1)) (hpass : ¬ X.step3FailOn H r a)
    (c : Id × X.Ty × Finset (Fin X.blockBound)) (hc : c ∈ X.refsOn H r a)
    (hk : X.p.kPrime n r.1.level ≤ X.refLen c.2.1 c.2.2) (x : Fin N) :
    T.proxyRow (Real.exp (-(X.p.delta * X.p.kPrime n r.1.level))) d x ≤
      Real.exp (X.p.a 4 * X.refLen c.2.1 c.2.2) *
        X.step3PostOn H r a (some c) (fun _ => x) := by
  have hgap : X.p.a 2 + 2 * X.p.delta ≤ X.p.a 4 := by
    have hδ := X.p.hdelta_a (2 : Fin 9) (4 : Fin 9) (by decide)
    have ha := X.p.ha_order (2 : Fin 9) (4 : Fin 9) (by decide)
    linarith
  have hkR : (X.p.kPrime n r.1.level : ℝ) ≤ X.refLen c.2.1 c.2.2 := Nat.cast_le.mpr hk
  have harg : X.p.delta * X.p.kPrime n r.1.level +
      (X.p.a 2 + X.p.delta) * X.refLen c.2.1 c.2.2 ≤
        X.p.a 4 * X.refLen c.2.1 c.2.2 := by
    have h₁ := mul_le_mul_of_nonneg_left hkR X.p.hdelta.1.le
    have h₂ := mul_le_mul_of_nonneg_right hgap (Nat.cast_nonneg (X.refLen c.2.1 c.2.2) :
      (0 : ℝ) ≤ X.refLen c.2.1 c.2.2)
    linarith
  have hQ : 0 ≤ X.step3PostOn H r a (some c) (fun _ => x) := by
    unfold Setup5.step3PostOn
    apply div_nonneg
    · apply mul_nonneg
      · apply mul_nonneg (Finset.prod_nonneg fun h _ => (X.prior H.1 r.1).nonneg x)
        split_ifs <;> norm_num
      · exact Lane_sol_s05_hist1b.obsLikOn_nonneg X H r a _ (some c)
    · exact Lane_sol_s05_hist1b.step3MassOn_nonneg X H r a (some c)
  calc
    _ ≤ _ := lowProxy_le_post X T H r a d hbase x
    _ ≤ Real.exp (X.p.delta * X.p.kPrime n r.1.level) *
        (Real.exp ((X.p.a 2 + X.p.delta) * X.refLen c.2.1 c.2.2) *
          X.step3PostOn H r a (some c) (fun _ => x)) :=
      mul_le_mul_of_nonneg_left (lowPost_delete X H r a hl hM hg hpass c hc x) (Real.exp_nonneg _)
    _ = Real.exp (X.p.delta * X.p.kPrime n r.1.level +
        (X.p.a 2 + X.p.delta) * X.refLen c.2.1 c.2.2) *
          X.step3PostOn H r a (some c) (fun _ => x) := by rw [← mul_assoc, ← Real.exp_add]
    _ ≤ _ := mul_le_mul_of_nonneg_right (Real.exp_le_exp.mpr harg) hQ

theorem lowProxy_cap (hl : r.1.isLeft)
    (hlower : Real.exp (-(X.p.delta * X.p.kPrime n r.1.level)) ≤ X.step3MassOn H r a none)
    (B : ℝ) (hprior : ∀ x, (N : ℝ) * (X.prior H.1 r.1).w x ≤ Real.exp B) (x : Fin N) :
    (N : ℝ) * T.proxyRow (Real.exp (-(X.p.delta * X.p.kPrime n r.1.level))) d x ≤
      Real.exp (B + 2 * X.p.delta * X.p.kPrime n r.1.level + X.p.a 2 * observationLength X r) := by
  calc
    _ ≤ (N : ℝ) * (Real.exp (X.p.delta * X.p.kPrime n r.1.level) *
        X.step3PostOn H r a none (fun _ => x)) :=
      mul_le_mul_of_nonneg_left (lowProxy_le_post X T H r a d hbase x) (Nat.cast_nonneg _)
    _ = Real.exp (X.p.delta * X.p.kPrime n r.1.level) *
        ((N : ℝ) * X.step3PostOn H r a none (fun _ => x)) := by ring
    _ ≤ Real.exp (X.p.delta * X.p.kPrime n r.1.level) *
        Real.exp (B + X.p.delta * X.p.kPrime n r.1.level + X.p.a 2 * observationLength X r) :=
      mul_le_mul_of_nonneg_left (lowPost_cap X H r a hl hlower B hprior x) (Real.exp_nonneg _)
    _ = _ := by rw [← Real.exp_add]; congr 1; ring

end Proxy

end
end HypercubeRamsey.Lane_sol_s05_k1
