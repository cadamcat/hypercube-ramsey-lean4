import HypercubeRamsey.S05.History_sol_s05_1f_post
import HypercubeRamsey.S05.History_sol_s05_h5l_counts

namespace HypercubeRamsey.Lane_sol_s05_1f
open Classical OAI.HypercubeRamsey
open scoped BigOperators
noncomputable section
set_option maxHeartbeats 400000
set_option synthInstance.maxSize 1024

variable {γ K' χ : ℝ} {n N : ℕ} {E : Fin N → Fin N → Prop} {G : Colour}
variable (X : Setup5 γ K' χ n N E G)
open Lane_sol_s05_h5l

/-- Keep the constant coarse-neighborhood bound opaque to kernel evaluation. -/
def coarseBudget (R : ℕ) : ℕ := Classical.choose
  (show ∃ D : ℕ, 2 * (2 * R + 1) ^ coarseChunkCount5 ≤ D from ⟨_, le_rfl⟩)

theorem coarseBall_card_budget {n : ℕ} (R : ℕ) (q : CoarseKey5 n) :
    (coarseBall R q).card ≤ coarseBudget R :=
  (coarseBall_card R q).trans (Classical.choose_spec _)

/-- All high types near one center have a bounded coarse-data description. -/
def highTypeUniverse (q : CoarseKey5 n) : Finset X.Ty :=
  ((coarseBall 1 q).product (coarseBall 2 q).powerset).image
    fun d => (d.1, d.2.image (fun i => (.inr i : X.Key)), none)

@[irreducible] def highTypeBudget : ℕ := coarseBudget 1 * 2 ^ coarseBudget 2

theorem highTypeUniverse_card (q : CoarseKey5 n) :
    (highTypeUniverse X q).card ≤ highTypeBudget := by
  calc
    _ ≤ ((coarseBall 1 q).product (coarseBall 2 q).powerset).card := Finset.card_image_le
    _ = (coarseBall 1 q).card * 2 ^ (coarseBall 2 q).card := by simp
    _ ≤ coarseBudget 1 * 2 ^ coarseBudget 2 := Nat.mul_le_mul
      (coarseBall_card_budget 1 q)
      (Nat.pow_le_pow_right (by omega : 0 < 2) (coarseBall_card_budget 2 q))
    _ = _ := by unfold highTypeBudget; rfl

theorem neighbor_high_type_mem (x y : CubeVertex n) (hxy : (cube n).Adj x y)
    (hy : X.p.J n < X.g.severity y) :
    X.g.evenType (X.p.J n) y ∈ highTypeUniverse X (X.g.key x) := by
  have hnear := coarseRange_near X.g x (X.g.key y) (adjacent_key_mem X.g x y hxy)
  have hq : X.g.key y ∈ coarseBall 1 (X.g.key x) := by
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, hnear⟩
  have hC : X.g.coarseRange y ⊆ coarseBall 2 (X.g.key x) := by
    intro q hq
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,
      coarseNear_trans hnear (coarseRange_near X.g y q hq)⟩
  apply Finset.mem_image.mpr
  refine ⟨(X.g.key y, X.g.coarseRange y),
    Finset.mem_product.mpr ⟨hq, Finset.mem_powerset.mpr hC⟩, ?_⟩
  simp [ChunkGeometry5.evenType, ChunkGeometry5.typeKeys, not_le.mpr hy]

/-- Every high record observes at most a fixed constant times T high pools. -/
theorem high_observed_high_card (r : X.AbsRecord) (hr : X.RecOccurs r) :
    (r.2.1.filter fun c => c.2.2.2 = none).card ≤ X.p.T n * highTypeBudget := by
  obtain ⟨y, μ, hrec⟩ := hr
  have hsub : r.2.1.filter (fun c => c.2.2.2 = none) ⊆
      (Finset.univ : Finset (Fin (X.p.T n))).product (highTypeUniverse X (X.g.key y.1)) := by
    intro c hc
    obtain ⟨hc, hnone⟩ := Finset.mem_filter.mp hc
    rw [hrec.2.1] at hc
    obtain ⟨a, ha, rfl⟩ := Finset.mem_image.mp hc
    have hy : X.p.J n < X.g.severity a.1 := by
      by_contra h
      have hle : X.g.severity a.1 ≤ X.p.J n := le_of_not_gt h
      simp [ChunkGeometry5.evenType, hle] at hnone
    exact Finset.mem_product.mpr ⟨Finset.mem_univ _,
      neighbor_high_type_mem X y.1 a.1 ((cube n).adj_symm (Finset.mem_filter.mp ha).2) hy⟩
  calc
    _ ≤ ((Finset.univ : Finset (Fin (X.p.T n))).product
        (highTypeUniverse X (X.g.key y.1))).card := Finset.card_le_card hsub
    _ = X.p.T n * (highTypeUniverse X (X.g.key y.1)).card := by simp
    _ ≤ _ := Nat.mul_le_mul_left _ (highTypeUniverse_card X _)

/-- In a high record every low observation has interface level J. -/
theorem high_observed_low_level (r : X.AbsRecord) (hr : X.RecOccurs r) (hh : r.1.isRight)
    (c : Fin (X.p.T n) × X.Ty) (hc : c ∈ r.2.1)
    (j : Fin (X.p.J n + 1)) (hj : c.2.2.2 = some j) : j.val = X.p.J n := by
  obtain ⟨y, μ, hrec⟩ := hr
  have hy : X.p.J n < X.g.severity y.1 := by
    by_contra h
    rw [← hrec.1] at hh
    simp [ChunkGeometry5.roleKey, le_of_not_gt h] at hh
  rw [hrec.2.1] at hc
  obtain ⟨a, ha, rfl⟩ := Finset.mem_image.mp hc
  have halow : X.g.severity a.1 ≤ X.p.J n := by
    by_contra h
    simp [ChunkGeometry5.evenType, h] at hj
  have hfringe := high_low_neighbor X.g (X.p.J n) y.1 a.1
    ((cube n).adj_symm (Finset.mem_filter.mp ha).2) hy halow
  have he : (⟨X.g.severity a.1, Nat.lt_succ_of_le halow⟩ : Fin (X.p.J n + 1)) = j := by
    simpa [ChunkGeometry5.evenType, halow] using hj
  exact (congrArg Fin.val he).symm.trans hfringe.2.1

/-- Total observed lengths for the joint posterior atom cap. -/
def observedLength (r : X.AbsRecord) : ℕ :=
  ∑ c ∈ r.2.1.filter (fun c => r.1 ∈ c.2.2.1),
    X.p.typeBlocks n c.2 * (X.p.q0 * X.p.typeSegs n c.2)

theorem high_observed_length (r : X.AbsRecord) (hr : X.RecOccurs r) (hh : r.1.isRight) :
    observedLength X r ≤
      (X.p.T n * highTypeBudget) * (X.p.poolBlocks n * (X.p.q0 * X.p.uStarSeg n)) +
        X.p.lowBlocks n (X.p.J n) * (X.p.q0 * X.p.uSeg n (X.p.J n)) := by
  let f := fun c : Fin (X.p.T n) × X.Ty =>
    X.p.typeBlocks n c.2 * (X.p.q0 * X.p.typeSegs n c.2)
  let SH := r.2.1.filter fun c => c.2.2.2 = none
  let SL := r.2.1.filter fun c => c.2.2.2.isSome
  have hsplit : SH ∪ SL = r.2.1 := by
    ext c
    cases h : c.2.2.2 <;> simp [SH, SL, h]
  have hd : Disjoint SH SL := by
    apply Finset.disjoint_left.mpr
    intro c hc hd
    have hn := (Finset.mem_filter.mp hc).2
    have hs := (Finset.mem_filter.mp hd).2
    simp [hn] at hs
  have hH : ∑ c ∈ SH, f c = SH.card * (X.p.poolBlocks n * (X.p.q0 * X.p.uStarSeg n)) := by
    calc
      _ = ∑ _c ∈ SH, X.p.poolBlocks n * (X.p.q0 * X.p.uStarSeg n) := by
        apply Finset.sum_congr rfl
        intro c hc
        simp [f, Params5.typeBlocks, Params5.typeSegs, (Finset.mem_filter.mp hc).2]
      _ = _ := by simp
  have hL : ∑ c ∈ SL, f c = SL.card *
      (X.p.lowBlocks n (X.p.J n) * (X.p.q0 * X.p.uSeg n (X.p.J n))) := by
    calc
      _ = ∑ _c ∈ SL, X.p.lowBlocks n (X.p.J n) *
          (X.p.q0 * X.p.uSeg n (X.p.J n)) := by
        apply Finset.sum_congr rfl
        intro c hc
        have hs := (Finset.mem_filter.mp hc).2
        cases hj : c.2.2.2 with
        | none => simp [hj] at hs
        | some j =>
          have hval := high_observed_low_level X r hr hh c (Finset.mem_filter.mp hc).1 j hj
          have he : j = ⟨X.p.J n, Nat.lt_succ_self _⟩ := Fin.ext hval
          simp [f, Params5.typeBlocks, Params5.typeSegs, hj, he]
      _ = _ := by simp
  calc
    _ ≤ ∑ c ∈ r.2.1, f c := Finset.sum_le_sum_of_subset (Finset.filter_subset _ _)
    _ = ∑ c ∈ SH, f c + ∑ c ∈ SL, f c := by rw [← hsplit, Finset.sum_union hd]
    _ = _ := by rw [hH, hL]
    _ ≤ _ := by
      apply Nat.add_le_add
      · exact Nat.mul_le_mul_right _ (high_observed_high_card X r hr)
      · have hcard := high_observed_low_card X r hr hh
        have hmul := Nat.mul_le_mul_right
          (X.p.lowBlocks n (X.p.J n) * (X.p.q0 * X.p.uSeg n (X.p.J n))) hcard
        simpa [SL] using hmul


/-- Only a fixed coarse shape and the central sign enter a generic high designation. -/
def genericHighSignatures (q : CoarseKey5 n) (t : CubeVertex (X.p.m n)) :
    Finset (X.Ty × Option X.Key) :=
  ((highTypeUniverse X q).product (Finset.univ : Finset Bool)).image fun d =>
    (d.1, if d.2 then some (.inl (d.1.1, t, ⟨X.p.J n, Nat.lt_succ_self _⟩)) else none)

theorem genericHighSignatures_card (q : CoarseKey5 n) (t : CubeVertex (X.p.m n)) :
    (genericHighSignatures X q t).card ≤ 2 * highTypeBudget := by
  calc
    _ ≤ ((highTypeUniverse X q).product (Finset.univ : Finset Bool)).card := Finset.card_image_le
    _ = 2 * (highTypeUniverse X q).card := by simp [Nat.mul_comm]
    _ ≤ _ := Nat.mul_le_mul_left 2 (highTypeUniverse_card X q)

/-- The exceptional image pays once for each state, even when many roles share it. -/
theorem image_card_generic_exceptional {A B C Id : Type*}
    [Fintype A] [Fintype B] [Fintype C] [Nonempty C] [Fintype Id]
    [DecidableEq A] [DecidableEq B] [DecidableEq C] [DecidableEq Id]
    (S : Finset A) (state : A → B) (sig : A → C) (μ : B → Id)
    (generic : Finset C) (exceptional : Finset B)
    (hg : ∀ a ∈ S, state a ∉ exceptional → sig a ∈ generic)
    (hsig : ∀ a b, state a = state b → sig a = sig b) :
    (S.image fun a => (μ (state a), sig a)).card ≤
      Fintype.card Id * generic.card + exceptional.card := by
  let SG := S.filter fun a => state a ∉ exceptional
  let SE := S.filter fun a => state a ∈ exceptional
  have hsplit : SG ∪ SE = S := by
    ext a
    by_cases h : state a ∈ exceptional <;> simp [SG, SE, h]
  have hG : (SG.image fun a => (μ (state a), sig a)).card ≤
      Fintype.card Id * generic.card := by
    apply (Finset.card_le_card (t := (Finset.univ : Finset Id).product generic) ?_).trans_eq
      (by simp)
    intro c hc
    obtain ⟨a, ha, rfl⟩ := Finset.mem_image.mp hc
    exact Finset.mem_product.mpr ⟨Finset.mem_univ _, hg a (Finset.mem_filter.mp ha).1
      (Finset.mem_filter.mp ha).2⟩
  let rep (b : B) : C := if h : ∃ a, state a = b then sig (Classical.choose h)
    else Classical.choice (show Nonempty C from inferInstance)
  have hE : (SE.image fun a => (μ (state a), sig a)).card ≤ exceptional.card := by
    apply (Finset.card_le_card (t := exceptional.image fun b => (μ b, rep b)) ?_).trans
      Finset.card_image_le
    intro c hc
    obtain ⟨a, ha, rfl⟩ := Finset.mem_image.mp hc
    refine Finset.mem_image.mpr ⟨state a, (Finset.mem_filter.mp ha).2, ?_⟩
    have hex : ∃ b, state b = state a := ⟨a, rfl⟩
    have hr : rep (state a) = sig a := by
      simp only [rep, dif_pos hex]
      exact hsig _ a (Classical.choose_spec hex)
    rw [hr]
  rw [← hsplit, Finset.image_union]
  exact (Finset.card_union_le _ _).trans (Nat.add_le_add hG hE)

private theorem noncritical_neighbor_sign (x y : CubeVertex n) (hxy : (cube n).Adj x y)
    (he : X.St.stateOf y ∉ ((Lane_sol_s05_hist1b.criticalChunks X.g x).biUnion X.g.fineChunks).image
      (fun a => X.St.stateOf (flipVertex5 x a))) : X.g.sign y = X.g.sign x := by
  obtain ⟨a, rfl⟩ := adjacent_flip x y hxy
  by_cases hex : ∃ i, a ∈ X.g.fineChunks i
  · obtain ⟨i, hi⟩ := hex
    have hcrit : i ∉ Lane_sol_s05_hist1b.criticalChunks X.g x := by
      intro h
      apply he
      exact Finset.mem_image.mpr ⟨a, Finset.mem_biUnion.mpr ⟨i, h, hi⟩, rfl⟩
    exact (Lane_sol_s05_hist1b.fine_flip_noncritical X.g x i a hi hcrit).1
  · push_neg at hex
    funext i
    simp only [ChunkGeometry5.sign, fineCount_flip_outside X.g x a i (hex i)]

/-- Computed high deletion references have O(T+J) designations, not T times J. -/
theorem high_designations_card (r : X.AbsRecord) (hr : X.RecOccurs r) (hh : r.1.isRight) :
    r.2.2.1.card ≤ X.p.T n * (2 * highTypeBudget) + 2 * (X.p.J n + 2) := by
  letI : DecidableEq (Fin (X.p.T n)) := Classical.decEq _
  obtain ⟨y, μ, hrec⟩ := hr
  let S := (Setup5.evenNbrs y).filter fun a =>
    r.1 ∈ (X.g.evenType (X.p.J n) a.1).2.1 ∧
      r.1.isLeft = (X.g.evenType (X.p.J n) a.1).2.2.isSome
  let sig := fun a : EvenRole5 n =>
    (X.g.evenType (X.p.J n) a.1, X.g.optionalKey (X.p.J n) a.1)
  let crit := ((Lane_sol_s05_hist1b.criticalChunks X.g y.1).biUnion X.g.fineChunks).image
    (fun a => X.St.stateOf (flipVertex5 y.1 a))
  let exc := if X.g.severity y.1 ≤ X.p.J n + 2 then crit else ∅
  have hsig (a b : EvenRole5 n) (he : X.St.stateOf a.1 = X.St.stateOf b.1) : sig a = sig b := by
    have hh := X.St.state_determines a.1 b.1 he
    exact Prod.ext hh.2.2.2.2.1 hh.2.2.2.2.2.1
  have hg (a : EvenRole5 n) (ha : a ∈ S) (he : X.St.stateOf a.1 ∉ exc) :
      sig a ∈ genericHighSignatures X (X.g.key y.1) (X.g.sign y.1) := by
    have haN := (Finset.mem_filter.mp ha).1
    have hmode := (Finset.mem_filter.mp ha).2.2
    have hhigh : X.p.J n < X.g.severity a.1 := by
      have hleft : r.1.isLeft = false := by cases h : r.1 <;> simp_all
      by_contra h
      simp [ChunkGeometry5.evenType, le_of_not_gt h, hleft] at hmode
    have hadj := (cube n).adj_symm (Finset.mem_filter.mp haN).2
    have hty := neighbor_high_type_mem X y.1 a.1 hadj hhigh
    by_cases hopt : X.g.severity a.1 = X.p.J n + 1
    · have hyle : X.g.severity y.1 ≤ X.p.J n + 2 := by
        have hh := adjacent_severity X.g y.1 a.1 hadj; omega
      have hcrit : X.St.stateOf a.1 ∉ crit := by simpa [exc, hyle] using he
      have hsign := noncritical_neighbor_sign X y.1 a.1 hadj hcrit
      refine Finset.mem_image.mpr ⟨(X.g.evenType (X.p.J n) a.1, true),
        Finset.mem_product.mpr ⟨hty, Finset.mem_univ _⟩, ?_⟩
      simp [sig, ChunkGeometry5.optionalKey, hopt, ChunkGeometry5.evenType, hsign]
    · refine Finset.mem_image.mpr ⟨(X.g.evenType (X.p.J n) a.1, false),
        Finset.mem_product.mpr ⟨hty, Finset.mem_univ _⟩, ?_⟩
      simp [sig, ChunkGeometry5.optionalKey, hopt]
  have hexc : exc.card ≤ 2 * (X.p.J n + 2) := by
    dsimp [exc]
    split_ifs with h
    · exact (Lane_sol_s05_hist1b.critical_flip_states_card_le X.g X.St y.1).trans
        (Nat.mul_le_mul_left 2 h)
    · simp
  rw [hrec.2.2.1]
  have hcount := image_card_generic_exceptional S (fun a => X.St.stateOf a.1) sig μ
    (genericHighSignatures X (X.g.key y.1) (X.g.sign y.1)) exc hg hsig
  have hG := Nat.mul_le_mul_left (X.p.T n)
    (genericHighSignatures_card X (X.g.key y.1) (X.g.sign y.1))
  exact hcount.trans (by simpa using Nat.add_le_add hG hexc)


/-- The complete observed likelihood pays only the sum of block lengths. -/
theorem observed_likelihood_bound (H : X.KeyHist) (r : X.AbsRecord)
    (a : X.ArraysOn (Fin (X.p.T n))) (θ : Fin (colLen5 (X.p.s n) r.1) → Fin N)
    (hg : X.candGateOn H r a θ) :
    X.obsLikOn H r a θ none ≤
      Real.exp (X.p.a 2 * observedLength X r * colLen5 (X.p.s n) r.1) := by
  let S := r.2.1.filter fun c => r.1 ∈ c.2.2.1
  let f := fun (c : Fin (X.p.T n) × X.Ty) (i : Fin (X.p.typeBlocks n c.2)) =>
    ratio5 ((X.blockLaw (X.withCol H r.1 θ) c.2).w (a c i))
      ((X.blockLawDel H c.2 r.1).w (a c i))
  have hc (c) (hmem : c ∈ S) :
      (∏ i, f c i) ≤ Real.exp (X.p.a 2 *
        (X.p.typeBlocks n c.2 * (X.p.q0 * X.p.typeSegs n c.2) : ℕ) *
          colLen5 (X.p.s n) r.1) := by
    have ht := (Finset.mem_filter.mp hmem).2
    have hgate := hg.1 c (Finset.mem_filter.mp hmem).1 ht
    calc
      _ ≤ ∏ _i : Fin (X.p.typeBlocks n c.2),
          Real.exp (X.p.a 2 * (X.p.q0 * X.p.typeSegs n c.2) * colLen5 (X.p.s n) r.1) :=
        Finset.prod_le_prod₀
          (fun i _ => Lane_q_s05_hist1b.ratio5_nonneg
            ((X.blockLaw (X.withCol H r.1 θ) c.2).nonneg _) ((X.blockLawDel H c.2 r.1).nonneg _))
          (fun i _ => candidate_block_likelihood X H c.2 r.1 θ ht hgate.1 hgate.2 (a c i))
      _ = _ := by
        simp only [Finset.prod_const, Finset.card_univ, Fintype.card_fin]
        rw [← Real.exp_nat_mul]
        congr 1
        simp only [Nat.cast_mul]
        ring
  have hh : X.obsLikOn H r a θ none = ∏ c ∈ S, ∏ i, f c i := by
    simp [Setup5.obsLikOn, Setup5.InRef, S, f]
  rw [hh]
  calc
    _ ≤ ∏ c ∈ S, Real.exp (X.p.a 2 *
        (X.p.typeBlocks n c.2 * (X.p.q0 * X.p.typeSegs n c.2) : ℕ) *
          colLen5 (X.p.s n) r.1) :=
      Finset.prod_le_prod₀ (fun c _ => Finset.prod_nonneg fun i _ =>
        Lane_q_s05_hist1b.ratio5_nonneg
          ((X.blockLaw (X.withCol H r.1 θ) c.2).nonneg _) ((X.blockLawDel H c.2 r.1).nonneg _)) hc
    _ = _ := by
      rw [← Real.exp_sum]
      congr 1
      simp only [observedLength, Nat.cast_sum, S]
      rw [Finset.mul_sum, Finset.sum_mul]

/-- The concrete joint atom budget, before its eventual O(J log m) conversion. -/
theorem posterior_atom_bound (H : X.KeyHist) (r : X.AbsRecord)
    (a : X.ArraysOn (Fin (X.p.T n))) (B : ℝ)
    (hprior : ∀ y, (N : ℝ) * (X.prior H.1 r.1).w y ≤ Real.exp B)
    (hmass : Real.exp (-(X.p.delta * colLen5 (X.p.s n) r.1)) ≤
      X.step3MassOn H r a none)
    (θ : Fin (colLen5 (X.p.s n) r.1) → Fin N) :
    (N : ℝ) ^ colLen5 (X.p.s n) r.1 * X.step3PostOn H r a none θ ≤
      Real.exp ((B + X.p.a 2 * observedLength X r + X.p.delta) *
        colLen5 (X.p.s n) r.1) := by
  let s := colLen5 (X.p.s n) r.1
  have hp : (N : ℝ) ^ s * (∏ h, (X.prior H.1 r.1).w (θ h)) ≤ Real.exp (B * s) := by
    calc
      _ = ∏ h : Fin s, (N : ℝ) * (X.prior H.1 r.1).w (θ h) := by
        rw [Finset.prod_mul_distrib]
        simp only [Finset.prod_const, Finset.card_univ, Fintype.card_fin]
        rfl
      _ ≤ ∏ _h : Fin s, Real.exp B := Finset.prod_le_prod₀
        (fun h _ => mul_nonneg (Nat.cast_nonneg _) ((X.prior H.1 r.1).nonneg _))
        (fun h _ => hprior (θ h))
      _ = _ := by simp [← Real.exp_nat_mul, mul_comm]
  have hm : 0 < X.step3MassOn H r a none := (Real.exp_pos _).trans_le hmass
  by_cases hg : X.candGateOn H r a θ
  · have hl := observed_likelihood_bound X H r a θ hg
    unfold Setup5.step3PostOn
    simp only [if_pos hg, mul_one]
    rw [← mul_div_assoc]
    calc
      _ ≤ (Real.exp (B * s) * Real.exp (X.p.a 2 * observedLength X r * s)) /
          X.step3MassOn H r a none := by
        apply div_le_div_of_nonneg_right _ hm.le
        rw [← mul_assoc]
        exact mul_le_mul hp hl (Lane_sol_s05_hist1b.obsLikOn_nonneg X H r a θ none)
          (Real.exp_pos _).le
      _ ≤ (Real.exp (B * s) * Real.exp (X.p.a 2 * observedLength X r * s)) /
          Real.exp (-(X.p.delta * s)) := div_le_div_of_nonneg_left
            (mul_nonneg (Real.exp_pos _).le (Real.exp_pos _).le) (Real.exp_pos _) hmass
      _ = _ := by rw [← Real.exp_add, ← Real.exp_sub]; congr 1; dsimp [s]; ring
  · simp only [Setup5.step3PostOn, if_neg hg, mul_zero, zero_mul, zero_div]
    exact (Real.exp_pos _).le

end
end HypercubeRamsey.Lane_sol_s05_1f
