import HypercubeRamsey.S05.History_sol_s05_hist1f_low
import HypercubeRamsey.S05.History_sol_s05_hist1f_paths
import HypercubeRamsey.S05.History_sol_s05_hist1e_apply
import HypercubeRamsey.S05.History_sol_s05_h5l_geom
import HypercubeRamsey.Tools.Concentration

namespace HypercubeRamsey.Lane_sol_s05_1f

open Classical OAI.HypercubeRamsey
open scoped BigOperators
noncomputable section
set_option maxHeartbeats 400000
set_option synthInstance.maxSize 1024

variable {γ K' χ : ℝ} {n N : ℕ} {E : Fin N → Fin N → Prop} {G : Colour}
variable (X : Setup5 γ K' χ n N E G)

/-- The rank definition of the first blocks has the expected cardinality. -/
theorem firstK_card (S : Finset (Fin X.blockBound)) (k : ℕ) :
    (X.firstK S k).card = min k S.card := by
  let e := S.orderEmbOfFin rfl
  have hrank (i : Fin S.card) : (S.filter fun j => j < e i).card = i.val := by
    have he : S.filter (fun j => j < e i) =
        (Finset.univ.filter fun j : Fin S.card => j < i).image e := by
      calc
        _ = (Finset.univ.image e).filter (fun j => j < e i) :=
          congrArg (fun A : Finset (Fin X.blockBound) => A.filter (fun j => j < e i))
            (Finset.image_orderEmbOfFin_univ S rfl).symm
        _ = _ := by
          rw [Finset.filter_image]
          congr 1
          ext j
          simp only [Finset.mem_filter, Finset.mem_univ, true_and]
          exact e.lt_iff_lt
    rw [he, Finset.card_image_of_injective _ e.injective]
    simp [Finset.filter_gt_eq_Iio, Fin.card_Iio]
  have he : X.firstK S k =
      (Finset.univ.filter fun i : Fin S.card => i.val < k).image e := by
    unfold Setup5.firstK
    calc
      _ = (Finset.univ.image e).filter
          (fun i => (S.filter fun i' => i' < i).card < k) :=
        congrArg (fun A : Finset (Fin X.blockBound) => A.filter
          (fun i => (S.filter fun i' => i' < i).card < k))
          (Finset.image_orderEmbOfFin_univ S rfl).symm
      _ = _ := by
        rw [Finset.filter_image]
        apply congrArg (Finset.image e)
        ext i
        simp only [Finset.mem_filter, Finset.mem_univ, true_and, hrank]
  rw [he, Finset.card_image_of_injective _ e.injective]
  rw [Fin.card_filter_val_lt, Nat.min_comm]

theorem poolIdx_card : X.poolIdx.card = X.p.poolBlocks n := by
  have hle : X.p.poolBlocks n ≤ X.blockBound := le_max_left _ _
  unfold Setup5.poolIdx
  rw [Fin.card_filter_val_lt, Nat.min_eq_right hle]

theorem usedBlocks_le_poolBlocks : X.p.usedBlocks n ≤ X.p.poolBlocks n := by
  have he : 1 ≤ Real.exp (X.p.Kh * ((X.p.q0 : ℝ) * X.p.uStarSeg n)) :=
    Real.one_le_exp_iff.mpr (mul_nonneg X.p.hKh.le (by positivity))
  have hh := Nat.le_ceil
    (Real.exp (X.p.Kh * ((X.p.q0 : ℝ) * X.p.uStarSeg n)) * X.p.usedBlocks n)
  have hu : (X.p.usedBlocks n : ℝ) ≤ X.p.poolBlocks n := by
    exact (le_mul_of_one_le_left (Nat.cast_nonneg _) he).trans hh
  exact_mod_cast hu

theorem high_record_ref_mode (r : X.AbsRecord) (hr : X.RecOccurs r) (hh : r.1.isRight)
    (c : Fin (X.p.T n) × X.Ty × Option X.Key) (hc : c ∈ r.2.2.1) :
    c.2.1.2.2 = none := by
  letI : DecidableEq (Fin (X.p.T n)) := Classical.decEq _
  obtain ⟨y, μ, _, _, href, _⟩ := hr
  rw [href] at hc
  obtain ⟨a, ha, he⟩ := Finset.mem_image.mp hc
  have hmode := (Finset.mem_filter.mp ha).2.2
  have hl : r.1.isLeft = false := by
    cases h : r.1 <;> simp_all
  have hcMode : c.2.1.2.2.isSome = false := by
    have hproj := congrArg (fun d => d.2.1.2.2.isSome) he
    exact hproj.symm.trans (hmode.symm.trans hl)
  cases h : c.2.1.2.2 <;> simp_all

theorem high_refSubset_mem (H : X.KeyHist) (a : X.ArraysOn (Fin (X.p.T n)))
    (c : Fin (X.p.T n) × X.Ty × Option X.Key) (hm : c.2.1.2.2 = none) :
    X.refSubsetOn H a (c.1, c.2.1) c.2.2 ⊆ X.poolIdx ∧
      (X.refSubsetOn H a (c.1, c.2.1) c.2.2).card = X.p.usedBlocks n := by
  let hits := match c.2.2 with
    | some (.inl k) => X.hitSet a (c.1, c.2.1) (X.lowCol H.2 k)
    | _ => X.poolIdx
  have hsub : hits ⊆ X.poolIdx := by
    dsimp [hits]
    split <;> try exact Finset.Subset.refl _
    exact Finset.filter_subset _ _
  let S := if X.p.usedBlocks n ≤ hits.card then hits else X.poolIdx
  have hSsub : S ⊆ X.poolIdx := by
    dsimp [S]
    split_ifs
    · exact hsub
    · exact Finset.Subset.refl _
  have hSlen : X.p.usedBlocks n ≤ S.card := by
    dsimp [S]
    split_ifs with h
    · exact h
    · rw [poolIdx_card]
      exact usedBlocks_le_poolBlocks X
  simp only [Setup5.refSubsetOn, hm]
  change X.firstK S (X.p.usedBlocks n) ⊆ X.poolIdx ∧
    (X.firstK S (X.p.usedBlocks n)).card = X.p.usedBlocks n
  constructor
  · exact (Finset.filter_subset _ _).trans hSsub
  · rw [firstK_card, Nat.min_eq_left hSlen]

/-- All possible subsets of one designated high pool. This is a union of
single-reference choices, rather than a product of simultaneous choices. -/
def highRefs (r : X.AbsRecord) :
    Finset (Fin (X.p.T n) × X.Ty × Finset (Fin X.blockBound)) :=
  r.2.2.1.biUnion fun c =>
    ((X.poolIdx.powerset).filter fun M => M.card = X.p.usedBlocks n).image
      fun M => (c.1, c.2.1, M)

theorem refsOn_high_subset (H : X.KeyHist) (r : X.AbsRecord) (hr : X.RecOccurs r)
    (hh : r.1.isRight) (a : X.ArraysOn (Fin (X.p.T n))) :
    X.refsOn H r a ⊆ highRefs X r := by
  intro d hd
  obtain ⟨c, hc, rfl⟩ := Finset.mem_image.mp hd
  obtain ⟨hsub, hcard⟩ := high_refSubset_mem X H a c (high_record_ref_mode X r hr hh c hc)
  apply Finset.mem_biUnion.mpr
  refine ⟨c, hc, Finset.mem_image.mpr ⟨_, ?_, rfl⟩⟩
  exact Finset.mem_filter.mpr ⟨Finset.mem_powerset.mpr hsub, hcard⟩

theorem highRefs_length (r : X.AbsRecord) (hr : X.RecOccurs r) (hh : r.1.isRight)
    (c) (hc : c ∈ highRefs X r) :
    X.refLen c.2.1 c.2.2 = X.p.usedBlocks n * (X.p.q0 * X.p.uStarSeg n) := by
  obtain ⟨d, hd, hc⟩ := Finset.mem_biUnion.mp hc
  obtain ⟨M, hM, rfl⟩ := Finset.mem_image.mp hc
  have hcard := (Finset.mem_filter.mp hM).2
  simp only [Setup5.refLen, hcard, Params5.typeSegs,
    high_record_ref_mode X r hr hh d hd]

theorem highRefs_card (r : X.AbsRecord) :
    (highRefs X r).card ≤ r.2.2.1.card * 2 ^ X.p.poolBlocks n := by
  apply (Finset.card_biUnion_le).trans
  calc
    _ ≤ ∑ _c ∈ r.2.2.1, 2 ^ X.p.poolBlocks n := by
      apply Finset.sum_le_sum
      intro c hc
      exact (Finset.card_image_le).trans ((Finset.card_filter_le _ _).trans_eq
        (by rw [Finset.card_powerset, poolIdx_card]))
    _ = _ := by simp

/-- A severity-decreasing bit flip crosses the merged 11/13 fringe. -/
theorem severity_drop_fringe {m : ℕ} (g : ChunkGeometry5 n m)
    (x : CubeVertex n) (a : Fin n) (hdrop : g.severity (flipVertex5 x a) < g.severity x) :
    ∃ i, a ∈ g.fineChunks i ∧
      Nat.dist (2 * g.fineCount x i) g.fineLength = 11 ∧
      Nat.dist (2 * g.fineCount (flipVertex5 x a) i) g.fineLength = 13 := by
  obtain ⟨i, hi⟩ : ∃ i, a ∈ g.fineChunks i := by
    by_contra hh
    push_neg at hh
    have hcounts := fun i => Lane_sol_s05_h5l.fineCount_flip_outside g x a i (hh i)
    have hsame : g.severity (flipVertex5 x a) = g.severity x := by
      unfold ChunkGeometry5.severity
      simp_rw [hcounts]
    exact (ne_of_lt hdrop) hsame
  let S := Finset.univ.filter fun j => Nat.dist (2 * g.fineCount x j) g.fineLength ≤ 11
  let T := Finset.univ.filter fun j => Nat.dist (2 * g.fineCount (flipVertex5 x a) j) g.fineLength ≤ 11
  have hcounts := Lane_sol_s05_h5l.fine_counts_single_change g x a i hi
  have herase : S.erase i = T.erase i := by
    ext j
    by_cases hj : j = i
    · subst j
      simp
    · simp [S, T, hj, hcounts j hj]
  have hc := congrArg Finset.card herase
  have hxmem : i ∈ S := by
    by_contra hh
    rw [Finset.erase_eq_of_notMem hh] at hc
    have hle := hc.trans_le (Finset.card_le_card (Finset.erase_subset i T))
    exact (not_le_of_gt hdrop) hle
  have hymem : i ∉ T := by
    intro hh
    rw [Finset.card_erase_of_mem hxmem, Finset.card_erase_of_mem hh] at hc
    have hxpos := Finset.card_pos.mpr ⟨i, hxmem⟩
    have hypos := Finset.card_pos.mpr ⟨i, hh⟩
    change T.card < S.card at hdrop
    omega
  have hdx : Nat.dist (2 * g.fineCount x i) g.fineLength ≤ 11 := (Finset.mem_filter.mp hxmem).2
  have hdy : 11 < Nat.dist (2 * g.fineCount (flipVertex5 x a) i) g.fineLength := by
    have hh : ¬ Nat.dist (2 * g.fineCount (flipVertex5 x a) i) g.fineLength ≤ 11 := by
      intro h
      exact hymem (by simp [T, h])
    omega
  have hstep := Lane_sol_s05_h5l.fineCount_flip_inside g x a i hi
  obtain ⟨k, hk⟩ := g.fine_length_odd
  refine ⟨i, hi, ?_, ?_⟩ <;> simp only [Nat.dist] at * <;> omega

/-- All low neighbours at a high interface are one state, including their
array IDs. Thus a high observation contains at most one low tuple. -/
theorem high_low_state_unique {m J : ℕ} (g : ChunkGeometry5 n m) (St : CubeStates5 g J)
    (x y z : CubeVertex n) (hxy : (cube n).Adj x y) (hxz : (cube n).Adj x z)
    (hx : J < g.severity x) (hy : g.severity y ≤ J) (hz : g.severity z ≤ J) :
    St.stateOf y = St.stateOf z := by
  have hfy := Lane_sol_s05_h5l.high_low_neighbor g J x y hxy hx hy
  have hfz := Lane_sol_s05_h5l.high_low_neighbor g J x z hxz hx hz
  obtain ⟨a, rfl⟩ := Lane_sol_s05_h5l.adjacent_flip x y hxy
  obtain ⟨b, rfl⟩ := Lane_sol_s05_h5l.adjacent_flip x z hxz
  obtain ⟨i, hi, hi0, hi1⟩ := severity_drop_fringe g x a (lt_of_le_of_lt hy hx)
  obtain ⟨j, hj, hj0, hj1⟩ := severity_drop_fringe g x b (lt_of_le_of_lt hz hx)
  exact Lane_sol_s05_hist1b.fine_outward_states_eq g St x i j a b
    hi hj hi0 hi1 hj0 hj1 (hfy.2.1.trans hfz.2.1.symm)

theorem high_observed_low_card (r : X.AbsRecord) (hr : X.RecOccurs r) (hh : r.1.isRight) :
    (r.2.1.filter fun c => c.2.2.2.isSome).card ≤ 1 := by
  obtain ⟨y, μ, hrecord⟩ := hr
  have hhigh : X.p.J n < X.g.severity y.1 := by
    by_contra h
    have hlow : X.g.severity y.1 ≤ X.p.J n := le_of_not_gt h
    rw [← hrecord.1] at hh
    simp [ChunkGeometry5.roleKey, hlow] at hh
  apply Finset.card_le_one.mpr
  intro c hc d hd
  obtain ⟨hc, hcm⟩ := Finset.mem_filter.mp hc
  obtain ⟨hd, hdm⟩ := Finset.mem_filter.mp hd
  rw [hrecord.2.1] at hc hd
  obtain ⟨a, ha, rfl⟩ := Finset.mem_image.mp hc
  obtain ⟨b, hb, rfl⟩ := Finset.mem_image.mp hd
  have halow : X.g.severity a.1 ≤ X.p.J n := by
    by_contra h
    have hn : ¬ X.g.severity a.1 ≤ X.p.J n := h
    simp [ChunkGeometry5.evenType, hn] at hcm
  have hblow : X.g.severity b.1 ≤ X.p.J n := by
    by_contra h
    simp [ChunkGeometry5.evenType, h] at hdm
  have hya := (Finset.mem_filter.mp ha).2
  have hyb := (Finset.mem_filter.mp hb).2
  have he := high_low_state_unique X.g X.St y.1 a.1 b.1
    ((cube n).adj_symm hya) ((cube n).adj_symm hyb) hhigh halow hblow
  exact Prod.ext (congrArg μ he) (X.St.state_determines a.1 b.1 he).2.2.2.2.1

/-- The denominator tests alone, before the conditional-path tests. -/
def denominatorFail (H : X.KeyHist) (r : X.AbsRecord)
    (a : X.ArraysOn (Fin (X.p.T n))) : Prop :=
  X.candGateOn H r a (H.2 r.1) ∧
    (X.step3MassOn H r a none < Real.exp (-(X.p.delta * X.p.s n)) ∨
      ∃ c ∈ X.refsOn H r a,
        X.step3MassOn H r a none <
          Real.exp (-(X.p.delta * X.refLen c.2.1 c.2.2 * colLen5 (X.p.s n) r.1)) *
            X.step3MassOn H r a (some c))

/-- Raw high-target denominator exceptions: union individual subsets of each
pool, with no simultaneous subset-choice factor (TeX 440–448). -/
theorem high_denominator_finite_bound (H : X.KeyHist) (r : X.AbsRecord)
    (hr : X.RecOccurs r) (hh : r.1.isRight) :
    (∑ θ : Fin (colLen5 (X.p.s n) r.1) → Fin N,
      (∏ h, (X.prior H.1 r.1).w (θ h)) *
        (X.recArrayLaw (X.withCol H r.1 θ)).pr (denominatorFail X (X.withCol H r.1 θ) r)) ≤
      Real.exp (-(X.p.delta * X.p.s n)) +
        (r.2.2.1.card : ℝ) * 2 ^ X.p.poolBlocks n *
          Real.exp (-(X.p.delta *
            (X.p.usedBlocks n * (X.p.q0 * X.p.uStarSeg n) : ℕ) * X.p.s n)) := by
  let P := FinProb.pi fun _ : Fin (colLen5 (X.p.s n) r.1) => X.prior H.1 r.1
  let Q := FinProb.bind P (fun θ => X.recArrayLaw (X.withCol H r.1 θ))
  let ε₀ := Real.exp (-(X.p.delta * X.p.s n))
  let ε₁ := Real.exp (-(X.p.delta *
    (X.p.usedBlocks n * (X.p.q0 * X.p.uStarSeg n) : ℕ) * X.p.s n))
  let lower := fun ta :
      (Fin (colLen5 (X.p.s n) r.1) → Fin N) × X.ArraysOn (Fin (X.p.T n)) =>
    X.candGateOn (X.withCol H r.1 ta.1) r ta.2 ta.1 ∧
      X.step3MassOn (X.withCol H r.1 ta.1) r ta.2 none < ε₀
  let ratio := fun (c : {c // c ∈ highRefs X r}) (ta :
      (Fin (colLen5 (X.p.s n) r.1) → Fin N) × X.ArraysOn (Fin (X.p.T n))) =>
    X.candGateOn (X.withCol H r.1 ta.1) r ta.2 ta.1 ∧
      X.step3MassOn (X.withCol H r.1 ta.1) r ta.2 none <
        ε₁ * X.step3MassOn (X.withCol H r.1 ta.1) r ta.2 (some c.1)
  have hpr (A : (Fin (colLen5 (X.p.s n) r.1) → Fin N) ×
      X.ArraysOn (Fin (X.p.T n)) → Prop) :
      Q.pr A = ∑ θ, P.w θ *
        (X.recArrayLaw (X.withCol H r.1 θ)).pr (fun a => A (θ, a)) := by
    unfold FinProb.pr Q
    simp only [FinProb.bind, Fintype.sum_prod_type]
    apply Finset.sum_congr rfl
    intro θ _
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro a _
    split_ifs <;> simp
  have hlo : Q.pr lower ≤ ε₀ := by
    rw [hpr]
    exact Lane_sol_s05_hist1b.step3_lower_tail X H r hr ε₀ (Real.exp_pos _).le
  have hratio (c : {c // c ∈ highRefs X r}) : Q.pr (ratio c) ≤ ε₁ := by
    rw [hpr]
    exact Lane_sol_s05_hist1b.step3_fixed_ratio_tail X H r hr c.1 ε₁ (Real.exp_pos _).le
  have hcol : colLen5 (X.p.s n) r.1 = X.p.s n := by
    cases h : r.1 <;> simp_all [colLen5]
  have hfail (ta) : denominatorFail X (X.withCol H r.1 ta.1) r ta.2 →
      lower ta ∨ ∃ c, ratio c ta := by
    have ht : (X.withCol H r.1 ta.1).2 r.1 = ta.1 := by simp [Setup5.withCol]
    rintro ⟨hg, hlo | ⟨c, hc, hrat⟩⟩
    · exact Or.inl ⟨by simpa only [ht] using hg, hlo⟩
    · have hc' := refsOn_high_subset X _ r hr hh ta.2 hc
      refine Or.inr ⟨⟨c, hc'⟩, by simpa only [ht] using hg, ?_⟩
      simpa only [ratio, ε₁, hcol, highRefs_length X r hr hh c hc'] using hrat
  have heq : (∑ θ : Fin (colLen5 (X.p.s n) r.1) → Fin N,
      (∏ h, (X.prior H.1 r.1).w (θ h)) *
        (X.recArrayLaw (X.withCol H r.1 θ)).pr (denominatorFail X (X.withCol H r.1 θ) r)) =
      Q.pr (fun ta => denominatorFail X (X.withCol H r.1 ta.1) r ta.2) := by
    rw [hpr]
    rfl
  rw [heq]
  calc
    _ ≤ Q.pr (fun ta => lower ta ∨ ∃ c, ratio c ta) := by
      unfold FinProb.pr
      apply Finset.sum_le_sum
      intro ta _
      by_cases hf : denominatorFail X (X.withCol H r.1 ta.1) r ta.2
      · simp only [if_pos hf, if_pos (hfail ta hf)]
        exact le_refl _
      · simp only [if_neg hf]
        split_ifs <;> simp [Q.nonneg ta]
    _ ≤ Q.pr lower + Q.pr (fun ta => ∃ c, ratio c ta) := Q.pr_union _ _
    _ ≤ ε₀ + ∑ c, Q.pr (ratio c) :=
      add_le_add hlo (FinProb.pr_exists_le_sum5 Q ratio)
    _ ≤ ε₀ + ∑ _c : {c // c ∈ highRefs X r}, ε₁ :=
      add_le_add (le_refl _) (Finset.sum_le_sum fun c _ => hratio c)
    _ = ε₀ + ((highRefs X r).card : ℝ) * ε₁ := by simp
    _ ≤ _ := by
      dsimp only [ε₀, ε₁]
      apply add_le_add (le_refl _)
      rw [← mul_assoc]
      apply mul_le_mul_of_nonneg_right _ (Real.exp_pos _).le
      exact_mod_cast highRefs_card X r

theorem record_designations_card (r : X.AbsRecord) (hr : X.RecOccurs r) :
    r.2.2.1.card ≤ n := by
  letI : DecidableEq (Fin (X.p.T n)) := Classical.decEq _
  obtain ⟨y, μ, hrecord⟩ := hr
  rw [hrecord.2.2.1]
  exact Finset.card_image_le.trans ((Finset.card_filter_le _ _).trans
    (Lane_sol_s05_hist1b.evenNbrs_card_le y))

/-- The finite denominator union has rate `δ/4` once the single-pool and
reference-count overheads fit in the high history budget. -/
theorem high_denominator_bound_of_budget (H : X.KeyHist) (r : X.AbsRecord)
    (hr : X.RecOccurs r) (hh : r.1.isRight) (hn : 0 < n)
    (hk : 1 ≤ X.p.usedBlocks n * (X.p.q0 * X.p.uStarSeg n))
    (hunion : Real.log (n : ℝ) + (X.p.poolBlocks n : ℝ) * Real.log 2 ≤
      X.p.delta * X.p.s n / 2)
    (habsorb : 4 * Real.log 2 ≤ X.p.delta * X.p.s n) :
    (∑ θ : Fin (colLen5 (X.p.s n) r.1) → Fin N,
      (∏ h, (X.prior H.1 r.1).w (θ h)) *
        (X.recArrayLaw (X.withCol H r.1 θ)).pr (denominatorFail X (X.withCol H r.1 θ) r)) ≤
      Real.exp (-((X.p.delta / 4) * X.p.s n)) := by
  have hnr : (0 : ℝ) < n := by exact_mod_cast hn
  have hpow : (2 : ℝ) ^ X.p.poolBlocks n =
      Real.exp ((X.p.poolBlocks n : ℝ) * Real.log 2) := by
    rw [Real.exp_nat_mul, Real.exp_log (by norm_num : (0 : ℝ) < 2)]
  have hrat : (n : ℝ) * 2 ^ X.p.poolBlocks n *
      Real.exp (-(X.p.delta *
        (X.p.usedBlocks n * (X.p.q0 * X.p.uStarSeg n) : ℕ) * X.p.s n)) ≤
        Real.exp (-(X.p.delta * X.p.s n) / 2) := by
    rw [hpow, ← Real.exp_log hnr, ← Real.exp_add, ← Real.exp_add]
    apply Real.exp_le_exp.mpr
    have hkr : (1 : ℝ) ≤ (X.p.usedBlocks n * (X.p.q0 * X.p.uStarSeg n) : ℕ) :=
      by exact_mod_cast hk
    have hp := mul_le_mul_of_nonneg_right hkr
      (mul_nonneg X.p.hdelta.1.le (Nat.cast_nonneg (X.p.s n)))
    nlinarith
  have hlo : Real.exp (-(X.p.delta * X.p.s n)) ≤
      Real.exp (-(X.p.delta * X.p.s n) / 2) := by
    apply Real.exp_le_exp.mpr
    have hp := mul_nonneg X.p.hdelta.1.le (Nat.cast_nonneg (X.p.s n))
    linarith
  apply (high_denominator_finite_bound X H r hr hh).trans
  calc
    _ ≤ Real.exp (-(X.p.delta * X.p.s n)) +
        (n : ℝ) * 2 ^ X.p.poolBlocks n *
          Real.exp (-(X.p.delta *
            (X.p.usedBlocks n * (X.p.q0 * X.p.uStarSeg n) : ℕ) * X.p.s n)) := by
      gcongr
      exact_mod_cast record_designations_card X r hr
    _ ≤ Real.exp (-(X.p.delta * X.p.s n) / 2) +
        Real.exp (-(X.p.delta * X.p.s n) / 2) := add_le_add hlo hrat
    _ = 2 * Real.exp (-(X.p.delta * X.p.s n) / 2) := by ring
    _ ≤ _ := by
      calc
        _ = Real.exp (Real.log 2 - (X.p.delta * X.p.s n) / 2) := by
          rw [sub_eq_add_neg, Real.exp_add, Real.exp_log (by norm_num : (0 : ℝ) < 2)]
          congr 1
          ring
        _ ≤ _ := Real.exp_le_exp.mpr (by nlinarith)

/-- Next-coordinate conditionals only use the prefix strictly before that
coordinate. -/
theorem condCoord_prefix_congr {s : ℕ} (P : (Fin s → Fin N) → ℝ)
    (θ ϑ : Fin s → Fin N) (h : Fin s)
    (hprefix : ∀ i, i < h → θ i = ϑ i) :
    X.condCoord P θ h = X.condCoord P ϑ h := by
  have hgate (z : Fin s → Fin N) :
      (∀ i, i < h → z i = θ i) ↔ (∀ i, i < h → z i = ϑ i) := by
    constructor
    · intro hz i hi
      exact (hz i hi).trans (hprefix i hi)
    · intro hz i hi
      exact (hz i hi).trans (hprefix i hi).symm
  unfold Setup5.condCoord
  simp_rw [hgate]

/-- At a positive prefix, the concrete `condCoord` is exactly the normalized
next-coordinate marginal. -/
theorem condCoord_expect {s : ℕ} (P : FinProb (Fin s → Fin N))
    (θ : Fin s → Fin N) (h : Fin s) (f : Fin N → ℝ)
    (hpos : 0 < P.pr (fun z => ∀ i, i < h → z i = θ i)) :
    (X.condCoord P.w θ h).expect f =
      (∑ z, if (∀ i, i < h → z i = θ i) then P.w z * f (z h) else 0) /
        P.pr (fun z => ∀ i, i < h → z i = θ i) := by
  let A := fun z : Fin s → Fin N => ∀ i, i < h → z i = θ i
  let w := fun y : Fin N => ∑ z, if A z ∧ z h = y then P.w z else 0
  have hw (y) : 0 ≤ w y := by
    apply Finset.sum_nonneg
    intro z _
    split_ifs <;> simp [P.nonneg z]
  have hmass : (∑ y, w y) = P.pr A := by
    unfold w FinProb.pr
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro z _
    by_cases ha : A z <;> simp [ha]
  have hweight (y) : (X.condCoord P.w θ h).w y = w y / P.pr A := by
    unfold Setup5.condCoord
    change (normalize5 w X.y₀).w y = w y / P.pr A
    rw [Lane_q_s05_hist1b.normalize5_weight_eq_div_of_nonneg w X.y₀ y hw
      (by simpa only [hmass] using hpos), hmass]
  unfold FinProb.expect
  simp_rw [hweight, div_mul_eq_mul_div]
  rw [← Finset.sum_div]
  congr 1
  dsimp only [w]
  simp_rw [Finset.sum_mul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro z _
  change (∑ y, (if A z ∧ z h = y then P.w z else 0) * f y) =
    if A z then P.w z * f (z h) else 0
  by_cases ha : A z <;> simp [ha]

/-- A supported path always gives a positive entering prefix. -/
theorem condCoord_prefix_pos {s : ℕ} (P : FinProb (Fin s → Fin N))
    (θ : Fin s → Fin N) (h : Fin s) (hθ : 0 < P.w θ) :
    0 < P.pr (fun z => ∀ i, i < h → z i = θ i) :=
  hθ.trans_le (FinProb.pr_fiber_single_le P _ θ (fun _ _ => rfl))

/-- The probability of the first `k` coordinates of a specified path. -/
def pathMass {s : ℕ} (P : FinProb (Fin s → Fin N)) (θ : Fin s → Fin N) (k : ℕ) : ℝ :=
  P.pr (fun z => ∀ i, i.val < k → z i = θ i)

theorem pathMass_pos {s : ℕ} (P : FinProb (Fin s → Fin N)) (θ : Fin s → Fin N)
    (hθ : 0 < P.w θ) (k : ℕ) : 0 < pathMass P θ k :=
  hθ.trans_le (FinProb.pr_fiber_single_le P _ θ (fun _ _ => rfl))

theorem condCoord_path_weight {s : ℕ} (P : FinProb (Fin s → Fin N))
    (θ : Fin s → Fin N) (hθ : 0 < P.w θ) (h : Fin s) :
    (X.condCoord P.w θ h).w (θ h) = pathMass P θ (h.val + 1) / pathMass P θ h.val := by
  have hc := condCoord_expect X P θ h (fun y => if y = θ h then 1 else 0)
    (condCoord_prefix_pos P θ h hθ)
  have hleft : (X.condCoord P.w θ h).expect (fun y => if y = θ h then 1 else 0) =
      (X.condCoord P.w θ h).w (θ h) := by simp [FinProb.expect]
  have hnum :
      (∑ z, if (∀ i, i < h → z i = θ i) then
        P.w z * (if z h = θ h then 1 else 0) else 0) = pathMass P θ (h.val + 1) := by
    unfold pathMass FinProb.pr
    apply Finset.sum_congr rfl
    intro z _
    have he : (∀ i, i.val < h.val + 1 → z i = θ i) ↔
        (∀ i, i < h → z i = θ i) ∧ z h = θ h := by
      constructor
      · intro hz
        exact ⟨fun i hi => hz i (by omega), hz h (by omega)⟩
      · rintro ⟨hz, hh⟩ i hi
        by_cases he : i = h
        · simpa only [he] using hh
        · exact hz i (by have hh := (Fin.ne_iff_vne i h).mp he; omega)
    simp only [he]
    split_ifs <;> simp_all
  rw [hleft, hnum] at hc
  exact hc

theorem condCoord_path_pos {s : ℕ} (P : FinProb (Fin s → Fin N))
    (θ : Fin s → Fin N) (hθ : 0 < P.w θ) (h : Fin s) :
    0 < (X.condCoord P.w θ h).w (θ h) := by
  rw [condCoord_path_weight X P θ hθ h]
  exact div_pos (pathMass_pos P θ hθ _) (pathMass_pos P θ hθ _)

/-- The concrete conditional-coordinate laws recover the joint path weight. -/
theorem condCoord_chain {s : ℕ} (P : FinProb (Fin s → Fin N))
    (θ : Fin s → Fin N) (hθ : 0 < P.w θ) :
    (∏ h, (X.condCoord P.w θ h).w (θ h)) = P.w θ := by
  have hzero : pathMass P θ 0 = 1 := by simp [pathMass, FinProb.pr, P.sum_eq_one]
  have hfull : pathMass P θ s = P.w θ := by
    have he (z : Fin s → Fin N) : (∀ i, i.val < s → z i = θ i) ↔ z = θ := by
      constructor
      · intro hz
        funext i
        exact hz i i.isLt
      · intro hz
        simp only [hz, implies_true]
    simp only [pathMass, FinProb.pr, he]
    simp
  have hpartial (m : ℕ) (hm : m ≤ s) :
      (∏ i : Fin m, (X.condCoord P.w θ
        ⟨i, lt_of_lt_of_le i.isLt hm⟩).w (θ ⟨i, lt_of_lt_of_le i.isLt hm⟩)) = pathMass P θ m := by
    induction m with
    | zero => simp [hzero]
    | succ m ih =>
      have hm' : m ≤ s := by omega
      have hm_lt : m < s := by omega
      rw [Fin.prod_univ_castSucc]
      change (∏ i : Fin m, (X.condCoord P.w θ
        ⟨i, lt_of_lt_of_le i.isLt hm'⟩).w (θ ⟨i, lt_of_lt_of_le i.isLt hm'⟩)) *
          (X.condCoord P.w θ ⟨m, hm_lt⟩).w (θ ⟨m, hm_lt⟩) = pathMass P θ (m + 1)
      rw [ih hm', condCoord_path_weight X P θ hθ]
      field_simp [(pathMass_pos P θ hθ m).ne']
  simpa only [hfull] using hpartial s le_rfl

/-- Chain rule for the unsmoothed log likelihood along a supported path. -/
theorem condCoord_log_chain {s : ℕ} (P Q : FinProb (Fin s → Fin N))
    (θ : Fin s → Fin N) (hP : 0 < P.w θ) (hQ : 0 < Q.w θ) :
    (∑ h, Real.log ((X.condCoord P.w θ h).w (θ h) /
      (X.condCoord Q.w θ h).w (θ h))) = Real.log (P.w θ / Q.w θ) := by
  rw [← Real.log_prod (fun h _ => div_ne_zero
    (condCoord_path_pos X P θ hP h).ne' (condCoord_path_pos X Q θ hQ h).ne')]
  rw [Finset.prod_div_distrib, condCoord_chain X P θ hP, condCoord_chain X Q θ hQ]

/-- Concentration of the predictable average of an arbitrary bounded cost,
using exactly the next-coordinate conditionals in the high-row definition.
The bound is taken under the original path law. -/
theorem condCoord_predictable_concentration {s : ℕ} (P : FinProb (Fin s → Fin N))
    (f : (Fin s → Fin N) → Fin s → Fin N → ℝ) (L ε : ℝ)
    (hs : 0 < s) (hL : 0 < L) (hε : 0 < ε)
    (hf : ∀ θ h y, 0 ≤ f θ h y ∧ f θ h y ≤ L)
    (hpredictable : ∀ θ ϑ h, (∀ i, i < h → θ i = ϑ i) → f θ h = f ϑ h) :
    P.pr (fun θ =>
      (∑ h, (X.condCoord P.w θ h).expect (f θ h)) >
        (∑ h, f θ h (θ h)) + ε * s) ≤
      Real.exp (-2 * (ε * s) ^ 2 / ((s : ℝ) * (2 * L) ^ 2)) := by
  let H := fun t : Fin (s + 1) => Fin t.val → Fin N
  let history := fun (t : Fin (s + 1)) (θ : Fin s → Fin N) =>
    fun i : Fin t.val => θ ⟨i, lt_of_lt_of_le i.isLt (Nat.le_of_lt_succ t.isLt)⟩
  let project := fun (i : Fin s) (z : H i.succ) => fun j : Fin i.val => z j.castSucc
  let mean := fun θ h => (X.condCoord P.w θ h).expect (f θ h)
  let Δ := fun h θ => f θ h (θ h) - mean θ h
  have hfiltration (i : Fin s) (θ) :
      history i.castSucc θ = project i (history i.succ θ) := rfl
  have hpre {m : ℕ} (hm : m ≤ s) (θ ϑ : Fin s → Fin N)
      (he : history ⟨m, Nat.lt_succ_of_le hm⟩ θ =
        history ⟨m, Nat.lt_succ_of_le hm⟩ ϑ) (i : Fin s) (hi : i.val < m) : θ i = ϑ i :=
    congrFun he ⟨i, hi⟩
  have hmean_congr (θ ϑ h) (he : ∀ i, i < h → θ i = ϑ i) : mean θ h = mean ϑ h := by
    dsimp only [mean]
    rw [condCoord_prefix_congr X P.w θ ϑ h he, hpredictable θ ϑ h he]
  have hadapted (m : ℕ) (hm : m ≤ s) (i : Fin s) (hi : i.val < m)
      (θ ϑ) (he : history ⟨m, Nat.lt_succ_of_le hm⟩ θ =
        history ⟨m, Nat.lt_succ_of_le hm⟩ ϑ) : Δ i θ = Δ i ϑ := by
    have hbefore (j) (hj : j < i) : θ j = ϑ j := hpre hm θ ϑ he j (lt_trans hj hi)
    dsimp only [Δ]
    rw [hmean_congr θ ϑ i hbefore, hpredictable θ ϑ i hbefore, hpre hm θ ϑ he i hi]
  have hmeanbounds (θ h) : 0 ≤ mean θ h ∧ mean θ h ≤ L := by
    constructor
    · simpa only [FinProb.expect_const] using
        ((X.condCoord P.w θ h).expect_mono (fun y => (hf θ h y).1))
    · simpa only [FinProb.expect_const] using
        ((X.condCoord P.w θ h).expect_mono (fun y => (hf θ h y).2))
  have hbound (h θ) : -L ≤ Δ h θ ∧ Δ h θ ≤ L := by
    have hm := hmeanbounds θ h
    have hh := hf θ h (θ h)
    dsimp only [Δ]
    constructor <;> linarith
  have hmean (i : Fin s) (histValue : H i.castSucc) :
      P.pr (fun θ => history i.castSucc θ = histValue) = 0 ∨
        (0 : ℝ) * P.pr (fun θ => history i.castSucc θ = histValue) ≤
          (∑ θ, if history i.castSucc θ = histValue then P.w θ * Δ i θ else 0) := by
    by_cases hzero : P.pr (fun θ => history i.castSucc θ = histValue) = 0
    · exact Or.inl hzero
    right
    let θ₀ : Fin s → Fin N := fun j => if hj : j < i then histValue ⟨j, hj⟩ else X.y₀
    have hA (θ : Fin s → Fin N) : history i.castSucc θ = histValue ↔
        ∀ j, j < i → θ j = θ₀ j := by
      constructor
      · intro he j hj
        have hz := congrFun he ⟨j, hj⟩
        simpa only [θ₀, dif_pos hj] using hz
      · intro he
        funext j
        have hj' : j.val < i.val := by simpa only [Fin.val_castSucc] using j.isLt
        have hz := he ⟨j, lt_trans j.isLt i.isLt⟩ j.isLt
        change θ ⟨j, lt_trans j.isLt i.isLt⟩ =
          (if hj : j.val < i.val then histValue ⟨j, hj⟩ else X.y₀) at hz
        split at hz
        · exact hz
        · omega
    have hpos : 0 < P.pr (fun θ => ∀ j, j < i → θ j = θ₀ j) := by
      have hnn : 0 ≤ P.pr (fun θ => history i.castSucc θ = histValue) := by
        unfold FinProb.pr
        apply Finset.sum_nonneg
        intro θ _
        split_ifs <;> simp [P.nonneg θ]
      have hp := lt_of_le_of_ne hnn (Ne.symm hzero)
      simpa only [hA] using hp
    have hc := condCoord_expect X P θ₀ i (f θ₀ i) hpos
    have hsum :
        (∑ θ, if history i.castSucc θ = histValue then P.w θ * Δ i θ else 0) =
          (∑ θ, if (∀ j, j < i → θ j = θ₀ j) then P.w θ * f θ₀ i (θ i) else 0) -
            P.pr (fun θ => ∀ j, j < i → θ j = θ₀ j) * mean θ₀ i := by
      unfold FinProb.pr
      rw [Finset.sum_mul, ← Finset.sum_sub_distrib]
      apply Finset.sum_congr rfl
      intro θ _
      by_cases ha : ∀ j, j < i → θ j = θ₀ j
      · have he := (hA θ).mpr ha
        simp only [if_pos he, if_pos ha, Δ, hmean_congr θ θ₀ i ha,
          hpredictable θ θ₀ i ha]
        ring
      · have he : history i.castSucc θ ≠ histValue := fun he => ha ((hA θ).mp he)
        simp [ha, he]
    rw [hsum]
    have hh := (eq_div_iff hpos.ne').mp hc
    dsimp only [mean]
    rw [mul_comm _ ((X.condCoord P.w θ₀ i).expect (f θ₀ i)), ← hh]
    simp
  have hwidth : 0 < ∑ _i : Fin s, (L - -L) ^ 2 := by
    simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    have hs' : (0 : ℝ) < s := by exact_mod_cast hs
    exact mul_pos hs' (sq_pos_of_pos (by linarith))
  have htail := xAzuma H P history project hfiltration Δ hadapted
    (fun _ => 0) (fun _ => -L) (fun _ => L) hbound hmean hwidth
    (ε * s) (mul_pos hε (by exact_mod_cast hs))
  have hevent : (fun θ => ∑ h, Δ h θ < (∑ _h : Fin s, (0 : ℝ)) - ε * s) =
      (fun θ => (∑ h, mean θ h) > (∑ h, f θ h (θ h)) + ε * s) := by
    funext θ
    apply propext
    dsimp only [Δ]
    rw [Finset.sum_sub_distrib]
    simp only [Finset.sum_const_zero, zero_sub]
    constructor <;> intro hh <;> linarith
  rw [hevent] at htail
  simpa only [mean, sub_neg_eq_add, ← two_mul, Finset.sum_const,
    Finset.card_univ, Fintype.card_fin, nsmul_eq_mul] using htail

/-- A next-coordinate exponential-moment bound is an unnormalized bound on
every entering prefix, including null prefixes. -/
theorem condCoord_fiber_exp_le {s : ℕ} (P : FinProb (Fin s → Fin N))
    (f : (Fin s → Fin N) → Fin s → Fin N → ℝ) (t B : ℝ)
    (hpredictable : ∀ θ ϑ h, (∀ i, i < h → θ i = ϑ i) → f θ h = f ϑ h)
    (hmgf : ∀ θ h, (X.condCoord P.w θ h).expect (fun y => Real.exp (t * f θ h y)) ≤ B)
    (θ₀ : Fin s → Fin N) (h : Fin s) :
    (∑ θ, if (∀ i, i < h → θ i = θ₀ i) then P.w θ * Real.exp (t * f θ h (θ h)) else 0) ≤
      P.pr (fun θ => ∀ i, i < h → θ i = θ₀ i) * B := by
  let A := fun θ : Fin s → Fin N => ∀ i, i < h → θ i = θ₀ i
  have hnn : 0 ≤ P.pr A := by
    unfold FinProb.pr
    apply Finset.sum_nonneg
    intro θ _
    split_ifs <;> simp [P.nonneg θ]
  by_cases hz : P.pr A = 0
  · have hzero (θ) (hθ : A θ) : P.w θ = 0 := by
      have hh := FinProb.pr_fiber_single_le P A θ hθ
      rw [hz] at hh
      exact le_antisymm hh (P.nonneg θ)
    change (∑ θ, if A θ then P.w θ * Real.exp (t * f θ h (θ h)) else 0) ≤ P.pr A * B
    rw [hz, zero_mul]
    apply le_of_eq
    apply Finset.sum_eq_zero
    intro θ _
    by_cases hθ : A θ <;> simp [hθ, hzero θ]
  · have hpos : 0 < P.pr A := lt_of_le_of_ne hnn (Ne.symm hz)
    have hc := condCoord_expect X P θ₀ h (fun y => Real.exp (t * f θ₀ h y)) hpos
    have heq :
        (∑ θ, if A θ then P.w θ * Real.exp (t * f θ h (θ h)) else 0) =
          (∑ θ, if A θ then P.w θ * Real.exp (t * f θ₀ h (θ h)) else 0) := by
      apply Finset.sum_congr rfl
      intro θ _
      by_cases hθ : A θ
      · simp only [if_pos hθ, hpredictable θ θ₀ h hθ]
      · simp only [if_neg hθ]
    change (∑ θ, if A θ then P.w θ * Real.exp (t * f θ h (θ h)) else 0) ≤ P.pr A * B
    rw [heq, ← (eq_div_iff hpos.ne').mp hc]
    exact mul_le_mul_of_nonneg_right (hmgf θ₀ h) hnn |>.trans_eq (mul_comm _ _)

/-- The finite negative-log moment bound applies on every true prefix. -/
theorem condCoord_exp_sum_moment {s : ℕ} (P : FinProb (Fin s → Fin N))
    (f : (Fin s → Fin N) → Fin s → Fin N → ℝ) (t B : ℝ) (hB : 0 ≤ B)
    (hpredictable : ∀ θ ϑ h, (∀ i, i < h → θ i = ϑ i) → f θ h = f ϑ h)
    (hmgf : ∀ θ h, (X.condCoord P.w θ h).expect (fun y => Real.exp (t * f θ h y)) ≤ B) :
    P.expect (fun θ => Real.exp (t * ∑ h, f θ h (θ h))) ≤ B ^ s := by
  have hmoment (m : ℕ) (hm : m ≤ s) :
      P.expect (fun θ => Real.exp (t * ∑ i : Fin m,
        f θ ⟨i, lt_of_lt_of_le i.isLt hm⟩ (θ ⟨i, lt_of_lt_of_le i.isLt hm⟩))) ≤ B ^ m := by
    induction m with
    | zero => simp [FinProb.expect_const]
    | succ m ih =>
      have hm' : m ≤ s := by omega
      have hm_lt : m < s := by omega
      let h : Fin s := ⟨m, hm_lt⟩
      let hist := fun θ : Fin s → Fin N => fun i : Fin m =>
        θ ⟨i, lt_of_lt_of_le i.isLt hm'⟩
      let F := fun θ => Real.exp (t * ∑ i : Fin m,
        f θ ⟨i, lt_of_lt_of_le i.isLt hm'⟩ (θ ⟨i, lt_of_lt_of_le i.isLt hm'⟩))
      have hF (θ ϑ) (he : hist θ = hist ϑ) : F θ = F ϑ := by
        dsimp only [F]
        congr 2
        apply Finset.sum_congr rfl
        intro i _
        let j : Fin s := ⟨i, lt_of_lt_of_le i.isLt hm'⟩
        have hpre (k : Fin s) (hk : k < j) : θ k = ϑ k :=
          congrFun he ⟨k, lt_trans hk i.isLt⟩
        have hj : θ j = ϑ j := congrFun he i
        change f θ j (θ j) = f ϑ j (ϑ j)
        rw [hpredictable θ ϑ j hpre, hj]
      have hlocal (v : Fin m → Fin N) :
          (∑ θ, if hist θ = v then P.w θ * Real.exp (-(-t) * (f θ h (θ h) - 0)) else 0) ≤
            (∑ θ, if hist θ = v then P.w θ else 0) * B := by
        let θ₀ : Fin s → Fin N := fun j => if hj : j.val < m then v ⟨j, hj⟩ else X.y₀
        have hA (θ : Fin s → Fin N) : hist θ = v ↔ ∀ j, j < h → θ j = θ₀ j := by
          constructor
          · intro he j hj
            have hh : j.val < m := hj
            have he' := congrFun he ⟨j, hh⟩
            simpa only [θ₀, dif_pos hh] using he'
          · intro he
            funext j
            have he' := he ⟨j, lt_of_lt_of_le j.isLt hm'⟩ j.isLt
            change θ ⟨j, lt_of_lt_of_le j.isLt hm'⟩ =
              (if hj : j.val < m then v ⟨j, hj⟩ else X.y₀) at he'
            split at he'
            · exact he'
            · omega
        simp only [hA, neg_neg, sub_zero]
        have heq : (∑ θ, if (∀ j, j < h → θ j = θ₀ j) then P.w θ else 0) =
            P.pr (fun θ => ∀ j, j < h → θ j = θ₀ j) := by
          unfold FinProb.pr
          apply Finset.sum_congr rfl
          intro θ _
          by_cases ha : ∀ j, j < h → θ j = θ₀ j <;> simp [ha]
        rw [heq]
        exact condCoord_fiber_exp_le X P f t B hpredictable hmgf θ₀ h
      have hstep := FinProb.expect_mul_fiber_exp_neg_centered_le P hist F
        (fun θ => f θ h (θ h)) 0 (-t) B hF (fun θ => (Real.exp_pos _).le) hlocal
      have heq :
          P.expect (fun θ => Real.exp (t * ∑ i : Fin (m + 1),
            f θ ⟨i, lt_of_lt_of_le i.isLt hm⟩ (θ ⟨i, lt_of_lt_of_le i.isLt hm⟩))) =
          P.expect (fun θ => F θ * Real.exp (-(-t) * (f θ h (θ h) - 0))) := by
        apply congrArg P.expect
        funext θ
        dsimp only [F]
        rw [Fin.sum_univ_castSucc]
        simp only [mul_add, Real.exp_add, neg_neg, sub_zero]
        rfl
      rw [heq]
      apply hstep.trans
      calc
        B * P.expect F ≤ B * B ^ m :=
          mul_le_mul_of_nonneg_left (ih hm') hB
        _ = B ^ (m + 1) := by rw [pow_succ]; ring
  exact hmoment s le_rfl

/-- The finite negative-log moment bound applies on every true prefix. -/
theorem condCoord_negative_log_fiber {s : ℕ} (P Q : FinProb (Fin s → Fin N))
    (θ₀ : Fin s → Fin N) (h : Fin s) :
    (∑ θ, if (∀ i, i < h → θ i = θ₀ i) then
      P.w θ * Real.exp (max 0 (Real.log
        ((X.condCoord Q.w θ h).w (θ h) / (X.condCoord P.w θ h).w (θ h))) / 2) else 0) ≤
      P.pr (fun θ => ∀ i, i < h → θ i = θ₀ i) * 2 := by
  let f := fun θ h y => max 0 (Real.log
    ((X.condCoord Q.w θ h).w y / (X.condCoord P.w θ h).w y))
  have hpre (θ ϑ h) (hh : ∀ i, i < h → θ i = ϑ i) : f θ h = f ϑ h := by
    dsimp only [f]
    rw [condCoord_prefix_congr X Q.w θ ϑ h hh, condCoord_prefix_congr X P.w θ ϑ h hh]
  have hm (θ h) : (X.condCoord P.w θ h).expect (fun y => Real.exp ((1 / 2 : ℝ) * f θ h y)) ≤ 2 := by
    simpa only [f, one_div, div_eq_mul_inv, one_mul, mul_comm] using
      Lane_sol_s05_hist1b.finite_negative_log_moment (X.condCoord P.w θ h) (X.condCoord Q.w θ h)
  simpa only [f, one_div, div_eq_mul_inv, one_mul, mul_comm] using
    condCoord_fiber_exp_le X P f (1 / 2) 2 hpre hm θ₀ h

/-- Negative-log moments tensorize along the concrete conditional path laws. -/
theorem condCoord_negative_log_moment {s : ℕ} (P Q : FinProb (Fin s → Fin N)) :
    P.expect (fun θ => Real.exp ((∑ h, max 0 (Real.log
      ((X.condCoord Q.w θ h).w (θ h) / (X.condCoord P.w θ h).w (θ h)))) / 2)) ≤
        (2 : ℝ) ^ s := by
  let f := fun θ h y => max 0 (Real.log
    ((X.condCoord Q.w θ h).w y / (X.condCoord P.w θ h).w y))
  have hpre (θ ϑ h) (hh : ∀ i, i < h → θ i = ϑ i) : f θ h = f ϑ h := by
    dsimp only [f]
    rw [condCoord_prefix_congr X Q.w θ ϑ h hh, condCoord_prefix_congr X P.w θ ϑ h hh]
  have hm (θ h) : (X.condCoord P.w θ h).expect (fun y => Real.exp ((1 / 2 : ℝ) * f θ h y)) ≤ 2 := by
    simpa only [f, one_div, div_eq_mul_inv, one_mul, mul_comm] using
      Lane_sol_s05_hist1b.finite_negative_log_moment (X.condCoord P.w θ h) (X.condCoord Q.w θ h)
  simpa only [f, one_div, div_eq_mul_inv, one_mul, mul_comm] using
    condCoord_exp_sum_moment X P f (1 / 2) 2 (by norm_num) hpre hm

/-- The negative conditional logs have an exponential tail under the original
path law. This needs no successful-path conditioning or absolute continuity. -/
theorem condCoord_negative_log_tail {s : ℕ} (P Q : FinProb (Fin s → Fin N)) (C : ℝ) :
    P.pr (fun θ => C * s ≤ ∑ h, max 0 (Real.log
      ((X.condCoord Q.w θ h).w (θ h) / (X.condCoord P.w θ h).w (θ h)))) ≤
        Real.exp (-((C / 2 - Real.log 2) * s)) := by
  let f := fun θ => ∑ h, max 0 (Real.log
    ((X.condCoord Q.w θ h).w (θ h) / (X.condCoord P.w θ h).w (θ h)))
  have hm : P.expect (fun θ => Real.exp ((1 / 2 : ℝ) * f θ)) ≤ (2 : ℝ) ^ s := by
    simpa only [f, one_div, div_eq_mul_inv, one_mul, mul_comm] using condCoord_negative_log_moment X P Q
  have hpow : (2 : ℝ) ^ s = Real.exp ((s : ℝ) * Real.log 2) := by
    rw [Real.exp_nat_mul, Real.exp_log (by norm_num : (0 : ℝ) < 2)]
  apply (FinProb.pr_exp_markov P f (1 / 2) (C * s) (by norm_num)).trans
  calc
    _ ≤ Real.exp (-(1 / 2 : ℝ) * (C * s)) * (2 : ℝ) ^ s :=
      mul_le_mul_of_nonneg_left hm (Real.exp_pos _).le
    _ = Real.exp (-((C / 2 - Real.log 2) * s)) := by
      rw [hpow, ← Real.exp_add]
      congr 1
      ring

/-- Joint domination and the log chain rule bound the actual positive costs
by the sum of the negative conditional logs. -/
theorem condCoord_positive_log_bound {s : ℕ} (P Q : FinProb (Fin s → Fin N))
    (B : ℝ) (hdom : ∀ θ, P.w θ ≤ Real.exp B * Q.w θ)
    (θ : Fin s → Fin N) (hP : 0 < P.w θ) :
    (∑ h, max 0 (Real.log
      ((X.condCoord P.w θ h).w (θ h) / (X.condCoord Q.w θ h).w (θ h)))) ≤
      B + ∑ h, max 0 (Real.log
        ((X.condCoord Q.w θ h).w (θ h) / (X.condCoord P.w θ h).w (θ h))) := by
  have hQ : 0 < Q.w θ := by
    by_contra h
    have hz : Q.w θ = 0 := le_antisymm (le_of_not_gt h) (Q.nonneg θ)
    have hh := hdom θ
    rw [hz, mul_zero] at hh
    exact (not_le_of_gt hP) hh
  have hjoint : Real.log (P.w θ / Q.w θ) ≤ B := by
    have hratio : P.w θ / Q.w θ ≤ Real.exp B := (div_le_iff₀ hQ).mpr (hdom θ)
    exact (Real.log_le_log (div_pos hP hQ) hratio).trans_eq (Real.log_exp B)
  have hsplit (h : Fin s) :
      max 0 (Real.log ((X.condCoord P.w θ h).w (θ h) / (X.condCoord Q.w θ h).w (θ h))) =
        Real.log ((X.condCoord P.w θ h).w (θ h) / (X.condCoord Q.w θ h).w (θ h)) +
          max 0 (Real.log ((X.condCoord Q.w θ h).w (θ h) / (X.condCoord P.w θ h).w (θ h))) := by
    have hp := condCoord_path_pos X P θ hP h
    have hq := condCoord_path_pos X Q θ hQ h
    have he : Real.log ((X.condCoord Q.w θ h).w (θ h) / (X.condCoord P.w θ h).w (θ h)) =
        -Real.log ((X.condCoord P.w θ h).w (θ h) / (X.condCoord Q.w θ h).w (θ h)) := by
      rw [Real.log_div hq.ne' hp.ne', Real.log_div hp.ne' hq.ne']
      ring
    rw [he]
    by_cases hh : 0 ≤ Real.log ((X.condCoord P.w θ h).w (θ h) / (X.condCoord Q.w θ h).w (θ h))
    · rw [max_eq_right hh, max_eq_left (neg_nonpos.mpr hh), add_zero]
    · have hh' := (lt_of_not_ge hh).le
      rw [max_eq_left hh', max_eq_right (neg_nonneg.mpr hh')]
      ring
  simp_rw [hsplit]
  rw [Finset.sum_add_distrib, condCoord_log_chain X P Q θ hP hQ]
  exact add_le_add hjoint (le_refl _)

/-- Actual positive-log path costs have a uniform exponential tail whenever
the joint path laws are dominated. Null source paths contribute zero mass. -/
theorem condCoord_positive_log_tail {s : ℕ} (P Q : FinProb (Fin s → Fin N))
    (B C : ℝ) (hdom : ∀ θ, P.w θ ≤ Real.exp B * Q.w θ) :
    P.pr (fun θ => B + C * s < ∑ h, max 0 (Real.log
      ((X.condCoord P.w θ h).w (θ h) / (X.condCoord Q.w θ h).w (θ h)))) ≤
        Real.exp (-((C / 2 - Real.log 2) * s)) := by
  apply le_trans _ (condCoord_negative_log_tail X P Q C)
  unfold FinProb.pr
  apply Finset.sum_le_sum
  intro θ _
  by_cases hP : P.w θ = 0
  · simp [hP]
  have hPpos : 0 < P.w θ := lt_of_le_of_ne (P.nonneg θ) (Ne.symm hP)
  by_cases hbad : B + C * s < ∑ h, max 0 (Real.log
      ((X.condCoord P.w θ h).w (θ h) / (X.condCoord Q.w θ h).w (θ h)))
  · have hb := condCoord_positive_log_bound X P Q B hdom θ hPpos
    have hn : C * s ≤ ∑ h, max 0 (Real.log
        ((X.condCoord Q.w θ h).w (θ h) / (X.condCoord P.w θ h).w (θ h))) := by linarith
    simp only [if_pos hbad, if_pos hn]
    exact le_refl _
  · rw [if_neg hbad]
    split_ifs <;> simp [P.nonneg θ]

/-- Normalizing a restriction retains pointwise domination by the original
law, as well as the atom cap and a cost bound. -/
theorem finite_restriction_domination {Ω : Type*} [Fintype Ω] [DecidableEq Ω]
    (P : FinProb Ω) (G : Ω → Prop) (f : Ω → ℝ) (D B β : ℝ)
    (hD : 0 ≤ D) (hB : 0 ≤ B) (hβ : 0 ≤ β) (hβ1 : β < 1)
    (hmass : 1 - β ≤ P.pr G) (hcap : ∀ ω, G ω → P.w ω ≤ D)
    (hcost : (∑ ω, if G ω then P.w ω * f ω else 0) ≤ B) :
    ∃ R : FinProb Ω,
      (∀ ω, R.w ω ≤ P.w ω / (1 - β)) ∧
      (∀ ω, R.w ω ≤ D / (1 - β)) ∧
      (∀ ω, R.w ω ≠ 0 → P.w ω ≠ 0) ∧ R.expect f ≤ B / (1 - β) := by
  have hden : 0 < 1 - β := by linarith
  have hpos : 0 < P.pr G := hden.trans_le hmass
  let R : FinProb Ω := {
    w := fun ω => (if G ω then P.w ω else 0) / P.pr G
    nonneg := by
      intro ω
      apply div_nonneg _ hpos.le
      split_ifs <;> simp [P.nonneg ω]
    sum_eq_one := by
      rw [← Finset.sum_div]
      change P.pr G / P.pr G = 1
      exact div_self hpos.ne' }
  refine ⟨R, ?_, ?_, ?_, ?_⟩
  · intro ω
    dsimp only [R]
    by_cases h : G ω
    · rw [if_pos h]
      exact div_le_div_of_nonneg_left (P.nonneg ω) hden hmass
    · rw [if_neg h, zero_div]
      exact div_nonneg (P.nonneg ω) hden.le
  · intro ω
    dsimp only [R]
    by_cases h : G ω
    · rw [if_pos h]
      exact div_le_div₀ hD (hcap ω h) hden hmass
    · rw [if_neg h, zero_div]
      exact div_nonneg hD hden.le
  · intro ω hω hz
    apply hω
    dsimp only [R]
    by_cases h : G ω <;> simp only [h, ite_true, ite_false, hz, zero_div]
  · have heq : R.expect f =
        (∑ ω, if G ω then P.w ω * f ω else 0) / P.pr G := by
      unfold FinProb.expect
      dsimp only [R]
      rw [Finset.sum_div]
      apply Finset.sum_congr rfl
      intro ω _
      by_cases h : G ω <;> simp [h, div_mul_eq_mul_div]
    rw [heq]
    exact (div_le_div_of_nonneg_right hcost hpos.le).trans
      (div_le_div_of_nonneg_left hB hden hmass)

/-- Simultaneous weighted selection costs incur only the one normalization
loss, because prices sum to one. -/
theorem finite_weighted_selection_cost {Ω I : Type*} [Fintype Ω] [Fintype I]
    (P R : FinProb Ω) (Q : I → FinProb Ω) (price : I → ℝ) (C : ℝ)
    (hprice : ∀ i, 0 ≤ price i) (hsum : ∑ i, price i = 1)
    (hC : 1 ≤ C) (hQ : ∀ i ω, 0 < (Q i).w ω)
    (hdom : ∀ ω, R.w ω ≤ C * P.w ω) :
    (∑ i, price i * R.expect (fun ω => max 0 (Real.log (R.w ω / (Q i).w ω)))) ≤
      R.expect (fun ω => ∑ i, price i * max 0 (Real.log (P.w ω / (Q i).w ω))) + Real.log C := by
  calc
    _ ≤ ∑ i, price i *
        (R.expect (fun ω => max 0 (Real.log (P.w ω / (Q i).w ω))) + Real.log C) := by
      apply Finset.sum_le_sum
      intro i _
      exact mul_le_mul_of_nonneg_left
        (Lane_sol_s05_hist1b.finite_log_cost_selection P R (Q i) C hC (hQ i) hdom)
        (hprice i)
    _ = _ := by
      simp only [FinProb.expect, mul_add, Finset.sum_add_distrib]
      rw [← Finset.sum_mul, hsum, one_mul]
      congr 1
      simp_rw [Finset.mul_sum]
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro ω _
      apply Finset.sum_congr rfl
      intro i _
      ring

/-- A clipped weighted source cost and a density exception budget give the
actual (unclipped) selection cost needed for one price direction. -/
theorem finite_clipped_price_law {Ω I : Type*} [Fintype Ω] [DecidableEq Ω] [Fintype I]
    (P : FinProb Ω) (Q : I → FinProb Ω) (price : I → ℝ) (D L B η β : ℝ)
    (hprice : ∀ i, 0 ≤ price i) (hsum : ∑ i, price i = 1)
    (hQ : ∀ i ω, 0 < (Q i).w ω)
    (hD : 0 ≤ D) (hL : 0 < L) (hB : 0 ≤ B) (hη : 0 ≤ η)
    (hβ : η + B / L ≤ β) (hβ1 : β < 1)
    (hdensity : P.pr (fun ω => D < P.w ω) ≤ η)
    (hclip : P.expect (fun ω => min L
      (∑ i, price i * max 0 (Real.log (P.w ω / (Q i).w ω)))) ≤ B) :
    ∃ R : FinProb Ω,
      (∀ ω, R.w ω ≤ D / (1 - β)) ∧
      (∀ ω, R.w ω ≠ 0 → P.w ω ≠ 0) ∧
      (∑ i, price i * R.expect (fun ω => max 0 (Real.log (R.w ω / (Q i).w ω)))) ≤
        B / (1 - β) + Real.log (1 / (1 - β)) := by
  let f := fun ω => ∑ i, price i * max 0 (Real.log (P.w ω / (Q i).w ω))
  have hf (ω) : 0 ≤ f ω :=
    Finset.sum_nonneg fun i _ => mul_nonneg (hprice i) (le_max_left _ _)
  let G := fun ω => P.w ω ≤ D ∧ f ω ≤ L
  letI : DecidablePred G := fun _ => Classical.propDecidable _
  have hbadCost : P.pr (fun ω => L < f ω) ≤ B / L := by
    have hm := P.markov (fun ω => min L (f ω)) L
      (fun ω => le_min hL.le (hf ω)) hL
    have hle : P.pr (fun ω => L < f ω) ≤ P.pr (fun ω => L ≤ min L (f ω)) := by
      unfold FinProb.pr
      apply Finset.sum_le_sum
      intro ω _
      by_cases h : L < f ω
      · simp only [if_pos h, if_pos (le_min (le_refl L) h.le)]
        exact le_refl _
      · simp only [if_neg h]
        split_ifs <;> simp [P.nonneg ω]
    exact hle.trans (hm.trans (div_le_div_of_nonneg_right hclip hL.le))
  have hbad : P.pr (fun ω => ¬ G ω) ≤ β := by
    have he : (fun ω => ¬ G ω) = (fun ω => D < P.w ω ∨ L < f ω) := by
      funext ω
      exact propext (not_and_or.trans (or_congr not_le not_le))
    rw [he]
    exact (P.pr_union _ _).trans ((add_le_add hdensity hbadCost).trans hβ)
  have hmass : 1 - β ≤ P.pr G := by
    have htotal : P.pr G + P.pr (fun ω => ¬ G ω) = 1 := by
      unfold FinProb.pr
      rw [← Finset.sum_add_distrib]
      calc
        _ = ∑ ω, P.w ω := by
          apply Finset.sum_congr rfl
          intro ω _
          by_cases h : G ω <;> simp [h]
        _ = 1 := P.sum_eq_one
    linarith
  have hcost : (∑ ω, if G ω then P.w ω * f ω else 0) ≤ B := by
    apply le_trans _ hclip
    unfold FinProb.expect
    apply Finset.sum_le_sum
    intro ω _
    by_cases h : G ω
    · change (if G ω then P.w ω * f ω else 0) ≤ P.w ω * min L (f ω)
      rw [if_pos h, min_eq_right h.2]
    · rw [if_neg h]
      exact mul_nonneg (P.nonneg ω) (le_min hL.le (hf ω))
  have hβ0 : 0 ≤ β := (add_nonneg hη (div_nonneg hB hL.le)).trans hβ
  obtain ⟨R, hdom, hcap, hsupp, hcost⟩ := finite_restriction_domination
    P G f D B β hD hB hβ0 hβ1 hmass (fun ω h => h.1) hcost
  refine ⟨R, hcap, hsupp, ?_⟩
  have hC : 1 ≤ 1 / (1 - β) := by
    apply (le_div_iff₀ (by linarith : 0 < 1 - β)).mpr
    linarith
  have hdom' (ω) : R.w ω ≤ (1 / (1 - β)) * P.w ω := by
    simpa only [one_div, div_eq_mul_inv, one_mul, mul_comm] using hdom ω
  exact (finite_weighted_selection_cost P R Q price _ hprice hsum hC hQ hdom').trans
    (add_le_add (by simpa only [f] using hcost) (le_refl _))

end
end HypercubeRamsey.Lane_sol_s05_1f
