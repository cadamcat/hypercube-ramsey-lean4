import HypercubeRamsey.S15.ClusterReference_sol_s15_transfer

namespace HypercubeRamsey.Lane_sol_s15_transfer

open Classical S15 Filter OAI.HypercubeRamsey
open scoped BigOperators

set_option backward.isDefEq.respectTransparency false

abbrev RawSlices {κ : CConsts} {T : Stage} {k : ℕ}
    (PT : ProfiledTiling κ T k) (hPT : PT.Valid)
    (hm : PT.tiling.mode = .highSmall ∨ PT.tiling.mode = .highLarge) :=
  ∀ s : ClusterSlice PT,
    (∀ r, (clusterSolver PT hPT hm s.1).Val r) × ClusterSliceOutcome PT s.1

def rawSlicesHistory {κ : CConsts} {T : Stage} {k : ℕ}
    {PT : ProfiledTiling κ T k} {hPT : PT.Valid}
    {hm : PT.tiling.mode = .highSmall ∨ PT.tiling.mode = .highLarge}
    (z : RawSlices PT hPT hm) : ClusterHistory PT hPT hm := fun r => (z r.1).1 r.2

def rawSlicesInternal {κ : CConsts} {T : Stage} {k : ℕ}
    {PT : ProfiledTiling κ T k} {hPT : PT.Valid}
    {hm : PT.tiling.mode = .highSmall ∨ PT.tiling.mode = .highLarge}
    (z : RawSlices PT hPT hm) : ClusterInternalData PT := fun s => (z s).2

noncomputable def sliceNominal {κ : CConsts} {T : Stage} {k : ℕ}
    (PT : ProfiledTiling κ T k) (hPT : PT.Valid)
    (hm : PT.tiling.mode = .highSmall ∨ PT.tiling.mode = .highLarge)
    (x : Fin (T.S.N k)) (b : OddPosition T k) (z : RawSlices PT hPT hm) : ℝ :=
  normalizedHit (T.S.E k) PT.tiling.c (PT.π (patchAt PT hPT b.1)) x
    ((z (clusterSliceAt PT hPT b.1)).2.2 (solverWordAt PT hPT hm b.1))

theorem slice_nominal_depends {κ : CConsts} {T : Stage} {k : ℕ}
    (PT : ProfiledTiling κ T k) (hPT : PT.Valid)
    (hm : PT.tiling.mode = .highSmall ∨ PT.tiling.mode = .highLarge)
    (x : Fin (T.S.N k)) (b : OddPosition T k) :
    FinProb.DependsOn (sliceNominal PT hPT hm x b) {clusterSliceAt PT hPT b.1} := by
  intro z z' hzz
  unfold sliceNominal
  rw [hzz _ (Finset.mem_singleton_self _)]

theorem slice_nominal_mean_one {κ : CConsts} {T : Stage} {k : ℕ}
    (PT : ProfiledTiling κ T k) (hPT : PT.Valid)
    (hm : PT.tiling.mode = .highSmall ∨ PT.tiling.mode = .highLarge)
    (x : Fin (T.S.N k)) (b : OddPosition T k)
    (hd : 0 < deg (T.S.E k) PT.tiling.c (PT.π (patchAt PT hPT b.1)).w x) :
    (FinLaw.pi (sliceRawLaw PT hPT hm)).E (sliceNominal PT hPT hm x b) = 1 := by
  let c : ClusterConsultation PT := wordAtOdd PT hPT hm b
  have hfun : sliceNominal PT hPT hm x b = (fun z : RawSlices PT hPT hm =>
      normalizedHit (T.S.E k) PT.tiling.c (PT.π c.1.1) x ((z c.1).2.2 c.2)) := rfl
  rw [hfun, E_pi_coord (sliceRawLaw PT hPT hm) c.1
    (fun ω => normalizedHit (T.S.E k) PT.tiling.c (PT.π c.1.1) x (ω.2.2 c.2))]
  change (sliceRawLaw PT hPT hm c.1).E (fun ω =>
    if 0 < deg (T.S.E k) PT.tiling.c (PT.π c.1.1).w x then
      hit (T.S.E k) PT.tiling.c x (ω.2.2 c.2) / deg (T.S.E k) PT.tiling.c (PT.π c.1.1).w x else 0) = 1
  have hd' : 0 < deg (T.S.E k) PT.tiling.c (PT.π c.1.1).w x := hd
  simp_rw [if_pos hd']
  exact raw_slice_nominal_hit_E PT hPT hm c.1 c.2 x hd'

theorem nominal_product_depends {κ : CConsts} {T : Stage} {k : ℕ}
    {α : Type*} [DecidableEq α]
    (PT : ProfiledTiling κ T k) (hPT : PT.Valid)
    (hm : PT.tiling.mode = .highSmall ∨ PT.tiling.mode = .highLarge)
    (x : Fin (T.S.N k)) (A : Finset α) (b : α → OddPosition T k) :
    FinProb.DependsOn (fun z => ∏ a ∈ A, sliceNominal PT hPT hm x (b a) z)
      (A.image fun a => clusterSliceAt PT hPT (b a).1) := by
  intro z z' hzz
  apply Finset.prod_congr rfl
  intro a ha
  apply slice_nominal_depends PT hPT hm x (b a)
  intro s hs
  have heq := Finset.mem_singleton.mp hs
  subst s
  exact hzz _ (Finset.mem_image.mpr ⟨a, ha, rfl⟩)

theorem nominal_product_mean_one {κ : CConsts} {T : Stage} {k : ℕ}
    {α : Type*} [DecidableEq α]
    (PT : ProfiledTiling κ T k) (hPT : PT.Valid)
    (hm : PT.tiling.mode = .highSmall ∨ PT.tiling.mode = .highLarge)
    (x : Fin (T.S.N k)) (A : Finset α) (b : α → OddPosition T k)
    (hinj : Set.InjOn (fun a => clusterSliceAt PT hPT (b a).1) A)
    (hd : ∀ a ∈ A, 0 < deg (T.S.E k) PT.tiling.c (PT.π (patchAt PT hPT (b a).1)).w x) :
    (FinLaw.pi (sliceRawLaw PT hPT hm)).E (fun z => ∏ a ∈ A, sliceNominal PT hPT hm x (b a) z) = 1 := by
  rw [E_pi_prod_of_disjoint (sliceRawLaw PT hPT hm) A (fun a => sliceNominal PT hPT hm x (b a))
    (fun a => {clusterSliceAt PT hPT (b a).1}) (fun a ha => slice_nominal_depends PT hPT hm x (b a))
    (fun a ha a' ha' hne => by
      apply Finset.disjoint_left.mpr
      intro s hs hs'
      have heq := (Finset.mem_singleton.mp hs).symm.trans (Finset.mem_singleton.mp hs')
      exact hne (hinj ha ha' heq))]
  apply Finset.prod_eq_one
  intro a ha
  exact slice_nominal_mean_one PT hPT hm x (b a) (hd a ha)

theorem slice_sigma_depends {κ : CConsts} {T : Stage} {k : ℕ}
    (PT : ProfiledTiling κ T k) (hPT : PT.Valid)
    (hm : PT.tiling.mode = .highSmall ∨ PT.tiling.mode = .highLarge)
    (i : Fin PT.tiling.m) (x : Fin (T.S.N k)) (a : EvenPosition T k) :
    FinProb.DependsOn (fun z : RawSlices PT hPT hm =>
      (PT.tiling.P i).M * clusterSigma PT hPT hm (rawSlicesHistory z) (rawSlicesInternal z) a x)
      {clusterSliceAt PT hPT a.1} := by
  intro z z' hzz
  have hs := hzz _ (Finset.mem_singleton_self (clusterSliceAt PT hPT a.1))
  let s := clusterSliceAt PT hPT a.1
  let v : EvenRole PT.tiling s.1 := clusterCenterRole PT hPT hm a
  change (PT.tiling.P i).M * (clusterSolver PT hPT hm s.1).σ v (z s).1
      (nbrLabels v.1 (z s).2.2) x =
    (PT.tiling.P i).M * (clusterSolver PT hPT hm s.1).σ v (z' s).1
      (nbrLabels v.1 (z' s).2.2) x
  rw [hs]

set_option maxHeartbeats 600000 in
theorem raw_core_row_mean_eq_sigma {κ : CConsts} {T : Stage} {k : ℕ}
    (PT : ProfiledTiling κ T k) (hPT : PT.Valid)
    (hm : PT.tiling.mode = .highSmall ∨ PT.tiling.mode = .highLarge)
    (i : Fin PT.tiling.m) (x : Fin (T.S.N k)) (a : EvenPosition T k)
    (hd : ∀ b ∈ clusterBulkNeighbours PT hPT a,
      0 < deg (T.S.E k) PT.tiling.c (PT.π (patchAt PT hPT b.1)).w x) :
    (clusterRawReferenceLaw PT hPT hm).E (fun z => coreRowProduct PT hPT hm i x a z.1 z.2) =
      (clusterRawReferenceLaw PT hPT hm).E (fun z => (PT.tiling.P i).M * clusterSigma PT hPT hm z.1 z.2 a x) := by
  classical
  let P := sliceRawLaw PT hPT hm
  let A := clusterBulkNeighbours PT hPT a
  let F (z : RawSlices PT hPT hm) :=
    (PT.tiling.P i).M * clusterSigma PT hPT hm (rawSlicesHistory z) (rawSlicesInternal z) a x
  let G (z : RawSlices PT hPT hm) := ∏ b ∈ A, sliceNominal PT hPT hm x b z
  have hF := slice_sigma_depends PT hPT hm i x a
  have hG : FinProb.DependsOn G (A.image (fun b : OddPosition T k => clusterSliceAt PT hPT b.1)) :=
    nominal_product_depends PT hPT hm x A id
  have hdis : Disjoint {clusterSliceAt PT hPT a.1} (A.image fun b : OddPosition T k => clusterSliceAt PT hPT b.1) := by
    apply Finset.disjoint_left.mpr
    intro s hs hs'
    obtain ⟨b, hb, hbs⟩ := Finset.mem_image.mp hs'
    have heq := hbs.trans (Finset.mem_singleton.mp hs)
    exact (Finset.mem_filter.mp hb).2.2.2 heq
  have hmeanG : (FinLaw.pi P).E G = 1 :=
    nominal_product_mean_one PT hPT hm x A id (bulk_slices_injective PT hPT a) hd
  rw [raw_reference_E_eq_slices, raw_reference_E_eq_slices]
  change (FinLaw.pi P).E (fun z => F z * G z) = (FinLaw.pi P).E F
  rw [E_pi_mul_of_disjoint P F G {clusterSliceAt PT hPT a.1}
    (A.image fun b : OddPosition T k => clusterSliceAt PT hPT b.1) hF hG hdis, hmeanG, mul_one]

theorem raw_kept_product_drop_crossings {κ : CConsts} {T : Stage} {k : ℕ}
    (PT : ProfiledTiling κ T k) (hPT : PT.Valid)
    (hm : PT.tiling.mode = .highSmall ∨ PT.tiling.mode = .highLarge)
    (i : Fin PT.tiling.m) (x : Fin (T.S.N k)) (M : ClusterMask PT)
    (hM : ClusterMaskGeometry PT hPT i M)
    (hwidth : ∀ j, ((PT.tiling.P j).h : ℝ) + 2 ≤ (T.S.n k : ℝ) ^ (2 * κ.ι))
    (hd : ∀ j, 0 < deg (T.S.E k) PT.tiling.c (PT.π j).w x) :
    (clusterRawReferenceLaw PT hPT hm).E (fun z => clusterKeptProduct PT hPT hm i x M z.1 z.2) =
      (clusterRawReferenceLaw PT hPT hm).E (fun z =>
        ∏ r ∈ clusterKeptRows M, coreRowProduct PT hPT hm i x (M.positions r) z.1 z.2) := by
  classical
  let P := sliceRawLaw PT hPT hm
  let A := clusterAllowedCrossings PT hPT M \ M.crossingBins
  let F (z : RawSlices PT hPT hm) := ∏ r ∈ clusterKeptRows M,
    coreRowProduct PT hPT hm i x (M.positions r) (rawSlicesHistory z) (rawSlicesInternal z)
  let G (z : RawSlices PT hPT hm) := ∏ q ∈ A, sliceNominal PT hPT hm x q.2 z
  let S : Finset (ClusterSlice PT) := Finset.univ.filter fun s => s.1 = i
  have hF : FinProb.DependsOn F S := by
    intro z z' hzz
    apply Finset.prod_congr rfl
    intro r hr
    have hp := Lane_q_s15_c2.patchAt_eq_of_evenPatchPosition hPT (hM.1 r)
    have hsig : (PT.tiling.P i).M * clusterSigma PT hPT hm (rawSlicesHistory z) (rawSlicesInternal z) (M.positions r) x =
        (PT.tiling.P i).M * clusterSigma PT hPT hm (rawSlicesHistory z') (rawSlicesInternal z') (M.positions r) x := by
      apply slice_sigma_depends PT hPT hm i x (M.positions r)
      intro s hs
      have heq := Finset.mem_singleton.mp hs
      subst s
      exact hzz _ (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hp⟩)
    unfold coreRowProduct
    rw [hsig]
    apply congrArg (fun y : ℝ =>
      (PT.tiling.P i).M * clusterSigma PT hPT hm (rawSlicesHistory z') (rawSlicesInternal z') (M.positions r) x * y)
    apply Finset.prod_congr rfl
    intro b hb
    have hbp := (Finset.mem_filter.mp hb).2.2.1
    apply slice_nominal_depends PT hPT hm x b
    intro s hs
    have heq := Finset.mem_singleton.mp hs
    subst s
    exact hzz _ (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hbp.trans hp⟩)
  have hG : FinProb.DependsOn G (A.image (fun q : Fin (T.S.n k) × OddPosition T k =>
      clusterSliceAt PT hPT q.2.1)) :=
    nominal_product_depends PT hPT hm x A (fun q : Fin (T.S.n k) × OddPosition T k => q.2)
  have hdis : Disjoint S (A.image fun q : Fin (T.S.n k) × OddPosition T k => clusterSliceAt PT hPT q.2.1) := by
    apply Finset.disjoint_left.mpr
    intro s hs hs'
    obtain ⟨q, hq, hqs⟩ := Finset.mem_image.mp hs'
    have hp := (Finset.mem_filter.mp hs).2
    rw [← hqs] at hp
    exact allowed_crossing_group_patch_ne PT hPT hm i M hM (Finset.mem_sdiff.mp hq).1 hp
  have hinj : Set.InjOn (fun q : Fin (T.S.n k) × OddPosition T k => clusterSliceAt PT hPT q.2.1) A := by
    intro q hq p hp hqp
    exact allowed_crossing_slices_injective PT hPT M hwidth
      (Finset.mem_sdiff.mp hq).1 (Finset.mem_sdiff.mp hp).1 hqp
  have hmeanG : (FinLaw.pi P).E G = 1 :=
    nominal_product_mean_one PT hPT hm x A (fun q : Fin (T.S.n k) × OddPosition T k => q.2) hinj (fun q hq => hd _)
  rw [raw_reference_E_eq_slices, raw_reference_E_eq_slices]
  change (FinLaw.pi P).E (fun z => F z * G z) = (FinLaw.pi P).E F
  rw [E_pi_mul_of_disjoint P F G S (A.image fun q : Fin (T.S.n k) × OddPosition T k => clusterSliceAt PT hPT q.2.1) hF hG hdis,
    hmeanG, mul_one]

theorem raw_reference_factorization {κ : CConsts} {T : Stage} {k : ℕ}
    (PT : ProfiledTiling κ T k) (hPT : PT.Valid)
    (hm : PT.tiling.mode = .highSmall ∨ PT.tiling.mode = .highLarge)
    (i : Fin PT.tiling.m) (x : Fin (T.S.N k)) (M : ClusterMask PT)
    (hM : ClusterMaskGeometry PT hPT i M)
    (hradius : (1 : ℝ) ≤ κ.ρ * (PT.tiling.P i).h)
    (hwidth : ∀ j, ((PT.tiling.P j).h : ℝ) + 2 ≤ (T.S.n k : ℝ) ^ (2 * κ.ι))
    (hd : ∀ j, 0 < deg (T.S.E k) PT.tiling.c (PT.π j).w x) :
    (clusterHistoryLaw PT hPT hm).E (clusterReferenceMean PT hPT hm i x M) =
      ∏ r ∈ clusterKeptRows M, (clusterRawReferenceLaw PT hPT hm).E
        (fun z => (PT.tiling.P i).M * clusterSigma PT hPT hm z.1 z.2 (M.positions r) x) := by
  rw [raw_reference_mean_eq, raw_kept_product_drop_crossings PT hPT hm i x M hM hwidth hd,
    raw_core_rows_factor PT hPT hm i x M hM hradius]
  apply Finset.prod_congr rfl
  intro r hr
  exact raw_core_row_mean_eq_sigma PT hPT hm i x (M.positions r) (fun b hb => hd _)

theorem eventual_nominal_degrees_pos (κ : CConsts) (hκ : κ.Admissible) (T : Stage) :
    ∀ᶠ k in atTop, ∀ PT : ProfiledTiling κ T k, ∀ hPT : PT.Valid,
      ∀ hm : PT.tiling.mode = .highSmall ∨ PT.tiling.mode = .highLarge,
      ∀ i x, x ∈ PT.envelope i → ∀ j, 0 < deg (T.S.E k) PT.tiling.c (PT.π j).w x := by
  have hwindow := Lane_q_s15_c2.clusterHighMode_degree_window hκ T
  let nR : ℕ → ℝ := fun k => T.S.n k
  have hn : Tendsto nR atTop atTop := tendsto_natCast_atTop_atTop.comp T.S.n_tendsto
  have hpow : Tendsto (fun k => nR k ^ (0.96 : ℝ)) atTop atTop :=
    (tendsto_rpow_atTop (by norm_num)).comp hn
  have heq k : bstar T k = (nR k ^ (0.96 : ℝ))⁻¹ := by
    dsimp [bstar, nR]
    rw [show (-1 + (0.04 : ℝ)) = -(0.96 : ℝ) by norm_num,
      Real.rpow_neg (Nat.cast_nonneg _)]
  have hzero : Tendsto (fun k => bstar T k) atTop (nhds 0) :=
    (tendsto_inv_atTop_zero.comp hpow).congr' (Filter.Eventually.of_forall fun k => (heq k).symm)
  filter_upwards [hwindow, hzero.eventually (Iio_mem_nhds (by norm_num : (0 : ℝ) < 1 / 18))]
    with k hw hb
  intro PT hPT hm i x hx j
  by_cases hji : j = i
  · subst j
    have hown := hPT.envelope_degree i x hx
    have herr : |deg (T.S.E k) PT.tiling.c (PT.π i).w x - 1 / 2| ≤
        10 * Real.rpow ((PT.tiling.P i).q : ℝ) κ.Cb / (T.S.n k : ℝ) := by
      rcases hm with hs | hl
      · simpa [OwnDegOK, hs] using hown
      · simpa [OwnDegOK, hl] using hown
    have hlow := (abs_le.mp (herr.trans (hw PT hPT hm i))).1
    linarith
  · have hlow := (abs_le.mp (hPT.envelope_other_degree i j hji x hx)).1
    linarith

end HypercubeRamsey.Lane_sol_s15_transfer
