import HypercubeRamsey.S18.Nodes_sol_split_d18l_sol_d18l_row
import HypercubeRamsey.S18.Nodes_sol_split_d18l_sol_d18l_row_source
import HypercubeRamsey.S18.Nodes_sol_split_d18l_sol_d18l_row_history
import HypercubeRamsey.S18.Nodes_sol_split_d18l_sol_d18l_row_pool
import HypercubeRamsey.S18.Nodes_sol_d18l_up_pool
import HypercubeRamsey.S18.Nodes_sol_split_d18l_sol_d18l_pal

namespace HypercubeRamsey.S18.Lane_sol_d18l_row

open Classical Filter
open S16 S16.Lane_sol_fix2_s16
open scoped BigOperators

variable {κ : CConsts} {T : Stage} {k : ℕ} {PT : ProfiledTiling κ T k}
  {G : LowGeom PT} {F : FreshCell G}

/-- The repaired raw certificate supplies the ordered-word invariant. -/
theorem raw_word_order (R : CellRawData G) : RawWordOrder R := R.word_order

private def OriginAt (D : ListGateContext κ T k PT) (v : Pos T k)
    (state : D.F.State (D.G.cellOf v))
    (i : Fin PT.tiling.m) (hi : i = D.G.patchOf v) : Prop :=
  ∃ (S : SliceSolver κ PT.tiling i PT.mesh)
    (e : EvenRole PT.tiling i) (W : ∀ r, S.Val r)
    (ys : InternalLabels PT.tiling i),
    PT.solver i = some S ∧ D.SolverRoleMatches v (cast (by rw [hi]) e) ∧
    0 < (S.recLaw PT.parameter).w W ∧
    (∀ (hle : (PT.tiling.P i).h ≤ T.S.n k) (j : Fin (PT.tiling.P i).h),
      ys j = D.F.label (D.G.cellOf v) state
        (flipPos v ⟨T.S.n k - (PT.tiling.P i).h + j.val, by omega⟩)) ∧
    D.F.prior (D.G.cellOf v) state v = S.σ e W ys

private theorem origin_transport (D : ListGateContext κ T k PT) (v : Pos T k)
    (state : D.F.State (D.G.cellOf v)) (i : Fin PT.tiling.m)
    (hi : i = D.G.patchOf v) (h : OriginAt D v state i hi) :
    OriginAt D v state (D.G.patchOf v) rfl := by
  subst i
  exact h

/-- Supported physical posteriors have the canonical solver word and the
actual labels at every ordered internal neighbour, including late dummies. -/
theorem physical_posterior_origin (hPT : PT.Valid) (hLow : PT.tiling.mode.isLow)
    (physical : PhysicalFreshCertificate G F)
    (v : Pos T k) (pool : F.Pool (G.cellOf v)) (state : F.State (G.cellOf v))
    (he : IsEvenRole v) (ht : F.typical (G.cellOf v) pool)
    (hs : (Lane_sol_s18_dl.physical_list_context hPT hLow physical).stateValid
      (G.cellOf v) pool state) (hc : PT.tiling.mode.isCluster) :
    let D := Lane_sol_s18_dl.physical_list_context hPT hLow physical
    ∃ (S : SliceSolver κ PT.tiling (G.patchOf v) PT.mesh)
      (e : EvenRole PT.tiling (G.patchOf v)) (W : ∀ r, S.Val r)
      (ys : InternalLabels PT.tiling (G.patchOf v)),
      PT.solver (G.patchOf v) = some S ∧ D.SolverRoleMatches v e ∧
      0 < (S.recLaw PT.parameter).w W ∧
      (∀ (hle : (PT.tiling.P (G.patchOf v)).h ≤ T.S.n k)
        (j : Fin (PT.tiling.P (G.patchOf v)).h),
        ys j = F.label (G.cellOf v) state
          (flipPos v ⟨T.S.n k - (PT.tiling.P (G.patchOf v)).h + j.val, by omega⟩)) ∧
      F.prior (G.cellOf v) state v = S.σ e W ys := by
  dsimp only
  obtain ⟨Wc, a, labels, hencode, hWc, ha, hl, hhist⟩ :=
    Lane_sol_d18l_fresh.fresh_supported_encoding physical (G.cellOf v) pool ht state
      (ne_of_gt hs.2)
  let R := physical.raw
  let C := G.cellOf v
  let p := (R.cellWords C).symm ⟨v, rfl⟩
  have hsite : (R.cellWords C p).1 = v :=
    congrArg Subtype.val ((R.cellWords C).apply_symm_apply ⟨v, rfl⟩)
  have heword : IsEvenRole p.2 := (R.word_parity hc C p.1 p.2).mp (by rwa [hsite])
  rcases physical.source_valid with hsource | hsource
  · obtain ⟨S, hS, records, groups, hLaw, hPass, hGroup, hQ, hTrim, hU, hPrior⟩ :=
      hsource.2.2 C
    let Wr := physical.construction.histories C Wc
    have hslice := Lane_sol_s16_prod1.pi_support
      (fun s => FinLaw.cond (R.sliceLaw C s) (R.slicePass C s) (R.slice_pos C s))
      Wr hhist p.1
    have hraw := (Lane_sol_s16_prod1.cond_support _ _ _ _ hslice).2
    rw [hLaw p.1] at hraw
    obtain ⟨W, hrecord, hW⟩ := Lane_q_s16_calib.finLaw_map_support _ _ _ hraw
    have hrec : records p.1 (Wr p.1) = W := by
      have h := congrArg (records p.1) hrecord
      simpa only [Equiv.apply_symm_apply] using h.symm
    let fallback : Fin (T.S.N k) := ⟨0, T.S.N_pos k⟩
    let e : EvenRole PT.tiling (G.cellPatch C) := ⟨p.2, heword⟩
    let ys := nbrLabels e.1 (R.wordLabel C labels p.1 fallback)
    have hprior : F.prior C state v = S.σ e W ys := by
      rw [← hencode]
      rw [physical.construction.prior_eq C pool Wc a labels v ht hWc ha hl rfl he]
      have h := hPrior Wr p.1 e labels fallback
      change R.rawPrior C Wr labels (R.cellWords C p).1 = _ at h
      rwa [hsite, hrec] at h
    have hrole := raw_word_order_solver_role R (raw_word_order R) hc
      (Lane_sol_s18_dl.physical_list_context hPT hLow physical) rfl v C p.1 e rfl hsite
    have hy (hle : (PT.tiling.P (G.cellPatch C)).h ≤ T.S.n k)
        (j : Fin (PT.tiling.P (G.cellPatch C)).h) :
        ys j = F.label C state (flipPos v (Lane_q_s16_prod1.cellAxis (G.cellPatch C) hle j)) := by
      have hflip := raw_word_order_flip R (raw_word_order R) hc C p.1 p.2 hle j
      rw [hsite] at hflip
      have ho : ¬ IsEvenRole (R.cellWords C (p.1, flipPos p.2 j)).1 := by
        rw [hflip]
        exact fun hn => ((Lane_sol_s16_prod1.flip_parity v _).mp hn) he
      change R.wordLabel C labels p.1 fallback (flipPos p.2 j) = _
      rw [CellRawData.wordLabel, dif_pos ho]
      have hlabel := physical.calibration.label_eq C pool Wc a labels
        ⟨(R.cellWords C (p.1, flipPos p.2 j)).1,
          (R.cellWords C (p.1, flipPos p.2 j)).2, ho⟩ ht hWc ha hl
      rw [hencode] at hlabel
      rw [← hlabel, hflip]
    change OriginAt (Lane_sol_s18_dl.physical_list_context hPT hLow physical)
      v state (G.patchOf v) rfl
    apply origin_transport _ v state (G.cellPatch C) (G.cellOf_patch v)
    exact ⟨S, e, W, ys, hS, hrole,
      lt_of_le_of_ne ((S.recLaw PT.parameter).nonneg W) hW.symm, hy, hprior⟩
  · exact (hsource.1 hc).elim


/-- A nontrivial binary late subspace has even cardinality, so the natural
half-class count in S16 is exactly the real half-class count used by S17. -/
theorem physical_late_count (physical : PhysicalFreshCertificate G F)
    (v : Pos T k) (he : IsEvenRole v) :
    (G.r : ℝ) / 2 ≤ (Finset.univ.filter fun j : Fin (T.S.n k) =>
      (G.classOf (flipPos v j)).isSome).card := by
  rcases physical with ⟨hκ, K16, Q, H, hG, hUniform, hScale, R, hR,
    Perm, hPerm, K, c0, Ds, stages, hTypicalEq, hGateEq, Cal, link,
    hF, hFailure, hPositive⟩
  subst G
  let S := H.data.syndrome
  have hr : 2 ≤ (S.r : ℝ) :=
    H.scale.class_scale.trans H.late_classes.subspace_size.1
  have hcard : S.r = 2 ^ Module.finrank (ZMod 2) S.Lsub := by
    rw [← H.late_classes.class_enum_card, Module.card_eq_pow_finrank, ZMod.card]
  have hdim : Module.finrank (ZMod 2) S.Lsub ≠ 0 := by
    intro h
    rw [h, pow_zero] at hcard
    rw [hcard] at hr
    norm_num at hr
  have hev : Even S.r := by
    rw [hcard]
    exact Nat.even_pow.mpr ⟨by decide, hdim⟩
  obtain ⟨m, hm⟩ := hev
  have hhalf := (H.late_classes.total_late_neighbour_bounds v he).1
  change S.r / 2 ≤ (Finset.univ.filter fun j : Fin (T.S.n k) =>
    (S.classOf (flipPos v j)).isSome).card at hhalf
  rw [hm] at hhalf
  have hdiv : (m + m) / 2 = m := by omega
  rw [hdiv] at hhalf
  change (S.r : ℝ) / 2 ≤ _
  rw [hm, Nat.cast_add]
  have hreal : (m : ℝ) ≤ (Finset.univ.filter fun j : Fin (T.S.n k) =>
    (S.classOf (flipPos v j)).isSome).card := by exact_mod_cast hhalf
  linarith

/-- The internal hit field is a direct projection of physical charged-state
validity, with no additional sampler assumption. -/
theorem physical_internal_hits (hPT : PT.Valid) (hLow : PT.tiling.mode.isLow)
    (physical : PhysicalFreshCertificate G F)
    (v : Pos T k) (P : F.Pool (G.cellOf v)) (s : F.State (G.cellOf v))
    (he : IsEvenRole v)
    (hs : (Lane_sol_s18_dl.physical_list_context hPT hLow physical).stateValid
      (G.cellOf v) P s) :
    ∀ j ∈ PT.tiling.Icoord (G.patchOf v), ∀ x,
      F.prior (G.cellOf v) s v x ≠ 0 →
      Hits (T.S.E k) PT.tiling.c x (F.label (G.cellOf v) s (flipPos v j)) := by
  intro j hj x hx
  exact ((hs.1.2 v rfl he).2 x hx).2 j (by simpa only [G.cellOf_patch] using hj)


private theorem flip_distance_le {n : ℕ} (v : CubePos n) (a : Fin n) :
    hammingDist v (flipPos v a) ≤ 1 := by
  have hsub : (Finset.univ.filter fun j => v j ≠ flipPos v a j) ⊆ {a} := by
    intro j hj
    by_contra hn
    have hne : j ≠ a := by simpa using hn
    exact (Finset.mem_filter.mp hj).2 (by simp [flipPos, hne])
  exact (Finset.card_le_card hsub).trans_eq (Finset.card_singleton _)

private theorem double_flip_distance_le {n : ℕ} (v : CubePos n) (a b : Fin n) :
    hammingDist (flipPos v a) (flipPos v b) ≤ 2 := by
  have hsub : (Finset.univ.filter fun j => flipPos v a j ≠ flipPos v b j) ⊆ {a, b} := by
    intro j hj
    by_contra hn
    have hne : j ≠ a ∧ j ≠ b := by simpa using hn
    exact (Finset.mem_filter.mp hj).2 (by simp [flipPos, hne.1, hne.2])
  exact (Finset.card_le_card hsub).trans (by simp; omega)

/-- An external flip remains external to its neighbour's patch. Prefix and
internal coordinates are disjoint uniformly over all patches. -/
theorem external_axis_at_neighbor (hPT : PT.Valid) (v : Pos T k)
    (a : Fin (T.S.n k)) (ha : a ∉ PT.tiling.Icoord (G.patchOf v)) :
    a ∉ PT.tiling.Icoord (G.patchOf (flipPos v a)) := by
  intro hw
  have htop : T.S.n k - (PT.tiling.P (G.patchOf (flipPos v a))).h ≤ a.val := by
    simpa [Tiling.Icoord, topCoordinates] using hw
  have hell : (PT.tiling.P (G.patchOf v)).ℓ ≤ a.val := by
    have hl := Finset.le_sup (f := fun i : Fin PT.tiling.m => (PT.tiling.P i).ℓ)
      (Finset.mem_univ (G.patchOf v))
    have hh := Finset.le_sup (f := fun i : Fin PT.tiling.m => (PT.tiling.P i).h)
      (Finset.mem_univ (G.patchOf (flipPos v a)))
    have hlen := hPT.tiling_valid.prefix_internal_length
    omega
  have hp := Lane_q_s17_pool.lowGeom_patch_flip_of_after_prefix G hPT v a hell
  exact ha (by simpa only [hp] using hw)

/-- Geometry projection, leaving only the two eventual polynomial slot
bounds as scalar inputs. All geometric data belong to the actual fresh cell. -/
theorem physical_geometry (hκ : κ.Admissible) (hPT : PT.Valid)
    (hLow : PT.tiling.mode.isLow) (physical : PhysicalFreshCertificate G F)
    (legacy : S18.L16QuantitativeValidity G F) (K17 : ℝ) (hK : 1 ≤ K17)
    (Q17 : LowModeQuantFacts hκ (PT := PT) K17)
    (hlog : 2 ≤ (Real.log (T.S.n k : ℝ)) ^ 3)
    (hslots : ∀ C, Real.rpow (T.S.n k : ℝ) ((κ.Ac : ℝ) - 1) ≤ G.nslot C ∧
      (G.nslot C : ℝ) ≤ Real.rpow (T.S.n k : ℝ) ((κ.Ac : ℝ) + 1)) :
    (Lane_sol_s18_dl.physical_list_context hPT hLow physical).S17GeometryValidity K17 := by
  have hlates := physical_late_count physical
  have hsep (v w : Pos T k) (hc : G.cellOf v = G.cellOf w)
      (hd : (hammingDist v w : ℝ) ≤ (Real.log (T.S.n k : ℝ)) ^ 3) :
      ∀ j, j ∉ PT.tiling.Icoord (G.patchOf v) → v j = w j := by
    intro j hj
    by_contra hne
    exact (not_lt_of_ge hd) (legacy.cell_spacing v w hc ⟨j, hj, hne⟩)
  have hstar (v : Pos T k) :
      (∀ w ∈ (Lane_sol_s18_dl.physical_list_context hPT hLow physical).externalEarly v,
        G.cellOf w ≠ G.cellOf v) ∧
      (∀ w ∈ (Lane_sol_s18_dl.physical_list_context hPT hLow physical).externalEarly v,
        ∀ z ∈ (Lane_sol_s18_dl.physical_list_context hPT hLow physical).externalEarly v,
        G.cellOf w = G.cellOf z → w = z) := by
    constructor
    · intro w hw heq
      obtain ⟨_, a, ha, rfl⟩ := Finset.mem_filter.mp hw |>.2
      have hd : (hammingDist v (flipPos v a) : ℝ) ≤ (Real.log (T.S.n k : ℝ)) ^ 3 := by
        have hh : (hammingDist v (flipPos v a) : ℝ) ≤ 1 := by exact_mod_cast flip_distance_le v a
        linarith
      have heqbit := hsep v (flipPos v a) heq.symm hd a ha
      cases hv : v a <;> simp [flipPos, hv] at heqbit
    · intro w hw z hz hcell
      obtain ⟨_, a, ha, rfl⟩ := Finset.mem_filter.mp hw |>.2
      obtain ⟨_, b, hb, rfl⟩ := Finset.mem_filter.mp hz |>.2
      by_cases hab : a = b
      · rw [hab]
      · have hd : (hammingDist (flipPos v a) (flipPos v b) : ℝ) ≤
            (Real.log (T.S.n k : ℝ)) ^ 3 := by
          exact (by exact_mod_cast double_flip_distance_le v a b).trans hlog
        have heqbit := hsep (flipPos v a) (flipPos v b) hcell hd a
          (external_axis_at_neighbor hPT v a ha)
        cases hv : v a <;> simp [flipPos, hab, hv] at heqbit
  rcases physical with ⟨hκ', K16, Q, H, hG, hUniform, hScale, R, hR,
    Perm, hPerm, K, c0, Ds, stages, hTypicalEq, hGateEq, Cal, link,
    hF, hFailure, hPositive⟩
  subst G
  refine {
    ids_injective := legacy.ids_distinct
    class_scale := H.late_classes.subspace_size
    late_count := ?_
    internal_late_count := ?_
    cell_nonempty := ?_
    slice_closed := ?_
    slice_separated := hsep
    star_distinct := fun v _ => hstar v
    cell_size := legacy.cell_size
    slots_eq := legacy.slot_eq
    slots_lower := fun C => (hslots C).1
    slots_upper := fun C => (hslots C).2
    slot_factor_eq := fun _ => rfl
    height_bound := Q17.height_bound
    prefix_bound := ?_
    mass_bound := ?_
    degree_drift := Q17.degree_bound
    conflict_bound := Q17.conflict_bound }
  · intro v he
    exact hlates v he
  · intro v he
    exact Lane_sol_d18l_pal.internal_late_le_one H.geom v (by
      intro a b ha hb hab
      exact legacy.internal_cosets (H.geom.patchOf v) a b ha hb hab)
  · intro C
    obtain ⟨v, hv⟩ := H.cell_partition.cells_nonempty C
    exact ⟨v, (Finset.mem_filter.mp hv).2⟩
  · intro v w hp hout
    exact legacy.whole_slices v w hp.symm hout
  · intro i
    exact (Q17.prefix_bound i).trans (by
      simpa only [one_mul] using mul_le_mul_of_nonneg_right hK (Real.sqrt_nonneg _))
  · intro i
    exact (Q17.patch_mass_bound i).trans (by
      simpa only [one_mul] using mul_le_mul_of_nonneg_right hK (Real.sqrt_nonneg _))


private theorem cast_bin_val (i j : Fin PT.tiling.m) (h : i = j)
    (B : Bin PT.tiling i) : (cast (by rw [h]) B : Bin PT.tiling j).1 = B.1 := by
  subst j
  rfl

/-- Permission labels contain whole bins, because the patch bins partition
its labels. This also handles the even-role empty permission set. -/
theorem whole_permitted_bin (Cal : FreshLabelCalibration F) (C : G.Cell)
    (P : F.Pool C) (b : Pos T k) (B : Bin PT.tiling (G.cellPatch C))
    (y : Fin (T.S.N k)) (hy : y ∈ B.1) (hp : y ∈ Cal.permittedLabels C P b) :
    ∀ z ∈ B.1, z ∈ Cal.permittedLabels C P b := by
  unfold FreshLabelCalibration.permittedLabels at hp ⊢
  split_ifs at hp ⊢ with hb
  · obtain ⟨B', hB', hy'⟩ := Finset.mem_biUnion.mp hp
    have heq : B' = B := Subtype.ext
      ((PT.tiling.P (G.cellPatch C)).bins.eq_of_mem_parts B'.2 B.2 hy' hy)
    subst B'
    intro z hz
    exact Finset.mem_biUnion.mpr ⟨B, hB', hz⟩
  · simp at hp

noncomputable def physical_permission_core (physical : PhysicalFreshCertificate G F)
    (b : Pos T k) : Finset (Fin (T.S.N k)) :=
  physical.calibration.permittedLabels (G.cellOf b)
    (fun _ => Classical.choice (physical.diagnostics.diagnostic (G.cellOf b)).bins_nonempty) b

noncomputable def physical_permitted_bin (physical : PhysicalFreshCertificate G F)
    (b : Pos T k) (B : Bin PT.tiling (G.patchOf b)) : Prop :=
  ∀ y ∈ B.1, y ∈ physical_permission_core physical b

private theorem permission_core_eq (physical : PhysicalFreshCertificate G F)
    (C : G.Cell) (P : F.Pool C) (b : Pos T k) (hb : G.cellOf b = C) :
    physical.calibration.permittedLabels C P b = physical_permission_core physical b := by
  subst C
  rfl

/-- The S17 permitted-label table is precisely the permitted whole bins
actually occurring in the selected pool. -/
theorem physical_permission_present (hPT : PT.Valid) (hLow : PT.tiling.mode.isLow)
    (physical : PhysicalFreshCertificate G F) (C : G.Cell) (P : F.Pool C)
    (b : Pos T k) (hb : G.cellOf b = C) (y : Fin (T.S.N k)) :
    y ∈ (Lane_sol_s18_dl.physical_list_context hPT hLow physical).permittedLabels C P b ↔
      ∃ j : Fin (G.nslot C), y ∈ (P j).1 ∧
        physical_permitted_bin physical b (cast (by rw [← hb, G.cellOf_patch]) (P j)) := by
  rw [Lane_sol_s18_dl.physical_list_context_permission]
  constructor
  · rintro ⟨hp, j, hy⟩
    refine ⟨j, hy, ?_⟩
    intro z hz
    have hval := cast_bin_val (PT := PT) (G.cellPatch C) (G.patchOf b)
      (by rw [← hb, G.cellOf_patch]) (P j)
    rw [hval] at hz
    rw [← permission_core_eq physical C P b hb]
    exact whole_permitted_bin physical.calibration C P b (P j) y hy hp z hz
  · rintro ⟨j, hy, hp⟩
    refine ⟨?_, j, hy⟩
    rw [permission_core_eq physical C P b hb]
    apply hp y
    rw [cast_bin_val]
    exact hy


/-- The raw permission test is the S17 base-law permission test. External
neighbours may lie in another patch; the prefix/internal disjointness lemma
keeps the incidence external at that neighbour as required by S16. -/
theorem physical_permission_test (hPT : PT.Valid) (hLow : PT.tiling.mode.isLow)
    (physical : PhysicalFreshCertificate G F) (v : Pos T k) (he : IsEvenRole v)
    (b : Pos T k)
    (hb : b ∈ (Lane_sol_s18_dl.physical_list_context hPT hLow physical).externalEarly v)
    (B : Bin PT.tiling (G.patchOf b)) (hB : physical_permitted_bin physical b B)
    (y : Fin (T.S.N k)) (hy : y ∈ B.1) :
    (physical_base_source hPT hLow physical v).law.pr (fun ω =>
      (physical_base_source hPT hLow physical v).readout ω ≠ 0 ∧
      |(∑ x, (physical_base_source hPT hLow physical v).readout ω x *
        hit (T.S.E k) PT.tiling.c x y) - 1 / 2| > 2 * bstar T k) ≤
      Real.exp (-κ.cperm * T.S.n k) := by
  obtain ⟨hclass, a, ha, hba⟩ := Finset.mem_filter.mp hb |>.2
  subst b
  let b := flipPos v a
  have ho : ¬ IsEvenRole b := by
    intro h
    exact ((Lane_sol_s16_prod1.flip_parity v a).mp h) he
  have hout : a ∉ PT.tiling.Icoord (G.patchOf b) := external_axis_at_neighbor hPT v a ha
  let C := G.cellOf b
  let r : OddCellRole G C := ⟨b, rfl, ho⟩
  have hcore := hB y hy
  unfold physical_permission_core FreshLabelCalibration.permittedLabels at hcore
  rw [dif_pos ⟨rfl, ho⟩] at hcore
  obtain ⟨B', hB', hy'⟩ := Finset.mem_biUnion.mp hcore
  have hBval : B'.1 = B.1 := by
    have hpart : B.1 ∈ (PT.tiling.P (G.cellPatch C)).bins.parts := by
      simpa only [C, G.cellOf_patch] using B.2
    exact (PT.tiling.P (G.cellPatch C)).bins.eq_of_mem_parts B'.2 hpart hy' hy
  have hperm : B' ∈ (physical.permissions.table C).permitted (physical.raw.groupOf C r) := by
    rw [← physical.construction.group_eq C r]
    rw [← physical.construction.permission_eq C (physical.calibration.groupOf C r)]
    exact hB'
  have htest := (physical.permissions.table C).permitted_iff _ _ |>.mp hperm
  have hbad := htest (r, a) (by rw [physical.permissions.group_eq]; rfl) y
    (by rw [physical.permissions.labels_eq]; exact hy')
  rw [physical.permissions.bad_eq] at hbad
  have hyY : y ∈ (PT.tiling.P (G.cellPatch C)).Y :=
    (PT.tiling.P (G.cellPatch C)).bins.subset B'.2 hy'
  have hflip : flipPos b a = v := by
    funext j
    by_cases hj : j = a
    · subst j
      simp [b, flipPos]
    · simp [b, flipPos, hj]
  rw [if_pos ⟨hyY, by simpa only [C, G.cellOf_patch] using hout, hclass⟩, hflip] at hbad
  exact hbad

/-- S16's exact slot formula and subpolynomial bin size supply the two
polynomial slot bounds in S17. -/
theorem physical_slot_bounds (hκ : κ.Admissible) (hPT : PT.Valid)
    (physical : PhysicalFreshCertificate G F) (legacy : S18.L16QuantitativeValidity G F)
    (hKcell : 1 ≤ κ.Kcell) (hlog : 1 ≤ Real.log (T.S.n k : ℝ))
    (hnK : κ.Kcell + 1 ≤ (T.S.n k : ℝ)) :
    ∀ C, Real.rpow (T.S.n k : ℝ) ((κ.Ac : ℝ) - 1) ≤ G.nslot C ∧
      (G.nslot C : ℝ) ≤ Real.rpow (T.S.n k : ℝ) ((κ.Ac : ℝ) + 1) := by
  intro C
  let n : ℝ := T.S.n k
  let d : ℝ := (PT.tiling.P (G.cellPatch C)).d
  let A := Real.rpow n (κ.Ac : ℝ)
  have hnpos : 0 < n := by
    dsimp [n]
    exact_mod_cast (lt_of_lt_of_le (by norm_num : 0 < 2) physical.quantitative.n_large)
  have hn : 1 ≤ n := by linarith
  have hA : 1 ≤ A := Real.one_le_rpow hn (Nat.cast_nonneg _)
  obtain ⟨y, hy⟩ := (hPT.tiling_valid.patch_nonempty (G.cellPatch C)).2
  obtain ⟨B, hB, hyB⟩ := (PT.tiling.P (G.cellPatch C)).bins.exists_mem hy
  have hdNat : 0 < (PT.tiling.P (G.cellPatch C)).d :=
    (Finset.card_pos.mpr ⟨y, hyB⟩).trans_eq (hPT.tiling_valid.bins_card _ B hB)
  have hd : 1 ≤ d := by exact_mod_cast hdNat
  have hdpos : 0 < d := by linarith
  have hbin := physical.quantitative.bin_count_bound (G.cellPatch C)
  have hsqrt : Real.sqrt (Real.log n) ≤ Real.log n := by
    have hsq := Real.sq_sqrt (show 0 ≤ Real.log n by linarith)
    have hp := Real.sqrt_nonneg (Real.log n)
    nlinarith
  have hdle : d ≤ n := by
    apply hbin.trans
    exact (Real.exp_le_exp.mpr hsqrt).trans_eq (Real.exp_log hnpos)
  have hslot : A ≤ (G.nslot C : ℝ) * n := by
    have h := legacy.slot_lower C
    have hS : 0 ≤ (G.nslot C : ℝ) := Nat.cast_nonneg _
    have hprod := mul_le_mul_of_nonneg_left hdle hS
    have hgrow : A ≤ κ.Kcell * A := by
      simpa only [one_mul] using mul_le_mul_of_nonneg_right hKcell (le_trans (by norm_num) hA)
    simpa only [Real.rpow_natCast] using hgrow.trans (h.trans hprod)
  constructor
  · rw [Real.rpow_sub_one hnpos.ne']
    exact (div_le_iff₀ hnpos).mpr hslot
  · have hceil : (G.nslot C : ℝ) ≤ κ.Kcell * A / d + 1 := by
      rw [legacy.slot_eq C]
      exact (Nat.ceil_lt_add_one (show 0 ≤ κ.Kcell * A / d by positivity)).le
    have hquot : κ.Kcell * A / d ≤ κ.Kcell * A := by
      exact div_le_self (by positivity) hd
    have hupper : (G.nslot C : ℝ) ≤ A * n := by
      have hprod := mul_le_mul_of_nonneg_right hnK (show 0 ≤ A by positivity)
      nlinarith
    simpa only [Real.rpow_add_one hnpos.ne'] using hupper

/-- L16.7 supplies the comparison for every nonnegative test of the raw
prior vector; the fixed coefficient precedes the eventual index. -/
theorem physical_raw_base_comparison (hκ : κ.Admissible) (T : Stage)
    (K17 : ℝ) (hK : 100 * κ.Kcell * (κ.Kp : ℝ) ≤ K17) :
    ∀ᶠ k in atTop, ∀ (PT : ProfiledTiling κ T k) (G : LowGeom PT)
      (F : FreshCell G) (physical : PhysicalFreshCertificate G F)
      (hpools : (permPools G).Nonempty) (v : Pos T k), IsEvenRole v →
      ∀ Φ : (Fin (T.S.N k) → ℝ) → ℝ,
      (∀ σ, 0 ≤ Φ σ) → Φ 0 = 0 →
      (iidPoolLaw G hpools).E (fun pools =>
        if F.typical (G.cellOf v) (pools (G.cellOf v)) then
          (F.fresh (G.cellOf v) (pools (G.cellOf v))).E
            (fun state => Φ (F.prior (G.cellOf v) state v)) else 0) ≤
        K17 * (physical.raw.baseExperiment (G.cellOf v) v).expect Φ := by
  obtain ⟨n₀, hpipeline⟩ := fresh_prior_pipeline_exists hκ
  filter_upwards [T.S.n_tendsto.eventually_ge_atTop n₀] with k hn
  intro PT G F physical hpools v he Φ hΦ hΦ0
  rcases physical with ⟨hκ', K16, Q, H, hG, hUniform, hScale, R, hR,
    Perm, hPerm, K, c0, Ds, stages, hTypicalEq, hGateEq, Cal, link,
    hF, hFailure, hPositive⟩
  subst G
  let C := H.geom.cellOf v
  let hBins (C : H.geom.Cell) :
      (Finset.univ : Finset (Bin PT.tiling (H.geom.cellPatch C))).Nonempty :=
    ⟨Classical.choice (Ds.diagnostic C).bins_nonempty, Finset.mem_univ _⟩
  obtain ⟨P, hSource, hBaseEq⟩ := hpipeline Q H hScale R Perm K Ds stages F Cal
    hR hn hPerm hTypicalEq hGateEq link C v rfl he
  have hCompare := fresh_internal_prior_comparison hκ Q H hBins C v rfl he
    P hSource Φ hΦ hΦ0
  rw [hBaseEq Φ] at hCompare
  have hIntegral : (iidPoolLaw H.geom hpools).E (fun pools =>
      if F.typical C (pools C) then (F.fresh C (pools C)).E
        (fun state => Φ (F.prior C state v)) else 0) =
      freshPriorTest F hBins C v rfl he Φ := by
    let testPool (pool : F.Pool C) := if F.typical C pool then
      (F.fresh C pool).E (fun state => Φ (F.prior C state v)) else 0
    have hMap := Lane_q_s16_comp2.map_expect (iidPoolLaw H.geom hpools)
      (fun pools => pools C) testPool
    change (iidPoolLaw H.geom hpools).E (fun pools => testPool (pools C)) = _
    rw [← hMap, Lane_sol_d18l_fresh.iid_marginal_eq hpools hBins C]
    rfl
  rw [hIntegral]
  apply hCompare.trans
  apply mul_le_mul_of_nonneg_right hK
  unfold PriorExperiment.expect FinLaw.E
  exact Finset.sum_nonneg (fun ω _ =>
    mul_nonneg ((R.baseExperiment C v).law.nonneg ω) (hΦ _))


/-- Polynomially many queried slots are negligible compared with every
patch's bin supply. The host exponent is fixed before the index. -/
theorem physical_pool_bin_budget (hκ : κ.Admissible) (hPT : PT.Valid)
    (physical : PhysicalFreshCertificate G F) (hlog : 1 ≤ Real.log (T.S.n k : ℝ))
    (hN : Real.rpow (T.S.n k : ℝ) (2 * (κ.Ac + 4 : ℕ) + 8 : ℕ) ≤ T.S.N k) :
    ∀ i, (((T.S.n k) ^ (κ.Ac + 4) + 1 : ℕ) : ℝ) ^ 2 *
      (1 + Real.rpow (T.S.n k : ℝ) (-3 : ℝ)) /
        Real.rpow (T.S.n k : ℝ) (-3 : ℝ) ≤
      (Fintype.card (Bin PT.tiling i) : ℝ) := by
  intro i
  let n : ℝ := T.S.n k
  let m := κ.Ac + 4
  have hn2 : 2 ≤ n := by exact_mod_cast physical.quantitative.n_large
  have hnpos : 0 < n := by linarith
  have hA : 1 ≤ n ^ m := one_le_pow₀ (by linarith)
  have hsqrt : Real.sqrt (Real.log n) ≤ Real.log n := by
    have hsq := Real.sq_sqrt (show 0 ≤ Real.log n by linarith)
    have hp := Real.sqrt_nonneg (Real.log n)
    nlinarith
  have he : Real.exp (Real.sqrt (Real.log n)) ≤ n :=
    (Real.exp_le_exp.mpr hsqrt).trans_eq (Real.exp_log hnpos)
  have hd : ((PT.tiling.P i).d : ℝ) ≤ n :=
    (physical.quantitative.bin_count_bound i).trans he
  have hM : 0 < ((PT.tiling.P i).M : ℝ) := by
    rw [← (PT.tiling.P i).cardX]
    exact_mod_cast Finset.card_pos.mpr (hPT.tiling_valid.patch_nonempty i).1
  have hNp : 0 < (T.S.N k : ℝ) := by exact_mod_cast T.S.N_pos k
  have hratio : (T.S.N k : ℝ) / (PT.tiling.P i).M ≤ n := by
    calc
      _ = Real.exp (Real.log ((T.S.N k : ℝ) / (PT.tiling.P i).M)) :=
        (Real.exp_log (div_pos hNp hM)).symm
      _ ≤ Real.exp (Real.sqrt (Real.log n)) :=
        Real.exp_le_exp.mpr (physical.quantitative.patch_mass_bound i)
      _ ≤ n := he
  have hNm : (T.S.N k : ℝ) ≤ (PT.tiling.P i).M * n := by
    have h := (div_le_iff₀ hM).mp hratio
    simpa only [mul_comm] using h
  have hcard : (Fintype.card (Bin PT.tiling i) : ℝ) * (PT.tiling.P i).d =
      (PT.tiling.P i).M := by
    exact_mod_cast Lane_q_s16_geom.bin_card_mul_bin_size PT hPT i
  have hNB : (T.S.N k : ℝ) ≤ (Fintype.card (Bin PT.tiling i) : ℝ) * n ^ 2 := by
    rw [← hcard] at hNm
    have hp := mul_le_mul_of_nonneg_left hd (Nat.cast_nonneg (Fintype.card (Bin PT.tiling i)))
    have hp' := mul_le_mul_of_nonneg_right hp hnpos.le
    simpa only [pow_two, mul_assoc] using hNm.trans hp'
  have hHost : n ^ (2 * m + 8) ≤ (T.S.N k : ℝ) := by
    simpa only [Real.rpow_natCast] using hN
  have hbig : n ^ (2 * m + 3) * n ^ 3 ≤ (Fintype.card (Bin PT.tiling i) : ℝ) := by
    have hh := hHost.trans hNB
    rw [show 2 * m + 8 = (2 * m + 3) + 3 + 2 by omega,
      pow_add, pow_add] at hh
    exact (mul_le_mul_right (show 0 < n ^ 2 by positivity)).mp hh
  have hn3 : 8 ≤ n ^ 3 := by
    calc
      8 = (2 : ℝ) ^ 3 := by norm_num
      _ ≤ n ^ 3 := pow_le_pow_left₀ (by norm_num) hn2 _
  have hbin : 8 * n ^ (2 * m + 3) ≤ (Fintype.card (Bin PT.tiling i) : ℝ) := by
    have h := mul_le_mul_of_nonneg_left hn3 (show 0 ≤ n ^ (2 * m + 3) by positivity)
    exact (by simpa only [mul_comm] using h).trans hbig
  have hε : Real.rpow n (-3 : ℝ) = (n ^ 3)⁻¹ := by
    rw [Real.rpow_neg hnpos.le, Real.rpow_natCast n 3]
  have hεone : Real.rpow n (-3 : ℝ) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by linarith) (by norm_num)
  have hεpos : 0 < Real.rpow n (-3 : ℝ) := Real.rpow_pos_of_pos hnpos _
  have hq : (n ^ m + 1) ^ 2 ≤ 4 * (n ^ m) ^ 2 := by nlinarith
  have htarget : (n ^ m + 1) ^ 2 * (1 + Real.rpow n (-3 : ℝ)) /
      Real.rpow n (-3 : ℝ) ≤ 8 * n ^ (2 * m + 3) := by
    calc
      _ ≤ (4 * (n ^ m) ^ 2) * 2 / Real.rpow n (-3 : ℝ) := by
        apply div_le_div_of_nonneg_right _ hεpos.le
        exact mul_le_mul hq (by linarith) (by positivity) (by positivity)
      _ = 8 * n ^ (2 * m + 3) := by
        rw [hε, div_inv_eq_mul, pow_add, show 2 * m = m * 2 by omega, pow_mul]
        ring
  exact (by simpa only [Nat.cast_add, Nat.cast_one, Nat.cast_pow] using htarget).trans hbin

/-- All sampler fields come from the one linked physical construction. -/
noncomputable def physical_sampler (hPT : PT.Valid) (hLow : PT.tiling.mode.isLow)
    (physical : PhysicalFreshCertificate G F) (K17 : ℝ)
    (hn : (100 : ℝ) ≤ T.S.n k)
    (hh : ∀ i, ((PT.tiling.P i).h : ℝ) ≤ T.S.n k)
    (hN : Real.log (T.S.N k : ℝ) ≤ 2 * T.S.n k)
    (hbudget : Real.log 3 + 8 * (T.S.n k : ℝ) ^ 2 ≤ Real.rpow (T.S.n k : ℝ) 2.01)
    (hCompare : ∀ (hpools : (permPools G).Nonempty) v, IsEvenRole v →
      ∀ Φ : (Fin (T.S.N k) → ℝ) → ℝ, (∀ σ, 0 ≤ Φ σ) → Φ 0 = 0 →
      (iidPoolLaw G hpools).E (fun pools =>
        if F.typical (G.cellOf v) (pools (G.cellOf v)) then
          (F.fresh (G.cellOf v) (pools (G.cellOf v))).E
            (fun state => Φ (F.prior (G.cellOf v) state v)) else 0) ≤
        K17 * (physical.raw.baseExperiment (G.cellOf v) v).expect Φ) :
    (Lane_sol_s18_dl.physical_list_context hPT hLow physical).S17SamplerData K17 := by
  refine {
    base := physical_base_source hPT hLow physical
    permittedBin := physical_permitted_bin physical
    permission_present := physical_permission_present hPT hLow physical
    permission_test := physical_permission_test hPT hLow physical
    localHistories := physical_local_histories hPT hLow physical
    priorHistories := physical_prior_histories hPT physical
    history_count := ?_
    prior_count := ?_
    history_cover := physical_local_history_cover hPT hLow physical
    prior_cover := physical_prior_history_cover hPT hLow physical
    posterior_origin := physical_posterior_origin hPT hLow physical
    internal_hits := ?_
    base_comparison := hCompare }
  · intro v
    exact ((physical_history_log_bounds hPT hLow physical v hn (hh _) hN).2).trans hbudget
  · intro v
    exact ((physical_history_log_bounds hPT hLow physical v hn (hh _) hN).1).trans hbudget
  · intro v P state he ht hs
    exact physical_internal_hits hPT hLow physical v P state he hs

/-- Quantitative validity has one remaining independent adapter input: the
S17 comparison on a queried scope spanning arbitrary patches. -/
noncomputable def physical_quantitative_adapter (hκ : κ.Admissible) (hPT : PT.Valid)
    (hLow : PT.tiling.mode.isLow) (physical : PhysicalFreshCertificate G F)
    (legacy : S18.L16QuantitativeValidity G F) (K17 : ℝ) (hK : 1 ≤ K17)
    (Q17 : LowModeQuantFacts hκ (PT := PT) K17)
    (hlog : 2 ≤ (Real.log (T.S.n k : ℝ)) ^ 3)
    (hslots : ∀ C, Real.rpow (T.S.n k : ℝ) ((κ.Ac : ℝ) - 1) ≤ G.nslot C ∧
      (G.nslot C : ℝ) ≤ Real.rpow (T.S.n k : ℝ) ((κ.Ac : ℝ) + 1))
    (sampler : (Lane_sol_s18_dl.physical_list_context hPT hLow physical).S17SamplerData K17)
    (hsmall : ((T.S.n k : ℝ) + 1) * Real.exp (-Real.rpow (T.S.n k : ℝ) (1 / 2)) ≤
      Real.rpow (T.S.n k : ℝ) (-((κ.R : ℝ) * initialResamplingRounds T k)))
    (hCompare : ∀ (μ : FinLaw ((Lane_sol_s18_dl.physical_list_context hPT hLow physical).PoolAssignment)),
      (Lane_sol_s18_dl.physical_list_context hPT hLow physical).IsPermOrPinnedPoolLaw legacy.pools_nonempty μ →
      ∃ ν : FinLaw ((Lane_sol_s18_dl.physical_list_context hPT hLow physical).PoolAssignment),
      (ν = iidPoolLaw G legacy.pools_nonempty ∨
        ∃ (pin : (Lane_sol_s18_dl.physical_list_context hPT hLow physical).PoolPin)
          (hpin : 0 < ∑ pools ∈ (Lane_sol_s18_dl.physical_list_context hPT hLow physical).poolPinSet pin,
            (iidPoolLaw G legacy.pools_nonempty).w pools),
          ν = FinLaw.cond (iidPoolLaw G legacy.pools_nonempty)
            ((Lane_sol_s18_dl.physical_list_context hPT hLow physical).poolPinSet pin) hpin) ∧
        ∀ (slots : Finset (Σ C : G.Cell, Fin (G.nslot C))) (f : (∀ C, F.Pool C) → ℝ),
        slots.card ≤ (T.S.n k) ^ (κ.Ac + 4) → (∀ pools, 0 ≤ f pools) →
        (∀ p q, (∀ a ∈ slots, p a.1 a.2 = q a.1 a.2) → f p = f q) →
        μ.E f ≤ (1 + Real.rpow (T.S.n k : ℝ) (-3 : ℝ)) * ν.E f) :
    (Lane_sol_s18_dl.physical_list_context hPT hLow physical).L16QuantitativeValidity K17 := by
  exact Lane_sol_d18l_up.physical_quantitative_of_remaining hPT hLow physical
    legacy.pools_nonempty K17 hsmall
    ⟨physical_geometry hκ hPT hLow physical legacy K17 hK Q17 hlog hslots,
      sampler, hCompare⟩

/-- Scalar requirements on the fixed S17 scale; they are independent of
all indices, tilings and fresh constructions. -/
def AdapterScale (κ : CConsts) (K : ℝ) : Prop :=
  1 ≤ K ∧ 2 ≤ K ∧ κ.Kbd ≤ K ∧ 4 * κ.KB ≤ K ∧
    100 * κ.Kcell * (κ.Kp : ℝ) ≤ K

private theorem admissible_KB_pos (hκ : κ.Admissible) : 0 < κ.KB := by
  have hP : 1 ≤ κ.P := by have h := hκ.P_big.2; omega
  have hR : 1 ≤ κ.R := by rw [hκ.R_eq]; exact Nat.one_le_pow 2 κ.P hP
  have hRreal : 1 ≤ (κ.R : ℝ) := by exact_mod_cast hR
  nlinarith [hκ.KB_big]

private theorem admissible_Kcell_one (hκ : κ.Admissible) : 1 ≤ κ.Kcell := by
  have hθ : 0 < κ.θstar := hκ.bucket.2.2.2.2
  have hKp : (40 : ℝ) ≤ κ.Kp := by exact_mod_cast hκ.bucket.1
  have hprod := hκ.bucket.2.2.1
  rw [hκ.clock.2.1] at hprod
  have hm := mul_le_mul_of_nonneg_right hKp hθ.le
  have hθone : κ.θstar ≤ 1 := by nlinarith
  have h100 : (100 : ℝ) ≤ 100 / κ.θstar := (le_div_iff₀ hθ).mpr (by nlinarith)
  linarith [h100.trans hκ.Kcell_big]

theorem fixed_adapter_scale (hκ : κ.Admissible) :
    AdapterScale κ (max 1 (κ.Kbd + 4 * κ.KB + 10 + 100 * κ.Kcell * (κ.Kp : ℝ))) := by
  have hKB := admissible_KB_pos hκ
  have hKcell := admissible_Kcell_one hκ
  have hKbd := hκ.bounded.2.2.2.1
  have hKp : 0 ≤ (κ.Kp : ℝ) := Nat.cast_nonneg _
  have hc : 0 ≤ 100 * κ.Kcell * (κ.Kp : ℝ) := by positivity
  have hmax := le_max_right 1 (κ.Kbd + 4 * κ.KB + 10 + 100 * κ.Kcell * (κ.Kp : ℝ))
  refine ⟨le_max_left _ _, ?_, ?_, ?_, ?_⟩ <;> linarith

/-- Shared D18.L adapter for the row and both upstream-bad nodes. It uses
the actual physical context, at a scale fixed before the eventual index. -/
theorem eventually_physical_remaining_inputs (hκ : κ.Admissible) (T : Stage)
    (K17 : ℝ) (hScale : AdapterScale κ K17) :
    ∀ᶠ k in atTop, ∀ (PT : ProfiledTiling κ T k) (hPT : PT.Valid)
      (G : LowGeom PT) (F : FreshCell G) (legacy : S18.L16QuantitativeValidity G F)
      (hLow : PT.tiling.mode.isLow) (physical : PhysicalFreshCertificate G F),
      Nonempty (Lane_sol_d18l_up.RemainingInputs
        (Lane_sol_s18_dl.physical_list_context hPT hLow physical) K17 legacy.pools_nonempty) := by
  have hKB := admissible_KB_pos hκ
  have hKcell := admissible_Kcell_one hκ
  have hEv := Lane_q_s18_bridge.eventually_low_input_scale_events hκ T K17 hKB hScale.1
  have hn : Tendsto (fun k => (T.S.n k : ℝ)) atTop atTop :=
    tendsto_natCast_atTop_atTop.comp T.S.n_tendsto
  have hlog : Tendsto (fun k => Real.log (T.S.n k : ℝ)) atTop atTop :=
    Real.tendsto_log_atTop.comp hn
  have hHost := Lane_sol_d18l_pal.polynomial_host_cutoff T
    ((2 * (κ.Ac + 4) + 8 : ℕ) : ℝ) (Nat.cast_nonneg _)
  filter_upwards [hEv, hHost, eventually_history_budget T,
    physical_raw_base_comparison hκ T K17 hScale.2.2.2.2,
    hn.eventually_ge_atTop (κ.Kcell + 1), hlog.eventually_ge_atTop 2]
    with k hEv hHost hHistory hBase hnK hlog2
  intro PT hPT G F legacy hLow physical
  let Q17 := Lane_q_s18_bridge.low_mode_quant_facts_of_events hκ hPT hLow hEv
    (lt_of_lt_of_le (by norm_num) hScale.1) hScale.2.1 hScale.2.2.1 hScale.2.2.2.1
  have hlog1 : 1 ≤ Real.log (T.S.n k : ℝ) := by linarith
  have hlog3 : 2 ≤ (Real.log (T.S.n k : ℝ)) ^ 3 := by
    have hpow := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 2) hlog2 3
    norm_num at hpow
    linarith
  have hslots := physical_slot_bounds hκ hPT physical legacy hKcell hlog1 hnK
  have hh : ∀ i, ((PT.tiling.P i).h : ℝ) ≤ T.S.n k := by
    intro i
    have h := Finset.le_sup (f := fun j : Fin PT.tiling.m => (PT.tiling.P j).h) (Finset.mem_univ i)
    have hlen := hPT.tiling_valid.prefix_internal_length
    exact_mod_cast (show (PT.tiling.P i).h ≤ T.S.n k by omega)
  let sampler := physical_sampler hPT hLow physical K17 hHost.1 hh hHost.2.2.2.2
    hHistory (hBase PT G F physical)
  have hBin := physical_pool_bin_budget hκ hPT physical hlog1 hHost.2.2.2.1
  have hε : 0 < Real.rpow (T.S.n k : ℝ) (-3 : ℝ) :=
    Real.rpow_pos_of_pos (by exact_mod_cast
      (lt_of_lt_of_le (by norm_num : 0 < 2) physical.quantitative.n_large)) _
  exact ⟨{
    geometry := physical_geometry hκ hPT hLow physical legacy K17 hScale.1 Q17 hlog3 hslots
    sampler := sampler
    pool_iid_comparison := PC.pool_iid_comparison_of_budget
      (Lane_sol_s18_dl.physical_list_context hPT hLow physical) legacy.pools_nonempty
      ((T.S.n k) ^ (κ.Ac + 4)) _ hε hBin }⟩

/-- The complete S17 quantitative certificate at the same fixed scale. -/
theorem eventually_physical_quantitative_validity (hκ : κ.Admissible) (T : Stage)
    (K17 : ℝ) (hScale : AdapterScale κ K17) :
    ∀ᶠ k in atTop, ∀ (PT : ProfiledTiling κ T k) (hPT : PT.Valid)
      (G : LowGeom PT) (F : FreshCell G) (legacy : S18.L16QuantitativeValidity G F)
      (hLow : PT.tiling.mode.isLow) (physical : PhysicalFreshCertificate G F),
      Nonempty ((Lane_sol_s18_dl.physical_list_context hPT hLow physical).L16QuantitativeValidity K17) := by
  filter_upwards [eventually_physical_remaining_inputs hκ T K17 hScale,
    Lane_sol_d18l_up.eventually_local_typical_tail T (κ.R : ℝ) (Nat.cast_nonneg κ.R)]
    with k hRest hsmall
  intro PT hPT G F legacy hLow physical
  exact ⟨Lane_sol_d18l_up.physical_quantitative_of_remaining hPT hLow physical
    legacy.pools_nonempty K17 hsmall (Classical.choice (hRest PT hPT G F legacy hLow physical))⟩

end HypercubeRamsey.S18.Lane_sol_d18l_row
