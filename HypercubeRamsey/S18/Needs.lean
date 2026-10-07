import HypercubeRamsey.PartC.LateProcess
import HypercubeRamsey.Framework.Embedding
import HypercubeRamsey.S15.DirectNodes
import HypercubeRamsey.S15.ClusterNodes
import HypercubeRamsey.S18.ProfileBridge
import HypercubeRamsey.S18.FreshBridge

/-!
# Section 18 interfaces supplied by earlier sections

The profile and geometry/fresh contracts assemble the producing sections
through explicit construction inputs. Remaining construction leaves are named
in ProducerInputs and ProfileBridge; positivity alone is never a certificate.
-/

namespace HypercubeRamsey
namespace S18

open Filter

/-- SHARED: L16.1 quantitative facts and the linked physical fresh sampler
consumed by the resampling and late-process nodes. -/
structure L16QuantitativeValidity {κ : CConsts} {T : Stage} {k : ℕ}
    {PT : ProfiledTiling κ T k} (G : LowGeom PT) (F : FreshCell G) : Prop where
  pools_nonempty : (permPools G).Nonempty
  slot_lower : ∀ C, κ.Kcell * (T.S.n k : ℝ) ^ κ.Ac ≤
    (G.nslot C : ℝ) * (PT.tiling.P (G.cellPatch C)).d
  /-- S16.CellPartitionFacts.slot_count (16:98–115). Nonempty permutation
  support alone allows a cell to read a macroscopic fraction of its bins. -/
  slot_eq : ∀ C, G.nslot C =
    ⌈κ.Kcell * Real.rpow (T.S.n k : ℝ) κ.Ac /
      (PT.tiling.P (G.cellPatch C)).d⌉₊
  /-- The actual Section 16 construction, including calibration, source
  identities, typicality estimates and internal probability priors. -/
  physical : Nonempty (PhysicalFreshCertificate G F)
  fresh_spec : ∃ validState permittedLabels, FreshCell.Spec F validState permittedLabels
  r_pos : 0 < G.r
  r_lower : κ.A0 * Real.log (T.S.n k) ≤ (G.r : ℝ)
  r_upper : (G.r : ℝ) * Real.log 2 ≤ 2 * κ.A0 * Real.log (T.S.n k)
  gain_upper : ∀ i, PT.tiling.gain i ≤ κ.KB * Real.log (T.S.n k)
  ids_distinct : Function.Injective G.ids
  internal_cosets : ∀ i a a', a ∈ PT.tiling.Icoord i → a' ∈ PT.tiling.Icoord i →
    G.ids a - G.ids a' ∈ G.Lsub → a = a'
  remaining_count : ∀ v : Pos T k, IsEvenRole v → ∀ j : Fin G.r,
    (G.r - j.val) / 2 ≤ (Finset.univ.filter fun a : Fin (T.S.n k) =>
      ∃ s : Fin G.r, j.val ≤ s.val ∧ G.classOf (flipPos v a) = some s).card
  whole_slices : ∀ b b', G.patchOf b = G.patchOf b' →
    (∀ a, a ∉ PT.tiling.Icoord (G.patchOf b) → b a = b' a) → G.cellOf b = G.cellOf b'
  cell_spacing : ∀ b b', G.cellOf b = G.cellOf b' →
    (∃ a, a ∉ PT.tiling.Icoord (G.patchOf b) ∧ b a ≠ b' a) →
      Real.log (T.S.n k) ^ 3 < (hammingDist b b' : ℝ)
  cell_size : ∀ C, (Finset.univ.filter fun b => G.cellOf b = C).card ≤ (T.S.n k) ^ κ.Ac
  one_per_class : ∀ v : Pos T k, ∀ j : Fin G.r, ∀ a a',
    G.classOf (flipPos v a) = some j → G.classOf (flipPos v a') = some j → a = a'

/-- C12.K followed by the fixed estimate/threshold selection needed by the
Section 14 and 16 constructors. Widths are transported by explicit equalities. -/
theorem exists_late_constants (T : Stage) (η0 : ℝ) (hη0 : 0 < η0)
    (hDeep : ∀ ε : ℝ, 0 < ε → ∃ x α : ℝ, 0 < x ∧ 0 < α ∧ DeepDisc T x α ε) :
    ∃ κ : CConsts, κ.Admissible ∧ κ.η0 = η0 ∧ LateThresholds κ ∧
      ProducerConstants κ ∧ DeepDisc T κ.xs κ.α 0.04 ∧ DeepDisc T κ.xι κ.αι (κ.ι / 2) := by
  obtain ⟨κ₀, hκ₀, hη, hd, hdι⟩ := exists_admissible T η0 hη0 hDeep
  obtain ⟨κ, hκ, hη', hxs, hα, hxι, hαι, hι, ht, hp⟩ := producer_constants_widening κ₀ hκ₀
  exact ⟨κ, hκ, hη'.trans hη, ht, hp, by simpa [hxs, hα] using hd,
    by simpa [hxι, hαι, hι] using hdι⟩

/-- P13.2 cleaning removes less than a fixed small fraction at each
active corner (Section 13:273–278); bare ProfiledTiling.Valid omits size. -/
def ProfileCornerMass {κ : CConsts} {T : Stage} {k : ℕ}
    (PT : ProfiledTiling κ T k) : Prop :=
  ∀ i v, v ∈ PT.activeVertices → ((PT.tiling.P i).M : ℝ) ≤ 2 * (PT.mesh.corner v i).card

private theorem even_of_odd_flip {n : ℕ} (v : CubePos n) (a : Fin n)
    (h : ¬ IsEvenRole (flipPos v a)) : IsEvenRole v := by
  let A := Finset.univ.filter fun j : Fin n => v j = true
  let B := Finset.univ.filter fun j : Fin n => flipPos v a j = true
  cases hv : v a with
  | false =>
    have hset : B = insert a A := by
      ext j
      by_cases hj : j = a
      · subst j; simp [A, B, flipPos, hv]
      · dsimp [A, B]
        simp only [Finset.mem_filter, Finset.mem_univ, Finset.mem_insert, true_and, hj, false_or]
        simp only [flipPos, Function.update_of_ne hj]
    have ha : a ∉ A := by simp [A, hv]
    have hcard : B.card = A.card + 1 := by rw [hset, Finset.card_insert_of_notMem ha]
    change ¬ Even B.card at h
    rw [hcard, Nat.even_add_one] at h
    exact not_not.mp h
  | true =>
    have hset : A = insert a B := by
      ext j
      by_cases hj : j = a
      · subst j; simp [A, B, flipPos, hv]
      · dsimp [A, B]
        simp only [Finset.mem_filter, Finset.mem_univ, Finset.mem_insert, true_and, hj, false_or]
        simp only [flipPos, Function.update_of_ne hj]
    have ha : a ∉ B := by simp [B, flipPos, hv]
    have hcard : A.card = B.card + 1 := by rw [hset, Finset.card_insert_of_notMem ha]
    change Even A.card
    change ¬ Even B.card at h
    rw [hcard, Nat.even_add_one]
    exact h

/-- Projection from the exact syndrome/cell certificate used by the fresh
construction, retaining its physical sampler certificate. -/
theorem l16_validity_of_certificate {κ : CConsts} (hκ : κ.Admissible)
    {T : Stage} {k : ℕ} {PT : ProfiledTiling κ T k} {K16 : ℝ}
    (Q : S16.LowModeQuantFacts hκ (PT := PT) K16)
    (H : S16.LowGeometryCertificate hκ Q)
    (hGain : ∀ i, PT.tiling.gain i ≤ κ.KB * Real.log (T.S.n k)) (F : FreshCell H.geom)
    (hPhysical : Nonempty (PhysicalFreshCertificate H.geom F)) :
    L16QuantitativeValidity H.geom F := by
  classical
  have hr : κ.A0 * Real.log (T.S.n k : ℝ) ≤ (H.geom.r : ℝ) := H.late_classes.subspace_size.1
  refine {
    pools_nonempty := H.perm_pool_nonempty
    slot_lower := ?_
    slot_eq := H.cell_partition.slot_count
    physical := hPhysical
    fresh_spec := by
      obtain ⟨physical⟩ := hPhysical
      exact ⟨_, _, physical.fresh_spec⟩
    r_pos := ?_
    r_lower := hr
    r_upper := ?_
    gain_upper := hGain
    ids_distinct := H.late_classes.ids_injective
    internal_cosets := ?_
    remaining_count := ?_
    whole_slices := ?_
    cell_spacing := ?_
    cell_size := ?_
    one_per_class := ?_ }
  · intro C
    let i := H.geom.cellPatch C
    obtain ⟨y, hy⟩ := (Q.profiled_valid.tiling_valid.patch_nonempty i).2
    obtain ⟨B, hB, hyB⟩ := (PT.tiling.P i).bins.exists_mem hy
    have hd : 0 < ((PT.tiling.P i).d : ℝ) := by
      exact_mod_cast (Finset.card_pos.mpr ⟨y, hyB⟩).trans_eq
        (Q.profiled_valid.tiling_valid.bins_card i B hB)
    have hceil := Nat.le_ceil (κ.Kcell * Real.rpow (T.S.n k : ℝ) κ.Ac / (PT.tiling.P i).d)
    have hslots : H.geom.nslot C = ⌈κ.Kcell * Real.rpow (T.S.n k : ℝ) κ.Ac /
        (PT.tiling.P i).d⌉₊ := H.cell_partition.slot_count C
    rw [← hslots] at hceil
    have hb := (div_le_iff₀ hd).mp hceil
    simpa only [Real.rpow_eq_pow, Real.rpow_natCast] using hb
  · have h2 : 2 ≤ (H.geom.r : ℝ) := H.scale.class_scale.trans hr
    exact_mod_cast (show (0 : ℝ) < H.geom.r by linarith)
  · have hlog : Real.log 2 ≤ 1 := by
      have hh := Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 2)
      norm_num at hh
      exact hh
    calc
      (H.geom.r : ℝ) * Real.log 2 ≤ H.geom.r := by
        simpa only [mul_one] using mul_le_mul_of_nonneg_left hlog (Nat.cast_nonneg H.geom.r)
      _ ≤ 2 * κ.A0 * Real.log (T.S.n k) := H.late_classes.subspace_size.2.le
  · intro i a a' ha ha' hdiff
    by_contra hne
    apply H.late_classes.internal_cosets_distinct a ?_ a' ?_ hne hdiff
    · exact Finset.mem_biUnion.mpr ⟨i, Finset.mem_univ _, ha⟩
    · exact Finset.mem_biUnion.mpr ⟨i, Finset.mem_univ _, ha'⟩
  · intro v hv j
    change Fin H.data.syndrome.r at j
    change (H.data.syndrome.r - j.val) / 2 ≤
      (Finset.univ.filter fun a : Fin (T.S.n k) =>
        ∃ s : Fin H.data.syndrome.r, j.val ≤ s.val ∧
          H.data.syndrome.classOf (flipPos v a) = some s).card
    have hb := (H.late_classes.suffix_neighbour_bounds v hv
      (H.data.syndrome.r - j.val) (Nat.sub_le _ _)).1
    simpa only [S16.SyndromeData.suffixNeighbours, S16.SyndromeData.suffix,
      Finset.mem_filter, Finset.mem_univ, true_and, Nat.sub_sub_self j.isLt.le] using hb
  · intro b b' hpatch hout
    apply Eq.symm
    apply H.cell_partition.whole_slices (H.geom.cellOf b) b rfl b'
    change ∀ a, a ∉ PT.tiling.Icoord (H.geom.cellPatch (H.geom.cellOf b)) → b a = b' a
    rw [H.geom.cellOf_patch b]
    exact hout
  · intro b b' hcell hdiff
    have hh := H.cell_partition.slice_separation (H.geom.cellOf b) b b' rfl hcell.symm
    have hn : ¬ S16.CellData.sameSlice (H.geom.cellPatch (H.geom.cellOf b)) b b' := by
      intro hs
      obtain ⟨a, ha, hne⟩ := hdiff
      exact hne (hs a (by simpa only [H.geom.cellOf_patch b] using ha))
    -- `hammingDist` here may be `HypercubeRamsey.hammingDist` (definitionally Mathlib's): close up to defeq
    have h2 := hh hn
    simp only [Real.rpow_eq_pow, Real.rpow_ofNat] at h2
    exact h2
  · intro C
    change (S16.CellData.positions H.data.cells C).card ≤ T.S.n k ^ κ.Ac
    simpa only [S16.CellData.positions, Real.rpow_eq_pow, Real.rpow_natCast, ← Nat.cast_pow, Nat.floor_natCast]
      using H.cell_partition.cell_size C
  · intro v j a a' ha ha'
    have hv : IsEvenRole v := by
      have hodd : ¬ IsEvenRole (flipPos v a) := by
        dsimp [LowGeom.classOf] at ha
        split_ifs at ha with htest
        exact htest.1
      exact even_of_odd_flip v a hodd
    have hb := H.late_classes.one_neighbour_per_class v hv j
    apply Finset.card_le_one.mp hb a ?_ a' ?_
    · exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, ha⟩
    · exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, ha'⟩

/-- L16.0 → L16.1 → the linked Section 16 fresh construction. The fixed
calibration room and constructed solver's uniform labels are explicit inputs. -/
theorem l16_quantitative_validity {κ : CConsts} (hκ : κ.Admissible)
    (hConstants : ProducerConstants κ) (T : Stage)
    (hInit : InitDisc T κ.η0)
    (hDeep : ∀ ε : ℝ, 0 < ε → ∃ x α : ℝ, 0 < x ∧ 0 < α ∧ DeepDisc T x α ε)
    (hDisc : DeepDisc T κ.xs κ.α 0.04) :
    ∀ᶠ k in atTop, ∀ PT : ProfiledTiling κ T k, PT.Valid → PT.tiling.mode.isLow →
      ProfileCornerMass PT → S16.Lane_sol_fix2_s16.SolverLabelsUniform PT →
      ∃ G : LowGeom PT, ∃ F : FreshCell G, L16QuantitativeValidity G F := by
  obtain ⟨K16, hquant⟩ := low_mode_quantitative_inputs hκ T
  obtain ⟨ng, Cg, _hCg, hg⟩ := S16.late_classes_and_cell_inputs hκ
  obtain ⟨nf, hf⟩ := fresh_cell_from_exports hκ
  have hlarge := T.S.eventually_large Cg (max ng nf)
  filter_upwards [hquant, hlarge, hDisc] with k hquant hlarge hAt
  intro PT hPT hlow _hCorners hUniform
  obtain ⟨Q, hGain⟩ := hquant PT hPT hlow
  obtain ⟨H⟩ := hg Q (by omega) hlarge.2.1
  have hCal := cell_calibration_of_constants hκ hConstants.calibration hPT hlow
  obtain ⟨F, hPhysical⟩ :=
    hf hDisc Q H hUniform hCal (by omega) hAt
  exact ⟨H.geom, F, l16_validity_of_certificate hκ Q H hGain F hPhysical⟩

/-- Oriented C14.F construction with corner mass and the producer's uniform
in-bin law certificate retained for the low-mode cell construction. -/
theorem profiled_tiling_exists {κ : CConsts} (hκ : κ.Admissible)
    (hConstants : ProducerConstants κ) (T : Stage)
    (hInit : InitDisc T κ.η0)
    (hDeep : ∀ ε : ℝ, 0 < ε → ∃ x α : ℝ, 0 < x ∧ 0 < α ∧ DeepDisc T x α ε)
    (hDisc : DeepDisc T κ.xs κ.α 0.04)
    (hDiscι : DeepDisc T κ.xι κ.αι (κ.ι / 2))
    (hClu : ∀ (ζ δ : ℚ), 0 < ζ → 0 < δ → (δ : ℝ) < min κ.η0 (min (ζ : ℝ) 1) / 2000 →
      ∀ (c : Colour) (o : Bool), ∀ᶠ k in atTop,
        ¬ ClusterWitnessAt (T.orient o) k c ζ δ) :
    ∀ᶠ k in atTop, ∃ o : Bool, ∃ PT : ProfiledTiling κ (T.orient o) k,
      PT.Valid ∧ ProfileCornerMass PT ∧ S16.Lane_sol_fix2_s16.SolverLabelsUniform PT := by
  obtain ⟨hconst⟩ := hConstants.height
  filter_upwards [producer_profiled_tiling_exists hκ hconst T hInit hDisc hDiscι hClu]
    with k hk
  obtain ⟨o, PT, hPT, hUniform⟩ := hk
  refine ⟨o, PT, hPT, ?_, hUniform⟩
  intro i v hv
  have hmass := (hPT.corner_clean i v hv).card_lower
  linarith

/-- F-swap, moving a monochromatic cube copy across a transposed relation.
Discharged by the framework export `copy_transpose E c h`, as below. -/
theorem cube_copy_of_transpose {N n : ℕ} (E : Fin N → Fin N → Prop) (c : Colour)
    (h : Nonempty ((OAI.HypercubeRamsey.cube n).Copy
      (OAI.HypercubeRamsey.crossGraph (Hits (transposeRel E) c)))) :
    Nonempty ((OAI.HypercubeRamsey.cube n).Copy
      (OAI.HypercubeRamsey.crossGraph (Hits E c))) := by
  exact copy_transpose E c h

/-- L15.1 high-direct cube conclusion. Discharged by
`S15.high_direct κ hκ T hDisc` on main; the output is identical. The producer
uses only this selected budget, not the existential deep regime. -/
theorem high_direct_cube {κ : CConsts} (hκ : κ.Admissible) (T : Stage)
    (hDisc : DeepDisc T κ.xs κ.α 0.04) :
    ∀ᶠ k in atTop, ∀ PT : ProfiledTiling κ T k, PT.Valid →
      PT.tiling.mode = .highDirect → CubeIn T k PT.tiling.c :=
  S15.high_direct κ hκ T hDisc

/-- C15.F high-cluster cube conclusion. Discharged by
`S15.high_cluster_exclusion κ hκ T hDisc` on main; the output is identical.
The producer uses only this selected budget. -/
theorem high_cluster_cube {κ : CConsts} (hκ : κ.Admissible) (T : Stage)
    (hDisc : DeepDisc T κ.xs κ.α 0.04) :
    ∀ᶠ k in atTop, ∀ PT : ProfiledTiling κ T k, PT.Valid →
      (PT.tiling.mode = .highSmall ∨ PT.tiling.mode = .highLarge) →
        CubeIn T k PT.tiling.c :=
  S15.high_cluster_exclusion κ hκ T hDisc

end S18
end HypercubeRamsey
