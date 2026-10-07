import HypercubeRamsey.S18.Lists
import HypercubeRamsey.S17.Needs

namespace HypercubeRamsey.S18.Lane_sol_s18_dl

open Classical
open S16 S16.Lane_sol_fix2_s16
open scoped BigOperators

variable {κ : CConsts} {T : Stage} {k : ℕ} {PT : ProfiledTiling κ T k}
  {G : LowGeom PT} {F : FreshCell G}

private theorem product_law_support {I : Type*} [Fintype I] [DecidableEq I]
    {Ω : I → Type*} [∀ i, Fintype (Ω i)] (P : ∀ i, FinLaw (Ω i))
    (x : ∀ i, Ω i) (hx : (FinLaw.pi P).w x ≠ 0) (i : I) :
    (P i).w (x i) ≠ 0 :=
  Finset.prod_ne_zero_iff.mp hx i (Finset.mem_univ i)

theorem product_fresh_valid (physical : PhysicalFreshCertificate G F)
    (pools : ∀ C, F.Pool C) (s : Config F)
    (ht : ∀ C, F.typical C (pools C))
    (hs : 0 < (FinLaw.pi fun C => F.fresh C (pools C)).w s) :
    ∀ C, InternallyValid F physical.calibration C (pools C) (s C) := by
  intro C
  have hC : (F.fresh C (pools C)).w (s C) ≠ 0 :=
    product_law_support (fun C => F.fresh C (pools C)) s (ne_of_gt hs) C
  exact physical.fresh_spec.fresh_valid C (pools C) (s C) (ht C)
    (lt_of_le_of_ne ((F.fresh C (pools C)).nonneg (s C)) hC.symm)

theorem internal_probability_and_hits (physical : PhysicalFreshCertificate G F)
    (pools : ∀ C, F.Pool C) (s : Config F)
    (hv : ∀ C, InternallyValid F physical.calibration C (pools C) (s C))
    (v : Pos T k) (heven : IsEvenRole v) :
    (∀ y, 0 ≤ F.prior (G.cellOf v) (s (G.cellOf v)) v y) ∧
    (∑ y, F.prior (G.cellOf v) (s (G.cellOf v)) v y) = 1 ∧
    (∀ y, F.prior (G.cellOf v) (s (G.cellOf v)) v y ≠ 0 →
      y ∈ PT.envelope (G.patchOf v) ∧
      ∀ j ∈ PT.tiling.Icoord (G.patchOf v),
        Hits (T.S.E k) PT.tiling.c y
          (F.label (G.cellOf v) (s (G.cellOf v)) (flipPos v j))) := by
  have h := (hv (G.cellOf v)).2 v rfl heven
  refine ⟨physical.fresh_spec.prior_nonneg _ _ v, h.1, ?_⟩
  simpa only [G.cellOf_patch v] using h.2

theorem odd_label_in_patch (physical : PhysicalFreshCertificate G F)
    (pools : ∀ C, F.Pool C) (s : Config F)
    (hv : ∀ C, InternallyValid F physical.calibration C (pools C) (s C))
    (b : Pos T k) (hodd : ¬ IsEvenRole b) :
    F.label (G.cellOf b) (s (G.cellOf b)) b ∈ (PT.tiling.P (G.patchOf b)).Y := by
  obtain ⟨slot, hslot⟩ := ((hv (G.cellOf b)).1 b rfl hodd).2
  have hy := (PT.tiling.P (G.cellPatch (G.cellOf b))).bins.subset
    (pools (G.cellOf b) slot).2 hslot
  simpa only [G.cellOf_patch b] using hy

theorem odd_labels_injective (hPT : PT.Valid)
    (physical : PhysicalFreshCertificate G F)
    (pools : ∀ C, F.Pool C) (s : Config F) (hp : pools ∈ permPools G)
    (hv : ∀ C, InternallyValid F physical.calibration C (pools C) (s C)) :
    Function.Injective (fun b : {v : Pos T k // ¬ IsEvenRole v} =>
      F.label (G.cellOf b.1) (s (G.cellOf b.1)) b.1) := by
  intro b b' heq
  change F.label (G.cellOf b.1) (s (G.cellOf b.1)) b.1 =
    F.label (G.cellOf b'.1) (s (G.cellOf b'.1)) b'.1 at heq
  have hpatch : G.patchOf b.1 = G.patchOf b'.1 := by
    by_contra hne
    have hd := hPT.tiling_valid.patch_Y_disjoint _ _ hne
    exact Finset.disjoint_left.mp hd
      (odd_label_in_patch physical pools s hv b.1 b.2)
      (by rw [heq]; exact odd_label_in_patch physical pools s hv b'.1 b'.2)
  have hcp : G.cellPatch (G.cellOf b.1) = G.cellPatch (G.cellOf b'.1) := by
    simpa only [G.cellOf_patch] using hpatch
  obtain ⟨slot, hslot⟩ := ((hv (G.cellOf b.1)).1 b.1 rfl b.2).2
  obtain ⟨slot', hslot'⟩ := ((hv (G.cellOf b'.1)).1 b'.1 rfl b'.2).2
  have hpart' : (pools (G.cellOf b'.1) slot').1 ∈
      (PT.tiling.P (G.cellPatch (G.cellOf b.1))).bins.parts := by
    rw [hcp]
    exact (pools (G.cellOf b'.1) slot').2
  have hbins : (pools (G.cellOf b.1) slot).1 =
      (pools (G.cellOf b'.1) slot').1 :=
    (PT.tiling.P (G.cellPatch (G.cellOf b.1))).bins.eq_of_mem_parts
      (pools (G.cellOf b.1) slot).2 hpart' hslot (by rw [heq]; exact hslot')
  have hpool := (Finset.mem_filter.mp hp).2
  have hcell : G.cellOf b.1 = G.cellOf b'.1 :=
    (hpool (G.cellOf b.1) (G.cellOf b'.1) slot slot' hcp hbins).1
  apply Subtype.ext
  by_contra hne
  have hneq := physical.fresh_spec.labels_injective (G.cellOf b.1)
    (s (G.cellOf b.1)) b.1 b'.1 rfl hcell.symm b.2 b'.2 hne
  apply hneq
  rw [← hcell] at heq
  exact heq

theorem runRounds_preserves_cell_validity (LE : ListEvent F)
    (valid : ∀ C, F.State C → Prop) (rounds : ℕ) (order : Pos T k → ℕ)
    (events : Finset (Pos T k)) (pools : ∀ C, F.Pool C)
    (tapes : ∀ C, ℕ → TapeEntry F C)
    (htape : ∀ C j, valid C (tapes C j (pools C))) :
    ∀ C, valid C ((LE.runRounds rounds order events pools tapes).1 C) := by
  induction rounds with
  | zero => exact fun C => htape C 0
  | succ rounds ih =>
      intro C
      change valid C (if _ then _ else _)
      split_ifs
      · exact htape C _
      · exact ih C

theorem initial_state_internally_valid (physical : PhysicalFreshCertificate G F)
    (E : LateEncoding F) (x : E.InitInput) (hx : 0 < E.permLaw.w x)
    (ht : ∀ C, F.typical C (x.1 C)) :
    ∀ C, InternallyValid F physical.calibration C (x.1 C)
      (E.initialState x C) := by
  have hx' : E.poolLaw.w x.1 * (tapeLaw F E.Ts).w x.2 ≠ 0 := ne_of_gt hx
  have hTape := (mul_ne_zero_iff.mp hx').2
  have hEntry : ∀ C j P, 0 < (F.fresh C P).w (x.2 C j P) := by
    intro C j P
    have hC := product_law_support _ x.2 hTape C
    have hj := product_law_support _ (x.2 C) hC j
    have hP := product_law_support _ (x.2 C j) hj P
    exact lt_of_le_of_ne ((F.fresh C P).nonneg (x.2 C j P)) hP.symm
  apply runRounds_preserves_cell_validity E.events
    (fun C s => InternallyValid F physical.calibration C (x.1 C) s)
    E.Ts E.order Finset.univ x.1 x.2.extend
  intro C j
  exact physical.fresh_spec.fresh_valid C (x.1 C) _ (ht C)
    (hEntry C _ (x.1 C))

theorem initial_odd_labels_injective (hPT : PT.Valid)
    (physical : PhysicalFreshCertificate G F) (E : LateEncoding F)
    (x : E.InitInput) (hx : 0 < E.permLaw.w x)
    (hp : x.1 ∈ permPools G) (ht : ∀ C, F.typical C (x.1 C)) :
    Function.Injective (fun b : {v : Pos T k // ¬ IsEvenRole v} =>
      F.label (G.cellOf b.1) (E.initialState x (G.cellOf b.1)) b.1) :=
  odd_labels_injective hPT physical x.1 (E.initialState x) hp
    (initial_state_internally_valid physical E x hx ht)

theorem initial_odd_label_support (physical : PhysicalFreshCertificate G F)
    (E : LateEncoding F) (x : E.InitInput) (hx : 0 < E.permLaw.w x)
    (ht : ∀ C, F.typical C (x.1 C)) (b : Pos T k) (hodd : ¬ IsEvenRole b) :
    F.label (G.cellOf b) (E.initialState x (G.cellOf b)) b ∈
      (PT.tiling.P (G.patchOf b)).Y :=
  odd_label_in_patch physical x.1 (E.initialState x)
    (initial_state_internally_valid physical E x hx ht) b hodd

/-- Restrict the S17 validity predicate to charged states, and include the
actual pool in the permitted-label table. -/
noncomputable def physical_list_context (hPT : PT.Valid)
    (hLow : PT.tiling.mode.isLow) (physical : PhysicalFreshCertificate G F) :
    ListGateContext κ T k PT := by
  let valid C P s := InternallyValid F physical.calibration C P s ∧
    0 < (F.fresh C P).w s
  let permitted C P b := (physical.calibration.permittedLabels C P b).filter
    (fun y => poolContainsLabel P y)
  refine {
    tiling_valid := hPT
    mode_low := hLow
    G := G
    F := F
    stateValid := valid
    permittedLabels := permitted
    slotFactor := fun b => (Fintype.card (Bin PT.tiling (G.patchOf b)) : ℝ) /
      (G.nslot (G.cellOf b) : ℝ)
    fresh_spec := {
      fresh_valid := ?_
      fresh_atypical := physical.fresh_spec.fresh_atypical
      label_permitted := ?_
      labels_injective := physical.fresh_spec.labels_injective
      prior_nonneg := physical.fresh_spec.prior_nonneg
      prior_subprob := physical.fresh_spec.prior_subprob } }
  · intro C P s ht hs
    exact ⟨physical.fresh_spec.fresh_valid C P s ht hs, hs⟩
  · intro C P s b hs hcell hodd
    exact Finset.mem_filter.mpr ((hs.1.1 b hcell hodd))

theorem physical_list_context_charged (hPT : PT.Valid)
    (hLow : PT.tiling.mode.isLow) (physical : PhysicalFreshCertificate G F)
    (C : G.Cell) (P : F.Pool C) (s : F.State C)
    (hs : (physical_list_context hPT hLow physical).stateValid C P s) :
    0 < (F.fresh C P).w s := hs.2

theorem physical_list_context_permission (hPT : PT.Valid)
    (hLow : PT.tiling.mode.isLow) (physical : PhysicalFreshCertificate G F)
    (C : G.Cell) (P : F.Pool C) (b : Pos T k) (y : Fin (T.S.N k)) :
    y ∈ (physical_list_context hPT hLow physical).permittedLabels C P b ↔
      y ∈ physical.calibration.permittedLabels C P b ∧ poolContainsLabel P y := by
  exact Finset.mem_filter

/-- The legacy S17 adapter needs the stronger cleaning bound at every corner.
The current S18 ProfileCornerMass premise alone supplies only M/2. -/
theorem legacy_quantitative_requires_strong_corner_mass
    (D : ListGateContext κ T k PT) (K : ℝ)
    (h : D.L16QuantitativeValidity K) :
    ∀ i a, a ∈ PT.activeVertices →
      (1 - κ.a) * (PT.tiling.P i).M ≤ (PT.mesh.corner a i).card :=
  h.corner_size

theorem legacy_quantitative_unavailable_at_small_corner
    (D : ListGateContext κ T k PT) (K : ℝ) (i : Fin PT.tiling.m)
    (a : PT.mesh.V) (ha : a ∈ PT.activeVertices)
    (hsmall : ((PT.mesh.corner a i).card : ℝ) <
      (1 - κ.a) * (PT.tiling.P i).M) :
    ¬ Nonempty (D.L16QuantitativeValidity K) := by
  rintro ⟨h⟩
  exact (not_lt_of_ge (h.corner_size i a ha)) hsmall

end HypercubeRamsey.S18.Lane_sol_s18_dl
