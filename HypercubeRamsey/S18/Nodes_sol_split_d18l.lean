import HypercubeRamsey.S18.Nodes_q_s18_dl
import HypercubeRamsey.S18.Nodes_sol_s18_dl
import HypercubeRamsey.S18.Nodes_sol_s18_dl_base
import HypercubeRamsey.S17.Nodes
import HypercubeRamsey.S18.Nodes_sol_split_d18l_sol_d18l_cal_query

/-! Component and input-estimate nodes for D18.L. The two given Spec fields
(corner mass and thresholds) are passed directly by the final assembly.
All other obligations refer to the concrete construction below. -/

namespace HypercubeRamsey.S18.Lane_sol_split_d18l
open Classical Filter
open scoped BigOperators

variable {κ : CConsts} {T : Stage} {k : ℕ} {PT : ProfiledTiling κ T k}

/-- The selected discrepancy inputs, fixed before the stage index.
TeX 18:11–20,43–49; 17:123–131. -/
def Sources (κ : CConsts) (T : Stage) : Prop :=
  InitDisc T κ.η0 ∧
  (∀ ε : ℝ, 0 < ε → ∃ x α : ℝ, 0 < x ∧ 0 < α ∧ DeepDisc T x α ε) ∧
  DeepDisc T κ.xs κ.α 0.04 ∧ DeepDisc T κ.xι κ.αι (κ.ι / 2)

/-- Host palette tables with the actual binary-code and label-colouring
readouts. No late estimate or Spec field is stored here.
TeX 17:233–300; 18:53–57,930–936. -/
structure PaletteData (G : LowGeom PT) where
  hle : ∀ i, (PT.tiling.P i).h ≤ T.S.n k
  code : ∀ i, S17PaletteCode i (hle i)
  colours : ∀ i, S17PaletteAssignment (code i)
  chi : Fin PT.tiling.m → ℕ
  colourEquiv : ∀ i, (Fin (code i).dimension → ZMod 2) ≃ Fin (chi i)
  chi_eq : ∀ i, chi i = s17Chi (code i)
  chi_pos : ∀ i, 0 < chi i
  colourOf : ∀ v : Pos T k, Fin (chi (G.patchOf v))
  colour_eq : ∀ v, colourOf v = colourEquiv (G.patchOf v) ((code (G.patchOf v)).roleColour v)
  palettes : ∀ i, Fin (chi i) → Finset (Fin (T.S.N k))
  palettes_eq : ∀ i a, palettes i a = Finset.univ.filter fun x =>
    x ∈ (PT.tiling.P i).X ∧ colours i x = (colourEquiv i).symm a
  nonempty : ∀ i a, (palettes i a).Nonempty
  subset : ∀ i a, palettes i a ⊆ (PT.tiling.P i).X
  global_disjoint : ∀ p q : (Σ i : Fin PT.tiling.m, Fin (chi i)), p ≠ q →
    Disjoint (palettes p.1 p.2) (palettes q.1 q.2)
  disjoint : ∀ i a a', a ≠ a' → Disjoint (palettes i a) (palettes i a')
  size : ∀ i a, (palettes i a).card ≤ 2 * ((PT.tiling.P i).M : ℝ) / chi i

/-- Choose the code and label colouring jointly for every patch. The
retention output is a Section 17 input estimate on supported fresh readouts,
not initial validity after resampling. TeX 17:233–300; 18:43–57.
The proof must adapt the S17 route to the supplied M/2 corner bound; the
legacy S17 certificate's stronger (1-a)M bound is not assumed. -/
theorem D18_L_palettes (hκ : κ.Admissible) (hThresholds : LateThresholds κ)
    (T : Stage) (hSources : Sources κ T) :
    ∀ᶠ k in atTop, ∀ (PT : ProfiledTiling κ T k) (hPT : PT.Valid)
      (G : LowGeom PT) (F : FreshCell G) (hL16 : L16QuantitativeValidity G F)
      (hLow : PT.tiling.mode.isLow), ProfileCornerMass PT → LargeIndex κ T k →
      ∃ P : PaletteData G,
        (∀ i, PaletteCodeSpec i (P.hle i) (P.code i)) ∧
        ∀ i, PaletteRetentionSpec
          (Lane_sol_s18_dl.physical_list_context hPT hLow (Classical.choice hL16.physical))
          i (P.hle i) (P.code i) (P.colours i) := by
  sorry

/-- Positive reserved pool sizes after one common cutoff. Natural floors
are retained: this is positivity of N/3/r, not a real-division identity.
TeX 16:33–44; 18:89–98,187–194. -/
theorem D18_L_late_pool_positive (hκ : κ.Admissible) (T : Stage) :
    ∀ᶠ k in atTop, ∀ (PT : ProfiledTiling κ T k) (G : LowGeom PT)
      (F : FreshCell G), L16QuantitativeValidity G F →
      ∀ B : LateProcessBase F, ∀ j, 0 < (B.latePool j).card := by
  sorry

/-- Total seed kernels for the raw encoding; P18.4a later replaces them by
its selected reference kernels. The seed is only used to make all direct
initial-data definitions available. TeX 18:66–71,89–110,810–825. -/
theorem D18_L_seed_kernels {G : LowGeom PT} {F : FreshCell G}
    (B : LateProcessBase F) (hPool : ∀ j, 0 < (B.latePool j).card) :
    Nonempty (LateKernels B) := by
  let fallback : Fin (T.S.N k) := ⟨0, T.S.N_pos k⟩
  let mask (b : Pos T k) : B.AllowedMask b := ⟨B.latePoolOf b, ⟨le_rfl, by omega⟩⟩
  have hLabel (j : Fin G.r) (b : {v : Pos T k // v ∈ B.classes j}) :
      (B.latePoolOf b.1).Nonempty := by
    have hb := (B.class_of_spec b.1 j).mp b.2
    simpa [LateProcessBase.latePoolOf, hb] using Finset.card_pos.mp (hPool j)
  let out (j : Fin G.r) (b : {v : Pos T k // v ∈ B.classes j}) : B.RowOut b.1 :=
    (mask b.1, (fun _ _ => fallback), ⟨(hLabel j b).choose, (hLabel j b).choose_spec⟩)
  refine ⟨{
    maskProfile := fun b => FinLaw.dirac (mask b)
    refK := fun j b _ => FinLaw.dirac (out j b)
    refK_mask_marginal := ?_ }⟩
  intro j b h
  have law_ext {Ω : Type} [Fintype Ω] (P Q : FinLaw Ω) (hw : P.w = Q.w) : P = Q := by
    cases P
    cases Q
    cases hw
    rfl
  apply law_ext
  funext S
  change (∑ o : B.RowOut b.1, if o.1 = S then
    (if o = out j b then (1 : ℝ) else 0) else 0) =
      if S = mask b.1 then 1 else 0
  rw [Finset.sum_eq_single (out j b)]
  · simp [out, eq_comm]
  · intro o _ hne
    simp [hne]
  · simp

/-- Concrete construction inputs. The palette estimates are the earlier
code/colouring outputs, and the schedule fields are deterministic facts.
No field contains LateData.Spec or an upstream pool/list probability bound.
TeX 17:233–300,364–369; 18:43–71. -/
structure Inputs (hPT : PT.Valid) where
  geom : LowGeom PT
  fresh : FreshCell geom
  l16 : L16QuantitativeValidity geom fresh
  low : PT.tiling.mode.isLow
  palette : PaletteData geom
  code_spec : ∀ i, PaletteCodeSpec i (palette.hle i) (palette.code i)
  retention : ∀ i, PaletteRetentionSpec
    (Lane_sol_s18_dl.physical_list_context hPT low (Classical.choice l16.physical))
    i (palette.hle i) (palette.code i) (palette.colours i)
  base : LateProcessBase fresh
  kernels : LateKernels base
  pool_pos : ∀ j, 0 < (base.latePool j).card
  processed_mono : ∀ j t, j.val ≤ t.val → base.processed j ⊆ base.processed t
  class_before : ∀ j t, j.val < t.val → base.classes j ⊆ base.processed t

/-- Assemble the finite data from the palette and pool nodes and the proved
physical/schedule helpers. TeX 16:36–115,457–482; 17:233–300; 18:43–71. -/
theorem D18_L_inputs (hκ : κ.Admissible) (hThresholds : LateThresholds κ)
    (T : Stage) (hSources : Sources κ T) :
    ∀ᶠ k in atTop, ∀ (PT : ProfiledTiling κ T k) (hPT : PT.Valid),
      PT.tiling.mode.isLow → ProfileCornerMass PT → LargeIndex κ T k →
      (∃ G : LowGeom PT, ∃ F : FreshCell G, L16QuantitativeValidity G F) →
      Nonempty (Inputs hPT) := by
  filter_upwards [Lane_q_s18_dl.canonical_physical_fresh hκ T hSources.2.2.1,
    D18_L_palettes hκ hThresholds T hSources,
    D18_L_late_pool_positive hκ T] with k hfresh hpal hpools
  intro PT hPT hLow hMass hLarge hOld
  obtain ⟨G, F, hL16⟩ := hfresh PT hPT hLow hOld
  obtain ⟨P, hCode, hRetention⟩ := hpal PT hPT G F hL16 hLow hMass hLarge
  obtain ⟨B, hMono, hBefore⟩ := Lane_sol_s18_dl.late_process_base_exists hPT F
  have hPos := hpools PT G F hL16 B
  obtain ⟨K⟩ := D18_L_seed_kernels B hPos
  exact ⟨{
    geom := G, fresh := F, l16 := hL16, low := hLow, palette := P,
    code_spec := hCode, retention := hRetention, base := B, kernels := K,
    pool_pos := hPos, processed_mono := hMono, class_before := hBefore }⟩

/-- Raw late data with the pool-aware S17 context, its actual list events,
canonical injective priorities, and the prescribed finite resampling horizon.
The physical support and injection fields reuse the proved helper lane.
TeX 17:12–29,364–369; 18:11–20,43–71. -/
noncomputable def rawData (hκ : κ.Admissible) {hPT : PT.Valid} (X : Inputs hPT) : LateData hPT := by
  let physical := Classical.choice X.l16.physical
  let context := Lane_sol_s18_dl.physical_list_context hPT X.low physical
  let E : LateEncoding X.fresh := {
    base := X.base
    kernels := X.kernels
    events := context.asListEvent
    Ts := ⌈Real.log (T.S.n k) ^ 2⌉₊
    Ts_eq := rfl
    order := fun v => (Fintype.equivFin (Pos T k) v).val
    pools_nonempty := X.l16.pools_nonempty }
  exact {
    geom := X.geom
    fresh := X.fresh
    encoding := E
    l16_valid := X.l16
    chi := X.palette.chi
    low_mode := X.low
    constants := hκ
    chi_pos := X.palette.chi_pos
    colourOf := X.palette.colourOf
    palettes := X.palette.palettes
    palette_nonempty := X.palette.nonempty
    palette_subset := X.palette.subset
    palettes_global_disjoint := X.palette.global_disjoint
    palette_disjoint := X.palette.disjoint
    palette_size := X.palette.size
    fallback := ⟨0, T.S.N_pos k⟩
    late_pool_pos := X.pool_pos
    processed_mono := X.processed_mono
    class_before := X.class_before
    early_injective := Lane_sol_s18_dl.initial_odd_labels_injective hPT physical E
    early_support := Lane_sol_s18_dl.initial_odd_label_support physical E }

/-- Full internal validity, adding cap and single-corner shape to the
already proved normalization/internal-hit facts. TeX 18:43–49; 16:196–201,457–459.
Only supported fresh states on typical pools are quantified. -/
theorem D18_L_fresh_internal (hκ : κ.Admissible) (hThresholds : LateThresholds κ)
    (T : Stage) (hSources : Sources κ T) :
    ∀ᶠ k in atTop, ∀ (PT : ProfiledTiling κ T k) (hPT : PT.Valid) (X : Inputs hPT),
      ProfileCornerMass PT → LargeIndex κ T k →
      let D := rawData hκ X
      ∀ (pools : ∀ C, D.fresh.Pool C) (s : Config D.fresh),
        (∀ C, D.fresh.typical C (pools C)) →
        0 < (FinLaw.pi fun C => D.fresh.fresh C (pools C)).w s →
        ∀ v, IsEvenRole v → D.internalValid v s := by
  sorry

/-- Own-prior iid mean estimate. TeX 16:513–529; 18:1076–1089.
This is the first component of FreshCalibration, before any queries. -/
theorem D18_L_prior_mean (hκ : κ.Admissible) (hThresholds : LateThresholds κ)
    (T : Stage) (hSources : Sources κ T) :
    ∀ᶠ k in atTop, ∀ (PT : ProfiledTiling κ T k) (hPT : PT.Valid) (X : Inputs hPT),
      ProfileCornerMass PT → LargeIndex κ T k →
      let D := rawData hκ X
      ∀ v y, IsEvenRole v →
        D.encoding.iidLaw.E (fun pools =>
          if D.fresh.typical (D.geom.cellOf v) (pools (D.geom.cellOf v)) then
            (D.fresh.fresh (D.geom.cellOf v) (pools (D.geom.cellOf v))).E
              (fun s => D.fresh.prior (D.geom.cellOf v) s v y) else 0) ≤
        κ.KB / ((PT.tiling.P (D.geom.patchOf v)).M : ℝ) := by
  sorry

/-- One-cell separated bounded-test estimate, with its actual iid marginal
pool law. TeX 16:469–482; 18:1134–1210. This isolates the calibration
and repeated-bin calculation from multiplication over independent cells. -/
def CellQueryCalibration {hPT : PT.Valid} (D : LateData hPT) : Prop :=
  ∀ C (q : ℕ), q ≤ T.S.n k ^ 2 → ∀ odd : Fin q → Pos T k,
    Function.Injective odd → (∀ a, D.geom.cellOf (odd a) = C) →
    (∀ a, ¬ IsEvenRole (odd a) ∧ D.geom.classOf (odd a) = none) →
    (∀ a a', a ≠ a' → (hammingDist (odd a) (odd a') : ℝ) >
      50 * κ.ρ * (PT.tiling.P (D.geom.patchOf (odd a))).h) →
    ∀ f : Fin q → Fin (T.S.N k) → ℝ, (∀ a y, 0 ≤ f a y ∧ f a y ≤ 1) →
      (D.cellPoolLaw C).E (fun P => if D.fresh.typical C P then
        (D.fresh.fresh C P).E (fun s => ∏ a, f a (D.fresh.label C s (odd a))) else 0) ≤
      Real.exp (0.002 * q) *
        ∏ a, ((∑ y, (PT.πraw (D.geom.patchOf (odd a))).w y * f a y) +
          Real.rpow (T.S.n k : ℝ) (-((κ.Ac : ℝ) - 3)))

/-- Exact independent-cell factorization. Only consulted cells occur in the
product; otherwise the empty-query case would incorrectly pay typicality
for every cell. TeX 18:277–285,1134–1210; 16:469–482. -/
def QueryFactorization {hPT : PT.Valid} (D : LateData hPT) : Prop :=
  ∀ (q : ℕ) (odd : Fin q → Pos T k) (f : Fin q → Fin (T.S.N k) → ℝ),
    D.freshQueryIntegral q odd f =
      ∏ C ∈ (Finset.univ.filter fun C => ∃ a, D.geom.cellOf (odd a) = C),
        (D.cellPoolLaw C).E (fun P => if D.fresh.typical C P then
          (D.fresh.fresh C P).E (fun s =>
            ∏ a : {a : Fin q // D.geom.cellOf (odd a) = C},
              f a.1 (D.fresh.label C s (odd a.1))) else 0)

/-- Local calibration and repeated-bin losses for separated consultations.
TeX 16:469–482; 18:1134–1210. The cutoff is before the cell, query
family and bounded tests; q=0 is permitted. -/
theorem D18_L_cell_query_calibration (hκ : κ.Admissible) (hThresholds : LateThresholds κ)
    (T : Stage) (hSources : Sources κ T) :
    ∀ᶠ k in atTop, ∀ (PT : ProfiledTiling κ T k) (hPT : PT.Valid) (X : Inputs hPT),
      ProfileCornerMass PT → LargeIndex κ T k → CellQueryCalibration (rawData hκ X) := by
  classical
  filter_upwards [T.S.n_tendsto.eventually_ge_atTop 1000000] with k hn
  intro PT hPT X hMass hLarge
  let D := rawData hκ X
  change CellQueryCalibration D
  intro C q hq odd hodd hCell hEarly hSep f hf
  by_cases hzero : q = 0
  · subst q
    exact Lane_sol_d18l_cal.zero_queries D C odd f
  let physical := Classical.choice X.l16.physical
  let roles : Fin q → S16.OddCellRole D.geom C :=
    fun a => ⟨odd a, hCell a, (hEarly a).1⟩
  have hroles : Function.Injective roles := by
    intro a b hab
    exact hodd (congrArg Subtype.val hab)
  by_cases hCluster : PT.tiling.mode.isCluster
  · have hSepC : ∀ a b, a ≠ b →
        50 * κ.ρ * (PT.tiling.P (D.geom.cellPatch C)).h <
          (hammingDist (roles a).1 (roles b).1 : ℝ) := by
      intro a b hab
      have hpatch : D.geom.patchOf (odd a) = D.geom.cellPatch C := by
        rw [← D.geom.cellOf_patch (odd a), hCell a]
      simpa only [hpatch] using hSep a b hab
    have hGroups : Function.Injective (fun a => physical.raw.groupOf C (roles a)) :=
      Lane_sol_d18l_cal.query_groups_injective hκ hThresholds hPT
        physical.raw physical.source_valid hCluster X.low C roles hSepC
    sorry
  · have hRawGroups : Function.Injective (physical.raw.groupOf C) := by
      rcases physical.source_valid with ⟨hm, _, hSource⟩ | ⟨_, hSource⟩
      · exact (hCluster (by simp [hm, Mode.isCluster])).elim
      · exact (hSource C).1
    have hGroups : Function.Injective (fun a => physical.raw.groupOf C (roles a)) :=
      hRawGroups.comp hroles
    sorry

/-- Product-pool/product-fresh algebra, without positivity or typicality
assumptions on unconsulted cells. TeX 18:277–285,1134–1210. -/
theorem D18_L_query_factorization (hκ : κ.Admissible) {hPT : PT.Valid} (X : Inputs hPT) :
    QueryFactorization (rawData hκ X) := by
  exact Lane_sol_d18l_cal.fresh_factorization (rawData hκ X)

/-- Assemble the general separated-test estimate from one-cell calibration
and exact factorization; reindex each queried fibre by its finite cardinality.
TeX 18:1134–1210. The exponential costs multiply to exp(.002q). -/
theorem D18_L_separated_calibration {hPT : PT.Valid} (D : LateData hPT)
    (hCells : CellQueryCalibration D) (hFactor : QueryFactorization D) :
    ∀ q : ℕ, q ≤ T.S.n k ^ 2 → ∀ odd : Fin q → Pos T k, Function.Injective odd →
      (∀ a, ¬ IsEvenRole (odd a) ∧ D.geom.classOf (odd a) = none) →
      (∀ a a', a ≠ a' → D.geom.cellOf (odd a) = D.geom.cellOf (odd a') →
        (hammingDist (odd a) (odd a') : ℝ) >
          50 * κ.ρ * (PT.tiling.P (D.geom.patchOf (odd a))).h) →
      ∀ f : Fin q → Fin (T.S.N k) → ℝ, (∀ a y, 0 ≤ f a y ∧ f a y ≤ 1) →
        D.freshQueryIntegral q odd f ≤ Real.exp (0.002 * q) *
          ∏ a, ((∑ y, (PT.πraw (D.geom.patchOf (odd a))).w y * f a y) +
            Real.rpow (T.S.n k : ℝ) (-((κ.Ac : ℝ) - 3))) := by
  classical
  intro q hq odd hodd hEarly hSep f hf
  let c := fun a => D.geom.cellOf (odd a)
  let S := Finset.univ.filter fun C => ∃ a, c a = C
  let b := fun a => (∑ y, (PT.πraw (D.geom.patchOf (odd a))).w y * f a y) +
    Real.rpow (T.S.n k : ℝ) (-((κ.Ac : ℝ) - 3))
  let L := fun C => (D.cellPoolLaw C).E (fun P => if D.fresh.typical C P then
    (D.fresh.fresh C P).E (fun s => ∏ a : {a : Fin q // c a = C},
      f a.1 (D.fresh.label C s (odd a.1))) else 0)
  have hL : ∀ C, 0 ≤ L C := by
    intro C
    dsimp only [L, FinLaw.E]
    apply Finset.sum_nonneg
    intro P _
    apply mul_nonneg ((D.cellPoolLaw C).nonneg P)
    split_ifs
    · apply Finset.sum_nonneg
      intro s _
      apply mul_nonneg ((D.fresh.fresh C P).nonneg s)
      exact Finset.prod_nonneg (fun a _ => (hf a.1 _).1)
    · exact le_rfl
  have hB (C : D.geom.Cell) :
      L C ≤ Real.exp (0.002 * Fintype.card {a : Fin q // c a = C}) *
        ∏ a : {a : Fin q // c a = C}, b a.1 := by
    let A := {a : Fin q // c a = C}
    let e := (Fintype.equivFin A).symm
    have hsize : Fintype.card A ≤ q := by
      calc
        Fintype.card A ≤ Fintype.card (Fin q) :=
          Fintype.card_le_of_injective Subtype.val Subtype.val_injective
        _ = q := Fintype.card_fin q
    have he : Function.Injective (fun a => odd (e a).1) :=
      hodd.comp (Subtype.val_injective.comp e.injective)
    have h := hCells C (Fintype.card A) (hsize.trans hq)
      (fun a => odd (e a).1) he (fun a => (e a).2)
      (fun a => hEarly (e a).1)
      (fun a a' hne => hSep (e a).1 (e a').1
        (fun hv => hne (e.injective (Subtype.ext hv)))
        ((e a).2.trans (e a').2.symm))
      (fun a => f (e a).1) (fun a y => hf (e a).1 y)
    have hprod (s : D.fresh.State C) :
        (∏ a : Fin (Fintype.card A), f (e a).1
          (D.fresh.label C s (odd (e a).1))) =
          ∏ a : A, f a.1 (D.fresh.label C s (odd a.1)) := by
      exact e.prod_comp (fun a : A => f a.1 (D.fresh.label C s (odd a.1)))
    simp_rw [hprod] at h
    have hrhs : (∏ a : Fin (Fintype.card A), b (e a).1) =
        ∏ a : A, b a.1 := e.prod_comp (fun a : A => b a.1)
    exact h.trans_eq (congrArg (fun x => Real.exp (0.002 * Fintype.card A) * x) hrhs)
  rw [hFactor q odd f]
  simpa only [S, c, L, b, Fintype.card_fin] using
    Lane_sol_d18l_cal.fibre_bounds c S (fun a => by simp [S]) L b 0.002 hL hB

/-- Unpinned upstream pool/list tail for the actual finite process.
TeX 17:123–131; 18:678–690. The exponent uses the prescribed Ts. -/
theorem D18_L_upstream_bad (hκ : κ.Admissible) (hThresholds : LateThresholds κ)
    (T : Stage) (hSources : Sources κ T) :
    ∀ᶠ k in atTop, ∀ (PT : ProfiledTiling κ T k) (hPT : PT.Valid) (X : Inputs hPT),
      ProfileCornerMass PT → LargeIndex κ T k →
      let D := rawData hκ X
      ∀ f, D.encoding.permLaw.pr (D.upstreamBad f) ≤
        Real.rpow (T.S.n k : ℝ) (-((κ.P : ℝ) * D.encoding.Ts / 2)) := by
  sorry

/-- The same tail with any one global slot-to-bin pin; zero-probability
pins retain Lean's zero quotient. TeX 17:123–131; 18:678–690. -/
theorem D18_L_upstream_bad_pinned (hκ : κ.Admissible) (hThresholds : LateThresholds κ)
    (T : Stage) (hSources : Sources κ T) :
    ∀ᶠ k in atTop, ∀ (PT : ProfiledTiling κ T k) (hPT : PT.Valid) (X : Inputs hPT),
      ProfileCornerMass PT → LargeIndex κ T k →
      let D := rawData hκ X
      ∀ C (slot : Fin (D.geom.nslot C)) (bin : Bin PT.tiling (D.geom.cellPatch C)) f,
        D.encoding.permLaw.pr (fun x => x.1 C slot = bin ∧ D.upstreamBad f x) /
          D.encoding.permLaw.pr (fun x => x.1 C slot = bin) ≤
        Real.rpow (T.S.n k : ℝ) (-((κ.P : ℝ) * D.encoding.Ts / 2)) := by
  sorry

/-- Transfer diagnostic typical positivity to the actual iid marginal
cell-pool law. TeX 16:260–296; 18:277–285. -/
theorem D18_L_typical_positive (hκ : κ.Admissible) {hPT : PT.Valid} (X : Inputs hPT) :
    let D := rawData hκ X
    ∀ C, 0 < ∑ P ∈ D.typicalPools C, (D.cellPoolLaw C).w P := by
  sorry

/-- Singleton under iid pools conditioned on individual typicality.
TeX 16:457–468; 18:277–285. Conditioning and the (1+KB n⁻³) loss
are part of the claim; no uniform law on states is substituted. -/
theorem D18_L_fresh_singleton (hκ : κ.Admissible) (hThresholds : LateThresholds κ)
    (T : Stage) (hSources : Sources κ T) :
    ∀ᶠ k in atTop, ∀ (PT : ProfiledTiling κ T k) (hPT : PT.Valid) (X : Inputs hPT),
      ProfileCornerMass PT → LargeIndex κ T k →
      let D := rawData hκ X
      ∀ b, ¬ IsEvenRole b → D.geom.classOf b = none → ∀ y,
        (D.typicalFresh (D.geom.cellOf b)).pr (fun Ps =>
          D.fresh.label (D.geom.cellOf b) Ps.2 b = y) ≤
        (1 + κ.KB * Real.rpow (T.S.n k : ℝ) (-3)) * (PT.π (D.geom.patchOf b)).w y := by
  sorry

/-- Transport the exact S17 event scope from external positions to flip
coordinates. TeX 17:12–29,364–369; 18:62–64,937–945. -/
theorem D18_L_scope_eq (hκ : κ.Admissible) {hPT : PT.Valid} (X : Inputs hPT) :
    let D := rawData hκ X
    ∀ v, D.encoding.events.scope v = D.directCells v := by
  sorry

/-- Palette row counts, transporting equal binary colour classes through
the actual allocated leaves and host density. TeX 17:233–272; 18:930–936.
The lower bound concerns every palette, including ones never queried later. -/
theorem D18_L_palette_counts (hκ : κ.Admissible) (hThresholds : LateThresholds κ)
    (T : Stage) (hSources : Sources κ T) :
    ∀ᶠ k in atTop, ∀ (PT : ProfiledTiling κ T k) (hPT : PT.Valid) (X : Inputs hPT),
      ProfileCornerMass PT → LargeIndex κ T k →
      let D := rawData hκ X
      ∀ i a,
        let rows := Finset.univ.filter fun v : Pos T k => IsEvenRole v ∧
          (D.geom.patchOf v = i ∧ D.palette v = D.palettes i a)
        (rows.card : ℝ) ≤ κ.KB * ((PT.tiling.P i).M : ℝ) / D.chi i / densityScale T k ∧
          (2 : ℝ) ^ ((T.S.n k : ℝ) - Real.sqrt (T.S.n k)) ≤ rows.card := by
  sorry

/-- Separation within an internal slice from the palette code's kernel
word exclusion. TeX 17:233–272; 18:1118–1123. Only distinct even rows
with the same palette and outer word are compared. -/
theorem D18_L_palette_separation (hκ : κ.Admissible) {hPT : PT.Valid} (X : Inputs hPT) :
    let D := rawData hκ X
    ∀ v w, IsEvenRole v → IsEvenRole w → v ≠ w → D.palette v = D.palette w →
      (∀ a, a ∉ PT.tiling.Icoord (D.geom.patchOf v) → v a = w a) →
        500 * κ.ρ * (PT.tiling.P (D.geom.patchOf v)).h < (hammingDist v w : ℝ) := by
  sorry

/-- Exact S17-to-S18 list-event adapter: flip coordinates biject with
external early positions, omitted-incidence cardinalities are unchanged,
and row weights use the same degree denominator. TeX 17:12–29;
18:43–49. No validity or success premise is used for this identity. -/
theorem D18_L_events_eq (hκ : κ.Admissible) {hPT : PT.Valid} (X : Inputs hPT) :
    let D := rawData hκ X
    ∀ v s, D.encoding.events.S v s ↔ IsEvenRole v ∧ D.listFailure v s := by
  sorry

/-- Starting atom cap after palette normalization. TeX 17:298–300;
18:126–134. Quantifies even, initially valid rows only, including the
actual starting remaining-neighbour count. -/
theorem D18_L_initial_cap (hκ : κ.Admissible) (hThresholds : LateThresholds κ)
    (T : Stage) (hSources : Sources κ T) :
    ∀ᶠ k in atTop, ∀ (PT : ProfiledTiling κ T k) (hPT : PT.Valid) (X : Inputs hPT),
      ProfileCornerMass PT → LargeIndex κ T k →
      let D := rawData hκ X
      ∀ v s, IsEvenRole v → D.initialValid v s → ∀ x,
        (D.initialPrior v s).w x ≤ 4 * κ.KB / densityScale T k *
          Real.exp (-199 * PT.tiling.gain (D.geom.patchOf v)) *
            Real.rpow 2 (-(D.remainingNeighbors v ⟨0, D.l16_valid.r_pos⟩ : ℝ)) := by
  sorry

/-- Supported resampling inputs with typical pools and all list successes
have internal validity and retained starting palette mass. TeX 17:273–300;
18:43–49. Physical tape support and palette retention must both be used. -/
theorem D18_L_initial_success (hκ : κ.Admissible) (hThresholds : LateThresholds κ)
    (T : Stage) (hSources : Sources κ T) :
    ∀ᶠ k in atTop, ∀ (PT : ProfiledTiling κ T k) (hPT : PT.Valid) (X : Inputs hPT),
      ProfileCornerMass PT → LargeIndex κ T k →
      let D := rawData hκ X
      ∀ x : D.encoding.InitInput, 0 < D.encoding.permLaw.w x →
        (∀ C, D.fresh.typical C (x.1 C)) →
        (∀ v, ¬ D.encoding.events.S v (D.encoding.initialState x)) →
        ∀ v, IsEvenRole v → D.initialValid v (D.encoding.initialState x) := by
  sorry

/-- Direct-data locality: equal own/external cells give identical initial
weights, also on invalid configurations. TeX 18:62–71,937–945. -/
theorem D18_L_prior_local {hPT : PT.Valid} (D : LateData hPT) :
    ∀ v s s', (∀ C ∈ D.directCells v, s C = s' C) →
      D.initialWeight v s = D.initialWeight v s' := by
  intro v s s' h
  have hown : s (D.geom.cellOf v) = s' (D.geom.cellOf v) :=
    h _ (by simp [LateData.directCells])
  have hext : ∀ a ∈ D.externalEarly v,
      s (D.geom.cellOf (flipPos v a)) = s' (D.geom.cellOf (flipPos v a)) := by
    intro a ha
    apply h
    exact Finset.mem_union_right _ (Finset.mem_image.mpr ⟨a, ha, rfl⟩)
  funext x
  unfold LateData.initialWeight LateData.sigma LateData.earlyLabel
  rw [hown]
  congr 1
  apply Finset.prod_congr rfl
  intro a ha
  rw [hext a ha]

end HypercubeRamsey.S18.Lane_sol_split_d18l
