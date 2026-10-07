import HypercubeRamsey.S18.Nodes_sol_split_d18l_sol_d18l_pal
import HypercubeRamsey.S18.Nodes_q_s18_dl
import HypercubeRamsey.S18.Nodes_sol_s18_dl
import HypercubeRamsey.S18.Nodes_sol_s18_dl_base
import HypercubeRamsey.S17.Nodes
import HypercubeRamsey.S18.Nodes_sol_split_d18l_sol_d18l_fresh

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
  let R : ℝ := max 1 (2 * κ.A0 / Real.log 2)
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hscale : ∀ᶠ k in atTop,
      3 * R ≤ (T.S.N k : ℝ) / (2 : ℝ) ^ T.S.n k :=
    T.S.ratio_tendsto.eventually_ge_atTop (3 * R)
  have hn : ∀ᶠ k in atTop, 1 ≤ T.S.n k :=
    T.S.n_tendsto.eventually_ge_atTop 1
  filter_upwards [hscale, hn] with k hscale hn
  intro PT G F hL16 B j
  have hnR : 1 ≤ (T.S.n k : ℝ) := by exact_mod_cast hn
  have hnpos : 0 < (T.S.n k : ℝ) := lt_of_lt_of_le zero_lt_one hnR
  have hlogn : Real.log (T.S.n k : ℝ) ≤ (T.S.n k : ℝ) :=
    Real.log_le_self hnpos.le
  have hRnonneg : 0 ≤ R := by dsimp [R]; positivity
  have hRlog : 2 * κ.A0 ≤ R * Real.log 2 := by
    dsimp [R]
    exact (div_le_iff₀ hlog2).mp (le_max_right _ _)
  have hr : (G.r : ℝ) ≤ R * Real.log (T.S.n k : ℝ) := by
    apply (mul_le_mul_iff_of_pos_right hlog2).mp
    calc
      (G.r : ℝ) * Real.log 2 ≤ 2 * κ.A0 * Real.log (T.S.n k : ℝ) :=
        hL16.r_upper
      _ ≤ R * Real.log 2 * Real.log (T.S.n k : ℝ) :=
        mul_le_mul_of_nonneg_right hRlog (Real.log_nonneg hnR)
      _ = (R * Real.log (T.S.n k : ℝ)) * Real.log 2 := by ring
  have hpow : (T.S.n k : ℝ) ≤ (2 : ℝ) ^ T.S.n k := by
    exact_mod_cast (S13.nat_le_two_pow (T.S.n k))
  have hNreal : 3 * (G.r : ℝ) ≤ (T.S.N k : ℝ) := by
    have hscale' : 3 * R * (2 : ℝ) ^ T.S.n k ≤ (T.S.N k : ℝ) :=
      (le_div_iff₀ (by positivity : (0 : ℝ) < (2 : ℝ) ^ T.S.n k)).mp hscale
    have hnRle : R * Real.log (T.S.n k : ℝ) ≤ R * (T.S.n k : ℝ) :=
      mul_le_mul_of_nonneg_left hlogn hRnonneg
    have hRn : R * (T.S.n k : ℝ) ≤ R * (2 : ℝ) ^ T.S.n k :=
      mul_le_mul_of_nonneg_left hpow hRnonneg
    nlinarith
  have hNnat : 3 * G.r ≤ T.S.N k := by exact_mod_cast hNreal
  have hdiv : G.r ≤ T.S.N k / 3 := by omega
  have hpos : 0 < (T.S.N k / 3) / G.r :=
    Nat.div_pos hdiv hL16.r_pos
  rw [B.latePool_card j]
  exact hpos

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
  filter_upwards [] with k
  intro PT hPT X hMass hLarge
  dsimp only
  intro pools s ht hs v he
  let physical := Classical.choice X.l16.physical
  have hv := Lane_sol_s18_dl.product_fresh_valid physical pools s ht hs
  have hp := Lane_sol_s18_dl.internal_probability_and_hits physical pools s hv v he
  have hsupport := S16.Lane_sol_s16_prod1.pi_support
    (fun C => X.fresh.fresh C (pools C)) s (ne_of_gt hs) (X.geom.cellOf v)
  have hshape := Lane_sol_d18l_fresh.physical_prior_shape hPT physical
    (X.geom.cellOf v) (pools (X.geom.cellOf v)) (ht _) (s (X.geom.cellOf v))
    hsupport v rfl he hp.2.1
  rw [X.geom.cellOf_patch v] at hshape
  change (∀ x, 0 ≤ X.fresh.prior (X.geom.cellOf v) (s (X.geom.cellOf v)) v x) ∧ _
  refine ⟨hp.1, hp.2.1, hshape.1, hshape.2, ?_⟩
  intro a ha x hx
  have hcell := Lane_sol_d18l_fresh.internal_neighbor_cell physical.raw v a ha
  change Hits (T.S.E k) PT.tiling.c x
    (X.fresh.label (X.geom.cellOf (flipPos v a)) (s (X.geom.cellOf (flipPos v a))) (flipPos v a))
  rw [hcell]
  exact (hp.2.2 x hx).2 a ha

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
  filter_upwards [Lane_sol_d18l_fresh.physical_prior_mean_bound hκ T] with k hk
  intro PT hPT X hMass hLarge
  dsimp only
  intro v y he
  have hMean := hk PT hPT X.geom X.fresh (Classical.choice X.l16.physical)
    X.l16.pools_nonempty hMass v y he
  apply hMean.trans
  apply div_le_div_of_nonneg_right _ (Nat.cast_nonneg _)
  exact hThresholds.2.1

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
  sorry

/-- Product-pool/product-fresh algebra, without positivity or typicality
assumptions on unconsulted cells. TeX 18:277–285,1134–1210. -/
theorem D18_L_query_factorization (hκ : κ.Admissible) {hPT : PT.Valid} (X : Inputs hPT) :
    QueryFactorization (rawData hκ X) := by
  sorry

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
  sorry

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
  classical
  filter_upwards [T.S.n_tendsto.eventually_ge_atTop 0] with k hk
  intro PT hPT X hMass hLarge
  dsimp only
  intro C slot bin f
  let D := rawData hκ X
  let pin : D.encoding.InitInput → Prop := fun x => x.1 C slot = bin
  let bad : D.encoding.InitInput → Prop := D.upstreamBad f
  change D.encoding.permLaw.pr (fun x => pin x ∧ bad x) /
      D.encoding.permLaw.pr pin ≤ _
  -- The zero-denominator pin retains Lean's zero quotient. The positive-pin
  -- case needs the actual S17 pinned pool/list tail.
  by_cases hden : D.encoding.permLaw.pr pin = 0
  · have hnum_nonneg : 0 ≤ D.encoding.permLaw.pr (fun x => pin x ∧ bad x) := by
      unfold FinLaw.pr
      apply Finset.sum_nonneg
      intro x hx
      split_ifs
      · exact D.encoding.permLaw.nonneg x
      · exact le_rfl
    have hnum_le : D.encoding.permLaw.pr (fun x => pin x ∧ bad x) ≤
        D.encoding.permLaw.pr pin := by
      unfold FinLaw.pr
      apply Finset.sum_le_sum
      intro x hx
      by_cases hp : pin x
      · by_cases hb : bad x
        · simp [hp, hb]
        · simpa [hp, hb] using D.encoding.permLaw.nonneg x
      · simp [hp]
    have hnum : D.encoding.permLaw.pr (fun x => pin x ∧ bad x) = 0 := by
      linarith
    have hpow : 0 ≤ Real.rpow (T.S.n k : ℝ) (-((κ.P : ℝ) * D.encoding.Ts / 2)) :=
      Real.rpow_nonneg (by positivity) _
    simpa [hden, hnum] using hpow
  · sorry

/-- Transfer diagnostic typical positivity to the actual iid marginal
cell-pool law. TeX 16:260–296; 18:277–285. -/
theorem D18_L_typical_positive (hκ : κ.Admissible) {hPT : PT.Valid} (X : Inputs hPT) :
    let D := rawData hκ X
    ∀ C, 0 < ∑ P ∈ D.typicalPools C, (D.cellPoolLaw C).w P := by
  change ∀ C : X.geom.Cell, 0 < ∑ P ∈ (rawData hκ X).typicalPools C,
    ((rawData hκ X).cellPoolLaw C).w P
  intro C
  let physical := Classical.choice X.l16.physical
  letI : ∀ C, Fintype (X.fresh.State C) := X.fresh.stFin
  letI : ∀ s, Fintype (physical.raw.Value C s) := physical.raw.valueFin C
  letI : Fintype (physical.raw.Hist C) := by
    change Fintype ((s : physical.raw.Slice C) → physical.raw.Value C s)
    infer_instance
  letI : Fintype (physical.diagnostics.Check C) := physical.diagnostics.checkFin C
  let diag := physical.diagnostics.diagnostic C
  let P₀ := X.l16.pools_nonempty.choose
  let Rest : Type := ∀ c : {c : X.geom.Cell // c ≠ C}, X.fresh.Pool c.1
  let split : (∀ c, X.fresh.Pool c) ≃ X.fresh.Pool C × Rest :=
    Equiv.piSplitAt C (fun c => X.fresh.Pool c)
  let uPool : FinLaw (X.fresh.Pool C) :=
    FinLaw.uniform Finset.univ ⟨P₀ C, Finset.mem_univ _⟩
  let pairLaw : FinLaw (X.fresh.Pool C × Rest) :=
    FinLaw.uniform Finset.univ ⟨(P₀ C, fun c => P₀ c.1), Finset.mem_univ _⟩
  have hIidMap (A : X.fresh.Pool C × Rest → Prop) :
      (iidPoolLaw X.geom X.l16.pools_nonempty).pr (fun P => A (split P)) = pairLaw.pr A := by
    have hsource : (Finset.univ : Finset (∀ c, X.fresh.Pool c)).Nonempty :=
      ⟨P₀, Finset.mem_univ _⟩
    have htarget : (Finset.univ : Finset (X.fresh.Pool C × Rest)).Nonempty :=
      ⟨(P₀ C, fun c => P₀ c.1), Finset.mem_univ _⟩
    have hcard : (Finset.univ : Finset (∀ c, X.fresh.Pool c)).card =
        (Finset.univ : Finset (X.fresh.Pool C × Rest)).card := by
      simpa using Fintype.card_congr split
    change (FinLaw.uniform Finset.univ hsource).pr (fun P => A (split P)) =
      (FinLaw.uniform Finset.univ htarget).pr A
    exact Lane_q_s16_comp1.uniform_pr_equiv Finset.univ hsource Finset.univ htarget
      split (by intro P; simp) hcard A
  have hMarg (A : X.fresh.Pool C → Prop) :
      (iidPoolLaw X.geom X.l16.pools_nonempty).pr (fun P => A (P C)) = uPool.pr A := by
    have hmap := hIidMap (fun z => A z.1)
    have hprod := Lane_q_s16_comp1.uniform_prod_pr_fst
      (⟨P₀ C⟩ : Nonempty (X.fresh.Pool C))
      (⟨fun c : {c : X.geom.Cell // c ≠ C} => P₀ c.1⟩ : Nonempty Rest) A
    calc
      _ = pairLaw.pr (fun z => A z.1) := by
        have hproj (P : ∀ c, X.fresh.Pool c) : (split P).1 = P C := rfl
        have hrewrite :
            (iidPoolLaw X.geom X.l16.pools_nonempty).pr (fun P => A (P C)) =
              (iidPoolLaw X.geom X.l16.pools_nonempty).pr
                (fun P => A ((split P).1)) := by
          apply Lane_q_s16_comp1.finlaw_pr_congr
          intro P
          rw [hproj]
        exact hrewrite.trans hmap
      _ = uPool.pr A := by simpa [pairLaw, uPool] using hprod
  have hdiagConst (P : X.fresh.Pool C) :
      diag.poolLaw.w P = ∏ t : Fin (X.geom.nslot C),
        (1 / (Fintype.card (Bin PT.tiling (X.geom.cellPatch C)) : ℝ)) := by
    simp [S16.CellPoolDiagnostics.poolLaw, FinLaw.pi, diag.uniform_slots]
  have huConst (P : X.fresh.Pool C) :
      uPool.w P = 1 / (Fintype.card (X.fresh.Pool C) : ℝ) := by
    simp [uPool, FinLaw.uniform]
  have hdiag : diag.poolLaw = uPool :=
    Lane_q_s16_comp1.finlaw_eq_of_const_weights diag.poolLaw uPool
      (∏ t : Fin (X.geom.nslot C),
        (1 / (Fintype.card (Bin PT.tiling (X.geom.cellPatch C)) : ℝ)))
      (1 / (Fintype.card (X.fresh.Pool C) : ℝ)) ⟨P₀ C⟩ hdiagConst huConst
  have hLaw : (rawData hκ X).cellPoolLaw C = diag.poolLaw := by
    change FinLaw.map (iidPoolLaw X.geom X.l16.pools_nonempty) (fun Q => Q C) = diag.poolLaw
    apply Lane_q_s16_comp1.finlaw_ext
    intro P
    change (FinLaw.map (iidPoolLaw X.geom X.l16.pools_nonempty)
      (fun Q => Q C)).w P = diag.poolLaw.w P
    calc
      _ = (iidPoolLaw X.geom X.l16.pools_nonempty).pr (fun Q => Q C = P) := by
        rw [S16.Lane_q_s16_comp2.map_weight_eq_pr]
      _ = uPool.pr (fun Q => Q = P) := hMarg (fun Q => Q = P)
      _ = uPool.w P := by
        simp [FinLaw.pr, Finset.sum_ite_eq', eq_comm]
      _ = diag.poolLaw.w P := by rw [← hdiag]
  rw [hLaw]
  change 0 < ∑ P ∈ Finset.univ.filter (X.fresh.typical C), diag.poolLaw.w P
  simpa [diag] using physical.typical_positive C

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
  filter_upwards [Lane_sol_d18l_fresh.eventually_typical_failure T] with k hk
  intro PT hPT X hMass hLarge
  dsimp only
  intro b hOdd hEarly y
  let D := rawData hκ X
  let physical := Classical.choice X.l16.physical
  obtain ⟨hpos, hbound⟩ := Lane_sol_d18l_fresh.physical_singleton physical
    X.l16.pools_nonempty hk b hOdd y
  have hpos' : 0 < ∑ P ∈ D.typicalPools (D.geom.cellOf b),
      (D.cellPoolLaw (D.geom.cellOf b)).w P := hpos
  change (D.typicalFresh (D.geom.cellOf b)).pr _ ≤ _
  rw [LateData.typicalFresh, dif_pos hpos']
  apply hbound.trans
  apply mul_le_mul_of_nonneg_right _ ((PT.π (X.geom.patchOf b)).nonneg y)
  have hP : 0 < κ.P := by have := hκ.P_big.2; omega
  have hR : (1 : ℕ) ≤ κ.R := by rw [hκ.R_eq]; exact Nat.one_le_iff_ne_zero.mpr (pow_ne_zero _ (Nat.ne_of_gt hP))
  have hRreal : (1 : ℝ) ≤ κ.R := by exact_mod_cast hR
  have hKB : 2 ≤ κ.KB := by nlinarith [hκ.KB_big]
  simpa only [add_comm, Real.rpow_eq_pow] using add_le_add_left
    (mul_le_mul_of_nonneg_right hKB (Real.rpow_nonneg (Nat.cast_nonneg (T.S.n k)) (-3))) 1

/-- Transport the exact S17 event scope from external positions to flip
coordinates. TeX 17:12–29,364–369; 18:62–64,937–945. -/
theorem D18_L_scope_eq (hκ : κ.Admissible) {hPT : PT.Valid} (X : Inputs hPT) :
    let D := rawData hκ X
    ∀ v, D.encoding.events.scope v = D.directCells v := by
  change ∀ v, (rawData hκ X).encoding.events.scope v = (rawData hκ X).directCells v
  intro v
  let ctx := Lane_sol_s18_dl.physical_list_context hPT X.low
    (Classical.choice X.l16.physical)
  have hext : ctx.externalEarly v =
      ((rawData hκ X).externalEarly v).image (fun a => flipPos v a) := by
    classical
    ext b
    simp only [ListGateContext.externalEarly, LateData.externalEarly,
      Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_image]
    constructor
    · rintro ⟨hclass, a, ha, rfl⟩
      exact ⟨a, ⟨ha, hclass⟩, rfl⟩
    · rintro ⟨a, ⟨ha, hclass⟩, rfl⟩
      exact ⟨hclass, a, ha, rfl⟩
  change ctx.scopeCells v = (rawData hκ X).directCells v
  simp only [ListGateContext.scopeCells, LateData.directCells]
  change {X.geom.cellOf v} ∪ (ctx.externalEarly v).image X.geom.cellOf =
    {X.geom.cellOf v} ∪
      ((rawData hκ X).externalEarly v).image (fun a => X.geom.cellOf (flipPos v a))
  rw [hext]
  apply congrArg (fun S : Finset X.geom.Cell => {X.geom.cellOf v} ∪ S)
  rw [Finset.image_image]
  apply Finset.image_congr
  intro a ha
  rfl

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
  have hKB : (800 : ℝ) ≤ κ.KB := by
    have hP := hκ.P_big.2
    have hR := hκ.R_eq
    have hRpos : (1 : ℝ) ≤ κ.R := by
      have : 1 ≤ κ.R := by
        rw [hκ.R_eq]
        have hPpos : 0 < κ.P := by omega
        exact Nat.one_le_iff_ne_zero.mpr (pow_ne_zero 2 (ne_of_gt hPpos))
      exact_mod_cast this
    linarith [hκ.KB_big]
  filter_upwards [Lane_sol_d18l_pal.small_prefix_height T] with k hSmall
  intro PT hPT X hMass hLarge
  let D := rawData hκ X
  dsimp only
  intro i a
  let Q := (Classical.choice X.l16.physical).quantitative
  obtain ⟨hLoss, hell⟩ := hSmall (PT.tiling.P i).ℓ (PT.tiling.P i).h
    (Q.prefix_bound i) (Q.height_bound i)
  let ψ := X.palette.code i
  let c := (X.palette.colourEquiv i).symm a
  let rows := Finset.univ.filter fun v : Pos T k => IsEvenRole v ∧
    (D.geom.patchOf v = i ∧ D.palette v = D.palettes i a)
  have hpalette (v : Pos T k) : D.palette v =
      s17Palette (X.palette.code (X.geom.patchOf v)) (X.palette.colours (X.geom.patchOf v)) v := by
    simp only [D, rawData, LateData.palette]
    rw [X.palette.palettes_eq, X.palette.colour_eq]
    simp only [Equiv.symm_apply_apply, s17Palette, ListGateContext.PaletteCode.palette]
  have hrows : rows = Finset.univ.filter fun v : Pos T k =>
      v ∈ PT.tiling.leaf i ∧ IsEvenRole v ∧ ψ.roleColour v = c := by
    ext v
    simp only [rows, Finset.mem_filter, Finset.mem_univ, true_and]
    constructor
    · rintro ⟨hv, hp, hpal⟩
      have hp' : X.geom.patchOf v = i := hp
      refine ⟨by simpa [← hp'] using X.geom.patchOf_leaf v, hv, ?_⟩
      obtain ⟨x, hx⟩ := X.palette.nonempty i a
      have hxv : x ∈ D.palette v := by rw [hpal]; exact hx
      rw [hpalette, hp'] at hxv
      rw [X.palette.palettes_eq i a] at hx
      exact ((Finset.mem_filter.mp hxv).2.2).symm.trans (Finset.mem_filter.mp hx).2.2
    · rintro ⟨hleaf, hv, hc⟩
      have hp : X.geom.patchOf v = i :=
        (hPT.tiling_valid.prefix_complete v).unique (X.geom.patchOf_leaf v) hleaf
      refine ⟨hv, hp, ?_⟩
      rw [hpalette, hp]
      change s17Palette ψ (X.palette.colours i) v = X.palette.palettes i a
      rw [X.palette.palettes_eq i a]
      simp only [s17Palette, ListGateContext.PaletteCode.palette, hc, c]
  have hcount : X.palette.chi i * rows.card = 2 ^ (T.S.n k - (PT.tiling.P i).ℓ - 1) := by
    rw [X.palette.chi_eq, hrows, Lane_sol_d18l_pal.code_fibre_count ψ (X.code_spec i),
      Lane_sol_d18l_pal.even_leaf_card i hell]
  have hcountR : (D.chi i : ℝ) * rows.card =
      (2 : ℝ) ^ (T.S.n k - (PT.tiling.P i).ℓ - 1) := by
    exact_mod_cast hcount
  have hchi : (0 : ℝ) < D.chi i := by exact_mod_cast X.palette.chi_pos i
  have hchiLe : (D.chi i : ℝ) ≤ (2 : ℝ) ^ (PT.tiling.P i).h := by
    have := Lane_sol_d18l_pal.code_chi_le ψ (X.code_spec i)
    rw [← X.palette.chi_eq] at this
    exact_mod_cast this
  have hN : (0 : ℝ) < T.S.N k := by exact_mod_cast T.S.N_pos k
  have hM : (0 : ℝ) < (PT.tiling.P i).M := by
    rw [← (PT.tiling.P i).cardX]
    exact_mod_cast Finset.card_pos.mpr (hPT.tiling_valid.patch_nonempty i).1
  have hS : (0 : ℝ) < PT.tiling.S := by
    linarith [hPT.tiling_valid.S_lower]
  constructor
  · apply (le_div_iff₀ (by unfold densityScale; exact div_pos hN (by positivity) : (0 : ℝ) < densityScale T k)).mpr
    apply (le_div_iff₀ hchi).mpr
    have hdyad := hPT.tiling_valid.dyadic_mass_upper i
    have hscale : (2 : ℝ) ^ (T.S.n k - (PT.tiling.P i).ℓ - 1) * densityScale T k =
        (T.S.N k : ℝ) / 2 * (2 : ℝ) ^ (-((PT.tiling.P i).ℓ : ℤ)) := by
      unfold densityScale
      have hex : T.S.n k = (T.S.n k - (PT.tiling.P i).ℓ - 1) + (PT.tiling.P i).ℓ + 1 := by omega
      have hpown : (2 : ℝ) ^ T.S.n k =
          (2 : ℝ) ^ (T.S.n k - (PT.tiling.P i).ℓ - 1) * (2 : ℝ) ^ (PT.tiling.P i).ℓ * 2 := by
        conv_lhs => rw [hex]
        rw [pow_add, pow_add, pow_one]
      rw [hpown, zpow_neg, zpow_natCast]
      field_simp <;> ring
    calc
      (rows.card : ℝ) * densityScale T k * D.chi i =
          ((D.chi i : ℝ) * rows.card) * densityScale T k := by ring
      _ = (T.S.N k : ℝ) / 2 * (2 : ℝ) ^ (-((PT.tiling.P i).ℓ : ℤ)) := by rw [hcountR, hscale]
      _ ≤ 800 * (PT.tiling.P i).M := by
        have hdyad' := (lt_div_iff₀ hS).mp hdyad
        have hNS : (T.S.N k : ℝ) ≤ 400 * PT.tiling.S := by
          linarith [hPT.tiling_valid.S_lower]
        have hmul := mul_le_mul_of_nonneg_left hNS
          (show (0 : ℝ) ≤ (2 : ℝ) ^ (-((PT.tiling.P i).ℓ : ℤ)) by positivity)
        nlinarith
      _ ≤ κ.KB * (PT.tiling.P i).M := mul_le_mul_of_nonneg_right hKB hM.le
  · have hNat : ((T.S.n k - (PT.tiling.P i).ℓ - 1 : ℕ) : ℝ) =
        (T.S.n k : ℝ) - (PT.tiling.P i).ℓ - 1 := by
      rw [Nat.cast_sub (by omega), Nat.cast_sub (by omega)]
      norm_num
    have hpow : (2 : ℝ) ^ ((T.S.n k : ℝ) - Real.sqrt (T.S.n k)) *
        (2 : ℝ) ^ (PT.tiling.P i).h ≤
          (2 : ℝ) ^ (T.S.n k - (PT.tiling.P i).ℓ - 1) := by
      rw [← Real.rpow_natCast, ← Real.rpow_add (by norm_num), ← Real.rpow_natCast, hNat]
      apply Real.rpow_le_rpow_of_exponent_le (by norm_num)
      linarith
    have hbase : 0 ≤ (2 : ℝ) ^ ((T.S.n k : ℝ) - Real.sqrt (T.S.n k)) := by positivity
    have h := mul_le_mul_of_nonneg_left hchiLe hbase
    rw [← hcountR] at hpow
    exact (mul_le_mul_iff_right₀ hchi).mp (by nlinarith)

/-- Separation within an internal slice from the palette code's kernel
word exclusion. TeX 17:233–272; 18:1118–1123. Only distinct even rows
with the same palette and outer word are compared. -/
theorem D18_L_palette_separation (hκ : κ.Admissible) {hPT : PT.Valid} (X : Inputs hPT) :
    let D := rawData hκ X
    ∀ v w, IsEvenRole v → IsEvenRole w → v ≠ w → D.palette v = D.palette w →
      (∀ a, a ∉ PT.tiling.Icoord (D.geom.patchOf v) → v a = w a) →
        500 * κ.ρ * (PT.tiling.P (D.geom.patchOf v)).h < (hammingDist v w : ℝ) := by
  let D := rawData hκ X
  dsimp only
  intro v w hv hw hne hpal houter
  have hpatch : D.geom.patchOf v = D.geom.patchOf w := by
    by_contra hneq
    have hpq : (⟨D.geom.patchOf v, D.colourOf v⟩ : Σ i, Fin (D.chi i)) ≠
        ⟨D.geom.patchOf w, D.colourOf w⟩ := by
      intro heq
      exact hneq (congrArg Sigma.fst heq)
    have hdisj := D.palettes_global_disjoint _ _ hpq
    obtain ⟨x, hx⟩ := D.palette_nonempty (D.geom.patchOf v) (D.colourOf v)
    exact Finset.disjoint_left.mp hdisj hx (by
      change x ∈ D.palette w
      rw [← hpal]
      exact hx)
  have hcol : (X.palette.code (X.geom.patchOf v)).roleColour v =
      (X.palette.code (X.geom.patchOf v)).roleColour w := by
    obtain ⟨x, hx⟩ := D.palette_nonempty (D.geom.patchOf v) (D.colourOf v)
    have hy : x ∈ D.palette w := by rw [← hpal]; exact hx
    change x ∈ X.palette.palettes (X.geom.patchOf v) (X.palette.colourOf v) at hx
    change x ∈ X.palette.palettes (X.geom.patchOf w) (X.palette.colourOf w) at hy
    rw [X.palette.palettes_eq] at hx hy
    have hcv := (Finset.mem_filter.mp hx).2.2
    have hcw := (Finset.mem_filter.mp hy).2.2
    rw [X.palette.colour_eq] at hcv hcw
    simp only [Equiv.symm_apply_apply] at hcv hcw
    have hp : X.geom.patchOf v = X.geom.patchOf w := hpatch
    rw [← hp] at hcw
    exact hcv.symm.trans hcw
  exact Lane_sol_d18l_pal.code_separation _ (X.code_spec _) v w hne hcol houter

/-- Exact S17-to-S18 list-event adapter: flip coordinates biject with
external early positions, omitted-incidence cardinalities are unchanged,
and row weights use the same degree denominator. TeX 17:12–29;
18:43–49. No validity or success premise is used for this identity. -/
theorem D18_L_events_eq (hκ : κ.Admissible) {hPT : PT.Valid} (X : Inputs hPT) :
    let D := rawData hκ X
    ∀ v s, D.encoding.events.S v s ↔ IsEvenRole v ∧ D.listFailure v s := by
  change ∀ v s, (rawData hκ X).encoding.events.S v s ↔
    IsEvenRole v ∧ (rawData hκ X).listFailure v s
  intro v s
  let D := rawData hκ X
  let ctx := Lane_sol_s18_dl.physical_list_context hPT X.low
    (Classical.choice X.l16.physical)
  have hflip : Function.Injective (flipPos v) := by
    intro a a' heq
    by_contra hne
    have h := congrFun heq a
    simp [flipPos, hne] at h
  have hExt : ctx.externalEarly v = (D.externalEarly v).image (flipPos v) := by
    classical
    ext b
    simp only [ListGateContext.externalEarly, LateData.externalEarly,
      Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_image]
    constructor
    · rintro ⟨hclass, a, ha, rfl⟩
      exact ⟨a, ⟨ha, hclass⟩, rfl⟩
    · rintro ⟨a, ⟨ha, hclass⟩, rfl⟩
      exact ⟨hclass, a, ha, rfl⟩
  have hrow : ctx.rowMass v (ctx.prior s v) (ctx.label s) =
      ∑ x, D.initialWeight v s x := by
    unfold ListGateContext.rowMass ListGateContext.row LateData.initialWeight
    rw [hExt]
    apply Finset.sum_congr rfl
    intro x hx
    rw [Finset.prod_image (by
      intro a ha a' ha' heq
      exact hflip heq)]
    simp only [ctx, D, rawData, Lane_sol_s18_dl.physical_list_context,
      ListGateContext.prior, LateData.sigma, ListGateContext.hitRatio,
      ListGateContext.label, LateData.earlyLabel]
    congr 1
  have hWithheld (J : Finset (Fin (T.S.n k)))
      (hJ : J ⊆ D.externalEarly v) :
      ctx.omittedList v (J.image (flipPos v)) (ctx.label s) = D.withheldList v s J := by
    have hDiff : (D.externalEarly v \ J).image (flipPos v) =
        ctx.externalEarly v \ (J.image (flipPos v)) := by
      rw [hExt]
      ext b
      simp only [Finset.mem_image, Finset.mem_sdiff]
      constructor
      · rintro ⟨a, ⟨haE, haJ⟩, rfl⟩
        refine ⟨⟨a, haE, rfl⟩, ?_⟩
        rintro ⟨a', haJ', hEq⟩
        have haa : a' = a := hflip (by simpa using hEq)
        exact haJ (haa ▸ haJ')
      · rintro ⟨⟨a, haE, rfl⟩, hnot⟩
        refine ⟨a, ⟨haE, ?_⟩, rfl⟩
        intro haJ
        exact hnot ⟨a, haJ, rfl⟩
    apply Finset.ext
    intro x
    simp only [ListGateContext.omittedList, LateData.withheldList,
      Finset.mem_filter, Finset.mem_univ, true_and]
    constructor
    · rintro ⟨hx, hh⟩
      refine ⟨hx, ?_⟩
      intro a ha
      have hmem : flipPos v a ∈ ctx.externalEarly v \ J.image (flipPos v) := by
        rw [← hDiff]
        exact Finset.mem_image.mpr ⟨a, ha, rfl⟩
      simpa [ctx, D, rawData, Lane_sol_s18_dl.physical_list_context,
        ListGateContext.label, LateData.earlyLabel] using hh _ hmem
    · rintro ⟨hx, hh⟩
      refine ⟨hx, ?_⟩
      intro b hb
      rw [← hDiff] at hb
      rcases Finset.mem_image.mp hb with ⟨a, ha, rfl⟩
      simpa [ctx, D, rawData, Lane_sol_s18_dl.physical_list_context,
        ListGateContext.label, LateData.earlyLabel] using hh a ha
  let coordsOf (J : Finset (Pos T k)) :=
    Finset.univ.filter fun a : Fin (T.S.n k) => flipPos v a ∈ J
  have hCoordsOf_subset (J : Finset (Pos T k)) (hJ : J ⊆ ctx.externalEarly v) :
      coordsOf J ⊆ D.externalEarly v := by
    intro a ha
    have hmem := (Finset.mem_filter.mp ha).2
    have hpos : flipPos v a ∈ ctx.externalEarly v := hJ hmem
    rw [hExt] at hpos
    obtain ⟨a', ha', heq⟩ := Finset.mem_image.mp hpos
    exact (hflip heq) ▸ ha'
  have hCoordsOf_image (J : Finset (Pos T k)) (hJ : J ⊆ ctx.externalEarly v) :
      (coordsOf J).image (flipPos v) = J := by
    ext b
    simp only [Finset.mem_image]
    constructor
    · rintro ⟨a, ha, rfl⟩
      exact (Finset.mem_filter.mp ha).2
    · intro hb
      have hmem := hJ hb
      rw [hExt] at hmem
      obtain ⟨a, ha, heq⟩ := Finset.mem_image.mp hmem
      refine ⟨a, ?_, heq⟩
      simp [coordsOf, heq, hb]
  have hCoordsOf_card (J : Finset (Pos T k)) (hJ : J ⊆ ctx.externalEarly v) :
      (coordsOf J).card = J.card := by
    calc
      (coordsOf J).card = ((coordsOf J).image (flipPos v)).card := by
        symm
        exact Finset.card_image_of_injective _ hflip
      _ = J.card := congrArg Finset.card (hCoordsOf_image J hJ)
  have hlogpow4 : (Real.log (T.S.n k : ℝ)) ^ 4 =
      Real.rpow (Real.log (T.S.n k : ℝ)) 4 := by
    exact (Real.rpow_natCast _ _).symm
  have hlogpow8 : (Real.log (T.S.n k : ℝ)) ^ 8 =
      Real.rpow (Real.log (T.S.n k : ℝ)) 8 := by
    exact (Real.rpow_natCast _ _).symm
  have hSupport :
      (∃ J : Finset (Pos T k), J ⊆ ctx.externalEarly v ∧
        (J.card : ℝ) ≤ Real.rpow (Real.log (T.S.n k : ℝ)) 4 ∧
        Real.exp (Real.rpow (Real.log (T.S.n k : ℝ)) 8) <
          (ctx.omittedList v J (ctx.label s)).card) ↔
      (∃ J : Finset (Fin (T.S.n k)), J ⊆ D.externalEarly v ∧
        (J.card : ℝ) ≤ Real.rpow (Real.log (T.S.n k : ℝ)) 4 ∧
        Real.exp (Real.rpow (Real.log (T.S.n k : ℝ)) 8) <
          (D.withheldList v s J).card) := by
    constructor
    · rintro ⟨J, hJ, hsize, hbig⟩
      let J' := coordsOf J
      have hJ' : J' ⊆ D.externalEarly v := hCoordsOf_subset J hJ
      have hImg := hCoordsOf_image J hJ
      have hcard := hCoordsOf_card J hJ
      have hlist := hWithheld J' hJ'
      have hlist' : ctx.omittedList v J (ctx.label s) = D.withheldList v s J' := by
        have hImg' : J'.image (flipPos v) = J := by simpa [J'] using hImg
        rw [← hImg']
        exact hlist
      refine ⟨J', hJ', ?_, ?_⟩
      · have hcardR : (J'.card : ℝ) = (J.card : ℝ) := by exact_mod_cast hcard
        have hsize' : (J'.card : ℝ) ≤ Real.rpow (Real.log (T.S.n k : ℝ)) 4 := by
          rw [hcardR]
          exact hsize
        exact hsize'
      · have hbig' : Real.exp (Real.rpow (Real.log (T.S.n k : ℝ)) 8) <
            (D.withheldList v s J').card := by
          rw [← congrArg Finset.card hlist']
          exact hbig
        exact hbig'
    · rintro ⟨J, hJ, hsize, hbig⟩
      let J' := J.image (flipPos v)
      have hJ' : J' ⊆ ctx.externalEarly v := by
        rw [hExt]
        exact Finset.image_subset_image hJ
      have hcard : J'.card = J.card := Finset.card_image_of_injective _ hflip
      have hlist := hWithheld J hJ
      refine ⟨J', hJ', ?_, ?_⟩
      · have hcardR : (J'.card : ℝ) = (J.card : ℝ) := by exact_mod_cast hcard
        have hsize' : (J'.card : ℝ) ≤ Real.rpow (Real.log (T.S.n k : ℝ)) 4 := by
          rw [hcardR]
          exact hsize
        exact hsize'
      · have hbig' : Real.exp (Real.rpow (Real.log (T.S.n k : ℝ)) 8) <
            (ctx.omittedList v J' (ctx.label s)).card := by
          rw [congrArg Finset.card hlist]
          exact hbig
        exact hbig'
  have hGate : ctx.gateBad v (ctx.prior s v) (ctx.label s) ↔ D.listFailure v s := by
    change (ctx.rowMass v (ctx.prior s v) (ctx.label s) < 1 / 2 ∨
      (∃ J : Finset (Pos T k), J ⊆ ctx.externalEarly v ∧
        (J.card : ℝ) ≤ Real.rpow (Real.log (T.S.n k : ℝ)) 4 ∧
        Real.exp (Real.rpow (Real.log (T.S.n k : ℝ)) 8) <
          (ctx.omittedList v J (ctx.label s)).card)) ↔
      ((∑ x, D.initialWeight v s x) < 1 / 2 ∨
      (∃ J : Finset (Fin (T.S.n k)), J ⊆ D.externalEarly v ∧
        (J.card : ℝ) ≤ Real.log (T.S.n k : ℝ) ^ 4 ∧
        Real.exp (Real.log (T.S.n k : ℝ) ^ 8) < (D.withheldList v s J).card))
    rw [hrow, hlogpow4, hlogpow8, hSupport]
  change (ctx.asListEvent).S v s ↔ IsEvenRole v ∧ D.listFailure v s
  change (IsEvenRole v ∧ ctx.gateBad v (ctx.prior s v) (ctx.label s)) ↔ _
  rw [hGate]

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
  filter_upwards [D18_L_fresh_internal hκ hThresholds T hSources] with k hFreshInternal
  intro PT hPT X hMass hLarge
  change ∀ x : (rawData hκ X).encoding.InitInput,
    0 < (rawData hκ X).encoding.permLaw.w x →
    (∀ C, (rawData hκ X).fresh.typical C (x.1 C)) →
    (∀ v, ¬ (rawData hκ X).encoding.events.S v
      ((rawData hκ X).encoding.initialState x)) →
    ∀ v, IsEvenRole v → (rawData hκ X).initialValid v
      ((rawData hκ X).encoding.initialState x)
  let D := rawData hκ X
  let E := D.encoding
  let physical := Classical.choice X.l16.physical
  let ctx := Lane_sol_s18_dl.physical_list_context hPT X.low physical
  intro x hx hTypical hNoEvents v heven
  let s := E.initialState x
  letI : ∀ C, Fintype (X.fresh.State C) := X.fresh.stFin
  letI : Fintype X.geom.Cell := X.geom.cellFin
  letI : DecidableEq X.geom.Cell := X.geom.cellDec
  have hnotFail : ¬ D.listFailure v s := by
    intro hfail
    apply hNoEvents v
    exact (D18_L_events_eq hκ X v s).mpr ⟨heven, hfail⟩
  have hnotParts : ¬ (∑ y, D.initialWeight v s y < 1 / 2) := by
    intro hlow
    apply hnotFail
    exact Or.inl hlow
  have hMass0 : (1 / 2 : ℝ) ≤ ∑ y, D.initialWeight v s y := le_of_not_gt hnotParts
  have hflip : Function.Injective (flipPos v) := by
    intro a a' heq
    by_contra hne
    have h := congrFun heq a
    simp [flipPos, hne] at h
  have hExt : ctx.externalEarly v = (D.externalEarly v).image (flipPos v) := by
    classical
    ext b
    simp only [ListGateContext.externalEarly, LateData.externalEarly,
      Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_image]
    constructor
    · rintro ⟨hclass, a, ha, rfl⟩
      exact ⟨a, ⟨ha, hclass⟩, rfl⟩
    · rintro ⟨a, ⟨ha, hclass⟩, rfl⟩
      exact ⟨hclass, a, ha, rfl⟩
  have hprod : E.poolLaw.w x.1 * (tapeLaw X.fresh E.Ts).w x.2 ≠ 0 := ne_of_gt hx
  have hTape : (tapeLaw X.fresh E.Ts).w x.2 ≠ 0 :=
    (mul_ne_zero_iff.mp hprod).2
  have hTapePi :
      (FinLaw.pi (fun C => FinLaw.pi (fun j : Fin (E.Ts + 2) =>
        FinLaw.pi (fun P : X.fresh.Pool C => X.fresh.fresh C P)))).w x.2 ≠ 0 := by
    simpa [tapeLaw] using hTape
  have hEntryNe : ∀ C (j : Fin (E.Ts + 2)) (P : X.fresh.Pool C),
      (X.fresh.fresh C P).w (x.2 C j P) ≠ 0 := by
    intro C j P
    letI : Fintype (X.fresh.State C) := X.fresh.stFin C
    have hC :
        (FinLaw.pi (fun j : Fin (E.Ts + 2) =>
          FinLaw.pi (fun P : X.fresh.Pool C => X.fresh.fresh C P))).w (x.2 C) ≠ 0 := by
      change (∏ C' : X.geom.Cell,
        (FinLaw.pi (fun j : Fin (E.Ts + 2) =>
          FinLaw.pi (fun P : X.fresh.Pool C' => X.fresh.fresh C' P))).w (x.2 C')) ≠ 0 at hTapePi
      exact Finset.prod_ne_zero_iff.mp hTapePi C (Finset.mem_univ C)
    have hj :
        (FinLaw.pi (fun P : X.fresh.Pool C => X.fresh.fresh C P)).w (x.2 C j) ≠ 0 := by
      change (∏ j' : Fin (E.Ts + 2),
        (FinLaw.pi (fun P : X.fresh.Pool C => X.fresh.fresh C P)).w (x.2 C j')) ≠ 0 at hC
      exact Finset.prod_ne_zero_iff.mp hC j (Finset.mem_univ j)
    change (∏ P' : X.fresh.Pool C,
      (X.fresh.fresh C P').w (x.2 C j P')) ≠ 0 at hj
    exact Finset.prod_ne_zero_iff.mp hj P (Finset.mem_univ P)
  have hEntry : ∀ C (j : Fin (E.Ts + 2)) (P : X.fresh.Pool C),
      0 < (X.fresh.fresh C P).w (x.2 C j P) := by
    intro C j P
    letI : Fintype (X.fresh.State C) := X.fresh.stFin C
    exact lt_of_le_of_ne ((X.fresh.fresh C P).nonneg (x.2 C j P))
      (hEntryNe C j P).symm
  have hCellSupport : ∀ C,
      0 < (X.fresh.fresh C (x.1 C)).w (s C) := by
    change ∀ C, 0 < (X.fresh.fresh C (x.1 C)).w
      ((E.events.runRounds E.Ts E.order Finset.univ x.1 x.2.extend).1 C)
    letI : ∀ C, Fintype (X.fresh.State C) := X.fresh.stFin
    let valid : (C : X.geom.Cell) → X.fresh.State C → Prop :=
      fun C z => 0 < (X.fresh.fresh C (x.1 C)).w z
    change ∀ C, valid C ((E.events.runRounds E.Ts E.order Finset.univ x.1 x.2.extend).1 C)
    have htape : ∀ C j, valid C (x.2.extend C j (x.1 C)) := by
      intro C j
      letI : Fintype (X.fresh.State C) := X.fresh.stFin C
      let idx : Fin (E.Ts + 2) := ⟨min j (E.Ts + 1), by omega⟩
      simpa [valid, Tapes.extend, idx] using hEntry C idx (x.1 C)
    exact Lane_sol_s18_dl.runRounds_preserves_cell_validity E.events valid
      E.Ts E.order Finset.univ x.1 x.2.extend htape
  have hFreshConfig :
      0 < (FinLaw.pi fun C => X.fresh.fresh C (x.1 C)).w s := by
    change 0 < ∏ C, (X.fresh.fresh C (x.1 C)).w (s C)
    exact Finset.prod_pos (fun C _ => hCellSupport C)
  have hStateInternal := Lane_sol_s18_dl.initial_state_internally_valid
    physical E x hx hTypical
  have hrowPoint (y : Fin (T.S.N k)) :
      ctx.row v (ctx.prior s v) (ctx.label s) y = D.initialWeight v s y := by
    unfold ListGateContext.row LateData.initialWeight
    rw [hExt]
    rw [Finset.prod_image (by
      intro a ha a' ha' heq
      exact hflip heq)]
    simp only [ctx, D, rawData, Lane_sol_s18_dl.physical_list_context,
      ListGateContext.prior, LateData.sigma, ListGateContext.hitRatio,
      ListGateContext.label, LateData.earlyLabel]
    congr 1
  have hrowMass : ctx.rowMass v (ctx.prior s v) (ctx.label s) =
      ∑ y, D.initialWeight v s y := by
    unfold ListGateContext.rowMass
    apply Finset.sum_congr rfl
    intro y hy
    exact hrowPoint y
  have hretMass :
      1 / (4 * (s17Chi (X.palette.code (X.geom.patchOf v)) : ℝ)) ≤
        ∑ y ∈ s17Palette (X.palette.code (X.geom.patchOf v))
          (X.palette.colours (X.geom.patchOf v)) v,
          ctx.row v (ctx.prior s v) (ctx.label s) y := by
    have htypScope : ∀ C ∈ ctx.scopeCells v, X.fresh.typical C (x.1 C) :=
      fun C _ => hTypical C
    have hstateScope : ∀ C ∈ ctx.scopeCells v,
        ctx.stateValid C (x.1 C) (s C) := by
      intro C hC
      letI : Fintype (X.fresh.State C) := X.fresh.stFin C
      change S16.Lane_sol_fix2_s16.InternallyValid X.fresh physical.calibration C
          (x.1 C) (s C) ∧
        0 < (X.fresh.fresh C (x.1 C)).w (s C)
      exact ⟨hStateInternal C, hCellSupport C⟩
    have hrow : (1 / 2 : ℝ) ≤ ctx.rowMass v (ctx.prior s v) (ctx.label s) := by
      rw [hrowMass]
      exact hMass0
    exact (X.retention (X.geom.patchOf v)).2.1 x.1 s v htypScope hstateScope
      (X.geom.patchOf_leaf v) heven hrow
  have hInternal := hFreshInternal PT hPT X hMass hLarge x.1 s hTypical
    hFreshConfig v heven
  have hPalette : D.palette v =
      s17Palette (X.palette.code (X.geom.patchOf v))
        (X.palette.colours (X.geom.patchOf v)) v := by
    change X.palette.palettes (X.geom.patchOf v) (X.palette.colourOf v) = _
    rw [X.palette.palettes_eq, X.palette.colour_eq]
    simp [s17Palette, ListGateContext.PaletteCode.palette]
  have hChi : D.chi (D.geom.patchOf v) = s17Chi (X.palette.code (X.geom.patchOf v)) := by
    change X.palette.chi (X.geom.patchOf v) = _
    exact X.palette.chi_eq (X.geom.patchOf v)
  have hPaletteMass :
      1 / (4 * (D.chi (D.geom.patchOf v) : ℝ)) ≤
        ∑ y ∈ D.palette v, D.initialWeight v s y := by
    calc
      _ = 1 / (4 * (s17Chi (X.palette.code (X.geom.patchOf v)) : ℝ)) := by
        rw [hChi]
      _ ≤ ∑ y ∈ s17Palette (X.palette.code (X.geom.patchOf v))
          (X.palette.colours (X.geom.patchOf v)) v,
          ctx.row v (ctx.prior s v) (ctx.label s) y := hretMass
      _ = ∑ y ∈ D.palette v, D.initialWeight v s y := by
        rw [hPalette]
        apply Finset.sum_congr rfl
        intro y hy
        exact hrowPoint y
  exact ⟨hInternal, hnotFail, hPaletteMass⟩

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
