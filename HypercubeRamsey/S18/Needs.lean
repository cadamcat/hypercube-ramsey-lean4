import HypercubeRamsey.PartC.LateProcess
import HypercubeRamsey.Framework.Embedding

/-!
# Section 18 interfaces supplied by earlier sections

These are copies of exports not yet present on this branch.  The quantitative
validity predicate is the shared input from L16.1: its slot lower bound is the
audited `K_cell n^A_c / d` bound, together with a valid fresh-cell sampler and
nonempty permutation-pool support.
-/

namespace HypercubeRamsey
namespace S18

open Filter

/-- SHARED: L16.1 quantitative facts consumed by the resampling and late-process nodes. -/
structure L16QuantitativeValidity {κ : CConsts} {T : Stage} {k : ℕ}
    {PT : ProfiledTiling κ T k} (G : LowGeom PT) (F : FreshCell G) : Prop where
  pools_nonempty : (permPools G).Nonempty
  slot_lower : ∀ C, κ.Kcell * (T.S.n k : ℝ) ^ κ.Ac ≤
    (G.nslot C : ℝ) * (PT.tiling.P (G.cellPatch C)).d
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

/-- The fixed cluster threshold used for the separated group queries
(18:1118–1123). This was absent from the generic QCond interface. -/
def LateThresholds (κ : CConsts) : Prop :=
  Real.exp (100 * κ.Kbd) + 100 * rowMeanConstant κ + κ.A0 ≤ κ.KB ∧
  ∀ h : ℕ, Real.rpow (κ.M1 * κ.Q0) κ.Mlo ≤ (h : ℝ) → 2 < 20 * κ.ρ * h

/-- C12.K with the further fixed threshold choice used in Section 18.
No stage index or endpoint tuple occurs before the constant choice. -/
theorem exists_late_constants (T : Stage) (η0 : ℝ) (hη0 : 0 < η0)
    (hDeep : ∀ ε : ℝ, 0 < ε → ∃ x α : ℝ, 0 < x ∧ 0 < α ∧ DeepDisc T x α ε) :
    ∃ κ : CConsts, κ.Admissible ∧ κ.η0 = η0 ∧ LateThresholds κ ∧
      DeepDisc T κ.xs κ.α 0.04 ∧ DeepDisc T κ.xι κ.αι (κ.ι / 2) := by
  sorry

/-- P13.2 cleaning removes less than a fixed small fraction at each
active corner (Section 13:273–278); bare ProfiledTiling.Valid omits size. -/
def ProfileCornerMass {κ : CConsts} {T : Stage} {k : ℕ}
    (PT : ProfiledTiling κ T k) : Prop :=
  ∀ i v, v ∈ PT.activeVertices → ((PT.tiling.P i).M : ℝ) ≤ 2 * (PT.mesh.corner v i).card

/-- SHARED: L16.1's quantitative validity is available eventually on every valid low-mode profile. -/
theorem l16_quantitative_validity {κ : CConsts} (hκ : κ.Admissible) (T : Stage)
    (hInit : InitDisc T κ.η0)
    (hDeep : ∀ ε : ℝ, 0 < ε → ∃ x α : ℝ, 0 < x ∧ 0 < α ∧ DeepDisc T x α ε) :
    ∀ᶠ k in atTop, ∀ PT : ProfiledTiling κ T k, PT.Valid → PT.tiling.mode.isLow → ProfileCornerMass PT →
      ∃ G : LowGeom PT, ∃ F : FreshCell G, L16QuantitativeValidity G F := by
  sorry

/-- SHARED: C14.F copied interface for profiled tilings, with the Section 16 inputs forwarded to it. -/
theorem profiled_tiling_exists {κ : CConsts} (hκ : κ.Admissible) (T : Stage)
    (hInit : InitDisc T κ.η0)
    (hDeep : ∀ ε : ℝ, 0 < ε → ∃ x α : ℝ, 0 < x ∧ 0 < α ∧ DeepDisc T x α ε)
    (hClu : ∀ (ζ δ : ℚ), 0 < ζ → 0 < δ → (δ : ℝ) < min κ.η0 (min (ζ : ℝ) 1) / 2000 →
      ∀ (c : Colour) (o : Bool), ∀ᶠ k in atTop,
        ¬ ClusterWitnessAt (T.orient o) k c ζ δ) :
    ∀ᶠ k in atTop, ∃ o : Bool, ∃ PT : ProfiledTiling κ (T.orient o) k, PT.Valid ∧ ProfileCornerMass PT := by
  sorry

/-- SHARED: F-swap, moving a monochromatic cube copy across a transposed relation. -/
theorem cube_copy_of_transpose {N n : ℕ} (E : Fin N → Fin N → Prop) (c : Colour)
    (h : Nonempty ((OAI.HypercubeRamsey.cube n).Copy
      (OAI.HypercubeRamsey.crossGraph (Hits (transposeRel E) c)))) :
    Nonempty ((OAI.HypercubeRamsey.cube n).Copy
      (OAI.HypercubeRamsey.crossGraph (Hits E c))) := by
  exact copy_transpose E c h

/-- SHARED: L15.1 high-direct cube conclusion. -/
theorem high_direct_cube {κ : CConsts} (hκ : κ.Admissible) (T : Stage)
    (hInit : InitDisc T κ.η0)
    (hDeep : ∀ ε : ℝ, 0 < ε → ∃ x α : ℝ, 0 < x ∧ 0 < α ∧ DeepDisc T x α ε) :
    ∀ᶠ k in atTop, ∀ PT : ProfiledTiling κ T k, PT.Valid →
      PT.tiling.mode = .highDirect → CubeIn T k PT.tiling.c := by
  sorry

/-- SHARED: C15.F high-cluster cube conclusion. -/
theorem high_cluster_cube {κ : CConsts} (hκ : κ.Admissible) (T : Stage)
    (hInit : InitDisc T κ.η0)
    (hDeep : ∀ ε : ℝ, 0 < ε → ∃ x α : ℝ, 0 < x ∧ 0 < α ∧ DeepDisc T x α ε) :
    ∀ᶠ k in atTop, ∀ PT : ProfiledTiling κ T k, PT.Valid →
      (PT.tiling.mode = .highSmall ∨ PT.tiling.mode = .highLarge) →
        CubeIn T k PT.tiling.c := by
  sorry

/-- Transfer of initial discrepancy across the two orientations. -/
theorem orient_init {T : Stage} {η : ℝ} (h : InitDisc T η) (o : Bool) :
    InitDisc (T.orient o) η := by
  sorry

/-- Transfer of the full deep-discrepancy regime across the two orientations. -/
theorem orient_deep {T : Stage}
    (h : ∀ ε : ℝ, 0 < ε → ∃ x α : ℝ, 0 < x ∧ 0 < α ∧ DeepDisc T x α ε) (o : Bool) :
    ∀ ε : ℝ, 0 < ε → ∃ x α : ℝ, 0 < x ∧ 0 < α ∧ DeepDisc (T.orient o) x α ε := by
  sorry

/-- The particular budgets returned by C12.K also transport to the swap. -/
theorem orient_deep_budget {T : Stage} {x α ε : ℝ}
    (h : DeepDisc T x α ε) (o : Bool) : DeepDisc (T.orient o) x α ε := by
  sorry

end S18
end HypercubeRamsey
