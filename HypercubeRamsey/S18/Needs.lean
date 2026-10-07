import HypercubeRamsey.PartC.LateProcess
import HypercubeRamsey.Framework.Embedding
import HypercubeRamsey.S15.DirectNodes
import HypercubeRamsey.S15.ClusterNodes

/-!
# Section 18 interfaces supplied by earlier sections

The high-mode contracts are direct copies of the named Section 15 exports on
main. The constant, profile and joint geometry/fresh-sampler contracts remain
integration obligations: their docstrings record the missing producer inputs.
In particular, positivity or bare profile validity does not supply them.
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
  /-- S16.CellPartitionFacts.slot_count (16:98–115). Nonempty permutation
  support alone allows a cell to read a macroscopic fraction of its bins. -/
  slot_eq : ∀ C, G.nslot C =
    ⌈κ.Kcell * Real.rpow (T.S.n k : ℝ) κ.Ac /
      (PT.tiling.P (G.cellPatch C)).d⌉₊
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
No stage index or endpoint tuple occurs before the constant choice.

Producer: `HypercubeRamsey.exists_admissible` on main, followed by fixed
numerical widening. It returns the other four conjuncts. Enlarge Q0 to at least
max 1 (1/ρ), choose a dyadic Qbd larger than both the old Qbd and M1*Q0, and
enlarge Kbd to at least exp(Cstar u ξ * Qbd). Enlarge KB to cover its old value
and exp(100*Kbd) + 100*rowMeanConstant + A0, then reduce β to the minimum of its
old value and .02/(1 + KB + 2*A0). QCond does not read the four updated fields
Q0/Qbd/Kbd/KB or β; its threshold is transported by increasing Q0. The new
Qbd/Kbd pay the bounded conditions, and all other admissibility fields and the
selected discrepancy widths are preserved. Since M1 ≥ 4 and Mlo ≥ 1, the new
Q0 ensures 20ρh > 2 on the specified height range. This is a numerical bridge,
not a claim that the original witness already has the threshold conjunct.
It does not supply the inherited c14/h0/cChernoff producer contracts. -/
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

/-- L16.1's quantitative validity, including its specified slot count.

Producer gap: `S16.late_classes_and_cell_inputs` returns a
`LowGeometryCertificate` from `LowModeQuantFacts` and uniform dimension/host
cutoffs. Its `cell_partition.slot_count` discharges `slot_eq` by projection.
`S16.Lane_sol_fix2_s16.fresh_cell_spec_exists` supplies the fresh specification
only after raw, permission, restricted-kernel, diagnostic and calibrated-stage
inputs and `CellCalibrationScale` are constructed. Neither export takes only
the hypotheses below. A joint bridge also needs those producer inputs; this
eventual combined contract is not discharged by the current exports. -/
theorem l16_quantitative_validity {κ : CConsts} (hκ : κ.Admissible) (T : Stage)
    (hInit : InitDisc T κ.η0)
    (hDeep : ∀ ε : ℝ, 0 < ε → ∃ x α : ℝ, 0 < x ∧ 0 < α ∧ DeepDisc T x α ε)
    (hDisc : DeepDisc T κ.xs κ.α 0.04) :
    ∀ᶠ k in atTop, ∀ PT : ProfiledTiling κ T k, PT.Valid → PT.tiling.mode.isLow → ProfileCornerMass PT →
      ∃ G : LowGeom PT, ∃ F : FreshCell G, L16QuantitativeValidity G F := by
  sorry

/-- C14.F profile extraction, with the selected cleaning budgets retained.

Producer gap: main has no C14.F export constructing an oriented
`ProfiledTiling`. `S14.balanced_profiles` instead returns `BalancedProfile`
on an already-cleaned `MeshReady` mesh, with `HeightConstantContract` as an
input. Its `corner_clean` and main's `CleanProps.card_lower` supply the corner
mass after profiling; the tiling, mesh and height-constant bridge remains
missing. The `OtherPatchDiscrepancyInput` of `S13.stable_cleaning` is exactly
the `hDisc` budget below, while its own-patch budget is `hDiscι`.
The two selected budgets below prevent arbitrary preselected widths, but do
not replace any of these construction inputs. -/
theorem profiled_tiling_exists {κ : CConsts} (hκ : κ.Admissible) (T : Stage)
    (hInit : InitDisc T κ.η0)
    (hDeep : ∀ ε : ℝ, 0 < ε → ∃ x α : ℝ, 0 < x ∧ 0 < α ∧ DeepDisc T x α ε)
    (hDisc : DeepDisc T κ.xs κ.α 0.04)
    (hDiscι : DeepDisc T κ.xι κ.αι (κ.ι / 2))
    (hClu : ∀ (ζ δ : ℚ), 0 < ζ → 0 < δ → (δ : ℝ) < min κ.η0 (min (ζ : ℝ) 1) / 2000 →
      ∀ (c : Colour) (o : Bool), ∀ᶠ k in atTop,
        ¬ ClusterWitnessAt (T.orient o) k c ζ δ) :
    ∀ᶠ k in atTop, ∃ o : Bool, ∃ PT : ProfiledTiling κ (T.orient o) k, PT.Valid ∧ ProfileCornerMass PT := by
  sorry

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

/-- Transfer of initial discrepancy across the two orientations. Bridge:
split `o`, retain the false branch, and use `dens_transpose` and the symmetric
two law-width clauses of `TwoBudgetDisc` in the true branch. No section
producer is required for this definitional framework transport. -/
theorem orient_init {T : Stage} {η : ℝ} (h : InitDisc T η) (o : Bool) :
    InitDisc (T.orient o) η := by
  sorry

/-- Transfer of the full deep-discrepancy regime across the two orientations.
Bridge: retain each x/alpha witness and apply the `orient_deep_budget`
framework transport, leaving epsilon before the existential witnesses. -/
theorem orient_deep {T : Stage}
    (h : ∀ ε : ℝ, 0 < ε → ∃ x α : ℝ, 0 < x ∧ 0 < α ∧ DeepDisc T x α ε) (o : Bool) :
    ∀ ε : ℝ, 0 < ε → ∃ x α : ℝ, 0 < x ∧ 0 < α ∧ DeepDisc (T.orient o) x α ε := by
  sorry

/-- The particular budgets returned by C12.K also transport to the swap.
Bridge: split `o`; `dens_transpose` and the symmetric `TwoBudgetDisc` clauses
transport the fixed x/alpha/epsilon budget in the true branch. -/
theorem orient_deep_budget {T : Stage} {x α ε : ℝ}
    (h : DeepDisc T x α ε) (o : Bool) : DeepDisc (T.orient o) x α ε := by
  sorry

end S18
end HypercubeRamsey
