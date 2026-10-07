import HypercubeRamsey.S18.Lists
import HypercubeRamsey.S17.Nodes

namespace HypercubeRamsey.S18
open Classical
open scoped BigOperators

variable {κ : CConsts} {T : Stage} {k : ℕ} {PT : ProfiledTiling κ T k}
  {hPT : PT.Valid}

/-- D18.L's equation (24) input (TeX 17:303–333), consumed by P18.5d
at TeX 18:1079–1083. Only supported own-cell readouts from typical pools
are quantified, matching S17's actual-prior provenance. No typicality or
support restriction is imposed on the other cells of the configuration.
Producers choose the positive `Krow` before the eventual index, uniformly
over profiles, palettes, roles, pools, readouts and envelope labels. -/
def PaletteRowInput (D : LateData hPT) (Krow : ℝ) : Prop :=
  ∀ v, IsEvenRole v → ∀ s, D.internalValid v s →
    ∀ P : D.fresh.Pool (D.geom.cellOf v),
      D.fresh.typical (D.geom.cellOf v) P →
      0 < (D.fresh.fresh (D.geom.cellOf v) P).w (s (D.geom.cellOf v)) →
    ∀ x ∈ PT.envelope (D.geom.patchOf v),
      (∑ z ∈ D.palette v,
        if D.nonconflict v x z then
          D.sigma v s z * ∏ a ∈ D.externalEarly v,
            externalPairFactor (PT := PT) (D.geom.patchOf (flipPos v a)) x z
        else 0) ≤ Krow / (D.chi (D.geom.patchOf v) : ℝ)

namespace Lane_sol_bridge_5d

/-- P18.4a changes the late kernels only. The palette-row input concerns
the unchanged fresh prior, geometry and palette (TeX 18:810–825,1079–1083). -/
theorem paletteRowInput_withKernels (D : LateData hPT)
    (K : LateKernels D.encoding.base) (Krow : ℝ) :
    PaletteRowInput (D.withKernels K) Krow ↔ PaletteRowInput D Krow :=
  Iff.rfl

end Lane_sol_bridge_5d
end HypercubeRamsey.S18
