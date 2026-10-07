import HypercubeRamsey.S18.Endpoints
import HypercubeRamsey.S17.Nodes

namespace HypercubeRamsey.S18.Lane_sol_s18_5d
open Classical Filter
open scoped BigOperators

variable {κ : CConsts} {T : Stage} {k : ℕ} {PT : ProfiledTiling κ T k}
  {hPT : PT.Valid}

/-- The Section 17 equation (24) input consumed at TeX 18:1079–1083.
Only supported own-cell readouts from typical pools are needed. This is
an upstream palette estimate, before fresh-cell integration; it is not
currently a field of `LateData.Spec`. -/
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

/-- Proposed repaired conclusion, not a proof of the frozen theorem.
The theorem's parameters must include `Krow` and its positivity; `Krow`
is fixed before the eventual stage, profile and late-data quantifiers. -/
def P18_5dRepair (κ : CConsts) (T : Stage) (Krow : ℝ) : Prop :=
  ∃ KI : ℝ, 1 ≤ KI ∧ ∀ᶠ k in atTop,
    ∀ PT : ProfiledTiling κ T k, ∀ hPT : PT.Valid, ∀ D : LateData hPT,
      D.Spec → PaletteRowInput D Krow → IsolateKernelFacts D KI

/-- The palette producer must export this together with its selected data,
with a positive constant chosen before the stage index. -/
def PaletteOutput (D : LateData hPT) (Krow : ℝ) : Prop :=
  D.Spec ∧ PaletteRowInput D Krow

end HypercubeRamsey.S18.Lane_sol_s18_5d
