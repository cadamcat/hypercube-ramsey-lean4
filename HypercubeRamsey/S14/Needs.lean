import HypercubeRamsey.S14.Construction

namespace HypercubeRamsey.S14

/-- SHARED: the constants producer must provide strict exponent slack and the
fixed dimension inequalities in `HeightConstantContract.threshold_slack`, as
well as the global and forced-present L3.8 estimates. Positivity of c14 and h0
in the present `CConsts.Admissible` is insufficient (TeX 45, 68, 155, 167).
This contract is an upstream obligation, not a theorem of this skeleton. -/
abbrev RequiredHeightConstants (κ : CConsts) := HeightConstantContract κ

/-- SHARED: stable cleaning must retain at least M/2 first labels at each
charged corner, and the mesh producer must realize a nonempty parameter
domain. `CleanProps` supplies nonemptiness and codegrees but has no mass
field; `Mesh` permits an empty parameter domain. See TeX 9–14, 132, 223. -/
abbrev RequiredMeshInputs {κ : CConsts} {T : Stage} {k : ℕ}
    {𝒯 : Tiling κ T k} (mesh : Mesh 𝒯) := MeshReady mesh

/-- SHARED: the Section 12 initial discrepancy conclusion must be threaded
through P14.1 and P14.2. Stage alone does not carry eq:source-2; the one-list
argument explicitly uses it at TeX 64. -/
abbrev RequiredListDiscrepancy (κ : CConsts) (T : Stage) := InitDisc T κ.η0

end HypercubeRamsey.S14
