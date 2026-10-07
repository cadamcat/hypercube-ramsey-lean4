import HypercubeRamsey.PartC.Cleaning
import HypercubeRamsey.PartC.SliceSolver

/-!
# Section 14 profiled tiling interface (D14.P)

A profiled tiling fixes the comparison laws, active cleaned corners, their
envelopes, and the internal solvers at one parameter point. In cluster modes
its validity records the conclusions of Proposition 14.2 (sections/14 lines
170–216): the comparison laws are the solver outputs at the parameter point
(`π⁰ᵢ` in high modes, the conditioned and pretrimmed `π^out_i` in low cluster
mode), `πraw` is the unrestricted mean `π⁰ᵢ`, and the low-mode total-variation
estimate compares the two. In direct and bounded modes the laws are uniform and
the envelope is the single cleaned support (sections/14 line 229).
-/

namespace HypercubeRamsey

open Classical
open scoped BigOperators

/-- Tiling together with comparison laws and the corner data fixed by profiling. -/
structure ProfiledTiling (κ : CConsts) (T : Stage) (k : ℕ) where
  tiling : Tiling κ T k
  mesh : Mesh tiling
  parameter : mesh.Param
  π : Fin tiling.m → Law (T.S.N k)
  πraw : Fin tiling.m → Law (T.S.N k)
  envelope : Fin tiling.m → Finset (Fin (T.S.N k))
  solver : ∀ i, Option (SliceSolver κ tiling i mesh)
  tvError : Fin tiling.m → ℝ

namespace ProfiledTiling

/-- Vertices with positive barycentric weight at the selected parameter. -/
noncomputable def activeVertices {κ : CConsts} {T : Stage} {k : ℕ}
    (PT : ProfiledTiling κ T k) : Finset PT.mesh.V :=
  Finset.univ.filter fun v => 0 < PT.mesh.wt v PT.parameter

/-- Validity of the cleaned profiles passed from Sections 14 to Sections 15–18. -/
structure Valid {κ : CConsts} {T : Stage} {k : ℕ}
    (PT : ProfiledTiling κ T k) : Prop where
  tiling_valid : Tiling.Valid PT.tiling
  /-- The comparison laws are the law component of the parameter point. -/
  param_law : ∀ i, PT.π i = PT.mesh.paramLaw PT.parameter i
  law_supported : ∀ i, (PT.π i).SupportedIn (PT.tiling.P i).Y
  law_uniform_direct : (PT.tiling.mode.isCluster) ∨
    ∀ i, PT.π i = Law.unifCore (PT.tiling.P i).Y (tiling_valid.patch_nonempty i).2
  /-- eq:source-16. -/
  law_cap : ∀ i y, (PT.π i).w y ≤ 11 / (PT.tiling.P i).M
  tv_error_eq : ∀ i, PT.tvError i =
    (1 / 2 : ℝ) * ∑ y, |(PT.πraw i).w y - (PT.π i).w y|
  envelope_eq : ∀ i, PT.envelope i =
    (PT.activeVertices.biUnion fun v => PT.mesh.corner v i)
  corner_clean : ∀ i v, v ∈ PT.activeVertices →
    CleanProps PT.tiling i PT.π (PT.mesh.corner v i)
  /-- In direct and bounded modes one cleaned support is used (`σ_v` is uniform on it). -/
  direct_single_corner : ¬ PT.tiling.mode.isCluster → PT.activeVertices.card = 1
  envelope_subset : ∀ i, PT.envelope i ⊆ (PT.tiling.P i).X
  envelope_degree : ∀ i x, x ∈ PT.envelope i → OwnDegOK PT.tiling i (PT.π i) x
  envelope_other_degree : ∀ i j, j ≠ i → ∀ x ∈ PT.envelope i,
    |deg (T.S.E k) PT.tiling.c (PT.π j).w x - 1 / 2| ≤ 3 * bstar T k
  envelope_row_tail : ∀ i j, ∀ x ∈ PT.envelope i,
    RowTailRelaxed (T.S.E k) PT.tiling.c (PT.π j).w
      (PT.tiling.P i).X (T.S.n k) κ.ξ x
  cluster_solver : PT.tiling.mode.isCluster → ∀ i, ∃ S, PT.solver i = some S
  /-- `πraw` is the unrestricted mean odd law `π⁰ᵢ` of the solver (any group, by (S7)). -/
  raw_profile : PT.tiling.mode.isCluster → ∀ i (S : SliceSolver κ PT.tiling i PT.mesh),
    PT.solver i = some S → ∀ g y, (PT.πraw i).w y = S.oddMean PT.parameter g y
  raw_direct : ¬ PT.tiling.mode.isCluster → ∀ i, PT.πraw i = PT.π i
  /-- High cluster modes: `πᵢ = π^out_i = π⁰ᵢ` (fixed point of P14.2). -/
  high_profile : (PT.tiling.mode = .highSmall ∨ PT.tiling.mode = .highLarge) →
    ∀ i, PT.π i = PT.πraw i
  /-- Low cluster mode: `πᵢ = π^out_i`, the conditioned and pretrimmed mean, for every group. -/
  low_profile : PT.tiling.mode = .lowCluster → ∀ i (S : SliceSolver κ PT.tiling i PT.mesh),
    PT.solver i = some S → ∀ g y, (PT.π i).w y = S.lowOut PT.parameter g y
  tv_error_nonneg : ∀ i, 0 ≤ PT.tvError i
  /-- P14.2(iii): `‖π⁰ᵢ − πᵢ‖_TV ≤ exp(−h^{1+c₁₄}) + 2h²√εᵢ` in low cluster mode. -/
  low_profile_tv : PT.tiling.mode = .lowCluster → ∀ i,
    PT.tvError i ≤
      Real.exp (-Real.rpow ((PT.tiling.P i).h : ℝ) (1 + κ.c14)) +
        2 * (PT.tiling.P i).h ^ 2 * Real.sqrt (sliceEps κ (PT.tiling.P i).h)

/-- A convenience projection of the chosen patch tiling. -/
abbrev tilingOf {κ : CConsts} {T : Stage} {k : ℕ}
    (PT : ProfiledTiling κ T k) := PT.tiling

end ProfiledTiling

end HypercubeRamsey
