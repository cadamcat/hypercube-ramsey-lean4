import HypercubeRamsey.PartC.Cleaning
import HypercubeRamsey.PartC.SliceSolver

/-!
# Section 14 profiled tiling interface (D14.P)

A profiled tiling fixes the comparison laws, active cleaned corners, their
envelopes, and the internal solvers at one parameter point.
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
  solver : ∀ i, Option (SliceSolver κ tiling i mesh parameter)
  tvError : Fin tiling.m → ℝ

namespace ProfiledTiling

/-- Vertices with positive barycentric weight at the selected parameter. -/
noncomputable def activeVertices {κ : CConsts} {T : Stage} {k : ℕ}
    (PT : ProfiledTiling κ T k) : Finset PT.mesh.V := by
  letI := PT.mesh.vFin
  exact Finset.univ.filter fun v => 0 < PT.mesh.wt v PT.parameter

/-- Validity of the cleaned profiles passed from Sections 14 to Sections 15–18. -/
structure Valid {κ : CConsts} {T : Stage} {k : ℕ}
    (PT : ProfiledTiling κ T k) : Prop where
  tiling_valid : Tiling.Valid PT.tiling
  law_supported : ∀ i, (PT.π i).SupportedIn (PT.tiling.P i).Y
  law_uniform_direct : (PT.tiling.mode.isCluster) ∨
    ∀ i, PT.π i = Law.unifCore (PT.tiling.P i).Y (tiling_valid.patch_nonempty i).2
  law_cap : ∀ i y, (PT.π i).w y ≤ 11 / (PT.tiling.P i).M
  tv_error_eq : ∀ i, PT.tvError i =
    (1 / 2 : ℝ) * ∑ y, |(PT.πraw i).w y - (PT.π i).w y|
  envelope_eq : ∀ i, PT.envelope i =
    (PT.activeVertices.biUnion fun v => PT.mesh.corner v i)
  corner_clean : ∀ i v, v ∈ PT.activeVertices →
    CleanProps PT.tiling i PT.π (PT.mesh.corner v i)
  envelope_subset : ∀ i, PT.envelope i ⊆ (PT.tiling.P i).X
  envelope_degree : ∀ i x, x ∈ PT.envelope i → OwnDegOK PT.tiling i (PT.π i) x
  envelope_other_degree : ∀ i j, j ≠ i → ∀ x ∈ PT.envelope i,
    |deg (T.S.E k) PT.tiling.c (PT.π j).w x - 1 / 2| ≤ 3 * bstar T k
  envelope_row_tail : ∀ i j, ∀ x ∈ PT.envelope i,
    RowTailRelaxed (T.S.E k) PT.tiling.c (PT.π j).w
      (PT.tiling.P i).X (T.S.n k) κ.ξ x
  cluster_solver : PT.tiling.mode.isCluster → ∀ i, ∃ S, PT.solver i = some S
  tv_error_nonneg : ∀ i, 0 ≤ PT.tvError i
  low_profile_tv : PT.tiling.mode = .lowCluster → ∀ i,
    PT.tvError i ≤
      Real.exp (-Real.rpow ((PT.tiling.P i).h : ℝ) (1 + κ.c14)) +
        2 * (PT.tiling.P i).h ^ 2 * Real.sqrt (sliceEps κ (PT.tiling.P i).h)

/-- A convenience projection of the chosen patch tiling. -/
abbrev tilingOf {κ : CConsts} {T : Stage} {k : ℕ}
    (PT : ProfiledTiling κ T k) := PT.tiling

end ProfiledTiling

end HypercubeRamsey
