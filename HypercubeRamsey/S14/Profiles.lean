import HypercubeRamsey.S14.Construction

/-!
# Section 14 balanced profiles and finite low-mode data

The profile proof is split into continuity, pretrim, capped-range, fixed-point,
price-cap and total-variation nodes (P14.2a–f). The export assembles these
nodes after obtaining the solver family from P14.1.
-/

namespace HypercubeRamsey.S14

open Classical
open Filter
open scoped BigOperators

/-- A family of the per-patch solvers produced by P14.1. -/
structure SolverFamily {κ : CConsts} {T : Stage} {k : ℕ}
    (𝒯 : Tiling κ T k) (mesh : Mesh 𝒯) where
  solverAt : ∀ i : Fin 𝒯.m, SolverWitness (𝒯 := 𝒯) (i := i) (mesh := mesh)

/-- Unrestricted profile `π⁰_i(p)` from the mean odd law. -/
noncomputable def rawWeight {κ : CConsts} {T : Stage} {k : ℕ}
    {𝒯 : Tiling κ T k} {mesh : Mesh 𝒯}
    (F : SolverFamily 𝒯 mesh) (p : mesh.Param) (i : Fin 𝒯.m)
    (g : Group 𝒯 i) (y : Fin (T.S.N k)) : ℝ :=
  (F.solverAt i).solver.oddMean p g y

/-- Conditioned and pretrimmed output profile `πᵢ^{out}(p)`. -/
noncomputable def outputWeight {κ : CConsts} {T : Stage} {k : ℕ}
    {𝒯 : Tiling κ T k} {mesh : Mesh 𝒯}
    (F : SolverFamily 𝒯 mesh) (p : mesh.Param) (i : Fin 𝒯.m)
    (g : Group 𝒯 i) (y : Fin (T.S.N k)) : ℝ :=
  if 𝒯.mode = .lowCluster then (F.solverAt i).solver.lowOut p g y
  else (F.solverAt i).solver.oddMean p g y

/-- Continuity of the output profile on the mesh parameter space. -/
def OutputContinuous {κ : CConsts} {T : Stage} {k : ℕ}
    {𝒯 : Tiling κ T k} {mesh : Mesh 𝒯} (F : SolverFamily 𝒯 mesh) : Prop :=
  ∀ i (g : Group 𝒯 i) y, Continuous fun p => outputWeight F p i g y

/-- Mass and conditioning estimates for the low-mode pretrim. -/
structure PretrimFacts {κ : CConsts} {T : Stage} {k : ℕ}
    {𝒯 : Tiling κ T k} {mesh : Mesh 𝒯} (F : SolverFamily 𝒯 mesh) : Prop where
  good_probability : ∀ i p,
    ((F.solverAt i).solver.recLaw p).pr (F.solverAt i).solver.AllGood ≥
      1 - Real.exp (-Real.rpow ((𝒯.P i).h : ℝ) (1 + κ.c14))
  retained_bins : ∀ i W g,
    (F.solverAt i).solver.AllGood W →
      1 - (𝒯.P i).h ^ 2 * Real.sqrt (sliceEps κ (𝒯.P i).h) ≤
        ∑ D ∈ (F.solverAt i).solver.pretrimBins W g, (F.solverAt i).solver.q g W D

/-- The output profiles lie in the capped law domain of D14.M. -/
structure OutputLawFacts {κ : CConsts} {T : Stage} {k : ℕ}
    {𝒯 : Tiling κ T k} {mesh : Mesh 𝒯} (F : SolverFamily 𝒯 mesh) : Prop where
  nonneg : ∀ p i g y, 0 ≤ outputWeight F p i g y
  support : ∀ p i g y, y ∉ (𝒯.P i).Y → outputWeight F p i g y = 0
  sum_one : ∀ p i g, ∑ y, outputWeight F p i g y = 1
  cap : ∀ p i g y,
    (𝒯.P i).M * outputWeight F p i g y ≤
      Real.exp (10 * (𝒯.kScale i : ℝ) * 𝒯.tScale i)

/-- P14.2a: continuity of the conditioned, pretrimmed output law. -/
theorem output_continuous {κ : CConsts} {T : Stage} {k : ℕ}
    {𝒯 : Tiling κ T k} {mesh : Mesh 𝒯} (F : SolverFamily 𝒯 mesh)
    (hconst : HeightConstantContract κ) : OutputContinuous F := by
  sorry

/-- P14.2b: conditioning and bin pretrim retain positive mass, uniformly in
the parameter point. -/
theorem pretrim_well_defined {κ : CConsts} {T : Stage} {k : ℕ}
    {𝒯 : Tiling κ T k} {mesh : Mesh 𝒯} (F : SolverFamily 𝒯 mesh)
    (hconst : HeightConstantContract κ) : PretrimFacts F := by
  sorry

/-- P14.2c: the S1 bounds place every output profile in the capped input
domain, including the low-mode conditioning and pretrim factors. -/
theorem output_in_capped_domain {κ : CConsts} {T : Stage} {k : ℕ}
    {𝒯 : Tiling κ T k} {mesh : Mesh 𝒯} (F : SolverFamily 𝒯 mesh)
    (hpre : PretrimFacts F) : OutputLawFacts F := by
  sorry

/-- A fixed point of the simultaneous output and price-response map. -/
structure ProfileFixedPoint {κ : CConsts} {T : Stage} {k : ℕ}
    {𝒯 : Tiling κ T k} {mesh : Mesh 𝒯} (F : SolverFamily 𝒯 mesh) where
  point : mesh.Param
  fixed_profile : ∀ i (g : Group 𝒯 i) y,
    (mesh.paramLaw point i).w y = outputWeight F point i g y
  price_maximizer : ∀ i,
    ∀ z : Fin (T.S.N k) → ℝ,
      (∀ y, 0 ≤ z y) → (∀ y, y ∉ (𝒯.P i).Y → z y = 0) →
      (∑ y, z y = 1) →
      ∑ y, z y * (mesh.paramLaw point i).w y ≤
        ∑ y, mesh.paramPrice point i y * (mesh.paramLaw point i).w y

/-- P14.2d: Kakutani on the compact convex finite-dimensional parameter
domain gives the simultaneous fixed profile and price maximizers. -/
theorem fixed_point {κ : CConsts} {T : Stage} {k : ℕ}
    {𝒯 : Tiling κ T k} {mesh : Mesh 𝒯} (domain : MeshProfileDomain mesh)
    (F : SolverFamily 𝒯 mesh) (hcont : OutputContinuous F)
    (hpre : PretrimFacts F) (hout : OutputLawFacts F) :
    Nonempty (ProfileFixedPoint F) := by
  sorry

/-- P14.2e: the fixed-point law has maximum atom at most `11/M`, by the
active-mask price bound and the price-maximizer identity. -/
theorem active_price_cap {κ : CConsts} {T : Stage} {k : ℕ}
    {𝒯 : Tiling κ T k} {mesh : Mesh 𝒯} (F : SolverFamily 𝒯 mesh)
    (hpre : PretrimFacts F)
    (p : ProfileFixedPoint F) :
    ∀ i y, (mesh.paramLaw p.point i).w y ≤ 11 / (𝒯.P i).M := by
  sorry

/-- P14.2f: conditioning on the test event and pretrimming bins changes the
unrestricted mean by the stated low-mode total-variation amount. -/
theorem low_mode_tv {κ : CConsts} {T : Stage} {k : ℕ}
    {𝒯 : Tiling κ T k} {mesh : Mesh 𝒯} (F : SolverFamily 𝒯 mesh)
    (hconst : HeightConstantContract κ) (hpre : PretrimFacts F)
    (p : ProfileFixedPoint F) :
    ∀ i, 𝒯.mode = .lowCluster → ∀ g : Group 𝒯 i,
      (1 / 2 : ℝ) * ∑ y,
        |rawWeight F p.point i g y -
          (mesh.paramLaw p.point i).w y| ≤
        Real.exp (-Real.rpow ((𝒯.P i).h : ℝ) (1 + κ.c14)) +
          2 * (𝒯.P i).h ^ 2 * Real.sqrt (sliceEps κ (𝒯.P i).h) := by
  sorry

/-- Active mesh vertices at the selected profile. -/
noncomputable def activeVertices {κ : CConsts} {T : Stage} {k : ℕ}
    {𝒯 : Tiling κ T k} {mesh : Mesh 𝒯} (p : mesh.Param) : Finset mesh.V :=
  Finset.univ.filter fun v => 0 < mesh.wt v p

/-- The union of the cleaned corners used at the selected profile. -/
noncomputable def profileEnvelope {κ : CConsts} {T : Stage} {k : ℕ}
    {𝒯 : Tiling κ T k} {mesh : Mesh 𝒯} (p : mesh.Param) (i : Fin 𝒯.m) :
    Finset (Fin (T.S.N k)) :=
  (activeVertices p).biUnion fun v => mesh.corner v i

/-- All conclusions of Proposition 14.2 at one profile point. -/
structure BalancedProfile {κ : CConsts} {T : Stage} {k : ℕ}
    {𝒯 : Tiling κ T k} {mesh : Mesh 𝒯} (hclean : MeshCleaned mesh) where
  solvers : SolverFamily 𝒯 mesh
  fixedPoint : ProfileFixedPoint solvers
  cap : ∀ i y, (mesh.paramLaw fixedPoint.point i).w y ≤ 11 / (𝒯.P i).M
  corner_clean : ∀ v i, v ∈ activeVertices fixedPoint.point →
    CleanProps 𝒯 i (mesh.paramLaw fixedPoint.point) (mesh.corner v i)
  envelope_subset : ∀ i, profileEnvelope fixedPoint.point i ⊆ (𝒯.P i).X
  envelope_degree : ∀ i x, x ∈ profileEnvelope fixedPoint.point i →
    OwnDegOK 𝒯 i (mesh.paramLaw fixedPoint.point i) x
  envelope_other_degree : ∀ i j, j ≠ i → ∀ x ∈ profileEnvelope fixedPoint.point i,
    |deg (T.S.E k) 𝒯.c (mesh.paramLaw fixedPoint.point j).w x - 1 / 2| ≤ 3 * bstar T k
  envelope_row_tail : ∀ i j, ∀ x ∈ profileEnvelope fixedPoint.point i,
    RowTailRelaxed (T.S.E k) 𝒯.c (mesh.paramLaw fixedPoint.point j).w
      (𝒯.P i).X (T.S.n k) κ.ξ x
  low_tv : ∀ i, 𝒯.mode = .lowCluster → ∀ g : Group 𝒯 i,
    (1 / 2 : ℝ) * ∑ y,
      |rawWeight solvers fixedPoint.point i g y -
        (mesh.paramLaw fixedPoint.point i).w y| ≤
      Real.exp (-Real.rpow ((𝒯.P i).h : ℝ) (1 + κ.c14)) +
        2 * (𝒯.P i).h ^ 2 * Real.sqrt (sliceEps κ (𝒯.P i).h)

/-- Proposition 14.2: balanced patch profiles for every mesh and solver
family in a valid cluster tiling. -/
theorem balanced_profiles (κ : CConsts) (hκ : κ.Admissible)
    (hconst : HeightConstantContract κ) (T : Stage) :
    ∀ᶠ k in atTop, ∀ (𝒯 : Tiling κ T k), Tiling.Valid 𝒯 → 𝒯.mode.isCluster →
      ∀ (mesh : Mesh 𝒯) (hclean : MeshCleaned mesh) (_domain : MeshProfileDomain mesh),
        Nonempty (BalancedProfile (𝒯 := 𝒯) (mesh := mesh) hclean) := by
  have hsolver := internal_slice_solver κ hκ hconst T
  filter_upwards [hsolver] with k hsolver
  intro 𝒯 h𝒯 hcluster mesh hclean _domain
  classical
  let F : SolverFamily 𝒯 mesh := ⟨fun i => Classical.choice (hsolver 𝒯 h𝒯 hcluster mesh hclean i)⟩
  have hcont : OutputContinuous F := output_continuous F hconst
  have hpre : PretrimFacts F := pretrim_well_defined F hconst
  have hout : OutputLawFacts F := output_in_capped_domain F hpre
  obtain ⟨fixed⟩ := fixed_point _domain F hcont hpre hout
  have hcap := active_price_cap F hpre fixed
  have htv := low_mode_tv F hconst hpre fixed
  refine ⟨{
    solvers := F
    fixedPoint := fixed
    cap := hcap
    corner_clean := ?_
    envelope_subset := ?_
    envelope_degree := ?_
    envelope_other_degree := ?_
    envelope_row_tail := ?_
    low_tv := htv
  }⟩
  · intro v i hv
    apply hclean v fixed.point i
    simpa [activeVertices] using hv
  · intro i x hx
    rcases Finset.mem_biUnion.mp hx with ⟨v, hv, hxv⟩
    exact (hclean v fixed.point i (by simpa [activeVertices] using hv)).sub hxv
  · intro i x hx
    rcases Finset.mem_biUnion.mp hx with ⟨v, hv, hxv⟩
    exact (hclean v fixed.point i (by simpa [activeVertices] using hv)).degOwn x hxv
  · intro i j hij x hx
    rcases Finset.mem_biUnion.mp hx with ⟨v, hv, hxv⟩
    exact (hclean v fixed.point i (by simpa [activeVertices] using hv)).degOther j hij x hxv
  · intro i j x hx
    rcases Finset.mem_biUnion.mp hx with ⟨v, hv, hxv⟩
    exact (hclean v fixed.point i (by simpa [activeVertices] using hv)).rowTail j x hxv

/-- L14.3: finite low-mode primitive data at every parameter point. -/
theorem finite_low_mode_data (κ : CConsts) (hκ : κ.Admissible)
    (hconst : HeightConstantContract κ) (T : Stage) :
    ∀ᶠ k in atTop, ∀ (𝒯 : Tiling κ T k), Tiling.Valid 𝒯 →
      𝒯.mode = .lowCluster → ∀ mesh : Mesh 𝒯, MeshCleaned mesh →
        ∀ i : Fin 𝒯.m, ∀ p : mesh.Param,
          ∃ S : SolverWitness (𝒯 := 𝒯) (i := i) (mesh := mesh),
            (((Finset.univ.filter fun W =>
              0 < (S.solver.recLaw p).w W).card : ℕ) : ℝ) ≤
              Real.exp ((T.S.n k : ℝ) ^ (1.01 : ℝ)) := by
  have hsolver := internal_slice_solver κ hκ hconst T
  filter_upwards [hsolver] with k hsolver
  intro 𝒯 h𝒯 hlow mesh hclean i p
  have hcluster : 𝒯.mode.isCluster := by
    rw [hlow]
    simp [Mode.isCluster]
  obtain ⟨S⟩ := hsolver 𝒯 h𝒯 hcluster mesh hclean i
  refine ⟨S, ?_⟩
  exact S.solver.low_support hlow p

end HypercubeRamsey.S14
