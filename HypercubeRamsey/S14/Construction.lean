import HypercubeRamsey.PartC.ProfiledTiling
import HypercubeRamsey.S03.Height.Selection
import HypercubeRamsey.S03.Mixtures
import HypercubeRamsey.S03.GatedPosterior
import HypercubeRamsey.S14.Construction_q_s14_post
import HypercubeRamsey.S14.Construction_sol_s14_lik
import HypercubeRamsey.Framework.FinProbLemmas
import HypercubeRamsey.S14.Construction_q_s14_hist

/-!
# Section 14 internal slice solver

This module records the construction in Section 14 as separate proof nodes.
The primitive record system, odd kernels, even rows and tests are kept as
separate data so the export assembles the existing `SliceSolver` interface
from P14.1a–l rather than hiding that interface in one theorem.
-/

namespace HypercubeRamsey.S14

open Classical
open Filter
open scoped BigOperators

/-- The global-height part of L3.8 at the Section 14 exponents. -/
def Section14GlobalHeightBound (J₀ b₀ b σ ζ c_d C_d c : ℝ)
    (D : ℕ) (reg : HDRegime b₀ b D) (n₀ : ℕ) : Prop :=
  ∀ p : HDParams, p.D = D → p.H = topScale p.n σ ζ →
    p.lam = (p.n : ℝ) ^ J₀ → p.b₀ = b₀ → p.b = b → n₀ ≤ p.n →
    c_d * p.n ≤ p.d → (p.d : ℝ) ≤ C_d * p.n → reg.ok p.n p.d p.r →
    ∀ (Sites : p.Sites) {Aux : Type} [Fintype Aux] (πAux : FinProb Aux)
      (Esel : (p.Loc → Bool) → Aux → p.EligMap),
      ((p.posLaw.prod πAux).prod p.actLaw).pr (fun ω =>
        p.Legal ω.1.1 (Esel ω.1.1 ω.1.2) Sites ∧
          ¬ p.GoodHeights Sites ω.1.1 ω.2 (Esel ω.1.1 ω.1.2)) ≤
        Real.exp (-(p.n : ℝ) ^ (1 + c))

/-- The forced-present positive-height part of L3.8 at the Section 14
exponents. -/
def Section14PositiveHeightBound (J₀ b₀ b σ ζ c_d C_d c : ℝ)
    (D : ℕ) (reg : HDRegime b₀ b D) (n₀ : ℕ) : Prop :=
  ∀ p : HDParams, p.D = D → p.H = topScale p.n σ ζ →
    p.lam = (p.n : ℝ) ^ J₀ → p.b₀ = b₀ → p.b = b → n₀ ≤ p.n →
    c_d * p.n ≤ p.d → (p.d : ℝ) ≤ C_d * p.n → reg.ok p.n p.d p.r →
    ∀ (Sites : p.Sites) (v : CubePos p.d) (_hv : v ∈ Sites)
      (forced : Option p.Loc) {Aux : Type} [Fintype Aux] (πAux : FinProb Aux)
      (Esel : (p.Loc → Bool) → Aux → p.EligMap),
      (((p.posLawForced forced).prod πAux).prod p.actLaw).pr (fun ω =>
        p.Legal ω.1.1 (Esel ω.1.1 ω.1.2) (p.domBall Sites v p.Rlong) ∧
          0 < p.height Sites ω.1.1 ω.2 (Esel ω.1.1 ω.1.2) p.Rlong v) ≤
        Real.exp (-(p.n : ℝ) ^ c)

/-- The exact finite numerical slack needed for the slice union bounds.
Constants and thresholds are fixed before all dimensions and host sizes. -/
def Section14Numerics (κ : CConsts) (cg cp cs : ℝ) (h : ℕ) : Prop :=
  let H := topScale h (κ.ω / 100) (κ.ω / 30)
  let V := ∑ j ∈ Finset.range (⌊κ.ρ * h⌋₊ + 1), Nat.choose h j
  let lam : ℝ := (h : ℝ) ^ 10
  let B : ℝ := (2 * h ^ 3 * lam * (H + 1) + 1) ^ (sliceT κ h + 1)
  2 ≤ h ∧ 0 < sliceK κ h ∧ lam ≤ (V : ℝ) / 2 ∧
  (h : ℝ) ^ (κ.ω / 8) ≤ lam ∧
  12 * (H : ℝ) + 4 * ⌊κ.ρ * h⌋₊ + 6 < 10 * κ.ρ * h ∧
  2 * (h : ℝ) ^ (κ.ω / 2) ≤ sliceT κ h ∧
  4 * (h : ℝ) ^ 4 * sliceT κ h ≤ lam / 4 ∧
  (2 : ℝ) ^ h * (H + 1) * 2 * Real.exp (-lam / 48) ≤
    Real.exp (-Real.rpow (h : ℝ) (1 + cs)) ∧
  (2 : ℝ) ^ h * (B * (2 * (sliceT κ h + 1) *
    Real.exp (-κ.c5 * κ.a ^ 2 * sliceK κ h))) ^ h ≤
    Real.exp (-Real.rpow (h : ℝ) (1 + cs)) ∧
  (2 : ℝ) ^ h * (V : ℝ) * (H + 1) *
    Real.exp (-0.01 * κ.a * sliceK κ h * h) / sliceEps κ h ≤
    Real.exp (-Real.rpow (h : ℝ) (1 + cs)) ∧
  (H + 1) * lam * Real.exp (-Real.rpow (h : ℝ) cp) ≤ 1 ∧
  Real.exp (-(sliceK κ h : ℝ)) + sliceT κ h *
    Real.exp (-0.24 * κ.a * sliceK κ h) ≤ 1 / 2 ∧
  2 * Real.exp (-Real.rpow (h : ℝ) (1 + cg)) +
    4 * Real.exp (-Real.rpow (h : ℝ) (1 + cs)) ≤
      Real.exp (-Real.rpow (h : ℝ) (1 + κ.c14))

/-- The Section 14 specialization of L3.8. Its exponent and threshold
inequalities are the actual global/forced-present outputs of the producing
height node; `CConsts.Admissible` currently lacks their c14/h0 compatibility
fields, which integration should add there. -/
structure HeightConstantContract (κ : CConsts) where
  J₀ : ℝ
  b₀ : ℝ
  b : ℝ
  σ : ℝ
  ζ : ℝ
  θ : ℝ
  a : ℝ
  c_d : ℝ
  C_d : ℝ
  α : ℝ
  admissible : HDAdmissible J₀ b₀ b σ ζ θ a c_d C_d 6
  regime : HDRegime b₀ b 6
  regime_linear : ∃ hρ : 0 < κ.ρ / 2 ∧ κ.ρ / 2 ≤ 1 / 4,
    regime = .lin (κ.ρ / 2) hρ
  exponents_match :
    J₀ = 10 ∧ b₀ = κ.ω / 8 ∧ b = κ.ω / 2 ∧ σ = κ.ω / 100 ∧
      ζ = κ.ω / 30 ∧ θ = 1 - κ.ω / 30 ∧ a = κ.ω / 12 ∧
      c_d = 1 ∧ C_d = 1 ∧ α = 1 / 2
  theta_large : 0.9 < θ
  alpha_range : 0 < α ∧ α < 2 * (1 - ζ)
  globalExponent : ℝ
  globalThreshold : ℕ
  global_exponent_pos : 0 < globalExponent
  global_bound : Section14GlobalHeightBound J₀ b₀ b σ ζ c_d C_d
    globalExponent 6 regime globalThreshold
  global_c14 : κ.c14 < globalExponent
  global_h0 : globalThreshold ≤ κ.h0
  positiveExponent : ℝ
  positiveThreshold : ℕ
  positive_exponent_pos : 0 < positiveExponent
  positive_bound : Section14PositiveHeightBound J₀ b₀ b σ ζ c_d C_d
    positiveExponent 6 regime positiveThreshold
  positive_h0 : positiveThreshold ≤ κ.h0
  sliceExponent : ℝ
  slice_exponent : κ.c14 < sliceExponent ∧ sliceExponent < globalExponent ∧
    sliceExponent < κ.ω / 1000
  threshold_slack : ∀ h : ℕ, κ.h0 ≤ h →
    Section14Numerics κ globalExponent positiveExponent sliceExponent h

/-- The mesh corners are cleaned at every parameter point charged by a
positive mesh weight. This is the stability conclusion of L13.4 at the mesh
scale, used by the slice construction and the profile fixed point. -/
def MeshCleaned {κ : CConsts} {T : Stage} {k : ℕ} {𝒯 : Tiling κ T k}
    (mesh : Mesh 𝒯) : Prop :=
  ∀ (v : mesh.V) (p : mesh.Param) (i : Fin 𝒯.m),
    0 < mesh.wt v p → CleanProps 𝒯 i (mesh.paramLaw p) (mesh.corner v i)

/-- A parameter profile in the capped law and price-simplex domain. -/
structure ParameterProfile {κ : CConsts} {T : Stage} {k : ℕ}
    (𝒯 : Tiling κ T k) where
  law : Fin 𝒯.m → Law (T.S.N k)
  price : Fin 𝒯.m → Fin (T.S.N k) → ℝ
  law_supported : ∀ i, (law i).SupportedIn (𝒯.P i).Y
  law_cap : ∀ i y,
    ((𝒯.P i).M : ℝ) * (law i).w y ≤
      Real.exp (10 * (𝒯.kScale i : ℝ) * 𝒯.tScale i)
  price_simplex : ∀ i,
    (∀ y, 0 ≤ price i y) ∧ (∀ y, y ∉ (𝒯.P i).Y → price i y = 0) ∧
      ∑ y, price i y = 1

/-- Finite-dimensional coordinates of a parameter profile. -/
def ParameterProfile.coordinates {κ : CConsts} {T : Stage} {k : ℕ}
    {𝒯 : Tiling κ T k} (p : ParameterProfile 𝒯) :
    (Fin 𝒯.m → Fin (T.S.N k) → ℝ) × (Fin 𝒯.m → Fin (T.S.N k) → ℝ) :=
  (fun i y => (p.law i).w y, p.price)

noncomputable instance instParameterProfileTop {κ : CConsts} {T : Stage} {k : ℕ}
    {𝒯 : Tiling κ T k} : TopologicalSpace (ParameterProfile 𝒯) :=
  TopologicalSpace.induced ParameterProfile.coordinates inferInstance

/-- A finite-dimensional compact convex realization of the parameter space
on which Kakutani can be applied. Besides the geometric domain, the witness
identifies every point with its law/price profile and realizes every valid
profile back as a mesh parameter. -/
structure MeshProfileDomain {κ : CConsts} {T : Stage} {k : ℕ}
    {𝒯 : Tiling κ T k} (mesh : Mesh 𝒯) where
  dim : ℕ
  carrier : Set (Fin dim → ℝ)
  encode : mesh.Param ≃ carrier
  encode_continuous : Continuous fun p => (encode p : Fin dim → ℝ)
  decode_continuous : Continuous fun x : carrier => encode.symm x
  domain : KuhnDomain dim carrier
  dimension_bound : dim ≤ 2 * T.S.N k
  coordinates : ParameterProfile 𝒯 → Fin dim → ℝ
  coordinates_mem : ∀ p, coordinates p ∈ carrier
  coordinates_continuous : Continuous coordinates
  profileOf : mesh.Param → ParameterProfile 𝒯
  profileOf_law : ∀ p i, (profileOf p).law i = mesh.paramLaw p i
  profileOf_price : ∀ p i y, (profileOf p).price i y = mesh.paramPrice p i y
  profileOf_coordinates : ∀ p,
    encode p = ⟨coordinates (profileOf p), coordinates_mem (profileOf p)⟩
  profileOf_continuous : Continuous profileOf
  realize : ParameterProfile 𝒯 → mesh.Param
  realize_law : ∀ p i, mesh.paramLaw (realize p) i = p.law i
  realize_price : ∀ p i y, mesh.paramPrice (realize p) i y = p.price i y
  realize_coordinates : ∀ p,
    encode (realize p) = ⟨coordinates p, coordinates_mem p⟩
  realize_profileOf : ∀ p, realize (profileOf p) = p
  profileOf_realize : ∀ p, profileOf (realize p) = p
  realize_continuous : Continuous realize

/-- Mesh producer obligations absent from the shared D14.M interface.
Active corner size is the retained-mass conclusion of L13.4, needed for the
prior cap `2/M`; cleaned properties alone do not bound cardinality. -/
structure MeshReady {κ : CConsts} {T : Stage} {k : ℕ}
    {𝒯 : Tiling κ T k} (mesh : Mesh 𝒯) : Prop where
  parameter_nonempty : Nonempty mesh.Param
  corner_size : ∀ v p i, 0 < mesh.wt v p →
    ((𝒯.P i).M : ℝ) / 2 ≤ (mesh.corner v i).card

/-- Host-dependent scalar estimates left after the fixed `h` threshold. -/
structure PatchScales {κ : CConsts} {T : Stage} {k : ℕ}
    (𝒯 : Tiling κ T k) (i : Fin 𝒯.m) : Prop where
  h_large : κ.h0 ≤ (𝒯.P i).h
  n_pos : 0 < T.S.n k
  M_pos : 0 < (𝒯.P i).M
  a_small : κ.a ≤ 1 / 10
  budget : 2 * (𝒯.kScale i : ℝ) * 𝒯.tScale i +
    Real.log ((T.S.N k : ℝ) / (𝒯.P i).M) + 3 ≤ (T.S.n k : ℝ) ^ κ.η0 / 2
  prior_width : 2 / (𝒯.P i).M ≤
    Real.exp ((T.S.n k : ℝ) ^ κ.η0 / 2) / (T.S.N k)
  posterior_allocation : Real.log (2 * (T.S.N k : ℝ) / (𝒯.P i).M) ≤
    0.01 * κ.a * (𝒯.P i).h
  truncation_cap : (200 / κ.a) * 2 ^ (𝒯.P i).h *
    Real.exp (-0.02 * κ.a * (𝒯.P i).h) ≤
      2 ^ (𝒯.P i).h * Real.exp (-500 * 𝒯.gain i)
  pretrim_small : (𝒯.P i).h ^ 2 * Real.sqrt (sliceEps κ (𝒯.P i).h) ≤ 1 / 4
  cap_slack : (32 / 3 : ℝ) * Real.exp (2 * (𝒯.kScale i : ℝ) * 𝒯.tScale i) ≤
    Real.exp (10 * (𝒯.kScale i : ℝ) * 𝒯.tScale i)

/-- Uniform ambient-stage threshold for the scalar estimates. -/
theorem patch_scales (κ : CConsts) (hκ : κ.Admissible) (T : Stage) :
    ∀ᶠ k in atTop, ∀ 𝒯 : Tiling κ T k, Tiling.Valid 𝒯 →
      𝒯.mode.isCluster → ∀ i, PatchScales 𝒯 i := by
  sorry

/-- The group of an odd internal word is obtained from its syndrome-zero
projection. -/
noncomputable def groupNeighborhood {κ : CConsts} {T : Stage} {k : ℕ}
    {𝒯 : Tiling κ T k} {i : Fin 𝒯.m} (g : Group 𝒯 i) : Finset (EvenRole 𝒯 i) := by
  classical
  exact Finset.univ.filter fun v =>
    ∃ l, flipPos v.1 l ∈ groupFiber g

structure ProjectionGeometry (κ : CConsts) {T : Stage} {k : ℕ}
    (𝒯 : Tiling κ T k) (i : Fin 𝒯.m) where
  syndromeIndex : IWord 𝒯 i → Fin (𝒯.P i).h
  syndromeIndex_spec : ∀ z j,
    ((syndromeIndex z).val.testBit j = true ↔ wordSyndrome z j = 1)
  project : IWord 𝒯 i → IWord 𝒯 i
  project_eq : ∀ z, project z = flipPos z (syndromeIndex z)
  project_zero : ∀ z, wordSyndrome (project z) = 0
  groupOf : IWord 𝒯 i → Group 𝒯 i
  groupOf_spec : ∀ z, ¬ IsEvenRole z → z ∈ groupFiber (groupOf z)
  partition : GroupPartition 𝒯 i
  fiber_card : ∀ g : Group 𝒯 i, (groupFiber g).card = (𝒯.P i).h
  multiplicity : EvenRole 𝒯 i → Group 𝒯 i → ℕ
  multiplicity_eq : ∀ v g,
    multiplicity v g =
      (Finset.univ.filter fun l : Fin (𝒯.P i).h =>
        flipPos v.1 l ∈ groupFiber g).card
  multiplicity_lower : ∀ v g, 0 < multiplicity v g → 2 ≤ multiplicity v g
  multiplicity_sum : ∀ v, ∑ g : Group 𝒯 i, multiplicity v g = (𝒯.P i).h
  /-- Sites in a group's neighborhood have pairwise distance at most six. -/
  neighborhood_distance : ∀ (g : Group 𝒯 i) (v v' : EvenRole 𝒯 i),
    v ∈ groupNeighborhood g →
    v' ∈ groupNeighborhood g → hammingDist v.1 v'.1 ≤ 6
  projected_distance : ∀ g (v v' : EvenRole 𝒯 i),
    v ∈ groupNeighborhood g → v' ∈ groupNeighborhood g →
      hammingDist (project v.1) (project v'.1) ≤ 6
  projected_overlap : ∀ x : IWord 𝒯 i,
    ((Finset.univ.filter fun g : Group 𝒯 i =>
      ∃ v ∈ groupNeighborhood g, project v.1 = x).card : ℝ) ≤ (𝒯.P i).h ^ 3
  /-- A site belongs to at most `h^3` group neighborhoods. -/
  neighborhood_overlap : ∀ (v : EvenRole 𝒯 i),
    ((Finset.univ.filter fun g : Group 𝒯 i => v ∈ groupNeighborhood g).card : ℝ) ≤
      (𝒯.P i).h ^ 3

/-- P14.1a: projection geometry, including the partition of odd roles and
the no-singleton incidence bound needed by the posterior calculation. -/
theorem projection_geometry (κ : CConsts) (hκ : κ.Admissible)
    {T : Stage} {k : ℕ} (𝒯 : Tiling κ T k) (h𝒯 : Tiling.Valid 𝒯)
    (hcluster : 𝒯.mode.isCluster) (i : Fin 𝒯.m) :
    Nonempty (ProjectionGeometry κ 𝒯 i) := by
  sorry

/-- The concrete mask law at one mesh vertex (P14.1b). -/
structure MaskFacts {κ : CConsts} {T : Stage} {k : ℕ}
    {𝒯 : Tiling κ T k} (i : Fin 𝒯.m) (mesh : Mesh 𝒯) (v : mesh.V) where
  cheap : Bin 𝒯 i → Finset (Fin (T.S.N k))
  retained : Finset (Bin 𝒯 i)
  prior : Bin 𝒯 i → ℝ
  within : Bin 𝒯 i → Fin (T.S.N k) → ℝ
  cheap_eq : ∀ D,
    cheap D = D.1.filter fun y =>
      mesh.paramPrice (mesh.base v) i y ≤ 10 / (𝒯.P i).M
  cheap_subset : ∀ D, cheap D ⊆ D.1
  cheap_nonempty : ∀ D, D ∈ retained → (cheap D).Nonempty
  retained_nonempty : retained.Nonempty
  cheap_price : ∀ D y, y ∈ cheap D →
    mesh.paramPrice (mesh.base v) i y ≤ 10 / (𝒯.P i).M
  retained_spec : ∀ D, D ∈ retained ↔ 2 * (cheap D).card ≥ (𝒯.P i).d
  prior_nonneg : ∀ D, 0 ≤ prior D
  prior_sum : ∑ D, prior D = 1
  prior_uniform : ∀ D, prior D =
    if D ∈ retained then 1 / (retained.card : ℝ) else 0
  within_nonneg : ∀ D y, 0 ≤ within D y
  within_sum : ∀ D, ∑ y, within D y = 1
  within_support : ∀ D y, within D y ≠ 0 → y ∈ D.1
  within_uniform : ∀ D y, within D y =
    if D ∈ retained then (if y ∈ cheap D then 1 / ((cheap D).card : ℝ) else 0)
    else (if y ∈ D.1 then 1 / (D.1.card : ℝ) else 0)
  expensive_labels :
    (((𝒯.P i).Y.filter fun y =>
      10 / (𝒯.P i).M < mesh.paramPrice (mesh.base v) i y).card : ℝ) ≤
        (𝒯.P i).M / 10
  expensive_bins :
    (((𝒯.P i).bins.parts.filter fun B =>
      ((B.filter fun y =>
        10 / (𝒯.P i).M < mesh.paramPrice (mesh.base v) i y).card : ℝ) >
          (𝒯.P i).d / 2).card : ℝ) ≤
      ((𝒯.P i).bins.parts.card : ℝ) / 5
  prior_cap : ∀ D, prior D ≤ 2 * (𝒯.P i).d / (𝒯.P i).M
  aggregate_masked_mass : ∀ y,
    ∑ D, prior D * within D y ≤ 4 / (𝒯.P i).M
  cleaned_codegree : 𝒯.mode.isCluster → ∀ (p : mesh.Param) (v' : mesh.V),
    0 < mesh.wt v' p → ∀ (D : Bin 𝒯 i)
      (y y' : Fin (T.S.N k)),
    (hy : y ∈ cheap D) → (hy' : y' ∈ cheap D) →
      1 / 4 + κ.a ≤
        (∑ x ∈ mesh.corner v' i,
          hit (T.S.E k) 𝒯.c x y * hit (T.S.E k) 𝒯.c x y') /
          (mesh.corner v' i).card

/-- P14.1b: masks discard at most a tenth of the labels and at most a fifth
of the physical bins. -/
theorem masks_and_price_cut (κ : CConsts) (hκ : κ.Admissible)
    {T : Stage} {k : ℕ} {𝒯 : Tiling κ T k} (h𝒯 : Tiling.Valid 𝒯)
    {i : Fin 𝒯.m} (mesh : Mesh 𝒯) (_hclean : MeshCleaned mesh) (v : mesh.V) :
    Nonempty (MaskFacts i mesh v) := by
  sorry

/-- Convert the shared host-side law to the Part C finite-law wrapper. -/
noncomputable def lawToFinLaw {N : ℕ} (μ : Law N) : FinLaw (Fin N) where
  w := μ.w
  nonneg := μ.nonneg
  sum_one := μ.sum_eq_one

/-- Finite list-test experiment (P14.1c). The hit set and squared bin mass
are defined from the sampled first-side tuples and a finite family of bin
laws. -/
structure ListTestModel (κ : CConsts) {T : Stage} {k : ℕ}
    (𝒯 : Tiling κ T k) (i : Fin 𝒯.m) where
  Id : Type
  [idFin : Fintype Id]
  [idDecEq : DecidableEq Id]
  idNonempty : Nonempty Id
  binPrior : FinProb (Bin 𝒯 i)
  binDist : Bin 𝒯 i → Law (T.S.N k)
  firstLaw : Id → Law (T.S.N k)
  bin_support : ∀ b, (binDist b).SupportedIn b.1
  first_law_supported : ∀ c, (firstLaw c).SupportedIn (T.X k)
  /-- Each candidate has one independent tuple with `k` coordinates. -/
  aggregate_cap : ∀ y,
    ∑ b, binPrior.w b * (binDist b).w y ≤ 4 / (𝒯.P i).M
  width_bound : ∀ c x,
    (firstLaw c).w x ≤ Real.exp ((T.S.n k : ℝ) ^ κ.η0 / 2) / (T.S.N k)
  codegree_bound : ∀ c b y y', binPrior.w b > 0 →
    (binDist b).w y ≠ 0 → (binDist b).w y' ≠ 0 →
    (1 / 4 : ℝ) + κ.a ≤
      ∑ x, (firstLaw c).w x * hit (T.S.E k) 𝒯.c x y * hit (T.S.E k) 𝒯.c x y'
  /-- The budget used by the clipped-log Azuma argument. -/
  budget : 2 * (𝒯.kScale i : ℝ) * (Fintype.card Id : ℝ) +
    Real.log ((T.S.N k : ℝ) / (𝒯.P i).M) + 3 ≤
      (T.S.n k : ℝ) ^ κ.η0 / 2

namespace ListTestModel

variable {κ : CConsts} {T : Stage} {k : ℕ} {𝒯 : Tiling κ T k} {i : Fin 𝒯.m}

instance instIdFintype (L : ListTestModel κ 𝒯 i) : Fintype L.Id := L.idFin
instance instIdDecidableEq (L : ListTestModel κ 𝒯 i) : DecidableEq L.Id := L.idDecEq

/-- Product law of the independent candidate tuples. -/
noncomputable def tupleLaw (L : ListTestModel κ 𝒯 i) :
    FinLaw (∀ _c : L.Id, Fin (𝒯.kScale i) → Fin (T.S.N k)) := by
  classical
  exact FinLaw.pi fun c => FinLaw.pi fun _ => lawToFinLaw (L.firstLaw c)

/-- Labels hit by every tuple entry in the list. -/
noncomputable def hitSet (L : ListTestModel κ 𝒯 i)
    (w : ∀ _c : L.Id, Fin (𝒯.kScale i) → Fin (T.S.N k)) : Finset (Fin (T.S.N k)) := by
  classical
  exact Finset.univ.filter fun y =>
    ∀ c : L.Id, ∀ r : Fin (𝒯.kScale i), Hits (T.S.E k) 𝒯.c (w c r) y

/-- Hit set after deleting one candidate tuple. -/
noncomputable def hitSetDelete (L : ListTestModel κ 𝒯 i)
    (w : ∀ _c : L.Id, Fin (𝒯.kScale i) → Fin (T.S.N k)) (c₀ : L.Id) :
    Finset (Fin (T.S.N k)) := by
  classical
  exact Finset.univ.filter fun y =>
    ∀ c : L.Id, c ≠ c₀ → ∀ r : Fin (𝒯.kScale i),
      Hits (T.S.E k) 𝒯.c (w c r) y

/-- Squared masked mass `A(J)=E_D D(J)^2`. -/
noncomputable def mass (L : ListTestModel κ 𝒯 i) (J : Finset (Fin (T.S.N k))) : ℝ :=
  ∑ b, L.binPrior.w b * (∑ y ∈ J, (L.binDist b).w y) ^ 2

/-- A list passes the absolute and deletion inequalities. The deletion
inequality is written after cross multiplication, with no division by a
possibly zero denominator. -/
def Good (L : ListTestModel κ 𝒯 i)
    (w : ∀ _c : L.Id, Fin (𝒯.kScale i) → Fin (T.S.N k)) : Prop :=
  L.mass (L.hitSet w) ≥ Real.exp (-2 * (𝒯.kScale i : ℝ) * Fintype.card L.Id) ∧
    ∀ c₀, L.mass (L.hitSet w) ≥
      Real.exp ((-Real.log 4 + 0.4 * κ.a) * (𝒯.kScale i : ℝ)) *
        L.mass (L.hitSetDelete w c₀)

/-- Failure probability for one list. -/
noncomputable def Failure (L : ListTestModel κ 𝒯 i)
    (w : ∀ _c : L.Id, Fin (𝒯.kScale i) → Fin (T.S.N k)) : Prop := ¬ L.Good w

end ListTestModel

/-- P14.1c: the one-list bound, uniformly at sufficiently large stage indices.
The small-width discrepancy estimate is the paper's eq:source-2 (TeX 64). -/
def GenericListBound (κ : CConsts) {T : Stage} {k : ℕ}
    (𝒯 : Tiling κ T k) (i : Fin 𝒯.m) : Prop :=
  ∀ L : ListTestModel κ 𝒯 i, Fintype.card L.Id ≤ 𝒯.tScale i → κ.a ≤ 1 / 10 →
    L.tupleLaw.pr L.Failure ≤ 2 * (𝒯.tScale i + 1 : ℝ) *
      Real.exp (-κ.c5 * κ.a ^ 2 * (𝒯.kScale i : ℝ))

theorem generic_list_test (κ : CConsts) (hκ : κ.Admissible)
    (T : Stage) (hinit : InitDisc T κ.η0) :
    ∀ᶠ k in atTop, ∀ 𝒯 : Tiling κ T k, Tiling.Valid 𝒯 → ∀ i, GenericListBound κ 𝒯 i := by
  sorry

/-- L3.8 parameters with ambient dimension `h`, not the host dimension `n`. -/
noncomputable def patchHD (κ : CConsts) (h : ℕ) : HDParams where
  n := h
  d := h
  D := 6
  r := ⌊κ.ρ * h⌋₊
  H := topScale h (κ.ω / 100) (κ.ω / 30)
  lam := (h : ℝ) ^ 10
  b₀ := κ.ω / 8
  b := κ.ω / 2

/-- Nonempty lists of at most `T` potential centers. Empty realized lists use
fallbacks; they are never forced into a nonempty list-test model. -/
def SmallList (p : HDParams) (t : ℕ) :=
  {S : Finset p.Loc // S.Nonempty ∧ S.card ≤ t}

noncomputable instance instSmallListFintype (p : HDParams) (t : ℕ) :
    Fintype (SmallList p t) := by
  classical
  unfold SmallList
  exact Fintype.ofFinite _

/-- Search priorities are categorical permutations of the finite list universe. -/
abbrev SearchPerm (p : HDParams) (t : ℕ) :=
  Equiv.Perm (Fin (Fintype.card (SmallList p t)))

/-- Primitive data contain only the corner priors. Every position, activation,
mask, tuple and independent order below is a concrete coordinate of a product
record law, not an arbitrary function with unspecified distribution. -/
structure PrimitiveHistory (κ : CConsts) {T : Stage} {k : ℕ}
    (𝒯 : Tiling κ T k) (i : Fin 𝒯.m) (mesh : Mesh 𝒯) where
  prior : mesh.V → Law (T.S.N k)
  prior_support : ∀ v, (prior v).SupportedIn (𝒯.P i).X
  prior_uniform : ∀ v p, 0 < mesh.wt v p → ∀ x,
    (prior v).w x = if x ∈ mesh.corner v i then (1 : ℝ) / ((mesh.corner v i).card : ℝ) else 0
  prior_cap : ∀ v p, 0 < mesh.wt v p → ∀ x, (prior v).w x ≤ 2 / (𝒯.P i).M

namespace PrimitiveHistory

variable {κ : CConsts} {T : Stage} {k : ℕ} {𝒯 : Tiling κ T k}
  {i : Fin 𝒯.m} {mesh : Mesh 𝒯}

noncomputable abbrev Device (H : PrimitiveHistory κ 𝒯 i mesh) := patchHD κ (𝒯.P i).h
abbrev Center (H : PrimitiveHistory κ 𝒯 i mesh) := H.Device.Loc
abbrev Tuple (H : PrimitiveHistory κ 𝒯 i mesh) := Fin (𝒯.kScale i) → Fin (T.S.N k)

/-- Independent records: one center record, one group record, one site-level
choice-order record. A center record combines its corner, tuple and two bits;
their conditional independence is specified by `centerLaw`. -/
abbrev Rec (H : PrimitiveHistory κ 𝒯 i mesh) :=
  H.Center ⊕ (Group 𝒯 i ⊕ H.Center)

abbrev Val (H : PrimitiveHistory κ 𝒯 i mesh) : H.Rec → Type
  | .inl _ => mesh.V × (H.Tuple × (Bool × Bool))
  | .inr (.inl _) => mesh.V × SearchPerm H.Device (𝒯.tScale i)
  | .inr (.inr _) => H.Device.TiePerm

noncomputable instance (priority := 2000) instRecDecidableEq
    (H : PrimitiveHistory κ 𝒯 i mesh) : DecidableEq H.Rec := Classical.decEq _

noncomputable instance instRecFintype (H : PrimitiveHistory κ 𝒯 i mesh) : Fintype H.Rec :=
  inferInstance
noncomputable instance instValFintype (H : PrimitiveHistory κ 𝒯 i mesh) :
    ∀ r, Fintype (H.Val r) := fun r => by cases r with
  | inl c => dsimp [Val]; infer_instance
  | inr r => cases r <;> dsimp [Val] <;> infer_instance

/-- The location of each record is its center, group center or queried site. -/
def loc (H : PrimitiveHistory κ 𝒯 i mesh) : H.Rec → IWord 𝒯 i
  | .inl c => c.1
  | .inr (.inl g) => g.1
  | .inr (.inr c) => c.1

/-- Convert a finite probability wrapper without changing its weights. -/
def finProbToFinLaw {Ω : Type*} [Fintype Ω] (P : FinProb Ω) : FinLaw Ω :=
  ⟨P.w, P.nonneg, P.sum_eq_one⟩

noncomputable def vertexLaw (p : mesh.Param) : FinLaw mesh.V :=
  ⟨fun v => mesh.wt v p, fun v => mesh.wt_nonneg v p, mesh.wt_sum_one p⟩

noncomputable def tuplePrior (H : PrimitiveHistory κ 𝒯 i mesh) (v : mesh.V) :
    FinLaw H.Tuple := FinLaw.pi fun _ => lawToFinLaw (H.prior v)

/-- Independent corner-conditioned tuple, position and activation draws. -/
noncomputable def centerLaw (H : PrimitiveHistory κ 𝒯 i mesh) (p : mesh.Param) :
    FinLaw (mesh.V × (H.Tuple × (Bool × Bool))) :=
  FinLaw.bind (vertexLaw p) fun v =>
    FinLaw.bind (H.tuplePrior v) fun _ =>
      FinLaw.bind (finProbToFinLaw (FinProb.bernoulli (H.Device.lam / H.Device.V)))
        fun _ => finProbToFinLaw (FinProb.bernoulli
          ((H.Device.n : ℝ) ^ H.Device.b₀ / H.Device.lam))

/-- A group's mask and its search order are independent draws. -/
noncomputable def groupLaw (H : PrimitiveHistory κ 𝒯 i mesh) (p : mesh.Param) :
    FinLaw (mesh.V × SearchPerm H.Device (𝒯.tScale i)) :=
  FinLaw.bind (vertexLaw p) fun _ =>
    finProbToFinLaw (FinProb.uniformAll ⟨1⟩)

noncomputable def tieLaw (H : PrimitiveHistory κ 𝒯 i mesh) : FinLaw H.Device.TiePerm :=
  finProbToFinLaw (FinProb.uniformAll ⟨1⟩)

noncomputable def record (H : PrimitiveHistory κ 𝒯 i mesh) (p : mesh.Param) :
    ∀ r, FinLaw (H.Val r)
  | .inl _ => H.centerLaw p
  | .inr (.inl _) => H.groupLaw p
  | .inr (.inr _) => H.tieLaw

noncomputable def lawRec (H : PrimitiveHistory κ 𝒯 i mesh) (p : mesh.Param) :
    ∀ r, H.Val r → ℝ := fun r => (H.record p r).w
noncomputable def recLaw (H : PrimitiveHistory κ 𝒯 i mesh) (p : mesh.Param) :
    FinLaw (∀ r, H.Val r) := by
  classical
  exact recordLaw (H.lawRec p) (fun r => (H.record p r).nonneg)
    (fun r => (H.record p r).sum_one)

def cornerOf (H : PrimitiveHistory κ 𝒯 i mesh) (W : ∀ r, H.Val r) (c : H.Center) : mesh.V :=
  (W (.inl c)).1
def tuple (H : PrimitiveHistory κ 𝒯 i mesh) (W : ∀ r, H.Val r) (c : H.Center) : H.Tuple :=
  (W (.inl c)).2.1
def present (H : PrimitiveHistory κ 𝒯 i mesh) (W : ∀ r, H.Val r) (c : H.Center) : Bool :=
  (W (.inl c)).2.2.1
def active (H : PrimitiveHistory κ 𝒯 i mesh) (W : ∀ r, H.Val r) (c : H.Center) : Bool :=
  (W (.inl c)).2.2.2
def maskVertex (H : PrimitiveHistory κ 𝒯 i mesh) (g : Group 𝒯 i) (W : ∀ r, H.Val r) : mesh.V :=
  (W (.inr (.inl g))).1
def searchOrder (H : PrimitiveHistory κ 𝒯 i mesh) (g : Group 𝒯 i) (W : ∀ r, H.Val r) :
    SearchPerm H.Device (𝒯.tScale i) := (W (.inr (.inl g))).2
def ties (H : PrimitiveHistory κ 𝒯 i mesh) (W : ∀ r, H.Val r) : H.Device.Ties :=
  fun c => W (.inr (.inr c))

/-- Vary only the tuple; retain its corner, presence and activation bits. -/
noncomputable def replaceTuple (H : PrimitiveHistory κ 𝒯 i mesh) (W : ∀ r, H.Val r)
    (c : H.Center) (w : H.Tuple) : ∀ r, H.Val r :=
  Function.update W (.inl c) ((H.cornerOf W c), (w, H.present W c, H.active W c))

end PrimitiveHistory

/-- P14.1d seed: choose fixed uniform corner priors (arbitrary unused corners
use the patch's uniform first law). No draw exists over an empty mesh. -/
theorem primitive_history (κ : CConsts) (hκ : κ.Admissible)
    {T : Stage} {k : ℕ} (𝒯 : Tiling κ T k) (h𝒯 : Tiling.Valid 𝒯)
    (hcluster : 𝒯.mode.isCluster) (i : Fin 𝒯.m) (mesh : Mesh 𝒯)
    (hclean : MeshCleaned mesh) (ready : MeshReady mesh) :
    Nonempty (PrimitiveHistory κ 𝒯 i mesh) := by
  classical
  let prior : mesh.V → Law (T.S.N k) := fun v =>
    if hv : ∃ p, 0 < mesh.wt v p then
      Law.unifCore (mesh.corner v i)
        (hclean v (Classical.choose hv) i (Classical.choose_spec hv)).nonempty
    else
      Law.unifCore (𝒯.P i).X (h𝒯.patch_nonempty i).1
  have hMpos_nat : 0 < (𝒯.P i).M := by
    have hXpos : 0 < (𝒯.P i).X.card := Finset.card_pos.mpr (h𝒯.patch_nonempty i).1
    simpa only [(𝒯.P i).cardX] using hXpos
  have hMpos : (0 : ℝ) < (𝒯.P i).M := by exact_mod_cast hMpos_nat
  have huniform (v : mesh.V) (p : mesh.Param) (hv : 0 < mesh.wt v p)
      (x : Fin (T.S.N k)) :
      (prior v).w x =
        if x ∈ mesh.corner v i then (1 : ℝ) / ((mesh.corner v i).card : ℝ) else 0 := by
    have hactive : ∃ p', 0 < mesh.wt v p' := ⟨p, hv⟩
    simp [prior, hactive, Law.unifCore]
  refine ⟨{
    prior := prior
    prior_support := by
      intro v x hx
      by_cases hv : ∃ p, 0 < mesh.wt v p
      · have hsub := (hclean v (Classical.choose hv) i (Classical.choose_spec hv)).sub
        have hxcorner : x ∉ mesh.corner v i := fun hmem => hx (hsub hmem)
        simp [prior, hv, Law.unifCore, hxcorner]
      · simp [prior, hv, Law.unifCore, hx]
    prior_uniform := by
      intro v p hp x
      exact huniform v p hp x
    prior_cap := by
      intro v p hp x
      rw [huniform v p hp x]
      by_cases hx : x ∈ mesh.corner v i
      · rw [if_pos hx]
        have hcard : ((𝒯.P i).M : ℝ) / 2 ≤ (mesh.corner v i).card :=
          ready.corner_size v p i hp
        calc
          (1 : ℝ) / (mesh.corner v i).card ≤ 1 / ((𝒯.P i).M / 2) :=
            one_div_le_one_div_of_le (by positivity) hcard
          _ = 2 / (𝒯.P i).M := by field_simp
      · simp only [if_neg hx]
        exact div_nonneg (show (0 : ℝ) ≤ (2 : ℝ) by norm_num) hMpos.le
  }⟩

/-- Continuity is proved for the concrete product law, rather than assumed
for arbitrary tuple/position/activation decoders. -/
theorem primitive_law_continuous {κ : CConsts} {T : Stage} {k : ℕ}
    {𝒯 : Tiling κ T k} {i : Fin 𝒯.m} {mesh : Mesh 𝒯}
    (H : PrimitiveHistory κ 𝒯 i mesh) :
    ∀ r x, Continuous fun p => H.lawRec p r x := by
  classical
  intro r x
  cases r with
  | inl c =>
      rcases x with ⟨v, ⟨w, ⟨b₁, b₂⟩⟩⟩
      simp only [PrimitiveHistory.lawRec, PrimitiveHistory.record,
        PrimitiveHistory.centerLaw, FinLaw.bind, PrimitiveHistory.vertexLaw,
        PrimitiveHistory.tuplePrior, lawToFinLaw, FinLaw.pi,
        PrimitiveHistory.finProbToFinLaw, FinProb.bernoulli]
      have hcont : Continuous (mesh.wt v) := Mesh.wt_cont mesh v
      fun_prop
  | inr r =>
      cases r with
      | inl g =>
          rcases x with ⟨v, σ⟩
          simp only [PrimitiveHistory.lawRec, PrimitiveHistory.record,
            PrimitiveHistory.groupLaw, FinLaw.bind, PrimitiveHistory.vertexLaw,
            PrimitiveHistory.finProbToFinLaw, FinProb.uniformAll]
          have hcont : Continuous (mesh.wt v) := Mesh.wt_cont mesh v
          fun_prop
      | inr c =>
          simp only [PrimitiveHistory.lawRec, PrimitiveHistory.record,
            PrimitiveHistory.tieLaw, PrimitiveHistory.finProbToFinLaw,
            FinProb.uniformAll]
          fun_prop

set_option maxHeartbeats 5000000
set_option maxRecDepth 4096
/-- L14.3 count node, separate from the eligibility theorem. It counts actual
positive product-record outcomes, including categorical order permutations. -/
theorem primitive_low_support (κ : CConsts) (hκ : κ.Admissible) (T : Stage) :
    ∀ᶠ k in atTop, ∀ (𝒯 : Tiling κ T k), Tiling.Valid 𝒯 →
      𝒯.mode = .lowCluster → ∀ i mesh (H : PrimitiveHistory κ 𝒯 i mesh) p,
        (((Finset.univ.filter fun W => 0 < (H.recLaw p).w W).card : ℕ) : ℝ) ≤
          Real.exp ((T.S.n k : ℝ) ^ (1.01 : ℝ)) := by
  classical
  have hlogT : Tendsto (fun k => Real.log (T.S.n k : ℝ)) atTop atTop :=
    Real.tendsto_log_atTop.comp (tendsto_natCast_atTop_atTop.comp T.S.n_tendsto)
  have htLarge : ∀ᶠ k in atTop, 1000 ≤ Real.log (T.S.n k : ℝ) :=
    hlogT.eventually_ge_atTop 1000
  have htTiny : ∀ᶠ k in atTop,
      1000000 * (Real.log (T.S.n k : ℝ)) ^ (0.3 : ℝ) ≤ Real.log (T.S.n k : ℝ) := by
    have h := hlogT.eventually (Lane_q_s14_hist.eventually_const_mul_rpow_le_rpow
      (a := (0.3 : ℝ)) (b := 1) (c := 1000000) (by norm_num) (by norm_num))
    filter_upwards [h] with k hk
    simpa [Real.rpow_one] using hk
  filter_upwards [htLarge, htTiny] with k htLarge htTiny
  intro 𝒯 h𝒯 hlow i mesh H p
  let n : ℝ := T.S.n k
  let t : ℝ := Real.log n
  have ht : 1000 ≤ t := by simpa [t, n] using htLarge
  have ht1 : 1 ≤ t := by linarith
  have htPow : 1000000 * t ^ (0.3 : ℝ) ≤ t := by simpa [t, n] using htTiny
  have hNpos : 0 < T.S.N k := T.S.N_pos k
  have hnpos : 0 < T.S.n k := by
    by_contra hzero
    have hz : T.S.n k = 0 := by omega
    have hfalse : ¬ (1000 : ℝ) ≤ 0 := by norm_num
    exact hfalse (by simpa [hz] using htLarge)
  have hNcast : (0 : ℝ) < T.S.N k := by exact_mod_cast hNpos
  have hncast : (0 : ℝ) < T.S.n k := by exact_mod_cast hnpos
  have hlogN : Real.log (T.S.N k : ℝ) ≤ 2 * n := by
    have hNle : (T.S.N k : ℝ) ≤ (T.S.n k : ℝ) * 2 ^ (T.S.n k) := by
      exact_mod_cast T.S.N_le k
    have hlog : Real.log (T.S.N k : ℝ) ≤
        Real.log ((T.S.n k : ℝ) * 2 ^ (T.S.n k)) := Real.log_le_log hNcast hNle
    have hlogn : Real.log (T.S.n k : ℝ) ≤ T.S.n k := by
      simpa [Real.rpow_one] using
        Real.log_natCast_le_rpow_div (T.S.n k) (by norm_num : (0 : ℝ) < 1)
    have hlogtwo : Real.log (2 : ℝ) ≤ 1 := by
      exact (Real.log_le_iff_le_exp (by norm_num)).2 Real.exp_one_gt_two.le
    rw [Real.log_mul (ne_of_gt hncast) (by positivity), Real.log_pow] at hlog
    dsimp [n]
    nlinarith

  have hcluster := h𝒯.cluster_data (Or.inl hlow) i
  rcases hcluster with
    ⟨_, _, _, _, _, _, _, hqLower, hhUpper, hlowIff, _, _⟩
  have hqUpper : (𝒯.P i).q ≤ Real.rpow t κ.cq := by
    have h := hlowIff.mp hlow
    simpa [t, n] using h
  have hMloPos : (0 : ℝ) < κ.Mlo := by
    have haC := hκ.aC_rng.1
    have haB := hκ.aB_rng.1
    have hCb : 100 < κ.Cb := by
      have hfrac : 0 < 100 * κ.aC / κ.aB := by positivity
      linarith [hκ.Cb_big]
    have hMlo : κ.Cb + 100 < (κ.Mlo : ℝ) := hκ.Mlo_big
    linarith
  have hcqMlo : κ.cq * (κ.Mlo : ℝ) < 1 / 20 := by
    have hcq := hκ.cq_rng.2
    calc
      κ.cq * (κ.Mlo : ℝ) < (1 / (20 * (κ.Mlo : ℝ))) * (κ.Mlo : ℝ) :=
        mul_lt_mul_of_pos_right hcq hMloPos
      _ = 1 / 20 := by field_simp [ne_of_gt hMloPos]
  have hqPow : Real.rpow ((𝒯.P i).q : ℝ) κ.Mlo ≤ Real.rpow t (1 / 20 : ℝ) := by
    calc
      Real.rpow ((𝒯.P i).q : ℝ) (κ.Mlo : ℝ) ≤
          Real.rpow (Real.rpow t κ.cq) (κ.Mlo : ℝ) := by
        apply Real.rpow_le_rpow (by positivity) hqUpper
        exact le_of_lt hMloPos
      _ = Real.rpow t (κ.cq * (κ.Mlo : ℝ)) := by
        exact (Real.rpow_mul (by linarith : 0 ≤ t) κ.cq (κ.Mlo : ℝ)).symm
      _ ≤ Real.rpow t (1 / 20 : ℝ) :=
        Real.rpow_le_rpow_of_exponent_le (by linarith) hcqMlo.le
  have hh : ((𝒯.P i).h : ℝ) < 2 * Real.rpow ((𝒯.P i).q : ℝ) κ.Mlo := by
    simpa [hlow] using hhUpper
  have hhSmall : ((𝒯.P i).h : ℝ) < 2 * Real.rpow t (1 / 20 : ℝ) := by
    exact lt_of_lt_of_le hh (mul_le_mul_of_nonneg_left hqPow (by norm_num))
  have hOmegaSmall : κ.ω < 1 / 5 := by
    have hMhi : 1 ≤ (κ.Mhi : ℝ) := by
      have hcq : 0 < κ.cq := hκ.cq_rng.1
      have hsum : 0 < (κ.Mlo : ℝ) + 10 / κ.cq := by positivity
      have hmhi : 0 < (κ.Mhi : ℝ) := lt_of_lt_of_le hsum hκ.Mhi_big.1
      exact_mod_cast (Nat.succ_le_iff.mpr (by exact_mod_cast hmhi))
    have hω := hκ.ω_rng.2
    have hωle : 5 * κ.ω ≤ 5 * κ.ω * (κ.Mhi : ℝ) := by
      nlinarith [hκ.ω_rng.1, hMhi]
    have hden : 0 < (10 : ℝ) ^ 6 := by positivity
    have hmin : min κ.η0 1 ≤ 1 := min_le_right _ _
    have hscaled : min κ.η0 1 / (10 : ℝ) ^ 6 ≤ 1 := by
      apply (div_le_iff₀ hden).2
      nlinarith
    have haCsmall : κ.aC < 1 := lt_of_lt_of_le hκ.aC_rng.2 hscaled
    nlinarith [hω, hωle, haCsmall]
  have hheightK : 3 * κ.ω ≤ 1 := by nlinarith [hOmegaSmall]
  have hheightT : κ.ω ≤ 1 := by linarith [hOmegaSmall]
  have hscale_le (a : ℝ) (ha0 : 0 < a) (ha : a ≤ 1) :
      ⌈Real.rpow ((𝒯.P i).h : ℝ) a⌉₊ ≤ (𝒯.P i).h + 1 := by
    have hp : Real.rpow ((𝒯.P i).h : ℝ) a ≤ (𝒯.P i).h + 1 := by
      by_cases hzero : (𝒯.P i).h = 0
      · simp [hzero, Real.zero_rpow ha0.ne']
      · have hbase : 1 ≤ (𝒯.P i).h := by omega
        calc
          Real.rpow ((𝒯.P i).h : ℝ) a ≤ Real.rpow ((𝒯.P i).h : ℝ) 1 :=
            Real.rpow_le_rpow_of_exponent_le (by exact_mod_cast hbase) ha
          _ = (𝒯.P i).h := Real.rpow_one _
          _ ≤ (𝒯.P i).h + 1 := by norm_num
    apply Nat.ceil_le.mpr
    exact_mod_cast hp
  have hK : 𝒯.kScale i ≤ (𝒯.P i).h + 1 := by
    change sliceK κ (𝒯.P i).h ≤ (𝒯.P i).h + 1
    exact hscale_le (3 * κ.ω) (by positivity [hκ.ω_rng.1]) hheightK
  have hTscale : 𝒯.tScale i ≤ (𝒯.P i).h + 1 := by
    change sliceT κ (𝒯.P i).h ≤ (𝒯.P i).h + 1
    exact hscale_le κ.ω hκ.ω_rng.1 hheightT
  let active : Finset mesh.V := Finset.univ.filter fun v => 0 < mesh.wt v p
  let A := active.card
  let L := Fintype.card H.Center
  let tupleCount := Fintype.card H.Tuple
  let listCount := Fintype.card (SmallList H.Device (𝒯.tScale i))
  let orderCount := Fintype.card (SearchPerm H.Device (𝒯.tScale i))
  let tiePermCount := Fintype.card H.Device.TiePerm
  let B := 4 * (A + 1) * (tupleCount + 1) * (orderCount + 1) * (tiePermCount + 1)
  have hActiveCard : A ≤ 2 * T.S.N k + 1 := by
    simpa [A, active] using mesh.active_bound p
  have hLocCard : L = 2 ^ (𝒯.P i).h * (H.Device.H + 1) := by
    calc
      L = Fintype.card H.Center := rfl
      _ = Fintype.card H.Device.Loc := rfl
      _ = Fintype.card
          (OAI.HypercubeRamsey.CubeVertex (𝒯.P i).h × Fin (H.Device.H + 1)) := by
            rfl
      _ = Fintype.card (OAI.HypercubeRamsey.CubeVertex (𝒯.P i).h) *
          Fintype.card (Fin (H.Device.H + 1)) := by
            simp only [Fintype.card_prod]
      _ = 2 ^ (𝒯.P i).h * (H.Device.H + 1) := by
          simp [OAI.HypercubeRamsey.card_cubeVertex]
  have hLocPos : 0 < L := by
    rw [hLocCard]
    positivity
  have hTop : H.Device.H ≤
      ((𝒯.P i).h + 2) ^ ((𝒯.P i).h + 1) * ((𝒯.P i).h ^ 2 + 1) := by
    exact Lane_q_s14_hist.topScale_le_nat_bound (𝒯.P i).h
      (κ.ω / 100) (κ.ω / 30)
      (div_pos hκ.ω_rng.1 (by norm_num))
      (by have hω := hκ.ω_rng.1; nlinarith)
      (by have hω := hOmegaSmall; nlinarith)
  have hHplus : H.Device.H + 1 ≤
      2 * (((𝒯.P i).h + 2) ^ ((𝒯.P i).h + 1) * ((𝒯.P i).h ^ 2 + 1)) := by
    have hpowpos : 1 ≤ ((𝒯.P i).h + 2) ^ ((𝒯.P i).h + 1) := by
      exact Nat.one_le_pow _ _ (by omega)
    have hpolypos : 1 ≤ (𝒯.P i).h ^ 2 + 1 := by omega
    have hfactor : 1 ≤
        ((𝒯.P i).h + 2) ^ ((𝒯.P i).h + 1) * ((𝒯.P i).h ^ 2 + 1) := by
      calc
        1 = 1 * 1 := by norm_num
        _ ≤ _ := Nat.mul_le_mul hpowpos hpolypos
    omega
  have hhBound : ((𝒯.P i).h : ℝ) ≤ 2 * t ^ (0.1 : ℝ) := by
    calc
      ((𝒯.P i).h : ℝ) ≤ 2 * t ^ (1 / 20 : ℝ) := hhSmall.le
      _ ≤ 2 * t ^ (0.1 : ℝ) := by
        gcongr
        linarith
  have hlogL : Real.log (L : ℝ) ≤ 30 * t ^ (0.2 : ℝ) := by
    have hlogH : Real.log ((H.Device.H + 1 : ℕ) : ℝ) ≤
        1 + ((𝒯.P i).h + 1 : ℝ) * ((𝒯.P i).h + 2 : ℝ) +
          Real.log ((𝒯.P i).h ^ 2 + 1 : ℝ) := by
      have hHpos : (0 : ℝ) < ((H.Device.H + 1 : ℕ) : ℝ) := by positivity
      let qNat : ℕ := ((𝒯.P i).h + 2) ^ ((𝒯.P i).h + 1) * ((𝒯.P i).h ^ 2 + 1)
      have hBound : ((H.Device.H + 1 : ℕ) : ℝ) ≤
          2 * (((𝒯.P i).h + 2 : ℕ) : ℝ) ^ ((𝒯.P i).h + 1) *
            (((𝒯.P i).h ^ 2 + 1 : ℕ) : ℝ) := by
        calc
          ((H.Device.H + 1 : ℕ) : ℝ) ≤ ((2 * qNat : ℕ) : ℝ) := by
            exact_mod_cast (by simpa [qNat] using hHplus)
          _ = 2 * (((𝒯.P i).h + 2 : ℕ) : ℝ) ^ ((𝒯.P i).h + 1) *
                (((𝒯.P i).h ^ 2 + 1 : ℕ) : ℝ) := by
            simp [qNat, Nat.cast_mul, Nat.cast_pow]
            ring
      have hlogBound := Real.log_le_log hHpos hBound
      rw [Real.log_mul (by positivity) (by positivity),
        Real.log_mul (by norm_num : (2 : ℝ) ≠ 0) (by positivity), Real.log_pow] at hlogBound
      push_cast at hlogBound
      have hlogBound' : Real.log ((H.Device.H + 1 : ℕ) : ℝ) ≤
          Real.log 2 + ((𝒯.P i).h + 1 : ℝ) * Real.log ((𝒯.P i).h + 2 : ℝ) +
            Real.log ((𝒯.P i).h ^ 2 + 1 : ℝ) := by
        simpa [Nat.cast_add, Nat.cast_pow] using hlogBound
      have hlogTwo : Real.log 2 ≤ 1 := by
        exact (Real.log_le_iff_le_exp (by norm_num)).2 Real.exp_one_gt_two.le
      have hlogHbase : Real.log ((𝒯.P i).h + 2 : ℝ) ≤ (𝒯.P i).h + 2 := by
        calc
          Real.log ((𝒯.P i).h + 2 : ℝ) ≤ ((𝒯.P i).h + 2 : ℝ) - 1 :=
            Real.log_le_sub_one_of_pos (by positivity)
          _ ≤ (𝒯.P i).h + 2 := by linarith
      have hlogHprod : ((𝒯.P i).h + 1 : ℝ) * Real.log ((𝒯.P i).h + 2 : ℝ) ≤
          ((𝒯.P i).h + 1 : ℝ) * ((𝒯.P i).h + 2 : ℝ) :=
        mul_le_mul_of_nonneg_left hlogHbase (by positivity)
      calc
        Real.log ((H.Device.H + 1 : ℕ) : ℝ) ≤
            Real.log 2 + ((𝒯.P i).h + 1 : ℝ) * Real.log ((𝒯.P i).h + 2 : ℝ) +
              Real.log ((𝒯.P i).h ^ 2 + 1 : ℝ) := hlogBound'
        _ ≤ 1 + ((𝒯.P i).h + 1 : ℝ) * ((𝒯.P i).h + 2 : ℝ) +
              Real.log ((𝒯.P i).h ^ 2 + 1 : ℝ) := by
          exact add_le_add (add_le_add hlogTwo hlogHprod) le_rfl
    rw [hLocCard, Nat.cast_mul, Nat.cast_pow, Real.log_mul (by positivity) (by positivity),
      Real.log_pow]
    have hlogTwo : Real.log 2 ≤ 1 := by
      exact (Real.log_le_iff_le_exp (by norm_num)).2 Real.exp_one_gt_two.le
    have hpow1 : 1 ≤ t ^ (0.1 : ℝ) := by
      simpa using Real.rpow_le_rpow_of_exponent_le ht1 (by norm_num : (0 : ℝ) ≤ 0.1)
    have hpow2 : 1 ≤ t ^ (0.2 : ℝ) := by
      simpa using Real.rpow_le_rpow_of_exponent_le ht1 (by norm_num : (0 : ℝ) ≤ 0.2)
    have hh1 : (𝒯.P i).h + 1 ≤ 3 * t ^ (0.1 : ℝ) := by
      have hcast : ((𝒯.P i).h : ℝ) + 1 ≤ 2 * t ^ (0.1 : ℝ) + 1 := by linarith [hhBound]
      calc
        ((𝒯.P i).h : ℝ) + 1 ≤ 2 * t ^ (0.1 : ℝ) + 1 := hcast
        _ ≤ 3 * t ^ (0.1 : ℝ) := by nlinarith [hpow1]
    have hh2 : ((𝒯.P i).h : ℝ) + 2 ≤ 4 * t ^ (0.1 : ℝ) := by
      have hcast : ((𝒯.P i).h : ℝ) + 2 ≤ 2 * t ^ (0.1 : ℝ) + 2 := by linarith [hhBound]
      calc
        ((𝒯.P i).h : ℝ) + 2 ≤ 2 * t ^ (0.1 : ℝ) + 2 := hcast
        _ ≤ 4 * t ^ (0.1 : ℝ) := by nlinarith [hpow1]
    have hprod : (((𝒯.P i).h : ℝ) + 1) * (((𝒯.P i).h : ℝ) + 2) ≤
        12 * t ^ (0.2 : ℝ) := by
      have hmul := mul_le_mul hh1 hh2 (by positivity) (by positivity)
      have hpowMul : t ^ (0.1 : ℝ) * t ^ (0.1 : ℝ) = t ^ (0.2 : ℝ) := by
        rw [← Real.rpow_add (by linarith : 0 < t)]
        congr 1
        ring
      calc
        _ ≤ (3 * t ^ (0.1 : ℝ)) * (4 * t ^ (0.1 : ℝ)) := hmul
        _ = 12 * (t ^ (0.1 : ℝ) * t ^ (0.1 : ℝ)) := by ring
        _ = 12 * t ^ (0.2 : ℝ) := by rw [hpowMul]
    have hlogBase : Real.log ((𝒯.P i).h + 2 : ℝ) ≤ 4 * t ^ (0.1 : ℝ) := by
      have hlog : Real.log ((𝒯.P i).h + 2 : ℝ) ≤ (𝒯.P i).h + 2 := by
        calc
          Real.log ((𝒯.P i).h + 2 : ℝ) ≤ ((𝒯.P i).h + 2 : ℝ) - 1 :=
            Real.log_le_sub_one_of_pos (by positivity)
          _ ≤ (𝒯.P i).h + 2 := by linarith
      exact hlog.trans (by linarith [hh2])
    have hlogPoly : Real.log ((𝒯.P i).h ^ 2 + 1 : ℝ) ≤ 5 * t ^ (0.2 : ℝ) := by
      have hnat : Real.log ((𝒯.P i).h ^ 2 + 1 : ℝ) ≤ (𝒯.P i).h ^ 2 + 1 := by
        calc
          Real.log ((𝒯.P i).h ^ 2 + 1 : ℝ) ≤ ((𝒯.P i).h ^ 2 + 1 : ℝ) - 1 :=
            Real.log_le_sub_one_of_pos (by positivity)
          _ ≤ (𝒯.P i).h ^ 2 + 1 := by linarith
      have hhBound' : ((𝒯.P i).h : ℝ) ≤ 2 * t ^ (0.1 : ℝ) := hhBound
      have hpowMul : t ^ (0.1 : ℝ) * t ^ (0.1 : ℝ) = t ^ (0.2 : ℝ) := by
        rw [← Real.rpow_add (by linarith : 0 < t)]
        congr 1
        ring
      have hsq : ((𝒯.P i).h : ℝ) ^ 2 ≤ 4 * t ^ (0.2 : ℝ) := by
        have hdiff : ((𝒯.P i).h : ℝ) - 2 * t ^ (0.1 : ℝ) ≤ 0 := by linarith [hhBound']
        have hsum : 0 ≤ ((𝒯.P i).h : ℝ) + 2 * t ^ (0.1 : ℝ) := by positivity
        have hprod : (((𝒯.P i).h : ℝ) - 2 * t ^ (0.1 : ℝ)) *
            (((𝒯.P i).h : ℝ) + 2 * t ^ (0.1 : ℝ)) ≤ 0 :=
          mul_nonpos_of_nonpos_of_nonneg hdiff hsum
        nlinarith [hprod, hpowMul]
      have hpoly : ((𝒯.P i).h : ℝ) ^ 2 + 1 ≤ 5 * t ^ (0.2 : ℝ) := by
        nlinarith only [hsq, hpow2]
      exact hnat.trans hpoly
    have htPow : t ^ (0.1 : ℝ) ≤ t ^ (0.2 : ℝ) :=
      Real.rpow_le_rpow_of_exponent_le ht1 (by norm_num)
    have hcalc :
        (𝒯.P i).h * Real.log 2 +
          Real.log ((H.Device.H + 1 : ℕ) : ℝ) ≤ 30 * t ^ (0.2 : ℝ) := by
      have hhBound' : ((𝒯.P i).h : ℝ) ≤ 2 * t ^ (0.1 : ℝ) := hhBound
      calc
        (𝒯.P i).h * Real.log 2 + Real.log ((H.Device.H + 1 : ℕ) : ℝ) ≤
            (𝒯.P i).h * Real.log 2 +
              (1 + ((𝒯.P i).h + 1 : ℝ) * ((𝒯.P i).h + 2 : ℝ) +
                Real.log ((𝒯.P i).h ^ 2 + 1 : ℝ)) := add_le_add le_rfl hlogH
        _ ≤ 30 * t ^ (0.2 : ℝ) := by
          nlinarith [hhBound', hprod, hlogTwo, hlogPoly, htPow, hpow2]
    simpa [n, t] using hcalc
  have hLexp : (L : ℝ) ≤ Real.exp (30 * t ^ (0.2 : ℝ)) := by
    have hLpos : (0 : ℝ) < L := by exact_mod_cast hLocPos
    rw [← Real.exp_log hLpos]
    exact Real.exp_le_exp.mpr hlogL
  have hTupleCount : tupleCount = (T.S.N k) ^ (𝒯.kScale i) := by
    simp [tupleCount, PrimitiveHistory.Tuple, Fintype.card_fun]
  have hListCardEq : Fintype.card (SmallList H.Device (𝒯.tScale i)) =
      Fintype.card {S : Finset H.Center // S.Nonempty ∧ S.card ≤ 𝒯.tScale i} := by
    apply Fintype.card_congr
    exact Equiv.refl _
  have hListCount : listCount ≤ (L + 1) ^ (2 * 𝒯.tScale i) := by
    calc
      listCount = Fintype.card (SmallList H.Device (𝒯.tScale i)) := rfl
      _ = Fintype.card {S : Finset H.Center // S.Nonempty ∧ S.card ≤ 𝒯.tScale i} := hListCardEq
      _ ≤ (L + 1) ^ (2 * 𝒯.tScale i) := by
        simpa [L] using
          Lane_q_s14_hist.small_finset_type_card_le_pow (α := H.Center) (𝒯.tScale i) hLocPos
  have hOrderCount : orderCount ≤ listCount ^ listCount := by
    simp only [orderCount, SearchPerm, Fintype.card_perm, Fintype.card_fin]
    exact Nat.factorial_le_pow listCount
  have hTiePermCount : tiePermCount ≤ L ^ L := by
    have hcard : tiePermCount = Nat.factorial (Fintype.card H.Device.Loc) := by
      change Fintype.card (Equiv.Perm (Fin (Fintype.card H.Device.Loc))) = _
      rw [Fintype.card_perm, Fintype.card_fin]
    rw [hcard]
    calc
      Nat.factorial (Fintype.card H.Device.Loc) ≤
          (Fintype.card H.Device.Loc) ^ (Fintype.card H.Device.Loc) :=
        Nat.factorial_le_pow _
      _ = L ^ L := by rfl
  have centerLaw_active {z : mesh.V × (H.Tuple × (Bool × Bool))}
      (hz : 0 < (H.centerLaw p).w z) : z.1 ∈ active := by
    by_contra hn
    have hzero : mesh.wt z.1 p = 0 := by
      apply le_antisymm (le_of_not_gt (by simpa [active] using hn))
      exact mesh.wt_nonneg _ _
    simp [PrimitiveHistory.centerLaw, FinLaw.bind, PrimitiveHistory.vertexLaw,
      PrimitiveHistory.tuplePrior, lawToFinLaw, FinLaw.pi,
      PrimitiveHistory.finProbToFinLaw, FinProb.bernoulli, hzero] at hz
  have groupLaw_active {z : mesh.V × SearchPerm H.Device (𝒯.tScale i)}
      (hz : 0 < (H.groupLaw p).w z) : z.1 ∈ active := by
    by_contra hn
    have hzero : mesh.wt z.1 p = 0 := by
      apply le_antisymm (le_of_not_gt (by simpa [active] using hn))
      exact mesh.wt_nonneg _ _
    simp [PrimitiveHistory.groupLaw, FinLaw.bind, PrimitiveHistory.vertexLaw,
      PrimitiveHistory.finProbToFinLaw, FinProb.uniformAll, hzero] at hz
  have centerSupportCard (c : H.Center) :
      Fintype.card {z : H.Val (.inl c) // 0 < (H.record p (.inl c)).w z} ≤
        A * tupleCount * 4 := by
    let f : {z : H.Val (.inl c) // 0 < (H.record p (.inl c)).w z} →
        {v : mesh.V // v ∈ active} × H.Tuple × (Bool × Bool) := fun z =>
      (⟨z.1.1, by
          have hz : 0 < (H.centerLaw p).w z.1 := by simpa [PrimitiveHistory.record] using z.2
          exact centerLaw_active hz⟩, z.1.2.1, z.1.2.2)
    have hf : Function.Injective f := by
      intro x y hxy
      apply Subtype.ext
      dsimp [f] at hxy
      have hv : x.1.1 = y.1.1 := congrArg Subtype.val (congrArg Prod.fst hxy)
      have hrest := congrArg Prod.snd hxy
      have hw : x.1.2.1 = y.1.2.1 := congrArg Prod.fst hrest
      have hb : x.1.2.2 = y.1.2.2 := congrArg Prod.snd hrest
      exact Prod.ext hv (Prod.ext hw hb)
    calc
      _ ≤ Fintype.card ({v : mesh.V // v ∈ active} × H.Tuple × (Bool × Bool)) :=
        Fintype.card_le_of_injective f hf
      _ = A * tupleCount * 4 := by
        have hactiveCard : Fintype.card {v : mesh.V // v ∈ active} = active.card :=
          Fintype.card_coe active
        simp [A, tupleCount, hactiveCard]
        ring
  have groupSupportCard (g : Group 𝒯 i) :
      Fintype.card {z : H.Val (.inr (.inl g)) // 0 < (H.record p (.inr (.inl g))).w z} ≤
        A * orderCount := by
    let f : {z : H.Val (.inr (.inl g)) // 0 < (H.record p (.inr (.inl g))).w z} →
        {v : mesh.V // v ∈ active} × SearchPerm H.Device (𝒯.tScale i) := fun z =>
      (⟨z.1.1, by
          have hz : 0 < (H.groupLaw p).w z.1 := by simpa [PrimitiveHistory.record] using z.2
          exact groupLaw_active hz⟩, z.1.2)
    have hf : Function.Injective f := by
      intro x y hxy
      apply Subtype.ext
      rcases Prod.mk.inj hxy with ⟨hv, hσ⟩
      exact Prod.ext (congrArg Subtype.val hv) hσ
    calc
      _ ≤ Fintype.card ({v : mesh.V // v ∈ active} × SearchPerm H.Device (𝒯.tScale i)) :=
        Fintype.card_le_of_injective f hf
      _ = A * orderCount := by
        have hactiveCard : Fintype.card {v : mesh.V // v ∈ active} = active.card :=
          Fintype.card_coe active
        simp [A, orderCount, hactiveCard]
  have hAmono : A ≤ A + 1 := Nat.le_succ A
  have hTmono : tupleCount ≤ tupleCount + 1 := Nat.le_succ tupleCount
  have hOmono : orderCount ≤ orderCount + 1 := Nat.le_succ orderCount
  have hPmono : tiePermCount ≤ tiePermCount + 1 := Nat.le_succ tiePermCount
  have hOpos : 1 ≤ orderCount + 1 := Nat.succ_le_succ (Nat.zero_le orderCount)
  have hPpos : 1 ≤ tiePermCount + 1 := Nat.succ_le_succ (Nat.zero_le tiePermCount)
  have hTpos : 1 ≤ tupleCount + 1 := Nat.succ_le_succ (Nat.zero_le tupleCount)
  have tieSupportCard (c : H.Center) :
      Fintype.card {z : H.Val (.inr (.inr c)) //
        0 < (H.record p (.inr (.inr c))).w z} ≤ tiePermCount := by
    apply Fintype.card_le_of_injective (fun z => z.1)
    intro x y hxy
    apply Subtype.ext
    exact hxy
  have hCenterB (c : H.Center) :
      Fintype.card {z : H.Val (.inl c) // 0 < (H.record p (.inl c)).w z} ≤ B := by
    apply (centerSupportCard c).trans
    calc
      A * tupleCount * 4 = 4 * (A * tupleCount) := by ring
      _ ≤ 4 * ((A + 1) * (tupleCount + 1)) := Nat.mul_le_mul_left 4 (Nat.mul_le_mul hAmono hTmono)
      _ = (4 * (A + 1) * (tupleCount + 1)) * 1 := by ring
      _ ≤ (4 * (A + 1) * (tupleCount + 1)) * (orderCount + 1) :=
        Nat.mul_le_mul_left _ hOpos
      _ = (4 * (A + 1) * (tupleCount + 1) * (orderCount + 1)) * 1 := by ring
      _ ≤ (4 * (A + 1) * (tupleCount + 1) * (orderCount + 1)) * (tiePermCount + 1) :=
        Nat.mul_le_mul_left _ hPpos
      _ = B := by rfl
  have hGroupB (g : Group 𝒯 i) :
      Fintype.card {z : H.Val (.inr (.inl g)) // 0 < (H.record p (.inr (.inl g))).w z} ≤ B := by
    apply (groupSupportCard g).trans
    have hTfac : 4 * (A + 1) ≤ 4 * (A + 1) * (tupleCount + 1) := by
      calc
        4 * (A + 1) = (4 * (A + 1)) * 1 := by simp
        _ ≤ (4 * (A + 1)) * (tupleCount + 1) :=
          Nat.mul_le_mul_left _ hTpos
    calc
      A * orderCount = 1 * (A * orderCount) := by simp
      _ ≤ 4 * (A * orderCount) := Nat.mul_le_mul_right _ (by norm_num)
      _ ≤ 4 * ((A + 1) * (orderCount + 1)) := Nat.mul_le_mul_left 4 (Nat.mul_le_mul hAmono hOmono)
      _ = (4 * (A + 1)) * (orderCount + 1) := by ring
      _ ≤ (4 * (A + 1) * (tupleCount + 1)) * (orderCount + 1) :=
        Nat.mul_le_mul_right _ hTfac
      _ = (4 * (A + 1) * (tupleCount + 1) * (orderCount + 1)) * 1 := by ring
      _ ≤ (4 * (A + 1) * (tupleCount + 1) * (orderCount + 1)) * (tiePermCount + 1) :=
        Nat.mul_le_mul_left _ hPpos
      _ = B := by rfl
  have hTieB (c : H.Center) :
      Fintype.card {z : H.Val (.inr (.inr c)) //
        0 < (H.record p (.inr (.inr c))).w z} ≤ B := by
    apply (tieSupportCard c).trans
    have hfac : 1 ≤ 4 * (A + 1) * (tupleCount + 1) * (orderCount + 1) := by
      calc
        1 = 1 * 1 * 1 * 1 := by norm_num
        _ ≤ 4 * (A + 1) * (tupleCount + 1) * (orderCount + 1) := by
          gcongr <;> omega
    calc
      tiePermCount ≤ tiePermCount + 1 := hPmono
      _ = 1 * (tiePermCount + 1) := by simp
      _ ≤ (4 * (A + 1) * (tupleCount + 1) * (orderCount + 1)) * (tiePermCount + 1) :=
        Nat.mul_le_mul_right _ hfac
      _ = B := by rfl
  have hCoordB (r : H.Rec) :
      Fintype.card {z : H.Val r // 0 < (H.record p r).w z} ≤ B := by
    cases r with
    | inl c => exact hCenterB c
    | inr q => cases q with
      | inl g => exact hGroupB g
      | inr c => exact hTieB c
  have hSupportNat :
      (Finset.univ.filter fun W => 0 < (H.recLaw p).w W).card ≤ B ^ Fintype.card H.Rec := by
    have hprod := Lane_q_s14_hist.positive_pi_support_card_le (H.record p)
    calc
      _ = (Finset.univ.filter fun W : ∀ r, H.Val r =>
        0 < ∏ r, (H.record p r).w (W r)).card := by
          apply congrArg Finset.card
          ext W
          simp [PrimitiveHistory.recLaw, recordLaw, PrimitiveHistory.lawRec, FinLaw.pi]
      _ ≤ ∏ r, Fintype.card {z : H.Val r // 0 < (H.record p r).w z} := hprod
      _ ≤ ∏ r : H.Rec, B := by
          apply Finset.prod_le_prod
          intro r hr
          exact hCoordB r
      _ = B ^ Fintype.card H.Rec := by simp
  have hGroupLe : Fintype.card (Group 𝒯 i) ≤ L := by
    apply Fintype.card_le_of_injective
      (fun g : Group 𝒯 i => (g.1, (⟨0, Nat.zero_lt_succ _⟩ : Fin (H.Device.H + 1))))
    intro g g' hgg'
    apply Subtype.ext
    exact congrArg Prod.fst hgg'
  have hRecCard : Fintype.card H.Rec ≤ 3 * L := by
    have hEq : Fintype.card H.Rec = L + (Fintype.card (Group 𝒯 i) + L) := by
      simp [PrimitiveHistory.Rec, L]
    rw [hEq]
    omega
  have hBpos : 1 ≤ B := by
    dsimp [B]
    have hA : 1 ≤ A + 1 := by omega
    have hT : 1 ≤ tupleCount + 1 := by omega
    have hO : 1 ≤ orderCount + 1 := by omega
    have hP : 1 ≤ tiePermCount + 1 := by omega
    calc
      1 ≤ 4 * (A + 1) := by
        calc
          1 ≤ 4 := by omega
          _ ≤ 4 * (A + 1) := by
            simpa using Nat.mul_le_mul_left 4 hA
      _ ≤ 4 * (A + 1) * (tupleCount + 1) := by
        simpa using Nat.mul_le_mul_left (4 * (A + 1)) hT
      _ ≤ 4 * (A + 1) * (tupleCount + 1) * (orderCount + 1) := by
        simpa using Nat.mul_le_mul_left (4 * (A + 1) * (tupleCount + 1)) hO
      _ ≤ 4 * (A + 1) * (tupleCount + 1) * (orderCount + 1) * (tiePermCount + 1) := by
        simpa using Nat.mul_le_mul_left (4 * (A + 1) * (tupleCount + 1) * (orderCount + 1)) hP
  have hSupportNat' :
      (Finset.univ.filter fun W => 0 < (H.recLaw p).w W).card ≤ B ^ (3 * L) := by
    calc
      _ ≤ B ^ Fintype.card H.Rec := hSupportNat
      _ ≤ B ^ (3 * L) := Nat.pow_le_pow_right hBpos hRecCard
  let supp : Finset (∀ r, H.Val r) :=
    Finset.univ.filter fun W => 0 < (H.recLaw p).w W
  have hSuppNe : supp.Nonempty := by
    by_contra hne
    have hempty : supp = ∅ := Finset.not_nonempty_iff_eq_empty.mp hne
    have hzero : ∀ W, (H.recLaw p).w W = 0 := by
      intro W
      have hnot : ¬ 0 < (H.recLaw p).w W := by
        intro hpos
        have hmem : W ∈ supp := by simp [supp, hpos]
        rw [hempty] at hmem
        simp at hmem
      exact le_antisymm (le_of_not_gt hnot) ((H.recLaw p).nonneg W)
    have hsum : ∑ W, (H.recLaw p).w W = 0 := by
      apply Finset.sum_eq_zero
      intro W hW
      exact hzero W
    rw [(H.recLaw p).sum_one] at hsum
    norm_num at hsum
  have hCountPos : (supp.card : ℝ) > 0 := by
    exact_mod_cast Finset.card_pos.mpr hSuppNe
  have hAplusNat : A + 1 ≤ 4 * T.S.N k := by
    have hNlower : 1 ≤ T.S.N k := Nat.succ_le_of_lt hNpos
    calc
      A + 1 ≤ 2 * T.S.N k + 2 := Nat.add_le_add_right hActiveCard 1
      _ ≤ 4 * T.S.N k := by omega
  have hAplusLog : Real.log ((A + 1 : ℕ) : ℝ) ≤ 2 + 2 * n := by
    have hApos : (0 : ℝ) < (A : ℝ) + 1 := by
      have hAnonneg : (0 : ℝ) ≤ (A : ℝ) := Nat.cast_nonneg A
      linarith
    have hAupper : (A : ℝ) + 1 ≤ 4 * (T.S.N k : ℝ) := by
      exact_mod_cast hAplusNat
    have hlog := Real.log_le_log hApos hAupper
    rw [Real.log_mul (by norm_num : (4 : ℝ) ≠ 0) (ne_of_gt hNcast)] at hlog
    have hlogFour : Real.log 4 ≤ 2 := by
      apply (Real.log_le_iff_le_exp (by norm_num)).2
      have hExp : 4 < Real.exp 2 := by
        rw [show (2 : ℝ) = 1 + 1 by norm_num, Real.exp_add]
        nlinarith [Real.exp_one_gt_two]
      exact hExp.le
    have hAplusLogReal : Real.log ((A : ℝ) + 1) ≤ 2 + 2 * n := by
      dsimp [n]
      linarith [hlog, hlogFour, hlogN]
    simpa [Nat.cast_add] using hAplusLogReal
  have hTuplePlusLog : Real.log ((tupleCount + 1 : ℕ) : ℝ) ≤
      1 + 6 * n * t ^ (0.1 : ℝ) := by
    have hTuplePosNat : 1 ≤ tupleCount := by
      rw [hTupleCount]
      exact Nat.one_le_pow _ _ hNpos
    have hTuplePlus : tupleCount + 1 ≤ 2 * tupleCount := by omega
    have hTuplePlusCast : ((tupleCount + 1 : ℕ) : ℝ) ≤ 2 * (tupleCount : ℝ) := by
      exact_mod_cast hTuplePlus
    have hTuplePlusReal : (tupleCount : ℝ) + 1 ≤ 2 * (tupleCount : ℝ) := by
      simpa [Nat.cast_add] using hTuplePlusCast
    have hTuplePosReal : 0 < (tupleCount : ℝ) := by
      exact_mod_cast (Nat.succ_le_iff.mp hTuplePosNat)
    have hTupleLogReal : Real.log ((tupleCount : ℝ) + 1) ≤
        Real.log 2 + Real.log (tupleCount : ℝ) := by
      have hlog := Real.log_le_log (by positivity) hTuplePlusReal
      rw [Real.log_mul (by norm_num : (2 : ℝ) ≠ 0) (ne_of_gt hTuplePosReal)] at hlog
      exact hlog
    have hTupleLog : Real.log ((tupleCount + 1 : ℕ) : ℝ) ≤
        Real.log 2 + Real.log (tupleCount : ℝ) := by
      simpa [Nat.cast_add] using hTupleLogReal
    have hlogTuple : Real.log (tupleCount : ℝ) =
        (𝒯.kScale i : ℝ) * Real.log (T.S.N k : ℝ) := by
      rw [hTupleCount, Nat.cast_pow, Real.log_pow]
    have hlogTwo : Real.log 2 ≤ 1 := by
      exact (Real.log_le_iff_le_exp (by norm_num)).2 Real.exp_one_gt_two.le
    have hlogNnonneg : 0 ≤ Real.log (T.S.N k : ℝ) := by
      apply Real.log_nonneg
      exact_mod_cast Nat.succ_le_of_lt hNpos
    have hpow1K : 1 ≤ t ^ (0.1 : ℝ) := by
      simpa using Real.rpow_le_rpow_of_exponent_le ht1 (by norm_num : (0 : ℝ) ≤ 0.1)
    have hKcast : (𝒯.kScale i : ℝ) ≤ 3 * t ^ (0.1 : ℝ) := by
      have hh : ((𝒯.P i).h : ℝ) ≤ 2 * t ^ (0.1 : ℝ) := hhBound
      have hscale : (𝒯.kScale i : ℝ) ≤ (𝒯.P i).h + 1 := by exact_mod_cast hK
      calc
        (𝒯.kScale i : ℝ) ≤ (𝒯.P i).h + 1 := hscale
        _ ≤ 3 * t ^ (0.1 : ℝ) := by nlinarith [hpow1K]
    calc
      Real.log ((tupleCount + 1 : ℕ) : ℝ) ≤ Real.log 2 + Real.log (tupleCount : ℝ) := hTupleLog
      _ = Real.log 2 + (𝒯.kScale i : ℝ) * Real.log (T.S.N k : ℝ) := by rw [hlogTuple]
      _ ≤ 1 + (𝒯.kScale i : ℝ) * Real.log (T.S.N k : ℝ) := by
        exact add_le_add hlogTwo le_rfl
      _ ≤ 1 + (3 * t ^ (0.1 : ℝ)) * (2 * n) := by
        exact add_le_add le_rfl
          (mul_le_mul hKcast hlogN hlogNnonneg (by positivity))
      _ = 1 + 6 * n * t ^ (0.1 : ℝ) := by ring
  have hLplusLog : Real.log ((L + 1 : ℕ) : ℝ) ≤ 1 + 30 * t ^ (0.2 : ℝ) := by
    have hLplusNat : L + 1 ≤ 2 * L := by omega
    have hLplusCast : ((L + 1 : ℕ) : ℝ) ≤ 2 * (L : ℝ) := by exact_mod_cast hLplusNat
    have hLplusReal : (L : ℝ) + 1 ≤ 2 * (L : ℝ) := by simpa [Nat.cast_add] using hLplusCast
    have hlogReal : Real.log ((L : ℝ) + 1) ≤ Real.log 2 + Real.log (L : ℝ) := by
      have hlog := Real.log_le_log (by positivity) hLplusReal
      rw [Real.log_mul (by norm_num : (2 : ℝ) ≠ 0) (ne_of_gt (by exact_mod_cast hLocPos))] at hlog
      exact hlog
    have hlog : Real.log ((L + 1 : ℕ) : ℝ) ≤ Real.log 2 + Real.log (L : ℝ) := by
      simpa [Nat.cast_add] using hlogReal
    have hlogTwo : Real.log 2 ≤ 1 := by
      exact (Real.log_le_iff_le_exp (by norm_num)).2 Real.exp_one_gt_two.le
    linarith [hlog, hlogTwo, hlogL]
  have hListPlusLog : Real.log ((listCount + 1 : ℕ) : ℝ) ≤ 200 * t ^ (0.3 : ℝ) := by
    have hbase : 1 ≤ (L + 1) ^ (2 * 𝒯.tScale i) :=
      Nat.one_le_pow _ _ (by omega)
    have hlistPlusNat : listCount + 1 ≤ 2 * (L + 1) ^ (2 * 𝒯.tScale i) := by
      calc
        listCount + 1 ≤ (L + 1) ^ (2 * 𝒯.tScale i) + 1 := Nat.add_le_add_right hListCount 1
        _ ≤ 2 * (L + 1) ^ (2 * 𝒯.tScale i) := by omega
    have hlistPlusCast : ((listCount + 1 : ℕ) : ℝ) ≤
        2 * ((L + 1 : ℕ) : ℝ) ^ (2 * 𝒯.tScale i) := by exact_mod_cast hlistPlusNat
    have hListCast : ((listCount + 1 : ℕ) : ℝ) = (listCount : ℝ) + 1 := by simp
    have hLCast : ((L + 1 : ℕ) : ℝ) = (L : ℝ) + 1 := by simp
    have hlistPlusReal : (listCount : ℝ) + 1 ≤
        2 * ((L : ℝ) + 1) ^ (2 * 𝒯.tScale i) := by
      rw [← hListCast, ← hLCast]
      exact hlistPlusCast
    have hlogReal : Real.log ((listCount : ℝ) + 1) ≤
        Real.log 2 + (2 * (𝒯.tScale i : ℝ)) * Real.log ((L : ℝ) + 1) := by
      have hlog := Real.log_le_log (by positivity) hlistPlusReal
      rw [Real.log_mul (by norm_num : (2 : ℝ) ≠ 0) (by positivity), Real.log_pow] at hlog
      push_cast at hlog
      exact hlog
    have hLplusLogReal : Real.log ((L : ℝ) + 1) ≤ 1 + 30 * t ^ (0.2 : ℝ) := by
      rw [← hLCast]
      exact hLplusLog
    have hlogTwo : Real.log 2 ≤ 1 := by
      exact (Real.log_le_iff_le_exp (by norm_num)).2 Real.exp_one_gt_two.le
    have hpow1List : 1 ≤ t ^ (0.1 : ℝ) := by
      simpa using Real.rpow_le_rpow_of_exponent_le ht1 (by norm_num : (0 : ℝ) ≤ 0.1)
    have hpow2List : 1 ≤ t ^ (0.2 : ℝ) := by
      simpa using Real.rpow_le_rpow_of_exponent_le ht1 (by norm_num : (0 : ℝ) ≤ 0.2)
    have htScaleCast : (𝒯.tScale i : ℝ) ≤ 3 * t ^ (0.1 : ℝ) := by
      have hscale : (𝒯.tScale i : ℝ) ≤ (𝒯.P i).h + 1 := by exact_mod_cast hTscale
      calc
        (𝒯.tScale i : ℝ) ≤ (𝒯.P i).h + 1 := hscale
        _ ≤ 3 * t ^ (0.1 : ℝ) := by nlinarith only [hhBound, hpow1List]
    have htPow : t ^ (0.1 : ℝ) ≤ t ^ (0.3 : ℝ) :=
      Real.rpow_le_rpow_of_exponent_le ht1 (by norm_num)
    have htPow2 : t ^ (0.2 : ℝ) ≤ t ^ (0.3 : ℝ) :=
      Real.rpow_le_rpow_of_exponent_le ht1 (by norm_num)
    have hpowMul : t ^ (0.1 : ℝ) * t ^ (0.2 : ℝ) = t ^ (0.3 : ℝ) := by
      rw [← Real.rpow_add (by linarith : 0 < t)]
      congr 1
      ring
    calc
      Real.log ((listCount + 1 : ℕ) : ℝ) ≤ Real.log 2 +
          (2 * (𝒯.tScale i : ℝ)) * Real.log ((L : ℝ) + 1) := by
            rw [hListCast]
            exact hlogReal
      _ ≤ 1 + (2 * (3 * t ^ (0.1 : ℝ))) * (1 + 30 * t ^ (0.2 : ℝ)) := by
        apply add_le_add
        · exact hlogTwo
        · exact mul_le_mul
            (by nlinarith [htScaleCast]) hLplusLogReal
            (Real.log_nonneg (by exact_mod_cast Nat.succ_le_succ (Nat.zero_le L)))
            (by positivity)
      _ ≤ 200 * t ^ (0.3 : ℝ) := by
        have hpow3List : 1 ≤ t ^ (0.3 : ℝ) := by
          simpa using Real.rpow_le_rpow_of_exponent_le ht1 (by norm_num : (0 : ℝ) ≤ 0.3)
        nlinarith only [hpow1List, hpow2List, hpow3List, htPow, htPow2, hpowMul]
  have hListPlusExp : ((listCount + 1 : ℕ) : ℝ) ≤ Real.exp (200 * t ^ (0.3 : ℝ)) := by
    have hpos : (0 : ℝ) < ((listCount + 1 : ℕ) : ℝ) := by positivity
    calc
      ((listCount + 1 : ℕ) : ℝ) = Real.exp (Real.log ((listCount + 1 : ℕ) : ℝ)) :=
        (Real.exp_log hpos).symm
      _ ≤ Real.exp (200 * t ^ (0.3 : ℝ)) := Real.exp_le_exp.mpr hListPlusLog
  have hOrderPlusNat : orderCount + 1 ≤
      2 * (listCount + 1) ^ (listCount + 1) := by
    have hpow : orderCount ≤ (listCount + 1) ^ (listCount + 1) := by
      calc
        orderCount ≤ listCount ^ listCount := hOrderCount
        _ ≤ (listCount + 1) ^ (listCount + 1) := by gcongr <;> omega
    have hbase : 1 ≤ (listCount + 1) ^ (listCount + 1) :=
      Nat.one_le_pow _ _ (by omega)
    omega
  have hOrderPlusLog : Real.log ((orderCount + 1 : ℕ) : ℝ) ≤
      1 + Real.exp (400 * t ^ (0.3 : ℝ)) := by
    have horderPlusCast : ((orderCount + 1 : ℕ) : ℝ) ≤
        2 * ((listCount + 1 : ℕ) : ℝ) ^ (listCount + 1) := by exact_mod_cast hOrderPlusNat
    have hOrderCast : ((orderCount + 1 : ℕ) : ℝ) = (orderCount : ℝ) + 1 := by simp
    have hListCast : ((listCount + 1 : ℕ) : ℝ) = (listCount : ℝ) + 1 := by simp
    have horderPlusReal : (orderCount : ℝ) + 1 ≤
        2 * ((listCount : ℝ) + 1) ^ (listCount + 1) := by
      rw [← hOrderCast, ← hListCast]
      exact horderPlusCast
    have hlogReal : Real.log ((orderCount : ℝ) + 1) ≤
        Real.log 2 + ((listCount : ℝ) + 1) * Real.log ((listCount : ℝ) + 1) := by
      have hlog := Real.log_le_log (by positivity) horderPlusReal
      rw [Real.log_mul (by norm_num : (2 : ℝ) ≠ 0) (by positivity), Real.log_pow] at hlog
      push_cast at hlog
      exact hlog
    have hlogU : Real.log ((listCount : ℝ) + 1) ≤ 200 * t ^ (0.3 : ℝ) := by
      rw [← hListCast]
      exact hListPlusLog
    have hU : (listCount : ℝ) + 1 ≤ Real.exp (200 * t ^ (0.3 : ℝ)) := by
      rw [← hListCast]
      exact hListPlusExp
    have hlogUnonneg : 0 ≤ Real.log ((listCount : ℝ) + 1) := by
      apply Real.log_nonneg
      have hlistNonneg : 0 ≤ (listCount : ℝ) := Nat.cast_nonneg _
      linarith
    have hxnonneg : 0 ≤ 200 * t ^ (0.3 : ℝ) := by positivity
    have hxle : 200 * t ^ (0.3 : ℝ) ≤ Real.exp (200 * t ^ (0.3 : ℝ)) := by
      linarith [Real.add_one_le_exp (200 * t ^ (0.3 : ℝ))]
    have hmul : ((listCount : ℝ) + 1) *
        Real.log ((listCount : ℝ) + 1) ≤ Real.exp (400 * t ^ (0.3 : ℝ)) := by
      calc
        _ ≤ Real.exp (200 * t ^ (0.3 : ℝ)) * (200 * t ^ (0.3 : ℝ)) := by
          exact mul_le_mul hU hlogU hlogUnonneg (by positivity)
        _ ≤ Real.exp (200 * t ^ (0.3 : ℝ)) * Real.exp (200 * t ^ (0.3 : ℝ)) :=
          mul_le_mul_of_nonneg_left hxle (Real.exp_nonneg _)
        _ = Real.exp (400 * t ^ (0.3 : ℝ)) := by rw [← Real.exp_add]; congr 1 <;> ring
    calc
      Real.log ((orderCount + 1 : ℕ) : ℝ) ≤ Real.log 2 +
          ((listCount : ℝ) + 1) * Real.log ((listCount : ℝ) + 1) := by
            rw [hOrderCast]
            exact hlogReal
      _ ≤ 1 + Real.exp (400 * t ^ (0.3 : ℝ)) := by
        exact add_le_add (by
          exact (Real.log_le_iff_le_exp (by norm_num)).2 Real.exp_one_gt_two.le)
          hmul
  have hTiePermPlusNat : tiePermCount + 1 ≤ 2 * L ^ L := by
    have hpow : tiePermCount ≤ L ^ L := hTiePermCount
    have hbase : 1 ≤ L ^ L := Nat.one_le_pow _ _ hLocPos
    omega
  have hTiePermPlusLog : Real.log ((tiePermCount + 1 : ℕ) : ℝ) ≤
      1 + (L : ℝ) * Real.log (L : ℝ) := by
    have hTiePermPlusCast : ((tiePermCount + 1 : ℕ) : ℝ) ≤
        2 * (L : ℝ) ^ L := by exact_mod_cast hTiePermPlusNat
    have hTiePermPlusReal : (tiePermCount : ℝ) + 1 ≤ 2 * (L : ℝ) ^ L := by
      simpa [Nat.cast_add] using hTiePermPlusCast
    have hlogReal : Real.log ((tiePermCount : ℝ) + 1) ≤ Real.log 2 +
        (L : ℝ) * Real.log (L : ℝ) := by
      have hlog := Real.log_le_log (by positivity) hTiePermPlusReal
      rw [Real.log_mul (by norm_num : (2 : ℝ) ≠ 0) (by positivity), Real.log_pow] at hlog
      exact hlog
    have hlog : Real.log ((tiePermCount + 1 : ℕ) : ℝ) ≤ Real.log 2 +
        (L : ℝ) * Real.log (L : ℝ) := by
      simpa [Nat.cast_add] using hlogReal
    have hlogTwo : Real.log 2 ≤ 1 := by
      exact (Real.log_le_iff_le_exp (by norm_num)).2 Real.exp_one_gt_two.le
    linarith [hlog, hlogTwo]
  have hTiePermPlusExp' : Real.log ((tiePermCount + 1 : ℕ) : ℝ) ≤
      1 + Real.exp (100 * t ^ (0.3 : ℝ)) := by
    have hLreal : (L : ℝ) ≤ Real.exp (30 * t ^ (0.2 : ℝ)) := hLexp
    have hxnonneg : 0 ≤ 30 * t ^ (0.2 : ℝ) := by positivity
    have hxle : 30 * t ^ (0.2 : ℝ) ≤ Real.exp (30 * t ^ (0.2 : ℝ)) := by
      linarith [Real.add_one_le_exp (30 * t ^ (0.2 : ℝ))]
    have hmul : (L : ℝ) * (30 * t ^ (0.2 : ℝ)) ≤
        Real.exp (60 * t ^ (0.2 : ℝ)) := by
      calc
        _ ≤ Real.exp (30 * t ^ (0.2 : ℝ)) * Real.exp (30 * t ^ (0.2 : ℝ)) :=
          mul_le_mul hLreal hxle (by positivity) (by positivity)
        _ = Real.exp (60 * t ^ (0.2 : ℝ)) := by rw [← Real.exp_add]; congr 1 <;> ring
    have htPow : t ^ (0.2 : ℝ) ≤ t ^ (0.3 : ℝ) :=
      Real.rpow_le_rpow_of_exponent_le ht1 (by norm_num)
    have hExpMono : Real.exp (60 * t ^ (0.2 : ℝ)) ≤ Real.exp (100 * t ^ (0.3 : ℝ)) := by
      apply Real.exp_le_exp.mpr
      nlinarith [htPow]
    have hlogLScaled : (L : ℝ) * Real.log (L : ℝ) ≤
        (L : ℝ) * (30 * t ^ (0.2 : ℝ)) :=
      mul_le_mul_of_nonneg_left hlogL (by positivity)
    calc
      Real.log ((tiePermCount + 1 : ℕ) : ℝ) ≤ 1 + (L : ℝ) * Real.log (L : ℝ) := hTiePermPlusLog
      _ ≤ 1 + (L : ℝ) * (30 * t ^ (0.2 : ℝ)) := by
        nlinarith only [hlogLScaled]
      _ ≤ 1 + Real.exp (100 * t ^ (0.3 : ℝ)) := by
        nlinarith only [hmul, hExpMono]
  have hBLog : Real.log (B : ℝ) ≤ 10 * n * t ^ (0.1 : ℝ) + 3 * Real.exp (500 * t ^ (0.3 : ℝ)) := by
    have hAcast : ((A + 1 : ℕ) : ℝ) = (A : ℝ) + 1 := by simp
    have hTcast : ((tupleCount + 1 : ℕ) : ℝ) = (tupleCount : ℝ) + 1 := by simp
    have hOcast : ((orderCount + 1 : ℕ) : ℝ) = (orderCount : ℝ) + 1 := by simp
    have hPcast : ((tiePermCount + 1 : ℕ) : ℝ) = (tiePermCount : ℝ) + 1 := by simp
    have hAplusLogReal : Real.log ((A : ℝ) + 1) ≤ 2 + 2 * n := by
      rw [← hAcast]
      exact hAplusLog
    have hTuplePlusLogReal : Real.log ((tupleCount : ℝ) + 1) ≤
        1 + 6 * n * t ^ (0.1 : ℝ) := by
      rw [← hTcast]
      exact hTuplePlusLog
    have hOrderPlusLogReal : Real.log ((orderCount : ℝ) + 1) ≤
        1 + Real.exp (400 * t ^ (0.3 : ℝ)) := by
      rw [← hOcast]
      exact hOrderPlusLog
    have hTiePlusLogReal : Real.log ((tiePermCount : ℝ) + 1) ≤
        1 + Real.exp (100 * t ^ (0.3 : ℝ)) := by
      rw [← hPcast]
      exact hTiePermPlusExp'
    have hBexp : (B : ℝ) = 4 * ((A : ℝ) + 1) * ((tupleCount : ℝ) + 1) *
        ((orderCount : ℝ) + 1) * ((tiePermCount : ℝ) + 1) := by
      change ((4 * (A + 1) * (tupleCount + 1) * (orderCount + 1) * (tiePermCount + 1) : ℕ) : ℝ) = _
      push_cast
      ring
    have hLogEq : Real.log (B : ℝ) = Real.log 4 + Real.log ((A : ℝ) + 1) +
        Real.log ((tupleCount : ℝ) + 1) + Real.log ((orderCount : ℝ) + 1) +
        Real.log ((tiePermCount : ℝ) + 1) := by
      have hApos : 0 < (A : ℝ) + 1 := by
        have hA0 : (0 : ℝ) ≤ (A : ℝ) := Nat.cast_nonneg A
        linarith
      have hTpos : 0 < (tupleCount : ℝ) + 1 := by
        have hT0 : (0 : ℝ) ≤ (tupleCount : ℝ) := Nat.cast_nonneg tupleCount
        linarith
      have hOpos : 0 < (orderCount : ℝ) + 1 := by
        have hO0 : (0 : ℝ) ≤ (orderCount : ℝ) := Nat.cast_nonneg orderCount
        linarith
      have hPpos : 0 < (tiePermCount : ℝ) + 1 := by
        have hP0 : (0 : ℝ) ≤ (tiePermCount : ℝ) := Nat.cast_nonneg tiePermCount
        linarith
      have hleft1 : 0 < 4 * ((A : ℝ) + 1) := mul_pos (by norm_num) hApos
      have hleft2 : 0 < 4 * ((A : ℝ) + 1) * ((tupleCount : ℝ) + 1) :=
        mul_pos hleft1 hTpos
      have hleft3 : 0 < 4 * ((A : ℝ) + 1) * ((tupleCount : ℝ) + 1) *
          ((orderCount : ℝ) + 1) := mul_pos hleft2 hOpos
      rw [hBexp,
        Real.log_mul (ne_of_gt hleft3) (ne_of_gt hPpos),
        Real.log_mul (ne_of_gt hleft2) (ne_of_gt hOpos),
        Real.log_mul (ne_of_gt hleft1) (ne_of_gt hTpos),
        Real.log_mul (by norm_num : (4 : ℝ) ≠ 0) (ne_of_gt hApos)]
    have hlogFour : Real.log 4 ≤ 2 := by
      apply (Real.log_le_iff_le_exp (by norm_num)).2
      have hExp : 4 < Real.exp 2 := by
        rw [show (2 : ℝ) = 1 + 1 by norm_num, Real.exp_add]
        nlinarith [Real.exp_one_gt_two]
      exact hExp.le
    have hconst : 7 ≤ n * t ^ (0.1 : ℝ) := by
      have hNreal : 1000 ≤ n := by
        have h := Real.add_one_le_exp t
        have hn : n = Real.exp t := by
          dsimp [n, t]
          exact (Real.exp_log hncast).symm
        rw [hn]
        linarith
      have hpow : 1 ≤ t ^ (0.1 : ℝ) := by
        simpa using Real.rpow_le_rpow_of_exponent_le ht1 (by norm_num : (0 : ℝ) ≤ 0.1)
      nlinarith
    have hu : 1 ≤ t ^ (0.1 : ℝ) := by
      simpa using Real.rpow_le_rpow_of_exponent_le ht1 (by norm_num : (0 : ℝ) ≤ 0.1)
    have hnu : n ≤ n * t ^ (0.1 : ℝ) := by
      calc
        n = n * 1 := by ring
        _ ≤ n * t ^ (0.1 : ℝ) := mul_le_mul_of_nonneg_left hu (le_of_lt hncast)
    have hexpO : Real.exp (400 * t ^ (0.3 : ℝ)) ≤ Real.exp (500 * t ^ (0.3 : ℝ)) := by
      apply Real.exp_le_exp.mpr
      nlinarith [Real.rpow_nonneg (by linarith : 0 ≤ t) (0.3 : ℝ)]
    have hexpT : Real.exp (100 * t ^ (0.3 : ℝ)) ≤ Real.exp (500 * t ^ (0.3 : ℝ)) := by
      apply Real.exp_le_exp.mpr
      nlinarith [Real.rpow_nonneg (by linarith : 0 ≤ t) (0.3 : ℝ)]
    calc
      Real.log (B : ℝ) ≤ 2 + (2 + 2 * n) + (1 + 6 * n * t ^ (0.1 : ℝ)) +
          (1 + Real.exp (400 * t ^ (0.3 : ℝ))) +
          (1 + Real.exp (100 * t ^ (0.3 : ℝ)) ) := by
        rw [hLogEq]
        exact add_le_add (add_le_add (add_le_add (add_le_add hlogFour hAplusLogReal)
          hTuplePlusLogReal) hOrderPlusLogReal) hTiePlusLogReal
      _ ≤ 10 * n * t ^ (0.1 : ℝ) + 3 * Real.exp (500 * t ^ (0.3 : ℝ)) := by
        calc
          _ = 7 + 2 * n + 6 * n * t ^ (0.1 : ℝ) +
              Real.exp (400 * t ^ (0.3 : ℝ)) + Real.exp (100 * t ^ (0.3 : ℝ)) := by ring
          _ ≤ 7 + 2 * n + 6 * n * t ^ (0.1 : ℝ) +
              2 * Real.exp (500 * t ^ (0.3 : ℝ)) := by
                nlinarith [hexpO, hexpT]
          _ ≤ 10 * n * t ^ (0.1 : ℝ) + 3 * Real.exp (500 * t ^ (0.3 : ℝ)) := by
                nlinarith [hconst, hnu, Real.exp_nonneg (500 * t ^ (0.3 : ℝ))]
  have hBLogNonneg : 0 ≤ Real.log (B : ℝ) := by
    apply Real.log_nonneg
    exact_mod_cast hBpos
  have hRecReal : (Fintype.card H.Rec : ℝ) ≤ 3 * (L : ℝ) := by exact_mod_cast hRecCard
  have hLtimes : 3 * (L : ℝ) ≤ Real.exp (32 * t ^ (0.2 : ℝ)) := by
    have hpow2L : 1 ≤ t ^ (0.2 : ℝ) := by
      simpa using Real.rpow_le_rpow_of_exponent_le ht1 (by norm_num : (0 : ℝ) ≤ 0.2)
    have hExp2 : 3 ≤ Real.exp (2 * t ^ (0.2 : ℝ)) := by
      have harg : 2 ≤ 2 * t ^ (0.2 : ℝ) := by
        nlinarith only [hpow2L]
      calc
        3 ≤ 2 + 1 := by norm_num
        _ ≤ Real.exp 2 := Real.add_one_le_exp 2
        _ ≤ Real.exp (2 * t ^ (0.2 : ℝ)) := Real.exp_le_exp.mpr harg
    calc
      3 * (L : ℝ) ≤ 3 * Real.exp (30 * t ^ (0.2 : ℝ)) :=
        mul_le_mul_of_nonneg_left hLexp (by norm_num)
      _ = Real.exp (30 * t ^ (0.2 : ℝ)) * 3 := by ring
      _ ≤ Real.exp (30 * t ^ (0.2 : ℝ)) * Real.exp (2 * t ^ (0.2 : ℝ)) :=
        mul_le_mul_of_nonneg_left hExp2 (Real.exp_nonneg _)
      _ = Real.exp (32 * t ^ (0.2 : ℝ)) := by rw [← Real.exp_add]; congr 1 <;> ring
  have hlogCount : Real.log (supp.card : ℝ) ≤
      10 * n * t ^ (0.1 : ℝ) * Real.exp (32 * t ^ (0.2 : ℝ)) +
        3 * Real.exp (532 * t ^ (0.3 : ℝ)) := by
    have hlogNat : (supp.card : ℝ) ≤ (B ^ (3 * L) : ℝ) := by exact_mod_cast hSupportNat'
    have hlog := Real.log_le_log hCountPos hlogNat
    rw [Real.log_pow] at hlog
    push_cast at hlog
    calc
      Real.log (supp.card : ℝ) ≤ (3 * (L : ℝ)) * Real.log (B : ℝ) := hlog
      _ ≤ Real.exp (32 * t ^ (0.2 : ℝ)) * Real.log (B : ℝ) :=
        mul_le_mul_of_nonneg_right hLtimes hBLogNonneg
      _ ≤ Real.exp (32 * t ^ (0.2 : ℝ)) *
          (10 * n * t ^ (0.1 : ℝ) + 3 * Real.exp (500 * t ^ (0.3 : ℝ))) :=
        mul_le_mul_of_nonneg_left hBLog (Real.exp_nonneg _)
      _ ≤ 10 * n * t ^ (0.1 : ℝ) * Real.exp (32 * t ^ (0.2 : ℝ)) +
          3 * Real.exp (532 * t ^ (0.3 : ℝ)) := by
        have htPow : t ^ (0.2 : ℝ) ≤ t ^ (0.3 : ℝ) :=
          Real.rpow_le_rpow_of_exponent_le ht1 (by norm_num)
        have hexpMono : Real.exp (32 * t ^ (0.2 : ℝ)) ≤ Real.exp (32 * t ^ (0.3 : ℝ)) :=
          Real.exp_le_exp.mpr (by gcongr)
        calc
          _ = 10 * n * t ^ (0.1 : ℝ) * Real.exp (32 * t ^ (0.2 : ℝ)) +
              3 * (Real.exp (32 * t ^ (0.2 : ℝ)) * Real.exp (500 * t ^ (0.3 : ℝ))) := by ring
          _ ≤ _ := by
            have hmulExp : Real.exp (32 * t ^ (0.2 : ℝ)) *
                Real.exp (500 * t ^ (0.3 : ℝ)) ≤ Real.exp (532 * t ^ (0.3 : ℝ)) := by
              rw [← Real.exp_add]
              apply Real.exp_le_exp.mpr
              nlinarith only [htPow]
            exact add_le_add le_rfl
              (mul_le_mul_of_nonneg_left hmulExp (by norm_num))
          _ = _ := by ring
  have hpowTiny3 : 33 * t ^ (0.3 : ℝ) ≤ (1 / 1000 : ℝ) * t := by
    nlinarith [htTiny]
  have hpowTiny532 : 532 * t ^ (0.3 : ℝ) ≤ (1 / 1000 : ℝ) * t := by
    nlinarith [htTiny]
  have huLeExp : t ^ (0.1 : ℝ) ≤ Real.exp (t ^ (0.3 : ℝ)) := by
    have h01 : t ^ (0.1 : ℝ) ≤ t ^ (0.3 : ℝ) :=
      Real.rpow_le_rpow_of_exponent_le ht1 (by norm_num)
    calc
      t ^ (0.1 : ℝ) ≤ t ^ (0.3 : ℝ) := h01
      _ ≤ Real.exp (t ^ (0.3 : ℝ)) := by linarith [Real.add_one_le_exp (t ^ (0.3 : ℝ))]
  have hExp32 : Real.exp (32 * t ^ (0.2 : ℝ)) ≤ Real.exp (32 * t ^ (0.3 : ℝ)) := by
    apply Real.exp_le_exp.mpr
    have htPow : t ^ (0.2 : ℝ) ≤ t ^ (0.3 : ℝ) :=
      Real.rpow_le_rpow_of_exponent_le ht1 (by norm_num)
    nlinarith [htPow]
  have hProdExp : t ^ (0.1 : ℝ) * Real.exp (32 * t ^ (0.2 : ℝ)) ≤
      Real.exp (33 * t ^ (0.3 : ℝ)) := by
    calc
      _ ≤ Real.exp (t ^ (0.3 : ℝ)) * Real.exp (32 * t ^ (0.3 : ℝ)) :=
        mul_le_mul huLeExp hExp32 (by positivity) (by positivity)
      _ = Real.exp (33 * t ^ (0.3 : ℝ)) := by
        have hsum : t ^ (0.3 : ℝ) + 32 * t ^ (0.3 : ℝ) = 33 * t ^ (0.3 : ℝ) := by ring
        rw [← Real.exp_add, hsum]
  have hnEq : n = Real.exp t := by
    dsimp [n, t]
    exact (Real.exp_log hncast).symm
  have hlogCountSmall : Real.log (supp.card : ℝ) ≤
      13 * Real.exp ((1 + (1 / 1000 : ℝ)) * t) := by
    calc
      Real.log (supp.card : ℝ) ≤
          10 * n * t ^ (0.1 : ℝ) * Real.exp (32 * t ^ (0.2 : ℝ)) +
            3 * Real.exp (532 * t ^ (0.3 : ℝ)) := hlogCount
      _ ≤ 10 * n * Real.exp (33 * t ^ (0.3 : ℝ)) +
            3 * Real.exp ((1 / 1000 : ℝ) * t) := by
          apply add_le_add
          · calc
              10 * n * t ^ (0.1 : ℝ) * Real.exp (32 * t ^ (0.2 : ℝ)) =
                  (10 * n) * (t ^ (0.1 : ℝ) * Real.exp (32 * t ^ (0.2 : ℝ))) := by ring
              _ ≤ (10 * n) * Real.exp (33 * t ^ (0.3 : ℝ)) :=
                mul_le_mul_of_nonneg_left hProdExp (by positivity)
              _ = 10 * n * Real.exp (33 * t ^ (0.3 : ℝ)) := by ring
          · exact mul_le_mul_of_nonneg_left
              (Real.exp_le_exp.mpr hpowTiny532) (by norm_num)
      _ ≤ 10 * n * Real.exp ((1 / 1000 : ℝ) * t) +
            3 * n * Real.exp ((1 / 1000 : ℝ) * t) := by
          have hn1 : 1 ≤ n := by rw [hnEq]; linarith [Real.add_one_le_exp t]
          have hexpNonneg : 0 ≤ Real.exp ((1 / 1000 : ℝ) * t) := Real.exp_nonneg _
          have hE : Real.exp ((1 / 1000 : ℝ) * t) ≤
              n * Real.exp ((1 / 1000 : ℝ) * t) := by
            simpa only [one_mul] using mul_le_mul_of_nonneg_right hn1 hexpNonneg
          exact add_le_add
            (mul_le_mul_of_nonneg_left
              (Real.exp_le_exp.mpr hpowTiny3) (by positivity))
            (calc
            3 * Real.exp ((1 / 1000 : ℝ) * t) ≤
                3 * (n * Real.exp ((1 / 1000 : ℝ) * t)) :=
              mul_le_mul_of_nonneg_left hE (by norm_num)
            _ = 3 * n * Real.exp ((1 / 1000 : ℝ) * t) := by ring)
      _ = 13 * Real.exp ((1 + (1 / 1000 : ℝ)) * t) := by
          rw [hnEq]
          have hexp : Real.exp t * Real.exp ((1 / 1000 : ℝ) * t) =
              Real.exp ((1 + (1 / 1000 : ℝ)) * t) := by
            rw [← Real.exp_add]
            have hsum : t + (1 / 1000 : ℝ) * t = (1 + (1 / 1000 : ℝ)) * t := by ring
            rw [hsum]
          calc
            _ = 13 * (Real.exp t * Real.exp ((1 / 1000 : ℝ) * t)) := by ring
            _ = 13 * Real.exp ((1 + (1 / 1000 : ℝ)) * t) := by rw [hexp]
  have hpowFinal : 13 * Real.exp ((1 + (1 / 1000 : ℝ)) * t) ≤ Real.exp ((1.01 : ℝ) * t) := by
    have h13 : 13 ≤ Real.exp ((9 : ℝ)) := by
      have hquad := Real.quadratic_le_exp_of_nonneg (by norm_num : (0 : ℝ) ≤ 9)
      norm_num at hquad ⊢
      linarith
    have harg : 9 ≤ ((1.01 : ℝ) - (1 + 1 / 1000)) * t := by
      have hcoef : (9 : ℝ) / 1000 ≤ (1.01 : ℝ) - (1 + 1 / 1000) := by norm_num
      calc
        9 ≤ (9 : ℝ) / 1000 * t := by nlinarith only [ht]
        _ ≤ ((1.01 : ℝ) - (1 + 1 / 1000)) * t :=
          mul_le_mul_of_nonneg_right hcoef (by linarith [ht])
    have hfinalarg : 9 + (1 + (1 / 1000 : ℝ)) * t ≤ (1.01 : ℝ) * t := by
      nlinarith only [harg]
    calc
      13 * Real.exp ((1 + (1 / 1000 : ℝ)) * t) ≤
          Real.exp 9 * Real.exp ((1 + (1 / 1000 : ℝ)) * t) :=
        mul_le_mul_of_nonneg_right h13 (Real.exp_nonneg _)
      _ = Real.exp (9 + (1 + (1 / 1000 : ℝ)) * t) := by rw [Real.exp_add]
      _ ≤ Real.exp ((1.01 : ℝ) * t) := Real.exp_le_exp.mpr hfinalarg
  have hcount : (supp.card : ℝ) ≤ Real.exp (n ^ (1.01 : ℝ)) := by
    have hlogTarget : Real.log (supp.card : ℝ) ≤ n ^ (1.01 : ℝ) := by
      rw [Real.rpow_def_of_pos hncast]
      calc
        Real.log (supp.card : ℝ) ≤ Real.exp ((1.01 : ℝ) * t) := hlogCountSmall.trans hpowFinal
        _ = Real.exp (Real.log n * (1.01 : ℝ)) := by
          congr 1
          dsimp [t]
          ring
    calc
      (supp.card : ℝ) = Real.exp (Real.log (supp.card : ℝ)) := (Real.exp_log hCountPos).symm
      _ ≤ Real.exp (n ^ (1.01 : ℝ)) := Real.exp_le_exp.mpr hlogTarget
  simpa [supp] using hcount

set_option maxHeartbeats 200000
set_option maxRecDepth 1000

section Rules

variable {κ : CConsts} {T : Stage} {k : ℕ} {𝒯 : Tiling κ T k}
  {i : Fin 𝒯.m} {mesh : Mesh 𝒯}

/-- Projected sites, with their original even-role indexing. -/
noncomputable def siteSet (Geom : ProjectionGeometry κ 𝒯 i) : (patchHD κ (𝒯.P i).h).Sites :=
  Finset.univ.image fun v : EvenRole 𝒯 i => Geom.project v.1

noncomputable def candidateBall (H : PrimitiveHistory κ 𝒯 i mesh)
    (v : IWord 𝒯 i) (j : Fin (H.Device.H + 1)) : Finset H.Center :=
  Finset.univ.filter fun c => c.2 = j ∧ hammingDist c.1 v ≤ H.Device.r

abbrev Masks (H : PrimitiveHistory κ 𝒯 i mesh) :=
  ∀ (g : Group 𝒯 i) (W : ∀ r, H.Val r), MaskFacts i mesh (H.maskVertex g W)

noncomputable def candidateRange (Geom : ProjectionGeometry κ 𝒯 i)
    (H : PrimitiveHistory κ 𝒯 i mesh) (g : Group 𝒯 i) : Finset H.Center :=
  (groupNeighborhood g).biUnion fun v =>
    Finset.univ.biUnion fun j => candidateBall H (Geom.project v.1) j

noncomputable def admissibleList (Geom : ProjectionGeometry κ 𝒯 i)
    (H : PrimitiveHistory κ 𝒯 i mesh) (g : Group 𝒯 i) (W : ∀ r, H.Val r)
    (S : Finset H.Center) : Prop :=
  S.Nonempty ∧ S.card ≤ 𝒯.tScale i ∧
    ∀ c ∈ S, c ∈ candidateRange Geom H g ∧ H.present W c = true

noncomputable def listHit (H : PrimitiveHistory κ 𝒯 i mesh)
    (W : ∀ r, H.Val r) (S : Finset H.Center) : Finset (Fin (T.S.N k)) :=
  Finset.univ.filter fun y => ∀ c ∈ S, ∀ r, Hits (T.S.E k) 𝒯.c (H.tuple W c r) y

noncomputable def maskedMass (H : PrimitiveHistory κ 𝒯 i mesh) (mask : Masks H)
    (g : Group 𝒯 i) (W : ∀ r, H.Val r) (J : Finset (Fin (T.S.N k))) : ℝ :=
  ∑ D, (mask g W).prior D * (∑ y ∈ J, (mask g W).within D y) ^ 2

noncomputable def listGood (H : PrimitiveHistory κ 𝒯 i mesh) (mask : Masks H)
    (g : Group 𝒯 i) (W : ∀ r, H.Val r) (S : Finset H.Center) : Prop :=
  maskedMass H mask g W (listHit H W S) ≥ Real.exp (-2 * (𝒯.kScale i : ℝ) * S.card) ∧
    ∀ c ∈ S, maskedMass H mask g W (listHit H W S) ≥
      Real.exp ((-Real.log 4 + 0.4 * κ.a) * (𝒯.kScale i : ℝ)) *
        maskedMass H mask g W (listHit H W (S.erase c))

/-- Scan the pre-randomized order and keep a failed list exactly when it is
 disjoint from every previously kept failed list. -/
noncomputable def greedyFailed {C : Type*} [Fintype C] [DecidableEq C]
    (items : List (Finset C)) (bad : Finset C → Prop) : Finset (Finset C) :=
  items.foldl (fun A S => if bad S ∧ ∀ S' ∈ A, Disjoint S S' then insert S A else A) ∅

noncomputable def failedFamily (Geom : ProjectionGeometry κ 𝒯 i)
    (H : PrimitiveHistory κ 𝒯 i mesh) (mask : Masks H)
    (g : Group 𝒯 i) (W : ∀ r, H.Val r) : Finset (Finset H.Center) :=
  let items := List.ofFn fun a : Fin (Fintype.card (SmallList H.Device (𝒯.tScale i))) =>
    ((Fintype.equivFin (SmallList H.Device (𝒯.tScale i))).symm (H.searchOrder g W a)).1
  greedyFailed items fun S => admissibleList Geom H g W S ∧ ¬ listGood H mask g W S

noncomputable def marked (Geom : ProjectionGeometry κ 𝒯 i)
    (H : PrimitiveHistory κ 𝒯 i mesh) (mask : Masks H)
    (g : Group 𝒯 i) (W : ∀ r, H.Val r) : Finset H.Center :=
  (failedFamily Geom H mask g W).biUnion id

/-- Eligibility reads positions, tuples, masks and search orders, before
activation and the independent choice ties. -/
noncomputable def eligible (Geom : ProjectionGeometry κ 𝒯 i)
    (H : PrimitiveHistory κ 𝒯 i mesh) (mask : Masks H) (W : ∀ r, H.Val r) : H.Device.EligMap :=
  fun v j => ((candidateBall H v j).filter fun c => H.present W c = true) \
    (Finset.univ.biUnion fun g : Group 𝒯 i =>
      if ∃ u ∈ groupNeighborhood g, Geom.project u.1 = v then marked Geom H mask g W else ∅)

/-- The exact long height rule and uniform active eligible tie of L3.8. -/
noncomputable def selected (Geom : ProjectionGeometry κ 𝒯 i)
    (H : PrimitiveHistory κ 𝒯 i mesh) (mask : Masks H) (W : ∀ r, H.Val r)
    (v : EvenRole 𝒯 i) : Option H.Center :=
  H.Device.selection (siteSet Geom) (H.present W) (H.active W)
    (eligible Geom H mask W) (H.ties W) (Geom.project v.1)

noncomputable def realizedList (Geom : ProjectionGeometry κ 𝒯 i)
    (H : PrimitiveHistory κ 𝒯 i mesh) (mask : Masks H)
    (g : Group 𝒯 i) (W : ∀ r, H.Val r) : Finset H.Center :=
  Finset.univ.filter fun c => ∃ v ∈ groupNeighborhood g, selected Geom H mask W v = some c

noncomputable def groupValid (Geom : ProjectionGeometry κ 𝒯 i)
    (H : PrimitiveHistory κ 𝒯 i mesh) (mask : Masks H)
    (g : Group 𝒯 i) (W : ∀ r, H.Val r) : Prop :=
  (∀ v ∈ groupNeighborhood g, ∃ c, selected Geom H mask W v = some c ∧
    (((candidateBall H (Geom.project v.1) c.2).filter fun d => H.present W d = true).card : ℝ) ≤
      2 * H.Device.lam) ∧
    admissibleList Geom H g W (realizedList Geom H mask g W) ∧
    listGood H mask g W (realizedList Geom H mask g W)

noncomputable def starValid (Geom : ProjectionGeometry κ 𝒯 i)
    (H : PrimitiveHistory κ 𝒯 i mesh) (mask : Masks H)
    (v : EvenRole 𝒯 i) (W : ∀ r, H.Val r) : Prop :=
  (∀ g, v ∈ groupNeighborhood g → groupValid Geom H mask g W) ∧
  (∀ u ∈ H.Device.domBall (siteSet Geom) (Geom.project v.1) H.Device.Rlong, ∀ j,
    (((candidateBall H u j).filter fun c => H.present W c = true).card : ℝ) ≤
      2 * H.Device.lam ∧ H.Device.lam / 2 ≤ (eligible Geom H mask W u j).card) ∧
  ∃ c, selected Geom H mask W v = some c

/-- Masks are fixed lookup tables: changing any center tuple, bit or tie does
not alter a group's mask when its mask vertex is unchanged. -/
def MaskLookup (H : PrimitiveHistory κ 𝒯 i mesh) (mask : Masks H) : Prop :=
  ∀ g W W', H.maskVertex g W = H.maskVertex g W' →
    (mask g W).prior = (mask g W').prior ∧ (mask g W).within = (mask g W').within

/-- Position counts need a quarter-margin before the failed-list deletion. -/
def PositionCountGate (H : PrimitiveHistory κ 𝒯 i mesh) (W : ∀ r, H.Val r) : Prop :=
  ∀ v j, |(((candidateBall H v j).filter fun c => H.present W c = true).card : ℝ) -
    H.Device.lam| ≤ H.Device.lam / 4

def PositionCountConcentration (hconst : HeightConstantContract κ)
    (H : PrimitiveHistory κ 𝒯 i mesh) : Prop :=
  ∀ p, (H.recLaw p).pr (fun W => ¬ PositionCountGate H W) ≤
    Real.exp (-Real.rpow ((𝒯.P i).h : ℝ) (1 + hconst.sliceExponent))

/-- Each query indexes an actual finite set of distinct present IDs, with its
corner-conditioned product tuple law. No model is demanded for an empty list. -/
structure ListFamily (Geom : ProjectionGeometry κ 𝒯 i)
    (H : PrimitiveHistory κ 𝒯 i mesh) (mask : Masks H) where
  model : ∀ p g W, 0 < (H.recLaw p).w W →
    ∀ S, admissibleList Geom H g W S → ListTestModel κ 𝒯 i
  ids : ∀ p g W hW S hS, (model p g W hW S hS).Id ≃ S
  first_law : ∀ p g W hW S hS c,
    (model p g W hW S hS).firstLaw c = H.prior (H.cornerOf W (ids p g W hW S hS c).1)
  prior : ∀ p g W hW S hS D,
    (model p g W hW S hS).binPrior.w D = (mask g W).prior D
  within : ∀ p g W hW S hS D y,
    ((model p g W hW S hS).binDist D).w y = (mask g W).within D y
  count : ∀ p g W hW S hS, Fintype.card (model p g W hW S hS).Id ≤ 𝒯.tScale i

/-- Joint position-count and eligibility estimates for the concrete greedy
marking, before activation (TeX 29, 68). The shared gate also supplies the
position upper bounds required by star validity (TeX 93). -/
structure EligibilityFacts (hconst : HeightConstantContract κ)
    (Geom : ProjectionGeometry κ 𝒯 i) (H : PrimitiveHistory κ 𝒯 i mesh)
    (mask : Masks H) : Prop where
  eligible_subset : ∀ W v j c, c ∈ eligible Geom H mask W v j →
    c ∈ candidateBall H v j ∧ H.present W c = true
  eligible_gate : ∀ p, (H.recLaw p).pr (fun W =>
    ¬ (PositionCountGate H W ∧
      ∀ v ∈ siteSet Geom, ∀ j,
        H.Device.lam / 2 ≤ (eligible Geom H mask W v j).card)) ≤
      2 * Real.exp (-Real.rpow ((𝒯.P i).h : ℝ) (1 + hconst.sliceExponent))

end Rules
/-- All nonempty, supported queries have corner-conditioned list-test models. -/
theorem candidate_list_models (κ : CConsts) (hκ : κ.Admissible)
    {T : Stage} {k : ℕ} {𝒯 : Tiling κ T k} (h𝒯 : Tiling.Valid 𝒯)
    (hcluster : 𝒯.mode.isCluster) {i : Fin 𝒯.m} {mesh : Mesh 𝒯}
    (scales : PatchScales 𝒯 i) (Geom : ProjectionGeometry κ 𝒯 i)
    (H : PrimitiveHistory κ 𝒯 i mesh) (mask : Masks H) :
    Nonempty (ListFamily Geom H mask) := by
  classical
  have record_pos {p : mesh.Param} {W : ∀ r, H.Val r}
      (hW : 0 < (H.recLaw p).w W) (r : H.Rec) :
      0 < H.lawRec p r (W r) := by
    have hprod : 0 < ∏ r, H.lawRec p r (W r) := by
      change 0 < ∏ r, H.lawRec p r (W r) at hW
      exact hW
    have hne : H.lawRec p r (W r) ≠ 0 := by
      intro hz
      have hzero : (∏ r, H.lawRec p r (W r)) = 0 :=
        Finset.prod_eq_zero (Finset.mem_univ r) hz
      rw [hzero] at hprod
      norm_num at hprod
    exact lt_of_le_of_ne (by
      simpa [PrimitiveHistory.lawRec] using (H.record p r).nonneg (W r)) (Ne.symm hne)
  have centerActive {p : mesh.Param} {W : ∀ r, H.Val r}
      (hW : 0 < (H.recLaw p).w W) (c : H.Center) :
      0 < mesh.wt (H.cornerOf W c) p := by
    have hc := record_pos hW (Sum.inl c)
    have hc' : 0 < (H.centerLaw p).w (W (Sum.inl c)) := by
      simpa [PrimitiveHistory.lawRec, PrimitiveHistory.record] using hc
    have hwt : 0 < mesh.wt (W (Sum.inl c)).1 p := by
      by_contra hn
      have hz : mesh.wt (W (Sum.inl c)).1 p = 0 :=
        le_antisymm (le_of_not_gt hn) (mesh.wt_nonneg _ _)
      simp [PrimitiveHistory.centerLaw, FinLaw.bind, PrimitiveHistory.vertexLaw,
        PrimitiveHistory.tuplePrior, lawToFinLaw, FinLaw.pi,
        PrimitiveHistory.finProbToFinLaw, FinProb.bernoulli, hz] at hc'
    simpa [PrimitiveHistory.cornerOf] using hwt
  have groupActive {p : mesh.Param} {W : ∀ r, H.Val r}
      (hW : 0 < (H.recLaw p).w W) (g : Group 𝒯 i) :
      0 < mesh.wt (H.maskVertex g W) p := by
    have hg := record_pos hW (Sum.inr (Sum.inl g))
    have hg' : 0 < (H.groupLaw p).w (W (Sum.inr (Sum.inl g))) := by
      simpa [PrimitiveHistory.lawRec, PrimitiveHistory.record] using hg
    have hwt : 0 < mesh.wt (W (Sum.inr (Sum.inl g))).1 p := by
      by_contra hn
      have hz : mesh.wt (W (Sum.inr (Sum.inl g))).1 p = 0 :=
        le_antisymm (le_of_not_gt hn) (mesh.wt_nonneg _ _)
      simp [PrimitiveHistory.groupLaw, FinLaw.bind, PrimitiveHistory.vertexLaw,
        PrimitiveHistory.finProbToFinLaw, FinProb.uniformAll, hz] at hg'
    simpa [PrimitiveHistory.maskVertex] using hwt
  have patchX_subset : (𝒯.P i).X ⊆ T.X k := by
    exact (h𝒯.patch_supports i).1.trans
      ((h𝒯.patch_supports i).2.1.trans Finset.sdiff_subset)
  refine ⟨{
    model := fun p g W hW S hS => by
      let c₀ : H.Center := Classical.choose hS.1
      have hc₀ : c₀ ∈ S := Classical.choose_spec hS.1
      letI : Fintype {c : H.Center // c ∈ S} := Fintype.ofFinite _
      refine {
        Id := {c : H.Center // c ∈ S}
        idNonempty := ⟨⟨c₀, hc₀⟩⟩
        binPrior := {
          w := (mask g W).prior
          nonneg := (mask g W).prior_nonneg
          sum_eq_one := (mask g W).prior_sum
        }
        binDist := fun D => {
          w := (mask g W).within D
          nonneg := (mask g W).within_nonneg D
          sum_eq_one := (mask g W).within_sum D
        }
        firstLaw := fun c => H.prior (H.cornerOf W c.1)
        bin_support := by
          intro D y hy
          change (mask g W).within D y = 0
          by_contra hne
          exact hy ((mask g W).within_support D y hne)
        first_law_supported := by
          intro c y hy
          exact H.prior_support (H.cornerOf W c.1) y (fun hmem => hy (patchX_subset hmem))
        aggregate_cap := (mask g W).aggregate_masked_mass
        width_bound := by
          intro c x
          exact (H.prior_cap (H.cornerOf W c.1) p (centerActive hW c.1) x).trans
            scales.prior_width
        codegree_bound := by
          intro c b y y' hb hy hy'
          change (mask g W).prior b > 0 at hb
          have hret : b ∈ (mask g W).retained := by
            rw [(mask g W).prior_uniform b] at hb
            by_contra hnot
            simp [hnot] at hb
          have hycheap : y ∈ (mask g W).cheap b := by
            by_contra hnot
            have hz : (mask g W).within b y = 0 := by
              rw [(mask g W).within_uniform b y]
              simp [hret, hnot]
            exact hy (by simpa using hz)
          have hy'cheap : y' ∈ (mask g W).cheap b := by
            by_contra hnot
            have hz : (mask g W).within b y' = 0 := by
              rw [(mask g W).within_uniform b y']
              simp [hret, hnot]
            exact hy' (by simpa using hz)
          let v' := H.cornerOf W c.1
          have hactive := centerActive hW c.1
          have hprior := H.prior_uniform v' p hactive
          have hcorner_pos : 0 < ((mesh.corner v' i).card : ℝ) := by
            by_contra hnot
            have hcardzero : (mesh.corner v' i).card = 0 := by
              exact Nat.eq_zero_of_not_pos (fun hpos => hnot (by exact_mod_cast hpos))
            have hempty : mesh.corner v' i = ∅ := Finset.card_eq_zero.mp hcardzero
            have hweights : ∀ x, (H.prior v').w x = 0 := by
              intro x
              rw [hprior x]
              simp [hempty]
            have hsum : ∑ x, (H.prior v').w x = 0 := by
              apply Finset.sum_eq_zero
              intro x hx
              exact hweights x
            rw [(H.prior v').sum_eq_one] at hsum
            norm_num at hsum
          have hmean :
              ∑ x, (H.prior v').w x * hit (T.S.E k) 𝒯.c x y * hit (T.S.E k) 𝒯.c x y' =
                (∑ x ∈ mesh.corner v' i,
                  hit (T.S.E k) 𝒯.c x y * hit (T.S.E k) 𝒯.c x y') /
                    (mesh.corner v' i).card := by
            calc
              _ = ∑ x, (if x ∈ mesh.corner v' i then
                    (1 : ℝ) / ((mesh.corner v' i).card : ℝ) else 0) *
                    (hit (T.S.E k) 𝒯.c x y * hit (T.S.E k) 𝒯.c x y') := by
                      apply Finset.sum_congr rfl
                      intro x hx
                      rw [hprior x]
                      ring
              _ = (∑ x ∈ mesh.corner v' i,
                    hit (T.S.E k) 𝒯.c x y * hit (T.S.E k) 𝒯.c x y') /
                    (mesh.corner v' i).card := by
                      simp only [ite_mul, zero_mul, Finset.sum_ite_mem, Finset.univ_inter]
                      rw [← Finset.mul_sum]
                      ring
          have hcodeg := (mask g W).cleaned_codegree hcluster p v' hactive
            b y y' hycheap hy'cheap
          rw [← hmean] at hcodeg
          exact hcodeg
        budget := by
          have hcard : Fintype.card {c : H.Center // c ∈ S} ≤ 𝒯.tScale i := by
            simpa using hS.2.1
          have hcard' : (Fintype.card {c : H.Center // c ∈ S} : ℝ) ≤ 𝒯.tScale i :=
            by exact_mod_cast hcard
          calc
            2 * (𝒯.kScale i : ℝ) * (Fintype.card {c : H.Center // c ∈ S} : ℝ) +
                Real.log ((T.S.N k : ℝ) / (𝒯.P i).M) + 3 ≤
              2 * (𝒯.kScale i : ℝ) * 𝒯.tScale i +
                Real.log ((T.S.N k : ℝ) / (𝒯.P i).M) + 3 := by
                  gcongr
            _ ≤ (T.S.n k : ℝ) ^ κ.η0 / 2 := scales.budget
      }
    ids := fun _ _ _ _ _ _ => Equiv.refl _
    first_law := by intro p g W hW S hS c; rfl
    prior := by intro p g W hW S hS D; rfl
    within := by intro p g W hW S hS D y; rfl
    count := by
      intro p g W hW S hS
      simpa using hS.2.1
  }⟩

set_option maxHeartbeats 1000000 in
theorem position_count_concentration (κ : CConsts) (hκ : κ.Admissible)
    (hconst : HeightConstantContract κ)
    {T : Stage} {k : ℕ} {𝒯 : Tiling κ T k} {i : Fin 𝒯.m} {mesh : Mesh 𝒯}
    (scales : PatchScales 𝒯 i) (H : PrimitiveHistory κ 𝒯 i mesh) :
    PositionCountConcentration hconst H := by
  classical
  intro p
  let q : ℝ := H.Device.lam / (H.Device.V : ℝ)
  have hnums := hconst.threshold_slack (𝒯.P i).h scales.h_large
  dsimp [Section14Numerics] at hnums
  rcases hnums with ⟨_, _, hLamV, _, _, _, _, hfinal, _⟩
  have hLamVdev : H.Device.lam ≤ (H.Device.V : ℝ) / 2 := by
    simpa [PrimitiveHistory.Device, patchHD, HDParams.lam, HDParams.V] using hLamV
  have hLamPos : 0 < H.Device.lam := by
    have hh : 0 < (𝒯.P i).h := lt_of_lt_of_le hκ.h0_pos scales.h_large
    dsimp [PrimitiveHistory.Device, patchHD, HDParams.lam]
    positivity
  have hVpos : 0 < (H.Device.V : ℝ) := by
    nlinarith [hLamVdev, hLamPos]
  have hq0 : 0 ≤ q := by
    dsimp [q]
    exact div_nonneg hLamPos.le (Nat.cast_nonneg _)
  have hq1 : q ≤ 1 := by
    dsimp [q]
    rw [div_le_iff₀ hVpos]
    nlinarith [hLamVdev]
  have hbern (s : ℝ) :
      (PrimitiveHistory.finProbToFinLaw (FinProb.bernoulli q)).E
        (fun b => Real.exp (s * if b then (1 : ℝ) else 0)) =
        1 + q * (Real.exp s - 1) := by
    simp [FinLaw.E, PrimitiveHistory.finProbToFinLaw, FinProb.bernoulli, hq0, hq1]
    <;> ring
  have hcenterMoment (s : ℝ) :
      (H.centerLaw p).E (fun z => Real.exp (s * if z.2.2.1 then (1 : ℝ) else 0)) =
        1 + q * (Real.exp s - 1) := by
    let presentLaw := PrimitiveHistory.finProbToFinLaw (FinProb.bernoulli q)
    let activationLaw := PrimitiveHistory.finProbToFinLaw
      (FinProb.bernoulli ((H.Device.n : ℝ) ^ H.Device.b₀ / H.Device.lam))
    let bitsLaw := FinLaw.bind presentLaw (fun _ => activationLaw)
    let bitsEval : Bool → ℝ := fun b => Real.exp (s * if b then (1 : ℝ) else 0)
    let bitsFun : Bool × Bool → ℝ := fun z => bitsEval z.1
    let tupleFun : H.Tuple × (Bool × Bool) → ℝ := fun z => bitsFun z.2
    let tupleBitsLaw (v : mesh.V) := FinLaw.bind (H.tuplePrior v) (fun _ => bitsLaw)
    have hbits : bitsLaw.E bitsFun = 1 + q * (Real.exp s - 1) := by
      change (FinLaw.bind presentLaw (fun _ => activationLaw)).E
        (fun z => bitsEval z.1) = _
      rw [Lane_q_s14_hist.bind_E_fst]
      simpa [presentLaw, bitsEval, FinLaw.E] using hbern s
    have htuple (v : mesh.V) : (tupleBitsLaw v).E tupleFun =
        1 + q * (Real.exp s - 1) := by
      change (FinLaw.bind (H.tuplePrior v) (fun _ => bitsLaw)).E
        (fun z => bitsFun z.2) = _
      rw [Lane_q_s14_hist.bind_E_snd, hbits]
      rw [← Finset.sum_mul, (H.tuplePrior v).sum_one]
      ring
    change (FinLaw.bind (PrimitiveHistory.vertexLaw p)
      (fun v => FinLaw.bind (H.tuplePrior v) (fun _ => bitsLaw))).E
        (fun z => tupleFun z.2) = _
    rw [Lane_q_s14_hist.bind_E_snd]
    calc
      _ = ∑ v, (PrimitiveHistory.vertexLaw p).w v *
          (1 + q * (Real.exp s - 1)) := by
            apply Finset.sum_congr rfl
            intro v hv
            exact congrArg (fun x : ℝ => (PrimitiveHistory.vertexLaw p).w v * x)
              (by simpa [tupleBitsLaw] using htuple v)
      _ = _ := by
            rw [← Finset.sum_mul, (PrimitiveHistory.vertexLaw p).sum_one]
            ring
  have hballCard (v : OAI.HypercubeRamsey.CubeVertex H.Device.d) (j : Fin (H.Device.H + 1)) :
      ((Finset.univ.filter fun c : H.Center =>
        c.2 = j ∧ hammingDist c.1 v ≤ H.Device.r).card : ℝ) = H.Device.V := by
    have hNat : (Finset.univ.filter fun c : H.Center =>
        c.2 = j ∧ hammingDist c.1 v ≤ H.Device.r).card = H.Device.V := by
      simpa [PrimitiveHistory.Device, PrimitiveHistory.Center, patchHD,
        HDParams.Loc, HDParams.V] using
          Lane_q_s14_hist.levelBall_card H.Device.d H.Device.H H.Device.r j v
    exact_mod_cast hNat
  have hballIndicators (v : OAI.HypercubeRamsey.CubeVertex H.Device.d) (j : Fin (H.Device.H + 1)) :
      (∑ c : H.Center,
        if c.2 = j ∧ hammingDist c.1 v ≤ H.Device.r then (1 : ℝ) else 0) =
          (H.Device.V : ℝ) := by
    calc
      _ = ((Finset.univ.filter fun c : H.Center =>
          c.2 = j ∧ hammingDist c.1 v ≤ H.Device.r).card : ℝ) := by
            simp [Finset.sum_ite_mem, Finset.univ_inter]
      _ = _ := hballCard v j
  have hinside (v : OAI.HypercubeRamsey.CubeVertex H.Device.d)
      (j : Fin (H.Device.H + 1)) :
      (∑ r : H.Rec, if ∃ c : H.Center, r = Sum.inl c ∧
          c.2 = j ∧ hammingDist c.1 v ≤ H.Device.r then (1 : ℝ) else 0) =
        (H.Device.V : ℝ) := by
    calc
      _ = ∑ c : H.Center,
          if c.2 = j ∧ hammingDist c.1 v ≤ H.Device.r then (1 : ℝ) else 0 := by
            rw [Fintype.sum_sum_type, Fintype.sum_sum_type]
            simp [PrimitiveHistory.Rec]
      _ = (H.Device.V : ℝ) := hballIndicators v j
  let term (v : OAI.HypercubeRamsey.CubeVertex H.Device.d) (j : Fin (H.Device.H + 1)) :
      ∀ r : H.Rec, H.Val r → ℝ := fun r =>
    match r with
    | .inl c => fun z =>
        if c.2 = j ∧ hammingDist c.1 v ≤ H.Device.r then
          if z.2.2.1 then 1 else 0 else 0
    | .inr (.inl _) => fun _ => 0
    | .inr (.inr _) => fun _ => 0
  let count (v : OAI.HypercubeRamsey.CubeVertex H.Device.d) (j : Fin (H.Device.H + 1))
      (W : ∀ r, H.Val r) : ℝ :=
    (((candidateBall H v j).filter fun c => H.present W c = true).card : ℝ)
  have hcount (v : OAI.HypercubeRamsey.CubeVertex H.Device.d) (j : Fin (H.Device.H + 1))
      (W : ∀ r, H.Val r) : count v j W = ∑ r : H.Rec, term v j r (W r) := by
    let S := candidateBall H v j
    have hnat : ((S.filter fun c => H.present W c = true).card : ℕ) =
        ∑ c : H.Center, if c ∈ S then if H.present W c = true then 1 else 0 else 0 := by
      rw [Finset.card_eq_sum_ite
        (s := S.filter fun c => H.present W c = true)
        (t := Finset.univ) (Finset.subset_univ _)]
      simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      apply Finset.sum_congr rfl
      intro c hc
      by_cases hs : c ∈ S <;> by_cases hp : H.present W c = true <;>
        simp [hs, hp]
    have hreal : ((S.filter fun c => H.present W c = true).card : ℝ) =
        ∑ c : H.Center, if c ∈ S then if H.present W c = true then (1 : ℝ) else 0 else 0 := by
      exact_mod_cast hnat
    calc
      count v j W =
          ∑ c : H.Center, if c ∈ S then if H.present W c = true then (1 : ℝ) else 0 else 0 := by
            exact hreal
      _ = ∑ r : H.Rec, term v j r (W r) := by
            simp [term, PrimitiveHistory.Rec, PrimitiveHistory.present, S, candidateBall]
            rfl
  have recordProduct (f : ∀ r : H.Rec, H.Val r → ℝ) :
      (H.recLaw p).E (fun W => ∏ r, f r (W r)) =
        ∏ r, (H.record p r).E (f r) := by
    simpa [PrimitiveHistory.recLaw, recordLaw, PrimitiveHistory.lawRec] using
      (Lane_q_s14_hist.pi_expect_prod (fun r : H.Rec => H.record p r) f)
  have hfactor (s : ℝ) (v : OAI.HypercubeRamsey.CubeVertex H.Device.d) (j : Fin (H.Device.H + 1))
      (r : H.Rec) :
      (H.record p r).E (fun z => Real.exp (s * term v j r z)) =
        match r with
        | .inl c => if c.2 = j ∧ hammingDist c.1 v ≤ H.Device.r then
            1 + q * (Real.exp s - 1) else 1
        | .inr _ => 1 := by
    cases r with
    | inl c =>
        by_cases hc : c.2 = j ∧ hammingDist c.1 v ≤ H.Device.r
        · simpa [term, hc, PrimitiveHistory.record] using hcenterMoment s
        · simp [term, hc, PrimitiveHistory.record, Lane_q_s14_hist.E_const]
    | inr r =>
        cases r <;> simp [term, PrimitiveHistory.record, Lane_q_s14_hist.E_const]
  have hmgf (s : ℝ) (v : OAI.HypercubeRamsey.CubeVertex H.Device.d) (j : Fin (H.Device.H + 1)) :
      (H.recLaw p).E (fun W => Real.exp (s * count v j W)) ≤
        Real.exp (H.Device.lam * (Real.exp s - 1)) := by
    let f : ∀ r : H.Rec, H.Val r → ℝ := fun r z => Real.exp (s * term v j r z)
    have hexp (W : ∀ r, H.Val r) :
        Real.exp (s * count v j W) = ∏ r, f r (W r) := by
      rw [← Real.exp_sum]
      congr 1
      rw [hcount, Finset.mul_sum]
    have hfact : (H.recLaw p).E (fun W => ∏ r, f r (W r)) =
        ∏ r, (H.record p r).E (f r) := recordProduct f
    have hnonneg (r : H.Rec) : 0 ≤ (H.record p r).E (f r) := by
      unfold FinLaw.E f
      exact Finset.sum_nonneg fun z hz =>
        mul_nonneg ((H.record p r).nonneg z) (Real.exp_nonneg _)
    have hbound (r : H.Rec) :
        (H.record p r).E (f r) ≤ Real.exp (q * (Real.exp s - 1) *
          (if ∃ c : H.Center, r = Sum.inl c ∧
              c.2 = j ∧ hammingDist c.1 v ≤ H.Device.r then (1 : ℝ) else 0)) := by
      cases r with
      | inl c =>
          by_cases hc : c.2 = j ∧ hammingDist c.1 v ≤ H.Device.r
          · simp [f, hfactor, hc]
            simpa [add_comm] using (Real.add_one_le_exp (q * (Real.exp s - 1)))
          · simp [f, hfactor, hc]
      | inr r => cases r <;> simp [f, hfactor]
    letI : PosMulMono ℝ := ⟨fun {a} ha {b c} hbc => mul_le_mul_of_nonneg_left hbc ha⟩
    calc
      (H.recLaw p).E (fun W => Real.exp (s * count v j W)) =
          (H.recLaw p).E (fun W => ∏ r, f r (W r)) := by
            congr 1
            funext W
            exact hexp W
      _ = ∏ r, (H.record p r).E (f r) := hfact
      _ ≤ ∏ r, Real.exp (q * (Real.exp s - 1) *
          (if ∃ c : H.Center, r = Sum.inl c ∧
              c.2 = j ∧ hammingDist c.1 v ≤ H.Device.r then (1 : ℝ) else 0)) := by
            apply Finset.prod_le_prod₀
            · intro r hr
              exact hnonneg r
            · intro r hr
              exact hbound r
      _ = Real.exp (H.Device.lam * (Real.exp s - 1)) := by
            rw [← Real.exp_sum]
            congr 1
            calc
              _ = q * (Real.exp s - 1) *
                    ∑ r : H.Rec, (if ∃ c : H.Center, r = Sum.inl c ∧
                      c.2 = j ∧ hammingDist c.1 v ≤ H.Device.r then (1 : ℝ) else 0) := by
                    rw [Finset.mul_sum]
              _ = q * (Real.exp s - 1) * (H.Device.V : ℝ) := by rw [hinside v j]
              _ = H.Device.lam * (Real.exp s - 1) := by
                    dsimp [q]
                    have hVne : (H.Device.V : ℝ) ≠ 0 :=
                      (Nat.cast_pos.mpr (by exact_mod_cast hVpos)).ne'
                    field_simp [hVne]
  have hExpUpper : Real.exp (1 / 5 : ℝ) ≤ 59 / 48 := by
    have hlog := Real.le_log_one_add_of_nonneg (x := (11 : ℝ) / 48) (by norm_num)
    have hlog' : 1 / 5 ≤ Real.log (59 / 48) := by
      have hfrac : (1 : ℝ) / 5 ≤ 2 * ((11 : ℝ) / 48) / ((11 : ℝ) / 48 + 2) := by norm_num
      calc
        (1 : ℝ) / 5 ≤ 2 * ((11 : ℝ) / 48) / ((11 : ℝ) / 48 + 2) := hfrac
        _ ≤ Real.log (1 + (11 : ℝ) / 48) := hlog
        _ = Real.log (59 / 48) := by congr 1 <;> norm_num
    calc
      Real.exp (1 / 5 : ℝ) ≤ Real.exp (Real.log (59 / 48)) := Real.exp_le_exp.mpr hlog'
      _ = 59 / 48 := Real.exp_log (by norm_num)
  have hExpNegFourth : Real.exp (-(1 / 4 : ℝ)) ≤ 19 / 24 := by
    have hquarter : (81 : ℝ) / 64 ≤ Real.exp (1 / 4) := by
      have hsmall := Real.add_one_le_exp (1 / 8 : ℝ)
      have hsmall' : (1 : ℝ) + 1 / 8 ≤ Real.exp (1 / 8) := by linarith [hsmall]
      have hpow : (1 + (1 : ℝ) / 8) ^ 2 ≤ Real.exp (1 / 8) ^ 2 := by
        nlinarith [mul_nonneg (sub_nonneg.mpr hsmall')
          (add_nonneg (by norm_num : (0 : ℝ) ≤ 1 + (1 : ℝ) / 8) (Real.exp_nonneg (1 / 8)))]
      calc
        (81 : ℝ) / 64 = (1 + (1 : ℝ) / 8) ^ 2 := by norm_num
        _ ≤ Real.exp (1 / 8) ^ 2 := hpow
        _ = Real.exp (1 / 4) := by
          calc
            Real.exp (1 / 8) ^ 2 = Real.exp (1 / 8) * Real.exp (1 / 8) := by ring
            _ = Real.exp (1 / 8 + 1 / 8) := by
              rw [← Real.exp_add]
            _ = Real.exp (1 / 4) := by congr 1 <;> norm_num
    calc
      Real.exp (-(1 / 4 : ℝ)) = (Real.exp (1 / 4))⁻¹ := by rw [Real.exp_neg]
      _ ≤ ((81 : ℝ) / 64)⁻¹ :=
        (inv_le_inv₀ (Real.exp_pos _) (by norm_num)).mpr hquarter
      _ = 64 / 81 := by norm_num
      _ ≤ 19 / 24 := by norm_num
  have hupper (v : OAI.HypercubeRamsey.CubeVertex H.Device.d) (j : Fin (H.Device.H + 1)) :
      (H.recLaw p).pr (fun W => 5 * H.Device.lam / 4 ≤ count v j W) ≤
        Real.exp (-H.Device.lam / 48) := by
    have hmark := Lane_q_s14_hist.pr_exp_markov (H.recLaw p)
      (fun W => count v j W) (1 / 5) (5 * H.Device.lam / 4) (by norm_num)
    have hmoment := hmgf (1 / 5) v j
    have hcoef : -(1 / 5 : ℝ) * (5 / 4) + (Real.exp (1 / 5) - 1) ≤ -(1 / 48 : ℝ) := by
      norm_num
      linarith [hExpUpper]
    calc
      _ ≤ Real.exp (-(1 / 5 : ℝ) * (5 * H.Device.lam / 4)) *
          (H.recLaw p).E (fun W => Real.exp ((1 / 5 : ℝ) * count v j W)) := hmark
      _ ≤ Real.exp (-(1 / 5 : ℝ) * (5 * H.Device.lam / 4)) *
          Real.exp (H.Device.lam * (Real.exp (1 / 5) - 1)) :=
            mul_le_mul_of_nonneg_left hmoment (Real.exp_nonneg _)
      _ ≤ Real.exp (-H.Device.lam / 48) := by
            rw [← Real.exp_add]
            apply Real.exp_le_exp.mpr
            have hterm := mul_le_mul_of_nonneg_left hcoef hLamPos.le
            nlinarith [hterm]
  have hlower (v : OAI.HypercubeRamsey.CubeVertex H.Device.d) (j : Fin (H.Device.H + 1)) :
      (H.recLaw p).pr (fun W => count v j W ≤ 3 * H.Device.lam / 4) ≤
        Real.exp (-H.Device.lam / 48) := by
    have hmark := Lane_q_s14_hist.pr_exp_markov (H.recLaw p)
      (fun W => -count v j W) (1 / 4) (-(3 * H.Device.lam / 4)) (by norm_num)
    have hmoment := hmgf (-(1 / 4 : ℝ)) v j
    have hmoment' : (H.recLaw p).E
        (fun W => Real.exp ((1 / 4 : ℝ) * (-count v j W))) ≤
          Real.exp (H.Device.lam * (Real.exp (-(1 / 4 : ℝ)) - 1)) := by
      simpa [neg_mul] using hmoment
    have hcoef : (3 / 16 : ℝ) + (Real.exp (-(1 / 4 : ℝ)) - 1) ≤ -(1 / 48 : ℝ) := by
      have h := sub_le_sub_right hExpNegFourth 1
      norm_num at h ⊢
      linarith
    have hEvent :
        (fun W => count v j W ≤ 3 * H.Device.lam / 4) =
          (fun W => -(3 * H.Device.lam / 4) ≤ -count v j W) := by
      funext W
      apply propext
      constructor <;> intro h <;> linarith
    calc
      (H.recLaw p).pr (fun W => count v j W ≤ 3 * H.Device.lam / 4) =
          (H.recLaw p).pr (fun W => -(3 * H.Device.lam / 4) ≤ -count v j W) := by
            rw [hEvent]
      _ ≤ Real.exp (-(1 / 4 : ℝ) * (-(3 * H.Device.lam / 4))) *
          (H.recLaw p).E (fun W => Real.exp ((1 / 4 : ℝ) * (-count v j W))) := hmark
      _ ≤ Real.exp (-(1 / 4 : ℝ) * (-(3 * H.Device.lam / 4))) *
          Real.exp (H.Device.lam * (Real.exp (-(1 / 4 : ℝ)) - 1)) :=
            mul_le_mul_of_nonneg_left hmoment' (Real.exp_nonneg _)
      _ ≤ Real.exp (-H.Device.lam / 48) := by
            rw [← Real.exp_add]
            apply Real.exp_le_exp.mpr
            have hterm := mul_le_mul_of_nonneg_left hcoef hLamPos.le
            nlinarith [hterm]
  let Index := OAI.HypercubeRamsey.CubeVertex H.Device.d × Fin (H.Device.H + 1)
  let bad (x : Index) (W : ∀ r, H.Val r) : Prop :=
    ¬ |count x.1 x.2 W - H.Device.lam| ≤ H.Device.lam / 4
  have hlocal (x : Index) :
      (H.recLaw p).pr (bad x) ≤ 2 * Real.exp (-H.Device.lam / 48) := by
    have hsubset (W : ∀ r, H.Val r) : bad x W →
        (count x.1 x.2 W ≤ 3 * H.Device.lam / 4) ∨
          5 * H.Device.lam / 4 ≤ count x.1 x.2 W := by
      intro hbad
      by_cases hlo : count x.1 x.2 W ≤ 3 * H.Device.lam / 4
      · exact Or.inl hlo
      · apply Or.inr
        by_contra hhi
        have hlow' : 3 * H.Device.lam / 4 < count x.1 x.2 W := lt_of_not_ge hlo
        have hhigh' : count x.1 x.2 W < 5 * H.Device.lam / 4 := lt_of_not_ge hhi
        apply hbad
        rw [abs_le]
        constructor <;> linarith
    calc
      _ ≤ (H.recLaw p).pr (fun W =>
          count x.1 x.2 W ≤ 3 * H.Device.lam / 4 ∨
            5 * H.Device.lam / 4 ≤ count x.1 x.2 W) :=
              Lane_q_s14_hist.pr_mono (H.recLaw p) _ _ hsubset
      _ ≤ (H.recLaw p).pr (fun W => count x.1 x.2 W ≤ 3 * H.Device.lam / 4) +
          (H.recLaw p).pr (fun W => 5 * H.Device.lam / 4 ≤ count x.1 x.2 W) :=
              Lane_q_s14_hist.pr_or_le (H.recLaw p) _ _
      _ ≤ Real.exp (-H.Device.lam / 48) + Real.exp (-H.Device.lam / 48) :=
            add_le_add (hlower x.1 x.2) (hupper x.1 x.2)
      _ = 2 * Real.exp (-H.Device.lam / 48) := by ring
  have hbad_eq :
      (fun W => ¬ PositionCountGate H W) = (fun W => ∃ x : Index, bad x W) := by
    funext W
    apply propext
    simp [PositionCountGate, bad, Index, count]
    rfl
  rw [hbad_eq]
  have hsum := Lane_q_s14_hist.pr_exists_le_sum (H.recLaw p) bad
  calc
    (H.recLaw p).pr (fun W => ∃ x : Index, bad x W) ≤ ∑ x : Index,
        (H.recLaw p).pr (bad x) := hsum
    _ ≤ ∑ _x : Index, 2 * Real.exp (-H.Device.lam / 48) := by
      apply Finset.sum_le_sum
      intro x hx
      exact hlocal x
    _ = (2 : ℝ) ^ (𝒯.P i).h * ((H.Device.H + 1 : ℕ) : ℝ) *
          2 * Real.exp (-H.Device.lam / 48) := by
      simp [Index, Finset.sum_const, nsmul_eq_mul]
      push_cast
      simp [PrimitiveHistory.Device, patchHD]
      ring
    _ ≤ Real.exp (-Real.rpow ((𝒯.P i).h : ℝ) (1 + hconst.sliceExponent)) := by
      simpa [PrimitiveHistory.Device, patchHD] using hfinal

private theorem greedy_acc_subset {C : Type*} [Fintype C] [DecidableEq C]
    (items : List (Finset C)) (bad : Finset C → Prop) (A : Finset (Finset C)) :
    A ⊆ items.foldl (fun A S =>
      if bad S ∧ ∀ S' ∈ A, Disjoint S S' then insert S A else A) A := by
  classical
  induction items generalizing A with
  | nil => exact Finset.Subset.refl _
  | cons S items ih =>
    simp only [List.foldl_cons]
    apply Finset.Subset.trans _ (ih _)
    split_ifs
    · exact Finset.subset_insert _ _
    · exact Finset.Subset.refl _

private theorem greedy_covers_bad {C : Type*} [Fintype C] [DecidableEq C]
    (items : List (Finset C)) (bad : Finset C → Prop) (A : Finset (Finset C))
    (S : Finset C) (hne : S.Nonempty) (hmem : S ∈ items) (hbad : bad S) :
    ∃ S' ∈ items.foldl (fun A S =>
      if bad S ∧ ∀ S' ∈ A, Disjoint S S' then insert S A else A) A,
      ¬ Disjoint S S' := by
  classical
  induction items generalizing A with
  | nil => simp at hmem
  | cons B items ih =>
    simp only [List.foldl_cons]
    rcases List.mem_cons.mp hmem with hSB | htail
    · subst B
      by_cases hd : ∀ S' ∈ A, Disjoint S S'
      · rw [if_pos ⟨hbad, hd⟩]
        refine ⟨S, greedy_acc_subset items bad (insert S A) (Finset.mem_insert_self _ _), ?_⟩
        intro hdisj
        obtain ⟨c, hc⟩ := hne
        exact Finset.disjoint_left.mp hdisj hc hc
      · rw [if_neg (fun h => hd h.2)]
        push_neg at hd
        obtain ⟨S', hS', hn⟩ := hd
        exact ⟨S', greedy_acc_subset items bad A hS', hn⟩
    · exact ih _ htail

section GreedyListProof

variable {κ : CConsts} {T : Stage} {k : ℕ} {𝒯 : Tiling κ T k}
  {i : Fin 𝒯.m} {mesh : Mesh 𝒯}

private theorem unmarked_list_good (Geom : ProjectionGeometry κ 𝒯 i)
    (H : PrimitiveHistory κ 𝒯 i mesh) (mask : Masks H)
    (g : Group 𝒯 i) (W : ∀ r, H.Val r) (S : Finset H.Center)
    (hS : admissibleList Geom H g W S) (hdisj : Disjoint S (marked Geom H mask g W)) :
    listGood H mask g W S := by
  classical
  by_contra hbad
  let items := List.ofFn fun a : Fin (Fintype.card (SmallList H.Device (𝒯.tScale i))) =>
    ((Fintype.equivFin (SmallList H.Device (𝒯.tScale i))).symm (H.searchOrder g W a)).1
  have hmem : S ∈ items := by
    let s : SmallList H.Device (𝒯.tScale i) := ⟨S, hS.1, hS.2.1⟩
    let a := (H.searchOrder g W).symm (Fintype.equivFin _ s)
    apply List.mem_ofFn.mpr
    refine ⟨a, ?_⟩
    dsimp only [a]
    rw [Equiv.apply_symm_apply]
    exact congrArg Subtype.val ((Fintype.equivFin (SmallList H.Device (𝒯.tScale i))).symm_apply_apply s)
  obtain ⟨S', hS', hn⟩ := greedy_covers_bad items
    (fun S => admissibleList Geom H g W S ∧ ¬ listGood H mask g W S) ∅ S hS.1 hmem ⟨hS, hbad⟩
  have hfamily : S' ∈ failedFamily Geom H mask g W := hS'
  have hsub : S' ⊆ marked Geom H mask g W := by
    intro c hc
    exact Finset.mem_biUnion.mpr ⟨S', hfamily, hc⟩
  exact hn (hdisj.mono_right hsub)

end GreedyListProof

section EligibilityCountProof

set_option maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency false

variable {κ : CConsts} {T : Stage} {k : ℕ} {𝒯 : Tiling κ T k}
  {i : Fin 𝒯.m} {mesh : Mesh 𝒯}

private theorem greedy_invariant {C : Type*} [Fintype C] [DecidableEq C]
    (items : List (Finset C)) (bad : Finset C → Prop) (A : Finset (Finset C))
    (ha : ∀ S ∈ A, bad S)
    (hd : ∀ S ∈ A, ∀ S' ∈ A, S ≠ S' → Disjoint S S') :
    (∀ S ∈ items.foldl (fun A S => if bad S ∧ ∀ S' ∈ A, Disjoint S S' then insert S A else A) A, bad S) ∧
    (∀ S ∈ items.foldl (fun A S => if bad S ∧ ∀ S' ∈ A, Disjoint S S' then insert S A else A) A,
      ∀ S' ∈ items.foldl (fun A S => if bad S ∧ ∀ S' ∈ A, Disjoint S S' then insert S A else A) A,
        S ≠ S' → Disjoint S S') := by
  classical
  induction items generalizing A with
  | nil => exact ⟨ha,hd⟩
  | cons B items ih =>
    simp only [List.foldl_cons]
    split_ifs with hb
    · apply ih (insert B A)
      · intro S hS
        rcases Finset.mem_insert.mp hS with rfl | hS
        · exact hb.1
        · exact ha S hS
      · intro S hS S' hS' hne
        by_cases hs : S = B
        · by_cases ht : S' = B
          · exact (hne (hs.trans ht.symm)).elim
          · rw [hs]
            exact hb.2 S' ((Finset.mem_insert.mp hS').resolve_left ht)
        · by_cases ht : S' = B
          · rw [ht]
            exact (hb.2 S ((Finset.mem_insert.mp hS).resolve_left hs)).symm
          · exact hd S ((Finset.mem_insert.mp hS).resolve_left hs)
              S' ((Finset.mem_insert.mp hS').resolve_left ht) hne
    · exact ih A ha hd

private theorem failedFamily_facts (Geom : ProjectionGeometry κ 𝒯 i)
    (H : PrimitiveHistory κ 𝒯 i mesh) (mask : Masks H)
    (g : Group 𝒯 i) (W : ∀ r, H.Val r) :
    (∀ S ∈ failedFamily Geom H mask g W,
      admissibleList Geom H g W S ∧ ¬ listGood H mask g W S) ∧
    (∀ S ∈ failedFamily Geom H mask g W, ∀ S' ∈ failedFamily Geom H mask g W,
      S ≠ S' → Disjoint S S') := by
  unfold failedFamily greedyFailed
  apply greedy_invariant
  · simp
  · simp

private theorem marked_card_bound (Geom : ProjectionGeometry κ 𝒯 i)
    (H : PrimitiveHistory κ 𝒯 i mesh) (mask : Masks H)
    (g : Group 𝒯 i) (W : ∀ r, H.Val r) :
    (marked Geom H mask g W).card ≤
      (failedFamily Geom H mask g W).card * 𝒯.tScale i := by
  classical
  unfold marked
  apply (Finset.card_biUnion_le).trans
  calc
    _ ≤ ∑ _S ∈ failedFamily Geom H mask g W, 𝒯.tScale i := by
      apply Finset.sum_le_sum
      intro S hS
      exact ((failedFamily_facts Geom H mask g W).1 S hS).1.2.1
    _ = _ := by simp

private theorem eligible_large_of_small_families (hconst : HeightConstantContract κ)
    (scales : PatchScales 𝒯 i) (Geom : ProjectionGeometry κ 𝒯 i)
    (H : PrimitiveHistory κ 𝒯 i mesh) (mask : Masks H)
    (W : ∀ r, H.Val r) (hcounts : PositionCountGate H W)
    (hf : ∀ g, (failedFamily Geom H mask g W).card < (𝒯.P i).h)
    (v : IWord 𝒯 i) (j : Fin (H.Device.H + 1)) :
    H.Device.lam / 2 ≤ (eligible Geom H mask W v j).card := by
  classical
  let A := (candidateBall H v j).filter fun c => H.present W c = true
  let G := Finset.univ.filter fun g : Group 𝒯 i => ∃ u ∈ groupNeighborhood g, Geom.project u.1 = v
  let U := G.biUnion fun g => marked Geom H mask g W
  have hel : eligible Geom H mask W v j = A \ U := by
    ext c
    simp only [eligible,A,U,G,Finset.mem_sdiff,Finset.mem_biUnion,
      Finset.mem_filter,Finset.mem_univ,true_and]
    apply and_congr_right
    intro _
    apply not_congr
    constructor
    · rintro ⟨g,hc⟩
      split_ifs at hc with hg
      · exact ⟨g,hg,hc⟩
      · simp at hc
    · rintro ⟨g,hg,hc⟩
      exact ⟨g,by rw [if_pos hg]; exact hc⟩
  have hU : (U.card : ℝ) ≤ (𝒯.P i).h ^ 4 * (𝒯.tScale i : ℝ) := by
    have hnat : U.card ≤ G.card * ((𝒯.P i).h * 𝒯.tScale i) := by
      apply (Finset.card_biUnion_le).trans
      calc
        _ ≤ ∑ _g ∈ G, (𝒯.P i).h * 𝒯.tScale i := by
          apply Finset.sum_le_sum
          intro g _
          exact (marked_card_bound Geom H mask g W).trans
            (Nat.mul_le_mul_right _ (hf g).le)
        _ = _ := by simp
    have hcast : (U.card : ℝ) ≤ (G.card : ℝ) * ((𝒯.P i).h * (𝒯.tScale i : ℝ)) := by exact_mod_cast hnat
    have hG : (G.card : ℝ) ≤ (𝒯.P i).h ^ 3 := Geom.projected_overlap v
    calc
      _ ≤ (G.card : ℝ) * ((𝒯.P i).h * (𝒯.tScale i : ℝ)) := hcast
      _ ≤ (𝒯.P i).h ^ 3 * ((𝒯.P i).h * (𝒯.tScale i : ℝ)) :=
        mul_le_mul_of_nonneg_right hG (by positivity)
      _ = _ := by ring
  have hloss : 4 * ((𝒯.P i).h : ℝ) ^ 4 * 𝒯.tScale i ≤ H.Device.lam / 4 :=
    (hconst.threshold_slack (𝒯.P i).h scales.h_large).2.2.2.2.2.2.1
  have hA : H.Device.lam * (3 / 4 : ℝ) ≤ (A.card : ℝ) := by
    have hlo := (abs_le.mp (hcounts v j)).1
    change -(H.Device.lam / 4) ≤ (A.card : ℝ) - H.Device.lam at hlo
    linarith
  have hcards := Finset.card_sdiff_add_card_inter A U
  have hinter := Finset.card_le_card (Finset.inter_subset_right (s₁ := A) (s₂ := U))
  have hcardsR : ((A \ U).card : ℝ) + ((A ∩ U).card : ℝ) = (A.card : ℝ) := by exact_mod_cast hcards
  have hiR : ((A ∩ U).card : ℝ) ≤ (U.card : ℝ) := by exact_mod_cast hinter
  rw [hel]
  linarith

private theorem eligibility_low_forces_many (hconst : HeightConstantContract κ)
    (scales : PatchScales 𝒯 i) (Geom : ProjectionGeometry κ 𝒯 i)
    (H : PrimitiveHistory κ 𝒯 i mesh) (mask : Masks H)
    (W : ∀ r, H.Val r) (hcounts : PositionCountGate H W)
    (hbad : ∃ v ∈ siteSet Geom, ∃ j, (eligible Geom H mask W v j).card < H.Device.lam / 2) :
    ∃ g, (𝒯.P i).h ≤ (failedFamily Geom H mask g W).card := by
  classical
  by_contra hn
  push_neg at hn
  obtain ⟨v,hv,j,hj⟩ := hbad
  exact (not_lt_of_ge (eligible_large_of_small_families hconst scales Geom H mask W hcounts hn v j)) hj

private noncomputable def eligibility_indicator (A : Prop) : ℝ :=
  @ite ℝ A (Classical.propDecidable A) 1 0

private theorem eligibility_pr_indicator {α : Type*} [Fintype α]
    (P : FinProb α) (A : α → Prop) : P.pr A = P.expect (fun a => eligibility_indicator (A a)) := by
  classical
  simp only [FinProb.pr,FinProb.expect,eligibility_indicator]
  apply Finset.sum_congr rfl
  intro a _
  split_ifs <;> ring

private theorem eligibility_pr_mono {α : Type*} [Fintype α]
    (P : FinProb α) (A B : α → Prop) (h : ∀ a, A a → B a) : P.pr A ≤ P.pr B := by
  classical
  unfold FinProb.pr
  apply Finset.sum_le_sum
  intro a _
  by_cases ha : A a
  · simp [ha,h a ha]
  · simp only [if_neg ha]
    split_ifs <;> simp [P.nonneg]

private theorem eligibility_pr_exists {α β : Type*} [Fintype α] [Fintype β]
    (P : FinProb α) (s : Finset β) (A : β → α → Prop) :
    P.pr (fun ω => ∃ b ∈ s, A b ω) ≤ ∑ b ∈ s, P.pr (A b) := by
  classical
  unfold FinProb.pr
  rw [Finset.sum_comm]
  apply Finset.sum_le_sum
  intro ω _
  by_cases he : ∃ b ∈ s, A b ω
  · obtain ⟨b,hb,hA⟩ := he
    rw [if_pos ⟨b,hb,hA⟩]
    have hle := Finset.single_le_sum (s := s)
      (f := fun b => if A b ω then P.w ω else 0)
      (fun _ _ => by split_ifs <;> simp [P.nonneg]) hb
    simpa [hA] using hle
  · rw [if_neg he]
    exact Finset.sum_nonneg fun _ _ => by split_ifs <;> simp [P.nonneg]

private theorem disjoint_family_probability {C : Type*} [Fintype C] [DecidableEq C]
    {Ω : C → Type*} [∀ c, Fintype (Ω c)] (P : ∀ c, FinProb (Ω c))
    (F : Finset (Finset C)) (E : Finset C → (∀ c, Ω c) → Prop)
    (hd : ∀ S ∈ F, ∀ S' ∈ F, S ≠ S' → Disjoint S S')
    (hdep : ∀ S ∈ F, FinProb.DependsOn (E S) S) :
    (FinProb.pi P).pr (fun ω => ∀ S ∈ F, E S ω) =
      ∏ S ∈ F, (FinProb.pi P).pr (E S) := by
  classical
  induction F using Finset.induction_on with
  | empty => simp [FinProb.pr, FinProb.sum_eq_one]
  | @insert S F hs ih =>
    let f : (∀ c, Ω c) → ℝ := fun ω => eligibility_indicator (E S ω)
    let g : (∀ c, Ω c) → ℝ := fun ω => eligibility_indicator (∀ S' ∈ F, E S' ω)
    have hf : FinProb.DependsOn f S := by
      intro ω ω' hω
      exact congrArg eligibility_indicator (hdep S (Finset.mem_insert_self _ _) ω ω' hω)
    have hg : FinProb.DependsOn g (F.biUnion id) := by
      intro ω ω' hω
      have he : (∀ S' ∈ F, E S' ω) ↔ (∀ S' ∈ F, E S' ω') := by
        apply forall_congr'
        intro S'
        apply imp_congr_right
        intro hS'
        have heq := hdep S' (Finset.mem_insert_of_mem hS') ω ω' (fun c hc =>
          hω c (Finset.mem_biUnion.mpr ⟨S',hS',hc⟩))
        exact heq ▸ Iff.rfl
      exact congrArg eligibility_indicator (propext he)
    have hdisj : Disjoint S (F.biUnion id) := by
      apply Finset.disjoint_left.mpr
      intro c hc hu
      obtain ⟨S',hS',hc'⟩ := Finset.mem_biUnion.mp hu
      exact (Finset.disjoint_left.mp (hd S (Finset.mem_insert_self _ _) S'
        (Finset.mem_insert_of_mem hS') (fun heq => hs (heq.symm ▸ hS')))) hc hc'
    have hprod := FinProb.pi_expect_mul_of_disjoint P f g S (F.biUnion id) hf hg hdisj
    have hind := ih (fun S' hS' S'' hS'' hne => hd S' (Finset.mem_insert_of_mem hS')
      S'' (Finset.mem_insert_of_mem hS'') hne)
      (fun S' hS' => hdep S' (Finset.mem_insert_of_mem hS'))
    have hfg : (fun ω => f ω * g ω) = (fun ω =>
        eligibility_indicator (∀ S' ∈ insert S F, E S' ω)) := by
      funext ω
      simp only [Finset.forall_mem_insert]
      dsimp [f,g,eligibility_indicator]
      split_ifs <;> simp_all
    rw [hfg] at hprod
    dsimp [f,g] at hprod
    rw [← eligibility_pr_indicator _ (fun ω => ∀ S' ∈ insert S F, E S' ω),
      ← eligibility_pr_indicator _ (E S),
      ← eligibility_pr_indicator _ (fun ω => ∀ S' ∈ F, E S' ω), hind] at hprod
    rw [Finset.prod_insert hs]
    exact hprod

private theorem disjoint_family_probability_le {C : Type*} [Fintype C] [DecidableEq C]
    {Ω : C → Type*} [∀ c, Fintype (Ω c)] (P : ∀ c, FinProb (Ω c))
    (F : Finset (Finset C)) (E : Finset C → (∀ c, Ω c) → Prop) (δ : ℝ)
    (hδ : 0 ≤ δ)
    (hd : ∀ S ∈ F, ∀ S' ∈ F, S ≠ S' → Disjoint S S')
    (hdep : ∀ S ∈ F, FinProb.DependsOn (E S) S)
    (hbound : ∀ S ∈ F, (FinProb.pi P).pr (E S) ≤ δ) :
    (FinProb.pi P).pr (fun ω => ∀ S ∈ F, E S ω) ≤ δ ^ F.card := by
  rw [disjoint_family_probability P F E hd hdep]
  calc
    _ ≤ ∏ _S ∈ F, δ := by
      apply Finset.prod_le_prod₀
      · intro S _
        unfold FinProb.pr
        exact Finset.sum_nonneg fun _ _ => by split_ifs <;> simp [FinProb.nonneg]
      · exact hbound
    _ = _ := by simp

private theorem disjoint_failures_union_bound {C : Type*} [Fintype C] [DecidableEq C]
    {Ω : C → Type*} [∀ c, Fintype (Ω c)] (P : ∀ c, FinProb (Ω c))
    (Lists : Finset (Finset C)) (E : Finset C → (∀ c, Ω c) → Prop) (h : ℕ) (δ : ℝ)
    (hδ : 0 ≤ δ)
    (hdep : ∀ S ∈ Lists, FinProb.DependsOn (E S) S)
    (hbound : ∀ S ∈ Lists, (FinProb.pi P).pr (E S) ≤ δ) :
    (FinProb.pi P).pr (fun ω => ∃ F ∈ Lists.powersetCard h,
      (∀ S ∈ F, ∀ S' ∈ F, S ≠ S' → Disjoint S S') ∧ ∀ S ∈ F, E S ω) ≤
      ((Lists.card : ℝ) * δ) ^ h := by
  classical
  apply le_trans (eligibility_pr_exists (FinProb.pi P) (Lists.powersetCard h) _)
  calc
    _ ≤ ∑ _F ∈ Lists.powersetCard h, δ ^ h := by
      apply Finset.sum_le_sum
      intro F hF
      obtain ⟨hsub,hcard⟩ := Finset.mem_powersetCard.mp hF
      by_cases hd : ∀ S ∈ F, ∀ S' ∈ F, S ≠ S' → Disjoint S S'
      · have hm := eligibility_pr_mono (FinProb.pi P)
          (fun ω => (∀ S ∈ F, ∀ S' ∈ F, S ≠ S' → Disjoint S S') ∧ ∀ S ∈ F, E S ω) (fun ω => ∀ S ∈ F, E S ω) (fun _ h => h.2)
        have hb := disjoint_family_probability_le P F E δ hδ hd
          (fun S hS => hdep S (hsub hS)) (fun S hS => hbound S (hsub hS))
        simpa [hcard] using hm.trans hb
      · simp [FinProb.pr,hd,pow_nonneg hδ]
    _ = ((Lists.card.choose h : ℕ) : ℝ) * δ ^ h := by
      simp [Finset.card_powersetCard]
    _ ≤ (Lists.card : ℝ) ^ h * δ ^ h := by
      apply mul_le_mul_of_nonneg_right _ (pow_nonneg hδ h)
      exact_mod_cast Nat.choose_le_pow Lists.card h
    _ = _ := (mul_pow _ _ _).symm

private theorem short_list_count {C : Type*} [Fintype C] [DecidableEq C]
    (R : Finset C) (t : ℕ) :
    (R.powerset.filter fun S => S.card ≤ t).card ≤ (R.card + 1) ^ (t + 1) := by
  classical
  have hsub : (R.powerset.filter fun S => S.card ≤ t) ⊆
      (Finset.range (t + 1)).biUnion fun j => R.powersetCard j := by
    intro S hS
    obtain ⟨hS,ht⟩ := Finset.mem_filter.mp hS
    refine Finset.mem_biUnion.mpr ⟨S.card,Finset.mem_range.mpr (by omega),?_⟩
    exact Finset.mem_powersetCard.mpr ⟨Finset.mem_powerset.mp hS,rfl⟩
  have hgeom (N t : ℕ) : (∑ j ∈ Finset.range (t + 1), N ^ j) ≤ (N + 1) ^ (t + 1) := by
    induction t with
    | zero => simp
    | succ t ih =>
      rw [Finset.sum_range_succ]
      by_cases hN : N = 0
      · simpa [hN] using ih
      · have hpow : N ^ (t + 1) ≤ (N + 1) ^ (t + 1) := Nat.pow_le_pow_left (by omega) _
        calc
          _ ≤ (N + 1) ^ (t + 1) + (N + 1) ^ (t + 1) := Nat.add_le_add ih hpow
          _ = 2 * (N + 1) ^ (t + 1) := by omega
          _ ≤ (N + 1) * (N + 1) ^ (t + 1) := Nat.mul_le_mul_right _ (by omega)
          _ = _ := by rw [pow_succ]; ring
  calc
    _ ≤ ((Finset.range (t + 1)).biUnion fun j => R.powersetCard j).card := Finset.card_le_card hsub
    _ ≤ ∑ j ∈ Finset.range (t + 1), (R.powersetCard j).card := Finset.card_biUnion_le
    _ ≤ ∑ j ∈ Finset.range (t + 1), R.card ^ j := by
      apply Finset.sum_le_sum
      intro j _
      rw [Finset.card_powersetCard]
      exact Nat.choose_le_pow _ _
    _ ≤ _ := hgeom _ _

private theorem neighborhood_card (Geom : ProjectionGeometry κ 𝒯 i)
    (g : Group 𝒯 i) : (groupNeighborhood g).card ≤ (𝒯.P i).h ^ 2 := by
  classical
  let S := fun l : Fin (𝒯.P i).h => Finset.univ.filter fun v : EvenRole 𝒯 i =>
    flipPos v.1 l ∈ groupFiber g
  have heq : groupNeighborhood g = Finset.univ.biUnion S := by
    ext v
    simp [groupNeighborhood,S]
  have hS (l : Fin (𝒯.P i).h) : (S l).card ≤ (𝒯.P i).h := by
    rw [← Geom.fiber_card g]
    apply Finset.card_le_card_of_injOn (fun v : EvenRole 𝒯 i => flipPos v.1 l)
    · intro v hv
      exact (Finset.mem_filter.mp hv).2
    · intro v hv v' hv' he
      apply Subtype.ext
      funext z
      have h := congrFun he z
      by_cases hz : z = l
      · subst z
        simpa [flipPos] using h
      · simpa [flipPos,Function.update_apply,hz] using h
  rw [heq]
  calc
    _ ≤ ∑ l : Fin (𝒯.P i).h, (S l).card := Finset.card_biUnion_le
    _ ≤ ∑ _l : Fin (𝒯.P i).h, (𝒯.P i).h := Finset.sum_le_sum fun l _ => hS l
    _ = _ := by simp [pow_two]

private theorem present_range_card (hconst : HeightConstantContract κ)
    (scales : PatchScales 𝒯 i) (Geom : ProjectionGeometry κ 𝒯 i)
    (H : PrimitiveHistory κ 𝒯 i mesh) (g : Group 𝒯 i)
    (W : ∀ r, H.Val r) (hc : PositionCountGate H W) :
    (((candidateRange Geom H g).filter fun c => H.present W c = true).card : ℝ) ≤
      2 * (𝒯.P i).h ^ 3 * H.Device.lam * (H.Device.H + 1) := by
  classical
  have hn := (hconst.threshold_slack (𝒯.P i).h scales.h_large).1
  have hlam : 0 ≤ H.Device.lam := by dsimp [PrimitiveHistory.Device,patchHD]; positivity
  have hb (v : EvenRole 𝒯 i) (j : Fin (H.Device.H + 1)) :
      (((candidateBall H (Geom.project v.1) j).filter fun c => H.present W c = true).card : ℝ) ≤
        2 * H.Device.lam := by
    have hhi := (abs_le.mp (hc (Geom.project v.1) j)).2
    linarith
  unfold candidateRange
  rw [Finset.filter_biUnion]
  have houter := Finset.card_biUnion_le (s := groupNeighborhood g)
    (t := fun v => (Finset.univ.biUnion fun j => candidateBall H (Geom.project v.1) j).filter
      fun c => H.present W c = true)
  have houterR : (((groupNeighborhood g).biUnion fun v =>
      (Finset.univ.biUnion fun j => candidateBall H (Geom.project v.1) j).filter
        fun c => H.present W c = true).card : ℝ) ≤
      ∑ v ∈ groupNeighborhood g,
        (((Finset.univ.biUnion fun j => candidateBall H (Geom.project v.1) j).filter
          fun c => H.present W c = true).card : ℝ) := by exact_mod_cast houter
  apply houterR.trans
  calc
    _ ≤ ∑ _v ∈ groupNeighborhood g, (H.Device.H + 1) * (2 * H.Device.lam) := by
      apply Finset.sum_le_sum
      intro v hv
      rw [Finset.filter_biUnion]
      have hj := Finset.card_biUnion_le (s := (Finset.univ : Finset (Fin (H.Device.H + 1))))
        (t := fun j => (candidateBall H (Geom.project v.1) j).filter fun c => H.present W c = true)
      have hjR : ((Finset.univ.biUnion fun j =>
          (candidateBall H (Geom.project v.1) j).filter fun c => H.present W c = true).card : ℝ) ≤
          ∑ j : Fin (H.Device.H + 1),
            (((candidateBall H (Geom.project v.1) j).filter fun c => H.present W c = true).card : ℝ) := by
        exact_mod_cast hj
      apply hjR.trans
      calc
        _ ≤ ∑ _j : Fin (H.Device.H + 1), 2 * H.Device.lam := Finset.sum_le_sum fun j _ => hb v j
        _ = _ := by simp [Nat.cast_add,Nat.cast_one]
    _ = ((groupNeighborhood g).card : ℝ) * ((H.Device.H + 1) * (2 * H.Device.lam)) := by simp
    _ ≤ ((𝒯.P i).h : ℝ) ^ 2 * ((H.Device.H + 1) * (2 * H.Device.lam)) := by
      apply mul_le_mul_of_nonneg_right _ (by positivity)
      exact_mod_cast neighborhood_card Geom g
    _ ≤ _ := by
      have hpow : ((𝒯.P i).h : ℝ) ^ 2 ≤ ((𝒯.P i).h : ℝ) ^ 3 := by
        have hR : (1 : ℝ) ≤ (𝒯.P i).h := by exact_mod_cast (show 1 ≤ (𝒯.P i).h by omega)
        nlinarith [sq_nonneg ((𝒯.P i).h : ℝ), mul_nonneg (sq_nonneg ((𝒯.P i).h : ℝ)) (sub_nonneg.mpr hR)]
      have hm := mul_le_mul_of_nonneg_right hpow
        (show 0 ≤ (H.Device.H + 1) * (2 * H.Device.lam) by positivity)
      nlinarith

private theorem failed_family_has_subfamily (Geom : ProjectionGeometry κ 𝒯 i)
    (H : PrimitiveHistory κ 𝒯 i mesh) (mask : Masks H)
    (g : Group 𝒯 i) (W : ∀ r, H.Val r)
    (h : ℕ) (hmany : h ≤ (failedFamily Geom H mask g W).card) :
    ∃ F : Finset (Finset H.Center), F.card = h ∧
      (∀ S ∈ F, admissibleList Geom H g W S ∧ ¬ listGood H mask g W S) ∧
      (∀ S ∈ F, ∀ S' ∈ F, S ≠ S' → Disjoint S S') := by
  obtain ⟨F,hsub,hcard⟩ := Finset.exists_subset_card_eq hmany
  refine ⟨F,hcard,?_,?_⟩
  · intro S hS
    exact (failedFamily_facts Geom H mask g W).1 S (hsub hS)
  · intro S hS S' hS' hne
    exact (failedFamily_facts Geom H mask g W).2 S (hsub hS) S' (hsub hS') hne

private noncomputable def replaceAllTuples (H : PrimitiveHistory κ 𝒯 i mesh)
    (W : ∀ r, H.Val r) (w : H.Center → H.Tuple) : ∀ r, H.Val r :=
  fun r => match r with
    | .inl c => (H.cornerOf W c, (w c, H.present W c, H.active W c))
    | .inr (.inl g) => W (.inr (.inl g))
    | .inr (.inr c) => W (.inr (.inr c))

private noncomputable def conditionedTuples (H : PrimitiveHistory κ 𝒯 i mesh)
    (W : ∀ r, H.Val r) : FinProb (H.Center → H.Tuple) :=
  FinProb.pi fun c => ⟨(H.tuplePrior (H.cornerOf W c)).w,
    (H.tuplePrior (H.cornerOf W c)).nonneg, (H.tuplePrior (H.cornerOf W c)).sum_one⟩

private noncomputable def reindexedListModel (Geom : ProjectionGeometry κ 𝒯 i)
    (H : PrimitiveHistory κ 𝒯 i mesh) (mask : Masks H) (L : ListFamily Geom H mask)
    (p : mesh.Param) (g : Group 𝒯 i) (W : ∀ r, H.Val r) (hW : 0 < (H.recLaw p).w W)
    (S : Finset H.Center) (hS : admissibleList Geom H g W S) : ListTestModel κ 𝒯 i where
  Id := S
  idNonempty := by obtain ⟨c,hc⟩ := hS.1; exact ⟨⟨c,hc⟩⟩
  binPrior := (L.model p g W hW S hS).binPrior
  binDist := (L.model p g W hW S hS).binDist
  firstLaw c := H.prior (H.cornerOf W c.1)
  bin_support := (L.model p g W hW S hS).bin_support
  first_law_supported c := by
    have hf := L.first_law p g W hW S hS ((L.ids p g W hW S hS).symm c)
    rw [Equiv.apply_symm_apply] at hf
    rw [← hf]
    exact (L.model p g W hW S hS).first_law_supported _
  aggregate_cap := (L.model p g W hW S hS).aggregate_cap
  width_bound c x := by
    have hf := L.first_law p g W hW S hS ((L.ids p g W hW S hS).symm c)
    rw [Equiv.apply_symm_apply] at hf
    rw [← hf]
    exact (L.model p g W hW S hS).width_bound _ x
  codegree_bound c b y y' hb hy hy' := by
    have hf := L.first_law p g W hW S hS ((L.ids p g W hW S hS).symm c)
    rw [Equiv.apply_symm_apply] at hf
    rw [← hf]
    exact (L.model p g W hW S hS).codegree_bound _ b y y' hb hy hy'
  budget := by
    rw [← Fintype.card_congr (L.ids p g W hW S hS)]
    exact (L.model p g W hW S hS).budget

private theorem reindexed_list_test (Geom : ProjectionGeometry κ 𝒯 i)
    (H : PrimitiveHistory κ 𝒯 i mesh) (mask : Masks H) (hl : MaskLookup H mask)
    (L : ListFamily Geom H mask) (p : mesh.Param) (g : Group 𝒯 i)
    (W : ∀ r, H.Val r) (hW : 0 < (H.recLaw p).w W)
    (S : Finset H.Center) (hS : admissibleList Geom H g W S) (w : H.Center → H.Tuple) :
    (reindexedListModel Geom H mask L p g W hW S hS).Good (fun c => w c.1) ↔
      listGood H mask g (replaceAllTuples H W w) S := by
  classical
  let M := reindexedListModel Geom H mask L p g W hW S hS
  let W' := replaceAllTuples H W w
  obtain ⟨hp,hw⟩ := hl g W W' (show H.maskVertex g W = H.maskVertex g W' from rfl)
  have hmass (J : Finset (Fin (T.S.N k))) : M.mass J = maskedMass H mask g W' J := by
    unfold ListTestModel.mass maskedMass
    apply Finset.sum_congr rfl
    intro D _
    have hprior := L.prior p g W hW S hS D
    have hwithin := L.within p g W hW S hS D
    dsimp [M,reindexedListModel]
    rw [hprior,hp]
    congr 2
    apply Finset.sum_congr rfl
    intro y _
    rw [hwithin,hw]
  have hhit : M.hitSet (fun c => w c.1) = listHit H W' S := by
    ext y
    simp only [ListTestModel.hitSet,listHit,Finset.mem_filter,Finset.mem_univ,true_and]
    constructor
    · intro hy c hc r
      exact hy ⟨c,hc⟩ r
    · intro hy c r
      exact hy c.1 c.2 r
  have hdelete (c₀ : S) : M.hitSetDelete (fun c => w c.1) c₀ = listHit H W' (S.erase c₀.1) := by
    ext y
    simp only [ListTestModel.hitSetDelete,listHit,Finset.mem_filter,Finset.mem_univ,true_and]
    constructor
    · intro hy c hc r
      obtain ⟨hne,hc⟩ := Finset.mem_erase.mp hc
      exact hy ⟨c,hc⟩ (fun he => hne (congrArg Subtype.val he)) r
    · intro hy c hne r
      apply hy c.1 (Finset.mem_erase.mpr ⟨?_,c.2⟩) r
      intro he
      exact hne (Subtype.ext he)
  change M.Good (fun c => w c.1) ↔ listGood H mask g W' S
  unfold ListTestModel.Good listGood
  rw [hhit,hmass]
  have hcM : Fintype.card M.Id = S.card := Fintype.card_coe S
  rw [hcM]
  apply and_congr_right
  intro _
  constructor
  · intro h c hc
    have he := h (⟨c,hc⟩ : S)
    rw [hdelete,hmass] at he
    exact he
  · intro h c
    rw [hdelete,hmass]
    exact h c.1 c.2

private theorem conditioned_list_failure (Geom : ProjectionGeometry κ 𝒯 i)
    (H : PrimitiveHistory κ 𝒯 i mesh) (mask : Masks H) (hl : MaskLookup H mask)
    (L : ListFamily Geom H mask) (p : mesh.Param) (g : Group 𝒯 i)
    (W : ∀ r, H.Val r) (hW : 0 < (H.recLaw p).w W)
    (S : Finset H.Center) (hS : admissibleList Geom H g W S)
    (ha : κ.a ≤ 1 / 10) (ht : GenericListBound κ 𝒯 i) :
    (conditionedTuples H W).pr (fun w => ¬ listGood H mask g (replaceAllTuples H W w) S) ≤
      2 * (𝒯.tScale i + 1 : ℝ) * Real.exp (-κ.c5 * κ.a ^ 2 * (𝒯.kScale i : ℝ)) := by
  classical
  let M := reindexedListModel Geom H mask L p g W hW S hS
  have hbound := ht M (by simpa [M,reindexedListModel] using hS.2.1) ha
  have heq : (conditionedTuples H W).pr (fun w => ¬ listGood H mask g (replaceAllTuples H W w) S) =
      M.tupleLaw.pr M.Failure := by
    rw [eligibility_pr_indicator]
    have he (w : H.Center → H.Tuple) :
        eligibility_indicator (¬ listGood H mask g (replaceAllTuples H W w) S) =
          eligibility_indicator (M.Failure (fun c => w c.1)) := by
      congr 1
      exact propext (not_congr (reindexed_list_test Geom H mask hl L p g W hW S hS w)).symm
    simp_rw [he]
    unfold conditionedTuples
    have hrestr := FinProb.pi_marginal_expect (Ω := fun _ : H.Center => H.Tuple)
      (fun c : H.Center => (⟨(H.tuplePrior (H.cornerOf W c)).w,
        (H.tuplePrior (H.cornerOf W c)).nonneg,
        (H.tuplePrior (H.cornerOf W c)).sum_one⟩ : FinProb H.Tuple)) S
      (fun w : S → H.Tuple => eligibility_indicator (M.Failure w))
    apply hrestr.trans
    unfold FinLaw.pr FinProb.expect eligibility_indicator
    apply Finset.sum_congr rfl
    intro w _
    by_cases hf : M.Failure w
    · simp only [if_pos hf,mul_one]
      rfl
    · simp only [if_neg hf,mul_zero]
  rw [heq]
  exact hbound

private theorem conditioned_failure_depends (H : PrimitiveHistory κ 𝒯 i mesh)
    (mask : Masks H) (hl : MaskLookup H mask) (g : Group 𝒯 i)
    (W : ∀ r, H.Val r) (S : Finset H.Center) :
    FinProb.DependsOn (fun w => ¬ listGood H mask g (replaceAllTuples H W w) S) S := by
  classical
  intro w w' he
  let W₁ := replaceAllTuples H W w
  let W₂ := replaceAllTuples H W w'
  obtain ⟨hp,hu⟩ := hl g W₁ W₂ (show H.maskVertex g W₁ = H.maskVertex g W₂ from rfl)
  have hhit (A : Finset H.Center) (ha : A ⊆ S) : listHit H W₁ A = listHit H W₂ A := by
    ext y
    simp only [listHit,Finset.mem_filter,Finset.mem_univ,true_and]
    constructor <;> intro hy c hc r
    · change Hits (T.S.E k) 𝒯.c (w' c r) y
      rw [← he c (ha hc)]
      exact hy c hc r
    · change Hits (T.S.E k) 𝒯.c (w c r) y
      rw [he c (ha hc)]
      exact hy c hc r
  have hm (J : Finset (Fin (T.S.N k))) : maskedMass H mask g W₁ J = maskedMass H mask g W₂ J := by
    unfold maskedMass
    rw [hp,hu]
  change (¬ listGood H mask g W₁ S) = (¬ listGood H mask g W₂ S)
  apply congrArg Not
  apply propext
  unfold listGood
  simp only [hhit S (Finset.Subset.refl _),hm]
  apply and_congr_right
  intro _
  apply forall_congr'
  intro c
  apply imp_congr_right
  intro hc
  simp only [hhit (S.erase c) (Finset.erase_subset _ _),hm]

private theorem conditioned_greedy_bound (hconst : HeightConstantContract κ)
    (scales : PatchScales 𝒯 i) (Geom : ProjectionGeometry κ 𝒯 i)
    (H : PrimitiveHistory κ 𝒯 i mesh) (mask : Masks H) (hl : MaskLookup H mask)
    (L : ListFamily Geom H mask) (ht : GenericListBound κ 𝒯 i)
    (p : mesh.Param) (W : ∀ r, H.Val r) (hW : 0 < (H.recLaw p).w W)
    (hc : PositionCountGate H W) :
    (conditionedTuples H W).pr (fun w => ∃ g,
      (𝒯.P i).h ≤ (failedFamily Geom H mask g (replaceAllTuples H W w)).card) ≤
      Real.exp (-Real.rpow ((𝒯.P i).h : ℝ) (1 + hconst.sliceExponent)) := by
  classical
  let δ : ℝ := 2 * (𝒯.tScale i + 1 : ℝ) * Real.exp (-κ.c5 * κ.a ^ 2 * (𝒯.kScale i : ℝ))
  let B : ℝ := (2 * (𝒯.P i).h ^ 3 * H.Device.lam * (H.Device.H + 1) + 1) ^ (𝒯.tScale i + 1)
  have hδ : 0 ≤ δ := by dsimp [δ]; positivity
  have hB : 0 ≤ B := by dsimp [B,PrimitiveHistory.Device,patchHD]; positivity
  have hgroup (g : Group 𝒯 i) :
      (conditionedTuples H W).pr (fun w =>
        (𝒯.P i).h ≤ (failedFamily Geom H mask g (replaceAllTuples H W w)).card) ≤
        (B * δ) ^ (𝒯.P i).h := by
    let Lists : Finset (Finset H.Center) := Finset.univ.filter (admissibleList Geom H g W)
    let R := (candidateRange Geom H g).filter fun c => H.present W c = true
    have hcount : (Lists.card : ℝ) ≤ B := by
      have hs : Lists ⊆ R.powerset.filter (fun S => S.card ≤ 𝒯.tScale i) := by
        intro S hS
        have hadm := (Finset.mem_filter.mp hS).2
        refine Finset.mem_filter.mpr ⟨Finset.mem_powerset.mpr ?_,hadm.2.1⟩
        intro c hc
        exact Finset.mem_filter.mpr (hadm.2.2 c hc)
      have hnat := (Finset.card_le_card hs).trans (short_list_count R (𝒯.tScale i))
      have hcast : (Lists.card : ℝ) ≤ ((R.card : ℝ) + 1) ^ (𝒯.tScale i + 1) := by exact_mod_cast hnat
      apply hcast.trans
      apply pow_le_pow_left₀ (by positivity)
      have hr := present_range_card hconst scales Geom H g W hc
      linarith
    let E := fun S w => ¬ listGood H mask g (replaceAllTuples H W w) S
    have hevent (w : H.Center → H.Tuple)
        (hmany : (𝒯.P i).h ≤ (failedFamily Geom H mask g (replaceAllTuples H W w)).card) :
        ∃ F ∈ Lists.powersetCard (𝒯.P i).h,
          (∀ S ∈ F, ∀ S' ∈ F, S ≠ S' → Disjoint S S') ∧ ∀ S ∈ F, E S w := by
      obtain ⟨F,hcard,hbad,hd⟩ := failed_family_has_subfamily Geom H mask g _ _ hmany
      refine ⟨F,Finset.mem_powersetCard.mpr ⟨?_,hcard⟩,hd,?_⟩
      · intro S hS
        apply Finset.mem_filter.mpr
        refine ⟨Finset.mem_univ _,?_⟩
        exact (hbad S hS).1
      · intro S hS
        exact (hbad S hS).2
    have hm := eligibility_pr_mono (conditionedTuples H W) _ _ hevent
    have hbound := disjoint_failures_union_bound
      (fun c : H.Center => (⟨(H.tuplePrior (H.cornerOf W c)).w,
        (H.tuplePrior (H.cornerOf W c)).nonneg, (H.tuplePrior (H.cornerOf W c)).sum_one⟩ : FinProb H.Tuple))
      Lists E (𝒯.P i).h δ hδ
      (fun S _ => conditioned_failure_depends H mask hl g W S)
      (fun S hS => conditioned_list_failure Geom H mask hl L p g W hW S
        (Finset.mem_filter.mp hS).2 scales.a_small ht)
    apply (hm.trans hbound).trans
    apply pow_le_pow_left₀ (mul_nonneg (Nat.cast_nonneg _) hδ)
    exact mul_le_mul_of_nonneg_right hcount hδ
  have hgcard : (Fintype.card (Group 𝒯 i) : ℝ) ≤ (2 : ℝ) ^ (𝒯.P i).h := by
    have hn : Fintype.card (Group 𝒯 i) ≤ Fintype.card (IWord 𝒯 i) :=
      Fintype.card_le_of_injective Subtype.val Subtype.val_injective
    simpa only [IWord,CubePos,Fintype.card_fun,Fintype.card_fin,Fintype.card_bool,Nat.cast_pow,Nat.cast_ofNat] using
      (show (Fintype.card (Group 𝒯 i) : ℝ) ≤ Fintype.card (IWord 𝒯 i) by exact_mod_cast hn)
  have hthreshold : (2 : ℝ) ^ (𝒯.P i).h * (B * δ) ^ (𝒯.P i).h ≤
      Real.exp (-Real.rpow ((𝒯.P i).h : ℝ) (1 + hconst.sliceExponent)) := by
    simpa only [B,δ,PrimitiveHistory.Device,patchHD,Tiling.kScale,Tiling.tScale,Nat.cast_add,Nat.cast_one] using
      (hconst.threshold_slack (𝒯.P i).h scales.h_large).2.2.2.2.2.2.2.2.1
  have hu := eligibility_pr_exists (conditionedTuples H W) (Finset.univ : Finset (Group 𝒯 i))
    (fun g w => (𝒯.P i).h ≤ (failedFamily Geom H mask g (replaceAllTuples H W w)).card)
  simp only [Finset.mem_univ,true_and] at hu
  apply hu.trans
  calc
    _ ≤ ∑ _g : Group 𝒯 i, (B * δ) ^ (𝒯.P i).h := Finset.sum_le_sum fun g _ => hgroup g
    _ = (Fintype.card (Group 𝒯 i) : ℝ) * (B * δ) ^ (𝒯.P i).h := by simp
    _ ≤ (2 : ℝ) ^ (𝒯.P i).h * (B * δ) ^ (𝒯.P i).h :=
      mul_le_mul_of_nonneg_right hgcard (pow_nonneg (mul_nonneg hB hδ) _)
    _ ≤ _ := hthreshold

end EligibilityCountProof

/-- The local height rule and star validity, before any bin or label draw. -/
structure HeightFacts {κ : CConsts} {T : Stage} {k : ℕ}
    {𝒯 : Tiling κ T k} {i : Fin 𝒯.m} {mesh : Mesh 𝒯}
    (hconst : HeightConstantContract κ) (Geom : ProjectionGeometry κ 𝒯 i)
    (H : PrimitiveHistory κ 𝒯 i mesh) (mask : Masks H) : Prop where
  validity_good : ∀ p, (H.recLaw p).pr (fun W => ∃ v, ¬ starValid Geom H mask v W) ≤
    Real.exp (-Real.rpow ((𝒯.P i).h : ℝ) (1 + hconst.globalExponent)) +
      2 * Real.exp (-Real.rpow ((𝒯.P i).h : ℝ) (1 + hconst.sliceExponent))
  chosen_eligible : ∀ W v c, selected Geom H mask W v = some c →
    c ∈ eligible Geom H mask W (Geom.project v.1) c.2 ∧ H.active W c = true
  selected_local : ∀ v W W',
    (∀ r, (hammingDist (H.loc r) v.1 : ℝ) ≤ 10 * κ.ρ * (𝒯.P i).h → W r = W' r) →
      selected Geom H mask W v = selected Geom H mask W' v

section SelectionLocalProof

set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000

variable {κ : CConsts} {T : Stage} {k : ℕ} {𝒯 : Tiling κ T k}
  {i : Fin 𝒯.m} {mesh : Mesh 𝒯}

private theorem flip_dist_le_one {d : ℕ} (z : CubePos d) (l : Fin d) :
    hammingDist (flipPos z l) z ≤ 1 := by
  calc
    _ ≤ ({l} : Finset (Fin d)).card := by
      apply Finset.card_le_card
      intro j hj
      have hdiff := (Finset.mem_filter.mp hj).2
      by_contra hn
      have hne : j ≠ l := by simpa using hn
      simp [flipPos, hne] at hdiff
    _ = 1 := by simp

private theorem projection_dist_le_one (Geom : ProjectionGeometry κ 𝒯 i)
    (z : IWord 𝒯 i) : hammingDist (Geom.project z) z ≤ 1 := by
  rw [Geom.project_eq]
  exact flip_dist_le_one z _

private theorem group_neighborhood_dist (g : Group 𝒯 i) (v : EvenRole 𝒯 i)
    (hv : v ∈ groupNeighborhood g) : hammingDist g.1 v.1 ≤ 2 := by
  obtain ⟨l, hl⟩ := (Finset.mem_filter.mp hv).2
  obtain ⟨j, _, hj⟩ := Finset.mem_image.mp hl
  have ha : hammingDist g.1 (flipPos g.1 j) ≤ 1 := by
    rw [hammingDist_comm]
    exact flip_dist_le_one _ _
  have hb : hammingDist (flipPos g.1 j) v.1 ≤ 1 := by
    rw [hj]
    exact flip_dist_le_one _ _
  have ht := hammingDist_triangle g.1 (flipPos g.1 j) v.1
  omega

private theorem patch_radius_pos (hconst : HeightConstantContract κ)
    (scales : PatchScales 𝒯 i) (H : PrimitiveHistory κ 𝒯 i mesh) : 1 ≤ H.Device.r := by
  have hnum := hconst.threshold_slack (𝒯.P i).h scales.h_large
  have hh := hnum.1
  have hlam := hnum.2.2.1
  have hp : (1 : ℝ) ≤ ((𝒯.P i).h : ℝ) ^ (10 : ℕ) := by
    have hn : (1 : ℝ) ≤ (𝒯.P i).h := by exact_mod_cast (by omega : 1 ≤ (𝒯.P i).h)
    simpa using pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 1) hn 10
  by_contra hn
  have hz : ⌊κ.ρ * (𝒯.P i).h⌋₊ = 0 := by
    change ¬ 1 ≤ ⌊κ.ρ * (𝒯.P i).h⌋₊ at hn
    omega
  simp only [hz, zero_add, Finset.range_one, Finset.sum_singleton, Nat.choose_zero_right,
    Nat.cast_one] at hlam
  norm_num [Real.rpow_natCast] at hlam
  nlinarith

private theorem candidate_range_dist (Geom : ProjectionGeometry κ 𝒯 i)
    (H : PrimitiveHistory κ 𝒯 i mesh) (g : Group 𝒯 i) (u : EvenRole 𝒯 i)
    (hu : u ∈ groupNeighborhood g) (c : H.Center) (hc : c ∈ candidateRange Geom H g) :
    hammingDist c.1 (Geom.project u.1) ≤ H.Device.r + 6 := by
  obtain ⟨v, hv, hc⟩ := Finset.mem_biUnion.mp hc
  obtain ⟨j, _, hc⟩ := Finset.mem_biUnion.mp hc
  have hd := (Finset.mem_filter.mp hc).2.2
  have hp := Geom.projected_distance g v u hv hu
  have ht := hammingDist_triangle c.1 (Geom.project v.1) (Geom.project u.1)
  dsimp only [PrimitiveHistory.Device, patchHD] at hd hp ht ⊢
  simp only [hammingDist, Finset.filter_congr_decidable] at hd hp ht ⊢
  omega

private theorem failedFamily_congr (Geom : ProjectionGeometry κ 𝒯 i)
    (H : PrimitiveHistory κ 𝒯 i mesh) (mask : Masks H) (hlookup : MaskLookup H mask)
    (g : Group 𝒯 i) (W W' : ∀ r, H.Val r)
    (hgroup : W (.inr (.inl g)) = W' (.inr (.inl g)))
    (hc : ∀ c ∈ candidateRange Geom H g,
      H.present W c = H.present W' c ∧ H.tuple W c = H.tuple W' c) :
    failedFamily Geom H mask g W = failedFamily Geom H mask g W' := by
  classical
  have hvertex : H.maskVertex g W = H.maskVertex g W' := congrArg Prod.fst hgroup
  have horder : H.searchOrder g W = H.searchOrder g W' := congrArg Prod.snd hgroup
  obtain ⟨hprior, hwithin⟩ := hlookup g W W' hvertex
  have hpres (c : H.Center) (h : c ∈ candidateRange Geom H g) :
      H.present W c = H.present W' c := (hc c h).1
  have htuple (c : H.Center) (h : c ∈ candidateRange Geom H g) :
      H.tuple W c = H.tuple W' c := (hc c h).2
  have hadm (S : Finset H.Center) :
      admissibleList Geom H g W S ↔ admissibleList Geom H g W' S := by
    unfold admissibleList
    constructor <;> rintro ⟨hne, hsize, hS⟩
    · refine ⟨hne, hsize, fun c hc => ?_⟩
      obtain ⟨hr, hp⟩ := hS c hc
      exact ⟨hr, by rwa [← hpres c hr]⟩
    · refine ⟨hne, hsize, fun c hc => ?_⟩
      obtain ⟨hr, hp⟩ := hS c hc
      exact ⟨hr, by rwa [hpres c hr]⟩
  have hhit (S : Finset H.Center) (hS : S ⊆ candidateRange Geom H g) :
      listHit H W S = listHit H W' S := by
    ext y
    simp only [listHit, Finset.mem_filter, Finset.mem_univ, true_and]
    constructor <;> intro hy c hc r
    · rw [← htuple c (hS hc)]
      exact hy c hc r
    · rw [htuple c (hS hc)]
      exact hy c hc r
  have hmass (J : Finset (Fin (T.S.N k))) :
      maskedMass H mask g W J = maskedMass H mask g W' J := by
    unfold maskedMass
    rw [hprior, hwithin]
  have hgood (S : Finset H.Center) (hS : S ⊆ candidateRange Geom H g) :
      listGood H mask g W S ↔ listGood H mask g W' S := by
    have hdel : ∀ c, listHit H W (S.erase c) = listHit H W' (S.erase c) :=
      fun c => hhit _ (Finset.Subset.trans (Finset.erase_subset _ _) hS)
    simp only [listGood, hhit S hS, hdel, hmass]
  have hbad : (fun S => admissibleList Geom H g W S ∧ ¬ listGood H mask g W S) =
      (fun S => admissibleList Geom H g W' S ∧ ¬ listGood H mask g W' S) := by
    funext S
    apply propext
    by_cases ha : admissibleList Geom H g W S
    · have hS : S ⊆ candidateRange Geom H g := fun c hc => (ha.2.2 c hc).1
      rw [hadm S, hgood S hS]
    · have ha' := mt (hadm S).mpr ha
      simp [ha, ha']
  unfold failedFamily
  rw [horder, hbad]

private theorem local_record_eq (hconst : HeightConstantContract κ)
    (scales : PatchScales 𝒯 i) (Geom : ProjectionGeometry κ 𝒯 i)
    (H : PrimitiveHistory κ 𝒯 i mesh) (v : EvenRole 𝒯 i) (W W' : ∀ r, H.Val r)
    (hW : ∀ r, (hammingDist (H.loc r) v.1 : ℝ) ≤ 10 * κ.ρ * (𝒯.P i).h → W r = W' r)
    (r : H.Rec) (hr : hammingDist (H.loc r) (Geom.project v.1) ≤
      H.Device.Rlong + H.Device.r + 6) : W r = W' r := by
  apply hW
  have hp := projection_dist_le_one Geom v.1
  have ht := hammingDist_triangle (H.loc r) (Geom.project v.1) v.1
  have hd : (hammingDist (H.loc r) v.1 : ℝ) ≤
      (H.Device.Rlong : ℝ) + H.Device.r + 7 := by exact_mod_cast (by omega :
        hammingDist (H.loc r) v.1 ≤ H.Device.Rlong + H.Device.r + 7)
  have hs := (hconst.threshold_slack (𝒯.P i).h scales.h_large).2.2.2.2.1
  have hrad := patch_radius_pos hconst scales H
  have hradR : (1 : ℝ) ≤ H.Device.r := by exact_mod_cast hrad
  norm_num only [HDParams.Rlong, show H.Device.D = 6 from rfl,
    Nat.cast_mul, Nat.cast_ofNat] at hd
  change 12 * (H.Device.H : ℝ) + 4 * (H.Device.r : ℝ) + 6 <
    10 * κ.ρ * (𝒯.P i).h at hs
  linarith

private theorem eligible_congr_local (hconst : HeightConstantContract κ)
    (scales : PatchScales 𝒯 i) (Geom : ProjectionGeometry κ 𝒯 i)
    (H : PrimitiveHistory κ 𝒯 i mesh) (mask : Masks H) (hlookup : MaskLookup H mask)
    (v : EvenRole 𝒯 i) (W W' : ∀ r, H.Val r)
    (hW : ∀ r, (hammingDist (H.loc r) v.1 : ℝ) ≤ 10 * κ.ρ * (𝒯.P i).h → W r = W' r)
    (u : IWord 𝒯 i) (hu : hammingDist u (Geom.project v.1) ≤ H.Device.Rlong)
    (j : Fin (H.Device.H + 1)) :
    eligible Geom H mask W u j = eligible Geom H mask W' u j := by
  have hcenter (c : H.Center) (hc : c ∈ candidateBall H u j) :
      W (.inl c) = W' (.inl c) := by
    apply local_record_eq hconst scales Geom H v W W' hW
    change hammingDist c.1 (Geom.project v.1) ≤ _
    have hd := (Finset.mem_filter.mp hc).2.2
    have ht := hammingDist_triangle c.1 u (Geom.project v.1)
    dsimp only [PrimitiveHistory.Device, patchHD] at hd hu ht ⊢
    simp only [hammingDist, Finset.filter_congr_decidable] at hd hu ht ⊢
    omega
  have hcounts : (candidateBall H u j).filter (fun c => H.present W c = true) =
      (candidateBall H u j).filter (fun c => H.present W' c = true) := by
    apply Finset.filter_congr
    intro c hc
    have h := congrArg (fun x => x.2.2.1) (hcenter c hc)
    change H.present W c = H.present W' c at h
    rw [h]
  have hmarked (g : Group 𝒯 i)
      (hg : ∃ u' ∈ groupNeighborhood g, Geom.project u'.1 = u) :
      marked Geom H mask g W = marked Geom H mask g W' := by
    obtain ⟨u', hu', heq⟩ := hg
    have hgroup : W (.inr (.inl g)) = W' (.inr (.inl g)) := by
      apply local_record_eq hconst scales Geom H v W W' hW
      change hammingDist g.1 (Geom.project v.1) ≤ _
      have hg := group_neighborhood_dist g u' hu'
      have hp := projection_dist_le_one Geom u'.1
      have ht := hammingDist_triangle g.1 u'.1 (Geom.project u'.1)
      have ht' := hammingDist_triangle g.1 u (Geom.project v.1)
      rw [hammingDist_comm (Geom.project u'.1) u'.1] at hp
      rw [heq] at ht
      rw [heq] at hp
      dsimp only [PrimitiveHistory.Device, patchHD] at hu ht' ⊢
      simp only [hammingDist, Finset.filter_congr_decidable] at hg hp ht ht' hu ⊢
      omega
    have hrange : ∀ c ∈ candidateRange Geom H g, W (.inl c) = W' (.inl c) := by
      intro c hc
      apply local_record_eq hconst scales Geom H v W W' hW
      change hammingDist c.1 (Geom.project v.1) ≤ _
      have hd := candidate_range_dist Geom H g u' hu' c hc
      rw [heq] at hd
      have ht := hammingDist_triangle c.1 u (Geom.project v.1)
      dsimp only [PrimitiveHistory.Device, patchHD] at hd hu ht ⊢
      simp only [hammingDist, Finset.filter_congr_decidable] at hd hu ht ⊢
      omega
    unfold marked
    rw [failedFamily_congr Geom H mask hlookup g W W' hgroup (fun c hc =>
      ⟨congrArg (fun x => x.2.2.1) (hrange c hc), congrArg (fun x => x.2.1) (hrange c hc)⟩)]
  unfold eligible
  rw [hcounts]
  congr 1
  apply Finset.biUnion_congr rfl
  intro g _
  split_ifs with hg
  · exact hmarked g hg
  · rfl

private theorem bad_congr_local (hconst : HeightConstantContract κ)
    (scales : PatchScales 𝒯 i) (Geom : ProjectionGeometry κ 𝒯 i)
    (H : PrimitiveHistory κ 𝒯 i mesh) (mask : Masks H) (hlookup : MaskLookup H mask)
    (v : EvenRole 𝒯 i) (W W' : ∀ r, H.Val r)
    (hW : ∀ r, (hammingDist (H.loc r) v.1 : ℝ) ≤ 10 * κ.ρ * (𝒯.P i).h → W r = W' r)
    (u : IWord 𝒯 i) (hu : hammingDist u (Geom.project v.1) ≤ H.Device.Rlong)
    (j : Fin (H.Device.H + 1)) :
    H.Device.Bad (H.present W) (H.active W) (eligible Geom H mask W) u j ↔
      H.Device.Bad (H.present W') (H.active W') (eligible Geom H mask W') u j := by
  have he := eligible_congr_local hconst scales Geom H mask hlookup v W W' hW u hu j
  have hactive (c : H.Center) (hc : c ∈ eligible Geom H mask W u j) :
      H.active W c = H.active W' c := by
    have hr : W (.inl c) = W' (.inl c) := by
      apply local_record_eq hconst scales Geom H v W W' hW
      change hammingDist c.1 (Geom.project v.1) ≤ _
      have hball := (Finset.mem_filter.mp (Finset.mem_sdiff.mp hc).1).1
      have hd := (Finset.mem_filter.mp hball).2.2
      have ht := hammingDist_triangle c.1 u (Geom.project v.1)
      dsimp only [PrimitiveHistory.Device, patchHD] at hd hu ht ⊢
      simp only [hammingDist, Finset.filter_congr_decidable] at hd hu ht ⊢
      omega
    exact congrArg (fun x => x.2.2.2) hr
  have hnone : (∀ c ∈ eligible Geom H mask W u j, H.active W c = false) ↔
      (∀ c ∈ eligible Geom H mask W' u j, H.active W' c = false) := by
    rw [← he]
    constructor <;> intro hn c hc
    · rw [← hactive c hc]
      exact hn c hc
    · rw [hactive c hc]
      exact hn c hc
  have hfilter : (Finset.univ.filter fun z : CubePos H.Device.d => H.present W (z, j) = true ∧
      H.active W (z, j) = true ∧ hammingDist z u ≤ H.Device.r + H.Device.D) =
      (Finset.univ.filter fun z : CubePos H.Device.d => H.present W' (z, j) = true ∧
      H.active W' (z, j) = true ∧ hammingDist z u ≤ H.Device.r + H.Device.D) := by
    ext z
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    by_cases hz : hammingDist z u ≤ H.Device.r + H.Device.D
    · have hr : W (.inl (z, j)) = W' (.inl (z, j)) := by
        apply local_record_eq hconst scales Geom H v W W' hW
        change hammingDist z (Geom.project v.1) ≤ _
        have ht := hammingDist_triangle z u (Geom.project v.1)
        have hD : H.Device.D = 6 := rfl
        dsimp only [PrimitiveHistory.Device, patchHD] at hz hu ht hD ⊢
        simp only [hammingDist, Finset.filter_congr_decidable] at hz hu ht ⊢
        omega
      have hp : H.present W (z, j) = H.present W' (z, j) := congrArg (fun x => x.2.2.1) hr
      have ha : H.active W (z, j) = H.active W' (z, j) := congrArg (fun x => x.2.2.2) hr
      rw [hp, ha]
    · simp [hz]
  unfold HDParams.Bad
  rw [hnone, hfilter]

private theorem reach_distance (p : HDParams) (Sites : p.Sites) (P A : p.Loc → Bool)
    (E : p.EligMap) (q u : CubePos p.d) (R j : ℕ)
    (h : p.Reach Sites P A E q R u j) : hammingDist u q ≤ R := by
  induction h with
  | start u _ hu => exact hu
  | up u j hj hr hb ih => exact ih
  | down u u' j hr hu' hd hnear ih => exact hd

private theorem reach_congr_bad (p : HDParams) (Sites : p.Sites)
    (P A P' A' : p.Loc → Bool) (E E' : p.EligMap) (q : CubePos p.d) (R : ℕ)
    (hbad : ∀ u, hammingDist u q ≤ R → ∀ j, p.BadN P A E u j ↔ p.BadN P' A' E' u j)
    (u : CubePos p.d) (j : ℕ) :
    p.Reach Sites P A E q R u j ↔ p.Reach Sites P' A' E' q R u j := by
  constructor <;> intro h
  · induction h with
    | start u hu hd => exact .start u hu hd
    | up u j hj hr hb ih =>
      exact .up u j hj ih ((hbad u (reach_distance p Sites P A E q u R j hr) j).mp hb)
    | down u u' j hr hu' hd hnear ih => exact .down u u' j ih hu' hd hnear
  · induction h with
    | start u hu hd => exact .start u hu hd
    | up u j hj hr hb ih =>
      exact .up u j hj ih ((hbad u (reach_distance p Sites P' A' E' q u R j hr) j).mpr hb)
    | down u u' j hr hu' hd hnear ih => exact .down u u' j ih hu' hd hnear

private theorem height_congr_local (hconst : HeightConstantContract κ)
    (scales : PatchScales 𝒯 i) (Geom : ProjectionGeometry κ 𝒯 i)
    (H : PrimitiveHistory κ 𝒯 i mesh) (mask : Masks H) (hlookup : MaskLookup H mask)
    (v : EvenRole 𝒯 i) (W W' : ∀ r, H.Val r)
    (hW : ∀ r, (hammingDist (H.loc r) v.1 : ℝ) ≤ 10 * κ.ρ * (𝒯.P i).h → W r = W' r) :
    H.Device.height (siteSet Geom) (H.present W) (H.active W) (eligible Geom H mask W)
        H.Device.Rlong (Geom.project v.1) =
      H.Device.height (siteSet Geom) (H.present W') (H.active W') (eligible Geom H mask W')
        H.Device.Rlong (Geom.project v.1) := by
  have hbad : ∀ u, hammingDist u (Geom.project v.1) ≤ H.Device.Rlong → ∀ j,
      H.Device.BadN (H.present W) (H.active W) (eligible Geom H mask W) u j ↔
        H.Device.BadN (H.present W') (H.active W') (eligible Geom H mask W') u j := by
    intro u hu j
    unfold HDParams.BadN
    exact exists_congr fun hj => bad_congr_local hconst scales Geom H mask hlookup v W W' hW u hu ⟨j, hj⟩
  unfold HDParams.height
  congr 1
  ext j
  simp only [Finset.mem_filter]
  exact and_congr_right fun _ => reach_congr_bad H.Device (siteSet Geom) (H.present W) (H.active W)
    (H.present W') (H.active W') (eligible Geom H mask W) (eligible Geom H mask W')
    (Geom.project v.1) H.Device.Rlong hbad (Geom.project v.1) j

private theorem selected_congr_local (hconst : HeightConstantContract κ)
    (scales : PatchScales 𝒯 i) (Geom : ProjectionGeometry κ 𝒯 i)
    (H : PrimitiveHistory κ 𝒯 i mesh) (mask : Masks H) (hlookup : MaskLookup H mask)
    (v : EvenRole 𝒯 i) (W W' : ∀ r, H.Val r)
    (hW : ∀ r, (hammingDist (H.loc r) v.1 : ℝ) ≤ 10 * κ.ρ * (𝒯.P i).h → W r = W' r) :
    selected Geom H mask W v = selected Geom H mask W' v := by
  have hq : hammingDist (Geom.project v.1) (Geom.project v.1) ≤ H.Device.Rlong := by
    simp
  have hh := height_congr_local hconst scales Geom H mask hlookup v W W' hW
  have hb (j : Fin (H.Device.H + 1)) :
      H.Device.Bad (H.present W) (H.active W) (eligible Geom H mask W) (Geom.project v.1) j =
      H.Device.Bad (H.present W') (H.active W') (eligible Geom H mask W') (Geom.project v.1) j :=
    propext (bad_congr_local hconst scales Geom H mask hlookup v W W' hW _ hq j)
  have he (j : Fin (H.Device.H + 1)) :
      ((eligible Geom H mask W (Geom.project v.1) j).filter fun c => H.active W c = true) =
      ((eligible Geom H mask W' (Geom.project v.1) j).filter fun c => H.active W' c = true) := by
    have hel := eligible_congr_local hconst scales Geom H mask hlookup v W W' hW _ hq j
    rw [← hel]
    apply Finset.filter_congr
    intro c hc
    have hr : W (.inl c) = W' (.inl c) := by
      apply local_record_eq hconst scales Geom H v W W' hW
      change hammingDist c.1 (Geom.project v.1) ≤ _
      have hball := (Finset.mem_filter.mp (Finset.mem_sdiff.mp hc).1).1
      have hd := (Finset.mem_filter.mp hball).2.2
      dsimp only [PrimitiveHistory.Device, patchHD] at hd ⊢
      simp only [hammingDist, Finset.filter_congr_decidable] at hd ⊢
      omega
    have ha : H.active W c = H.active W' c := congrArg (fun x => x.2.2.2) hr
    rw [ha]
  have hp (j : Fin (H.Device.H + 1)) :
      H.Device.priority (H.ties W) (Geom.project v.1, j) =
        H.Device.priority (H.ties W') (Geom.project v.1, j) := by
    have hr := local_record_eq hconst scales Geom H v W W' hW
      (.inr (.inr (Geom.project v.1, j))) (by
        change hammingDist (Geom.project v.1) (Geom.project v.1) ≤ _
        rw [hammingDist_self]
        omega)
    funext c
    change W (.inr (.inr (Geom.project v.1, j))) _ = W' (.inr (.inr (Geom.project v.1, j))) _
    rw [hr]
  unfold selected HDParams.selection HDParams.selectionAt
  simp only [hh, hb, he, hp]

private theorem eligible_input_congr (Geom : ProjectionGeometry κ 𝒯 i)
    (H : PrimitiveHistory κ 𝒯 i mesh) (mask : Masks H) (hlookup : MaskLookup H mask)
    (W W' : ∀ r, H.Val r)
    (hgroup : ∀ g, W (.inr (.inl g)) = W' (.inr (.inl g)))
    (hc : ∀ c, H.present W c = H.present W' c ∧ H.tuple W c = H.tuple W' c) :
    eligible Geom H mask W = eligible Geom H mask W' := by
  classical
  funext u j
  have hcounts : (candidateBall H u j).filter (fun c => H.present W c = true) =
      (candidateBall H u j).filter (fun c => H.present W' c = true) := by
    apply Finset.filter_congr
    intro c _
    rw [(hc c).1]
  unfold eligible
  rw [hcounts]
  congr 1
  apply Finset.biUnion_congr rfl
  intro g _
  split_ifs
  · unfold marked
    rw [failedFamily_congr Geom H mask hlookup g W W' (hgroup g) (fun c _ => hc c)]
  · rfl

end SelectionLocalProof

section RecordFactorProof

set_option backward.isDefEq.respectTransparency false

variable {κ : CConsts} {T : Stage} {k : ℕ} {𝒯 : Tiling κ T k}
  {i : Fin 𝒯.m} {mesh : Mesh 𝒯}

private abbrev HeightAux (H : PrimitiveHistory κ 𝒯 i mesh) :=
  (H.Center → mesh.V × H.Tuple) ×
    ((Group 𝒯 i → mesh.V × SearchPerm H.Device (𝒯.tScale i)) × H.Device.Ties)

private noncomputable def heightAuxLaw (H : PrimitiveHistory κ 𝒯 i mesh)
    (p : mesh.Param) : FinProb (HeightAux H) := by
  classical
  let CT := FinLaw.pi fun _c : H.Center =>
    FinLaw.bind (PrimitiveHistory.vertexLaw p) H.tuplePrior
  let G := FinLaw.pi fun _g : Group 𝒯 i => H.groupLaw p
  let τ := FinLaw.pi fun _c : H.Center => H.tieLaw
  let A := FinLaw.bind CT fun _ => FinLaw.bind G fun _ => τ
  exact ⟨A.w, A.nonneg, A.sum_one⟩

private noncomputable def heightUnpack (H : PrimitiveHistory κ 𝒯 i mesh) :
    (∀ r, H.Val r) ≃ (((H.Center → Bool) × HeightAux H) × (H.Center → Bool)) where
  toFun W := ((H.present W,
    ((fun c => (H.cornerOf W c, H.tuple W c)),
      ((fun g => W (.inr (.inl g))), H.ties W))), H.active W)
  invFun ω := fun r => match r with
    | .inl c => ((ω.1.2.1 c).1, ((ω.1.2.1 c).2, ω.1.1 c, ω.2 c))
    | .inr (.inl g) => ω.1.2.2.1 g
    | .inr (.inr c) => ω.1.2.2.2 c
  left_inv W := by
    funext r
    cases r with
    | inl c => rfl
    | inr r => cases r <;> rfl
  right_inv ω := by
    rcases ω with ⟨⟨P, CT, G, τ⟩, A⟩
    rfl

private theorem heightUnpack_weight (H : PrimitiveHistory κ 𝒯 i mesh)
    (p : mesh.Param) (W : ∀ r, H.Val r) :
    (H.recLaw p).w W =
      ((H.Device.posLaw.prod (heightAuxLaw H p)).prod H.Device.actLaw).w (heightUnpack H W) := by
  classical
  dsimp [PrimitiveHistory.recLaw, recordLaw, FinLaw.pi, PrimitiveHistory.lawRec,
    heightAuxLaw, HDParams.posLaw, HDParams.actLaw, FinProb.pi, FinProb.prod,
    FinLaw.bind, heightUnpack]
  rw [Fintype.prod_sum_type, Fintype.prod_sum_type]
  dsimp [PrimitiveHistory.record, PrimitiveHistory.centerLaw, PrimitiveHistory.groupLaw,
    PrimitiveHistory.tieLaw, FinLaw.bind, PrimitiveHistory.finProbToFinLaw,
    PrimitiveHistory.vertexLaw, PrimitiveHistory.cornerOf, PrimitiveHistory.tuple,
    PrimitiveHistory.present, PrimitiveHistory.active, PrimitiveHistory.ties]
  simp only [Finset.prod_mul_distrib]
  ring

private theorem recLaw_pr_heightUnpack (H : PrimitiveHistory κ 𝒯 i mesh)
    (p : mesh.Param) (F : (∀ r, H.Val r) → Prop) :
    (H.recLaw p).pr F =
      ((H.Device.posLaw.prod (heightAuxLaw H p)).prod H.Device.actLaw).pr
        (fun ω => F ((heightUnpack H).symm ω)) := by
  classical
  unfold FinLaw.pr FinProb.pr
  apply Fintype.sum_equiv (heightUnpack H)
  intro W
  simp only [Equiv.symm_apply_apply]
  split_ifs
  · exact heightUnpack_weight H p W
  · rfl

private noncomputable def heightEligibility (Geom : ProjectionGeometry κ 𝒯 i)
    (H : PrimitiveHistory κ 𝒯 i mesh) (mask : Masks H)
    (P : H.Center → Bool) (aux : HeightAux H) : H.Device.EligMap :=
  eligible Geom H mask ((heightUnpack H).symm ((P, aux), fun _ => false))

private theorem heightEligibility_eq (Geom : ProjectionGeometry κ 𝒯 i)
    (H : PrimitiveHistory κ 𝒯 i mesh) (mask : Masks H) (hlookup : MaskLookup H mask)
    (ω : ((H.Center → Bool) × HeightAux H) × (H.Center → Bool)) :
    eligible Geom H mask ((heightUnpack H).symm ω) = heightEligibility Geom H mask ω.1.1 ω.1.2 := by
  apply eligible_input_congr Geom H mask hlookup
  · intro g
    rfl
  · intro c
    exact ⟨rfl, rfl⟩

private theorem patch_regime_ok (hκ : κ.Admissible) (hconst : HeightConstantContract κ)
    (scales : PatchScales 𝒯 i) (H : PrimitiveHistory κ 𝒯 i mesh) :
    hconst.regime.ok H.Device.n H.Device.d H.Device.r := by
  obtain ⟨hρ, hreg⟩ := hconst.regime_linear
  rw [hreg]
  change (κ.ρ / 2) * (𝒯.P i).h ≤ (⌊κ.ρ * (𝒯.P i).h⌋₊ : ℝ) ∧
    4 * ⌊κ.ρ * (𝒯.P i).h⌋₊ ≤ (𝒯.P i).h
  have hrad := patch_radius_pos hconst scales H
  have hr : (1 : ℝ) ≤ ⌊κ.ρ * (𝒯.P i).h⌋₊ := by exact_mod_cast hrad
  have hlo := Nat.lt_floor_add_one (κ.ρ * (𝒯.P i).h)
  have hhi := Nat.floor_le (mul_nonneg hκ.ρ_rng.1.le (Nat.cast_nonneg (𝒯.P i).h))
  constructor
  · nlinarith
  · have hfour : (4 : ℝ) * ⌊κ.ρ * (𝒯.P i).h⌋₊ ≤ (𝒯.P i).h := by
      nlinarith [mul_nonneg (show 0 ≤ 1 / 4 - κ.ρ by linarith [hκ.ρ_rng.2.1])
        (Nat.cast_nonneg (𝒯.P i).h)]
    exact_mod_cast hfour

private theorem patch_global_height_bound (hκ : κ.Admissible) (hconst : HeightConstantContract κ)
    (scales : PatchScales 𝒯 i) (Geom : ProjectionGeometry κ 𝒯 i)
    (H : PrimitiveHistory κ 𝒯 i mesh) (mask : Masks H) (hlookup : MaskLookup H mask)
    (p : mesh.Param) :
    (H.recLaw p).pr (fun W =>
      H.Device.Legal (H.present W) (eligible Geom H mask W) (siteSet Geom) ∧
        ¬ H.Device.GoodHeights (siteSet Geom) (H.present W) (H.active W) (eligible Geom H mask W)) ≤
      Real.exp (-Real.rpow ((𝒯.P i).h : ℝ) (1 + hconst.globalExponent)) := by
  obtain ⟨hJ, hb₀, hb, hσ, hζ, hθ, ha, hcd, hCd, hα⟩ := hconst.exponents_match
  have hbound := hconst.global_bound H.Device rfl
    (by rw [hσ, hζ]; rfl)
    (by simp [hJ, PrimitiveHistory.Device, patchHD, Real.rpow_natCast])
    (by rw [hb₀]; rfl) (by rw [hb]; rfl)
    (le_trans hconst.global_h0 scales.h_large)
    (by rw [hcd]; simp [PrimitiveHistory.Device, patchHD])
    (by rw [hCd]; simp [PrimitiveHistory.Device, patchHD])
    (patch_regime_ok hκ hconst scales H)
    (siteSet Geom) (heightAuxLaw H p) (heightEligibility Geom H mask)
  rw [recLaw_pr_heightUnpack H p]
  simp_rw [heightEligibility_eq Geom H mask hlookup]
  exact hbound

private theorem patch_positive_height_bound (hκ : κ.Admissible) (hconst : HeightConstantContract κ)
    (scales : PatchScales 𝒯 i) (Geom : ProjectionGeometry κ 𝒯 i)
    (H : PrimitiveHistory κ 𝒯 i mesh) (mask : Masks H) (hlookup : MaskLookup H mask)
    (πAux : FinProb (HeightAux H)) (v : EvenRole 𝒯 i) (forced : Option H.Center) :
    (((H.Device.posLawForced forced).prod πAux).prod H.Device.actLaw).pr
      (fun ω =>
        let W := (heightUnpack H).symm ω
        H.Device.Legal (H.present W) (eligible Geom H mask W)
          (H.Device.domBall (siteSet Geom) (Geom.project v.1) H.Device.Rlong) ∧
        0 < H.Device.height (siteSet Geom) (H.present W) (H.active W)
          (eligible Geom H mask W) H.Device.Rlong (Geom.project v.1)) ≤
      Real.exp (-Real.rpow ((𝒯.P i).h : ℝ) hconst.positiveExponent) := by
  obtain ⟨hJ, hb₀, hb, hσ, hζ, hθ, ha, hcd, hCd, hα⟩ := hconst.exponents_match
  have hv : Geom.project v.1 ∈ siteSet Geom := Finset.mem_image.mpr ⟨v, Finset.mem_univ _, rfl⟩
  have hbound := hconst.positive_bound H.Device rfl
    (by rw [hσ, hζ]; rfl)
    (by simp [hJ, PrimitiveHistory.Device, patchHD, Real.rpow_natCast])
    (by rw [hb₀]; rfl) (by rw [hb]; rfl)
    (le_trans hconst.positive_h0 scales.h_large)
    (by rw [hcd]; simp [PrimitiveHistory.Device, patchHD])
    (by rw [hCd]; simp [PrimitiveHistory.Device, patchHD])
    (patch_regime_ok hκ hconst scales H)
    (siteSet Geom) (Geom.project v.1) hv forced πAux (heightEligibility Geom H mask)
  dsimp only []
  simp_rw [heightEligibility_eq Geom H mask hlookup]
  exact hbound

private theorem eligibility_gate_legal (hconst : HeightConstantContract κ)
    (Geom : ProjectionGeometry κ 𝒯 i) (H : PrimitiveHistory κ 𝒯 i mesh) (mask : Masks H)
    (he : EligibilityFacts hconst Geom H mask) (W : ∀ r, H.Val r)
    (hlarge : ∀ u ∈ siteSet Geom, ∀ j, H.Device.lam / 2 ≤ (eligible Geom H mask W u j).card) :
    H.Device.Legal (H.present W) (eligible Geom H mask W) (siteSet Geom) := by
  intro u hu j
  constructor
  · intro c hc
    obtain ⟨hb, hp⟩ := he.eligible_subset W u j c hc
    obtain ⟨_, hl, hd⟩ := Finset.mem_filter.mp hb
    exact ⟨hp, hl, hd⟩
  · have hlam_nonneg : 0 ≤ H.Device.lam := by dsimp [PrimitiveHistory.Device, patchHD]; positivity
    have := hlarge u hu j
    linarith

private theorem position_gate_upper (H : PrimitiveHistory κ 𝒯 i mesh)
    (W : ∀ r, H.Val r) (hgate : PositionCountGate H W)
    (u : IWord 𝒯 i) (j : Fin (H.Device.H + 1)) :
    (((candidateBall H u j).filter fun c => H.present W c = true).card : ℝ) ≤
      2 * H.Device.lam := by
  have hlam_nonneg : 0 ≤ H.Device.lam := by dsimp [PrimitiveHistory.Device, patchHD]; positivity
  have := (abs_le.mp (hgate u j)).2
  linarith

private theorem selection_exists_of_good (p : HDParams) (Sites : p.Sites)
    (P A : p.Loc → Bool) (E : p.EligMap) (τ : p.Ties) (v : CubePos p.d)
    (hv : v ∈ Sites) (hgood : p.GoodHeights Sites P A E) :
    ∃ c, p.selection Sites P A E τ v = some c := by
  classical
  have hh := (hgood v hv).1
  let j : Fin (p.H + 1) := ⟨p.height Sites P A E p.Rlong v, by omega⟩
  have hb : ¬ p.Bad P A E v j := fun h => (hgood v hv).2.1 ⟨by omega, h⟩
  have ha : ∃ c ∈ E v j, A c = true := by
    by_contra hn
    push_neg at hn
    apply hb
    left
    intro c hc
    cases heq : A c
    · rfl
    · exact False.elim (hn c hc heq)
  obtain ⟨c, hc, hAc⟩ := ha
  have hne : (((E v j).filter fun ℓ => A ℓ = true).image
      (fun ℓ => p.priority τ (v, j) ℓ)).Nonempty := by
    refine ⟨p.priority τ (v, j) c, ?_⟩
    exact Finset.mem_image.mpr ⟨c, Finset.mem_filter.mpr ⟨hc, hAc⟩, rfl⟩
  unfold HDParams.selection HDParams.selectionAt
  dsimp only []
  rw [dif_pos hh, dif_neg hb, dif_pos hne]
  exact ⟨_, rfl⟩

private theorem realizedList_disjoint_marked (Geom : ProjectionGeometry κ 𝒯 i)
    (H : PrimitiveHistory κ 𝒯 i mesh) (mask : Masks H)
    (hchosen : ∀ W v c, selected Geom H mask W v = some c →
      c ∈ eligible Geom H mask W (Geom.project v.1) c.2)
    (g : Group 𝒯 i) (W : ∀ r, H.Val r) :
    Disjoint (realizedList Geom H mask g W) (marked Geom H mask g W) := by
  classical
  apply Finset.disjoint_left.mpr
  intro c hc hm
  obtain ⟨u, hu, hs⟩ := (Finset.mem_filter.mp hc).2
  have he := hchosen W u c hs
  apply (Finset.mem_sdiff.mp he).2
  apply Finset.mem_biUnion.mpr
  refine ⟨g, Finset.mem_univ _, ?_⟩
  rw [if_pos ⟨u, hu, rfl⟩]
  exact hm

private theorem realizedList_good_of_admissible (Geom : ProjectionGeometry κ 𝒯 i)
    (H : PrimitiveHistory κ 𝒯 i mesh) (mask : Masks H)
    (hchosen : ∀ W v c, selected Geom H mask W v = some c →
      c ∈ eligible Geom H mask W (Geom.project v.1) c.2)
    (g : Group 𝒯 i) (W : ∀ r, H.Val r)
    (hadm : admissibleList Geom H g W (realizedList Geom H mask g W)) :
    listGood H mask g W (realizedList Geom H mask g W) :=
  unmarked_list_good Geom H mask g W _ hadm (realizedList_disjoint_marked Geom H mask hchosen g W)

private theorem groupNeighborhood_nonempty (hconst : HeightConstantContract κ)
    (scales : PatchScales 𝒯 i) (g : Group 𝒯 i) : (groupNeighborhood g).Nonempty := by
  have hh := (hconst.threshold_slack (𝒯.P i).h scales.h_large).1
  let l : Fin (𝒯.P i).h := ⟨0, by omega⟩
  refine ⟨groupCenter g, Finset.mem_filter.mpr ⟨Finset.mem_univ _, l, ?_⟩⟩
  exact Finset.mem_image.mpr ⟨l, Finset.mem_univ _, rfl⟩

private theorem selected_eligible_level (hconst : HeightConstantContract κ)
    (Geom : ProjectionGeometry κ 𝒯 i) (H : PrimitiveHistory κ 𝒯 i mesh) (mask : Masks H)
    (he : EligibilityFacts hconst Geom H mask) (W : ∀ r, H.Val r) (v : EvenRole 𝒯 i)
    (c : H.Center) (hs : selected Geom H mask W v = some c) :
    (c ∈ eligible Geom H mask W (Geom.project v.1) c.2 ∧ H.active W c = true) ∧
      c.2.val = H.Device.height (siteSet Geom) (H.present W) (H.active W)
        (eligible Geom H mask W) H.Device.Rlong (Geom.project v.1) := by
  classical
  unfold selected HDParams.selection HDParams.selectionAt at hs
  dsimp only [] at hs
  split_ifs at hs with hj hbad hne
  let j : Fin (H.Device.H + 1) :=
    ⟨H.Device.height (siteSet Geom) (H.present W) (H.active W)
      (eligible Geom H mask W) H.Device.Rlong (Geom.project v.1), by omega⟩
  let active := ((eligible Geom H mask W (Geom.project v.1) j).filter
    fun ℓ => H.active W ℓ = true)
  let priorities := active.image
    (fun ℓ => H.Device.priority (H.ties W) (Geom.project v.1, j) ℓ)
  have hq : priorities.min' hne ∈ priorities := Finset.min'_mem _ _
  have hmem := Finset.mem_image.mp hq
  have hsel_eq : Classical.choose hmem = c := Option.some.inj hs
  have hchosen : c ∈ active := by
    rw [← hsel_eq]
    exact (Classical.choose_spec hmem).1
  rcases Finset.mem_filter.mp hchosen with ⟨hcElig, hcActive⟩
  have hcLevel : c.2 = j :=
    (Finset.mem_filter.mp (he.eligible_subset W (Geom.project v.1) j c hcElig).1).2.1
  exact ⟨⟨by simpa [hcLevel] using hcElig, hcActive⟩, congrArg Fin.val hcLevel⟩

private theorem realizedList_card_bound (hconst : HeightConstantContract κ)
    (scales : PatchScales 𝒯 i) (Geom : ProjectionGeometry κ 𝒯 i)
    (H : PrimitiveHistory κ 𝒯 i mesh) (mask : Masks H)
    (he : EligibilityFacts hconst Geom H mask) (W : ∀ r, H.Val r)
    (hg : H.Device.GoodHeights (siteSet Geom) (H.present W) (H.active W) (eligible Geom H mask W))
    (g : Group 𝒯 i) : (realizedList Geom H mask g W).card ≤ 𝒯.tScale i := by
  classical
  let f := fun u : EvenRole 𝒯 i => H.Device.height (siteSet Geom) (H.present W) (H.active W)
    (eligible Geom H mask W) H.Device.Rlong (Geom.project u.1)
  have hne := groupNeighborhood_nonempty hconst scales g
  obtain ⟨lo, hlo, hlomin⟩ := Finset.exists_max_image (groupNeighborhood g)
    (fun u => OrderDual.toDual (f u)) hne
  obtain ⟨hi, hhi, hhimax⟩ := Finset.exists_max_image (groupNeighborhood g) f hne
  have hsite (u : EvenRole 𝒯 i) : Geom.project u.1 ∈ siteSet Geom :=
    Finset.mem_image.mpr ⟨u, Finset.mem_univ _, rfl⟩
  have hnear := Geom.projected_distance g hi lo hhi hlo
  have hheight := (hg (Geom.project hi.1) (hsite hi)).2.2 (Geom.project lo.1) (hsite lo) hnear
  have hgap : f hi ≤ f lo + 1 := by
    have := (abs_le.mp hheight).2
    dsimp only [f]
    omega
  have hlevels (u : EvenRole 𝒯 i) (hu : u ∈ groupNeighborhood g) : f u = f lo ∨ f u = f hi := by
    have hl : f lo ≤ f u := hlomin u hu
    have hh := hhimax u hu
    omega
  let jl : Fin (H.Device.H + 1) := ⟨f lo, by have := (hg _ (hsite lo)).1; dsimp [f] at *; omega⟩
  let jh : Fin (H.Device.H + 1) := ⟨f hi, by have := (hg _ (hsite hi)).1; dsimp [f] at *; omega⟩
  let ball := fun (u : EvenRole 𝒯 i) (j : Fin (H.Device.H + 1)) =>
    Finset.univ.filter fun z : CubePos H.Device.d => H.present W (z, j) = true ∧
      H.active W (z, j) = true ∧ hammingDist z (Geom.project u.1) ≤ H.Device.r + H.Device.D
  let Bl := (ball lo jl).image fun z => (z, jl)
  let Bh := (ball hi jh).image fun z => (z, jh)
  have hsub : realizedList Geom H mask g W ⊆ Bl ∪ Bh := by
    intro c hc
    obtain ⟨u, hu, hs⟩ := (Finset.mem_filter.mp hc).2
    have hsel := selected_eligible_level hconst Geom H mask he W u c hs
    have hcand := he.eligible_subset W (Geom.project u.1) c.2 c hsel.1.1
    have hdist := (Finset.mem_filter.mp hcand.1).2.2
    have hselLevel : c.2.val = f u := hsel.2
    have hmem (r : EvenRole 𝒯 i) (hr : r ∈ groupNeighborhood g)
        (j : Fin (H.Device.H + 1)) (hj : c.2 = j) :
        c ∈ (ball r j).image (fun z => (z, j)) := by
      have hnear := Geom.projected_distance g u r hu hr
      have hnear' : hammingDist (Geom.project u.1) (Geom.project r.1) ≤ 6 := by
        convert hnear using 1 <;> congr
      have ht := hammingDist_triangle c.1 (Geom.project u.1) (Geom.project r.1)
      have hd : hammingDist c.1 (Geom.project r.1) ≤ H.Device.r + H.Device.D := by
        have hD : H.Device.D = 6 := rfl
        dsimp only [PrimitiveHistory.Device, patchHD] at hdist hnear' ht hD ⊢
        simp only [hammingDist, Finset.filter_congr_decidable] at hdist hnear' ht ⊢
        omega
      have hpair : (c.1, j) = c := Prod.ext rfl hj.symm
      apply Finset.mem_image.mpr
      refine ⟨c.1, Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_⟩, ?_⟩
      · exact ⟨by rw [hpair]; exact hcand.2, by rw [hpair]; exact hsel.1.2, hd⟩
      · exact Prod.ext rfl hj.symm
    rcases hlevels u hu with hl | hh
    · apply Finset.mem_union_left
      exact hmem lo hlo jl (Fin.ext (hselLevel.trans hl))
    · apply Finset.mem_union_right
      exact hmem hi hhi jh (Fin.ext (hselLevel.trans hh))
  have hball (u : EvenRole 𝒯 i) (j : Fin (H.Device.H + 1)) (hj : j.val = f u) :
      ((ball u j).card : ℝ) ≤ (H.Device.n : ℝ) ^ H.Device.b := by
    have hb : ¬ H.Device.Bad (H.present W) (H.active W) (eligible Geom H mask W) (Geom.project u.1) j := by
      intro hb
      apply (hg _ (hsite u)).2.1
      have hN : H.Device.BadN (H.present W) (H.active W) (eligible Geom H mask W)
          (Geom.project u.1) j.val := ⟨j.isLt, hb⟩
      rwa [hj] at hN
    exact le_of_not_gt fun hc => hb (Or.inr hc)
  have hcard : ((realizedList Geom H mask g W).card : ℝ) ≤ 2 * (H.Device.n : ℝ) ^ H.Device.b := by
    have hnat := le_trans (Finset.card_le_card hsub) (Finset.card_union_le Bl Bh)
    have hreal : ((realizedList Geom H mask g W).card : ℝ) ≤ (Bl.card : ℝ) + Bh.card := by exact_mod_cast hnat
    have hl : (Bl.card : ℝ) ≤ (ball lo jl).card := by exact_mod_cast Finset.card_image_le
    have hh : (Bh.card : ℝ) ≤ (ball hi jh).card := by exact_mod_cast Finset.card_image_le
    linarith [hball lo jl rfl, hball hi jh rfl]
  have ht := (hconst.threshold_slack (𝒯.P i).h scales.h_large).2.2.2.2.2.1
  exact_mod_cast le_trans hcard ht

private theorem starValid_of_gates (hconst : HeightConstantContract κ)
    (scales : PatchScales 𝒯 i) (Geom : ProjectionGeometry κ 𝒯 i)
    (H : PrimitiveHistory κ 𝒯 i mesh) (mask : Masks H)
    (he : EligibilityFacts hconst Geom H mask) (W : ∀ r, H.Val r)
    (hcounts : PositionCountGate H W)
    (helig : ∀ u ∈ siteSet Geom, ∀ j, H.Device.lam / 2 ≤ (eligible Geom H mask W u j).card)
    (hgood : H.Device.GoodHeights (siteSet Geom) (H.present W) (H.active W) (eligible Geom H mask W))
    (v : EvenRole 𝒯 i) : starValid Geom H mask v W := by
  classical
  have hsite (u : EvenRole 𝒯 i) : Geom.project u.1 ∈ siteSet Geom :=
    Finset.mem_image.mpr ⟨u, Finset.mem_univ _, rfl⟩
  have hsel (u : EvenRole 𝒯 i) : ∃ c, selected Geom H mask W u = some c :=
    selection_exists_of_good H.Device (siteSet Geom) (H.present W) (H.active W)
      (eligible Geom H mask W) (H.ties W) _ (hsite u) hgood
  have hchosen : ∀ W u c, selected Geom H mask W u = some c →
      c ∈ eligible Geom H mask W (Geom.project u.1) c.2 :=
    fun W u c hs => (selected_eligible_level hconst Geom H mask he W u c hs).1.1
  refine ⟨?_, ?_, hsel v⟩
  · intro g hvg
    have hadm : admissibleList Geom H g W (realizedList Geom H mask g W) := by
      refine ⟨?_, realizedList_card_bound hconst scales Geom H mask he W hgood g, ?_⟩
      · obtain ⟨c, hc⟩ := hsel v
        exact ⟨c, Finset.mem_filter.mpr ⟨Finset.mem_univ _, v, hvg, hc⟩⟩
      · intro c hc
        obtain ⟨u, hu, hs⟩ := (Finset.mem_filter.mp hc).2
        obtain ⟨hb, hp⟩ := he.eligible_subset W _ _ c (hchosen W u c hs)
        refine ⟨?_, hp⟩
        exact Finset.mem_biUnion.mpr ⟨u, hu,
          Finset.mem_biUnion.mpr ⟨c.2, Finset.mem_univ _, hb⟩⟩
    refine ⟨?_, hadm, realizedList_good_of_admissible Geom H mask hchosen g W hadm⟩
    intro u hu
    obtain ⟨c, hc⟩ := hsel u
    exact ⟨c, hc, position_gate_upper H W hcounts _ _⟩
  · intro u hu j
    exact ⟨position_gate_upper H W hcounts u j, helig u (Finset.mem_filter.mp hu).1 j⟩

end RecordFactorProof

/-- P14.1e: L3.8 for the actual independent Bernoulli and uniform tie draws. -/
theorem height_selection_at_patch (κ : CConsts) (hκ : κ.Admissible)
    (hconst : HeightConstantContract κ)
    {T : Stage} {k : ℕ} {𝒯 : Tiling κ T k} (h𝒯 : Tiling.Valid 𝒯)
    (hcluster : 𝒯.mode.isCluster) {i : Fin 𝒯.m} {mesh : Mesh 𝒯}
    (scales : PatchScales 𝒯 i) (Geom : ProjectionGeometry κ 𝒯 i)
    (H : PrimitiveHistory κ 𝒯 i mesh) (mask : Masks H) (hlookup : MaskLookup H mask)
    (he : EligibilityFacts hconst Geom H mask) : HeightFacts hconst Geom H mask := by
  classical
  refine ⟨?_, ?_, ?_⟩
  · intro p
    let A := fun W => ¬ (PositionCountGate H W ∧
      ∀ u ∈ siteSet Geom, ∀ j, H.Device.lam / 2 ≤ (eligible Geom H mask W u j).card)
    let B := fun W => H.Device.Legal (H.present W) (eligible Geom H mask W) (siteSet Geom) ∧
      ¬ H.Device.GoodHeights (siteSet Geom) (H.present W) (H.active W) (eligible Geom H mask W)
    have himp (W : ∀ r, H.Val r) (hf : ∃ v, ¬ starValid Geom H mask v W) : A W ∨ B W := by
      by_cases hg : PositionCountGate H W ∧
          ∀ u ∈ siteSet Geom, ∀ j, H.Device.lam / 2 ≤ (eligible Geom H mask W u j).card
      · right
        refine ⟨eligibility_gate_legal hconst Geom H mask he W hg.2, ?_⟩
        intro hh
        obtain ⟨v, hv⟩ := hf
        exact hv (starValid_of_gates hconst scales Geom H mask he W hg.1 hg.2 hh v)
      · exact Or.inl hg
    calc
      (H.recLaw p).pr (fun W => ∃ v, ¬ starValid Geom H mask v W) ≤
          (H.recLaw p).pr A + (H.recLaw p).pr B := by
        unfold FinLaw.pr
        rw [← Finset.sum_add_distrib]
        apply Finset.sum_le_sum
        intro W _
        by_cases hf : ∃ v, ¬ starValid Geom H mask v W
        · rcases himp W hf with ha | hb
          · simp only [if_pos hf, if_pos ha]
            split_ifs <;> linarith [(H.recLaw p).nonneg W]
          · simp only [if_pos hf, if_pos hb]
            split_ifs <;> linarith [(H.recLaw p).nonneg W]
        · simp only [if_neg hf]
          split_ifs <;> linarith [(H.recLaw p).nonneg W]
      _ ≤ 2 * Real.exp (-Real.rpow ((𝒯.P i).h : ℝ) (1 + hconst.sliceExponent)) +
          Real.exp (-Real.rpow ((𝒯.P i).h : ℝ) (1 + hconst.globalExponent)) :=
        add_le_add (he.eligible_gate p) (patch_global_height_bound hκ hconst scales Geom H mask hlookup p)
      _ = _ := by ring
  · intro W v c hs
    exact (selected_eligible_level hconst Geom H mask he W v c hs).1
  · exact selected_congr_local hconst scales Geom H mask hlookup

/-- The selected tuple's average coordinate incidence, with the actual local
selection/validity gate and unrestricted primitive law. -/
noncomputable def SelectionIncidence {κ : CConsts} {T : Stage} {k : ℕ}
    {𝒯 : Tiling κ T k} {i : Fin 𝒯.m} {mesh : Mesh 𝒯}
    (Geom : ProjectionGeometry κ 𝒯 i) (H : PrimitiveHistory κ 𝒯 i mesh)
    (mask : Masks H) : Prop :=
  ∀ p v x, (H.recLaw p).E (fun W =>
    if starValid Geom H mask v W then
      match selected Geom H mask W v with
      | none => 0
      | some c => (∑ r, if H.tuple W c r = x then (1 : ℝ) else 0) / 𝒯.kScale i
    else 0) ≤ 16 / (𝒯.P i).M

section IncidenceProof

set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000

variable {κ : CConsts} {T : Stage} {k : ℕ} {𝒯 : Tiling κ T k}
  {i : Fin 𝒯.m} {mesh : Mesh 𝒯}

private theorem prob_prod_expect {α β : Type*} [Fintype α] [Fintype β]
    (P : FinProb α) (Q : FinProb β) (f : α × β → ℝ) :
    (P.prod Q).expect f = ∑ a, P.w a * Q.expect (fun b => f (a,b)) := by
  simp only [FinProb.expect, FinProb.prod, Fintype.sum_prod_type]
  congr 1
  funext a
  rw [Finset.mul_sum]
  congr 1
  funext b
  ring

private theorem prob_prod_nested {α β : Type*} [Fintype α] [Fintype β]
    (P : FinProb α) (Q : FinProb β) (f : α × β → ℝ) :
    (P.prod Q).expect f =
      P.expect (fun a => Q.expect (fun b => f (a,b))) := prob_prod_expect P Q _

private theorem prob_three_nested {α β γ : Type*}
    [Fintype α] [Fintype β] [Fintype γ]
    (P : FinProb α) (Q : FinProb β) (R : FinProb γ) (f : (α × β) × γ → ℝ) :
    ((P.prod Q).prod R).expect f =
      P.expect (fun a => Q.expect (fun b => R.expect (fun c => f ((a,b),c)))) := by
  rw [prob_prod_nested, prob_prod_nested]

private theorem prob_swap_expect {α β : Type*} [Fintype α] [Fintype β]
    (P : FinProb α) (Q : FinProb β) (f : α → β → ℝ) :
    P.expect (fun a => Q.expect (f a)) = Q.expect (fun b => P.expect (fun a => f a b)) := by
  simp only [FinProb.expect, Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro b _
  apply Finset.sum_congr rfl
  intro a _
  ring

private theorem prob_pr_indicator {α : Type*} [Fintype α]
    (P : FinProb α) (A : α → Prop) : P.pr A = P.expect (fun a => if A a then 1 else 0) := by
  classical
  simp only [FinProb.pr, FinProb.expect]
  apply Finset.sum_congr rfl
  intro a _
  split_ifs <;> ring

private theorem prob_delta_expect {α : Type*} [Fintype α] [DecidableEq α]
    (a : α) (f : α → ℝ) :
    (FinProb.uniform {a} (Finset.singleton_nonempty _)).expect f = f a := by
  classical
  simp [FinProb.expect, FinProb.uniform]

private theorem prob_pi_coord {α β : Type*} [Fintype α] [DecidableEq α]
    [Fintype β] (P : α → FinProb β) (c : α) (f : β → ℝ) :
    (FinProb.pi P).expect (fun ω => f (ω c)) = (P c).expect f := by
  classical
  have hprod (ω : α → β) :
      (∏ a, (P a).w (ω a)) * f (ω c) =
        ∏ a, (P a).w (ω a) * (if a = c then f (ω a) else 1) := by
    rw [Finset.prod_mul_distrib]
    simp
  simp only [FinProb.expect, FinProb.pi, hprod]
  rw [← Fintype.prod_sum (fun a (b : β) => (P a).w b * (if a = c then f b else 1))]
  have hsum (a : α) :
      (∑ b, (P a).w b * (if a = c then f b else 1)) =
        if a = c then (P c).expect f else 1 := by
    split_ifs with h
    · subst a; rfl
    · simpa [h] using (P a).sum_eq_one
  simp_rw [hsum]
  simp [FinProb.expect]

private theorem prob_expect_sum {α β : Type*} [Fintype α] [Fintype β]
    (P : FinProb α) (f : β → α → ℝ) :
    P.expect (fun a => ∑ b, f b a) = ∑ b, P.expect (f b) := by
  simp only [FinProb.expect, Finset.mul_sum]
  exact Finset.sum_comm

private theorem recLaw_E_heightUnpack (H : PrimitiveHistory κ 𝒯 i mesh)
    (p : mesh.Param) (f : (∀ r, H.Val r) → ℝ) :
    (H.recLaw p).E f =
      ((H.Device.posLaw.prod (heightAuxLaw H p)).prod H.Device.actLaw).expect
        (fun ω => f ((heightUnpack H).symm ω)) := by
  unfold FinLaw.E FinProb.expect
  apply Fintype.sum_equiv (heightUnpack H)
  intro W
  rw [heightUnpack_weight]
  simp

private noncomputable def tupleIncidence (H : PrimitiveHistory κ 𝒯 i mesh)
    (x : Fin (T.S.N k)) (w : H.Tuple) : ℝ :=
  (∑ r, if w r = x then (1 : ℝ) else 0) / 𝒯.kScale i

private theorem tupleIncidence_nonneg (H : PrimitiveHistory κ 𝒯 i mesh)
    (x : Fin (T.S.N k)) (w : H.Tuple) : 0 ≤ tupleIncidence H x w := by
  unfold tupleIncidence
  positivity

private theorem tuplePrior_incidence (H : PrimitiveHistory κ 𝒯 i mesh)
    (p : mesh.Param) (v : mesh.V) (hv : 0 < mesh.wt v p)
    (hk : 0 < 𝒯.kScale i) (x : Fin (T.S.N k)) :
    (⟨(H.tuplePrior v).w, (H.tuplePrior v).nonneg, (H.tuplePrior v).sum_one⟩ : FinProb H.Tuple).expect
      (tupleIncidence H x) ≤ 2 / (𝒯.P i).M := by
  change (FinProb.pi fun _ : Fin (𝒯.kScale i) =>
      (⟨(H.prior v).w, (H.prior v).nonneg, (H.prior v).sum_eq_one⟩ : FinProb _)).expect
      (tupleIncidence H x) ≤ _
  let P : FinProb (Fin (T.S.N k)) :=
    ⟨(H.prior v).w, (H.prior v).nonneg, (H.prior v).sum_eq_one⟩
  change (FinProb.pi fun _ : Fin (𝒯.kScale i) => P).expect
      (fun w => (∑ r, if w r = x then (1 : ℝ) else 0) / 𝒯.kScale i) ≤ _
  have heq : (FinProb.pi fun _ : Fin (𝒯.kScale i) => P).expect
      (fun w => (∑ r, if w r = x then (1 : ℝ) else 0) / 𝒯.kScale i) = P.w x := by
    simp_rw [div_eq_mul_inv, mul_comm _ ((𝒯.kScale i : ℝ)⁻¹)]
    rw [FinProb.expect_smul, prob_expect_sum]
    have heach (r : Fin (𝒯.kScale i)) := prob_pi_coord (fun _ : Fin (𝒯.kScale i) => P) r
      (fun y => if y = x then (1 : ℝ) else 0)
    simp_rw [heach]
    have hkR : (𝒯.kScale i : ℝ) ≠ 0 := by exact_mod_cast hk.ne'
    simp only [FinProb.expect, mul_ite, mul_one, mul_zero, Finset.sum_ite_eq',
      Finset.mem_univ, if_true, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
      nsmul_eq_mul]
    rw [← mul_assoc, inv_mul_cancel₀ hkR, one_mul]
  rw [heq]
  exact H.prior_cap v p hv x

private abbrev IncAux (H : PrimitiveHistory κ 𝒯 i mesh) :=
  (H.Center → mesh.V × H.Tuple) ×
    (Group 𝒯 i → mesh.V × SearchPerm H.Device (𝒯.tScale i))

private noncomputable def incAuxLaw (H : PrimitiveHistory κ 𝒯 i mesh)
    (p : mesh.Param) : FinProb (IncAux H) :=
  (⟨(FinLaw.pi fun _c : H.Center => FinLaw.bind (PrimitiveHistory.vertexLaw p) H.tuplePrior).w,
    (FinLaw.pi fun _c : H.Center => FinLaw.bind (PrimitiveHistory.vertexLaw p) H.tuplePrior).nonneg,
    (FinLaw.pi fun _c : H.Center => FinLaw.bind (PrimitiveHistory.vertexLaw p) H.tuplePrior).sum_one⟩ : FinProb (H.Center → mesh.V × H.Tuple)).prod
  ⟨(FinLaw.pi fun _g : Group 𝒯 i => H.groupLaw p).w,
    (FinLaw.pi fun _g : Group 𝒯 i => H.groupLaw p).nonneg,
    (FinLaw.pi fun _g : Group 𝒯 i => H.groupLaw p).sum_one⟩

private def auxJoin (H : PrimitiveHistory κ 𝒯 i mesh)
    (u : IncAux H) (τ : H.Device.Ties) : HeightAux H := (u.1, (u.2,τ))

private theorem heightAux_expect (H : PrimitiveHistory κ 𝒯 i mesh)
    (p : mesh.Param) (f : HeightAux H → ℝ) :
    (heightAuxLaw H p).expect f =
      (incAuxLaw H p).expect (fun u => H.Device.tieLaw.expect (fun τ => f (auxJoin H u τ))) := by
  simp only [FinProb.expect, heightAuxLaw, incAuxLaw, FinProb.prod, FinLaw.bind,
    Fintype.sum_prod_type, HDParams.tieLaw, FinProb.pi, FinLaw.pi, PrimitiveHistory.tieLaw,
    PrimitiveHistory.finProbToFinLaw, auxJoin, Finset.mul_sum]
  congr 1
  funext CT
  congr 1
  funext G
  congr 1
  funext τ
  ring

private theorem incAux_incidence (H : PrimitiveHistory κ 𝒯 i mesh)
    (p : mesh.Param) (hk : 0 < 𝒯.kScale i) (c : H.Center) (x : Fin (T.S.N k)) :
    (incAuxLaw H p).expect (fun u => tupleIncidence H x (u.1 c).2) ≤ 2 / (𝒯.P i).M := by
  unfold incAuxLaw
  rw [prob_prod_expect]
  simp_rw [FinProb.expect_const]
  let C : FinProb (mesh.V × H.Tuple) :=
    ⟨(FinLaw.bind (PrimitiveHistory.vertexLaw p) H.tuplePrior).w,
      (FinLaw.bind (PrimitiveHistory.vertexLaw p) H.tuplePrior).nonneg,
      (FinLaw.bind (PrimitiveHistory.vertexLaw p) H.tuplePrior).sum_one⟩
  change (FinProb.pi fun _ : H.Center => C).expect
    (fun ω => tupleIncidence H x (ω c).2) ≤ _
  rw [prob_pi_coord (fun _ : H.Center => C) c (fun vw => tupleIncidence H x vw.2)]
  change (FinProb.bind
    (⟨fun v => mesh.wt v p, fun v => mesh.wt_nonneg v p, mesh.wt_sum_one p⟩ : FinProb mesh.V)
    (fun v => ⟨(H.tuplePrior v).w, (H.tuplePrior v).nonneg, (H.tuplePrior v).sum_one⟩)).expect
    (fun vw => tupleIncidence H x vw.2) ≤ _
  rw [FinProb.bind_expect _ _ (fun _ w => tupleIncidence H x w)]
  calc
    _ ≤ ∑ v, mesh.wt v p * (2 / (𝒯.P i).M) := by
      apply Finset.sum_le_sum
      intro v _
      by_cases hv : 0 < mesh.wt v p
      · apply mul_le_mul_of_nonneg_left _ (mesh.wt_nonneg v p)
        exact tuplePrior_incidence H p v hv hk x
      · have hz : mesh.wt v p = 0 := le_antisymm (le_of_not_gt hv) (mesh.wt_nonneg v p)
        simp [hz]
    _ = _ := by rw [← Finset.sum_mul, mesh.wt_sum_one]; ring

private theorem heightAux_incidence (H : PrimitiveHistory κ 𝒯 i mesh)
    (p : mesh.Param) (hk : 0 < 𝒯.kScale i) (c : H.Center) (x : Fin (T.S.N k)) :
    (heightAuxLaw H p).expect (fun u => tupleIncidence H x (u.1 c).2) ≤ 2 / (𝒯.P i).M := by
  rw [heightAux_expect]
  simp only [auxJoin]
  simp_rw [FinProb.expect_const]
  exact incAux_incidence H p hk c x

private noncomputable def incRecord (H : PrimitiveHistory κ 𝒯 i mesh)
    (P : H.Center → Bool) (u : IncAux H) (A : H.Center → Bool) (τ : H.Device.Ties) :
    ∀ r, H.Val r := (heightUnpack H).symm ((P, auxJoin H u τ), A)

private noncomputable def incEligibility (Geom : ProjectionGeometry κ 𝒯 i)
    (H : PrimitiveHistory κ 𝒯 i mesh) (mask : Masks H)
    (P : H.Center → Bool) (u : IncAux H) : H.Device.EligMap :=
  eligible Geom H mask (incRecord H P u (fun _ => false) (fun _ => 1))

private theorem incEligibility_eq (Geom : ProjectionGeometry κ 𝒯 i)
    (H : PrimitiveHistory κ 𝒯 i mesh) (mask : Masks H) (hl : MaskLookup H mask)
    (P : H.Center → Bool) (u : IncAux H) (A : H.Center → Bool) (τ : H.Device.Ties) :
    eligible Geom H mask (incRecord H P u A τ) = incEligibility Geom H mask P u := by
  apply eligible_input_congr Geom H mask hl
  · intro g; rfl
  · intro c; exact ⟨rfl, rfl⟩

private theorem incRecord_selected (Geom : ProjectionGeometry κ 𝒯 i)
    (H : PrimitiveHistory κ 𝒯 i mesh) (mask : Masks H) (hl : MaskLookup H mask)
    (P : H.Center → Bool) (u : IncAux H) (A : H.Center → Bool) (τ : H.Device.Ties)
    (v : EvenRole 𝒯 i) :
    selected Geom H mask (incRecord H P u A τ) v =
      H.Device.selection (siteSet Geom) P A (incEligibility Geom H mask P u) τ (Geom.project v.1) := by
  unfold selected
  rw [incEligibility_eq Geom H mask hl]
  rfl

private theorem intrinsic_selected_level (Geom : ProjectionGeometry κ 𝒯 i)
    (H : PrimitiveHistory κ 𝒯 i mesh) (mask : Masks H)
    (W : ∀ r, H.Val r) (v : EvenRole 𝒯 i) (c : H.Center)
    (hs : selected Geom H mask W v = some c) :
    c.2.val = H.Device.height (siteSet Geom) (H.present W) (H.active W)
      (eligible Geom H mask W) H.Device.Rlong (Geom.project v.1) := by
  classical
  unfold selected HDParams.selection HDParams.selectionAt at hs
  dsimp only [] at hs
  split_ifs at hs with hj hb hn
  let j : Fin (H.Device.H + 1) :=
    ⟨H.Device.height (siteSet Geom) (H.present W) (H.active W)
      (eligible Geom H mask W) H.Device.Rlong (Geom.project v.1), by omega⟩
  have hm := Classical.choose_spec
    (Finset.mem_image.mp (Finset.min'_mem
      (((eligible Geom H mask W (Geom.project v.1) j).filter fun ℓ => H.active W ℓ = true).image
        (fun ℓ => H.Device.priority (H.ties W) (Geom.project v.1,j) ℓ)) hn))
  have hc : c ∈ eligible Geom H mask W (Geom.project v.1) j := by
    have he : Classical.choose (Finset.mem_image.mp (Finset.min'_mem _ hn)) = c := Option.some.inj hs
    rw [he] at hm
    exact (Finset.mem_filter.mp hm.1).1
  have hball := (Finset.mem_filter.mp (Finset.mem_sdiff.mp hc).1).1
  exact congrArg Fin.val (Finset.mem_filter.mp hball).2.1

private theorem star_legal (Geom : ProjectionGeometry κ 𝒯 i)
    (H : PrimitiveHistory κ 𝒯 i mesh) (mask : Masks H)
    (v : EvenRole 𝒯 i) (W : ∀ r, H.Val r) (hv : starValid Geom H mask v W) :
    H.Device.Legal (H.present W) (eligible Geom H mask W)
      (H.Device.domBall (siteSet Geom) (Geom.project v.1) H.Device.Rlong) := by
  intro q hq j
  refine ⟨?_, ?_⟩
  · intro c hc
    obtain ⟨hb, hp⟩ := Finset.mem_filter.mp (Finset.mem_sdiff.mp hc).1
    obtain ⟨_, hj, hd⟩ := Finset.mem_filter.mp hb
    exact ⟨hp,hj,hd⟩
  · have := (hv.2.1 q hq j).2
    have hn : 0 ≤ H.Device.lam := by dsimp [PrimitiveHistory.Device,patchHD]; positivity
    linarith

private theorem inc_zero_kernel (hconst : HeightConstantContract κ)
    (scales : PatchScales 𝒯 i) (Geom : ProjectionGeometry κ 𝒯 i)
    (H : PrimitiveHistory κ 𝒯 i mesh) (mask : Masks H) (hl : MaskLookup H mask)
    (hh : HeightFacts hconst Geom H mask)
    (P : H.Center → Bool) (u : IncAux H) (v : EvenRole 𝒯 i) (c : H.Center)
    (hc : c.2.val = 0) :
    (H.Device.actLaw.prod H.Device.tieLaw).pr (fun aτ =>
      starValid Geom H mask v (incRecord H P u aτ.1 aτ.2) ∧
        selected Geom H mask (incRecord H P u aτ.1 aτ.2) v = some c) ≤ 3 / H.Device.lam := by
  classical
  let E := incEligibility Geom H mask P u
  let j0 : Fin (H.Device.H + 1) := ⟨0, by omega⟩
  have hcz : c.2 = j0 := Fin.ext hc
  have hq : Geom.project v.1 ∈ H.Device.domBall (siteSet Geom) (Geom.project v.1) H.Device.Rlong := by
    apply Finset.mem_filter.mpr
    exact ⟨Finset.mem_image.mpr ⟨v,Finset.mem_univ _,rfl⟩, by simp⟩
  by_cases hex : ∃ aτ : (H.Center → Bool) × H.Device.Ties, starValid Geom H mask v (incRecord H P u aτ.1 aτ.2) ∧
      selected Geom H mask (incRecord H P u aτ.1 aτ.2) v = some c
  · obtain ⟨aτ, hstar, hsel⟩ := hex
    have hlegal := star_legal Geom H mask v _ hstar (Geom.project v.1) hq j0
    rw [incEligibility_eq Geom H mask hl] at hlegal
    have hmem := (hh.chosen_eligible _ v c hsel).1
    rw [incEligibility_eq Geom H mask hl, hcz] at hmem
    have hlam : 0 < H.Device.lam := by
      have hn := (hconst.threshold_slack (𝒯.P i).h scales.h_large).1
      dsimp [PrimitiveHistory.Device,patchHD]
      positivity
    have ht := height_selection_tie H.Device hlam P E (siteSet Geom) (Geom.project v.1) c hlegal hmem
    apply le_trans _ ht
    unfold FinProb.pr
    apply Finset.sum_le_sum
    intro b _
    by_cases hb : starValid Geom H mask v (incRecord H P u b.1 b.2) ∧
        selected Geom H mask (incRecord H P u b.1 b.2) v = some c
    · have hheight := intrinsic_selected_level Geom H mask _ v c hb.2
      rw [hc, incEligibility_eq Geom H mask hl] at hheight
      have hs := incRecord_selected Geom H mask hl P u b.1 b.2 v
      have htarget : H.Device.height (siteSet Geom) P b.1 E H.Device.Rlong (Geom.project v.1) = 0 ∧
          H.Device.selection (siteSet Geom) P b.1 E b.2 (Geom.project v.1) = some c :=
        ⟨hheight.symm, hs.symm.trans hb.2⟩
      simp only [if_pos hb, if_pos htarget, le_refl]
    · simp only [if_neg hb]
      split_ifs <;> simp [FinProb.nonneg]
  · have hz : (H.Device.actLaw.prod H.Device.tieLaw).pr (fun aτ =>
        starValid Geom H mask v (incRecord H P u aτ.1 aτ.2) ∧
          selected Geom H mask (incRecord H P u aτ.1 aτ.2) v = some c) = 0 := by
      unfold FinProb.pr
      apply Finset.sum_eq_zero
      intro b _
      rw [if_neg (fun h => hex ⟨b,h⟩)]
    rw [hz]
    have hn : 0 ≤ H.Device.lam := by dsimp [PrimitiveHistory.Device,patchHD]; positivity
    positivity

private theorem inc_positive_fixed (hκ : κ.Admissible) (hconst : HeightConstantContract κ)
    (scales : PatchScales 𝒯 i) (Geom : ProjectionGeometry κ 𝒯 i)
    (H : PrimitiveHistory κ 𝒯 i mesh) (mask : Masks H) (hl : MaskLookup H mask)
    (u : IncAux H) (τ : H.Device.Ties) (v : EvenRole 𝒯 i) (forced : Option H.Center) :
    ((H.Device.posLawForced forced).prod H.Device.actLaw).pr (fun PA =>
      H.Device.Legal PA.1 (incEligibility Geom H mask PA.1 u)
        (H.Device.domBall (siteSet Geom) (Geom.project v.1) H.Device.Rlong) ∧
      0 < H.Device.height (siteSet Geom) PA.1 PA.2 (incEligibility Geom H mask PA.1 u)
        H.Device.Rlong (Geom.project v.1)) ≤
      Real.exp (-Real.rpow ((𝒯.P i).h : ℝ) hconst.positiveExponent) := by
  classical
  let aux := auxJoin H u τ
  let π : FinProb (HeightAux H) := FinProb.uniform {aux} (Finset.singleton_nonempty _)
  have ht := patch_positive_height_bound hκ hconst scales Geom H mask hl π v forced
  rw [prob_pr_indicator, prob_three_nested] at ht
  simp only [π, prob_delta_expect] at ht
  have hp (P A : H.Center → Bool) :
      H.present ((heightUnpack H).symm ((P,aux),A)) = P := rfl
  have ha (P A : H.Center → Bool) :
      H.active ((heightUnpack H).symm ((P,aux),A)) = A := rfl
  have he (P A : H.Center → Bool) :
      eligible Geom H mask ((heightUnpack H).symm ((P,aux),A)) =
        incEligibility Geom H mask P u := incEligibility_eq Geom H mask hl P u A τ
  simp_rw [hp,ha,he] at ht
  rw [prob_pr_indicator, prob_prod_nested]
  convert ht using 1
  apply congrArg (H.Device.posLawForced forced).expect
  funext P
  apply congrArg H.Device.actLaw.expect
  funext A
  split_ifs <;> rfl

private theorem pos_present_weight (hconst : HeightConstantContract κ)
    (scales : PatchScales 𝒯 i) (H : PrimitiveHistory κ 𝒯 i mesh)
    (c : H.Center) (P : H.Center → Bool) :
    (if P c = true then H.Device.posLaw.w P else 0) =
      (H.Device.lam / H.Device.V) * (H.Device.posLawForced (some c)).w P := by
  classical
  let q := H.Device.lam / (H.Device.V : ℝ)
  have hn := hconst.threshold_slack (𝒯.P i).h scales.h_large
  have hq0 : 0 ≤ q := by dsimp [q, PrimitiveHistory.Device,patchHD]; positivity
  have hprob : H.Device.lam ≤ (H.Device.V : ℝ) / 2 := hn.2.2.1
  have hq1 : q ≤ 1 := by
    have hV : 0 < (H.Device.V : ℝ) := by
      have hlam : 0 < H.Device.lam := by
        have hlarge := hn.1
        dsimp [PrimitiveHistory.Device,patchHD]
        positivity
      linarith [hprob]
    apply (div_le_one hV).mpr
    linarith [hprob]
  change (if P c = true then ∏ z, (FinProb.bernoulli q).w (P z) else 0) =
    q * ∏ z, (if some c = some z then FinProb.bernoulli 1 else FinProb.bernoulli q).w (P z)
  rw [← Finset.mul_prod_erase Finset.univ (fun z =>
    (if some c = some z then FinProb.bernoulli 1 else FinProb.bernoulli q).w (P z)) (Finset.mem_univ c)]
  have hrest : (∏ z ∈ Finset.univ.erase c,
      (if some c = some z then FinProb.bernoulli 1 else FinProb.bernoulli q).w (P z)) =
      ∏ z ∈ Finset.univ.erase c, (FinProb.bernoulli q).w (P z) := by
    apply Finset.prod_congr rfl
    intro z hz
    have hzc := (Finset.mem_erase.mp hz).1
    simp [Ne.symm hzc]
  rw [hrest]
  by_cases hc : P c = true
  · rw [if_pos hc, ← Finset.mul_prod_erase Finset.univ (fun z => (FinProb.bernoulli q).w (P z)) (Finset.mem_univ c)]
    simp [FinProb.bernoulli, hc, min_eq_left hq1, max_eq_right hq0]
  · have hf : P c = false := Bool.eq_false_iff.mpr hc
    simp [hf, FinProb.bernoulli]

private theorem inc_positive_kernel (hκ : κ.Admissible) (hconst : HeightConstantContract κ)
    (scales : PatchScales 𝒯 i) (Geom : ProjectionGeometry κ 𝒯 i)
    (H : PrimitiveHistory κ 𝒯 i mesh) (mask : Masks H) (hl : MaskLookup H mask)
    (u : IncAux H) (v : EvenRole 𝒯 i) (c : H.Center) (hc : 0 < c.2.val) :
    ((H.Device.posLawForced (some c)).prod (H.Device.actLaw.prod H.Device.tieLaw)).pr (fun ω =>
      starValid Geom H mask v (incRecord H ω.1 u ω.2.1 ω.2.2) ∧
        selected Geom H mask (incRecord H ω.1 u ω.2.1 ω.2.2) v = some c) ≤
      Real.exp (-Real.rpow ((𝒯.P i).h : ℝ) hconst.positiveExponent) := by
  classical
  let F := fun PA : (H.Center → Bool) × (H.Center → Bool) =>
    H.Device.Legal PA.1 (incEligibility Geom H mask PA.1 u)
      (H.Device.domBall (siteSet Geom) (Geom.project v.1) H.Device.Rlong) ∧
      0 < H.Device.height (siteSet Geom) PA.1 PA.2 (incEligibility Geom H mask PA.1 u)
        H.Device.Rlong (Geom.project v.1)
  have ht := inc_positive_fixed hκ hconst scales Geom H mask hl u (fun _ => 1) v (some c)
  have hle : ((H.Device.posLawForced (some c)).prod (H.Device.actLaw.prod H.Device.tieLaw)).pr (fun ω =>
      starValid Geom H mask v (incRecord H ω.1 u ω.2.1 ω.2.2) ∧
        selected Geom H mask (incRecord H ω.1 u ω.2.1 ω.2.2) v = some c) ≤
      ((H.Device.posLawForced (some c)).prod (H.Device.actLaw.prod H.Device.tieLaw)).pr
        (fun ω => F (ω.1, ω.2.1)) := by
    unfold FinProb.pr
    apply Finset.sum_le_sum
    intro ω _
    by_cases he : starValid Geom H mask v (incRecord H ω.1 u ω.2.1 ω.2.2) ∧
        selected Geom H mask (incRecord H ω.1 u ω.2.1 ω.2.2) v = some c
    · have hg := star_legal Geom H mask v _ he.1
      have hh := intrinsic_selected_level Geom H mask _ v c he.2
      rw [incEligibility_eq Geom H mask hl] at hg hh
      change c.2.val = H.Device.height (siteSet Geom) ω.1 ω.2.1
        (incEligibility Geom H mask ω.1 u) H.Device.Rlong (Geom.project v.1) at hh
      have hf : F (ω.1,ω.2.1) := ⟨hg, by dsimp [F]; rw [← hh]; exact hc⟩
      simp [he,hf]
    · simp only [if_neg he]
      split_ifs <;> simp [FinProb.nonneg]
  apply hle.trans
  have heq : ((H.Device.posLawForced (some c)).prod (H.Device.actLaw.prod H.Device.tieLaw)).pr
      (fun ω => F (ω.1, ω.2.1)) =
      ((H.Device.posLawForced (some c)).prod H.Device.actLaw).pr F := by
    simp only [FinProb.pr, FinProb.prod, Fintype.sum_prod_type]
    congr 1
    funext P
    congr 1
    funext A
    by_cases hf : F (P,A)
    · simp only [if_pos hf, ← mul_assoc, ← Finset.mul_sum, H.Device.tieLaw.sum_eq_one, mul_one]
    · simp only [if_neg hf, Finset.sum_const_zero]
  rw [heq]
  exact ht

private theorem inc_center_kernel (hκ : κ.Admissible) (hconst : HeightConstantContract κ)
    (scales : PatchScales 𝒯 i) (Geom : ProjectionGeometry κ 𝒯 i)
    (H : PrimitiveHistory κ 𝒯 i mesh) (mask : Masks H) (hl : MaskLookup H mask)
    (hh : HeightFacts hconst Geom H mask)
    (u : IncAux H) (v : EvenRole 𝒯 i) (c : H.Center) :
    (H.Device.posLaw.prod (H.Device.actLaw.prod H.Device.tieLaw)).pr (fun ω =>
      starValid Geom H mask v (incRecord H ω.1 u ω.2.1 ω.2.2) ∧
        selected Geom H mask (incRecord H ω.1 u ω.2.1 ω.2.2) v = some c) ≤
      (H.Device.lam / H.Device.V) *
        (if c.2.val = 0 then 3 / H.Device.lam else
          Real.exp (-Real.rpow ((𝒯.P i).h : ℝ) hconst.positiveExponent)) := by
  classical
  let F := fun (P : H.Center → Bool) (aτ : (H.Center → Bool) × H.Device.Ties) => starValid Geom H mask v (incRecord H P u aτ.1 aτ.2) ∧
    selected Geom H mask (incRecord H P u aτ.1 aτ.2) v = some c
  have hp (P : H.Center → Bool) (aτ : (H.Center → Bool) × H.Device.Ties) (he : F P aτ) : P c = true := by
    have hm := (hh.chosen_eligible _ v c he.2).1
    exact (Finset.mem_filter.mp (Finset.mem_sdiff.mp hm).1).2
  have hnn : 0 ≤ H.Device.lam / (H.Device.V : ℝ) := by
    dsimp [PrimitiveHistory.Device,patchHD]; positivity
  by_cases hc : c.2.val = 0
  · rw [if_pos hc]
    unfold FinProb.pr
    simp only [FinProb.prod, Fintype.sum_prod_type]
    calc
      _ = ∑ P, H.Device.posLaw.w P *
          (H.Device.actLaw.prod H.Device.tieLaw).pr (F P) := by
        simp only [FinProb.pr, FinProb.prod, Fintype.sum_prod_type, Finset.mul_sum]
        congr 1
        funext P
        congr 1
        funext A
        congr 1
        funext τ
        split_ifs <;> ring
      _ ≤ ∑ P, (if P c = true then H.Device.posLaw.w P else 0) * (3 / H.Device.lam) := by
        apply Finset.sum_le_sum
        intro P _
        by_cases hpc : P c = true
        · rw [if_pos hpc]
          exact mul_le_mul_of_nonneg_left
            (inc_zero_kernel hconst scales Geom H mask hl hh P u v c hc) (H.Device.posLaw.nonneg P)
        · have hz : (H.Device.actLaw.prod H.Device.tieLaw).pr (F P) = 0 := by
            unfold FinProb.pr
            apply Finset.sum_eq_zero
            intro b _
            rw [if_neg (fun h => hpc (hp P b h))]
          simp [hz,hpc]
      _ = _ := by
        simp_rw [pos_present_weight hconst scales H c]
        rw [← Finset.sum_mul, ← Finset.mul_sum, (H.Device.posLawForced (some c)).sum_eq_one]
        ring
  · rw [if_neg hc]
    have hpos : 0 < c.2.val := by omega
    have ht := inc_positive_kernel hκ hconst scales Geom H mask hl u v c hpos
    have heq : (H.Device.posLaw.prod (H.Device.actLaw.prod H.Device.tieLaw)).pr
        (fun ω => F ω.1 ω.2) = (H.Device.lam / H.Device.V) *
      ((H.Device.posLawForced (some c)).prod (H.Device.actLaw.prod H.Device.tieLaw)).pr
        (fun ω => F ω.1 ω.2) := by
      simp only [FinProb.pr, FinProb.prod, Fintype.sum_prod_type, Finset.mul_sum]
      congr 1
      funext P
      congr 1
      funext A
      congr 1
      funext τ
      by_cases hf : F P (A,τ)
      · rw [if_pos hf, if_pos hf]
        have hw := pos_present_weight hconst scales H c P
        rw [if_pos (hp P (A,τ) hf)] at hw
        rw [hw]
        ring
      · simp [hf]
    rw [heq]
    exact mul_le_mul_of_nonneg_left ht hnn

private theorem recLaw_incidence_integral (H : PrimitiveHistory κ 𝒯 i mesh)
    (p : mesh.Param) (f : (∀ r, H.Val r) → ℝ) :
    (H.recLaw p).E f =
      (incAuxLaw H p).expect (fun u =>
        (H.Device.posLaw.prod (H.Device.actLaw.prod H.Device.tieLaw)).expect
          (fun ω => f (incRecord H ω.1 u ω.2.1 ω.2.2))) := by
  rw [recLaw_E_heightUnpack, prob_three_nested]
  rw [prob_swap_expect]
  rw [heightAux_expect]
  simp_rw [prob_prod_nested]
  apply congrArg (incAuxLaw H p).expect
  funext u
  rw [prob_swap_expect]
  apply congrArg H.Device.posLaw.expect
  funext P
  rw [prob_swap_expect]
  rfl

private theorem inc_center_bound (hκ : κ.Admissible) (hconst : HeightConstantContract κ)
    (scales : PatchScales 𝒯 i) (Geom : ProjectionGeometry κ 𝒯 i)
    (H : PrimitiveHistory κ 𝒯 i mesh) (mask : Masks H) (hl : MaskLookup H mask)
    (hh : HeightFacts hconst Geom H mask)
    (p : mesh.Param) (hk : 0 < 𝒯.kScale i) (v : EvenRole 𝒯 i) (c : H.Center)
    (x : Fin (T.S.N k)) :
    (H.recLaw p).E (fun W => if starValid Geom H mask v W ∧
        selected Geom H mask W v = some c then tupleIncidence H x (H.tuple W c) else 0) ≤
      (H.Device.lam / H.Device.V) *
        (if c.2.val = 0 then 3 / H.Device.lam else
          Real.exp (-Real.rpow ((𝒯.P i).h : ℝ) hconst.positiveExponent)) * (2 / (𝒯.P i).M) := by
  classical
  let C := (H.Device.lam / H.Device.V) *
    (if c.2.val = 0 then 3 / H.Device.lam else
      Real.exp (-Real.rpow ((𝒯.P i).h : ℝ) hconst.positiveExponent))
  have hC : 0 ≤ C := by dsimp [C,PrimitiveHistory.Device,patchHD]; split_ifs <;> positivity
  rw [recLaw_incidence_integral]
  have heq (u : IncAux H) :
      (H.Device.posLaw.prod (H.Device.actLaw.prod H.Device.tieLaw)).expect (fun ω =>
        if starValid Geom H mask v (incRecord H ω.1 u ω.2.1 ω.2.2) ∧
            selected Geom H mask (incRecord H ω.1 u ω.2.1 ω.2.2) v = some c
          then tupleIncidence H x (H.tuple (incRecord H ω.1 u ω.2.1 ω.2.2) c) else 0) =
      tupleIncidence H x (u.1 c).2 *
        (H.Device.posLaw.prod (H.Device.actLaw.prod H.Device.tieLaw)).pr (fun ω =>
          starValid Geom H mask v (incRecord H ω.1 u ω.2.1 ω.2.2) ∧
            selected Geom H mask (incRecord H ω.1 u ω.2.1 ω.2.2) v = some c) := by
    simp only [FinProb.expect, FinProb.pr, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro ω _
    have htuple : H.tuple (incRecord H ω.1 u ω.2.1 ω.2.2) c = (u.1 c).2 := rfl
    rw [htuple]
    split_ifs <;> ring
  simp_rw [heq]
  calc
    _ ≤ (incAuxLaw H p).expect (fun u => C * tupleIncidence H x (u.1 c).2) := by
      apply FinProb.expect_mono
      intro u
      rw [mul_comm C]
      exact mul_le_mul_of_nonneg_left
        (inc_center_kernel hκ hconst scales Geom H mask hl hh u v c)
        (tupleIncidence_nonneg H x _)
    _ = C * (incAuxLaw H p).expect (fun u => tupleIncidence H x (u.1 c).2) :=
      FinProb.expect_smul _ _ _
    _ ≤ C * (2 / (𝒯.P i).M) :=
      mul_le_mul_of_nonneg_left (incAux_incidence H p hk c x) hC

private def diffSet {d : ℕ} (v u : CubePos d) : Finset (Fin d) :=
  Finset.univ.filter (fun i => u i ≠ v i)

private def vertexOfDiff {d : ℕ} (v : CubePos d) (s : Finset (Fin d)) : CubePos d :=
  fun i => if i ∈ s then !(v i) else v i

private def diffEquiv {d : ℕ} (v : CubePos d) : CubePos d ≃ Finset (Fin d) where
  toFun := diffSet v
  invFun := vertexOfDiff v
  left_inv := by
    intro u
    funext i
    by_cases hi : u i = v i
    · simp [vertexOfDiff, diffSet, hi]
    · have hmem : i ∈ diffSet v u := by simp [diffSet, hi]
      have hbool : v i = !(u i) := by
        cases hu : u i <;> cases hv : v i <;> simp_all
      simp [vertexOfDiff, hmem, hbool]
  right_inv := by
    intro s
    ext i
    by_cases hi : i ∈ s
    · simp [diffSet, vertexOfDiff, hi]
    · simp [diffSet, vertexOfDiff, hi]

private theorem diffSet_card {d : ℕ} (v u : CubePos d) :
    (diffSet v u).card = hammingDist u v := by
  simp [diffSet, hammingDist, ne_comm]

private def ballToSubsets {d r : ℕ} (v : CubePos d) :
    {u : CubePos d // hammingDist u v ≤ r} ≃ {s : Finset (Fin d) // s.card ≤ r} where
  toFun u := ⟨diffSet v u.1, by rw [diffSet_card]; exact u.2⟩
  invFun s := ⟨vertexOfDiff v s.1, by
    rw [← diffSet_card]
    simp [diffSet, vertexOfDiff]
    exact s.2⟩
  left_inv := by
    intro u
    apply Subtype.ext
    exact (diffEquiv v).left_inv u.1
  right_inv := by
    intro s
    apply Subtype.ext
    exact (diffEquiv v).right_inv s.1

private def smallSubsetFiberEquiv (d r : ℕ) (i : Fin (r + 1)) :
    {s : {s : Finset (Fin d) // s.card ≤ r} // (⟨s.1.card, by omega⟩ : Fin (r + 1)) = i} ≃
      {s : Finset (Fin d) // s.card = i.val} where
  toFun s := ⟨s.1.1, by
    have h := congrArg Fin.val s.2
    simpa using h⟩
  invFun s := ⟨⟨s.1, by rw [s.2]; omega⟩, by
    apply Fin.ext
    exact s.2⟩
  left_inv := by
    intro s
    apply Subtype.ext
    apply Subtype.ext
    rfl
  right_inv := by
    intro s
    apply Subtype.ext
    rfl

private def subsetsSmallEquiv (d r : ℕ) :
    {s : Finset (Fin d) // s.card ≤ r} ≃
      Σ i : Fin (r + 1), {s : Finset (Fin d) // s.card = i.val} := by
  let f : {s : Finset (Fin d) // s.card ≤ r} → Fin (r + 1) :=
    fun s => ⟨s.1.card, by omega⟩
  exact (Equiv.sigmaFiberEquiv f).symm.trans
    (Equiv.sigmaCongrRight (smallSubsetFiberEquiv d r))

private theorem card_small_subsets (d r : ℕ) :
    Fintype.card {s : Finset (Fin d) // s.card ≤ r} =
      ∑ i ∈ Finset.range (r + 1), Nat.choose d i := by
  classical
  rw [Fintype.card_congr (subsetsSmallEquiv d r), Fintype.card_sigma]
  have hfiber (i : Fin (r + 1)) :
      Fintype.card {s : Finset (Fin d) // s.card = i.val} = Nat.choose d i.val := by
    let S : Finset (Finset (Fin d)) := Finset.univ.powersetCard i.val
    let e : {s : Finset (Fin d) // s.card = i.val} ≃ S :=
      { toFun := fun s => ⟨s.1, by
          rw [Finset.mem_powersetCard]
          exact ⟨Finset.subset_univ _, s.2⟩⟩
        invFun := fun s => ⟨s.1, (Finset.mem_powersetCard.mp s.2).2⟩
        left_inv := by intro s; apply Subtype.ext; rfl
        right_inv := by intro s; apply Subtype.ext; rfl }
    calc
      Fintype.card {s : Finset (Fin d) // s.card = i.val} = Fintype.card S := Fintype.card_congr e
      _ = S.card := Fintype.card_coe S
      _ = Nat.choose d i.val := by simp [S, Finset.card_powersetCard]
  simp_rw [hfiber]
  rw [← Fin.sum_univ_eq_sum_range]

private theorem hammingBall_card (d r : ℕ) (v : CubePos d) :
    (Finset.univ.filter (fun u : CubePos d => hammingDist u v ≤ r)).card =
      ∑ i ∈ Finset.range (r + 1), Nat.choose d i := by
  classical
  have hcard : Fintype.card {u : CubePos d // hammingDist u v ≤ r} =
      (Finset.univ.filter (fun u : CubePos d => hammingDist u v ≤ r)).card := by
    simpa using (Fintype.card_subtype (fun u : CubePos d => hammingDist u v ≤ r))
  exact hcard.symm.trans ((Fintype.card_congr (ballToSubsets v)).trans (card_small_subsets d r))

private def levelBallEquiv (d H r : ℕ) (j : Fin (H + 1)) (v : CubePos d) :
    {u : CubePos d // hammingDist u v ≤ r} ≃
      {ℓ : CubePos d × Fin (H + 1) // ℓ.2 = j ∧ hammingDist ℓ.1 v ≤ r} where
  toFun u := ⟨(u.1, j), by simp [u.2]⟩
  invFun ℓ := ⟨ℓ.1.1, ℓ.2.2⟩
  left_inv := by intro u; apply Subtype.ext; rfl
  right_inv := by
    intro ℓ
    rcases ℓ with ⟨⟨u, k⟩, ⟨hk, hdist⟩⟩
    apply Subtype.ext
    exact Prod.ext rfl hk.symm

private theorem levelBall_card (d H r : ℕ) (j : Fin (H + 1)) (v : CubePos d) :
    (Finset.univ.filter (fun ℓ : CubePos d × Fin (H + 1) =>
      ℓ.2 = j ∧ hammingDist ℓ.1 v ≤ r)).card =
      ∑ i ∈ Finset.range (r + 1), Nat.choose d i := by
  classical
  calc
    (Finset.univ.filter (fun ℓ : CubePos d × Fin (H + 1) =>
      ℓ.2 = j ∧ hammingDist ℓ.1 v ≤ r)).card =
        Fintype.card {ℓ : CubePos d × Fin (H + 1) // ℓ.2 = j ∧ hammingDist ℓ.1 v ≤ r} := by
          symm
          exact Fintype.card_subtype _
    _ = Fintype.card {u : CubePos d // hammingDist u v ≤ r} :=
          Fintype.card_congr (levelBallEquiv d H r j v).symm
    _ = (Finset.univ.filter (fun u : CubePos d => hammingDist u v ≤ r)).card :=
          Fintype.card_subtype _
    _ = _ := hammingBall_card d r v

/-- P14.1j height subnode: level-zero active ties and the position-averaged
forced-present positive-height bound. No global success is conditioned on. -/
theorem forced_present_incidence (κ : CConsts) (hκ : κ.Admissible)
    (hconst : HeightConstantContract κ)
    {T : Stage} {k : ℕ} {𝒯 : Tiling κ T k} (h𝒯 : Tiling.Valid 𝒯)
    (hcluster : 𝒯.mode.isCluster) {i : Fin 𝒯.m} {mesh : Mesh 𝒯}
    (scales : PatchScales 𝒯 i) (Geom : ProjectionGeometry κ 𝒯 i)
    (H : PrimitiveHistory κ 𝒯 i mesh) (mask : Masks H) (hlookup : MaskLookup H mask)
    (hh : HeightFacts hconst Geom H mask) : SelectionIncidence Geom H mask := by
  classical
  intro p v x
  let q := Geom.project v.1
  let B : Finset H.Center := Finset.univ.filter fun c => hammingDist c.1 q ≤ H.Device.r
  let e := Real.exp (-Real.rpow ((𝒯.P i).h : ℝ) hconst.positiveExponent)
  have hn := hconst.threshold_slack (𝒯.P i).h scales.h_large
  have hk : 0 < 𝒯.kScale i := hn.2.1
  have hlam : 0 < H.Device.lam := by
    have hlarge := hn.1
    dsimp [PrimitiveHistory.Device,patchHD]
    positivity
  have hV : 0 < (H.Device.V : ℝ) := by
    have hv : H.Device.lam ≤ (H.Device.V : ℝ) / 2 := hn.2.2.1
    linarith
  have hM : 0 < ((𝒯.P i).M : ℝ) := by exact_mod_cast scales.M_pos
  have hbudget : (H.Device.H + 1 : ℕ) * H.Device.lam * e ≤ 1 := by
    simpa only [PrimitiveHistory.Device,patchHD,e,Nat.cast_add,Nat.cast_one] using hn.2.2.2.2.2.2.2.2.2.2.1
  have hB : B.card = H.Device.V * (H.Device.H + 1) := by
    dsimp [B]
    rw [Finset.card_filter, Fintype.sum_prod_type]
    have hsum (z : CubePos H.Device.d) :
        (∑ j : Fin (H.Device.H + 1), if hammingDist z q ≤ H.Device.r then 1 else 0) =
          (if hammingDist z q ≤ H.Device.r then 1 else 0) * (H.Device.H + 1) := by
      simp
    simp_rw [hsum]
    rw [← Finset.sum_mul, ← Finset.card_filter, hammingBall_card]
    rfl
  have hB0 : (B.filter fun c => c.2.val = 0).card = H.Device.V := by
    let j0 : Fin (H.Device.H + 1) := ⟨0, by omega⟩
    have heq : B.filter (fun c => c.2.val = 0) =
        Finset.univ.filter (fun c : H.Center => c.2 = j0 ∧ hammingDist c.1 q ≤ H.Device.r) := by
      ext c
      simp only [B, Finset.mem_filter, Finset.mem_univ, true_and]
      have hj : c.2.val = 0 ↔ c.2 = j0 := ⟨fun h => Fin.ext h, fun h => congrArg Fin.val h⟩
      rw [hj, and_comm]
    rw [heq, levelBall_card]
    rfl
  have hpoint (W : ∀ r, H.Val r) :
      (if starValid Geom H mask v W then
        match selected Geom H mask W v with
        | none => 0
        | some c => tupleIncidence H x (H.tuple W c)
      else 0) =
      ∑ c ∈ B, if starValid Geom H mask v W ∧ selected Geom H mask W v = some c
        then tupleIncidence H x (H.tuple W c) else 0 := by
    by_cases hs : starValid Geom H mask v W
    · obtain ⟨c,hc⟩ := hs.2.2
      have hm := (hh.chosen_eligible W v c hc).1
      have hb := (Finset.mem_filter.mp (Finset.mem_sdiff.mp hm).1).1
      have hd := (Finset.mem_filter.mp hb).2.2
      have hmem : c ∈ B := Finset.mem_filter.mpr ⟨Finset.mem_univ _,hd⟩
      simp [hs,hc,Option.some.injEq,eq_comm,hmem]
    · simp [hs]
  change (H.recLaw p).E (fun W => if starValid Geom H mask v W then
    match selected Geom H mask W v with
    | none => 0
    | some c => tupleIncidence H x (H.tuple W c)
    else 0) ≤ _
  simp_rw [hpoint]
  have heq : (H.recLaw p).E (fun W => ∑ c ∈ B,
      if starValid Geom H mask v W ∧ selected Geom H mask W v = some c
        then tupleIncidence H x (H.tuple W c) else 0) =
      ∑ c ∈ B, (H.recLaw p).E (fun W =>
        if starValid Geom H mask v W ∧ selected Geom H mask W v = some c
          then tupleIncidence H x (H.tuple W c) else 0) := by
    unfold FinLaw.E
    simp only [Finset.mul_sum]
    exact Finset.sum_comm
  rw [heq]
  calc
    _ ≤ ∑ c ∈ B, (H.Device.lam / H.Device.V) *
        (if c.2.val = 0 then 3 / H.Device.lam else e) * (2 / (𝒯.P i).M) := by
      apply Finset.sum_le_sum
      intro c _
      exact inc_center_bound hκ hconst scales Geom H mask hlookup hh p hk v c x
    _ ≤ ∑ c ∈ B, (H.Device.lam / H.Device.V) *
        ((if c.2.val = 0 then 3 / H.Device.lam else 0) + e) * (2 / (𝒯.P i).M) := by
      apply Finset.sum_le_sum
      intro c _
      apply mul_le_mul_of_nonneg_right _ (by positivity)
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      split_ifs <;> linarith [Real.exp_pos (-Real.rpow ((𝒯.P i).h : ℝ) hconst.positiveExponent)]
    _ = (H.Device.lam / H.Device.V) *
        ((H.Device.V : ℝ) * (3 / H.Device.lam) +
          ((H.Device.V : ℝ) * (H.Device.H + 1)) * e) * (2 / (𝒯.P i).M) := by
      rw [← Finset.sum_mul, ← Finset.mul_sum, Finset.sum_add_distrib]
      rw [← Finset.sum_filter]
      simp only [Finset.sum_const, nsmul_eq_mul, hB0, hB, Nat.cast_mul, Nat.cast_add, Nat.cast_one]
    _ = 6 / (𝒯.P i).M + (2 / (𝒯.P i).M) * ((H.Device.H + 1 : ℕ) * H.Device.lam * e) := by
      push_cast
      field_simp [hlam.ne',hV.ne',hM.ne']
      <;> ring
    _ ≤ 6 / (𝒯.P i).M + (2 / (𝒯.P i).M) * 1 := by
      exact add_le_add le_rfl (mul_le_mul_of_nonneg_left hbudget
        (show 0 ≤ 2 / ((𝒯.P i).M : ℝ) by positivity))
    _ ≤ 16 / (𝒯.P i).M := by
      field_simp [hM.ne']
      <;> nlinarith

end IncidenceProof

section EligibilityRefreshProof

set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000

variable {κ : CConsts} {T : Stage} {k : ℕ} {𝒯 : Tiling κ T k}
  {i : Fin 𝒯.m} {mesh : Mesh 𝒯}

private noncomputable def ctLaw (H : PrimitiveHistory κ 𝒯 i mesh)
    (p : mesh.Param) : FinProb (H.Center → mesh.V × H.Tuple) :=
  FinProb.pi fun _ => FinProb.bind
    ⟨fun v => mesh.wt v p, fun v => mesh.wt_nonneg v p, mesh.wt_sum_one p⟩
    (fun v => ⟨(H.tuplePrior v).w,(H.tuplePrior v).nonneg,(H.tuplePrior v).sum_one⟩)

private noncomputable def cornerLaw (H : PrimitiveHistory κ 𝒯 i mesh)
    (p : mesh.Param) : FinProb (H.Center → mesh.V) :=
  FinProb.pi fun _ => ⟨fun v => mesh.wt v p, fun v => mesh.wt_nonneg v p, mesh.wt_sum_one p⟩

private noncomputable def tuplesAt (H : PrimitiveHistory κ 𝒯 i mesh)
    (v : H.Center → mesh.V) : FinProb (H.Center → H.Tuple) :=
  FinProb.pi fun c => ⟨(H.tuplePrior (v c)).w,(H.tuplePrior (v c)).nonneg,(H.tuplePrior (v c)).sum_one⟩

private def ctFactor (H : PrimitiveHistory κ 𝒯 i mesh) :
    (H.Center → mesh.V × H.Tuple) ≃ (H.Center → mesh.V) × (H.Center → H.Tuple) where
  toFun CT := (fun c => (CT c).1,fun c => (CT c).2)
  invFun vw c := (vw.1 c,vw.2 c)
  left_inv _ := rfl
  right_inv _ := rfl

private theorem ctFactor_expect (H : PrimitiveHistory κ 𝒯 i mesh)
    (p : mesh.Param) (f : (H.Center → mesh.V × H.Tuple) → ℝ) :
    (ctLaw H p).expect f = (cornerLaw H p).expect (fun v =>
      (tuplesAt H v).expect (fun w => f (fun c => (v c,w c)))) := by
  unfold FinProb.expect
  simp only [Finset.mul_sum]
  rw [← Fintype.sum_prod_type']
  apply Fintype.sum_equiv (ctFactor H)
  intro CT
  dsimp only [ctLaw,cornerLaw,tuplesAt,FinProb.pi,FinProb.bind,ctFactor]
  rw [Finset.prod_mul_distrib]
  exact mul_assoc _ _ _

private theorem ct_refresh (H : PrimitiveHistory κ 𝒯 i mesh)
    (p : mesh.Param) (f : (H.Center → mesh.V × H.Tuple) → ℝ) :
    (ctLaw H p).expect f = (ctLaw H p).expect (fun CT =>
      (tuplesAt H (fun c => (CT c).1)).expect (fun w => f (fun c => ((CT c).1,w c)))) := by
  rw [ctFactor_expect,ctFactor_expect]
  change (cornerLaw H p).expect (fun v =>
    (tuplesAt H v).expect (fun w => f (fun c => (v c,w c)))) =
      (cornerLaw H p).expect (fun v => (tuplesAt H v).expect (fun _ =>
        (tuplesAt H v).expect (fun w => f (fun c => (v c,w c)))))
  simp_rw [FinProb.expect_const]

private theorem recLaw_refresh_tuples (H : PrimitiveHistory κ 𝒯 i mesh)
    (p : mesh.Param) (f : (∀ r, H.Val r) → ℝ) :
    (H.recLaw p).E f = (H.recLaw p).E (fun W =>
      (conditionedTuples H W).expect (fun w => f (replaceAllTuples H W w))) := by
  rw [recLaw_incidence_integral,recLaw_incidence_integral]
  let G : FinProb (Group 𝒯 i → mesh.V × SearchPerm H.Device (𝒯.tScale i)) :=
    ⟨(FinLaw.pi fun _g : Group 𝒯 i => H.groupLaw p).w,
      (FinLaw.pi fun _g : Group 𝒯 i => H.groupLaw p).nonneg,
      (FinLaw.pi fun _g : Group 𝒯 i => H.groupLaw p).sum_one⟩
  let PAτ := H.Device.posLaw.prod (H.Device.actLaw.prod H.Device.tieLaw)
  change ((ctLaw H p).prod G).expect (fun u => PAτ.expect
      (fun ω => f (incRecord H ω.1 u ω.2.1 ω.2.2))) =
    ((ctLaw H p).prod G).expect (fun u => PAτ.expect (fun ω =>
      (conditionedTuples H (incRecord H ω.1 u ω.2.1 ω.2.2)).expect (fun w =>
        f (replaceAllTuples H (incRecord H ω.1 u ω.2.1 ω.2.2) w))))
  rw [prob_prod_nested,prob_prod_nested]
  rw [ct_refresh H p (fun CT => G.expect (fun g => PAτ.expect
    (fun ω => f (incRecord H ω.1 (CT,g) ω.2.1 ω.2.2))))]
  apply congrArg (ctLaw H p).expect
  funext CT
  rw [prob_swap_expect]
  apply congrArg G.expect
  funext g
  rw [prob_swap_expect]
  apply congrArg PAτ.expect
  funext ω
  have hlaw : conditionedTuples H (incRecord H ω.1 (CT,g) ω.2.1 ω.2.2) =
      tuplesAt H (fun c => (CT c).1) := rfl
  rw [hlaw]
  apply congrArg (tuplesAt H (fun c => (CT c).1)).expect
  funext w
  have he : replaceAllTuples H (incRecord H ω.1 (CT,g) ω.2.1 ω.2.2) w =
      incRecord H ω.1 ((fun c => ((CT c).1,w c)),g) ω.2.1 ω.2.2 := rfl
  rw [he]

/-- P14.1d: disjoint tests refer to distinct center coordinates of the product
law. Their models are conditioned on positions, masks and corner draws; tuple
values remain random. The eligibility function is the greedy marking rule. -/
theorem eligibility_from_tests (κ : CConsts) (hκ : κ.Admissible)
    (hconst : HeightConstantContract κ)
    {T : Stage} {k : ℕ} {𝒯 : Tiling κ T k} (h𝒯 : Tiling.Valid 𝒯)
    (hcluster : 𝒯.mode.isCluster) {i : Fin 𝒯.m} {mesh : Mesh 𝒯}
    (scales : PatchScales 𝒯 i) (Geom : ProjectionGeometry κ 𝒯 i)
    (H : PrimitiveHistory κ 𝒯 i mesh) (mask : Masks H) (hlookup : MaskLookup H mask)
    (L : ListFamily Geom H mask) (hcounts : PositionCountConcentration hconst H)
    (htests : GenericListBound κ 𝒯 i) : EligibilityFacts hconst Geom H mask := by
  refine ⟨?_, ?_⟩
  · intro W v j c hc
    have hleft := (Finset.mem_sdiff.mp hc).1
    rcases Finset.mem_filter.mp hleft with ⟨hball, hpresent⟩
    exact ⟨hball, hpresent⟩
  · classical
    intro p
    let err := Real.exp (-Real.rpow ((𝒯.P i).h : ℝ) (1 + hconst.sliceExponent))
    let F := fun W => PositionCountGate H W ∧
      ∃ g, (𝒯.P i).h ≤ (failedFamily Geom H mask g W).card
    have hF : (H.recLaw p).pr F ≤ err := by
      have hid : (H.recLaw p).pr F = (H.recLaw p).E (fun W => eligibility_indicator (F W)) := by
        unfold FinLaw.pr FinLaw.E eligibility_indicator
        apply Finset.sum_congr rfl
        intro W _
        by_cases hf : F W
        · simp only [if_pos hf,mul_one]
        · simp only [if_neg hf,mul_zero]
      rw [hid,recLaw_refresh_tuples]
      calc
        _ ≤ (H.recLaw p).E (fun _ => err) := by
          unfold FinLaw.E
          apply Finset.sum_le_sum
          intro W _
          by_cases hW : 0 < (H.recLaw p).w W
          · apply mul_le_mul_of_nonneg_left _ ((H.recLaw p).nonneg W)
            by_cases hc : PositionCountGate H W
            · have he (w : H.Center → H.Tuple) :
                  eligibility_indicator (F (replaceAllTuples H W w)) =
                    eligibility_indicator (∃ g, (𝒯.P i).h ≤
                      (failedFamily Geom H mask g (replaceAllTuples H W w)).card) := by
                have hcp : PositionCountGate H (replaceAllTuples H W w) := hc
                simp only [F,hcp,true_and]
              simp_rw [he]
              rw [← eligibility_pr_indicator]
              exact conditioned_greedy_bound hconst scales Geom H mask hlookup L htests p W hW hc
            · have he (w : H.Center → H.Tuple) :
                  eligibility_indicator (F (replaceAllTuples H W w)) = 0 := by
                have hcp : ¬ PositionCountGate H (replaceAllTuples H W w) := hc
                simp [F,hcp,eligibility_indicator]
              simp only [he,FinProb.expect_const]
              exact (Real.exp_pos _).le
          · have hz : (H.recLaw p).w W = 0 := le_antisymm (le_of_not_gt hW) ((H.recLaw p).nonneg W)
            simp [hz]
        _ = err := by simp [FinLaw.E,← Finset.sum_mul,(H.recLaw p).sum_one]
    have himp (W : ∀ r, H.Val r)
        (hbad : ¬ (PositionCountGate H W ∧
          ∀ v ∈ siteSet Geom, ∀ j, H.Device.lam / 2 ≤ (eligible Geom H mask W v j).card)) :
        (¬ PositionCountGate H W) ∨ F W := by
      by_cases hc : PositionCountGate H W
      · right
        refine ⟨hc,eligibility_low_forces_many hconst scales Geom H mask W hc ?_⟩
        have hbad' : ¬ (∀ v ∈ siteSet Geom, ∀ j,
            H.Device.lam / 2 ≤ (eligible Geom H mask W v j).card) := fun h => hbad ⟨hc,h⟩
        push_neg at hbad'
        exact hbad'
      · exact Or.inl hc
    calc
      _ ≤ (H.recLaw p).pr (fun W => ¬ PositionCountGate H W) + (H.recLaw p).pr F := by
        unfold FinLaw.pr
        rw [← Finset.sum_add_distrib]
        apply Finset.sum_le_sum
        intro W _
        by_cases hb : ¬ (PositionCountGate H W ∧
          ∀ v ∈ siteSet Geom, ∀ j, H.Device.lam / 2 ≤ (eligible Geom H mask W v j).card)
        · obtain hc | hf := himp W hb
          · simp only [if_pos hb,if_pos hc]
            split_ifs <;> linarith [(H.recLaw p).nonneg W]
          · simp only [if_pos hb,if_pos hf]
            split_ifs <;> linarith [(H.recLaw p).nonneg W]
        · simp only [if_neg hb]
          split_ifs <;> linarith [(H.recLaw p).nonneg W]
      _ ≤ err + err := add_le_add (hcounts p) hF
      _ = _ := by dsimp [err]; ring

end EligibilityRefreshProof

section OddRecipe

variable {κ : CConsts} {T : Stage} {k : ℕ} {𝒯 : Tiling κ T k}
  {i : Fin 𝒯.m} {mesh : Mesh 𝒯}

noncomputable def hitMass (H : PrimitiveHistory κ 𝒯 i mesh) (mask : Masks H)
    (g : Group 𝒯 i) (W : ∀ r, H.Val r) (D : Bin 𝒯 i) (S : Finset H.Center) : ℝ :=
  ∑ y ∈ listHit H W S, (mask g W).within D y

noncomputable def restrictedBin (Geom : ProjectionGeometry κ 𝒯 i)
    (H : PrimitiveHistory κ 𝒯 i mesh) (mask : Masks H)
    (g : Group 𝒯 i) (W : ∀ r, H.Val r) (D : Bin 𝒯 i) : Prop :=
  let S := realizedList Geom H mask g W
  hitMass H mask g W D S ≥ Real.exp (-1.5 * (𝒯.kScale i : ℝ) * S.card) ∧
    ∀ c ∈ S, hitMass H mask g W D S ≥
      Real.exp ((-Real.log 2 + 0.08 * κ.a) * (𝒯.kScale i : ℝ)) *
        hitMass H mask g W D (S.erase c)

noncomputable def tiltWeight (Geom : ProjectionGeometry κ 𝒯 i)
    (H : PrimitiveHistory κ 𝒯 i mesh) (mask : Masks H)
    (g : Group 𝒯 i) (W : ∀ r, H.Val r) (D : Bin 𝒯 i) : ℝ :=
  if restrictedBin Geom H mask g W D then
    (mask g W).prior D * hitMass H mask g W D (realizedList Geom H mask g W) ^ 2 else 0

noncomputable def oddQ (Geom : ProjectionGeometry κ 𝒯 i)
    (H : PrimitiveHistory κ 𝒯 i mesh) (mask : Masks H)
    (g : Group 𝒯 i) (W : ∀ r, H.Val r) (D : Bin 𝒯 i) : ℝ :=
  if groupValid Geom H mask g W then
    tiltWeight Geom H mask g W D / ∑ D', tiltWeight Geom H mask g W D'
  else (mask g W).prior D

noncomputable def oddU (Geom : ProjectionGeometry κ 𝒯 i)
    (H : PrimitiveHistory κ 𝒯 i mesh) (mask : Masks H)
    (g : Group 𝒯 i) (W : ∀ r, H.Val r) (D : Bin 𝒯 i) (y : Fin (T.S.N k)) : ℝ :=
  if groupValid Geom H mask g W ∧ 0 < oddQ Geom H mask g W D then
    if y ∈ listHit H W (realizedList Geom H mask g W) then
      (mask g W).within D y / hitMass H mask g W D (realizedList Geom H mask g W) else 0
  else (mask g W).within D y

/-- S1 bounds for precisely the restricted tilt and its prescribed fallback. -/
structure OddKernels (Geom : ProjectionGeometry κ 𝒯 i)
    (H : PrimitiveHistory κ 𝒯 i mesh) (mask : Masks H) where
  q : Group 𝒯 i → (∀ r, H.Val r) → Bin 𝒯 i → ℝ
  U : Group 𝒯 i → (∀ r, H.Val r) → Bin 𝒯 i → Fin (T.S.N k) → ℝ
  q_eq : q = oddQ Geom H mask
  U_eq : U = oddU Geom H mask
  restricted_mass : ∀ g W, groupValid Geom H mask g W →
    maskedMass H mask g W (listHit H W (realizedList Geom H mask g W)) / 2 ≤
      ∑ D, tiltWeight Geom H mask g W D
  q_nonneg : ∀ g W D, 0 ≤ q g W D
  q_sum : ∀ g W, ∑ D : Bin 𝒯 i, q g W D = 1
  U_nonneg : ∀ g W D y, 0 ≤ U g W D y
  U_sum : ∀ g W D, ∑ y, U g W D y = 1
  U_support : ∀ g W D y, U g W D y ≠ 0 → y ∈ D.1
  q_cap : ∀ g W D, q g W D ≤
    4 * Real.exp (2 * (𝒯.kScale i : ℝ) * 𝒯.tScale i) * (𝒯.P i).d / (𝒯.P i).M
  marginal_cap : ∀ g W y, ∑ D, q g W D * U g W D y ≤
    8 * Real.exp (2 * (𝒯.kScale i : ℝ) * 𝒯.tScale i) / (𝒯.P i).M
  U_support_size : ∀ g W D, 0 < q g W D →
    ((Finset.univ.filter fun y => U g W D y ≠ 0).card : ℝ) ≥
      (1 / 2 : ℝ) * (𝒯.P i).d * Real.exp (-1.5 * (𝒯.kScale i : ℝ) * 𝒯.tScale i)
  /-- Atom bound of the uniform-subset law (required by the shared `SliceSolver.U_atom_cap`). -/
  U_atom_cap : ∀ g W D y, 0 < q g W D →
    U g W D y ≤ 2 * Real.exp (1.5 * (𝒯.kScale i : ℝ) * 𝒯.tScale i) / (𝒯.P i).d
  /-- The conditional law and its masked-prior fallback are uniform on
  subsets (14:75). Section 16 uses the resulting lower atom bound under a pin. -/
  U_uniform : ∀ g W D, 0 < q g W D →
    ∃ support : Finset (Fin (T.S.N k)), ∃ hs : support.Nonempty,
      ∀ y, U g W D y = (FinLaw.uniform support hs).w y
  cheap_mean_support : ∀ p g y,
    (H.recLaw p).E (fun W => ∑ D, q g W D * U g W D y) > 0 →
      ∃ v : mesh.V, 0 < mesh.wt v p ∧
        mesh.paramPrice (mesh.base v) i y ≤ 10 / (𝒯.P i).M

end OddRecipe

section OddKernelProof

variable {κ : CConsts} {T : Stage} {k : ℕ} {𝒯 : Tiling κ T k}
  {i : Fin 𝒯.m} {mesh : Mesh 𝒯}

private theorem hitMass_nonneg (H : PrimitiveHistory κ 𝒯 i mesh) (mask : Masks H)
    (g : Group 𝒯 i) (W : ∀ r, H.Val r) (D : Bin 𝒯 i) (S : Finset H.Center) :
    0 ≤ hitMass H mask g W D S :=
  Finset.sum_nonneg fun y _ => (mask g W).within_nonneg D y

private theorem hitMass_le_one (H : PrimitiveHistory κ 𝒯 i mesh) (mask : Masks H)
    (g : Group 𝒯 i) (W : ∀ r, H.Val r) (D : Bin 𝒯 i) (S : Finset H.Center) :
    hitMass H mask g W D S ≤ 1 := by
  calc
    _ ≤ ∑ y, (mask g W).within D y :=
      Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _)
        (fun y _ _ => (mask g W).within_nonneg D y)
    _ = 1 := (mask g W).within_sum D

private theorem tiltWeight_nonneg (Geom : ProjectionGeometry κ 𝒯 i)
    (H : PrimitiveHistory κ 𝒯 i mesh) (mask : Masks H)
    (g : Group 𝒯 i) (W : ∀ r, H.Val r) (D : Bin 𝒯 i) :
    0 ≤ tiltWeight Geom H mask g W D := by
  unfold tiltWeight
  split_ifs
  · exact mul_nonneg ((mask g W).prior_nonneg D) (sq_nonneg _)
  · rfl

private theorem restricted_mass_bound (hconst : HeightConstantContract κ)
    (scales : PatchScales 𝒯 i) (Geom : ProjectionGeometry κ 𝒯 i)
    (H : PrimitiveHistory κ 𝒯 i mesh) (mask : Masks H)
    (g : Group 𝒯 i) (W : ∀ r, H.Val r) (hv : groupValid Geom H mask g W) :
    maskedMass H mask g W (listHit H W (realizedList Geom H mask g W)) / 2 ≤
      ∑ D, tiltWeight Geom H mask g W D := by
  classical
  let S := realizedList Geom H mask g W
  let m := fun D => hitMass H mask g W D S
  let r := (mask g W).prior
  let A := maskedMass H mask g W (listHit H W S)
  let K : ℝ := 𝒯.kScale i
  let n : ℝ := S.card
  let a := κ.a
  let z := Real.exp (-1.5 * K * n)
  let e := Real.exp ((-Real.log 2 + 0.08 * a) * K)
  let small := fun D => m D < z
  let bad := fun c D => m D < e * hitMass H mask g W D (S.erase c)
  let w := fun D => r D * m D ^ 2
  have hS := hv.2.1
  have hg := hv.2.2
  have hn : 1 ≤ n := by
    dsimp [n, S]
    exact_mod_cast Finset.card_pos.mpr hS.1
  have hnT : n ≤ 𝒯.tScale i := by
    dsimp [n, S]
    exact_mod_cast hS.2.1
  have hK : 0 ≤ K := by dsimp [K]; positivity
  have hA : Real.exp (-2 * K * n) ≤ A := hg.1
  have hA0 : 0 ≤ A := le_trans (Real.exp_pos _).le hA
  have hsum : (∑ D, w D) = A := rfl
  have hw : ∀ D, 0 ≤ w D := fun D =>
    mul_nonneg ((mask g W).prior_nonneg D) (sq_nonneg _)
  have habs : (∑ D, if small D then w D else 0) ≤ Real.exp (-K) * A := by
    calc
      _ ≤ ∑ D, r D * z ^ 2 := by
        apply Finset.sum_le_sum
        intro D _
        split_ifs with hd
        · exact mul_le_mul_of_nonneg_left
            (pow_le_pow_left₀ (hitMass_nonneg H mask g W D S) hd.le 2)
            ((mask g W).prior_nonneg D)
        · exact mul_nonneg ((mask g W).prior_nonneg D) (sq_nonneg z)
      _ = z ^ 2 := by rw [← Finset.sum_mul, (mask g W).prior_sum]; ring
      _ = Real.exp (-3 * K * n) := by rw [← Real.exp_nat_mul]; congr 1; dsimp [z]; ring
      _ ≤ Real.exp (-K) * Real.exp (-2 * K * n) := by
        rw [← Real.exp_add]
        apply Real.exp_le_exp.mpr
        nlinarith
      _ ≤ Real.exp (-K) * A := mul_le_mul_of_nonneg_left hA (Real.exp_pos _).le
  have hbad : ∀ c ∈ S, (∑ D, if bad c D then w D else 0) ≤
      Real.exp (-0.24 * a * K) * A := by
    intro c hc
    have hd := hg.2 c hc
    have heq : e ^ 2 = Real.exp ((-Real.log 4 + 0.16 * a) * K) := by
      have hlog : Real.log (4 : ℝ) = 2 * Real.log 2 := by
        rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.log_pow]; norm_num
      dsimp [e]
      rw [← Real.exp_nat_mul, hlog]
      congr 1
      ring
    have hm := mul_le_mul_of_nonneg_left hd (Real.exp_pos (-0.24 * a * K)).le
    have hcancel : Real.exp (-0.24 * a * K) *
        Real.exp ((-Real.log 4 + 0.4 * a) * K) = e ^ 2 := by
      rw [heq, ← Real.exp_add]
      congr 1
      ring
    calc
      _ ≤ ∑ D, r D * (e * hitMass H mask g W D (S.erase c)) ^ 2 := by
        apply Finset.sum_le_sum
        intro D _
        split_ifs with hd
        · exact mul_le_mul_of_nonneg_left
            (pow_le_pow_left₀ (hitMass_nonneg H mask g W D S) hd.le 2)
            ((mask g W).prior_nonneg D)
        · exact mul_nonneg ((mask g W).prior_nonneg D) (sq_nonneg _)
      _ = e ^ 2 * maskedMass H mask g W (listHit H W (S.erase c)) := by
        unfold maskedMass
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro D _
        dsimp [r, hitMass]
        ring
      _ ≤ Real.exp (-0.24 * a * K) * A := by
        change Real.exp (-0.24 * a * K) *
          (Real.exp ((-Real.log 4 + 0.4 * a) * K) *
            maskedMass H mask g W (listHit H W (S.erase c))) ≤
          Real.exp (-0.24 * a * K) * A at hm
        rwa [← mul_assoc, hcancel] at hm
  have hpoint : ∀ D, w D ≤ tiltWeight Geom H mask g W D +
      (if small D then w D else 0) + ∑ c ∈ S, if bad c D then w D else 0 := by
    intro D
    have hb0 : 0 ≤ ∑ c ∈ S, if bad c D then w D else 0 :=
      Finset.sum_nonneg fun c _ => by split_ifs <;> [exact hw D; rfl]
    by_cases hr : restrictedBin Geom H mask g W D
    · simp only [tiltWeight, if_pos hr]
      have hsmall0 : 0 ≤ if small D then w D else 0 := by split_ifs <;> [exact hw D; rfl]
      change w D ≤ w D + _ + _
      linarith
    · simp only [tiltWeight, if_neg hr, zero_add]
      by_cases hs : small D
      · simp only [if_pos hs]; linarith
      · have hex : ∃ c ∈ S, bad c D := by
          by_contra h
          apply hr
          refine ⟨le_of_not_gt hs, ?_⟩
          intro c hc
          exact le_of_not_gt fun hbad => h ⟨c, hc, hbad⟩
        rcases hex with ⟨c, hc, hb⟩
        simp only [if_neg hs, zero_add]
        calc
          w D = (if bad c D then w D else 0) := by rw [if_pos hb]
          _ ≤ ∑ c ∈ S, if bad c D then w D else 0 := by
            apply Finset.single_le_sum (f := fun c => if bad c D then w D else 0)
            · intro c _
              split_ifs <;> [exact hw D; rfl]
            · exact hc
  have hbound : A ≤ (∑ D, tiltWeight Geom H mask g W D) +
      (Real.exp (-K) + (𝒯.tScale i : ℝ) * Real.exp (-0.24 * a * K)) * A := by
    calc
      A = ∑ D, w D := hsum.symm
      _ ≤ ∑ D, (tiltWeight Geom H mask g W D +
          (if small D then w D else 0) + ∑ c ∈ S, if bad c D then w D else 0) :=
        Finset.sum_le_sum fun D _ => hpoint D
      _ = (∑ D, tiltWeight Geom H mask g W D) +
          (∑ D, if small D then w D else 0) +
          ∑ c ∈ S, ∑ D, if bad c D then w D else 0 := by
        simp only [Finset.sum_add_distrib]
        rw [Finset.sum_comm]
      _ ≤ (∑ D, tiltWeight Geom H mask g W D) + Real.exp (-K) * A +
          ∑ _c ∈ S, Real.exp (-0.24 * a * K) * A :=
        add_le_add (add_le_add le_rfl habs) (Finset.sum_le_sum hbad)
      _ ≤ (∑ D, tiltWeight Geom H mask g W D) +
          (Real.exp (-K) + (𝒯.tScale i : ℝ) * Real.exp (-0.24 * a * K)) * A := by
        simp only [Finset.sum_const, nsmul_eq_mul]
        nlinarith [mul_le_mul_of_nonneg_right hnT
          (mul_nonneg (Real.exp_pos (-0.24 * a * K)).le hA0)]
  have hslack := (hconst.threshold_slack (𝒯.P i).h scales.h_large).2.2.2.2.2.2.2.2.2.2.2
  have hhalf : Real.exp (-K) + (𝒯.tScale i : ℝ) * Real.exp (-0.24 * a * K) ≤ 1 / 2 :=
    hslack.1
  have := mul_le_mul_of_nonneg_right hhalf hA0
  change A / 2 ≤ _
  linarith

private theorem tilt_normalizer_pos (hconst : HeightConstantContract κ)
    (scales : PatchScales 𝒯 i) (Geom : ProjectionGeometry κ 𝒯 i)
    (H : PrimitiveHistory κ 𝒯 i mesh) (mask : Masks H)
    (g : Group 𝒯 i) (W : ∀ r, H.Val r) (hv : groupValid Geom H mask g W) :
    0 < ∑ D, tiltWeight Geom H mask g W D := by
  have hm := hv.2.2.1
  have hr := restricted_mass_bound hconst scales Geom H mask g W hv
  have := Real.exp_pos (-2 * (𝒯.kScale i : ℝ) * (realizedList Geom H mask g W).card)
  linarith

private theorem oddQ_nonneg (Geom : ProjectionGeometry κ 𝒯 i)
    (H : PrimitiveHistory κ 𝒯 i mesh) (mask : Masks H)
    (g : Group 𝒯 i) (W : ∀ r, H.Val r) (D : Bin 𝒯 i) :
    0 ≤ oddQ Geom H mask g W D := by
  unfold oddQ
  split_ifs
  · exact div_nonneg (tiltWeight_nonneg Geom H mask g W D)
      (Finset.sum_nonneg fun D _ => tiltWeight_nonneg Geom H mask g W D)
  · exact (mask g W).prior_nonneg D

private theorem oddQ_sum (hconst : HeightConstantContract κ)
    (scales : PatchScales 𝒯 i) (Geom : ProjectionGeometry κ 𝒯 i)
    (H : PrimitiveHistory κ 𝒯 i mesh) (mask : Masks H)
    (g : Group 𝒯 i) (W : ∀ r, H.Val r) : ∑ D, oddQ Geom H mask g W D = 1 := by
  classical
  by_cases hv : groupValid Geom H mask g W
  · simp only [oddQ, if_pos hv]
    rw [← Finset.sum_div, div_self (tilt_normalizer_pos hconst scales Geom H mask g W hv).ne']
  · simpa only [oddQ, if_neg hv] using (mask g W).prior_sum

private theorem positive_oddQ (hconst : HeightConstantContract κ)
    (scales : PatchScales 𝒯 i) (Geom : ProjectionGeometry κ 𝒯 i)
    (H : PrimitiveHistory κ 𝒯 i mesh) (mask : Masks H)
    (g : Group 𝒯 i) (W : ∀ r, H.Val r) (D : Bin 𝒯 i)
    (hq : 0 < oddQ Geom H mask g W D) :
    0 < (mask g W).prior D ∧
      (groupValid Geom H mask g W → restrictedBin Geom H mask g W D) := by
  classical
  by_cases hv : groupValid Geom H mask g W
  · have hZ := tilt_normalizer_pos hconst scales Geom H mask g W hv
    rw [oddQ, if_pos hv] at hq
    have hnum : 0 < tiltWeight Geom H mask g W D := by
      have := (lt_div_iff₀ hZ).mp hq
      simpa only [zero_mul] using this
    have hr : restrictedBin Geom H mask g W D := by
      by_contra h
      simp [tiltWeight, h] at hnum
    rw [tiltWeight, if_pos hr] at hnum
    refine ⟨?_, fun _ => hr⟩
    by_contra h
    have hz : (mask g W).prior D = 0 :=
      le_antisymm (le_of_not_gt h) ((mask g W).prior_nonneg D)
    simp [hz] at hnum
  · rw [oddQ, if_neg hv] at hq
    exact ⟨hq, fun h => False.elim (hv h)⟩

private theorem oddU_nonneg (Geom : ProjectionGeometry κ 𝒯 i)
    (H : PrimitiveHistory κ 𝒯 i mesh) (mask : Masks H)
    (g : Group 𝒯 i) (W : ∀ r, H.Val r) (D : Bin 𝒯 i) (y : Fin (T.S.N k)) :
    0 ≤ oddU Geom H mask g W D y := by
  unfold oddU
  split_ifs
  · exact div_nonneg ((mask g W).within_nonneg D y) (hitMass_nonneg H mask g W D _)
  · rfl
  · exact (mask g W).within_nonneg D y

private theorem oddU_sum (hconst : HeightConstantContract κ)
    (scales : PatchScales 𝒯 i) (Geom : ProjectionGeometry κ 𝒯 i)
    (H : PrimitiveHistory κ 𝒯 i mesh) (mask : Masks H)
    (g : Group 𝒯 i) (W : ∀ r, H.Val r) (D : Bin 𝒯 i) :
    ∑ y, oddU Geom H mask g W D y = 1 := by
  classical
  by_cases hv : groupValid Geom H mask g W ∧ 0 < oddQ Geom H mask g W D
  · have hr := (positive_oddQ hconst scales Geom H mask g W D hv.2).2 hv.1
    have hm : 0 < hitMass H mask g W D (realizedList Geom H mask g W) :=
      lt_of_lt_of_le (Real.exp_pos _) hr.1
    simp only [oddU, if_pos hv]
    have heq : (∑ y, if y ∈ listHit H W (realizedList Geom H mask g W) then
        (mask g W).within D y else 0) =
        hitMass H mask g W D (realizedList Geom H mask g W) := by
      simp [hitMass, Finset.sum_ite_mem]
    have hterm (y : Fin (T.S.N k)) :
        (if y ∈ listHit H W (realizedList Geom H mask g W) then
          (mask g W).within D y / hitMass H mask g W D (realizedList Geom H mask g W)
        else 0) = (if y ∈ listHit H W (realizedList Geom H mask g W) then
          (mask g W).within D y else 0) /
          hitMass H mask g W D (realizedList Geom H mask g W) := by
      split_ifs <;> simp
    simp_rw [hterm]
    rw [← Finset.sum_div, heq, div_self hm.ne']
  · simpa only [oddU, if_neg hv] using (mask g W).within_sum D

private theorem oddU_support (Geom : ProjectionGeometry κ 𝒯 i)
    (H : PrimitiveHistory κ 𝒯 i mesh) (mask : Masks H)
    (g : Group 𝒯 i) (W : ∀ r, H.Val r) (D : Bin 𝒯 i) (y : Fin (T.S.N k))
    (hy : oddU Geom H mask g W D y ≠ 0) : y ∈ D.1 := by
  apply (mask g W).within_support D y
  intro hz
  apply hy
  unfold oddU
  split_ifs <;> simp [hz]

private theorem tilt_normalizer_bound (hconst : HeightConstantContract κ)
    (scales : PatchScales 𝒯 i) (Geom : ProjectionGeometry κ 𝒯 i)
    (H : PrimitiveHistory κ 𝒯 i mesh) (mask : Masks H)
    (g : Group 𝒯 i) (W : ∀ r, H.Val r) (hv : groupValid Geom H mask g W) :
    1 ≤ (2 * Real.exp (2 * (𝒯.kScale i : ℝ) * 𝒯.tScale i)) *
      ∑ D, tiltWeight Geom H mask g W D := by
  have hr := restricted_mass_bound hconst scales Geom H mask g W hv
  have ht : ((realizedList Geom H mask g W).card : ℝ) ≤ 𝒯.tScale i := by
    exact_mod_cast hv.2.1.2.1
  have he : Real.exp (-2 * (𝒯.kScale i : ℝ) * 𝒯.tScale i) ≤
      Real.exp (-2 * (𝒯.kScale i : ℝ) * (realizedList Geom H mask g W).card) := by
    apply Real.exp_le_exp.mpr
    nlinarith [show (0 : ℝ) ≤ 𝒯.kScale i by positivity]
  have hl : Real.exp (-2 * (𝒯.kScale i : ℝ) * 𝒯.tScale i) ≤
      2 * ∑ D, tiltWeight Geom H mask g W D := by linarith [hv.2.2.1]
  have hm := mul_le_mul_of_nonneg_left hl
    (Real.exp_pos (2 * (𝒯.kScale i : ℝ) * 𝒯.tScale i)).le
  have hc : Real.exp (2 * (𝒯.kScale i : ℝ) * 𝒯.tScale i) *
      Real.exp (-2 * (𝒯.kScale i : ℝ) * 𝒯.tScale i) = 1 := by
    rw [← Real.exp_add]
    convert Real.exp_zero using 1 <;> ring
  rw [hc] at hm
  nlinarith

private theorem oddQ_le_prior (hconst : HeightConstantContract κ)
    (scales : PatchScales 𝒯 i) (Geom : ProjectionGeometry κ 𝒯 i)
    (H : PrimitiveHistory κ 𝒯 i mesh) (mask : Masks H)
    (g : Group 𝒯 i) (W : ∀ r, H.Val r) (D : Bin 𝒯 i) :
    oddQ Geom H mask g W D ≤
      (2 * Real.exp (2 * (𝒯.kScale i : ℝ) * 𝒯.tScale i)) * (mask g W).prior D := by
  classical
  have hp := (mask g W).prior_nonneg D
  have hC : 1 ≤ 2 * Real.exp (2 * (𝒯.kScale i : ℝ) * 𝒯.tScale i) := by
    have he : 1 ≤ Real.exp (2 * (𝒯.kScale i : ℝ) * 𝒯.tScale i) :=
      Real.one_le_exp_iff.mpr (by positivity)
    linarith
  by_cases hv : groupValid Geom H mask g W
  · rw [oddQ, if_pos hv]
    apply (div_le_iff₀ (tilt_normalizer_pos hconst scales Geom H mask g W hv)).mpr
    have hZ := tilt_normalizer_bound hconst scales Geom H mask g W hv
    have hw : tiltWeight Geom H mask g W D ≤ (mask g W).prior D := by
      unfold tiltWeight
      split_ifs
      · have hm0 := hitMass_nonneg H mask g W D (realizedList Geom H mask g W)
        have hm1 := hitMass_le_one H mask g W D (realizedList Geom H mask g W)
        nlinarith [mul_nonneg hp (by nlinarith :
          0 ≤ 1 - hitMass H mask g W D (realizedList Geom H mask g W) ^ 2)]
      · exact hp
    have := mul_le_mul_of_nonneg_right hZ hp
    nlinarith
  · rw [oddQ, if_neg hv]
    nlinarith [mul_le_mul_of_nonneg_right hC hp]

private theorem odd_marginal_term_bound (hconst : HeightConstantContract κ)
    (scales : PatchScales 𝒯 i) (Geom : ProjectionGeometry κ 𝒯 i)
    (H : PrimitiveHistory κ 𝒯 i mesh) (mask : Masks H)
    (g : Group 𝒯 i) (W : ∀ r, H.Val r) (D : Bin 𝒯 i) (y : Fin (T.S.N k)) :
    oddQ Geom H mask g W D * oddU Geom H mask g W D y ≤
      (2 * Real.exp (2 * (𝒯.kScale i : ℝ) * 𝒯.tScale i)) *
        ((mask g W).prior D * (mask g W).within D y) := by
  classical
  have hp := (mask g W).prior_nonneg D
  have hy0 := (mask g W).within_nonneg D y
  by_cases hv : groupValid Geom H mask g W
  · by_cases hq : 0 < oddQ Geom H mask g W D
    · have hr := (positive_oddQ hconst scales Geom H mask g W D hq).2 hv
      have hm := lt_of_lt_of_le (Real.exp_pos _) hr.1
      have hZ := tilt_normalizer_pos hconst scales Geom H mask g W hv
      have hZb := tilt_normalizer_bound hconst scales Geom H mask g W hv
      unfold oddU
      rw [if_pos ⟨hv, hq⟩]
      split_ifs with hy
      · have heq : oddQ Geom H mask g W D *
            ((mask g W).within D y /
              hitMass H mask g W D (realizedList Geom H mask g W)) =
            ((mask g W).prior D * hitMass H mask g W D (realizedList Geom H mask g W) *
              (mask g W).within D y) / ∑ D', tiltWeight Geom H mask g W D' := by
          rw [oddQ, if_pos hv, tiltWeight, if_pos hr]
          field_simp [hm.ne', hZ.ne']
          <;> ring
        rw [heq]
        apply (div_le_iff₀ hZ).mpr
        have hm1 := hitMass_le_one H mask g W D (realizedList Geom H mask g W)
        calc
          _ ≤ (mask g W).prior D * (mask g W).within D y := by
            have := mul_le_mul_of_nonneg_left hm1 (mul_nonneg hp hy0)
            nlinarith
          _ ≤ _ := by
            have := mul_le_mul_of_nonneg_right hZb (mul_nonneg hp hy0)
            nlinarith
      · simp only [mul_zero]
        positivity
    · have hz : oddQ Geom H mask g W D = 0 :=
        le_antisymm (le_of_not_gt hq) (oddQ_nonneg Geom H mask g W D)
      rw [hz, zero_mul]
      positivity
  · rw [oddQ, if_neg hv, oddU, if_neg (fun h => hv h.1)]
    have he : 1 ≤ Real.exp (2 * (𝒯.kScale i : ℝ) * 𝒯.tScale i) :=
      Real.one_le_exp_iff.mpr (by positivity)
    nlinarith [mul_le_mul_of_nonneg_right he (mul_nonneg hp hy0)]

private theorem prior_pos_retained (H : PrimitiveHistory κ 𝒯 i mesh) (mask : Masks H)
    (g : Group 𝒯 i) (W : ∀ r, H.Val r) (D : Bin 𝒯 i)
    (hp : 0 < (mask g W).prior D) : D ∈ (mask g W).retained := by
  by_contra h
  rw [(mask g W).prior_uniform D, if_neg h] at hp
  exact lt_irrefl _ hp

private theorem mask_atom_cap (h𝒯 : Tiling.Valid 𝒯)
    (H : PrimitiveHistory κ 𝒯 i mesh) (mask : Masks H)
    (g : Group 𝒯 i) (W : ∀ r, H.Val r) (D : Bin 𝒯 i) (y : Fin (T.S.N k))
    (hp : 0 < (mask g W).prior D) : (mask g W).within D y ≤ 2 / (𝒯.P i).d := by
  classical
  have hr := prior_pos_retained H mask g W D hp
  have hc : 0 < ((mask g W).cheap D).card :=
    Finset.card_pos.mpr ((mask g W).cheap_nonempty D hr)
  have hd : (𝒯.P i).d ≤ 2 * ((mask g W).cheap D).card :=
    ((mask g W).retained_spec D).mp hr
  have hdpos : 0 < (𝒯.P i).d := by
    rw [← h𝒯.bins_card i D.1 D.2]
    apply Finset.card_pos.mpr
    obtain ⟨x, hx⟩ := (mask g W).cheap_nonempty D hr
    exact ⟨x, (mask g W).cheap_subset D hx⟩
  rw [(mask g W).within_uniform D y, if_pos hr]
  split_ifs
  · apply (div_le_div_iff₀ (by exact_mod_cast hc) (by positivity)).mpr
    simp only [one_mul]
    exact_mod_cast hd
  · positivity

private theorem oddU_atom_bound (hconst : HeightConstantContract κ)
    (scales : PatchScales 𝒯 i) (h𝒯 : Tiling.Valid 𝒯) (Geom : ProjectionGeometry κ 𝒯 i)
    (H : PrimitiveHistory κ 𝒯 i mesh) (mask : Masks H)
    (g : Group 𝒯 i) (W : ∀ r, H.Val r) (D : Bin 𝒯 i) (y : Fin (T.S.N k))
    (hq : 0 < oddQ Geom H mask g W D) :
    oddU Geom H mask g W D y ≤
      2 * Real.exp (1.5 * (𝒯.kScale i : ℝ) * 𝒯.tScale i) / (𝒯.P i).d := by
  classical
  have hp := (positive_oddQ hconst scales Geom H mask g W D hq).1
  have hy := mask_atom_cap h𝒯 H mask g W D y hp
  let E := Real.exp (1.5 * (𝒯.kScale i : ℝ) * 𝒯.tScale i)
  have he : 1 ≤ E := Real.one_le_exp_iff.mpr (by positivity)
  by_cases hv : groupValid Geom H mask g W
  · have hr := (positive_oddQ hconst scales Geom H mask g W D hq).2 hv
    have hm := lt_of_lt_of_le (Real.exp_pos _) hr.1
    have ht : ((realizedList Geom H mask g W).card : ℝ) ≤ 𝒯.tScale i := by
      exact_mod_cast hv.2.1.2.1
    have hl : Real.exp (-1.5 * (𝒯.kScale i : ℝ) * 𝒯.tScale i) ≤
        hitMass H mask g W D (realizedList Geom H mask g W) := by
      apply le_trans _ hr.1
      apply Real.exp_le_exp.mpr
      nlinarith [show (0 : ℝ) ≤ 𝒯.kScale i by positivity]
    have heq : E * Real.exp (-1.5 * (𝒯.kScale i : ℝ) * 𝒯.tScale i) = 1 := by
      dsimp [E]
      rw [← Real.exp_add]
      convert Real.exp_zero using 1 <;> ring
    have heM : 1 ≤ E * hitMass H mask g W D (realizedList Geom H mask g W) := by
      have h := mul_le_mul_of_nonneg_left hl (show 0 ≤ E from (Real.exp_pos _).le)
      rwa [heq] at h
    unfold oddU
    rw [if_pos ⟨hv, hq⟩]
    split_ifs
    · apply (div_le_iff₀ hm).mpr
      calc
        (mask g W).within D y ≤ (2 : ℝ) / (𝒯.P i).d := hy
        _ ≤ ((2 : ℝ) / (𝒯.P i).d) * (E *
            hitMass H mask g W D (realizedList Geom H mask g W)) := by
          have := mul_le_mul_of_nonneg_left heM (by positivity : (0 : ℝ) ≤ 2 / (𝒯.P i).d)
          simpa only [mul_one] using this
        _ = _ := by dsimp [E]; ring
    · positivity
  · rw [oddU, if_neg (fun h => hv h.1)]
    calc
      (mask g W).within D y ≤ (2 : ℝ) / (𝒯.P i).d := hy
      _ ≤ _ := by
        have := mul_le_mul_of_nonneg_left he (by positivity : (0 : ℝ) ≤ 2 / (𝒯.P i).d)
        dsimp [E] at this
        simpa only [mul_one, div_mul_eq_mul_div] using this

private theorem oddU_support_bound (hconst : HeightConstantContract κ)
    (scales : PatchScales 𝒯 i) (h𝒯 : Tiling.Valid 𝒯) (Geom : ProjectionGeometry κ 𝒯 i)
    (H : PrimitiveHistory κ 𝒯 i mesh) (mask : Masks H)
    (g : Group 𝒯 i) (W : ∀ r, H.Val r) (D : Bin 𝒯 i)
    (hq : 0 < oddQ Geom H mask g W D) :
    ((Finset.univ.filter fun y => oddU Geom H mask g W D y ≠ 0).card : ℝ) ≥
      (1 / 2 : ℝ) * (𝒯.P i).d *
        Real.exp (-1.5 * (𝒯.kScale i : ℝ) * 𝒯.tScale i) := by
  classical
  let F := Finset.univ.filter fun y => oddU Geom H mask g W D y ≠ 0
  let E := Real.exp (1.5 * (𝒯.kScale i : ℝ) * 𝒯.tScale i)
  have hp := (positive_oddQ hconst scales Geom H mask g W D hq).1
  have hr := prior_pos_retained H mask g W D hp
  have hd : (0 : ℝ) < (𝒯.P i).d := by
    apply Nat.cast_pos.mpr
    rw [← h𝒯.bins_card i D.1 D.2]
    apply Finset.card_pos.mpr
    obtain ⟨x, hx⟩ := (mask g W).cheap_nonempty D hr
    exact ⟨x, (mask g W).cheap_subset D hx⟩
  have hsum : (∑ y ∈ F, oddU Geom H mask g W D y) = 1 := by
    rw [← oddU_sum hconst scales Geom H mask g W D]
    apply Finset.sum_subset (Finset.filter_subset ..)
    intro y _ hy
    simpa [F] using hy
  have hbound : 1 ≤ (F.card : ℝ) * (2 * E / (𝒯.P i).d) := by
    calc
      1 = ∑ y ∈ F, oddU Geom H mask g W D y := hsum.symm
      _ ≤ ∑ _y ∈ F, 2 * E / (𝒯.P i).d :=
        Finset.sum_le_sum fun y _ => oddU_atom_bound hconst scales h𝒯 Geom H mask g W D y hq
      _ = _ := by simp only [Finset.sum_const, nsmul_eq_mul]
  have he : 0 < E := Real.exp_pos _
  have hc : (1 / 2 : ℝ) * (𝒯.P i).d / E ≤ (F.card : ℝ) := by
    have hb : (𝒯.P i).d ≤ (F.card : ℝ) * (2 * E) := by
      have := (le_div_iff₀ hd).mp (show 1 ≤ (F.card : ℝ) * (2 * E) / (𝒯.P i).d by
        simpa [mul_div_assoc] using hbound)
      simpa using this
    apply (div_le_iff₀ he).mpr
    nlinarith
  have heq : 1 / E = Real.exp (-1.5 * (𝒯.kScale i : ℝ) * 𝒯.tScale i) := by
    dsimp [E]
    rw [one_div, ← Real.exp_neg]
    congr 1
    ring
  change _ ≤ (F.card : ℝ)
  calc
    _ = (1 / 2 : ℝ) * (𝒯.P i).d / E := by
      rw [← heq]
      ring
    _ ≤ _ := hc

private theorem record_mask_vertex_pos (H : PrimitiveHistory κ 𝒯 i mesh)
    (p : mesh.Param) (g : Group 𝒯 i) (W : ∀ r, H.Val r)
    (hw : 0 < (H.recLaw p).w W) : 0 < mesh.wt (H.maskVertex g W) p := by
  classical
  have hne : (H.record p (.inr (.inl g))).w (W (.inr (.inl g))) ≠ 0 := by
    intro hz
    have he : (H.recLaw p).w W = 0 := by
      change (∏ r, (H.record p r).w (W r)) = 0
      exact Finset.prod_eq_zero (Finset.mem_univ (.inr (.inl g))) hz
    linarith
  have hwt : mesh.wt (H.maskVertex g W) p ≠ 0 := by
    intro hz
    apply hne
    change mesh.wt (H.maskVertex g W) p * _ = 0
    rw [hz, zero_mul]
  exact lt_of_le_of_ne (mesh.wt_nonneg _ _) (Ne.symm hwt)

private theorem positive_marginal_cheap (hconst : HeightConstantContract κ)
    (scales : PatchScales 𝒯 i) (Geom : ProjectionGeometry κ 𝒯 i)
    (H : PrimitiveHistory κ 𝒯 i mesh) (mask : Masks H)
    (g : Group 𝒯 i) (W : ∀ r, H.Val r) (D : Bin 𝒯 i) (y : Fin (T.S.N k))
    (hpos : 0 < oddQ Geom H mask g W D * oddU Geom H mask g W D y) :
    mesh.paramPrice (mesh.base (H.maskVertex g W)) i y ≤ 10 / (𝒯.P i).M := by
  classical
  have hq : 0 < oddQ Geom H mask g W D := by
    by_contra h
    have hz := le_antisymm (le_of_not_gt h) (oddQ_nonneg Geom H mask g W D)
    rw [hz, zero_mul] at hpos
    exact lt_irrefl _ hpos
  have hu : oddU Geom H mask g W D y ≠ 0 := by
    intro hz
    rw [hz, mul_zero] at hpos
    exact lt_irrefl _ hpos
  have hp := (positive_oddQ hconst scales Geom H mask g W D hq).1
  have hr := prior_pos_retained H mask g W D hp
  have hwithin : (mask g W).within D y ≠ 0 := by
    intro hz
    apply hu
    unfold oddU
    split_ifs <;> simp [hz]
  have hcheap : y ∈ (mask g W).cheap D := by
    by_contra h
    rw [(mask g W).within_uniform D y, if_pos hr, if_neg h] at hwithin
    exact hwithin rfl
  exact (mask g W).cheap_price D y hcheap

private theorem positive_summand {Ω : Type*} [Fintype Ω] (f : Ω → ℝ)
    (h : 0 < ∑ ω, f ω) : ∃ ω, 0 < f ω := by
  by_contra hn
  push_neg at hn
  have hs : (∑ ω, f ω) ≤ 0 := Finset.sum_nonpos fun ω _ => hn ω
  exact (not_le_of_gt h) hs

end OddKernelProof

/-- L14 (14:75): on a positive bin the conditional law is uniform on a subset — the masked within-bin law is
uniform (`MaskFacts.within_uniform`) and the restriction to the realized list hits renormalizes it. Supplies
`OddKernels.U_uniform` (consumed by Section 16 for a lower atom bound under a pin). -/
theorem oddU_uniform {κ : CConsts} {T : Stage} {k : ℕ} {𝒯 : Tiling κ T k} {i : Fin 𝒯.m} {mesh : Mesh 𝒯}
    (Geom : ProjectionGeometry κ 𝒯 i) (H : PrimitiveHistory κ 𝒯 i mesh) (mask : Masks H) :
    ∀ g W D, 0 < oddQ Geom H mask g W D →
      ∃ support : Finset (Fin (T.S.N k)), ∃ hs : support.Nonempty,
        ∀ y, oddU Geom H mask g W D y = (FinLaw.uniform support hs).w y := by
  classical
  intro g W D hq
  by_cases hv : groupValid Geom H mask g W
  · have hden0 : 0 ≤ ∑ D', tiltWeight Geom H mask g W D' :=
      Finset.sum_nonneg fun D' _ => tiltWeight_nonneg Geom H mask g W D'
    have hnum0 : 0 ≤ tiltWeight Geom H mask g W D :=
      tiltWeight_nonneg Geom H mask g W D
    have hdiv : 0 < tiltWeight Geom H mask g W D ∧
        0 < ∑ D', tiltWeight Geom H mask g W D' := by
      have hpos : (0 < tiltWeight Geom H mask g W D ∧
          0 < ∑ D', tiltWeight Geom H mask g W D') ∨
          (tiltWeight Geom H mask g W D < 0 ∧
            ∑ D', tiltWeight Geom H mask g W D' < 0) := by
        have hq' : 0 < tiltWeight Geom H mask g W D /
            ∑ D', tiltWeight Geom H mask g W D' := by
          simpa only [oddQ, if_pos hv] using hq
        exact (div_pos_iff.mp hq')
      rcases hpos with hpos | hneg
      · exact hpos
      · exact False.elim ((not_lt_of_ge hnum0) hneg.1)
    have htw : 0 < tiltWeight Geom H mask g W D := hdiv.1
    have hrestricted : restrictedBin Geom H mask g W D := by
      unfold tiltWeight at htw
      split_ifs at htw with hrestricted
      · exact hrestricted
      · norm_num at htw
    have hprod : 0 < (mask g W).prior D *
        hitMass H mask g W D (realizedList Geom H mask g W) ^ 2 := by
      rw [tiltWeight, if_pos hrestricted] at htw
      exact htw
    have hprior : 0 < (mask g W).prior D := by
      by_contra h
      have hz : (mask g W).prior D = 0 :=
        le_antisymm (le_of_not_gt h) ((mask g W).prior_nonneg D)
      rw [hz, zero_mul] at hprod
      exact (lt_irrefl 0) hprod
    have hmass : 0 < hitMass H mask g W D (realizedList Geom H mask g W) := by
      have hnonneg := hitMass_nonneg H mask g W D (realizedList Geom H mask g W)
      by_contra h
      have hz : hitMass H mask g W D (realizedList Geom H mask g W) = 0 :=
        le_antisymm (le_of_not_gt h) hnonneg
      rw [hz] at hprod
      norm_num at hprod
    have hretained := prior_pos_retained H mask g W D hprior
    let support := (listHit H W (realizedList Geom H mask g W)).filter
      fun y => y ∈ (mask g W).cheap D
    have hsupport : support.Nonempty := by
      have hform : hitMass H mask g W D (realizedList Geom H mask g W) =
          ∑ y, if y ∈ listHit H W (realizedList Geom H mask g W)
            then (mask g W).within D y else 0 := by
        simp [hitMass]
      obtain ⟨y, hy⟩ := positive_summand
        (f := fun y : Fin (T.S.N k) =>
          if y ∈ listHit H W (realizedList Geom H mask g W)
          then (mask g W).within D y else 0)
        (by rw [← hform]; exact hmass)
      have hyhit : y ∈ listHit H W (realizedList Geom H mask g W) := by
        by_contra hyhit
        simp [hyhit] at hy
      have hywithin : 0 < (mask g W).within D y := by
        simpa [hyhit] using hy
      have hycheap : y ∈ (mask g W).cheap D := by
        rw [(mask g W).within_uniform D y, if_pos hretained] at hywithin
        split_ifs at hywithin with hycheap
        · exact hycheap
        · norm_num at hywithin
      exact ⟨y, Finset.mem_filter.mpr ⟨hyhit, hycheap⟩⟩
    have hcheap_pos : 0 < ((mask g W).cheap D).card :=
      Finset.card_pos.mpr ((mask g W).cheap_nonempty D hretained)
    have hsupport_pos : 0 < (support.card : ℝ) := by
      exact_mod_cast Finset.card_pos.mpr hsupport
    have hcheap_cast_pos : 0 < ((mask g W).cheap D).card := by
      exact_mod_cast hcheap_pos
    have hmass_eq : hitMass H mask g W D (realizedList Geom H mask g W) =
        (support.card : ℝ) / ((mask g W).cheap D).card := by
      calc
        hitMass H mask g W D (realizedList Geom H mask g W) =
            ∑ y ∈ listHit H W (realizedList Geom H mask g W),
              if y ∈ (mask g W).cheap D then
                (1 : ℝ) / ((mask g W).cheap D).card else 0 := by
          unfold hitMass
          apply Finset.sum_congr rfl
          intro y hy
          rw [(mask g W).within_uniform D y, if_pos hretained]
        _ = ∑ y ∈ support, (1 : ℝ) / ((mask g W).cheap D).card := by
          dsimp [support]
          rw [← Finset.sum_filter]
        _ = (support.card : ℝ) / ((mask g W).cheap D).card := by
          simp [div_eq_mul_inv]
    refine ⟨support, hsupport, ?_⟩
    intro y
    have hcond : groupValid Geom H mask g W ∧ 0 < oddQ Geom H mask g W D := ⟨hv, hq⟩
    rw [oddU, if_pos hcond]
    by_cases hy : y ∈ listHit H W (realizedList Geom H mask g W)
    · rw [if_pos hy, (mask g W).within_uniform D y, if_pos hretained]
      by_cases hycheap : y ∈ (mask g W).cheap D
      · have hysupport : y ∈ support := Finset.mem_filter.mpr ⟨hy, hycheap⟩
        rw [if_pos hycheap]
        simp only [FinLaw.uniform, hysupport]
        simp only [if_true]
        rw [hmass_eq]
        field_simp [ne_of_gt hcheap_cast_pos, ne_of_gt hsupport_pos]
        <;> ring_nf
      · have hysupport : y ∉ support := by
          simp [support, hy, hycheap]
        rw [if_neg hycheap]
        simp only [FinLaw.uniform, hysupport]
        simp
    · have hysupport : y ∉ support := by
        simp [support, hy]
      rw [if_neg hy]
      simp only [FinLaw.uniform, hysupport]
      simp
  · have hprior : 0 < (mask g W).prior D := by
      simpa [oddQ, hv] using hq
    have hretained := prior_pos_retained H mask g W D hprior
    refine ⟨(mask g W).cheap D,
      (mask g W).cheap_nonempty D hretained, ?_⟩
    intro y
    have hcond : ¬ (groupValid Geom H mask g W ∧ 0 < oddQ Geom H mask g W D) :=
      fun h => hv h.1
    rw [oddU, if_neg hcond, (mask g W).within_uniform D y, if_pos hretained,
      FinLaw.uniform]

theorem odd_bin_laws (κ : CConsts) (hκ : κ.Admissible)
    (hconst : HeightConstantContract κ)
    {T : Stage} {k : ℕ} {𝒯 : Tiling κ T k} (h𝒯 : Tiling.Valid 𝒯)
    {i : Fin 𝒯.m} {mesh : Mesh 𝒯} (scales : PatchScales 𝒯 i)
    (Geom : ProjectionGeometry κ 𝒯 i) (H : PrimitiveHistory κ 𝒯 i mesh) (mask : Masks H) :
    Nonempty (OddKernels Geom H mask) := by
  classical
  refine ⟨{
    q := oddQ Geom H mask
    U := oddU Geom H mask
    q_eq := rfl
    U_eq := rfl
    restricted_mass := restricted_mass_bound hconst scales Geom H mask
    q_nonneg := oddQ_nonneg Geom H mask
    q_sum := oddQ_sum hconst scales Geom H mask
    U_nonneg := oddU_nonneg Geom H mask
    U_sum := oddU_sum hconst scales Geom H mask
    U_support := oddU_support Geom H mask
    q_cap := ?_
    marginal_cap := ?_
    U_support_size := oddU_support_bound hconst scales h𝒯 Geom H mask
    U_atom_cap := fun g W D y hq => oddU_atom_bound hconst scales h𝒯 Geom H mask g W D y hq
    U_uniform := oddU_uniform Geom H mask
    cheap_mean_support := ?_ }⟩
  · intro g W D
    calc
      oddQ Geom H mask g W D ≤
          (2 * Real.exp (2 * (𝒯.kScale i : ℝ) * 𝒯.tScale i)) * (mask g W).prior D :=
        oddQ_le_prior hconst scales Geom H mask g W D
      _ ≤ (2 * Real.exp (2 * (𝒯.kScale i : ℝ) * 𝒯.tScale i)) *
          (2 * (𝒯.P i).d / (𝒯.P i).M) :=
        mul_le_mul_of_nonneg_left ((mask g W).prior_cap D) (by positivity)
      _ = _ := by ring
  · intro g W y
    calc
      (∑ D, oddQ Geom H mask g W D * oddU Geom H mask g W D y) ≤
          ∑ D, (2 * Real.exp (2 * (𝒯.kScale i : ℝ) * 𝒯.tScale i)) *
            ((mask g W).prior D * (mask g W).within D y) :=
        Finset.sum_le_sum fun D _ => odd_marginal_term_bound hconst scales Geom H mask g W D y
      _ = (2 * Real.exp (2 * (𝒯.kScale i : ℝ) * 𝒯.tScale i)) *
          ∑ D, (mask g W).prior D * (mask g W).within D y := by rw [Finset.mul_sum]
      _ ≤ (2 * Real.exp (2 * (𝒯.kScale i : ℝ) * 𝒯.tScale i)) *
          (4 / (𝒯.P i).M) :=
        mul_le_mul_of_nonneg_left ((mask g W).aggregate_masked_mass y) (by positivity)
      _ = _ := by ring
  · intro p g y hmean
    obtain ⟨W, hW⟩ := positive_summand _ hmean
    have hpair := (mul_pos_iff.mp hW).resolve_right
      (fun h => (not_lt_of_ge ((H.recLaw p).nonneg W)) h.1)
    obtain ⟨D, hD⟩ := positive_summand _ hpair.2
    exact ⟨H.maskVertex g W, record_mask_vertex_pos H p g W hpair.1,
      positive_marginal_cheap hconst scales Geom H mask g W D y hD⟩

section PosteriorRecipe

variable {κ : CConsts} {T : Stage} {k : ℕ} {𝒯 : Tiling κ T k}
  {i : Fin 𝒯.m} {mesh : Mesh 𝒯}

noncomputable def refLaw (Geom : ProjectionGeometry κ 𝒯 i)
    (H : PrimitiveHistory κ 𝒯 i mesh) (mask : Masks H)
    (O : OddKernels Geom H mask) (W : ∀ r, H.Val r) :=
  internalRefLaw (fun g => O.q g W) (fun g => O.q_nonneg g W) (fun g => O.q_sum g W)
    (fun g => O.U g W) (fun g => O.U_nonneg g W) (fun g => O.U_sum g W) Geom.groupOf

/-- The actual selected-and-valid sublikelihood, recomputing all rules at `w`. -/
noncomputable def subLikelihood (Geom : ProjectionGeometry κ 𝒯 i)
    (H : PrimitiveHistory κ 𝒯 i mesh) (mask : Masks H) (O : OddKernels Geom H mask)
    (v : EvenRole 𝒯 i) (c : H.Center) (W : ∀ r, H.Val r)
    (w : H.Tuple) (ys : InternalLabels 𝒯 i) : ℝ :=
  let W' := H.replaceTuple W c w
  if selected Geom H mask W' v = some c ∧ starValid Geom H mask v W' then
    (refLaw Geom H mask O W').pr (fun ω => nbrLabels v.1 ω.2 = ys) else 0

noncomputable def referenceLists (Geom : ProjectionGeometry κ 𝒯 i)
    (H : PrimitiveHistory κ 𝒯 i mesh) (g : Group 𝒯 i) (c : H.Center)
    (W : ∀ r, H.Val r) : Finset (Finset H.Center) :=
  Finset.univ.filter fun S => admissibleList Geom H g W S ∧ c ∈ S

/-- Deleted squared-tilt prior, with the masked-prior fallback at mass zero. -/
noncomputable def deletedQ (H : PrimitiveHistory κ 𝒯 i mesh) (mask : Masks H)
    (g : Group 𝒯 i) (c : H.Center) (W : ∀ r, H.Val r) (S : Finset H.Center)
    (D : Bin 𝒯 i) : ℝ :=
  let A := maskedMass H mask g W (listHit H W (S.erase c))
  if 0 < A then (mask g W).prior D * hitMass H mask g W D (S.erase c) ^ 2 / A
  else (mask g W).prior D

noncomputable def deletedU (H : PrimitiveHistory κ 𝒯 i mesh) (mask : Masks H)
    (g : Group 𝒯 i) (c : H.Center) (W : ∀ r, H.Val r) (S : Finset H.Center)
    (D : Bin 𝒯 i) (y : Fin (T.S.N k)) : ℝ :=
  let m := hitMass H mask g W D (S.erase c)
  if 0 < m then if y ∈ listHit H W (S.erase c) then (mask g W).within D y / m else 0
  else (mask g W).within D y

noncomputable def groupLabelMass (Geom : ProjectionGeometry κ 𝒯 i)
    (v : EvenRole 𝒯 i) (g : Group 𝒯 i)
    (q : Bin 𝒯 i → ℝ) (U : Bin 𝒯 i → Fin (T.S.N k) → ℝ)
    (ys : InternalLabels 𝒯 i) : ℝ :=
  ∑ D, q D * ∏ l, if Geom.groupOf (flipPos v.1 l) = g then U D (ys l) else 1

/-- Product of uniform list mixtures, using only frozen positions and deleted
hit sets. This reference is independent of the varied tuple (TeX 108–113). -/
noncomputable def referenceWeight (Geom : ProjectionGeometry κ 𝒯 i)
    (H : PrimitiveHistory κ 𝒯 i mesh) (mask : Masks H)
    (v : EvenRole 𝒯 i) (c : H.Center) (W : ∀ r, H.Val r)
    (ys : InternalLabels 𝒯 i) : ℝ :=
  ∏ g : Group 𝒯 i,
    let lists := referenceLists Geom H g c W
    if lists.Nonempty then
      (∑ S ∈ lists, groupLabelMass Geom v g
        (deletedQ H mask g c W S) (deletedU H mask g c W S) ys) / lists.card
    else groupLabelMass Geom v g (mask g W).prior (mask g W).within ys

/-- Domination is about the fixed actual sublikelihood, not a freely chosen value. -/
def LikelihoodDomination (Geom : ProjectionGeometry κ 𝒯 i)
    (H : PrimitiveHistory κ 𝒯 i mesh) (mask : Masks H) (O : OddKernels Geom H mask) : Prop :=
  ∀ v c W w ys, subLikelihood Geom H mask O v c W w ys ≤
    Real.exp ((Real.log 2 - 0.06 * κ.a) * (𝒯.kScale i : ℝ) * (𝒯.P i).h) *
      referenceWeight Geom H mask v c W ys

structure LikelihoodData (Geom : ProjectionGeometry κ 𝒯 i)
    (H : PrimitiveHistory κ 𝒯 i mesh) (mask : Masks H) (O : OddKernels Geom H mask) where
  reference : ∀ v c W, FinLaw (InternalLabels 𝒯 i)
  reference_eq : ∀ v c W ys, (reference v c W).w ys = referenceWeight Geom H mask v c W ys
  independent : ∀ v c W w, reference v c (H.replaceTuple W c w) = reference v c W
  domination : LikelihoodDomination Geom H mask O

end PosteriorRecipe

set_option maxHeartbeats 800000 in
/-- P14.1g: the specified probability reference and actual counterfactual likelihood. -/
theorem likelihood_ratio_domination (κ : CConsts) (hκ : κ.Admissible)
    (hconst : HeightConstantContract κ)
    {T : Stage} {k : ℕ} {𝒯 : Tiling κ T k} (h𝒯 : Tiling.Valid 𝒯)
    {i : Fin 𝒯.m} {mesh : Mesh 𝒯} (scales : PatchScales 𝒯 i)
    (Geom : ProjectionGeometry κ 𝒯 i) (H : PrimitiveHistory κ 𝒯 i mesh)
    (mask : Masks H) (hlookup : MaskLookup H mask) (O : OddKernels Geom H mask) :
    Nonempty (LikelihoodData Geom H mask O) := by
  classical
  have hmaskTransport (g : Group 𝒯 i) (W : ∀ r, H.Val r) (c : H.Center)
      (w : H.Tuple) :
      (mask g (H.replaceTuple W c w)).prior = (mask g W).prior ∧
        (mask g (H.replaceTuple W c w)).within = (mask g W).within := by
    apply hlookup
    simp [PrimitiveHistory.maskVertex, PrimitiveHistory.replaceTuple]
  have hlistTransport (g : Group 𝒯 i) (W : ∀ r, H.Val r) (c : H.Center)
      (w : H.Tuple) :
      referenceLists Geom H g c (H.replaceTuple W c w) =
        referenceLists Geom H g c W := by
    have hpresent (d : H.Center) :
        H.present (H.replaceTuple W c w) d = H.present W d := by
      by_cases hdc : d = c
      · subst d
        simp [PrimitiveHistory.present, PrimitiveHistory.replaceTuple,
          PrimitiveHistory.cornerOf, PrimitiveHistory.active]
      · simp [PrimitiveHistory.present, PrimitiveHistory.replaceTuple, hdc]
    ext S
    simp only [referenceLists, Finset.mem_filter, Finset.mem_univ, true_and]
    constructor
    · rintro ⟨hlist, hc⟩
      unfold admissibleList at hlist ⊢
      rcases hlist with ⟨hn, hcard, hprops⟩
      refine ⟨⟨hn, hcard, ?_⟩, hc⟩
      intro d hd
      rcases hprops d hd with ⟨hrange, hpres⟩
      exact ⟨hrange, (hpresent d) ▸ hpres⟩
    · rintro ⟨hlist, hc⟩
      unfold admissibleList at hlist ⊢
      rcases hlist with ⟨hn, hcard, hprops⟩
      refine ⟨⟨hn, hcard, ?_⟩, hc⟩
      intro d hd
      rcases hprops d hd with ⟨hrange, hpres⟩
      exact ⟨hrange, (hpresent d).symm ▸ hpres⟩
  have hhitTransport (W : ∀ r, H.Val r) (c : H.Center) (w : H.Tuple)
      (S : Finset H.Center) :
      listHit H W (S.erase c) = listHit H (H.replaceTuple W c w) (S.erase c) := by
    ext y
    simp only [listHit, Finset.mem_filter, Finset.mem_univ, true_and]
    constructor
    · intro h d hd r
      have hdc : d ≠ c := (Finset.mem_erase.mp hd).1
      have htuple : H.tuple (H.replaceTuple W c w) d = H.tuple W d := by
        simp [PrimitiveHistory.tuple, PrimitiveHistory.replaceTuple, hdc]
      simpa [htuple] using h d hd r
    · intro h d hd r
      have hdc : d ≠ c := (Finset.mem_erase.mp hd).1
      have htuple : H.tuple (H.replaceTuple W c w) d = H.tuple W d := by
        simp [PrimitiveHistory.tuple, PrimitiveHistory.replaceTuple, hdc]
      simpa [htuple] using h d hd r
  have hmassTransport (g : Group 𝒯 i) (W : ∀ r, H.Val r) (c : H.Center)
      (w : H.Tuple) (S : Finset H.Center) (D : Bin 𝒯 i) :
      hitMass H mask g W D (S.erase c) =
        hitMass H mask g (H.replaceTuple W c w) D (S.erase c) := by
    unfold hitMass
    rw [hhitTransport W c w S, (hmaskTransport g W c w).2]
  have hmaskedTransport (g : Group 𝒯 i) (W : ∀ r, H.Val r) (c : H.Center)
      (w : H.Tuple) (S : Finset H.Center) :
      maskedMass H mask g W (listHit H W (S.erase c)) =
        maskedMass H mask g (H.replaceTuple W c w)
          (listHit H (H.replaceTuple W c w) (S.erase c)) := by
    unfold maskedMass
    rw [hhitTransport W c w S, (hmaskTransport g W c w).1,
      (hmaskTransport g W c w).2]
  have hdeletedQ (g : Group 𝒯 i) (W : ∀ r, H.Val r) (c : H.Center)
      (w : H.Tuple) (S : Finset H.Center) (D : Bin 𝒯 i) :
    deletedQ H mask g c W S D =
        deletedQ H mask g c (H.replaceTuple W c w) S D := by
    unfold deletedQ
    rw [hmaskedTransport g W c w S, hmassTransport g W c w S D,
      (hmaskTransport g W c w).1]
  have hdeletedU (g : Group 𝒯 i) (W : ∀ r, H.Val r) (c : H.Center)
      (w : H.Tuple) (S : Finset H.Center) (D : Bin 𝒯 i) (y : Fin (T.S.N k)) :
    deletedU H mask g c W S D y =
        deletedU H mask g c (H.replaceTuple W c w) S D y := by
    unfold deletedU
    rw [hmassTransport g W c w S D, hhitTransport W c w S,
      (hmaskTransport g W c w).2]
  have hgroupMassTransport (Geom : ProjectionGeometry κ 𝒯 i)
      (v : EvenRole 𝒯 i) (g : Group 𝒯 i) (W : ∀ r, H.Val r)
      (c : H.Center) (w : H.Tuple) (S : Finset H.Center)
      (ys : InternalLabels 𝒯 i) :
      groupLabelMass Geom v g
          (deletedQ H mask g c (H.replaceTuple W c w) S)
          (deletedU H mask g c (H.replaceTuple W c w) S) ys =
        groupLabelMass Geom v g (deletedQ H mask g c W S)
          (deletedU H mask g c W S) ys := by
    unfold groupLabelMass
    apply Finset.sum_congr rfl
    intro D hD
    rw [(hdeletedQ g W c w S D).symm]
    apply congrArg (fun z => deletedQ H mask g c W S D * z)
    apply Finset.prod_congr rfl
    intro l hl
    by_cases hgroup : Geom.groupOf (flipPos v.1 l) = g
    · simp [hgroup, (hdeletedU g W c w S D (ys l)).symm]
    · simp [hgroup]
  have hreferenceWeightTransport (v : EvenRole 𝒯 i) (c : H.Center)
      (W : ∀ r, H.Val r) (w : H.Tuple) (ys : InternalLabels 𝒯 i) :
      referenceWeight Geom H mask v c (H.replaceTuple W c w) ys =
        referenceWeight Geom H mask v c W ys := by
    unfold referenceWeight
    apply Finset.prod_congr rfl
    intro g hg
    dsimp only
    rw [hlistTransport g W c w]
    by_cases hne : (referenceLists Geom H g c W).Nonempty
    · simp only [if_pos hne]
      congr 1
      apply Finset.sum_congr rfl
      intro S hS
      exact hgroupMassTransport Geom v g W c w S ys
    · have hmask := hmaskTransport g W c w
      simp [hne, hmask.1, hmask.2]
  have hmasked_nonneg (g : Group 𝒯 i) (W : ∀ r, H.Val r)
      (J : Finset (Fin (T.S.N k))) :
      0 ≤ maskedMass H mask g W J := by
    unfold maskedMass
    apply Finset.sum_nonneg
    intro D hD
    exact mul_nonneg ((mask g W).prior_nonneg D) (sq_nonneg _)
  have hhit_nonneg (g : Group 𝒯 i) (W : ∀ r, H.Val r)
      (D : Bin 𝒯 i) (S : Finset H.Center) :
      0 ≤ hitMass H mask g W D S := by
    unfold hitMass
    apply Finset.sum_nonneg
    intro y hy
    exact (mask g W).within_nonneg D y
  have hdeletedQ_sum (g : Group 𝒯 i) (W : ∀ r, H.Val r)
      (c : H.Center) (S : Finset H.Center) :
      ∑ D, deletedQ H mask g c W S D = 1 := by
    let A := maskedMass H mask g W (listHit H W (S.erase c))
    have hA_nonneg : 0 ≤ A := hmasked_nonneg g W _
    have hnum : (∑ D, (mask g W).prior D *
        hitMass H mask g W D (S.erase c) ^ 2) = A := by
      simp [A, maskedMass, hitMass]
    by_cases hA : 0 < A
    · calc
        (∑ D, deletedQ H mask g c W S D) = A / A := by
          calc
            _ = (∑ D, (mask g W).prior D *
                hitMass H mask g W D (S.erase c) ^ 2) /
                  maskedMass H mask g W (listHit H W (S.erase c)) := by
                    simp [deletedQ, A, hA, ← Finset.sum_div]
            _ = A / A := by rw [hnum]
        _ = 1 := div_self (ne_of_gt hA)
    · have hAzero : A = 0 := le_antisymm (le_of_not_gt hA) hA_nonneg
      simp [deletedQ, A, hAzero, (mask g W).prior_sum]
  have hdeletedU_sum (g : Group 𝒯 i) (W : ∀ r, H.Val r)
      (c : H.Center) (S : Finset H.Center) (D : Bin 𝒯 i) :
      ∑ y, deletedU H mask g c W S D y = 1 := by
    let J := listHit H W (S.erase c)
    let m := hitMass H mask g W D (S.erase c)
    have hm_nonneg : 0 ≤ m := hhit_nonneg g W D (S.erase c)
    by_cases hm : 0 < m
    · calc
        (∑ y, deletedU H mask g c W S D y) =
            (∑ y ∈ J, (mask g W).within D y) / m := by
          simp [deletedU, J, m, hm, Finset.sum_ite_mem, Finset.univ_inter,
            Finset.sum_div]
        _ = m / m := by
          rw [show (∑ y ∈ J, (mask g W).within D y) = m by
            simp [m, J, hitMass]]
        _ = 1 := div_self (ne_of_gt hm)
    · have hmzero : m = 0 := le_antisymm (le_of_not_gt hm) hm_nonneg
      simp [deletedU, J, m, hm, hmzero, (mask g W).within_sum]
  have hdeletedQ_nonneg (g : Group 𝒯 i) (W : ∀ r, H.Val r)
      (c : H.Center) (S : Finset H.Center) (D : Bin 𝒯 i) :
      0 ≤ deletedQ H mask g c W S D := by
    by_cases hA : 0 < maskedMass H mask g W (listHit H W (S.erase c))
    · simpa [deletedQ, hA] using
        (div_nonneg (mul_nonneg ((mask g W).prior_nonneg D) (sq_nonneg _)) hA.le)
    · simpa [deletedQ, hA] using (mask g W).prior_nonneg D
  have hdeletedU_nonneg (g : Group 𝒯 i) (W : ∀ r, H.Val r)
      (c : H.Center) (S : Finset H.Center) (D : Bin 𝒯 i)
      (y : Fin (T.S.N k)) : 0 ≤ deletedU H mask g c W S D y := by
    by_cases hm : 0 < hitMass H mask g W D (S.erase c)
    · by_cases hy : y ∈ listHit H W (S.erase c)
      · simpa [deletedU, hm, hy] using
          (div_nonneg ((mask g W).within_nonneg D y) hm.le)
      · simp [deletedU, hm, hy]
    · simp [deletedU, hm]
      exact (mask g W).within_nonneg D y
  let RefChoice := Finset H.Center × Bin 𝒯 i
  let choiceWeight : Group 𝒯 i → H.Center → (∀ r, H.Val r) →
      RefChoice → ℝ := fun g c W sd =>
    if (referenceLists Geom H g c W).Nonempty then
      if sd.1 ∈ referenceLists Geom H g c W then
        (1 / (referenceLists Geom H g c W).card) *
          deletedQ H mask g c W sd.1 sd.2
      else 0
    else if sd.1 = ∅ then (mask g W).prior sd.2 else 0
  let choiceKernel : Group 𝒯 i → H.Center → (∀ r, H.Val r) →
      RefChoice → Fin (T.S.N k) → ℝ := fun g c W sd y =>
    if (referenceLists Geom H g c W).Nonempty then
      deletedU H mask g c W sd.1 sd.2 y
    else (mask g W).within sd.2 y
  have hchoiceWeight_nonneg (g : Group 𝒯 i) (c : H.Center)
      (W : ∀ r, H.Val r) (sd : RefChoice) :
      0 ≤ choiceWeight g c W sd := by
    by_cases hL : (referenceLists Geom H g c W).Nonempty
    · by_cases hS : sd.1 ∈ referenceLists Geom H g c W
      · have hfrac : 0 ≤ (1 : ℝ) /
            ((referenceLists Geom H g c W).card : ℝ) :=
          div_nonneg (by norm_num) (Nat.cast_nonneg _)
        simpa [choiceWeight, hL, hS] using
          (mul_nonneg hfrac (hdeletedQ_nonneg g W c sd.1 sd.2))
      · simp [choiceWeight, hL, hS]
    · by_cases hS : sd.1 = ∅
      · simp [choiceWeight, hL, hS]
        exact (mask g W).prior_nonneg sd.2
      · simp [choiceWeight, hL, hS]
  have hchoiceWeight_sum (g : Group 𝒯 i) (c : H.Center)
      (W : ∀ r, H.Val r) : ∑ sd : RefChoice, choiceWeight g c W sd = 1 := by
    classical
    rw [Fintype.sum_prod_type]
    by_cases hL : (referenceLists Geom H g c W).Nonempty
    · let Ls := referenceLists Geom H g c W
      have hcard : 0 < (Ls.card : ℝ) := by
        exact_mod_cast Finset.card_pos.mpr hL
      calc
        _ = ∑ S ∈ Ls, ∑ D, (1 / (Ls.card : ℝ)) *
              deletedQ H mask g c W S D := by
          simp [choiceWeight, Ls, hL, Finset.sum_ite_mem]
        _ = ∑ S ∈ Ls, (1 / (Ls.card : ℝ)) := by
          apply Finset.sum_congr rfl
          intro S hS
          rw [← Finset.mul_sum]
          rw [hdeletedQ_sum]
          ring
        _ = 1 := by
          rw [Finset.sum_const, nsmul_eq_mul]
          field_simp [ne_of_gt hcard]
    · calc
        _ = ∑ D, (mask g W).prior D := by
          simp [choiceWeight, hL, Finset.sum_ite_eq']
        _ = 1 := (mask g W).prior_sum
  have hchoiceKernel_nonneg (g : Group 𝒯 i) (c : H.Center)
      (W : ∀ r, H.Val r) (sd : RefChoice) (y : Fin (T.S.N k)) :
      0 ≤ choiceKernel g c W sd y := by
    by_cases hL : (referenceLists Geom H g c W).Nonempty
    · simp [choiceKernel, hL]
      exact hdeletedU_nonneg g W c sd.1 sd.2 y
    · simp [choiceKernel, hL]
      exact (mask g W).within_nonneg sd.2 y
  have hchoiceKernel_sum (g : Group 𝒯 i) (c : H.Center)
      (W : ∀ r, H.Val r) (sd : RefChoice) :
      ∑ y, choiceKernel g c W sd y = 1 := by
    by_cases hL : (referenceLists Geom H g c W).Nonempty
    · simp [choiceKernel, hL, hdeletedU_sum]
    · simp [choiceKernel, hL, (mask g W).within_sum]
  let choiceLaw : H.Center → (∀ r, H.Val r) → Group 𝒯 i → FinLaw RefChoice :=
    fun c W g => ⟨choiceWeight g c W, hchoiceWeight_nonneg g c W,
      hchoiceWeight_sum g c W⟩
  let owner : EvenRole 𝒯 i → Fin (𝒯.P i).h → Group 𝒯 i :=
    fun v l => Geom.groupOf (flipPos v.1 l)
  let makeReference : ∀ (v : EvenRole 𝒯 i) (c : H.Center)
      (W : ∀ r, H.Val r), FinLaw (InternalLabels 𝒯 i) := fun v c W =>
    FinLaw.map
      (FinLaw.bind (FinLaw.pi fun g => choiceLaw c W g)
        (fun a => FinLaw.pi fun l =>
          ⟨fun y => choiceKernel (owner v l) c W (a (owner v l)) y,
            hchoiceKernel_nonneg (owner v l) c W (a (owner v l)),
            hchoiceKernel_sum (owner v l) c W (a (owner v l))⟩))
      Prod.snd
  have hmakeReference_weight (v : EvenRole 𝒯 i) (c : H.Center)
      (W : ∀ r, H.Val r) (ys : InternalLabels 𝒯 i) :
      (makeReference v c W).w ys =
      ∑ a : Group 𝒯 i → RefChoice,
          (∏ g, choiceWeight g c W (a g)) *
            ∏ l, choiceKernel (owner v l) c W (a (owner v l)) (ys l) := by
    simp only [makeReference, choiceLaw, FinLaw.map, FinLaw.bind, FinLaw.pi]
    rw [Fintype.sum_prod_type]
    simp [eq_comm]
  have hgroupFactor (v : EvenRole 𝒯 i) (c : H.Center)
      (W : ∀ r, H.Val r) (ys : InternalLabels 𝒯 i) (g : Group 𝒯 i) :
      (∑ sd : RefChoice, choiceWeight g c W sd *
        ∏ l, if owner v l = g then choiceKernel g c W sd (ys l) else 1) =
        (if (referenceLists Geom H g c W).Nonempty then
          (∑ S ∈ referenceLists Geom H g c W,
            groupLabelMass Geom v g
              (deletedQ H mask g c W S) (deletedU H mask g c W S) ys) /
              (referenceLists Geom H g c W).card
        else groupLabelMass Geom v g (mask g W).prior (mask g W).within ys) := by
    classical
    let Ls := referenceLists Geom H g c W
    by_cases hL : Ls.Nonempty
    · have hcard : 0 < (Ls.card : ℝ) := by
        exact_mod_cast Finset.card_pos.mpr hL
      have hinner (S : Finset H.Center) :
          (∑ D, (1 / (Ls.card : ℝ)) *
            (deletedQ H mask g c W S D *
              ∏ l, if owner v l = g then deletedU H mask g c W S D (ys l) else 1)) =
            (1 / (Ls.card : ℝ)) *
              groupLabelMass Geom v g
                (deletedQ H mask g c W S) (deletedU H mask g c W S) ys := by
        calc
          _ = (1 / (Ls.card : ℝ)) * ∑ D,
              deletedQ H mask g c W S D *
                ∏ l, if owner v l = g then deletedU H mask g c W S D (ys l) else 1 := by
                rw [← Finset.mul_sum]
          _ = (1 / (Ls.card : ℝ)) *
              groupLabelMass Geom v g
                (deletedQ H mask g c W S) (deletedU H mask g c W S) ys := by
                simpa [groupLabelMass, owner]
      calc
        _ = ∑ S ∈ Ls, ∑ D,
            (1 / (Ls.card : ℝ)) *
              (deletedQ H mask g c W S D *
                ∏ l, if owner v l = g then deletedU H mask g c W S D (ys l) else 1) := by
          rw [Fintype.sum_prod_type]
          have hL' : (referenceLists Geom H g c W).Nonempty := by
            simpa [Ls] using hL
          simp [choiceWeight, choiceKernel, hL',
            Finset.sum_ite_mem_eq, Finset.sum_ite_irrel, Ls]
          apply Finset.sum_congr rfl
          intro S hS
          apply Finset.sum_congr rfl
          intro D hD
          ring
        _ = ∑ S ∈ Ls, (1 / (Ls.card : ℝ)) *
            groupLabelMass Geom v g
              (deletedQ H mask g c W S) (deletedU H mask g c W S) ys := by
          apply Finset.sum_congr rfl
          intro S hS
          exact hinner S
        _ = (1 / (Ls.card : ℝ)) * ∑ S ∈ Ls,
            groupLabelMass Geom v g
              (deletedQ H mask g c W S) (deletedU H mask g c W S) ys := by
          rw [← Finset.mul_sum]
        _ = (∑ S ∈ Ls,
            groupLabelMass Geom v g
              (deletedQ H mask g c W S) (deletedU H mask g c W S) ys) /
              (Ls.card : ℝ) := by
          field_simp [ne_of_gt hcard]
        _ = (if (referenceLists Geom H g c W).Nonempty then
              (∑ S ∈ referenceLists Geom H g c W,
                groupLabelMass Geom v g
                  (deletedQ H mask g c W S) (deletedU H mask g c W S) ys) /
                  (referenceLists Geom H g c W).card
            else groupLabelMass Geom v g (mask g W).prior (mask g W).within ys) := by
          simp [Ls, hL]
    · calc
        _ = ∑ D, (mask g W).prior D *
            ∏ l, if owner v l = g then (mask g W).within D (ys l) else 1 := by
          rw [Fintype.sum_prod_type]
          have hLs : Ls = ∅ := Finset.not_nonempty_iff_eq_empty.mp hL
          simp [choiceWeight, choiceKernel, Ls, hLs, Finset.sum_ite_eq']
        _ = groupLabelMass Geom v g (mask g W).prior (mask g W).within ys := by
          simp [groupLabelMass, owner]
        _ = (if (referenceLists Geom H g c W).Nonempty then
              (∑ S ∈ referenceLists Geom H g c W,
                groupLabelMass Geom v g
                  (deletedQ H mask g c W S) (deletedU H mask g c W S) ys) /
                  (referenceLists Geom H g c W).card
            else groupLabelMass Geom v g (mask g W).prior (mask g W).within ys) := by
          simp [Ls, hL]
  have hreference_eq (v : EvenRole 𝒯 i) (c : H.Center)
      (W : ∀ r, H.Val r) (ys : InternalLabels 𝒯 i) :
      (makeReference v c W).w ys = referenceWeight Geom H mask v c W ys := by
    rw [hmakeReference_weight]
    rw [HypercubeRamsey.Lane_q_s14_post.sum_pi_grouped
      (owner v) (fun g sd => choiceWeight g c W sd)
      (fun g sd y => choiceKernel g c W sd y) ys]
    calc
      _ = ∏ g, (if (referenceLists Geom H g c W).Nonempty then
            (∑ S ∈ referenceLists Geom H g c W,
              groupLabelMass Geom v g
                (deletedQ H mask g c W S) (deletedU H mask g c W S) ys) /
                (referenceLists Geom H g c W).card
          else groupLabelMass Geom v g (mask g W).prior (mask g W).within ys) := by
        apply Finset.prod_congr rfl
        intro g hg
        exact hgroupFactor v c W ys g
      _ = referenceWeight Geom H mask v c W ys := rfl
  have hdeletedGroup0 (v : EvenRole 𝒯 i) (g : Group 𝒯 i) (c : H.Center)
      (W : ∀ r, H.Val r) (S : Finset H.Center) (ys : InternalLabels 𝒯 i) :
      0 ≤ groupLabelMass Geom v g (deletedQ H mask g c W S)
        (deletedU H mask g c W S) ys := by
    unfold groupLabelMass
    exact Finset.sum_nonneg fun D _ => mul_nonneg (hdeletedQ_nonneg g W c S D)
      (Finset.prod_nonneg fun l _ => by
        split_ifs <;> first | exact hdeletedU_nonneg g W c S D (ys l) | norm_num)
  have hoddGroup0 (v : EvenRole 𝒯 i) (g : Group 𝒯 i)
      (W : ∀ r, H.Val r) (ys : InternalLabels 𝒯 i) :
      0 ≤ groupLabelMass Geom v g (O.q g W) (O.U g W) ys := by
    unfold groupLabelMass
    exact Finset.sum_nonneg fun D _ => mul_nonneg (O.q_nonneg g W D)
      (Finset.prod_nonneg fun l _ => by
        split_ifs <;> first | exact O.U_nonneg g W D (ys l) | norm_num)
  have hbinDeletion (v : EvenRole 𝒯 i) (g : Group 𝒯 i) (c : H.Center)
      (W : ∀ r, H.Val r) (ys : InternalLabels 𝒯 i)
      (hv : groupValid Geom H mask g W)
      (hc : c ∈ realizedList Geom H mask g W)
      (hj : 2 ≤ (Finset.univ.filter fun l => Geom.groupOf (flipPos v.1 l) = g).card) :
      groupLabelMass Geom v g (O.q g W) (O.U g W) ys ≤
        (2 * Real.exp (((Real.log 2 - 0.08 * κ.a) *
          (Finset.univ.filter fun l => Geom.groupOf (flipPos v.1 l) = g).card -
          0.24 * κ.a) * (𝒯.kScale i : ℝ))) *
        groupLabelMass Geom v g
          (deletedQ H mask g c W (realizedList Geom H mask g W))
          (deletedU H mask g c W (realizedList Geom H mask g W)) ys := by
    let S := realizedList Geom H mask g W
    let I := Finset.univ.filter fun l => Geom.groupOf (flipPos v.1 l) = g
    let A := maskedMass H mask g W (listHit H W S)
    let B := maskedMass H mask g W (listHit H W (S.erase c))
    let Z := ∑ D, tiltWeight Geom H mask g W D
    let C := 2 * Real.exp (((Real.log 2 - 0.08 * κ.a) * I.card -
      0.24 * κ.a) * (𝒯.kScale i : ℝ))
    have hsubset : listHit H W S ⊆ listHit H W (S.erase c) := by
      intro y hy
      apply Finset.mem_filter.mpr
      refine ⟨Finset.mem_univ _, ?_⟩
      intro d hd r
      exact (Finset.mem_filter.mp hy).2 d (Finset.mem_of_mem_erase hd) r
    have hmass (D : Bin 𝒯 i) : hitMass H mask g W D S ≤
        hitMass H mask g W D (S.erase c) :=
      Finset.sum_le_sum_of_subset_of_nonneg hsubset
        (fun y _ _ => (mask g W).within_nonneg D y)
    have hApos : 0 < A := lt_of_lt_of_le (Real.exp_pos _) hv.2.2.1
    have hAB : A ≤ B := by
      apply Finset.sum_le_sum
      intro D _
      exact mul_le_mul_of_nonneg_left
        (pow_le_pow_left₀ (hitMass_nonneg H mask g W D S) (hmass D) 2)
        ((mask g W).prior_nonneg D)
    have hBpos : 0 < B := hApos.trans_le hAB
    have hret : A / 2 ≤ Z := O.restricted_mass g W hv
    have hZpos : 0 < Z := lt_of_lt_of_le (half_pos hApos) hret
    have hAdel : Real.exp ((-Real.log 4 + 0.4 * κ.a) * (𝒯.kScale i : ℝ)) * B ≤ A :=
      hv.2.2.2 c hc
    have hprod (U : Bin 𝒯 i → Fin (T.S.N k) → ℝ) (D : Bin 𝒯 i) :
        (∏ l, if Geom.groupOf (flipPos v.1 l) = g then U D (ys l) else 1) =
        ∏ l ∈ I, U D (ys l) := by
      simp [I, Finset.prod_filter]
    have hterm (D : Bin 𝒯 i) :
        O.q g W D * (∏ l ∈ I, O.U g W D (ys l)) ≤
          C * (deletedQ H mask g c W S D *
            ∏ l ∈ I, deletedU H mask g c W S D (ys l)) := by
      by_cases hq : O.q g W D = 0
      · rw [hq, zero_mul]
        exact mul_nonneg (by dsimp [C]; positivity)
          (mul_nonneg (hdeletedQ_nonneg g W c S D)
            (Finset.prod_nonneg fun l _ => hdeletedU_nonneg g W c S D (ys l)))
      have hqpos : 0 < O.q g W D := lt_of_le_of_ne (O.q_nonneg g W D) (Ne.symm hq)
      have htpos : 0 < tiltWeight Geom H mask g W D := by
        have heq : O.q g W D = tiltWeight Geom H mask g W D / Z := by
          rw [O.q_eq]
          simp only [oddQ, if_pos hv]
          rfl
        rw [heq] at hqpos
        exact (div_pos_iff.mp hqpos).resolve_right (fun h => (not_lt_of_ge hZpos.le) h.2) |>.1
      have hr : restrictedBin Geom H mask g W D := by
        by_contra hn
        simp [tiltWeight, hn] at htpos
      let m := hitMass H mask g W D S
      let n := hitMass H mask g W D (S.erase c)
      have hm : 0 < m := lt_of_lt_of_le (Real.exp_pos _) hr.1
      have hn : 0 < n := hm.trans_le (hmass D)
      let f := fun l => if ys l ∈ listHit H W S then (mask g W).within D (ys l) else 0
      have hf : ∀ l ∈ I, 0 ≤ f l := by
        intro l _
        dsimp [f]
        split_ifs <;> first | exact (mask g W).within_nonneg D (ys l) | exact le_rfl
      have hU (l : Fin (𝒯.P i).h) : O.U g W D (ys l) = f l / m := by
        rw [O.U_eq]
        have hcond : groupValid Geom H mask g W ∧ 0 < oddQ Geom H mask g W D :=
          ⟨hv, by simpa only [O.q_eq] using hqpos⟩
        rw [oddU, if_pos hcond]
        dsimp only [f, m, S]
        split_ifs <;> simp
      have hUd (l : Fin (𝒯.P i).h) : f l / n ≤ deletedU H mask g c W S D (ys l) := by
        have hn' : 0 < hitMass H mask g W D (S.erase c) := hn
        by_cases hy : ys l ∈ listHit H W S
        · simp only [deletedU, if_pos hn', if_pos (hsubset hy)]
          simp only [f, if_pos hy]
          exact le_rfl
        · simp only [f, if_neg hy, zero_div]
          exact hdeletedU_nonneg g W c S D (ys l)
      have hQ : O.q g W D = (mask g W).prior D * m ^ 2 / Z := by
        rw [O.q_eq]
        simp only [oddQ, if_pos hv, tiltWeight, if_pos hr]
        rfl
      have hQd : deletedQ H mask g c W S D = (mask g W).prior D * n ^ 2 / B := by
        have hBpos' : 0 < maskedMass H mask g W (listHit H W (S.erase c)) := hBpos
        rw [deletedQ, if_pos hBpos']
      have hd := Lane_sol_s14_lik.deletion_label_product_le I
        ((mask g W).prior D) m n A B Z κ.a (𝒯.kScale i) f
        ((mask g W).prior_nonneg D) hf hm hn hBpos hZpos hAdel hret (hr.2 c hc) hj
      calc
        _ = ((mask g W).prior D * m ^ 2 / Z) * ∏ l ∈ I, f l / m := by
          rw [hQ]
          simp_rw [hU]
        _ ≤ C * (((mask g W).prior D * n ^ 2 / B) * ∏ l ∈ I, f l / n) := hd
        _ ≤ C * (deletedQ H mask g c W S D *
            ∏ l ∈ I, deletedU H mask g c W S D (ys l)) := by
          rw [← hQd]
          apply mul_le_mul_of_nonneg_left _ (by dsimp [C]; positivity)
          apply mul_le_mul_of_nonneg_left _ (hdeletedQ_nonneg g W c S D)
          exact Finset.prod_le_prod₀ (fun l hl => div_nonneg (hf l hl) hn.le)
            (fun l _ => hUd l)
    unfold groupLabelMass
    simp_rw [hprod]
    rw [Finset.mul_sum]
    exact Finset.sum_le_sum fun D _ => hterm D
  have hlam0 : 0 ≤ H.Device.lam := by
    dsimp [PrimitiveHistory.Device, patchHD]
    positivity
  let Bcount : ℝ := (2 * (𝒯.P i).h ^ 3 * H.Device.lam * (H.Device.H + 1) + 1) ^
    (𝒯.tScale i + 1)
  have hBcost : 2 * Bcount ≤ Real.exp (0.04 * κ.a * (𝒯.kScale i : ℝ)) := by
    have hnums := hconst.threshold_slack (𝒯.P i).h scales.h_large
    rcases hnums with ⟨hh, hK, hV, hLam, hlocal, hT, hloss, hpos, hfail, rest⟩
    apply Lane_sol_s14_lik.mixture_cost_le Bcount κ.a (𝒯.kScale i) κ.c5
      hconst.sliceExponent (𝒯.P i).h (𝒯.tScale i) hh (by
        have hθ := hκ.θ_rng.1
        rw [hκ.a_eq]
        positivity) scales.a_small (by positivity) hκ.c5_le (by dsimp [Bcount]; positivity)
    simpa [Bcount, PrimitiveHistory.Device, patchHD, Tiling.kScale, Tiling.tScale] using hfail
  have hlistCost (v : EvenRole 𝒯 i) (c : H.Center) (W : ∀ r, H.Val r)
      (hv : starValid Geom H mask v W) (g : Group 𝒯 i)
      (hg : v ∈ groupNeighborhood g) :
      2 * ((referenceLists Geom H g c W).card : ℝ) ≤
        Real.exp (0.04 * κ.a * (𝒯.kScale i : ℝ)) := by
    let R := (candidateRange Geom H g).filter fun d => H.present W d = true
    have hH : 0 < H.Device.H := by
      dsimp [PrimitiveHistory.Device, patchHD, topScale]
      positivity
    have hRlong : 6 ≤ H.Device.Rlong := by
      change 6 ≤ 2 * 6 * H.Device.H
      omega
    have hcounts (u : EvenRole 𝒯 i) (hu : u ∈ groupNeighborhood g)
        (j : Fin (H.Device.H + 1)) :
        (((candidateBall H (Geom.project u.1) j).filter fun d => H.present W d = true).card : ℝ) ≤
          2 * H.Device.lam := by
      apply (hv.2.1 (Geom.project u.1) ?_ j).1
      apply Finset.mem_filter.mpr
      refine ⟨Finset.mem_image.mpr ⟨u, Finset.mem_univ _, rfl⟩, ?_⟩
      exact (Geom.projected_distance g u v hu hg).trans hRlong
    have hR : (R.card : ℝ) ≤ 2 * (𝒯.P i).h ^ 3 * H.Device.lam * (H.Device.H + 1) := by
      dsimp [R, candidateRange]
      rw [Finset.filter_biUnion]
      have houter := Finset.card_biUnion_le (s := groupNeighborhood g)
        (t := fun u => (Finset.univ.biUnion fun j => candidateBall H (Geom.project u.1) j).filter
          fun d => H.present W d = true)
      have houterR :
          (((groupNeighborhood g).biUnion fun u =>
            (Finset.univ.biUnion fun j => candidateBall H (Geom.project u.1) j).filter
              fun d => H.present W d = true).card : ℝ) ≤
            ∑ u ∈ groupNeighborhood g,
              (((Finset.univ.biUnion fun j => candidateBall H (Geom.project u.1) j).filter
                fun d => H.present W d = true).card : ℝ) := by exact_mod_cast houter
      apply houterR.trans
      calc
        _ ≤ ∑ _u ∈ groupNeighborhood g, (H.Device.H + 1) * (2 * H.Device.lam) := by
          apply Finset.sum_le_sum
          intro u hu
          rw [Finset.filter_biUnion]
          have hinner := Finset.card_biUnion_le
            (s := (Finset.univ : Finset (Fin (H.Device.H + 1))))
            (t := fun j => (candidateBall H (Geom.project u.1) j).filter fun d => H.present W d = true)
          have hinnerR :
              ((Finset.univ.biUnion fun j =>
                (candidateBall H (Geom.project u.1) j).filter fun d => H.present W d = true).card : ℝ) ≤
                ∑ j : Fin (H.Device.H + 1),
                  (((candidateBall H (Geom.project u.1) j).filter fun d => H.present W d = true).card : ℝ) := by
            exact_mod_cast hinner
          exact hinnerR.trans (by
            calc
              _ ≤ ∑ _j : Fin (H.Device.H + 1), 2 * H.Device.lam :=
                Finset.sum_le_sum fun j _ => hcounts u hu j
              _ = _ := by simp)
        _ = (groupNeighborhood g).card * ((H.Device.H + 1) * (2 * H.Device.lam)) := by simp
        _ ≤ (𝒯.P i).h ^ 3 * ((H.Device.H + 1) * (2 * H.Device.lam)) := by
          apply mul_le_mul_of_nonneg_right _ (by positivity)
          have hcard : ((groupNeighborhood g).card : ℝ) ≤ (𝒯.P i).h ^ 2 := by
            exact_mod_cast neighborhood_card Geom g
          have hh : (1 : ℝ) ≤ (𝒯.P i).h := by
            exact_mod_cast (by have h := (hconst.threshold_slack _ scales.h_large).1; omega : 1 ≤ (𝒯.P i).h)
          have hpow : ((𝒯.P i).h : ℝ) ^ 2 ≤ ((𝒯.P i).h : ℝ) ^ 3 := by
            nlinarith only [mul_nonneg (sq_nonneg ((𝒯.P i).h : ℝ)) (sub_nonneg.mpr hh)]
          exact hcard.trans hpow
        _ = _ := by ring
    have hsub : referenceLists Geom H g c W ⊆
        R.powerset.filter fun S => S.card ≤ 𝒯.tScale i := by
      intro S hS
      obtain ⟨hS, hc⟩ := (Finset.mem_filter.mp hS).2
      apply Finset.mem_filter.mpr
      refine ⟨Finset.mem_powerset.mpr ?_, hS.2.1⟩
      intro d hd
      exact Finset.mem_filter.mpr (hS.2.2 d hd)
    have hn := (Finset.card_le_card hsub).trans (short_list_count R (𝒯.tScale i))
    have hcount : ((referenceLists Geom H g c W).card : ℝ) ≤ Bcount := by
      have hcast : ((referenceLists Geom H g c W).card : ℝ) ≤
          ((R.card : ℝ) + 1) ^ (𝒯.tScale i + 1) := by exact_mod_cast hn
      exact hcast.trans (pow_le_pow_left₀ (by positivity) (by linarith [hR]) _)
    exact (mul_le_mul_of_nonneg_left hcount (by norm_num)).trans hBcost
  have hlabelMarginal (v : EvenRole 𝒯 i) (W : ∀ r, H.Val r)
      (ys : InternalLabels 𝒯 i) :
      (refLaw Geom H mask O W).pr (fun ω => nbrLabels v.1 ω.2 = ys) =
        ∏ g, groupLabelMass Geom v g (O.q g W) (O.U g W) ys := by
    have hinj : Function.Injective (flipPos v.1) := by
      intro l l' h
      by_contra hn
      have hb := congrFun h l
      simp [flipPos, hn] at hb
    have hquery (d : Group 𝒯 i → Bin 𝒯 i) :
        (FinLaw.pi fun z : IWord 𝒯 i =>
          (⟨O.U (Geom.groupOf z) W (d (Geom.groupOf z)), O.U_nonneg _ _ _, O.U_sum _ _ _⟩ :
            FinLaw (Fin (T.S.N k)))).pr (fun lab => nbrLabels v.1 lab = ys) =
          ∏ l, O.U (Geom.groupOf (flipPos v.1 l)) W
            (d (Geom.groupOf (flipPos v.1 l))) (ys l) :=
      Lane_sol_s14_lik.pi_query_probability _ (flipPos v.1) hinj ys
    simp only [refLaw, internalRefLaw, FinLaw.pr, FinLaw.bind, FinLaw.pi]
    rw [Fintype.sum_prod_type]
    calc
      _ = ∑ d : Group 𝒯 i → Bin 𝒯 i, (∏ g, O.q g W (d g)) *
          (FinLaw.pi fun z : IWord 𝒯 i =>
            (⟨O.U (Geom.groupOf z) W (d (Geom.groupOf z)), O.U_nonneg _ _ _, O.U_sum _ _ _⟩ :
              FinLaw (Fin (T.S.N k)))).pr (fun lab => nbrLabels v.1 lab = ys) := by
        apply Finset.sum_congr rfl
        intro d _
        unfold FinLaw.pr
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro lab _
        split_ifs <;> simp [FinLaw.pi]
      _ = ∑ d : Group 𝒯 i → Bin 𝒯 i, (∏ g, O.q g W (d g)) *
          ∏ l, O.U (Geom.groupOf (flipPos v.1 l)) W
            (d (Geom.groupOf (flipPos v.1 l))) (ys l) := by simp_rw [hquery]
      _ = _ := Lane_q_s14_post.sum_pi_grouped
        (fun l => Geom.groupOf (flipPos v.1 l)) (fun g => O.q g W)
        (fun g => O.U g W) ys
  have howner (v : EvenRole 𝒯 i) (g : Group 𝒯 i) (l : Fin (𝒯.P i).h) :
      Geom.groupOf (flipPos v.1 l) = g ↔ flipPos v.1 l ∈ groupFiber g := by
    have hodd : ¬ IsEvenRole (flipPos v.1 l) := by
      let A : Finset (Fin (𝒯.P i).h) := Finset.univ.filter fun j => v.1 j = true
      let B : Finset (Fin (𝒯.P i).h) := Finset.univ.filter fun j => flipPos v.1 l j = true
      have hEvenA : Even A.card := by simpa [A, IsEvenRole] using v.2
      change ¬ Even B.card
      cases hbit : v.1 l with
      | true =>
        have hlA : l ∈ A := Finset.mem_filter.mpr ⟨Finset.mem_univ _, hbit⟩
        have hBA : B = A.erase l := by
          ext j
          by_cases hj : j = l
          · subst j; simp [A, B, flipPos, hbit]
          · simp [A, B, flipPos, hj, Ne.symm hj, hbit]
        intro hEvenB
        have hEvenSub : Even (A.card - 1) := by
          rw [← Finset.card_erase_of_mem hlA, ← hBA]
          exact hEvenB
        rcases hEvenA with ⟨a, ha⟩
        rcases hEvenSub with ⟨b, hb⟩
        have hposA : 0 < A.card := Finset.card_pos.mpr ⟨l, hlA⟩
        omega
      | false =>
        have hlA : l ∉ A := by simp [A, hbit]
        have hBA : B = insert l A := by
          ext j
          by_cases hj : j = l
          · subst j; simp [A, B, flipPos, hbit]
          · simp [A, B, flipPos, hj, Ne.symm hj, hbit]
        intro hEvenB
        have hEvenIns : Even (A.card + 1) := by
          rw [← Finset.card_insert_of_notMem hlA, ← hBA]
          exact hEvenB
        rcases hEvenA with ⟨a, ha⟩
        rcases hEvenIns with ⟨b, hb⟩
        omega
    constructor
    · intro heq
      rw [← heq]
      exact Geom.groupOf_spec _ hodd
    · intro hmem
      obtain ⟨g₀, hg₀, huniq⟩ := Geom.partition _ hodd
      exact (huniq _ (Geom.groupOf_spec _ hodd)).trans (huniq g hmem).symm
  have hcard (v : EvenRole 𝒯 i) (g : Group 𝒯 i) :
      (Finset.univ.filter fun l => Geom.groupOf (flipPos v.1 l) = g).card =
        Geom.multiplicity v g := by
    rw [Geom.multiplicity_eq]
    congr 1
    ext l
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    exact howner v g l
  refine ⟨{
    reference := makeReference
    reference_eq := hreference_eq
    independent := ?_
    domination := ?_
  }⟩
  · intro v c W w
    have hw : (makeReference v c (H.replaceTuple W c w)).w =
        (makeReference v c W).w := by
      funext ys
      rw [hreference_eq, hreference_eq]
      exact hreferenceWeightTransport v c W w ys
    cases hleft : makeReference v c (H.replaceTuple W c w) with
    | mk wl hwl hsl =>
      cases hright : makeReference v c W with
      | mk wr hwr hsr =>
        simp only [FinLaw.mk.injEq]
        simpa [hleft, hright] using hw
  · intro v c W w ys
    let W' := H.replaceTuple W c w
    let mix := fun g : Group 𝒯 i =>
      if (referenceLists Geom H g c W').Nonempty then
        (∑ S ∈ referenceLists Geom H g c W', groupLabelMass Geom v g
          (deletedQ H mask g c W' S) (deletedU H mask g c W' S) ys) /
          (referenceLists Geom H g c W').card
      else groupLabelMass Geom v g (mask g W').prior (mask g W').within ys
    have hmix0 (g : Group 𝒯 i) : 0 ≤ mix g := by
      dsimp [mix]
      split_ifs
      · apply div_nonneg _ (by positivity)
        exact Finset.sum_nonneg fun S _ => Finset.sum_nonneg fun D _ =>
          mul_nonneg (hdeletedQ_nonneg g W' c S D)
            (Finset.prod_nonneg fun l _ => by
              split_ifs <;> first | exact hdeletedU_nonneg g W' c S D (ys l) | norm_num)
      · exact Finset.sum_nonneg fun D _ =>
          mul_nonneg ((mask g W').prior_nonneg D)
            (Finset.prod_nonneg fun l _ => by
              split_ifs <;> first | exact (mask g W').within_nonneg D (ys l) | norm_num)
    have href0 : 0 ≤ referenceWeight Geom H mask v c W ys := by
      rw [← hreference_eq]
      exact (makeReference v c W).nonneg ys
    by_cases hv : selected Geom H mask W' v = some c ∧ starValid Geom H mask v W'
    · have hgroup (g : Group 𝒯 i) :
          groupLabelMass Geom v g (O.q g W') (O.U g W') ys ≤
            Real.exp ((Real.log 2 - 0.08 * κ.a) * (𝒯.kScale i : ℝ) *
              Geom.multiplicity v g) * mix g := by
        by_cases hj : Geom.multiplicity v g = 0
        · have hnone (l : Fin (𝒯.P i).h) : Geom.groupOf (flipPos v.1 l) ≠ g := by
            intro hl
            have hmem : l ∈ Finset.univ.filter fun l => Geom.groupOf (flipPos v.1 l) = g := by simp [hl]
            have hpos := Finset.card_pos.mpr ⟨l, hmem⟩
            rw [hcard, hj] at hpos
            omega
          have hact : groupLabelMass Geom v g (O.q g W') (O.U g W') ys = 1 := by
            simp [groupLabelMass, hnone, O.q_sum]
          have hmix : mix g = 1 := by
            dsimp [mix]
            split_ifs with hL
            · have hLs : (referenceLists Geom H g c W').card ≠ 0 :=
                (Finset.card_pos.mpr hL).ne'
              simp [groupLabelMass, hnone, hdeletedQ_sum, hLs]
            · simp [groupLabelMass, hnone, (mask g W').prior_sum]
          simp [hj, hact, hmix]
        have hpos : 0 < Geom.multiplicity v g := Nat.pos_of_ne_zero hj
        have hg : v ∈ groupNeighborhood g := by
          have hfilter : 0 < (Finset.univ.filter fun l => Geom.groupOf (flipPos v.1 l) = g).card := by
            rw [hcard]; exact hpos
          obtain ⟨l, hl⟩ := Finset.card_pos.mp hfilter
          exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, l,
            (howner v g l).mp (Finset.mem_filter.mp hl).2⟩
        have hvalid := hv.2.1 g hg
        let S := realizedList Geom H mask g W'
        have hcS : c ∈ S := Finset.mem_filter.mpr ⟨Finset.mem_univ _, v, hg, hv.1⟩
        have hS : S ∈ referenceLists Geom H g c W' :=
          Finset.mem_filter.mpr ⟨Finset.mem_univ _, hvalid.2.1, hcS⟩
        have hL : (referenceLists Geom H g c W').Nonempty := ⟨S, hS⟩
        have hLp : (0 : ℝ) < (referenceLists Geom H g c W').card := by
          exact_mod_cast Finset.card_pos.mpr hL
        have hmix : groupLabelMass Geom v g
            (deletedQ H mask g c W' S) (deletedU H mask g c W' S) ys ≤
              (referenceLists Geom H g c W').card * mix g := by
          have hs := Finset.single_le_sum (s := referenceLists Geom H g c W')
            (fun S _ => hdeletedGroup0 v g c W' S ys) hS
          have heq : (referenceLists Geom H g c W').card * mix g =
              ∑ S ∈ referenceLists Geom H g c W', groupLabelMass Geom v g
                (deletedQ H mask g c W' S) (deletedU H mask g c W' S) ys := by
            dsimp [mix]
            rw [if_pos hL]
            field_simp [hLp.ne']
          rw [heq]
          exact hs
        let C := 2 * Real.exp (((Real.log 2 - 0.08 * κ.a) *
          Geom.multiplicity v g - 0.24 * κ.a) * (𝒯.kScale i : ℝ))
        have hbin : groupLabelMass Geom v g (O.q g W') (O.U g W') ys ≤
            C * groupLabelMass Geom v g
              (deletedQ H mask g c W' S) (deletedU H mask g c W' S) ys := by
          have h := hbinDeletion v g c W' ys hvalid hcS (by
            rw [hcard]; exact Geom.multiplicity_lower v g hpos)
          simpa only [hcard] using h
        have hC : C * (referenceLists Geom H g c W').card ≤
            Real.exp ((Real.log 2 - 0.08 * κ.a) * (𝒯.kScale i : ℝ) * Geom.multiplicity v g) := by
          have ha0 : 0 ≤ κ.a := by
            rw [hκ.a_eq]
            exact div_nonneg hκ.θ_rng.1.le (by norm_num)
          calc
            _ = (2 * ((referenceLists Geom H g c W').card : ℝ)) *
                Real.exp (((Real.log 2 - 0.08 * κ.a) *
                  Geom.multiplicity v g - 0.24 * κ.a) * (𝒯.kScale i : ℝ)) := by dsimp [C]; ring
            _ ≤ Real.exp (0.04 * κ.a * (𝒯.kScale i : ℝ)) *
                Real.exp (((Real.log 2 - 0.08 * κ.a) *
                  Geom.multiplicity v g - 0.24 * κ.a) * (𝒯.kScale i : ℝ)) :=
              mul_le_mul_of_nonneg_right (hlistCost v c W' hv.2 g hg) (Real.exp_pos _).le
            _ = Real.exp (0.04 * κ.a * (𝒯.kScale i : ℝ) +
                ((Real.log 2 - 0.08 * κ.a) * Geom.multiplicity v g - 0.24 * κ.a) *
                  (𝒯.kScale i : ℝ)) := (Real.exp_add _ _).symm
            _ ≤ _ := by
              apply Real.exp_le_exp.mpr
              nlinarith [show (0 : ℝ) ≤ 𝒯.kScale i by positivity]
        calc
          _ ≤ C * groupLabelMass Geom v g
              (deletedQ H mask g c W' S) (deletedU H mask g c W' S) ys := hbin
          _ ≤ C * ((referenceLists Geom H g c W').card * mix g) :=
            mul_le_mul_of_nonneg_left hmix (by dsimp [C]; positivity)
          _ = (C * (referenceLists Geom H g c W').card) * mix g := by ring
          _ ≤ _ := mul_le_mul_of_nonneg_right hC (hmix0 g)
      have hprod : (∏ g, groupLabelMass Geom v g (O.q g W') (O.U g W') ys) ≤
          ∏ g, Real.exp ((Real.log 2 - 0.08 * κ.a) * (𝒯.kScale i : ℝ) *
            Geom.multiplicity v g) * mix g :=
        Finset.prod_le_prod₀ (fun g _ => hoddGroup0 v g W' ys) (fun g _ => hgroup g)
      have hexp : (∏ g, Real.exp ((Real.log 2 - 0.08 * κ.a) * (𝒯.kScale i : ℝ) *
          Geom.multiplicity v g)) =
          Real.exp ((Real.log 2 - 0.08 * κ.a) * (𝒯.kScale i : ℝ) * (𝒯.P i).h) := by
        rw [← Real.exp_sum]
        congr 1
        rw [← Finset.mul_sum, ← Nat.cast_sum, Geom.multiplicity_sum]
      rw [Finset.prod_mul_distrib, hexp] at hprod
      have hmixWeight : (∏ g, mix g) = referenceWeight Geom H mask v c W ys := by
        change referenceWeight Geom H mask v c W' ys = _
        exact hreferenceWeightTransport v c W w ys
      rw [hmixWeight] at hprod
      have hsub : subLikelihood Geom H mask O v c W w ys =
          (refLaw Geom H mask O W').pr (fun ω => nbrLabels v.1 ω.2 = ys) := by
        have hgate : selected Geom H mask (H.replaceTuple W c w) v = some c ∧
            starValid Geom H mask v (H.replaceTuple W c w) := hv
        rw [subLikelihood, if_pos hgate]
      rw [hsub, hlabelMarginal]
      apply hprod.trans
      apply mul_le_mul_of_nonneg_right _ href0
      apply Real.exp_le_exp.mpr
      have ha0 : 0 ≤ κ.a := by
        rw [hκ.a_eq]
        exact div_nonneg hκ.θ_rng.1.le (by norm_num)
      have hK0 : (0 : ℝ) ≤ 𝒯.kScale i := by positivity
      have hh0 : (0 : ℝ) ≤ (𝒯.P i).h := by positivity
      nlinarith [mul_nonneg ha0 (mul_nonneg hK0 hh0)]
    · have hgate : ¬ (selected Geom H mask (H.replaceTuple W c w) v = some c ∧
          starValid Geom H mask v (H.replaceTuple W c w)) := hv
      rw [subLikelihood, if_neg hgate]
      exact mul_nonneg (Real.exp_pos _).le href0

section Rows

variable {κ : CConsts} {T : Stage} {k : ℕ} {𝒯 : Tiling κ T k}
  {i : Fin 𝒯.m} {mesh : Mesh 𝒯}

noncomputable def predictiveMass (Geom : ProjectionGeometry κ 𝒯 i)
    (H : PrimitiveHistory κ 𝒯 i mesh) (mask : Masks H) (O : OddKernels Geom H mask)
    (v : EvenRole 𝒯 i) (c : H.Center) (W : ∀ r, H.Val r) (ys : InternalLabels 𝒯 i) : ℝ :=
  ∑ w, (H.tuplePrior (H.cornerOf W c)).w w * subLikelihood Geom H mask O v c W w ys

noncomputable def posteriorMean (Geom : ProjectionGeometry κ 𝒯 i)
    (H : PrimitiveHistory κ 𝒯 i mesh) (mask : Masks H) (O : OddKernels Geom H mask)
    (v : EvenRole 𝒯 i) (c : H.Center) (W : ∀ r, H.Val r)
    (ys : InternalLabels 𝒯 i) (x : Fin (T.S.N k)) : ℝ :=
  ∑ w, ((H.tuplePrior (H.cornerOf W c)).w w * subLikelihood Geom H mask O v c W w ys /
    predictiveMass Geom H mask O v c W ys) *
      ((∑ r, if w r = x then (1 : ℝ) else 0) / 𝒯.kScale i)

noncomputable def retainedLabels (Geom : ProjectionGeometry κ 𝒯 i)
    (H : PrimitiveHistory κ 𝒯 i mesh) (mask : Masks H) (O : OddKernels Geom H mask)
    (v : EvenRole 𝒯 i) (c : H.Center) (W : ∀ r, H.Val r) (ys : InternalLabels 𝒯 i) :=
  Finset.univ.filter fun x => (T.S.N k : ℝ) * posteriorMean Geom H mask O v c W ys x ≤
    2 ^ (𝒯.P i).h * Real.exp (-0.02 * κ.a * (𝒯.P i).h)

/-- Uncharged corner outcomes may be unusable. They produce zero rows; every
charged outcome has an active corner and its `2/M` prior cap. -/
def UsableCorner (H : PrimitiveHistory κ 𝒯 i mesh) (W : ∀ r, H.Val r) (c : H.Center) : Prop :=
  (H.prior (H.cornerOf W c)).SupportedIn (mesh.corner (H.cornerOf W c) i) ∧
    ∀ x, (H.prior (H.cornerOf W c)).w x ≤ 2 / (𝒯.P i).M

noncomputable def posteriorGate (Geom : ProjectionGeometry κ 𝒯 i)
    (H : PrimitiveHistory κ 𝒯 i mesh) (mask : Masks H) (O : OddKernels Geom H mask)
    (L : LikelihoodData Geom H mask O) (v : EvenRole 𝒯 i) (c : H.Center)
    (W : ∀ r, H.Val r) (ys : InternalLabels 𝒯 i) : Prop :=
  selected Geom H mask W v = some c ∧ starValid Geom H mask v W ∧ UsableCorner H W c ∧
    0 < predictiveMass Geom H mask O v c W ys ∧
    Real.exp (-0.01 * κ.a * (𝒯.kScale i : ℝ) * (𝒯.P i).h) * (L.reference v c W).w ys ≤
      predictiveMass Geom H mask O v c W ys

/-- The normalized truncated posterior, zero on exactly the failed gates. -/
noncomputable def posteriorRow (Geom : ProjectionGeometry κ 𝒯 i)
    (H : PrimitiveHistory κ 𝒯 i mesh) (mask : Masks H) (O : OddKernels Geom H mask)
    (L : LikelihoodData Geom H mask O) (v : EvenRole 𝒯 i) (W : ∀ r, H.Val r)
    (ys : InternalLabels 𝒯 i) (x : Fin (T.S.N k)) : ℝ :=
  match selected Geom H mask W v with
  | none => 0
  | some c => if posteriorGate Geom H mask O L v c W ys ∧
      x ∈ retainedLabels Geom H mask O v c W ys then
      posteriorMean Geom H mask O v c W ys x /
        ∑ z ∈ retainedLabels Geom H mask O v c W ys, posteriorMean Geom H mask O v c W ys z
    else 0

structure EvenRows (Geom : ProjectionGeometry κ 𝒯 i)
    (H : PrimitiveHistory κ 𝒯 i mesh) (mask : Masks H) (O : OddKernels Geom H mask)
    (L : LikelihoodData Geom H mask O) where
  σ : EvenRole 𝒯 i → (∀ r, H.Val r) → InternalLabels 𝒯 i → Fin (T.S.N k) → ℝ
  σ_eq : σ = posteriorRow Geom H mask O L
  retained_mass : ∀ v c W ys, posteriorGate Geom H mask O L v c W ys →
    κ.a / 200 ≤ ∑ x ∈ retainedLabels Geom H mask O v c W ys,
      posteriorMean Geom H mask O v c W ys x
  nonneg : ∀ v W ys x, 0 ≤ σ v W ys x
  probability : ∀ v W ys, σ v W ys ≠ 0 → ∑ x, σ v W ys x = 1
  cap : ∀ v W ys x, (T.S.N k : ℝ) * σ v W ys x ≤
    2 ^ (𝒯.P i).h * Real.exp (-500 * 𝒯.gain i)

end Rows

/-- P14.1h: the exact posterior construction, its retained mass and S3. -/
theorem posterior_even_rows (κ : CConsts) (hκ : κ.Admissible)
    {T : Stage} {k : ℕ} {𝒯 : Tiling κ T k} (h𝒯 : Tiling.Valid 𝒯)
    {i : Fin 𝒯.m} {mesh : Mesh 𝒯} (scales : PatchScales 𝒯 i)
    (Geom : ProjectionGeometry κ 𝒯 i) (H : PrimitiveHistory κ 𝒯 i mesh)
    (mask : Masks H) (O : OddKernels Geom H mask) (L : LikelihoodData Geom H mask O) :
    Nonempty (EvenRows Geom H mask O L) := by
  classical
  have ha : 0 < κ.a := by
    rw [hκ.a_eq]
    exact div_pos hκ.θ_rng.1 (by norm_num)
  have hsub0 : ∀ (v : EvenRole 𝒯 i) c (W : ∀ r, H.Val r) w ys,
      0 ≤ subLikelihood Geom H mask O v c W w ys := by
    intro v c W w ys
    dsimp [subLikelihood]
    split_ifs
    · unfold FinLaw.pr
      apply Finset.sum_nonneg
      intro ω hω
      split_ifs
      · exact (refLaw Geom H mask O (H.replaceTuple W c w)).nonneg ω
      · exact le_rfl
    · exact le_rfl
  have hpred0 : ∀ (v : EvenRole 𝒯 i) c (W : ∀ r, H.Val r) ys,
      0 ≤ predictiveMass Geom H mask O v c W ys := by
    intro v c W ys
    unfold predictiveMass
    apply Finset.sum_nonneg
    intro w hw
    exact mul_nonneg ((H.tuplePrior (H.cornerOf W c)).nonneg w) (hsub0 v c W w ys)
  have hpm0 : ∀ (v : EvenRole 𝒯 i) c (W : ∀ r, H.Val r) ys x,
      0 ≤ posteriorMean Geom H mask O v c W ys x := by
    intro v c W ys x
    unfold posteriorMean
    apply Finset.sum_nonneg
    intro w hw
    apply mul_nonneg
    · exact div_nonneg
        (mul_nonneg ((H.tuplePrior (H.cornerOf W c)).nonneg w) (hsub0 v c W w ys))
        (hpred0 v c W ys)
    · apply div_nonneg
      · apply Finset.sum_nonneg
        intro r hr
        split_ifs <;> positivity
      · exact_mod_cast (Nat.zero_le (𝒯.kScale i))
  have hretained : ∀ (v : EvenRole 𝒯 i) c (W : ∀ r, H.Val r) ys,
      posteriorGate Geom H mask O L v c W ys →
        κ.a / 200 ≤ ∑ x ∈ retainedLabels Geom H mask O v c W ys,
          posteriorMean Geom H mask O v c W ys x := by
    intro v c W ys hg
    rcases hg with ⟨_, _, _, hpred, _⟩
    have hpatch : 0 < (𝒯.P i).h := lt_of_lt_of_le hκ.h0_pos scales.h_large
    have hk : 0 < 𝒯.kScale i := by
      change 0 < sliceK κ (𝒯.P i).h
      unfold sliceK
      apply Nat.ceil_pos.mpr
      exact Real.rpow_pos_of_pos (by exact_mod_cast hpatch) _
    have hcoordinate_count (w : H.Tuple) :
        (∑ x, ∑ r, if w r = x then (1 : ℝ) else 0) = (𝒯.kScale i : ℝ) := by
      rw [Finset.sum_comm]
      simp [Finset.sum_ite_eq', eq_comm]
    have hscore (w : H.Tuple) :
        (∑ x, (∑ r, if w r = x then (1 : ℝ) else 0) /
          (𝒯.kScale i : ℝ)) = 1 := by
      rw [← Finset.sum_div, hcoordinate_count]
      exact div_self (by exact_mod_cast hk.ne')
    have htotalMean :
        ∑ x, posteriorMean Geom H mask O v c W ys x = 1 := by
      unfold posteriorMean
      calc
        _ = ∑ w, ((H.tuplePrior (H.cornerOf W c)).w w *
              subLikelihood Geom H mask O v c W w ys /
                predictiveMass Geom H mask O v c W ys) *
              (∑ x, (∑ r, if w r = x then (1 : ℝ) else 0) /
                (𝒯.kScale i : ℝ)) := by
          rw [Finset.sum_comm]
          apply Finset.sum_congr rfl
          intro w hw
          rw [← Finset.mul_sum]
        _ = ∑ w, ((H.tuplePrior (H.cornerOf W c)).w w *
              subLikelihood Geom H mask O v c W w ys /
                predictiveMass Geom H mask O v c W ys) * 1 := by
          apply Finset.sum_congr rfl
          intro w hw
          rw [hscore]
        _ = ∑ w, (H.tuplePrior (H.cornerOf W c)).w w *
              subLikelihood Geom H mask O v c W w ys /
                predictiveMass Geom H mask O v c W ys := by
          simp
        _ = (∑ w, (H.tuplePrior (H.cornerOf W c)).w w *
              subLikelihood Geom H mask O v c W w ys) /
                predictiveMass Geom H mask O v c W ys := by
          rw [← Finset.sum_div]
        _ = predictiveMass Geom H mask O v c W ys /
              predictiveMass Geom H mask O v c W ys := rfl
        _ = 1 := div_self hpred.ne'
    have _ := htotalMean
    sorry
  refine ⟨{
    σ := posteriorRow Geom H mask O L
    σ_eq := rfl
    retained_mass := hretained
    nonneg := ?_
    probability := ?_
    cap := ?_
  }⟩
  · intro v W ys x
    cases hs : selected Geom H mask W v with
    | none => simp [posteriorRow, hs]
    | some c =>
      by_cases hg : posteriorGate Geom H mask O L v c W ys
      · by_cases hx : x ∈ retainedLabels Geom H mask O v c W ys
        · let den := ∑ z ∈ retainedLabels Geom H mask O v c W ys,
            posteriorMean Geom H mask O v c W ys z
          have hm := hretained v c W ys hg
          have hdenpos : 0 < den := by
            dsimp [den]
            exact lt_of_lt_of_le (div_pos ha (by norm_num)) hm
          simpa [posteriorRow, hs, hg, hx, den] using
            (div_nonneg (hpm0 v c W ys x) hdenpos.le)
        · simp [posteriorRow, hs, hg, hx] <;> positivity
      · simp [posteriorRow, hs, hg] <;> positivity
  · intro v W ys hσ
    have hsome : ∃ x, posteriorRow Geom H mask O L v W ys x ≠ 0 := by
      by_contra hnone
      apply hσ
      funext x
      by_contra hx
      exact hnone ⟨x, hx⟩
    rcases hsome with ⟨x₀, hx₀⟩
    cases hs : selected Geom H mask W v with
    | none => simp [posteriorRow, hs] at hx₀
    | some c =>
      have hg : posteriorGate Geom H mask O L v c W ys := by
        by_contra hnot
        simp [posteriorRow, hs, hnot] at hx₀
      let S := retainedLabels Geom H mask O v c W ys
      let den := ∑ z ∈ S, posteriorMean Geom H mask O v c W ys z
      have hden : κ.a / 200 ≤ den := by
        dsimp [den, S]
        exact hretained v c W ys hg
      have hdenpos : 0 < den := lt_of_lt_of_le (div_pos ha (by norm_num)) hden
      have hsum : (∑ x, posteriorRow Geom H mask O L v W ys x) = 1 := by
        calc
          _ = ∑ x, if x ∈ S then posteriorMean Geom H mask O v c W ys x / den else 0 := by
            simp [posteriorRow, hs, hg, S, den]
          _ = ∑ x ∈ S, posteriorMean Geom H mask O v c W ys x / den := by
            simp [Finset.sum_ite_mem]
          _ = den / den := by
            rw [← Finset.sum_div]
          _ = 1 := div_self hdenpos.ne'
      simpa [posteriorRow, hs] using hsum
  · intro v W ys x
    cases hs : selected Geom H mask W v with
    | none => simp [posteriorRow, hs]; positivity
    | some c =>
      by_cases hg : posteriorGate Geom H mask O L v c W ys
      · by_cases hx : x ∈ retainedLabels Geom H mask O v c W ys
        · let den := ∑ z ∈ retainedLabels Geom H mask O v c W ys,
            posteriorMean Geom H mask O v c W ys z
          have hm := hretained v c W ys hg
          have hdenpos : 0 < den := by
            dsimp [den]
            exact lt_of_lt_of_le (div_pos ha (by norm_num)) hm
          have hfactor : 1 ≤ (200 / κ.a) * den := by
            have hcancel : (200 / κ.a) * (κ.a / 200) = 1 := by
              field_simp [ne_of_gt ha]
            calc
              1 = (200 / κ.a) * (κ.a / 200) := hcancel.symm
              _ ≤ (200 / κ.a) * den :=
                mul_le_mul_of_nonneg_left hm (by positivity)
          have hratio :
              posteriorMean Geom H mask O v c W ys x / den ≤
                (200 / κ.a) * posteriorMean Geom H mask O v c W ys x := by
            apply (div_le_iff₀ hdenpos).2
            calc
              posteriorMean Geom H mask O v c W ys x =
                  1 * posteriorMean Geom H mask O v c W ys x := by ring
              _ ≤ ((200 / κ.a) * den) * posteriorMean Geom H mask O v c W ys x :=
                mul_le_mul_of_nonneg_right hfactor (hpm0 v c W ys x)
              _ = (200 / κ.a) * posteriorMean Geom H mask O v c W ys x * den := by ring
          have hthreshold := (Finset.mem_filter.mp hx).2
          have hrow : posteriorRow Geom H mask O L v W ys x =
              posteriorMean Geom H mask O v c W ys x / den := by
            simp [posteriorRow, hs, hg, hx, den]
          calc
            (T.S.N k : ℝ) * posteriorRow Geom H mask O L v W ys x ≤
                (T.S.N k : ℝ) * ((200 / κ.a) * posteriorMean Geom H mask O v c W ys x) := by
                  rw [hrow]
                  exact mul_le_mul_of_nonneg_left hratio (by positivity)
            _ = (200 / κ.a) * ((T.S.N k : ℝ) *
                posteriorMean Geom H mask O v c W ys x) := by ring
            _ ≤ ((200 / κ.a) * 2 ^ (𝒯.P i).h) *
                Real.exp (-0.02 * κ.a * (𝒯.P i).h) := by
                  calc
                    (200 / κ.a) * ((T.S.N k : ℝ) *
                        posteriorMean Geom H mask O v c W ys x) ≤
                        (200 / κ.a) *
                          (2 ^ (𝒯.P i).h * Real.exp (-0.02 * κ.a * (𝒯.P i).h)) :=
                            mul_le_mul_of_nonneg_left hthreshold (by positivity)
                    _ = ((200 / κ.a) * 2 ^ (𝒯.P i).h) *
                        Real.exp (-0.02 * κ.a * (𝒯.P i).h) := by ring
            _ ≤ 2 ^ (𝒯.P i).h * Real.exp (-500 * 𝒯.gain i) := scales.truncation_cap
        · simp [posteriorRow, hs, hg, hx] <;> exact le_of_lt (Real.exp_pos _)
      · simp [posteriorRow, hs, hg] <;> exact le_of_lt (Real.exp_pos _)

section Conclusions

variable {κ : CConsts} {T : Stage} {k : ℕ} {𝒯 : Tiling κ T k}
  {i : Fin 𝒯.m} {mesh : Mesh 𝒯}

def RowSupport (Geom : ProjectionGeometry κ 𝒯 i) (H : PrimitiveHistory κ 𝒯 i mesh)
    (mask : Masks H) (O : OddKernels Geom H mask) (L : LikelihoodData Geom H mask O)
    (R : EvenRows Geom H mask O L) : Prop :=
  ∀ v W ys, R.σ v W ys ≠ 0 → ∃ v' : mesh.V,
    (∀ p, 0 < (H.recLaw p).w W → 0 < mesh.wt v' p) ∧
      ∀ x, R.σ v W ys x ≠ 0 → x ∈ mesh.corner v' i ∧ ∀ l, Hits (T.S.E k) 𝒯.c x (ys l)

def RowMeanBound (Geom : ProjectionGeometry κ 𝒯 i) (H : PrimitiveHistory κ 𝒯 i mesh)
    (mask : Masks H) (O : OddKernels Geom H mask) (L : LikelihoodData Geom H mask O)
    (R : EvenRows Geom H mask O L) : Prop :=
  ∀ p v x, (H.recLaw p).E (fun W =>
    (refLaw Geom H mask O W).E (fun ω => R.σ v W (nbrLabels v.1 ω.2) x)) ≤
      rowMeanConstant κ / (𝒯.P i).M

noncomputable def goodTest (Geom : ProjectionGeometry κ 𝒯 i)
    (H : PrimitiveHistory κ 𝒯 i mesh) (mask : Masks H) (O : OddKernels Geom H mask)
    (L : LikelihoodData Geom H mask O) (R : EvenRows Geom H mask O L)
    (v : EvenRole 𝒯 i) (W : ∀ r, H.Val r) : Prop :=
  starValid Geom H mask v W ∧
    (refLaw Geom H mask O W).pr (fun ω => R.σ v W (nbrLabels v.1 ω.2) = 0) ≤
      sliceEps κ (𝒯.P i).h

structure GoodTests (Geom : ProjectionGeometry κ 𝒯 i) (H : PrimitiveHistory κ 𝒯 i mesh)
    (mask : Masks H) (O : OddKernels Geom H mask) (L : LikelihoodData Geom H mask O)
    (R : EvenRows Geom H mask O L) where
  Hgood : EvenRole 𝒯 i → (∀ r, H.Val r) → Prop
  Hgood_eq : Hgood = goodTest Geom H mask O L R
  zero_bound : ∀ v W, Hgood v W →
    (refLaw Geom H mask O W).pr (fun ω => R.σ v W (nbrLabels v.1 ω.2) = 0) ≤ sliceEps κ (𝒯.P i).h
  bad_bound : ∀ p, (H.recLaw p).pr (fun W => ∃ v, ¬ Hgood v W) ≤
    Real.exp (-Real.rpow ((𝒯.P i).h : ℝ) (1 + κ.c14))

/-- Full law-preserving transport of the constructed experiment. Raw mean
symmetry alone does not imply symmetry after conditioning and pretrim. -/
structure RuleSymmetry (Geom : ProjectionGeometry κ 𝒯 i) (H : PrimitiveHistory κ 𝒯 i mesh)
    (mask : Masks H) (O : OddKernels Geom H mask) (L : LikelihoodData Geom H mask O)
    (R : EvenRows Geom H mask O L) (Tests : GoodTests Geom H mask O L R) where
  history : ∀ g g' : Group 𝒯 i, (∀ r, H.Val r) ≃ (∀ r, H.Val r)
  groups : ∀ g g' : Group 𝒯 i, Group 𝒯 i ≃ Group 𝒯 i
  roles : ∀ g g' : Group 𝒯 i, EvenRole 𝒯 i ≃ EvenRole 𝒯 i
  groups_target : ∀ g g', groups g g' g = g'
  law_preserved : ∀ p g g' W, (H.recLaw p).w (history g g' W) = (H.recLaw p).w W
  q_preserved : ∀ g g' W a, O.q (groups g g' a) (history g g' W) = O.q a W
  U_preserved : ∀ g g' W a D, O.U (groups g g' a) (history g g' W) D = O.U a W D
  row_failure_preserved : ∀ g g' W v a D,
    (refLaw Geom H mask O (history g g' W)).pr (fun ω =>
      ω.1 (groups g g' a) = D ∧ R.σ (roles g g' v) (history g g' W)
        (nbrLabels (roles g g' v).1 ω.2) = 0) =
    (refLaw Geom H mask O W).pr (fun ω => ω.1 a = D ∧ R.σ v W (nbrLabels v.1 ω.2) = 0)
  test_preserved : ∀ g g' W v, Tests.Hgood (roles g g' v) (history g g' W) ↔ Tests.Hgood v W
  incidence_preserved : ∀ g g' v a,
    (roles g g' v) ∈ groupNeighborhood (groups g g' a) ↔ v ∈ groupNeighborhood a

structure LocalSymmetry (Geom : ProjectionGeometry κ 𝒯 i) (H : PrimitiveHistory κ 𝒯 i mesh)
    (mask : Masks H) (O : OddKernels Geom H mask) (L : LikelihoodData Geom H mask O)
    (R : EvenRows Geom H mask O L) (Tests : GoodTests Geom H mask O L R) where
  q_local : ∀ g W W',
    (∀ r, (hammingDist (H.loc r) (groupCenter g).1 : ℝ) ≤ 10 * κ.ρ * (𝒯.P i).h → W r = W' r) →
      O.q g W = O.q g W'
  U_local : ∀ g W W' D,
    (∀ r, (hammingDist (H.loc r) (groupCenter g).1 : ℝ) ≤ 10 * κ.ρ * (𝒯.P i).h → W r = W' r) →
      O.U g W D = O.U g W' D
  σ_local : ∀ v W W' ys,
    (∀ r, (hammingDist (H.loc r) v.1 : ℝ) ≤ 10 * κ.ρ * (𝒯.P i).h → W r = W' r) →
      R.σ v W ys = R.σ v W' ys
  Hgood_local : ∀ v W W',
    (∀ r, (hammingDist (H.loc r) v.1 : ℝ) ≤ 10 * κ.ρ * (𝒯.P i).h → W r = W' r) →
      (Tests.Hgood v W ↔ Tests.Hgood v W')
  averaged_marginal_invariant : ∀ p g g' y,
    (H.recLaw p).E (fun W => ∑ D, O.q g W D * O.U g W D y) =
      (H.recLaw p).E (fun W => ∑ D, O.q g' W D * O.U g' W D y)
  symmetry : RuleSymmetry Geom H mask O L R Tests

end Conclusions
set_option maxHeartbeats 2000000 in
/-- P14.1i: exact posterior support; arbitrary capped rows are insufficient. -/
theorem posterior_row_support (κ : CConsts) (hκ : κ.Admissible)
    {T : Stage} {k : ℕ} {𝒯 : Tiling κ T k} {i : Fin 𝒯.m} {mesh : Mesh 𝒯}
    (Geom : ProjectionGeometry κ 𝒯 i) (H : PrimitiveHistory κ 𝒯 i mesh)
    (mask : Masks H) (O : OddKernels Geom H mask) (L : LikelihoodData Geom H mask O)
    (R : EvenRows Geom H mask O L) : RowSupport Geom H mask O L R := by
  classical
  intro v W ys hrow
  have hsomeCoord : ∃ x, R.σ v W ys x ≠ 0 := by
    by_contra hnone
    apply hrow
    funext x
    by_contra hx
    exact hnone ⟨x, hx⟩
  rcases hsomeCoord with ⟨x₀, hx₀⟩
  have hpost : ∀ x, R.σ v W ys x ≠ 0 →
      posteriorRow Geom H mask O L v W ys x ≠ 0 := by
    intro x hx
    rw [← R.σ_eq]
    exact hx
  have hchosen : ∃ c, selected Geom H mask W v = some c ∧
      posteriorGate Geom H mask O L v c W ys := by
    have hp := hpost x₀ hx₀
    cases hc : selected Geom H mask W v with
    | none => simp [posteriorRow, hc] at hp
    | some c =>
      have hpair : posteriorGate Geom H mask O L v c W ys ∧
          x₀ ∈ retainedLabels Geom H mask O v c W ys := by
        by_contra hnot
        apply hp
        simp [posteriorRow, hc, hnot]
      exact ⟨c, rfl, hpair.1⟩
  rcases hchosen with ⟨c, hsel, hgateBase⟩
  have hgateAt : ∀ x, R.σ v W ys x ≠ 0 →
      posteriorGate Geom H mask O L v c W ys ∧
        x ∈ retainedLabels Geom H mask O v c W ys := by
    intro x hx
    have hp := hpost x hx
    by_contra hnot
    apply hp
    simp [posteriorRow, hsel, hnot]
  rcases (hgateAt x₀ hx₀).1 with ⟨_, _, ⟨hpriorSupport, _⟩, _, _⟩
  let postTerm (x : Fin (T.S.N k)) (w : H.Tuple) : ℝ :=
    ((H.tuplePrior (H.cornerOf W c)).w w *
      subLikelihood Geom H mask O v c W w ys /
        predictiveMass Geom H mask O v c W ys) *
      ((∑ r, if w r = x then (1 : ℝ) else 0) / 𝒯.kScale i)
  have hmeanNe : ∀ x, R.σ v W ys x ≠ 0 →
      posteriorMean Geom H mask O v c W ys x ≠ 0 := by
    intro x hx
    have hfrac :
        posteriorMean Geom H mask O v c W ys x /
          (∑ z ∈ retainedLabels Geom H mask O v c W ys,
            posteriorMean Geom H mask O v c W ys z) ≠ 0 := by
      simpa [posteriorRow, hsel, hgateAt x hx] using hpost x hx
    intro hz
    apply hfrac
    simp [hz]
  have tupleCoordinate : ∀ x, R.σ v W ys x ≠ 0 →
      ∃ w : H.Tuple, ∃ r, postTerm x w ≠ 0 ∧ w r = x := by
    intro x hx
    have hm := hmeanNe x hx
    have hexists : ∃ w : H.Tuple, postTerm x w ≠ 0 := by
      by_contra hnone
      push_neg at hnone
      have hzero : posteriorMean Geom H mask O v c W ys x = 0 := by
        unfold posteriorMean
        apply Finset.sum_eq_zero
        intro w hw
        simpa [postTerm] using hnone w
      exact hm hzero
    rcases hexists with ⟨w, hterm⟩
    have hcountDiv :
        ((∑ r, if w r = x then (1 : ℝ) else 0) / 𝒯.kScale i) ≠ 0 :=
      (mul_ne_zero_iff.mp hterm).2
    have hcount : (∑ r, if w r = x then (1 : ℝ) else 0) ≠ 0 := by
      intro hz
      apply hcountDiv
      simp [hz]
    have hr : ∃ r, w r = x := by
      by_contra hnone
      push_neg at hnone
      apply hcount
      simp [hnone]
    rcases hr with ⟨r, hrx⟩
    exact ⟨w, r, hterm, hrx⟩
  have cornerOfTuple : ∀ x (w : H.Tuple) (r : Fin (𝒯.kScale i)),
      (H.tuplePrior (H.cornerOf W c)).w w ≠ 0 → w r = x →
      x ∈ mesh.corner (H.cornerOf W c) i := by
    intro x w r htuple hrx
    have hprod :
        (∏ r' : Fin (𝒯.kScale i), (H.prior (H.cornerOf W c)).w (w r')) ≠ 0 := by
      simpa [PrimitiveHistory.tuplePrior, FinLaw.pi, lawToFinLaw] using htuple
    have hcoord := (Finset.prod_ne_zero_iff.mp hprod) r (Finset.mem_univ r)
    have hcoord' : (H.prior (H.cornerOf W c)).w x ≠ 0 := by
      simpa [hrx] using hcoord
    by_contra hx
    have hzero := hpriorSupport x hx
    exact hcoord' hzero
  have hactive : ∀ p, 0 < (H.recLaw p).w W →
      0 < mesh.wt (H.cornerOf W c) p := by
    intro p hp
    let r₀ : H.Rec := Sum.inl c
    have hprod : 0 < ∏ r : H.Rec, H.lawRec p r (W r) := by
      change 0 < ∏ r : H.Rec, H.lawRec p r (W r) at hp
      exact hp
    have hcenterLaw : 0 < (H.centerLaw p).w (W r₀) := by
      have hprodNe : (∏ r : H.Rec, H.lawRec p r (W r)) ≠ 0 := ne_of_gt hprod
      have hfactorNe := (Finset.prod_ne_zero_iff.mp hprodNe)
        r₀ (Finset.mem_univ r₀)
      have hfactorNonneg : 0 ≤ H.lawRec p r₀ (W r₀) :=
        (H.record p r₀).nonneg (W r₀)
      have hfactorPos : 0 < H.lawRec p r₀ (W r₀) := by
        by_contra hnot
        have hle := le_of_not_gt hnot
        have hz := le_antisymm hle hfactorNonneg
        exact hfactorNe hz
      simpa [PrimitiveHistory.lawRec, PrimitiveHistory.record, r₀] using hfactorPos
    have hwtNe : mesh.wt (H.cornerOf W c) p ≠ 0 := by
      intro hz
      apply (ne_of_gt hcenterLaw)
      have hz' : mesh.wt (W r₀).1 p = 0 := by
        simpa [PrimitiveHistory.cornerOf] using hz
      simp [PrimitiveHistory.centerLaw, PrimitiveHistory.vertexLaw,
        FinLaw.bind, r₀, hz']
    by_contra hnot
    have hle : mesh.wt (H.cornerOf W c) p ≤ 0 := le_of_not_gt hnot
    have hz : mesh.wt (H.cornerOf W c) p = 0 :=
      le_antisymm hle (mesh.wt_nonneg _ _)
    exact hwtNe hz
  have prPosWitness
      (P : FinLaw ((Group 𝒯 i → Bin 𝒯 i) × (IWord 𝒯 i → Fin (T.S.N k))))
      (A : ((Group 𝒯 i → Bin 𝒯 i) × (IWord 𝒯 i → Fin (T.S.N k))) → Prop)
      (hP : 0 < P.pr A) : ∃ ω, A ω ∧ 0 < P.w ω := by
    classical
    by_contra hnone
    push_neg at hnone
    have hzero : P.pr A = 0 := by
      unfold FinLaw.pr
      apply Finset.sum_eq_zero
      intro ω hω
      by_cases hA : A ω
      · have hle : P.w ω ≤ 0 := hnone ω hA
        have hz : P.w ω = 0 := le_antisymm hle (P.nonneg ω)
        simp [hA, hz]
      · simp [hA]
    exact (ne_of_gt hP) hzero
  have hsubPositive : ∀ w, subLikelihood Geom H mask O v c W w ys ≠ 0 →
      0 < subLikelihood Geom H mask O v c W w ys := by
    intro w hne
    have hnonneg : 0 ≤ subLikelihood Geom H mask O v c W w ys := by
      by_cases hh : selected Geom H mask (H.replaceTuple W c w) v = some c ∧
          starValid Geom H mask v (H.replaceTuple W c w)
      · have hp : 0 ≤ (refLaw Geom H mask O (H.replaceTuple W c w)).pr
            (fun ω => nbrLabels v.1 ω.2 = ys) := by
          unfold FinLaw.pr
          apply Finset.sum_nonneg
          intro ω hω
          split_ifs
          · exact (refLaw Geom H mask O (H.replaceTuple W c w)).nonneg ω
          · exact le_rfl
        simpa [subLikelihood, hh] using hp
      · simp [subLikelihood, hh]
    by_contra hnot
    have hle : subLikelihood Geom H mask O v c W w ys ≤ 0 := le_of_not_gt hnot
    have hz : subLikelihood Geom H mask O v c W w ys = 0 := le_antisymm hle hnonneg
    exact hne hz
  have hitsOfTuple : ∀ (x : Fin (T.S.N k)) (w : H.Tuple)
      (r : Fin (𝒯.kScale i)), postTerm x w ≠ 0 → w r = x →
      ∀ l, Hits (T.S.E k) 𝒯.c x (ys l) := by
    intro x w r hterm hrx l
    have htupleNe : (H.tuplePrior (H.cornerOf W c)).w w ≠ 0 := by
      intro hz
      apply hterm
      simp [postTerm, hz]
    have hsubNe : subLikelihood Geom H mask O v c W w ys ≠ 0 := by
      intro hz
      apply hterm
      simp [postTerm, hz]
    have hsubPos := hsubPositive w hsubNe
    let W' := H.replaceTuple W c w
    have hsubCond : selected Geom H mask W' v = some c ∧
        starValid Geom H mask v W' := by
      by_contra hnot
      have hz : subLikelihood Geom H mask O v c W w ys = 0 := by
        simp [subLikelihood, W', hnot]
      exact hsubNe hz
    have hRefPos : 0 < (refLaw Geom H mask O W').pr
        (fun ω => nbrLabels v.1 ω.2 = ys) := by
      simpa [subLikelihood, W', hsubCond] using hsubPos
    obtain ⟨ω, hωlabels, hωweight⟩ := prPosWitness
      (refLaw Geom H mask O W') (fun ω => nbrLabels v.1 ω.2 = ys) hRefPos
    let qprod : ℝ := ∏ g₀ : Group 𝒯 i, O.q g₀ W' (ω.1 g₀)
    let uprod : ℝ := ∏ z : IWord 𝒯 i,
      O.U (Geom.groupOf z) W' (ω.1 (Geom.groupOf z)) (ω.2 z)
    have hweight : 0 < qprod * uprod := by
      simpa [qprod, uprod, refLaw, internalRefLaw, FinLaw.bind, FinLaw.pi] using hωweight
    have hqprodNonneg : 0 ≤ qprod := by
      dsimp [qprod]
      exact Finset.prod_nonneg fun g₀ hg₀ => O.q_nonneg g₀ W' (ω.1 g₀)
    have huproductNonneg : 0 ≤ uprod := by
      dsimp [uprod]
      exact Finset.prod_nonneg fun z hz => O.U_nonneg (Geom.groupOf z) W'
        (ω.1 (Geom.groupOf z)) (ω.2 z)
    have hqprodPos : 0 < qprod := by
      by_contra hnot
      have hz : qprod = 0 := le_antisymm (le_of_not_gt hnot) hqprodNonneg
      simp [hz] at hweight
    have huproductPos : 0 < uprod := by
      by_contra hnot
      have hz : uprod = 0 := le_antisymm (le_of_not_gt hnot) huproductNonneg
      simp [hz] at hweight
    have hqAt : ∀ g₀, 0 < O.q g₀ W' (ω.1 g₀) := by
      have hprodNe : (∏ g₀ : Group 𝒯 i, O.q g₀ W' (ω.1 g₀)) ≠ 0 := by
        simpa [qprod] using (ne_of_gt hqprodPos)
      intro g₀
      have hne := (Finset.prod_ne_zero_iff.mp hprodNe) g₀ (Finset.mem_univ g₀)
      by_contra hnot
      have hle := le_of_not_gt hnot
      have hz := le_antisymm hle (O.q_nonneg g₀ W' (ω.1 g₀))
      exact hne hz
    have huAt : ∀ z : IWord 𝒯 i,
        0 < O.U (Geom.groupOf z) W' (ω.1 (Geom.groupOf z)) (ω.2 z) := by
      have hprodNe : (∏ z : IWord 𝒯 i,
          O.U (Geom.groupOf z) W' (ω.1 (Geom.groupOf z)) (ω.2 z)) ≠ 0 := by
        simpa [uprod] using (ne_of_gt huproductPos)
      intro z
      have hne := (Finset.prod_ne_zero_iff.mp hprodNe) z (Finset.mem_univ z)
      by_contra hnot
      have hle := le_of_not_gt hnot
      have hz := le_antisymm hle (O.U_nonneg (Geom.groupOf z) W'
        (ω.1 (Geom.groupOf z)) (ω.2 z))
      exact hne hz
    have hflipOdd : ∀ l : Fin (𝒯.P i).h, ¬ IsEvenRole (flipPos v.1 l) := by
      intro l
      classical
      let A : Finset (Fin (𝒯.P i).h) := Finset.univ.filter fun j => v.1 j = true
      let B : Finset (Fin (𝒯.P i).h) :=
        Finset.univ.filter fun j => flipPos v.1 l j = true
      have hEvenA : Even A.card := by
        simpa [A, IsEvenRole] using v.2
      change ¬ Even B.card
      cases hbit : v.1 l with
      | true =>
        have hlA : l ∈ A := Finset.mem_filter.mpr ⟨Finset.mem_univ _, hbit⟩
        have hBA : B = A.erase l := by
          ext j
          by_cases hj : j = l
          · subst j
            simp [A, B, flipPos, hbit]
          · simp [A, B, flipPos, hj, Ne.symm hj, hbit]
        intro hevenB
        have hevenSub : Even (A.card - 1) := by
          rw [← Finset.card_erase_of_mem hlA, ← hBA]
          exact hevenB
        rcases hEvenA with ⟨a, ha⟩
        rcases hevenSub with ⟨b, hb⟩
        have hposA : 0 < A.card := Finset.card_pos.mpr ⟨l, hlA⟩
        omega
      | false =>
        have hlA : l ∉ A := by simp [A, hbit]
        have hBA : B = insert l A := by
          ext j
          by_cases hj : j = l
          · subst j
            simp [A, B, flipPos, hbit]
          · simp [A, B, flipPos, hj, Ne.symm hj, hbit]
        intro hevenB
        have hevenIns : Even (A.card + 1) := by
          rw [← Finset.card_insert_of_notMem hlA, ← hBA]
          exact hevenB
        rcases hEvenA with ⟨a, ha⟩
        rcases hevenIns with ⟨b, hb⟩
        omega
    let z : IWord 𝒯 i := flipPos v.1 l
    have hzOdd : ¬ IsEvenRole z := by simpa [z] using hflipOdd l
    have hzGroup : z ∈ groupFiber (Geom.groupOf z) := Geom.groupOf_spec z hzOdd
    have hvGroup : v ∈ groupNeighborhood (Geom.groupOf z) := by
      simp [groupNeighborhood, z]
      exact ⟨l, hzGroup⟩
    have hgroupValid : groupValid Geom H mask (Geom.groupOf z) W' :=
      hsubCond.2.1 (Geom.groupOf z) hvGroup
    have hcList : c ∈ realizedList Geom H mask (Geom.groupOf z) W' := by
      unfold realizedList
      simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      exact ⟨v, hvGroup, hsubCond.1⟩
    have hqfactor : 0 < O.q (Geom.groupOf z) W' (ω.1 (Geom.groupOf z)) :=
      hqAt (Geom.groupOf z)
    have hUfactor : 0 < O.U (Geom.groupOf z) W'
        (ω.1 (Geom.groupOf z)) (ω.2 z) := huAt z
    have hlabel : ω.2 z = ys l := by
      have h := congrFun hωlabels l
      simpa [nbrLabels, z] using h
    have hqOdd : 0 < oddQ Geom H mask (Geom.groupOf z) W'
        (ω.1 (Geom.groupOf z)) := by
      have hqeq := congrFun (congrFun (congrFun O.q_eq (Geom.groupOf z)) W')
        (ω.1 (Geom.groupOf z))
      rw [← hqeq]
      exact hqfactor
    have huHit : ys l ∈ listHit H W'
        (realizedList Geom H mask (Geom.groupOf z) W') := by
      have hUeq := congrFun (congrFun (congrFun (congrFun O.U_eq (Geom.groupOf z)) W')
        (ω.1 (Geom.groupOf z))) (ω.2 z)
      have huPos0 : 0 < oddU Geom H mask (Geom.groupOf z) W'
          (ω.1 (Geom.groupOf z)) (ω.2 z) := by
        rw [← hUeq]
        exact hUfactor
      have huPos : 0 < oddU Geom H mask (Geom.groupOf z) W'
          (ω.1 (Geom.groupOf z)) (ys l) := by
        rw [← hlabel]
        exact huPos0
      have hcond : groupValid Geom H mask (Geom.groupOf z) W' ∧
          0 < oddQ Geom H mask (Geom.groupOf z) W' (ω.1 (Geom.groupOf z)) :=
        ⟨hgroupValid, hqOdd⟩
      unfold oddU at huPos
      rw [if_pos hcond] at huPos
      by_cases hhit : ys l ∈ listHit H W' (realizedList Geom H mask (Geom.groupOf z) W')
      · exact hhit
      · simp [hhit] at huPos
    have htupleEq : H.tuple W' c r = w r := by
      simp [W', PrimitiveHistory.tuple, PrimitiveHistory.replaceTuple]
    have htupleHit : Hits (T.S.E k) 𝒯.c (H.tuple W' c r) (ys l) := by
      exact (Finset.mem_filter.mp huHit).2 c hcList r
    simpa [htupleEq, hrx] using htupleHit
  refine ⟨H.cornerOf W c, hactive, ?_⟩
  intro x hx
  rcases tupleCoordinate x hx with ⟨w, r, hterm, hrx⟩
  refine ⟨cornerOfTuple x w r ?_ hrx, ?_⟩
  · intro hz
    apply hterm
    simp [postTerm, hz]
  · exact hitsOfTuple x w r hterm hrx


set_option maxHeartbeats 2000000 in
/-- P14.1j: posterior cancellation, retained-mass cost and the independently
proved forced-present selection incidence estimate. -/
theorem posterior_row_mean (κ : CConsts) (hκ : κ.Admissible)
    {T : Stage} {k : ℕ} {𝒯 : Tiling κ T k} {i : Fin 𝒯.m} {mesh : Mesh 𝒯}
    (Geom : ProjectionGeometry κ 𝒯 i) (H : PrimitiveHistory κ 𝒯 i mesh)
    (mask : Masks H) (O : OddKernels Geom H mask) (L : LikelihoodData Geom H mask O)
    (R : EvenRows Geom H mask O L) (hinc : SelectionIncidence Geom H mask) :
    RowMeanBound Geom H mask O L R := by
  classical
  intro p v x
  let vWord : CubePos (𝒯.P i).h := v.1
  have ha : 0 < κ.a := by
    rw [hκ.a_eq]
    exact div_pos hκ.θ_rng.1 (by norm_num)
  have hsub0 : ∀ c (W : ∀ r, H.Val r) w ys,
      0 ≤ subLikelihood Geom H mask O v c W w ys := by
    intro c W w ys
    dsimp [subLikelihood]
    split_ifs
    · unfold FinLaw.pr
      apply Finset.sum_nonneg
      intro ω hω
      split_ifs
      · exact (refLaw Geom H mask O (H.replaceTuple W c w)).nonneg ω
      · exact le_rfl
    · exact le_rfl
  have hpred0 : ∀ c (W : ∀ r, H.Val r) ys,
      0 ≤ predictiveMass Geom H mask O v c W ys := by
    intro c W ys
    unfold predictiveMass
    apply Finset.sum_nonneg
    intro w hw
    exact mul_nonneg ((H.tuplePrior (H.cornerOf W c)).nonneg w) (hsub0 c W w ys)
  have hpm0 : ∀ c (W : ∀ r, H.Val r) ys,
      0 ≤ posteriorMean Geom H mask O v c W ys x := by
    intro c W ys
    unfold posteriorMean
    apply Finset.sum_nonneg
    intro w hw
    apply mul_nonneg
    · exact div_nonneg
        (mul_nonneg ((H.tuplePrior (H.cornerOf W c)).nonneg w) (hsub0 c W w ys))
        (hpred0 c W ys)
    · apply div_nonneg
      · apply Finset.sum_nonneg
        intro r hr
        split_ifs <;> positivity
      · exact_mod_cast (Nat.zero_le (𝒯.kScale i))
  let postMass : (∀ r, H.Val r) → InternalLabels 𝒯 i → ℝ := fun W ys =>
    match selected Geom H mask W v with
    | none => 0
    | some c =>
      if posteriorGate Geom H mask O L v c W ys then
        posteriorMean Geom H mask O v c W ys x else 0
  have hpoint : ∀ W ys, R.σ v W ys x ≤ (200 / κ.a) * postMass W ys := by
    intro W ys
    rw [R.σ_eq]
    cases hs : selected Geom H mask W v with
    | none => simp [posteriorRow, postMass, hs]
    | some c =>
      by_cases hg : posteriorGate Geom H mask O L v c W ys
      · by_cases hx : x ∈ retainedLabels Geom H mask O v c W ys
        · have hm := R.retained_mass v c W ys hg
          let den := ∑ z ∈ retainedLabels Geom H mask O v c W ys,
            posteriorMean Geom H mask O v c W ys z
          have hden : κ.a / 200 ≤ den := hm
          have hdenpos : 0 < den := lt_of_lt_of_le (div_pos ha (by norm_num)) hden
          have hfac : 1 ≤ (200 / κ.a) * den := by
            have hcancel : (200 / κ.a) * (κ.a / 200) = 1 := by
              field_simp [ne_of_gt ha]
            calc
              1 = (200 / κ.a) * (κ.a / 200) := hcancel.symm
              _ ≤ (200 / κ.a) * den :=
                mul_le_mul_of_nonneg_left hden (by positivity)
          have hratio :
              posteriorMean Geom H mask O v c W ys x / den ≤
                (200 / κ.a) * posteriorMean Geom H mask O v c W ys x := by
            apply (div_le_iff₀ hdenpos).2
            calc
              posteriorMean Geom H mask O v c W ys x =
                  1 * posteriorMean Geom H mask O v c W ys x := by ring
              _ ≤ ((200 / κ.a) * den) * posteriorMean Geom H mask O v c W ys x :=
                mul_le_mul_of_nonneg_right hfac (hpm0 c W ys)
              _ = (200 / κ.a) * posteriorMean Geom H mask O v c W ys x * den := by ring
          simpa [posteriorRow, postMass, hs, hg, hx, den] using hratio
        · have hnonneg := mul_nonneg (by positivity : 0 ≤ (200 / κ.a)) (hpm0 c W ys)
          simpa [posteriorRow, postMass, hs, hg, hx] using hnonneg
      · simp [posteriorRow, postMass, hs, hg]
  have hrecordSplit (c : H.Center) (F : (∀ r, H.Val r) → ℝ) :
      (∑ W, (H.recLaw p).w W * F W) =
        ∑ z : H.Val (.inl c), H.lawRec p (.inl c) z *
          ∑ rest : ∀ r : {r // r ≠ Sum.inl c}, H.Val r.1,
            (∏ r : {r // r ≠ Sum.inl c}, H.lawRec p r.1 (rest r)) *
              F ((Equiv.piSplitAt (Sum.inl c) H.Val).symm (z, rest)) := by
    simpa [PrimitiveHistory.recLaw, PrimitiveHistory.lawRec, recordLaw, FinLaw.pi] using
      (HypercubeRamsey.Lane_q_s14_post.sum_pi_splitAt (H.lawRec p) (Sum.inl c) F)
  have hlabelMarginal (W : ∀ r, H.Val r) :
      (refLaw Geom H mask O W).E
          (fun ω => R.σ v W (nbrLabels v.1 ω.2) x) =
        ∑ ys, (refLaw Geom H mask O W).pr
          (fun ω => nbrLabels v.1 ω.2 = ys) * R.σ v W ys x := by
    exact HypercubeRamsey.Lane_q_s14_post.expect_comp_eq_sum_pr
      (refLaw Geom H mask O W) (fun ω => nbrLabels v.1 ω.2) (fun ys => R.σ v W ys x)
  have hbayes (c : H.Center) (W : ∀ r, H.Val r) :
      (∑ ys, predictiveMass Geom H mask O v c W ys *
        posteriorMean Geom H mask O v c W ys x) =
        ∑ w, ∑ ys, (H.tuplePrior (H.cornerOf W c)).w w *
          ((∑ r, if w r = x then (1 : ℝ) else 0) / 𝒯.kScale i) *
            subLikelihood Geom H mask O v c W w ys := by
    let π : FinProb H.Tuple := {
      w := (H.tuplePrior (H.cornerOf W c)).w
      nonneg := (H.tuplePrior (H.cornerOf W c)).nonneg
      sum_eq_one := (H.tuplePrior (H.cornerOf W c)).sum_one
    }
    let Q : FinProb (InternalLabels 𝒯 i) := {
      w := (L.reference v c W).w
      nonneg := (L.reference v c W).nonneg
      sum_eq_one := (L.reference v c W).sum_one
    }
    let F : H.Tuple → InternalLabels 𝒯 i → ℝ :=
      fun w ys => subLikelihood Geom H mask O v c W w ys
    let freq : H.Tuple → InternalLabels 𝒯 i → ℝ := fun w _ =>
      (∑ r, if w r = x then (1 : ℝ) else 0) / 𝒯.kScale i
    let m : InternalLabels 𝒯 i → ℝ := fun ys => ∑ w, π.w w * F w ys
    have hcan :=
      (gated_posterior π F (hsub0 c W) Q 1 0 (by norm_num)).2.2 freq
    have hleft :
        (∑ ys, predictiveMass Geom H mask O v c W ys *
          posteriorMean Geom H mask O v c W ys x) =
          ∑ ys, m ys * ∑ w, freq w ys * (π.w w * F w ys / m ys) := by
      apply Finset.sum_congr rfl
      intro ys hys
      simp only [predictiveMass, posteriorMean, m, F, freq]
      rw [Finset.mul_sum]
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro w hw
      ring
    calc
      _ = ∑ ys, m ys * ∑ w, freq w ys * (π.w w * F w ys / m ys) := hleft
      _ = ∑ w, ∑ ys, π.w w * freq w ys * F w ys := hcan
      _ = _ := by
        apply Finset.sum_congr rfl
        intro w hw
        apply Finset.sum_congr rfl
        intro ys hys
        simp [π, F, freq]
  have hsubSum (c : H.Center) (W : ∀ r, H.Val r) (w : H.Tuple) :
      (∑ ys, subLikelihood Geom H mask O v c W w ys) =
        if selected Geom H mask (H.replaceTuple W c w) v = some c ∧
            starValid Geom H mask v (H.replaceTuple W c w) then 1 else 0 := by
    dsimp [subLikelihood]
    split_ifs
    · exact HypercubeRamsey.Lane_q_s14_post.sum_pr_eq_one
        (refLaw Geom H mask O (H.replaceTuple W c w)) (fun ω => nbrLabels v.1 ω.2)
    · simp
  have htupleReplace (c : H.Center) (W : ∀ r, H.Val r) :
      H.replaceTuple W c (H.tuple W c) = W := by
    funext r
    by_cases hr : r = Sum.inl c
    · subst r
      simp [PrimitiveHistory.replaceTuple, PrimitiveHistory.cornerOf,
        PrimitiveHistory.tuple, PrimitiveHistory.present, PrimitiveHistory.active]
    · simp [PrimitiveHistory.replaceTuple, hr]
  have hsubActual (c : H.Center) (W : ∀ r, H.Val r) (ys : InternalLabels 𝒯 i) :
      subLikelihood Geom H mask O v c W (H.tuple W c) ys =
        if selected Geom H mask W v = some c ∧ starValid Geom H mask v W then
          (refLaw Geom H mask O W).pr (fun ω => nbrLabels v.1 ω.2 = ys) else 0 := by
    simp [subLikelihood, htupleReplace]
  have hreplaceReplace (c : H.Center) (W : ∀ r, H.Val r) (w₀ w₁ : H.Tuple) :
      H.replaceTuple (H.replaceTuple W c w₀) c w₁ = H.replaceTuple W c w₁ := by
    funext r
    by_cases hr : r = Sum.inl c
    · subst r
      simp [PrimitiveHistory.replaceTuple, PrimitiveHistory.cornerOf,
        PrimitiveHistory.tuple, PrimitiveHistory.present, PrimitiveHistory.active]
    · simp [PrimitiveHistory.replaceTuple, hr]
  have hsubInvariant (c : H.Center) (W : ∀ r, H.Val r) (w₀ w₁ w : H.Tuple)
      (ys : InternalLabels 𝒯 i) :
      subLikelihood Geom H mask O v c (H.replaceTuple W c w₀) w ys =
        subLikelihood Geom H mask O v c (H.replaceTuple W c w₁) w ys := by
    simp [subLikelihood, hreplaceReplace]
  have hpmInvariant (c : H.Center) (W : ∀ r, H.Val r) (w₀ w₁ : H.Tuple)
      (ys : InternalLabels 𝒯 i) :
      posteriorMean Geom H mask O v c (H.replaceTuple W c w₀) ys x =
        posteriorMean Geom H mask O v c (H.replaceTuple W c w₁) ys x := by
    have hc₀ : H.cornerOf (H.replaceTuple W c w₀) c = H.cornerOf W c := by
      simp [PrimitiveHistory.cornerOf, PrimitiveHistory.replaceTuple]
    have hc₁ : H.cornerOf (H.replaceTuple W c w₁) c = H.cornerOf W c := by
      simp [PrimitiveHistory.cornerOf, PrimitiveHistory.replaceTuple]
    unfold posteriorMean predictiveMass
    rw [hc₀, hc₁]
    have hden :
        (∑ w, (H.tuplePrior (H.cornerOf W c)).w w *
          subLikelihood Geom H mask O v c (H.replaceTuple W c w₀) w ys) =
        ∑ w, (H.tuplePrior (H.cornerOf W c)).w w *
          subLikelihood Geom H mask O v c (H.replaceTuple W c w₁) w ys := by
      apply Finset.sum_congr rfl
      intro w hw
      rw [hsubInvariant c W w₀ w₁ w ys]
    rw [hden]
    apply Finset.sum_congr rfl
    intro w hw
    rw [hsubInvariant c W w₀ w₁ w ys]
  have hselProb (c : H.Center) (W : ∀ r, H.Val r) :
      (refLaw Geom H mask O W).E (fun ω =>
        if selected Geom H mask W v = some c ∧ starValid Geom H mask v W then
          posteriorMean Geom H mask O v c W (nbrLabels v.1 ω.2) x else 0) =
      ∑ ys, subLikelihood Geom H mask O v c W (H.tuple W c) ys *
        posteriorMean Geom H mask O v c W ys x := by
    have hpush := HypercubeRamsey.Lane_q_s14_post.expect_comp_eq_sum_pr
      (refLaw Geom H mask O W) (fun ω => nbrLabels v.1 ω.2)
      (fun ys => if selected Geom H mask W v = some c ∧ starValid Geom H mask v W then
        posteriorMean Geom H mask O v c W ys x else 0)
    by_cases he : selected Geom H mask W v = some c ∧ starValid Geom H mask v W
    · calc
        _ = ∑ ys, (refLaw Geom H mask O W).pr
            (fun ω => nbrLabels v.1 ω.2 = ys) * posteriorMean Geom H mask O v c W ys x := by
              simpa [he] using hpush
        _ = ∑ ys, subLikelihood Geom H mask O v c W (H.tuple W c) ys *
            posteriorMean Geom H mask O v c W ys x := by
              apply Finset.sum_congr rfl
              intro ys hys
              rw [hsubActual c W ys]
              simp [he]
    · calc
        _ = 0 := by simpa [he] using hpush
        _ = ∑ ys, subLikelihood Geom H mask O v c W (H.tuple W c) ys *
            posteriorMean Geom H mask O v c W ys x := by
              symm
              apply Finset.sum_eq_zero
              intro ys hys
              rw [hsubActual c W ys]
              simp [he]
  have hcenterTuple (c : H.Center) (W : ∀ r, H.Val r) :
      (∑ w, (H.tuplePrior (H.cornerOf W c)).w w *
        ∑ ys, subLikelihood Geom H mask O v c (H.replaceTuple W c w) w ys *
          posteriorMean Geom H mask O v c (H.replaceTuple W c w) ys x) =
      ∑ w, (H.tuplePrior (H.cornerOf W c)).w w *
        (if selected Geom H mask (H.replaceTuple W c w) v = some c ∧
            starValid Geom H mask v (H.replaceTuple W c w) then
          (∑ r, if w r = x then (1 : ℝ) else 0) / 𝒯.kScale i else 0) := by
    let π : FinProb H.Tuple := {
      w := (H.tuplePrior (H.cornerOf W c)).w
      nonneg := (H.tuplePrior (H.cornerOf W c)).nonneg
      sum_eq_one := (H.tuplePrior (H.cornerOf W c)).sum_one
    }
    let Wb := fun b : H.Tuple => H.replaceTuple W c b
    let freq : H.Tuple → ℝ := fun w =>
      (∑ r, if w r = x then (1 : ℝ) else 0) / 𝒯.kScale i
    let G : H.Tuple → H.Tuple → ℝ := fun b a =>
      ∑ ys, subLikelihood Geom H mask O v c (Wb b) a ys *
        posteriorMean Geom H mask O v c (Wb b) ys x
    have hG : ∀ b b' a, G b a = G b' a := by
      intro b b' a
      unfold G
      apply Finset.sum_congr rfl
      intro ys hys
      rw [hsubInvariant c W b b' a ys, hpmInvariant c W b b' ys]
    have hdiag := HypercubeRamsey.Lane_q_s14_post.sum_diagonal_eq_base π G hG
    have hinner (b : H.Tuple) :
        ∑ a, π.w a * G b a =
          ∑ a, π.w a * (if selected Geom H mask (Wb a) v = some c ∧
            starValid Geom H mask v (Wb a) then freq a else 0) := by
      have hcorner : H.cornerOf (Wb b) c = H.cornerOf W c := by
        simp [Wb, PrimitiveHistory.cornerOf, PrimitiveHistory.replaceTuple]
      calc
        _ = ∑ ys, predictiveMass Geom H mask O v c (Wb b) ys *
            posteriorMean Geom H mask O v c (Wb b) ys x := by
              unfold G predictiveMass
              rw [hcorner]
              calc
                _ = ∑ a, ∑ ys, π.w a *
                    (subLikelihood Geom H mask O v c (Wb b) a ys *
                      posteriorMean Geom H mask O v c (Wb b) ys x) := by
                        apply Finset.sum_congr rfl
                        intro a ha
                        rw [Finset.mul_sum]
                _ = ∑ ys, ∑ a, π.w a *
                    (subLikelihood Geom H mask O v c (Wb b) a ys *
                      posteriorMean Geom H mask O v c (Wb b) ys x) := Finset.sum_comm
                _ = ∑ ys, (∑ a, π.w a *
                    subLikelihood Geom H mask O v c (Wb b) a ys) *
                    posteriorMean Geom H mask O v c (Wb b) ys x := by
                      apply Finset.sum_congr rfl
                      intro ys hys
                      rw [Finset.sum_mul]
                      apply Finset.sum_congr rfl
                      intro a ha
                      ring
        _ = ∑ a, ∑ ys, (H.tuplePrior (H.cornerOf (Wb b) c)).w a * freq a *
            subLikelihood Geom H mask O v c (Wb b) a ys := by
              simpa [freq] using hbayes c (Wb b)
        _ = ∑ a, ∑ ys, π.w a * freq a *
            subLikelihood Geom H mask O v c (Wb b) a ys := by
              simp [π, hcorner]
        _ = ∑ a, π.w a *
            (freq a * ∑ ys, subLikelihood Geom H mask O v c (Wb b) a ys) := by
              apply Finset.sum_congr rfl
              intro a ha
              rw [← Finset.mul_sum]
              ring
        _ = ∑ a, π.w a *
            (if selected Geom H mask (Wb a) v = some c ∧
                starValid Geom H mask v (Wb a) then freq a else 0) := by
              apply Finset.sum_congr rfl
              intro a ha
              rw [hsubSum c (Wb b) a]
              have hreplace : H.replaceTuple (Wb b) c a = Wb a := by
                exact hreplaceReplace c W b a
              rw [hreplace]
              by_cases hg : selected Geom H mask (Wb a) v = some c ∧
                  starValid Geom H mask v (Wb a)
              · simp [hg]
              · simp [hg]
    calc
      _ = ∑ b, π.w b * ∑ a, π.w a * G b a := by
        simpa [π, Wb, G] using hdiag
      _ = ∑ b, π.w b *
          ∑ a, π.w a * (if selected Geom H mask (Wb a) v = some c ∧
            starValid Geom H mask v (Wb a) then freq a else 0) := by
          apply Finset.sum_congr rfl
          intro b hb
          rw [hinner]
      _ = ∑ a, π.w a * (if selected Geom H mask (Wb a) v = some c ∧
          starValid Geom H mask v (Wb a) then freq a else 0) := by
          rw [← Finset.sum_mul, π.sum_eq_one]
          ring
      _ = _ := by simp [π, Wb, freq]
  let posLaw : FinLaw Bool := PrimitiveHistory.finProbToFinLaw
    (FinProb.bernoulli (H.Device.lam / H.Device.V))
  let actLaw : FinLaw Bool := PrimitiveHistory.finProbToFinLaw
    (FinProb.bernoulli ((H.Device.n : ℝ) ^ H.Device.b₀ / H.Device.lam))
  have hcenterExp (c : H.Center) (F : H.Val (.inl c) → ℝ) :
      (H.record p (.inl c)).E F =
        (PrimitiveHistory.vertexLaw p).E (fun u => (H.tuplePrior u).E (fun w =>
          posLaw.E (fun bp => actLaw.E (fun ba => F (u, (w, (bp, ba))))))) := by
    dsimp [PrimitiveHistory.record, PrimitiveHistory.centerLaw, posLaw, actLaw]
    simp_rw [HypercubeRamsey.Lane_q_s14_post.expect_bind]
  let bitPairLaw : FinLaw (Bool × Bool) := FinLaw.bind posLaw (fun _ => actLaw)
  have hcenterExpSwap (c : H.Center) (F : H.Val (.inl c) → ℝ) :
      (H.record p (.inl c)).E F =
        (PrimitiveHistory.vertexLaw p).E (fun u => bitPairLaw.E (fun bits =>
          (H.tuplePrior u).E (fun w => F (u, (w, bits))))) := by
    have hbits (u : mesh.V) (w : H.Tuple) :
        posLaw.E (fun bp => actLaw.E (fun ba => F (u, (w, (bp, ba))))) =
          bitPairLaw.E (fun bits => F (u, (w, bits))) := by
      exact (HypercubeRamsey.Lane_q_s14_post.expect_bind posLaw
        (fun _ => actLaw) (fun bits => F (u, (w, bits)))).symm
    rw [hcenterExp c F]
    simp_rw [hbits]
    apply congrArg (fun f => (PrimitiveHistory.vertexLaw p).E f)
    funext u
    exact HypercubeRamsey.Lane_q_s14_post.expect_swap (H.tuplePrior u) bitPairLaw
      (fun w bits => F (u, (w, bits)))
  let selMass : (∀ r, H.Val r) → InternalLabels 𝒯 i → ℝ := fun W ys =>
    ∑ c : H.Center,
      if selected Geom H mask W v = some c ∧ starValid Geom H mask v W then
        posteriorMean Geom H mask O v c W ys x else 0
  have hselExpand (W : ∀ r, H.Val r) (ys : InternalLabels 𝒯 i) :
      selMass W ys = ∑ c : H.Center,
        if selected Geom H mask W v = some c ∧ starValid Geom H mask v W then
          posteriorMean Geom H mask O v c W ys x else 0 := by rfl
  have hselExpectedExpand :
      (H.recLaw p).E (fun W =>
        (refLaw Geom H mask O W).E (fun ω => selMass W (nbrLabels vWord ω.2))) =
        ∑ c : H.Center, (H.recLaw p).E (fun W =>
          (refLaw Geom H mask O W).E (fun ω =>
            if selected Geom H mask W v = some c ∧ starValid Geom H mask v W then
              posteriorMean Geom H mask O v c W (nbrLabels vWord ω.2) x else 0)) := by
    unfold FinLaw.E
    calc
      _ = ∑ W, ∑ ω, ∑ c, (H.recLaw p).w W *
          ((refLaw Geom H mask O W).w ω *
            if selected Geom H mask W v = some c ∧ starValid Geom H mask v W then
              posteriorMean Geom H mask O v c W (nbrLabels v.1 ω.2) x else 0) := by
            apply Finset.sum_congr rfl
            intro W hW
            rw [Finset.mul_sum]
            apply Finset.sum_congr rfl
            intro ω hω
            change (H.recLaw p).w W * ((refLaw Geom H mask O W).w ω *
              (∑ c : H.Center,
                if selected Geom H mask W v = some c ∧ starValid Geom H mask v W then
                  posteriorMean Geom H mask O v c W (nbrLabels vWord ω.2) x else 0)) =
              ∑ c : H.Center, (H.recLaw p).w W *
                ((refLaw Geom H mask O W).w ω *
                  if selected Geom H mask W v = some c ∧ starValid Geom H mask v W then
                    posteriorMean Geom H mask O v c W (nbrLabels vWord ω.2) x else 0)
            rw [Finset.mul_sum]
            rw [Finset.mul_sum]
      _ = ∑ W, ∑ c, ∑ ω, (H.recLaw p).w W *
          ((refLaw Geom H mask O W).w ω *
            if selected Geom H mask W v = some c ∧ starValid Geom H mask v W then
              posteriorMean Geom H mask O v c W (nbrLabels v.1 ω.2) x else 0) := by
            apply Finset.sum_congr rfl
            intro W hW
            rw [Finset.sum_comm]
      _ = ∑ c, ∑ W, ∑ ω, (H.recLaw p).w W *
          ((refLaw Geom H mask O W).w ω *
            if selected Geom H mask W v = some c ∧ starValid Geom H mask v W then
              posteriorMean Geom H mask O v c W (nbrLabels v.1 ω.2) x else 0) :=
            Finset.sum_comm
      _ = ∑ c, (H.recLaw p).E (fun W =>
          (refLaw Geom H mask O W).E (fun ω =>
            if selected Geom H mask W v = some c ∧ starValid Geom H mask v W then
              posteriorMean Geom H mask O v c W (nbrLabels v.1 ω.2) x else 0)) := by
            apply Finset.sum_congr rfl
            intro c hc
            unfold FinLaw.E
            apply Finset.sum_congr rfl
            intro W hW
            rw [Finset.mul_sum]
  have hcenterHist (c : H.Center) :
      (H.recLaw p).E (fun W => (refLaw Geom H mask O W).E (fun ω =>
        if selected Geom H mask W v = some c ∧ starValid Geom H mask v W then
          posteriorMean Geom H mask O v c W (nbrLabels v.1 ω.2) x else 0)) =
      (H.recLaw p).E (fun W =>
        if selected Geom H mask W v = some c ∧ starValid Geom H mask v W then
          (∑ r, if H.tuple W c r = x then (1 : ℝ) else 0) / 𝒯.kScale i else 0) := by
    let e := Equiv.piSplitAt (Sum.inl c) H.Val
    let fL : (∀ r, H.Val r) → ℝ := fun W =>
      (refLaw Geom H mask O W).E (fun ω =>
        if selected Geom H mask W v = some c ∧ starValid Geom H mask v W then
          posteriorMean Geom H mask O v c W (nbrLabels v.1 ω.2) x else 0)
    let fR : (∀ r, H.Val r) → ℝ := fun W =>
      if selected Geom H mask W v = some c ∧ starValid Geom H mask v W then
        (∑ r, if H.tuple W c r = x then (1 : ℝ) else 0) / 𝒯.kScale i else 0
    let rwLaw (rest : ∀ r : {r // r ≠ Sum.inl c}, H.Val r.1) : ℝ :=
      ∏ r : {r // r ≠ Sum.inl c}, H.lawRec p r.1 (rest r)
    have hWreplace (rest : ∀ r : {r // r ≠ Sum.inl c}, H.Val r.1)
        (u : mesh.V) (w₀ w : H.Tuple) (bits : Bool × Bool) :
        e.symm ((u, (w, bits)), rest) =
          H.replaceTuple (e.symm ((u, (w₀, bits)), rest)) c w := by
      funext r
      by_cases hr : r = Sum.inl c
      · subst r
        simp [e, Equiv.piSplitAt, Equiv.symm, PrimitiveHistory.replaceTuple,
          PrimitiveHistory.cornerOf, PrimitiveHistory.present, PrimitiveHistory.active]
      · simp [e, Equiv.piSplitAt, Equiv.symm, PrimitiveHistory.replaceTuple, hr]
    have hTupleAvg (rest : ∀ r : {r // r ≠ Sum.inl c}, H.Val r.1)
        (u : mesh.V) (bits : Bool × Bool) :
        (H.tuplePrior u).E (fun w => fL (e.symm ((u, (w, bits)), rest))) =
          (H.tuplePrior u).E (fun w => fR (e.symm ((u, (w, bits)), rest))) := by
      let w₀ := Classical.choice
        (HypercubeRamsey.Lane_q_s14_post.finLaw_nonempty (H.tuplePrior u))
      let Wbase := e.symm ((u, (w₀, bits)), rest)
      have htuple (w : H.Tuple) : H.tuple (e.symm ((u, (w, bits)), rest)) c = w := by
        rw [hWreplace rest u w₀ w bits]
        simp [PrimitiveHistory.tuple, PrimitiveHistory.replaceTuple]
      have hleft (w : H.Tuple) :
          fL (e.symm ((u, (w, bits)), rest)) =
            ∑ ys, subLikelihood Geom H mask O v c (H.replaceTuple Wbase c w) w ys *
              posteriorMean Geom H mask O v c (H.replaceTuple Wbase c w) ys x := by
        dsimp [fL]
        rw [hWreplace rest u w₀ w bits]
        rw [hselProb c (H.replaceTuple Wbase c w)]
        rw [show H.tuple (H.replaceTuple Wbase c w) c = w by
          simp [PrimitiveHistory.tuple, PrimitiveHistory.replaceTuple]]
      have hright (w : H.Tuple) :
          fR (e.symm ((u, (w, bits)), rest)) =
            if selected Geom H mask (H.replaceTuple Wbase c w) v = some c ∧
              starValid Geom H mask v (H.replaceTuple Wbase c w) then
              (∑ r, if w r = x then (1 : ℝ) else 0) / 𝒯.kScale i else 0 := by
        simp [fR, Wbase, hWreplace rest u w₀ w bits, PrimitiveHistory.tuple,
          PrimitiveHistory.replaceTuple]
      have hcorner : H.cornerOf Wbase c = u := by
        simp [Wbase, e, Equiv.piSplitAt, Equiv.symm, PrimitiveHistory.cornerOf]
      calc
        _ = ∑ w, (H.tuplePrior u).w w *
            (∑ ys, subLikelihood Geom H mask O v c (H.replaceTuple Wbase c w) w ys *
              posteriorMean Geom H mask O v c (H.replaceTuple Wbase c w) ys x) := by
              unfold FinLaw.E
              apply Finset.sum_congr rfl
              intro w hw
              exact congrArg ((H.tuplePrior u).w w * ·) (hleft w)
        _ = ∑ w, (H.tuplePrior u).w w *
            (if selected Geom H mask (H.replaceTuple Wbase c w) v = some c ∧
              starValid Geom H mask v (H.replaceTuple Wbase c w) then
              (∑ r, if w r = x then (1 : ℝ) else 0) / 𝒯.kScale i else 0) := by
              simpa [hcorner] using (hcenterTuple c Wbase)
        _ = _ := by
              unfold FinLaw.E
              apply Finset.sum_congr rfl
              intro w hw
              exact (congrArg ((H.tuplePrior u).w w * ·) (hright w)).symm
    have hcenterE (rest : ∀ r : {r // r ≠ Sum.inl c}, H.Val r.1) :
        (H.record p (Sum.inl c)).E (fun z => fL (e.symm (z, rest))) =
          (H.record p (Sum.inl c)).E (fun z => fR (e.symm (z, rest))) := by
      rw [hcenterExpSwap c (fun z => fL (e.symm (z, rest))),
        hcenterExpSwap c (fun z => fR (e.symm (z, rest)))]
      change
        (PrimitiveHistory.vertexLaw p).E (fun u =>
          bitPairLaw.E (fun bits =>
            (H.tuplePrior u).E (fun w => fL (e.symm ((u, (w, bits)), rest))))) =
        (PrimitiveHistory.vertexLaw p).E (fun u =>
          bitPairLaw.E (fun bits =>
            (H.tuplePrior u).E (fun w => fR (e.symm ((u, (w, bits)), rest)))))
      apply Finset.sum_congr rfl
      intro u hu
      apply congrArg ((PrimitiveHistory.vertexLaw p).w u * ·)
      unfold FinLaw.E
      apply Finset.sum_congr rfl
      intro bits hbits
      exact congrArg (bitPairLaw.w bits * ·) (hTupleAvg rest u bits)
    have hcommute (F : (∀ r, H.Val r) → ℝ) :
        (∑ z, H.lawRec p (Sum.inl c) z *
          ∑ rest : (∀ r : {r // r ≠ Sum.inl c}, H.Val r.1),
            rwLaw rest * F (e.symm (z, rest))) =
        ∑ rest : (∀ r : {r // r ≠ Sum.inl c}, H.Val r.1),
          rwLaw rest * ∑ z, H.lawRec p (Sum.inl c) z * F (e.symm (z, rest)) := by
      calc
        _ = ∑ z, ∑ rest, H.lawRec p (Sum.inl c) z *
              (rwLaw rest * F (e.symm (z, rest))) := by
                apply Finset.sum_congr rfl
                intro z hz
                rw [Finset.mul_sum]
        _ = ∑ rest, ∑ z, H.lawRec p (Sum.inl c) z *
              (rwLaw rest * F (e.symm (z, rest))) := Finset.sum_comm
        _ = ∑ rest, rwLaw rest * ∑ z,
              H.lawRec p (Sum.inl c) z * F (e.symm (z, rest)) := by
                apply Finset.sum_congr rfl
                intro rest hrest
                rw [Finset.mul_sum]
                apply Finset.sum_congr rfl
                intro z hz
                ring
    change (∑ W, (H.recLaw p).w W * fL W) =
      ∑ W, (H.recLaw p).w W * fR W
    rw [hrecordSplit c fL, hrecordSplit c fR]
    calc
      _ = ∑ rest : ∀ r : {r // r ≠ Sum.inl c}, H.Val r.1,
          rwLaw rest * ∑ z, H.lawRec p (Sum.inl c) z * fL (e.symm (z, rest)) := hcommute fL
      _ = ∑ rest : ∀ r : {r // r ≠ Sum.inl c}, H.Val r.1,
          rwLaw rest * ∑ z, H.lawRec p (Sum.inl c) z * fR (e.symm (z, rest)) := by
            apply Finset.sum_congr rfl
            intro rest hrest
            have hc := hcenterE rest
            change (∑ z, H.lawRec p (Sum.inl c) z * fL (e.symm (z, rest))) =
              ∑ z, H.lawRec p (Sum.inl c) z * fR (e.symm (z, rest)) at hc
            exact congrArg (rwLaw rest * ·) hc
      _ = _ := (hcommute fR).symm
  have hpostLeSel : ∀ W ys, postMass W ys ≤ selMass W ys := by
    intro W ys
    cases hs : selected Geom H mask W v with
    | none => simp [postMass, selMass, hs]
    | some c =>
      by_cases hv : starValid Geom H mask v W
      · by_cases hg : posteriorGate Geom H mask O L v c W ys
        · simp [postMass, selMass, hs, hv, hg]
        · have hnonneg := hpm0 c W ys
          simpa [postMass, selMass, hs, hv, hg] using hnonneg
      · have hg : ¬ posteriorGate Geom H mask O L v c W ys := by
          intro h
          exact hv h.2.1
        simp [postMass, selMass, hs, hv, hg]
  have hreduce :
      (H.recLaw p).E (fun W =>
        (refLaw Geom H mask O W).E (fun ω => R.σ v W (nbrLabels v.1 ω.2) x)) ≤
        (200 / κ.a) * (H.recLaw p).E (fun W =>
          (refLaw Geom H mask O W).E (fun ω => selMass W (nbrLabels v.1 ω.2))) := by
    have hrow (W : ∀ r, H.Val r)
        (ω : (Group 𝒯 i → Bin 𝒯 i) × (IWord 𝒯 i → Fin (T.S.N k))) :
        R.σ v W (nbrLabels v.1 ω.2) x ≤
          (200 / κ.a) * selMass W (nbrLabels v.1 ω.2) := by
      calc
        R.σ v W (nbrLabels v.1 ω.2) x ≤
            (200 / κ.a) * postMass W (nbrLabels v.1 ω.2) := hpoint W _
        _ ≤ (200 / κ.a) * selMass W (nbrLabels v.1 ω.2) :=
          mul_le_mul_of_nonneg_left (hpostLeSel W _) (by positivity)
    unfold FinLaw.E
    calc
      _ ≤ ∑ W, (H.recLaw p).w W *
          ((200 / κ.a) * ∑ ω, (refLaw Geom H mask O W).w ω *
            selMass W (nbrLabels v.1 ω.2)) := by
            apply Finset.sum_le_sum
            intro W hW
            apply mul_le_mul_of_nonneg_left _ ((H.recLaw p).nonneg W)
            change (∑ ω, (refLaw Geom H mask O W).w ω *
                R.σ v W (nbrLabels v.1 ω.2) x) ≤
              (200 / κ.a) * ∑ ω, (refLaw Geom H mask O W).w ω *
                selMass W (nbrLabels v.1 ω.2)
            rw [Finset.mul_sum]
            apply Finset.sum_le_sum
            intro ω hω
            calc
              (refLaw Geom H mask O W).w ω * R.σ v W (nbrLabels v.1 ω.2) x ≤
                  (refLaw Geom H mask O W).w ω *
                    ((200 / κ.a) * selMass W (nbrLabels v.1 ω.2)) :=
                mul_le_mul_of_nonneg_left (hrow W ω)
                  ((refLaw Geom H mask O W).nonneg ω)
              _ = (200 / κ.a) *
                  ((refLaw Geom H mask O W).w ω * selMass W (nbrLabels v.1 ω.2)) := by ring
      _ = (200 / κ.a) * ∑ W, (H.recLaw p).w W *
          ∑ ω, (refLaw Geom H mask O W).w ω * selMass W (nbrLabels v.1 ω.2) := by
            rw [Finset.mul_sum]
            apply Finset.sum_congr rfl
            intro W hW
            ring
  have hselInc :
      (H.recLaw p).E (fun W =>
        (refLaw Geom H mask O W).E (fun ω => selMass W (nbrLabels v.1 ω.2))) =
        (H.recLaw p).E (fun W =>
          if starValid Geom H mask v W then
            match selected Geom H mask W v with
            | none => 0
            | some c => (∑ r, if H.tuple W c r = x then (1 : ℝ) else 0) /
                𝒯.kScale i else 0) := by
    calc
      _ = ∑ c, (H.recLaw p).E (fun W =>
          (refLaw Geom H mask O W).E (fun ω =>
            if selected Geom H mask W v = some c ∧ starValid Geom H mask v W then
              posteriorMean Geom H mask O v c W (nbrLabels v.1 ω.2) x else 0)) :=
            hselExpectedExpand
      _ = ∑ c, (H.recLaw p).E (fun W =>
          if selected Geom H mask W v = some c ∧ starValid Geom H mask v W then
            (∑ r, if H.tuple W c r = x then (1 : ℝ) else 0) / 𝒯.kScale i else 0) := by
            apply Finset.sum_congr rfl
            intro c hc
            exact hcenterHist c
      _ = (H.recLaw p).E (fun W =>
          if starValid Geom H mask v W then
            match selected Geom H mask W v with
            | none => 0
            | some c => (∑ r, if H.tuple W c r = x then (1 : ℝ) else 0) /
                𝒯.kScale i else 0) := by
            unfold FinLaw.E
            rw [Finset.sum_comm]
            apply Finset.sum_congr rfl
            intro W hW
            cases hs : selected Geom H mask W v with
            | none => by_cases hv : starValid Geom H mask v W <;> simp [hs, hv]
            | some c => by_cases hv : starValid Geom H mask v W <;> simp [hs, hv]
  calc
    _ ≤ (200 / κ.a) * (H.recLaw p).E (fun W =>
        if starValid Geom H mask v W then
          match selected Geom H mask W v with
          | none => 0
          | some c => (∑ r, if H.tuple W c r = x then (1 : ℝ) else 0) /
              𝒯.kScale i else 0) := by rw [← hselInc]; exact hreduce
    _ ≤ (200 / κ.a) * (16 / (𝒯.P i).M) :=
      mul_le_mul_of_nonneg_left (hinc p v x) (by positivity)
    _ = rowMeanConstant κ / (𝒯.P i).M := by
      simp [rowMeanConstant]
      <;> ring

/-- P14.1k: tests are exactly validity plus the raw predictive failure bound. -/
theorem posterior_good_tests (κ : CConsts) (hκ : κ.Admissible)
    (hconst : HeightConstantContract κ)
    {T : Stage} {k : ℕ} {𝒯 : Tiling κ T k} (h𝒯 : Tiling.Valid 𝒯)
    {i : Fin 𝒯.m} {mesh : Mesh 𝒯} (scales : PatchScales 𝒯 i)
    (Geom : ProjectionGeometry κ 𝒯 i) (H : PrimitiveHistory κ 𝒯 i mesh)
    (mask : Masks H) (O : OddKernels Geom H mask) (L : LikelihoodData Geom H mask O)
    (R : EvenRows Geom H mask O L) (hh : HeightFacts hconst Geom H mask) :
    Nonempty (GoodTests Geom H mask O L R) := by
  classical
  refine ⟨{
    Hgood := goodTest Geom H mask O L R
    Hgood_eq := rfl
    zero_bound := ?_
    bad_bound := ?_
  }⟩
  · intro v W hgood
    exact hgood.2
  · intro p
    let hp := (𝒯.P i).h
    let Vh : ℕ :=
      ∑ j ∈ Finset.range (⌊κ.ρ * hp⌋₊ + 1), Nat.choose hp j
    let Hh := topScale hp (κ.ω / 100) (κ.ω / 30)
    let eps := sliceEps κ hp
    let rate : ℝ := (Vh : ℝ) * (Hh + 1 : ℝ) *
      Real.exp (-0.01 * κ.a * (sliceK κ hp : ℝ) * hp)
    let badValidity : (∀ r, H.Val r) → Prop := fun W =>
      ∃ v, ¬ starValid Geom H mask v W
    let failProb : EvenRole 𝒯 i → (∀ r, H.Val r) → ℝ := fun v W =>
      (refLaw Geom H mask O W).pr
        (fun ω => R.σ v W (nbrLabels v.1 ω.2) = 0)
    let failMass : EvenRole 𝒯 i → (∀ r, H.Val r) → ℝ := fun v W =>
      if starValid Geom H mask v W then failProb v W else 0
    let badAbove : (∀ r, H.Val r) → Prop := fun W =>
      ∃ v, starValid Geom H mask v W ∧ eps < failProb v W
    have heps : 0 < eps := by
      dsimp [eps, sliceEps]
      exact Real.exp_pos _
    have hslack := hconst.threshold_slack hp scales.h_large
    rcases hslack with ⟨_, _, _, _, _, _, _, _, _, hpost, _, _, hfinal⟩
    have hpost' :
        (2 : ℝ) ^ hp * (Vh : ℝ) * (Hh + 1 : ℝ) *
          Real.exp (-0.01 * κ.a * (sliceK κ hp : ℝ) * hp) / eps ≤
            Real.exp (-Real.rpow (hp : ℝ) (1 + hconst.sliceExponent)) := by
      simpa [Section14Numerics, hp, Vh, Hh, eps, sliceEps] using hpost
    have hfinal' :
        2 * Real.exp (-Real.rpow (hp : ℝ) (1 + hconst.globalExponent)) +
          4 * Real.exp (-Real.rpow (hp : ℝ) (1 + hconst.sliceExponent)) ≤
            Real.exp (-Real.rpow (hp : ℝ) (1 + κ.c14)) := by
      simpa [Section14Numerics, hp, Vh, Hh, eps, sliceEps] using hfinal
    have hraw_nonneg (v : EvenRole 𝒯 i) (W : ∀ r, H.Val r) :
        0 ≤ failProb v W := by
      unfold failProb FinLaw.pr
      apply Finset.sum_nonneg
      intro ω hω
      split_ifs
      · exact (refLaw Geom H mask O W).nonneg ω
      · exact le_rfl
    have hmass_nonneg (v : EvenRole 𝒯 i) (W : ∀ r, H.Val r) :
        0 ≤ failMass v W := by
      by_cases hv : starValid Geom H mask v W
      · simp [failMass, hv]
        exact hraw_nonneg v W
      · simp [failMass, hv]
    have hroleMean (v : EvenRole 𝒯 i) :
        (H.recLaw p).E (fun W => failMass v W) ≤ rate := by
      sorry
    have hroleAbove (v : EvenRole 𝒯 i) :
        (H.recLaw p).pr (fun W =>
          starValid Geom H mask v W ∧ eps < failProb v W) ≤ rate / eps := by
      have hsub : ∀ W,
          (starValid Geom H mask v W ∧ eps < failProb v W) → eps < failMass v W := by
        intro W hW
        simpa [failMass, hW.1] using hW.2
      calc
        _ ≤ (H.recLaw p).pr (fun W => eps < failMass v W) :=
          HypercubeRamsey.Lane_q_s14_post.finLaw_pr_mono
            (H.recLaw p) _ _ hsub
        _ ≤ (H.recLaw p).E (failMass v) / eps :=
          HypercubeRamsey.Lane_q_s14_post.finLaw_markov
            (H.recLaw p) (failMass v) eps heps (hmass_nonneg v)
        _ ≤ rate / eps := div_le_div_of_nonneg_right (hroleMean v) heps.le
    have hcardRoles : Fintype.card (EvenRole 𝒯 i) ≤ 2 ^ hp := by
      calc
        _ ≤ Fintype.card (IWord 𝒯 i) :=
          Fintype.card_le_of_injective Subtype.val Subtype.val_injective
        _ = 2 ^ hp := by simp [IWord, CubePos, hp]
    have hcardRolesReal :
        (Fintype.card (EvenRole 𝒯 i) : ℝ) ≤ (2 : ℝ) ^ hp := by
      exact_mod_cast hcardRoles
    have habove : (H.recLaw p).pr badAbove ≤
        Real.exp (-Real.rpow (hp : ℝ) (1 + hconst.sliceExponent)) := by
      calc
        _ ≤ ∑ v : EvenRole 𝒯 i, (H.recLaw p).pr (fun W =>
              starValid Geom H mask v W ∧ eps < failProb v W) :=
          HypercubeRamsey.Lane_q_s14_post.finLaw_pr_exists_le_sum
            (H.recLaw p) (fun v W =>
              starValid Geom H mask v W ∧ eps < failProb v W)
        _ ≤ ∑ v : EvenRole 𝒯 i, rate / eps := by
          apply Finset.sum_le_sum
          intro v hv
          exact hroleAbove v
        _ = (Fintype.card (EvenRole 𝒯 i) : ℝ) * (rate / eps) := by
          simp [Finset.sum_const, nsmul_eq_mul]
        _ ≤ (2 : ℝ) ^ hp * (rate / eps) :=
          mul_le_mul_of_nonneg_right hcardRolesReal (div_nonneg (by positivity) heps.le)
        _ ≤ Real.exp (-Real.rpow (hp : ℝ) (1 + hconst.sliceExponent)) := by
          have hrewrite : (2 : ℝ) ^ hp * (rate / eps) =
              (2 : ℝ) ^ hp * (Vh : ℝ) * (Hh + 1 : ℝ) *
                Real.exp (-0.01 * κ.a * (sliceK κ hp : ℝ) * hp) / eps := by
            dsimp [rate]
            field_simp [ne_of_gt heps]
            <;> ring
          rw [hrewrite]
          exact hpost'
    have hbadSplit : ∀ W, (∃ v, ¬ goodTest Geom H mask O L R v W) →
        badValidity W ∨ badAbove W := by
      intro W hW
      rcases hW with ⟨v, hvbad⟩
      unfold goodTest at hvbad
      by_cases hv : starValid Geom H mask v W
      · right
        refine ⟨v, hv, ?_⟩
        exact lt_of_not_ge (fun hle => hvbad ⟨hv, hle⟩)
      · exact Or.inl ⟨v, hv⟩
    have hbadProb : (H.recLaw p).pr
        (fun W => ∃ v, ¬ goodTest Geom H mask O L R v W) ≤
          (H.recLaw p).pr badValidity + (H.recLaw p).pr badAbove := by
      calc
        _ ≤ (H.recLaw p).pr (fun W => badValidity W ∨ badAbove W) :=
          HypercubeRamsey.Lane_q_s14_post.finLaw_pr_mono
            (H.recLaw p) _ _ hbadSplit
        _ ≤ (H.recLaw p).pr badValidity + (H.recLaw p).pr badAbove :=
          HypercubeRamsey.Lane_q_s14_post.finLaw_pr_or_le_add
            (H.recLaw p) badValidity badAbove
    have hvalid := hh.validity_good p
    calc
      _ ≤ (H.recLaw p).pr badValidity + (H.recLaw p).pr badAbove := hbadProb
      _ ≤ (Real.exp (-Real.rpow (hp : ℝ) (1 + hconst.globalExponent)) +
            2 * Real.exp (-Real.rpow (hp : ℝ) (1 + hconst.sliceExponent))) +
            Real.exp (-Real.rpow (hp : ℝ) (1 + hconst.sliceExponent)) :=
          add_le_add hvalid habove
      _ ≤ 2 * Real.exp (-Real.rpow (hp : ℝ) (1 + hconst.globalExponent)) +
            4 * Real.exp (-Real.rpow (hp : ℝ) (1 + hconst.sliceExponent)) := by
          nlinarith [le_of_lt (Real.exp_pos (-Real.rpow (hp : ℝ)
            (1 + hconst.globalExponent))),
            le_of_lt (Real.exp_pos (-Real.rpow (hp : ℝ)
            (1 + hconst.sliceExponent)))]
      _ ≤ Real.exp (-Real.rpow (hp : ℝ) (1 + κ.c14)) := hfinal'

/-- P14.1l: locality and complete symmetry for the concrete rules, including
search, choice, validity, posterior and predictive-test computations. -/
theorem locality_and_symmetry (κ : CConsts) (hκ : κ.Admissible)
    (hconst : HeightConstantContract κ)
    {T : Stage} {k : ℕ} {𝒯 : Tiling κ T k} (h𝒯 : Tiling.Valid 𝒯)
    {i : Fin 𝒯.m} {mesh : Mesh 𝒯} (scales : PatchScales 𝒯 i)
    (Geom : ProjectionGeometry κ 𝒯 i) (H : PrimitiveHistory κ 𝒯 i mesh)
    (mask : Masks H) (hlookup : MaskLookup H mask) (O : OddKernels Geom H mask)
    (L : LikelihoodData Geom H mask O) (R : EvenRows Geom H mask O L)
    (Tests : GoodTests Geom H mask O L R) (hh : HeightFacts hconst Geom H mask) :
    Nonempty (LocalSymmetry Geom H mask O L R Tests) := by
  classical
  have hgeometry (g g' : Group 𝒯 i) :
      ∃ (e : IWord 𝒯 i ≃ IWord 𝒯 i)
        (eg : Group 𝒯 i ≃ Group 𝒯 i) (ev : EvenRole 𝒯 i ≃ EvenRole 𝒯 i),
        eg g = g' ∧ (∀ a, (eg a).1 = e a.1) ∧
        (∀ v, (ev v).1 = e v.1) ∧
        (∀ z l, e (flipPos z l) = flipPos (e z) l) ∧
        (∀ z z', hammingDist (e z) (e z') = hammingDist z z') ∧
        (∀ z, Geom.project (e z) = e (Geom.project z)) := by
    let s := Lane_sol_s14_lik.shift g.1 g'.1
    have hsEven : IsEvenRole s :=
      (Lane_sol_s14_lik.shift_even g.1 g'.1 g.2.1).mpr g'.2.1
    have hsZero : wordSyndrome s = 0 := by
      rw [Lane_sol_s14_lik.shift_syndrome, g.2.2, g'.2.2, zero_add]
    let e := Lane_sol_s14_lik.shiftEquiv s
    have hsynd (z : IWord 𝒯 i) : wordSyndrome (e z) = wordSyndrome z := by
      change wordSyndrome (Lane_sol_s14_lik.shift s z) = _
      rw [Lane_sol_s14_lik.shift_syndrome, hsZero, zero_add]
    let eg : Group 𝒯 i ≃ Group 𝒯 i := Equiv.subtypeEquiv e (fun z => by
      change (IsEvenRole z ∧ wordSyndrome z = 0) ↔
        (IsEvenRole (e z) ∧ wordSyndrome (e z) = 0)
      rw [hsynd]
      have hp : IsEvenRole z ↔ IsEvenRole (e z) :=
        (Lane_sol_s14_lik.shift_even s z hsEven).symm
      exact and_congr hp Iff.rfl)
    let ev : EvenRole 𝒯 i ≃ EvenRole 𝒯 i :=
      Equiv.subtypeEquiv e (fun z => (Lane_sol_s14_lik.shift_even s z hsEven).symm)
    have htarget : eg g = g' := by
      apply Subtype.ext
      change Lane_sol_s14_lik.shift (Lane_sol_s14_lik.shift g.1 g'.1) g.1 = g'.1
      funext l
      cases hg : g.1 l <;> cases hg' : g'.1 l <;> simp [Lane_sol_s14_lik.shift, hg, hg']
    refine ⟨e, eg, ev, htarget, (fun _ => rfl), (fun _ => rfl),
      (fun z l => Lane_sol_s14_lik.shift_flip s z l),
      (fun z z' => Lane_sol_s14_lik.shift_distance s z z'), ?_⟩
    intro z
    have hindex : Geom.syndromeIndex (e z) = Geom.syndromeIndex z := by
      apply Fin.ext
      apply Nat.eq_of_testBit_eq
      intro j
      apply Bool.eq_iff_iff.mpr
      rw [Geom.syndromeIndex_spec, Geom.syndromeIndex_spec]
      rw [hsynd]
    rw [Geom.project_eq, Geom.project_eq, hindex]
    exact (Lane_sol_s14_lik.shift_flip s z _).symm
  have hincidenceTransport (e : IWord 𝒯 i ≃ IWord 𝒯 i)
      (eg : Group 𝒯 i ≃ Group 𝒯 i) (ev : EvenRole 𝒯 i ≃ EvenRole 𝒯 i)
      (hgroup : ∀ a, (eg a).1 = e a.1) (hrole : ∀ v, (ev v).1 = e v.1)
      (hflip : ∀ z l, e (flipPos z l) = flipPos (e z) l)
      (v : EvenRole 𝒯 i) (a : Group 𝒯 i) :
      ev v ∈ groupNeighborhood (eg a) ↔ v ∈ groupNeighborhood a := by
    simp only [groupNeighborhood, Finset.mem_filter, Finset.mem_univ, true_and,
      groupFiber, Finset.mem_image]
    simp_rw [hgroup, hrole, ← hflip]
    simp only [e.injective.eq_iff]

  have hmaskEqual (a b : Group 𝒯 i) (W W' : ∀ r, H.Val r)
      (hvertex : H.maskVertex a W = H.maskVertex b W') :
      (mask a W).prior = (mask b W').prior ∧ (mask a W).within = (mask b W').within := by
    have hcheap (D : Bin 𝒯 i) : (mask a W).cheap D = (mask b W').cheap D := by
      rw [(mask a W).cheap_eq, (mask b W').cheap_eq, hvertex]
    have hret : (mask a W).retained = (mask b W').retained := by
      ext D
      rw [(mask a W).retained_spec, (mask b W').retained_spec, hcheap]
    constructor
    · funext D
      rw [(mask a W).prior_uniform, (mask b W').prior_uniform, hret]
    · funext D y
      rw [(mask a W).within_uniform, (mask b W').within_uniform, hret, hcheap]
  have hrecordTransport (ec : H.Center ≃ H.Center) (eg : Group 𝒯 i ≃ Group 𝒯 i)
      (pl : SearchPerm H.Device (𝒯.tScale i)) (pc : H.Device.TiePerm) :
      ∃ eh : (∀ r, H.Val r) ≃ (∀ r, H.Val r),
        (∀ p W, (H.recLaw p).w (eh W) = (H.recLaw p).w W) ∧
        (∀ W c, (eh W) (.inl (ec c)) = W (.inl c)) ∧
        (∀ W a, (eh W) (.inr (.inl (eg a))) =
          ((W (.inr (.inl a))).1, (W (.inr (.inl a))).2.trans pl)) ∧
        (∀ W c, (eh W) (.inr (.inr (ec c))) = pc.symm.trans (W (.inr (.inr c)))) := by
    let er := Equiv.sumCongr ec (Equiv.sumCongr eg ec)
    let fiber : ∀ r, H.Val r ≃ H.Val (er r) := fun r => by
      cases r with
      | inl c => exact Equiv.refl _
      | inr r => cases r with
        | inl a => exact Equiv.prodCongr (Equiv.refl _) (Lane_sol_s14_lik.postcompose pl)
        | inr c => exact Lane_sol_s14_lik.precompose pc.symm
    let eh := Equiv.piCongr er fiber
    have hpres (p : mesh.Param) (r : H.Rec) (x : H.Val r) :
        (H.record p (er r)).w (fiber r x) = (H.record p r).w x := by
      cases r with
      | inl c => rfl
      | inr r => cases r with
        | inl a =>
          rcases x with ⟨u, σ⟩
          simp [PrimitiveHistory.record, er, fiber, Lane_sol_s14_lik.postcompose,
            PrimitiveHistory.groupLaw, FinLaw.bind, PrimitiveHistory.finProbToFinLaw,
            FinProb.uniformAll, FinProb.uniform] <;> rfl
        | inr c =>
          simp [PrimitiveHistory.record, er, fiber, Lane_sol_s14_lik.precompose,
            PrimitiveHistory.tieLaw, PrimitiveHistory.finProbToFinLaw,
            FinProb.uniformAll, FinProb.uniform]
    refine ⟨eh, ?_, ?_, ?_, ?_⟩
    · intro p W
      change (∏ r, (H.record p r).w (eh W r)) = ∏ r, (H.record p r).w (W r)
      rw [← er.prod_comp (fun r => (H.record p r).w (eh W r))]
      apply Finset.prod_congr rfl
      intro r _
      rw [show eh W (er r) = fiber r (W r) from Equiv.piCongr_apply_apply er fiber W r]
      exact hpres p r (W r)
    · intro W c
      exact Equiv.piCongr_apply_apply er fiber W (.inl c)
    · intro W a
      exact Equiv.piCongr_apply_apply er fiber W (.inr (.inl a))
    · intro W c
      exact Equiv.piCongr_apply_apply er fiber W (.inr (.inr c))

  sorry

/-- Canonical mask equations make every mask family a fixed vertex lookup. -/
theorem masks_are_lookups {κ : CConsts} {T : Stage} {k : ℕ}
    {𝒯 : Tiling κ T k} {i : Fin 𝒯.m} {mesh : Mesh 𝒯}
    (H : PrimitiveHistory κ 𝒯 i mesh) (mask : Masks H) : MaskLookup H mask := by
  sorry

/-- Supplement to D14.S: conditioning and pretrim preserve group symmetry. -/
def LowOutputInvariant {κ : CConsts} {T : Stage} {k : ℕ}
    {𝒯 : Tiling κ T k} {i : Fin 𝒯.m} {mesh : Mesh 𝒯}
    (S : SliceSolver κ 𝒯 i mesh) : Prop :=
  ∀ p g g' y, 𝒯.mode = .lowCluster → S.lowOut p g y = S.lowOut p g' y

/-- Field-by-field assembly of the shared solver interface. L14.3's independent
count node supplies `low_support`, rather than the eligibility theorem. -/
noncomputable def assembleSolver {κ : CConsts} {T : Stage} {k : ℕ}
    {𝒯 : Tiling κ T k} {i : Fin 𝒯.m} {mesh : Mesh 𝒯}
    (Geom : ProjectionGeometry κ 𝒯 i) (H : PrimitiveHistory κ 𝒯 i mesh)
    (mask : Masks H) (O : OddKernels Geom H mask) (L : LikelihoodData Geom H mask O)
    (R : EvenRows Geom H mask O L) (Tests : GoodTests Geom H mask O L R)
    (hsupp : RowSupport Geom H mask O L R) (hmean : RowMeanBound Geom H mask O L R)
    (hlocal : LocalSymmetry Geom H mask O L R Tests)
    (hlow : 𝒯.mode = .lowCluster → ∀ p,
      (((Finset.univ.filter fun W => 0 < (H.recLaw p).w W).card : ℕ) : ℝ) ≤
        Real.exp ((T.S.n k : ℝ) ^ (1.01 : ℝ))) : SliceSolver κ 𝒯 i mesh := {
  Rec := H.Rec
  recFin := H.instRecFintype
  loc := H.loc
  Val := H.Val
  valFin := H.instValFintype
  lawRec := H.lawRec
  lawRec_nonneg := fun p r x => (H.record p r).nonneg x
  lawRec_sum := fun p r => (H.record p r).sum_one
  lawRec_cont := primitive_law_continuous H
  groupOf := Geom.groupOf
  groupOf_spec := Geom.groupOf_spec
  group_partition := Geom.partition
  q := O.q
  U := O.U
  σ := R.σ
  Hgood := Tests.Hgood
  q_nonneg := O.q_nonneg
  q_sum := O.q_sum
  U_nonneg := O.U_nonneg
  U_sum := O.U_sum
  U_support := O.U_support
  q_cap := O.q_cap
  marginal_cap := O.marginal_cap
  U_support_size := O.U_support_size
  U_atom_cap := O.U_atom_cap
  σ_nonneg := R.nonneg
  σ_prob := R.probability
  σ_support := hsupp
  σ_cap := R.cap
  σ_mean := hmean
  Hgood_zero := Tests.zero_bound
  Hgood_bad := Tests.bad_bound
  q_local := hlocal.q_local
  U_local := hlocal.U_local
  σ_local := hlocal.σ_local
  Hgood_local := hlocal.Hgood_local
  averaged_marginal_invariant := hlocal.averaged_marginal_invariant
  low_support := hlow
}

set_option maxHeartbeats 2000000 in
/-- Law-preserving history transport carries the entire test event and the
conditional failure probabilities defining the pretrim bins. -/
theorem low_output_group_invariant {κ : CConsts} {T : Stage} {k : ℕ}
    {𝒯 : Tiling κ T k} {i : Fin 𝒯.m} {mesh : Mesh 𝒯}
    (Geom : ProjectionGeometry κ 𝒯 i) (H : PrimitiveHistory κ 𝒯 i mesh)
    (mask : Masks H) (O : OddKernels Geom H mask) (L : LikelihoodData Geom H mask O)
    (R : EvenRows Geom H mask O L) (Tests : GoodTests Geom H mask O L R)
    (hsupp : RowSupport Geom H mask O L R) (hmean : RowMeanBound Geom H mask O L R)
    (hlocal : LocalSymmetry Geom H mask O L R Tests)
    (hlow : 𝒯.mode = .lowCluster → ∀ p,
      (((Finset.univ.filter fun W => 0 < (H.recLaw p).w W).card : ℕ) : ℝ) ≤
        Real.exp ((T.S.n k : ℝ) ^ (1.01 : ℝ))) :
    LowOutputInvariant (assembleSolver Geom H mask O L R Tests hsupp hmean hlocal hlow) := by
  classical
  let S := assembleSolver Geom H mask O L R Tests hsupp hmean hlocal hlow
  change LowOutputInvariant S
  intro p g g' y hmode
  let Sym := hlocal.symmetry
  let e : (∀ r, S.Val r) ≃ (∀ r, S.Val r) := Sym.history g g'
  have hqTransport : ∀ W D, S.q g' (e W) D = S.q g W D := by
    intro W D
    have hqfun := Sym.q_preserved g g' W g
    change O.q g' (Sym.history g g' W) D = O.q g W D
    rw [Sym.groups_target] at hqfun
    exact congrFun hqfun D
  have hUTransport : ∀ W D, ∀ y, S.U g' (e W) D y = S.U g W D y := by
    intro W D y
    have hUfun := Sym.U_preserved g g' W g D
    change O.U g' (Sym.history g g' W) D y = O.U g W D y
    rw [Sym.groups_target] at hUfun
    exact congrFun hUfun y
  have hpre : ∀ W D,
      D ∈ S.pretrimBins W g ↔ D ∈ S.pretrimBins (e W) g' := by
    intro W D
    simp only [SliceSolver.pretrimBins, Finset.mem_filter, Finset.mem_univ, true_and]
    constructor
    · rintro ⟨hq, hfail⟩
      constructor
      · rw [hqTransport W D]
        exact hq
      · intro v hv
        have hv' : v ∈ groupNeighborhood g' := by
          simpa [SliceSolver.Incident, groupNeighborhood] using hv
        let v₀ := (Sym.roles g g').symm v
        have hrole : Sym.roles g g' v₀ = v := by simp [v₀]
        have hv₀' : Sym.roles g g' v₀ ∈ groupNeighborhood (Sym.groups g g' g) := by
          simpa [Sym.groups_target, hrole] using hv'
        have hv₀ : v₀ ∈ groupNeighborhood g :=
          (Sym.incidence_preserved g g' v₀ g).mp hv₀'
        have hv₀I : SliceSolver.Incident v₀ g := by
          simpa [SliceSolver.Incident, groupNeighborhood] using hv₀
        have hprob := Sym.row_failure_preserved g g' W v₀ g D
        have hprobS :
            (S.refLaw (e W)).pr (fun ω =>
              ω.1 g' = D ∧ S.σ v (e W) (nbrLabels v.1 ω.2) = 0) =
              (S.refLaw W).pr (fun ω =>
                ω.1 g = D ∧ S.σ v₀ W (nbrLabels v₀.1 ω.2) = 0) := by
          change (refLaw Geom H mask O (Sym.history g g' W)).pr (fun ω =>
              ω.1 g' = D ∧ R.σ v (Sym.history g g' W) (nbrLabels v.1 ω.2) = 0) =
            (refLaw Geom H mask O W).pr (fun ω =>
              ω.1 g = D ∧ R.σ v₀ W (nbrLabels v₀.1 ω.2) = 0)
          simpa only [Sym.groups_target, hrole] using hprob
        have hineq := hfail v₀ hv₀I
        rw [hprobS, hqTransport]
        exact hineq
    · rintro ⟨hq, hfail⟩
      constructor
      · rw [← hqTransport W D]
        exact hq
      · intro v hv
        have hv₀ : v ∈ groupNeighborhood g := by
          simpa [SliceSolver.Incident, groupNeighborhood] using hv
        have hv' : Sym.roles g g' v ∈ groupNeighborhood g' := by
          have hi := Sym.incidence_preserved g g' v g
          simpa [Sym.groups_target] using hi.mpr hv₀
        have hv'I : SliceSolver.Incident (Sym.roles g g' v) g' := by
          simpa [SliceSolver.Incident, groupNeighborhood] using hv'
        have hprob := Sym.row_failure_preserved g g' W v g D
        have hprobS :
            (S.refLaw (e W)).pr (fun ω =>
              ω.1 g' = D ∧ S.σ (Sym.roles g g' v) (e W)
                (nbrLabels (Sym.roles g g' v).1 ω.2) = 0) =
              (S.refLaw W).pr (fun ω =>
                ω.1 g = D ∧ S.σ v W (nbrLabels v.1 ω.2) = 0) := by
          change (refLaw Geom H mask O (Sym.history g g' W)).pr (fun ω =>
              ω.1 g' = D ∧ R.σ (Sym.roles g g' v) (Sym.history g g' W)
                (nbrLabels (Sym.roles g g' v).1 ω.2) = 0) =
            (refLaw Geom H mask O W).pr (fun ω =>
              ω.1 g = D ∧ R.σ v W (nbrLabels v.1 ω.2) = 0)
          simpa only [Sym.groups_target] using hprob
        have hineq := hfail (Sym.roles g g' v) hv'I
        rw [hprobS, hqTransport] at hineq
        exact hineq
  have hpreSet : ∀ W, S.pretrimBins W g = S.pretrimBins (e W) g' := by
    intro W
    ext D
    exact hpre W D
  have hqin : ∀ W D, S.qin W g D = S.qin (e W) g' D := by
    intro W D
    have hden :
        (∑ D' ∈ S.pretrimBins W g, S.q g W D') =
          ∑ D' ∈ S.pretrimBins (e W) g', S.q g' (e W) D' := by
      rw [hpreSet W]
      apply Finset.sum_congr rfl
      intro D' hD'
      simpa [S, assembleSolver] using (hqTransport W D').symm
    unfold SliceSolver.qin
    by_cases hmem : D ∈ S.pretrimBins W g
    · have hmem' := (hpre W D).mp hmem
      simp [hmem, hmem', hden, hqTransport W D]
    · have hmem' : D ∉ S.pretrimBins (e W) g' := by
        intro hm
        exact hmem ((hpre W D).mpr hm)
      simp [hmem, hmem']
  have hgood : ∀ W, S.AllGood W ↔ S.AllGood (e W) := by
    intro W
    change (∀ v, Tests.Hgood v W) ↔ (∀ v, Tests.Hgood v (e W))
    constructor
    · intro h v
      obtain ⟨v₀, hv₀⟩ := (Sym.roles g g').surjective v
      rw [← hv₀]
      exact (Sym.test_preserved g g' W v₀).mpr (h v₀)
    · intro h v
      exact (Sym.test_preserved g g' W v).mp (h (Sym.roles g g' v))
  have hinner : ∀ W,
      (if S.AllGood W then ∑ D, S.qin W g D * S.U g W D y else 0) =
        (if S.AllGood (e W) then ∑ D, S.qin (e W) g' D * S.U g' (e W) D y else 0) := by
    intro W
    by_cases hg : S.AllGood W
    · have hg' := (hgood W).mp hg
      simp only [hg, hg', ite_true]
      apply Finset.sum_congr rfl
      intro D hD
      have hq := hqin W D
      rw [hq, ← hUTransport W D y]
    · have hg' : ¬ S.AllGood (e W) := fun h => hg ((hgood W).mpr h)
      simp [hg, hg']
  have hnum :
      (∑ W, (S.recLaw p).w W *
        (if S.AllGood W then ∑ D, S.qin W g D * S.U g W D y else 0)) =
      ∑ W, (S.recLaw p).w W *
        (if S.AllGood W then ∑ D, S.qin W g' D * S.U g' W D y else 0) := by
    calc
      _ = ∑ W, (S.recLaw p).w (e W) *
          (if S.AllGood (e W) then ∑ D, S.qin (e W) g' D * S.U g' (e W) D y else 0) := by
            apply Finset.sum_congr rfl
            intro W hW
            have hw : (S.recLaw p).w (e W) = (S.recLaw p).w W := by
              change (H.recLaw p).w (Sym.history g g' W) = (H.recLaw p).w W
              exact Sym.law_preserved p g g' W
            rw [hinner W, ← hw]
      _ = ∑ W, (S.recLaw p).w W *
          (if S.AllGood W then ∑ D, S.qin W g' D * S.U g' W D y else 0) := by
            exact Equiv.sum_comp e (fun W => (S.recLaw p).w W *
              (if S.AllGood W then ∑ D, S.qin W g' D * S.U g' W D y else 0))
  change (S.lowOut p g y) = S.lowOut p g' y
  unfold SliceSolver.lowOut
  rw [hnum]

structure SolverWitness {κ : CConsts} {T : Stage} {k : ℕ}
    {𝒯 : Tiling κ T k} {i : Fin 𝒯.m} {mesh : Mesh 𝒯} where
  solver : SliceSolver κ 𝒯 i mesh
  low_output_invariant : LowOutputInvariant solver
  labels_uniform : ∀ g W D, 0 < solver.q g W D →
    ∃ support : Finset (Fin (T.S.N k)), ∃ hs : support.Nonempty,
      ∀ y, solver.U g W D y = (FinLaw.uniform support hs).w y
  cheap_raw_support : ∀ p g y, solver.oddMean p g y > 0 →
    ∃ v : mesh.V, 0 < mesh.wt v p ∧
      mesh.paramPrice (mesh.base v) i y ≤ 10 / (𝒯.P i).M

set_option maxHeartbeats 2000000 in
/-- Fixed-index P14.1 assembly; all eventual estimates are supplied explicitly. -/
theorem internal_slice_solver_at_patch (κ : CConsts) (hκ : κ.Admissible)
    (hconst : HeightConstantContract κ) (T : Stage)
    {k : ℕ} (𝒯 : Tiling κ T k) (h𝒯 : Tiling.Valid 𝒯)
    (hcluster : 𝒯.mode.isCluster) (mesh : Mesh 𝒯) (hclean : MeshCleaned mesh)
    (ready : MeshReady mesh) (i : Fin 𝒯.m) (scales : PatchScales 𝒯 i)
    (htest : GenericListBound κ 𝒯 i)
    (hfinite : ∀ H : PrimitiveHistory κ 𝒯 i mesh, 𝒯.mode = .lowCluster → ∀ p,
      (((Finset.univ.filter fun W => 0 < (H.recLaw p).w W).card : ℕ) : ℝ) ≤
        Real.exp ((T.S.n k : ℝ) ^ (1.01 : ℝ))) :
    Nonempty (SolverWitness (𝒯 := 𝒯) (i := i) (mesh := mesh)) := by
  classical
  obtain ⟨Geom⟩ := projection_geometry κ hκ 𝒯 h𝒯 hcluster i
  obtain ⟨H⟩ := primitive_history κ hκ 𝒯 h𝒯 hcluster i mesh hclean ready
  let mask : Masks H := fun g W =>
    Classical.choice (masks_and_price_cut κ hκ h𝒯 mesh hclean (H.maskVertex g W))
  have hlookup := masks_are_lookups H mask
  obtain ⟨Lists⟩ := candidate_list_models κ hκ h𝒯 hcluster scales Geom H mask
  have hcounts := position_count_concentration κ hκ hconst scales H
  have he := eligibility_from_tests κ hκ hconst h𝒯 hcluster scales Geom H mask hlookup Lists hcounts htest
  have hh := height_selection_at_patch κ hκ hconst h𝒯 hcluster scales Geom H mask hlookup he
  have hinc := forced_present_incidence κ hκ hconst h𝒯 hcluster scales Geom H mask hlookup hh
  obtain ⟨O⟩ := odd_bin_laws κ hκ hconst h𝒯 scales Geom H mask
  obtain ⟨L⟩ := likelihood_ratio_domination κ hκ hconst h𝒯 scales Geom H mask hlookup O
  obtain ⟨R⟩ := posterior_even_rows κ hκ h𝒯 scales Geom H mask O L
  have hsupp := posterior_row_support κ hκ Geom H mask O L R
  have hmean := posterior_row_mean κ hκ Geom H mask O L R hinc
  obtain ⟨Tests⟩ := posterior_good_tests κ hκ hconst h𝒯 scales Geom H mask O L R hh
  obtain ⟨hlocal⟩ := locality_and_symmetry κ hκ hconst h𝒯 scales Geom H mask hlookup O L R Tests hh
  let S := assembleSolver Geom H mask O L R Tests hsupp hmean hlocal (hfinite H)
  have hlow : LowOutputInvariant S :=
    low_output_group_invariant Geom H mask O L R Tests hsupp hmean hlocal (hfinite H)
  refine ⟨⟨S, hlow, O.U_uniform, ?_⟩⟩
  intro p g y hpos
  exact O.cheap_mean_support p g y hpos

/-- P14.1: the original S1–S8 conclusion, with explicit discrepancy, nonempty
mesh and retained-corner-mass inputs. Thresholds are chosen before all tilings. -/
theorem internal_slice_solver (κ : CConsts) (hκ : κ.Admissible)
    (hconst : HeightConstantContract κ) (T : Stage) (hinit : InitDisc T κ.η0) :
    ∀ᶠ k in atTop, ∀ (𝒯 : Tiling κ T k), Tiling.Valid 𝒯 → 𝒯.mode.isCluster →
      ∀ (mesh : Mesh 𝒯), MeshCleaned mesh → MeshReady mesh → ∀ i,
        Nonempty (SolverWitness (𝒯 := 𝒯) (i := i) (mesh := mesh)) := by
  have hscales := patch_scales κ hκ T
  have htests := generic_list_test κ hκ T hinit
  have hfinite := primitive_low_support κ hκ T
  filter_upwards [hscales, htests, hfinite] with k hscales htests hfinite
  intro 𝒯 h𝒯 hcluster mesh hclean ready i
  apply internal_slice_solver_at_patch κ hκ hconst T 𝒯 h𝒯 hcluster mesh hclean ready i
    (hscales 𝒯 h𝒯 hcluster i) (htests 𝒯 h𝒯 i)
  intro H hlow p
  exact hfinite 𝒯 h𝒯 hlow i mesh H p

end HypercubeRamsey.S14
