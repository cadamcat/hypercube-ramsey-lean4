import HypercubeRamsey.PartC.ProfiledTiling
import HypercubeRamsey.S03.Height.Selection
import HypercubeRamsey.S03.Mixtures
import HypercubeRamsey.Framework.FinProbLemmas

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
    (prior v).w x = if x ∈ mesh.corner v i then 1 / (mesh.corner v i).card else 0
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
  sorry

/-- Continuity is proved for the concrete product law, rather than assumed
for arbitrary tuple/position/activation decoders. -/
theorem primitive_law_continuous {κ : CConsts} {T : Stage} {k : ℕ}
    {𝒯 : Tiling κ T k} {i : Fin 𝒯.m} {mesh : Mesh 𝒯}
    (H : PrimitiveHistory κ 𝒯 i mesh) :
    ∀ r x, Continuous fun p => H.lawRec p r x := by
  sorry

/-- L14.3 count node, separate from the eligibility theorem. It counts actual
positive product-record outcomes, including categorical order permutations. -/
theorem primitive_low_support (κ : CConsts) (hκ : κ.Admissible) (T : Stage) :
    ∀ᶠ k in atTop, ∀ (𝒯 : Tiling κ T k), Tiling.Valid 𝒯 →
      𝒯.mode = .lowCluster → ∀ i mesh (H : PrimitiveHistory κ 𝒯 i mesh) p,
        (((Finset.univ.filter fun W => 0 < (H.recLaw p).w W).card : ℕ) : ℝ) ≤
          Real.exp ((T.S.n k : ℝ) ^ (1.01 : ℝ)) := by
  sorry

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
  sorry

theorem position_count_concentration (κ : CConsts) (hκ : κ.Admissible)
    (hconst : HeightConstantContract κ)
    {T : Stage} {k : ℕ} {𝒯 : Tiling κ T k} {i : Fin 𝒯.m} {mesh : Mesh 𝒯}
    (scales : PatchScales 𝒯 i) (H : PrimitiveHistory κ 𝒯 i mesh) :
    PositionCountConcentration hconst H := by
  sorry

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

/-- P14.1g: the specified probability reference and actual counterfactual likelihood. -/
theorem likelihood_ratio_domination (κ : CConsts) (hκ : κ.Admissible)
    (hconst : HeightConstantContract κ)
    {T : Stage} {k : ℕ} {𝒯 : Tiling κ T k} (h𝒯 : Tiling.Valid 𝒯)
    {i : Fin 𝒯.m} {mesh : Mesh 𝒯} (scales : PatchScales 𝒯 i)
    (Geom : ProjectionGeometry κ 𝒯 i) (H : PrimitiveHistory κ 𝒯 i mesh)
    (mask : Masks H) (hlookup : MaskLookup H mask) (O : OddKernels Geom H mask) :
    Nonempty (LikelihoodData Geom H mask O) := by
  sorry

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
  sorry

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
/-- P14.1i: exact posterior support; arbitrary capped rows are insufficient. -/
theorem posterior_row_support (κ : CConsts) (hκ : κ.Admissible)
    {T : Stage} {k : ℕ} {𝒯 : Tiling κ T k} {i : Fin 𝒯.m} {mesh : Mesh 𝒯}
    (Geom : ProjectionGeometry κ 𝒯 i) (H : PrimitiveHistory κ 𝒯 i mesh)
    (mask : Masks H) (O : OddKernels Geom H mask) (L : LikelihoodData Geom H mask O)
    (R : EvenRows Geom H mask O L) : RowSupport Geom H mask O L R := by
  sorry

/-- P14.1j: posterior cancellation, retained-mass cost and the independently
proved forced-present selection incidence estimate. -/
theorem posterior_row_mean (κ : CConsts) (hκ : κ.Admissible)
    {T : Stage} {k : ℕ} {𝒯 : Tiling κ T k} {i : Fin 𝒯.m} {mesh : Mesh 𝒯}
    (Geom : ProjectionGeometry κ 𝒯 i) (H : PrimitiveHistory κ 𝒯 i mesh)
    (mask : Masks H) (O : OddKernels Geom H mask) (L : LikelihoodData Geom H mask O)
    (R : EvenRows Geom H mask O L) (hinc : SelectionIncidence Geom H mask) :
    RowMeanBound Geom H mask O L R := by
  sorry

/-- P14.1k: tests are exactly validity plus the raw predictive failure bound. -/
theorem posterior_good_tests (κ : CConsts) (hκ : κ.Admissible)
    (hconst : HeightConstantContract κ)
    {T : Stage} {k : ℕ} {𝒯 : Tiling κ T k} (h𝒯 : Tiling.Valid 𝒯)
    {i : Fin 𝒯.m} {mesh : Mesh 𝒯} (scales : PatchScales 𝒯 i)
    (Geom : ProjectionGeometry κ 𝒯 i) (H : PrimitiveHistory κ 𝒯 i mesh)
    (mask : Masks H) (O : OddKernels Geom H mask) (L : LikelihoodData Geom H mask O)
    (R : EvenRows Geom H mask O L) (hh : HeightFacts hconst Geom H mask) :
    Nonempty (GoodTests Geom H mask O L R) := by
  sorry

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
  sorry

structure SolverWitness {κ : CConsts} {T : Stage} {k : ℕ}
    {𝒯 : Tiling κ T k} {i : Fin 𝒯.m} {mesh : Mesh 𝒯} where
  solver : SliceSolver κ 𝒯 i mesh
  low_output_invariant : LowOutputInvariant solver
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
  refine ⟨⟨S, hlow, ?_⟩⟩
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
