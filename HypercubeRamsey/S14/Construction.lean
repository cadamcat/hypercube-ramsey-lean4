import HypercubeRamsey.PartC.ProfiledTiling
import HypercubeRamsey.S03.Height.Selection
import HypercubeRamsey.S03.Mixtures
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
  sorry

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
  have activeCornerSingleton {p : mesh.Param} (v : mesh.V)
      (hv : 0 < mesh.wt v p) : (mesh.corner v i).card = 1 := by
    let C := mesh.corner v i
    have hsum :
        ∑ x, (if x ∈ C then ((1 / C.card : ℕ) : ℝ) else 0) = 1 := by
      calc
        _ = ∑ x, (H.prior v).w x := by
          apply Finset.sum_congr rfl
          intro x hx
          rw [H.prior_uniform v p hv x]
          simp [C]
        _ = 1 := (H.prior v).sum_eq_one
    by_contra hne
    rcases Nat.eq_zero_or_pos C.card with hzero | hpos
    · simp [C, hzero] at hsum
    · have hlarge : 1 < C.card :=
        Nat.one_lt_iff_ne_zero_and_ne_one.mpr ⟨hpos.ne', hne⟩
      have hdiv : 1 / C.card = 0 := Nat.div_eq_of_lt hlarge
      simp [hdiv] at hsum
  have activePrior {p : mesh.Param} (v : mesh.V) (hv : 0 < mesh.wt v p) (x : Fin (T.S.N k)) :
      (H.prior v).w x = if x ∈ mesh.corner v i then (1 : ℝ) else 0 := by
    rw [H.prior_uniform v p hv x]
    simp [activeCornerSingleton v hv]
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
          have hprior := activePrior v' hactive
          have hmean :
              ∑ x, (H.prior v').w x * hit (T.S.E k) 𝒯.c x y * hit (T.S.E k) 𝒯.c x y' =
                (∑ x ∈ mesh.corner v' i,
                  hit (T.S.E k) 𝒯.c x y * hit (T.S.E k) 𝒯.c x y') /
                    (mesh.corner v' i).card := by
            calc
              _ = ∑ x, (if x ∈ mesh.corner v' i then (1 : ℝ) else 0) *
                    (hit (T.S.E k) 𝒯.c x y * hit (T.S.E k) 𝒯.c x y') := by
                      apply Finset.sum_congr rfl
                      intro x hx
                      rw [hprior x]
                      ring
              _ = ∑ x ∈ mesh.corner v' i,
                    hit (T.S.E k) 𝒯.c x y * hit (T.S.E k) 𝒯.c x y' := by
                      simp [Finset.sum_ite_mem, Finset.univ_inter]
              _ = _ := by rw [activeCornerSingleton v' hactive]; norm_num
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
  sorry

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

/-- P14.1e: L3.8 for the actual independent Bernoulli and uniform tie draws. -/
theorem height_selection_at_patch (κ : CConsts) (hκ : κ.Admissible)
    (hconst : HeightConstantContract κ)
    {T : Stage} {k : ℕ} {𝒯 : Tiling κ T k} (h𝒯 : Tiling.Valid 𝒯)
    (hcluster : 𝒯.mode.isCluster) {i : Fin 𝒯.m} {mesh : Mesh 𝒯}
    (scales : PatchScales 𝒯 i) (Geom : ProjectionGeometry κ 𝒯 i)
    (H : PrimitiveHistory κ 𝒯 i mesh) (mask : Masks H) (hlookup : MaskLookup H mask)
    (he : EligibilityFacts hconst Geom H mask) : HeightFacts hconst Geom H mask := by
  sorry

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

/-- P14.1j height subnode: level-zero active ties and the position-averaged
forced-present positive-height bound. No global success is conditioned on. -/
theorem forced_present_incidence (κ : CConsts) (hκ : κ.Admissible)
    (hconst : HeightConstantContract κ)
    {T : Stage} {k : ℕ} {𝒯 : Tiling κ T k} (h𝒯 : Tiling.Valid 𝒯)
    (hcluster : 𝒯.mode.isCluster) {i : Fin 𝒯.m} {mesh : Mesh 𝒯}
    (scales : PatchScales 𝒯 i) (Geom : ProjectionGeometry κ 𝒯 i)
    (H : PrimitiveHistory κ 𝒯 i mesh) (mask : Masks H) (hlookup : MaskLookup H mask)
    (hh : HeightFacts hconst Geom H mask) : SelectionIncidence Geom H mask := by
  sorry

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

theorem odd_bin_laws (κ : CConsts) (hκ : κ.Admissible)
    (hconst : HeightConstantContract κ)
    {T : Stage} {k : ℕ} {𝒯 : Tiling κ T k} (h𝒯 : Tiling.Valid 𝒯)
    {i : Fin 𝒯.m} {mesh : Mesh 𝒯} (scales : PatchScales 𝒯 i)
    (Geom : ProjectionGeometry κ 𝒯 i) (H : PrimitiveHistory κ 𝒯 i mesh) (mask : Masks H) :
    Nonempty (OddKernels Geom H mask) := by
  sorry

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
