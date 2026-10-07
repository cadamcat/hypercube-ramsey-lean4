import HypercubeRamsey.PartC.ProfiledTiling
import HypercubeRamsey.S03.Height.Selection
import HypercubeRamsey.S03.Mixtures

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
  global_c14 : κ.c14 ≤ globalExponent
  global_h0 : globalThreshold ≤ κ.h0
  positiveExponent : ℝ
  positiveThreshold : ℕ
  positive_exponent_pos : 0 < positiveExponent
  positive_bound : Section14PositiveHeightBound J₀ b₀ b σ ζ c_d C_d
    positiveExponent 6 regime positiveThreshold
  positive_h0 : positiveThreshold ≤ κ.h0

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

/-- Primitive categorical records for the Section 14 experiment. Their laws
are products of the per-record laws, as in lines 26–29 of the paper. Derived
bin laws, even rows and tests are supplied by later nodes. -/
structure PrimitiveHistory (κ : CConsts) {T : Stage} {k : ℕ}
    (𝒯 : Tiling κ T k) (i : Fin 𝒯.m) (mesh : Mesh 𝒯) where
  Rec : Type
  [recFin : Fintype Rec]
  loc : Rec → IWord 𝒯 i
  Val : Rec → Type
  [valFin : ∀ r, Fintype (Val r)]
  lawRec : mesh.Param → ∀ r, Val r → ℝ
  lawRec_nonneg : ∀ p r x, 0 ≤ lawRec p r x
  lawRec_sum : ∀ p r, ∑ x, lawRec p r x = 1
  lawRec_cont : ∀ r x, Continuous fun p => lawRec p r x
  /-- The level-indexed candidate records exposed to the selection rule. -/
  candidates : EvenRole 𝒯 i → Fin ((𝒯.P i).h + 1) → Finset Rec
  /-- The prospective-position bit in a primitive history. -/
  present : (∀ r, Val r) → Rec → Bool
  /-- The activation bit in a primitive history. -/
  active : (∀ r, Val r) → Rec → Bool
  /-- Group-local price-mask vertex draw. -/
  maskVertex : Group 𝒯 i → (∀ r, Val r) → mesh.V
  /-- Its marginal is the parameter point's barycentric mesh law. -/
  mask_law : ∀ p g v,
    (recordLaw (lawRec p) (lawRec_nonneg p) (lawRec_sum p)).pr
      (fun W => maskVertex g W = v) = mesh.wt v p
  /-- Cleaned corner used to generate a center's tuple. The vertex is part of
  that center's categorical record value. -/
  cornerOf : Rec → (∀ r, Val r) → mesh.V
  /-- Eligibility after the deterministic failed-list marking rule. -/
  eligible : (∀ r, Val r) → EvenRole 𝒯 i → Fin ((𝒯.P i).h + 1) → Finset Rec
  /-- The selected candidate at each even site, defined by the long height
  rule and the independently sampled choice tie. -/
  selected : (∀ r, Val r) → EvenRole 𝒯 i →
    Option (Fin ((𝒯.P i).h + 1) × Rec)

instance instHistoryRecFintype {κ : CConsts} {T : Stage} {k : ℕ}
    {𝒯 : Tiling κ T k} {i : Fin 𝒯.m} {mesh : Mesh 𝒯}
    (H : PrimitiveHistory κ 𝒯 i mesh) : Fintype H.Rec := H.recFin

instance instHistoryValFintype {κ : CConsts} {T : Stage} {k : ℕ}
    {𝒯 : Tiling κ T k} {i : Fin 𝒯.m} {mesh : Mesh 𝒯}
    (H : PrimitiveHistory κ 𝒯 i mesh) : ∀ r, Fintype (H.Val r) := H.valFin

namespace PrimitiveHistory

variable {κ : CConsts} {T : Stage} {k : ℕ} {𝒯 : Tiling κ T k}
  {i : Fin 𝒯.m} {mesh : Mesh 𝒯}

/-- Product law of the independent primitive records at a parameter point. -/
noncomputable def recLaw (H : PrimitiveHistory κ 𝒯 i mesh) (p : mesh.Param) :
    FinLaw (∀ r, H.Val r) :=
  recordLaw (H.lawRec p) (H.lawRec_nonneg p) (H.lawRec_sum p)

end PrimitiveHistory

/-- The group of an odd internal word is obtained from its syndrome-zero
projection. -/
noncomputable def groupNeighborhood {κ : CConsts} {T : Stage} {k : ℕ}
    {𝒯 : Tiling κ T k} {i : Fin 𝒯.m} (g : Group 𝒯 i) : Finset (EvenRole 𝒯 i) := by
  classical
  exact Finset.univ.filter fun v =>
    ∃ l, flipPos v.1 l ∈ groupFiber g

structure ProjectionGeometry (κ : CConsts) {T : Stage} {k : ℕ}
    (𝒯 : Tiling κ T k) (i : Fin 𝒯.m) where
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
  within_uniform : ∀ D, D ∈ retained → ∀ y, within D y =
    if y ∈ cheap D then 1 / ((cheap D).card : ℝ) else 0
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
  cleaned_codegree : ∀ (v' : mesh.V) (D : Bin 𝒯 i)
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
  first_law_supported : ∀ c, (firstLaw c).SupportedIn (𝒯.P i).X
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

/-- Convert the shared host-side law to the Part C finite-law wrapper. -/
noncomputable def lawToFinLaw {N : ℕ} (μ : Law N) : FinLaw (Fin N) where
  w := μ.w
  nonneg := μ.nonneg
  sum_one := μ.sum_eq_one

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

/-- P14.1c: the generic one-list test. The nondegenerate list and budget
hypotheses are explicit; the conclusion is uniform over all such models. -/
theorem generic_list_test (κ : CConsts) (hκ : κ.Admissible)
    {T : Stage} {k : ℕ} (𝒯 : Tiling κ T k) (i : Fin 𝒯.m)
    (L : ListTestModel κ 𝒯 i)
    (hcount : Fintype.card L.Id ≤ 𝒯.tScale i)
    (hsmall : κ.a ≤ 1 / 10) :
    L.tupleLaw.pr (L.Failure) ≤
      2 * (𝒯.tScale i + 1 : ℝ) *
        Real.exp (-κ.c5 * κ.a ^ 2 * (𝒯.kScale i : ℝ)) := by
  sorry

/-- The candidate lists exposed by a primitive history. -/
structure ListFamily {κ : CConsts} {T : Stage} {k : ℕ}
    {𝒯 : Tiling κ T k} {i : Fin 𝒯.m} {mesh : Mesh 𝒯}
    (H : PrimitiveHistory κ 𝒯 i mesh) (hclean : MeshCleaned mesh)
    (mask : ∀ (g : Group 𝒯 i) (W : ∀ r, H.Val r),
      MaskFacts i mesh (H.maskVertex g W)) where
  model : Group 𝒯 i → (∀ r, H.Val r) → ListTestModel κ 𝒯 i
  recordOf : ∀ (g : Group 𝒯 i) (W : ∀ r, H.Val r), (model g W).Id → H.Rec
  record_candidate : ∀ (g : Group 𝒯 i) (W : ∀ r, H.Val r) (c : (model g W).Id),
    ∃ v j, recordOf g W c ∈ H.candidates v j
  record_present : ∀ (g : Group 𝒯 i) (W : ∀ r, H.Val r) (c : (model g W).Id),
    H.present W (recordOf g W c) = true
  corner_active : ∀ (p : mesh.Param) (g : Group 𝒯 i) (W : ∀ r, H.Val r)
      (c : (model g W).Id),
    (H.recLaw p).w W > 0 →
      0 < mesh.wt (H.cornerOf (recordOf g W c) W) p
  first_law_uniform : ∀ (p : mesh.Param) (g : Group 𝒯 i) (W : ∀ r, H.Val r)
      (c : (model g W).Id) (hW : (H.recLaw p).w W > 0),
    (model g W).firstLaw c = Law.unifCore
      (mesh.corner (H.cornerOf (recordOf g W c) W) i)
      (hclean (H.cornerOf (recordOf g W c) W) p i
        (corner_active p g W c hW)).nonempty
  count : ∀ (g : Group 𝒯 i) (W : ∀ r, H.Val r),
    Fintype.card (model g W).Id ≤ 𝒯.tScale i
  small : κ.a ≤ 1 / 10
  prior_matches_mask : ∀ (g : Group 𝒯 i) (W : ∀ r, H.Val r) (D : Bin 𝒯 i),
    (model g W).binPrior.w D = (mask g W).prior D
  bin_law_matches_mask : ∀ (g : Group 𝒯 i) (W : ∀ r, H.Val r)
      (D : Bin 𝒯 i) (y : Fin (T.S.N k)),
    ((model g W).binDist D).w y = (mask g W).within D y

/-- Count gate supplied by the binomial position estimate. -/
def PositionCountGate {κ : CConsts} {T : Stage} {k : ℕ}
    {𝒯 : Tiling κ T k} {i : Fin 𝒯.m} {mesh : Mesh 𝒯}
    (H : PrimitiveHistory κ 𝒯 i mesh) (W : ∀ r, H.Val r) : Prop :=
  ∀ v j,
    (𝒯.P i).h ^ 10 / 2 ≤
      ((H.candidates v j).filter (fun r => H.present W r = true)).card ∧
    ((H.candidates v j).filter (fun r => H.present W r = true)).card ≤
      2 * (𝒯.P i).h ^ 10

/-- Position-count concentration from X-Chernoff. -/
def PositionCountConcentration {κ : CConsts} {T : Stage} {k : ℕ}
    {𝒯 : Tiling κ T k} {i : Fin 𝒯.m} {mesh : Mesh 𝒯}
    (H : PrimitiveHistory κ 𝒯 i mesh) : Prop :=
  ∀ p, (H.recLaw p).pr (fun W => PositionCountGate H W) ≥
    1 - Real.exp (-Real.rpow ((𝒯.P i).h : ℝ) (1 + κ.c14))

/-- The good-position and eligibility event used by the height device. -/
structure EligibilityFacts {κ : CConsts} {T : Stage} {k : ℕ}
    {𝒯 : Tiling κ T k} {i : Fin 𝒯.m} {mesh : Mesh 𝒯}
    (H : PrimitiveHistory κ 𝒯 i mesh) : Prop where
  eligible_subset : ∀ W v j r, r ∈ H.eligible W v j →
    r ∈ H.candidates v j ∧ H.present W r = true ∧ H.active W r = true
  /-- Position counts and maximal failed-list marking leave at least half the
  nominal number of eligible records at every queried site and level. -/
  eligible_gate : ∀ p,
    (H.recLaw p).pr (fun W => ∀ v j,
      (H.eligible W v j).card ≥ (𝒯.P i).h ^ 10 / 2) ≥
        1 - Real.exp (-Real.rpow ((𝒯.P i).h : ℝ) (1 + κ.c14))
  low_support : 𝒯.mode = .lowCluster → ∀ p,
    (((Finset.univ.filter fun W => (H.recLaw p).w W > 0).card : ℕ) : ℝ) ≤
      Real.exp ((T.S.n k : ℝ) ^ (1.01 : ℝ))

/-- P14.1d seed: the primitive center, position, activation, mask and tie
records, with their continuously parameterized product law. -/
theorem primitive_history (κ : CConsts) (hκ : κ.Admissible)
    {T : Stage} {k : ℕ} (𝒯 : Tiling κ T k) (h𝒯 : Tiling.Valid 𝒯)
    (hcluster : 𝒯.mode.isCluster) (i : Fin 𝒯.m) (mesh : Mesh 𝒯)
    (hclean : MeshCleaned mesh) :
    Nonempty (PrimitiveHistory κ 𝒯 i mesh) := by
  sorry

/-- P14.1d list enumeration subnode: all position-conditioned candidate
families fit the size and width budgets used by P14.1c. -/
theorem candidate_list_models (κ : CConsts) (hκ : κ.Admissible)
    {T : Stage} {k : ℕ} {𝒯 : Tiling κ T k} (h𝒯 : Tiling.Valid 𝒯)
    (hcluster : 𝒯.mode.isCluster) {i : Fin 𝒯.m} {mesh : Mesh 𝒯}
    (hclean : MeshCleaned mesh) (H : PrimitiveHistory κ 𝒯 i mesh)
    (hmask : ∀ (g : Group 𝒯 i) (W : ∀ r, H.Val r),
      MaskFacts i mesh (H.maskVertex g W)) :
    Nonempty (ListFamily H hclean hmask) := by
  sorry

/-- P14.1d position-count subnode. -/
theorem position_count_concentration (κ : CConsts) (hκ : κ.Admissible)
    (hconst : HeightConstantContract κ)
    {T : Stage} {k : ℕ} {𝒯 : Tiling κ T k} (h𝒯 : Tiling.Valid 𝒯)
    (hcluster : 𝒯.mode.isCluster) {i : Fin 𝒯.m} {mesh : Mesh 𝒯}
    (H : PrimitiveHistory κ 𝒯 i mesh) : PositionCountConcentration H := by
  sorry

/-- Combining list-test failure probabilities with the position gate gives
the deterministic maximal-family eligibility estimate. -/
theorem eligibility_from_tests (κ : CConsts) (hκ : κ.Admissible)
    (hconst : HeightConstantContract κ)
    {T : Stage} {k : ℕ} {𝒯 : Tiling κ T k} (h𝒯 : Tiling.Valid 𝒯)
    (hcluster : 𝒯.mode.isCluster) {i : Fin 𝒯.m} {mesh : Mesh 𝒯}
    (Geom : ProjectionGeometry κ 𝒯 i)
    (hdistance : ∀ (g : Group 𝒯 i) (v v' : EvenRole 𝒯 i),
      v ∈ groupNeighborhood g → v' ∈ groupNeighborhood g →
      hammingDist v.1 v'.1 ≤ 6)
    (hoverlap : ∀ (v : EvenRole 𝒯 i),
      ((Finset.univ.filter fun g : Group 𝒯 i => v ∈ groupNeighborhood g).card : ℝ) ≤
        (𝒯.P i).h ^ 3)
    (H : PrimitiveHistory κ 𝒯 i mesh) (hclean : MeshCleaned mesh)
    (hmask : ∀ (g : Group 𝒯 i) (W : ∀ r, H.Val r),
      MaskFacts i mesh (H.maskVertex g W))
    (L : ListFamily H hclean hmask)
    (hcounts : PositionCountConcentration H)
    (htests : ∀ g W, (L.model g W).tupleLaw.pr (L.model g W).Failure ≤
      2 * (𝒯.tScale i + 1 : ℝ) *
        Real.exp (-κ.c5 * κ.a ^ 2 * (𝒯.kScale i : ℝ))) :
    EligibilityFacts H := by
  sorry

/-- P14.1d count subnode: position concentration and deterministic
maximal-family marking imply the eligibility gate. -/
theorem searches_eligibility (κ : CConsts) (hκ : κ.Admissible)
    (hconst : HeightConstantContract κ)
    {T : Stage} {k : ℕ} {𝒯 : Tiling κ T k} (h𝒯 : Tiling.Valid 𝒯)
    (hcluster : 𝒯.mode.isCluster) {i : Fin 𝒯.m} {mesh : Mesh 𝒯}
    (Geom : ProjectionGeometry κ 𝒯 i)
    (H : PrimitiveHistory κ 𝒯 i mesh) (hclean : MeshCleaned mesh)
    (hmask : ∀ (g : Group 𝒯 i) (W : ∀ r, H.Val r),
      MaskFacts i mesh (H.maskVertex g W))
    (L : ListFamily H hclean hmask)
    (hcounts : PositionCountConcentration H) : EligibilityFacts H := by
  apply eligibility_from_tests κ hκ hconst h𝒯 hcluster Geom
    Geom.neighborhood_distance Geom.neighborhood_overlap H hclean hmask L hcounts
  intro g W
  exact generic_list_test κ hκ 𝒯 i (L.model g W) (L.count g W) L.small

/-- P14.1e: the ambient-`h` height selection result, including the numerical
contract tying the constants in `CConsts` to the L3.8 output. -/
structure HeightFacts {κ : CConsts} {T : Stage} {k : ℕ}
    {𝒯 : Tiling κ T k} {i : Fin 𝒯.m} {mesh : Mesh 𝒯}
    (H : PrimitiveHistory κ 𝒯 i mesh) : Prop where
  height_good : ∀ p,
    (H.recLaw p).pr (fun W => ∀ v, ∃ jr, H.selected W v = some jr) ≥
      1 - Real.exp (-Real.rpow ((𝒯.P i).h : ℝ) (1 + κ.c14))
  chosen_eligible : ∀ W v j r, H.selected W v = some (j, r) → r ∈ H.eligible W v j
  selected_local : ∀ v W W',
    (∀ r, (hammingDist (H.loc r) v.1 : ℝ) ≤ 10 * κ.ρ * (𝒯.P i).h → W r = W' r) →
      H.selected W v = H.selected W' v

/-- P14.1e: apply L3.8 with ambient parameter `h`, using the constants
contract supplied by the producing node. -/
theorem height_selection_at_patch (κ : CConsts) (hκ : κ.Admissible)
    (hconst : HeightConstantContract κ)
    {T : Stage} {k : ℕ} {𝒯 : Tiling κ T k} (h𝒯 : Tiling.Valid 𝒯)
    (hcluster : 𝒯.mode.isCluster) {i : Fin 𝒯.m} {mesh : Mesh 𝒯}
    (H : PrimitiveHistory κ 𝒯 i mesh) (he : EligibilityFacts H) : HeightFacts H := by
  sorry

/-- Odd bin kernels and their probability/support bounds (S1). -/
structure OddKernels {κ : CConsts} {T : Stage} {k : ℕ}
    {𝒯 : Tiling κ T k} {i : Fin 𝒯.m} {mesh : Mesh 𝒯}
    (H : PrimitiveHistory κ 𝒯 i mesh) where
  q : Group 𝒯 i → (∀ r, H.Val r) → Bin 𝒯 i → ℝ
  U : Group 𝒯 i → (∀ r, H.Val r) → Bin 𝒯 i → Fin (T.S.N k) → ℝ
  /-- Tuple-independent reference mixture used by the posterior comparison. -/
  reference : EvenRole 𝒯 i → InternalLabels 𝒯 i → ℝ
  q_nonneg : ∀ g W D, 0 ≤ q g W D
  q_sum : ∀ g W, ∑ D : Bin 𝒯 i, q g W D = 1
  U_nonneg : ∀ g W D y, 0 ≤ U g W D y
  U_sum : ∀ g W D, ∑ y, U g W D y = 1
  U_support : ∀ g W D y, U g W D y ≠ 0 → y ∈ D.1
  q_cap : ∀ g W D,
    q g W D ≤ 4 * Real.exp (2 * (𝒯.kScale i : ℝ) * 𝒯.tScale i) *
      (𝒯.P i).d / (𝒯.P i).M
  marginal_cap : ∀ g W y,
    ∑ D : Bin 𝒯 i, q g W D * U g W D y ≤
      8 * Real.exp (2 * (𝒯.kScale i : ℝ) * 𝒯.tScale i) / (𝒯.P i).M
  U_support_size : ∀ g W D, q g W D > 0 →
    ((Finset.univ.filter fun y => U g W D y ≠ 0).card : ℝ) ≥
      (1 / 2 : ℝ) * (𝒯.P i).d *
        Real.exp (-1.5 * (𝒯.kScale i : ℝ) * 𝒯.tScale i)
  /-- Positive output mass can only use labels cheap at a mesh vertex that is
  active at the parameter point. -/
  cheap_mean_support : ∀ p g y,
    (H.recLaw p).E (fun W => ∑ D : Bin 𝒯 i, q g W D * U g W D y) > 0 →
      ∃ v : mesh.V, 0 < mesh.wt v p ∧
        mesh.paramPrice (mesh.base v) i y ≤ 10 / (𝒯.P i).M

/-- P14.1f: the restricted squared-mass tilt and masked-prior fallback
produce the odd bin and in-bin laws satisfying eq:source-13. -/
theorem odd_bin_laws (κ : CConsts) (hκ : κ.Admissible)
    {T : Stage} {k : ℕ} {𝒯 : Tiling κ T k} (h𝒯 : Tiling.Valid 𝒯)
    {i : Fin 𝒯.m} {mesh : Mesh 𝒯} (H : PrimitiveHistory κ 𝒯 i mesh)
    (hmask : ∀ g W, MaskFacts i mesh (H.maskVertex g W))
    (he : EligibilityFacts H)
    (hh : HeightFacts H) : Nonempty (OddKernels H) := by
  sorry

/-- P14.1g likelihood-ratio estimate for changing one selected tuple while
holding the fixed reference mixture independent of that tuple. -/
def LikelihoodDomination {κ : CConsts} {T : Stage} {k : ℕ}
    {𝒯 : Tiling κ T k} {i : Fin 𝒯.m} {mesh : Mesh 𝒯}
    (H : PrimitiveHistory κ 𝒯 i mesh) (O : OddKernels H)
    (likelihood : EvenRole 𝒯 i → (∀ r, H.Val r) → InternalLabels 𝒯 i → ℝ) : Prop :=
  ∀ v : EvenRole 𝒯 i, ∀ W, ∀ ys : InternalLabels 𝒯 i,
    likelihood v W ys ≤
      Real.exp ((Real.log 2 - 0.06 * κ.a) * (𝒯.kScale i : ℝ) * (𝒯.P i).h) *
        O.reference v ys

/-- The likelihood field and its P14.1g comparison. -/
structure LikelihoodData {κ : CConsts} {T : Stage} {k : ℕ}
    {𝒯 : Tiling κ T k} {i : Fin 𝒯.m} {mesh : Mesh 𝒯}
    (H : PrimitiveHistory κ 𝒯 i mesh) (O : OddKernels H) where
  value : EvenRole 𝒯 i → (∀ r, H.Val r) → InternalLabels 𝒯 i → ℝ
  domination : LikelihoodDomination H O value

/-- P14.1g: deletion-ratio tests and incidence multiplicities give
likelihood-ratio domination. -/
theorem likelihood_ratio_domination (κ : CConsts) (hκ : κ.Admissible)
    {T : Stage} {k : ℕ} {𝒯 : Tiling κ T k} (h𝒯 : Tiling.Valid 𝒯)
    {i : Fin 𝒯.m} {mesh : Mesh 𝒯} (G : ProjectionGeometry κ 𝒯 i)
    (hfiber : ∀ g : Group 𝒯 i, (groupFiber g).card = (𝒯.P i).h)
    (hmultiplicity : ∀ v g,
      G.multiplicity v g =
        (Finset.univ.filter fun l : Fin (𝒯.P i).h =>
          flipPos v.1 l ∈ groupFiber g).card)
    (hmultiplicity_lower : ∀ v g, 0 < G.multiplicity v g → 2 ≤ G.multiplicity v g)
    (hmultiplicity_sum : ∀ v, ∑ g : Group 𝒯 i, G.multiplicity v g = (𝒯.P i).h)
    (H : PrimitiveHistory κ 𝒯 i mesh) (O : OddKernels H) :
    Nonempty (LikelihoodData H O) := by
  sorry

/-- Posterior even-row data. -/
structure EvenRows {κ : CConsts} {T : Stage} {k : ℕ}
    {𝒯 : Tiling κ T k} {i : Fin 𝒯.m} {mesh : Mesh 𝒯}
    (H : PrimitiveHistory κ 𝒯 i mesh) (O : OddKernels H) where
  σ : EvenRole 𝒯 i → (∀ r, H.Val r) → InternalLabels 𝒯 i → Fin (T.S.N k) → ℝ
  nonneg : ∀ v W ys x, 0 ≤ σ v W ys x
  probability : ∀ v W ys, σ v W ys ≠ 0 → ∑ x, σ v W ys x = 1
  cap : ∀ v W ys x,
    (T.S.N k : ℝ) * σ v W ys x ≤
      2 ^ (𝒯.P i).h * Real.exp (-500 * 𝒯.gain i)

/-- P14.1h: truncate and renormalize the posterior coordinate marginal to
obtain the capped even row. -/
theorem posterior_even_rows (κ : CConsts) (hκ : κ.Admissible)
    {T : Stage} {k : ℕ} {𝒯 : Tiling κ T k} (h𝒯 : Tiling.Valid 𝒯)
    {i : Fin 𝒯.m} {mesh : Mesh 𝒯} (H : PrimitiveHistory κ 𝒯 i mesh)
    (O : OddKernels H) (L : LikelihoodData H O) :
    Nonempty (EvenRows H O) := by
  sorry

/-- P14.1i support conclusion for the posterior row. -/
def RowSupport {κ : CConsts} {T : Stage} {k : ℕ}
    {𝒯 : Tiling κ T k} {i : Fin 𝒯.m} {mesh : Mesh 𝒯}
    (H : PrimitiveHistory κ 𝒯 i mesh) (O : OddKernels H) (R : EvenRows H O) : Prop :=
  ∀ v W ys, (R.σ v W ys) ≠ 0 →
    ∃ v' : mesh.V,
      (∀ p, 0 < (recordLaw (H.lawRec p) (H.lawRec_nonneg p) (H.lawRec_sum p)).w W →
        0 < mesh.wt v' p) ∧
      ∀ x, R.σ v W ys x ≠ 0 → x ∈ mesh.corner v' i ∧
        ∀ l, Hits (T.S.E k) 𝒯.c x (ys l)

/-- P14.1i: every nonzero posterior row is supported in one active cleaned
corner and on common neighbors of all internal labels. -/
theorem posterior_row_support (κ : CConsts) (hκ : κ.Admissible)
    {T : Stage} {k : ℕ} {𝒯 : Tiling κ T k} (h𝒯 : Tiling.Valid 𝒯)
    {i : Fin 𝒯.m} {mesh : Mesh 𝒯} (H : PrimitiveHistory κ 𝒯 i mesh)
    (O : OddKernels H) (R : EvenRows H O)
    (hh : HeightFacts H)
    (hmask : ∀ g W, MaskFacts i mesh (H.maskVertex g W)) : RowSupport H O R := by
  sorry

/-- P14.1j mean-bound conclusion (eq:source-14). -/
def RowMeanBound {κ : CConsts} {T : Stage} {k : ℕ}
    {𝒯 : Tiling κ T k} {i : Fin 𝒯.m} {mesh : Mesh 𝒯}
    (G : ProjectionGeometry κ 𝒯 i) (H : PrimitiveHistory κ 𝒯 i mesh)
    (O : OddKernels H) (R : EvenRows H O) : Prop :=
  ∀ p (v : EvenRole 𝒯 i) x,
    (recordLaw (H.lawRec p) (H.lawRec_nonneg p) (H.lawRec_sum p)).E (fun W =>
      ((internalRefLaw (fun g => O.q g W) (fun g => O.q_nonneg g W) (fun g => O.q_sum g W)
        (fun g => O.U g W) (fun g => O.U_nonneg g W) (fun g => O.U_sum g W)
        G.groupOf).E (fun ω => R.σ v W (nbrLabels v.1 ω.2) x))) ≤
      rowMeanConstant κ / (𝒯.P i).M

/-- P14.1j: posterior cancellation and the forced-present height estimate
give the expected-row bound. -/
theorem posterior_row_mean (κ : CConsts) (hκ : κ.Admissible)
    {T : Stage} {k : ℕ} {𝒯 : Tiling κ T k} (h𝒯 : Tiling.Valid 𝒯)
    (hconst : HeightConstantContract κ)
    {i : Fin 𝒯.m} {mesh : Mesh 𝒯} (H : PrimitiveHistory κ 𝒯 i mesh)
    (G : ProjectionGeometry κ 𝒯 i) (O : OddKernels H) (R : EvenRows H O)
    (L : LikelihoodData H O) : RowMeanBound G H O R := by
  sorry

/-- The deterministic good-test predicate and its internal zero-row bound. -/
structure GoodTests {κ : CConsts} {T : Stage} {k : ℕ}
    {𝒯 : Tiling κ T k} {i : Fin 𝒯.m} {mesh : Mesh 𝒯}
    (G : ProjectionGeometry κ 𝒯 i) (H : PrimitiveHistory κ 𝒯 i mesh)
    (O : OddKernels H) (R : EvenRows H O) where
  Hgood : EvenRole 𝒯 i → (∀ r, H.Val r) → Prop
  zero_bound : ∀ v W, Hgood v W →
    (internalRefLaw (fun g => O.q g W) (fun g => O.q_nonneg g W) (fun g => O.q_sum g W)
      (fun g => O.U g W) (fun g => O.U_nonneg g W) (fun g => O.U_sum g W)
      G.groupOf).pr
      (fun ω => R.σ v W (nbrLabels v.1 ω.2) = 0) ≤ sliceEps κ (𝒯.P i).h
  bad_bound : ∀ p,
    (recordLaw (H.lawRec p) (H.lawRec_nonneg p) (H.lawRec_sum p)).pr
      (fun W => ∃ v : EvenRole 𝒯 i, ¬ Hgood v W) ≤
        Real.exp (-Real.rpow ((𝒯.P i).h : ℝ) (1 + κ.c14))

/-- P14.1k: the gated-posterior failure estimate and a union bound give the
local tests (S5). -/
theorem posterior_good_tests (κ : CConsts) (hκ : κ.Admissible)
    (hconst : HeightConstantContract κ)
    {T : Stage} {k : ℕ} {𝒯 : Tiling κ T k} (h𝒯 : Tiling.Valid 𝒯)
    {i : Fin 𝒯.m} {mesh : Mesh 𝒯} (H : PrimitiveHistory κ 𝒯 i mesh)
    (G : ProjectionGeometry κ 𝒯 i) (O : OddKernels H) (R : EvenRows H O)
    (hh : HeightFacts H) (L : LikelihoodData H O) :
    Nonempty (GoodTests G H O R) := by
  sorry

/-- P14.1l: locality, raw-law symmetry and low-mode output symmetry. -/
structure LocalSymmetry {κ : CConsts} {T : Stage} {k : ℕ}
    {𝒯 : Tiling κ T k} {i : Fin 𝒯.m} {mesh : Mesh 𝒯}
    (Geom : ProjectionGeometry κ 𝒯 i) (H : PrimitiveHistory κ 𝒯 i mesh)
    (O : OddKernels H) (R : EvenRows H O) (G : GoodTests Geom H O R) : Prop where
  q_local : ∀ g W W',
    (∀ r, (hammingDist (H.loc r) (groupCenter g).1 : ℝ) ≤ 10 * κ.ρ * (𝒯.P i).h →
      W r = W' r) → O.q g W = O.q g W'
  U_local : ∀ g W W' D,
    (∀ r, (hammingDist (H.loc r) (groupCenter g).1 : ℝ) ≤ 10 * κ.ρ * (𝒯.P i).h →
      W r = W' r) → O.U g W D = O.U g W' D
  σ_local : ∀ v W W' ys,
    (∀ r, (hammingDist (H.loc r) v.1 : ℝ) ≤ 10 * κ.ρ * (𝒯.P i).h → W r = W' r) →
      R.σ v W ys = R.σ v W' ys
  Hgood_local : ∀ v W W',
    (∀ r, (hammingDist (H.loc r) v.1 : ℝ) ≤ 10 * κ.ρ * (𝒯.P i).h → W r = W' r) →
      (G.Hgood v W ↔ G.Hgood v W')
  averaged_marginal_invariant : ∀ p g g' y,
    (recordLaw (H.lawRec p) (H.lawRec_nonneg p) (H.lawRec_sum p)).E
      (fun W => ∑ D : Bin 𝒯 i, O.q g W D * O.U g W D y) =
    (recordLaw (H.lawRec p) (H.lawRec_nonneg p) (H.lawRec_sum p)).E
      (fun W => ∑ D : Bin 𝒯 i, O.q g' W D * O.U g' W D y)

/-- P14.1l: the deterministic tie conventions give the local and raw-law
symmetry claims for the constructed rules. -/
theorem locality_and_symmetry (κ : CConsts) (hκ : κ.Admissible)
    {T : Stage} {k : ℕ} {𝒯 : Tiling κ T k} (h𝒯 : Tiling.Valid 𝒯)
    {i : Fin 𝒯.m} {mesh : Mesh 𝒯} (Geom : ProjectionGeometry κ 𝒯 i)
    (H : PrimitiveHistory κ 𝒯 i mesh) (O : OddKernels H) (R : EvenRows H O)
    (G : GoodTests Geom H O R) (hh : HeightFacts H) :
    LocalSymmetry Geom H O R G := by
  sorry

/-- Supplement to D14.S: the low-mode output agrees for every group. -/
def LowOutputInvariant {κ : CConsts} {T : Stage} {k : ℕ}
    {𝒯 : Tiling κ T k} {i : Fin 𝒯.m} {mesh : Mesh 𝒯}
    (S : SliceSolver κ 𝒯 i mesh) : Prop :=
  ∀ p g g' y, 𝒯.mode = .lowCluster → S.lowOut p g y = S.lowOut p g' y

/-- Assemble all frozen D14.S fields from the separate P14.1 node outputs. -/
noncomputable def assembleSolver {κ : CConsts} {T : Stage} {k : ℕ}
    {𝒯 : Tiling κ T k} {i : Fin 𝒯.m} {mesh : Mesh 𝒯}
    (Geom : ProjectionGeometry κ 𝒯 i) (H : PrimitiveHistory κ 𝒯 i mesh)
    (O : OddKernels H) (R : EvenRows H O) (Tests : GoodTests Geom H O R)
    (he : EligibilityFacts H) (hsupp : RowSupport H O R)
    (hmean : RowMeanBound Geom H O R)
    (hlocal : LocalSymmetry Geom H O R Tests) : SliceSolver κ 𝒯 i mesh := {
  Rec := H.Rec
  recFin := H.recFin
  loc := H.loc
  Val := H.Val
  valFin := H.valFin
  lawRec := H.lawRec
  lawRec_nonneg := H.lawRec_nonneg
  lawRec_sum := H.lawRec_sum
  lawRec_cont := H.lawRec_cont
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
  σ_nonneg := R.nonneg
  σ_prob := R.probability
  σ_support := hsupp
  σ_cap := R.cap
  σ_mean := by simpa [RowMeanBound] using hmean
  Hgood_zero := Tests.zero_bound
  Hgood_bad := Tests.bad_bound
  q_local := hlocal.q_local
  U_local := hlocal.U_local
  σ_local := hlocal.σ_local
  Hgood_local := hlocal.Hgood_local
  averaged_marginal_invariant := hlocal.averaged_marginal_invariant
  low_support := he.low_support
}

/-- P14.1l: symmetry of the complete low-mode output after the D14.S fields
have been assembled. -/
theorem low_output_group_invariant {κ : CConsts} {T : Stage} {k : ℕ}
    {𝒯 : Tiling κ T k} {i : Fin 𝒯.m} {mesh : Mesh 𝒯}
    (Geom : ProjectionGeometry κ 𝒯 i) (H : PrimitiveHistory κ 𝒯 i mesh)
    (O : OddKernels H) (R : EvenRows H O) (Tests : GoodTests Geom H O R)
    (he : EligibilityFacts H) (hsupp : RowSupport H O R)
    (hmean : RowMeanBound Geom H O R) (hlocal : LocalSymmetry Geom H O R Tests) :
    LowOutputInvariant (assembleSolver Geom H O R Tests he hsupp hmean hlocal) := by
  sorry

/-- A solver together with the group symmetry needed to define one low-mode
profile for the whole patch. -/
structure SolverWitness {κ : CConsts} {T : Stage} {k : ℕ}
    {𝒯 : Tiling κ T k} {i : Fin 𝒯.m} {mesh : Mesh 𝒯} where
  solver : SliceSolver κ 𝒯 i mesh
  low_output_invariant : LowOutputInvariant solver
  cheap_raw_support : ∀ p g y, solver.oddMean p g y > 0 →
    ∃ v : mesh.V, 0 < mesh.wt v p ∧
      mesh.paramPrice (mesh.base v) i y ≤ 10 / (𝒯.P i).M

/-- Fixed-index assembly of the P14.1 construction. -/
theorem internal_slice_solver_at_patch (κ : CConsts) (hκ : κ.Admissible)
    (hconst : HeightConstantContract κ) (T : Stage)
    {k : ℕ} (𝒯 : Tiling κ T k) (h𝒯 : Tiling.Valid 𝒯)
    (hcluster : 𝒯.mode.isCluster) (mesh : Mesh 𝒯) (hclean : MeshCleaned mesh)
    (i : Fin 𝒯.m) : Nonempty (SolverWitness (𝒯 := 𝒯) (i := i) (mesh := mesh)) := by
  classical
  obtain ⟨Geom⟩ := projection_geometry κ hκ 𝒯 h𝒯 hcluster i
  obtain ⟨H⟩ := primitive_history κ hκ 𝒯 h𝒯 hcluster i mesh hclean
  have hmask : ∀ (g : Group 𝒯 i) (W : ∀ r, H.Val r),
      MaskFacts i mesh (H.maskVertex g W) := fun g W =>
    Classical.choice (masks_and_price_cut κ hκ h𝒯 mesh hclean (H.maskVertex g W))
  obtain ⟨L⟩ := candidate_list_models κ hκ h𝒯 hcluster hclean H hmask
  have hcounts := position_count_concentration κ hκ hconst h𝒯 hcluster H
  have he : EligibilityFacts H := searches_eligibility κ hκ hconst h𝒯 hcluster Geom
    H hclean hmask L hcounts
  let hh : HeightFacts H := height_selection_at_patch κ hκ hconst h𝒯 hcluster H he
  obtain ⟨O⟩ := odd_bin_laws κ hκ h𝒯 H hmask he hh
  obtain ⟨Lratio⟩ := likelihood_ratio_domination κ hκ h𝒯 Geom
    Geom.fiber_card Geom.multiplicity_eq Geom.multiplicity_lower Geom.multiplicity_sum H O
  obtain ⟨R⟩ := posterior_even_rows κ hκ h𝒯 H O Lratio
  have hsupp : RowSupport H O R := posterior_row_support κ hκ h𝒯 H O R hh hmask
  have hmean : RowMeanBound Geom H O R :=
    posterior_row_mean κ hκ h𝒯 hconst H Geom O R Lratio
  obtain ⟨Tests⟩ := posterior_good_tests κ hκ hconst h𝒯 H Geom O R hh Lratio
  have hlocal : LocalSymmetry Geom H O R Tests :=
    locality_and_symmetry κ hκ h𝒯 Geom H O R Tests hh
  let S := assembleSolver Geom H O R Tests he hsupp hmean hlocal
  have hlow : LowOutputInvariant S :=
    low_output_group_invariant Geom H O R Tests he hsupp hmean hlocal
  refine ⟨⟨S, hlow, ?_⟩⟩
  intro p g y hpos
  simpa [SliceSolver.oddMean, SliceSolver.oddMarginal, PrimitiveHistory.recLaw] using
    O.cheap_mean_support p g y hpos

/-- P14.1: for all sufficiently large stage indices, each cleaned cluster
patch and mesh has a solver satisfying the frozen D14.S interface. -/
theorem internal_slice_solver (κ : CConsts) (hκ : κ.Admissible)
    (hconst : HeightConstantContract κ) (T : Stage) :
    ∀ᶠ k in atTop, ∀ (𝒯 : Tiling κ T k), Tiling.Valid 𝒯 → 𝒯.mode.isCluster →
      ∀ mesh : Mesh 𝒯, MeshCleaned mesh → ∀ i : Fin 𝒯.m,
        Nonempty (SolverWitness (𝒯 := 𝒯) (i := i) (mesh := mesh)) := by
  refine Filter.eventually_atTop.2 ⟨0, ?_⟩
  intro k _hk 𝒯 h𝒯 hcluster mesh hclean i
  exact internal_slice_solver_at_patch κ hκ hconst T 𝒯 h𝒯 hcluster mesh hclean i

end HypercubeRamsey.S14
