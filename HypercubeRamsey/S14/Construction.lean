import HypercubeRamsey.PartC.ProfiledTiling
import HypercubeRamsey.S03.Height.Selection
import HypercubeRamsey.S03.Mixtures
import HypercubeRamsey.S14.Construction_q_s14_geom

open HypercubeRamsey.S14.Geometry_q_s14_geom

set_option maxHeartbeats 5000000

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
  have hminη : min κ.xs (min κ.η0 0.01) ≤ κ.η0 :=
    le_trans (min_le_right _ _) (min_le_left _ _)
  have hιη : κ.ι < κ.η0 / 1000 := by
    calc
      κ.ι < min κ.xs (min κ.η0 0.01) / 1000 := hκ.ι_rng.2
      _ ≤ κ.η0 / 1000 := by gcongr
  have hgap : 0 < κ.η0 - 4 * κ.ι := by nlinarith [hκ.η0_pos]
  have hbudgetLarge : ∀ᶠ k in atTop,
      12 ≤ (T.S.n k : ℝ) ^ (κ.η0 - 4 * κ.ι) := by
    have htend := (tendsto_rpow_atTop hgap).comp
      (tendsto_natCast_atTop_atTop.comp T.S.n_tendsto)
    exact htend.eventually_ge_atTop 12
  have hCbPos : 0 < κ.Cb := by
    have hfrac : 0 < 100 * κ.aC / κ.aB :=
      div_pos (mul_pos (by norm_num) hκ.aC_rng.1) hκ.aB_rng.1
    nlinarith [hκ.Cb_big]
  have hMloPos : 0 < (κ.Mlo : ℝ) := by nlinarith [hκ.Mlo_big]
  have hMloNat : 0 < κ.Mlo := by exact_mod_cast hMloPos
  have hMloOneNat : 1 ≤ κ.Mlo := Nat.succ_le_iff.mpr hMloNat
  have hMloOne : 1 ≤ (κ.Mlo : ℝ) := by exact_mod_cast hMloOneNat
  have hMhiPos : 0 < (κ.Mhi : ℝ) := by
    have hqpos : 0 < 10 / κ.cq := div_pos (by norm_num) hκ.cq_rng.1
    nlinarith [hκ.Mhi_big.1, hMloPos]
  have hMhiNat : 0 < κ.Mhi := by exact_mod_cast hMhiPos
  have hMhiOneNat : 1 ≤ κ.Mhi := Nat.succ_le_iff.mpr hMhiNat
  have hMhiOne : 1 ≤ (κ.Mhi : ℝ) := by exact_mod_cast hMhiOneNat
  have hωlt : κ.ω < 1 := by
    have haC : κ.aC < 1 / 10 ^ 6 := by
      calc
        κ.aC < min κ.η0 1 / 10 ^ 6 := hκ.aC_rng.2
        _ ≤ 1 / 10 ^ 6 := by
          gcongr
          exact min_le_right _ _
    have hωhi := hκ.ω_rng.2
    have hωle : κ.ω ≤ κ.ω * (κ.Mhi : ℝ) := by
      calc
        κ.ω = κ.ω * 1 := by ring
        _ ≤ κ.ω * (κ.Mhi : ℝ) :=
          mul_le_mul_of_nonneg_left hMhiOne (le_of_lt hκ.ω_rng.1)
    nlinarith [hκ.Mhi_big.1, hMhiOne, hωle]
  have hxiSmall : κ.ξ < 1 / 100 := by
    have hpow : Real.rpow 2 (-(10 * (κ.u : ℝ) + 100)) < 1 :=
      Real.rpow_lt_one_of_one_lt_of_neg one_lt_two (by
        have hu : 0 ≤ (κ.u : ℝ) := Nat.cast_nonneg _
        linarith)
    have hmul : κ.α * Real.rpow 2 (-(10 * (κ.u : ℝ) + 100)) < κ.α := by
      calc
        κ.α * Real.rpow 2 (-(10 * (κ.u : ℝ) + 100)) < κ.α * 1 :=
          mul_lt_mul_of_pos_left hpow hκ.α_rng.1
        _ = κ.α := by ring
    calc
      κ.ξ < κ.α * Real.rpow 2 (-(10 * (κ.u : ℝ) + 100)) := hκ.ξ_rng.2
      _ < κ.α := hmul
      _ < 1 / 100 := by nlinarith [hκ.α_rng.2]
  have haSmall : κ.a ≤ 1 / 10 := by
    have hξsq : κ.ξ ^ 2 < (1 / 100 : ℝ) ^ 2 := by
      nlinarith [hκ.ξ_rng.1, hxiSmall]
    have hden : (3 : ℝ) ≤ 3 * (4 : ℝ) ^ (κ.u + 3 : ℕ) := by
      have hp : 1 ≤ (4 : ℝ) ^ (κ.u + 3 : ℕ) :=
        one_le_pow₀ (by norm_num)
      nlinarith
    have hfrac₁ : κ.ξ ^ 2 / (3 * 4 ^ (κ.u + 3 : ℕ)) ≤ κ.ξ ^ 2 / 3 :=
      div_le_div_of_nonneg_left (sq_nonneg κ.ξ) (by norm_num) hden
    have hfrac₂ : κ.ξ ^ 2 / 3 ≤ (1 / 100 : ℝ) ^ 2 / 3 := by
      gcongr
    have hθ : κ.θ < (1 / 100 : ℝ) ^ 2 / 3 :=
      lt_of_lt_of_le hκ.θ_rng.2 (le_trans hfrac₁ hfrac₂)
    rw [hκ.a_eq]
    nlinarith
  have hceilK : ∀ h : ℕ, 1 ≤ h → sliceK κ h ≤ h ^ 3 := by
    intro h hhNat
    change ⌈Real.rpow (h : ℝ) (3 * κ.ω)⌉₊ ≤ h ^ 3
    rw [Nat.ceil_le, Nat.cast_pow]
    have hh : 1 ≤ (h : ℝ) := by exact_mod_cast hhNat
    have hexp : 3 * κ.ω ≤ 3 := by linarith [hωlt]
    calc
      Real.rpow (h : ℝ) (3 * κ.ω) ≤ Real.rpow (h : ℝ) 3 :=
        Real.rpow_le_rpow_of_exponent_le hh hexp
      _ = (h : ℝ) ^ 3 := Real.rpow_natCast (h : ℝ) 3
  have hceilT : ∀ h : ℕ, 1 ≤ h → sliceT κ h ≤ h := by
    intro h hhNat
    change ⌈Real.rpow (h : ℝ) κ.ω⌉₊ ≤ h
    rw [Nat.ceil_le]
    have hh : 1 ≤ (h : ℝ) := by exact_mod_cast hhNat
    have hexp : κ.ω ≤ 1 := hωlt.le
    calc
      Real.rpow (h : ℝ) κ.ω ≤ Real.rpow (h : ℝ) 1 :=
        Real.rpow_le_rpow_of_exponent_le hh hexp
      _ = (h : ℝ) := Real.rpow_one (h : ℝ)
  filter_upwards [T.S.n_tendsto.eventually_ge_atTop 1, hbudgetLarge] with k hnk hgrow
  intro 𝒯 h𝒯 hcluster i
  classical
  have hmodeCluster : 𝒯.mode = .lowCluster ∨ 𝒯.mode = .highSmall ∨
      𝒯.mode = .highLarge := by
    cases hm : 𝒯.mode <;> simp [Mode.isCluster, hm] at hcluster ⊢
  have hclusterData := h𝒯.cluster_data hmodeCluster i
  rcases hclusterData with
    ⟨hscaleLo, hgq, hMbound, hdSmall, hdLarge, hcodegree, hdyadic, hExpLo, hExpHi,
      hLowMode, hSmallMode, hLargeMode⟩
  have hhNatPos : 0 < (𝒯.P i).h := by
    rw [hdyadic]
    positivity
  have hhNatOne : 1 ≤ (𝒯.P i).h := Nat.succ_le_of_lt hhNatPos
  have hmodeLarge : 𝒯.mode = .lowCluster ∨ 𝒯.mode = .highSmall ∨
      𝒯.mode = .highLarge := hmodeCluster
  have hqpos : 0 < ((𝒯.P i).q : ℝ) := by
    have hhpos : 0 < ((𝒯.P i).h : ℝ) := by
      rw [hdyadic]
      positivity
    have hexpPos : 0 < (if 𝒯.mode = .lowCluster then (κ.Mlo : ℝ)
        else (κ.Mhi : ℝ)) := by
      split_ifs with hm
      · exact hMloPos
      · exact hMhiPos
    by_contra hq
    have hq0 : (↑(𝒯.P i).q : ℝ) = 0 := by
      exact le_antisymm (not_lt.mp hq) (Nat.cast_nonneg _)
    have hexpZero : Real.rpow (↑(𝒯.P i).q : ℝ)
        (if 𝒯.mode = .lowCluster then (κ.Mlo : ℝ) else (κ.Mhi : ℝ)) = 0 := by
      rw [hq0]
      change (0 : ℝ) ^
        (if 𝒯.mode = .lowCluster then (κ.Mlo : ℝ) else (κ.Mhi : ℝ)) = 0
      exact Real.zero_rpow (ne_of_gt hexpPos)
    rw [hexpZero] at hExpHi
    norm_num at hExpHi
    linarith
  have hqNatPos : 0 < (𝒯.P i).q := by exact_mod_cast hqpos
  have hqone : 1 ≤ ((𝒯.P i).q : ℝ) := by
    exact_mod_cast (Nat.succ_le_iff.mpr hqNatPos)
  have hM1pos : 0 < κ.M1 := by linarith [hκ.M1_big.1]
  have hqQ0 : κ.Q0 ≤ (𝒯.P i).q := by
    have hmax : max (↑(𝒯.P i).g : ℝ) (↑(𝒯.P i).q : ℝ) ≤
        κ.M1 * (↑(𝒯.P i).q : ℝ) := by
      apply max_le
      · exact hgq
      · nlinarith [hκ.M1_big.1, hqone]
    have hmul : κ.M1 * κ.Q0 ≤ κ.M1 * (↑(𝒯.P i).q : ℝ) :=
      le_trans hscaleLo (by simpa using hmax)
    exact (mul_le_mul_iff_of_pos_left hM1pos).mp hmul
  have hMloLeMhi : (κ.Mlo : ℝ) ≤ (κ.Mhi : ℝ) := by
    have hcq : 0 < κ.cq := hκ.cq_rng.1
    have := hκ.Mhi_big.1
    have hdiv : 0 < 10 / κ.cq := by positivity
    nlinarith
  have heLo : (κ.Mlo : ℝ) ≤
      (if 𝒯.mode = .lowCluster then (κ.Mlo : ℝ) else (κ.Mhi : ℝ)) := by
    by_cases hm : 𝒯.mode = .lowCluster
    · simp [hm]
    · simpa [hm] using hMloLeMhi
  have heHi :
      (if 𝒯.mode = .lowCluster then (κ.Mlo : ℝ) else (κ.Mhi : ℝ)) ≤
        (κ.Mhi : ℝ) := by
    by_cases hm : 𝒯.mode = .lowCluster
    · simpa [hm] using hMloLeMhi
    · simp [hm]
  have hQ0 := hκ.Q0_large (↑(𝒯.P i).q : ℝ) hqQ0
  unfold QCond at hQ0
  rcases hQ0 with ⟨_, _, _, _, _, _, _, _, hQrange⟩
  have hQparts := hQrange (𝒯.P i).h
    (by
      calc
        Real.rpow (↑(𝒯.P i).q : ℝ) (κ.Mlo : ℝ) ≤
            Real.rpow (↑(𝒯.P i).q : ℝ)
              (if 𝒯.mode = .lowCluster then (κ.Mlo : ℝ) else (κ.Mhi : ℝ)) :=
          Real.rpow_le_rpow_of_exponent_le hqone heLo
        _ ≤ (↑(𝒯.P i).h : ℝ) := hExpLo)
    (by
      have hrpow := Real.rpow_le_rpow_of_exponent_le hqone heHi
      exact lt_of_lt_of_le hExpHi (mul_le_mul_of_nonneg_left hrpow (by norm_num)))
  rcases hQparts with ⟨hh0, _, htrunc, _, _, hpretrim, _, _, _, _, _⟩
  have hnpos : 1 ≤ (T.S.n k : ℝ) := by exact_mod_cast hnk
  have hMpos : 0 < (𝒯.P i).M := by
    obtain ⟨hX, _⟩ := h𝒯.patch_nonempty i
    rw [← (𝒯.P i).cardX]
    exact_mod_cast (Finset.card_pos.mpr hX)
  have hMposR : 0 < ((𝒯.P i).M : ℝ) := by exact_mod_cast hMpos
  have hMhiNat : 0 < κ.Mhi := by exact_mod_cast hMhiPos
  have huPos : 0 < (κ.u : ℝ) := by
    have huLarge := hκ.u_rng.2
    have huNat : 0 < κ.u := by omega
    exact_mod_cast huNat
  have hkScale : 𝒯.kScale i ≤ (𝒯.P i).h ^ 3 := by
    simpa [Tiling.kScale] using hceilK (𝒯.P i).h hhNatOne
  have htScale : 𝒯.tScale i ≤ (𝒯.P i).h := by
    simpa [Tiling.tScale] using hceilT (𝒯.P i).h hhNatOne
  have halloc := h𝒯.allocation_bounds i
  have hhN : ((𝒯.P i).h : ℝ) < (T.S.n k : ℝ) ^ κ.ι := by
    exact lt_of_le_of_lt (by
      exact_mod_cast (le_max_left (𝒯.P i).h (𝒯.P i).ℓ)) halloc.1
  have hlogNM : Real.log ((T.S.N k : ℝ) / (𝒯.P i).M) ≤
      (𝒯.gain i) / (1000 * κ.u) := by
    rcases halloc.2 with hb | ⟨_, hlog⟩
    · simp [Mode.isCluster, hb] at hcluster
    · exact hlog
  have hgain : 𝒯.gain i = κ.a * (𝒯.P i).h / 10 ^ 6 := by
    cases hm : 𝒯.mode <;> simp [Tiling.gain, Mode.isCluster, hm] at hcluster ⊢
  have hlogSmall : Real.log ((T.S.N k : ℝ) / (𝒯.P i).M) ≤ (𝒯.P i).h := by
    rw [hgain] at hlogNM
    have hcoef : κ.a / (10 ^ 6 * (1000 * κ.u)) ≤ 1 := by
      have huNat : 0 < κ.u := by exact_mod_cast huPos
      have hu : 1 ≤ (κ.u : ℝ) := by
        exact_mod_cast (Nat.succ_le_iff.mpr huNat)
      have hden : 1 ≤ 10 ^ 6 * (1000 * (κ.u : ℝ)) := by nlinarith only [hu]
      have hnum : κ.a ≤ 1 := by linarith only [haSmall]
      have hraw : κ.a ≤ 10 ^ 6 * (1000 * (κ.u : ℝ)) := by linarith only [hden, hnum]
      exact (div_le_iff₀ (show 0 < 10 ^ 6 * (1000 * (κ.u : ℝ)) by positivity)).2
        (by simpa using hraw)
    have hhpos : 0 ≤ ((𝒯.P i).h : ℝ) := Nat.cast_nonneg _
    have hdiv : κ.a * (↑(𝒯.P i).h : ℝ) / 10 ^ 6 / (1000 * κ.u) ≤
        (𝒯.P i).h := by
      have hfactor : κ.a * (↑(𝒯.P i).h : ℝ) / 10 ^ 6 / (1000 * κ.u) =
          (κ.a / (10 ^ 6 * (1000 * κ.u))) * (𝒯.P i).h := by
        field_simp
      calc
        κ.a * (↑(𝒯.P i).h : ℝ) / 10 ^ 6 / (1000 * κ.u) =
            (κ.a / (10 ^ 6 * (1000 * κ.u))) * (𝒯.P i).h := hfactor
        _ ≤ 1 * (𝒯.P i).h := mul_le_mul_of_nonneg_right hcoef hhpos
        _ = (𝒯.P i).h := by ring
    exact hlogNM.trans (by simpa [div_eq_mul_inv, mul_assoc, mul_comm, mul_left_comm] using hdiv)
  have hscaleTerm : 2 * (𝒯.kScale i : ℝ) * 𝒯.tScale i ≤
      2 * ((𝒯.P i).h : ℝ) ^ 4 := by
    have hk : (𝒯.kScale i : ℝ) ≤ ((𝒯.P i).h : ℝ) ^ 3 := by exact_mod_cast hkScale
    have ht : (𝒯.tScale i : ℝ) ≤ (𝒯.P i).h := by exact_mod_cast htScale
    have hht : 0 ≤ (𝒯.P i).h := Nat.cast_nonneg _
    calc
      2 * (𝒯.kScale i : ℝ) * 𝒯.tScale i ≤
          2 * ((𝒯.P i).h : ℝ) ^ 3 * (𝒯.P i).h := by gcongr
      _ = 2 * ((𝒯.P i).h : ℝ) ^ 4 := by ring
  have hsmallBudget : 2 * (𝒯.kScale i : ℝ) * 𝒯.tScale i +
      Real.log ((T.S.N k : ℝ) / (𝒯.P i).M) + 3 ≤
      (T.S.n k : ℝ) ^ κ.η0 / 2 := by
    have hpowI : ((𝒯.P i).h : ℝ) ^ 4 ≤ (T.S.n k : ℝ) ^ (4 * κ.ι) := by
      calc
        ((𝒯.P i).h : ℝ) ^ 4 = Real.rpow ((𝒯.P i).h : ℝ) 4 :=
          (Real.rpow_natCast ((𝒯.P i).h : ℝ) 4).symm
        _ ≤ Real.rpow ((T.S.n k : ℝ) ^ κ.ι) 4 := by
          exact Real.rpow_le_rpow (by positivity) (le_of_lt hhN) (by norm_num)
        _ = Real.rpow (T.S.n k : ℝ) (κ.ι * 4) :=
          (Real.rpow_mul (le_trans (by norm_num) hnpos) κ.ι 4).symm
        _ = (T.S.n k : ℝ) ^ (4 * κ.ι) := by congr 1; ring
    have hhSq : 1 ≤ ((𝒯.P i).h : ℝ) ^ 4 := by
      have hh : 1 ≤ ((𝒯.P i).h : ℝ) := by exact_mod_cast hhNatOne
      exact one_le_pow₀ hh
    have hmain : 6 * (T.S.n k : ℝ) ^ (4 * κ.ι) ≤
        (T.S.n k : ℝ) ^ κ.η0 / 2 := by
      have hdecomp : (T.S.n k : ℝ) ^ κ.η0 =
          (T.S.n k : ℝ) ^ (4 * κ.ι) *
            (T.S.n k : ℝ) ^ (κ.η0 - 4 * κ.ι) := by
        have heqExp : 4 * κ.ι + (κ.η0 - 4 * κ.ι) = κ.η0 := by ring
        calc
          (T.S.n k : ℝ) ^ κ.η0 =
              (T.S.n k : ℝ) ^ (4 * κ.ι + (κ.η0 - 4 * κ.ι)) :=
            congrArg (Real.rpow (T.S.n k : ℝ)) heqExp.symm
          _ = (T.S.n k : ℝ) ^ (4 * κ.ι) *
              (T.S.n k : ℝ) ^ (κ.η0 - 4 * κ.ι) :=
            @Real.rpow_add (T.S.n k : ℝ) (lt_of_lt_of_le zero_lt_one hnpos)
              (4 * κ.ι) (κ.η0 - 4 * κ.ι)
      have hA_nonneg : 0 ≤ Real.rpow (T.S.n k : ℝ) (4 * κ.ι) :=
        @Real.rpow_nonneg (T.S.n k : ℝ) (le_trans (by norm_num) hnpos) (4 * κ.ι)
      have hmul : Real.rpow (T.S.n k : ℝ) (4 * κ.ι) * 12 ≤
          Real.rpow (T.S.n k : ℝ) (4 * κ.ι) *
            Real.rpow (T.S.n k : ℝ) (κ.η0 - 4 * κ.ι) :=
        mul_le_mul_of_nonneg_left hgrow hA_nonneg
      calc
        6 * (T.S.n k : ℝ) ^ (4 * κ.ι) =
            ((T.S.n k : ℝ) ^ (4 * κ.ι) * 12) / 2 := by ring
        _ ≤ (((T.S.n k : ℝ) ^ (4 * κ.ι) *
            (T.S.n k : ℝ) ^ (κ.η0 - 4 * κ.ι)) / 2) :=
          div_le_div_of_nonneg_right hmul (by norm_num)
        _ = (T.S.n k : ℝ) ^ κ.η0 / 2 := by rw [← hdecomp]
    have hpow3 : (𝒯.P i).h ≤ ((𝒯.P i).h : ℝ) ^ 4 := by
      have hh : 1 ≤ ((𝒯.P i).h : ℝ) := by exact_mod_cast hhNatOne
      have h3 : 1 ≤ ((𝒯.P i).h : ℝ) ^ 3 := one_le_pow₀ hh
      calc
        ((𝒯.P i).h : ℝ) = ((𝒯.P i).h : ℝ) * 1 := by ring
        _ ≤ ((𝒯.P i).h : ℝ) * ((𝒯.P i).h : ℝ) ^ 3 :=
          mul_le_mul_of_nonneg_left h3 (by positivity)
        _ = ((𝒯.P i).h : ℝ) ^ 4 := by ring
    have hsumSmall : 2 * (𝒯.kScale i : ℝ) * 𝒯.tScale i +
        Real.log ((T.S.N k : ℝ) / (𝒯.P i).M) ≤
          2 * ((𝒯.P i).h : ℝ) ^ 4 + (𝒯.P i).h :=
      add_le_add hscaleTerm hlogSmall
    calc
      2 * (𝒯.kScale i : ℝ) * 𝒯.tScale i +
          Real.log ((T.S.N k : ℝ) / (𝒯.P i).M) + 3
          = (2 * (𝒯.kScale i : ℝ) * 𝒯.tScale i +
              Real.log ((T.S.N k : ℝ) / (𝒯.P i).M)) + 3 := by ring
      _ ≤ (2 * ((𝒯.P i).h : ℝ) ^ 4 + (𝒯.P i).h) + 3 :=
        by linarith only [hsumSmall]
      _ ≤ 6 * ((𝒯.P i).h : ℝ) ^ 4 := by
        nlinarith only [hhSq, hpow3]
      _ ≤ 6 * (T.S.n k : ℝ) ^ (4 * κ.ι) := by gcongr
      _ ≤ (T.S.n k : ℝ) ^ κ.η0 / 2 := hmain
  have hNcast : 0 < (T.S.N k : ℝ) := by exact_mod_cast T.S.N_pos k
  have hprior : 2 / (𝒯.P i).M ≤
      Real.exp ((T.S.n k : ℝ) ^ κ.η0 / 2) / (T.S.N k) := by
    have hratio : 0 < (T.S.N k : ℝ) / (𝒯.P i).M := div_pos hNcast hMposR
    have hlogle : Real.log (2 * (T.S.N k : ℝ) / (𝒯.P i).M) ≤
        (T.S.n k : ℝ) ^ κ.η0 / 2 := by
      have hlog2 : Real.log 2 ≤ 3 := by
        rw [Real.log_le_iff_le_exp (by norm_num)]
        have h := Real.add_one_le_exp (3 : ℝ)
        nlinarith
      have hlogarg : 2 * (T.S.N k : ℝ) / (𝒯.P i).M =
          2 * ((T.S.N k : ℝ) / (𝒯.P i).M) := by ring
      rw [hlogarg, Real.log_mul (by norm_num : (2:ℝ) ≠ 0) (ne_of_gt hratio)]
      nlinarith only [hsmallBudget, hlog2]
    have hExp := Real.exp_le_exp.mpr hlogle
    have hratio2 : 0 < 2 * (T.S.N k : ℝ) / (𝒯.P i).M := by positivity
    have hExp' : 2 * (T.S.N k : ℝ) / (𝒯.P i).M ≤
        Real.exp ((T.S.n k : ℝ) ^ κ.η0 / 2) := by
      simpa only [Real.exp_log hratio2] using hExp
    rw [div_le_div_iff₀ hMposR hNcast]
    have hmul := mul_le_mul_of_nonneg_right hExp' (le_of_lt hMposR)
    field_simp at hmul ⊢
    nlinarith
  have haPos : 0 < κ.a := by
    rw [hκ.a_eq]
    exact div_pos hκ.θ_rng.1 (by norm_num)
  have hhPosR : 0 ≤ ((𝒯.P i).h : ℝ) := by exact_mod_cast (Nat.zero_le (𝒯.P i).h)
  have hAhNonneg : 0 ≤ κ.a * (𝒯.P i).h := mul_nonneg (le_of_lt haPos) hhPosR
  have hlogC : Real.log (200 / κ.a) ≤ (0.0195 : ℝ) * κ.a * (𝒯.P i).h := by
    nlinarith only [htrunc]
  have hbase4 : 4 ≤ 200 / κ.a := by
    rw [le_div_iff₀ haPos]
    nlinarith only [haSmall]
  have hCpos : 0 < 200 / κ.a := div_pos (by norm_num) haPos
  have hlog4 : Real.log 4 ≤ Real.log (200 / κ.a) := by
    rw [Real.log_le_iff_le_exp (by norm_num)]
    rw [Real.exp_log hCpos]
    exact hbase4
  have hlog4eq : Real.log (4 : ℝ) = Real.log 2 + Real.log 2 := by
    rw [show (4 : ℝ) = 2 * 2 by norm_num,
      Real.log_mul (by norm_num) (by norm_num)]
  have hlog2small : Real.log 2 ≤ (0.00975 : ℝ) * κ.a * (𝒯.P i).h := by
    nlinarith only [hlogC, hlog4, hlog4eq]
  have huNatPos : 0 < κ.u := by exact_mod_cast huPos
  have huOne : 1 ≤ κ.u := Nat.succ_le_iff.mpr huNatPos
  have hden4000 : (4000 : ℝ) ≤ 10 ^ 9 * κ.u := by
    have huOneR : 1 ≤ (κ.u : ℝ) := by exact_mod_cast huOne
    calc
      (4000 : ℝ) ≤ 10 ^ 9 := by norm_num
      _ ≤ 10 ^ 9 * (κ.u : ℝ) := by
        calc
          10 ^ 9 = 10 ^ 9 * 1 := by ring
          _ ≤ 10 ^ 9 * (κ.u : ℝ) := mul_le_mul_of_nonneg_left huOneR (by norm_num)
  have hlogNMTiny : Real.log ((T.S.N k : ℝ) / (𝒯.P i).M) ≤
      (0.00025 : ℝ) * κ.a * (𝒯.P i).h := by
    have hgainBound : Real.log ((T.S.N k : ℝ) / (𝒯.P i).M) ≤
        κ.a * (𝒯.P i).h / (10 ^ 9 * κ.u) := by
      rw [hgain] at hlogNM
      have heq : κ.a * (𝒯.P i).h / 10 ^ 6 / (1000 * κ.u) =
          κ.a * (𝒯.P i).h / (10 ^ 9 * κ.u) := by ring
      rw [heq] at hlogNM
      exact hlogNM
    have hdiv := div_le_div_of_nonneg_left hAhNonneg (by norm_num : 0 < (4000 : ℝ)) hden4000
    have hfrac : κ.a * (𝒯.P i).h / (10 ^ 9 * κ.u) ≤
        (0.00025 : ℝ) * κ.a * (𝒯.P i).h := by
      have : κ.a * (𝒯.P i).h / (10 ^ 9 * κ.u) ≤
          κ.a * (𝒯.P i).h / 4000 := hdiv
      norm_num at this ⊢
      nlinarith
    exact hgainBound.trans hfrac
  have hpost : Real.log (2 * (T.S.N k : ℝ) / (𝒯.P i).M) ≤
      (0.01 : ℝ) * κ.a * (𝒯.P i).h := by
    have hratio : 0 < (T.S.N k : ℝ) / (𝒯.P i).M := by positivity
    have harg : 2 * (T.S.N k : ℝ) / (𝒯.P i).M =
        2 * ((T.S.N k : ℝ) / (𝒯.P i).M) := by ring
    rw [harg, Real.log_mul (by norm_num) (ne_of_gt hratio)]
    nlinarith only [hlog2small, hlogNMTiny]
  have htruncInner : (200 / κ.a) *
      Real.exp (-0.02 * κ.a * (𝒯.P i).h) ≤
        Real.exp (-500 * 𝒯.gain i) := by
    have hlogexp : Real.log (200 / κ.a) + (-0.02 * κ.a * (𝒯.P i).h) ≤
        -500 * (κ.a * (𝒯.P i).h / 10 ^ 6) := by
      nlinarith only [htrunc]
    have hmulExp : (200 / κ.a) * Real.exp (-0.02 * κ.a * (𝒯.P i).h) =
        Real.exp (Real.log (200 / κ.a) + (-0.02 * κ.a * (𝒯.P i).h)) := by
      calc
        _ = Real.exp (Real.log (200 / κ.a)) *
            Real.exp (-0.02 * κ.a * (𝒯.P i).h) := by
              rw [Real.exp_log (by positivity)]
        _ = _ := (Real.exp_add _ _).symm
    calc
      (200 / κ.a) * Real.exp (-0.02 * κ.a * (𝒯.P i).h) =
          Real.exp (Real.log (200 / κ.a) + (-0.02 * κ.a * (𝒯.P i).h)) := hmulExp
      _ ≤ Real.exp (-500 * (κ.a * (𝒯.P i).h / 10 ^ 6)) :=
          Real.exp_le_exp.mpr hlogexp
      _ = Real.exp (-500 * 𝒯.gain i) := by rw [hgain]
  have htruncation : (200 / κ.a) * 2 ^ (𝒯.P i).h *
      Real.exp (-0.02 * κ.a * (𝒯.P i).h) ≤
        2 ^ (𝒯.P i).h * Real.exp (-500 * 𝒯.gain i) := by
    calc
      (200 / κ.a) * 2 ^ (𝒯.P i).h * Real.exp (-0.02 * κ.a * (𝒯.P i).h) =
          (2 ^ (𝒯.P i).h : ℝ) *
            ((200 / κ.a) * Real.exp (-0.02 * κ.a * (𝒯.P i).h)) := by ring
      _ ≤ (2 ^ (𝒯.P i).h : ℝ) * Real.exp (-500 * 𝒯.gain i) :=
          mul_le_mul_of_nonneg_left htruncInner (by positivity)
  have hpretrimGoal : ((𝒯.P i).h : ℝ) ^ 2 *
      Real.sqrt (sliceEps κ (𝒯.P i).h) ≤ 1 / 4 := by
    have hh4 : 1 ≤ ((𝒯.P i).h : ℝ) ^ 4 := by
      exact one_le_pow₀ (by exact_mod_cast hhNatOne)
    have hpow : ((𝒯.P i).h : ℝ) ^ 2 ≤ ((𝒯.P i).h : ℝ) ^ 6 := by
      calc
        ((𝒯.P i).h : ℝ) ^ 2 ≤ ((𝒯.P i).h : ℝ) ^ 2 * ((𝒯.P i).h : ℝ) ^ 4 :=
          le_mul_of_one_le_right (by positivity) hh4
        _ = ((𝒯.P i).h : ℝ) ^ 6 := by ring
    have hrootnonneg : 0 ≤ Real.sqrt (sliceEps κ (𝒯.P i).h) :=
      Real.sqrt_nonneg (sliceEps κ (𝒯.P i).h)
    have hsmallEps : Real.rpow 10 (-3 : ℝ) = 1 / 1000 := by
      calc
        Real.rpow 10 (-3 : ℝ) = (10 : ℝ) ^ (-3 : ℤ) :=
          Real.rpow_neg_natCast (10 : ℝ) 3
        _ = 1 / 1000 := by norm_num
    have hmul := mul_le_mul_of_nonneg_right hpow hrootnonneg
    calc
      ((𝒯.P i).h : ℝ) ^ 2 * Real.sqrt (sliceEps κ (𝒯.P i).h) ≤
          ((𝒯.P i).h : ℝ) ^ 6 * Real.sqrt (sliceEps κ (𝒯.P i).h) := hmul
      _ ≤ 1 / 1000 := by
        calc
          _ ≤ Real.rpow 10 (-3 : ℝ) := hpretrim
          _ = 1 / 1000 := hsmallEps
      _ ≤ 1 / 4 := by norm_num
  have hkReal : 1 ≤ (𝒯.kScale i : ℝ) := by
    change 1 ≤ (sliceK κ (𝒯.P i).h : ℝ)
    have hh : 1 ≤ ((𝒯.P i).h : ℝ) := by exact_mod_cast hhNatOne
    have hωnonneg : 0 ≤ κ.ω := le_of_lt hκ.ω_rng.1
    have hexpNonneg : 0 ≤ (3 : ℝ) * κ.ω := mul_nonneg (by norm_num) hωnonneg
    have hp := Real.one_le_rpow hh hexpNonneg
    have hceil : Real.rpow ((𝒯.P i).h : ℝ) (3 * κ.ω) ≤
        (sliceK κ (𝒯.P i).h : ℝ) := by
      exact_mod_cast (Nat.le_ceil (Real.rpow ((𝒯.P i).h : ℝ) (3 * κ.ω)))
    exact le_trans hp hceil
  have htReal : 1 ≤ (𝒯.tScale i : ℝ) := by
    change 1 ≤ (sliceT κ (𝒯.P i).h : ℝ)
    have hh : 1 ≤ ((𝒯.P i).h : ℝ) := by exact_mod_cast hhNatOne
    have hp := Real.one_le_rpow hh (le_of_lt hκ.ω_rng.1)
    have hceil : Real.rpow ((𝒯.P i).h : ℝ) κ.ω ≤
        (sliceT κ (𝒯.P i).h : ℝ) := by
      exact_mod_cast (Nat.le_ceil (Real.rpow ((𝒯.P i).h : ℝ) κ.ω))
    exact le_trans hp hceil
  have hkt : 1 ≤ (𝒯.kScale i : ℝ) * 𝒯.tScale i := by
    have hmul := mul_le_mul hkReal htReal (by norm_num : 0 ≤ (1 : ℝ))
      (le_trans (by norm_num : 0 ≤ (1 : ℝ)) hkReal)
    nlinarith only [hmul]
  have hExp2 : 3 ≤ Real.exp 2 := by
    have := Real.add_one_le_exp (2 : ℝ)
    nlinarith
  have hExp2Sq : 9 ≤ (Real.exp 2) ^ 2 := by
    have hm := mul_le_mul_of_nonneg_left hExp2 (Real.exp_nonneg 2)
    nlinarith [hm]
  have hExp2Fourth : 81 ≤ (Real.exp 2) ^ 4 := by
    have hm := mul_le_mul_of_nonneg_left hExp2Sq
      (show 0 ≤ (Real.exp 2) ^ 2 by positivity)
    nlinarith [hm]
  have hExp8 : (32 / 3 : ℝ) ≤ Real.exp 8 := by
    have heq : Real.exp 8 = (Real.exp 2) ^ 4 := by
      rw [show (8 : ℝ) = 2 + (2 + (2 + 2)) by norm_num,
        Real.exp_add, Real.exp_add, Real.exp_add]
      ring
    rw [heq]
    exact le_trans (by norm_num : (32 / 3 : ℝ) ≤ 81) hExp2Fourth
  have hExpLarge : (32 / 3 : ℝ) ≤
      Real.exp (8 * ((𝒯.kScale i : ℝ) * 𝒯.tScale i)) := by
    exact le_trans hExp8 (Real.exp_le_exp.mpr (by nlinarith [hkt]))
  have hcap : (32 / 3 : ℝ) * Real.exp
      (2 * (𝒯.kScale i : ℝ) * 𝒯.tScale i) ≤
      Real.exp (10 * (𝒯.kScale i : ℝ) * 𝒯.tScale i) := by
    calc
      (32 / 3 : ℝ) * Real.exp (2 * (𝒯.kScale i : ℝ) * 𝒯.tScale i) =
          (32 / 3 : ℝ) * Real.exp (2 * ((𝒯.kScale i : ℝ) * 𝒯.tScale i)) := by
            congr 1
            ring
      _ ≤
          Real.exp (8 * ((𝒯.kScale i : ℝ) * 𝒯.tScale i)) *
            Real.exp (2 * ((𝒯.kScale i : ℝ) * 𝒯.tScale i)) :=
        mul_le_mul_of_nonneg_right hExpLarge
          (Real.exp_nonneg (2 * ((𝒯.kScale i : ℝ) * 𝒯.tScale i)))
      _ = Real.exp (10 * (𝒯.kScale i : ℝ) * 𝒯.tScale i) := by
        rw [← Real.exp_add]
        congr 1
        ring
  exact ⟨hh0, Nat.succ_le_iff.mp hnk, hMpos, haSmall, hsmallBudget,
    hprior, hpost, htruncation, hpretrimGoal, hcap⟩
set_option maxHeartbeats 200000

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

set_option maxHeartbeats 5000000
/-- P14.1a: projection geometry, including the partition of odd roles and
the no-singleton incidence bound needed by the posterior calculation. -/
theorem projection_geometry (κ : CConsts) (hκ : κ.Admissible)
    {T : Stage} {k : ℕ} (𝒯 : Tiling κ T k) (h𝒯 : Tiling.Valid 𝒯)
    (hcluster : 𝒯.mode.isCluster) (i : Fin 𝒯.m) :
    Nonempty (ProjectionGeometry κ 𝒯 i) := by
  classical
  have hmode : 𝒯.mode = .lowCluster ∨ 𝒯.mode = .highSmall ∨
      𝒯.mode = .highLarge := by
    cases hm : 𝒯.mode <;> simp [Mode.isCluster, hm] at hcluster ⊢
  rcases h𝒯.cluster_data hmode i with
    ⟨hscale, hgq, _, _, _, _, hdyadic, hExpLo, hExpHi, _, _, _⟩
  let h := (𝒯.P i).h
  let m := Nat.log2 h
  have hh : h = 2 ^ m := hdyadic
  have hCbPos : 0 < κ.Cb := by
    have hr : 0 < 100 * κ.aC / κ.aB :=
      div_pos (mul_pos (by norm_num) hκ.aC_rng.1) hκ.aB_rng.1
    nlinarith [hκ.Cb_big]
  have hMloPosR : 0 < (κ.Mlo : ℝ) := by nlinarith [hκ.Mlo_big, hCbPos]
  have hMloNat : 0 < κ.Mlo := by exact_mod_cast hMloPosR
  have hMhiPosR : 0 < (κ.Mhi : ℝ) := by
    have hcq : 0 < 10 / κ.cq := div_pos (by norm_num) hκ.cq_rng.1
    nlinarith [hκ.Mhi_big.1, hMloPosR, hcq]
  have hM1Pos : 0 < κ.M1 := by linarith [hκ.M1_big.1]
  have hPPos : 0 < κ.P := by
    have hP := hκ.P_big.2
    rw [hκ.Ac_eq] at hP
    omega
  have hRPos : 0 < κ.R := by rw [hκ.R_eq]; positivity
  have hLPos : 0 < κ.L := by rw [hκ.L_eq]; positivity
  have huPosNat : 0 < κ.u := by
    have hu := hκ.u_rng.2
    nlinarith
  have huPos : 0 < (κ.u : ℝ) := by exact_mod_cast huPosNat
  have hpowNeg : Real.rpow 2 (-(10 * (κ.u : ℝ) + 100)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by
      have : 0 ≤ (κ.u : ℝ) := Nat.cast_nonneg _
      nlinarith)
  have hAlpha : κ.α < 1 / 100 := by
    have ha := hκ.α_rng.2
    norm_num at ha ⊢
    exact ha
  have hxiSmall : κ.ξ < 1 / 100 := by
    calc
      κ.ξ < κ.α * Real.rpow 2 (-(10 * (κ.u : ℝ) + 100)) := hκ.ξ_rng.2
      _ ≤ κ.α := by nlinarith [hκ.α_rng.1, hpowNeg]
      _ < 1 / 100 := hAlpha
  have hden : (3 : ℝ) ≤ 3 * (4 : ℝ) ^ (κ.u + 3 : ℕ) := by
    have hp : 1 ≤ (4 : ℝ) ^ (κ.u + 3 : ℕ) := one_le_pow₀ (by norm_num)
    nlinarith
  have hθSmall : κ.θ < 1 := by
    have hfrac : κ.ξ ^ 2 / (3 * (4 : ℝ) ^ (κ.u + 3 : ℕ)) ≤ κ.ξ ^ 2 / 3 :=
      div_le_div_of_nonneg_left (sq_nonneg κ.ξ) (by norm_num) hden
    have hθ := lt_of_lt_of_le hκ.θ_rng.2 hfrac
    have hxiSq : κ.ξ ^ 2 < 1 := by nlinarith [hκ.ξ_rng.1, hxiSmall]
    nlinarith [hxiSq]
  have haLeOne : κ.a ≤ 1 := by rw [hκ.a_eq]; nlinarith [hθSmall]
  have hqNatPos : 0 < (𝒯.P i).q := by
    by_contra hq
    have hq0 : (𝒯.P i).q = 0 := Nat.eq_zero_of_not_pos hq
    have hqR : ((𝒯.P i).q : ℝ) = 0 := by exact_mod_cast hq0
    have hexpPos : 0 < (if 𝒯.mode = .lowCluster then (κ.Mlo : ℝ) else (κ.Mhi : ℝ)) := by
      split_ifs <;> positivity
    have hexpZero : Real.rpow ((𝒯.P i).q : ℝ)
        (if 𝒯.mode = .lowCluster then (κ.Mlo : ℝ) else (κ.Mhi : ℝ)) = 0 := by
      rw [hqR]
      exact Real.zero_rpow (ne_of_gt hexpPos)
    rw [hexpZero] at hExpHi
    norm_num at hExpHi
    exact (not_lt_of_ge (Nat.cast_nonneg (𝒯.P i).h)) hExpHi
  have hqOne : 1 ≤ ((𝒯.P i).q : ℝ) := by
    exact_mod_cast (Nat.succ_le_of_lt hqNatPos)
  have hmax : max (↑(𝒯.P i).g : ℝ) (↑(𝒯.P i).q : ℝ) ≤
      κ.M1 * (↑(𝒯.P i).q : ℝ) := by
    apply max_le
    · exact hgq
    · nlinarith [hκ.M1_big.1, hqOne]
  have hqQ0 : κ.Q0 ≤ (𝒯.P i).q := by
    have hmul : κ.M1 * κ.Q0 ≤ κ.M1 * (↑(𝒯.P i).q : ℝ) :=
      le_trans hscale (by simpa using hmax)
    exact (mul_le_mul_iff_of_pos_left hM1Pos).mp hmul
  have hQ0 := hκ.Q0_large (↑(𝒯.P i).q : ℝ) hqQ0
  unfold QCond at hQ0
  rcases hQ0 with ⟨_, hQsecond, _, _, _, _, _, _, _⟩
  have haPos : 0 < κ.a := by rw [hκ.a_eq]; exact div_pos hκ.θ_rng.1 (by norm_num)
  have hqGtOne : 1 < ((𝒯.P i).q : ℝ) := by
    by_contra hq
    have hqLeOne : ((𝒯.P i).q : ℝ) ≤ 1 := le_of_not_gt hq
    have hpowLe : Real.rpow ((𝒯.P i).q : ℝ) (κ.Mlo : ℝ) ≤ 1 :=
      Real.rpow_le_one (Nat.cast_nonneg _) hqLeOne (by exact_mod_cast Nat.zero_le κ.Mlo)
    have haDiv : 0 ≤ κ.a / 10 ^ 6 ∧ κ.a / 10 ^ 6 ≤ 1 := by
      constructor
      · positivity
      · rw [div_le_iff₀ (by positivity)]
        nlinarith [haLeOne]
    have huOne : 1 ≤ (κ.u : ℝ) := by exact_mod_cast (Nat.succ_le_of_lt huPosNat)
    have hdenOne : 1 ≤ 1000 * (κ.u : ℝ) := by nlinarith
    have hprod : (κ.a / 10 ^ 6) *
        Real.rpow ((𝒯.P i).q : ℝ) κ.Mlo ≤ 1 := by
      calc
        _ ≤ 1 * Real.rpow ((𝒯.P i).q : ℝ) κ.Mlo :=
          mul_le_mul_of_nonneg_right haDiv.2 (Real.rpow_nonneg (Nat.cast_nonneg _) _)
        _ ≤ 1 * 1 := mul_le_mul_of_nonneg_left hpowLe (by norm_num)
        _ = 1 := by ring
    have hfactor : (κ.a / 10 ^ 6) *
        Real.rpow ((𝒯.P i).q : ℝ) κ.Mlo / (1000 * κ.u) ≤ 1 := by
      apply (div_le_iff₀ (by positivity)).2
      nlinarith [hprod, hdenOne]
    have hpowNonneg : 0 ≤ Real.rpow ((𝒯.P i).q : ℝ) κ.aC :=
      Real.rpow_nonneg (Nat.cast_nonneg _) _
    nlinarith [hQsecond, hfactor, hpowNonneg]
  have hqNatTwo : 2 ≤ (𝒯.P i).q := by exact_mod_cast hqGtOne
  have hqPowTwo : (2 : ℝ) ≤ Real.rpow ((𝒯.P i).q : ℝ) (κ.Mlo : ℝ) := by
    have hbase : (2 : ℝ) ≤ (𝒯.P i).q := by exact_mod_cast hqNatTwo
    have hexp : (1 : ℝ) ≤ (κ.Mlo : ℝ) := by exact_mod_cast (Nat.succ_le_of_lt hMloNat)
    calc
      (2 : ℝ) = Real.rpow 2 1 := (Real.rpow_one 2).symm
      _ ≤ Real.rpow ((𝒯.P i).q : ℝ) 1 :=
        Real.rpow_le_rpow (by norm_num) hbase (by norm_num)
      _ ≤ Real.rpow ((𝒯.P i).q : ℝ) (κ.Mlo : ℝ) :=
        Real.rpow_le_rpow_of_exponent_le hqOne hexp
  have hMloLeMhi : (κ.Mlo : ℝ) ≤ (κ.Mhi : ℝ) := by
    have hcqPos : 0 < κ.cq := hκ.cq_rng.1
    have hdiv : 0 < 10 / κ.cq := div_pos (by norm_num) hcqPos
    nlinarith [hκ.Mhi_big.1, hdiv]
  have hExpLoMlo : Real.rpow ((𝒯.P i).q : ℝ) (κ.Mlo : ℝ) ≤ (𝒯.P i).h := by
    have hexpLo : (κ.Mlo : ℝ) ≤
        (if 𝒯.mode = .lowCluster then (κ.Mlo : ℝ) else (κ.Mhi : ℝ)) := by
      split_ifs <;> nlinarith [hMloLeMhi]
    exact (Real.rpow_le_rpow_of_exponent_le hqOne hexpLo).trans hExpLo
  have hhTwoR : (2 : ℝ) ≤ (h : ℝ) := le_trans hqPowTwo hExpLoMlo
  have hhTwo : 2 ≤ h := by exact_mod_cast hhTwoR
  let G := Fin m → ZMod 2
  let e : Fin h ≃ G := HypercubeRamsey.S14.Geometry_q_s14_geom.coordEquiv hh
  let word : (Fin h → Bool) → G → Bool :=
    HypercubeRamsey.S14.Geometry_q_s14_geom.coordWord hh
  let idx : (Fin h → Bool) → Fin h :=
    HypercubeRamsey.S14.Geometry_q_s14_geom.syndromeIndex hh
  let project : (Fin h → Bool) → Fin h → Bool := fun z l =>
    HypercubeRamsey.S10.chunkProject (word z) (e l)
  have h₂ : ∀ g : G, g + g = 0 := by
    intro g
    funext j
    exact ZModModule.add_self (g j)
  have hP10 := HypercubeRamsey.S10.p10_1a_hamming_projection h₂
  rcases hP10 with ⟨hP10zero, hP10fiber⟩
  have hindexCoord (z : Fin h → Bool) : e (idx z) =
      HypercubeRamsey.S10.chunkSyndrome (word z) := by
    exact e.apply_symm_apply _
  have hwordEval : ∀ z l, word z (e l) = z l := by
    intro z l
    change z ((coordEquiv hh).symm (e l)) = z l
    rw [e.symm_apply_apply]
  have hwordProject (z : Fin h → Bool) :
      word (project z) = HypercubeRamsey.S10.chunkProject (word z) := by
    funext g
    change project z ((coordEquiv hh).symm g) =
      HypercubeRamsey.S10.chunkProject (word z) g
    dsimp [project]
    rw [e.apply_symm_apply]
  have hprojectEq : ∀ z, project z = flipPos z (idx z) := by
    intro z
    funext l
    change HypercubeRamsey.S10.chunkProject (word z) (e l) =
      Function.update z (idx z) (!z (idx z)) l
    change (if e l = HypercubeRamsey.S10.chunkSyndrome (word z) then
        !word z (e l) else word z (e l)) =
      Function.update z (idx z) (!z (idx z)) l
    rw [Function.update_apply]
    by_cases hl : l = idx z
    · subst l
      have heq := hindexCoord z
      rw [if_pos heq, if_pos rfl]
      exact congrArg Bool.not (hwordEval z (idx z))
    · have he : e l ≠ HypercubeRamsey.S10.chunkSyndrome (word z) := by
        intro he
        apply hl
        apply e.injective
        exact he.trans (hindexCoord z).symm
      rw [if_neg he, if_neg hl]
      exact hwordEval z l
  have hprojectZero : ∀ z, wordSyndrome (project z) = 0 := by
    intro z
    have hwp : coordWord hh (project z) =
        HypercubeRamsey.S10.chunkProject (coordWord hh z) := by
      simpa [word] using hwordProject z
    have hchunk : HypercubeRamsey.S10.chunkSyndrome (coordWord hh (project z)) = 0 := by
      rw [hwp]
      simpa [word] using (hP10zero (word z)).1
    exact (HypercubeRamsey.S14.Geometry_q_s14_geom.chunk_zero_iff_word_zero hh _).1 hchunk
  let zeroWord : Fin h → Bool := fun _ => false
  have hzeroEven : IsEvenRole zeroWord := by simp [IsEvenRole, zeroWord]
  have hzeroSyndrome : wordSyndrome zeroWord = 0 := by
    funext j
    simp [wordSyndrome, zeroWord]
  let zeroGroup : Group 𝒯 i := ⟨zeroWord, hzeroEven, hzeroSyndrome⟩
  have hprojectEven : ∀ z, ¬ IsEvenRole z → IsEvenRole (project z) := by
    intro z hz
    rw [hprojectEq z]
    exact (HypercubeRamsey.S15.evenRole_flipPos z (idx z)).2 hz
  let groupOf : (Fin h → Bool) → Group 𝒯 i := fun z =>
    if hz : ¬ IsEvenRole z then
      ⟨project z, hprojectEven z hz, hprojectZero z⟩
    else zeroGroup
  have hgroupOfVal : ∀ z, ¬ IsEvenRole z → (groupOf z).1 = project z := by
    intro z hz
    simp [groupOf, hz]
  have hflipInv : ∀ (z : Fin h → Bool) (l : Fin h),
      flipPos (flipPos z l) l = z := by
    intro z l
    funext j
    by_cases hj : j = l <;> simp [flipPos, hj]
  have hgroupOfSpec : ∀ z, ¬ IsEvenRole z → z ∈ groupFiber (groupOf z) := by
    intro z hz
    unfold groupFiber
    simp only [hgroupOfVal z hz]
    refine Finset.mem_image.mpr ⟨idx z, Finset.mem_univ _, ?_⟩
    rw [hprojectEq z]
    exact hflipInv z (idx z)
  have hfiberProject : ∀ z (g : Group 𝒯 i), z ∈ groupFiber g → project z = g.1 := by
    intro z g hmem
    rcases Finset.mem_image.mp hmem with ⟨l, _, hfl⟩
    have hgzero := (HypercubeRamsey.S14.Geometry_q_s14_geom.chunk_zero_iff_word_zero hh g.1).2 g.2.2
    have hgzero' : HypercubeRamsey.S10.chunkSyndrome (word g.1) = 0 := by
      change HypercubeRamsey.S10.chunkSyndrome (coordWord hh g.1) = 0
      exact hgzero
    have hzword : word z = HypercubeRamsey.S10.flipChunkBit (word g.1) (e l) := by
      rw [← hfl]
      exact HypercubeRamsey.S14.Geometry_q_s14_geom.coordWord_flip hh g.1 l
    have hsyn : HypercubeRamsey.S10.chunkSyndrome (word z) = e l := by
      rw [hzword, HypercubeRamsey.S14.Geometry_q_s14_geom.chunkSyndrome_flipChunkBit h₂]
      rw [hgzero']
      simp
    have hsyn' : HypercubeRamsey.S10.chunkSyndrome
        (HypercubeRamsey.S10.flipChunkBit (word g.1) (e l)) = e l := by
      rw [← hzword]
      exact hsyn
    have hwords : word (project z) = word g.1 := by
      rw [hwordProject z, hzword, HypercubeRamsey.S10.chunkProject, hsyn']
      funext a
      by_cases ha : a = e l
      · subst a
        simp [HypercubeRamsey.S10.flipChunkBit]
      · simp [HypercubeRamsey.S10.flipChunkBit, ha]
    funext a
    have ha := congrFun hwords (e a)
    change project z ((coordEquiv hh).symm (e a)) =
      g.1 ((coordEquiv hh).symm (e a)) at ha
    rw [e.symm_apply_apply] at ha
    exact ha
  have hfiberIff (z : Fin h → Bool) (hz : ¬ IsEvenRole z) (g : Group 𝒯 i) :
      z ∈ groupFiber g ↔ project z = g.1 := by
    constructor
    · exact hfiberProject z g
    · intro hp
      have heq : groupOf z = g := by
        apply Subtype.ext
        exact (hgroupOfVal z hz).trans hp
      rw [← heq]
      exact hgroupOfSpec z hz
  have hwordNeighbor (v : Fin h → Bool) (l : Fin h) :
      word (project (flipPos v l)) =
        HypercubeRamsey.S10.projectedNeighbor (word v) (e l) := by
    calc
      word (project (flipPos v l)) =
          HypercubeRamsey.S10.chunkProject (word (flipPos v l)) := hwordProject _
      _ = HypercubeRamsey.S10.projectedNeighbor (word v) (e l) := by
        rw [show word (flipPos v l) =
          HypercubeRamsey.S10.flipChunkBit (word v) (e l) by
            simpa [word] using
              HypercubeRamsey.S14.Geometry_q_s14_geom.coordWord_flip hh v l]
        rfl
  have hwordInjective : Function.Injective (word : (Fin h → Bool) → G → Bool) := by
    change Function.Injective (coordWord hh)
    exact (HypercubeRamsey.S14.Geometry_q_s14_geom.wordEquiv hh).injective
  have hgroupPartition : GroupPartition 𝒯 i := by
    intro z hz
    refine ⟨groupOf z, hgroupOfSpec z hz, ?_⟩
    intro g hmem
    apply Subtype.ext
    exact ((hgroupOfVal z hz).trans (hfiberProject z g hmem)).symm
  let multiplicity : EvenRole 𝒯 i → Group 𝒯 i → ℕ := fun v g =>
    (Finset.univ.filter fun l : Fin h => flipPos v.1 l ∈ groupFiber g).card
  have hflipOdd (v : EvenRole 𝒯 i) (l : Fin h) :
      ¬ IsEvenRole (flipPos v.1 l) := by
    intro hv
    exact (HypercubeRamsey.S15.evenRole_flipPos v.1 l).mp hv v.2
  have hGcard : Fintype.card G = h := by
    dsimp [G]
    simp [Fintype.card_fun, hh]
  have hmultP10 (v : EvenRole 𝒯 i) (g : Group 𝒯 i) :
      multiplicity v g = HypercubeRamsey.S10.projectedNeighborMultiplicity
        (word v.1) (word g.1) := by
    unfold multiplicity HypercubeRamsey.S10.projectedNeighborMultiplicity
      HypercubeRamsey.S10.projectedNeighborFiber
    apply Finset.card_bij (fun l _ => e l)
    · intro l hl
      apply Finset.mem_filter.mpr
      constructor
      · exact Finset.mem_univ _
      · have hmem := (Finset.mem_filter.mp hl).2
        have hproj := (hfiberIff (flipPos v.1 l) (hflipOdd v l) g).1 hmem
        have hword := congrArg word hproj
        exact (hwordNeighbor v.1 l).symm.trans hword
    · intro l hl l' hl' heq
      exact e.injective heq
    · intro b hb
      refine ⟨e.symm b, ?_, e.apply_symm_apply b⟩
      apply Finset.mem_filter.mpr
      constructor
      · exact Finset.mem_univ _
      · have htarget := (Finset.mem_filter.mp hb).2
        have hneigh := hwordNeighbor v.1 (e.symm b)
        have hword : word (project (flipPos v.1 (e.symm b))) = word g.1 := by
          calc
            word (project (flipPos v.1 (e.symm b))) =
                HypercubeRamsey.S10.projectedNeighbor (word v.1) (e (e.symm b)) := hneigh
            _ = word g.1 := by rw [e.apply_symm_apply]; exact htarget
        exact (hfiberIff _ (hflipOdd v (e.symm b)) g).2 (hwordInjective hword)
  have hmultLower (v : EvenRole 𝒯 i) (g : Group 𝒯 i)
      (hpos : 0 < multiplicity v g) : 2 ≤ multiplicity v g := by
    rw [hmultP10] at hpos ⊢
    have hcases := HypercubeRamsey.S10.p10_1a_neighbour_multiplicities h₂
      (word v.1) (word g.1)
    rcases hcases with hzero | hzero | hdouble
    · rw [hzero] at hpos
      omega
    · rw [hzero.2]
      rw [hGcard]
      exact hhTwo
    · exact Nat.le_of_eq hdouble.2.symm
  let coordsFor : EvenRole 𝒯 i → Group 𝒯 i → Finset (Fin h) := fun v g =>
    Finset.univ.filter fun l : Fin h => flipPos v.1 l ∈ groupFiber g
  have hcoordsPairwise (v : EvenRole 𝒯 i) :
      (↑(Finset.univ : Finset (Group 𝒯 i)) : Set (Group 𝒯 i)).PairwiseDisjoint
        (coordsFor v) := by
    intro g hg g' hg' hne
    apply Finset.disjoint_left.mpr
    intro l hl hl'
    have hz := hflipOdd v l
    have hmem : flipPos v.1 l ∈ groupFiber g := (Finset.mem_filter.mp hl).2
    have hmem' : flipPos v.1 l ∈ groupFiber g' := (Finset.mem_filter.mp hl').2
    obtain ⟨g₀, hg₀, huniq⟩ := hgroupPartition (flipPos v.1 l) hz
    have heq := huniq g hmem
    have heq' := huniq g' hmem'
    exact hne (heq.trans heq'.symm)
  have hcoordsUnion (v : EvenRole 𝒯 i) :
      (Finset.univ.biUnion (coordsFor v)) = (Finset.univ : Finset (Fin h)) := by
    apply Finset.Subset.antisymm
    · intro l hl
      exact Finset.mem_univ _
    · intro l hl
      have hz := hflipOdd v l
      obtain ⟨g, hg, _⟩ := hgroupPartition (flipPos v.1 l) hz
      have hcoord : l ∈ coordsFor v g := by
        dsimp [coordsFor]
        exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, hg⟩
      exact Finset.mem_biUnion.mpr ⟨g, Finset.mem_univ _, hcoord⟩
  have hmultSum (v : EvenRole 𝒯 i) : ∑ g, multiplicity v g = h := by
    calc
      (∑ g, multiplicity v g) = ∑ g, (coordsFor v g).card := by rfl
      _ = (Finset.univ.biUnion (coordsFor v)).card :=
        (Finset.card_biUnion (hcoordsPairwise v)).symm
      _ = h := by rw [hcoordsUnion v]; simp
  have hneighborhoodSpec (g : Group 𝒯 i) (v : EvenRole 𝒯 i) :
      v ∈ groupNeighborhood g ↔ ∃ l : Fin h, flipPos v.1 l ∈ groupFiber g := by
    unfold groupNeighborhood
    simp
    rfl
  have hcenterDist (g : Group 𝒯 i) (v : EvenRole 𝒯 i)
      (hv : v ∈ groupNeighborhood g) : hammingDist v.1 g.1 ≤ 2 := by
    rcases hneighborhoodSpec g v |>.1 hv with ⟨l, hl⟩
    rcases Finset.mem_image.mp hl with ⟨l', _, hfl⟩
    have hdistV := HypercubeRamsey.S14.Geometry_q_s14_geom.hammingDist_flipPos v.1 l
    have hdistG : hammingDist (flipPos v.1 l) g.1 = 1 := by
      calc
        hammingDist (flipPos v.1 l) g.1 = hammingDist (flipPos g.1 l') g.1 := by rw [← hfl]
        _ = hammingDist g.1 (flipPos g.1 l') := hammingDist_comm _ _
        _ = 1 := HypercubeRamsey.S14.Geometry_q_s14_geom.hammingDist_flipPos g.1 l'
    calc
      hammingDist v.1 g.1 ≤ hammingDist v.1 (flipPos v.1 l) +
          hammingDist (flipPos v.1 l) g.1 := hammingDist_triangle _ _ _
      _ = 1 + 1 := by rw [hdistV, hdistG]
      _ ≤ 2 := by omega
  have hprojectDistOne (v : EvenRole 𝒯 i) :
      hammingDist (project v.1) v.1 = 1 := by
    rw [hprojectEq, hammingDist_comm]
    exact HypercubeRamsey.S14.Geometry_q_s14_geom.hammingDist_flipPos v.1 (idx v.1)
  let groupsAt : EvenRole 𝒯 i → Finset (Group 𝒯 i) := fun v =>
    Finset.univ.filter fun g : Group 𝒯 i => v ∈ groupNeighborhood g
  have hgroupsAtCard (v : EvenRole 𝒯 i) :
      (Finset.univ.filter fun g : Group 𝒯 i => v ∈ groupNeighborhood g).card ≤ h := by
    have hcard : (groupsAt v).card ≤ ∑ g, multiplicity v g := by
      calc
        (groupsAt v).card = ∑ g ∈ groupsAt v, 1 := by simp
        _ ≤ ∑ g ∈ groupsAt v, multiplicity v g := by
          apply Finset.sum_le_sum
          intro g hg
          obtain ⟨l, hl⟩ := hneighborhoodSpec g v |>.1 (Finset.mem_filter.mp hg).2
          have hp : 0 < multiplicity v g :=
            Finset.card_pos.mpr ⟨l, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hl⟩⟩
          exact le_trans (by norm_num : 1 ≤ 2) (hmultLower v g hp)
        _ ≤ ∑ g, multiplicity v g := by
          exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _) (by
            intro g hgU hgNot
            exact Nat.zero_le _)
    exact hcard.trans (by rw [hmultSum v])
  let allPreimage : (Fin h → Bool) → Finset (Fin h → Bool) := fun x =>
    Finset.univ.filter fun z => project z = x
  have hAllPreimageCard (x : Fin h → Bool) : (allPreimage x).card ≤ h := by
    by_cases hx : wordSyndrome x = 0
    · have hchunk : HypercubeRamsey.S10.chunkSyndrome (word x) = 0 :=
        (HypercubeRamsey.S14.Geometry_q_s14_geom.chunk_zero_iff_word_zero hh x).2 hx
      have hcardEq : (allPreimage x).card =
          (Finset.univ.filter fun s : G → Bool =>
            HypercubeRamsey.S10.chunkProject s = word x).card := by
        unfold allPreimage
        apply Finset.card_bij (fun z _ => word z)
        · intro z hz
          apply Finset.mem_filter.mpr
          constructor
          · exact Finset.mem_univ _
          · have hzproj := (Finset.mem_filter.mp hz).2
            calc
              HypercubeRamsey.S10.chunkProject (word z) = word (project z) :=
                (hwordProject z).symm
              _ = word x := congrArg word hzproj
        · intro z hz z' hz' heq
          exact hwordInjective heq
        · intro s hs
          let z : Fin h → Bool :=
            (HypercubeRamsey.S14.Geometry_q_s14_geom.wordEquiv hh).symm s
          have hzword : word z = s := by
            change coordWord hh
              ((HypercubeRamsey.S14.Geometry_q_s14_geom.wordEquiv hh).symm s) = s
            exact (HypercubeRamsey.S14.Geometry_q_s14_geom.wordEquiv hh).apply_symm_apply s
          refine ⟨z, ?_, hzword⟩
          apply Finset.mem_filter.mpr
          constructor
          · exact Finset.mem_univ _
          · have htarget := (Finset.mem_filter.mp hs).2
            have hwp : word (project z) = word x := by
              calc
                word (project z) = HypercubeRamsey.S10.chunkProject (word z) := hwordProject z
                _ = HypercubeRamsey.S10.chunkProject s := by rw [hzword]
                _ = word x := htarget
            exact hwordInjective hwp
      rw [hcardEq, hP10fiber (word x) hchunk, hGcard]
    · have hempty : allPreimage x = ∅ := by
        apply Finset.eq_empty_iff_forall_notMem.mpr
        intro z hz
        have hzproj := (Finset.mem_filter.mp hz).2
        have hchunk : HypercubeRamsey.S10.chunkSyndrome (word x) = 0 := by
          have hchunk' : HypercubeRamsey.S10.chunkSyndrome (word (project z)) = 0 := by
            rw [hwordProject z]
            exact (hP10zero (word z)).1
          rw [congrArg word hzproj] at hchunk'
          exact hchunk'
        exact hx ((HypercubeRamsey.S14.Geometry_q_s14_geom.chunk_zero_iff_word_zero hh x).1 hchunk)
      simp [allPreimage, hempty]
  let evenPreimage : (Fin h → Bool) → Finset (EvenRole 𝒯 i) := fun x =>
    Finset.univ.filter fun v => project v.1 = x
  let evenUnderlying : EvenRole 𝒯 i ↪ (Fin h → Bool) :=
    ⟨fun v => v.1, by intro v v' h; exact Subtype.ext h⟩
  have hEvenPreimageCard (x : Fin h → Bool) : (evenPreimage x).card ≤ h := by
    have hsubset : (evenPreimage x).map evenUnderlying ⊆ allPreimage x := by
      intro z hz
      rcases Finset.mem_map.mp hz with ⟨v, hv, rfl⟩
      exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, (Finset.mem_filter.mp hv).2⟩
    calc
      (evenPreimage x).card = ((evenPreimage x).map evenUnderlying).card := by simp
      _ ≤ (allPreimage x).card := Finset.card_le_card hsubset
      _ ≤ h := hAllPreimageCard x
  have hbiUnionCard (s : Finset (EvenRole 𝒯 i)) :
      (s.biUnion groupsAt).card ≤ ∑ v ∈ s, (groupsAt v).card := by
    classical
    induction s using Finset.induction_on with
    | empty => simp
    | @insert v s hv ih =>
        simp only [Finset.biUnion_insert]
        calc
          (groupsAt v ∪ s.biUnion groupsAt).card ≤
              (groupsAt v).card + (s.biUnion groupsAt).card := Finset.card_union_le _ _
          _ ≤ (groupsAt v).card + ∑ w ∈ s, (groupsAt w).card := by omega
          _ = ∑ w ∈ insert v s, (groupsAt w).card := by simp [hv]
  have hRealHcube : (h : ℝ) ≤ (h : ℝ) ^ 3 := by
    have hOne : 1 ≤ (h : ℝ) := by exact_mod_cast (show 1 ≤ h by omega)
    have hsq : 1 ≤ (h : ℝ) ^ 2 := one_le_pow₀ hOne
    calc
      (h : ℝ) = (h : ℝ) * 1 := by ring
      _ ≤ (h : ℝ) * (h : ℝ) ^ 2 :=
        mul_le_mul_of_nonneg_left hsq (by positivity)
      _ = (h : ℝ) ^ 3 := by ring
  have hRealSquareCube : (h : ℝ) ^ 2 ≤ (h : ℝ) ^ 3 := by
    have hOne : 1 ≤ (h : ℝ) := by exact_mod_cast (show 1 ≤ h by omega)
    calc
      (h : ℝ) ^ 2 = (h : ℝ) ^ 2 * 1 := by ring
      _ ≤ (h : ℝ) ^ 2 * (h : ℝ) :=
        mul_le_mul_of_nonneg_left hOne (sq_nonneg (h : ℝ))
      _ = (h : ℝ) ^ 3 := by ring
  have hProjectedGroupsCard (x : Fin h → Bool) :
      ((Finset.univ.filter fun g : Group 𝒯 i =>
        ∃ v ∈ groupNeighborhood g, project v.1 = x).card : ℕ) ≤ h * h := by
    let projectedGroups : Finset (Group 𝒯 i) := Finset.univ.filter fun g =>
      ∃ v ∈ groupNeighborhood g, project v.1 = x
    have hsubset : projectedGroups ⊆ (evenPreimage x).biUnion groupsAt := by
      intro g hg
      rcases (Finset.mem_filter.mp hg).2 with ⟨v, hv, hx⟩
      have hvpre : v ∈ evenPreimage x := Finset.mem_filter.mpr ⟨Finset.mem_univ _, hx⟩
      have hgin : g ∈ groupsAt v := Finset.mem_filter.mpr ⟨Finset.mem_univ _, hv⟩
      exact Finset.mem_biUnion.mpr ⟨v, hvpre, hgin⟩
    have hsumAt : ∑ v ∈ evenPreimage x, (groupsAt v).card ≤
        ∑ v ∈ evenPreimage x, h := by
      apply Finset.sum_le_sum
      intro v hv
      exact hgroupsAtCard v
    calc
      projectedGroups.card ≤ ((evenPreimage x).biUnion groupsAt).card :=
        Finset.card_le_card hsubset
      _ ≤ ∑ v ∈ evenPreimage x, (groupsAt v).card := hbiUnionCard (evenPreimage x)
      _ ≤ ∑ v ∈ evenPreimage x, h := hsumAt
      _ = (evenPreimage x).card * h := by
        simp [Finset.sum_const, nsmul_eq_mul]
      _ ≤ h * h := Nat.mul_le_mul_right h (hEvenPreimageCard x)
  refine ⟨{
    syndromeIndex := idx
    syndromeIndex_spec := HypercubeRamsey.S14.Geometry_q_s14_geom.syndromeIndex_spec hh
    project := project
    project_eq := hprojectEq
    project_zero := hprojectZero
    groupOf := groupOf
    groupOf_spec := hgroupOfSpec
    partition := hgroupPartition
    fiber_card := by
      intro g
      have hinj : Set.InjOn (flipPos g.1)
          (↑(Finset.univ : Finset (Fin h)) : Set (Fin h)) := by
        intro l hl l' hl' heq
        by_contra hne
        have hval := congrFun heq l
        simp [flipPos, hne] at hval
      change (Finset.univ.image (flipPos g.1)).card = h
      rw [Finset.card_image_of_injOn hinj]
      exact Finset.card_fin h
    multiplicity := multiplicity
    multiplicity_eq := by intro v g; rfl
    multiplicity_lower := hmultLower
    multiplicity_sum := hmultSum
    neighborhood_distance := by
      intro g v v' hv hv'
      have hvg := hcenterDist g v hv
      have hgv' : hammingDist g.1 v'.1 ≤ 2 := by
        simpa [hammingDist_comm] using hcenterDist g v' hv'
      calc
        hammingDist v.1 v'.1 ≤ hammingDist v.1 g.1 + hammingDist g.1 v'.1 :=
          hammingDist_triangle _ _ _
        _ ≤ 2 + 2 := Nat.add_le_add hvg hgv'
        _ ≤ 6 := by omega
    projected_distance := by
      intro g v v' hv hv'
      have hvg := hcenterDist g v hv
      have hgv' : hammingDist g.1 v'.1 ≤ 2 := by
        simpa [hammingDist_comm] using hcenterDist g v' hv'
      have hleft : hammingDist (project v.1) g.1 ≤ 3 := by
        calc
          hammingDist (project v.1) g.1 ≤
              hammingDist (project v.1) v.1 + hammingDist v.1 g.1 := hammingDist_triangle _ _ _
          _ ≤ 1 + 2 := Nat.add_le_add (le_of_eq (hprojectDistOne v)) hvg
          _ ≤ 3 := by omega
      have hright : hammingDist g.1 (project v'.1) ≤ 3 := by
        have hlast : hammingDist v'.1 (project v'.1) = 1 := by
          simpa [hammingDist_comm] using hprojectDistOne v'
        calc
          hammingDist g.1 (project v'.1) ≤
              hammingDist g.1 v'.1 + hammingDist v'.1 (project v'.1) := hammingDist_triangle _ _ _
          _ ≤ 2 + 1 := Nat.add_le_add hgv' (by omega)
          _ ≤ 3 := by omega
      calc
        hammingDist (project v.1) (project v'.1) ≤
            hammingDist (project v.1) g.1 + hammingDist g.1 (project v'.1) :=
          hammingDist_triangle _ _ _
        _ ≤ 3 + 3 := Nat.add_le_add hleft hright
        _ ≤ 6 := by omega
    projected_overlap := by
      intro x
      calc
        ((Finset.univ.filter fun g : Group 𝒯 i =>
          ∃ v ∈ groupNeighborhood g, project v.1 = x).card : ℝ) ≤ (h : ℝ) ^ 2 := by
            have hNat := hProjectedGroupsCard x
            have hCast : ((Finset.univ.filter fun g : Group 𝒯 i =>
                ∃ v ∈ groupNeighborhood g, project v.1 = x).card : ℝ) ≤
                ((h * h : ℕ) : ℝ) := by exact_mod_cast hNat
            simpa [Nat.cast_mul, pow_two] using hCast
        _ ≤ (h : ℝ) ^ 3 := hRealSquareCube
    neighborhood_overlap := by
      intro v
      have hcard := hgroupsAtCard v
      have hcardR : ((Finset.univ.filter fun g : Group 𝒯 i =>
          v ∈ groupNeighborhood g).card : ℝ) ≤ (h : ℝ) := by exact_mod_cast hcard
      have hOne : 1 ≤ (h : ℝ) := by
        exact_mod_cast (show 1 ≤ h by omega)
      have hsq : 1 ≤ (h : ℝ) ^ 2 := one_le_pow₀ hOne
      have hpow : (h : ℝ) ≤ (h : ℝ) ^ 3 := by
        calc
          (h : ℝ) = (h : ℝ) * 1 := by ring
          _ ≤ (h : ℝ) * (h : ℝ) ^ 2 :=
            mul_le_mul_of_nonneg_left hsq (by positivity)
          _ = (h : ℝ) ^ 3 := by ring
      exact hcardR.trans hpow
  }⟩
set_option maxHeartbeats 200000

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

set_option maxHeartbeats 5000000
/-- P14.1b: masks discard at most a tenth of the labels and at most a fifth
of the physical bins. -/
theorem masks_and_price_cut (κ : CConsts) (hκ : κ.Admissible)
    {T : Stage} {k : ℕ} {𝒯 : Tiling κ T k} (h𝒯 : Tiling.Valid 𝒯)
    {i : Fin 𝒯.m} (mesh : Mesh 𝒯) (_hclean : MeshCleaned mesh) (v : mesh.V) :
    Nonempty (MaskFacts i mesh v) := by
  classical
  let price : Fin (T.S.N k) → ℝ := fun y => mesh.paramPrice (mesh.base v) i y
  let cheap : Bin 𝒯 i → Finset (Fin (T.S.N k)) := fun D =>
    D.1.filter fun y => price y ≤ 10 / (𝒯.P i).M
  let retained : Finset (Bin 𝒯 i) :=
    Finset.univ.filter fun D => 2 * (cheap D).card ≥ (𝒯.P i).d
  let prior : Bin 𝒯 i → ℝ := fun D =>
    if D ∈ retained then 1 / (retained.card : ℝ) else 0
  let within : Bin 𝒯 i → Fin (T.S.N k) → ℝ := fun D y =>
    if D ∈ retained then
      if y ∈ cheap D then 1 / ((cheap D).card : ℝ) else 0
    else if y ∈ D.1 then 1 / (D.1.card : ℝ) else 0
  let expensive : Finset (Fin (T.S.N k)) :=
    (𝒯.P i).Y.filter fun y => 10 / (𝒯.P i).M < price y
  have hcheapSubset : ∀ D, cheap D ⊆ D.1 := by
    intro D y hy
    exact (Finset.mem_filter.mp hy).1
  have hMnat : 0 < (𝒯.P i).M := by
    rw [← (𝒯.P i).cardX]
    exact Finset.card_pos.mpr (h𝒯.patch_nonempty i).1
  have hMpos : 0 < ((𝒯.P i).M : ℝ) := by exact_mod_cast hMnat
  have hYne := (h𝒯.patch_nonempty i).2
  obtain ⟨y₀, hy₀⟩ := hYne
  obtain ⟨B₀, hB₀, hyB₀⟩ := (𝒯.P i).bins.exists_mem hy₀
  have hB₀ne := (𝒯.P i).bins.nonempty_of_mem_parts hB₀
  have hdNat : 0 < (𝒯.P i).d := by
    rw [← h𝒯.bins_card i B₀ hB₀]
    exact Finset.card_pos.mpr hB₀ne
  have hdPos : 0 < ((𝒯.P i).d : ℝ) := by exact_mod_cast hdNat
  have hpartsM : (𝒯.P i).bins.parts.card * (𝒯.P i).d = (𝒯.P i).M := by
    calc
      (𝒯.P i).bins.parts.card * (𝒯.P i).d =
          ∑ B ∈ (𝒯.P i).bins.parts, (𝒯.P i).d := by simp
      _ = ∑ B ∈ (𝒯.P i).bins.parts, B.card := by
        apply Finset.sum_congr rfl
        intro B hB
        exact (h𝒯.bins_card i B hB).symm
      _ = (𝒯.P i).Y.card := (𝒯.P i).bins.sum_card_parts
      _ = (𝒯.P i).M := (𝒯.P i).cardY
  have hpriceSimplex := mesh.paramPrice_simplex (mesh.base v) i
  rcases hpriceSimplex with ⟨hpriceNonneg, hpriceSupport, hpriceSum⟩
  have hsumPriceY : ∑ y ∈ (𝒯.P i).Y, price y = 1 := by
    calc
      ∑ y ∈ (𝒯.P i).Y, price y = ∑ y, price y := by
        exact Finset.sum_subset (Finset.subset_univ (𝒯.P i).Y) (by
          intro y hyU hyNot
          exact hpriceSupport y hyNot)
      _ = 1 := by simpa [price] using hpriceSum
  have hexpensiveSubset : expensive ⊆ (𝒯.P i).Y := Finset.filter_subset _ _
  have hexpensiveLower : (expensive.card : ℝ) * (10 / ((𝒯.P i).M : ℝ)) ≤
      ∑ y ∈ expensive, price y := by
    have hconst : ∑ y ∈ expensive, (10 / ((𝒯.P i).M : ℝ)) =
        (expensive.card : ℝ) * (10 / ((𝒯.P i).M : ℝ)) := by
      rw [Finset.sum_const, nsmul_eq_mul]
    calc
      (expensive.card : ℝ) * (10 / (𝒯.P i).M) =
          ∑ y ∈ expensive, (10 / ((𝒯.P i).M : ℝ)) := hconst.symm
      _ ≤ ∑ y ∈ expensive, price y := by
        apply Finset.sum_le_sum
        intro y hy
        exact le_of_lt (Finset.mem_filter.mp hy).2
  have hexpensiveUpper : ∑ y ∈ expensive, price y ≤ 1 := by
    calc
      ∑ y ∈ expensive, price y ≤ ∑ y ∈ (𝒯.P i).Y, price y :=
        Finset.sum_le_sum_of_subset_of_nonneg hexpensiveSubset (by
          intro y hyY hyNot
          exact hpriceNonneg y)
      _ = 1 := hsumPriceY
  have hexpensiveCard : (expensive.card : ℝ) ≤ (𝒯.P i).M / 10 := by
    have hdiv : ((expensive.card : ℝ) * 10) / ((𝒯.P i).M : ℝ) ≤ 1 := by
      calc
        ((expensive.card : ℝ) * 10) / (𝒯.P i).M =
            (expensive.card : ℝ) * (10 / ((𝒯.P i).M : ℝ)) := by ring
        _ ≤ 1 := hexpensiveLower.trans hexpensiveUpper
    have hraw : (expensive.card : ℝ) * 10 ≤ (𝒯.P i).M := by
      have h := (div_le_iff₀ hMpos).1 hdiv
      simpa only [one_mul] using h
    exact (le_div_iff₀ (by norm_num : 0 < (10 : ℝ))).2 hraw
  let expensiveIn : Finset (Fin (T.S.N k)) → Finset (Fin (T.S.N k)) := fun B =>
    B.filter fun y => 10 / (𝒯.P i).M < price y
  let badParts : Finset (Finset (Fin (T.S.N k))) :=
    (𝒯.P i).bins.parts.filter fun B =>
      ((expensiveIn B).card : ℝ) > (𝒯.P i).d / 2
  have hBadPairwise : (badParts : Set (Finset (Fin (T.S.N k)))).PairwiseDisjoint expensiveIn := by
    intro B hB B' hB' hne
    have hBmem : B ∈ (𝒯.P i).bins.parts := (Finset.mem_filter.mp hB).1
    have hB'mem : B' ∈ (𝒯.P i).bins.parts := (Finset.mem_filter.mp hB').1
    have hpartsDisj : Disjoint B B' := (𝒯.P i).bins.disjoint hBmem hB'mem hne
    apply Finset.disjoint_left.mpr
    intro y hy hy'
    have hnot : y ∉ B' :=
      (Finset.disjoint_left.mp hpartsDisj) (Finset.mem_filter.mp hy).1
    exact hnot (Finset.mem_filter.mp hy').1
  have hBadUnionSubset : badParts.biUnion expensiveIn ⊆ expensive := by
    apply Finset.biUnion_subset.2
    intro B hB y hy
    have hBmem : B ∈ (𝒯.P i).bins.parts := (Finset.mem_filter.mp hB).1
    exact Finset.mem_filter.mpr ⟨(𝒯.P i).bins.le hBmem (Finset.mem_filter.mp hy).1,
      (Finset.mem_filter.mp hy).2⟩
  have hBadSumCast :
      (∑ B ∈ badParts, (expensiveIn B).card : ℝ) = (badParts.biUnion expensiveIn).card := by
    calc
      (∑ B ∈ badParts, (expensiveIn B).card : ℝ) =
          ((∑ B ∈ badParts, (expensiveIn B).card : ℕ) : ℝ) := by simp
      _ = (badParts.biUnion expensiveIn).card := by
        exact_mod_cast (Finset.card_biUnion hBadPairwise).symm
  have hBadSumLower : (badParts.card : ℝ) * ((𝒯.P i).d : ℝ) / 2 ≤
      ∑ B ∈ badParts, ((expensiveIn B).card : ℝ) := by
    have hconst : ∑ B ∈ badParts, ((𝒯.P i).d : ℝ) / 2 =
        (badParts.card : ℝ) * ((𝒯.P i).d : ℝ) / 2 := by
      rw [Finset.sum_eq_card_nsmul (fun B hB => rfl), nsmul_eq_mul]
      ring_nf
    rw [← hconst]
    apply Finset.sum_le_sum
    intro B hB
    exact le_of_lt (Finset.mem_filter.mp hB).2
  have hBadSumUpper : (∑ B ∈ badParts, ((expensiveIn B).card : ℝ)) ≤
      (expensive.card : ℝ) := by
    calc
      (∑ B ∈ badParts, (expensiveIn B).card : ℝ) =
          (badParts.biUnion expensiveIn).card := hBadSumCast
      _ ≤ (expensive.card : ℝ) := by exact_mod_cast Finset.card_le_card hBadUnionSubset
  have hPartsMReal : ((𝒯.P i).bins.parts.card : ℝ) * (𝒯.P i).d = (𝒯.P i).M := by
    exact_mod_cast hpartsM
  have hBadCountMul :
      5 * (badParts.card : ℝ) * (𝒯.P i).d ≤
        (𝒯.P i).bins.parts.card * (𝒯.P i).d := by
    have hbound : (badParts.card : ℝ) * (𝒯.P i).d / 2 ≤
        (𝒯.P i).bins.parts.card * (𝒯.P i).d / 10 := by
      calc
        _ ≤ (expensive.card : ℝ) := hBadSumLower.trans hBadSumUpper
        _ ≤ (𝒯.P i).M / 10 := hexpensiveCard
        _ = (𝒯.P i).bins.parts.card * (𝒯.P i).d / 10 := by rw [← hPartsMReal]
    nlinarith only [hbound]
  have hBadCount : 5 * (badParts.card : ℝ) ≤ (𝒯.P i).bins.parts.card := by
    exact (mul_le_mul_iff_of_pos_right hdPos).mp hBadCountMul
  have hExpensiveBins : (badParts.card : ℝ) ≤ (𝒯.P i).bins.parts.card / 5 := by
    have hBadCount' : (badParts.card : ℝ) * 5 ≤ (𝒯.P i).bins.parts.card := by
      simpa [mul_comm] using hBadCount
    exact (le_div_iff₀ (by norm_num : 0 < (5 : ℝ))).2 hBadCount'
  have hsplitCheapExp (D : Bin 𝒯 i) :
      (cheap D).card + (expensiveIn D.1).card = D.1.card := by
    have hfilter := Finset.card_filter_add_card_filter_not
      (s := D.1) (p := fun y => price y ≤ 10 / (𝒯.P i).M)
    have hnot : D.1.filter (fun y => ¬ price y ≤ 10 / (𝒯.P i).M) =
        expensiveIn D.1 := by
      ext y
      simp [expensiveIn, not_le]
    simpa [cheap, hnot] using hfilter
  have hUnretainedBad : ∀ D : Bin 𝒯 i, D ∉ retained → D.1 ∈ badParts := by
    intro D hDnot
    have hcheapFail : 2 * (cheap D).card < (𝒯.P i).d := by
      by_contra h
      apply hDnot
      exact Finset.mem_filter.mpr ⟨Finset.mem_univ D, le_of_not_gt h⟩
    have hsplit := hsplitCheapExp D
    have hBcard := h𝒯.bins_card i D.1 D.2
    have hexpLarge : (𝒯.P i).d < 2 * (expensiveIn D.1).card := by omega
    have hexpLargeR : ((𝒯.P i).d : ℝ) < 2 * (expensiveIn D.1).card := by
      exact_mod_cast hexpLarge
    have hreal : ((𝒯.P i).d : ℝ) / 2 < ((expensiveIn D.1).card : ℝ) := by
      rw [div_lt_iff₀ (by norm_num : 0 < (2 : ℝ))]
      nlinarith only [hexpLargeR]
    exact Finset.mem_filter.mpr ⟨D.2, by simpa only [gt_iff_lt] using hreal⟩
  have hretainedNonempty : retained.Nonempty := by
    by_contra hret
    have hretEmpty : retained = ∅ := Finset.not_nonempty_iff_eq_empty.mp hret
    have hDnot : ∀ D : Bin 𝒯 i, D ∉ retained := by
      intro D hD
      rw [hretEmpty] at hD
      simpa using hD
    have hpartsSub : (𝒯.P i).bins.parts ⊆ badParts := by
      intro B hB
      exact hUnretainedBad ⟨B, hB⟩ (hDnot ⟨B, hB⟩)
    have hbadEq : badParts = (𝒯.P i).bins.parts :=
      Finset.Subset.antisymm (Finset.filter_subset _ _) hpartsSub
    have hpartsPos : 0 < ((𝒯.P i).bins.parts.card : ℝ) := by
      exact_mod_cast (Finset.card_pos.mpr ⟨B₀, hB₀⟩)
    rw [hbadEq] at hExpensiveBins
    nlinarith only [hExpensiveBins, hpartsPos]
  let notRetained : Finset (Bin 𝒯 i) :=
    Finset.univ.filter fun D => ¬ 2 * (cheap D).card ≥ (𝒯.P i).d
  have hsplitRetained : retained.card + notRetained.card = (𝒯.P i).bins.parts.card := by
    have hfilter := Finset.card_filter_add_card_filter_not
      (s := (Finset.univ : Finset (Bin 𝒯 i)))
      (fun D => 2 * (cheap D).card ≥ (𝒯.P i).d)
    calc
      retained.card + notRetained.card = Fintype.card (Bin 𝒯 i) := by
        simpa [retained, notRetained] using hfilter
      _ = (𝒯.P i).bins.parts.card := by
        exact Fintype.subtype_card (𝒯.P i).bins.parts (by intro B; rfl)
  let binUnderlying : Bin 𝒯 i ↪ Finset (Fin (T.S.N k)) :=
    ⟨fun D => D.1, by intro D D' h; exact Subtype.ext h⟩
  have hnotMapSubset : notRetained.map binUnderlying ⊆ badParts := by
    intro B hB
    rcases Finset.mem_map.mp hB with ⟨D, hD, rfl⟩
    have hDnot : D ∉ retained := by
      intro hmem
      exact (Finset.mem_filter.mp hD).2 (Finset.mem_filter.mp hmem).2
    exact hUnretainedBad D hDnot
  have hnotRetainedCard : notRetained.card ≤ badParts.card := by
    calc
      notRetained.card = (notRetained.map binUnderlying).card := by simp
      _ ≤ badParts.card := Finset.card_le_card hnotMapSubset
  have hretainedLower : (4 / 5 : ℝ) * (𝒯.P i).bins.parts.card ≤ retained.card := by
    have hsplitR : (retained.card : ℝ) + notRetained.card =
        (𝒯.P i).bins.parts.card := by exact_mod_cast hsplitRetained
    have hnotR : (notRetained.card : ℝ) ≤ (badParts.card : ℝ) := by exact_mod_cast hnotRetainedCard
    nlinarith only [hsplitR, hnotR, hExpensiveBins]
  have hretainedCardPos : 0 < (retained.card : ℝ) := by
    exact_mod_cast Finset.card_pos.mpr hretainedNonempty
  have hpriorCap : ∀ D, prior D ≤ 2 * (𝒯.P i).d / (𝒯.P i).M := by
    intro D
    by_cases hDret : D ∈ retained
    · have hretScaled := mul_le_mul_of_nonneg_right hretainedLower (le_of_lt hdPos)
      have hnum : (1 : ℝ) * (𝒯.P i).M ≤
          (2 * (𝒯.P i).d) * (retained.card : ℝ) := by
        rw [← hPartsMReal]
        have hpartsPos : 0 <
            ((𝒯.P i).bins.parts.card : ℝ) * (𝒯.P i).d := by
          exact mul_pos (by exact_mod_cast Finset.card_pos.mpr ⟨B₀, hB₀⟩) hdPos
        nlinarith only [hretScaled, hpartsPos]
      simp only [prior, if_pos hDret]
      exact (div_le_div_iff₀ hretainedCardPos hMpos).2 hnum
    · simp [prior, hDret]
      positivity
  have hcheapCardLower : ∀ D, D ∈ retained →
      ((𝒯.P i).d : ℝ) / 2 ≤ ((cheap D).card : ℝ) := by
    intro D hD
    have hret := (Finset.mem_filter.mp hD).2
    have hretRReal : ((𝒯.P i).d : ℝ) ≤ 2 * ((cheap D).card : ℝ) := by
      exact_mod_cast hret
    exact (div_le_iff₀ (by norm_num : 0 < (2 : ℝ))).2 (by nlinarith only [hretRReal])
  have hwithinCap : ∀ D, D ∈ retained → ∀ y,
      within D y ≤ 2 / (𝒯.P i).d := by
    intro D hD y
    by_cases hy : y ∈ cheap D
    · have hcpos : 0 < ((cheap D).card : ℝ) :=
        lt_of_lt_of_le (div_pos hdPos (by norm_num)) (hcheapCardLower D hD)
      have hrecip : 1 / ((cheap D).card : ℝ) ≤ 2 / (𝒯.P i).d := by
        apply (div_le_div_iff₀ hcpos hdPos).2
        nlinarith [hcheapCardLower D hD]
      simpa [within, hD, hy] using hrecip
    · simp only [within, if_pos hD, if_neg hy]
      exact div_nonneg (by norm_num) (le_of_lt hdPos)
  have haggregate : ∀ y,
      ∑ D : Bin 𝒯 i, prior D * within D y ≤ 4 / (𝒯.P i).M := by
    intro y
    by_cases hyY : y ∈ (𝒯.P i).Y
    · obtain ⟨B, hB, hyB⟩ := (𝒯.P i).bins.exists_mem hyY
      let D₀ : Bin 𝒯 i := ⟨B, hB⟩
      have hsum : (∑ D : Bin 𝒯 i, prior D * within D y) =
          prior D₀ * within D₀ y := by
        refine Finset.sum_eq_single D₀ ?_ ?_
        · intro D hD hne
          have hnotD : y ∉ D.1 := by
            intro hyD
            have hneUnderlying : D₀.1 ≠ D.1 := by
              intro heq
              apply hne
              exact Subtype.ext heq.symm
            have hdisj := (𝒯.P i).bins.disjoint D₀.2 D.2 hneUnderlying
            exact (Finset.disjoint_left.mp hdisj) hyB hyD
          have hwithinZero : within D y = 0 := by
            by_cases hDret : D ∈ retained
            · have hyCheap : y ∉ cheap D := by
                intro hyC
                exact hnotD (hcheapSubset D hyC)
              simp [within, hDret, hyCheap]
            · simp [within, hDret, hnotD]
          simp [hwithinZero]
        · intro hD₀
          exact (hD₀ (Finset.mem_univ _)).elim
      rw [hsum]
      by_cases hDret : D₀ ∈ retained
      · have hwithin := hwithinCap D₀ hDret y
        calc
          prior D₀ * within D₀ y ≤
              (2 * (𝒯.P i).d / (𝒯.P i).M) * within D₀ y :=
            mul_le_mul_of_nonneg_right (hpriorCap D₀) (by positivity)
          _ ≤ (2 * (𝒯.P i).d / (𝒯.P i).M) * (2 / (𝒯.P i).d) :=
            mul_le_mul_of_nonneg_left hwithin (by positivity)
          _ = 4 / (𝒯.P i).M := by field_simp <;> ring
      · simp [prior, hDret]
        positivity
    · have hnotD : ∀ D : Bin 𝒯 i, y ∉ D.1 := by
        intro D hyD
        exact hyY ((𝒯.P i).bins.le D.2 hyD)
      calc
        (∑ D : Bin 𝒯 i, prior D * within D y) = 0 := by
          apply Finset.sum_eq_zero
          intro D hD
          by_cases hDret : D ∈ retained
          · have hyCheap : y ∉ cheap D := by
              intro hyC
              exact hnotD D (hcheapSubset D hyC)
            simp [within, hDret, hyCheap]
          · simp [prior, hDret]
        _ ≤ 4 / (𝒯.P i).M := by positivity
  refine ⟨{
    cheap := cheap
    retained := retained
    prior := prior
    within := within
    cheap_eq := by intro D; rfl
    cheap_subset := hcheapSubset
    cheap_nonempty := by
      intro D hD
      have hcard := hcheapCardLower D hD
      have hpos : 0 < ((cheap D).card : ℝ) :=
        lt_of_lt_of_le (div_pos hdPos (by norm_num)) (hcheapCardLower D hD)
      exact Finset.card_pos.mp (by exact_mod_cast hpos)
    retained_nonempty := hretainedNonempty
    cheap_price := by
      intro D y hy
      exact (Finset.mem_filter.mp hy).2
    retained_spec := by intro D; simp [retained]
    prior_nonneg := by
      intro D
      simp only [prior]
      split_ifs <;> positivity
    prior_sum := by
      simp only [prior]
      rw [Finset.sum_ite_mem, Finset.univ_inter, Finset.sum_const, nsmul_eq_mul]
      field_simp
    prior_uniform := by intro D; rfl
    within_nonneg := by
      intro D y
      simp only [within]
      split_ifs <;> positivity
    within_sum := by
      intro D
      by_cases hD : D ∈ retained
      · have hcpos : 0 < (cheap D).card := by
          have hreal : 0 < ((cheap D).card : ℝ) :=
            lt_of_lt_of_le (div_pos hdPos (by norm_num)) (hcheapCardLower D hD)
          exact_mod_cast hreal
        have hcne : ((cheap D).card : ℝ) ≠ 0 := by exact_mod_cast hcpos.ne'
        simp only [within, if_pos hD]
        rw [Finset.sum_ite_mem, Finset.univ_inter, Finset.sum_const, nsmul_eq_mul]
        field_simp
      · have hDcard : (𝒯.P i).d = D.1.card := (h𝒯.bins_card i D.1 D.2).symm
        have hDpos : 0 < D.1.card := by omega
        have hDne : (D.1.card : ℝ) ≠ 0 := by exact_mod_cast hDpos.ne'
        simp only [within, if_neg hD]
        rw [Finset.sum_ite_mem, Finset.univ_inter, Finset.sum_const, nsmul_eq_mul]
        field_simp
    within_support := by
      intro D y h
      by_cases hD : D ∈ retained
      · by_cases hy : y ∈ cheap D
        · exact hcheapSubset D hy
        · simp [within, hD, hy] at h
      · by_cases hy : y ∈ D.1
        · exact hy
        · simp [within, hD, hy] at h
    within_uniform := by intro D y; rfl
    expensive_labels := by simpa [expensive, price] using hexpensiveCard
    expensive_bins := by simpa [badParts, expensiveIn, price] using hExpensiveBins
    prior_cap := hpriorCap
    aggregate_masked_mass := haggregate
    cleaned_codegree := by
      intro hcluster p v' hwt D y y' hy hy'
      have hprops := _hclean v' p i hwt
      exact hprops.codeg hcluster D.1 D.2 y (hcheapSubset D hy)
        y' (hcheapSubset D hy')
  }⟩
set_option maxHeartbeats 200000

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

set_option maxHeartbeats 5000000 in
theorem generic_list_test (κ : CConsts) (hκ : κ.Admissible)
    (T : Stage) (hinit : InitDisc T κ.η0) :
    ∀ᶠ k in atTop, ∀ 𝒯 : Tiling κ T k, Tiling.Valid 𝒯 → ∀ i, GenericListBound κ 𝒯 i := by
  classical
  have hminη : min κ.xs (min κ.η0 0.01) ≤ κ.η0 :=
    le_trans (min_le_right _ _) (min_le_left _ _)
  have hιη : κ.ι < κ.η0 / 1000 := by
    calc
      κ.ι < min κ.xs (min κ.η0 0.01) / 1000 := hκ.ι_rng.2
      _ ≤ κ.η0 / 1000 := by gcongr
  have hαExp : Real.rpow 2 (-(10 * (κ.u : ℝ) + 100)) < 1 :=
    Real.rpow_lt_one_of_one_lt_of_neg one_lt_two (by
      have hu : 0 ≤ (κ.u : ℝ) := Nat.cast_nonneg _
      linarith)
  have hξsmall : κ.ξ < 1 / 100 := by
    calc
      κ.ξ < κ.α * Real.rpow 2 (-(10 * (κ.u : ℝ) + 100)) := hκ.ξ_rng.2
      _ < κ.α := by
        calc
          κ.α * Real.rpow 2 (-(10 * (κ.u : ℝ) + 100)) < κ.α * 1 :=
            mul_lt_mul_of_pos_left hαExp hκ.α_rng.1
          _ = κ.α := by ring
      _ < 1 / 100 := by nlinarith [hκ.α_rng.2]
  have hpow4 : (1 : ℝ) ≤ (4 : ℝ) ^ (κ.u + 3 : ℕ) := one_le_pow₀ (by norm_num)
  have hden4 : (3 : ℝ) ≤ 3 * (4 : ℝ) ^ (κ.u + 3 : ℕ) := by nlinarith
  have hθsmall : κ.θ < (1 / 100 : ℝ) ^ 2 / 3 := by
    calc
      κ.θ < κ.ξ ^ 2 / (3 * 4 ^ (κ.u + 3 : ℕ)) := hκ.θ_rng.2
      _ ≤ κ.ξ ^ 2 / 3 :=
        div_le_div_of_nonneg_left (sq_nonneg κ.ξ) (by norm_num) hden4
      _ ≤ (1 / 100 : ℝ) ^ 2 / 3 := by
        have hξsq : κ.ξ ^ 2 ≤ (1 / 100 : ℝ) ^ 2 := by
          nlinarith [hκ.ξ_rng.1, hξsmall]
        exact div_le_div_of_nonneg_right hξsq (by norm_num)
  have haSmall : κ.a ≤ 1 / 10 := by
    rw [hκ.a_eq]
    nlinarith [hθsmall]
  have hθpos : 0 < κ.θ := hκ.θ_rng.1
  have haPos : 0 < κ.a := by rw [hκ.a_eq]; positivity
  have hMloPosR : 0 < (κ.Mlo : ℝ) := by
    have hfrac : 0 < 100 * κ.aC / κ.aB :=
      div_pos (mul_pos (by norm_num) hκ.aC_rng.1) hκ.aB_rng.1
    have hCb : 0 < κ.Cb := by nlinarith [hκ.Cb_big]
    nlinarith [hκ.Mlo_big]
  have hMhiPosR : 0 < (κ.Mhi : ℝ) := by
    have hq : 0 < 10 / κ.cq := div_pos (by norm_num) hκ.cq_rng.1
    nlinarith [hκ.Mhi_big.1, hMloPosR]
  have hMhiPos : 0 < κ.Mhi := by exact_mod_cast hMhiPosR
  have hMhiOne : 1 ≤ (κ.Mhi : ℝ) := by
    exact_mod_cast (Nat.succ_le_iff.mpr hMhiPos)
  have hωlt : κ.ω < 1 := by
    have hωle : κ.ω ≤ κ.ω * (κ.Mhi : ℝ) := by
      calc
        κ.ω = κ.ω * 1 := by ring
        _ ≤ κ.ω * (κ.Mhi : ℝ) :=
          mul_le_mul_of_nonneg_left hMhiOne (le_of_lt hκ.ω_rng.1)
    have haCsmall : κ.aC < 1 / 10 ^ 6 := by
      calc
        κ.aC < min κ.η0 1 / 10 ^ 6 := hκ.aC_rng.2
        _ ≤ 1 / 10 ^ 6 := by
          gcongr
          exact min_le_right _ _
    nlinarith [hκ.ω_rng.2, haCsmall, hωle]
  have hceilK : ∀ h : ℕ, 1 ≤ h → sliceK κ h ≤ h ^ 3 := by
    intro h hh
    change ⌈Real.rpow (h : ℝ) (3 * κ.ω)⌉₊ ≤ h ^ 3
    rw [Nat.ceil_le, Nat.cast_pow]
    have hhR : 1 ≤ (h : ℝ) := by exact_mod_cast hh
    have hexp : 3 * κ.ω ≤ 3 := by linarith
    calc
      Real.rpow (h : ℝ) (3 * κ.ω) ≤ Real.rpow (h : ℝ) 3 :=
        Real.rpow_le_rpow_of_exponent_le hhR hexp
      _ = (h : ℝ) ^ 3 := Real.rpow_natCast (h : ℝ) 3
  have hceilT : ∀ h : ℕ, 1 ≤ h → sliceT κ h ≤ h ^ 3 := by
    intro h hh
    change ⌈Real.rpow (h : ℝ) κ.ω⌉₊ ≤ h ^ 3
    rw [Nat.ceil_le, Nat.cast_pow]
    have hhR : 1 ≤ (h : ℝ) := by exact_mod_cast hh
    have hexp : κ.ω ≤ 3 := by linarith
    calc
      Real.rpow (h : ℝ) κ.ω ≤ Real.rpow (h : ℝ) 3 :=
        Real.rpow_le_rpow_of_exponent_le hhR hexp
      _ = (h : ℝ) ^ 3 := Real.rpow_natCast (h : ℝ) 3
  have hnatPos : ∀ᶠ k in atTop, 1 ≤ T.S.n k :=
    T.S.n_tendsto.eventually_ge_atTop 1
  have hpowTend := (tendsto_rpow_atTop hκ.η0_pos).comp
    (tendsto_natCast_atTop_atTop.comp T.S.n_tendsto)
  have hpowLarge : ∀ᶠ k in atTop, 10 ≤ (T.S.n k : ℝ) ^ κ.η0 :=
    hpowTend.eventually_ge_atTop 10
  have herrTend := (tendsto_rpow_neg_atTop hκ.η0_pos).comp
    (tendsto_natCast_atTop_atTop.comp T.S.n_tendsto)
  have herrScaled : Tendsto (fun k => (100 : ℝ) * (T.S.n k : ℝ) ^ (-κ.η0))
      atTop (nhds 0) := by
    simpa [mul_comm] using herrTend.const_mul 100
  have herrEvent : ∀ᶠ k in atTop,
      100 * (T.S.n k : ℝ) ^ (-κ.η0) ≤ κ.a := by
    filter_upwards [herrScaled.eventually (Iio_mem_nhds haPos)] with k hk
    exact le_of_lt hk
  have hexceptionEvent : ∀ᶠ k in atTop,
      ∀ h r K : ℕ, (h : ℝ) < (T.S.n k : ℝ) ^ κ.ι →
        K ≤ h ^ 3 → r ≤ h ^ 3 →
        ((r : ℝ) + 1) * (K : ℝ) * (r : ℝ) *
            Real.exp (-((T.S.n k : ℝ) ^ κ.η0 / 2)) ≤
          Real.exp (-(κ.a ^ 2 * (K : ℝ)) / 50) := by
    filter_upwards [hnatPos, hpowLarge] with k hnk hηlarge
    have hn : 1 ≤ (T.S.n k : ℝ) := by exact_mod_cast hnk
    intro h r K hh hK hr
    let n : ℝ := T.S.n k
    let x : ℝ := Real.rpow n (3 * κ.ι)
    let E : ℝ := Real.rpow n κ.η0
    have hnpos : 0 < n := lt_of_lt_of_le (by norm_num) hn
    have hηpos : 0 < κ.η0 := hκ.η0_pos
    have hιpos : 0 < κ.ι := hκ.ι_rng.1
    have hElarge : 10 ≤ E := by simpa [E, n] using hηlarge
    have hιcast : (h : ℝ) ≤ Real.rpow n κ.ι := by
      simpa [n] using hh.le
    have hhPow : (h : ℝ) ^ 3 ≤ x := by
      calc
        (h : ℝ) ^ 3 = Real.rpow (h : ℝ) 3 := (Real.rpow_natCast (h : ℝ) 3).symm
        _ ≤ Real.rpow (Real.rpow n κ.ι) 3 :=
          Real.rpow_le_rpow (by positivity) hιcast (by norm_num)
        _ = Real.rpow n (κ.ι * 3) := (Real.rpow_mul (le_of_lt hnpos) κ.ι 3).symm
        _ = x := by congr 1 <;> ring
    have hKx : (K : ℝ) ≤ x := by
      have hK' : (K : ℝ) ≤ (h : ℝ) ^ 3 := by exact_mod_cast hK
      exact le_trans hK' hhPow
    have hrx : (r : ℝ) ≤ x := by
      have hr' : (r : ℝ) ≤ (h : ℝ) ^ 3 := by exact_mod_cast hr
      exact le_trans hr' hhPow
    have hxone : 1 ≤ x := Real.one_le_rpow hn (by positivity)
    have hrplus : (r : ℝ) + 1 ≤ 2 * x := by nlinarith [hrx, hxone]
    have hprod : ((r : ℝ) + 1) * (K : ℝ) * (r : ℝ) ≤ 2 * x ^ 3 := by
      calc
        ((r : ℝ) + 1) * (K : ℝ) * (r : ℝ) ≤ (2 * x) * x * x := by
          gcongr
        _ = 2 * x ^ 3 := by ring
    have hιsmall : 9 * κ.ι ≤ κ.η0 / 100 := by nlinarith [hιη]
    have hx3 : x ^ 3 = Real.rpow n (9 * κ.ι) := by
      dsimp [x]
      change (Real.rpow n (3 * κ.ι)) ^ 3 = Real.rpow n (9 * κ.ι)
      calc
        (Real.rpow n (3 * κ.ι)) ^ 3 = Real.rpow n ((3 * κ.ι) * 3) :=
          (Real.rpow_mul_natCast (le_of_lt hnpos) (3 * κ.ι) 3).symm
        _ = Real.rpow n (9 * κ.ι) := by congr 1 <;> ring
    have hx3le : x ^ 3 ≤ Real.rpow n (κ.η0 / 100) := by
      rw [hx3]
      exact Real.rpow_le_rpow_of_exponent_le hn hιsmall
    have hprod' : ((r : ℝ) + 1) * (K : ℝ) * (r : ℝ) ≤
        2 * Real.rpow n (κ.η0 / 100) := by
      exact le_trans hprod (mul_le_mul_of_nonneg_left hx3le (by norm_num))
    have hιK : 3 * κ.ι ≤ κ.η0 := by nlinarith [hιη]
    have hKleE : (K : ℝ) ≤ E := by
      dsimp [E]
      exact le_trans hKx (Real.rpow_le_rpow_of_exponent_le hn hιK)
    have hlogn : Real.log n ≤ Real.rpow n (κ.η0 / 4) / (κ.η0 / 4) :=
      Real.log_le_rpow_div (by linarith : (0 : ℝ) ≤ n) (by positivity)
    have hlogterm : κ.η0 / 100 * Real.log n ≤
        Real.rpow n (κ.η0 / 4) / 25 := by
      calc
        κ.η0 / 100 * Real.log n ≤
            κ.η0 / 100 * (Real.rpow n (κ.η0 / 4) / (κ.η0 / 4)) :=
          mul_le_mul_of_nonneg_left hlogn (by positivity)
        _ = Real.rpow n (κ.η0 / 4) / 25 := by field_simp [ne_of_gt hηpos]; ring
    have hpowQuarter : Real.rpow n (κ.η0 / 4) ≤ E := by
      dsimp [E]
      exact Real.rpow_le_rpow_of_exponent_le hn (by linarith [hηpos])
    have hlogterm' : κ.η0 / 100 * Real.log n ≤ E / 25 := by
      exact le_trans hlogterm (div_le_div_of_nonneg_right hpowQuarter (by norm_num))
    have haSq : κ.a ^ 2 ≤ 1 / 100 := by nlinarith [haSmall]
    have hcoeff : κ.a ^ 2 / 50 ≤ 1 / 5000 := by nlinarith [haSq]
    have hKterm : κ.a ^ 2 * (K : ℝ) / 50 ≤ E / 5000 := by
      calc
        κ.a ^ 2 * (K : ℝ) / 50 = (κ.a ^ 2 / 50) * (K : ℝ) := by ring
        _ ≤ (1 / 5000 : ℝ) * E :=
          mul_le_mul hcoeff hKleE (by positivity) (by positivity)
        _ = E / 5000 := by ring
    have hlog2 : Real.log 2 ≤ 1 := by
      nlinarith [Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 2)]
    have hlog2' : Real.log 2 ≤ E / 10 := by nlinarith [hlog2, hElarge]
    have hlogprod : Real.log (2 * Real.rpow n (κ.η0 / 100)) =
        Real.log 2 + κ.η0 / 100 * Real.log n := by
      calc
        Real.log (2 * Real.rpow n (κ.η0 / 100)) =
            Real.log 2 + Real.log (Real.rpow n (κ.η0 / 100)) :=
          Real.log_mul (x := 2) (y := Real.rpow n (κ.η0 / 100))
            (by norm_num) (ne_of_gt (Real.rpow_pos_of_pos hnpos _))
        _ = Real.log 2 + κ.η0 / 100 * Real.log n := by
          change Real.log 2 + Real.log (n ^ (κ.η0 / 100)) = _
          rw [Real.log_rpow hnpos (κ.η0 / 100)]
    have hlogsum : Real.log 2 + κ.η0 / 100 * Real.log n +
        κ.a ^ 2 * (K : ℝ) / 50 ≤ E / 2 := by
      nlinarith [hlog2', hlogterm', hKterm]
    have hexpProd : 2 * Real.rpow n (κ.η0 / 100) ≤
        Real.exp (E / 2 - κ.a ^ 2 * (K : ℝ) / 50) := by
      have hlogpos : 0 < 2 * Real.rpow n (κ.η0 / 100) :=
        mul_pos (by norm_num) (Real.rpow_pos_of_pos hnpos _)
      have hlogineq : Real.log (2 * Real.rpow n (κ.η0 / 100)) ≤
          E / 2 - κ.a ^ 2 * (K : ℝ) / 50 := by
        rw [hlogprod]
        linarith [hlogsum]
      have hlogbound := Real.exp_le_exp.mpr hlogineq
      rw [Real.exp_log hlogpos] at hlogbound
      exact hlogbound
    have hcore : 2 * Real.rpow n (κ.η0 / 100) *
        Real.exp (-E / 2) ≤ Real.exp (-(κ.a ^ 2 * (K : ℝ)) / 50) := by
      calc
        2 * Real.rpow n (κ.η0 / 100) * Real.exp (-E / 2) ≤
            Real.exp (E / 2 - κ.a ^ 2 * (K : ℝ) / 50) * Real.exp (-E / 2) :=
          mul_le_mul_of_nonneg_right hexpProd (Real.exp_nonneg _)
        _ = Real.exp (-(κ.a ^ 2 * (K : ℝ)) / 50) := by
          rw [← Real.exp_add]
          congr 1
          ring
    have hExpEq : Real.exp (-E / 2) =
        Real.exp (-((T.S.n k : ℝ) ^ κ.η0 / 2)) := by
      congr 1
      dsimp [E, n]
      ring
    rw [← hExpEq]
    calc
      ((r : ℝ) + 1) * (K : ℝ) * (r : ℝ) * Real.exp (-E / 2) ≤
          2 * Real.rpow n (κ.η0 / 100) * Real.exp (-E / 2) :=
        mul_le_mul_of_nonneg_right hprod' (Real.exp_nonneg _)
      _ ≤ Real.exp (-(κ.a ^ 2 * (K : ℝ)) / 50) := hcore
  have hscalesEvent := patch_scales κ hκ T
  filter_upwards [hinit, hscalesEvent, hnatPos, hpowLarge, herrEvent,
    hexceptionEvent] with k hdisc hscales hnk hηlarge herr hException
  intro 𝒯 h𝒯 i
  unfold GenericListBound
  intro L hcard hsmallA
  have hK : 𝒯.kScale i = 0 ∨ 𝒯.mode.isCluster := by
    by_cases hcluster : 𝒯.mode.isCluster
    · exact Or.inr hcluster
    · left
      cases hm : 𝒯.mode with
      | lowCluster => simp [Mode.isCluster, hm] at hcluster
      | highSmall => simp [Mode.isCluster, hm] at hcluster
      | highLarge => simp [Mode.isCluster, hm] at hcluster
      | lowDirect =>
          rcases h𝒯.direct_data (Or.inl hm) i with ⟨_, _, _, _, hh, _, _⟩
          change sliceK κ (𝒯.P i).h = 0
          rw [hh]
          have hexp : 3 * κ.ω ≠ 0 := ne_of_gt (mul_pos (by norm_num) hκ.ω_rng.1)
          simp [sliceK, Real.zero_rpow hexp]
      | highDirect =>
          rcases h𝒯.direct_data (Or.inr hm) i with ⟨_, _, _, _, hh, _, _⟩
          change sliceK κ (𝒯.P i).h = 0
          rw [hh]
          have hexp : 3 * κ.ω ≠ 0 := ne_of_gt (mul_pos (by norm_num) hκ.ω_rng.1)
          simp [sliceK, Real.zero_rpow hexp]
      | bounded =>
          have hh : (𝒯.P i).h = 0 := (h𝒯.bounded_data hm).2 i |>.2.1
          change sliceK κ (𝒯.P i).h = 0
          rw [hh]
          have hexp : 3 * κ.ω ≠ 0 := ne_of_gt (mul_pos (by norm_num) hκ.ω_rng.1)
          simp [sliceK, Real.zero_rpow hexp]
  rcases hK with hKzero | hcluster
  · have hGood : ∀ W, L.Good W := by
      intro W
      unfold ListTestModel.Good
      have hhit : L.hitSet W = Finset.univ := by
        ext y
        simp [ListTestModel.hitSet, hKzero]
      have hhitDel : ∀ c₀, L.hitSetDelete W c₀ = Finset.univ := by
        intro c₀
        ext y
        simp [ListTestModel.hitSetDelete, hKzero]
      have hmass : L.mass Finset.univ = 1 := by
        have hmassD (b : Bin 𝒯 i) :
            (∑ y, (L.binDist b).w y) = 1 := (L.binDist b).sum_eq_one
        unfold ListTestModel.mass
        simp_rw [hmassD]
        simp [L.binPrior.sum_eq_one]
      constructor
      · rw [hhit, hmass]
        simp [hKzero]
      · intro c₀
        rw [hhit, hhitDel c₀, hmass]
        simp [hKzero]
    have hprob : L.tupleLaw.pr L.Failure ≤ 1 := by
      unfold FinLaw.pr
      calc
        (∑ W, if L.Failure W then L.tupleLaw.w W else 0) ≤ ∑ W, L.tupleLaw.w W := by
          apply Finset.sum_le_sum
          intro W hW
          by_cases hfail : L.Failure W
          · simp [hfail, L.tupleLaw.nonneg W]
          · simp [hfail, L.tupleLaw.nonneg W]
        _ = 1 := L.tupleLaw.sum_one
    have hnever : ∀ W, ¬ L.Failure W := by
      intro W
      simp [ListTestModel.Failure, hGood W]
    have hzero : L.tupleLaw.pr L.Failure = 0 := by
      unfold FinLaw.pr
      simp [hnever]
    rw [hzero]
    positivity
  · have hpatchScales := hscales 𝒯 h𝒯 hcluster i
    let r : ℕ := Fintype.card L.Id
    let q : ℕ := Fintype.card (Bin 𝒯 i)
    let K : ℕ := 𝒯.kScale i
    let w : ℝ := (T.S.n k : ℝ) ^ κ.η0
    let wμ : ℝ := w / 2
    let wν : ℝ := Real.log ((T.S.N k : ℝ) / (𝒯.P i).M)
    let ε : ℝ := (T.S.n k : ℝ) ^ (-κ.η0)
    let eId : Fin r ≃ L.Id := (Fintype.equivFin L.Id).symm
    let eBin : Fin q ≃ Bin 𝒯 i := (Fintype.equivFin (Bin 𝒯 i)).symm
    let μ : Fin r → Law (T.S.N k) := fun b => L.firstLaw (eId b)
    let ρ : FinProb (Fin q) := {
      w := fun b => L.binPrior.w (eBin b)
      nonneg := fun b => L.binPrior.nonneg (eBin b)
      sum_eq_one := by
        change (∑ b : Fin q, L.binPrior.w (eBin b)) = 1
        calc
          (∑ b : Fin q, L.binPrior.w (eBin b)) =
              ∑ B : Bin 𝒯 i, L.binPrior.w B :=
            Fintype.sum_equiv eBin _ _ (by intro b; rfl)
          _ = 1 := L.binPrior.sum_eq_one
    }
    let D : Fin q → Law (T.S.N k) := fun b => L.binDist (eBin b)
    let ν : Law (T.S.N k) := Law.unifCore (𝒯.P i).Y (h𝒯.patch_nonempty i).2
    let eW : (∀ c : L.Id, Fin K → Fin (T.S.N k)) ≃
        (Fin r → Fin K → Fin (T.S.N k)) := {
      toFun := fun W b => W (eId b)
      invFun := fun W c => W (eId.symm c)
      left_inv := by intro W; funext c; simp
      right_inv := by intro W; funext b; simp
    }
    have hμ : ∀ b, (μ b).SupportedIn (T.X k) ∧ (μ b).WidthLE wμ := by
      intro b
      exact ⟨L.first_law_supported (eId b), L.width_bound (eId b)⟩
    have hpatchY : (𝒯.P i).Y ⊆ T.Y k := by
      rcases h𝒯.patch_supports i with ⟨_, _, hY, hYres⟩
      intro y hy
      exact (Finset.mem_sdiff.mp (hYres (hY hy))).1
    have hD : ∀ b, (D b).SupportedIn (T.Y k) := by
      intro b y hy
      apply L.bin_support (eBin b) y
      intro hyB
      exact hy (hpatchY ((𝒯.P i).bins.subset (eBin b).property hyB))
    have hνwidth : ν.WidthLE wν := by
      simpa [ν, wν, Law.unifCore, FinProb.uniform, (𝒯.P i).cardY] using
        (Law.uniform_width (𝒯.P i).Y (h𝒯.patch_nonempty i).2)
    have hmix (y : Fin (T.S.N k)) :
        (∑ b : Fin q, ρ.w b * (D b).w y) =
          ∑ B : Bin 𝒯 i, L.binPrior.w B * (L.binDist B).w y := by
      exact Fintype.sum_equiv eBin _ _ (by intro b; rfl)
    have hagg : ∀ y, (∑ b : Fin q, ρ.w b * (D b).w y) ≤ 4 * ν.w y := by
      intro y
      by_cases hy : y ∈ (𝒯.P i).Y
      · have hνy : ν.w y = ((𝒯.P i).M : ℝ)⁻¹ := by
          simp [ν, Law.unifCore, hy]
          rw [(𝒯.P i).cardY]
        calc
          (∑ b : Fin q, ρ.w b * (D b).w y) ≤ 4 / (𝒯.P i).M := by
            rw [hmix y]
            exact L.aggregate_cap y
          _ = 4 * ν.w y := by rw [hνy]; ring
      · have hzero : (∑ b : Fin q, ρ.w b * (D b).w y) = 0 := by
          rw [hmix y]
          apply Finset.sum_eq_zero
          intro B hB
          have hyB : y ∉ B.1 := by
            intro hyB
            exact hy ((𝒯.P i).bins.subset B.2 hyB)
          have hdist := L.bin_support B y hyB
          simp [hdist]
        rw [hzero]
        simp [ν, Law.unifCore, hy]
    have hdiscOne : DiscOne (T.S.E k) (T.X k) (T.Y k) w w ε := by
      intro μ' ν' hμ' hν' hwμ' hwν' c
      exact hdisc c μ' ν' hμ' hν' (Or.inl ⟨hwμ', hwν'⟩)
    have hεnonneg : 0 ≤ ε := by
      dsimp [ε]
      positivity
    have hεa : 100 * ε ≤ κ.a := by simpa [ε, w] using herr
    have ha : κ.a ≤ 1 / 10 := haSmall
    have hbudget : wν + Real.log 4 + 2 * (K : ℝ) * (r : ℝ) ≤ w := by
      have hr : (r : ℝ) ≤ (𝒯.tScale i : ℝ) := by exact_mod_cast hcard
      have hmul : 2 * (K : ℝ) * (r : ℝ) ≤
          2 * (K : ℝ) * 𝒯.tScale i := by gcongr
      have hlog4 : Real.log 4 ≤ 3 := by
        nlinarith [Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 4)]
      have hwNonneg : 0 ≤ w := by
        dsimp [w]
        positivity
      calc
        wν + Real.log 4 + 2 * (K : ℝ) * (r : ℝ) ≤
            2 * (K : ℝ) * 𝒯.tScale i +
              Real.log ((T.S.N k : ℝ) / (𝒯.P i).M) + 3 := by
                dsimp [wν]
                linarith
        _ ≤ w / 2 := hpatchScales.budget
        _ ≤ w := by linarith
    have hrNat : r ≤ 𝒯.tScale i := by simpa [r] using hcard
    let target : ℝ := 2 * (𝒯.tScale i + 1 : ℝ) *
      Real.exp (-κ.c5 * κ.a ^ 2 * (K : ℝ))
    have hlogOfTarget : target < 1 →
        Real.log ((r : ℝ) + 1) ≤ κ.a ^ 2 * (K : ℝ) / 100 := by
      intro htarget
      have hFactorPos : 0 < 2 * (𝒯.tScale i + 1 : ℝ) := by positivity
      have hlogprod : Real.log target =
          Real.log (2 * (𝒯.tScale i + 1 : ℝ)) - κ.c5 * κ.a ^ 2 * (K : ℝ) := by
        dsimp [target]
        rw [Real.log_mul (by positivity) (ne_of_gt (Real.exp_pos _)), Real.log_exp]
        ring
      have hlogtarget : Real.log (2 * (𝒯.tScale i + 1 : ℝ)) <
          κ.c5 * κ.a ^ 2 * (K : ℝ) := by
        have ht := Real.log_lt_log (by positivity : 0 < target) htarget
        rw [hlogprod, Real.log_one] at ht
        linarith
      have hrplus : (r : ℝ) + 1 ≤ 2 * (𝒯.tScale i + 1 : ℝ) := by
        have hr' : (r : ℝ) ≤ (𝒯.tScale i : ℝ) := by exact_mod_cast hcard
        nlinarith
      have hlogmono := Real.log_le_log (by positivity : (0 : ℝ) < (r : ℝ) + 1)
        hrplus
      have hcoef : κ.c5 ≤ 1 / 1000 := hκ.c5_le
      have hnonneg : 0 ≤ κ.a ^ 2 * (K : ℝ) := by positivity
      nlinarith
    have hKnat : 1 ≤ (𝒯.P i).h := by
      have hh0 : 0 < κ.h0 := hκ.h0_pos
      have hh1 : 1 ≤ κ.h0 := Nat.succ_le_iff.mpr hh0
      exact le_trans hh1 hpatchScales.h_large
    have hKbound : 𝒯.kScale i ≤ (𝒯.P i).h ^ 3 :=
      hceilK (𝒯.P i).h hKnat
    have htbound : 𝒯.tScale i ≤ (𝒯.P i).h ^ 3 :=
      hceilT (𝒯.P i).h hKnat
    have halloc := h𝒯.allocation_bounds i
    have hhN : ((𝒯.P i).h : ℝ) < (T.S.n k : ℝ) ^ κ.ι := by
      exact lt_of_le_of_lt (by exact_mod_cast (le_max_left (𝒯.P i).h (𝒯.P i).ℓ)) halloc.1
    have hExceptionBound :
        ((r : ℝ) + 1) * (K : ℝ) * (r : ℝ) *
            Real.exp (wμ - w) ≤ Real.exp (-(κ.a ^ 2 * (K : ℝ)) / 50) := by
      have hEx := hException (𝒯.P i).h r K hhN hKbound (le_trans hrNat htbound)
      have hwExponent : wμ - w = -((T.S.n k : ℝ) ^ κ.η0 / 2) := by
        dsimp [wμ, w]
        ring
      rw [hwExponent]
      simpa [K] using hEx
    have hWeight (W : ∀ c : L.Id, Fin K → Fin (T.S.N k)) :
        L.tupleLaw.w W = HypercubeRamsey.S10.tupleArrayWeight μ (eW W) := by
      simp only [ListTestModel.tupleLaw, FinLaw.pi, lawToFinLaw,
        HypercubeRamsey.S10.tupleArrayWeight]
      change (∏ c : L.Id, ∏ t : Fin K, (L.firstLaw c).w (W c t)) =
        ∏ b : Fin r, ∏ t : Fin K, (L.firstLaw (eId b)).w (W (eId b) t)
      symm
      exact Fintype.prod_equiv eId _ _ (by intro b; rfl)
    have hMass (A : Finset (Fin (T.S.N k))) :
        HypercubeRamsey.S10.squaredClusterMass ρ D A = L.mass A := by
      unfold HypercubeRamsey.S10.squaredClusterMass
        HypercubeRamsey.S10.lawMassOn ListTestModel.mass
      exact Fintype.sum_equiv eBin _ _ (by intro b; rfl)
    have hHit (W : ∀ c : L.Id, Fin K → Fin (T.S.N k)) :
        HypercubeRamsey.S10.fixedListHitSet (T.S.E k) 𝒯.c (eW W) =
          L.hitSet W := by
      ext y
      simp only [HypercubeRamsey.S10.fixedListHitSet, ListTestModel.hitSet,
        Finset.mem_filter, Finset.mem_univ, true_and]
      change (∀ b : Fin r, ∀ t : Fin K,
          Hits (T.S.E k) 𝒯.c (W (eId b) t) y) ↔
        (∀ c : L.Id, ∀ t : Fin K, Hits (T.S.E k) 𝒯.c (W c t) y)
      constructor
      · intro h c t
        simpa using h (eId.symm c) t
      · intro h b t
        exact h (eId b) t
    have hHitDelete (W : ∀ c : L.Id, Fin K → Fin (T.S.N k)) (b : Fin r) :
        HypercubeRamsey.S10.fixedListHitSetWithout (T.S.E k) 𝒯.c (eW W) b =
          L.hitSetDelete W (eId b) := by
      ext y
      simp only [HypercubeRamsey.S10.fixedListHitSetWithout,
        ListTestModel.hitSetDelete, Finset.mem_filter, Finset.mem_univ, true_and]
      change (∀ b' : Fin r, b' ≠ b → ∀ t : Fin K,
          Hits (T.S.E k) 𝒯.c (W (eId b') t) y) ↔
        (∀ c' : L.Id, c' ≠ eId b → ∀ t : Fin K,
          Hits (T.S.E k) 𝒯.c (W c' t) y)
      constructor
      · intro h c' hc' t
        have hneq : eId.symm c' ≠ b := by
          intro heq
          apply hc'
          calc
            c' = eId (eId.symm c') := (eId.apply_symm_apply c').symm
            _ = eId b := congrArg eId heq
        simpa using h (eId.symm c') hneq t
      · intro h b' hb' t
        apply h (eId b')
        intro heq
        apply hb'
        exact eId.injective heq
    have hown (b : Fin r) :
        HypercubeRamsey.S10.FixedListOwnBlock (T.S.E k) 𝒯.c ρ D (μ b) κ.a := by
      intro j hj y y' hy hy'
      have hprior : 0 < L.binPrior.w (eBin j) := by simpa [ρ] using hj
      have hyD : (L.binDist (eBin j)).w y ≠ 0 := ne_of_gt (by simpa [D] using hy)
      have hy'D : (L.binDist (eBin j)).w y' ≠ 0 := ne_of_gt (by simpa [D] using hy')
      have hcodeg := L.codegree_bound (eId b) (eBin j) y y' hprior hyD hy'D
      have hEq : HypercubeRamsey.codeg (T.S.E k) 𝒯.c (μ b) y y' =
          ∑ x, (μ b).w x * HypercubeRamsey.hit (T.S.E k) 𝒯.c x y *
            HypercubeRamsey.hit (T.S.E k) 𝒯.c x y' := by
        unfold HypercubeRamsey.codeg HypercubeRamsey.hit
        apply Finset.sum_congr rfl
        intro x hx
        by_cases hxy : Hits (T.S.E k) 𝒯.c x y <;>
          by_cases hxy' : Hits (T.S.E k) 𝒯.c x y' <;>
            simp [hxy, hxy'] <;> ring
      change (1 / 4 : ℝ) + κ.a ≤ HypercubeRamsey.codeg (T.S.E k) 𝒯.c (μ b) y y'
      rw [hEq]
      exact hcodeg
    have hmassNonneg (A : Finset (Fin (T.S.N k))) : 0 ≤ L.mass A := by
      unfold ListTestModel.mass
      apply Finset.sum_nonneg
      intro b hb
      exact mul_nonneg (L.binPrior.nonneg b) (sq_nonneg _)
    have hFailureMap (W : ∀ c : L.Id, Fin K → Fin (T.S.N k)) :
        L.Failure W →
          HypercubeRamsey.S10.fixedListFailure (T.S.E k) 𝒯.c ρ D μ κ.a (eW W) := by
      intro hfail
      have hnotGood : ¬ (L.mass (L.hitSet W) ≥
          Real.exp (-2 * (K : ℝ) * (r : ℝ)) ∧
          ∀ c₀, L.mass (L.hitSet W) ≥
            Real.exp ((-Real.log 4 + 0.4 * κ.a) * (K : ℝ)) *
              L.mass (L.hitSetDelete W c₀)) := by
        simpa [ListTestModel.Failure, ListTestModel.Good, r, K] using hfail
      have hbad : L.mass (L.hitSet W) < Real.exp (-2 * (K : ℝ) * (r : ℝ)) ∨
          ∃ c₀, L.mass (L.hitSet W) <
            Real.exp ((-Real.log 4 + 0.4 * κ.a) * (K : ℝ)) *
              L.mass (L.hitSetDelete W c₀) := by
        by_cases habs : L.mass (L.hitSet W) < Real.exp (-2 * (K : ℝ) * (r : ℝ))
        · exact Or.inl habs
        · right
          by_contra hnone
          push_neg at hnone
          exact hnotGood ⟨le_of_not_gt habs, fun c₀ => hnone c₀⟩
      have hcoeff : (2 / 5 : ℝ) = 0.4 := by norm_num
      rcases hbad with habs | ⟨c₀, hdel⟩
      · left
        change HypercubeRamsey.S10.squaredClusterMass ρ D
          (HypercubeRamsey.S10.fixedListHitSet (T.S.E k) 𝒯.c (eW W)) < _
        rw [hHit W, hMass]
        exact habs
      · right
        left
        let b : Fin r := eId.symm c₀
        refine ⟨b, ?_⟩
        have hdelpos : 0 < L.mass (L.hitSetDelete W c₀) := by
          by_contra hz
          have hz' : L.mass (L.hitSetDelete W c₀) = 0 :=
            le_antisymm (le_of_not_gt hz) (hmassNonneg _)
          rw [hz'] at hdel
          have hAneg : L.mass (L.hitSet W) < 0 := by simpa using hdel
          exact (not_lt_of_ge (hmassNonneg (L.hitSet W))) hAneg
        have hratio : L.mass (L.hitSet W) / L.mass (L.hitSetDelete W c₀) <
            Real.exp ((-Real.log 4 + (2 / 5 : ℝ) * κ.a) * (K : ℝ)) := by
          have hdel' : L.mass (L.hitSet W) <
              Real.exp ((-Real.log 4 + (2 / 5 : ℝ) * κ.a) * (K : ℝ)) *
                L.mass (L.hitSetDelete W c₀) := by simpa [hcoeff] using hdel
          exact (div_lt_iff₀ hdelpos).2 hdel'
        have hfull : HypercubeRamsey.S10.squaredClusterMass ρ D
            (HypercubeRamsey.S10.fixedListHitSet (T.S.E k) 𝒯.c (eW W)) =
              L.mass (L.hitSet W) := by rw [hHit W, hMass]
        have hdeleted : HypercubeRamsey.S10.squaredClusterMass ρ D
            (HypercubeRamsey.S10.fixedListHitSetWithout (T.S.E k) 𝒯.c (eW W) b) =
              L.mass (L.hitSetDelete W c₀) := by
          rw [hHitDelete W b, show eId b = c₀ by simp [b], hMass]
        change HypercubeRamsey.S10.FixedListOwnBlock (T.S.E k) 𝒯.c ρ D (μ b) κ.a ∧
          HypercubeRamsey.S10.squaredClusterMass ρ D
              (HypercubeRamsey.S10.fixedListHitSet (T.S.E k) 𝒯.c (eW W)) /
            HypercubeRamsey.S10.squaredClusterMass ρ D
              (HypercubeRamsey.S10.fixedListHitSetWithout (T.S.E k) 𝒯.c (eW W) b) < _
        constructor
        · exact hown b
        · rw [hfull, hdeleted]
          exact hratio
    have hprobLe : L.tupleLaw.pr L.Failure ≤
        HypercubeRamsey.S10.fixedListFailureWeight (N := T.S.N k)
          (r := r) (k := K) (q := q)
          (T.S.E k) 𝒯.c ρ D μ κ.a := by
      unfold FinLaw.pr HypercubeRamsey.S10.fixedListFailureWeight
      calc
        (∑ W, if L.Failure W then L.tupleLaw.w W else 0) ≤
            ∑ W, if HypercubeRamsey.S10.fixedListFailure
                (T.S.E k) 𝒯.c ρ D μ κ.a (eW W) then L.tupleLaw.w W else 0 := by
          apply Finset.sum_le_sum
          intro W hW
          by_cases hf : L.Failure W
          · simp [hf, hFailureMap W hf, L.tupleLaw.nonneg W]
          · by_cases hFixed : HypercubeRamsey.S10.fixedListFailure
                (T.S.E k) 𝒯.c ρ D μ κ.a (eW W)
            · simp [hf, hFixed, L.tupleLaw.nonneg W]
            · simp [hf, hFixed]
        _ = ∑ W, if HypercubeRamsey.S10.fixedListFailure
              (T.S.E k) 𝒯.c ρ D μ κ.a W then
                L.tupleLaw.w (eW.symm W) else 0 := by
          exact Fintype.sum_equiv eW _ _ (by intro W; simp)
        _ = ∑ W, if HypercubeRamsey.S10.fixedListFailure
              (T.S.E k) 𝒯.c ρ D μ κ.a W then
                HypercubeRamsey.S10.tupleArrayWeight μ W else 0 := by
          apply Finset.sum_congr rfl
          intro W hW
          by_cases hf : HypercubeRamsey.S10.fixedListFailure
              (T.S.E k) 𝒯.c ρ D μ κ.a W
          · simp [hf, hWeight (eW.symm W)]
          · simp [hf]
    have hprobOne : L.tupleLaw.pr L.Failure ≤ 1 := by
      unfold FinLaw.pr
      calc
        (∑ W, if L.Failure W then L.tupleLaw.w W else 0) ≤ ∑ W, L.tupleLaw.w W := by
          apply Finset.sum_le_sum
          intro W hW
          by_cases hfail : L.Failure W
          · simp [hfail, L.tupleLaw.nonneg W]
          · simp [hfail, L.tupleLaw.nonneg W]
        _ = 1 := L.tupleLaw.sum_one
    by_cases htarget : target < 1
    · have hlog := hlogOfTarget htarget
      have hfixed := fixedListBound_explicit (T.S.N k) r K q (T.S.E k)
        (T.X k) (T.Y k) 𝒯.c ρ D ν μ w ε κ.a wμ wν hμ hνwidth hD hagg
        hdiscOne hεnonneg hεa ha hbudget hlog hExceptionBound
      have hc5 : κ.c5 ≤ (1 / 100 : ℝ) := le_trans hκ.c5_le (by norm_num)
      have hexponent : -(1 / 100 : ℝ) * κ.a ^ 2 * (K : ℝ) ≤
          -κ.c5 * κ.a ^ 2 * (K : ℝ) := by
        have hnonneg : 0 ≤ κ.a ^ 2 * (K : ℝ) := by positivity
        nlinarith
      have hfactor : 1 ≤ 2 * (𝒯.tScale i + 1 : ℝ) := by
        have htNonneg : 0 ≤ (𝒯.tScale i : ℝ) := Nat.cast_nonneg _
        nlinarith
      calc
        L.tupleLaw.pr L.Failure ≤
            HypercubeRamsey.S10.fixedListFailureWeight (N := T.S.N k)
              (r := r) (k := K) (q := q)
              (T.S.E k) 𝒯.c ρ D μ κ.a := hprobLe
        _ ≤ Real.exp (-(1 / 100 : ℝ) * κ.a ^ 2 * (K : ℝ)) := hfixed
        _ ≤ Real.exp (-κ.c5 * κ.a ^ 2 * (K : ℝ)) := Real.exp_le_exp.mpr hexponent
        _ ≤ 2 * (𝒯.tScale i + 1 : ℝ) *
            Real.exp (-κ.c5 * κ.a ^ 2 * (K : ℝ)) := by
          calc
            Real.exp (-κ.c5 * κ.a ^ 2 * (K : ℝ)) =
                1 * Real.exp (-κ.c5 * κ.a ^ 2 * (K : ℝ)) := by ring
            _ ≤ 2 * (𝒯.tScale i + 1 : ℝ) *
                Real.exp (-κ.c5 * κ.a ^ 2 * (K : ℝ)) :=
              mul_le_mul_of_nonneg_right hfactor (Real.exp_nonneg _)
    · exact le_trans hprobOne (le_of_not_gt htarget)

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
  classical
  intro g W W' hvertex
  have hcheap : (mask g W).cheap = (mask g W').cheap := by
    funext D
    rw [(mask g W).cheap_eq, (mask g W').cheap_eq, hvertex]
  have hretained : (mask g W).retained = (mask g W').retained := by
    apply Finset.ext
    intro D
    rw [(mask g W).retained_spec, (mask g W').retained_spec, hcheap]
  constructor
  · funext D
    rw [(mask g W).prior_uniform, (mask g W').prior_uniform, hretained]
  · funext D y
    rw [(mask g W).within_uniform, (mask g W').within_uniform, hretained, hcheap]

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
