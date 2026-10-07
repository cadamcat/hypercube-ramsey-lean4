import HypercubeRamsey.S06.Selection

/-!
# Section 6 parent reduction and admitted histories

L6.1a and the conditioning interface of L6.1h.  The parent record fixes the
threshold support, posterior mixture, symmetric relation, and partner laws
used by all later Section 6 nodes.
-/

namespace HypercubeRamsey
namespace S06

open Classical
open OAI.HypercubeRamsey

noncomputable def heavySet6 {n N : ℕ} (Dstar : ℝ) (π : Law N) : Finset (Fin N) :=
  Finset.univ.filter fun y => (n : ℝ) ^ (-Dstar) ≤ (N : ℝ) * π.w y

noncomputable def related6 {N : ℕ} (E : Fin N → Fin N → Prop) (G : Colour)
    (M : TagMix N) (y y' : Fin N) : Prop :=
  c₀ ≤ colDeg E G (broadLaw6 M y) y' ∧
    c₀ ≤ colDeg E G (broadLaw6 M y') y

/-- Case 2 data from the reduction.  Primary names are the labels `y`, not sampled tag identities. -/
structure ParentCase6 (n N : ℕ) (E : Fin N → Fin N → Prop) (G : Colour)
    (M : TagMix N) (γ Dstar : ℝ) where
  heavy : Finset (Fin N)
  heavy_eq : heavy = heavySet6 (n := n) Dstar (secondMixture6 M)
  piPrime : Law N
  retained_mass : ∑ y ∈ heavy, (secondMixture6 M).w y ≥ 1 - (n : ℝ) ^ (-Dstar)
  piPrime_supported : piPrime.SupportedIn heavy
  piPrime_cap : ∀ y, piPrime.w y ≤ 2 * (secondMixture6 M).w y
  eta_cap : ∀ y ∈ heavy, ∀ i,
    (tagPosterior6 M y).w i ≤ (n : ℝ) ^ (2 * Dstar) * M.Λ i
  eta_mean : ∀ i, ∑ y, (secondMixture6 M).w y * (tagPosterior6 M y).w i = M.Λ i
  broad_width : ∀ y ∈ heavy,
    (broadLaw6 M y).WidthLE ((n : ℝ) ^ γ)
  S₀ : Finset (Fin N)
  S₀_eq : S₀ = heavy.filter fun y =>
    (FinProb.pr piPrime (fun y' => related6 E G M y y') : ℝ) ≥ 1 / 10
  S₀_mass : FinProb.pr piPrime (fun y => y ∈ S₀) ≥ 7 / 10
  partner_mass : ∀ y ∈ S₀,
    FinProb.pr piPrime (fun y' => related6 E G M y y') ≥ 1 / 10
  partner_cap : ∀ y ∈ S₀, ∀ z,
    (partnerLaw6 piPrime (related6 E G M) y y).w z ≤ 20 * (secondMixture6 M).w z

/-- Constants selected in the order prescribed at the start of the Section 6 proof. -/
structure Parameters6 (Dstar γ p₀ K : ℝ) where
  n₀ : ℕ
  C₀ : ℝ
  α : ℝ
  geometryN₀ : ℕ
  Dstar_pos : 0 < Dstar
  alpha_pos : 0 < α
  C₀_pos : 0 < C₀
  geometry_threshold : geometryN₀ ≤ n₀
  geometry_available : ∀ n, geometryN₀ ≤ n →
    ∃ g : ChunkGeometry6 n α,
      (n : ℝ) ^ α ≤ g.m ∧ (g.m : ℝ) < (n : ℝ) ^ α + 1

/-- The small universal density exponent and the later dimension/scale choices. -/
theorem L6_1_constants : ∃ Dstar : ℝ, 0 < Dstar := by
  sorry

theorem L6_1_parameters (Dstar γ p₀ K : ℝ) (hD : 0 < Dstar)
    (hγ : 0 < γ ∧ γ < 1) (hp : 0 < p₀) (hK : 0 < K) :
    Nonempty (Parameters6 Dstar γ p₀ K) := by
  sorry

/-- L6.1a: either the opposite colour already has a cube, or the parent relation has a broad core. -/
theorem L6_1a {n₀ n N : ℕ} {C₀ γ p₀ K Dstar : ℝ}
    {E : Fin N → Fin N → Prop} {G : Colour} (M : TagMix N)
    (hLarge : LargeAt n₀ C₀ n N) (hBal : M.Balanced K)
    (hWidth : ∀ i, 0 < M.Λ i → (M.μ i).WidthLE ((n : ℝ) ^ γ))
    (hCap : ∀ i, 0 < M.Λ i → (M.ν i).CapLE ((n : ℝ) ^ Dstar))
    (hDeg : ∀ i y, 0 < M.Λ i → 0 < (M.ν i).w y →
      1 - (n : ℝ) ^ (-p₀) ≤ colDeg E G (M.μ i) y)
    (hDstar : 0 < Dstar) :
    CubeAt n N E ∨ Nonempty (ParentCase6 n N E G M γ Dstar) := by
  sorry

/-- The admitted parent/base/hidden history and the inputs for L6.1i–j. -/
structure ConditionedCase6 (n N : ℕ) {E : Fin N → Fin N → Prop} {G : Colour}
    {M : TagMix N} {γ Dstar α : ℝ}
    (parents : ParentCase6 n N E G M γ Dstar) (geometry : ChunkGeometry6 n α)
    (states : StateEncoding6 geometry) where
  Center : Type
  [centerFintype : Fintype Center]
  [centerDecEq : DecidableEq Center]
  Odd : Type
  [oddFintype : Fintype Odd]
  [oddDecEq : DecidableEq Odd]
  Descriptor : Type
  [descriptorFintype : Fintype Descriptor]
  [descriptorDecEq : DecidableEq Descriptor]
  Raw : Type
  [rawFintype : Fintype Raw]
  [rawDecEq : DecidableEq Raw]
  Record : Type
  [recordFintype : Fintype Record]
  [recordDecEq : DecidableEq Record]
  k : ℕ
  heightSetup : HeightSetup6 n states.Site Center Odd Descriptor Raw
  heightHypotheses : HeightHypotheses6 heightSetup
  oddInput : OddPosteriorInput6 n N geometry.m k Odd Record Raw

attribute [instance] ConditionedCase6.centerFintype ConditionedCase6.centerDecEq
attribute [instance] ConditionedCase6.oddFintype ConditionedCase6.oddDecEq
attribute [instance] ConditionedCase6.descriptorFintype ConditionedCase6.descriptorDecEq
attribute [instance] ConditionedCase6.rawFintype ConditionedCase6.rawDecEq
attribute [instance] ConditionedCase6.recordFintype ConditionedCase6.recordDecEq

/-- L6.1h: restrict the successive parent, base-tag, and hidden-scalar histories. -/
theorem L6_1h {n N : ℕ} {E : Fin N → Fin N → Prop} {G : Colour}
    {M : TagMix N} {γ Dstar α : ℝ}
    (parents : ParentCase6 n N E G M γ Dstar) (g : ChunkGeometry6 n α)
    (states : StateEncoding6 g) :
    Nonempty (ConditionedCase6 n N parents g states) := by
  sorry

end S06
end HypercubeRamsey
