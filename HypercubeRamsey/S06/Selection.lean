import HypercubeRamsey.S06.ChunkGeometry

/-!
# Section 6 marking, height selection, and selected odd posteriors

L6.1i–j (06:505–637).  The statement records make the Section 5 height rule
and its Section 6 modifications explicit.  Low rows use a short-rule
selection lookup; the very same lookup is used to evaluate long-rule rows.
-/

namespace HypercubeRamsey
namespace S06

open OAI.HypercubeRamsey
open Filter
open scoped BigOperators

abbrev ArrayIndex6 (Center Descriptor : Type*) := Center × Descriptor

structure Subprob6 (N : ℕ) where
  w : Fin N → ℝ
  nonneg : ∀ y, 0 ≤ w y
  mass_le_one : ∑ y, w y ≤ 1

namespace Subprob6

def zero (N : ℕ) : Subprob6 N where
  w := fun _ => 0
  nonneg _ := le_rfl
  mass_le_one := by simp

end Subprob6

/-- The center/descriptor input left after the admitted-history stage (L6.1h). -/
structure HeightSetup6 (n : ℕ) (Site Center Odd Descriptor Raw : Type*)
    [Fintype Site] [DecidableEq Site] [Fintype Center] [DecidableEq Center]
    [Fintype Odd] [DecidableEq Odd] [Fintype Descriptor] [DecidableEq Descriptor]
    [Fintype Raw] [DecidableEq Raw] where
  height : ℕ
  lambda : ℕ
  T : ℕ
  k : ℕ
  radius : ℕ
  rawLaw : FinProb Raw
  prospective : Raw → Site → Fin (height + 1) → Finset Center
  oddStar : Odd → Finset Site
  descriptorIds : Descriptor → Finset (ArrayIndex6 Center Descriptor)
  descriptorsAt : Raw → Odd → Finset Descriptor
  failsStep3 : Raw → Odd → Descriptor → Prop
  failedIDSet : Raw → Odd → Finset (ArrayIndex6 Center Descriptor) → Prop
  incidentInputsAgree : Raw → Raw → Site → Prop

def HeightHypotheses6 {n : ℕ} {Site Center Odd Descriptor Raw : Type*}
    [Fintype Site] [DecidableEq Site] [Fintype Center] [DecidableEq Center]
    [Fintype Odd] [DecidableEq Odd] [Fintype Descriptor] [DecidableEq Descriptor]
    [Fintype Raw] [DecidableEq Raw]
    (P : HeightSetup6 n Site Center Odd Descriptor Raw) : Prop := by
  classical
  exact
    P.lambda = n ^ 10 ∧
    (∀ s l, P.rawLaw.pr (fun ω =>
      (P.prospective ω s l).card < P.lambda / 2 ∨ 2 * P.lambda < (P.prospective ω s l).card) ≤
        Real.exp (-(2 : ℝ) * n)) ∧
    (∀ b d, P.rawLaw.pr (fun ω => P.failsStep3 ω b d) ≤ Real.exp (-0.001 * (P.k : ℝ))) ∧
    (∀ ω b, ((P.descriptorsAt ω b).card : ℝ) ≤
      Real.exp (0.0005 * (P.k : ℝ))) ∧
      (∀ b (D : Finset Descriptor),
      (∀ d ∈ D, ∀ e ∈ D, d ≠ e → Disjoint (P.descriptorIds d) (P.descriptorIds e)) →
      P.rawLaw.pr (fun ω => ∀ d ∈ D, P.failsStep3 ω b d) ≤
        (Real.exp (-0.001 * (P.k : ℝ))) ^ D.card)

/-- Raw choices for a fixed local center environment. -/
structure HeightOutcome6 {n : ℕ} {Site Center Odd Descriptor Raw : Type*}
    [Fintype Site] [DecidableEq Site] [Fintype Center] [DecidableEq Center]
    [Fintype Odd] [DecidableEq Odd] [Fintype Descriptor] [DecidableEq Descriptor]
    [Fintype Raw] [DecidableEq Raw]
    (P : HeightSetup6 n Site Center Odd Descriptor Raw) where
  markFamily : Raw → Odd → (Fin (P.height + 1) × Fin (P.height + 1)) →
    Finset (Finset (ArrayIndex6 Center Descriptor))
  marked : Raw → Site → Fin (P.height + 1) → Finset Center
  eligible : Raw → Site → Fin (P.height + 1) → Finset Center
  choice : Raw → Site → Option (Fin (P.height + 1) × Center)
  markerSuccess : Raw → Prop
  success : Raw → Prop

def usedCenters6 {n : ℕ} {Site Center Odd Descriptor Raw : Type*}
    [Fintype Site] [DecidableEq Site] [Fintype Center] [DecidableEq Center]
    [Fintype Odd] [DecidableEq Odd] [Fintype Descriptor] [DecidableEq Descriptor]
    [Fintype Raw] [DecidableEq Raw]
    {P : HeightSetup6 n Site Center Odd Descriptor Raw}
    (o : HeightOutcome6 P) (ω : Raw) (b : Odd) : Finset Center := by
  classical
  exact (P.oddStar b).biUnion fun s =>
    match o.choice ω s with
    | none => ∅
    | some (_, c) => {c}

def HeightConclusion6 {n : ℕ} {Site Center Odd Descriptor Raw : Type*}
    [Fintype Site] [DecidableEq Site] [Fintype Center] [DecidableEq Center]
    [Fintype Odd] [DecidableEq Odd] [Fintype Descriptor] [DecidableEq Descriptor]
    [Fintype Raw] [DecidableEq Raw]
    (P : HeightSetup6 n Site Center Odd Descriptor Raw)
    (o : HeightOutcome6 P) (c : ℝ) : Prop := by
  classical
  exact
    0 < c ∧
    P.rawLaw.pr o.markerSuccess ≥ 1 - Real.exp (-(n : ℝ)) ∧
    P.rawLaw.pr o.success ≥ 1 - (n : ℝ) ^ (-c) ∧
    (∀ ω, o.markerSuccess ω → ∀ b levels A A',
      A ∈ o.markFamily ω b levels → A' ∈ o.markFamily ω b levels →
        A ≠ A' → Disjoint A A') ∧
    (∀ ω, o.markerSuccess ω → ∀ b levels A, A ∈ o.markFamily ω b levels →
      P.failedIDSet ω b A) ∧
    (∀ ω, o.markerSuccess ω → ∀ b levels A,
      P.failedIDSet ω b A →
      (∀ A' ∈ o.markFamily ω b levels, Disjoint A A') → A ∈ o.markFamily ω b levels) ∧
    (∀ ω, o.markerSuccess ω → ∀ b levels,
      (o.markFamily ω b levels).card < n) ∧
    (∀ ω, o.success ω → ∀ s l,
      P.lambda / 2 ≤ (P.prospective ω s l).card ∧
      (P.prospective ω s l).card ≤ 2 * P.lambda ∧
      (o.eligible ω s l).card ≥ P.lambda / 3) ∧
    (∀ ω, o.success ω → ∀ b,
      (usedCenters6 o ω b).card ≤ P.T ∧
      ∃ l, ∀ s ∈ P.oddStar b, ∀ l' c', o.choice ω s = some (l', c') → l' = l ∨ l' = l + 1) ∧
    (∀ ω b d, d ∈ P.descriptorsAt ω b → o.success ω → ¬ P.failsStep3 ω b d) ∧
    (∀ ω, o.markerSuccess ω → ∀ b levels s l, s ∈ P.oddStar b →
      (l = levels.1 ∨ l = levels.2) →
      ∀ A ∈ o.markFamily ω b levels, ∀ entry ∈ A, entry.1 ∈ o.marked ω s l) ∧
    (∀ ω s l center, center ∈ o.marked ω s l →
      ∃ b levels A entry, s ∈ P.oddStar b ∧ (l = levels.1 ∨ l = levels.2) ∧
        A ∈ o.markFamily ω b levels ∧ entry ∈ A ∧ center = entry.1) ∧
    (∀ ω ω' s l, P.incidentInputsAgree ω ω' s →
      o.marked ω s l = o.marked ω' s l) ∧
    (∀ ω s l, o.eligible ω s l = P.prospective ω s l \ o.marked ω s l)

/-- L6.1i: maximal disjoint failed-ID marking followed by the long height rule. -/
theorem L6_1i {n : ℕ} {Site Center Odd Descriptor Raw : Type*}
    [Fintype Site] [DecidableEq Site] [Fintype Center] [DecidableEq Center]
    [Fintype Odd] [DecidableEq Odd] [Fintype Descriptor] [DecidableEq Descriptor]
    [Fintype Raw] [DecidableEq Raw]
    (P : HeightSetup6 n Site Center Odd Descriptor Raw)
    (hP : HeightHypotheses6 P) :
    ∃ o : HeightOutcome6 P, ∃ c : ℝ, HeightConclusion6 P o c := by
  sorry

/-! ### TS-B4: fixed high-target local data list -/

inductive LocalVariable6 (W : Type*) (m : ℕ) where
  | hidden (ℓ : HiddenKey6 W m)
  | parent (p : ParentName6 W)
  | baseTag (h : CoarseKey6 W)
  deriving DecidableEq

/--
The fixed high-target list: hidden scalars in observed types, the named
parents of those types except the target, then the base tags near each listed
hidden key and those tags' named parents.  It contains no tuple observation;
thus deleting tuple `c` integrates its listed kernels to mass at most one.
-/
noncomputable def highLocalList6 {W : Type*} [Fintype W] [DecidableEq W] {m : ℕ}
    (binAdjacent : W → W → Prop) (target : ParentName6 W)
    (observedTypes : Finset (Type6 W m)) : Finset (LocalVariable6 W m) := by
  classical
  let hidden : Finset (LocalVariable6 W m) :=
    observedTypes.biUnion fun β => β.observations.image LocalVariable6.hidden
  let otherParents : Finset (LocalVariable6 W m) := observedTypes.biUnion fun β =>
    let pairNames : Finset (LocalVariable6 W m) :=
      {LocalVariable6.parent (primaryName6 β.key),
       LocalVariable6.parent (otherPrimaryName6 β.key)}
    pairNames.filter fun p => p ≠ LocalVariable6.parent target
  let nearTags : Finset (LocalVariable6 W m) := observedTypes.biUnion fun β =>
    β.observations.biUnion fun ℓ =>
    let h := ℓ.1
    (keyNeighborhood6 binAdjacent h).image LocalVariable6.baseTag
  let nearParents : Finset (LocalVariable6 W m) := observedTypes.biUnion fun β =>
    β.observations.biUnion fun ℓ =>
    (keyNeighborhood6 binAdjacent ℓ.1).biUnion fun h =>
      {LocalVariable6.parent (primaryName6 h), LocalVariable6.parent (otherPrimaryName6 h)}
  exact hidden ∪ otherParents ∪ nearTags ∪ nearParents

/-! ### TS-B2: selection lookup and long/short odd rows -/

structure AdjustmentTable6 (N : ℕ) (Record Raw : Type*)
    [Fintype Record] [Fintype Raw] where
  likelihood : Record → Fin N → ℝ
  adjustment : Record → Fin N → ℝ
  referenceDensity : Record → ℝ
  targetExperiment : Fin N → FinProb Raw
  presented : Record → Raw → Prop
  adjustment_nonneg : ∀ r y, 0 ≤ adjustment r y
  adjustment_le_one : ∀ r y, adjustment r y ≤ 1
  reference_nonneg : ∀ r, 0 ≤ referenceDensity r
  density_identity : ∀ r y,
    (targetExperiment y).pr (presented r) =
      likelihood r y * adjustment r y * referenceDensity r
  presentations_disjoint : ∀ ω r r', presented r ω → presented r' ω → r = r'

def likelihoodMass6 {N : ℕ} {Record Raw : Type*} [Fintype Record] [Fintype Raw]
    (π : Law N) (A : AdjustmentTable6 N Record Raw) (r : Record) : ℝ :=
  ∑ y, π.w y * A.likelihood r y

def adjustedMass6 {N : ℕ} {Record Raw : Type*} [Fintype Record] [Fintype Raw]
    (π : Law N) (A : AdjustmentTable6 N Record Raw) (r : Record) : ℝ :=
  ∑ y, π.w y * A.likelihood r y * A.adjustment r y

/-- The data available before the selection adjustment (L6.1f–i). -/
structure OddPosteriorInput6 (n N m k : ℕ) (Odd Record Raw : Type*)
    [Fintype Odd] [DecidableEq Odd] [Fintype Record] [DecidableEq Record]
    [Fintype Raw] [DecidableEq Raw] where
  centerLaw : Odd → FinProb Raw
  low : Odd → Prop
  [lowDecidable : DecidablePred low]
  prior : Odd → Law N
  table : Odd → AdjustmentTable6 N Record Raw
  presentedRecord : Raw → Odd → Record
  valid : Raw → Odd → Prop
  records : Odd → Finset Record
  records_cover_presentations : ∀ ω b, valid ω b → presentedRecord ω b ∈ records b
  record_count_small : ∀ b, (records b).card ≤ Nat.floor (Real.exp (0.01 * (k : ℝ)))
  deletionReference : Odd → Odd → Fin N → ℝ
  sameModeAndPrimary : Odd → Odd → Prop
  commonNeighbor : Odd → Fin N → Prop
  J : ℕ
  step3Failure : Raw → Odd → Record → Prop
  step3_failure_mass : ∀ b r, r ∈ records b →
    (centerLaw b).pr (fun ω => step3Failure ω b r) ≤ Real.exp (-0.02 * (k : ℝ))
  likelihood_nonneg : ∀ b r y, r ∈ records b → 0 ≤ (table b).likelihood r y
  likelihood_mass_pos : ∀ b r, r ∈ records b →
    0 < likelihoodMass6 (prior b) (table b) r
  basePosterior : Odd → Record → Fin N → ℝ
  basePosterior_exact : ∀ b r y, r ∈ records b →
    basePosterior b r y = ((prior b).w y * (table b).likelihood r y) *
      (likelihoodMass6 (prior b) (table b) r)⁻¹
  basePosterior_deletion : ∀ b r c y, r ∈ records b → low b →
    sameModeAndPrimary b c →
    basePosterior b r y ≤ Real.exp (0.16 * (k : ℝ)) * deletionReference b c y
  basePosterior_cap : ∀ b r y, r ∈ records b →
    if low b then (N : ℝ) * basePosterior b r y ≤
        Real.exp (((m : ℝ) ^ (0.15 : ℝ)) / 2)
    else (N : ℝ) * basePosterior b r y ≤
        (n : ℝ) ^ ((0.05 : ℝ) * (J : ℝ))
  basePosterior_common_support : ∀ b r y, r ∈ records b →
    0 < basePosterior b r y → commonNeighbor b y

attribute [instance] OddPosteriorInput6.lowDecidable

structure SelectedOddRows6 {n N m k : ℕ} {Odd Record Raw : Type*}
    [Fintype Odd] [DecidableEq Odd] [Fintype Record] [DecidableEq Record]
    [Fintype Raw] [DecidableEq Raw]
    (I : OddPosteriorInput6 n N m k Odd Record Raw) where
  proxy : Raw → Odd → Fin N → ℝ
  long : Raw → Odd → Fin N → ℝ
  shortLookup : Raw → Odd → Fin N → ℝ
  longLookup : Raw → Odd → Fin N → ℝ
  localityConstant : ℕ
  consultedSignRadius : ℕ
  ambientRadiusExcess : ℕ
  proxy_is_adjusted_when_mass_survives : ∀ ω b y, I.valid ω b → I.low b →
    Real.exp (-0.02 * (k : ℝ)) * likelihoodMass6 (I.prior b) (I.table b) (I.presentedRecord ω b) ≤
        adjustedMass6 (I.prior b) (I.table b) (I.presentedRecord ω b) →
      proxy ω b y =
        ((I.prior b).w y * (I.table b).likelihood (I.presentedRecord ω b) y *
          (I.table b).adjustment (I.presentedRecord ω b) y) *
        (adjustedMass6 (I.prior b) (I.table b) (I.presentedRecord ω b))⁻¹
  proxy_fallback_when_mass_small : ∀ ω b y, I.valid ω b → I.low b →
    adjustedMass6 (I.prior b) (I.table b) (I.presentedRecord ω b) <
        Real.exp (-0.02 * (k : ℝ)) * likelihoodMass6 (I.prior b) (I.table b) (I.presentedRecord ω b) →
      proxy ω b y = ((I.prior b).w y *
        (I.table b).likelihood (I.presentedRecord ω b) y) *
          (likelihoodMass6 (I.prior b) (I.table b) (I.presentedRecord ω b))⁻¹
  long_uses_same_lookup : ∀ ω b y, longLookup ω b y = shortLookup ω b y
  row_nonneg : ∀ ω b y, 0 ≤ long ω b y
  row_mass : ∀ ω b, I.valid ω b → ∑ y, long ω b y = 1
  invalid_zero : ∀ ω b y, ¬ I.valid ω b → long ω b y = 0
  matching_deletion_bound : ∀ ω b c y, I.valid ω b → I.sameModeAndPrimary b c →
    long ω b y ≤ Real.exp (0.2 * (k : ℝ)) * I.deletionReference b c y
  low_cap : ∀ ω b y, I.valid ω b → I.low b →
    (N : ℝ) * long ω b y ≤ Real.exp ((m : ℝ) ^ (0.15 : ℝ))
  high_cap : ∀ ω b y, I.valid ω b → ¬ I.low b →
    (N : ℝ) * long ω b y ≤ (n : ℝ) ^ ((0.05 : ℝ) * (I.J : ℝ))
  common_hit_support : ∀ ω b y, I.valid ω b → 0 < long ω b y → I.commonNeighbor b y
  proxy_mean : ∀ b y,
    ∑ ω, (I.centerLaw b).w ω * proxy ω b y ≤ 2 * (I.prior b).w y
  long_short_mean : ∀ b y,
    (N : ℝ) * ∑ ω, (I.centerLaw b).w ω * long ω b y ≤
      (N : ℝ) * ∑ ω, (I.centerLaw b).w ω * proxy ω b y + (n : ℝ) ^ (-0.01 : ℝ)
  sign_locality : consultedSignRadius ≤ localityConstant * Nat.ceil (Real.sqrt (m : ℝ))
  radius_locality : ambientRadiusExcess ≤ localityConstant * Nat.ceil (Real.sqrt (m : ℝ))
  presentationEventsDisjoint : ∀ b ω r r',
    (I.table b).presented r ω → (I.table b).presented r' ω → r = r'

/-- L6.1j: selection-adjusted posteriors, their deletion/cap bounds, and the proxy/long comparison. -/
theorem L6_1j {n N m k : ℕ} {Odd Record Raw : Type*}
    [Fintype Odd] [DecidableEq Odd] [Fintype Record] [DecidableEq Record]
    [Fintype Raw] [DecidableEq Raw]
    (I : OddPosteriorInput6 n N m k Odd Record Raw)
    : Nonempty (SelectedOddRows6 I) := by
  sorry

end S06
end HypercubeRamsey
