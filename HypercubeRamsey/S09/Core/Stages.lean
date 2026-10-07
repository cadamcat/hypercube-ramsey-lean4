import HypercubeRamsey.S09.Core.Defs
import HypercubeRamsey.Framework.Hall

/-!
# Section 9 one-shot sub-nodes

Each P9.2 sub-node refers to the explicit finite experiment and row filters in
`Core.Defs`. The proof lane can replace each local `sorry` without reopening
the other construction steps. The final Hall bridge is assembled here.
-/

namespace HypercubeRamsey

open OAI.HypercubeRamsey Classical
open scoped BigOperators

/-- P9.2-tags (09:120–144): positive tag weights, inherited law supports and
widths, and masks contained in the second host side. -/
def tagSupport9 {P : Params9} {n N : ℕ} {E : Fin N → Fin N → Prop} {G : Colour}
    {M : TagMix N} {W : HeightWitness9 P n} {I : IDMap9 P n W}
    (S : TagExperiment9 P n N E G M W I) (X Y : Finset (Fin N)) : Prop :=
  (∀ z, 0 < M.Λ (S.tag z)) ∧
  (∀ id, (S.inputs.anchorLaw id).SupportedIn X ∧
    (S.inputs.anchorLaw id).WidthLE ((n : ℝ) ^ (P.xS : ℝ) +
      (P.hPlus : ℝ) * Real.log (n : ℝ) + 1)) ∧
  (∀ b, (baseSecondLaw9 S b).SupportedIn Y ∧
    (baseSecondLaw9 S b).WidthLE (P.Ss (n : ℝ))) ∧
  (∀ b A, (S.inputs.maskLaw b).w A ≠ 0 → A ⊆ Y)

/-- The flipped special word at coordinate `j`. -/
def flipSpecial9 {m : ℕ} (z : CubeVertex m) (j : Fin m) : CubeVertex m :=
  fun i => if i = j then !(z i) else z i

/-- The special-neighbour surplus used to choose tags in the linear case. -/
noncomputable def specialSurplus9 {P : Params9} {n N : ℕ}
    {E : Fin N → Fin N → Prop} {G : Colour} {M : TagMix N}
    {W : HeightWitness9 P n} {I : IDMap9 P n W}
    (S : TagExperiment9 P n N E G M W I) (z : CubeVertex W.specialBits)
    (x : Fin N) : ℝ :=
  ∑ j : Fin W.specialBits,
    (rowDeg E G x (M.ν (S.tag (flipSpecial9 z j))) - 1 / 2)

/-- The linear-only tag condition from 09:120–139. -/
noncomputable def linearTagCondition9 {P : Params9} {n N : ℕ}
    {E : Fin N → Fin N → Prop} {G : Colour} {M : TagMix N}
    {W : HeightWitness9 P n} {I : IDMap9 P n W}
    (S : TagExperiment9 P n N E G M W I) : Prop :=
  match P.case with
  | .sub _ _ _ => True
  | .lin _ _ _ _ =>
      ∀ z, 1 - Real.exp (-(localScale9 P n)) ≤
        ∑ x ∈ Finset.univ.filter (fun x =>
          -((1 / 20 : ℝ) * aStar9 P n * n) ≤ specialSurplus9 S z x),
          (M.μ (S.tag z)).w x

/-- L3.6c tag-load bound for the fixed first- and second-side laws. -/
def TagSliceLoadCertificate9 {P : Params9} {n N : ℕ}
    {E : Fin N → Fin N → Prop} {G : Colour} {M : TagMix N}
    {W : HeightWitness9 P n} {I : IDMap9 P n W}
    (S : TagExperiment9 P n N E G M W I) (κ : ℝ) : Prop :=
  (∀ x, (∑ z : CubeVertex W.specialBits, (M.μ (S.tag z)).w x) ≤
    (8 / κ) * ((2 : ℝ) ^ W.specialBits / N)) ∧
  (∀ y, (∑ z : CubeVertex W.specialBits, (M.ν (S.tag z)).w y) ≤
    (8 / κ) * ((2 : ℝ) ^ W.specialBits / N))

/-- P9.2-tags / L3.6c: expected filtered rows are dominated by their tagged
second law, with bounded total odd load. -/
def TagLoadCertificate9 {P : Params9} {n N : ℕ} {E : Fin N → Fin N → Prop}
    {G : Colour} {M : TagMix N} {W : HeightWitness9 P n} {I : IDMap9 P n W}
    (S : TagExperiment9 P n N E G M W I) (κ : ℝ) : Prop :=
  (∀ b y, rawRowMean9 S b y ≤
    (1 + Real.exp (-(localScale9 P n))) * (baseSecondLaw9 S b).w y) ∧
  (∀ y, rawOddLoad9 S y ≤
    (8 / κ) * ((2 : ℝ) ^ n / N) * (1 + Real.exp (-(localScale9 P n))))

/-- P9.2-reg (09:156–169): each even star has the three fixed prefix families
with high probability. The list orders are fixed by `starIDOrder9` and
`coreIDOrder9`; there is no assertion over arbitrary permutations. -/
def RegularityCertificate9 {P : Params9} {n N : ℕ} {E : Fin N → Fin N → Prop}
    {G : Colour} {M : TagMix N} {W : HeightWitness9 P n} {I : IDMap9 P n W}
    (S : TagExperiment9 P n N E G M W I) : Prop :=
  ∀ v : EvenSites9 n,
    1 - Real.exp (-(localScale9 P n)) ≤
      FinProb.pr (experimentLaw9 S.inputs) (fun ω => starRegular9 S ω v)

/-- P9.2-condmean (09:171–184): conditional target-last fraction versus the
target degree into Q filtered by the other core IDs. -/
def ConditionalMeanCertificate9 {P : Params9} {n N : ℕ}
    {E : Fin N → Fin N → Prop} {G : Colour} {M : TagMix N}
    {W : HeightWitness9 P n} {I : IDMap9 P n W}
    (S : TagExperiment9 P n N E G M W I) : Prop :=
  ∀ v b, b ∈ cubeNeighbors9 v.1 → ∀ ω₀,
    0 < coreHistoryMass9 S v ω₀ →
      |conditionalTargetMean9 S v b ω₀ - coreMeanDegree9 S v b ω₀| ≤
        ((I.core v).card : ℝ) * bStar9 P n ^ 2 + Real.exp (-(localScale9 P n))

/-- P9.2-erase (09:186–220): the core-free mean filter is close in L1 to a
small scalar multiple of the tagged second law. -/
def CoreErasureCertificate9 {P : Params9} {n N : ℕ}
    {E : Fin N → Fin N → Prop} {G : Colour} {M : TagMix N}
    {W : HeightWitness9 P n} {I : IDMap9 P n W}
    (S : TagExperiment9 P n N E G M W I) : Prop := erasedCoreMean9 S

/-- Covariance bounds at every ordered core prefix for one star. -/
noncomputable def starCovarianceGood9 {P : Params9} {n N : ℕ}
    {E : Fin N → Fin N → Prop} {G : Colour} {M : TagMix N}
    {W : HeightWitness9 P n} {I : IDMap9 P n W}
    (S : TagExperiment9 P n N E G M W I)
    (ω : ExperimentOutcome9 (m := W.specialBits) (n := n) (N := N) (H := W.levels))
    (v : EvenSites9 n) : Prop :=
  ∀ b ∈ cubeNeighbors9 v.1, ∀ before id after,
    coreIDOrder9 I v b = before ++ id :: after →
      |hitCovariance9 S ω v b before id| ≤
        aStar9 P n * (n : ℝ) ^ (-(2 * (P.χ : ℝ)))

/-- P9.2-cov (09:222–262): covariance bounds hold at every core prefix
outside an exponentially small part of the independent experiment. -/
def CovarianceCertificate9 {P : Params9} {n N : ℕ}
    {E : Fin N → Fin N → Prop} {G : Colour} {M : TagMix N}
    {W : HeightWitness9 P n} {I : IDMap9 P n W}
    (S : TagExperiment9 P n N E G M W I) : Prop :=
  ∀ v : EvenSites9 n,
    1 - Real.exp (-(localScale9 P n)) ≤
      FinProb.pr (experimentLaw9 S.inputs) (fun ω => starCovarianceGood9 S ω v)

/-- P9.2-gain (09:264–294): clipped target-last fractions have a positive
logarithmic surplus at each even star with high probability. -/
structure GainCertificate9 {P : Params9} {n N : ℕ}
    {E : Fin N → Fin N → Prop} {G : Colour} {M : TagMix N}
    {W : HeightWitness9 P n} {I : IDMap9 P n W}
    (S : TagExperiment9 P n N E G M W I) where
  c₄ : ℝ
  c₄_pos : 0 < c₄
  probability : ∀ v : EvenSites9 n,
    1 - Real.exp (-(localScale9 P n)) ≤
      FinProb.pr (experimentLaw9 S.inputs) (fun ω =>
        starRegular9 S ω v ∧
        starLogGain9 S ω v ≥ -(n : ℝ) * Real.log 2 + c₄ * n * aStar9 P n)

/-- The predictive likelihood of one local odd-label tuple under a proposed
target anchor. -/
noncomputable def predictiveLikelihood9 {P : Params9} {n N : ℕ}
    {E : Fin N → Fin N → Prop} {G : Colour} {M : TagMix N}
    {W : HeightWitness9 P n} {I : IDMap9 P n W}
    (S : TagExperiment9 P n N E G M W I)
    (ω : ExperimentOutcome9 (m := W.specialBits) (n := n) (N := N) (H := W.levels))
    (v : EvenSites9 n) (x : Fin N) (ys : StarLabels9 (n := n) (N := N) v) : ℝ :=
  ∏ b, (targetRowLaw9 S ω v b x).w (ys b)

/-- The deletion likelihood against which the predictive likelihood is tested. -/
noncomputable def deletionLikelihood9 {P : Params9} {n N : ℕ}
    {E : Fin N → Fin N → Prop} {G : Colour} {M : TagMix N}
    {W : HeightWitness9 P n} {I : IDMap9 P n W}
    (S : TagExperiment9 P n N E G M W I)
    (ω : ExperimentOutcome9 (m := W.specialBits) (n := n) (N := N) (H := W.levels))
    (v : EvenSites9 n) (ys : StarLabels9 (n := n) (N := N) v) : ℝ :=
  ∏ b, (deletionRowLaw9 S ω v b).w (ys b)

/-- The mixture predictive mass, integrating the proposed target anchor. -/
noncomputable def predictiveMass9 {P : Params9} {n N : ℕ}
    {E : Fin N → Fin N → Prop} {G : Colour} {M : TagMix N}
    {W : HeightWitness9 P n} {I : IDMap9 P n W}
    (S : TagExperiment9 P n N E G M W I)
    (ω : ExperimentOutcome9 (m := W.specialBits) (n := n) (N := N) (H := W.levels))
    (v : EvenSites9 n) (ys : StarLabels9 (n := n) (N := N) v) : ℝ :=
  ∑ x, (M.μ (vertexTag9 S v.1)).w x * predictiveLikelihood9 S ω v x ys

/-- A local tuple fails the predictive test when its mixture mass vanishes or
falls below the gain-scaled fraction of its deletion mass. -/
noncomputable def predictiveFailure9 {P : Params9} {n N : ℕ}
    {E : Fin N → Fin N → Prop} {G : Colour} {M : TagMix N}
    {W : HeightWitness9 P n} {I : IDMap9 P n W}
    (S : TagExperiment9 P n N E G M W I) (gain : GainCertificate9 S)
    (ω : ExperimentOutcome9 (m := W.specialBits) (n := n) (N := N) (H := W.levels))
    (v : EvenSites9 n) (ys : StarLabels9 (n := n) (N := N) v) : Prop :=
  predictiveMass9 S ω v ys = 0 ∨
    predictiveMass9 S ω v ys < Real.exp (-(gain.c₄ * n * aStar9 P n / 4)) *
      deletionLikelihood9 S ω v ys

/-- Probability of predictive failure in the independent deletion experiment. -/
noncomputable def predictiveFailureProbability9 {P : Params9} {n N : ℕ}
    {E : Fin N → Fin N → Prop} {G : Colour} {M : TagMix N}
    {W : HeightWitness9 P n} {I : IDMap9 P n W}
    (S : TagExperiment9 P n N E G M W I) (gain : GainCertificate9 S)
    (ω : ExperimentOutcome9 (m := W.specialBits) (n := n) (N := N) (H := W.levels))
    (v : EvenSites9 n) : ℝ :=
  FinProb.pr (deletionProductLaw9 S ω v) (predictiveFailure9 S gain ω v)

/-- P9.2-assignA: the gated-posterior estimate makes predictive failure
exponentially rare at every even star. -/
def PredictiveTailCertificate9 {P : Params9} {n N : ℕ}
    {E : Fin N → Fin N → Prop} {G : Colour} {M : TagMix N}
    {W : HeightWitness9 P n} {I : IDMap9 P n W}
    (S : TagExperiment9 P n N E G M W I) (gain : GainCertificate9 S) : Prop :=
  ∀ v : EvenSites9 n,
    1 - Real.exp (-(localScale9 P n)) ≤
      FinProb.pr (experimentLaw9 S.inputs) (fun ω =>
        starRegular9 S ω v ∧
        starLogGain9 S ω v ≥ -(n : ℝ) * Real.log 2 + gain.c₄ * n * aStar9 P n ∧
        predictiveFailureProbability9 S gain ω v ≤
          Real.exp (-(gain.c₄ * n * aStar9 P n / 8)))

/-- P9.2-assignA (09:296–320): a positive-probability anchor event on which
all even stars pass regularity/gain and predictive-tail tests. -/
structure AnchorAvoidanceCertificate9 {P : Params9} {n N : ℕ}
    {E : Fin N → Fin N → Prop} {G : Colour} {M : TagMix N}
    {W : HeightWitness9 P n} {I : IDMap9 P n W}
    (S : TagExperiment9 P n N E G M W I) (gain : GainCertificate9 S) where
  event : ExperimentOutcome9 (m := W.specialBits) (n := n) (N := N) (H := W.levels) → Prop
  probability : 0 < FinProb.pr (experimentLaw9 S.inputs) event
  good : ∀ ω, event ω → ∀ v : EvenSites9 n,
    starRegular9 S ω v ∧
      starLogGain9 S ω v ≥ -(n : ℝ) * Real.log 2 + gain.c₄ * n * aStar9 P n
  predictive_good : ∀ ω, event ω → ∀ v : EvenSites9 n,
    predictiveFailureProbability9 S gain ω v ≤
      Real.exp (-(gain.c₄ * n * aStar9 P n / 8))

/-- P9.2-map2 (09:102–118), with the ceiling choice for T made explicit so
later filter-width bounds can use both sides of the threshold. -/
theorem p92_bounded_idmap9 (P : Params9) (hP : P.Valid) (n : ℕ)
    (W : HeightWitness9 P n) : Nonempty (IDMap9 P n W) := by
  sorry

/-- P9.2-tags (09:120–144): choose the tags, anchors and masks, preserving
the tag-load inputs from P9.2-prep and the linear special-neighbour condition. -/
theorem p92_tags {P : Params9} {n N : ℕ} {E : Fin N → Fin N → Prop}
    {X Y : Finset (Fin N)} (κ : ℝ) (hκ : 0 < κ)
    (hP : P.Valid) (hn : 1 ≤ n) (hN : 0 < N)
    (hDeep : P.DeepAt n N E X Y) (hBroad : P.BroadAt n N E X Y)
    (hAvail : AvailableAt κ P.BiasProperty n N E X Y)
    (G : Colour) (M : TagMix N)
    (hM : M.Balanced (8 / κ) ∧
      ∀ i, 0 < M.Λ i → (M.μ i).SupportedIn X ∧ (M.ν i).SupportedIn Y ∧
        (M.μ i).WidthLE ((n : ℝ) ^ (P.xS : ℝ) +
          (P.hPlus : ℝ) * Real.log (n : ℝ) + 1) ∧
        (M.ν i).WidthLE (P.Ss (n : ℝ)) ∧
        ∀ x, (M.μ i).w x ≠ 0 →
          1 / 2 + (n : ℝ) ^ (-(P.hPlus : ℝ)) / 2 ≤ rowDeg E G x (M.ν i))
    (W : HeightWitness9 P n) (I : IDMap9 P n W) :
    ∃ S : TagExperiment9 P n N E G M W I,
      tagSupport9 S X Y ∧ TagSliceLoadCertificate9 S κ ∧ linearTagCondition9 S := by
  sorry

/-- P9.2-tags / L3.6c: transfer balanced tags and price-selected masks to
pointwise control of raw row laws and their odd total load. -/
theorem p92_tag_loads {P : Params9} {n N : ℕ} {E : Fin N → Fin N → Prop}
    {G : Colour} {M : TagMix N} {W : HeightWitness9 P n} {I : IDMap9 P n W}
    {X Y : Finset (Fin N)} (κ : ℝ) (S : TagExperiment9 P n N E G M W I)
    (hBal : M.Balanced (8 / κ)) (hSupport : tagSupport9 S X Y)
    (hSliceLoad : TagSliceLoadCertificate9 S κ) :
    TagLoadCertificate9 S κ := by
  sorry

/-- P9.2-reg (09:156–169): prefix-hit regularity in the three fixed ID orders,
using the deep discrepancy condition. -/
theorem p92_regularity {P : Params9} {n N : ℕ} {E : Fin N → Fin N → Prop}
    {G : Colour} {M : TagMix N} {W : HeightWitness9 P n} {I : IDMap9 P n W}
    {X Y : Finset (Fin N)} {C₀ : ℝ}
    (S : TagExperiment9 P n N E G M W I) (hP : P.Valid)
    (hLarge : LargeAt 1 C₀ n N)
    (hn : 1 ≤ n) (hDeep : P.DeepAt n N E X Y)
    (hSupport : tagSupport9 S X Y) : RegularityCertificate9 S := by
  sorry

/-- P9.2-condmean (09:171–184): condition the target-last fraction on the core
anchors and compare it to the averaged outer-filter law. -/
theorem p92_conditional_mean {P : Params9} {n N : ℕ}
    {E : Fin N → Fin N → Prop} {G : Colour} {M : TagMix N}
    {W : HeightWitness9 P n} {I : IDMap9 P n W}
    (S : TagExperiment9 P n N E G M W I) (hRegular : RegularityCertificate9 S) :
    ConditionalMeanCertificate9 S := by
  sorry

/-- P9.2-erase (09:186–220): remove the core's effect from the averaged mean
filter, with a bounded scalar correction and exponentially small L1 error. -/
theorem p92_erase_core {P : Params9} {n N : ℕ} {κ : ℝ}
    {E : Fin N → Fin N → Prop} {G : Colour} {M : TagMix N}
    {W : HeightWitness9 P n} {I : IDMap9 P n W}
    (S : TagExperiment9 P n N E G M W I) (hRegular : RegularityCertificate9 S)
    (hMean : ConditionalMeanCertificate9 S) (hLoad : TagLoadCertificate9 S κ) :
    CoreErasureCertificate9 S := by
  sorry

/-- P9.2-cov (09:222–262): use the signed-test argument to control the
covariance at every unmasked core prefix. -/
theorem p92_covariance {P : Params9} {n N : ℕ} {E : Fin N → Fin N → Prop}
    {G : Colour} {M : TagMix N} {W : HeightWitness9 P n} {I : IDMap9 P n W}
    {X Y : Finset (Fin N)} (S : TagExperiment9 P n N E G M W I) (hP : P.Valid)
    (hn : 1 ≤ n) (hDeep : P.DeepAt n N E X Y)
    (hRegular : RegularityCertificate9 S) (hMean : ConditionalMeanCertificate9 S)
    (hErase : CoreErasureCertificate9 S) : CovarianceCertificate9 S := by
  sorry

/-- P9.2-gain (09:264–294): combine conditional means, core erasure,
covariance cancellation, tag surpluses, and X-Finner concentration. -/
theorem p92_gain {P : Params9} {n N : ℕ} {κ : ℝ}
    {E : Fin N → Fin N → Prop} {G : Colour} {M : TagMix N}
    {W : HeightWitness9 P n} {I : IDMap9 P n W}
    (S : TagExperiment9 P n N E G M W I) (hP : P.Valid)
    (hRegular : RegularityCertificate9 S) (hTags : linearTagCondition9 S)
    (hLoad : TagLoadCertificate9 S κ)
    (hMean : ConditionalMeanCertificate9 S) (hErase : CoreErasureCertificate9 S)
    (hCov : CovarianceCertificate9 S) : Nonempty (GainCertificate9 S) := by
  sorry

/-- P9.2-assignA (09:296–320): the gated-posterior estimate bounds the
probability of predictive failure under each star's deletion product law. -/
theorem p92_predictive_tests {P : Params9} {n N : ℕ}
    {E : Fin N → Fin N → Prop} {G : Colour} {M : TagMix N}
    {W : HeightWitness9 P n} {I : IDMap9 P n W}
    (S : TagExperiment9 P n N E G M W I) (hP : P.Valid)
    (hRegular : RegularityCertificate9 S) (gain : GainCertificate9 S) :
    PredictiveTailCertificate9 S gain := by
  sorry

/-- P9.2-assignA (09:296–320): predictive tests and conditional avoidance
select a positive-probability anchor event on all even stars. -/
theorem p92_anchor_avoidance {P : Params9} {n N : ℕ}
    {E : Fin N → Fin N → Prop} {G : Colour} {M : TagMix N}
    {W : HeightWitness9 P n} {I : IDMap9 P n W}
    (S : TagExperiment9 P n N E G M W I) (hP : P.Valid) (hn : 1 ≤ n)
    (hTags : linearTagCondition9 S) (hRegular : RegularityCertificate9 S)
    (hGain : GainCertificate9 S) (hPredictive : PredictiveTailCertificate9 S hGain) :
    Nonempty (AnchorAvoidanceCertificate9 S hGain) := by
  sorry

/-- P9.2-assignB (09:322–329): predictive avoidance and scattered moments
produce odd candidate rows with normalized column loads. -/
theorem p92_odd_candidates {P : Params9} {n N : ℕ}
    {E : Fin N → Fin N → Prop} {G : Colour} {M : TagMix N}
    {W : HeightWitness9 P n} {I : IDMap9 P n W}
    {X Y : Finset (Fin N)} (S : TagExperiment9 P n N E G M W I)
    (κ C₀ : ℝ) (hC₀ : 32 / κ ≤ C₀) (hLarge : LargeAt 1 C₀ n N)
    (hSupport : tagSupport9 S X Y) (hLoad : TagLoadCertificate9 S κ)
    {gain : GainCertificate9 S} (hAvoid : AnchorAvoidanceCertificate9 S gain) :
    Nonempty (OddCandidates9 S Y) := by
  sorry

/-- P9.2-assignB (09:322–329): combine the predictive avoidance events with
the odd load bounds to choose an accepted odd injection. -/
theorem p92_odd_injection {P : Params9} {n N : ℕ} {E : Fin N → Fin N → Prop}
    {G : Colour} {M : TagMix N} {W : HeightWitness9 P n} {I : IDMap9 P n W}
    {X Y : Finset (Fin N)} (S : TagExperiment9 P n N E G M W I)
    (κ : ℝ) (hκ : 0 < κ) (hP : P.Valid) (hn : 1 ≤ n)
    (C₀ : ℝ) (hLarge : LargeAt 1 C₀ n N)
    (hDeep : P.DeepAt n N E X Y) (hBroad : P.BroadAt n N E X Y)
    (hAvail : AvailableAt κ P.BiasProperty n N E X Y)
    (hSupport : tagSupport9 S X Y) (hTags : linearTagCondition9 S)
    (hLoad : TagLoadCertificate9 S κ) (hGain : GainCertificate9 S)
    (hAvoid : AnchorAvoidanceCertificate9 S hGain)
    (C : OddCandidates9 S Y) :
    Nonempty (OddInjection9 (n := n) (N := N) (E := E) (G := G) X Y) := by
  sorry

/-- P9.2-assignC (09:331–350): posterior even rows are supported on labels in
X adjacent to the fixed odd injection and have column load at most one. -/
theorem p92_even_rows {P : Params9} {n N : ℕ} {E : Fin N → Fin N → Prop}
    {G : Colour} {M : TagMix N} {W : HeightWitness9 P n} {I : IDMap9 P n W}
    (S : TagExperiment9 P n N E G M W I) (X Y : Finset (Fin N))
    (odd : OddInjection9 (n := n) (N := N) (E := E) (G := G) X Y) (hP : P.Valid)
    (κ : ℝ) (hκ : 0 < κ) (hn : 1 ≤ n)
    (C₀ : ℝ) (hLarge : LargeAt 1 C₀ n N)
    (hDeep : P.DeepAt n N E X Y) (hBroad : P.BroadAt n N E X Y)
    (hAvail : AvailableAt κ P.BiasProperty n N E X Y)
    (hTags : linearTagCondition9 S) (hLoad : TagLoadCertificate9 S κ)
    (hGain : GainCertificate9 S) (hAvoid : AnchorAvoidanceCertificate9 S hGain) :
    Nonempty (EvenRows9 (n := n) (N := N)
      (E := E) (G := G) X Y odd) := by
  sorry

/-- P9.2-assignC / F-HallEmbed: turn the fractional even rows into an
injective assignment, then use the parity-copy bridge. -/
theorem p92_hall_embed {n N : ℕ} {E : Fin N → Fin N → Prop} {G : Colour}
    (X Y : Finset (Fin N))
    (odd : OddInjection9 (n := n) (N := N) (E := E) (G := G) X Y)
    (rows : EvenRows9 (n := n) (N := N) (E := E) (G := G) X Y odd) : CubeAt n N E := by
  classical
  obtain ⟨even, heven, hmem⟩ := exists_injective_of_fractional
    rows.weight rows.candidate rows.nonnegative rows.row_sum rows.supported rows.column_load
  have hedge : ∀ a b, (cube n).Adj a.1 b.1 → Hits E G (even a) (odd.label b) := by
    intro a b hadj
    exact rows.edge a b (even a) hadj (hmem a)
  refine ⟨G, ?_⟩
  exact cube_copy_of_parts even odd.label heven odd.injective hedge

end HypercubeRamsey
