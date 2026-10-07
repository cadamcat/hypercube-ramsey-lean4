import HypercubeRamsey.S09.Needs

/-!
# Concrete objects for the Section 9 one-shot construction

This file fixes the finite random experiment used by the tags, anchor, mask,
and row-filter steps.  The certificates proved in `Core.Stages` refer to these
objects, rather than to an unspecified one-shot embedding package.
-/

namespace HypercubeRamsey

open OAI.HypercubeRamsey Classical
open scoped BigOperators

private def centerIDEquiv (m n H : ℕ) :
    CenterID9 m n H ≃ CubeVertex m × CubeVertex n × Fin (H + 1) where
  toFun c := (c.slice, c.location, c.level)
  invFun p := ⟨p.1, p.2.1, p.2.2⟩
  left_inv c := by cases c; rfl
  right_inv p := by cases p with | mk a bc => cases bc with | mk b c => rfl

noncomputable instance instFintypeCenterID9 (m n H : ℕ) : Fintype (CenterID9 m n H) :=
  Fintype.ofEquiv (CubeVertex m × CubeVertex n × Fin (H + 1)) (centerIDEquiv m n H).symm

/-- The even vertices of the cube, viewed as a finite row index type. -/
abbrev EvenSites9 (n : ℕ) := {v : CubeVertex n // IsEvenRole v}

/-- The odd vertices of the cube, viewed as a finite row index type. -/
abbrev OddSites9 (n : ℕ) := {v : CubeVertex n // ¬ IsEvenRole v}

/-- The neighbours of one cube vertex, as a finite set. -/
noncomputable def cubeNeighbors9 {n : ℕ} (v : CubeVertex n) : Finset (CubeVertex n) :=
  Finset.univ.filter fun b => (cube n).Adj v b

/-- P9.2-map2's centre map and its per-even-vertex core. -/
structure IDMap9 (P : Params9) (n : ℕ) (W : HeightWitness9 P n) where
  threshold : ℕ
  threshold_lower : (n : ℝ) ^ (1 - (P.σ : ℝ) + W.ε) ≤ threshold
  threshold_upper : (threshold : ℝ) ≤
    (n : ℝ) ^ (1 - (P.σ : ℝ) + W.ε) + 1
  center : CubeVertex n → CenterID9 W.specialBits n W.levels
  center_spec : ∀ v, (center v).slice = specialWord9 W.specialBits_le v ∧
    residualDistance9 W.specialBits (center v).location v ≤ W.radius ∧
    (center v).level = W.height v ∧ center v ∈ W.active
  odd_seen_card : ∀ b, ¬ IsEvenRole b → (seenIDs9 center b).card ≤ threshold + W.specialBits
  core : EvenSites9 n → Finset (CenterID9 W.specialBits n W.levels)
  center_mem_core : ∀ v, center v.1 ∈ core v
  core_card : ∀ v, ((core v).card : ℝ) ≤ (n : ℝ) ^ (P.χ : ℝ)
  read_bound : ∀ v id, id ∉ core v →
    (Finset.univ.filter fun b : CubeVertex n =>
      ¬ IsEvenRole b ∧ (cube n).Adj v.1 b ∧ id ∈ seenIDs9 center b).card ≤ W.radius + 3

/-- One outcome records all anchors and all row masks. -/
abbrev ExperimentOutcome9 {m n N H : ℕ} :=
  (CenterID9 m n H → Fin N) × (CubeVertex n → Finset (Fin N))

/-- The independent input laws for the anchors and masks. -/
structure ExperimentInputs9 {m n N H : ℕ} where
  anchorLaw : CenterID9 m n H → Law N
  maskLaw : CubeVertex n → FinProb (Finset (Fin N))

/-- The product law of all independent anchors and masks. -/
noncomputable def experimentLaw9 {m n N H : ℕ} (I : ExperimentInputs9 (m := m) (n := n) (N := N) (H := H)) :
    FinProb (ExperimentOutcome9 (m := m) (n := n) (N := N) (H := H)) := by
  classical
  exact FinProb.bind (FinProb.pi I.anchorLaw) (fun _ => FinProb.pi I.maskLaw)

/-- Read the sampled anchor named by an ID. -/
def anchorValue9 {m n N H : ℕ}
    (ω : ExperimentOutcome9 (m := m) (n := n) (N := N) (H := H))
    (id : CenterID9 m n H) : Fin N := ω.1 id

/-- Read the sampled mask for one cube row. -/
def maskValue9 {m n N H : ℕ}
    (ω : ExperimentOutcome9 (m := m) (n := n) (N := N) (H := H))
    (b : CubeVertex n) : Finset (Fin N) := ω.2 b

/-- Fixed tags, independent anchor laws, and independent row-mask laws. -/
structure TagExperiment9 (P : Params9) (n N : ℕ)
    (E : Fin N → Fin N → Prop) (G : Colour) (M : TagMix N)
    (W : HeightWitness9 P n) (I : IDMap9 P n W) where
  tag : CubeVertex W.specialBits → M.ι
  inputs : ExperimentInputs9 (m := W.specialBits) (n := n) (N := N) (H := W.levels)
  anchorLaw_eq : ∀ id, inputs.anchorLaw id = M.μ (tag id.slice)
  mask_mass : ∀ b A, (inputs.maskLaw b).w A ≠ 0 →
    (Real.exp (-(n : ℝ) ^ ((P.xS : ℝ) / 2)) / 2) ≤
      ∑ y ∈ A, (M.ν (tag (specialWord9 W.specialBits_le b))).w y

/-- The tag chosen for the special slice of a cube vertex. -/
def vertexTag9 {P : Params9} {n N : ℕ} {E : Fin N → Fin N → Prop} {G : Colour}
    {M : TagMix N} {W : HeightWitness9 P n} {I : IDMap9 P n W}
    (S : TagExperiment9 P n N E G M W I) (v : CubeVertex n) : M.ι :=
  S.tag (specialWord9 W.specialBits_le v)

/-- The unmasked second-side law prescribed by a vertex's special-slice tag. -/
def baseSecondLaw9 {P : Params9} {n N : ℕ} {E : Fin N → Fin N → Prop} {G : Colour}
    {M : TagMix N} {W : HeightWitness9 P n} {I : IDMap9 P n W}
    (S : TagExperiment9 P n N E G M W I) (b : CubeVertex n) : Law N :=
  M.ν (vertexTag9 S b)

/-- Restrict a law to a set when possible, and use the original law on an empty filter. -/
noncomputable def restrictOrBase9 {N : ℕ} (μ : Law N) (A : Finset (Fin N)) : Law N := by
  classical
  by_cases h : 0 < ∑ x ∈ A, μ.w x
  · exact μ.restrict A h
  · exact μ

/-- Labels surviving the hits of a specified finite set of IDs. -/
noncomputable def hitSet9 {P : Params9} {n N : ℕ} {E : Fin N → Fin N → Prop} {G : Colour}
    {M : TagMix N} {W : HeightWitness9 P n} {I : IDMap9 P n W}
    (S : TagExperiment9 P n N E G M W I)
    (ω : ExperimentOutcome9 (m := W.specialBits) (n := n) (N := N) (H := W.levels))
    (ids : Finset (CenterID9 W.specialBits n W.levels)) : Finset (Fin N) := by
  classical
  exact Finset.univ.filter fun y => ∀ id ∈ ids, Hits E G (anchorValue9 ω id) y

/-- Apply the hits in an ID list in its specified order, with a fallback at empty filters. -/
noncomputable def filterListLaw9 {P : Params9} {n N : ℕ} {E : Fin N → Fin N → Prop}
    {G : Colour} {M : TagMix N} {W : HeightWitness9 P n} {I : IDMap9 P n W}
    (S : TagExperiment9 P n N E G M W I)
    (ω : ExperimentOutcome9 (m := W.specialBits) (n := n) (N := N) (H := W.levels))
    (b : CubeVertex n) (μ : Law N) (ids : List (CenterID9 W.specialBits n W.levels)) : Law N := by
  classical
  exact ids.foldl (fun current id =>
    restrictOrBase9 current ((Finset.univ.filter fun y => Hits E G (anchorValue9 ω id) y))) μ

/-- The sampled mask law restricted to the mask, using the stipulated nonempty fallback. -/
noncomputable def maskedBaseLaw9 {P : Params9} {n N : ℕ} {E : Fin N → Fin N → Prop}
    {G : Colour} {M : TagMix N} {W : HeightWitness9 P n} {I : IDMap9 P n W}
    (S : TagExperiment9 P n N E G M W I)
    (ω : ExperimentOutcome9 (m := W.specialBits) (n := n) (N := N) (H := W.levels))
    (b : CubeVertex n) : Law N :=
  restrictOrBase9 (baseSecondLaw9 S b) (maskValue9 ω b)

/-- The actual row law: its mask followed by the full set of observed-ID hits. -/
noncomputable def filteredRowLaw9 {P : Params9} {n N : ℕ} {E : Fin N → Fin N → Prop}
    {G : Colour} {M : TagMix N} {W : HeightWitness9 P n} {I : IDMap9 P n W}
    (S : TagExperiment9 P n N E G M W I)
    (ω : ExperimentOutcome9 (m := W.specialBits) (n := n) (N := N) (H := W.levels))
    (b : CubeVertex n) : Law N :=
  restrictOrBase9 (maskedBaseLaw9 S ω b) (hitSet9 S ω (seenIDs9 I.center b))

/-- The fixed deterministic ID order for an even star: outer IDs, core IDs other
than the target, then the target ID. -/
noncomputable def starIDOrder9 {P : Params9} {n : ℕ} {W : HeightWitness9 P n}
    (I : IDMap9 P n W) (v : EvenSites9 n) (b : CubeVertex n) :
    List (CenterID9 W.specialBits n W.levels) :=
  let observed := seenIDs9 I.center b
  let outer := observed \ I.core v
  let coreOther := (observed ∩ I.core v).erase (I.center v.1)
  outer.toList ++ coreOther.toList ++ [I.center v.1]

/-- The core-only ID order used in the covariance telescoping argument. -/
noncomputable def coreIDOrder9 {P : Params9} {n : ℕ} {W : HeightWitness9 P n}
    (I : IDMap9 P n W) (v : EvenSites9 n) (b : CubeVertex n) :
    List (CenterID9 W.specialBits n W.levels) :=
  ((seenIDs9 I.center b ∩ I.core v).erase (I.center v.1)).toList

/-- The odd rows around one even cube vertex. -/
abbrev StarOddSites9 {n : ℕ} (v : EvenSites9 n) :=
  {b : OddSites9 n // (cube n).Adj v.1 b.1}

/-- Assign one host label to every odd neighbour of an even vertex. -/
abbrev StarLabels9 {n N : ℕ} (v : EvenSites9 n) := StarOddSites9 v → Fin N

/-- The deletion kernel at an odd row: apply its mask and all observed ID hits
except for the target even vertex's ID. -/
noncomputable def deletionRowLaw9 {P : Params9} {n N : ℕ}
    {E : Fin N → Fin N → Prop} {G : Colour} {M : TagMix N}
    {W : HeightWitness9 P n} {I : IDMap9 P n W}
    (S : TagExperiment9 P n N E G M W I)
    (ω : ExperimentOutcome9 (m := W.specialBits) (n := n) (N := N) (H := W.levels))
    (v : EvenSites9 n) (b : StarOddSites9 v) : Law N :=
  let order := starIDOrder9 I v b.1.1
  filterListLaw9 S ω b.1.1 (maskedBaseLaw9 S ω b.1.1)
    (order.take (order.length - 1))

/-- The row kernel after imposing a hypothetical target anchor `x`. -/
noncomputable def targetRowLaw9 {P : Params9} {n N : ℕ}
    {E : Fin N → Fin N → Prop} {G : Colour} {M : TagMix N}
    {W : HeightWitness9 P n} {I : IDMap9 P n W}
    (S : TagExperiment9 P n N E G M W I)
    (ω : ExperimentOutcome9 (m := W.specialBits) (n := n) (N := N) (H := W.levels))
    (v : EvenSites9 n) (b : StarOddSites9 v) (x : Fin N) : Law N := by
  classical
  exact restrictOrBase9 (deletionRowLaw9 S ω v b)
    (Finset.univ.filter fun y => Hits E G x y)

/-- The product of deletion kernels used to evaluate the predictive test. -/
noncomputable def deletionProductLaw9 {P : Params9} {n N : ℕ}
    {E : Fin N → Fin N → Prop} {G : Colour} {M : TagMix N}
    {W : HeightWitness9 P n} {I : IDMap9 P n W}
    (S : TagExperiment9 P n N E G M W I)
    (ω : ExperimentOutcome9 (m := W.specialBits) (n := n) (N := N) (H := W.levels))
    (v : EvenSites9 n) : FinProb (StarLabels9 (n := n) (N := N) v) := by
  classical
  exact FinProb.pi (fun b => deletionRowLaw9 S ω v b)

/-- The preceding filtered second law at a prefix of the fixed order. -/
noncomputable def prefixLaw9 {P : Params9} {n N : ℕ} {E : Fin N → Fin N → Prop}
    {G : Colour} {M : TagMix N} {W : HeightWitness9 P n} {I : IDMap9 P n W}
    (S : TagExperiment9 P n N E G M W I)
    (ω : ExperimentOutcome9 (m := W.specialBits) (n := n) (N := N) (H := W.levels))
    (b : CubeVertex n) (μ : Law N) (order : List (CenterID9 W.specialBits n W.levels))
    (k : ℕ) : Law N :=
  filterListLaw9 S ω b μ (order.take k)

/-- The fraction of a current second law retained by the next anchor hit. -/
noncomputable def hitFraction9 {P : Params9} {n N : ℕ} {E : Fin N → Fin N → Prop}
    {G : Colour} {M : TagMix N} {W : HeightWitness9 P n} {I : IDMap9 P n W}
    (S : TagExperiment9 P n N E G M W I)
    (ω : ExperimentOutcome9 (m := W.specialBits) (n := n) (N := N) (H := W.levels))
    (id : CenterID9 W.specialBits n W.levels) (μ : Law N) : ℝ :=
  rowDeg E G (anchorValue9 ω id) μ

/-- The target-last hit fraction after all other IDs in the even star have been
filtered, as used in the gain estimate. -/
noncomputable def targetFraction9 {P : Params9} {n N : ℕ} {E : Fin N → Fin N → Prop}
    {G : Colour} {M : TagMix N} {W : HeightWitness9 P n} {I : IDMap9 P n W}
    (S : TagExperiment9 P n N E G M W I)
    (ω : ExperimentOutcome9 (m := W.specialBits) (n := n) (N := N) (H := W.levels))
    (v : EvenSites9 n) (b : CubeVertex n) : ℝ :=
  let order := starIDOrder9 I v b
  let preceding := order.take (order.length - 1)
  hitFraction9 S ω (I.center v.1)
    (filterListLaw9 S ω b (maskedBaseLaw9 S ω b) preceding)

/-- The sum of log gains around one even star. -/
noncomputable def starLogGain9 {P : Params9} {n N : ℕ} {E : Fin N → Fin N → Prop}
    {G : Colour} {M : TagMix N} {W : HeightWitness9 P n} {I : IDMap9 P n W}
    (S : TagExperiment9 P n N E G M W I)
    (ω : ExperimentOutcome9 (m := W.specialBits) (n := n) (N := N) (H := W.levels))
    (v : EvenSites9 n) : ℝ :=
  ∑ b ∈ cubeNeighbors9 v.1, Real.log (targetFraction9 S ω v b)

/-- Fixed-core history for an outcome: all anchors named by this even vertex's
core agree with the reference outcome. -/
def sameCoreHistory9 {P : Params9} {n N : ℕ} {E : Fin N → Fin N → Prop}
    {G : Colour} {M : TagMix N} {W : HeightWitness9 P n} {I : IDMap9 P n W}
    (S : TagExperiment9 P n N E G M W I)
    (v : EvenSites9 n)
    (ω₀ ω : ExperimentOutcome9 (m := W.specialBits) (n := n) (N := N) (H := W.levels)) : Prop :=
  ∀ id ∈ I.core v, anchorValue9 ω id = anchorValue9 ω₀ id

/-- The outer-filter mean law Q, averaged over the independent row mask and
outside-core anchors. Core coordinates are ignored by this definition. -/
noncomputable def outerMeanLaw9 {P : Params9} {n N : ℕ} {E : Fin N → Fin N → Prop}
    {G : Colour} {M : TagMix N} {W : HeightWitness9 P n} {I : IDMap9 P n W}
    (S : TagExperiment9 P n N E G M W I) (v : EvenSites9 n) (b : CubeVertex n) : Law N := by
  classical
  let outer := seenIDs9 I.center b \ I.core v
  exact Law.mix (experimentLaw9 S.inputs) (fun ω =>
    filterListLaw9 S ω b (maskedBaseLaw9 S ω b) outer.toList)

/-- Q filtered by the fixed core anchors other than the target ID. -/
noncomputable def meanCoreLaw9 {P : Params9} {n N : ℕ} {E : Fin N → Fin N → Prop}
    {G : Colour} {M : TagMix N} {W : HeightWitness9 P n} {I : IDMap9 P n W}
    (S : TagExperiment9 P n N E G M W I)
    (ω : ExperimentOutcome9 (m := W.specialBits) (n := n) (N := N) (H := W.levels))
    (v : EvenSites9 n) (b : CubeVertex n) : Law N :=
  filterListLaw9 S ω b (outerMeanLaw9 S v b) (coreIDOrder9 I v b)

/-- The real parameter scales used by the one-shot estimates. -/
noncomputable def aStar9 (P : Params9) (n : ℕ) : ℝ :=
  (n : ℝ) ^ (-(P.hPlus : ℝ)) / 2

noncomputable def bStar9 (P : Params9) (n : ℕ) : ℝ :=
  (n : ℝ) ^ (-(P.hMinus : ℝ))

noncomputable def localScale9 (P : Params9) (n : ℕ) : ℝ :=
  (n : ℝ) ^ ((P.xS : ℝ) / 2)

/-- Prefix regularity tests for one fixed order. Every earlier hit must retain
at least .49, and the next hit must have degree within `2 b_*` of one half. -/
noncomputable def orderRegular9 {P : Params9} {n N : ℕ} {E : Fin N → Fin N → Prop} {G : Colour}
    {M : TagMix N} {W : HeightWitness9 P n} {I : IDMap9 P n W}
    (S : TagExperiment9 P n N E G M W I)
    (ω : ExperimentOutcome9 (m := W.specialBits) (n := n) (N := N) (H := W.levels))
    (b : CubeVertex n) (base : Law N) (order : List (CenterID9 W.specialBits n W.levels)) : Prop :=
  ∀ before id after, order = before ++ id :: after →
    (∀ earlier id₀ tail, before = earlier ++ id₀ :: tail →
      (49 / 100 : ℝ) ≤ hitFraction9 S ω id₀
        (filterListLaw9 S ω b base earlier)) →
      |hitFraction9 S ω id (filterListLaw9 S ω b base before) - 1 / 2| ≤
        2 * bStar9 P n

/-- The three deterministic order tests from the paper: masked and unmasked
outer/core orders, plus the unmasked core-only order. -/
noncomputable def starRegular9 {P : Params9} {n N : ℕ} {E : Fin N → Fin N → Prop} {G : Colour}
    {M : TagMix N} {W : HeightWitness9 P n} {I : IDMap9 P n W}
    (S : TagExperiment9 P n N E G M W I)
    (ω : ExperimentOutcome9 (m := W.specialBits) (n := n) (N := N) (H := W.levels))
    (v : EvenSites9 n) : Prop :=
  ∀ b ∈ cubeNeighbors9 v.1,
    orderRegular9 S ω b (maskedBaseLaw9 S ω b) (starIDOrder9 I v b) ∧
    orderRegular9 S ω b (baseSecondLaw9 S b) (starIDOrder9 I v b) ∧
    orderRegular9 S ω b (baseSecondLaw9 S b) (coreIDOrder9 I v b)

/-- Probability that a specified core history occurs. -/
noncomputable def coreHistoryMass9 {P : Params9} {n N : ℕ} {E : Fin N → Fin N → Prop}
    {G : Colour} {M : TagMix N} {W : HeightWitness9 P n} {I : IDMap9 P n W}
    (S : TagExperiment9 P n N E G M W I) (v : EvenSites9 n)
    (ω₀ : ExperimentOutcome9 (m := W.specialBits) (n := n) (N := N) (H := W.levels)) : ℝ :=
  FinProb.pr (experimentLaw9 S.inputs) (fun ω => sameCoreHistory9 S v ω₀ ω)

/-- Conditional mean of the target-last fraction given all core anchors. -/
noncomputable def conditionalTargetMean9 {P : Params9} {n N : ℕ}
    {E : Fin N → Fin N → Prop} {G : Colour} {M : TagMix N}
    {W : HeightWitness9 P n} {I : IDMap9 P n W}
    (S : TagExperiment9 P n N E G M W I) (v : EvenSites9 n)
    (b : CubeVertex n) (ω₀ : ExperimentOutcome9 (m := W.specialBits) (n := n) (N := N) (H := W.levels)) : ℝ :=
  FinProb.condExp (experimentLaw9 S.inputs) (fun ω => targetFraction9 S ω v b)
    (fun ω => sameCoreHistory9 S v ω₀ ω)

/-- The deterministic mean degree after applying the core hits to Q. -/
noncomputable def coreMeanDegree9 {P : Params9} {n N : ℕ}
    {E : Fin N → Fin N → Prop} {G : Colour} {M : TagMix N}
    {W : HeightWitness9 P n} {I : IDMap9 P n W}
    (S : TagExperiment9 P n N E G M W I) (v : EvenSites9 n)
    (b : CubeVertex n) (ω₀ : ExperimentOutcome9 (m := W.specialBits) (n := n) (N := N) (H := W.levels)) : ℝ :=
  rowDeg E G (anchorValue9 ω₀ (I.center v.1)) (meanCoreLaw9 S ω₀ v b)

/-- Total-variation error (in the unnormalised L1 convention) in erasing the
core from the mean filter. -/
def erasedCoreMean9 {P : Params9} {n N : ℕ} {E : Fin N → Fin N → Prop} {G : Colour}
    {M : TagMix N} {W : HeightWitness9 P n} {I : IDMap9 P n W}
    (S : TagExperiment9 P n N E G M W I) : Prop :=
  ∀ v b, b ∈ cubeNeighbors9 v.1 → ∃ ψ : ℝ, |ψ| ≤ 4 * (I.core v).card * bStar9 P n ∧
    (∑ y, |(outerMeanLaw9 S v b).w y - (1 + ψ) * (baseSecondLaw9 S b).w y|) ≤
      Real.exp (-(localScale9 P n))

/-- A covariance at a core prefix between the next anchor-hit indicator and
the target anchor-hit indicator. -/
noncomputable def hitCovariance9 {P : Params9} {n N : ℕ}
    {E : Fin N → Fin N → Prop} {G : Colour} {M : TagMix N}
    {W : HeightWitness9 P n} {I : IDMap9 P n W}
    (S : TagExperiment9 P n N E G M W I)
    (ω : ExperimentOutcome9 (m := W.specialBits) (n := n) (N := N) (H := W.levels))
    (v : EvenSites9 n) (b : CubeVertex n) (before : List (CenterID9 W.specialBits n W.levels))
    (id : CenterID9 W.specialBits n W.levels) : ℝ := by
  classical
  let μ := filterListLaw9 S ω b (baseSecondLaw9 S b) before
  let f : Fin N → ℝ := fun y => if Hits E G (anchorValue9 ω id) y then 1 else 0
  let g : Fin N → ℝ := fun y => if Hits E G (anchorValue9 ω (I.center v.1)) y then 1 else 0
  exact FinProb.expect μ (fun y => f y * g y) -
    FinProb.expect μ f * FinProb.expect μ g

/-- The clipped target-last fractions used in the log-gain estimate. -/
noncomputable def clippedTargetFraction9 {P : Params9} {n N : ℕ}
    {E : Fin N → Fin N → Prop} {G : Colour} {M : TagMix N}
    {W : HeightWitness9 P n} {I : IDMap9 P n W}
    (S : TagExperiment9 P n N E G M W I)
    (ω : ExperimentOutcome9 (m := W.specialBits) (n := n) (N := N) (H := W.levels))
    (v : EvenSites9 n) (b : CubeVertex n) : ℝ :=
  min (1 / 2 + 2 * bStar9 P n)
    (max (1 / 2 - 2 * bStar9 P n) (targetFraction9 S ω v b))

/-- Odd rows with their actual filtered law. -/
noncomputable def oddRowLoad9 {P : Params9} {n N : ℕ} {E : Fin N → Fin N → Prop} {G : Colour}
    {M : TagMix N} {W : HeightWitness9 P n} {I : IDMap9 P n W}
    (S : TagExperiment9 P n N E G M W I)
    (ω : ExperimentOutcome9 (m := W.specialBits) (n := n) (N := N) (H := W.levels))
    (y : Fin N) : ℝ :=
  ∑ b ∈ Finset.univ.filter (fun b : CubeVertex n => ¬ IsEvenRole b),
    (filteredRowLaw9 S ω b).w y

/-- The row marginal of the raw independent experiment. -/
noncomputable def rawRowMean9 {P : Params9} {n N : ℕ}
    {E : Fin N → Fin N → Prop} {G : Colour} {M : TagMix N}
    {W : HeightWitness9 P n} {I : IDMap9 P n W}
    (S : TagExperiment9 P n N E G M W I) (b : CubeVertex n) (y : Fin N) : ℝ :=
  FinProb.expect (experimentLaw9 S.inputs) (fun ω => (filteredRowLaw9 S ω b).w y)

/-- The unconditional law of one row after averaging its independent masks and anchors. -/
noncomputable def rawRowLaw9 {P : Params9} {n N : ℕ}
    {E : Fin N → Fin N → Prop} {G : Colour} {M : TagMix N}
    {W : HeightWitness9 P n} {I : IDMap9 P n W}
    (S : TagExperiment9 P n N E G M W I) (b : CubeVertex n) : Law N :=
  Law.mix (experimentLaw9 S.inputs) (fun ω => filteredRowLaw9 S ω b)

/-- The expected total pointwise load of the odd rows. -/
noncomputable def rawOddLoad9 {P : Params9} {n N : ℕ}
    {E : Fin N → Fin N → Prop} {G : Colour} {M : TagMix N}
    {W : HeightWitness9 P n} {I : IDMap9 P n W}
    (S : TagExperiment9 P n N E G M W I) (y : Fin N) : ℝ :=
  ∑ b ∈ Finset.univ.filter (fun b : CubeVertex n => ¬ IsEvenRole b),
    (rawRowLaw9 S b).w y

/-- Odd assignment candidates obtained after anchor avoidance and load control. -/
structure OddCandidates9 {P : Params9} {n N : ℕ} {E : Fin N → Fin N → Prop}
    {G : Colour} {M : TagMix N} {W : HeightWitness9 P n} {I : IDMap9 P n W}
    (S : TagExperiment9 P n N E G M W I) (Y : Finset (Fin N)) where
  weight : OddSites9 n → Fin N → ℝ
  candidate : OddSites9 n → Finset (Fin N)
  weight_eq_raw : ∀ b y, weight b y = (rawRowLaw9 S b.1).w y
  candidate_iff_pos : ∀ b y, y ∈ candidate b ↔ 0 < weight b y
  nonnegative : ∀ b y, 0 ≤ weight b y
  row_sum : ∀ b, ∑ y, weight b y = 1
  supported : ∀ b y, y ∉ candidate b → weight b y = 0
  candidate_in_Y : ∀ b, candidate b ⊆ Y
  column_load : ∀ y, ∑ b, weight b y ≤ 1

/-- An injection for the odd cube roles. -/
structure OddInjection9 {n N : ℕ} {E : Fin N → Fin N → Prop} {G : Colour}
    (X Y : Finset (Fin N)) where
  label : OddSites9 n → Fin N
  injective : Function.Injective label
  supported : ∀ b, label b ∈ Y
  predictive_safe : ∀ v : EvenSites9 n, ∃ x ∈ X,
    ∀ b : CubeVertex n, (cube n).Adj v.1 b → ∀ hOdd : ¬ IsEvenRole b,
      Hits E G x (label ⟨b, hOdd⟩)

/-- Fractional posterior rows for the even roles after fixing the odd injection. -/
structure EvenRows9 {n N : ℕ} {E : Fin N → Fin N → Prop} {G : Colour}
    (X Y : Finset (Fin N))
    (odd : OddInjection9 (E := E) (G := G) (n := n) (N := N) X Y) where
  weight : EvenSites9 n → Fin N → ℝ
  candidate : EvenSites9 n → Finset (Fin N)
  nonnegative : ∀ v y, 0 ≤ weight v y
  row_sum : ∀ v, ∑ y, weight v y = 1
  supported : ∀ v y, y ∉ candidate v → weight v y = 0
  candidate_in_X : ∀ v, candidate v ⊆ X
  column_load : ∀ y, ∑ v, weight v y ≤ 1
  edge : ∀ v b y, (cube n).Adj v.1 b.1 → y ∈ candidate v →
    Hits E G y (odd.label b)

end HypercubeRamsey
