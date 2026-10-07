import HypercubeRamsey.Framework.OneShot
import HypercubeRamsey.Framework.PartC
import HypercubeRamsey.S03.GatedPosterior

/-!
Finite objects used by the Section 11 slice and outer-word experiments.  All experiments are expressed as
explicit weights on finite assignment spaces; no probabilistic object is hidden behind an axiom or an
incomplete definition.
-/

namespace HypercubeRamsey.S11.Core

open HypercubeRamsey OAI.HypercubeRamsey
open Classical
open scoped BigOperators

abbrev EvenRole (n : ℕ) := {v : CubeVertex n // HypercubeRamsey.IsEvenRole v}
abbrev OddRole (n : ℕ) := {v : CubeVertex n // ¬ HypercubeRamsey.IsEvenRole v}
abbrev SliceTuples (h k N : ℕ) := EvenRole h → Fin k → Fin N
abbrev SliceOddLabels (h N : ℕ) := OddRole h → Fin N

/-- The inner slice dimension `⌊n^.1⌋`. -/
noncomputable def innerDimension (n : ℕ) : ℕ := Nat.floor ((n : ℝ) ^ ((1 : ℝ) / 10))

/-- The number of outer coordinates. -/
noncomputable def outerDimension (n : ℕ) : ℕ := n - innerDimension n

/-- The number of independent samples in each even row, `⌈n^.2⌉`. -/
noncomputable def tupleLength (n : ℕ) : ℕ := Nat.ceil ((n : ℝ) ^ ((1 : ℝ) / 5))

/-- The Section 11 surplus and correlation thresholds. -/
noncomputable def sliceSurplus (n : ℕ) : ℝ := (n : ℝ) ^ (-(1 : ℝ) / 100)
noncomputable def signedBiasScale (n : ℕ) : ℝ := (n : ℝ) ^ (-(19 : ℝ) / 20)

/-- A bounded zero-or-one encoding of a coloured edge. -/
noncomputable def edgeIndicator {N : ℕ} (E : Fin N → Fin N → Prop) (G : Colour)
    (x y : Fin N) : ℝ := by
  classical
  exact if Hits E G x y then 1 else 0

/-- The centered sign `f_x(y)`. -/
noncomputable def signedEdge {N : ℕ} (E : Fin N → Fin N → Prop) (G : Colour)
    (x y : Fin N) : ℝ := 2 * edgeIndicator E G x y - 1

/-- `m_x = E_π f_x`. -/
noncomputable def signedMean {N : ℕ} (E : Fin N → Fin N → Prop) (G : Colour)
    (π : Law N) (x : Fin N) : ℝ := ∑ y, π.w y * signedEdge E G x y

/-- The row degree into a law. -/
noncomputable def lawDegree {N : ℕ} (E : Fin N → Fin N → Prop) (G : Colour)
    (π : Law N) (x : Fin N) : ℝ := ∑ y, π.w y * edgeIndicator E G x y

/-- `K_π(x,x') = E_π f_x f_x'`. -/
noncomputable def signedCorrelation {N : ℕ} (E : Fin N → Fin N → Prop) (G : Colour)
    (π : Law N) (x x' : Fin N) : ℝ :=
  ∑ y, π.w y * signedEdge E G x y * signedEdge E G x' y

/-- The normalized hit factor `1[x~y]/D_x`, with value zero when `D_x=0`. -/
noncomputable def normalizedHit {N : ℕ} (E : Fin N → Fin N → Prop) (G : Colour)
    (π : Law N) (x y : Fin N) : ℝ :=
  if lawDegree E G π x = 0 then 0 else edgeIndicator E G x y / lawDegree E G π x

/-- The centered likelihood factor `a_x(y)`. -/
noncomputable def likelihoodFactor {N : ℕ} (E : Fin N → Fin N → Prop) (G : Colour)
    (π : Law N) (x y : Fin N) : ℝ := normalizedHit E G π x y - 1

/-- An interaction indexed by a finite set of sampled labels. -/
noncomputable def interaction {N u : ℕ} (E : Fin N → Fin N → Prop) (G : Colour)
    (π : Law N) (J : Finset (Fin u)) (x : Fin u → Fin N) : ℝ :=
  ∑ y, π.w y * ∏ j ∈ J, likelihoodFactor E G π (x j) y

/-- The outer mass tested by L11.3 for a law `σ` and a tuple of outer labels. -/
noncomputable def outerMass {N d : ℕ} (E : Fin N → Fin N → Prop) (G : Colour)
    (π σ : Law N) (Y : Fin d → Fin N) : ℝ :=
  ∑ x, σ.w x * ∏ j, (1 + likelihoodFactor E G π x (Y j))

/-- The first-side common-neighbour set inside a slice. -/
noncomputable def commonNeighbourSet {h N : ℕ} (E : Fin N → Fin N → Prop) (G : Colour)
    (μ : Law N) (Y : SliceOddLabels h N) (v : EvenRole h) : Finset (Fin N) := by
  classical
  exact Finset.univ.filter fun x => μ.w x ≠ 0 ∧
    ∀ b : OddRole h, (cube h).Adj v.1 b.1 → Hits E G x (Y b)

/-- The threshold used to make an even row uniform on its internal common neighbours. -/
noncomputable def commonNeighbourCutoff (N h : ℕ) (g : ℝ) : ℝ :=
  (N : ℝ) * Real.exp (-((Real.log 2 - g / 2) * h))

/-- The subprobability row `σ_v`: uniform on the common-neighbour set above the cutoff, zero otherwise. -/
noncomputable def commonNeighbourWeight {N h : ℕ} (E : Fin N → Fin N → Prop) (G : Colour)
    (μ : Law N) (Y : SliceOddLabels h N) (v : EvenRole h) (g : ℝ) (x : Fin N) : ℝ := by
  classical
  let C := commonNeighbourSet E G μ Y v
  exact if x ∈ C ∧ (C.card : ℝ) ≥ commonNeighbourCutoff N h g then (C.card : ℝ)⁻¹ else 0

/-- The one-row tilted law `ρ_y(w)=μ(w)1[w~y]/d_G(μ,y)`. -/
noncomputable def hitConditionedWeight {N : ℕ} (E : Fin N → Fin N → Prop) (G : Colour)
    (μ : Law N) (y x : Fin N) : ℝ := by
  classical
  exact if Hits E G x y then μ.w x / colDeg E G μ y else 0

/-- The likelihood of the even tuples incident to one odd role. -/
noncomputable def sliceLikelihood {h k N : ℕ} (E : Fin N → Fin N → Prop) (G : Colour)
    (μ : Law N) (W : SliceTuples h k N) (b : OddRole h) (y : Fin N) : ℝ := by
  classical
  exact ∏ v : EvenRole h, ∏ j : Fin k,
    if (cube h).Adj v.1 b.1 then hitConditionedWeight E G μ (W v j) y else 1

/-- The likelihood normalizer `Z_b`. -/
noncomputable def sliceNormalizer {h k N : ℕ} (E : Fin N → Fin N → Prop) (G : Colour)
    (μ ν : Law N) (W : SliceTuples h k N) (b : OddRole h) : ℝ :=
  ∑ y, ν.w y * sliceLikelihood E G μ W b y

/-- The deletion normalizer `Z_{b,-v}`. -/
noncomputable def sliceDeletionNormalizer {h k N : ℕ} (E : Fin N → Fin N → Prop) (G : Colour)
    (μ ν : Law N) (W : SliceTuples h k N) (b : OddRole h) (v : EvenRole h) : ℝ := by
  classical
  exact ∑ y, ν.w y * (∏ v' : EvenRole h, ∏ j : Fin k,
    if v' ≠ v ∧ (cube h).Adj v'.1 b.1 then
      hitConditionedWeight E G μ (W v' j) y else 1)

/-- The three gates defining a passing odd row. -/
def sliceTestsPass {h k N : ℕ} (E : Fin N → Fin N → Prop) (G : Colour)
    (μ ν : Law N) (W : SliceTuples h k N) (b : OddRole h) (g : ℝ) : Prop :=
  0 < sliceNormalizer E G μ ν W b ∧
  Real.exp (-(k * h : ℝ)) ≤ sliceNormalizer E G μ ν W b ∧
  ∀ v : EvenRole h, (cube h).Adj v.1 b.1 →
    Real.exp (-((1 / 5 : ℝ) * g * k)) * sliceDeletionNormalizer E G μ ν W b v ≤
      sliceNormalizer E G μ ν W b

/-- The gated posterior row, with the original second law as its fallback. -/
noncomputable def posteriorWeight {h k N : ℕ} (E : Fin N → Fin N → Prop) (G : Colour)
    (μ ν : Law N) (W : SliceTuples h k N) (b : OddRole h) (g : ℝ) (y : Fin N) : ℝ := by
  classical
  exact if sliceTestsPass E G μ ν W b g then
    ν.w y * sliceLikelihood E G μ W b y / sliceNormalizer E G μ ν W b
  else ν.w y

/-- Product weight of the independent hit-conditioned tuples in one slice. -/
noncomputable def tupleProductWeight {h k N : ℕ} (E : Fin N → Fin N → Prop) (G : Colour)
    (μ : Law N) (y₀ : Fin N) (W : SliceTuples h k N) : ℝ := by
  classical
  exact ∏ v : EvenRole h, ∏ j : Fin k, hitConditionedWeight E G μ y₀ (W v j)

/-- Product weight of all odd outputs conditional on the even tuples. -/
noncomputable def oddOutputProductWeight {h k N : ℕ} (E : Fin N → Fin N → Prop) (G : Colour)
    (μ ν : Law N) (W : SliceTuples h k N) (g : ℝ) (Y : SliceOddLabels h N) : ℝ := by
  classical
  exact ∏ b : OddRole h, posteriorWeight E G μ ν W b g (Y b)

/-- The averaged odd-row weight `π_i`, before asserting that its weights sum to one. -/
noncomputable def meanOddRowWeight {h k N : ℕ} (E : Fin N → Fin N → Prop) (G : Colour)
    (μ ν : Law N) (y₀ : Fin N) (g : ℝ) (b : OddRole h) (y : Fin N) : ℝ := by
  classical
  exact
  ∑ W : SliceTuples h k N,
    tupleProductWeight E G μ y₀ W * posteriorWeight E G μ ν W b g y

/-- Failure mass of the posterior tests under the fixed-base tuple experiment. -/
noncomputable def sliceTestFailureMass {h k N : ℕ} (E : Fin N → Fin N → Prop) (G : Colour)
    (μ ν : Law N) (y₀ : Fin N) (g : ℝ) (b : OddRole h) : ℝ := by
  classical
  exact ∑ W : SliceTuples h k N,
    tupleProductWeight E G μ y₀ W * (if sliceTestsPass E G μ ν W b g then 0 else 1)

/-- The averaged even subprobability row `α_i`, before asserting its mass bounds. -/
noncomputable def meanEvenRowWeight {h k N : ℕ} (E : Fin N → Fin N → Prop) (G : Colour)
    (μ ν : Law N) (y₀ : Fin N) (g : ℝ) (v : EvenRole h) (x : Fin N) : ℝ := by
  classical
  exact
  ∑ W : SliceTuples h k N, tupleProductWeight E G μ y₀ W *
    ∑ Y : SliceOddLabels h N,
      oddOutputProductWeight E G μ ν W g Y * commonNeighbourWeight E G μ Y v g x

/-- A nonnegative subprobability weight function on a finite host side. -/
structure SubLaw (N : ℕ) where
  w : Fin N → ℝ
  nonneg : ∀ x, 0 ≤ w x
  mass_le_one : ∑ x, w x ≤ 1

/-- A finite tag menu with the slice-side laws and their removal robustness. -/
structure BiasedMenu (n N : ℕ) (E : Fin N → Fin N → Prop) (X Y : Finset (Fin N))
    (κ h₀ : ℝ) where
  mix : TagMix N
  G : Colour
  μ_supported : ∀ i, (mix.μ i).SupportedIn X
  ν_supported : ∀ i, (mix.ν i).SupportedIn Y
  μ_width : ∀ i, (mix.μ i).WidthLE ((n : ℝ) ^ (1 / 100 : ℝ))
  ν_width : ∀ i, (mix.ν i).WidthLE ((11 / 1000 : ℝ) * n)
  high_columns : ∀ i y, 0 < (mix.ν i).w y →
    (1 / 2 : ℝ) + 2 * sliceSurplus n ≤ colDeg E G (mix.μ i) y
  bias : ∀ i, (n : ℝ) ^ (-h₀) ≤
    |dens E true (mix.μ i) (mix.ν i) - 1 / 2|
  removal_menu : ∀ RX RY : Finset (Fin N),
    (RX.card : ℝ) ≤ (κ / 2) * N → (RY.card : ℝ) ≤ (κ / 2) * N →
    ∃ i, (mix.μ i).SupportedIn (X \ RX) ∧ (mix.ν i).SupportedIn (Y \ RY)

/-- The deterministic base point and mean odd rows selected by P11.1a. -/
structure SliceSeed {n N : ℕ} {E : Fin N → Fin N → Prop} {X Y : Finset (Fin N)}
    {κ h₀ : ℝ} (M : BiasedMenu n N E X Y κ h₀) (h k : ℕ) (g : ℝ) where
  y₀ : M.mix.ι → Fin N
  y₀_supported : ∀ i, (M.mix.ν i).w (y₀ i) > 0
  π : M.mix.ι → Law N
  π_eq : ∀ i (b : OddRole h) y,
    (π i).w y = meanOddRowWeight (h := h) (k := k)
      E M.G (M.mix.μ i) (M.mix.ν i) (y₀ i) g b y
  π_role_invariant : ∀ i (b b' : OddRole h) y,
    meanOddRowWeight (h := h) (k := k)
        E M.G (M.mix.μ i) (M.mix.ν i) (y₀ i) g b y =
      meanOddRowWeight (h := h) (k := k)
        E M.G (M.mix.μ i) (M.mix.ν i) (y₀ i) g b' y
  π_width : ∀ i, (π i).WidthLE ((1 / 50 : ℝ) * n)
  row_cap : ∀ i (W : SliceTuples h k N) (b : OddRole h) y,
    posteriorWeight (h := h) (k := k)
      E M.G (M.mix.μ i) (M.mix.ν i) W b g y ≤ Real.exp ((1 / 50 : ℝ) * n) / N
  test_failure : ∀ i (b : OddRole h),
    sliceTestFailureMass (h := h) (k := k)
      E M.G (M.mix.μ i) (M.mix.ν i) (y₀ i) g b ≤
      Real.exp (-((k * h : ℝ))) + h * Real.exp (-((1 / 5 : ℝ) * g * k))

/-- The mean even sublaws and the common-neighbour success estimate from P11.1b. -/
structure CommonRows {n N : ℕ} {E : Fin N → Fin N → Prop} {X Y : Finset (Fin N)}
    {κ h₀ : ℝ} {M : BiasedMenu n N E X Y κ h₀} {h k : ℕ} {g : ℝ}
    (S : SliceSeed M h k g) where
  α : M.mix.ι → SubLaw N
  α_eq : ∀ i (v : EvenRole h) x,
    (α i).w x = meanEvenRowWeight (h := h) (k := k)
      E M.G (M.mix.μ i) (M.mix.ν i) (S.y₀ i) g v x
  α_role_invariant : ∀ i (v v' : EvenRole h) x,
    meanEvenRowWeight (h := h) (k := k)
        E M.G (M.mix.μ i) (M.mix.ν i) (S.y₀ i) g v x =
      meanEvenRowWeight (h := h) (k := k)
        E M.G (M.mix.μ i) (M.mix.ν i) (S.y₀ i) g v' x
  row_failure : ∀ i (v : EvenRole h),
    (∑ W : SliceTuples h k N, tupleProductWeight (h := h) (k := k)
        E M.G (M.mix.μ i) (S.y₀ i) W *
      ∑ Y' : SliceOddLabels h N,
        oddOutputProductWeight (h := h) (k := k)
          E M.G (M.mix.μ i) (M.mix.ν i) W g Y' *
        (if (∑ x, commonNeighbourWeight E M.G (M.mix.μ i) Y' v g x) = 1 then 0 else 1)) ≤
      Real.exp (-((1 / 2 : ℝ) * g * k * h)) +
        h * (Real.exp (-((k * h : ℝ))) + h * Real.exp (-((1 / 5 : ℝ) * g * k)))

/-- Pointwise profile mixtures of the mean laws and sublaws. -/
noncomputable def profileLaw {ι : Type*} {N : ℕ} [Fintype ι]
    (p : FinProb ι) (π : ι → Law N) : Law N := Law.mix p π

noncomputable def profileSubWeight {ι : Type*} {N : ℕ} [Fintype ι]
    (p : FinProb ι) (α : ι → SubLaw N) (x : Fin N) : ℝ := ∑ i, p.w i * (α i).w x

end HypercubeRamsey.S11.Core
