import HypercubeRamsey.Framework.OneShot

/-!
# Signed discrepancy tests

F-SignedTest turns ordinary two-colour discrepancy into tests weighted by any bounded signed function. The
width budget pays for the positive/negative decomposition. The second theorem records the equal-normalizer
tilt pair used in Sections 9 and 11.
-/

namespace HypercubeRamsey

open scoped BigOperators

open Classical in
/-- The signed second test against a finite host colouring. -/
noncomputable def signedHitExpectation {N : ℕ} (E : Fin N → Fin N → Prop) (c : Colour)
    (μ π : Law N) (f : Fin N → ℝ) : ℝ :=
  ∑ x, μ.w x * ∑ y, π.w y * ((if Hits E c x y then (1 : ℝ) else 0) - 1 / 2) * f y

/-- F-SignedTest: from `DiscOne`, every bounded signed second test is at most
`2(B+1)·err`, after paying `log(2B+2)` in the second width budget. -/
theorem signedTest_of_discrepancy {N : ℕ} {E : Fin N → Fin N → Prop} {X Y : Finset (Fin N)}
    {wX wY err B : ℝ} (hB : 0 ≤ B)
    (hdisc : DiscOne E X Y wX wY err)
    (μ π : Law N) (hμX : μ.SupportedIn X) (hπY : π.SupportedIn Y)
    (hμ : μ.WidthLE wX)
    (hπ : π.WidthLE (wY - Real.log (2 * B + 2)))
    (f : Fin N → ℝ) (hf : ∀ y, |f y| ≤ B) (c : Colour) :
    |signedHitExpectation E c μ π f| ≤ 2 * (B + 1) * err := by
  sorry

/-- F-SignedTest, equal-normalizer pair form: two tilts of a common law with the same normalizer are
controlled by the bounded signed test `(S₊-S₋)/Z`. -/
theorem signedTest_equalNormalizer {N : ℕ} {E : Fin N → Fin N → Prop} {X Y : Finset (Fin N)}
    {wX wY err B : ℝ} (hB : 0 ≤ B)
    (hdisc : DiscOne E X Y wX wY err)
    (μ baseLaw plusLaw minusLaw : Law N) (hμX : μ.SupportedIn X) (hBaseSupported : baseLaw.SupportedIn Y)
    (hμ : μ.WidthLE wX)
    (hBaseWidth : baseLaw.WidthLE (wY - Real.log (2 * B + 2)))
    (base Z : ℝ) (hZ : 0 < Z) (Splus Sminus : Fin N → ℝ)
    (hplus : ∀ y, plusLaw.w y = ((base + Splus y) / Z) * baseLaw.w y)
    (hminus : ∀ y, minusLaw.w y = ((base + Sminus y) / Z) * baseLaw.w y)
    (hnormPlus : ∑ y, (base + Splus y) * baseLaw.w y = Z)
    (hnormMinus : ∑ y, (base + Sminus y) * baseLaw.w y = Z)
    (hbound : ∀ y, |(Splus y - Sminus y) / Z| ≤ B) (c : Colour)
    [DecidableRel (Hits E c)] :
    |∑ x, μ.w x * ∑ y, (plusLaw.w y - minusLaw.w y) *
      ((if Hits E c x y then (1 : ℝ) else 0) - 1 / 2)| ≤ 2 * (B + 1) * err := by
  sorry

end HypercubeRamsey
