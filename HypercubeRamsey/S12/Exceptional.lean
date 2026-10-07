import HypercubeRamsey.S12.Defs

/-!
# Section 12 exceptional sets

These are the one-sign conditioning, weighted-test, and conditioning-width
interfaces used by the later interaction and trimming estimates.
-/

namespace HypercubeRamsey.Law

open scoped BigOperators

/-- L12.0(d): conditioning on a positive-mass set increases width by its log cost. -/
theorem cond_widthLE {N : ℕ} (τ : _root_.HypercubeRamsey.Law N)
    (S : Finset (Fin N)) (h : 0 < ∑ x ∈ S, τ.w x)
    {w : ℝ} (hw : τ.WidthLE w) :
    (τ.cond S h).WidthLE (w + Real.log (1 / ∑ x ∈ S, τ.w x)) := by
  sorry

end HypercubeRamsey.Law

namespace HypercubeRamsey.S12

open HypercubeRamsey
open Classical
open scoped BigOperators

/-- L12.0(a): exceptional first-side mass under a narrow second-side law. -/
theorem exceptional_first {T : Stage} {k : ℕ} {wS wL err : ℝ}
    (hD : TwoBudgetDisc T k wS wL err) (c : Colour)
    {w₁ W₂ w : ℝ}
    (hpair : (w₁ ≤ wS ∧ W₂ ≤ wL) ∨ (w₁ ≤ wL ∧ W₂ ≤ wS))
    (ν : Law (T.S.N k)) (hν : ν.SupportedIn (T.Y k)) (hνw : ν.WidthLE w₁)
    (τ : Law (T.S.N k)) (hτ : τ.SupportedIn (T.X k)) (hτw : τ.WidthLE w) :
    ∑ x ∈ Finset.univ.filter
      (fun x => err < |deg (T.S.E k) c ν.w x - 1 / 2|), τ.w x ≤
        2 * Real.exp (w - W₂) := by
  sorry

/-- L12.0(b): exceptional second-side mass under a narrow first-side law. -/
theorem exceptional_second {T : Stage} {k : ℕ} {wS wL err : ℝ}
    (hD : TwoBudgetDisc T k wS wL err) (c : Colour)
    {w₁ W₂ w : ℝ}
    (hpair : (w₁ ≤ wS ∧ W₂ ≤ wL) ∨ (w₁ ≤ wL ∧ W₂ ≤ wS))
    (τ : Law (T.S.N k)) (hτ : τ.SupportedIn (T.X k)) (hτw : τ.WidthLE w₁)
    (ν : Law (T.S.N k)) (hν : ν.SupportedIn (T.Y k)) (hνw : ν.WidthLE w) :
    ∑ y ∈ Finset.univ.filter (fun y => err <
      |(∑ x, τ.w x * hit (T.S.E k) c x y) - 1 / 2|), ν.w y ≤
        2 * Real.exp (w - W₂) := by
  sorry

/-- L12.0(c), first orientation: a bounded signed test on the second side. -/
theorem exceptional_signed {T : Stage} {k : ℕ} {wS wL err : ℝ}
    (hD : TwoBudgetDisc T k wS wL err) (c : Colour)
    {w₁ W₂ w : ℝ}
    (hpair : (w₁ ≤ wS ∧ W₂ ≤ wL) ∨ (w₁ ≤ wL ∧ W₂ ≤ wS))
    (π : Law (T.S.N k)) (hπ : π.SupportedIn (T.Y k))
    (hπw : π.WidthLE (w₁ - Real.log 3))
    (τ : Law (T.S.N k)) (hτ : τ.SupportedIn (T.X k)) (hτw : τ.WidthLE w)
    (f : Fin (T.S.N k) → ℝ) (hf : ∀ y, |f y| ≤ 1) :
    ∑ x ∈ Finset.univ.filter (fun x => 6 * err <
      |∑ y, π.w y * f y * (hit (T.S.E k) c x y - deg (T.S.E k) c π.w x)|),
      τ.w x ≤ 4 * Real.exp (w - W₂) := by
  sorry

/-- L12.0(c), transposed orientation: a bounded signed test on the first side. -/
theorem exceptional_signed_second {T : Stage} {k : ℕ} {wS wL err : ℝ}
    (hD : TwoBudgetDisc T k wS wL err) (c : Colour)
    {w₁ W₂ w : ℝ}
    (hpair : (w₁ ≤ wS ∧ W₂ ≤ wL) ∨ (w₁ ≤ wL ∧ W₂ ≤ wS))
    (τ : Law (T.S.N k)) (hτ : τ.SupportedIn (T.X k))
    (hτw : τ.WidthLE (w₁ - Real.log 3))
    (ν : Law (T.S.N k)) (hν : ν.SupportedIn (T.Y k)) (hνw : ν.WidthLE w)
    (f : Fin (T.S.N k) → ℝ) (hf : ∀ x, |f x| ≤ 1) :
    ∑ y ∈ Finset.univ.filter (fun y => 6 * err <
      |∑ x, τ.w x * f x * (hit (T.S.E k) c x y -
        ∑ z, τ.w z * hit (T.S.E k) c z y)|),
      ν.w y ≤ 4 * Real.exp (w - W₂) := by
  sorry

/-- L12.0: the four exceptional-set conclusions at a fixed two-budget discrepancy input. -/
def ExceptionalSetClaims {T : Stage} {k : ℕ} {wS wL err : ℝ} (c : Colour) : Prop :=
    (∀ {w₁ W₂ w : ℝ},
      ((w₁ ≤ wS ∧ W₂ ≤ wL) ∨ (w₁ ≤ wL ∧ W₂ ≤ wS)) →
      ∀ (ν : Law (T.S.N k)), ν.SupportedIn (T.Y k) → ν.WidthLE w₁ →
      ∀ (τ : Law (T.S.N k)), τ.SupportedIn (T.X k) → τ.WidthLE w →
      ∑ x ∈ Finset.univ.filter
        (fun x => err < |deg (T.S.E k) c ν.w x - 1 / 2|), τ.w x ≤
          2 * Real.exp (w - W₂)) ∧
    (∀ {w₁ W₂ w : ℝ},
      ((w₁ ≤ wS ∧ W₂ ≤ wL) ∨ (w₁ ≤ wL ∧ W₂ ≤ wS)) →
      ∀ (τ : Law (T.S.N k)), τ.SupportedIn (T.X k) → τ.WidthLE w₁ →
      ∀ (ν : Law (T.S.N k)), ν.SupportedIn (T.Y k) → ν.WidthLE w →
      ∑ y ∈ Finset.univ.filter (fun y => err <
        |(∑ x, τ.w x * hit (T.S.E k) c x y) - 1 / 2|), ν.w y ≤
          2 * Real.exp (w - W₂)) ∧
    (∀ {w₁ W₂ w : ℝ},
      ((w₁ ≤ wS ∧ W₂ ≤ wL) ∨ (w₁ ≤ wL ∧ W₂ ≤ wS)) →
      ∀ (π : Law (T.S.N k)), π.SupportedIn (T.Y k) →
        π.WidthLE (w₁ - Real.log 3) →
      ∀ (τ : Law (T.S.N k)), τ.SupportedIn (T.X k) → τ.WidthLE w →
      ∀ (f : Fin (T.S.N k) → ℝ), (∀ y, |f y| ≤ 1) →
      ∑ x ∈ Finset.univ.filter (fun x => 6 * err <
        |∑ y, π.w y * f y *
          (hit (T.S.E k) c x y - deg (T.S.E k) c π.w x)|),
        τ.w x ≤ 4 * Real.exp (w - W₂)) ∧
    (∀ {w₁ W₂ w : ℝ},
      ((w₁ ≤ wS ∧ W₂ ≤ wL) ∨ (w₁ ≤ wL ∧ W₂ ≤ wS)) →
      ∀ (τ : Law (T.S.N k)), τ.SupportedIn (T.X k) →
        τ.WidthLE (w₁ - Real.log 3) →
      ∀ (ν : Law (T.S.N k)), ν.SupportedIn (T.Y k) → ν.WidthLE w →
      ∀ (f : Fin (T.S.N k) → ℝ), (∀ x, |f x| ≤ 1) →
      ∑ y ∈ Finset.univ.filter (fun y => 6 * err <
        |∑ x, τ.w x * f x *
          (hit (T.S.E k) c x y - ∑ z, τ.w z * hit (T.S.E k) c z y)|),
        ν.w y ≤ 4 * Real.exp (w - W₂))

/-- L12.0: assembled exceptional-set tools for both sides and both signed-test orientations. -/
theorem exceptional_set_lemma {T : Stage} {k : ℕ} {wS wL err : ℝ}
    (hD : TwoBudgetDisc T k wS wL err) (c : Colour) :
    ExceptionalSetClaims (T := T) (k := k) (wS := wS) (wL := wL) (err := err) c := by
  exact ⟨fun hpair => exceptional_first hD c hpair,
    fun hpair => exceptional_second hD c hpair,
    fun hpair => exceptional_signed hD c hpair,
    fun hpair => exceptional_signed_second hD c hpair⟩

/-- L12.0: package the conditioning-width estimate alongside the four exception bounds. -/
theorem exceptional_export {T : Stage} {k : ℕ} {wS wL err : ℝ}
    (hD : TwoBudgetDisc T k wS wL err) (c : Colour) :
    ExceptionalSetClaims (T := T) (k := k) (wS := wS) (wL := wL) (err := err) c ∧
    (∀ {N : ℕ} (τ : Law N) (S : Finset (Fin N))
      (h : 0 < ∑ x ∈ S, τ.w x) {w : ℝ} (hw : τ.WidthLE w),
      (τ.cond S h).WidthLE (w + Real.log (1 / ∑ x ∈ S, τ.w x))) := by
  exact ⟨exceptional_set_lemma hD c,
    fun {N} τ S h {w} hw => _root_.HypercubeRamsey.Law.cond_widthLE (w := w) τ S h hw⟩

end HypercubeRamsey.S12
