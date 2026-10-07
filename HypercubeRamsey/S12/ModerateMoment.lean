import HypercubeRamsey.S12.InteractionTails

/-!
# Section 12 moderate interactions
-/

namespace HypercubeRamsey.S12

open HypercubeRamsey Filter
open Classical
open scoped BigOperators

/-- L12.4a: on a moderate tuple from the support, a positive product term has an exponential bound. -/
theorem moderate_posTerm_pointwise (κ : CConsts) (hκ : κ.Admissible) (T : Stage)
    (hDeep : DeepDisc T κ.xs κ.α 0.04) (c : Colour) (C0 : ℝ) (hC0 : 1 ≤ C0) :
    ∀ᶠ k in atTop,
      ∀ (S : InterSetting T k (κ.xs / 4)) (t : ℝ)
        (xs : Fin κ.u → Fin (T.S.N k)) (I : Finset (Fin κ.u)),
        (∀ i, 0 < S.τ.w (xs i)) →
        Moderate (T.S.E k) c (fun l => (S.π l).w) t xs →
        posTerm (T.S.E k) c (fun l => (S.π l).w) I xs ≤
          Real.exp (((2 : ℝ) ^ κ.u) * S.d * t) := by
  sorry

/-- L12.4b: the two large-interaction ranges have exponentially small product-law mass. -/
theorem moderate_tail_ranges (κ : CConsts) (hκ : κ.Admissible) (T : Stage)
    (hDeep : DeepDisc T κ.xs κ.α 0.04) (c : Colour) (C0 : ℝ) (hC0 : 1 ≤ C0) :
    ∀ᶠ k in atTop,
      ∀ (S : InterSetting T k (κ.xs / 4)), S.DegOK c C0 →
        (∑ xs : Fin κ.u → Fin (T.S.N k),
          if ¬ Moderate (T.S.E k) c (fun l => (S.π l).w)
            ((T.S.n k : ℝ) ^ (-(1.03 : ℝ))) xs
          then prodW S.τ.w xs else 0) ≤
            (T.S.n k : ℝ) * 4 ^ κ.u *
              Real.exp (-((T.S.n k : ℝ) ^ (0.4 : ℝ))) ∧
        (∑ xs : Fin κ.u → Fin (T.S.N k),
          if ¬ Moderate (T.S.E k) c (fun l => (S.π l).w)
            ((T.S.n k : ℝ) ^ (-(0.94 : ℝ))) xs
          then prodW S.τ.w xs else 0) ≤
            (T.S.n k : ℝ) * 4 ^ κ.u *
              Real.exp (-(κ.α * T.S.n k / 3)) := by
  sorry

/-- L12.4c: inclusion-exclusion cancellation on the very small-interaction range. -/
theorem moderate_cancellation (κ : CConsts) (hκ : κ.Admissible) (T : Stage)
    (hDeep : DeepDisc T κ.xs κ.α 0.04) (c : Colour) (C0 : ℝ) (hC0 : 1 ≤ C0) :
    ∀ᶠ k in atTop,
      ∀ (S : InterSetting T k (κ.xs / 4)), S.DegOK c C0 →
        |∑ xs : Fin κ.u → Fin (T.S.N k),
          if Moderate (T.S.E k) c (fun l => (S.π l).w)
            ((T.S.n k : ℝ) ^ (-(1.03 : ℝ))) xs
          then prodW S.τ.w xs * Phi (T.S.E k) c (fun l => (S.π l).w) xs else 0| ≤
            (T.S.n k : ℝ) ^ (-(3 * (κ.R : ℝ))) / 3 := by
  sorry

/-- L12.4: combine the pointwise, tail-range, and cancellation subnodes. -/
theorem moderate_moment_core (κ : CConsts) (hκ : κ.Admissible) (T : Stage)
    (hDeep : DeepDisc T κ.xs κ.α 0.04) (c : Colour) (C0 : ℝ) (hC0 : 1 ≤ C0)
    (hPointwise : ∀ᶠ k in atTop,
      ∀ (S : InterSetting T k (κ.xs / 4)) (t : ℝ)
        (xs : Fin κ.u → Fin (T.S.N k)) (I : Finset (Fin κ.u)),
        (∀ i, 0 < S.τ.w (xs i)) →
        Moderate (T.S.E k) c (fun l => (S.π l).w) t xs →
        posTerm (T.S.E k) c (fun l => (S.π l).w) I xs ≤
          Real.exp (((2 : ℝ) ^ κ.u) * S.d * t))
    (hTails : ∀ᶠ k in atTop,
      ∀ (S : InterSetting T k (κ.xs / 4)), S.DegOK c C0 →
        (∑ xs : Fin κ.u → Fin (T.S.N k),
          if ¬ Moderate (T.S.E k) c (fun l => (S.π l).w)
            ((T.S.n k : ℝ) ^ (-(1.03 : ℝ))) xs
          then prodW S.τ.w xs else 0) ≤
            (T.S.n k : ℝ) * 4 ^ κ.u *
              Real.exp (-((T.S.n k : ℝ) ^ (0.4 : ℝ))) ∧
        (∑ xs : Fin κ.u → Fin (T.S.N k),
          if ¬ Moderate (T.S.E k) c (fun l => (S.π l).w)
            ((T.S.n k : ℝ) ^ (-(0.94 : ℝ))) xs
          then prodW S.τ.w xs else 0) ≤
            (T.S.n k : ℝ) * 4 ^ κ.u *
              Real.exp (-(κ.α * T.S.n k / 3)))
    (hCancel : ∀ᶠ k in atTop,
      ∀ (S : InterSetting T k (κ.xs / 4)), S.DegOK c C0 →
        |∑ xs : Fin κ.u → Fin (T.S.N k),
          if Moderate (T.S.E k) c (fun l => (S.π l).w)
            ((T.S.n k : ℝ) ^ (-(1.03 : ℝ))) xs
          then prodW S.τ.w xs * Phi (T.S.E k) c (fun l => (S.π l).w) xs else 0| ≤
            (T.S.n k : ℝ) ^ (-(3 * (κ.R : ℝ))) / 3) :
    ∀ᶠ k in atTop, ∀ (S : InterSetting T k (κ.xs / 4)), S.DegOK c C0 →
      |∑ xs : Fin κ.u → Fin (T.S.N k),
          if Moderate (T.S.E k) c (fun l => (S.π l).w) (2 * κ.ξ) xs
          then prodW S.τ.w xs * Phi (T.S.E k) c (fun l => (S.π l).w) xs else 0|
        ≤ (T.S.n k : ℝ) ^ (-(3 * (κ.R : ℝ))) ∧
      ∀ u' ≤ κ.u, ∀ I : Finset (Fin u'),
        ∑ xs : Fin u' → Fin (T.S.N k),
          (if Moderate (T.S.E k) c (fun l => (S.π l).w) (2 * κ.ξ) xs
           then prodW S.τ.w xs *
             posTerm (T.S.E k) c (fun l => (S.π l).w) I xs else 0) ≤ 2 := by
  sorry

/-- L12.4: the conjunction of the moderate signed-moment and positive-term estimates. -/
def ModerateMomentClaim (κ : CConsts) (T : Stage) (c : Colour) (C0 : ℝ) : Prop :=
  ∀ᶠ k in atTop, ∀ (S : InterSetting T k (κ.xs / 4)), S.DegOK c C0 →
    |∑ xs : Fin κ.u → Fin (T.S.N k),
        if Moderate (T.S.E k) c (fun l => (S.π l).w) (2 * κ.ξ) xs
        then prodW S.τ.w xs * Phi (T.S.E k) c (fun l => (S.π l).w) xs else 0|
      ≤ (T.S.n k : ℝ) ^ (-(3 * (κ.R : ℝ))) ∧
    ∀ u' ≤ κ.u, ∀ I : Finset (Fin u'),
      ∑ xs : Fin u' → Fin (T.S.N k),
        (if Moderate (T.S.E k) c (fun l => (S.π l).w) (2 * κ.ξ) xs
         then prodW S.τ.w xs *
           posTerm (T.S.E k) c (fun l => (S.π l).w) I xs else 0) ≤ 2

/-- L12.4: the exported moderate-interaction moment estimate. -/
theorem moderate_moment (κ : CConsts) (hκ : κ.Admissible) (T : Stage)
    (hDeep : DeepDisc T κ.xs κ.α 0.04) (c : Colour) (C0 : ℝ) (hC0 : 1 ≤ C0) :
    ModerateMomentClaim κ T c C0 := by
  exact moderate_moment_core κ hκ T hDeep c C0 hC0
    (moderate_posTerm_pointwise κ hκ T hDeep c C0 hC0)
    (moderate_tail_ranges κ hκ T hDeep c C0 hC0)
    (moderate_cancellation κ hκ T hDeep c C0 hC0)

end HypercubeRamsey.S12
