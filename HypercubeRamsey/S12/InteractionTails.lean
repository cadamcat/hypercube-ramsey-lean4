import HypercubeRamsey.S12.Exceptional
import HypercubeRamsey.S12.CenteredMoment

/-!
# Section 12 interaction tails
-/

namespace HypercubeRamsey.S12

open HypercubeRamsey Filter
open Classical
open scoped BigOperators

/-- L12.3a: a gated one-coordinate interaction tail. -/
theorem inter_tail_one (κ : CConsts) (hκ : κ.Admissible) (T : Stage)
    (hDeep : DeepDisc T κ.xs κ.α 0.04) (c : Colour) (u : ℕ)
    (C0 : ℝ) (hC0 : 1 ≤ C0) :
    ∀ᶠ k in atTop,
      ∀ (S : InterSetting T k (κ.xs / 4)) (l : Fin S.d)
        (J : Finset (Fin u)) (i₀ : Fin u),
        i₀ ∈ J → 2 ≤ J.card →
        ∀ xs : Fin u → Fin (T.S.N k),
          (∀ i ∈ J, i ≠ i₀ →
            DegGate (T.S.E k) c (S.π l).w C0 (bstar T k) (xs i)) →
          ∑ z ∈ Finset.univ.filter (fun z =>
            DegGate (T.S.E k) c (S.π l).w C0 (bstar T k) z ∧
            100 * 3 ^ u * C0 * bstar T k <
              |inter (T.S.E k) c (S.π l).w J (Function.update xs i₀ z)|),
            S.τ.w z ≤ Real.exp (-(κ.α * T.S.n k / 3)) := by
  sorry

/-- L12.3a: the raw one-coordinate correlation tail, without a degree gate. -/
theorem corr_tail_one (κ : CConsts) (hκ : κ.Admissible) (T : Stage)
    (hDeep : DeepDisc T κ.xs κ.α 0.04) (c : Colour) (u : ℕ)
    (C0 : ℝ) (hC0 : 1 ≤ C0) :
    ∀ᶠ k in atTop,
      ∀ (S : InterSetting T k (κ.xs / 4)) (l : Fin S.d) (x : Fin (T.S.N k)),
        ∑ z ∈ Finset.univ.filter (fun z =>
          100 * 3 ^ u * C0 * bstar T k <
            |corr (T.S.E k) c (S.π l).w x z|),
          S.τ.w z ≤ Real.exp (-(κ.α * T.S.n k / 3)) := by
  sorry

/-- L12.3b: a gated two-coordinate interaction tail. -/
theorem inter_tail_two (κ : CConsts) (hκ : κ.Admissible) (T : Stage)
    (hDeep : DeepDisc T κ.xs κ.α 0.04) (c : Colour) (u : ℕ)
    (C0 : ℝ) (hC0 : 1 ≤ C0) :
    ∀ᶠ k in atTop,
      ∀ (S : InterSetting T k (κ.xs / 4)) (l : Fin S.d)
        (J : Finset (Fin u)) (i₀ i₁ : Fin u),
        i₀ ∈ J → i₁ ∈ J → i₀ ≠ i₁ → 2 ≤ J.card →
        ∀ xs : Fin u → Fin (T.S.N k),
          (∀ i ∈ J, i ≠ i₀ → i ≠ i₁ →
            DegGate (T.S.E k) c (S.π l).w C0 (bstar T k) (xs i)) →
          ∑ z, ∑ z',
            (if DegGate (T.S.E k) c (S.π l).w C0 (bstar T k) z ∧
                DegGate (T.S.E k) c (S.π l).w C0 (bstar T k) z' ∧
                (T.S.n k : ℝ) ^ (-(1.03 : ℝ)) <
                  |inter (T.S.E k) c (S.π l).w J
                    (Function.update (Function.update xs i₀ z) i₁ z')|
             then S.τ.w z * S.τ.w z' else 0) ≤
            Real.exp (-((T.S.n k : ℝ) ^ (0.4 : ℝ))) := by
  sorry

/-- L12.3b: the raw two-coordinate correlation tail, without a degree gate. -/
theorem corr_tail_two (κ : CConsts) (hκ : κ.Admissible) (T : Stage)
    (hDeep : DeepDisc T κ.xs κ.α 0.04) (c : Colour) (u : ℕ)
    (C0 : ℝ) (hC0 : 1 ≤ C0) :
    ∀ᶠ k in atTop,
      ∀ (S : InterSetting T k (κ.xs / 4)) (l : Fin S.d),
        ∑ z, ∑ z',
          (if (T.S.n k : ℝ) ^ (-(1.03 : ℝ)) <
              |corr (T.S.E k) c (S.π l).w z z'|
           then S.τ.w z * S.τ.w z' else 0) ≤
            Real.exp (-((T.S.n k : ℝ) ^ (0.4 : ℝ))) := by
  sorry

/-- L12.3c: mean absolute interaction size under the iid first-side law. -/
theorem inter_mean (κ : CConsts) (hκ : κ.Admissible) (T : Stage)
    (hDeep : DeepDisc T κ.xs κ.α 0.04) (c : Colour) (u : ℕ)
    (C0 : ℝ) (hC0 : 1 ≤ C0) :
    ∀ᶠ k in atTop,
      ∀ (S : InterSetting T k (κ.xs / 4)) (l : Fin S.d)
        (J : Finset (Fin u)),
        2 ≤ J.card → J.card ≤ u → S.DegOK c C0 →
        ∑ xs : Fin u → Fin (T.S.N k),
          prodW S.τ.w xs * |inter (T.S.E k) c (S.π l).w J xs| ≤
            (T.S.n k : ℝ) ^ (-0.4 * (J.card : ℝ)) := by
  sorry

/-- L12.3: assemble the one-free, two-free, raw-correlation, and mean interaction estimates. -/
theorem interaction_tails (κ : CConsts) (hκ : κ.Admissible) (T : Stage)
    (hDeep : DeepDisc T κ.xs κ.α 0.04) (c : Colour) (u : ℕ)
    (C0 : ℝ) (hC0 : 1 ≤ C0) :
    (∀ᶠ k in atTop,
      ∀ (S : InterSetting T k (κ.xs / 4)) (l : Fin S.d)
        (J : Finset (Fin u)) (i₀ : Fin u),
        i₀ ∈ J → 2 ≤ J.card →
        ∀ xs : Fin u → Fin (T.S.N k),
          (∀ i ∈ J, i ≠ i₀ →
            DegGate (T.S.E k) c (S.π l).w C0 (bstar T k) (xs i)) →
          ∑ z ∈ Finset.univ.filter (fun z =>
            DegGate (T.S.E k) c (S.π l).w C0 (bstar T k) z ∧
            100 * 3 ^ u * C0 * bstar T k <
              |inter (T.S.E k) c (S.π l).w J (Function.update xs i₀ z)|),
            S.τ.w z ≤ Real.exp (-(κ.α * T.S.n k / 3))) ∧
    (∀ᶠ k in atTop,
      ∀ (S : InterSetting T k (κ.xs / 4)) (l : Fin S.d)
        (x : Fin (T.S.N k)),
          ∑ z ∈ Finset.univ.filter (fun z =>
            100 * 3 ^ u * C0 * bstar T k <
              |corr (T.S.E k) c (S.π l).w x z|),
            S.τ.w z ≤ Real.exp (-(κ.α * T.S.n k / 3))) ∧
    (∀ᶠ k in atTop,
      ∀ (S : InterSetting T k (κ.xs / 4)) (l : Fin S.d)
        (J : Finset (Fin u)) (i₀ i₁ : Fin u),
        i₀ ∈ J → i₁ ∈ J → i₀ ≠ i₁ → 2 ≤ J.card →
        ∀ xs : Fin u → Fin (T.S.N k),
          (∀ i ∈ J, i ≠ i₀ → i ≠ i₁ →
            DegGate (T.S.E k) c (S.π l).w C0 (bstar T k) (xs i)) →
          ∑ z, ∑ z',
            (if DegGate (T.S.E k) c (S.π l).w C0 (bstar T k) z ∧
                DegGate (T.S.E k) c (S.π l).w C0 (bstar T k) z' ∧
                (T.S.n k : ℝ) ^ (-(1.03 : ℝ)) <
                  |inter (T.S.E k) c (S.π l).w J
                    (Function.update (Function.update xs i₀ z) i₁ z')|
             then S.τ.w z * S.τ.w z' else 0) ≤
            Real.exp (-((T.S.n k : ℝ) ^ (0.4 : ℝ)))) ∧
    (∀ᶠ k in atTop,
      ∀ (S : InterSetting T k (κ.xs / 4)) (l : Fin S.d),
        ∑ z, ∑ z',
          (if (T.S.n k : ℝ) ^ (-(1.03 : ℝ)) <
              |corr (T.S.E k) c (S.π l).w z z'|
           then S.τ.w z * S.τ.w z' else 0) ≤
            Real.exp (-((T.S.n k : ℝ) ^ (0.4 : ℝ)))) ∧
    (∀ᶠ k in atTop,
      ∀ (S : InterSetting T k (κ.xs / 4)) (l : Fin S.d)
        (J : Finset (Fin u)),
        2 ≤ J.card → J.card ≤ u → S.DegOK c C0 →
        ∑ xs : Fin u → Fin (T.S.N k),
          prodW S.τ.w xs * |inter (T.S.E k) c (S.π l).w J xs| ≤
            (T.S.n k : ℝ) ^ (-0.4 * (J.card : ℝ))) := by
  exact ⟨inter_tail_one κ hκ T hDeep c u C0 hC0,
    corr_tail_one κ hκ T hDeep c u C0 hC0,
    inter_tail_two κ hκ T hDeep c u C0 hC0,
    corr_tail_two κ hκ T hDeep c u C0 hC0,
    inter_mean κ hκ T hDeep c u C0 hC0⟩

end HypercubeRamsey.S12
