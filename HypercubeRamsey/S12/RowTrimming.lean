import HypercubeRamsey.S12.InteractionTails

/-!
# Section 12 simultaneous row trimming
-/

namespace HypercubeRamsey.S12

open HypercubeRamsey Filter
open Classical
open scoped BigOperators

/-- L12.6: simultaneously trim rows for a finite family of narrow second-side laws. -/
theorem row_trimming (κ : CConsts) (hκ : κ.Admissible) (T : Stage)
    (hDeep : DeepDisc T κ.xs κ.α 0.04) (c : Colour) :
    ∀ᶠ k in atTop,
      ∀ (X₀ : Finset (Fin (T.S.N k))) (hX₀ : X₀.Nonempty),
        X₀ ⊆ T.X k →
        Real.log ((T.S.N k : ℝ) / X₀.card) ≤
          (T.S.n k : ℝ) ^ (κ.xs / 4) →
        ∀ {ι : Type} (𝒥 : Finset ι) (π : ι → Law (T.S.N k)),
          (∀ j, (π j).SupportedIn (T.Y k)) →
          (∀ j, (π j).WidthLE ((T.S.n k : ℝ) ^ (κ.xs / 4))) →
          (𝒥.card : ℝ) ≤ Real.exp ((T.S.n k : ℝ) ^ (0.1 : ℝ)) →
          ∃ X₁ ⊆ X₀,
            ((X₀ \ X₁).card : ℝ) ≤
              Real.exp (-((T.S.n k : ℝ) ^ (0.3 : ℝ))) * X₀.card ∧
            ∀ j ∈ 𝒥, ∀ x ∈ X₁,
              RowTail (T.S.E k) c (π j).w X₀ (T.S.n k) κ.ξ x := by
  sorry

/-- L12.6b: a sufficiently close law inherits the relaxed row-tail estimate. -/
theorem rowTail_relax (κ : CConsts) (hκ : κ.Admissible) (T : Stage)
    (hDeep : DeepDisc T κ.xs κ.α 0.04) (c : Colour) :
    ∀ᶠ k in atTop,
      ∀ (π π' : Law (T.S.N k)) (X₀ : Finset (Fin (T.S.N k)))
        (x : Fin (T.S.N k)),
        RowTail (T.S.E k) c π.w X₀ (T.S.n k) κ.ξ x →
        (∑ y, |π.w y - π'.w y|) ≤ (T.S.n k : ℝ) ^ (-3 : ℝ) →
        RowTailRelaxed (T.S.E k) c π'.w X₀ (T.S.n k) κ.ξ x := by
  sorry

/-- L12.6: assembly exposing both the simultaneous trimming and interpolation relaxation. -/
theorem row_trimming_export (κ : CConsts) (hκ : κ.Admissible) (T : Stage)
    (hDeep : DeepDisc T κ.xs κ.α 0.04) (c : Colour) :
    (∀ᶠ k in atTop,
      ∀ (X₀ : Finset (Fin (T.S.N k))) (hX₀ : X₀.Nonempty),
        X₀ ⊆ T.X k →
        Real.log ((T.S.N k : ℝ) / X₀.card) ≤
          (T.S.n k : ℝ) ^ (κ.xs / 4) →
        ∀ {ι : Type} (𝒥 : Finset ι) (π : ι → Law (T.S.N k)),
          (∀ j, (π j).SupportedIn (T.Y k)) →
          (∀ j, (π j).WidthLE ((T.S.n k : ℝ) ^ (κ.xs / 4))) →
          (𝒥.card : ℝ) ≤ Real.exp ((T.S.n k : ℝ) ^ (0.1 : ℝ)) →
          ∃ X₁ ⊆ X₀,
            ((X₀ \ X₁).card : ℝ) ≤
              Real.exp (-((T.S.n k : ℝ) ^ (0.3 : ℝ))) * X₀.card ∧
            ∀ j ∈ 𝒥, ∀ x ∈ X₁,
              RowTail (T.S.E k) c (π j).w X₀ (T.S.n k) κ.ξ x) ∧
    (∀ᶠ k in atTop,
      ∀ (π π' : Law (T.S.N k)) (X₀ : Finset (Fin (T.S.N k)))
        (x : Fin (T.S.N k)),
        RowTail (T.S.E k) c π.w X₀ (T.S.n k) κ.ξ x →
        (∑ y, |π.w y - π'.w y|) ≤ (T.S.n k : ℝ) ^ (-3 : ℝ) →
        RowTailRelaxed (T.S.E k) c π'.w X₀ (T.S.n k) κ.ξ x) := by
  exact ⟨row_trimming κ hκ T hDeep c, rowTail_relax κ hκ T hDeep c⟩

end HypercubeRamsey.S12
