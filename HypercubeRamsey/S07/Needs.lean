import HypercubeRamsey.Framework.Props
import HypercubeRamsey.S04.Lemma41
import HypercubeRamsey.S06.Assembly

/-!
Local copies of the consumed Section 4 and Section 6 statements. The shared
lanes have not been merged into this worktree yet.
-/

namespace HypercubeRamsey.S07.Needs

open Filter

/-- The one-shot conclusion supplied by Section 6 at a fixed broad-side exponent. -/
def BroadSideProperty (Dstar : ℝ) : Prop :=
  ∀ γ p₀ K : ℝ, 0 < γ → γ < 1 → 0 < p₀ → 0 < K →
    ∃ n₀ : ℕ, ∃ C₀ : ℝ, ∀ n N : ℕ, ∀ E : Fin N → Fin N → Prop, ∀ G : Colour,
      ∀ M : TagMix N, LargeAt n₀ C₀ n N → M.Balanced K →
      (∀ i, 0 < M.Λ i → (M.μ i).WidthLE ((n : ℝ) ^ γ)) →
      (∀ i, 0 < M.Λ i → (M.ν i).CapLE ((n : ℝ) ^ Dstar)) →
      (∀ i y, 0 < M.Λ i → 0 < (M.ν i).w y →
        1 - (n : ℝ) ^ (-p₀) ≤ colDeg E G (M.μ i) y) →
      CubeAt n N E

/-- SHARED: L6.1 (06:4–12), the broad-side lemma consumed by E7.1. -/
theorem small_polynomial_broad_side :
    ∃ Dstar : ℝ, 0 < Dstar ∧ BroadSideProperty Dstar := by
  obtain ⟨D, hD, h⟩ := HypercubeRamsey.small_polynomial_broad_side
  exact ⟨D, hD, h⟩

/-- SHARED: L4.1 (04:9–16), in the monotone consumed form used by C7.2c. -/
theorem L4_1_consumed :
    ∀ β γ : ℝ, 0 < β → β ≤ γ → γ < 1 →
      ∃ h : ℝ, 0 < h ∧
        ∀ h' : ℝ, 0 < h' → h' ≤ h → ∀ T : Stage,
          Available T (PBias (pw β) (pw γ) h').toPatch →
          EventuallyAbsent T (PPure β γ h').toPatch → False :=
  fun β γ hβ hβγ hγ => HypercubeRamsey.L4_1 β γ hβ hβγ hγ

end HypercubeRamsey.S07.Needs
