import HypercubeRamsey.Framework.Props

/-!
# Section 8: asymmetric purity exclusion

The main one-shot node is L8.1. The reversed-orientation form used by C8.2 is proved from it by transposing the
colouring and exchanging the two sides.
-/

namespace HypercubeRamsey

/-- L8.1 (08:8–455): asymmetric purity exclusion, one-shot form. -/
theorem asymmetric_purity (η₀ γ β p K : ℝ)
    (hη₀ : 0 < η₀) (hγ₀ : 0 < γ) (hγ₁ : γ < 1)
    (hβ₀ : 0 < β) (hβτ : β < tau8 η₀ / 4)
    (hp : 0 < p) (hK : 0 < K) :
    ∃ n₀ : ℕ, ∃ C₀ : ℝ,
      ∀ n N : ℕ, ∀ E : Fin N → Fin N → Prop,
        ∀ X Y : Finset (Fin N), ∀ G : Colour, ∀ M : TagMix N,
          LargeAt n₀ C₀ n N →
          DiscOne E X Y ((n : ℝ) ^ η₀) ((n : ℝ) ^ η₀) ((n : ℝ) ^ (-η₀)) →
          M.Balanced K →
          (∀ i, 0 < M.Λ i →
            (M.μ i).SupportedIn X ∧ (M.ν i).SupportedIn Y ∧
            (M.μ i).WidthLE ((n : ℝ) ^ γ) ∧ (M.ν i).WidthLE ((n : ℝ) ^ β) ∧
            (∀ y, 0 < (M.ν i).w y →
              1 - Real.exp (-((n : ℝ) ^ p)) ≤ colDeg E G (M.μ i) y)) →
          CubeAt n N E := by
  sorry

/-- L8.1r: the one-shot theorem with the two sides reversed. -/
theorem asymmetric_purity_reversed (η₀ γ β p K : ℝ)
    (hη₀ : 0 < η₀) (hγ₀ : 0 < γ) (hγ₁ : γ < 1)
    (hβ₀ : 0 < β) (hβτ : β < tau8 η₀ / 4)
    (hp : 0 < p) (hK : 0 < K) :
    ∃ n₀ : ℕ, ∃ C₀ : ℝ,
      ∀ n N : ℕ, ∀ E : Fin N → Fin N → Prop,
        ∀ X Y : Finset (Fin N), ∀ G : Colour, ∀ M : TagMix N,
          LargeAt n₀ C₀ n N →
          DiscOne E X Y ((n : ℝ) ^ η₀) ((n : ℝ) ^ η₀) ((n : ℝ) ^ (-η₀)) →
          M.Balanced K →
          (∀ i, 0 < M.Λ i →
            (M.μ i).SupportedIn X ∧ (M.ν i).SupportedIn Y ∧
            (M.μ i).WidthLE ((n : ℝ) ^ β) ∧ (M.ν i).WidthLE ((n : ℝ) ^ γ) ∧
            (∀ x, 0 < (M.μ i).w x →
              1 - Real.exp (-((n : ℝ) ^ p)) ≤ rowDeg E G x (M.ν i))) →
          CubeAt n N E := by
  obtain ⟨n₀, C₀, hshot⟩ := asymmetric_purity η₀ γ β p K hη₀ hγ₀ hγ₁ hβ₀ hβτ hp hK
  refine ⟨n₀, C₀, ?_⟩
  intro n N E X Y G M hLarge hDisc hBal hRows
  let M' : TagMix N := {
    ι := M.ι
    Λ := M.Λ
    Λ_nonneg := M.Λ_nonneg
    Λ_sum := M.Λ_sum
    μ := M.ν
    ν := M.μ
  }
  have hBal' : M'.Balanced K := ⟨hBal.2, hBal.1⟩
  have hDisc' : DiscOne (transposeRel E) Y X
      ((n : ℝ) ^ η₀) ((n : ℝ) ^ η₀) ((n : ℝ) ^ (-η₀)) := by
    exact (DiscOne.transpose_iff E X Y
      ((n : ℝ) ^ η₀) ((n : ℝ) ^ η₀) ((n : ℝ) ^ (-η₀))).mpr hDisc
  have hRows' : ∀ i, 0 < M'.Λ i →
      (M'.μ i).SupportedIn Y ∧ (M'.ν i).SupportedIn X ∧
      (M'.μ i).WidthLE ((n : ℝ) ^ γ) ∧ (M'.ν i).WidthLE ((n : ℝ) ^ β) ∧
      (∀ x, 0 < (M'.ν i).w x →
        1 - Real.exp (-((n : ℝ) ^ p)) ≤ colDeg (transposeRel E) G (M'.μ i) x) := by
    intro i hi
    rcases hRows i hi with ⟨hμX, hνY, hμw, hνw, hdeg⟩
    refine ⟨hνY, hμX, hνw, hμw, ?_⟩
    intro x hx
    simpa only [colDeg_transpose] using hdeg x hx
  have hLarge' : LargeAt n₀ C₀ n N := hLarge
  have hCube' := hshot n N (transposeRel E) Y X G M' hLarge' hDisc' hBal' hRows'
  exact CubeAt.of_transpose hCube'

end HypercubeRamsey
