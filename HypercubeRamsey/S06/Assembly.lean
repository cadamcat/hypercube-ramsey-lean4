import HypercubeRamsey.S06.Reduction
import HypercubeRamsey.Framework.Hall

/-!
# Section 6 one-shot export

The exported statement is the scratch-B/L6.1 one-shot form.  The final cube
step is assembled from the odd injection and fractional even rows using the
framework Hall embedding theorem.
-/

namespace HypercubeRamsey
namespace S06

open OAI.HypercubeRamsey

abbrev EvenRole6 (n : ℕ) := {v : CubeVertex n // IsEvenRole v}
abbrev OddRole6 (n : ℕ) := {v : CubeVertex n // ¬ IsEvenRole v}

noncomputable instance evenRole6Fintype (n : ℕ) : Fintype (EvenRole6 n) := by
  classical
  exact Subtype.fintype IsEvenRole

noncomputable instance oddRole6Fintype (n : ℕ) : Fintype (OddRole6 n) := by
  classical
  exact Subtype.fintype (fun v => ¬ IsEvenRole v)

/-- The final Hall data: an injective odd placement and fractional even rows. -/
structure FractionalRows6 (n N : ℕ) (E : Fin N → Fin N → Prop) (G : Colour) where
  oddMap : OddRole6 n → Fin N
  oddInjective : Function.Injective oddMap
  evenRows : EvenRole6 n → Fin N → ℝ
  evenNonneg : ∀ a x, 0 ≤ evenRows a x
  evenMass : ∀ a, ∑ x, evenRows a x = 1
  evenSupport : ∀ a x, evenRows a x ≠ 0 →
    ∀ b : OddRole6 n, (cube n).Adj a.1 b.1 → Hits E G x (oddMap b)
  columnLoad : ∀ x, ∑ a, evenRows a x ≤ 1

/-- L6.1m: the odd injection and posterior reconstruction supply Hall data. -/
theorem L6_1m {n N : ℕ} {E : Fin N → Fin N → Prop} {G : Colour}
    {γ Dstar α : ℝ} {M : TagMix N}
    (parents : ParentCase6 n N E G M γ Dstar)
    (g : ChunkGeometry6 n α)
    (states : StateEncoding6 g)
    (C : ConditionedCase6 n N parents g states)
    (o : HeightOutcome6 C.heightSetup) (ho : ∃ c, HeightConclusion6 C.heightSetup o c)
    (R : SelectedOddRows6 C.oddInput) : Nonempty (FractionalRows6 n N E G) := by
  sorry

/-- L6.1n and F-HallEmbed: the fractional rows give a monochromatic cube in colour `G`. -/
theorem L6_1n {n N : ℕ} {E : Fin N → Fin N → Prop} {G : Colour}
    (R : FractionalRows6 n N E G) : CubeAt n N E := by
  classical
  let support : EvenRole6 n → Finset (Fin N) := fun a =>
    Finset.univ.filter fun x => R.evenRows a x ≠ 0
  obtain ⟨evenMap, evenInjective, evenSupport⟩ :=
    exists_injective_of_fractional R.evenRows support R.evenNonneg R.evenMass
      (by
        intro a x hx
        by_contra hne
        apply hx
        simp [support, hne])
      R.columnLoad
  refine ⟨G, cube_copy_of_parts evenMap R.oddMap evenInjective R.oddInjective ?_⟩
  intro a b hab
  have hmem := evenSupport a
  simp [support] at hmem
  have hne : R.evenRows a (evenMap a) ≠ 0 := hmem
  exact R.evenSupport a (evenMap a) hne b hab

/-- L6.1 (one-shot form), with the frozen binders and hypotheses from scratch-B. -/
theorem small_polynomial_broad_side_core :
    ∃ Dstar > (0 : ℝ), ∀ γ p₀ K : ℝ, 0 < γ → γ < 1 → 0 < p₀ → 0 < K →
      ∃ (n₀ : ℕ) (C₀ : ℝ),
        ∀ (n N : ℕ) (E : Fin N → Fin N → Prop) (G : Colour) (M : TagMix N),
          LargeAt n₀ C₀ n N → M.Balanced K →
          (∀ i, 0 < M.Λ i → (M.μ i).WidthLE ((n : ℝ) ^ γ)) →
          (∀ i, 0 < M.Λ i → (M.ν i).CapLE ((n : ℝ) ^ Dstar)) →
          (∀ i y, 0 < M.Λ i → 0 < (M.ν i).w y →
            1 - (n : ℝ) ^ (-p₀) ≤ colDeg E G (M.μ i) y) →
          CubeAt n N E := by
  classical
  obtain ⟨Dstar, hDstar⟩ := L6_1_constants
  refine ⟨Dstar, hDstar, ?_⟩
  intro γ p₀ K hγ0 hγ1 hp hK
  obtain ⟨params⟩ :=
    L6_1_parameters Dstar γ p₀ K hDstar ⟨hγ0, hγ1⟩ hp hK
  refine ⟨params.n₀, params.C₀, ?_⟩
  intro n N E G M hLarge hBal hWidth hCap hDeg
  rcases L6_1a M hLarge hBal hWidth hCap hDeg hDstar with hCube | hParents
  · exact hCube
  · let parents : ParentCase6 n N E G M γ Dstar := Classical.choice hParents
    obtain ⟨geometry, _hmLower, _hmUpper⟩ :=
      params.geometry_available n (le_trans params.geometry_threshold hLarge.1)
    obtain ⟨states⟩ := L6_1e geometry
    let conditioned : ConditionedCase6 n N parents geometry states :=
      Classical.choice (L6_1h parents geometry states)
    obtain ⟨heightOutcome, heightExponent, heightSuccess⟩ :=
      L6_1i conditioned.heightSetup conditioned.heightHypotheses
    obtain ⟨oddRows⟩ := L6_1j conditioned.oddInput
    obtain ⟨hallRows⟩ := L6_1m parents geometry states conditioned heightOutcome
      ⟨heightExponent, heightSuccess⟩ oddRows
    exact L6_1n (G := G) hallRows

end S06

/-- Public L6.1 export, matching the statement in `scratch-B/StatementsBody.lean`. -/
theorem small_polynomial_broad_side :
    ∃ Dstar > (0 : ℝ), ∀ γ p₀ K : ℝ, 0 < γ → γ < 1 → 0 < p₀ → 0 < K →
      ∃ (n₀ : ℕ) (C₀ : ℝ),
        ∀ (n N : ℕ) (E : Fin N → Fin N → Prop) (G : Colour) (M : TagMix N),
          LargeAt n₀ C₀ n N → M.Balanced K →
          (∀ i, 0 < M.Λ i → (M.μ i).WidthLE ((n : ℝ) ^ γ)) →
          (∀ i, 0 < M.Λ i → (M.ν i).CapLE ((n : ℝ) ^ Dstar)) →
          (∀ i y, 0 < M.Λ i → 0 < (M.ν i).w y →
            1 - (n : ℝ) ^ (-p₀) ≤ colDeg E G (M.μ i) y) →
          CubeAt n N E :=
  S06.small_polynomial_broad_side_core

end HypercubeRamsey
