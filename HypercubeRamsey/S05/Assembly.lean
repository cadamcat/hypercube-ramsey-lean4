import HypercubeRamsey.S05.Selection

/-!
# L5.1m–o and the Part B one-shot export

The two construction outputs are separated into an injective odd assignment and fractional even rows.  Their
assembly uses the repository's Hall embedding interface and has no proof hole of its own.
-/

namespace HypercubeRamsey

open Classical OAI.HypercubeRamsey

/-- The injective labels chosen for odd roles by the clock sampler. -/
structure OddAssignment5 {n N : ℕ} (E : Fin N → Fin N → Prop) (G : Colour) where
  label : {v : CubeVertex n // ¬ IsEvenRole v} → Fin N
  injective : Function.Injective label

open Classical in
/-- Fractional placement rows for even roles after the odd labels have been fixed. -/
structure EvenPlacement5 {n N : ℕ} {E : Fin N → Fin N → Prop} {G : Colour}
    (O : OddAssignment5 E G) where
  row : {v : CubeVertex n // IsEvenRole v} → Fin N → ℝ
  nonneg : ∀ a x, 0 ≤ row a x
  sum_one : ∀ a, ∑ x, row a x = 1
  common_neighborhood : ∀ a x, row a x ≠ 0 →
    ∀ b : {v : CubeVertex n // ¬ IsEvenRole v},
      (cube n).Adj a.1 b.1 → Hits E G x (O.label b)
  column_load : ∀ x, ∑ a, row a x ≤ 1

/-- L5.1m: successful high-row deletion budgets and clock sampling give an injective odd assignment. -/
theorem L5_1m (γ K' χ : ℝ) (hγ : 0 < γ) (hγ' : γ < 1)
    (hK : 0 < K') (hχ : 0 < χ) :
    ∃ n₀ : ℕ, ∃ C₀ : ℝ, 0 < C₀ ∧
      ∀ (n N : ℕ) (E : Fin N → Fin N → Prop) (G : Colour)
        {ι : Type*} [Fintype ι] (Λ : ι → ℝ) (μ : ι → Law N),
        LargeAt n₀ C₀ n N → (∀ i, 0 ≤ Λ i) → (∑ i, Λ i = 1) →
        (∀ i, 0 < Λ i → (μ i).WidthLE ((n : ℝ) ^ γ)) →
        (∀ x, (N : ℝ) * ∑ i, Λ i * (μ i).w x ≤ K') →
        (∀ i, 0 < Λ i → χ * N ≤
          ((Finset.univ.filter (fun y => (95 : ℝ) / 100 ≤ colDeg E G (μ i) y)).card : ℝ)) →
        Nonempty (OddAssignment5 (n := n) (N := N) E G) := by
  sorry

/-- L5.1n: after the odd assignment, deletion of primitive tuple blocks and the even load estimate give
fractional rows on common neighborhoods. -/
theorem L5_1n (γ K' χ : ℝ) (hγ : 0 < γ) (hγ' : γ < 1)
    (hK : 0 < K') (hχ : 0 < χ) (n₀ : ℕ) (C₀ : ℝ) (hC₀ : 0 < C₀)
    {n N : ℕ} (E : Fin N → Fin N → Prop) (G : Colour)
    {ι : Type*} [Fintype ι] (Λ : ι → ℝ) (μ : ι → Law N)
    (hLarge : LargeAt n₀ C₀ n N) (hΛ : ∀ i, 0 ≤ Λ i) (hΛsum : ∑ i, Λ i = 1)
    (hwidth : ∀ i, 0 < Λ i → (μ i).WidthLE ((n : ℝ) ^ γ))
    (hbalance : ∀ x, (N : ℝ) * ∑ i, Λ i * (μ i).w x ≤ K')
    (hgood : ∀ i, 0 < Λ i → χ * N ≤
      ((Finset.univ.filter (fun y => (95 : ℝ) / 100 ≤ colDeg E G (μ i) y)).card : ℝ))
    (O : OddAssignment5 (n := n) (N := N) E G) :
    Nonempty (EvenPlacement5 (n := n) (N := N) O) := by
  sorry

/-- L5.1o: the odd assignment and even fractional rows assemble into a cube row certificate. -/
def L5_1o_rows {n N : ℕ} {E : Fin N → Fin N → Prop} {G : Colour}
    (O : OddAssignment5 (n := n) (N := N) E G)
    (A : EvenPlacement5 (n := n) (N := N) O) :
    CubeRows5 (n := n) (N := N) E G := by
  exact {
    oddLabel := O.label
    odd_injective := O.injective
    evenRow := A.row
    row_nonneg := A.nonneg
    row_sum := A.sum_one
    row_supported := A.common_neighborhood
    column_load := A.column_load
  }

/-- L5.1, consumed one-shot form used by Part B. -/
theorem L5_1_consumed : ∀ γ K' χ : ℝ, 0 < γ → γ < 1 → 0 < K' → 0 < χ →
    ∃ (n₀ : ℕ) (C₀ : ℝ), ∀ (n N : ℕ) (E : Fin N → Fin N → Prop) (G : Colour)
      (ι : Type*) [Fintype ι] (Λ : ι → ℝ) (μ : ι → Law N),
      LargeAt n₀ C₀ n N → (∀ i, 0 ≤ Λ i) → ∑ i, Λ i = 1 →
      (∀ i, 0 < Λ i → (μ i).WidthLE ((n : ℝ) ^ γ)) →
      (∀ x, (N : ℝ) * ∑ i, Λ i * (μ i).w x ≤ K') →
      (∀ i, 0 < Λ i → χ * N ≤ ((Finset.univ.filter
        (fun y => (95 : ℝ) / 100 ≤ colDeg E G (μ i) y)).card : ℝ)) →
      CubeAt n N E := by
  intro γ K' χ hγ hγ' hK hχ
  obtain ⟨n₀, C₀, hC₀, hOdd⟩ := L5_1m γ K' χ hγ hγ' hK hχ
  refine ⟨n₀, C₀, ?_⟩
  intro n N E G ι inst Λ μ hLarge hΛ hΛsum hwidth hbalance hgood
  obtain ⟨O⟩ := hOdd n N E G Λ μ hLarge hΛ hΛsum hwidth hbalance hgood
  obtain ⟨A⟩ := L5_1n γ K' χ hγ hγ' hK hχ n₀ C₀ hC₀
    E G Λ μ hLarge hΛ hΛsum hwidth hbalance hgood O
  exact cube_of_rows5 (L5_1o_rows O A)

end HypercubeRamsey
