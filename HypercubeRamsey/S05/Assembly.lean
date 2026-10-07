import HypercubeRamsey.S05.Selection

/-!
# L5.1n–o and the Part B one-shot export

The construction outputs an injective odd assignment together with fractional even rows on its common
neighborhoods (L5.1n).  Their assembly uses the repository's Hall embedding interface and has no proof hole of
its own.
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

/-- L5.1n (05:15–18; construction 05:40–1282 without the final Hall step): for large `n` and `N ≥ C₀ 2^n`, the
staged experiment has an outcome giving an injective odd assignment together with fractional even rows on
the common `G`-neighborhoods with column loads at most one (05:1275–1281: "with positive probability the odd
assignment is injective and every even row is a probability law on its common neighborhood, with all even
column sums at most one").

The odd assignment is an output, not an input: the paper's even rows exist only for odd labels drawn by the
clock sampler from the odd rows of a successful history (05:1063–1084, 05:1170–1177, 05:1259–1273), so no
statement quantifying over every injective assignment is true.  This node therefore covers L5.1a–n and the
probabilistic part of L5.1o; it is a single construction node pending a Section 5 skeleton revision that
defines the staged experiment. -/
theorem L5_1n (γ K' χ : ℝ) (hγ : 0 < γ) (hγ' : γ < 1)
    (hK : 0 < K') (hχ : 0 < χ) :
    ∃ n₀ : ℕ, ∃ C₀ : ℝ, 0 < C₀ ∧
      ∀ (n N : ℕ) (E : Fin N → Fin N → Prop) (G : Colour)
        {ι : Type*} [Fintype ι] (Λ : ι → ℝ) (μ : ι → Law N),
        LargeAt n₀ C₀ n N → (∀ i, 0 ≤ Λ i) → (∑ i, Λ i = 1) →
        (∀ i, 0 < Λ i → (μ i).WidthLE ((n : ℝ) ^ γ)) →
        (∀ x, (N : ℝ) * ∑ i, Λ i * (μ i).w x ≤ K') →
        (∀ i, 0 < Λ i → χ * N ≤
          ((Finset.univ.filter (fun y => (95 : ℝ) / 100 ≤ colDeg E G (μ i) y)).card : ℝ)) →
        ∃ O : OddAssignment5 (n := n) (N := N) E G, Nonempty (EvenPlacement5 O) := by
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
  obtain ⟨n₀, C₀, _hC₀, hRows⟩ := L5_1n γ K' χ hγ hγ' hK hχ
  refine ⟨n₀, C₀, ?_⟩
  intro n N E G ι inst Λ μ hLarge hΛ hΛsum hwidth hbalance hgood
  obtain ⟨O, ⟨A⟩⟩ := hRows n N E G Λ μ hLarge hΛ hΛsum hwidth hbalance hgood
  exact cube_of_rows5 (L5_1o_rows O A)

end HypercubeRamsey
