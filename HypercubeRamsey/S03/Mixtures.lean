import HypercubeRamsey.Framework.Law

/-!
# Lemma 3.3: balanced mixtures and simultaneous profiles

Source: `sections/03-…tex`, Lemma 3.3 and its proof (separation for the first assertion, Kakutani's theorem for
the second).
-/

namespace HypercubeRamsey

/-- Lemma 3.3, first assertion, at one dimension: a finite menu of law pairs that survives every removal of at
most `κ N` labels per side has a mixture with all expected atoms at most `4 / (κ N)`. -/
theorem balanced_mixture {N : ℕ} (hN : 0 < N) {ι : Type*} [Fintype ι]
    (μ ν : ι → Law N) (κ : ℝ) (hκ : 0 < κ)
    (havail : ∀ RX RY : Finset (Fin N), (RX.card : ℝ) ≤ κ * N → (RY.card : ℝ) ≤ κ * N →
      ∃ i, (∀ x ∈ RX, (μ i).w x = 0) ∧ (∀ y ∈ RY, (ν i).w y = 0)) :
    ∃ t : ι → ℝ, (∀ i, 0 ≤ t i) ∧ ∑ i, t i = 1 ∧
      (∀ x, ∑ i, t i * (μ i).w x ≤ 4 / (κ * N)) ∧
      (∀ y, ∑ i, t i * (ν i).w y ≤ 4 / (κ * N)) := sorry

/-- Lemma 3.3, second assertion: finitely many players with finite action sets; player `j`'s expected output
vector, under independent profiles, can be pushed below `b j` by a best response to any profiles of the others.
Then one profile meets every bound simultaneously. -/
theorem simultaneous_profiles {J : Type*} [Fintype J] [DecidableEq J]
    {A : J → Type*} [∀ j, Fintype (A j)] [∀ j, DecidableEq (A j)] [∀ j, Nonempty (A j)]
    {m : J → ℕ} (X : ∀ j, (∀ i, A i) → Fin (m j) → ℝ) (b : ∀ j, Fin (m j) → ℝ)
    (hresp : ∀ j (q : ∀ i, A i → ℝ), (∀ i a, 0 ≤ q i a) → (∀ i, ∑ a, q i a = 1) →
      ∃ qj : A j → ℝ, (∀ a, 0 ≤ qj a) ∧ ∑ a, qj a = 1 ∧
        ∀ r, ∑ σ : (∀ i, A i), (∏ i, (Function.update q j qj) i (σ i)) * X j σ r ≤ b j r) :
    ∃ q : ∀ i, A i → ℝ, (∀ i a, 0 ≤ q i a) ∧ (∀ i, ∑ a, q i a = 1) ∧
      ∀ j r, ∑ σ : (∀ i, A i), (∏ i, q i (σ i)) * X j σ r ≤ b j r := sorry

end HypercubeRamsey
