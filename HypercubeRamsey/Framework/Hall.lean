import Mathlib

/-!
# Hall interface

Fractional rows with column loads at most one give distinct representatives (Section 3, after Lemma 3.3).
-/

namespace HypercubeRamsey

theorem exists_injective_of_fractional {ι : Type*} [Fintype ι] [DecidableEq ι] {N : ℕ}
    (p : ι → Fin N → ℝ) (L : ι → Finset (Fin N))
    (hnonneg : ∀ v y, 0 ≤ p v y) (hsum : ∀ v, ∑ y, p v y = 1)
    (hsupp : ∀ v y, y ∉ L v → p v y = 0) (hload : ∀ y, ∑ v, p v y ≤ 1) :
    ∃ f : ι → Fin N, Function.Injective f ∧ ∀ v, f v ∈ L v := sorry

end HypercubeRamsey
