import Mathlib

/-!
# Lemma 3.5: scattered moments

Source: `sections/03-…tex`, Lemma 3.5 and its proof. The success event is `succ`; the comparison means are
`d`; `near v` is the near set of `v` (containing `v`), of size at most `f |U|`.
-/

namespace HypercubeRamsey

theorem scattered_moments {Ω : Type*} [Fintype Ω] (w : Ω → ℝ) (hw : ∀ ω, 0 ≤ w ω)
    {U : Type*} [Fintype U] [DecidableEq U] [Nonempty U]
    (succ : Finset Ω) (Z : U → Ω → ℝ) (hZ0 : ∀ v ω, 0 ≤ Z v ω) (L : ℝ) (hL : 0 ≤ L)
    (hZL : ∀ v, ∀ ω ∈ succ, Z v ω ≤ L)
    (near : U → Finset U) (hself : ∀ v, v ∈ near v) (f : ℝ)
    (hnear : ∀ v, ((near v).card : ℝ) ≤ f * Fintype.card U)
    (n : ℕ) (K : ℝ) (hK : 1 ≤ K) (d : U → ℝ) (hd : ∀ v, 0 ≤ d v)
    (hjoint : ∀ (m : ℕ), m ≤ n → ∀ s : Fin m → U,
      (∀ i j : Fin m, j < i → s i ∉ near (s j)) →
        ∑ ω ∈ succ, w ω * ∏ i, Z (s i) ω ≤ K ^ m * ∏ i, d (s i)) :
    ∑ ω ∈ succ, w ω * ((Fintype.card U : ℝ)⁻¹ * ∑ v, Z v ω) ^ n ≤
      K ^ n * ((Fintype.card U : ℝ)⁻¹ * ∑ v, d v + n * f * L) ^ n := sorry

end HypercubeRamsey
