import HypercubeRamsey.S04.CoreLemmas
import HypercubeRamsey.S04.GadgetNodes_q_s04_gadget

/-!
# L4.1c, L4.1d: the key gadget and the patch tags

Source: `sections/04-…tex`, lines 100–162; blueprint L4.1c, D4.3/L4.1d.
-/

namespace HypercubeRamsey.S04

open Classical OAI.HypercubeRamsey
open scoped BigOperators

/-- L4.1c(1) (04:118–127, 134–138): all one-bit changes of an input change at most one gadget, and within a
gadget produce at most `1 + 2 log₂ S` outputs (the first changed comparison on the search path and the direction of
the move determine the new multiset; the moving chunk stays on the same side of every elementary midpoint).  Hence
`|Z_u| ≤ 1 + G_n (2 log₂ S + 1) ≤ n^{γ - 0.9ω}` for large `n`. -/
theorem key_nbr_card (β γ : ℝ) (hβ : 0 < β) (hβγ : β ≤ γ) (hγ : γ < 1) :
    ∃ n₀ : ℕ, ∀ n ≥ n₀, KeyNbrCard β γ n := by
  sorry

/-- L4.1c(3) (04:134–136, 393–394): the key depends only on the `m = G_n s' ℓ ≤ 128 n^{γ+13ω}` special
coordinates, so at most `n^{γ+14ω}` coordinate flips of a vertex change its key (for large `n`). -/
theorem key_local (β γ : ℝ) (hβ : 0 < β) (hβγ : β ≤ γ) (hγ : γ < 1) :
    ∃ n₀ : ℕ, ∀ n ≥ n₀, KeyLocal β γ n := by
  obtain ⟨n₀, hn₀⟩ := HypercubeRamsey.Lane_q_s04_gadget.specialNum_eventually_bound hβ hβγ hγ
  refine ⟨n₀, ?_⟩
  intro n hn v
  exact (HypercubeRamsey.Lane_q_s04_gadget.keyLocal_le_specialNum n v).trans (hn₀ n hn)

/-- L4.1c(2) (04:128–143): for a fixed output each chunk lies on a prescribed side of a fixed midpoint, which has
probability at most `2/3` (each clipped endpoint has probability at least `1/3`: the counts are symmetric and the
central interval has `Binomial(ℓ, 1/2)`-mass `O(S² s'^{-3})`); chunks are independent and a parity class induces
the uniform law on the `m < n` special coordinates.  So each key has parity-class fraction at most
`(2/3)^{s' G_n} ≤ exp(-n^{γ+ω}/10)` for large `n`. -/
theorem key_fiber (β γ : ℝ) (hβ : 0 < β) (hβγ : β ≤ γ) (hγ : γ < 1) :
    ∃ n₀ : ℕ, ∀ n ≥ n₀, KeyFiber β γ n := by
  sorry

/-- D4.3/L4.1d (04:145–162): independent tags `tag κ ∼ ρ`; at a fixed label the normalized parity average is a
sum of independent terms `α_κ N μ_{tag κ}(x) ≤ exp(-n^{γ+ω}/10 + 3n^β/2)` (`KeyFiber` and the width `sX ≤ 3n^β/2`;
on the odd side `sY + 1 ≤ 3n^γ/2 + 1`) with mean at most `K`; bounded-summand concentration bounds a deviation `K`
by `exp(-Ω(exp(c n^{γ+ω})))`, and a union over the `2N ≤ 2n2^n` labels leaves an assignment with both averages at
most `2K`. -/
theorem tag_exists (β γ K : ℝ) (hβ : 0 < β) (hβγ : β ≤ γ) (hγ : γ < 1) (hK : 0 < K) :
    ∃ n₀ : ℕ, ∀ n ≥ n₀, KeyFiber β γ n →
      ∀ {N : ℕ} {E : Fin N → Fin N → Prop} {G : Colour} {X Y : Finset (Fin N)}
        (M : Menu4 β γ G n N E X Y) (ρ : FinProb M.ι), N ≤ n * 2 ^ n →
        Balanced ρ M.μ M.ν K → ∃ tag : Key β γ n → M.ι, TagBal M tag (2 * K) := by
  exact HypercubeRamsey.Lane_q_s04_gadget.tag_exists_bound β γ K hβ hβγ hγ hK

end HypercubeRamsey.S04
