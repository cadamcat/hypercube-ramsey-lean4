import HypercubeRamsey.S04.CoreLemmas
import HypercubeRamsey.S04.ValidityNodes_q_s04_valid

/-!
# L4.1e: validity of a fixed ID set

Source: `sections/04-…tex`, lines 235–298; blueprint L4.1e1–e3.  Masks are fixed; the tuples `W_{c,κ}`,
`(c, κ) ∈ D × Z_u`, are exposed entry by entry (any specified tuple last).  After a successful prefix (all retained
fractions `≥ e^{-L}`), the current law `η` on `Y` is the masked second law restricted to the previous hits; its width
is at most `sY + 1 + log 2 + kT|Z_u|L` and `kT|Z_u|L = n^{γ - 0.53ω + h} = o(n^{γ-ω/2})` (`KeyNbrCard`).
-/

namespace HypercubeRamsey.S04

open Classical OAI.HypercubeRamsey
open scoped BigOperators

/-- L4.1e1, low entries (04:245–252): if an entry from `μ_i^S` had `q(x) = d_G(x, η) < e^{-L}` with probability
above `exp(-n^{β-ω/2}/4)`, conditioning `μ_i^S` on that event (width `≤ sX + log 2 + n^{β-ω/2}/4 ≤ 2n^β`) and `η`
would be a pair on `X × Y` at doubled widths with `G`-density below `e^{-L} = exp(-n^h)`, excluded by `NoPure`. -/
theorem entry_low (β γ : ℝ) (hβ : 0 < β) (hβγ : β ≤ γ) (hγ : γ < 1) :
    ∃ n₀ : ℕ, ∀ n ≥ n₀, ∀ {N : ℕ} {E : Fin N → Fin N → Prop} {G : Colour} {X Y : Finset (Fin N)}
      (M : Menu4 β γ G n N E X Y), NoPure β γ n N E G X Y → EntryLow M := by
  exact HypercubeRamsey.Lane_q_s04_valid.entry_low_core β γ hβ hβγ hγ

/-- L4.1e1, own key (04:254–281): for `η` on the support of `ν_i` within the second width margin, (P4) gives
`Pr(q > p + n^{-ω/3}) ≤ exp(-n^{β-ω/2}/4)`; `2μ_i - μ_i^S` is a law of width `≤ sX + log 2`, so (P3) and (P4) give
`E q ≥ 2(p - n^{-ω/5}) - (p + n^{-ω/3}) ≥ p - 3n^{-ω/5}`; comparing, `Pr(q < p - a_i/4) ≤ 20 n^{-ω/5}/a_i`. -/
theorem entry_own (β γ : ℝ) (hβ : 0 < β) (hβγ : β ≤ γ) (hγ : γ < 1) :
    ∃ n₀ : ℕ, ∀ n ≥ n₀, ∀ {N : ℕ} {E : Fin N → Fin N → Prop} {G : Colour} {X Y : Finset (Fin N)}
      (M : Menu4 β γ G n N E X Y), EntryOwn M := by
  exact HypercubeRamsey.Lane_q_s04_valid.entry_own_core β γ hβ hβγ hγ

/-- L4.1e2, low part (04:235–252, 293–295): in any exposure order the first entry retaining less than `e^{-L}`
follows a successful prefix, so (`EntryLow`, width via `KeyNbrCard`) it occurs with probability at most
`kT|Z_u| exp(-n^{β-ω/2}/4)`; on the complement every fraction is `≥ e^{-L}`, which gives the mass condition (any
order) and every cross-key ratio (that tuple last).  A union over the `≤ T|Z_u| + 1` orders is at most
`exp(-2n^{ω/5})`. -/
theorem exposure_low (β γ : ℝ) (hβ : 0 < β) (hβγ : β ≤ γ) (hγ : γ < 1) :
    ∃ n₀ : ℕ, ∀ n ≥ n₀, ∀ {N : ℕ} {E : Fin N → Fin N → Prop} {G : Colour} {X Y : Finset (Fin N)}
      (M : Menu4 β γ G n N E X Y) (tag : Key β γ n → M.ι),
      KeyNbrCard β γ n → EntryLow M → ExposureLow M tag := by
  sorry

/-- L4.1e2, own key (04:283–295): expose the own-key tuple `W_{c,g(u)}` last; a dip is an entry with
`q < p - a_i/4`, its indicator stopped at the first entry with `q < e^{-L}`.  By `EntryOwn` the conditional dip
probability is `O(n^{-ω/5}/a_i) = o(a_*/L)`, so Azuma bounds the number of dips by `a_* k/(20L)` except with
probability `exp(-Ω(k a_*²/L²))`, `k a_*²/L² = n^{ω/3 - 4h + o(1)}`.  On a path without a step below `e^{-L}`
(`EntryLow`) the `k` own-key fractions multiply to at least `exp(k(-log 2 + c₁ a_*))` (`log q ≥ -log 2 + .7a_i`
off dips, `≥ -L` at dips). -/
theorem own_ratio (β γ : ℝ) (hβ : 0 < β) (hβγ : β ≤ γ) (hγ : γ < 1) :
    ∃ n₀ : ℕ, ∀ n ≥ n₀, ∀ {N : ℕ} {E : Fin N → Fin N → Prop} {G : Colour} {X Y : Finset (Fin N)}
      (M : Menu4 β γ G n N E X Y) (tag : Key β γ n → M.ι),
      KeyNbrCard β γ n → EntryLow M → EntryOwn M → OwnRatio M tag := by
  sorry

/-- L4.1e3 (04:235–236, 296–298): invalidity is the low failure or an own-key ratio failure at one of the
`≤ T` IDs; `(1 + T) exp(-2n^{ω/5}) ≤ exp(-n^{ω/5})` for large `n`. -/
theorem valid_prob (β γ : ℝ) (hβ : 0 < β) (hβγ : β ≤ γ) (hγ : γ < 1) :
    ∃ n₀ : ℕ, ∀ n ≥ n₀, ∀ {N : ℕ} {E : Fin N → Fin N → Prop} {G : Colour} {X Y : Finset (Fin N)}
      (M : Menu4 β γ G n N E X Y) (tag : Key β γ n → M.ι),
      ExposureLow M tag → OwnRatio M tag → ValidProb M tag := by
  exact HypercubeRamsey.Lane_q_s04_valid.valid_prob_core β γ hβ hβγ hγ

end HypercubeRamsey.S04
