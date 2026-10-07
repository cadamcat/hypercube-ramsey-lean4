import HypercubeRamsey.S04.CoreLemmas

/-!
# L4.1h: mask profiles balancing the rows

Source: `sections/04-…tex`, lines 437–496; blueprint L4.1h.
-/

namespace HypercubeRamsey.S04

open Classical OAI.HypercubeRamsey
open scoped BigOperators

/-- L4.1h, selection probability (04:469–477): `E` at `(a, c)` needs `c` present (probability `λ/V`), legal
eligibility on `a`'s consultation ball and `sel a = c`.  At level zero, given positions and masks/tuples,
L3.8i bounds `Pr(height 0 ∧ sel = c) ≤ 3/λ`; at a positive level, L3.8g with `c` forced present bounds
`Pr(legal ∧ height > 0) ≤ exp(-n^{c₃})`.  Both bounds are uniform over the eligibility selector, hence over all mask
profiles (`Aux` = masks × tuples). -/
theorem select_prob (β γ : ℝ) (hβ : 0 < β) (hβγ : β ≤ γ) (hγ : γ < 1) :
    ∃ c₃ > (0 : ℝ), ∃ n₀ : ℕ, ∀ n ≥ n₀,
      ∀ {N : ℕ} {E : Fin N → Fin N → Prop} {G : Colour} {X Y : Finset (Fin N)}
        (M : Menu4 β γ G n N E X Y) (tag : Key β γ n → M.ι), SelectBound M tag c₃ := by
  sorry

/-- L4.1h (04:449–496): Lemma 3.3(2) (`simultaneous_profiles`) with players the odd roles `u` (output `E p_u`,
bound `2ν_{i_{g(u)}}`) and the pairs `(c, κ)` (output: the expected even rows of the roles with key `κ` selecting
`c`, bound `2 n_{c,κ} w_c μ_{i_κ}`, `n_{c,κ}` = number of even roles with key `κ` within distance `r` of `c`).  Against
prices `π ≥ 0` the pure mask `{π ≤ 2⟨π, law⟩}` (mass `≥ 1/2` by Markov) answers every profile of the others: odd rows
and even rows are supported in their masks with mass at most one (`EvenRowFacts`), and the even output needs `E`,
of probability at most `w_c` (`SelectBound`); separation (`finite_minimax`) turns price responses into mixed
responses.  Summing, `∑_{c ∈ range a} w_c ≤ 3 + Hλe^{-n^{c₃}} ≤ 4` gives the even bound with `8`. -/
theorem mask_profiles (β γ : ℝ) (hβ : 0 < β) (hβγ : β ≤ γ) (hγ : γ < 1) (c₃ : ℝ) (hc₃ : 0 < c₃) :
    ∃ n₀ : ℕ, ∀ n ≥ n₀, ∀ {N : ℕ} {E : Fin N → Fin N → Prop} {G : Colour} {X Y : Finset (Fin N)}
      (M : Menu4 β γ G n N E X Y) (tag : Key β γ n → M.ι),
      SelectBound M tag c₃ → EvenRowFacts M tag →
      ∃ (q : XProf M tag) (q' : YProf M tag), ProfOK M tag q q' := by
  sorry

end HypercubeRamsey.S04
