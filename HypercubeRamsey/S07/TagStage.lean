import HypercubeRamsey.S07.Profiles
import HypercubeRamsey.S03.ConditionalAvoidance
import HypercubeRamsey.Tools.ScatteredUnion

/-!
# L7.1, Step 2: filter tails, tag avoidance and typical tags

Source: `sections/07-…tex`, lines 136–194.  `cond_product_bound` is the local-lemma tool used by all three
conditioning steps (tags here, anchors in Step 4, targets in Step 6).
-/

namespace HypercubeRamsey.S07

open Classical OAI.HypercubeRamsey
open scoped BigOperators

/-- Lemma 3.4 on a product law with free coordinates (TeX 03, Lemma 3.4 and the independent-variables paragraph
after it; `S03/ConditionalAvoidance.lean`): with events joined when their scopes meet, the avoidance event has
positive mass; removing the events whose scopes meet `U` costs `∏ (1 - x)^{-1}` (third assertion), and the
remaining events are independent of the coordinates in `U`. -/
theorem cond_product_bound : CondProductBound := by
  sorry

/-- L7.1d(i) (07:136–154): the raw mean cross-failure probability at a key is at most `4s²K n^{-D₀}`.  In a step
of a cross order the current filtered law `τ` has width `≤ n^{d/2} + 2cs log n < n^{1/4}`, and the next anchor
has raw marginal `α` with `N α ≤ K`, independent of the history; if `α(H_τ) ≥ K n^{-D₀}`,
`H_τ = {x : d_G(x, τ) < n^{-c}}`, the restriction of `α` to `H_τ` violates (7.1).  There are at most `(2s)²`
order–step pairs. -/
theorem cross_fail_mean (D₀ d : ℝ) (hd : 0 < d) (hd' : d < 1 / 8) :
    ∃ n₀ : ℕ, ∀ n ≥ n₀, ∀ {N : ℕ} {E : Fin N → Fin N → Prop} {G : Colour} {X Y : Finset (Fin N)}
      {p κ : ℝ} (Γ : Geom d n) (M : Menu7 n N E G X Y d p κ) (Q : Γ.Key → FinProb M.ι) (K : ℝ),
      0 < N → GeomLocal Γ → (∀ g x, (N : ℝ) * ∑ i, (Q g).w i * (M.μ i).w x ≤ K) →
      Eq71At D₀ d n N E X Y →
      ∀ g, (FinProb.pi Q).expect (fun σ => crossFailKey Γ M σ g) ≤
        4 * (gS d n : ℝ) ^ 2 * K * (n : ℝ) ^ (-D₀) := by
  sorry

/-- L7.1e(i)–(ii) (07:163–175): the tag events satisfy the local-lemma input with charge `n^{-D₀/4}`: `B_g`
reads the tags on `{g} ∪ E(g)`, two events meet only within grid distance two, and Markov's inequality gives
`Pr(B_g) ≤ 4s²K n^{-D₀/2} ≤ n^{-D₀/4} (1 - n^{-D₀/4})^{(2s+1)²}` for large `n`. -/
theorem tag_lll (D₀ d K : ℝ) (hD₀ : 0 < D₀) (hd : 0 < d) (hd' : d < D₀ / 1000) :
    ∃ n₀ : ℕ, ∀ n ≥ n₀, ∀ {N : ℕ} {E : Fin N → Fin N → Prop} {G : Colour} {X Y : Finset (Fin N)}
      {p κ : ℝ} (Γ : Geom d n) (M : Menu7 n N E G X Y d p κ) (Q : Γ.Key → FinProb M.ι),
      GeomLocal Γ → GeomBalls Γ →
      (∀ g, (FinProb.pi Q).expect (fun σ => crossFailKey Γ M σ g) ≤
        4 * (gS d n : ℝ) ^ 2 * K * (n : ℝ) ^ (-D₀)) →
      TagLLL Γ M Q D₀ := by
  sorry

/-- L7.1e(iii) (07:177–194): under the tag law the tags are typical with constant `8(K+1)` except with probability
`n 2^n 4^{-n}`.  Moments: for even roles with distinct grid keys, removing the at most `2s+1` tag events touching
each key costs a factor `2` per role and leaves independent raw tags with means `≤ K` (profile (i)); then
Lemma 3.6 with near = same grid key (fraction `(2n^{-d/4})^s`, cap `e^{n^{d/2}}`) and a union over labels
(`scatteredMoments_union_labels`). -/
theorem typical_tags (D₀ d K : ℝ) (hD₀ : 0 < D₀) (hd : 0 < d) (hd' : d < D₀ / 1000) (hK : 0 ≤ K) :
    ∃ n₀ : ℕ, ∀ n ≥ n₀, ∀ {N : ℕ} {E : Fin N → Fin N → Prop} {G : Colour} {X Y : Finset (Fin N)}
      {p κ : ℝ} (Γ : Geom d n) (M : Menu7 n N E G X Y d p κ) (Q : Γ.Key → FinProb M.ι),
      0 < N → N ≤ n * 2 ^ n → CondProductBound → GeomFacts Γ →
      (∀ g x, (N : ℝ) * ∑ i, (Q g).w i * (M.μ i).w x ≤ K) → TagLLL Γ M Q D₀ →
      (tagLaw Γ M Q D₀).pr (fun σ => ¬ Typical Γ M (8 * (K + 1)) σ) ≤
        (n : ℝ) * 2 ^ n * (1 / 4 : ℝ) ^ n := by
  sorry

/-- Step 2 assembled: the tag events satisfy the local-lemma input and the tag law gives typical tags. -/
theorem tag_stage (D₀ d K : ℝ) (hD₀ : 0 < D₀) (hD₀' : D₀ < 1 / 10) (hd : 0 < d)
    (hd' : d < D₀ / 1000) (hK : 0 ≤ K) :
    ∃ n₀ : ℕ, ∀ n ≥ n₀, ∀ {N : ℕ} {E : Fin N → Fin N → Prop} {G : Colour} {X Y : Finset (Fin N)}
      {p κ : ℝ} (Γ : Geom d n) (M : Menu7 n N E G X Y d p κ) (P : Profiles7 Γ M K),
      0 < N → N ≤ n * 2 ^ n → GeomFacts Γ → Eq71At D₀ d n N E X Y →
      TagLLL Γ M P.Q D₀ ∧
        (tagLaw Γ M P.Q D₀).pr (fun σ => ¬ Typical Γ M (8 * (K + 1)) σ) ≤
          (n : ℝ) * 2 ^ n * (1 / 4 : ℝ) ^ n := by
  have hd8 : d < 1 / 8 := by linarith
  obtain ⟨n₁, hcross⟩ := cross_fail_mean D₀ d hd hd8
  obtain ⟨n₂, hlll⟩ := tag_lll D₀ d K hD₀ hd hd'
  obtain ⟨n₃, htyp⟩ := typical_tags D₀ d K hD₀ hd hd' hK
  refine ⟨max n₁ (max n₂ n₃), ?_⟩
  intro n hn N E G X Y p κ Γ M P hN hNle hG h71
  have hn₁ : n₁ ≤ n := le_trans (le_max_left _ _) hn
  have hn₂ : n₂ ≤ n := le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) hn
  have hn₃ : n₃ ≤ n := le_trans (le_trans (le_max_right _ _) (le_max_right _ _)) hn
  have hT : TagLLL Γ M P.Q D₀ :=
    hlll n hn₂ Γ M P.Q hG.loc hG.balls (hcross n hn₁ Γ M P.Q K hN hG.loc P.mu_mean h71)
  exact ⟨hT, htyp n hn₃ Γ M P.Q hN hNle cond_product_bound hG P.mu_mean hT⟩

end HypercubeRamsey.S07
