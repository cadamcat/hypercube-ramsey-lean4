import HypercubeRamsey.S04.CoreLemmas

/-!
# L4.1i–k: odd loads and the odd injection, predictive thresholds, even loads

Source: `sections/04-…tex`, lines 498–597; blueprint L4.1i, L4.1j, L4.1k.  The injection law at a pre-injection
history is any law with `InjOK` (one exists by Lemma 3.9, node `injection_exists`); the probability bounds hold for
every such family.
-/

namespace HypercubeRamsey.S04

open Classical OAI.HypercubeRamsey
open scoped BigOperators

/-- L4.1i, odd loads (04:499–508): Lemma 3.6 (`scattered_moments`) with `Z_u = N p_u(y)`, cap `exp(2n^γ)`
(`OddCap`), near sets the balls of radius `2 locR` (fraction `V(2 locR)/2^{n-1}`, `n · fraction · cap → 0`),
separated factorization (`OddFactor`, `K = 1`) and mean `≤ 2·2K` (`ProfOK.odd`, `TagBal`); Markov at
`4(4K + 1)` and a union over the `N ≤ n2^n` labels leave probability `≤ n2^{-n}`; since `|B|/N ≤ 1/(2C₀)`, the column
sums are then at most `1/10` once `C₀ ≥ 20(4K + 1)`. -/
theorem odd_load_prob (β γ K : ℝ) (hβ : 0 < β) (hβγ : β ≤ γ) (hγ : γ < 1) (hK : 0 < K) :
    ∃ n₀ : ℕ, ∃ C₀ : ℝ, ∀ n ≥ n₀, ∀ N : ℕ, LargeHost C₀ n N →
      ∀ {E : Fin N → Fin N → Prop} {G : Colour} {X Y : Finset (Fin N)}
        (M : Menu4 β γ G n N E X Y) (tag : Key β γ n → M.ι) (q : XProf M tag) (q' : YProf M tag),
        TagBal M tag (2 * K) → ProfOK M tag q q' → OddFactor M tag q q' → OddCap M tag →
        (prepLaw M tag q q').pr (fun ω => ∃ y, 1 / 10 < oddCol M tag ω y) ≤ 1 / 10 := by
  sorry

/-- L4.1i, injection (04:512–526): on `S_pre` all odd rows are probabilities (`GeoCons`) with atoms
`≤ exp(2n^γ)/N ≤ N^{-0.95}` (`OddCap`, `N ≥ 2^n`) and column sums `≤ 1/10 ≤ 0.4`; Lemma 3.9
(`near_product_injection`, `d = N`, labels = outputs) gives an injective law whose joint probabilities on
`≤ n² ≤ N^{0.025}` outputs are at most `exp(N^{-0.04} n²) ≤ 2` times the product of the rows. -/
theorem injection_exists (β γ : ℝ) (hβ : 0 < β) (hβγ : β ≤ γ) (hγ : γ < 1) :
    ∃ n₀ : ℕ, ∀ n ≥ n₀, ∀ N : ℕ, (2 : ℝ) ^ n ≤ N →
      ∀ {E : Fin N → Fin N → Prop} {G : Colour} {X Y : Finset (Fin N)}
        (M : Menu4 β γ G n N E X Y) (tag : Key β γ n → M.ι),
        GeoCons M tag → OddCap M tag →
        ∀ ω : Prep M tag, SPre M tag ω → ∃ J, InjOK M tag ω J := by
  sorry

/-- L4.1j (04:528–551): for a fixed even role `a` and reference `c`, on `S_pre` with `sel a = c` the event `E`
holds (`GeoCons`); the injection comparison (`InjOK`, the `n` neighbouring outputs) bounds the failure by twice its
product-draw probability, where `1_E ∏ p_u(y_u) = F_z(y)` at the actual tuple `z`; dropping `S_pre`, resampling
`z` from its prior (`Resample`; the failure set does not read `z`, `RefIndep`) gives `∑_{y ∈ D_c} M_c(y)`, at most
`ε₄ ∑ Q = ε₄` by Lemma 3.7(1) (`gated_posterior`).  A union over the `≤ 2^n · 2^n (H+1)` pairs is at most
`2^{2n+1}(H+1) ε₄ ≤ 1/10`, as `a_* k n = n^{1+ω/3-h+o(1)}`. -/
theorem pred_fail_prob (β γ : ℝ) (hβ : 0 < β) (hβγ : β ≤ γ) (hγ : γ < 1) :
    ∃ n₀ : ℕ, ∀ n ≥ n₀, ∀ {N : ℕ} {E : Fin N → Fin N → Prop} {G : Colour} {X Y : Finset (Fin N)}
      (M : Menu4 β γ G n N E X Y) (tag : Key β γ n → M.ι) (q : XProf M tag) (q' : YProf M tag)
      (J : Prep M tag → FinProb (OddRole n → Fin N)),
      GeoCons M tag → RefIndep M tag → Resample M tag q q' →
      (∀ ω, SPre M tag ω → InjOK M tag ω (J ω)) →
      ∑ ω, (prepLaw M tag q q').w ω *
          (if SPre M tag ω then (J ω).pr (fun f => ∃ a, PredFail M tag ω a (nbrLabels f a)) else 0) ≤
        1 / 10 := by
  sorry

/-- L4.1k, comparison (04:562–574): separated even roles have disjoint neighbourhoods, so the product of their
rows reads at most `mn ≤ n²` odd outputs; `InjOK` bounds its injection integral by twice its integral under the
product of the odd rows, which on `S_pre` are the sampling laws (`GeoCons`), and under independent draws the
product factors into the mean rows. -/
theorem even_clock {β γ : ℝ} {G : Colour} {n N : ℕ} {E : Fin N → Fin N → Prop} {X Y : Finset (Fin N)}
    (M : Menu4 β γ G n N E X Y) (tag : Key β γ n → M.ι) (_hgeo : GeoCons M tag) : EvenClock M tag := by
  sorry

/-- L4.1k, even loads (04:553–591): Lemma 3.6 with weights `prepLaw(ω) 1_{S_pre}(ω) J_ω(f)`, `Z_a = N p_a(x)`,
cap `exp((log 2 - c₂ a_*/2) n)` (`EvenRowFacts`), near sets of radius `2 locR` (`n · fraction · cap → 0` since
`log V(2 locR) = o(a_* n)`), separated products at most `2^m ∏ E_raw[N p_a(x)]` (`EvenClock`, then dropping
`S_pre`, `EvenFactor`), and mean `≤ 8 · 2K` (`ProfOK.even`, `TagBal`); Markov at `8(16K + 1)` and a union over the
labels leave `≤ n2^{-n}`; the column sums are at most one once `C₀ ≥ 4(16K + 1)`. -/
theorem even_load_prob (β γ K : ℝ) (hβ : 0 < β) (hβγ : β ≤ γ) (hγ : γ < 1) (hK : 0 < K) :
    ∃ n₀ : ℕ, ∃ C₀ : ℝ, ∀ n ≥ n₀, ∀ N : ℕ, LargeHost C₀ n N →
      ∀ {E : Fin N → Fin N → Prop} {G : Colour} {X Y : Finset (Fin N)}
        (M : Menu4 β γ G n N E X Y) (tag : Key β γ n → M.ι) (q : XProf M tag) (q' : YProf M tag)
        (J : Prep M tag → FinProb (OddRole n → Fin N)),
        TagBal M tag (2 * K) → ProfOK M tag q q' → EvenFactor M tag q q' → EvenClock M tag →
        EvenRowFacts M tag → (∀ ω, SPre M tag ω → InjOK M tag ω (J ω)) →
        ∑ ω, (prepLaw M tag q q').w ω *
            (if SPre M tag ω then (J ω).pr (fun f => ∃ x, 1 < evenCol M tag ω f x) else 0) ≤
          1 / 10 := by
  sorry

end HypercubeRamsey.S04
