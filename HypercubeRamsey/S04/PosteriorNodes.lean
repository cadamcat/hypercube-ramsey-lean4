import HypercubeRamsey.S04.CoreLemmas

/-!
# D4.6 caps and L4.1g: the posterior tuple and even common neighbourhoods

Source: `sections/04-…tex`, lines 340–432; blueprint D4.6, L4.1g.
-/

namespace HypercubeRamsey.S04

open Classical OAI.HypercubeRamsey
open scoped BigOperators

/-- D4.6 (04:349–351): an odd row is zero or `ν^{M'}(y) 1[hits]/R_u(D)` with `ν^{M'} ≤ 2ν_i ≤ 2e^{sY+1}/N` and
`R_u(D) ≥ exp(-LkT|Z_u|)`, `LkT|Z_u| = o(n^γ)` (`KeyNbrCard`); so `N p_u(y) ≤ exp(2n^γ)` for large `n`. -/
theorem odd_cap (β γ : ℝ) (hβ : 0 < β) (hβγ : β ≤ γ) (hγ : γ < 1) :
    ∃ n₀ : ℕ, ∀ n ≥ n₀, KeyNbrCard β γ n →
      ∀ {N : ℕ} {E : Fin N → Fin N → Prop} {G : Colour} {X Y : Finset (Fin N)}
        (M : Menu4 β γ G n N E X Y) (tag : Key β γ n → M.ι), OddCap M tag := by
  sorry

/-- L4.1g(1) (04:386–389): the reference laws use positions, odd masks and the tuples other than `W_{c,g(a)}`
(every requirement from that tuple is deleted), so `Q` does not read it; `M_c` integrates it out. -/
theorem ref_indep {β γ : ℝ} {G : Colour} {n N : ℕ} {E : Fin N → Fin N → Prop} {X Y : Finset (Fin N)}
    (M : Menu4 β γ G n N E X Y) (tag : Key β γ n → M.ι) : RefIndep M tag := by
  sorry

/-- L4.1g(2) (04:392–404): on `E` (recomputed at `z`), each neighbouring kernel `p_u` is at most
`R_u^{-(c,g(a))}(D_u)/R_u(D_u)` times its own deleted-tuple law, which is one of the at most `exp(O(T log n))` terms
of the mixture `Q_u` (count condition in `E`); the validity ratios give `exp(k(log 2 - c₁ a_*))` for the own-key
neighbours and `exp(Lk)` for the at most `n^{γ+14ω}` others (`KeyLocal`).  Since `T log n = o(k a_*)` and
`n^{γ+14ω} L = o(a_* n)`, the product is at most `exp((log 2 - c₂ a_*) k n) Q(y)` for large `n`. -/
theorem lik_bound (β γ : ℝ) (hβ : 0 < β) (hβγ : β ≤ γ) (hγ : γ < 1) :
    ∃ n₀ : ℕ, ∀ n ≥ n₀, KeyLocal β γ n →
      ∀ {N : ℕ} {E : Fin N → Fin N → Prop} {G : Colour} {X Y : Finset (Fin N)}
        (M : Menu4 β γ G n N E X Y) (tag : Key β γ n → M.ι), LikBound M tag := by
  sorry

/-- L4.1g(3) (04:409–427): by `LikBound` and Lemma 3.7(2) (`gated_posterior`) the posterior `π(z) F_z(y)/M_c(y)`
is at most `exp((log 2 - c₂ a_*)kn) ε₄⁻¹ π(z)`, and `π(z) ≤ (2e^{sX}/N)^k`; it is supported on `S^k` (a positive
`F_z(y)` makes every `y_u` hit every entry of `z`, as `c ∈ D_u` and `g(a) ∈ Z_u`, and `π(z) > 0` puts the entries in
the mask).  So `1 ≤ |S|^k exp((log 2 - c₂ a_*)kn + c₂ a_* kn/4 + k(sX + log 2)) N^{-k}`, and `sX + log 2 ≤
c₂ a_* n/4` for large `n`. -/
theorem comm_large (β γ : ℝ) (hβ : 0 < β) (hβγ : β ≤ γ) (hγ : γ < 1) :
    ∃ n₀ : ℕ, ∀ n ≥ n₀, ∀ {N : ℕ} {E : Fin N → Fin N → Prop} {G : Colour} {X Y : Finset (Fin N)}
      (M : Menu4 β γ G n N E X Y) (tag : Key β γ n → M.ι), LikBound M tag → CommLarge M tag := by
  sorry

/-- L4.1g (04:428–432): by definition an even row is zero or uniform on `S_{a,c}(y)` inside the mask of the
selected reference, on `E` and the predictive requirement; by `CommLarge` the set is nonempty there and
`N p_a ≤ N/|S| ≤ exp((log 2 - c₂ a_*/2) n)`. -/
theorem even_row_facts {β γ : ℝ} {G : Colour} {n N : ℕ} {E : Fin N → Fin N → Prop} {X Y : Finset (Fin N)}
    (M : Menu4 β γ G n N E X Y) (tag : Key β γ n → M.ι) (_hcomm : CommLarge M tag) :
    EvenRowFacts M tag := by
  sorry

end HypercubeRamsey.S04
