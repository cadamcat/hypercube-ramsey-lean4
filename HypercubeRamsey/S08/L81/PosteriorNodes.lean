import HypercubeRamsey.S08.L81.SelectionNodes

/-!
# Lemma 8.1, Steps 6–8: selection adjustment, posterior truncation, the ordinary-anchor hit test

Source: `sections/08-…tex`, lines 227–300 (L8.1g, L8.1h).
-/

noncomputable section

namespace HypercubeRamsey.S08

open Classical OAI.HypercubeRamsey
open scoped BigOperators

section Nodes

variable (η₀ γ β p K : ℝ) (h : ℕ)

/-- L8.1g(i) (08:230–234): in the raw experiment at candidate `ξ`, the listed centres (distinct IDs: internal ones in
slice `g`, one per cross slice) first need the observed independent tags (laws `S_g`, `S_u`); selection and
validity only reduce the probability; given the selections the cross anchors are independent with laws
`U_{u,i}`; validity includes the candidate's gates.  Dividing by `Q` gives `F_ξ a_ξ ≤ F_ξ` (both sides vanish
where a reference vanishes). -/
theorem gsel_le_f (D : Ctx η₀ β p h) : D.GselLeF := by
  sorry

/-- L8.1g(ii) (08:245–254): on a valid presentation (`M ≥ ε₀`, at most `T` internal IDs), the base posterior has
density at most `e^{1.5δhs log n}`; the selected posterior `F_ξ a_ξ dR'/M^a` with `M^a ≥ ε₀ M` is at most `ε₀^{-1}`
times the base posterior (`a_ξ ≤ 1`); `2.5δ ≤ .003`. -/
theorem sel_post_cap (hh : 1 ≤ h) :
    ∃ n₀ : ℕ, ∀ D : Ctx η₀ β p h, n₀ ≤ D.n → D.PostCap → D.GselLeF → D.SelPostCap := by
  sorry

/-- L8.1g(iii) (08:256–264): with `q` the average coordinate marginal of the selected posterior and
`𝓗 = {y : Nq(y) > e^{.01 s log n}}`, `F-HeavyTrunc` (`heavyTruncation` with `A = .003hs log n`,
`B = .01 s log n`, `⌈h/2⌉` coordinates) gives `q(𝓗) ≤ 1/2 + 1/(2h) + o(1) ≤ .6`, so the light mass is at least
`.4`; `p⁰` is `q` off `𝓗` normalized. -/
theorem p0_law (hh : 10 ≤ h) :
    ∃ n₀ : ℕ, ∀ D : Ctx η₀ β p h, n₀ ≤ D.n → GridFacts η₀ D.n → D.SelPostCap → D.P0Law := by
  sorry

/-- L8.1g(iv) (08:171–176, 293): a label in the support of `p⁰` is a coordinate of a candidate with positive
selected posterior, hence with `F_ξ > 0` (directly, or through `F_ξ a_ξ ≤ F_ξ`), hence hitting every observed cross
anchor. -/
theorem p0_support (D : Ctx η₀ β p h) (hF : D.FSupport) (hG : D.GselLeF) : D.P0Support := by
  sorry

/-- L8.1g(v) (08:266–283): valid data for a presentation `π` have subdensity `M^a_π` against `Q_π`; on the
selected-posterior cases cancellation gives at most `dR'(ξ) Σ_π ∫ F_ξ a_ξ dQ_π ≤ dR'(ξ)`; on the other cases
`M^a < ε₀ M` bounds the contribution by `ε₀ L_n dR'(ξ) = o(dR'(ξ))` (validly presentable lists are candidate lists
at positions with incident counts `≤ 2λ`, `h ≥ 10⁸`).  Taking average coordinate marginals,
`E_{R'}` of a coordinate is `E_Λ ν_i` (`N max ≤ 4K`), and the truncation costs `5/2`.  The density bounds make
the valid-presentation probability vanish wherever the reference `Q_π` does, so it equals `F_ξ a_ξ Q_π`. -/
theorem p0_raw_mean (hη₀ : 0 < η₀) (hK : 0 < K) (hh : 10 ^ 8 ≤ h) :
    ∃ n₀ : ℕ, ∀ D : Ctx η₀ β p h, n₀ ≤ D.n → ∀ X Y R : Finset (Fin D.N), Std D γ K X Y R →
      GridFacts η₀ D.n → D.DensityBounds → D.ListCount → D.P0Law → D.GselLeF → D.P0RawMean K := by
  sorry

/-- L8.1g(vi) (08:285–290): `p⁰_{g,a}` reads the selections at its incident even cells (`SelLocal`, keys within one
of `g`), the tags of the selected IDs, the position gate, the gates and references (hidden keys within two), the
selection adjustment (the raw experiment at fixed positions and non-target tuples, whose relevant marginals read
hidden keys within four and positions within three) and the cross anchors. -/
theorem p0_local (D : Ctx η₀ β p h) (hS : D.SelLocal) : D.P0Local := by
  sorry

/-- L8.1h(i) (08:295–297): fix the valid presentation and cross anchors.  A label of `p⁰` is a coordinate of a
supported candidate `ξ`; for an observed internal tag `i`, the cutoff under `ξ` gives
`μ_i{misses ξ | hits Θ_{E(g)}} ≤ Δ`, and the true cutoff (the tag has positive probability under `S_g`, `Z_g > 0`)
gives `d_i^+ ≥ (1-Δ)d_i^-`, so under `U_{g,i}` the miss probability is at most `Δ/(1-Δ)`.  Summing over the at most
`n+1` ordinary anchors and Markov at `.02` (with `Σ p⁰ = 1`, `P0Law`) gives the bound. -/
theorem hit_tail (D : Ctx η₀ β p h) (hn : 1 ≤ D.n) (hF : D.FSupport) (hG : D.GselLeF) (hL : D.P0Law) :
    D.HitTail := by
  sorry

/-- L8.1h(ii) (08:293–300): the odd row restricts `p⁰` (cross hits) to ordinary hits, normalized by a retained mass
`≥ .98`, so `p ≤ p⁰/.98`, `N max p ≤ 3e^{.01 s log n}/.98 ≤ e^{.02 s log n}` for large `n`, and `p` hits every
padded even anchor. -/
theorem prow_facts :
    ∃ n₀ : ℕ, ∀ D : Ctx η₀ β p h, n₀ ≤ D.n → D.P0Law → D.P0Support → D.PRowFacts := by
  sorry

end Nodes

end HypercubeRamsey.S08
