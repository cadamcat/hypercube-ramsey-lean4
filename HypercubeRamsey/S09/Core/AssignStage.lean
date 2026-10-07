import HypercubeRamsey.S09.Core.GainStage
import HypercubeRamsey.S07.TagStage
import HypercubeRamsey.S03.GatedPosterior
import HypercubeRamsey.S03.ClockSampling
import HypercubeRamsey.Tools.ScatteredUnion
import HypercubeRamsey.S09.Core.AssignStage_q_s09_assign2

/-!
# Proposition 9.2, core: predictive tests, anchor avoidance, odd injection, even rows (P9.2-assignA–C)

Source: `sections/09-intermediate-powers-of-bias.tex`, lines 296–350; blueprint `research/blueprint/PART-B.md`
§3.9, P9.2-assignA, P9.2-assignB, P9.2-assignC.  Lemma 3.4 is `S07.cond_product_bound` (product form with free
coordinates), Lemma 3.6 is `scatteredMoments_union_labels`, Lemma 3.7 is `gated_posterior`, Lemma 3.10 is
`clock_sampling`.
-/

namespace HypercubeRamsey

open OAI.HypercubeRamsey Classical
open scoped BigOperators

/-- Monotonicity of the large regime in its constants. -/
theorem largeAt_mono9 {n₀ n₀' : ℕ} {C₀ C₀' : ℝ} {n N : ℕ} (h : LargeAt n₀ C₀ n N)
    (hn : n₀' ≤ n₀) (hC : C₀' ≤ C₀) : LargeAt n₀' C₀' n N :=
  ⟨le_trans hn h.1, le_trans (mul_le_mul_of_nonneg_right hC (by positivity)) h.2.1, h.2.2⟩

/-! ## P9.2-assignA (09:296–320) -/

/-- P9.2-assignA, predictive alarm mean (09:305–310): with everything but `W_*` fixed, `M_v` and `P⁻` do not
depend on `W_*` (the deletion kernels erase the target ID), the alarm at `W_* = x` integrates to
`∑_y M_v(y) 1[predictive failure]`, and the first assertion of Lemma 3.7 (`gated_posterior`,
`ε = e^{-c₄ n a_*/4}`, reference law `P⁻`) bounds it. -/
theorem p92_alarm_mean {P : Params9} {n N : ℕ} {M : TagMix N} (S : Setup9 P n N M)
    (I : IDMap9 P n) (E : Fin N → Fin N → Prop) (G : Colour) : AlarmMean9 S I E G := by
  sorry

/-- P9.2-assignA, star events (09:309–312): the star event fails validity with raw probability `e^{-c₀ n^u}`
(`GainCert9`); the alarm reads `W_*` (law `μ_{i_{z(v)}}`, independent of the other inputs) and Markov with
`AlarmMean9` bounds the alarm event by `e^{-c₄ n a_*/8}`, which is `≤ e^{-n^u}` for large `n`
(`ScalesAt9`). -/
theorem p92_star_bad_prob (P : Params9) (hP : P.Valid) (c₀ : ℝ) (hc₀ : 0 < c₀) :
    ∃ c > (0 : ℝ), ∃ n₀ : ℕ, ∀ n ≥ n₀, ∀ {N : ℕ} {E : Fin N → Fin N → Prop}
      {X Y : Finset (Fin N)} {κ : ℝ} {G : Colour} {M : TagMix N} (S : Setup9 P n N M)
      (I : IDMap9 P n),
      CoreInput9 P κ E X Y G M S I → GainCert9 S I E G c₀ → AlarmMean9 S I E G →
        ∀ v : EvenSites9 n, (rawLaw9 S I).pr (fun ω => StarBad9 S E G ω v) ≤ P.tail c n := by
  sorry

/-- P9.2-assignA, locality (09:314–316): the star event of `v` reads only the anchors of IDs seen at its odd
neighbours and their masks; a shared ID or mask forces special distance at most `4` and residual distance at
most `2r + 4` (`IDMap9.center_slice`, `IDMap9.center_near`), so at most `(m+1)^4 (n-m+1)^{2r+4} ≤ (n+1)^{2r+8}`
other star events meet it. -/
theorem p92_star_scope {P : Params9} {n N : ℕ} {M : TagMix N} (S : Setup9 P n N M)
    (I : IDMap9 P n) (E : Fin N → Fin N → Prop) (G : Colour) : StarScopeFacts9 S I E G := by
  sorry

/-- P9.2-assignA, the local-lemma input (09:316–318): charges `x = e^{-c₁ n^u/2}` meet
`e^{-c₁ n^u} ≤ x (1 - x)^{(n+1)^{2r+8}}` for large `n`, since `r log n = o(n^u)` (`σ < u`). -/
theorem p92_anchor_lll (P : Params9) (hP : P.Valid) (c₁ : ℝ) (hc₁ : 0 < c₁) :
    ∃ n₀ : ℕ, ∀ n ≥ n₀, ∀ {N : ℕ} {E : Fin N → Fin N → Prop} {M : TagMix N}
      (S : Setup9 P n N M) (I : IDMap9 P n) (G : Colour),
      (∀ v : EvenSites9 n, (rawLaw9 S I).pr (fun ω => StarBad9 S E G ω v) ≤ P.tail c₁ n) →
      StarScopeFacts9 S I E G → AnchorLLL9 S I E G (c₁ / 2) := by
  sorry

/-! ## P9.2-assignB (09:322–329) -/

/-- Row widths (09:162, 09:323): every odd row has an even neighbour whose masked full order passes its tests,
so each successive hit retains at least `.49` (`b_* ≤ 1/200`) and the full filter keeps mass at least
`.49^{T+m}` of the masked law (`IDMap9.odd_ids`); the masked law has width at most `S_s + n^u + log 2`
(`MasksOK9`, `Prep9`), so `N p_b ≤ e^{P.filterBudget n} ≤ e^{S_d}`. -/
theorem p92_row_cap (P : Params9) (hP : P.Valid) :
    ∃ n₀ : ℕ, ∀ n ≥ n₀, ∀ {N : ℕ} {E : Fin N → Fin N → Prop} {X Y : Finset (Fin N)} {κ : ℝ}
      {G : Colour} {M : TagMix N} (S : Setup9 P n N M) (I : IDMap9 P n),
      CoreInput9 P κ E X Y G M S I → RowCap9 S I E G := by
  sorry

/-- P9.2-assignB, odd moments (09:324–327): separated odd rows (`¬ siteNear9`) have disjoint inputs (anchors of
the IDs they see and their own masks); removing the star events touching these inputs (at most
`(n+1)^{2r+8}` per row, factor `2` per row for large `n`, `S07.CondProductBound`) leaves independent raw inputs,
whose product integral is `∏ N R_b(y)`. -/
theorem p92_odd_moment (P : Params9) (hP : P.Valid) (c : ℝ) (hc : 0 < c) :
    ∃ n₀ : ℕ, ∀ n ≥ n₀, ∀ {N : ℕ} {E : Fin N → Fin N → Prop} {M : TagMix N} {G : Colour}
      (S : Setup9 P n N M) (I : IDMap9 P n),
      S07.CondProductBound → AnchorLLL9 S I E G c → StarScopeFacts9 S I E G →
        OddMoment9 S I E G := by
  sorry

/-- P9.2-assignB, odd column sums (09:322–327): Lemma 3.6 with weights `N p_b(y)`, cap `e^{S_d}` on the
avoidance event (`RowCap9`), near fraction at most `(n+1)^{4r+12} 2^{1-n}` (and
`n (n+1)^{4r+12} 2^{1-n} e^{S_d} ≤ 1`), comparison means `N R_b(y) ≤ (1 + e^{-n^u}) N ν_{i_{z(b)}}(y)` of average at
most `2 · tagLoadConst9 κ` (`MasksOK9`, `TagsOK9`), and a union over the at most `n 2^n` labels; the column sum is
`2^{n-1}/N` times the normalized average, at most `θ₀ = 10⁻⁸` once `N ≥ C₀ 2^n`. -/
theorem p92_odd_loads (P : Params9) (hP : P.Valid) (κ : ℝ) (hκ : 0 < κ) :
    ∃ n₀ : ℕ, ∃ C₀ : ℝ, ∀ n N : ℕ, LargeAt n₀ C₀ n N →
      ∀ {E : Fin N → Fin N → Prop} {X Y : Finset (Fin N)} {G : Colour} {M : TagMix N}
        (S : Setup9 P n N M) (I : IDMap9 P n) (cT : ℝ),
        CoreInput9 P κ E X Y G M S I → TagsOK9 κ E G cT S.tag → RowCap9 S I E G →
        OddMoment9 S I E G → 0 < (rawLaw9 S I).pr (fun ω => ∀ v, ¬ StarBad9 S E G ω v) →
        (anchorLaw9 S I E G).pr (fun ω => ∃ y, (1e-8 : ℝ) < oddColumn9 S E G ω y) ≤
          (n : ℝ) * 2 ^ n * (1 / 4 : ℝ) ^ n := by
  sorry

/-- P9.2-assignB, odd injection (09:327–329): at a successful prehistory, Lemma 3.10 (`clock_sampling`, `B = 3`)
applies to the odd rows (probability laws with atoms `≤ e^{S_d}/N ≤ n^{-A}`, column sums `≤ θ₀`), with the
predictive failures of the even stars as predicates (each reads its `n` odd neighbours, each row is read by `n`
predicates, product-law probability equal to the alarm `≤ e^{-c₄ n a_*/8} ≤ n^{-P}`); it gives an injective odd
assignment avoiding every predictive failure with joint comparison `1 + ε n ≤ 2` on at most `n³` rows. -/
theorem p92_odd_clock (P : Params9) (hP : P.Valid) :
    ∃ n₀ : ℕ, ∃ C₀ : ℝ, ∀ n N : ℕ, LargeAt n₀ C₀ n N →
      ∀ {E : Fin N → Fin N → Prop} {X Y : Finset (Fin N)} {κ : ℝ} {G : Colour} {M : TagMix N}
        (S : Setup9 P n N M) (I : IDMap9 P n),
        CoreInput9 P κ E X Y G M S I → RowCap9 S I E G →
        ∀ ω : Outcome9 I N, GoodPre9 S E G ω → ∃ J, ClockOK9 S E G ω J := by
  sorry

/-! ## P9.2-assignC (09:331–350) -/

/-- The likelihood bound (09:303–304): on `𝒱` (recomputed with `W_* = x`) every filter is a genuine restriction,
`p_b = del_b|_{N_G(x)}` with `del_b(N_G(x)) = q_b`, so `∏ p_b(y_b) ≤ P⁻(y) / ∏ q_b ≤ 2^n e^{-c₄ n a_*} P⁻(y)` by
(9.1); off `𝒱` the left side is zero. -/
theorem p92_star_lik_bound (P : Params9) (hP : P.Valid) :
    ∃ n₀ : ℕ, ∀ n ≥ n₀, ∀ {N : ℕ} {E : Fin N → Fin N → Prop} {X Y : Finset (Fin N)} {κ : ℝ}
      {G : Colour} {M : TagMix N} (S : Setup9 P n N M) (I : IDMap9 P n),
      CoreInput9 P κ E X Y G M S I → StarLikBound9 S I E G := by
  sorry

/-- P9.2-assignC, posterior rows (09:331–335): on predictive success `M_v > 0`, so the posterior row is a
probability law; a nonzero entry at `x` forces `𝒱` with `W_* = x`, hence every neighbour label hits `x`
(the target ID is seen at every odd neighbour); and `N μ_{i_z}(x) ≤ e^{n^{x_s} + O(log n)} ≤ e^{c₄ n a_*/4}` with
the likelihood bound and `M_v ≥ e^{-c₄ n a_*/4} P⁻` give the cap `2^n e^{-c₄ n a_*/2}`. -/
theorem p92_even_rows (P : Params9) (hP : P.Valid) :
    ∃ n₀ : ℕ, ∀ n ≥ n₀, ∀ {N : ℕ} {E : Fin N → Fin N → Prop} {X Y : Finset (Fin N)} {κ : ℝ}
      {G : Colour} {M : TagMix N} (S : Setup9 P n N M) (I : IDMap9 P n),
      CoreInput9 P κ E X Y G M S I → StarLikBound9 S I E G →
        EvenRowLaw9 S I E G ∧ EvenRowCap9 S I E G := by
  sorry

/-- P9.2-assignC, cancellation (09:342–346): integrating the target anchor turns the gated neighbour product into
`M_v`, which cancels the posterior denominator: `∑_y M_v(y) F_x(y) μ(x)/M_v(y) ≤ μ(x) ∑_y F_x(y) ≤ μ(x)`
(third assertion of `gated_posterior`); predictive success only decreases the integral. -/
theorem p92_star_cancel {P : Params9} {n N : ℕ} {M : TagMix N} (S : Setup9 P n N M)
    (I : IDMap9 P n) (E : Fin N → Fin N → Prop) (G : Colour) : StarCancel9 S I E G := by
  exact Lane_q_s09_assign2.starCancel9_core S E G

/-- P9.2-assignC, clock comparison (09:337–341): separated even sites have disjoint odd neighbourhoods (at most
`n²` labels in all), the clock law is supported on predictive success, and its joint comparison replaces the
injection by independent draws from the odd rows; on a successful prehistory every star gate is open, so the
integral is at most twice the product of the star integrals. -/
theorem p92_clock_factor {P : Params9} {n N : ℕ} {M : TagMix N} (S : Setup9 P n N M)
    (I : IDMap9 P n) (E : Fin N → Fin N → Prop) (G : Colour)
    (J : Outcome9 I N → FinProb (OddSites9 n → Fin N))
    (hJ : ∀ ω, GoodPre9 S E G ω → ClockOK9 S E G ω (J ω)) : ClockFactor9 S I E G J := by
  sorry

/-- P9.2-assignC, anchor integral (09:341–347): remove the star events touching the separated target IDs (at
most `(n+1)^{2r+8}` each, factor `2` per site for large `n`); the remaining events do not read the targets, each
star integral reads only its own target among them (separation and the fixed-map locality), so the targets
integrate independently and `StarCancel9` bounds each factor by `N μ_{i_{z(v)}}(x)`. -/
theorem p92_even_anchor_integral (P : Params9) (hP : P.Valid) (c : ℝ) (hc : 0 < c) :
    ∃ n₀ : ℕ, ∀ n ≥ n₀, ∀ {N : ℕ} {E : Fin N → Fin N → Prop} {M : TagMix N} {G : Colour}
      (S : Setup9 P n N M) (I : IDMap9 P n),
      S07.CondProductBound → AnchorLLL9 S I E G c → StarScopeFacts9 S I E G →
        StarCancel9 S I E G → EvenAnchorIntegral9 S I E G := by
  sorry

/-- P9.2-assignC, assembled moment (09:347–349): the clock comparison at every successful prehistory and the
anchor integral give `4^k ∏ N μ_{i_{z(v)}}(x)`. -/
theorem p92_even_moment {P : Params9} {n N : ℕ} {M : TagMix N} (S : Setup9 P n N M)
    (I : IDMap9 P n) (E : Fin N → Fin N → Prop) (G : Colour)
    (J : Outcome9 I N → FinProb (OddSites9 n → Fin N))
    (hfac : ClockFactor9 S I E G J) (hint : EvenAnchorIntegral9 S I E G) : EvenMoment9 S I E G J := by
  exact Lane_q_s09_assign2.p92_even_moment_helper S I E G J hfac hint

/-- P9.2-assignC, even column sums (09:347–350): Lemma 3.6 with near = `siteNear9` (fraction
`(n+1)^{4r+12} 2^{1-n}`), cap `2^n e^{-c₄ n a_*/2}` on predictive success (`EvenRowCap9`; repeat cost
`e^{O(r log n) - c₄ n a_*/2} = o(1)`), comparison means `N μ_{i_{z(v)}}(x)` of average at most `tagLoadConst9 κ`
(`TagsOK9`), and a union over labels; even column sums are `2^{n-1}/N` times the normalized average, at most one
once `N ≥ C₀ 2^n`. -/
theorem p92_even_loads (P : Params9) (hP : P.Valid) (κ : ℝ) (hκ : 0 < κ) :
    ∃ n₀ : ℕ, ∃ C₀ : ℝ, ∀ n N : ℕ, LargeAt n₀ C₀ n N →
      ∀ {E : Fin N → Fin N → Prop} {X Y : Finset (Fin N)} {G : Colour} {M : TagMix N}
        (S : Setup9 P n N M) (I : IDMap9 P n) (cT : ℝ)
        (J : Outcome9 I N → FinProb (OddSites9 n → Fin N)),
        CoreInput9 P κ E X Y G M S I → TagsOK9 κ E G cT S.tag → EvenRowCap9 S I E G →
        (∀ ω, GoodPre9 S E G ω → ClockOK9 S E G ω (J ω)) → EvenMoment9 S I E G J →
        ∑ ω, (anchorLaw9 S I E G).w ω *
            (if GoodPre9 S E G ω then (J ω).pr (fun f => ∃ x, 1 < evenColumn9 S E G ω f x) else 0) ≤
          (n : ℝ) * 2 ^ n * (1 / 4 : ℝ) ^ n := by
  exact Lane_q_s09_assign2.p92_even_loads_core P hP κ hκ

/-- P9.2-assignB/C averaged (09:327–350): if the avoidance event has positive raw mass, the odd column sums
exceed `θ₀` with anchor-law probability at most `δ = n 2^n 4^{-n}`, successful prehistories admit clock-sampler
laws, and every clock-sampler family has even column sums above one with probability at most `δ`, then (as
`2δ < 1`) some outcome and odd assignment avoid every star event, are injective, avoid every predictive failure
and have even column sums at most one. -/
theorem p92_realization :
    ∃ n₀ : ℕ, ∀ n ≥ n₀, ∀ {P : Params9} {N : ℕ} {M : TagMix N} {E : Fin N → Fin N → Prop}
      {G : Colour} (S : Setup9 P n N M) (I : IDMap9 P n), 0 < N →
      0 < (rawLaw9 S I).pr (fun ω => ∀ v, ¬ StarBad9 S E G ω v) →
      (anchorLaw9 S I E G).pr (fun ω => ∃ y, (1e-8 : ℝ) < oddColumn9 S E G ω y) ≤
        (n : ℝ) * 2 ^ n * (1 / 4 : ℝ) ^ n →
      (∀ ω : Outcome9 I N, GoodPre9 S E G ω → ∃ J, ClockOK9 S E G ω J) →
      (∀ J : Outcome9 I N → FinProb (OddSites9 n → Fin N),
        (∀ ω, GoodPre9 S E G ω → ClockOK9 S E G ω (J ω)) →
        ∑ ω, (anchorLaw9 S I E G).w ω *
            (if GoodPre9 S E G ω then (J ω).pr (fun f => ∃ x, 1 < evenColumn9 S E G ω f x) else 0) ≤
          (n : ℝ) * 2 ^ n * (1 / 4 : ℝ) ^ n) →
      ∃ (ω : Outcome9 I N) (f : OddSites9 n → Fin N), (∀ v, ¬ StarBad9 S E G ω v) ∧
        Function.Injective f ∧ (∀ v, ¬ predFail9 S E G ω v (nbrLabels9 f)) ∧
        ∀ x, evenColumn9 S E G ω f x ≤ 1 := by
  refine ⟨3, ?_⟩
  intro n hn P N M E G S I hN havoid hodd hsampler heven
  have hδ := Lane_q_s09_assign2.p92_delta_lt_half hn
  have hδ' : 2 * ((n : ℝ) * 2 ^ n * (1 / 4 : ℝ) ^ n) < 1 := by
    linarith
  exact Lane_q_s09_assign2.p92_realization_core S hN havoid hodd hsampler heven hδ'

/-- F-HallEmbed (09:349–350): the posterior even rows of a good realization are probability laws on the common
neighbourhoods of the injective odd labels with column sums at most one. -/
theorem p92_hall9 {P : Params9} {n N : ℕ} {M : TagMix N} (S : Setup9 P n N M) (I : IDMap9 P n)
    (E : Fin N → Fin N → Prop) (G : Colour) (hlaw : EvenRowLaw9 S I E G) (ω : Outcome9 I N)
    (f : OddSites9 n → Fin N) (hinj : Function.Injective f)
    (hpf : ∀ v, ¬ predFail9 S E G ω v (nbrLabels9 f)) (hcol : ∀ x, evenColumn9 S E G ω f x ≤ 1) :
    CubeAt n N E :=
  cubeAt_of_rows E G f hinj (fun v x => evenRow9 S E G ω f v x)
    (fun v x => (hlaw ω f v (hpf v)).1 x) (fun v => (hlaw ω f v (hpf v)).2.1)
    (fun v x hx b hb => (hlaw ω f v (hpf v)).2.2 x hx b hb) hcol

/-- The assignment stage assembled (09:296–350): with the tags, the masks and the gain bound, the one-shot
experiment produces a monochromatic cube. -/
theorem p92_assign_stage (P : Params9) (hP : P.Valid) (κ : ℝ) (hκ : 0 < κ) (c₀ : ℝ) (hc₀ : 0 < c₀) :
    ∃ n₀ : ℕ, ∃ C₀ : ℝ, ∀ n N : ℕ, LargeAt n₀ C₀ n N →
      ∀ {E : Fin N → Fin N → Prop} {X Y : Finset (Fin N)} {G : Colour} {M : TagMix N}
        (S : Setup9 P n N M) (I : IDMap9 P n) (cT : ℝ),
        CoreInput9 P κ E X Y G M S I → TagsOK9 κ E G cT S.tag → GainCert9 S I E G c₀ →
          CubeAt n N E := by
  obtain ⟨c₁, hc₁, n₁, hsb⟩ := p92_star_bad_prob P hP c₀ hc₀
  obtain ⟨n₂, hlll⟩ := p92_anchor_lll P hP c₁ hc₁
  obtain ⟨n₃, hrc⟩ := p92_row_cap P hP
  obtain ⟨n₄, hom⟩ := p92_odd_moment P hP (c₁ / 2) (by positivity)
  obtain ⟨n₅, C₅, hol⟩ := p92_odd_loads P hP κ hκ
  obtain ⟨n₆, C₆, hck⟩ := p92_odd_clock P hP
  obtain ⟨n₇, hslb⟩ := p92_star_lik_bound P hP
  obtain ⟨n₈, her⟩ := p92_even_rows P hP
  obtain ⟨n₉, heai⟩ := p92_even_anchor_integral P hP (c₁ / 2) (by positivity)
  obtain ⟨n₁₀, C₁₀, hel⟩ := p92_even_loads P hP κ hκ
  obtain ⟨n₁₁, hreal⟩ := p92_realization
  refine ⟨max (max (max n₁ n₂) (max n₃ n₄)) (max (max n₅ n₆) (max (max n₇ n₈) (max n₉ (max n₁₀ n₁₁)))),
    max (max C₅ C₆) C₁₀, ?_⟩
  intro n N hL E X Y G M S I cT hin htags hgain
  have hn := hL.1
  have h1 : n₁ ≤ n := by omega
  have h2 : n₂ ≤ n := by omega
  have h3 : n₃ ≤ n := by omega
  have h4 : n₄ ≤ n := by omega
  have h7 : n₇ ≤ n := by omega
  have h8 : n₈ ≤ n := by omega
  have h9 : n₉ ≤ n := by omega
  have h11 : n₁₁ ≤ n := by omega
  have hL5 : LargeAt n₅ C₅ n N :=
    largeAt_mono9 hL (by omega) (le_trans (le_max_left _ _) (le_max_left _ _))
  have hL6 : LargeAt n₆ C₆ n N :=
    largeAt_mono9 hL (by omega) (le_trans (le_max_right _ _) (le_max_left _ _))
  have hL10 : LargeAt n₁₀ C₁₀ n N := largeAt_mono9 hL (by omega) (le_max_right _ _)
  have hAM := p92_alarm_mean S I E G
  have hSB := hsb n h1 S I hin hgain hAM
  have hSF := p92_star_scope S I E G
  have hLLL := hlll n h2 S I G hSB hSF
  have hpos := (S07.cond_product_bound _ _ _ _ _ hLLL).1
  have hRC := hrc n h3 S I hin
  have hOM := hom n h4 S I S07.cond_product_bound hLLL hSF
  have hOL := hol n N hL5 S I cT hin htags hRC hOM hpos
  have hCK := hck n N hL6 S I hin hRC
  have hSLB := hslb n h7 S I hin
  obtain ⟨hERL, hERC⟩ := her n h8 S I hin hSLB
  have hEAI := heai n h9 S I S07.cond_product_bound hLLL hSF (p92_star_cancel S I E G)
  have hEL : ∀ J : Outcome9 I N → FinProb (OddSites9 n → Fin N),
      (∀ ω, GoodPre9 S E G ω → ClockOK9 S E G ω (J ω)) →
      ∑ ω, (anchorLaw9 S I E G).w ω *
          (if GoodPre9 S E G ω then (J ω).pr (fun f => ∃ x, 1 < evenColumn9 S E G ω f x) else 0) ≤
        (n : ℝ) * 2 ^ n * (1 / 4 : ℝ) ^ n := fun J hJ =>
    hel n N hL10 S I cT J hin htags hERC hJ
      (p92_even_moment S I E G J (p92_clock_factor S I E G J hJ) hEAI)
  obtain ⟨ω, f, _hgood, hinj, hpf, hcol⟩ := hreal n h11 S I hin.1 hpos hOL hCK hEL
  exact p92_hall9 S I E G hERL ω f hinj hpf hcol

end HypercubeRamsey
