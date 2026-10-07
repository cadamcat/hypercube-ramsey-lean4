import HypercubeRamsey.S09.Core.Experiment
import HypercubeRamsey.Tools.Finner
import HypercubeRamsey.Tools.Concentration
import HypercubeRamsey.Tools.SignedTest
import HypercubeRamsey.S09.Core.GainStage_q_s09_gain2

set_option maxHeartbeats 1000000

/-!
# Proposition 9.2, core: regularity, conditional means, erasure, covariance and the gain (9.1)

Source: `sections/09-intermediate-powers-of-bias.tex`, lines 146–294; blueprint `research/blueprint/PART-B.md`
§3.9, P9.2-reg, P9.2-condmean, P9.2-erase, P9.2-cov, P9.2-gain.

All probabilities are over the raw experiment `rawLaw9 S I` (independent anchors and masks, tags and ID map
fixed).  Each node produces a named fact of `Core.Experiment` with an explicit tail constant; a node consuming
an earlier fact receives its constant as an argument, so the order of the constant choices is the paper's.
-/

namespace HypercubeRamsey

open OAI.HypercubeRamsey Classical
open scoped BigOperators

/-! ## Deterministic consequences of deep discrepancy (09:162–169) -/

/-- Forward degree test (09:162–166): against a second law within the deep budget, a first law of width
`w ≤ n^{x_d}` gives mass at most `2 e^{w - n^{x_d}}` to first labels whose degree differs from `1/2` by more than
`2b_*`.  (Restricting the first law to either signed exceptional set of mass `ρ` costs width `log(1/ρ)`; within the
deep budget its density would contradict `DeepAt`.) -/
theorem deep_forward9 {P : Params9} {n N : ℕ} {E : Fin N → Fin N → Prop} {X Y : Finset (Fin N)}
    (hdeep : P.DeepAt n N E X Y) (G : Colour) (lam : Law N) (hlamY : lam.SupportedIn Y)
    (hlamW : lam.WidthLE (P.Sd (n : ℝ))) (α : Law N) (hαX : α.SupportedIn X) (w : ℝ)
    (hαW : α.WidthLE w) (hw : w ≤ (n : ℝ) ^ (P.xD : ℝ)) :
    ∑ x ∈ Finset.univ.filter (fun x => 2 * P.bStar n < |rowDeg E G x lam - 1 / 2|), α.w x ≤
      2 * Real.exp (w - (n : ℝ) ^ (P.xD : ℝ)) := by
  sorry

/-- Reverse degree test (09:168–169): against a first law within the deep budget, a second law of width
`s ≤ S_d` gives mass at most `2 e^{s - S_d}` to second labels whose degree differs from `1/2` by more than
`2b_*`. -/
theorem deep_reverse9 {P : Params9} {n N : ℕ} {E : Fin N → Fin N → Prop} {X Y : Finset (Fin N)}
    (hdeep : P.DeepAt n N E X Y) (G : Colour) (σ : Law N) (hσX : σ.SupportedIn X)
    (hσW : σ.WidthLE ((n : ℝ) ^ (P.xD : ℝ))) (lam : Law N) (hlamY : lam.SupportedIn Y) (s : ℝ)
    (hlamW : lam.WidthLE s) (hs : s ≤ P.Sd (n : ℝ)) :
    ∑ y ∈ Finset.univ.filter (fun y => 2 * P.bStar n < |colDeg E G σ y - 1 / 2|), lam.w y ≤
      2 * Real.exp (s - P.Sd (n : ℝ)) := by
  sorry

/-- The degree tests packaged for `CoreInput9`. -/
theorem deep_tools9 {P : Params9} {n N : ℕ} {E : Fin N → Fin N → Prop} {X Y : Finset (Fin N)}
    (hdeep : P.DeepAt n N E X Y) : DeepTools9 P n N E X Y :=
  ⟨fun G lam hlamY hlamW α hαX w hαW hw => deep_forward9 hdeep G lam hlamY hlamW α hαX w hαW hw,
    fun G σ hσX hσW lam hlamY s hlamW hs => deep_reverse9 hdeep G σ hσX hσW lam hlamY s hlamW hs⟩

/-! ## P9.2-reg (09:156–169) -/

/-- P9.2-reg (09:156–167): the filter tests of every star hold except with raw probability `e^{-c n^u}`.  At a
prefix whose preceding hits each retained at least `.49`, the current second law (masked: width
`≤ S_s + n^u + log 2`; unmasked: `≤ S_s`) has width at most `P.filterBudget n < S_d` (`ScalesAt9`); the
next anchor is independent of it with law `μ_{i_z}` of width `n^{x_s} + h_+ log n + 1`, so `deep_forward9` bounds
the probability of an irregular next hit; a union over the `O(n(T+m))` prefixes of the three orders of every edge
of the star.  (The scale facts and degree tests are part of `CoreInput9`.) -/
theorem p92_regularity (P : Params9) (hP : P.Valid) :
    ∃ c > (0 : ℝ), ∃ n₀ : ℕ, ∀ n ≥ n₀, ∀ {N : ℕ} {E : Fin N → Fin N → Prop}
      {X Y : Finset (Fin N)} {κ : ℝ} {G : Colour} {M : TagMix N} (S : Setup9 P n N M)
      (I : IDMap9 P n),
      CoreInput9 P κ E X Y G M S I → RegularityCert9 S I E G c := by
  sorry

/-! ## P9.2-condmean (09:171–184) -/

/-- P9.2-condmean (09:171–184): condition on the whole core anchor vector `W_{C_v}`.  Conditional Markov applied
to the outer-then-core tests leaves, outside core histories of mass `e^{-Ω(n^u)}`, conditional failure
`e^{-Ω(n^u)}`; there `P_O(J_-) = 2^{1-k}(1 + O(k b_*))` and `P_O(J_D) = P_O(J_-) q̂_b`, so
`d_G(W_*; Q|_{J_-})` is a weighted mean of `q̂_b` whose weight is `2^{1-k}` up to relative `O(k b_*)`; since `q̂_b`
oscillates by `O(b_*)`, removing the weight costs `O(k b_*²)`, and `k ≤ n^χ = o(n^u)` keeps the exceptional error
`2^k e^{-Ω(n^u)}` exponentially small. -/
theorem p92_conditional_mean (P : Params9) (hP : P.Valid) (c₀ : ℝ) (hc₀ : 0 < c₀) :
    ∃ C > (0 : ℝ), ∃ c > (0 : ℝ), ∃ n₀ : ℕ, ∀ n ≥ n₀, ∀ {N : ℕ} {E : Fin N → Fin N → Prop}
      {X Y : Finset (Fin N)} {κ : ℝ} {G : Colour} {M : TagMix N} (S : Setup9 P n N M)
      (I : IDMap9 P n),
      CoreInput9 P κ E X Y G M S I → RegularityCert9 S I E G c₀ → CondMeanCert9 S I E G C c := by
  sorry

/-! ## P9.2-erase (09:186–220) -/

/-- P9.2-erase, first part (09:186–208): averaging the core as well returns to `R_b`; independence of the core
anchors gives `2^k E[P_O 1_{J_D}] = a_D Q` with `a_D = 2^k ∏_{c ∈ D} d_G(μ_{i_{z(c)}}, ·)`, so
`R_b = (1 + θ) a_D Q + e` with `|θ| ≤ C k b_*` and `‖e‖₁ = e^{-Ω(n^u)}` (bad histories cost their probability
times `1 + 2^k`).  The fallback of `P_O` bounds the width of `Q`, the reverse degree test makes
`a_D = 1 + O(k b_*)` outside a `Q`-set of mass `e^{-Ω(n^u)}` (`a_D ≤ 2^k` there), and `R_b ≤ (1 + e^{-n^u}) ν`
(`MasksOK9`) gives `Q = (1 + ψ) ν + err`. -/
theorem p92_erase_mean (P : Params9) (hP : P.Valid) (c₀ : ℝ) (hc₀ : 0 < c₀) :
    ∃ C > (0 : ℝ), ∃ c > (0 : ℝ), ∃ n₀ : ℕ, ∀ n ≥ n₀, ∀ {N : ℕ} {E : Fin N → Fin N → Prop}
      {X Y : Finset (Fin N)} {κ : ℝ} {G : Colour} {M : TagMix N} (S : Setup9 P n N M)
      (I : IDMap9 P n),
      CoreInput9 P κ E X Y G M S I → RegularityCert9 S I E G c₀ → EraseCert9 S I E G C c := by
  sorry

/-- P9.2-erase, second part (09:209–220): fix the core except `W_*`.  The unmasked core tests give
`ν(J_-) ≥ .49^k` outside an exponentially small exception, so restricting `Q = (1 + ψ)ν + err` to `J_-` changes
`λ = ν|_{J_-}` by a signed density `s` with `E_λ s = 0`, `|s| ≤ C k b_*`, up to negligible mass.  With
`τ = (1 + s/(C k b_*)) λ` (width `+ log 2`) and `W_*` independent of `λ` and `τ`, the forward degree test gives
`d_G(W_*; τ) - d_G(W_*; λ) = O(b_*)` outside an exponential tail; rescaling gives `O(k b_*²)`. -/
theorem p92_erase_replace (P : Params9) (hP : P.Valid) (c₀ C₁ c₁ : ℝ) (hc₀ : 0 < c₀) (hC₁ : 0 < C₁)
    (hc₁ : 0 < c₁) :
    ∃ C > (0 : ℝ), ∃ c > (0 : ℝ), ∃ n₀ : ℕ, ∀ n ≥ n₀, ∀ {N : ℕ} {E : Fin N → Fin N → Prop}
      {X Y : Finset (Fin N)} {κ : ℝ} {G : Colour} {M : TagMix N} (S : Setup9 P n N M)
      (I : IDMap9 P n),
      CoreInput9 P κ E X Y G M S I → RegularityCert9 S I E G c₀ → EraseCert9 S I E G C₁ c₁ →
        ReplaceCert9 S I E G C c := by
  sorry

/-! ## P9.2-cov (09:222–268) -/

/-- P9.2-cov (09:226–262): at each prefix `λ` of the unmasked core order, the covariance of the next anchor's
and the target's hit indicators has magnitude at most `a_* n^{-2χ}` outside raw probability `e^{-c n^u}`.  If not,
fix a sign and target set `X_0` of mass `ρ = e^{-O(n^u)}` with conditioned anchor sets `B_x` of mass `ρ`; draw
`t = ⌈n^{8χ}⌉` conditioned anchors, use `E‖S‖²_{L²(λ)} = O(t)` (reverse degree test, `t b_*² = o(1)`) and Fubini to
fix one norm-good tuple whose simultaneous violation set has mass `e^{-O(t n^u)}` (width `O(n^{u+8χ})` fits the
first deep budget); the equal-normalizer tilts `λ_± = (√t + S_±)/Z · λ` (`signedTest_equalNormalizer`) bound the
averaged test by `O(b_* √t)`, against the forced `t a_* n^{-2χ}`; `√t a_* n^{-2χ}/b_* ≍ n^{2χ-(h_+-h_-)} → ∞`. -/
theorem p92_covariance (P : Params9) (hP : P.Valid) (c₀ : ℝ) (hc₀ : 0 < c₀) :
    ∃ c > (0 : ℝ), ∃ n₀ : ℕ, ∀ n ≥ n₀, ∀ {N : ℕ} {E : Fin N → Fin N → Prop}
      {X Y : Finset (Fin N)} {κ : ℝ} {G : Colour} {M : TagMix N} (S : Setup9 P n N M)
      (I : IDMap9 P n),
      CoreInput9 P κ E X Y G M S I → RegularityCert9 S I E G c₀ → CovCert9 S I E G c := by
  let c := c₀ / 2
  have hc : 0 < c := by dsimp [c]; linarith
  refine ⟨c, hc, 1, ?_⟩
  intro n hn N E X Y κ G M S I hin hreg
  intro v b hadj k
  by_cases hk : (coreOrder9 I v b)[k]? = none
  · have ha : 0 ≤ P.aStar n := by
      dsimp [Params9.aStar]
      positivity
    have hp : 0 ≤ (n : ℝ) ^ (-(2 * (P.χ : ℝ))) :=
      Real.rpow_nonneg (by positivity) _
    have hthreshold : 0 ≤ P.aStar n * (n : ℝ) ^ (-(2 * (P.χ : ℝ))) :=
      mul_nonneg ha hp
    have hzero : ∀ ω : Outcome9 I N, coreCov9 S E G ω v b k = 0 := by
      intro ω
      simp [coreCov9, hk]
    have hfalse : ∀ ω : Outcome9 I N, ¬ P.aStar n * (n : ℝ) ^ (-(2 * (P.χ : ℝ))) <
        |coreCov9 S E G ω v b k| := by
      intro ω hbad
      rw [hzero ω, abs_zero] at hbad
      exact (not_lt_of_ge hthreshold) hbad
    have hprob : (rawLaw9 S I).pr (fun ω =>
        P.aStar n * (n : ℝ) ^ (-(2 * (P.χ : ℝ))) <
          |coreCov9 S E G ω v b k|) = 0 := by
      unfold FinProb.pr
      apply Finset.sum_eq_zero
      intro ω hω
      simp [hfalse ω]
    rw [hprob]
    exact Real.exp_nonneg _
  · rcases Option.ne_none_iff_exists'.mp hk with ⟨w, hw⟩
    let lam := fun ω : Outcome9 I N =>
      prefixLaw9 E G ω (siteSecond9 S b.1) (coreOrder9 I v b) k
    have hnext : (coreOrder9 I v b)[k]? = some w := hw
    have hcovFormula (ω : Outcome9 I N) :
        coreCov9 S E G ω v b k =
          (lam ω).expect (fun y => hitInd9 E G (anc9 ω w) y *
            hitInd9 E G (anc9 ω (I.center v.1)) y) -
            (lam ω).expect (hitInd9 E G (anc9 ω w)) *
              (lam ω).expect (hitInd9 E G (anc9 ω (I.center v.1))) := by
      simp [coreCov9, lam, hnext]
    -- The remaining case is the signed-test contradiction: condition the next-anchor law on each signed
    -- covariance witness, sample a norm-good tuple, then apply `signedTest_equalNormalizer` against `DeepAt`.
    -- The finite Fubini selection and the conditioned-width accounting remain to be formalized here.
    sorry

/-- The effect of the core hits (09:222–225, 09:264–266): along the unmasked core order the degree of the target
changes at each hit by `cov_λ(g_w, g_x)/d_G(w; λ)` with `d_G(w; λ) ≥ .49` on the core-order tests; at most
`k ≤ n^χ` hits (`IDMap9.core_card`) each of covariance at most `a_* n^{-2χ}` give a total shift at most
`3 a_* n^{-χ}`; a union over the at most `n^χ` prefixes. -/
theorem p92_core_hits (P : Params9) (hP : P.Valid) (c₀ c₁ : ℝ) (hc₀ : 0 < c₀) (hc₁ : 0 < c₁) :
    ∃ c > (0 : ℝ), ∃ n₀ : ℕ, ∀ n ≥ n₀, ∀ {N : ℕ} {E : Fin N → Fin N → Prop}
      {X Y : Finset (Fin N)} {κ : ℝ} {G : Colour} {M : TagMix N} (S : Setup9 P n N M)
      (I : IDMap9 P n),
      CoreInput9 P κ E X Y G M S I → RegularityCert9 S I E G c₀ → CovCert9 S I E G c₁ →
        CoreHitCert9 S I E G c := by
  have hu : 0 < P.u := by
    have hxs : 0 < (P.xS : ℝ) := by exact_mod_cast hP.1.1
    dsimp [Params9.u]
    linarith
  have hcHalf : 0 < c₁ / 2 := by linarith
  let c : ℝ := min c₀ (c₁ / 2) / 2
  have hc : 0 < c := by
    dsimp [c]
    exact div_pos (lt_min hc₀ hcHalf) (by norm_num)
  obtain ⟨nPoly, hPoly⟩ := Lane_q_s09_gain2.eventual_poly_tail
    (u := P.u) (c := c₁) (A := 1) (s := P.χ) hu hc₁
  obtain ⟨nTail, hTail⟩ := Lane_q_s09_gain2.eventual_tail_sum2
    (u := P.u) (c₁ := c₀) (c₂ := c₁ / 2) hu hc₀ hcHalf
  refine ⟨c, hc, max nPoly nTail, ?_⟩
  intro n hn N E X Y κ G M S I hin hreg hcov
  have hnPoly : nPoly ≤ n := le_trans (le_max_left nPoly nTail) hn
  have hnTail : nTail ≤ n := le_trans (le_max_right nPoly nTail) hn
  have hpolyN := hPoly n hnPoly
  have htailN := hTail n hnTail
  rcases hin with ⟨hN, hprep, hdeep, htags, hmasks, htools, hexps, hscales⟩
  rcases hscales with ⟨hnDim, hm, hr, hwidth, hfilter, hfirstWidth, hbsmall, hgain⟩
  have hcount (v : EvenSites9 n) (b : OddSites9 n) :
      (coreCount9 I v b : ℝ) ≤ (n : ℝ) ^ (P.χ : ℝ) := by
    unfold coreCount9
    calc
      ((I.seen b.1 ∩ I.core v.1).card : ℝ) ≤ (I.core v.1).card := by
        exact_mod_cast
          (Finset.card_le_card (Finset.inter_subset_right :
            I.seen b.1 ∩ I.core v.1 ⊆ I.core v.1))
      _ ≤ (n : ℝ) ^ (P.χ : ℝ) := I.core_card v.1 v.2
  have hlen (v : EvenSites9 n) (b : OddSites9 n) :
      ((coreOrder9 I v b).length : ℝ) ≤ (n : ℝ) ^ (P.χ : ℝ) := by
    have hlenNat : (coreOrder9 I v b).length ≤ coreCount9 I v b := by
      simp only [coreOrder9, Finset.length_toList, coreIDs9, coreCount9]
      exact Finset.card_erase_le
    have hlenR : ((coreOrder9 I v b).length : ℝ) ≤ (coreCount9 I v b : ℝ) := by
      exact_mod_cast hlenNat
    exact le_trans hlenR (hcount v b)
  intro v b hb
  classical
  let regBad : Outcome9 I N → Prop := fun ω => ¬ starRegular9 S E G ω v
  let covBad : Outcome9 I N → Prop := fun ω =>
    ∃ k ∈ Finset.range (coreOrder9 I v b).length,
      P.aStar n * (n : ℝ) ^ (-(2 * (P.χ : ℝ))) < |coreCov9 S E G ω v b k|
  let targetBad : Outcome9 I N → Prop := fun ω =>
    3 * P.aStar n * (n : ℝ) ^ (-(P.χ : ℝ)) <
      |rowDeg E G (anc9 ω (I.center v.1))
          (restrictOr9 (siteSecond9 S b.1) (coreHitSet9 E G ω v b)) -
        rowDeg E G (anc9 ω (I.center v.1)) (siteSecond9 S b.1)|
  have hIncl : ∀ ω, targetBad ω → regBad ω ∨ covBad ω := by
    intro ω hbad
    by_contra hnot
    have hregω : starRegular9 S E G ω v := by
      by_contra h
      exact hnot (Or.inl h)
    have hcovω : ¬ covBad ω := by
      intro h
      exact hnot (Or.inr h)
    have hCovGood : ∀ k, k < (coreOrder9 I v b).length →
        |coreCov9 S E G ω v b k| ≤
          P.aStar n * (n : ℝ) ^ (-(2 * (P.χ : ℝ))) := by
      intro k hk
      by_contra hlarge
      apply hcovω
      exact ⟨k, Finset.mem_range.mpr hk, lt_of_not_ge hlarge⟩
    have hdet := Lane_q_s09_gain2.core_order_hit_shift_bound
      S I E G ω v b (hregω b hb).2.2 hbsmall hCovGood hnDim (hlen v b)
    exact (not_lt_of_ge hdet) hbad
  have hcovProb : (rawLaw9 S I).pr covBad ≤
      (coreOrder9 I v b).length * P.tail c₁ n := by
    calc
      (rawLaw9 S I).pr covBad ≤
          ∑ k ∈ Finset.range (coreOrder9 I v b).length,
            (rawLaw9 S I).pr (fun ω =>
              P.aStar n * (n : ℝ) ^ (-(2 * (P.χ : ℝ))) < |coreCov9 S E G ω v b k|) := by
        simpa [covBad] using Lane_q_s09_gain2.pr_exists_finset_le_sum
          (rawLaw9 S I) (Finset.range (coreOrder9 I v b).length)
          (fun k ω => P.aStar n * (n : ℝ) ^ (-(2 * (P.χ : ℝ))) <
            |coreCov9 S E G ω v b k|)
      _ ≤ ∑ k ∈ Finset.range (coreOrder9 I v b).length, P.tail c₁ n := by
        apply Finset.sum_le_sum
        intro k hk
        exact hcov v b hb k
      _ = (coreOrder9 I v b).length * P.tail c₁ n := by simp
  have htailNonneg : 0 ≤ P.tail c₁ n := by
    dsimp [Params9.tail]
    positivity
  have hcovTail : (rawLaw9 S I).pr covBad ≤
      Real.exp (-((c₁ / 2) * (n : ℝ) ^ P.u)) := by
    calc
      (rawLaw9 S I).pr covBad ≤ (coreOrder9 I v b).length * P.tail c₁ n := hcovProb
      _ ≤ (n : ℝ) ^ (P.χ : ℝ) * P.tail c₁ n :=
        mul_le_mul_of_nonneg_right (hlen v b) htailNonneg
      _ ≤ Real.exp (-((c₁ / 2) * (n : ℝ) ^ P.u)) := by
        simpa [Params9.tail, mul_assoc] using hpolyN
  have htailCombined : P.tail c₀ n + Real.exp (-((c₁ / 2) * (n : ℝ) ^ P.u)) ≤
      P.tail c n := by
    simpa [c, Params9.tail, mul_assoc] using htailN
  have hmono := FinProb.pr_mono (rawLaw9 S I) targetBad
    (fun ω => regBad ω ∨ covBad ω) hIncl
  calc
    (rawLaw9 S I).pr targetBad ≤ (rawLaw9 S I).pr (fun ω => regBad ω ∨ covBad ω) := hmono
    _ ≤ (rawLaw9 S I).pr regBad + (rawLaw9 S I).pr covBad :=
      Lane_q_s09_gain2.pr_or_le (rawLaw9 S I) regBad covBad
    _ ≤ P.tail c₀ n + Real.exp (-((c₁ / 2) * (n : ℝ) ^ P.u)) := by
      exact add_le_add (hreg v) hcovTail
    _ ≤ P.tail c n := htailCombined

/-- The combined mean comparison (09:266–268): the three comparisons hold together outside raw probability
`3 max(tails)`, and `C₁ k b_*² + e^{-c₁ n^u} + C₂ k b_*² + 3 a_* n^{-χ} ≤ a_*/100` for large `n` because
`k ≤ n^χ` and `χ + h_+ < 2 h_-` (C-common). -/
theorem p92_mean_comparison (P : Params9) (hP : P.Valid) (C₁ c₁ C₂ c₂ c₃ : ℝ) (hC₁ : 0 < C₁)
    (hc₁ : 0 < c₁) (hC₂ : 0 < C₂) (hc₂ : 0 < c₂) (hc₃ : 0 < c₃) :
    ∃ c > (0 : ℝ), ∃ n₀ : ℕ, ∀ n ≥ n₀, ∀ {N : ℕ} {E : Fin N → Fin N → Prop}
      {X Y : Finset (Fin N)} {κ : ℝ} {G : Colour} {M : TagMix N} (S : Setup9 P n N M)
      (I : IDMap9 P n),
      CoreInput9 P κ E X Y G M S I → CondMeanCert9 S I E G C₁ c₁ → ReplaceCert9 S I E G C₂ c₂ →
        CoreHitCert9 S I E G c₃ → MeanCert9 S I E G c := by
  obtain ⟨nE, hE⟩ :=
    Lane_q_s09_gain2.eventual_mean_error_bound P hP C₁ C₂ c₁ c₂ hc₁ hc₂
  let C : ℝ := min c₁ (min c₂ c₃)
  let c : ℝ := C / 2
  have hC : 0 < C := by dsimp [C]; exact lt_min hc₁ (lt_min hc₂ hc₃)
  have hc : 0 < c := by dsimp [c]; linarith
  have hu : 0 < P.u := by
    have hxS : (0 : ℝ) < (P.xS : ℝ) := by exact_mod_cast hP.1.1
    dsimp [Params9.u]
    linarith
  obtain ⟨nT, hT⟩ := Lane_q_s09_gain2.eventual_tail_sum3
    (u := P.u) (c₁ := c₁) (c₂ := c₂) (c₃ := c₃) hu hc₁ hc₂ hc₃
  refine ⟨c, hc, max nE nT, ?_⟩
  intro n hn N E X Y κ G M S I hin hcond hreplace hcore
  rcases hin with ⟨hN, hprep, hdeep, htags, hmasks, htools, hexps, hscales⟩
  have hnE : nE ≤ n := le_trans (le_max_left nE nT) hn
  have hnT : nT ≤ n := le_trans (le_max_right nE nT) hn
  have htail := hT n hnT
  have hsmall := hE n hnE
  have hcount (v : EvenSites9 n) (b : OddSites9 n) :
      (coreCount9 I v b : ℝ) ≤ (n : ℝ) ^ (P.χ : ℝ) := by
    unfold coreCount9
    calc
      ((I.seen b.1 ∩ I.core v.1).card : ℝ) ≤ (I.core v.1).card := by
        exact_mod_cast Finset.card_le_card Finset.inter_subset_right
      _ ≤ (n : ℝ) ^ (P.χ : ℝ) := I.core_card v.1 v.2
  intro v b hb
  classical
  let A : Outcome9 I N → Prop := fun ω =>
    C₁ * (coreCount9 I v b : ℝ) * P.bStar n ^ 2 + P.tail c₁ n <
      |condCoreMean9 S I E G v b ω -
        rowDeg E G (anc9 ω (I.center v.1))
          (restrictOr9 (outerMean9 S I E G v b)
            (coreHitSet9 E G ω v b))|
  let B : Outcome9 I N → Prop := fun ω =>
    C₂ * (coreCount9 I v b : ℝ) * P.bStar n ^ 2 <
      |rowDeg E G (anc9 ω (I.center v.1))
          (restrictOr9 (outerMean9 S I E G v b)
            (coreHitSet9 E G ω v b)) -
        rowDeg E G (anc9 ω (I.center v.1))
          (restrictOr9 (siteSecond9 S b.1) (coreHitSet9 E G ω v b))|
  let D : Outcome9 I N → Prop := fun ω =>
    3 * P.aStar n * (n : ℝ) ^ (-(P.χ : ℝ)) <
      |rowDeg E G (anc9 ω (I.center v.1))
          (restrictOr9 (siteSecond9 S b.1) (coreHitSet9 E G ω v b)) -
        rowDeg E G (anc9 ω (I.center v.1)) (siteSecond9 S b.1)|
  have hAprob : (rawLaw9 S I).pr A ≤ P.tail c₁ n := by
    simpa [A] using hcond v b hb
  have hBprob : (rawLaw9 S I).pr B ≤ P.tail c₂ n := by
    simpa [B] using hreplace v b hb
  have hDprob : (rawLaw9 S I).pr D ≤ P.tail c₃ n := by
    simpa [D] using hcore v b hb
  have hIncl : ∀ ω, P.aStar n / 100 <
      |condCoreMean9 S I E G v b ω -
        rowDeg E G (anc9 ω (I.center v.1)) (siteSecond9 S b.1)| →
      A ω ∨ B ω ∨ D ω := by
    intro ω hbad
    by_contra hnot
    have hnot' : ¬ A ω ∧ ¬ B ω ∧ ¬ D ω := by
      simpa only [not_or] using hnot
    have hAa : |condCoreMean9 S I E G v b ω -
        rowDeg E G (anc9 ω (I.center v.1))
          (restrictOr9 (outerMean9 S I E G v b)
            (coreHitSet9 E G ω v b))| ≤
        C₁ * (coreCount9 I v b : ℝ) * P.bStar n ^ 2 + P.tail c₁ n :=
      le_of_not_gt hnot'.1
    have hBb : |rowDeg E G (anc9 ω (I.center v.1))
          (restrictOr9 (outerMean9 S I E G v b)
            (coreHitSet9 E G ω v b)) -
        rowDeg E G (anc9 ω (I.center v.1))
          (restrictOr9 (siteSecond9 S b.1) (coreHitSet9 E G ω v b))| ≤
        C₂ * (coreCount9 I v b : ℝ) * P.bStar n ^ 2 := le_of_not_gt hnot'.2.1
    have hDb : |rowDeg E G (anc9 ω (I.center v.1))
          (restrictOr9 (siteSecond9 S b.1) (coreHitSet9 E G ω v b)) -
        rowDeg E G (anc9 ω (I.center v.1)) (siteSecond9 S b.1)| ≤
        3 * P.aStar n * (n : ℝ) ^ (-(P.χ : ℝ)) := le_of_not_gt hnot'.2.2
    have hk := hcount v b
    have hcoeff :
        C₁ * (coreCount9 I v b : ℝ) * P.bStar n ^ 2 +
          C₂ * (coreCount9 I v b : ℝ) * P.bStar n ^ 2 ≤
            (C₁ + C₂) * (n : ℝ) ^ (P.χ : ℝ) * P.bStar n ^ 2 := by
      have h1 := mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left hk hC₁.le) (sq_nonneg (P.bStar n))
      have h2 := mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left hk hC₂.le) (sq_nonneg (P.bStar n))
      nlinarith
    have hbudget :
        C₁ * (coreCount9 I v b : ℝ) * P.bStar n ^ 2 + P.tail c₁ n +
          C₂ * (coreCount9 I v b : ℝ) * P.bStar n ^ 2 +
          3 * P.aStar n * (n : ℝ) ^ (-(P.χ : ℝ)) ≤ P.aStar n / 100 := by
      have ht₂ : 0 ≤ P.tail c₂ n := by
        change 0 ≤ Real.exp _
        exact Real.exp_nonneg _
      linarith [hsmall, hcoeff, ht₂]
    have htri :
        |condCoreMean9 S I E G v b ω -
          rowDeg E G (anc9 ω (I.center v.1)) (siteSecond9 S b.1)| ≤
        C₁ * (coreCount9 I v b : ℝ) * P.bStar n ^ 2 + P.tail c₁ n +
          C₂ * (coreCount9 I v b : ℝ) * P.bStar n ^ 2 +
          3 * P.aStar n * (n : ℝ) ^ (-(P.χ : ℝ)) := by
      let x := condCoreMean9 S I E G v b ω
      let y := rowDeg E G (anc9 ω (I.center v.1))
        (restrictOr9 (outerMean9 S I E G v b)
          (coreHitSet9 E G ω v b))
      let z := rowDeg E G (anc9 ω (I.center v.1))
        (restrictOr9 (siteSecond9 S b.1) (coreHitSet9 E G ω v b))
      let t := rowDeg E G (anc9 ω (I.center v.1)) (siteSecond9 S b.1)
      have hxy : |x - y| ≤ C₁ * (coreCount9 I v b : ℝ) * P.bStar n ^ 2 + P.tail c₁ n := hAa
      have hyz : |y - z| ≤ C₂ * (coreCount9 I v b : ℝ) * P.bStar n ^ 2 := hBb
      have hzt : |z - t| ≤ 3 * P.aStar n * (n : ℝ) ^ (-(P.χ : ℝ)) := hDb
      change |x - t| ≤ _
      calc
        |x - t| = |(x - y) + (y - z) + (z - t)| := by congr 1; ring
        _ ≤ |(x - y) + (y - z)| + |z - t| := abs_add_le _ _
        _ ≤ |x - y| + |y - z| + |z - t| := by
          linarith [abs_add_le (x - y) (y - z)]
        _ ≤ _ := by linarith [hxy, hyz, hzt]
    exact (not_lt_of_ge (htri.trans hbudget)) hbad
  have hmono := FinProb.pr_mono (rawLaw9 S I)
    (fun ω => P.aStar n / 100 <
      |condCoreMean9 S I E G v b ω -
        rowDeg E G (anc9 ω (I.center v.1)) (siteSecond9 S b.1)|)
    (fun ω => A ω ∨ B ω ∨ D ω) hIncl
  calc
    (rawLaw9 S I).pr (fun ω₀ => P.aStar n / 100 <
        |condCoreMean9 S I E G v b ω₀ -
          rowDeg E G (anc9 ω₀ (I.center v.1)) (siteSecond9 S b.1)|) ≤
        (rawLaw9 S I).pr (fun ω => A ω ∨ B ω ∨ D ω) := hmono
    _ ≤ (rawLaw9 S I).pr A + (rawLaw9 S I).pr B + (rawLaw9 S I).pr D :=
        Lane_q_s09_gain2.pr_or3_le _ A B D
    _ ≤ P.tail c₁ n + P.tail c₂ n + P.tail c₃ n := by linarith [hAprob, hBprob, hDprob]
    _ ≤ P.tail c n := by
        simpa [c, C, Params9.tail] using htail
/-! ## P9.2-gain (09:270–294) -/

/-- The surplus of the conditional means (09:270–274): ordinary neighbours (residual flips, same slice as `v`)
have `d_G(W_*; ν_{i_{z(v)}}) ≥ 1/2 + a_*` because `W_*` lies in the support of `μ_{i_{z(v)}}` (`Prep9`); the
special neighbours lose at most `.05 a_* n` outside `E_z` (linear case, `TagsOK9`) or at most `2 m b_* = o(n a_*)`
outside a forward-test exception (sublinear case); with `MeanCert9` at the `n` neighbours the sum of conditional
means is at least `n/2 + (9/10) n a_*` outside core histories of mass `e^{-c n^u}`. -/
theorem p92_gain_means (P : Params9) (hP : P.Valid) (cT c₁ : ℝ) (hcT : 0 < cT) (hc₁ : 0 < c₁) :
    ∃ c > (0 : ℝ), ∃ n₀ : ℕ, ∀ n ≥ n₀, ∀ {N : ℕ} {E : Fin N → Fin N → Prop}
      {X Y : Finset (Fin N)} {κ : ℝ} {G : Colour} {M : TagMix N} (S : Setup9 P n N M)
      (I : IDMap9 P n),
      CoreInput9 P κ E X Y G M S I → TagsOK9 κ E G cT S.tag → MeanCert9 S I E G c₁ →
        GainMeanCert9 S I E G c := by
  obtain ⟨cReg, hcReg, nReg, hregCert⟩ := p92_regularity P hP
  have hu : 0 < P.u := by
    have hxs : 0 < (P.xS : ℝ) := by exact_mod_cast hP.1.1
    dsimp [Params9.u]
    linarith
  have hcHalf : 0 < c₁ / 2 := by linarith
  let cSpec : ℝ := min cT (1 / 2)
  have hcSpec : 0 < cSpec := by
    dsimp [cSpec]
    exact lt_min hcT (by norm_num)
  let c : ℝ := min cReg (min (c₁ / 2) cSpec) / 2
  have hc : 0 < c := by
    dsimp [c]
    exact div_pos (lt_min hcReg (lt_min hcHalf hcSpec)) (by norm_num)
  obtain ⟨nPoly, hPoly⟩ := Lane_q_s09_gain2.eventual_poly_tail
    (u := P.u) (c := c₁) (A := 1) (s := 1) hu hc₁
  obtain ⟨nDeep, hDeepPoly⟩ := Lane_q_s09_gain2.eventual_poly_tail
    (u := P.u) (c := 1) (A := 2) (s := 1) hu (by norm_num)
  obtain ⟨nTail, hTail⟩ := Lane_q_s09_gain2.eventual_tail_sum3
    (u := P.u) (c₁ := cReg) (c₂ := c₁ / 2) (c₃ := cSpec) hu hcReg hcHalf hcSpec
  obtain ⟨nMargin, hMargin⟩ := Lane_q_s09_gain2.eventual_gain_mean_margin9 P hP
  let nBase := max nReg (max nDeep (max nPoly nTail))
  refine ⟨c, hc, max nBase nMargin, ?_⟩
  intro n hn N E X Y κ G M S I hin hTagsOK hMean
  have hnBase : nBase ≤ n := le_trans (le_max_left nBase nMargin) hn
  have hnMargin : nMargin ≤ n := le_trans (le_max_right nBase nMargin) hn
  have hnReg : nReg ≤ n := le_trans (le_max_left nReg (max nDeep (max nPoly nTail))) hnBase
  have hnRest : max nDeep (max nPoly nTail) ≤ n :=
    le_trans (le_max_right nReg _) hnBase
  have hnDeep : nDeep ≤ n := le_trans (le_max_left nDeep (max nPoly nTail)) hnRest
  have hnPair : max nPoly nTail ≤ n := le_trans (le_max_right nDeep _) hnRest
  have hnPoly : nPoly ≤ n := le_trans (le_max_left nPoly nTail) hnPair
  have hnTail : nTail ≤ n := le_trans (le_max_right nPoly nTail) hnPair
  have hpolyN := hPoly n hnPoly
  have hDeepPolyN := hDeepPoly n hnDeep
  have htailN := hTail n hnTail
  have hinCopy := hin
  rcases hin with ⟨hN, hprep, hdeep, htags, hmasks, htools, hexps, hscales⟩
  rcases hscales with ⟨hnDim, hm, hr, hwidth, hfilter, hfirstWidth, hbsmall, hgain⟩
  have hregAt : RegularityCert9 S I E G cReg := hregCert n hnReg S I hinCopy
  intro v
  classical
  let z : CubeVertex (P.m n) := specialWord9 (P.m n) v.1
  let μv : Law N := M.μ (S.tag z)
  have hCoordinate (w : Fin N) :
      (rawLaw9 S I).pr (fun ω => anc9 ω (I.center v.1) = w) = μv.w w := by
    change (FinProb.pi (inputLaw9 S I)).pr
      (fun ω => ω (Sum.inl (I.center v.1)) = w) = μv.w w
    rw [Lane_q_s09_gain2.pi_pr_coordinate (inputLaw9 S I)
      (Sum.inl (I.center v.1)) w]
    simp [inputLaw9, z, μv, I.center_slice]
  have hcoordSet (A : Finset (Fin N)) :
      (rawLaw9 S I).pr (fun ω => anc9 ω (I.center v.1) ∈ A) ≤
        ∑ w ∈ A, μv.w w := by
    calc
      (rawLaw9 S I).pr (fun ω => anc9 ω (I.center v.1) ∈ A) ≤
          ∑ w ∈ A, (rawLaw9 S I).pr (fun ω => anc9 ω (I.center v.1) = w) := by
        simpa using Lane_q_s09_gain2.pr_exists_finset_le_sum
          (rawLaw9 S I) A (fun w ω => anc9 ω (I.center v.1) = w)
      _ = ∑ w ∈ A, μv.w w := by
        apply Finset.sum_congr rfl
        intro w hw
        exact hCoordinate w
  let xBad : Outcome9 I N → Prop := fun ω =>
    ∃ b : StarOdd9 v, P.aStar n / 100 <
      |condCoreMean9 S I E G v b.1 ω -
        rowDeg E G (anc9 ω (I.center v.1)) (siteSecond9 S b.1)|
  let regBad : Outcome9 I N → Prop := fun ω => ¬ starRegular9 S E G ω v
  let tagBad : Outcome9 I N → Prop := fun ω =>
    match P.case with
    | .sub _ _ _ => False
    | .lin _ _ _ _ => anc9 ω (I.center v.1) ∈ tagFail9 E G S.tag z
  let deepBad : Outcome9 I N → Prop := fun ω =>
    match P.case with
    | .sub _ _ _ =>
        ∃ j : Fin (P.m n), 2 * P.bStar n <
          |rowDeg E G (anc9 ω (I.center v.1))
            (M.ν (S.tag (flipWord9 z j))) - 1 / 2|
    | .lin _ _ _ _ => False
  let specBad : Outcome9 I N → Prop := fun ω => tagBad ω ∨ deepBad ω
  let supportBad : Outcome9 I N → Prop := fun ω => (rawLaw9 S I).w ω = 0
  let targetBad : Outcome9 I N → Prop := fun ω =>
    ∑ b : StarOdd9 v, condCoreMean9 S I E G v b.1 ω <
      (n : ℝ) / 2 + (9 / 10 : ℝ) * n * P.aStar n
  have hCardStar : (Fintype.card (StarOdd9 v) : ℝ) = n := by
    have h := Fintype.card_congr (Lane_q_s09_gain2.starCoordEquiv9 v)
    simpa using congrArg (fun k : ℕ => (k : ℝ)) h.symm
  have hMeanProb : (rawLaw9 S I).pr xBad ≤ n * P.tail c₁ n := by
    calc
      (rawLaw9 S I).pr xBad ≤
          ∑ b ∈ (Finset.univ : Finset (StarOdd9 v)), (rawLaw9 S I).pr (fun ω =>
            P.aStar n / 100 <
              |condCoreMean9 S I E G v b.1 ω -
                rowDeg E G (anc9 ω (I.center v.1)) (siteSecond9 S b.1)|) := by
        simpa [xBad] using Lane_q_s09_gain2.pr_exists_finset_le_sum
          (rawLaw9 S I) (Finset.univ : Finset (StarOdd9 v))
          (fun b ω => P.aStar n / 100 <
            |condCoreMean9 S I E G v b.1 ω -
              rowDeg E G (anc9 ω (I.center v.1)) (siteSecond9 S b.1)|)
      _ ≤ ∑ b ∈ (Finset.univ : Finset (StarOdd9 v)), P.tail c₁ n := by
        apply Finset.sum_le_sum
        intro b hb
        exact hMean v b.1 b.2
      _ = ((Finset.univ : Finset (StarOdd9 v)).card : ℝ) * P.tail c₁ n := by simp
      _ = n * P.tail c₁ n := by
        have hcard :
            ((Finset.univ : Finset (StarOdd9 v)).card : ℝ) = n := by
          simpa using hCardStar
        rw [hcard]
  have hMeanTail : (rawLaw9 S I).pr xBad ≤
      Real.exp (-((c₁ / 2) * (n : ℝ) ^ P.u)) := by
    calc
      (rawLaw9 S I).pr xBad ≤ n * P.tail c₁ n := hMeanProb
      _ ≤ Real.exp (-((c₁ / 2) * (n : ℝ) ^ P.u)) := by
        simpa [Params9.tail] using hpolyN
  have hSsFilter : P.Ss (n : ℝ) ≤ P.filterBudget n := by
    have hlog2 : 0 ≤ Real.log 2 := Real.log_nonneg (by norm_num)
    have hlogRatio : 0 ≤ Real.log (100 / 49 : ℝ) := Real.log_nonneg (by norm_num)
    have hID : 0 ≤ P.idBudget n := by
      dsimp [Params9.idBudget]
      positivity
    have hm0 : 0 ≤ (P.m n : ℝ) := by positivity
    have hu0 : 0 ≤ (n : ℝ) ^ P.u := by positivity
    have hExtra : 0 ≤ (n : ℝ) ^ P.u + Real.log 2 +
        Real.log (100 / 49 : ℝ) * (P.idBudget n + (P.m n : ℝ)) := by
      positivity
    dsimp [Params9.filterBudget]
    linarith
  have hFilterLeD : P.filterBudget n ≤ P.Sd (n : ℝ) := by
    have hu0 : 0 ≤ (n : ℝ) ^ P.u := by positivity
    linarith [hfilter]
  have hSsLeD : P.Ss (n : ℝ) ≤ P.Sd (n : ℝ) := le_trans hSsFilter hFilterLeD
  have hTagProb : (rawLaw9 S I).pr tagBad ≤ P.tail cT n := by
    cases hcase : P.case with
    | sub yS yD yM =>
        simp [FinProb.pr, tagBad, hcase, Params9.tail] <;> positivity
    | lin αS αD hB yB =>
        have htagMass :
            ∑ w ∈ tagFail9 E G S.tag z, μv.w w ≤ P.tail cT n := by
          have hnot := hTagsOK.2.2 z
          have hnot' : ¬ P.tail cT n <
              ∑ w ∈ tagFail9 E G S.tag z, (M.μ (S.tag z)).w w := by
            simpa [tagBad9, hcase] using hnot
          exact le_of_not_gt hnot'
        calc
          (rawLaw9 S I).pr tagBad ≤
              ∑ w ∈ tagFail9 E G S.tag z, μv.w w := by
            simpa [tagBad, hcase] using hcoordSet (tagFail9 E G S.tag z)
          _ ≤ P.tail cT n := htagMass
  have hDeepProb : (rawLaw9 S I).pr deepBad ≤
      Real.exp (-((1 / 2 : ℝ) * (n : ℝ) ^ P.u)) := by
    cases hcase : P.case with
    | lin αS αD hB yB =>
        simp [FinProb.pr, deepBad, hcase, Params9.tail] <;> positivity
    | sub yS yD yM =>
        let badJ : Fin (P.m n) → Outcome9 I N → Prop := fun j ω =>
          2 * P.bStar n <
            |rowDeg E G (anc9 ω (I.center v.1))
              (M.ν (S.tag (flipWord9 z j))) - 1 / 2|
        have hchiPos : 0 < (P.χ : ℝ) := by
          exact_mod_cast hP.2.2.2.2.1.1
        have hnReal : 1 ≤ (n : ℝ) := by exact_mod_cast hnDim
        have hpow : (n : ℝ) ^ P.u ≤ (n : ℝ) ^ (P.u + 8 * (P.χ : ℝ)) :=
          Real.rpow_le_rpow_of_exponent_le hnReal (by nlinarith)
        have hSingle : ∀ j : Fin (P.m n),
            (rawLaw9 S I).pr (badJ j) ≤ 2 * Real.exp (-(n : ℝ) ^ P.u) := by
          intro j
          let νj : Law N := M.ν (S.tag (flipWord9 z j))
          rcases hprep.2 (S.tag z) (htags z) with
            ⟨hμX, hμY, hμWidth, hνWidth, hdegree⟩
          rcases hprep.2 (S.tag (flipWord9 z j)) (htags (flipWord9 z j)) with
            ⟨hμjX, hνjY, hμjWidth, hνjWidth, hdegreej⟩
          let w₀ : ℝ := (n : ℝ) ^ (P.xS : ℝ) + (P.hPlus : ℝ) * Real.log (n : ℝ) + 1
          have hμWidth' : μv.WidthLE w₀ := by simpa [μv, w₀] using hμWidth
          have hνWidthD : νj.WidthLE (P.Sd (n : ℝ)) := by
            intro y
            dsimp [νj]
            exact le_trans (hνjWidth y)
              (div_le_div_of_nonneg_right (Real.exp_le_exp.mpr hSsLeD) (by positivity))
          have hfit : w₀ + (n : ℝ) ^ (P.u + 8 * (P.χ : ℝ)) ≤
              (n : ℝ) ^ (P.xD : ℝ) := by simpa [w₀] using hfirstWidth
          have hwidthD : w₀ ≤ (n : ℝ) ^ (P.xD : ℝ) := by
            have hpowerNonneg : 0 ≤ (n : ℝ) ^ (P.u + 8 * (P.χ : ℝ)) := by positivity
            linarith
          have hforward := htools.1 G νj hνjY hνWidthD μv hμX w₀ hμWidth' hwidthD
          let A : Finset (Fin N) := Finset.univ.filter (fun y =>
            2 * P.bStar n < |rowDeg E G y νj - 1 / 2|)
          have hset : badJ j = fun ω => anc9 ω (I.center v.1) ∈ A := by
            funext ω
            simp [badJ, A, νj, Finset.mem_filter]
          have harg : w₀ - (n : ℝ) ^ (P.xD : ℝ) ≤ -(n : ℝ) ^ P.u := by
            linarith [hfit, hpow]
          have hmassBad : ∑ y ∈ A, μv.w y ≤
              2 * Real.exp (w₀ - (n : ℝ) ^ (P.xD : ℝ)) := by
            simpa [A, νj] using hforward
          calc
            (rawLaw9 S I).pr (badJ j) =
                (rawLaw9 S I).pr (fun ω => anc9 ω (I.center v.1) ∈ A) := by rw [hset]
            _ ≤ ∑ y ∈ A, μv.w y := hcoordSet A
            _ ≤ 2 * Real.exp (w₀ - (n : ℝ) ^ (P.xD : ℝ)) := hmassBad
            _ ≤ 2 * Real.exp (-(n : ℝ) ^ P.u) := by
              exact mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr harg) (by norm_num)
        have hUnion : (rawLaw9 S I).pr (deepBad) ≤
            (P.m n : ℝ) * (2 * Real.exp (-(n : ℝ) ^ P.u)) := by
          calc
            (rawLaw9 S I).pr deepBad ≤
                ∑ j ∈ (Finset.univ : Finset (Fin (P.m n))),
                  (rawLaw9 S I).pr (badJ j) := by
              simpa [deepBad, hcase, badJ] using Lane_q_s09_gain2.pr_exists_finset_le_sum
                (rawLaw9 S I) (Finset.univ : Finset (Fin (P.m n))) badJ
            _ ≤ ∑ j ∈ (Finset.univ : Finset (Fin (P.m n))),
                  2 * Real.exp (-(n : ℝ) ^ P.u) := by
              apply Finset.sum_le_sum
              intro j hj
              exact hSingle j
            _ = (P.m n : ℝ) * (2 * Real.exp (-(n : ℝ) ^ P.u)) := by simp
        have hmR : (P.m n : ℝ) ≤ (n : ℝ) := by exact_mod_cast hm
        calc
          (rawLaw9 S I).pr deepBad ≤ (P.m n : ℝ) *
              (2 * Real.exp (-(n : ℝ) ^ P.u)) := hUnion
          _ ≤ (n : ℝ) * (2 * Real.exp (-(n : ℝ) ^ P.u)) :=
              mul_le_mul_of_nonneg_right hmR (by positivity)
          _ = 2 * (n : ℝ) * Real.exp (-(1 : ℝ) * (n : ℝ) ^ P.u) := by ring
          _ ≤ Real.exp (-((1 / 2 : ℝ) * (n : ℝ) ^ P.u)) := by
              simpa [Params9.tail, mul_assoc] using hDeepPolyN
  have hSpecProb : (rawLaw9 S I).pr specBad ≤ P.tail cSpec n := by
    cases hcase : P.case with
    | sub yS yD yM =>
        have htailOrder : Real.exp (-((1 / 2 : ℝ) * (n : ℝ) ^ P.u)) ≤ P.tail cSpec n := by
          dsimp [Params9.tail]
          apply Real.exp_le_exp.mpr
          have hpow0 : 0 ≤ (n : ℝ) ^ P.u := by positivity
          have hmin : cSpec ≤ (1 / 2 : ℝ) := by dsimp [cSpec]; exact min_le_right _ _
          nlinarith [mul_nonneg (sub_nonneg.mpr hmin) hpow0]
        simpa [specBad, tagBad, deepBad, hcase] using hDeepProb.trans htailOrder
    | lin αS αD hB yB =>
        have htailOrder : P.tail cT n ≤ P.tail cSpec n := by
          dsimp [Params9.tail]
          apply Real.exp_le_exp.mpr
          have hpow0 : 0 ≤ (n : ℝ) ^ P.u := by positivity
          have hmin : cSpec ≤ cT := by dsimp [cSpec]; exact min_le_left _ _
          nlinarith [mul_nonneg (sub_nonneg.mpr hmin) hpow0]
        have htag := hTagProb
        simpa [specBad, deepBad, hcase] using htag.trans htailOrder
  have hSupportProb : (rawLaw9 S I).pr supportBad = 0 := by
    unfold FinProb.pr
    apply Finset.sum_eq_zero
    intro ω hω
    by_cases hz : (rawLaw9 S I).w ω = 0 <;> simp [supportBad, hz]
  have hBadUnion : (rawLaw9 S I).pr
      (fun ω => regBad ω ∨ xBad ω ∨ specBad ω ∨ supportBad ω) ≤
        P.tail cReg n + Real.exp (-((c₁ / 2) * (n : ℝ) ^ P.u)) + P.tail cSpec n := by
    calc
      (rawLaw9 S I).pr (fun ω => regBad ω ∨ xBad ω ∨ specBad ω ∨ supportBad ω) ≤
          (rawLaw9 S I).pr (fun ω => regBad ω ∨ xBad ω ∨ specBad ω) +
            (rawLaw9 S I).pr supportBad :=
              by
                simpa only [or_assoc] using
                  (Lane_q_s09_gain2.pr_or_le (rawLaw9 S I)
                    (fun ω => regBad ω ∨ xBad ω ∨ specBad ω) supportBad)
      _ ≤ (rawLaw9 S I).pr regBad + (rawLaw9 S I).pr xBad +
            (rawLaw9 S I).pr specBad := by
        have h := Lane_q_s09_gain2.pr_or3_le (rawLaw9 S I) regBad xBad specBad
        rw [hSupportProb]
        linarith
      _ ≤ P.tail cReg n + Real.exp (-((c₁ / 2) * (n : ℝ) ^ P.u)) + P.tail cSpec n := by
        exact add_le_add (add_le_add (hregAt v) hMeanTail) hSpecProb
  have htailCombined :
      P.tail cReg n + Real.exp (-((c₁ / 2) * (n : ℝ) ^ P.u)) + P.tail cSpec n ≤ P.tail c n := by
    simpa [c, Params9.tail, add_assoc] using htailN
  have hIncl : ∀ ω, targetBad ω →
      regBad ω ∨ xBad ω ∨ specBad ω ∨ supportBad ω := by
    intro ω hbad
    by_contra hnot
    have hregω : starRegular9 S E G ω v := by
      by_contra h
      exact hnot (Or.inl h)
    have hmeanω : ¬ xBad ω := by
      intro h
      exact hnot (Or.inr (Or.inl h))
    have hspecω : ¬ specBad ω := by
      intro h
      exact hnot (Or.inr (Or.inr (Or.inl h)))
    have hsupportω : (rawLaw9 S I).w ω ≠ 0 := by
      intro h
      exact hnot (Or.inr (Or.inr (Or.inr h)))
    have hdet : ¬ targetBad ω := by
      let x := anc9 ω (I.center v.1)
      have hmeanBound (b : StarOdd9 v) :
          |condCoreMean9 S I E G v b.1 ω -
            rowDeg E G (anc9 ω (I.center v.1)) (siteSecond9 S b.1)| ≤
              P.aStar n / 100 := by
        by_contra hlarge
        apply hmeanω
        exact ⟨b, lt_of_not_ge hlarge⟩
      have hrawPos : 0 < (rawLaw9 S I).w ω :=
        lt_of_le_of_ne ((rawLaw9 S I).nonneg ω) hsupportω.symm
      have hAtom : (rawLaw9 S I).w ω ≤
          (rawLaw9 S I).pr (fun ω' => anc9 ω' (I.center v.1) = x) := by
        have hsingle := Finset.single_le_sum
          (s := (Finset.univ : Finset (Outcome9 I N)))
          (f := fun ω' => @ite ℝ (anc9 ω' (I.center v.1) = x)
            (Classical.propDecidable _) ((rawLaw9 S I).w ω') 0)
          (fun ω' hω' => by
            split_ifs
            · exact (rawLaw9 S I).nonneg ω'
            · norm_num)
          (Finset.mem_univ ω)
        simpa [x, FinProb.pr] using hsingle
      have hcoordPos : 0 < μv.w x := by
        have h := lt_of_lt_of_le hrawPos hAtom
        rw [hCoordinate x] at h
        exact h
      have hxNZ : μv.w x ≠ 0 := ne_of_gt hcoordPos
      have hOrdinary : ∀ j : Fin n, P.m n ≤ j.val →
          1 / 2 + P.aStar n ≤
            rowDeg E G x (siteSecond9 S (Lane_q_s09_gain2.starCoord9 v j).1) := by
        intro j hj
        have hsite : siteSecond9 S (Lane_q_s09_gain2.starCoord9 v j).1 =
            M.ν (S.tag z) := by
          dsimp [siteSecond9, Lane_q_s09_gain2.starCoord9, z]
          rw [Lane_q_s09_gain2.specialWord9_starCoord_residual v j hm hj]
        rcases hprep.2 (S.tag z) (htags z) with ⟨_, _, _, _, hdegree⟩
        rw [hsite]
        exact hdegree x hxNZ
      let d : Fin n → ℝ := fun j =>
        rowDeg E G x (siteSecond9 S (Lane_q_s09_gain2.starCoord9 v j).1)
      let Jsp : Finset (Fin n) := Finset.univ.filter (fun j => j.val < P.m n)
      let Jres : Finset (Fin n) := Finset.univ.filter (fun j => P.m n ≤ j.val)
      have hsumBase :
          (∑ b : StarOdd9 v, rowDeg E G x (siteSecond9 S b.1)) = ∑ j : Fin n, d j := by
        symm
        exact Fintype.sum_equiv (Lane_q_s09_gain2.starCoordEquiv9 v)
          (fun j => d j)
          (fun b => rowDeg E G x (siteSecond9 S b.1))
          (by intro j; rfl)
      have hsumSurplus :
          (∑ b : StarOdd9 v, (rowDeg E G x (siteSecond9 S b.1) - 1 / 2)) =
            ∑ j : Fin n, (d j - 1 / 2) := by
        symm
        exact Fintype.sum_equiv (Lane_q_s09_gain2.starCoordEquiv9 v)
          (fun j => d j - 1 / 2)
          (fun b => rowDeg E G x (siteSecond9 S b.1) - 1 / 2)
          (by intro j; rfl)
      have hsplit :
          (∑ j : Fin n, (d j - 1 / 2)) =
            (∑ j ∈ Jsp, (d j - 1 / 2)) + (∑ j ∈ Jres, (d j - 1 / 2)) := by
        simpa [Jsp, Jres, not_lt] using
          (Finset.sum_filter_add_sum_filter_not (Finset.univ : Finset (Fin n))
            (fun j : Fin n => j.val < P.m n) (fun j => d j - 1 / 2)).symm
      have hcardSpecial : Jsp.card = P.m n := by
        have hcardSub : Fintype.card {j : Fin n // j.val < P.m n} = P.m n := by
          have h := Fintype.card_congr (Lane_q_s09_gain2.specialCoordEquiv9 hm)
          simpa using h.symm
        have hcardSubtype : Fintype.card {j : Fin n // j.val < P.m n} = Jsp.card :=
          Fintype.card_of_subtype Jsp (by intro j; simp [Jsp])
        exact hcardSubtype.symm.trans hcardSub
      have hcardSplit : Jsp.card + Jres.card = n := by
        have h := Finset.card_filter_add_card_filter_not
          (s := (Finset.univ : Finset (Fin n))) (fun j : Fin n => j.val < P.m n)
        simpa [Jsp, Jres, not_lt] using h
      have hcardResidual : Jres.card = n - P.m n := by omega
      have hcardResidualR : (Jres.card : ℝ) = (n : ℝ) - (P.m n : ℝ) := by
        have h := congrArg (fun k : ℕ => (k : ℝ)) hcardResidual
        simpa [Nat.cast_sub hm] using h
      have hresidualLower : ((n : ℝ) - (P.m n : ℝ)) * P.aStar n ≤
          ∑ j ∈ Jres, (d j - 1 / 2) := by
        have hlower : (Jres.card : ℝ) * P.aStar n ≤
            ∑ j ∈ Jres, (d j - 1 / 2) := by
          calc
            (Jres.card : ℝ) * P.aStar n = ∑ j ∈ Jres, P.aStar n := by simp
            _ ≤ ∑ j ∈ Jres, (d j - 1 / 2) := by
              apply Finset.sum_le_sum
              intro j hj
              have hjres : P.m n ≤ j.val := (Finset.mem_filter.mp hj).2
              have hdegree := hOrdinary j hjres
              linarith
        rw [hcardResidualR] at hlower
        exact hlower
      let eSpecial := Lane_q_s09_gain2.specialCoordEquiv9 hm
      have hspecialWord (j : Fin (P.m n)) :
          specialWord9 (P.m n) (cubeFlip v.1 (eSpecial j).1) = flipWord9 z j := by
        have h := Lane_q_s09_gain2.specialWord9_starCoord v (eSpecial j).1 hm (eSpecial j).2
        have hidx : (eSpecial j).1.val = j.val := by
          change (Fin.castLE hm j).val = j.val
          rfl
        have hcast : (⟨(eSpecial j).1.val, (eSpecial j).2⟩ : Fin (P.m n)) = j :=
          Fin.ext hidx
        calc
          specialWord9 (P.m n) (cubeFlip v.1 (eSpecial j).1) =
              flipWord9 (specialWord9 (P.m n) v.1)
                ⟨(eSpecial j).1.val, (eSpecial j).2⟩ := h
          _ = flipWord9 z j := by
            change flipWord9 (specialWord9 (P.m n) v.1)
                ⟨(eSpecial j).1.val, (eSpecial j).2⟩ =
              flipWord9 (specialWord9 (P.m n) v.1) j
            exact congrArg (flipWord9 (specialWord9 (P.m n) v.1)) hcast
      have hsiteSpecial (j : Fin (P.m n)) :
          d (eSpecial j).1 =
            rowDeg E G x (M.ν (S.tag (flipWord9 z j))) := by
        change rowDeg E G x (M.ν (S.tag
          (specialWord9 (P.m n) (cubeFlip v.1 (eSpecial j).1)))) = _
        rw [hspecialWord j]
      have hsumSubtype :
          (∑ j : Fin (P.m n),
            (rowDeg E G x (M.ν (S.tag (flipWord9 z j))) - 1 / 2)) =
          ∑ q : {j : Fin n // j.val < P.m n}, (d q.1 - 1 / 2) := by
        exact Fintype.sum_equiv eSpecial
          (fun j => rowDeg E G x (M.ν (S.tag (flipWord9 z j))) - 1 / 2)
          (fun q => d q.1 - 1 / 2)
          (by intro j; rw [hsiteSpecial j])
      have hsumSpecial :
          (∑ j : Fin (P.m n),
            (rowDeg E G x (M.ν (S.tag (flipWord9 z j))) - 1 / 2)) =
          ∑ j ∈ Jsp, (d j - 1 / 2) := by
        have hcardSubtype :
            Fintype.card {j : Fin n // j.val < P.m n} = Jsp.card :=
          Fintype.card_of_subtype Jsp (by intro j; simp [Jsp])
        have hsumD :
            (∑ q : {j : Fin n // j.val < P.m n}, d q.1) = ∑ j ∈ Jsp, d j := by
          simpa [Jsp] using
            (Finset.sum_subtype_eq_sum_filter
              (s := (Finset.univ : Finset (Fin n)))
              (p := fun j : Fin n => j.val < P.m n) (f := d))
        calc
          (∑ j : Fin (P.m n),
              (rowDeg E G x (M.ν (S.tag (flipWord9 z j))) - 1 / 2)) =
              ∑ q : {j : Fin n // j.val < P.m n}, (d q.1 - 1 / 2) := hsumSubtype
          _ = (∑ q : {j : Fin n // j.val < P.m n}, d q.1) -
                (Fintype.card {j : Fin n // j.val < P.m n} : ℝ) * (1 / 2) := by simp
          _ = (∑ j ∈ Jsp, d j) - (Jsp.card : ℝ) * (1 / 2) := by rw [hsumD, hcardSubtype]
          _ = ∑ j ∈ Jsp, (d j - 1 / 2) := by rw [Finset.sum_sub_distrib]; simp
      let specialLoss : ℝ := match P.case with
        | .sub _ _ _ => -(P.m n : ℝ) * (2 * P.bStar n)
        | .lin _ _ _ _ => -((1 / 20 : ℝ) * P.aStar n * n)
      have hspecialLower : specialLoss ≤ ∑ j ∈ Jsp, (d j - 1 / 2) := by
        cases hcase : P.case with
        | lin αS αD hB yB =>
          simp only [specialLoss, hcase]
          have hnotTag : ¬ tagBad ω := by
            intro h
            exact hspecω (Or.inl h)
          have hnotMem : x ∉ tagFail9 E G S.tag z := by
            simpa [tagBad, hcase, x] using hnotTag
          have hnotSurplus : ¬ tagSurplus9 E G S.tag z x <
              -((1 / 20 : ℝ) * P.aStar n * n) := by
            intro hlt
            apply hnotMem
            exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, hlt⟩
          have htagLower : -((1 / 20 : ℝ) * P.aStar n * n) ≤
              tagSurplus9 E G S.tag z x := le_of_not_gt hnotSurplus
          have hsumTag : tagSurplus9 E G S.tag z x =
              ∑ j : Fin (P.m n),
                (rowDeg E G x (M.ν (S.tag (flipWord9 z j))) - 1 / 2) := rfl
          calc
            -((1 / 20 : ℝ) * P.aStar n * n) ≤ tagSurplus9 E G S.tag z x := htagLower
            _ = ∑ j : Fin (P.m n),
                (rowDeg E G x (M.ν (S.tag (flipWord9 z j))) - 1 / 2) := hsumTag
            _ = ∑ j ∈ Jsp, (d j - 1 / 2) := hsumSpecial
        | sub yS yD yM =>
          simp only [specialLoss, hcase]
          have hdeepGood : ∀ j : Fin (P.m n),
              |rowDeg E G x (M.ν (S.tag (flipWord9 z j))) - 1 / 2| ≤
                2 * P.bStar n := by
            intro j
            by_contra hlarge
            have hlt : 2 * P.bStar n <
                |rowDeg E G (anc9 ω (I.center v.1))
                  (M.ν (S.tag (flipWord9 z j))) - (2 : ℝ)⁻¹| := by
              simpa [x, one_div] using lt_of_not_ge hlarge
            have hbad : deepBad ω := by
              simpa [deepBad, hcase, one_div] using ⟨j, hlt⟩
            exact hspecω (Or.inr hbad)
          have hlow : -(P.m n : ℝ) * (2 * P.bStar n) ≤
              ∑ j : Fin (P.m n),
                (rowDeg E G x (M.ν (S.tag (flipWord9 z j))) - 1 / 2) := by
            calc
              -(P.m n : ℝ) * (2 * P.bStar n) =
                  ∑ j : Fin (P.m n), -(2 * P.bStar n) := by simp
              _ ≤ ∑ j : Fin (P.m n),
                  (rowDeg E G x (M.ν (S.tag (flipWord9 z j))) - 1 / 2) := by
                apply Finset.sum_le_sum
                intro j hj
                have habs := abs_le.mp (hdeepGood j)
                linarith
          calc
            -(P.m n : ℝ) * (2 * P.bStar n) ≤
                ∑ j : Fin (P.m n),
                  (rowDeg E G x (M.ν (S.tag (flipWord9 z j))) - 1 / 2) := hlow
            _ = ∑ j ∈ Jsp, (d j - 1 / 2) := hsumSpecial
      let baseDegree : StarOdd9 v → ℝ := fun b =>
        rowDeg E G x (siteSecond9 S b.1)
      have hconstStar : (∑ b : StarOdd9 v, (1 / 2 : ℝ)) = (n : ℝ) / 2 := by
        calc
          (∑ b : StarOdd9 v, (1 / 2 : ℝ)) =
              (Fintype.card (StarOdd9 v) : ℝ) * (1 / 2) := by simp
          _ = (n : ℝ) / 2 := by rw [hCardStar]; ring
      have hbaseEq :
          (∑ b : StarOdd9 v, baseDegree b) =
            (n : ℝ) / 2 + (∑ j ∈ Jsp, (d j - 1 / 2)) +
              ∑ j ∈ Jres, (d j - 1 / 2) := by
        calc
          (∑ b : StarOdd9 v, baseDegree b) =
              ∑ b : StarOdd9 v, ((baseDegree b - 1 / 2) + 1 / 2) := by
                apply Finset.sum_congr rfl
                intro b hb
                ring
          _ = (∑ b : StarOdd9 v, (baseDegree b - 1 / 2)) +
                ∑ b : StarOdd9 v, (1 / 2 : ℝ) := by rw [Finset.sum_add_distrib]
          _ = (∑ j : Fin n, (d j - 1 / 2)) + (n : ℝ) / 2 := by
                rw [hsumSurplus, hconstStar]
          _ = (n : ℝ) / 2 + (∑ j ∈ Jsp, (d j - 1 / 2)) +
                ∑ j ∈ Jres, (d j - 1 / 2) := by rw [hsplit]; ring
      have hbaseLower :
          (n : ℝ) / 2 + ((n : ℝ) - (P.m n : ℝ)) * P.aStar n + specialLoss ≤
            ∑ b : StarOdd9 v, baseDegree b := by
        rw [hbaseEq]
        linarith [hresidualLower, hspecialLower]
      have hmeanPoint (b : StarOdd9 v) :
          baseDegree b - P.aStar n / 100 ≤ condCoreMean9 S I E G v b.1 ω := by
        have habs := abs_le.mp (hmeanBound b)
        linarith
      have hmeanSum :
          (∑ b : StarOdd9 v, baseDegree b) - (n : ℝ) * P.aStar n / 100 ≤
            ∑ b : StarOdd9 v, condCoreMean9 S I E G v b.1 ω := by
        have hsumPoint :
            (∑ b : StarOdd9 v, (baseDegree b - P.aStar n / 100)) ≤
              ∑ b : StarOdd9 v, condCoreMean9 S I E G v b.1 ω := by
          apply Finset.sum_le_sum
          intro b hb
          exact hmeanPoint b
        have hconst :
            (∑ b : StarOdd9 v, (P.aStar n / 100)) =
              (n : ℝ) * P.aStar n / 100 := by
          calc
            (∑ b : StarOdd9 v, (P.aStar n / 100)) =
                (Fintype.card (StarOdd9 v) : ℝ) * (P.aStar n / 100) := by simp
            _ = (n : ℝ) * P.aStar n / 100 := by rw [hCardStar]; ring
        calc
          (∑ b : StarOdd9 v, baseDegree b) - (n : ℝ) * P.aStar n / 100 =
              ∑ b : StarOdd9 v, (baseDegree b - P.aStar n / 100) := by
                rw [Finset.sum_sub_distrib, hconst]
          _ ≤ ∑ b : StarOdd9 v, condCoreMean9 S I E G v b.1 ω := hsumPoint
      have hmeanSumLower :
          (n : ℝ) / 2 + ((n : ℝ) - (P.m n : ℝ)) * P.aStar n + specialLoss -
              (n : ℝ) * P.aStar n / 100 ≤
            ∑ b : StarOdd9 v, condCoreMean9 S I E G v b.1 ω := by
        linarith [hbaseLower, hmeanSum]
      have hmargin :
          (n : ℝ) / 2 + ((n : ℝ) - (P.m n : ℝ)) * P.aStar n + specialLoss -
              (n : ℝ) * P.aStar n / 100 ≥
            (n : ℝ) / 2 + (9 / 10 : ℝ) * n * P.aStar n := by
        change (n : ℝ) / 2 + ((n : ℝ) - (P.m n : ℝ)) * P.aStar n +
            Lane_q_s09_gain2.gainMeanSpecialLoss9 P n -
              (n : ℝ) * P.aStar n / 100 ≥
          (n : ℝ) / 2 + (9 / 10 : ℝ) * n * P.aStar n
        linarith [hMargin n hnMargin]
      have hfinal :
          (n : ℝ) / 2 + (9 / 10 : ℝ) * n * P.aStar n ≤
            ∑ b : StarOdd9 v, condCoreMean9 S I E G v b.1 ω :=
        le_trans hmargin hmeanSumLower
      intro htarget
      exact (not_lt_of_ge hfinal) htarget
    exact hdet hbad
  have hmono := FinProb.pr_mono (rawLaw9 S I) targetBad
    (fun ω => regBad ω ∨ xBad ω ∨ specBad ω ∨ supportBad ω) hIncl
  calc
    (rawLaw9 S I).pr targetBad ≤
        (rawLaw9 S I).pr (fun ω => regBad ω ∨ xBad ω ∨ specBad ω ∨ supportBad ω) := hmono
    _ ≤ P.tail cReg n + Real.exp (-((c₁ / 2) * (n : ℝ) ^ P.u)) + P.tail cSpec n := hBadUnion
    _ ≤ P.tail c n := htailCombined

/-- The concentration bound with the core fixed (09:276–290): conditionally on the core history of `ω₀`, a
downward deviation of `.1 n a_*` of the clipped fractions below their conditional means has probability at most
`exp(-n a_*²/(800 (r+3) b_*²))`. -/
def GainConc9 {P : Params9} {n N : ℕ} {M : TagMix N} (S : Setup9 P n N M) (I : IDMap9 P n)
    (E : Fin N → Fin N → Prop) (G : Colour) : Prop :=
  ∀ (v : EvenSites9 n) (ω₀ : Outcome9 I N),
    condCorePr9 S I v ω₀ (fun ω =>
      ∑ b : StarOdd9 v, clippedFrac9 S E G ω v b.1 ≤
        ∑ b : StarOdd9 v, condCoreMean9 S I E G v b.1 ω₀ - (n : ℝ) * P.aStar n / 10) ≤
      Real.exp (-((n : ℝ) * P.aStar n ^ 2 / (800 * ((P.radius n : ℝ) + 3) * P.bStar n ^ 2)))

/-- P9.2-gain, concentration (09:276–290): with the core fixed, the remaining inputs are independent outside-core
anchors and row masks; each clipped fraction reads one mask and its outer anchors, and each outer anchor is read
at most `r + 3` times (`IDMap9.read_bound`).  Exponential Markov, the product-space Hölder inequality
(`xFinner`, `d = r + 3`) and Hoeffding's lemma (`xHoeffdingLemma`, range `4 b_*`) give the bound `GainConc9`
for every dimension `n ≥ 1`. -/
theorem p92_gain_concentration {P : Params9} {n N : ℕ} {M : TagMix N} (S : Setup9 P n N M)
    (I : IDMap9 P n) (E : Fin N → Fin N → Prop) (G : Colour) (hn : 1 ≤ n) (hN : 0 < N) :
    GainConc9 S I E G := by
  intro v ω₀
  have hB : 0 ≤ P.bStar n := by
    dsimp [Params9.bStar]
    exact Real.rpow_nonneg (by positivity) _
  have hclip (b : StarOdd9 v) (ω : Outcome9 I N) :
      1 / 2 - 2 * P.bStar n ≤ clippedFrac9 S E G ω v b.1 ∧
        clippedFrac9 S E G ω v b.1 ≤ 1 / 2 + 2 * P.bStar n :=
    Lane_q_s09_gain2.clippedFrac9_bounds ω v b.1 hB
  have hcentered (b : StarOdd9 v) (ω : Outcome9 I N) :
      -(2 * P.bStar n) ≤ clippedFrac9 S E G ω v b.1 - 1 / 2 ∧
        clippedFrac9 S E G ω v b.1 - 1 / 2 ≤ 2 * P.bStar n := by
    constructor <;> linarith [(hclip b ω).1, (hclip b ω).2]
  -- After conditioning on `sameCore9`, the row masks and noncore anchors are product inputs. The read bound
  -- controls each anchor's degree in the scopes, so `xFinner` and Hoeffding apply to this centered sum.
  have hWidth : ∀ b : StarOdd9 v, ∀ ω : Outcome9 I N,
      (-(2 * P.bStar n) : ℝ) ≤ clippedFrac9 S E G ω v b.1 - 1 / 2 ∧
        clippedFrac9 S E G ω v b.1 - 1 / 2 ≤ 2 * P.bStar n := hcentered
  sorry

/-- P9.2-gain (09:146–154, 09:286–294): on the filter tests the clipped fractions equal the actual `q_b`;
outside the bad core histories of `GainMeanCert9` the concentration bound (exponent
`n a_*²/((r+3) b_*²) = n^{1-σ-2(h_+-h_-)+o(1)} ≫ n^u`) leaves `∑ q_b ≥ n/2 + .8 n a_*`, and
`log(1/2 + t) = -log 2 + 2t + O(t²)` for `|t| ≤ 2 b_*` with quadratic loss `O(n b_*²) = o(n a_*)` gives (9.1)
with `c₄ = gainConst9`. -/
theorem p92_gain (P : Params9) (hP : P.Valid) (c₀ c₁ : ℝ) (hc₀ : 0 < c₀) (hc₁ : 0 < c₁) :
    ∃ c > (0 : ℝ), ∃ n₀ : ℕ, ∀ n ≥ n₀, ∀ {N : ℕ} {E : Fin N → Fin N → Prop}
      {X Y : Finset (Fin N)} {κ : ℝ} {G : Colour} {M : TagMix N} (S : Setup9 P n N M)
      (I : IDMap9 P n),
      CoreInput9 P κ E X Y G M S I → RegularityCert9 S I E G c₀ → GainMeanCert9 S I E G c₁ →
        GainConc9 S I E G → GainCert9 S I E G c := by
  -- Split each star failure into a filter failure, a low conditional-mean history, or a downward deviation.
  -- On the complementary event `starRegular9` identifies each clipped fraction with `targetFrac9`; the
  -- remaining deterministic log estimate uses the `4 b_*` interval and the scale gap `h_+ - h_- < χ/10`.
  let c := min c₀ c₁ / 2
  have hc : 0 < c := by
    dsimp [c]
    exact div_pos (lt_min hc₀ hc₁) (by norm_num)
  have hu : 0 < P.u := by
    have hxS : 0 < (P.xS : ℝ) := by exact_mod_cast hP.1.1
    dsimp [Params9.u]
    linarith
  obtain ⟨nTail, hTail⟩ := Lane_q_s09_gain2.eventual_tail_sum3
    (u := P.u) (c₁ := c₀) (c₂ := c₁) (c₃ := c₁) hu hc₀ hc₁ hc₁
  obtain ⟨nLog, hLog⟩ := Lane_q_s09_gain2.eventual_gain_log_error9 P hP
  refine ⟨c, hc, max nTail nLog, ?_⟩
  intro n hn N E X Y κ G M S I hin hreg hmean hconc
  have hnTail : nTail ≤ n := le_trans (le_max_left nTail nLog) hn
  have hnLog : nLog ≤ n := le_trans (le_max_right nTail nLog) hn
  have htailN := hTail n hnTail
  have hmargin := hLog n hnLog
  rcases hin with ⟨hN, hprep, hdeep, htags, hmasks, htools, hexps, hscales⟩
  rcases hscales with ⟨hnDim, hm, hr, hwidth, hfilter, hfirstWidth, hbsmall, hgain⟩
  intro v
  have hregAt := hreg v
  have hmeanAt := hmean v
  have hconcAt := hconc v
  let meanBad (ω₀ : Outcome9 I N) : Prop :=
    ∑ b : StarOdd9 v, condCoreMean9 S I E G v b.1 ω₀ <
      (n : ℝ) / 2 + (9 / 10 : ℝ) * n * P.aStar n
  let devBad (ω₀ ω : Outcome9 I N) : Prop :=
    ∑ b : StarOdd9 v, clippedFrac9 S E G ω v b.1 ≤
      ∑ b : StarOdd9 v, condCoreMean9 S I E G v b.1 ω₀ - (n : ℝ) * P.aStar n / 10
  have hsplit (ω : Outcome9 I N) :
      ¬ starValid9 S E G ω v →
        (¬ starRegular9 S E G ω v ∨ meanBad ω ∨ devBad ω ω) := by
    intro hbad
    by_cases hregular : starRegular9 S E G ω v
    · by_cases hmeanBad : meanBad ω
      · exact Or.inr (Or.inl hmeanBad)
      · have hmeanGood :
            (n : ℝ) / 2 + (9 / 10 : ℝ) * n * P.aStar n ≤
              ∑ b : StarOdd9 v, condCoreMean9 S I E G v b.1 ω :=
          le_of_not_gt hmeanBad
        by_cases hdevBad : devBad ω ω
        · exact Or.inr (Or.inr hdevBad)
        · have hdevGood :
              ∑ b : StarOdd9 v, condCoreMean9 S I E G v b.1 ω -
                  (n : ℝ) * P.aStar n / 10 <
                ∑ b : StarOdd9 v, clippedFrac9 S E G ω v b.1 :=
            lt_of_not_ge hdevBad
          have hfrac (b : StarOdd9 v) :
              1 / 2 - 2 * P.bStar n ≤ targetFrac9 S E G ω v b.1 ∧
                targetFrac9 S E G ω v b.1 ≤ 1 / 2 + 2 * P.bStar n := by
            have habs := Lane_q_s09_gain2.starRegular_targetFrac_bounds9
              ω v b.1 hbsmall hregular b.2
            have habs' := abs_le.mp habs
            constructor <;> linarith
          have hclipEq (b : StarOdd9 v) :
              clippedFrac9 S E G ω v b.1 = targetFrac9 S E G ω v b.1 := by
            have hq := hfrac b
            change max (1 / 2 - 2 * P.bStar n)
              (min (1 / 2 + 2 * P.bStar n) (targetFrac9 S E G ω v b.1)) = _
            rw [min_eq_right hq.2, max_eq_right hq.1]
          have hclipSum :
              (∑ b : StarOdd9 v, clippedFrac9 S E G ω v b.1) =
                ∑ b : StarOdd9 v, targetFrac9 S E G ω v b.1 := by
            apply Finset.sum_congr rfl
            intro b hb
            exact hclipEq b
          have ha : 0 ≤ P.aStar n := by
            dsimp [Params9.aStar]
            positivity
          have hclipLower :
              (n : ℝ) / 2 + (8 / 10 : ℝ) * n * P.aStar n ≤
                ∑ b : StarOdd9 v, clippedFrac9 S E G ω v b.1 := by
            nlinarith
          have hsumTarget :
              (n : ℝ) / 2 + (8 / 10 : ℝ) * n * P.aStar n ≤
                ∑ b : StarOdd9 v, targetFrac9 S E G ω v b.1 := by
            rw [← hclipSum]
            exact hclipLower
          have hgain : -(n : ℝ) * Real.log 2 + gainConst9 * n * P.aStar n ≤
              starGain9 S E G ω v :=
            Lane_q_s09_gain2.star_gain_lower_of_mean9 ω v hbsmall hmargin hfrac hsumTarget
          exact False.elim (hbad ⟨hregular, hgain⟩)
    · exact Or.inl hregular
  -- The remaining step converts the fiberwise `hconcAt` bounds into the unconditional deviation tail,
  -- then unions that tail with the regularity and mean-history tails.
  sorry

/-- The gain stage assembled (09:146–294): from the tags, the star validity event fails with raw probability at
most `e^{-c n^u}` at every even star. -/
theorem p92_gain_stage (P : Params9) (hP : P.Valid) (cT : ℝ) (hcT : 0 < cT) :
    ∃ c > (0 : ℝ), ∃ n₀ : ℕ, ∀ n ≥ n₀, ∀ {N : ℕ} {E : Fin N → Fin N → Prop}
      {X Y : Finset (Fin N)} {κ : ℝ} {G : Colour} {M : TagMix N} (S : Setup9 P n N M)
      (I : IDMap9 P n),
      CoreInput9 P κ E X Y G M S I → TagsOK9 κ E G cT S.tag → GainCert9 S I E G c := by
  obtain ⟨c₀, hc₀, n₀, hreg⟩ := p92_regularity P hP
  obtain ⟨C₁, hC₁, c₁, hc₁, n₁, hmean⟩ := p92_conditional_mean P hP c₀ hc₀
  obtain ⟨C₂, hC₂, c₂, hc₂, n₂, herase⟩ := p92_erase_mean P hP c₀ hc₀
  obtain ⟨C₃, hC₃, c₃, hc₃, n₃, hrepl⟩ := p92_erase_replace P hP c₀ C₂ c₂ hc₀ hC₂ hc₂
  obtain ⟨c₄, hc₄, n₄, hcov⟩ := p92_covariance P hP c₀ hc₀
  obtain ⟨c₅, hc₅, n₅, hhits⟩ := p92_core_hits P hP c₀ c₄ hc₀ hc₄
  obtain ⟨c₆, hc₆, n₆, hcomp⟩ := p92_mean_comparison P hP C₁ c₁ C₃ c₃ c₅ hC₁ hc₁ hC₃ hc₃ hc₅
  obtain ⟨c₇, hc₇, n₇, hgm⟩ := p92_gain_means P hP cT c₆ hcT hc₆
  obtain ⟨c₈, hc₈, n₈, hgain⟩ := p92_gain P hP c₀ c₇ hc₀ hc₇
  refine ⟨c₈, hc₈, max (max (max n₀ n₁) (max n₂ n₃)) (max (max n₄ n₅) (max (max n₆ n₇) (max n₈ 1))),
    ?_⟩
  intro n hn N E X Y κ G M S I hin htags
  have h0 : n₀ ≤ n := by omega
  have h1 : n₁ ≤ n := by omega
  have h2 : n₂ ≤ n := by omega
  have h3 : n₃ ≤ n := by omega
  have h4 : n₄ ≤ n := by omega
  have h5 : n₅ ≤ n := by omega
  have h6 : n₆ ≤ n := by omega
  have h7 : n₇ ≤ n := by omega
  have h8 : n₈ ≤ n := by omega
  have h9 : 1 ≤ n := by omega
  have hR := hreg n h0 S I hin
  have hM := hmean n h1 S I hin hR
  have hE := herase n h2 S I hin hR
  have hP' := hrepl n h3 S I hin hR hE
  have hC := hcov n h4 S I hin hR
  have hH := hhits n h5 S I hin hR hC
  have hMC := hcomp n h6 S I hin hM hP' hH
  have hGM := hgm n h7 S I hin htags hMC
  exact hgain n h8 S I hin hR hGM (p92_gain_concentration S I E G h9 hin.1)

end HypercubeRamsey
