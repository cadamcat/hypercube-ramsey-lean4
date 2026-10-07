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
  sorry

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
  sorry

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
