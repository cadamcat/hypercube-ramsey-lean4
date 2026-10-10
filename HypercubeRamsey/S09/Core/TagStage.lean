import HypercubeRamsey.S09.Core.Experiment
import HypercubeRamsey.S09.Core.TagStage_q_s09_tag
import HypercubeRamsey.S07.TagStage
import HypercubeRamsey.Framework.Minimax

/-!
# Proposition 9.2, core: tags and masks (P9.2-tags)

Source: `sections/09-intermediate-powers-of-bias.tex`, lines 120–144.  Tags are drawn independently from the
mixture law, one per special word; in the linear case the tag events `B_z` are avoided with Lemma 3.4
(`S07.cond_product_bound`); the tag loads follow from Lemma 3.6 (`scatteredMoments_union_labels`).  Masks are
chosen row by row by convex separation (`finite_minimax`).
-/

namespace HypercubeRamsey

open OAI.HypercubeRamsey Classical
open scoped BigOperators

set_option maxHeartbeats 100000000 in
/-- P9.2-tags(ii) (09:128–134): the raw probability of a tag event is exponentially small.  For a fixed `z`,
draw `w ∼ μ_{i_z}`: the broad test (`BroadAt`, the tag-average second law has width `log(8/κ) = O(1)`) gives
degree `1/2 ± o(a_*)` into the tag-average second law outside first-law mass `e^{-Ω(n^u)}`, and deep
discrepancy gives individual degrees `1/2 ± 2b_*` outside joint probability `e^{-Ω(n^u)}`; clipping every
summand to `[-2b_*, 2b_*]`, the summands are independent given `w` and Hoeffding bounds a downward deviation of
order `n a_*` by `exp(-Ω(n a_*²/b_*²))`.  Markov with threshold `e^{-c n^u}` gives `Pr(B_z) ≤ e^{-c' n^u}`.  In
the sublinear case `B_z` is empty. -/
theorem p92_tag_bad_prob (P : Params9) (hP : P.Valid) (κ : ℝ) (hκ : 0 < κ) :
    ∃ c > (0 : ℝ), ∃ c' > (0 : ℝ), ∃ n₀ : ℕ, ∀ n ≥ n₀, ∀ {N : ℕ} {E : Fin N → Fin N → Prop}
      {X Y : Finset (Fin N)} {G : Colour} {M : TagMix N},
      0 < N → Prep9 P κ n N E X Y G M → P.DeepAt n N E X Y → P.BroadAt n N E X Y →
      ∀ z : CubeVertex (P.m n),
        (FinProb.pi (fun _ : CubeVertex (P.m n) => tagMixLaw9 M)).pr
          (fun tag => tagBad9 (P := P) E G c tag z) ≤ P.tail c' n := by
  classical
  cases hcase : P.case with
  | sub yS yD yM =>
      refine ⟨1 / 100, by norm_num, 1 / 100, by norm_num, 0, ?_⟩
      intro n hn N E X Y G M hN hprep hdeep hbroad z
      have ht : 0 ≤ P.tail (1 / 100) n := by
        rw [Params9.tail]
        exact Real.exp_nonneg _
      simpa [tagBad9, hcase, FinProb.pr] using ht
  | lin αS αD hB yB =>
      have hlin : 0 < 100 * αS ∧ 100 * αS < αD ∧ αD < 1 / 100 ∧
          P.σ < P.χ / 10 ∧ P.hPlus < hB ∧ hB < 1 ∧ 0 < yB ∧ yB < 1 := by
        simpa [hcase] using hP.2.2.2.2.2.2
      obtain ⟨h100, hgapα, hαsmall, hσχ, hplusB, hB1, hyB, hyB1⟩ := hlin
      obtain ⟨hScaleExps, nScale, hScales⟩ := scales_eventually9 P hP
      let D₀ : ℝ := 8 / κ
      let r : ℝ := 1 - 2 * ((P.hPlus : ℝ) - (P.hMinus : ℝ))
      have hD₀pos : 0 < D₀ := by dsimp [D₀]; positivity
      have hu : 0 < P.u := hScaleExps.2.2.1
      have hxS : 0 < (P.xS : ℝ) := by exact_mod_cast hP.1.1
      have hMinusPos : (0 : ℝ) < (P.hMinus : ℝ) := by exact_mod_cast hP.2.1.1
      have hMinusPlus : (P.hMinus : ℝ) < (P.hPlus : ℝ) := by exact_mod_cast hP.2.1.2.1
      have hPlus : 0 < (P.hPlus : ℝ) := lt_trans hMinusPos hMinusPlus
      have hPlusLt1 : (P.hPlus : ℝ) < 1 := by exact_mod_cast hP.2.1.2.2
      have hBcast : (P.hPlus : ℝ) < (hB : ℝ) := by exact_mod_cast hplusB
      have hyBcast : 0 < (yB : ℝ) := by exact_mod_cast hyB
      have hgapHM : (P.hPlus : ℝ) - (P.hMinus : ℝ) < (P.χ : ℝ) / 10 := by
        exact_mod_cast hP.2.2.2.2.2.1
      have hχSmall : (P.χ : ℝ) < P.u / 50 := hScaleExps.2.2.2.2
      have huSmall : P.u < 1 / 20 := by
        rw [Params9.u]
        have hxsxd : (P.xS : ℝ) < (P.xD : ℝ) := by exact_mod_cast hP.1.2.1
        have hxdQ : P.xD < (1 : ℚ) / 10 := hP.1.2.2
        have hxdCast : (P.xD : ℝ) < ((((1 : ℚ) / 10 : ℚ) : ℝ)) := by exact_mod_cast hxdQ
        have hxd : (P.xD : ℝ) < (1 : ℝ) / 10 := by norm_num at hxdCast ⊢; exact hxdCast
        linarith
      have hrU : P.u < r := by
        dsimp [r]
        nlinarith [hgapHM, hχSmall, huSmall]
      have hWμlim : Filter.Tendsto (fun n : ℕ => (n : ℝ) ^ (P.xS : ℝ)) Filter.atTop Filter.atTop :=
        (tendsto_rpow_atTop hxS).comp tendsto_natCast_atTop_atTop
      have hWμevent := hWμlim.eventually_ge_atTop (Real.log D₀)
      obtain ⟨nWμ, hnWμ⟩ := Filter.eventually_atTop.mp hWμevent
      have hYlim : Filter.Tendsto (fun n : ℕ => (n : ℝ) ^ (yB : ℝ)) Filter.atTop Filter.atTop :=
        (tendsto_rpow_atTop hyBcast).comp tendsto_natCast_atTop_atTop
      have hYevent := hYlim.eventually_ge_atTop (Real.log D₀)
      obtain ⟨nY, hnY⟩ := Filter.eventually_atTop.mp hYevent
      have hErrLim := Lane_q_s09_tag.rpow_ratio_tendsto (-(hB : ℝ))
        (-(P.hPlus : ℝ)) (by linarith)
      have hErrevent : ∀ᶠ n : ℕ in Filter.atTop,
          (n : ℝ) ^ (-(hB : ℝ)) / (n : ℝ) ^ (-(P.hPlus : ℝ)) < 1 / 200 :=
        hErrLim.eventually (Iio_mem_nhds (by norm_num))
      obtain ⟨nErr, hnErr⟩ := Filter.eventually_atTop.mp hErrevent
      have hExpSquare := Lane_q_s09_tag.expTail_square_tendsto P hP (1 / 4) (by norm_num)
      have hClipEvent : ∀ᶠ n : ℕ in Filter.atTop,
          (n : ℝ) ^ 2 * P.tail (1 / 4) n < 1 / 200 :=
        hExpSquare.eventually (Iio_mem_nhds (by norm_num))
      obtain ⟨nClip, hnClip⟩ := Filter.eventually_atTop.mp hClipEvent
      have hLogLim : Filter.Tendsto (fun n : ℕ => Real.log (n : ℝ) / (n : ℝ) ^ P.u)
          Filter.atTop (nhds 0) :=
        ((isLittleO_log_rpow_atTop hu).tendsto_div_nhds_zero).comp
          tendsto_natCast_atTop_atTop
      have hLogEvent : ∀ᶠ n : ℕ in Filter.atTop,
          Real.log (n : ℝ) / (n : ℝ) ^ P.u < 1 / 8 :=
        hLogLim.eventually (Iio_mem_nhds (by norm_num))
      obtain ⟨nLog, hnLog⟩ := Filter.eventually_atTop.mp hLogEvent
      have hConcLim := Lane_q_s09_tag.rpow_ratio_tendsto P.u r hrU
      have hConcEvent : ∀ᶠ n : ℕ in Filter.atTop,
          (n : ℝ) ^ P.u / (n : ℝ) ^ r < 1 / 400000 :=
        hConcLim.eventually (Iio_mem_nhds (by norm_num))
      obtain ⟨nConc, hnConc⟩ := Filter.eventually_atTop.mp hConcEvent
      have hUlim : Filter.Tendsto (fun n : ℕ => (n : ℝ) ^ P.u) Filter.atTop Filter.atTop :=
        (tendsto_rpow_atTop hu).comp tendsto_natCast_atTop_atTop
      obtain ⟨nBig, hnBig⟩ := Filter.eventually_atTop.mp
        (hUlim.eventually_ge_atTop (100 : ℝ))
      let n₀ := max nScale (max nWμ (max nY (max nErr (max nClip (max nLog (max nConc nBig))))))
      refine ⟨1 / 100, by norm_num, 1 / 100, by norm_num, n₀, ?_⟩
      intro n hn N E X Y G M hN hprep hdeep hbroad z
      have hnBounds :
          nScale ≤ n ∧ nWμ ≤ n ∧ nY ≤ n ∧ nErr ≤ n ∧ nClip ≤ n ∧ nLog ≤ n ∧
            nConc ≤ n ∧ nBig ≤ n := by
        simp only [n₀, Nat.max_le] at hn
        rcases hn with ⟨hnScale, hnWμ, hnY, hnErr, hnClip, hnLog, hnConc, hnBig⟩
        exact ⟨hnScale, hnWμ, hnY, hnErr, hnClip, hnLog, hnConc, hnBig⟩
      rcases hnBounds with ⟨hnScaleN, hnWμN, hnYN, hnErrN, hnClipN, hnLogN, hnConcN, hnBigN⟩
      have hscale := hScales n hnScaleN
      have hnRpos : 0 < (n : ℝ) := by exact_mod_cast (lt_of_lt_of_le (by decide : 0 < 1) hscale.1)
      have hnRone : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hscale.1
      have hlognNonneg : 0 ≤ Real.log (n : ℝ) := Real.log_nonneg hnRone
      let Wμn : ℝ := (n : ℝ) ^ (P.xS : ℝ) + (P.hPlus : ℝ) * Real.log (n : ℝ) + 1
      have hWμ : Real.log D₀ ≤ Wμn := by
        have hp := hnWμ n hnWμN
        dsimp [Wμn]
        nlinarith [hlognNonneg, hPlus]
      have hYwidth : Real.log D₀ ≤ (n : ℝ) ^ (yB : ℝ) := hnY n hnYN
      have hrpos : 0 < r := by dsimp [r]; linarith [hPlusLt1]
      have hErrRat := hnErr n hnErrN
      have hErrDen : 0 < (n : ℝ) ^ (-(P.hPlus : ℝ)) := Real.rpow_pos_of_pos hnRpos _
      have hErrNum : (n : ℝ) ^ (-(hB : ℝ)) <
          (1 / 200 : ℝ) * (n : ℝ) ^ (-(P.hPlus : ℝ)) :=
        (div_lt_iff₀ hErrDen).mp hErrRat
      have hErrSmall : (n : ℝ) ^ (-(hB : ℝ)) < P.aStar n / 100 := by
        calc
          (n : ℝ) ^ (-(hB : ℝ)) < (1 / 200 : ℝ) * (n : ℝ) ^ (-(P.hPlus : ℝ)) := hErrNum
          _ = P.aStar n / 100 := by dsimp [Params9.aStar]; ring
      have hClipEvent := hnClip n hnClipN
      have hplusLe2 : (P.hPlus : ℝ) ≤ 2 := by linarith [hPlusLt1]
      have hpowPlusR : (n : ℝ) ^ (P.hPlus : ℝ) ≤ (n : ℝ) ^ (2 : ℝ) :=
        Real.rpow_le_rpow_of_exponent_le hnRone hplusLe2
      have hpowPlus : (n : ℝ) ^ (P.hPlus : ℝ) ≤ (n : ℝ) ^ 2 := by
        calc
          (n : ℝ) ^ (P.hPlus : ℝ) ≤ (n : ℝ) ^ (2 : ℝ) := hpowPlusR
          _ = (n : ℝ) ^ 2 := Real.rpow_natCast (n : ℝ) 2
      have htailNonneg : 0 ≤ P.tail (1 / 4) n := by
        rw [Params9.tail]
        exact Real.exp_nonneg _
      have hclipProd : (n : ℝ) ^ (P.hPlus : ℝ) * P.tail (1 / 4) n < 1 / 200 := by
        calc
          (n : ℝ) ^ (P.hPlus : ℝ) * P.tail (1 / 4) n ≤
              (n : ℝ) ^ 2 * P.tail (1 / 4) n :=
            mul_le_mul_of_nonneg_right hpowPlus htailNonneg
          _ < 1 / 200 := hClipEvent
      have hclipByAst : P.tail (1 / 4) n ≤ P.aStar n / 100 := by
        have hpowPos : 0 < (n : ℝ) ^ (P.hPlus : ℝ) := Real.rpow_pos_of_pos hnRpos _
        have hclipProd' : P.tail (1 / 4) n * (n : ℝ) ^ (P.hPlus : ℝ) < 1 / 200 := by
          calc
            P.tail (1 / 4) n * (n : ℝ) ^ (P.hPlus : ℝ) =
                (n : ℝ) ^ (P.hPlus : ℝ) * P.tail (1 / 4) n := by ring
            _ < 1 / 200 := hclipProd
        have hdiv : P.tail (1 / 4) n < (1 / 200 : ℝ) /
            (n : ℝ) ^ (P.hPlus : ℝ) :=
          (lt_div_iff₀ hpowPos).2 hclipProd'
        have hneg : (n : ℝ) ^ (-(P.hPlus : ℝ)) =
            ((n : ℝ) ^ (P.hPlus : ℝ))⁻¹ := by rw [Real.rpow_neg hnRpos.le]
        have hclipStrict : P.tail (1 / 4) n < P.aStar n / 100 := calc
          P.tail (1 / 4) n < (1 / 200 : ℝ) /
              (n : ℝ) ^ (P.hPlus : ℝ) := hdiv
          _ = P.aStar n / 100 := by rw [Params9.aStar, hneg]; ring
        exact hclipStrict.le
      have hLogRatio := hnLog n hnLogN
      have hLogN : Real.log (n : ℝ) < (n : ℝ) ^ P.u / 8 := by
        have h := (div_lt_iff₀ (Real.rpow_pos_of_pos hnRpos P.u)).mp hLogRatio
        nlinarith
      have hConcRatio := hnConc n hnConcN
      have hUbig := hnBig n hnBigN
      let tagLaw : FinProb M.ι := tagMixLaw9 M
      let μbar : Law N := Law.mix tagLaw M.μ
      let νbar : Law N := Law.mix tagLaw M.ν
      have hNreal : 0 < (N : ℝ) := by exact_mod_cast hN
      have hμbarSupp : μbar.SupportedIn X := by
        intro w hw
        change (∑ i, M.Λ i * (M.μ i).w w) = 0
        apply Finset.sum_eq_zero
        intro i hi
        by_cases hweight0 : M.Λ i = 0
        · simp [hweight0]
        · have hweightpos : 0 < M.Λ i := lt_of_le_of_ne (M.Λ_nonneg i) (Ne.symm hweight0)
          have hzero := (hprep.2 i hweightpos).1 w hw
          simp [hzero]
      have hνbarSupp : νbar.SupportedIn Y := by
        intro w hw
        change (∑ i, M.Λ i * (M.ν i).w w) = 0
        apply Finset.sum_eq_zero
        intro i hi
        by_cases hweight0 : M.Λ i = 0
        · simp [hweight0]
        · have hweightpos : 0 < M.Λ i := lt_of_le_of_ne (M.Λ_nonneg i) (Ne.symm hweight0)
          have hzero := (hprep.2 i hweightpos).2.1 w hw
          simp [hzero]
      have hμbarWidth : μbar.WidthLE (Real.log D₀) := by
        intro y
        change (∑ i, M.Λ i * (M.μ i).w y) ≤ Real.exp (Real.log D₀) / N
        rw [Real.exp_log hD₀pos]
        exact (le_div_iff₀ hNreal).2 (by simpa [D₀, mul_comm] using hprep.1.1 y)
      have hνbarWidth : νbar.WidthLE (Real.log D₀) := by
        intro y
        change (∑ i, M.Λ i * (M.ν i).w y) ≤ Real.exp (Real.log D₀) / N
        rw [Real.exp_log hD₀pos]
        exact (le_div_iff₀ hNreal).2 (by simpa [D₀, mul_comm] using hprep.1.2 y)
      have hνbarBroadWidth : νbar.WidthLE ((n : ℝ) ^ (yB : ℝ)) := by
        intro y
        exact le_trans (hνbarWidth y)
          (div_le_div_of_nonneg_right (Real.exp_le_exp.mpr hYwidth) (Nat.cast_nonneg N))
      have hdeepBudget :
          (n : ℝ) ^ (P.xS : ℝ) + (P.hPlus : ℝ) * Real.log (n : ℝ) + 1 +
            (n : ℝ) ^ (P.u + 8 * (P.χ : ℝ)) ≤ (n : ℝ) ^ (P.xD : ℝ) :=
        hscale.2.2.2.2.2.1
      have hχpos : 0 < (P.χ : ℝ) := by exact_mod_cast hP.2.2.2.2.1.1
      have hpowMargin : (n : ℝ) ^ P.u / 4 ≤
          (n : ℝ) ^ (P.u + 8 * (P.χ : ℝ)) := by
        have hpow := Real.rpow_le_rpow_of_exponent_le hnRone
          (by linarith [hχpos] : P.u ≤ P.u + 8 * (P.χ : ℝ))
        nlinarith [hpow, Real.rpow_nonneg (Nat.cast_nonneg n) P.u]
      have hlowBudget : Real.log D₀ + (n : ℝ) ^ P.u / 4 ≤ (n : ℝ) ^ (P.xD : ℝ) := by
        have hsum := add_le_add hWμ hpowMargin
        dsimp [Wμn] at hsum
        exact hsum.trans hdeepBudget
      have hbroad : DiscOne E X Y ((n : ℝ) ^ (P.xD : ℝ)) ((n : ℝ) ^ (yB : ℝ))
          ((n : ℝ) ^ (-(hB : ℝ))) := by
        simpa [Params9.BroadAt, hcase] using hbroad
      have hδpos : 0 < P.aStar n / 100 := by
        unfold Params9.aStar
        positivity
      have hLowMass := Lane_q_s09_tag.broad_low_degree_mass_q_s09_tag (G := G)
        ((n : ℝ) ^ (P.xD : ℝ)) ((n : ℝ) ^ (yB : ℝ)) ((n : ℝ) ^ (-(hB : ℝ)))
        (Real.log D₀) (P.aStar n / 100) ((n : ℝ) ^ P.u / 4)
        hbroad hμbarSupp hνbarSupp hμbarWidth hνbarBroadWidth hlowBudget hErrSmall hδpos
      have hαLe : (αS : ℝ) ≤ (αD : ℝ) := by
        have hα : (100 : ℝ) * (αS : ℝ) < (αD : ℝ) := by exact_mod_cast hgapα
        have h100R : (0 : ℝ) < 100 * (αS : ℝ) := by exact_mod_cast h100
        have hαSsmall : (αS : ℝ) < 100 * (αS : ℝ) := by linarith [h100R]
        exact le_of_lt (lt_trans hαSsmall hα)
      have hSsLeSd : P.Ss (n : ℝ) ≤ P.Sd (n : ℝ) := by
        simp [Params9.Ss, Params9.Sd, hcase]
        exact mul_le_mul_of_nonneg_right hαLe (Nat.cast_nonneg n)
      have hbarDeepWidth : (Real.log D₀) ≤ (n : ℝ) ^ (P.xD : ℝ) := by
        have hpos : 0 ≤ (n : ℝ) ^ P.u / 4 := by positivity
        exact le_trans (le_add_of_nonneg_right hpos) hlowBudget
      let qBad : Fin N → ℝ := fun w =>
        tagLaw.pr (fun i => 2 * P.bStar n < |rowDeg E G w (M.ν i) - 1 / 2|)
      let epsDeep : ℝ := 2 * Real.exp (Real.log D₀ - (n : ℝ) ^ (P.xD : ℝ))
      have hqNonneg (w : Fin N) : 0 ≤ qBad w := by
        dsimp [qBad]
        unfold FinProb.pr
        apply Finset.sum_nonneg
        intro i hi
        split_ifs
        · exact tagLaw.nonneg i
        · exact le_rfl
      have hdeepPair (i : M.ι) (hi : 0 < M.Λ i) :
          (∑ w ∈ Finset.univ.filter
            (fun w => 2 * P.bStar n < |rowDeg E G w (M.ν i) - 1 / 2|), μbar.w w) ≤ epsDeep := by
        rcases hprep.2 i hi with ⟨hμsupp, hνsupp, _, hνwidth, _⟩
        have hνwidth' : (M.ν i).WidthLE (P.Sd (n : ℝ)) :=
          Law.WidthLE.mono hνwidth hSsLeSd
        have hDeep := deep_forward9 hdeep G (M.ν i) hνsupp hνwidth' μbar
          hμbarSupp (Real.log D₀) hμbarWidth hbarDeepWidth
        simpa [epsDeep, FinProb.pr, Finset.sum_filter] using hDeep
      have hqMean : μbar.expect qBad ≤ epsDeep := by
        dsimp [qBad]
        unfold FinProb.expect
        change (∑ w, μbar.w w *
          ∑ i, if 2 * P.bStar n < |rowDeg E G w (M.ν i) - 1 / 2| then tagLaw.w i else 0) ≤ epsDeep
        calc
          (∑ w, μbar.w w *
              ∑ i, if 2 * P.bStar n < |rowDeg E G w (M.ν i) - 1 / 2| then tagLaw.w i else 0) =
              ∑ i, tagLaw.w i *
                ∑ w, if 2 * P.bStar n < |rowDeg E G w (M.ν i) - 1 / 2| then μbar.w w else 0 := by
            calc
              _ = ∑ w, ∑ i, μbar.w w *
                  (if 2 * P.bStar n < |rowDeg E G w (M.ν i) - 1 / 2| then tagLaw.w i else 0) := by
                apply Finset.sum_congr rfl
                intro w hw
                rw [Finset.mul_sum]
              _ = ∑ i, ∑ w, μbar.w w *
                  (if 2 * P.bStar n < |rowDeg E G w (M.ν i) - 1 / 2| then tagLaw.w i else 0) :=
                Finset.sum_comm
              _ = ∑ i, tagLaw.w i *
                  ∑ w, if 2 * P.bStar n < |rowDeg E G w (M.ν i) - 1 / 2| then μbar.w w else 0 := by
                apply Finset.sum_congr rfl
                intro i hi
                rw [Finset.mul_sum]
                apply Finset.sum_congr rfl
                intro w hw
                by_cases hb : 2 * P.bStar n < |rowDeg E G w (M.ν i) - 1 / 2| <;> simp [hb] <;> ring
          _ ≤ ∑ i, tagLaw.w i * epsDeep := by
            apply Finset.sum_le_sum
            intro i hi
            by_cases hzero : tagLaw.w i = 0
            · simp [hzero]
            · have hiPos : 0 < M.Λ i := by
                have hnotzero : M.Λ i ≠ 0 := by simpa [tagMixLaw9, tagLaw] using hzero
                exact lt_of_le_of_ne (M.Λ_nonneg i) (Ne.symm hnotzero)
              have h := hdeepPair i hiPos
              have hprob : μbar.pr
                  (fun w => 2 * P.bStar n < |rowDeg E G w (M.ν i) - 1 / 2|) ≤ epsDeep := by
                simpa [FinProb.pr, Finset.sum_filter] using h
              have hmul := mul_le_mul_of_nonneg_left hprob (tagLaw.nonneg i)
              simpa [FinProb.pr, tagMixLaw9, tagLaw, Finset.mul_sum] using hmul
          _ = epsDeep := by
            rw [← Finset.sum_mul, tagLaw.sum_eq_one]
            ring
      let p₀ : ℝ := Real.exp (-(n : ℝ) ^ P.u / 4)
      have hp₀ : 0 < p₀ := by dsimp [p₀]; positivity
      have hscaleDeepMargin :
          (n : ℝ) ^ (P.xS : ℝ) + (P.hPlus : ℝ) * Real.log (n : ℝ) + 1 +
            (n : ℝ) ^ (P.u + 8 * (P.χ : ℝ)) ≤ (n : ℝ) ^ (P.xD : ℝ) :=
        hscale.2.2.2.2.2.1
      have hpowDeep : (n : ℝ) ^ P.u ≤
          (n : ℝ) ^ (P.u + 8 * (P.χ : ℝ)) := by
        exact Real.rpow_le_rpow_of_exponent_le hnRone
          (by linarith [hχpos] : P.u ≤ P.u + 8 * (P.χ : ℝ))
      have hlogD0Deep : Real.log D₀ + (n : ℝ) ^ P.u ≤ (n : ℝ) ^ (P.xD : ℝ) := by
        have hsum := add_le_add hWμ hpowDeep
        dsimp [Wμn] at hsum
        linarith [hscaleDeepMargin]
      have hdeepExp : epsDeep ≤ 2 * Real.exp (-(n : ℝ) ^ P.u) := by
        change 2 * Real.exp (Real.log D₀ - (n : ℝ) ^ (P.xD : ℝ)) ≤
          2 * Real.exp (-(n : ℝ) ^ P.u)
        exact mul_le_mul_of_nonneg_left
          (Real.exp_le_exp.mpr (by linarith [hlogD0Deep])) (by norm_num : 0 ≤ (2 : ℝ))
      have hlog2 : Real.log 2 ≤ 1 := by
        have := Real.log_two_lt_d9
        linarith
      have hgapExp : 2 * Real.exp (-3 * ((n : ℝ) ^ P.u) / 4) ≤
          Real.exp (-((n : ℝ) ^ P.u) / 2) := by
        have hquarter : 1 ≤ (n : ℝ) ^ P.u / 4 := by
          have hq := div_le_div_of_nonneg_right hUbig (by norm_num : 0 ≤ (1 : ℝ) / 4)
          norm_num at hq
          linarith
        have hlogQuarter : Real.log 2 ≤ (n : ℝ) ^ P.u / 4 := le_trans hlog2 hquarter
        have hlog : Real.log 2 - 3 * ((n : ℝ) ^ P.u) / 4 ≤
            -((n : ℝ) ^ P.u) / 2 := by
          calc
            Real.log 2 - 3 * ((n : ℝ) ^ P.u) / 4 ≤
                ((n : ℝ) ^ P.u) / 4 - 3 * ((n : ℝ) ^ P.u) / 4 :=
              sub_le_sub_right hlogQuarter _
            _ = -((n : ℝ) ^ P.u) / 2 := by ring
        have htwo : 2 * Real.exp (-3 * ((n : ℝ) ^ P.u) / 4) =
            Real.exp (Real.log 2 - 3 * ((n : ℝ) ^ P.u) / 4) := by
          calc
            2 * Real.exp (-3 * ((n : ℝ) ^ P.u) / 4) =
                Real.exp (Real.log 2) * Real.exp (-3 * ((n : ℝ) ^ P.u) / 4) := by
              rw [Real.exp_log (by norm_num : (0 : ℝ) < 2)]
            _ = Real.exp (Real.log 2 + (-3 * ((n : ℝ) ^ P.u) / 4)) :=
              (Real.exp_add _ _).symm
            _ = Real.exp (Real.log 2 - 3 * ((n : ℝ) ^ P.u) / 4) := by congr 1 <;> ring
        calc
          2 * Real.exp (-3 * ((n : ℝ) ^ P.u) / 4) =
              Real.exp (Real.log 2 - 3 * ((n : ℝ) ^ P.u) / 4) := htwo
          _ ≤ Real.exp (-((n : ℝ) ^ P.u) / 2) := Real.exp_le_exp.mpr hlog
      have hhighMass : μbar.pr (fun w => p₀ ≤ qBad w) ≤ Real.exp (-((n : ℝ) ^ P.u) / 2) := by
        have hmarkov := FinProb.markov μbar qBad p₀ hqNonneg hp₀
        have hratio : epsDeep / p₀ ≤ Real.exp (-((n : ℝ) ^ P.u) / 2) := by
          calc
            epsDeep / p₀ ≤
                (2 * Real.exp (-(n : ℝ) ^ P.u)) / p₀ :=
              div_le_div_of_nonneg_right hdeepExp (le_of_lt hp₀)
            _ = 2 * Real.exp (-3 * ((n : ℝ) ^ P.u) / 4) := by
              dsimp [p₀]
              calc
                (2 * Real.exp (-(n : ℝ) ^ P.u)) / Real.exp (-((n : ℝ) ^ P.u) / 4) =
                    2 * (Real.exp (-(n : ℝ) ^ P.u) /
                      Real.exp (-((n : ℝ) ^ P.u) / 4)) := by ring
                _ = 2 * Real.exp (-(n : ℝ) ^ P.u - (-(n : ℝ) ^ P.u / 4)) := by
                  rw [← Real.exp_sub]
                _ = 2 * Real.exp (-3 * ((n : ℝ) ^ P.u) / 4) := by congr 1 <;> ring
            _ ≤ Real.exp (-((n : ℝ) ^ P.u) / 2) := hgapExp
        have hmeanRatio : μbar.expect qBad / p₀ ≤ epsDeep / p₀ :=
          div_le_div_of_nonneg_right hqMean (le_of_lt hp₀)
        calc
          μbar.pr (fun w => p₀ ≤ qBad w) ≤ μbar.expect qBad / p₀ := hmarkov
          _ ≤ epsDeep / p₀ := hmeanRatio
          _ ≤ Real.exp (-((n : ℝ) ^ P.u) / 2) := hratio
      have hmle : P.m n ≤ n := hscale.2.1
      have h100R : 0 < (100 : ℝ) * (αS : ℝ) := by exact_mod_cast h100
      have hαSpos : 0 < (αS : ℝ) := by linarith only [h100R]
      have hSsPos : 0 < P.Ss (n : ℝ) := by
        unfold Params9.Ss
        rw [hcase]
        exact mul_pos hαSpos hnRpos
      have hmlogPos : 0 < (P.m n : ℝ) * Real.log 2 := by
        have hleft : 0 < P.Ss (n : ℝ) + Real.log (n : ℝ) :=
          add_pos_of_pos_of_nonneg hSsPos hlognNonneg
        exact lt_trans hleft hscale.2.2.2.1
      have hmposR : 0 < (P.m n : ℝ) := by
        by_contra hmnot
        have hmle : (P.m n : ℝ) ≤ 0 := le_of_not_gt hmnot
        have hmzero : (P.m n : ℝ) = 0 := le_antisymm hmle (Nat.cast_nonneg _)
        rw [hmzero] at hmlogPos
        norm_num at hmlogPos
      have hmpos : 0 < P.m n := by exact_mod_cast hmposR
      have hbStarPos : 0 < P.bStar n := by
        unfold Params9.bStar
        exact Real.rpow_pos_of_pos hnRpos _
      have haStarPos : 0 < P.aStar n := by
        unfold Params9.aStar
        positivity
      have hbStarScale : P.bStar n ≤ 1 / 200 := hscale.2.2.2.2.2.2.1
      have hclipB : 2 * P.bStar n ≤ 1 / 100 := by linarith [hbStarScale]
      have hp₀eq : p₀ = P.tail (1 / 4) n := by
        simp [p₀, Params9.tail]
        congr 1
        ring
      let lowLabel : Fin N → Prop := fun w =>
        rowDeg E G w νbar ≤ 1 / 2 - P.aStar n / 100
      let highLabel : Fin N → Prop := fun w => p₀ ≤ qBad w
      let exceptionalLabel : Fin N → Prop := fun w => lowLabel w ∨ highLabel w
      let neighborP : Fin (P.m n) → FinProb M.ι := fun _ => tagLaw
      let neighborLaw : FinProb (Fin (P.m n) → M.ι) := FinProb.pi neighborP
      let failProb : Fin N → ℝ := fun w => neighborLaw.pr (fun tags =>
        ∑ j : Fin (P.m n), (rowDeg E G w (M.ν (tags j)) - 1 / 2) <
          -((1 / 20 : ℝ) * P.aStar n * (n : ℝ)))
      have htailGood (w : Fin N) (hnotLow : ¬ lowLabel w)
          (hnotHigh : ¬ highLabel w) :
          failProb w ≤ (n : ℝ) * p₀ + Real.exp (-((n : ℝ) ^ P.u)) := by
        let f : Fin (P.m n) → M.ι → ℝ := fun _ i =>
          rowDeg E G w (M.ν i) - 1 / 2
        have hraw (j : Fin (P.m n)) (i : M.ι) :
            -(1 / 2 : ℝ) ≤ f j i ∧ f j i ≤ 1 / 2 := by
          rcases Lane_q_s09_tag.rowDeg_bounds_q_s09_tag E G w (M.ν i) with ⟨h0, h1⟩
          dsimp [f]
          constructor <;> linarith
        have hmean (j : Fin (P.m n)) :
            -(P.aStar n / 100) ≤ (neighborP j).expect (f j) := by
          change -(P.aStar n / 100) ≤
            (tagMixLaw9 M).expect (fun i => rowDeg E G w (M.ν i) - 1 / 2)
          rw [Lane_q_s09_tag.rowDeg_center_tagMix_q_s09_tag M E G w]
          have hgt : 1 / 2 - P.aStar n / 100 < rowDeg E G w νbar :=
            lt_of_not_ge hnotLow
          linarith
        have hbad (j : Fin (P.m n)) :
            (neighborP j).pr (fun i => 2 * P.bStar n < |f j i|) ≤ p₀ := by
          have hq : qBad w < p₀ := lt_of_not_ge hnotHigh
          change tagLaw.pr
            (fun i => 2 * P.bStar n < |rowDeg E G w (M.ν i) - 1 / 2|) ≤ p₀
          exact le_of_lt (by simpa [qBad, tagLaw] using hq)
        have hcard : (Fintype.card (Fin (P.m n)) : ℝ) ≤ (n : ℝ) := by
          have hmleR : (P.m n : ℝ) ≤ (n : ℝ) := by exact_mod_cast hmle
          simpa using hmleR
        have hcardpos : 0 < (Fintype.card (Fin (P.m n)) : ℝ) := by
          simpa using hmposR
        have hsmall : p₀ ≤ P.aStar n / 100 := by
          rw [hp₀eq]
          exact hclipByAst
        have hscaleSq₀ := Lane_q_s09_tag.aStar_sq_n_div_bStar_sq_q_s09_tag P hnRpos
        have hrExp :
            1 - 2 * (P.hPlus : ℝ) + 2 * (P.hMinus : ℝ) = r := by
          dsimp [r]
          ring
        rw [hrExp] at hscaleSq₀
        have hbound := Lane_q_s09_tag.clipped_lower_tail_q_s09_tag
          neighborP f (P.aStar n) (P.bStar n) (n : ℝ) P.u r p₀
          haStarPos hbStarPos hnRpos hcard hcardpos hclipB hraw hmean hbad
          (le_of_lt hp₀) hsmall hConcRatio hUbig hscaleSq₀
        have hbound' : neighborLaw.pr (fun tags =>
            ∑ j : Fin (P.m n), f j (tags j) < -(P.aStar n / 20) * (n : ℝ)) ≤
            (n : ℝ) * p₀ + Real.exp (-((n : ℝ) ^ P.u)) := by
          simpa [neighborLaw] using hbound
        have hle : failProb w ≤ neighborLaw.pr (fun tags =>
            ∑ j : Fin (P.m n), f j (tags j) < -(P.aStar n / 20) * (n : ℝ)) := by
          apply FinProb.pr_mono
          intro tags htag
          change (∑ j : Fin (P.m n),
              (rowDeg E G w (M.ν (tags j)) - 1 / 2)) <
            -((1 / 20 : ℝ) * P.aStar n * (n : ℝ)) at htag
          change (∑ j : Fin (P.m n), f j (tags j)) <
            -(P.aStar n / 20) * (n : ℝ)
          have heq : -((1 / 20 : ℝ) * P.aStar n * (n : ℝ)) =
              -(P.aStar n / 20) * (n : ℝ) := by ring
          rw [heq] at htag
          exact htag
        exact hle.trans hbound'
      let mass (tag : CubeVertex (P.m n) → M.ι) : ℝ :=
        ∑ w, (M.μ (tag z)).w w *
          (if tagSurplus9 (P := P) E G tag z w <
              -((1 / 20 : ℝ) * P.aStar n * (n : ℝ)) then 1 else 0)
      let raw : FinProb (CubeVertex (P.m n) → M.ι) :=
        FinProb.pi (fun _ : CubeVertex (P.m n) => tagLaw)
      have hmassNonneg (tag : CubeVertex (P.m n) → M.ι) : 0 ≤ mass tag := by
        dsimp [mass]
        apply Finset.sum_nonneg
        intro w hw
        by_cases hfail : tagSurplus9 (P := P) E G tag z w <
            -((1 / 20 : ℝ) * P.aStar n * (n : ℝ))
        · rw [if_pos hfail]
          exact mul_nonneg ((M.μ (tag z)).nonneg w) (by norm_num)
        · rw [if_neg hfail]
          simp
      have hmassFilter (tag : CubeVertex (P.m n) → M.ι) :
          (∑ w ∈ tagFail9 (P := P) E G tag z, (M.μ (tag z)).w w) = mass tag := by
        simp [mass, tagFail9, tagSurplus9, Finset.sum_filter]
      let threshold : ℝ := (1 / 20 : ℝ) * P.aStar n * (n : ℝ)
      have hmassFactor := Lane_q_s09_tag.tag_failure_mass_expect_eq_q_s09_tag
        (P := P) (n := n) (N := N) (M := M) E G z threshold
      have hmassFactor' : raw.expect mass = μbar.expect failProb := by
        simpa [raw, mass, failProb, neighborLaw, neighborP, threshold, tagLaw, μbar,
          FinProb.expect]
          using hmassFactor
      have hfailMass : μbar.expect failProb ≤ Real.exp (-((n : ℝ) ^ P.u) / 10) := by
        have hCnonneg : 0 ≤ (n : ℝ) * p₀ + Real.exp (-((n : ℝ) ^ P.u)) := by positivity
        have hpoint (w : Fin N) : failProb w ≤
            (if exceptionalLabel w then 1 else 0) +
              ((n : ℝ) * p₀ + Real.exp (-((n : ℝ) ^ P.u))) := by
          by_cases hex : exceptionalLabel w
          · have hone := Lane_q_s09_tag.pr_le_one_q_s09_tag neighborLaw
              (fun tags => ∑ j : Fin (P.m n),
                (rowDeg E G w (M.ν (tags j)) - 1 / 2) <
                  -((1 / 20 : ℝ) * P.aStar n * (n : ℝ)))
            have hpr : failProb w ≤ 1 := by simpa [failProb] using hone
            simp [hex]
            linarith [hpr, hCnonneg]
          · have hlo : ¬ lowLabel w := fun h => hex (Or.inl h)
            have hhi : ¬ highLabel w := fun h => hex (Or.inr h)
            simpa [hex] using htailGood w hlo hhi
        have hEbad : μbar.expect (fun w => if exceptionalLabel w then 1 else 0) =
            μbar.pr exceptionalLabel := by
          unfold FinProb.expect FinProb.pr
          apply Finset.sum_congr rfl
          intro w hw
          by_cases h : exceptionalLabel w <;> simp [h]
        have hEbad' : (∑ w, μbar.w w * (if exceptionalLabel w then 1 else 0)) =
            μbar.pr exceptionalLabel := by
          change μbar.expect (fun w => if exceptionalLabel w then 1 else 0) = _
          exact hEbad
        have hEupper : μbar.expect (fun w =>
            (if exceptionalLabel w then 1 else 0) +
              ((n : ℝ) * p₀ + Real.exp (-((n : ℝ) ^ P.u))) ) =
              μbar.pr exceptionalLabel +
                ((n : ℝ) * p₀ + Real.exp (-((n : ℝ) ^ P.u))) := by
          have hconst : (∑ w, μbar.w w *
              ((n : ℝ) * p₀ + Real.exp (-((n : ℝ) ^ P.u)))) =
              (n : ℝ) * p₀ + Real.exp (-((n : ℝ) ^ P.u)) := by
            calc
              _ = (∑ w, μbar.w w) *
                  ((n : ℝ) * p₀ + Real.exp (-((n : ℝ) ^ P.u))) := by
                rw [← Finset.sum_mul]
              _ = _ := by rw [μbar.sum_eq_one]; ring
          unfold FinProb.expect
          calc
            (∑ w, μbar.w w *
                ((if exceptionalLabel w then 1 else 0) +
                  ((n : ℝ) * p₀ + Real.exp (-((n : ℝ) ^ P.u))))) =
                (∑ w, μbar.w w * (if exceptionalLabel w then 1 else 0)) +
                  ∑ w, μbar.w w *
                    ((n : ℝ) * p₀ + Real.exp (-((n : ℝ) ^ P.u))) := by
              calc
                _ = ∑ w, (μbar.w w * (if exceptionalLabel w then 1 else 0) +
                    μbar.w w * ((n : ℝ) * p₀ + Real.exp (-((n : ℝ) ^ P.u)))) := by
                  apply Finset.sum_congr rfl
                  intro w hw
                  ring
                _ = _ := Finset.sum_add_distrib
            _ = _ := by rw [hEbad', hconst]
        have hException : μbar.pr exceptionalLabel ≤
            Real.exp (-((n : ℝ) ^ P.u) / 4) +
              Real.exp (-((n : ℝ) ^ P.u) / 2) := by
          calc
            μbar.pr exceptionalLabel ≤ μbar.pr lowLabel + μbar.pr highLabel :=
              FinProb.pr_union_le μbar lowLabel highLabel
            _ ≤ Real.exp (-((n : ℝ) ^ P.u) / 4) +
                Real.exp (-((n : ℝ) ^ P.u) / 2) := by
              apply add_le_add
              · convert hLowMass using 1 <;> congr 1 <;> ring
              · simpa [highLabel] using hhighMass
        have hlogNexp :
            (n : ℝ) * p₀ ≤ Real.exp (-((n : ℝ) ^ P.u) / 8) := by
          calc
            (n : ℝ) * p₀ = Real.exp (Real.log (n : ℝ)) *
                Real.exp (-((n : ℝ) ^ P.u) / 4) := by
              rw [Real.exp_log hnRpos]
            _ = Real.exp (Real.log (n : ℝ) - ((n : ℝ) ^ P.u) / 4) := by
              rw [← Real.exp_add]
              congr 1
              ring
            _ ≤ Real.exp (-((n : ℝ) ^ P.u) / 8) :=
              Real.exp_le_exp.mpr (by linarith [hLogN])
        have hnuNonneg : 0 ≤ (n : ℝ) ^ P.u := Real.rpow_nonneg (Nat.cast_nonneg n) P.u
        have hLowExp : Real.exp (-((n : ℝ) ^ P.u) / 4) ≤
            Real.exp (-((n : ℝ) ^ P.u) / 8) :=
          Real.exp_le_exp.mpr (by nlinarith [hnuNonneg])
        have hHighExp : Real.exp (-((n : ℝ) ^ P.u) / 2) ≤
            Real.exp (-((n : ℝ) ^ P.u) / 8) :=
          Real.exp_le_exp.mpr (by nlinarith [hnuNonneg])
        have hDeepExp : Real.exp (-((n : ℝ) ^ P.u)) ≤
            Real.exp (-((n : ℝ) ^ P.u) / 8) :=
          Real.exp_le_exp.mpr (by nlinarith [hnuNonneg])
        have hsumBound : μbar.expect failProb ≤
            4 * Real.exp (-((n : ℝ) ^ P.u) / 8) := by
          calc
            μbar.expect failProb ≤
                μbar.expect (fun w => (if exceptionalLabel w then 1 else 0) +
                ((n : ℝ) * p₀ + Real.exp (-((n : ℝ) ^ P.u)))) :=
              μbar.expect_mono hpoint
            _ = μbar.pr exceptionalLabel +
                ((n : ℝ) * p₀ + Real.exp (-((n : ℝ) ^ P.u))) := hEupper
            _ ≤ Real.exp (-((n : ℝ) ^ P.u) / 4) +
                Real.exp (-((n : ℝ) ^ P.u) / 2) +
                (n : ℝ) * p₀ + Real.exp (-((n : ℝ) ^ P.u)) := by
              linarith [hException]
            _ ≤ 4 * Real.exp (-((n : ℝ) ^ P.u) / 8) := by
              calc
                _ ≤ Real.exp (-((n : ℝ) ^ P.u) / 8) +
                    Real.exp (-((n : ℝ) ^ P.u) / 8) +
                    Real.exp (-((n : ℝ) ^ P.u) / 8) +
                    Real.exp (-((n : ℝ) ^ P.u) / 8) := by
                  gcongr
                _ = 4 * Real.exp (-((n : ℝ) ^ P.u) / 8) := by ring
        have hlog2 : Real.log 2 ≤ 1 := by linarith [Real.log_two_lt_d9]
        have hlog4 : Real.log 4 ≤ 2 := by
          have hpow := Real.log_pow (2 : ℝ) 2
          norm_num at hpow ⊢
          nlinarith [hpow, hlog2]
        have hnu40 : 2 ≤ ((n : ℝ) ^ P.u) / 40 := by nlinarith [hUbig]
        have hfactor : 4 * Real.exp (-((n : ℝ) ^ P.u) / 8) =
            Real.exp (Real.log 4 - ((n : ℝ) ^ P.u) / 8) := by
          calc
            4 * Real.exp (-((n : ℝ) ^ P.u) / 8) =
                Real.exp (Real.log 4) * Real.exp (-((n : ℝ) ^ P.u) / 8) := by
              rw [Real.exp_log (by norm_num : (0 : ℝ) < 4)]
            _ = Real.exp (Real.log 4 - ((n : ℝ) ^ P.u) / 8) := by
              rw [← Real.exp_add]
              congr 1
              ring
        calc
          μbar.expect failProb ≤ 4 * Real.exp (-((n : ℝ) ^ P.u) / 8) := hsumBound
          _ = Real.exp (Real.log 4 - ((n : ℝ) ^ P.u) / 8) := hfactor
          _ ≤ Real.exp (-((n : ℝ) ^ P.u) / 10) := by
            apply Real.exp_le_exp.mpr
            linarith [hlog4, hnu40]
      have hrawMass : raw.expect mass ≤ Real.exp (-((n : ℝ) ^ P.u) / 10) := by
        rw [hmassFactor']
        exact hfailMass
      have hτpos : 0 < P.tail (1 / 100) n := by
        rw [Params9.tail]
        exact Real.exp_pos _
      have hτeq : P.tail (1 / 100) n = Real.exp (-((n : ℝ) ^ P.u) / 100) := by
        rw [Params9.tail]
        congr 1
        ring
      have hmarkov := FinProb.markov raw mass (P.tail (1 / 100) n) hmassNonneg hτpos
      have hbadImpl (tag : CubeVertex (P.m n) → M.ι)
          (htag : tagBad9 (P := P) E G (1 / 100) tag z) :
          P.tail (1 / 100) n ≤ mass tag := by
        have htag' : P.tail (1 / 100) n <
            ∑ w ∈ tagFail9 (P := P) E G tag z, (M.μ (tag z)).w w := by
          simpa [tagBad9, hcase] using htag
        rw [hmassFilter tag] at htag'
        exact le_of_lt htag'
      have hbadProb : raw.pr (fun tag =>
          tagBad9 (P := P) E G (1 / 100) tag z) ≤ P.tail (1 / 100) n := by
        calc
          raw.pr (fun tag => tagBad9 (P := P) E G (1 / 100) tag z) ≤
              raw.pr (fun tag => P.tail (1 / 100) n ≤ mass tag) :=
            FinProb.pr_mono raw _ _ hbadImpl
          _ ≤ raw.expect mass / P.tail (1 / 100) n := hmarkov
          _ ≤ Real.exp (-((n : ℝ) ^ P.u) / 10) /
                P.tail (1 / 100) n := by
            exact div_le_div_of_nonneg_right hrawMass (le_of_lt hτpos)
          _ ≤ P.tail (1 / 100) n := by
            rw [hτeq]
            have hratioTail : Real.exp (-((n : ℝ) ^ P.u) / 10) /
                Real.exp (-((n : ℝ) ^ P.u) / 100) ≤
                  Real.exp (-((n : ℝ) ^ P.u) / 100) := by
              rw [← Real.exp_sub]
              apply Real.exp_le_exp.mpr
              nlinarith [hUbig]
            exact hratioTail
      simpa [raw, tagLaw] using hbadProb

set_option maxHeartbeats 100000000 in
/-- P9.2-tags(ii) (09:135–137): the tag events satisfy the local-lemma input with charge `e^{-c' n^u/2}`:
`B_z` reads the tags on `{z} ∪ {z^j}` (`tagScope9`), two events meet only within special distance two (at
most `(m+1)²` others), and `e^{-c' n^u} ≤ x (1 - x)^{(m+1)²}` with `x = e^{-c' n^u/2}` for large `n`. -/
theorem p92_tag_lll (P : Params9) (hP : P.Valid) (c c' : ℝ) (hc : 0 < c) (hc' : 0 < c') :
    ∃ n₀ : ℕ, ∀ n ≥ n₀, ∀ {N : ℕ} (M : TagMix N) (E : Fin N → Fin N → Prop) (G : Colour),
      (∀ z : CubeVertex (P.m n),
        (FinProb.pi (fun _ : CubeVertex (P.m n) => tagMixLaw9 M)).pr
          (fun tag => tagBad9 (P := P) E G c tag z) ≤ P.tail c' n) →
      TagLLL9 P n M E G c (c' / 2) := by
  classical
  obtain ⟨nBasic, hBasic⟩ := Lane_q_s09_tag.basic_m_le_n_eventually_q_s09_tag P hP
  have hsmallEventually : ∀ᶠ n : ℕ in Filter.atTop,
      (n : ℝ) ^ 2 * P.tail (c' / 2) n < 1 / 8 := by
    have hlim := Lane_q_s09_tag.expTail_square_tendsto P hP (c' / 2) (by positivity)
    have h := hlim.eventually (Iio_mem_nhds (by norm_num : (0 : ℝ) < 1 / 8))
    filter_upwards [h] with n hn
    simpa only [Set.mem_Iio] using hn
  obtain ⟨nExp, hExp⟩ := Filter.eventually_atTop.mp hsmallEventually
  refine ⟨max nBasic nExp, ?_⟩
  intro n hn N M E G hprob
  have hnBasic : nBasic ≤ n := le_trans (le_max_left _ _) hn
  have hnExp : nExp ≤ n := le_trans (le_max_right _ _) hn
  have hbasic := hBasic n hnBasic
  have hn1 : 1 ≤ n := hbasic.1
  have hm : P.m n ≤ n := hbasic.2
  let x : ℝ := P.tail (c' / 2) n
  let Δ : ℕ := (P.m n + 1) ^ 2
  have hsmall : (n : ℝ) ^ 2 * x < 1 / 8 := by
    simpa [x] using hExp n hnExp
  have hxpos : 0 < x := by
    dsimp [x, Params9.tail]
    exact Real.exp_pos _
  have hnPow : (1 : ℝ) ≤ (n : ℝ) ^ 2 := by nlinarith [show (1 : ℝ) ≤ n by exact_mod_cast hn1]
  have hxltHalf : x < 1 / 2 := by
    calc
      x = 1 * x := by ring
      _ ≤ (n : ℝ) ^ 2 * x := mul_le_mul_of_nonneg_right hnPow hxpos.le
      _ < 1 / 8 := hsmall
      _ < 1 / 2 := by norm_num
  have hxle : x ≤ 1 / 2 := hxltHalf.le
  have hxlt : x < 1 := lt_of_le_of_lt hxle (by norm_num)
  have hMle : (P.m n : ℝ) ≤ (n : ℝ) := by exact_mod_cast hm
  have hMbase : (P.m n : ℝ) + 1 ≤ 2 * (n : ℝ) := by
    have hnR : 1 ≤ (n : ℝ) := by exact_mod_cast hn1
    linarith
  have hDle : (Δ : ℝ) ≤ 4 * (n : ℝ) ^ 2 := by
    have hdiff : 0 ≤ 2 * (n : ℝ) - ((P.m n : ℝ) + 1) := sub_nonneg.mpr hMbase
    have hsum : 0 ≤ 2 * (n : ℝ) + ((P.m n : ℝ) + 1) := by positivity
    have hprod := mul_nonneg hdiff hsum
    dsimp [Δ]
    norm_cast
    nlinarith
  have hDxLt : (Δ : ℝ) * x < 1 / 2 := by
    calc
      (Δ : ℝ) * x ≤ (4 * (n : ℝ) ^ 2) * x :=
        mul_le_mul_of_nonneg_right hDle hxpos.le
      _ < 1 / 2 := by nlinarith [hsmall]
  have hDx : (Δ : ℝ) * x ≤ 1 / 2 := hDxLt.le
  have hx1 : x ≤ 1 := hxle.trans (by norm_num)
  have hbern := Lane_q_s09_tag.one_sub_mul_le_pow hxpos.le hx1 Δ
  have hgeom : x / 2 ≤ x * (1 - x) ^ Δ := by
    have hone : 1 / 2 ≤ 1 - (Δ : ℝ) * x := by linarith
    calc
      x / 2 = (1 / 2) * x := by ring
      _ ≤ (1 - (Δ : ℝ) * x) * x := mul_le_mul_of_nonneg_right hone hxpos.le
      _ ≤ (1 - x) ^ Δ * x := mul_le_mul_of_nonneg_right hbern hxpos.le
      _ = x * (1 - x) ^ Δ := by ring
  have htailSq : P.tail c' n = x ^ 2 := by
    dsimp [x, Params9.tail]
    rw [pow_two, ← Real.exp_add]
    congr 1
    ring
  have htail : P.tail c' n ≤ x * (1 - x) ^ Δ := by
    rw [htailSq]
    calc
      x ^ 2 = x * x := by ring
      _ ≤ (1 / 2) * x := mul_le_mul_of_nonneg_right hxle hxpos.le
      _ = x / 2 := by ring
      _ ≤ x * (1 - x) ^ Δ := hgeom
  unfold TagLLL9
  refine ⟨hxpos.le, hxlt, ?_, ?_, ?_⟩
  · intro z tag tag' hagree
    have hzmem : z ∈ tagScope9 z := by simp [tagScope9]
    have htagz : tag z = tag' z := hagree z hzmem
    have hsurplus : ∀ w, tagSurplus9 E G tag z w = tagSurplus9 E G tag' z w := by
      intro w
      unfold tagSurplus9
      apply Finset.sum_congr rfl
      intro j hj
      have hjmem : flipWord9 z j ∈ tagScope9 z := by
        unfold tagScope9
        exact Finset.mem_insert_of_mem
          (Finset.mem_image.mpr ⟨j, Finset.mem_univ j, rfl⟩)
      rw [hagree (flipWord9 z j) hjmem]
    have hfailset : tagFail9 E G tag z = tagFail9 E G tag' z := by
      ext w
      simp [tagFail9, hsurplus w]
    cases hcase : P.case with
    | sub yS yD yM => simp [tagBad9, hcase]
    | lin αS αD hB yB => simp [tagBad9, hcase, htagz, hfailset]
  · intro z
    let dep := Finset.univ.filter (fun z' : CubeVertex (P.m n) =>
      z' ≠ z ∧ ¬ Disjoint (tagScope9 z) (tagScope9 z'))
    let fiber := fun a : CubeVertex (P.m n) =>
      Finset.univ.filter (fun z' : CubeVertex (P.m n) => a ∈ tagScope9 z')
    have hsubset : dep ⊆ (tagScope9 z).biUnion fiber := by
      intro z' hz'
      have hnd : ¬ Disjoint (tagScope9 z) (tagScope9 z') :=
        (Finset.mem_filter.mp hz').2.2
      have hcommon : ∃ a, a ∈ tagScope9 z ∧ a ∈ tagScope9 z' := by
        by_contra hnone
        apply hnd
        exact Finset.disjoint_left.mpr (by
          intro a ha ha'
          exact hnone ⟨a, ha, ha'⟩)
      obtain ⟨a, ha, ha'⟩ := hcommon
      exact Finset.mem_biUnion.mpr ⟨a, ha,
        Finset.mem_filter.mpr ⟨Finset.mem_univ _, ha'⟩⟩
    have hbi : ((tagScope9 z).biUnion fiber).card ≤
        (tagScope9 z).card * (P.m n + 1) := by
      exact Finset.card_biUnion_le_card_mul _ _ _ (by
        intro a ha
        exact Lane_q_s09_tag.tagScope_fiber_card_le P n a)
    have hdegree : dep.card ≤ Δ := by
      calc
        dep.card ≤ ((tagScope9 z).biUnion fiber).card := Finset.card_le_card hsubset
        _ ≤ (tagScope9 z).card * (P.m n + 1) := hbi
        _ ≤ (P.m n + 1) * (P.m n + 1) :=
          Nat.mul_le_mul_right _ (Lane_q_s09_tag.tagScope_card_le P n z)
        _ = Δ := by simp [Δ, pow_two]
    simpa [dep, Δ] using hdegree
  · intro z
    exact (hprob z).trans htail

/-- P9.2-tags(i) (09:122–124, 09:136–137): under the tag law the normalized tag loads exceed
`tagLoadConst9 κ` with probability at most `2 n 2^n 4^{-n}` (first and second laws separately).  Moments: for distinct special words, remove the at
most `(m+1)²` tag events touching each (factor `2` per word, `S07.CondProductBound`), leaving independent raw
tags whose mean laws are the balanced averages (`N ∑ Λ_i μ_i ≤ 8/κ`, the same for `ν`); then Lemma 3.6 with
near = same special word (fraction `2^{-m}`, caps `e^{S_s}` and `e^{n^{x_s} + O(log n)}`, and
`n 2^{-m} · cap ≤ 1` since `m log 2` exceeds both widths by `log n` for large `n`: `S_s + log n < m log 2` by
`ScalesAt9`, and `n^{x_s} + O(log n) < m log 2` by `P.CoreAdmissible`, i.e. `x_s < y_m`, in the sublinear case) and a union over the at most `n 2^n` labels
(`scatteredMoments_union_labels` with `K = 2`, `D₀ = 8/κ`). -/
theorem p92_tag_loads (P : Params9) (hP : P.Valid) (hA : P.CoreAdmissible) (κ : ℝ) (hκ : 0 < κ)
    (c' : ℝ) (hc' : 0 < c') :
    ∃ n₀ : ℕ, ∀ n ≥ n₀, ∀ {N : ℕ} {E : Fin N → Fin N → Prop} {X Y : Finset (Fin N)} {G : Colour}
      {M : TagMix N} (c : ℝ),
      0 < N → N ≤ n * 2 ^ n → Prep9 P κ n N E X Y G M → S07.CondProductBound →
      TagLLL9 P n M E G c c' →
      (tagLaw9 P n M E G c).pr (fun tag => ¬ tagLoadOK9 M tag (tagLoadConst9 κ)) ≤
        2 * ((n : ℝ) * 2 ^ n * (1 / 4 : ℝ) ^ n) := by
  classical
  rcases scales_eventually9 P hP with ⟨_, nScale, hScales⟩
  obtain ⟨nWidth, hWidth⟩ := Lane_q_s09_tag.tag_first_width_budget P hP hA
  have hsmallEventually : ∀ᶠ n : ℕ in Filter.atTop,
      (n : ℝ) ^ 2 * P.tail c' n < 1 / 8 := by
    have hlim := Lane_q_s09_tag.expTail_square_tendsto P hP c' hc'
    have h := hlim.eventually (Iio_mem_nhds (by norm_num : (0 : ℝ) < 1 / 8))
    filter_upwards [h] with n hn
    simpa only [Set.mem_Iio] using hn
  obtain ⟨nTail, hTail⟩ := Filter.eventually_atTop.mp hsmallEventually
  refine ⟨max nScale (max nWidth nTail), ?_⟩
  intro n hn N E X Y G M c hN hNle hprep hCond hLLL
  have hnScale : nScale ≤ n := le_trans (le_max_left _ _) hn
  have hnWidth : nWidth ≤ n := le_trans (le_max_left _ _) (le_trans (le_max_right _ _) hn)
  have hnTail : nTail ≤ n :=
    le_trans (le_trans (le_max_right nWidth nTail) (le_max_right nScale (max nWidth nTail))) hn
  have hscale : ScalesAt9 P n := hScales n hnScale
  have hwidth :
      (n : ℝ) ^ (P.xS : ℝ) + (P.hPlus : ℝ) * Real.log (n : ℝ) + 1 +
        Real.log (n : ℝ) ≤ (P.m n : ℝ) * Real.log 2 := hWidth n hnWidth
  have hsmall : (n : ℝ) ^ 2 * P.tail c' n < 1 / 8 := hTail n hnTail
  have hn1 : 1 ≤ n := hscale.1
  have hm : P.m n ≤ n := hscale.2.1
  have hNreal : 0 < (N : ℝ) := by exact_mod_cast hN
  let TagΩ := CubeVertex (P.m n) → M.ι
  let raw : FinProb TagΩ := FinProb.pi (fun _ : CubeVertex (P.m n) => tagMixLaw9 M)
  let good : TagΩ → Prop := fun tag => ∀ z, ¬ tagBad9 (P := P) E G c tag z
  have hAvoid := hCond _ _ _ _ _ hLLL
  have havoid : 0 < raw.pr good := by simpa [raw, good, TagLLL9] using hAvoid.1
  let Ptag : FinProb TagΩ := tagLaw9 P n M E G c
  have htaglaw : Ptag = raw.cond good havoid := by
    change S07.condOr raw good = raw.cond good havoid
    unfold S07.condOr
    rw [dif_pos havoid]
  let succ : Finset TagΩ := Finset.univ.filter fun tag => ∀ z, 0 < M.Λ (tag z)
  have hsupport (tag : TagΩ) (ht : Ptag.w tag ≠ 0) : tag ∈ succ := by
    have htpos : 0 < Ptag.w tag := lt_of_le_of_ne (Ptag.nonneg tag) (Ne.symm ht)
    refine Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_⟩
    intro z
    exact Lane_q_s09_tag.tagLaw_pos_coord P n N M E G c havoid tag htpos z
  have hzeroOutside (tag : TagΩ) (ht : tag ∉ succ) : Ptag.w tag = 0 := by
    by_contra hne
    exact ht (hsupport tag hne)
  let U := CubeVertex (P.m n)
  haveI : Nonempty U := ⟨fun _ => false⟩
  have hcardPow : (Fintype.card U : ℝ) = (2 : ℝ) ^ (P.m n) := by
    simp [U, CubeVertex]
  have hcardPos : 0 < (Fintype.card U : ℝ) := by positivity
  let Wμ : ℝ := (n : ℝ) ^ (P.xS : ℝ) + (P.hPlus : ℝ) * Real.log (n : ℝ) + 1
  let Wν : ℝ := P.Ss (n : ℝ)
  let W : ℝ := max Wμ Wν
  let L : ℝ := Real.exp W
  let D₀ : ℝ := 8 / κ
  have hthreshold : tagLoadConst9 κ = 4 * (2 : ℝ) * (D₀ + 1) := by
    dsimp [tagLoadConst9, D₀]
    ring
  have hWbudget : W + Real.log (n : ℝ) ≤ (P.m n : ℝ) * Real.log 2 := by
    have hμ : Wμ ≤ (P.m n : ℝ) * Real.log 2 - Real.log (n : ℝ) := by
      dsimp [Wμ]
      linarith
    have hν : Wν ≤ (P.m n : ℝ) * Real.log 2 - Real.log (n : ℝ) := by
      dsimp [Wν]
      linarith [hscale.2.2.2.1]
    have hmax : max Wμ Wν ≤ (P.m n : ℝ) * Real.log 2 - Real.log (n : ℝ) :=
      max_le_iff.mpr ⟨hμ, hν⟩
    dsimp [W]
    linarith
  have hexpPow : Real.exp ((P.m n : ℝ) * Real.log 2) = (2 : ℝ) ^ (P.m n) := by
    calc
      Real.exp ((P.m n : ℝ) * Real.log 2) = (2 : ℝ) ^ (P.m n : ℝ) := by
        simpa only [mul_comm] using
          (Real.rpow_def_of_pos (by norm_num : (0 : ℝ) < 2) (P.m n : ℝ)).symm
      _ = (2 : ℝ) ^ (P.m n) := Real.rpow_natCast 2 (P.m n)
  have hExpBudget : (n : ℝ) * L ≤ (Fintype.card U : ℝ) := by
    have hnR : 0 < (n : ℝ) := by exact_mod_cast (lt_of_lt_of_le (by decide : 0 < 1) hn1)
    have hExp : Real.exp (W + Real.log (n : ℝ)) ≤ Real.exp ((P.m n : ℝ) * Real.log 2) :=
      Real.exp_le_exp.mpr hWbudget
    have hprod : Real.exp (W + Real.log (n : ℝ)) = (n : ℝ) * L := by
      rw [Real.exp_add, Real.exp_log hnR]
      dsimp [L]
      ring
    rw [hprod, hexpPow, ← hcardPow] at hExp
    exact hExp
  let frac : ℝ := (Fintype.card U : ℝ)⁻¹
  have hsmallLoad : (n : ℝ) * frac * L ≤ 1 := by
    have h := mul_le_mul_of_nonneg_left hExpBudget (inv_nonneg.mpr hcardPos.le)
    calc
      (n : ℝ) * frac * L = frac * ((n : ℝ) * L) := by ring
      _ ≤ frac * (Fintype.card U : ℝ) := h
      _ = 1 := by dsimp [frac]; field_simp [ne_of_gt hcardPos]
  have hlabels : (Fintype.card (Fin N) : ℝ) ≤ (n : ℝ) * 2 ^ n := by
    simpa using (show (N : ℝ) ≤ (n : ℝ) * 2 ^ n by exact_mod_cast hNle)
  have hnpos : 0 < n := by omega
  have hxpos : 0 < P.tail c' n := by
    dsimp [Params9.tail]
    exact Real.exp_pos _
  have hxnonneg : 0 ≤ P.tail c' n := le_of_lt hxpos
  have hxle : P.tail c' n ≤ 1 := by
    rw [Params9.tail, Real.exp_le_one_iff]
    exact neg_nonpos.mpr (mul_nonneg hc'.le (Real.rpow_nonneg (Nat.cast_nonneg n) _))
  have hnSq : (1 : ℝ) ≤ (n : ℝ) ^ 2 := by exact_mod_cast (Nat.one_le_pow 2 n hn1)
  have hxsmall : P.tail c' n < 1 / 8 := by nlinarith [hsmall]
  let near : U → Finset U := fun v => {v}
  have hself (v : U) : v ∈ near v := by simp [near]
  have hfracNonneg : 0 ≤ frac := inv_nonneg.mpr hcardPos.le
  have hnear (v : U) : ((near v).card : ℝ) ≤ frac * (Fintype.card U : ℝ) := by
    simp [near, frac]
  have hbalMu : ∀ y, (N : ℝ) * ∑ i, M.Λ i * (M.μ i).w y ≤ D₀ := by
    simpa [D₀] using hprep.1.1
  have hbalNu : ∀ y, (N : ℝ) * ∑ i, M.Λ i * (M.ν i).w y ≤ D₀ := by
    simpa [D₀] using hprep.1.2
  have componentTail (lawOf : M.ι → Law N)
      (hlawWidth : ∀ i, 0 < M.Λ i → (lawOf i).WidthLE W)
      (hbal : ∀ y, (N : ℝ) * ∑ i, M.Λ i * (lawOf i).w y ≤ D₀) :
      Ptag.pr (fun tag => ∃ y, 4 * (2 : ℝ) * (D₀ + 1) <
        frac * ∑ v : U, (N : ℝ) * (lawOf (tag v)).w y) ≤
        (n : ℝ) * 2 ^ n * (1 / 4 : ℝ) ^ n := by
    let Z : U → Fin N → TagΩ → ℝ := fun v y tag => (N : ℝ) * (lawOf (tag v)).w y
    let mean : Fin N → ℝ := fun y =>
      (tagMixLaw9 M).expect (fun i => (N : ℝ) * (lawOf i).w y)
    let d : U → Fin N → ℝ := fun _ y => mean y
    have hZ0 : ∀ v y tag, 0 ≤ Z v y tag := by
      intro v y tag
      exact mul_nonneg (Nat.cast_nonneg N) ((lawOf (tag v)).nonneg y)
    have hLnonneg : 0 ≤ L := le_of_lt (Real.exp_pos W)
    have hZL : ∀ v y tag, tag ∈ succ → Z v y tag ≤ L := by
      intro v y tag htag
      have hΛ : 0 < M.Λ (tag v) := (Finset.mem_filter.mp htag).2 v
      have hwidthLaw := hlawWidth (tag v) hΛ y
      dsimp [Z, L]
      calc
        (N : ℝ) * (lawOf (tag v)).w y ≤
            (N : ℝ) * (Real.exp W / N) :=
          mul_le_mul_of_nonneg_left hwidthLaw (Nat.cast_nonneg N)
        _ = Real.exp W := by field_simp [ne_of_gt hNreal]
    have hd : ∀ v y, 0 ≤ d v y := by
      intro v y
      dsimp [d, mean, FinProb.expect]
      apply Finset.sum_nonneg
      intro i hi
      exact mul_nonneg ((tagMixLaw9 M).nonneg i)
        (mul_nonneg (Nat.cast_nonneg N) ((lawOf i).nonneg y))
    have hmeanBound (y : Fin N) :
        (Fintype.card U : ℝ)⁻¹ * ∑ v : U, d v y ≤ D₀ := by
      have hmeanEq : mean y =
          (N : ℝ) * ∑ i, M.Λ i * (lawOf i).w y := by
        dsimp [mean, FinProb.expect, tagMixLaw9]
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro i hi
        ring
      have hmeanSum : ∑ v : U, d v y = (Fintype.card U : ℝ) * mean y := by
        simp [d, Finset.sum_const]
      rw [hmeanSum, hmeanEq]
      have hcancel : (Fintype.card U : ℝ)⁻¹ * (Fintype.card U : ℝ) = 1 :=
        inv_mul_cancel₀ (ne_of_gt hcardPos)
      calc
        (Fintype.card U : ℝ)⁻¹ * ((Fintype.card U : ℝ) *
            ((N : ℝ) * ∑ i, M.Λ i * (lawOf i).w y)) =
            (N : ℝ) * ∑ i, M.Λ i * (lawOf i).w y := by rw [← mul_assoc, hcancel, one_mul]
        _ ≤ D₀ := hbal y
    have hjoint : ∀ y (k : ℕ), k ≤ n → ∀ s : Fin k → U,
        (∀ i j : Fin k, j < i → s i ∉ near (s j)) →
          ∑ tag ∈ succ, Ptag.w tag * ∏ i, Z (s i) y tag ≤
            (2 : ℝ) ^ k * ∏ i, d (s i) y := by
      intro y k hk s hsep
      have hsInjective : Function.Injective s := by
        intro i j hij
        by_contra hne
        rcases lt_or_gt_of_ne hne with hlt | hgt
        · have h := hsep j i hlt
          have hmem : s j ∈ near (s i) := by simpa [near, hij]
          exact h hmem
        · have h := hsep i j hgt
          have hmem : s i ∈ near (s j) := by simpa [near, hij]
          exact h hmem
      let selected : Finset U := Finset.univ.image s
      let touching : Finset (CubeVertex (P.m n)) :=
        Finset.univ.filter fun z => ¬ Disjoint (tagScope9 (P := P) z) selected
      have hselectedCard : selected.card ≤ k := by
        dsimp [selected]
        exact (Finset.card_image_le).trans_eq (by simp)
      have htouch := Lane_q_s09_tag.tagScope_touch_card_q_s09_tag P n selected
      have htouchNat : touching.card ≤ n * (n + 1) := by
        calc
          touching.card ≤ selected.card * (P.m n + 1) := by exact htouch
          _ ≤ k * (P.m n + 1) := Nat.mul_le_mul_right _ hselectedCard
          _ ≤ n * (n + 1) := Nat.mul_le_mul hk (Nat.succ_le_succ hm)
      have htouchReal : (touching.card : ℝ) ≤ (n : ℝ) * ((n + 1 : ℕ) : ℝ) := by
        exact_mod_cast htouchNat
      have hnplus : ((n + 1 : ℕ) : ℝ) ≤ 2 * (n : ℝ) := by
        have hnNat : n + 1 ≤ 2 * n := by omega
        exact_mod_cast hnNat
      have htouchx : (touching.card : ℝ) * P.tail c' n < 1 / 4 := by
        calc
          (touching.card : ℝ) * P.tail c' n ≤
              (n : ℝ) * ((n + 1 : ℕ) : ℝ) * P.tail c' n :=
            mul_le_mul_of_nonneg_right htouchReal hxnonneg
          _ ≤ 2 * (n : ℝ) ^ 2 * P.tail c' n := by
            have hmult := mul_le_mul_of_nonneg_left hnplus (Nat.cast_nonneg n)
            nlinarith [mul_le_mul_of_nonneg_right hmult hxnonneg]
          _ < 1 / 4 := by nlinarith [hsmall, hnSq, hn1]
      have hbern := Lane_q_s09_tag.one_sub_mul_le_pow hxnonneg hxle touching.card
      have hfactorLower : (1 / 2 : ℝ) ≤ (1 - P.tail c' n) ^ touching.card := by
        have hprod : 1 - (touching.card : ℝ) * P.tail c' n ≤
            (1 - P.tail c' n) ^ touching.card := hbern
        nlinarith
      have hinvFactor : ((1 - P.tail c' n) ^ touching.card)⁻¹ ≤ 2 := by
        have h := one_div_le_one_div_of_le (by norm_num : (0 : ℝ) < 1 / 2) hfactorLower
        calc
          ((1 - P.tail c' n) ^ touching.card)⁻¹ ≤ (1 / 2 : ℝ)⁻¹ := by
            simpa only [one_div] using h
          _ = 2 := by norm_num
      have hinvPow : ((1 - P.tail c' n) ^ touching.card)⁻¹ ≤ (2 : ℝ) ^ k := by
        by_cases hk0 : k = 0
        · subst k
          have hselected0 : selected.card = 0 := by
            have hle := hselectedCard
            simp at hle
            omega
          have htouch0 : touching.card = 0 := by
            have hle : touching.card ≤ 0 := by
              rw [hselected0] at htouch
              simpa only [Nat.zero_mul] using htouch
            exact Nat.eq_zero_of_le_zero hle
          simp [htouch0]
        · have hk1 : 1 ≤ k := Nat.one_le_iff_ne_zero.mpr hk0
          have h2pow : (2 : ℝ) ≤ (2 : ℝ) ^ k := by
            calc
              (2 : ℝ) = (2 : ℝ) ^ 1 := by norm_num
              _ ≤ (2 : ℝ) ^ k := pow_le_pow_right₀ (by norm_num) hk1
          exact hinvFactor.trans h2pow
      have hprodNonneg : 0 ≤ ∏ i : Fin k, d (s i) y :=
        Finset.prod_nonneg fun i hi => hd (s i) y
      have hcond := Lane_q_s09_tag.cond_product_tuple_expect_q_s09_tag
        hCond (fun _ : U => tagMixLaw9 M)
        (fun z tag => tagBad9 (P := P) E G c tag z) tagScope9 (P.tail c' n)
        ((P.m n + 1) ^ 2) hLLL s hsInjective (fun i tag => (N : ℝ) * (lawOf tag).w y) (by
          intro ω
          exact Finset.prod_nonneg fun i hi =>
            mul_nonneg (Nat.cast_nonneg N) ((lawOf (ω (s i))).nonneg y))
      have hcondP : Ptag.expect (fun tag => ∏ i, Z (s i) y tag) ≤
          ((1 - P.tail c' n) ^ touching.card)⁻¹ * ∏ i, d (s i) y := by
        simpa [Ptag, tagLaw9, raw, good, Z, d, mean] using hcond
      have hsumLe :
          ∑ tag ∈ succ, Ptag.w tag * ∏ i, Z (s i) y tag ≤
            Ptag.expect (fun tag => ∏ i, Z (s i) y tag) := by
        unfold FinProb.expect
        exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ succ) (by
          intro tag htag hnot
          exact mul_nonneg (Ptag.nonneg tag)
            (Finset.prod_nonneg fun i hi => hZ0 (s i) y tag))
      calc
        ∑ tag ∈ succ, Ptag.w tag * ∏ i, Z (s i) y tag ≤
            ((1 - P.tail c' n) ^ touching.card)⁻¹ * ∏ i, d (s i) y := hsumLe.trans hcondP
        _ ≤ (2 : ℝ) ^ k * ∏ i, d (s i) y :=
          mul_le_mul_of_nonneg_right hinvPow hprodNonneg
    have htail := scatteredMoments_union_labels Ptag succ Z hZ0 L hLnonneg hZL
      near hself frac hfracNonneg hnear n (by exact_mod_cast hnpos) 2 D₀
      (by norm_num) (by positivity) d hd hmeanBound hjoint hsmallLoad hlabels
    have hthreshold : tagLoadConst9 κ = 4 * (2 : ℝ) * (D₀ + 1) := by
      dsimp [tagLoadConst9, D₀]
      ring
    have hfail :
        Ptag.pr (fun tag => ∃ y, tagLoadConst9 κ < frac *
          ∑ v : U, (N : ℝ) * (lawOf (tag v)).w y) =
        ∑ tag, if tag ∈ succ ∧ ∃ y, 4 * (2 : ℝ) * (D₀ + 1) <
          frac * ∑ v : U, (N : ℝ) * (lawOf (tag v)).w y then Ptag.w tag else 0 := by
      unfold FinProb.pr
      apply Finset.sum_congr rfl
      intro tag htag
      by_cases hs : tag ∈ succ
      · simp [hs, hthreshold]
      · simp [hs, hzeroOutside tag hs]
    rw [← hthreshold, hfail]
    simpa [frac, Z] using htail
  have hμwidth : ∀ i, 0 < M.Λ i → (M.μ i).WidthLE W := by
    intro i hi
    rcases hprep.2 i hi with ⟨_, _, hμ, _, _⟩
    intro y
    exact le_trans (hμ y)
      (div_le_div_of_nonneg_right
        (Real.exp_le_exp.mpr (le_max_left Wμ Wν)) (Nat.cast_nonneg N))
  have hνwidth : ∀ i, 0 < M.Λ i → (M.ν i).WidthLE W := by
    intro i hi
    rcases hprep.2 i hi with ⟨_, _, _, hν, _⟩
    intro y
    exact le_trans (hν y)
      (div_le_div_of_nonneg_right
        (Real.exp_le_exp.mpr (le_max_right Wμ Wν)) (Nat.cast_nonneg N))
  have hμtail := componentTail M.μ hμwidth hbalMu
  have hνtail := componentTail M.ν hνwidth hbalNu
  let failMu : TagΩ → Prop := fun tag => ∃ y,
    tagLoadConst9 κ < frac * ∑ v : U, (N : ℝ) * (M.μ (tag v)).w y
  let failNu : TagΩ → Prop := fun tag => ∃ y,
    tagLoadConst9 κ < frac * ∑ v : U, (N : ℝ) * (M.ν (tag v)).w y
  have havgMu (tag : TagΩ) (y : Fin N) :
        ((2 : ℝ) ^ (P.m n))⁻¹ * ∑ z, (N : ℝ) * (M.μ (tag z)).w y =
        frac * ∑ v : U, (N : ℝ) * (M.μ (tag v)).w y := by
    dsimp [frac]
    rw [hcardPow]
  have havgNu (tag : TagΩ) (y : Fin N) :
        ((2 : ℝ) ^ (P.m n))⁻¹ * ∑ z, (N : ℝ) * (M.ν (tag z)).w y =
        frac * ∑ v : U, (N : ℝ) * (M.ν (tag v)).w y := by
    dsimp [frac]
    rw [hcardPow]
  have hbadEq (tag : TagΩ) :
      (¬ tagLoadOK9 M tag (tagLoadConst9 κ)) ↔ (failMu tag ∨ failNu tag) := by
    change (¬ ((∀ x, ((2 : ℝ) ^ (P.m n))⁻¹ *
        ∑ z, (N : ℝ) * (M.μ (tag z)).w x ≤ tagLoadConst9 κ) ∧
      (∀ y, ((2 : ℝ) ^ (P.m n))⁻¹ *
        ∑ z, (N : ℝ) * (M.ν (tag z)).w y ≤ tagLoadConst9 κ))) ↔ _
    constructor
    · intro hbad
      rcases not_and_or.mp hbad with hμ | hν
      · left
        push_neg at hμ
        obtain ⟨y, hy⟩ := hμ
        have hy' := hy
        rw [havgMu tag y] at hy'
        exact ⟨y, hy'⟩
      · right
        push_neg at hν
        obtain ⟨y, hy⟩ := hν
        have hy' := hy
        rw [havgNu tag y] at hy'
        exact ⟨y, hy'⟩
    · rintro (⟨y, hy⟩ | ⟨y, hy⟩) hgood
      · have hμ := hgood.1 y
        rw [havgMu] at hμ
        exact (not_le_of_gt hy) hμ
      · have hν := hgood.2 y
        rw [havgNu] at hν
        exact (not_le_of_gt hy) hν
  have hprobEq :
      Ptag.pr (fun tag => ¬ tagLoadOK9 M tag (tagLoadConst9 κ)) =
        Ptag.pr (fun tag => failMu tag ∨ failNu tag) := by
    unfold FinProb.pr
    apply Finset.sum_congr rfl
    intro tag htag
    by_cases h : failMu tag ∨ failNu tag
    · have hn : ¬ tagLoadOK9 M tag (tagLoadConst9 κ) := (hbadEq tag).2 h
      simp [h, hn]
    · have hg : tagLoadOK9 M tag (tagLoadConst9 κ) := by
        by_contra hb
        exact h ((hbadEq tag).1 hb)
      simp [h, hg]
  have hμtail' : Ptag.pr failMu ≤ (n : ℝ) * 2 ^ n * (1 / 4 : ℝ) ^ n := by
    simpa [failMu, hthreshold] using hμtail
  have hνtail' : Ptag.pr failNu ≤ (n : ℝ) * 2 ^ n * (1 / 4 : ℝ) ^ n := by
    simpa [failNu, hthreshold] using hνtail
  calc
    (tagLaw9 P n M E G c).pr (fun tag => ¬ tagLoadOK9 M tag (tagLoadConst9 κ)) =
        Ptag.pr (fun tag => ¬ tagLoadOK9 M tag (tagLoadConst9 κ)) := by rfl
    _ = Ptag.pr (fun tag => failMu tag ∨ failNu tag) := hprobEq
    _ ≤ Ptag.pr failMu + Ptag.pr failNu := FinProb.pr_union Ptag failMu failNu
    _ ≤ (n : ℝ) * 2 ^ n * (1 / 4 : ℝ) ^ n +
        (n : ℝ) * 2 ^ n * (1 / 4 : ℝ) ^ n := add_le_add hμtail' hνtail'
    _ = 2 * ((n : ℝ) * 2 ^ n * (1 / 4 : ℝ) ^ n) := by ring

/-- P9.2-tags (09:137–138), choice of the fixed tags: if the avoidance event of the tag events has positive raw
mass and the tag loads fail under the tag law with probability at most `2 n 2^n 4^{-n} < 1`, some tag function in
the support of the tag law satisfies `TagsOK9` (its tags have positive mixture weight because the raw law is
supported on such tags). -/
theorem tags_of_tag_law :
    ∃ n₀ : ℕ, ∀ n ≥ n₀, ∀ {P : Params9} {N : ℕ} {M : TagMix N} (κ : ℝ) (E : Fin N → Fin N → Prop)
      (G : Colour) (c : ℝ),
      0 < (FinProb.pi (fun _ : CubeVertex (P.m n) => tagMixLaw9 M)).pr
          (fun tag => ∀ z, ¬ tagBad9 (P := P) E G c tag z) →
      (tagLaw9 P n M E G c).pr (fun tag => ¬ tagLoadOK9 M tag (tagLoadConst9 κ)) ≤
        2 * ((n : ℝ) * 2 ^ n * (1 / 4 : ℝ) ^ n) →
      ∃ tag : CubeVertex (P.m n) → M.ι, TagsOK9 κ E G c tag := by
  classical
  refine ⟨3, ?_⟩
  intro n hn P N M κ E G c havoid hfail
  let raw : FinProb (CubeVertex (P.m n) → M.ι) :=
    FinProb.pi (fun _ : CubeVertex (P.m n) => tagMixLaw9 M)
  let good : (CubeVertex (P.m n) → M.ι) → Prop :=
    fun tag => ∀ z, ¬ tagBad9 (P := P) E G c tag z
  let badLoad : (CubeVertex (P.m n) → M.ι) → Prop :=
    fun tag => ¬ tagLoadOK9 M tag (tagLoadConst9 κ)
  letI : DecidablePred badLoad := fun tag => Classical.propDecidable (badLoad tag)
  let q : FinProb (CubeVertex (P.m n) → M.ι) := tagLaw9 P n M E G c
  have hdelta : 2 * ((n : ℝ) * 2 ^ n * (1 / 4 : ℝ) ^ n) < 1 := by
    have hpow : ∀ k : ℕ, 3 ≤ k → (k : ℝ) < (2 : ℝ) ^ (k - 1) := by
      intro k
      induction k with
      | zero => intro hk; omega
      | succ k ih =>
          intro hk
          by_cases hk2 : k = 2
          · subst k
            norm_num
          · have hk3 : 3 ≤ k := by omega
            have hrec := ih hk3
            have hkge : 2 ≤ k := by omega
            have hmul : 2 * (k : ℝ) < 2 * ((2 : ℝ) ^ (k - 1)) :=
              mul_lt_mul_of_pos_left hrec (by norm_num)
            have hpow' : 2 * ((2 : ℝ) ^ (k - 1)) = (2 : ℝ) ^ k := by
              have hExp : k - 1 + 1 = k := by omega
              calc
                2 * (2 : ℝ) ^ (k - 1) = (2 : ℝ) ^ (k - 1) * 2 := by ring
                _ = (2 : ℝ) ^ (k - 1 + 1) := by rw [pow_succ]
                _ = (2 : ℝ) ^ k := by rw [hExp]
            have hlinN : k + 1 ≤ 2 * k := by omega
            have hlin : ((k + 1 : ℕ) : ℝ) ≤ 2 * (k : ℝ) := by
              exact_mod_cast hlinN
            have hpowNext : ((k + 1 : ℕ) : ℝ) < (2 : ℝ) ^ k := by
              exact lt_of_le_of_lt hlin (hpow'.symm ▸ hmul)
            simpa using hpowNext
    have hpowN := hpow n hn
    have hpowpos : 0 < (2 : ℝ) ^ (n - 1) := by positivity
    have hratio : 2 * (n : ℝ) * (1 / 2 : ℝ) ^ n =
        (n : ℝ) / (2 : ℝ) ^ (n - 1) := by
      have hpowhalf : (1 / 2 : ℝ) ^ n = 1 / (2 : ℝ) ^ n := by
        rw [div_pow]
        norm_num
      have hpowN' : (2 : ℝ) ^ n = 2 * (2 : ℝ) ^ (n - 1) := by
        have hExp : n - 1 + 1 = n := by omega
        calc
          (2 : ℝ) ^ n = (2 : ℝ) ^ (n - 1 + 1) := by rw [hExp]
          _ = (2 : ℝ) ^ (n - 1) * 2 := by rw [pow_succ]
          _ = 2 * (2 : ℝ) ^ (n - 1) := by ring
      rw [hpowhalf, hpowN']
      field_simp
    have hbase : (2 : ℝ) ^ n * (1 / 4 : ℝ) ^ n = (1 / 2 : ℝ) ^ n := by
      rw [← mul_pow]
      norm_num
    calc
      2 * ((n : ℝ) * 2 ^ n * (1 / 4 : ℝ) ^ n) =
          2 * (n : ℝ) * (2 ^ n * (1 / 4 : ℝ) ^ n) := by ring
      _ = 2 * (n : ℝ) * (1 / 2 : ℝ) ^ n := by rw [hbase]
      _ = (n : ℝ) / (2 : ℝ) ^ (n - 1) := hratio
      _ < 1 := (div_lt_one hpowpos).2 hpowN
  have hqAvoid : ∀ tag, q.w tag ≠ 0 → good tag := by
    intro tag htag
    have hrawpos : 0 < raw.pr good := havoid
    have hqeq : q = raw.cond good hrawpos := by
      change S07.condOr raw good = raw.cond good hrawpos
      unfold S07.condOr
      rw [dif_pos hrawpos]
    by_contra hnot
    have hzero : (raw.cond good hrawpos).w tag = 0 := by
      simp [FinProb.cond, hnot]
    exact htag (by simpa [hqeq] using hzero)
  have hex : ∃ tag, q.w tag ≠ 0 ∧ ¬ badLoad tag := by
    by_contra hnone
    have hsum : ∑ tag, (if badLoad tag then q.w tag else 0) = ∑ tag, q.w tag := by
      apply Finset.sum_congr rfl
      intro tag _
      by_cases hb : badLoad tag
      · simp [hb]
      · have hz : q.w tag = 0 := by
          by_contra hne
          exact hnone ⟨tag, hne, hb⟩
        simp [hb, hz]
    have hbadone : q.pr badLoad = 1 := by
      unfold FinProb.pr
      exact hsum.trans q.sum_eq_one
    have hcontr := hfail
    change q.pr badLoad ≤ 2 * ((n : ℝ) * 2 ^ n * (1 / 4 : ℝ) ^ n) at hcontr
    rw [hbadone] at hcontr
    linarith
  obtain ⟨tag, htag, htagLoad⟩ := hex
  have hgood : good tag := hqAvoid tag htag
  have hqeq : q = raw.cond good havoid := by
    change S07.condOr raw good = raw.cond good havoid
    unfold S07.condOr
    rw [dif_pos havoid]
  have htagPos : 0 < q.w tag := lt_of_le_of_ne (q.nonneg tag) (Ne.symm htag)
  have hrawPos : 0 < raw.w tag := by
    rw [hqeq, FinProb.cond] at htagPos
    have hden : 0 < raw.pr good := havoid
    by_cases ht : good tag
    · simpa [ht] using (div_pos_iff_of_pos_right hden).mp htagPos
    · simp [ht] at htagPos
  have hmixPos : ∀ z, 0 < M.Λ (tag z) := by
    intro z
    have hcoord : 0 < (tagMixLaw9 M).w (tag z) := by
      by_contra hnz
      have hz : (tagMixLaw9 M).w (tag z) = 0 :=
        le_antisymm (not_lt.mp hnz) ((tagMixLaw9 M).nonneg _)
      have hzero : raw.w tag = 0 := by
        dsimp [raw, FinProb.pi]
        exact Finset.prod_eq_zero (Finset.mem_univ z) (by simpa [tagMixLaw9] using hz)
      exact (ne_of_gt hrawPos) hzero
    simpa [tagMixLaw9] using hcoord
  refine ⟨tag, ?_⟩
  unfold TagsOK9
  have hload : tagLoadOK9 M tag (tagLoadConst9 κ) := by
    simpa [badLoad] using htagLoad
  exact ⟨hmixPos, hload, hgood⟩

/-- P9.2-tags assembled (09:120–138): fixed tags with positive mixture weights, bounded loads, and (linear case)
the special-neighbour surplus condition outside first-law mass `e^{-c n^u}`. -/
theorem p92_tags (P : Params9) (hP : P.Valid) (hA : P.CoreAdmissible) (κ : ℝ) (hκ : 0 < κ) :
    ∃ c > (0 : ℝ), ∃ n₀ : ℕ, ∀ n ≥ n₀, ∀ {N : ℕ} {E : Fin N → Fin N → Prop}
      {X Y : Finset (Fin N)} {G : Colour} {M : TagMix N},
      0 < N → N ≤ n * 2 ^ n → Prep9 P κ n N E X Y G M → P.DeepAt n N E X Y →
      P.BroadAt n N E X Y →
      ∃ tag : CubeVertex (P.m n) → M.ι, TagsOK9 κ E G c tag := by
  obtain ⟨c, hc, c', hc', n₁, hbad⟩ := p92_tag_bad_prob P hP κ hκ
  obtain ⟨n₂, hlll⟩ := p92_tag_lll P hP c c' hc hc'
  obtain ⟨n₃, hload⟩ := p92_tag_loads P hP hA κ hκ (c' / 2) (by positivity)
  obtain ⟨n₄, hchoose⟩ := tags_of_tag_law
  refine ⟨c, hc, max (max n₁ n₂) (max n₃ n₄), ?_⟩
  intro n hn N E X Y G M hN hNle hprep hdeep hbroad
  have hn₁ : n₁ ≤ n := le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) hn
  have hn₂ : n₂ ≤ n := le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) hn
  have hn₃ : n₃ ≤ n := le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) hn
  have hn₄ : n₄ ≤ n := le_trans (le_trans (le_max_right _ _) (le_max_right _ _)) hn
  have hT : TagLLL9 P n M E G c (c' / 2) := hlll n hn₂ M E G (hbad n hn₁ hN hprep hdeep hbroad)
  have hpos := (S07.cond_product_bound _ _ _ _ _ hT).1
  exact hchoose n hn₄ κ E G c hpos (hload n hn₃ c hN hNle hprep S07.cond_product_bound hT)

/-- P9.2-tags(iii) (09:139–144), F-PriceSep: for fixed tags there are mask laws, independent across rows, with
every mask of `ν`-mass at least `½ e^{-n^u}` and `R_b ≤ (1 + e^{-n^u}) ν` pointwise.  For a nonnegative price
`p`, the labels with `p ≤ (1 + δ) E_ν p` (`δ = e^{-n^u} ≤ 1`) have `ν`-mass at least `δ/(1+δ) ≥ δ/2` and every
output of the row filter from that mask (including the fallback) has the same price bound; the finite minimax
theorem over masks and prices gives a mask law with `E_{mask, anchors} E_{p_b} p ≤ (1+δ) E_ν p` for every
price, hence pointwise. -/
theorem p92_masks {P : Params9} {n N : ℕ} {M : TagMix N} (E : Fin N → Fin N → Prop) (G : Colour)
    (I : IDMap9 P n) (tag : CubeVertex (P.m n) → M.ι) (hN : 0 < N) :
    ∃ maskLaw : OddSites9 n → FinProb (Finset (Fin N)),
      MasksOK9 (⟨tag, maskLaw⟩ : Setup9 P n N M) I E G := by
  classical
  haveI : Nonempty (Fin N) := ⟨⟨0, hN⟩⟩
  have hu : 0 ≤ (n : ℝ) ^ P.u := by positivity
  let δ : ℝ := Real.exp (-(n : ℝ) ^ P.u)
  have hδpos : 0 < δ := by positivity
  have hδle : δ ≤ 1 := by
    dsimp [δ]
    rw [Real.exp_le_one_iff]
    linarith
  let defaultMask : FinProb (Finset (Fin N)) := FinProb.uniform {∅} (by simp)
  let Sbase : Setup9 P n N M := ⟨tag, fun _ => defaultMask⟩
  let R : OddSites9 n → Finset (Fin N) → Law N := fun b A =>
    Lane_q_s09_tag.tagActionLaw_q_s09_tag (I := I) Sbase E G b A
  have hR (b : OddSites9 n) (A : Finset (Fin N))
      (hA : 0 < Lane_q_s09_tag.maskMass (siteSecond9 Sbase b.1) A) (y : Fin N) (hy : y ∉ A) :
      (R b A).w y = 0 := by
    dsimp [R, Lane_q_s09_tag.tagActionLaw_q_s09_tag, Law.mix]
    apply Finset.sum_eq_zero
    intro a _
    have hmask : msk9 (Lane_q_s09_tag.tagAnchorOutcome_q_s09_tag a b A) b = A := by
      simp [msk9, Lane_q_s09_tag.tagAnchorOutcome_q_s09_tag]
    have hmasked :
        (maskedLaw9 Sbase (Lane_q_s09_tag.tagAnchorOutcome_q_s09_tag a b A) b).w y = 0 := by
      change (restrictOr9 (siteSecond9 Sbase b.1)
        (msk9 (Lane_q_s09_tag.tagAnchorOutcome_q_s09_tag a b A) b)).w y = 0
      rw [hmask]
      apply Lane_q_s09_tag.restrictOr9_outside
      · exact hA
      · exact hy
    have hrow :
        (rowLaw9 Sbase E G (Lane_q_s09_tag.tagAnchorOutcome_q_s09_tag a b A) b).w y = 0 :=
      Lane_q_s09_tag.restrictOr9_zero
        (maskedLaw9 Sbase (Lane_q_s09_tag.tagAnchorOutcome_q_s09_tag a b A) b)
        (hitSet9 E G (Lane_q_s09_tag.tagAnchorOutcome_q_s09_tag a b A) (I.seen b.1)) y hmasked
    simp [hrow]
  let pick (b : OddSites9 n) :=
    Classical.choose
      (Lane_q_s09_tag.finite_mask_minimax (siteSecond9 Sbase b.1) δ hδpos hδle (R b) (hR b))
  have hpick (b : OddSites9 n) (y : Fin N) :
      ∑ A, (pick b).w A * (R b A.1).w y ≤
        (1 + δ) * (siteSecond9 Sbase b.1).w y :=
    Classical.choose_spec
      (Lane_q_s09_tag.finite_mask_minimax (siteSecond9 Sbase b.1) δ hδpos hδle (R b) (hR b)) y
  let maskLaw : OddSites9 n → FinProb (Finset (Fin N)) :=
    fun b => FinProb.map (pick b) Subtype.val
  let Sfinal : Setup9 P n N M := ⟨tag, maskLaw⟩
  have hAction (b : OddSites9 n) (A : Finset (Fin N)) :
      Lane_q_s09_tag.tagActionLaw_q_s09_tag (I := I) Sfinal E G b A = R b A := by
    exact Lane_q_s09_tag.tagActionLaw_eq_of_tag_eq_q_s09_tag
      Sfinal Sbase E G b A rfl
  refine ⟨maskLaw, ?_⟩
  unfold MasksOK9
  constructor
  · intro b A hweight
    by_contra hnot
    have hno : ∀ a : {A : Finset (Fin N) // δ / 2 ≤
        Lane_q_s09_tag.maskMass (siteSecond9 Sbase b.1) A}, a.1 ≠ A := by
      intro a ha
      subst A
      exact hnot (by
        simpa [siteSecond9, δ, Lane_q_s09_tag.maskMass, div_eq_mul_inv, mul_comm] using a.property)
    have hzero : (FinProb.map (pick b) Subtype.val).w A = 0 := by
      simp only [FinProb.map]
      apply Finset.sum_eq_zero
      intro a _
      simp [hno a]
    exact hweight (by simpa [maskLaw] using hzero)
  · intro b y
    have hmap :
        ∑ A, (maskLaw b).w A * (R b A).w y =
          ∑ a, (pick b).w a * (R b a.1).w y := by
      calc
        ∑ A, (maskLaw b).w A * (R b A).w y =
            (FinProb.map (pick b) Subtype.val).expect (fun A => (R b A).w y) := rfl
        _ = (pick b).expect (fun a => (R b a.1).w y) :=
          FinProb.map_expect (pick b) Subtype.val (fun A => (R b A).w y)
        _ = _ := rfl
    have hmean :
        (rawRowLaw9 Sfinal I E G b).w y =
          ∑ a, (pick b).w a * (R b a.1).w y := by
      rw [Lane_q_s09_tag.rawRowLaw_eq_mask_mix_q_s09_tag (I := I) Sfinal E G b]
      simp only [Law.mix]
      calc
        ∑ A, (maskLaw b).w A *
            (Lane_q_s09_tag.tagActionLaw_q_s09_tag (I := I) Sfinal E G b A).w y =
            ∑ A, (maskLaw b).w A * (R b A).w y := by
          apply Finset.sum_congr rfl
          intro A hA
          rw [hAction]
        _ = ∑ a, (pick b).w a * (R b a.1).w y := hmap
    rw [hmean]
    simpa [Sfinal, Sbase, δ, siteSecond9] using hpick b y

end HypercubeRamsey
