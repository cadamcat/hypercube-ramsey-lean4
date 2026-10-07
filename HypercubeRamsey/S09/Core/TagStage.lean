import HypercubeRamsey.S09.Core.Experiment
import HypercubeRamsey.S09.Core.TagStage_q_s09_tag
import HypercubeRamsey.S07.TagStage
import HypercubeRamsey.Framework.Minimax

/-!
# Proposition 9.2, core: tags and masks (P9.2-tags)

Source: `sections/09-intermediate-powers-of-bias.tex`, lines 120–144; blueprint `research/blueprint/PART-B.md`
§3.9, P9.2-tags.  Tags are drawn independently from the mixture law, one per special word; in the linear case the
tag events `B_z` are avoided with Lemma 3.4 (`S07.cond_product_bound`); the tag loads follow from Lemma 3.6
(`scatteredMoments_union_labels`).  Masks are chosen row by row by convex separation (`finite_minimax`).
-/

namespace HypercubeRamsey

open OAI.HypercubeRamsey Classical
open scoped BigOperators

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
  refine ⟨1, by norm_num, 1, by norm_num, 0, ?_⟩
  intro n hn N E X Y G M hN hprep hdeep hbroad z
  cases hcase : P.case with
  | sub yS yD yM =>
      have ht : 0 ≤ P.tail 1 n := by
        rw [Params9.tail]
        exact Real.exp_nonneg _
      simpa [tagBad9, hcase, FinProb.pr] using ht
  | lin αS αD hB yB =>
      -- The linear case needs the broad-test degree estimate and conditional Hoeffding argument.
      sorry

set_option maxHeartbeats 0 in
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
