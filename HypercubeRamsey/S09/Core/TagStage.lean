import HypercubeRamsey.S09.Core.Experiment
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
  sorry

/-- P9.2-tags(ii) (09:135–137): the tag events satisfy the local-lemma input with charge `e^{-c' n^u/2}`:
`B_z` reads the tags on `{z} ∪ {z^j}` (`tagScope9`), two events meet only within special distance two (at
most `(m+1)²` others), and `e^{-c' n^u} ≤ x (1 - x)^{(m+1)²}` with `x = e^{-c' n^u/2}` for large `n`. -/
theorem p92_tag_lll (P : Params9) (hP : P.Valid) (c c' : ℝ) (hc : 0 < c) (hc' : 0 < c') :
    ∃ n₀ : ℕ, ∀ n ≥ n₀, ∀ {N : ℕ} (M : TagMix N) (E : Fin N → Fin N → Prop) (G : Colour),
      (∀ z : CubeVertex (P.m n),
        (FinProb.pi (fun _ : CubeVertex (P.m n) => tagMixLaw9 M)).pr
          (fun tag => tagBad9 (P := P) E G c tag z) ≤ P.tail c' n) →
      TagLLL9 P n M E G c (c' / 2) := by
  sorry

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
  sorry

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
  sorry

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
  sorry

end HypercubeRamsey
