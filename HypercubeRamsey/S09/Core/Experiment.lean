import HypercubeRamsey.S09.Core.Scales
import HypercubeRamsey.S07.Experiment

/-!
# Proposition 9.2, core: the one-shot experiment and its named facts

Source: `sections/09-intermediate-powers-of-bias.tex`, lines 61 (prepared mixture), 120–144 (tags and masks),
146–294 (filters, regularity, conditional means, erasure, covariance, gain), 296–350 (predictive tests, anchor
avoidance, odd injection, even rows); blueprint `research/blueprint/PART-B.md` §3.9, P9.2-prep … P9.2-assignC.

Every object of the construction is an explicit finite formula of the prepared mixture `M`, the ID map `I`,
the tags and the mask laws (`Setup9`):

* the experiment: one anchor `W_c ∼ μ_{i_{z(c)}}` per ID and one mask per odd row, all independent
  (`rawLaw9`, 09:136–144);
* the odd row `p_b` (mask, then the hits of all distinct IDs seen at `b`, fallback the masked law), the deletion
  kernel at `b` for a target ID, and the target-last fraction `q_b` (09:136–138, 09:148–150, 09:301–303);
* the three fixed ID orders per star edge and their prefix tests (09:156–167);
* the outer filter `P_O` with its `.49^{|O|}` fallback, its mean `Q`, the core history, the clipped fraction
  `q̂_b` and its conditional mean given the core (09:171–184);
* the covariance at a core prefix (09:222–230), the star validity event `𝒱` (filter tests and (9.1));
* the predictive objects `F_x`, `M_v`, `P⁻`, predictive failure and the alarm (09:298–312), the star events
  and the anchor law (raw law conditioned on avoiding every star event, 09:312–320);
* odd and even column sums, the posterior even rows and their star integrals, the clock output (09:322–350).

Named facts (`RegularityCert9`, …, `ClockOK9`) are the conclusions of the nodes in `TagStage`, `GainStage`
and `AssignStage`; a node that needs another node's conclusion takes it as a hypothesis.  Tail constants are
explicit arguments: the paper's `exp(-Ω(n^u))` is `P.tail c n` for a constant `c > 0` produced by the node.
-/

namespace HypercubeRamsey

open OAI.HypercubeRamsey Classical
open scoped BigOperators

/-! ## Prepared mixture and fixed data -/

/-- P9.2-prep's output (09:61): a balanced mixture whose positive-weight patches are supported in `X × Y`, with
first width `n^{x_s} + h_+ log n + 1`, second width `S_s`, and minimum degree `1/2 + a_*` of every first
label into its second law in colour `G`.  This is literally the conclusion of `p92_patch_preparation`. -/
def Prep9 (P : Params9) (κ : ℝ) (n N : ℕ) (E : Fin N → Fin N → Prop) (X Y : Finset (Fin N))
    (G : Colour) (M : TagMix N) : Prop :=
  M.Balanced (8 / κ) ∧
  ∀ i, 0 < M.Λ i → (M.μ i).SupportedIn X ∧ (M.ν i).SupportedIn Y ∧
    (M.μ i).WidthLE ((n : ℝ) ^ (P.xS : ℝ) + (P.hPlus : ℝ) * Real.log (n : ℝ) + 1) ∧
    (M.ν i).WidthLE (P.Ss (n : ℝ)) ∧
    ∀ x, (M.μ i).w x ≠ 0 →
      1 / 2 + (n : ℝ) ^ (-(P.hPlus : ℝ)) / 2 ≤ rowDeg E G x (M.ν i)

/-- The mixture law of the tags (09:122). -/
noncomputable def tagMixLaw9 {N : ℕ} (M : TagMix N) : FinProb M.ι :=
  ⟨M.Λ, M.Λ_nonneg, M.Λ_sum⟩

/-- Fixed tags (one per special word, 09:122) and per-row mask laws (09:139–144).  Pure data: the required
properties are `TagsOK9` and `MasksOK9`, produced by the nodes `p92_tags` and `p92_masks`. -/
structure Setup9 (P : Params9) (n N : ℕ) (M : TagMix N) where
  tag : CubeVertex (P.m n) → M.ι
  maskLaw : OddSites9 n → FinProb (Finset (Fin N))

variable {P : Params9} {n N : ℕ} {M : TagMix N}

/-- The tagged first law of a site, `μ_{i_{z(v)}}`. -/
noncomputable def siteFirst9 (S : Setup9 P n N M) (v : CubeVertex n) : Law N :=
  M.μ (S.tag (specialWord9 (P.m n) v))

/-- The tagged second law of a site, `ν_{i_{z(b)}}`. -/
noncomputable def siteSecond9 (S : Setup9 P n N M) (b : CubeVertex n) : Law N :=
  M.ν (S.tag (specialWord9 (P.m n) b))

/-! ## The independent experiment (09:136–144) -/

/-- The values of the experiment's variables: an anchor label for every ID, a mask for every odd row. -/
def Val9 (I : IDMap9 P n) (N : ℕ) : I.ID ⊕ OddSites9 n → Type
  | .inl _ => Fin N
  | .inr _ => Finset (Fin N)

instance instFintypeVal9 (I : IDMap9 P n) (N : ℕ) : ∀ v, Fintype (Val9 I N v)
  | .inl _ => inferInstanceAs (Fintype (Fin N))
  | .inr _ => inferInstanceAs (Fintype (Finset (Fin N)))

instance instDecEqVal9 (I : IDMap9 P n) (N : ℕ) : ∀ v, DecidableEq (Val9 I N v)
  | .inl _ => inferInstanceAs (DecidableEq (Fin N))
  | .inr _ => inferInstanceAs (DecidableEq (Finset (Fin N)))

/-- An outcome: all anchors and all masks. -/
abbrev Outcome9 (I : IDMap9 P n) (N : ℕ) := ∀ v : I.ID ⊕ OddSites9 n, Val9 I N v

variable {I : IDMap9 P n}

/-- The anchor `W_c` of an ID. -/
def anc9 (ω : Outcome9 I N) (c : I.ID) : Fin N := ω (Sum.inl c)

/-- The mask of an odd row. -/
def msk9 (ω : Outcome9 I N) (b : OddSites9 n) : Finset (Fin N) := ω (Sum.inr b)

/-- Replace the anchor of the ID `t` by `x`. -/
noncomputable def updAnc9 (ω : Outcome9 I N) (t : I.ID) (x : Fin N) : Outcome9 I N :=
  Function.update ω (Sum.inl t) (show Val9 I N (Sum.inl t) from x)

/-- The input laws: `W_c ∼ μ_{i_{z(c)}}` (09:136) and the row's mask law. -/
noncomputable def inputLaw9 (S : Setup9 P n N M) (I : IDMap9 P n) :
    ∀ v : I.ID ⊕ OddSites9 n, FinProb (Val9 I N v)
  | .inl c => M.μ (S.tag c.slice)
  | .inr b => S.maskLaw b

/-- The raw experiment: all anchors and masks independent (09:136–144, 09:146–147). -/
noncomputable def rawLaw9 (S : Setup9 P n N M) (I : IDMap9 P n) : FinProb (Outcome9 I N) :=
  FinProb.pi (inputLaw9 S I)

/-! ## Filters (09:136–150, 09:301–303) -/

/-- Restriction of a law to a set, the law itself when the set has mass zero. -/
noncomputable def restrictOr9 (μ : Law N) (A : Finset (Fin N)) : Law N :=
  if h : 0 < ∑ x ∈ A, μ.w x then μ.restrict A h else μ

/-- The second labels hitting (in colour `G`) the anchors of every ID in `ids`. -/
noncomputable def hitSet9 (E : Fin N → Fin N → Prop) (G : Colour) (ω : Outcome9 I N)
    (ids : Finset I.ID) : Finset (Fin N) :=
  Finset.univ.filter (fun y => ∀ c ∈ ids, Hits E G (anc9 ω c) y)

/-- The masked law at an odd row: `ν_{i_{z(b)}}` restricted to the sampled mask (09:137). -/
noncomputable def maskedLaw9 (S : Setup9 P n N M) (ω : Outcome9 I N) (b : OddSites9 n) : Law N :=
  restrictOr9 (siteSecond9 S b.1) (msk9 ω b)

/-- The odd row `p_b` (09:137–138): the masked law restricted to labels hitting the anchors at every distinct ID
seen at `b`; on an empty filter, the masked law. -/
noncomputable def rowLaw9 (S : Setup9 P n N M) (E : Fin N → Fin N → Prop) (G : Colour)
    (ω : Outcome9 I N) (b : OddSites9 n) : Law N :=
  restrictOr9 (maskedLaw9 S ω b) (hitSet9 E G ω (I.seen b.1))

/-- The deletion kernel at `b` for the target ID `t` (09:301–303): the same filter without the hit of `t`;
on an empty filter, the masked law (a fallback that does not read `W_t`). -/
noncomputable def delLaw9 (S : Setup9 P n N M) (E : Fin N → Fin N → Prop) (G : Colour)
    (ω : Outcome9 I N) (b : OddSites9 n) (t : I.ID) : Law N :=
  restrictOr9 (maskedLaw9 S ω b) (hitSet9 E G ω ((I.seen b.1).erase t))

/-- The odd neighbours of an even site (the rows of its star). -/
abbrev StarOdd9 (v : EvenSites9 n) := {b : OddSites9 n // (cube n).Adj v.1 b.1}

/-- The target-last fraction `q_b` (09:148–150): the fraction of the deletion kernel retained by the hit of
`W_* = W_{c(v)}`. -/
noncomputable def targetFrac9 (S : Setup9 P n N M) (E : Fin N → Fin N → Prop) (G : Colour)
    (ω : Outcome9 I N) (v : EvenSites9 n) (b : OddSites9 n) : ℝ :=
  rowDeg E G (anc9 ω (I.center v.1)) (delLaw9 S E G ω b (I.center v.1))

/-! ## Regularity tests (09:156–167) -/

/-- The outer IDs `O_b = I_b \ C_v` (09:171–173). -/
noncomputable def outerIDs9 (I : IDMap9 P n) (v : EvenSites9 n) (b : OddSites9 n) : Finset I.ID :=
  I.seen b.1 \ I.core v.1

/-- The core IDs other than the target, `D_b \ {c(v)}` (09:171–175). -/
noncomputable def coreIDs9 (I : IDMap9 P n) (v : EvenSites9 n) (b : OddSites9 n) : Finset I.ID :=
  (I.seen b.1 ∩ I.core v.1).erase (I.center v.1)

/-- The full ID order of a star edge (09:157–159): outer IDs, core IDs other than `c(v)`, then `c(v)`, each
block in the fixed order of `Finset.toList`. -/
noncomputable def fullOrder9 (I : IDMap9 P n) (v : EvenSites9 n) (b : OddSites9 n) : List I.ID :=
  (outerIDs9 I v b).toList ++ (coreIDs9 I v b).toList ++ [I.center v.1]

/-- The core order (09:160–161): the core IDs other than `c(v)`. -/
noncomputable def coreOrder9 (I : IDMap9 P n) (v : EvenSites9 n) (b : OddSites9 n) : List I.ID :=
  (coreIDs9 I v b).toList

/-- The prefix law after the first `k` hits of an order, from a starting law. -/
noncomputable def prefixLaw9 (E : Fin N → Fin N → Prop) (G : Colour) (ω : Outcome9 I N)
    (base : Law N) (order : List I.ID) (k : ℕ) : Law N :=
  restrictOr9 base (hitSet9 E G ω (order.take k).toFinset)

/-- The sequential tests of one order (09:162–167): at every prefix whose preceding hits each retained at least
`.49`, the next hit fraction is `1/2 ± 2b_*`. -/
def orderRegular9 (E : Fin N → Fin N → Prop) (G : Colour) (ω : Outcome9 I N) (base : Law N)
    (order : List I.ID) : Prop :=
  ∀ k c, order[k]? = some c →
    (∀ j c', j < k → order[j]? = some c' →
      (49 / 100 : ℝ) ≤ rowDeg E G (anc9 ω c') (prefixLaw9 E G ω base order j)) →
    |rowDeg E G (anc9 ω c) (prefixLaw9 E G ω base order k) - 1 / 2| ≤ 2 * P.bStar n

/-- The filter tests of a star (09:157–161): at every odd neighbour, the full order from the masked law and from
the unmasked law, and the core order from the unmasked law. -/
def starRegular9 (S : Setup9 P n N M) (E : Fin N → Fin N → Prop) (G : Colour) (ω : Outcome9 I N)
    (v : EvenSites9 n) : Prop :=
  ∀ b : OddSites9 n, (cube n).Adj v.1 b.1 →
    orderRegular9 E G ω (maskedLaw9 S ω b) (fullOrder9 I v b) ∧
    orderRegular9 E G ω (siteSecond9 S b.1) (fullOrder9 I v b) ∧
    orderRegular9 E G ω (siteSecond9 S b.1) (coreOrder9 I v b)

/-- The log-gain of a star, `∑_{b∼v} log q_b` (09:150). -/
noncomputable def starGain9 (S : Setup9 P n N M) (E : Fin N → Fin N → Prop) (G : Colour)
    (ω : Outcome9 I N) (v : EvenSites9 n) : ℝ :=
  ∑ b : StarOdd9 v, Real.log (targetFrac9 S E G ω v b.1)

/-- The star validity event `𝒱` (09:146–150, 09:298–302): the filter tests and the log-gain bound (9.1). -/
def starValid9 (S : Setup9 P n N M) (E : Fin N → Fin N → Prop) (G : Colour) (ω : Outcome9 I N)
    (v : EvenSites9 n) : Prop :=
  starRegular9 S E G ω v ∧
    -(n : ℝ) * Real.log 2 + gainConst9 * n * P.aStar n ≤ starGain9 S E G ω v

/-! ## Conditioning on the core (09:171–220) -/

/-- The outer filter `P_O` (09:176–177): the masked law filtered by the outer hits, with the width-preserving
fallback (the masked law) when the retained mass is below `.49^{|O|}`. -/
noncomputable def outerFilter9 (S : Setup9 P n N M) (E : Fin N → Fin N → Prop) (G : Colour)
    (ω : Outcome9 I N) (v : EvenSites9 n) (b : OddSites9 n) : Law N :=
  if (49 / 100 : ℝ) ^ (outerIDs9 I v b).card ≤
      ∑ y ∈ hitSet9 E G ω (outerIDs9 I v b), (maskedLaw9 S ω b).w y then
    restrictOr9 (maskedLaw9 S ω b) (hitSet9 E G ω (outerIDs9 I v b))
  else maskedLaw9 S ω b

/-- `Q = E P_O` (09:177–178), averaging the outer anchors and the row's mask; it does not depend on the core. -/
noncomputable def outerMean9 (S : Setup9 P n N M) (I : IDMap9 P n) (E : Fin N → Fin N → Prop)
    (G : Colour) (v : EvenSites9 n) (b : OddSites9 n) : Law N :=
  Law.mix (rawLaw9 S I) (fun ω => outerFilter9 S E G ω v b)

/-- `J_-` (09:175): the labels hitting the core anchors of `b` other than the target. -/
noncomputable def coreHitSet9 (E : Fin N → Fin N → Prop) (G : Colour) (ω : Outcome9 I N)
    (v : EvenSites9 n) (b : OddSites9 n) : Finset (Fin N) :=
  hitSet9 E G ω (coreIDs9 I v b)

/-- The number `k = |D_b|` of core IDs seen at `b` (09:174). -/
noncomputable def coreCount9 (I : IDMap9 P n) (v : EvenSites9 n) (b : OddSites9 n) : ℕ :=
  (I.seen b.1 ∩ I.core v.1).card

/-- Two outcomes share the core history of `v`: equal anchors on `C_v` (09:174). -/
def sameCore9 (I : IDMap9 P n) (v : EvenSites9 n) (ω₀ ω : Outcome9 I N) : Prop :=
  ∀ c ∈ I.core v.1, anc9 ω c = anc9 ω₀ c

/-- The clipped fraction `q̂_b = clip(q_b)` to `[1/2 - 2b_*, 1/2 + 2b_*]` (09:179–180); invalid filters are
handled by the fallbacks of the deletion kernel, which read only this filter's inputs. -/
noncomputable def clippedFrac9 (S : Setup9 P n N M) (E : Fin N → Fin N → Prop) (G : Colour)
    (ω : Outcome9 I N) (v : EvenSites9 n) (b : OddSites9 n) : ℝ :=
  max (1 / 2 - 2 * P.bStar n) (min (1 / 2 + 2 * P.bStar n) (targetFrac9 S E G ω v b))

/-- `E[q̂_b | W_{C_v}]` at the core history of `ω₀` (09:181–184). -/
noncomputable def condCoreMean9 (S : Setup9 P n N M) (I : IDMap9 P n) (E : Fin N → Fin N → Prop)
    (G : Colour) (v : EvenSites9 n) (b : OddSites9 n) (ω₀ : Outcome9 I N) : ℝ :=
  (rawLaw9 S I).condExp (fun ω => clippedFrac9 S E G ω v b) (sameCore9 I v ω₀)

/-- The conditional probability of an event given the core history of `ω₀`. -/
noncomputable def condCorePr9 (S : Setup9 P n N M) (I : IDMap9 P n) (v : EvenSites9 n)
    (ω₀ : Outcome9 I N) (A : Outcome9 I N → Prop) : ℝ :=
  (rawLaw9 S I).condExp (fun ω => if A ω then 1 else 0) (sameCore9 I v ω₀)

/-- The colour-`G` adjacency indicator `g_x(y)` (09:224). -/
noncomputable def hitInd9 (E : Fin N → Fin N → Prop) (G : Colour) (x y : Fin N) : ℝ :=
  if Hits E G x y then 1 else 0

/-- The covariance `cov_λ(g_w, g_{W_*})` at the `k`-th prefix `λ` of the unmasked core order, `w` the next
core anchor (09:222–230); zero past the end of the order. -/
noncomputable def coreCov9 (S : Setup9 P n N M) (E : Fin N → Fin N → Prop) (G : Colour)
    (ω : Outcome9 I N) (v : EvenSites9 n) (b : OddSites9 n) (k : ℕ) : ℝ :=
  match (coreOrder9 I v b)[k]? with
  | none => 0
  | some c =>
      let lam := prefixLaw9 E G ω (siteSecond9 S b.1) (coreOrder9 I v b) k
      let x := anc9 ω (I.center v.1)
      lam.expect (fun y => hitInd9 E G (anc9 ω c) y * hitInd9 E G x y) -
        lam.expect (hitInd9 E G (anc9 ω c)) * lam.expect (hitInd9 E G x)

/-! ## Tags and masks (09:120–144) -/

/-- The special-neighbour surplus `∑_{j ≤ m} (d_G(w, ν_{i_{z^j}}) - 1/2)` (09:125–127). -/
noncomputable def tagSurplus9 (E : Fin N → Fin N → Prop) (G : Colour)
    (tag : CubeVertex (P.m n) → M.ι) (z : CubeVertex (P.m n)) (w : Fin N) : ℝ :=
  ∑ j : Fin (P.m n), (rowDeg E G w (M.ν (tag (flipWord9 z j))) - 1 / 2)

/-- `E_z`: the first labels whose special-neighbour surplus is below `-.05 a_* n` (09:125–127, 09:133). -/
noncomputable def tagFail9 (E : Fin N → Fin N → Prop) (G : Colour)
    (tag : CubeVertex (P.m n) → M.ι) (z : CubeVertex (P.m n)) : Finset (Fin N) :=
  Finset.univ.filter (fun w => tagSurplus9 E G tag z w < -((1 / 20 : ℝ) * P.aStar n * n))

/-- `B_z = {μ_{i_z}(E_z) > e^{-c n^u}}` in the linear case (09:133–135); no tag events in the sublinear case. -/
def tagBad9 (E : Fin N → Fin N → Prop) (G : Colour) (c : ℝ) (tag : CubeVertex (P.m n) → M.ι)
    (z : CubeVertex (P.m n)) : Prop :=
  match P.case with
  | .sub _ _ _ => False
  | .lin _ _ _ _ => P.tail c n < ∑ w ∈ tagFail9 E G tag z, (M.μ (tag z)).w w

/-- The scope of `B_z`: the tag at `z` and at its special neighbours (09:135–136). -/
noncomputable def tagScope9 (z : CubeVertex (P.m n)) : Finset (CubeVertex (P.m n)) :=
  insert z (Finset.univ.image (flipWord9 z))

/-- The tag law (09:136–138): raw independent tags conditioned on avoiding every `B_z`. -/
noncomputable def tagLaw9 (P : Params9) (n : ℕ) (M : TagMix N) (E : Fin N → Fin N → Prop)
    (G : Colour) (c : ℝ) : FinProb (CubeVertex (P.m n) → M.ι) :=
  S07.condOr (FinProb.pi (fun _ => tagMixLaw9 M)) (fun tag => ∀ z, ¬ tagBad9 (P := P) E G c tag z)

/-- The local-lemma input for the tag events (09:135–137): scope `{z} ∪ {z^j}`, dependency degree
`(m+1)²`, charge `e^{-c' n^u}`. -/
def TagLLL9 (P : Params9) (n : ℕ) (M : TagMix N) (E : Fin N → Fin N → Prop) (G : Colour)
    (c c' : ℝ) : Prop :=
  S07.LLLInput (fun _ : CubeVertex (P.m n) => tagMixLaw9 M)
    (fun z tag => tagBad9 (P := P) E G c tag z) tagScope9 (P.tail c' n) ((P.m n + 1) ^ 2)

/-- The constant of the tag loads (09:122–124): `4·K·(D₀+1)` of `scatteredMoments_union_labels` with `K = 2`
(the avoidance comparison) and `D₀ = 8/κ` (the balance of the prepared mixture). -/
noncomputable def tagLoadConst9 (κ : ℝ) : ℝ := 8 * (8 / κ + 1)

/-- Normalized pointwise tag loads (09:122): the average over special words of `N μ_{i_z}` and `N ν_{i_z}` is at
most `K` at every label. -/
def tagLoadOK9 (M : TagMix N) {m : ℕ} (tag : CubeVertex m → M.ι) (K : ℝ) : Prop :=
  (∀ x, ((2 : ℝ) ^ m)⁻¹ * ∑ z, (N : ℝ) * (M.μ (tag z)).w x ≤ K) ∧
  (∀ y, ((2 : ℝ) ^ m)⁻¹ * ∑ z, (N : ℝ) * (M.ν (tag z)).w y ≤ K)

/-- The fixed tags of 09:137–138: in the support of the mixture, with the tag loads, and avoiding every `B_z`
(the linear tag condition 09:125–127 with exceptional mass `e^{-c n^u}`). -/
def TagsOK9 (κ : ℝ) (E : Fin N → Fin N → Prop) (G : Colour) (c : ℝ)
    (tag : CubeVertex (P.m n) → M.ι) : Prop :=
  (∀ z, 0 < M.Λ (tag z)) ∧ tagLoadOK9 M tag (tagLoadConst9 κ) ∧
    ∀ z, ¬ tagBad9 (P := P) E G c tag z

/-- The unconditional mean `R_b = E p_b` of an odd row (09:142–144). -/
noncomputable def rawRowLaw9 (S : Setup9 P n N M) (I : IDMap9 P n) (E : Fin N → Fin N → Prop)
    (G : Colour) (b : OddSites9 n) : Law N :=
  Law.mix (rawLaw9 S I) (fun ω => rowLaw9 S E G ω b)

/-- The mask laws of 09:139–144: every mask has `ν`-mass at least `½ e^{-n^u}`, and the unconditional row mean
satisfies `R_b ≤ (1 + e^{-n^u}) ν` pointwise. -/
def MasksOK9 (S : Setup9 P n N M) (I : IDMap9 P n) (E : Fin N → Fin N → Prop) (G : Colour) : Prop :=
  (∀ b A, (S.maskLaw b).w A ≠ 0 →
    (1 / 2 : ℝ) * Real.exp (-(n : ℝ) ^ P.u) ≤ ∑ y ∈ A, (siteSecond9 S b.1).w y) ∧
  ∀ b y, (rawRowLaw9 S I E G b).w y ≤ (1 + Real.exp (-(n : ℝ) ^ P.u)) * (siteSecond9 S b.1).w y

/-! ## Predictive tests, star events and the anchor law (09:296–320) -/

/-- The neighbour labels of an even site under an odd assignment. -/
def nbrLabels9 {v : EvenSites9 n} (f : OddSites9 n → Fin N) : StarOdd9 v → Fin N :=
  fun b => f b.1

/-- The data sublikelihood `F_x(y) = 1_𝒱 ∏_{b∼v} p_b(y_b)` with `W_* = x` (09:298–300). -/
noncomputable def starLik9 (S : Setup9 P n N M) (E : Fin N → Fin N → Prop) (G : Colour)
    (ω : Outcome9 I N) (v : EvenSites9 n) (x : Fin N) (ys : StarOdd9 v → Fin N) : ℝ :=
  (if starValid9 S E G (updAnc9 ω (I.center v.1) x) v then 1 else 0) *
    ∏ b : StarOdd9 v, (rowLaw9 S E G (updAnc9 ω (I.center v.1) x) b.1).w (ys b)

/-- `M_v = ∫ F_x dμ_{i_z}(x)` (09:305). -/
noncomputable def starMarg9 (S : Setup9 P n N M) (E : Fin N → Fin N → Prop) (G : Colour)
    (ω : Outcome9 I N) (v : EvenSites9 n) (ys : StarOdd9 v → Fin N) : ℝ :=
  ∑ x, (siteFirst9 S v.1).w x * starLik9 S E G ω v x ys

/-- `P⁻`: the product of the deletion kernels (09:301–303). -/
noncomputable def starRef9 (S : Setup9 P n N M) (E : Fin N → Fin N → Prop) (G : Colour)
    (ω : Outcome9 I N) (v : EvenSites9 n) (ys : StarOdd9 v → Fin N) : ℝ :=
  ∏ b : StarOdd9 v, (delLaw9 S E G ω b.1 (I.center v.1)).w (ys b)

/-- Predictive failure (09:306–307): `M_v = 0` or `M_v < e^{-c₄ n a_*/4} P⁻`. -/
def predFail9 (S : Setup9 P n N M) (E : Fin N → Fin N → Prop) (G : Colour) (ω : Outcome9 I N)
    (v : EvenSites9 n) (ys : StarOdd9 v → Fin N) : Prop :=
  starMarg9 S E G ω v ys = 0 ∨
    starMarg9 S E G ω v ys < Real.exp (-(gainConst9 * n * P.aStar n / 4)) * starRef9 S E G ω v ys

/-- The alarm `1_𝒱 Pr_{∏ p_b}(predictive failure)` at the actual anchors (09:309–312). -/
noncomputable def alarm9 (S : Setup9 P n N M) (E : Fin N → Fin N → Prop) (G : Colour)
    (ω : Outcome9 I N) (v : EvenSites9 n) : ℝ :=
  ∑ ys : StarOdd9 v → Fin N, starLik9 S E G ω v (anc9 ω (I.center v.1)) ys *
    (if predFail9 S E G ω v ys then 1 else 0)

/-- The star event (09:296–312): filter tests or (9.1) fail, or the alarm exceeds `e^{-c₄ n a_*/8}`. -/
def StarBad9 (S : Setup9 P n N M) (E : Fin N → Fin N → Prop) (G : Colour) (ω : Outcome9 I N)
    (v : EvenSites9 n) : Prop :=
  ¬ starValid9 S E G ω v ∨ Real.exp (-(gainConst9 * n * P.aStar n / 8)) < alarm9 S E G ω v

/-- The variables read by the star event of `v` (09:314–316): the anchors of every ID seen at an odd
neighbour, and the masks of the odd neighbours. -/
noncomputable def starScope9 (I : IDMap9 P n) (v : EvenSites9 n) : Finset (I.ID ⊕ OddSites9 n) :=
  (Finset.univ.filter (fun b : OddSites9 n => (cube n).Adj v.1 b.1)).biUnion
    (fun b => (I.seen b.1).image Sum.inl ∪ {Sum.inr b})

/-- The dependency degree of the star events, `(n+1)^{2r+8}` (09:314–316: poly(n) e^{O(r log n)}). -/
noncomputable def lllDegree9 (P : Params9) (n : ℕ) : ℕ := (n + 1) ^ (2 * P.radius n + 8)

/-- The local-lemma input for the star events with charge `e^{-c n^u}` (09:314–318). -/
def AnchorLLL9 (S : Setup9 P n N M) (I : IDMap9 P n) (E : Fin N → Fin N → Prop) (G : Colour)
    (c : ℝ) : Prop :=
  S07.LLLInput (inputLaw9 S I) (fun v ω => StarBad9 S E G ω v) (starScope9 I) (P.tail c n)
    (lllDegree9 P n)

/-- The anchor law (09:312–320): the raw experiment conditioned on avoiding every star event. -/
noncomputable def anchorLaw9 (S : Setup9 P n N M) (I : IDMap9 P n) (E : Fin N → Fin N → Prop)
    (G : Colour) : FinProb (Outcome9 I N) :=
  S07.condOr (rawLaw9 S I) (fun ω => ∀ v, ¬ StarBad9 S E G ω v)

/-! ## Column sums, the clock output and the even rows (09:322–350) -/

/-- Sites near each other for the scattered-moment estimates (09:324–326, 09:337–338): special words within
distance 4 and residual words within distance `4r + 8`. -/
def siteNear9 (P : Params9) (n : ℕ) (u w : CubeVertex n) : Prop :=
  _root_.hammingDist (specialWord9 (P.m n) u) (specialWord9 (P.m n) w) ≤ 4 ∧
    _root_.hammingDist (residualWord9 (P.m n) u) (residualWord9 (P.m n) w) ≤ 4 * P.radius n + 8

/-- The odd column sum at a second label (09:322). -/
noncomputable def oddColumn9 (S : Setup9 P n N M) (E : Fin N → Fin N → Prop) (G : Colour)
    (ω : Outcome9 I N) (y : Fin N) : ℝ :=
  ∑ b : OddSites9 n, (rowLaw9 S E G ω b).w y

/-- A successful prehistory (09:327–329): an outcome of the raw experiment (positive raw weight, so every mask is
an allowed mask and every anchor lies in its law's support) with no star event and odd column sums at most
`θ₀ = 10⁻⁸`. -/
def GoodPre9 (S : Setup9 P n N M) (E : Fin N → Fin N → Prop) (G : Colour) (ω : Outcome9 I N) :
    Prop :=
  (rawLaw9 S I).w ω ≠ 0 ∧ (∀ v, ¬ StarBad9 S E G ω v) ∧ ∀ y, oddColumn9 S E G ω y ≤ (1e-8 : ℝ)

/-- The clock-sampler output (09:327–329, Lemma 3.10 with `B = 3`): injective odd labels avoiding every
predictive failure, with joint upper comparison at most twice the product of the odd rows on sets of at most
`n³` odd sites. -/
def ClockOK9 (S : Setup9 P n N M) (E : Fin N → Fin N → Prop) (G : Colour) (ω : Outcome9 I N)
    (J : FinProb (OddSites9 n → Fin N)) : Prop :=
  (∀ f, J.w f ≠ 0 → Function.Injective f ∧
      ∀ v : EvenSites9 n, ¬ predFail9 S E G ω v (nbrLabels9 f)) ∧
    ∀ (T : Finset (OddSites9 n)) (o : OddSites9 n → Fin N), (T.card : ℝ) ≤ (n : ℝ) ^ 3 →
      J.pr (fun f => ∀ b ∈ T, f b = o b) ≤ 2 * ∏ b ∈ T, (rowLaw9 S E G ω b).w (o b)

/-- The posterior even row `F_x dμ_{i_z}(x)/M_v` at neighbour data `ys` (09:333). -/
noncomputable def evenRowAt9 (S : Setup9 P n N M) (E : Fin N → Fin N → Prop) (G : Colour)
    (ω : Outcome9 I N) (v : EvenSites9 n) (ys : StarOdd9 v → Fin N) (x : Fin N) : ℝ :=
  starLik9 S E G ω v x ys * (siteFirst9 S v.1).w x / starMarg9 S E G ω v ys

/-- The posterior even row at an odd assignment. -/
noncomputable def evenRow9 (S : Setup9 P n N M) (E : Fin N → Fin N → Prop) (G : Colour)
    (ω : Outcome9 I N) (f : OddSites9 n → Fin N) (v : EvenSites9 n) (x : Fin N) : ℝ :=
  evenRowAt9 S E G ω v (nbrLabels9 f) x

/-- The even column sum at a first label (09:349–350). -/
noncomputable def evenColumn9 (S : Setup9 P n N M) (E : Fin N → Fin N → Prop) (G : Colour)
    (ω : Outcome9 I N) (f : OddSites9 n → Fin N) (x : Fin N) : ℝ :=
  ∑ v : EvenSites9 n, evenRow9 S E G ω f v x

/-- The star integral of one even site (09:339–346): independent neighbour draws from the actual rows with the
true local star gate kept (`starLik9` at the actual target anchor is `1_𝒱 ∏ p_b`), predictive success retained,
times the normalized posterior row at `x`.  On the anchor law every gate is open. -/
noncomputable def evenStar9 (S : Setup9 P n N M) (E : Fin N → Fin N → Prop) (G : Colour)
    (ω : Outcome9 I N) (v : EvenSites9 n) (x : Fin N) : ℝ :=
  ∑ ys : StarOdd9 v → Fin N, starLik9 S E G ω v (anc9 ω (I.center v.1)) ys *
    ((if predFail9 S E G ω v ys then 0 else 1) * ((N : ℝ) * evenRowAt9 S E G ω v ys x))

/-! ## Named facts: the gain stage (09:156–294) -/

/-- The forward and reverse degree tests (09:162–169), consequences of `DeepAt` (nodes `deep_forward9`,
`deep_reverse9`): against a second law within the deep budget, a first law of width `w ≤ n^{x_d}` gives mass at
most `2 e^{w - n^{x_d}}` to first labels whose degree is not `1/2 ± 2b_*`; against a first law within the deep
budget, a second law of width `s ≤ S_d` gives mass at most `2 e^{s - S_d}` to second labels whose degree is not
`1/2 ± 2b_*`. -/
def DeepTools9 (P : Params9) (n N : ℕ) (E : Fin N → Fin N → Prop) (X Y : Finset (Fin N)) : Prop :=
  (∀ (G : Colour) (lam : Law N), lam.SupportedIn Y → lam.WidthLE (P.Sd (n : ℝ)) →
    ∀ (α : Law N), α.SupportedIn X → ∀ w : ℝ, α.WidthLE w → w ≤ (n : ℝ) ^ (P.xD : ℝ) →
      ∑ x ∈ Finset.univ.filter (fun x => 2 * P.bStar n < |rowDeg E G x lam - 1 / 2|), α.w x ≤
        2 * Real.exp (w - (n : ℝ) ^ (P.xD : ℝ))) ∧
  (∀ (G : Colour) (σ : Law N), σ.SupportedIn X → σ.WidthLE ((n : ℝ) ^ (P.xD : ℝ)) →
    ∀ (lam : Law N), lam.SupportedIn Y → ∀ s : ℝ, lam.WidthLE s → s ≤ P.Sd (n : ℝ) →
      ∑ y ∈ Finset.univ.filter (fun y => 2 * P.bStar n < |colDeg E G σ y - 1 / 2|), lam.w y ≤
        2 * Real.exp (s - P.Sd (n : ℝ)))

/-- The standing hypotheses of the core nodes at one dimension: a nonempty host side, the prepared mixture,
deep discrepancy and its degree tests, tags of positive mixture weight, the mask laws of 09:139–144, and the
scale facts of `Core.Scales`. -/
def CoreInput9 (P : Params9) (κ : ℝ) {n N : ℕ} (E : Fin N → Fin N → Prop) (X Y : Finset (Fin N))
    (G : Colour) (M : TagMix N) (S : Setup9 P n N M) (I : IDMap9 P n) : Prop :=
  0 < N ∧ Prep9 P κ n N E X Y G M ∧ P.DeepAt n N E X Y ∧ (∀ z, 0 < M.Λ (S.tag z)) ∧
    MasksOK9 S I E G ∧ DeepTools9 P n N E X Y ∧ ScaleExps9 P ∧ ScalesAt9 P n

/-- P9.2-reg's conclusion: the filter tests of each star fail with raw probability at most `e^{-c n^u}`. -/
def RegularityCert9 (S : Setup9 P n N M) (I : IDMap9 P n) (E : Fin N → Fin N → Prop) (G : Colour)
    (c : ℝ) : Prop :=
  ∀ v : EvenSites9 n, (rawLaw9 S I).pr (fun ω => ¬ starRegular9 S E G ω v) ≤ P.tail c n

/-- P9.2-condmean's conclusion (09:181–184): outside core histories of raw mass `e^{-c n^u}`,
`E[q̂_b | W_{C_v}] = d_G(W_*; Q|_{J_-}) ± (C k b_*² + e^{-c n^u})`. -/
def CondMeanCert9 (S : Setup9 P n N M) (I : IDMap9 P n) (E : Fin N → Fin N → Prop) (G : Colour)
    (C c : ℝ) : Prop :=
  ∀ (v : EvenSites9 n) (b : OddSites9 n), (cube n).Adj v.1 b.1 →
    (rawLaw9 S I).pr (fun ω₀ =>
      C * (coreCount9 I v b : ℝ) * P.bStar n ^ 2 + P.tail c n <
        |condCoreMean9 S I E G v b ω₀ -
          rowDeg E G (anc9 ω₀ (I.center v.1))
            (restrictOr9 (outerMean9 S I E G v b) (coreHitSet9 E G ω₀ v b))|) ≤ P.tail c n

/-- P9.2-erase, first part (09:186–208): `Q = (1 + ψ) ν + err` with a pointwise multiplier `|ψ| ≤ C k b_*` and
`‖err‖₁ ≤ e^{-c n^u}`, all independent of the core data. -/
def EraseCert9 (S : Setup9 P n N M) (I : IDMap9 P n) (E : Fin N → Fin N → Prop) (G : Colour)
    (C c : ℝ) : Prop :=
  ∀ (v : EvenSites9 n) (b : OddSites9 n), (cube n).Adj v.1 b.1 →
    ∃ ψ : Fin N → ℝ, (∀ y, |ψ y| ≤ C * (coreCount9 I v b : ℝ) * P.bStar n) ∧
      ∑ y, |(outerMean9 S I E G v b).w y - (1 + ψ y) * (siteSecond9 S b.1).w y| ≤ P.tail c n

/-- P9.2-erase, second part (09:209–220): replacing `Q|_{J_-}` by `ν|_{J_-}` in the target degree costs
`C k b_*²`, outside raw probability `e^{-c n^u}`. -/
def ReplaceCert9 (S : Setup9 P n N M) (I : IDMap9 P n) (E : Fin N → Fin N → Prop) (G : Colour)
    (C c : ℝ) : Prop :=
  ∀ (v : EvenSites9 n) (b : OddSites9 n), (cube n).Adj v.1 b.1 →
    (rawLaw9 S I).pr (fun ω =>
      C * (coreCount9 I v b : ℝ) * P.bStar n ^ 2 <
        |rowDeg E G (anc9 ω (I.center v.1))
            (restrictOr9 (outerMean9 S I E G v b) (coreHitSet9 E G ω v b)) -
          rowDeg E G (anc9 ω (I.center v.1))
            (restrictOr9 (siteSecond9 S b.1) (coreHitSet9 E G ω v b))|) ≤ P.tail c n

/-- P9.2-cov's conclusion (09:226–262): at every prefix of the unmasked core order the covariance has magnitude
at most `a_* n^{-2χ}`, outside raw probability `e^{-c n^u}`. -/
def CovCert9 (S : Setup9 P n N M) (I : IDMap9 P n) (E : Fin N → Fin N → Prop) (G : Colour)
    (c : ℝ) : Prop :=
  ∀ (v : EvenSites9 n) (b : OddSites9 n), (cube n).Adj v.1 b.1 → ∀ k : ℕ,
    (rawLaw9 S I).pr (fun ω =>
      P.aStar n * (n : ℝ) ^ (-(2 * (P.χ : ℝ))) < |coreCov9 S E G ω v b k|) ≤ P.tail c n

/-- The effect of the core hits (09:264–268): `d_G(W_*; ν|_{J_-})` and `d_G(W_*; ν)` differ by at most
`3 a_* n^{-χ}` (at most `k ≤ n^χ` hits, each shifting the degree by `cov/d_G(w; λ)` with denominator `≥ .49`),
outside raw probability `e^{-c n^u}`. -/
def CoreHitCert9 (S : Setup9 P n N M) (I : IDMap9 P n) (E : Fin N → Fin N → Prop) (G : Colour)
    (c : ℝ) : Prop :=
  ∀ (v : EvenSites9 n) (b : OddSites9 n), (cube n).Adj v.1 b.1 →
    (rawLaw9 S I).pr (fun ω =>
      3 * P.aStar n * (n : ℝ) ^ (-(P.χ : ℝ)) <
        |rowDeg E G (anc9 ω (I.center v.1))
            (restrictOr9 (siteSecond9 S b.1) (coreHitSet9 E G ω v b)) -
          rowDeg E G (anc9 ω (I.center v.1)) (siteSecond9 S b.1)|) ≤ P.tail c n

/-- The combined mean comparison (09:266–268): `E[q̂_b | W_{C_v}] = d_G(W_*; ν_{i_{z(b)}}) ± a_*/100`, outside
core histories of raw mass `e^{-c n^u}`. -/
def MeanCert9 (S : Setup9 P n N M) (I : IDMap9 P n) (E : Fin N → Fin N → Prop) (G : Colour)
    (c : ℝ) : Prop :=
  ∀ (v : EvenSites9 n) (b : OddSites9 n), (cube n).Adj v.1 b.1 →
    (rawLaw9 S I).pr (fun ω₀ =>
      P.aStar n / 100 <
        |condCoreMean9 S I E G v b ω₀ - rowDeg E G (anc9 ω₀ (I.center v.1)) (siteSecond9 S b.1)|) ≤
      P.tail c n

/-- The surplus of the conditional means (09:270–274): `∑_{b∼v} E[q̂_b | W_{C_v}] ≥ n/2 + (9/10) n a_*`,
outside core histories of raw mass `e^{-c n^u}`. -/
def GainMeanCert9 (S : Setup9 P n N M) (I : IDMap9 P n) (E : Fin N → Fin N → Prop) (G : Colour)
    (c : ℝ) : Prop :=
  ∀ v : EvenSites9 n, (rawLaw9 S I).pr (fun ω₀ =>
    ∑ b : StarOdd9 v, condCoreMean9 S I E G v b.1 ω₀ <
      (n : ℝ) / 2 + (9 / 10 : ℝ) * n * P.aStar n) ≤ P.tail c n

/-- P9.2-gain's conclusion (09:146–154): the star validity event fails with raw probability at most
`e^{-c n^u}`. -/
def GainCert9 (S : Setup9 P n N M) (I : IDMap9 P n) (E : Fin N → Fin N → Prop) (G : Colour)
    (c : ℝ) : Prop :=
  ∀ v : EvenSites9 n, (rawLaw9 S I).pr (fun ω => ¬ starValid9 S E G ω v) ≤ P.tail c n

/-! ## Named facts: the assignment stage (09:296–350) -/

/-- The mean alarm over the target anchor (09:305–310): `E_{W_*} alarm ≤ e^{-c₄ n a_*/4}`, all other inputs
fixed. -/
def AlarmMean9 (S : Setup9 P n N M) (I : IDMap9 P n) (E : Fin N → Fin N → Prop) (G : Colour) :
    Prop :=
  ∀ (ω : Outcome9 I N) (v : EvenSites9 n),
    ∑ x, (siteFirst9 S v.1).w x * alarm9 S E G (updAnc9 ω (I.center v.1) x) v ≤
      Real.exp (-(gainConst9 * n * P.aStar n / 4))

/-- Locality of the star events (09:314–316): each reads only its scope, and at most `(n+1)^{2r+8}` other star
events have a scope meeting it. -/
def StarScopeFacts9 (S : Setup9 P n N M) (I : IDMap9 P n) (E : Fin N → Fin N → Prop) (G : Colour) :
    Prop :=
  (∀ v : EvenSites9 n, FinProb.DependsOn (fun ω : Outcome9 I N => StarBad9 S E G ω v) (starScope9 I v)) ∧
  ∀ v : EvenSites9 n, (Finset.univ.filter (fun v' : EvenSites9 n =>
    v' ≠ v ∧ ¬ Disjoint (starScope9 I v) (starScope9 I v'))).card ≤ lllDegree9 P n

/-- Row widths on valid stars (09:162, 09:323): at an outcome of the raw experiment (so every mask is allowed)
where every star passes its filter tests, every odd row has normalized cap `e^{S_d}`. -/
def RowCap9 (S : Setup9 P n N M) (I : IDMap9 P n) (E : Fin N → Fin N → Prop) (G : Colour) : Prop :=
  ∀ ω : Outcome9 I N, (rawLaw9 S I).w ω ≠ 0 → (∀ v, starRegular9 S E G ω v) →
    ∀ b y, (N : ℝ) * (rowLaw9 S E G ω b).w y ≤ Real.exp (P.Sd (n : ℝ))

/-- Separated odd-row products under the anchor law (09:324–327). -/
def OddMoment9 (S : Setup9 P n N M) (I : IDMap9 P n) (E : Fin N → Fin N → Prop) (G : Colour) :
    Prop :=
  ∀ (y : Fin N) (k : ℕ), k ≤ n → ∀ s : Fin k → OddSites9 n,
    (∀ i j : Fin k, j < i → ¬ siteNear9 P n (s i).1 (s j).1) →
    (anchorLaw9 S I E G).expect (fun ω => ∏ i, (N : ℝ) * (rowLaw9 S E G ω (s i)).w y) ≤
      2 ^ k * ∏ i, (N : ℝ) * (rawRowLaw9 S I E G (s i)).w y

/-- `F_x ≤ 2^n e^{-c₄ n a_*} P⁻` (09:303–304). -/
def StarLikBound9 (S : Setup9 P n N M) (I : IDMap9 P n) (E : Fin N → Fin N → Prop) (G : Colour) :
    Prop :=
  ∀ (ω : Outcome9 I N) (v : EvenSites9 n) (x : Fin N) (ys : StarOdd9 v → Fin N),
    starLik9 S E G ω v x ys ≤
      (2 : ℝ) ^ n * Real.exp (-(gainConst9 * n * P.aStar n)) * starRef9 S E G ω v ys

/-- On predictive success the posterior even row is a probability law on the common neighbours of the odd
labels (09:331–333, 09:349–350). -/
def EvenRowLaw9 (S : Setup9 P n N M) (I : IDMap9 P n) (E : Fin N → Fin N → Prop) (G : Colour) :
    Prop :=
  ∀ (ω : Outcome9 I N) (f : OddSites9 n → Fin N) (v : EvenSites9 n),
    ¬ predFail9 S E G ω v (nbrLabels9 f) →
      (∀ x, 0 ≤ evenRow9 S E G ω f v x) ∧ (∑ x, evenRow9 S E G ω f v x = 1) ∧
      ∀ x, evenRow9 S E G ω f v x ≠ 0 → ∀ b : OddSites9 n, (cube n).Adj v.1 b.1 → Hits E G x (f b)

/-- The normalized cap of the posterior rows on predictive success, `2^n e^{-c₄ n a_*/2}` (09:333–335). -/
def EvenRowCap9 (S : Setup9 P n N M) (I : IDMap9 P n) (E : Fin N → Fin N → Prop) (G : Colour) :
    Prop :=
  ∀ (ω : Outcome9 I N) (v : EvenSites9 n) (ys : StarOdd9 v → Fin N), ¬ predFail9 S E G ω v ys →
    ∀ x, (N : ℝ) * evenRowAt9 S E G ω v ys x ≤ (2 : ℝ) ^ n * Real.exp (-(gainConst9 * n * P.aStar n / 2))

/-- The star cancellation (09:342–346): integrating the target anchor gives at most `N μ_{i_z}(x)`. -/
def StarCancel9 (S : Setup9 P n N M) (I : IDMap9 P n) (E : Fin N → Fin N → Prop) (G : Colour) :
    Prop :=
  ∀ (ω : Outcome9 I N) (v : EvenSites9 n) (x : Fin N),
    ∑ x', (siteFirst9 S v.1).w x' * evenStar9 S E G (updAnc9 ω (I.center v.1) x') v x ≤
      (N : ℝ) * (siteFirst9 S v.1).w x

/-- The clock comparison for separated even sites (09:337–341). -/
def ClockFactor9 (S : Setup9 P n N M) (I : IDMap9 P n) (E : Fin N → Fin N → Prop) (G : Colour)
    (J : Outcome9 I N → FinProb (OddSites9 n → Fin N)) : Prop :=
  ∀ ω, GoodPre9 S E G ω → ∀ (x : Fin N) (k : ℕ), k ≤ n → ∀ a : Fin k → EvenSites9 n,
    (∀ i j : Fin k, j < i → ¬ siteNear9 P n (a i).1 (a j).1) →
    ∑ f, (J ω).w f * ∏ i, (N : ℝ) * evenRow9 S E G ω f (a i) x ≤ 2 * ∏ i, evenStar9 S E G ω (a i) x

/-- The anchor integral of separated star integrals (09:341–347). -/
def EvenAnchorIntegral9 (S : Setup9 P n N M) (I : IDMap9 P n) (E : Fin N → Fin N → Prop)
    (G : Colour) : Prop :=
  ∀ (x : Fin N) (k : ℕ), k ≤ n → ∀ a : Fin k → EvenSites9 n,
    (∀ i j : Fin k, j < i → ¬ siteNear9 P n (a i).1 (a j).1) →
    (anchorLaw9 S I E G).expect (fun ω => ∏ i, evenStar9 S E G ω (a i) x) ≤
      2 ^ k * ∏ i, (N : ℝ) * (siteFirst9 S (a i).1).w x

/-- Separated even-row products under the anchor law and the clock sampler (09:347–349). -/
def EvenMoment9 (S : Setup9 P n N M) (I : IDMap9 P n) (E : Fin N → Fin N → Prop) (G : Colour)
    (J : Outcome9 I N → FinProb (OddSites9 n → Fin N)) : Prop :=
  ∀ (x : Fin N) (k : ℕ), k ≤ n → ∀ a : Fin k → EvenSites9 n,
    (∀ i j : Fin k, j < i → ¬ siteNear9 P n (a i).1 (a j).1) →
    ∑ ω, (anchorLaw9 S I E G).w ω *
        (if GoodPre9 S E G ω then ∑ f, (J ω).w f * ∏ i, (N : ℝ) * evenRow9 S E G ω f (a i) x else 0) ≤
      4 ^ k * ∏ i, (N : ℝ) * (siteFirst9 S (a i).1).w x

end HypercubeRamsey
