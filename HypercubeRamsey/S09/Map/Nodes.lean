import HypercubeRamsey.S09.Map.Device

/-!
# Proposition 9.2: good heights and the ID map (P9.2-map1, P9.2-map2)

Source: `sections/09-intermediate-powers-of-bias.tex`, lines 63–118; blueprint `research/blueprint/PART-B.md`
§3.9, P9.2-map1 and P9.2-map2 (thin spot TS-B3).  The ID map is built once from an outcome of the adapted height
experiment with good heights and then fixed; it does not depend on the coloring.
-/

namespace HypercubeRamsey

open OAI.HypercubeRamsey Classical
open scoped BigOperators

/-- P9.2-map1, parameter choice (09:82–83, 09:96–98): admissible internal exponents exist for valid parameters
(take `θ` near `1`, then `ζ, σ_h` small, `a` between `ζ + σ_h + (1-θ)` and `b₀`, and `b₀ < ε' < ε` small in terms
of `χ`, using `σ < χ/10` in the linear case). -/
theorem p92_height_choice (P : Params9) (hP : P.Valid) : ∃ hc : HeightChoice9 P, hc.Admissible := by
  sorry

/-- P9.2-map1, base estimate (09:84–85, Lemma 3.8 Step 2): given an eligible set of size at least `s n^{10}`
within `C`, the activations of its members are independent of the positions, so a hole has probability at most
`(1 - n^{b₀-10})^{s n^{10}} ≤ exp(-s n^{b₀})`; each crowd count within `C` is at most the corresponding count over
all positions, binomial with mean `n^{b₀}`, `O(m n^{b₀} r/n)` and `O(n^{b₀} n/r)` (`V_{r-1}/V = O(r/n)`,
`V_{r+1}/V = O(n/r)`), a fixed power below its threshold even after the factor `t ≥ 1/3`; a union over the five
levels of the window. -/
theorem p92_height_base (P : Params9) (hP : P.Valid) (hc : HeightChoice9 P) (hadm : hc.Admissible) :
    ∃ c > (0 : ℝ), ∃ n₀ : ℕ, ∀ n ≥ n₀, HeightBase9 P hc n c := by
  sorry

/-- P9.2-map1, position counts (09:85): each eligible-set size is binomial with mean `n^{10}` (`V` positions,
probability `n^{10}/V`); a Chernoff lower tail `e^{-n^{10}/8}` and a union over the `2^n (H+1)` site-levels
(`H = O(n^{1-ζ+σ_h})`). -/
theorem p92_height_counts (P : Params9) (hP : P.Valid) (hc : HeightChoice9 P) (hadm : hc.Admissible) :
    ∃ n₀ : ℕ, ∀ n ≥ n₀, HeightCounts9 P hc n := by
  sorry

/-- P9.2-map1, cross-slice overlap (09:86–92): a child domain of radius `R'` consults slices within `O(R')` and
residual locations within `r + O(R')`; for starts separated by `K R'` either the consulted slice ranges are
disjoint or the residual separation is `Ω(K R')`; if the residual balls meet, `R' = O(r)` and the shell and
hypergeometric estimates (`hypergeometric_intersection_tail`) bound the residual overlap fraction by
`exp(-Ω(K R' log n))`, while enumerating slices and enlarging balls costs `exp(O(R' log n))`; for large fixed `K`
the overlap at one level is at most `V e^{-c₀ R'}`. -/
theorem p92_height_overlap (P : Params9) (hP : P.Valid) (hc : HeightChoice9 P) (hadm : hc.Admissible) :
    ∃ K > (0 : ℝ), ∃ c₀ > (0 : ℝ), ∃ n₀ : ℕ, ∀ n ≥ n₀, HeightOverlap9 P hc n K c₀ := by
  sorry

/-- P9.2-map1, scale induction (09:93–100): with degraded thresholds at successive scales for every crowd count
and the eligible-set size, deletion of overlaps to private child regions (holes are preserved; the loss of a count
fits the threshold gap unless an overlap holds too many centers, probability `exp(-Ω(n^{χ/2} R'/q))`), the base and
overlap estimates and independence on private regions run Lemma 3.8's induction (`scale_induction_step`) with
`0 < σ_h < ζ`, `b₀ > a > ζ + σ_h + (1-θ)`, `χ/2 > a + 4σ_h`; the radius-`(r+2)` crowd test of Lemma 3.8 is not
needed.  The base estimate is used uniformly in the center domain and on correct eligible sizes (`HeightCounts9`).
Some outcome has good heights. -/
theorem p92_height_induction (P : Params9) (hP : P.Valid) (hc : HeightChoice9 P) (hadm : hc.Admissible)
    (c K c₀ : ℝ) (hc0 : 0 < c) (hK : 0 < K) (hc₀ : 0 < c₀) :
    ∃ n₀ : ℕ, ∀ n ≥ n₀, HeightBase9 P hc n c → HeightCounts9 P hc n → HeightOverlap9 P hc n K c₀ →
      ∃ Pp A : Pos9 P hc n → Bool, GoodHeights9 Pp A := by
  sorry

/-- P9.2-map2 (09:102–112): from good heights choose an active eligible center at every site's height (no hole).
At an odd row the residual-flip neighbours use IDs of the row's slice within residual distance `r + 1` at levels
within `1` of the row's height (distance-two regularity), at most `3 n^{1-σ+ε'} ≤ n^{1-σ+ε}` by the
radius-`(r+1)` crowd test at the row itself; the special-flip neighbours add at most `m`.  At an even site the core
is the set of observed IDs (at sites within distance `2`) in the same-slice radius-`r` ball or an adjacent-slice
radius-`(r-1)` ball, together with the site's own ID; the two smaller crowd tests over the level window bound it by
`6 n^{χ/2} ≤ n^χ`; the identity `d_H(c, v'^{i,j}) = d_H(c, v') + 2 - 2(1_{i∈Δ} + 1_{j∈Δ})` gives the read bound
`r + 3`. -/
theorem p92_idmap_of_heights (P : Params9) (hP : P.Valid) (hc : HeightChoice9 P) (hadm : hc.Admissible) :
    ∃ n₀ : ℕ, ∀ n ≥ n₀, ∀ Pp A : Pos9 P hc n → Bool, GoodHeights9 Pp A → Nonempty (IDMap9 P n) := by
  sorry

/-- P9.2-map1 and P9.2-map2 assembled (09:63–118): for all large `n` the fixed ID map exists. -/
theorem p92_idmap (P : Params9) (hP : P.Valid) : ∃ n₀ : ℕ, ∀ n ≥ n₀, Nonempty (IDMap9 P n) := by
  obtain ⟨hc, hadm⟩ := p92_height_choice P hP
  obtain ⟨c, hc0, n₁, hbase⟩ := p92_height_base P hP hc hadm
  obtain ⟨K, hK, c₀, hc₀, n₂, hover⟩ := p92_height_overlap P hP hc hadm
  obtain ⟨n₃, hind⟩ := p92_height_induction P hP hc hadm c K c₀ hc0 hK hc₀
  obtain ⟨n₄, hmap⟩ := p92_idmap_of_heights P hP hc hadm
  obtain ⟨n₅, hcounts⟩ := p92_height_counts P hP hc hadm
  refine ⟨max (max n₁ n₂) (max n₃ (max n₄ n₅)), ?_⟩
  intro n hn
  obtain ⟨Pp, A, hgood⟩ :=
    hind n (by omega) (hbase n (by omega)) (hcounts n (by omega)) (hover n (by omega))
  exact hmap n (by omega) Pp A hgood

end HypercubeRamsey
