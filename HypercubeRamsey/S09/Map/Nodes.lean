import HypercubeRamsey.S09.Map.Device
import HypercubeRamsey.S09.Map.Nodes_q_s09_map

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
  rcases hP with ⟨hcommon, hminus, hx, hσ, hχ, hgap, hcase⟩
  rcases hσ with ⟨hσpos, hσsmall⟩
  rcases hχ with ⟨hχpos, hχsmall⟩
  have hχlt1 : (P.χ : ℝ) < 1 := by
    have hh : (P.hMinus : ℝ) < 1 := by
      exact_mod_cast lt_trans hminus.2.1 hminus.2.2
    have hmin : min (P.xS : ℝ) (min (P.hMinus : ℝ) (1 - (P.hPlus : ℝ))) < 1 := by
      apply lt_of_le_of_lt (min_le_right _ _)
      exact lt_of_le_of_lt (min_le_left _ _) hh
    have hcχ : (P.χ : ℝ) < min (P.xS : ℝ) (min (P.hMinus : ℝ) (1 - (P.hPlus : ℝ))) / 100 := by
      exact_mod_cast hχsmall
    linarith
  cases hc : P.case with
  | sub yS yD yM =>
      have hbranch : 0 < yS ∧ yS < yM ∧ yM < 1 - P.σ ∧ 1 - P.σ < yD ∧ yD < 1 ∧
          P.χ < P.σ / 10 := by simpa [hc] using hcase
      have heps : 0 < P.eps := by
        rw [Params9.eps, hc]
        apply div_pos
        apply lt_min
        · exact_mod_cast hσpos
        · have : (1 - P.σ : ℚ) < yD := hbranch.2.2.2.1
          exact_mod_cast sub_pos.mpr this
        · norm_num
      have hχr : 0 < (P.χ : ℝ) := by exact_mod_cast hχpos
      let b0 : ℝ := min (P.eps / 2) ((P.χ : ℝ) / 4)
      have hb0pos : 0 < b0 := by
        dsimp [b0]
        apply lt_min
        · linarith
        · positivity
      have hb0eps : b0 < P.eps := by
        have hb : b0 ≤ P.eps / 2 := min_le_left _ _
        linarith
      have hb0chi : b0 < (P.χ : ℝ) / 2 := by
        have hb : b0 ≤ (P.χ : ℝ) / 4 := min_le_right _ _
        linarith
      let hc' : HeightChoice9 P :=
        ⟨b0, (b0 + P.eps) / 2, b0 / 16, b0 / 64, 1 - b0 / 64, b0 / 2⟩
      refine ⟨hc', ?_⟩
      dsimp [HeightChoice9.Admissible, hc']
      constructor
      · positivity
      constructor
      · linarith
      constructor
      · linarith
      constructor
      · linarith [hb0chi, hχlt1]
      constructor
      · linarith
      constructor
      · norm_num
        linarith
      constructor
      · norm_num
        linarith
      constructor
      · nlinarith [hb0chi]
      constructor
      · exact hb0pos
      constructor
      · linarith
      constructor
      · linarith
      · simpa [hc] using hb0chi
  | lin αS αD hB yB =>
      have hbranch : 0 < 100 * αS ∧ 100 * αS < αD ∧ αD < 1 / 100 ∧
          P.σ < P.χ / 10 ∧ P.hPlus < hB ∧ hB < 1 ∧ 0 < yB ∧ yB < 1 := by
        simpa [hc] using hcase
      have heps : 0 < P.eps := by
        rw [Params9.eps, hc]
        exact div_pos (by exact_mod_cast hσpos) (by norm_num)
      have hσr : (P.σ : ℝ) < (P.χ : ℝ) / 10 := by exact_mod_cast hbranch.2.2.2.1
      have hχr : 0 < (P.χ : ℝ) := by exact_mod_cast hχpos
      let b0 : ℝ := min (P.eps / 2) (((P.χ : ℝ) / 2 - (P.σ : ℝ)) / 2)
      have hb0pos : 0 < b0 := by
        dsimp [b0]
        apply lt_min
        · linarith
        · linarith
      have hb0eps : b0 < P.eps := by
        have hb : b0 ≤ P.eps / 2 := min_le_left _ _
        linarith
      have hb0lin : b0 + (P.σ : ℝ) < (P.χ : ℝ) / 2 := by
        have hb : b0 ≤ ((P.χ : ℝ) / 2 - (P.σ : ℝ)) / 2 := min_le_right _ _
        linarith
      have hσrpos : 0 < (P.σ : ℝ) := by exact_mod_cast hσpos
      have hb0chi : b0 < (P.χ : ℝ) / 2 := by linarith [hb0lin, hσrpos]
      let hc' : HeightChoice9 P :=
        ⟨b0, (b0 + P.eps) / 2, b0 / 16, b0 / 64, 1 - b0 / 64, b0 / 2⟩
      refine ⟨hc', ?_⟩
      dsimp [HeightChoice9.Admissible, hc']
      constructor
      · positivity
      constructor
      · linarith
      constructor
      · linarith
      constructor
      · linarith [hb0chi, hχlt1]
      constructor
      · norm_num
        linarith
      constructor
      · norm_num
        linarith
      constructor
      · norm_num
        linarith
      constructor
      · nlinarith [hb0chi]
      constructor
      · exact hb0pos
      constructor
      · linarith
      constructor
      · linarith
      simpa [hc] using hb0lin

/-- P9.2-map1, base estimate (09:84–85, Lemma 3.8 Step 2): given an eligible set of size at least `s n^{10}`
within `C`, the activations of its members are independent of the positions, so a hole has probability at most
`(1 - n^{b₀-10})^{s n^{10}} ≤ exp(-s n^{b₀})`; each crowd count within `C` is at most the corresponding count over
all positions, binomial with mean `n^{b₀}`, `O(m n^{b₀} r/n)` and `O(n^{b₀} n/r)` (`V_{r-1}/V = O(r/n)`,
`V_{r+1}/V = O(n/r)`), a fixed power below its threshold even after the factor `t ≥ 1/3`; a union over the five
levels of the window. -/
theorem p92_height_base (P : Params9) (hP : P.Valid) (hc : HeightChoice9 P) (hadm : hc.Admissible) :
    ∃ c > (0 : ℝ), ∃ n₀ : ℕ, ∀ n ≥ n₀, HeightBase9 P hc n c := by
  rcases hadm with ⟨_, _, _, _, _, _, _, _, hbpos, _, _, _⟩
  refine ⟨hc.b₀ / 2, div_pos hbpos (by norm_num), 2, ?_⟩
  intro n hn
  have hn2 : 2 ≤ n := by omega
  -- The hole term has exponent `b₀`; the three crowd terms require the corresponding
  -- product-binomial upper tails after reducing restricted domains to `univ`.
  sorry

/-- P9.2-map1, position counts (09:85): each eligible-set size is binomial with mean `n^{10}` (`V` positions,
probability `n^{10}/V`); a Chernoff lower tail `e^{-n^{10}/8}` and a union over the `2^n (H+1)` site-levels
(`H = O(n^{1-ζ+σ_h})`). -/
theorem p92_height_counts (P : Params9) (hP : P.Valid) (hc : HeightChoice9 P) (hadm : hc.Admissible) :
    ∃ n₀ : ℕ, ∀ n ≥ n₀, HeightCounts9 P hc n := by
  obtain ⟨nV, hV⟩ := Lane_q_s09_map.height_counts9_volume_bounds P hP
  obtain ⟨nTail, hTail⟩ := Lane_q_s09_map.height_counts9_union_tail P hc hadm
  refine ⟨max 1 (max nV nTail), ?_⟩
  intro n hn
  have hn1 : 1 ≤ n := le_trans (le_max_left 1 _) hn
  have houter : max nV nTail ≤ n := le_trans (le_max_right 1 _) hn
  have hnV : nV ≤ n := le_trans (le_max_left nV nTail) houter
  have hnTail : nTail ≤ n := le_trans (le_max_right nV nTail) houter
  have hVn := hV n hnV
  have hTailn := hTail n hnTail
  have hnreal : 0 < (n : ℝ) := by exact_mod_cast (show 0 < n by omega)
  have hlam : 0 < (n : ℝ) ^ (10 : ℝ) := Real.rpow_pos_of_pos hnreal _
  exact Lane_q_s09_map.height_counts9_of_bounds P hc n hlam
    hVn.1 hVn.2.1 hVn.2.2 hTailn

/-- P9.2-map1, cross-slice overlap (09:86–92): a child domain of radius `R'` consults slices within `O(R')` and
residual locations within `r + O(R')`; for starts separated by `K R'` either the consulted slice ranges are
disjoint or the residual separation is `Ω(K R')`; if the residual balls meet, `R' = O(r)` and the shell and
hypergeometric estimates (`hypergeometric_intersection_tail`) bound the residual overlap fraction by
`exp(-Ω(K R' log n))`, while enumerating slices and enlarging balls costs `exp(O(R' log n))`; for large fixed `K`
the overlap at one level is at most `V e^{-c₀ R'}`. -/
theorem p92_height_overlap (P : Params9) (hP : P.Valid) (hc : HeightChoice9 P) (hadm : hc.Admissible) :
    ∃ K > (0 : ℝ), ∃ c₀ > (0 : ℝ), ∃ n₀ : ℕ, ∀ n ≥ n₀, HeightOverlap9 P hc n K c₀ := by
  refine ⟨16, by norm_num, 1, by norm_num, 2, ?_⟩
  intro n hn v v' R' j hR hsep
  have hlocal : ∀ c : Pos9 P hc n,
      c ∈ consulted9 (P := P) (hc := hc) (n := n) v R' ∩ consulted9 v' R' →
        _root_.hammingDist c.slice (specialWord9 (P.m n) v) ≤ 2 * R' + 1 ∧
        _root_.hammingDist c.slice (specialWord9 (P.m n) v') ≤ 2 * R' + 1 ∧
        _root_.hammingDist c.location (residualWord9 (P.m n) v) ≤ P.radius n + 2 * R' + 1 ∧
        _root_.hammingDist c.location (residualWord9 (P.m n) v') ≤ P.radius n + 2 * R' + 1 := by
    intro c hc
    exact Lane_q_s09_map.sharedConsulted_local_bounds v v' R' c hc
  -- The remaining estimate is the shell/hypergeometric bound for the two residual balls,
  -- combined with the count of consulted slices.
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
  classical
  rcases hP with ⟨_, _, _, _, ⟨hχpos, _⟩, _, _⟩
  have hχR : 0 < (P.χ : ℝ) := by exact_mod_cast hχpos
  refine ⟨1, ?_⟩
  intro n hn Pp A hgood
  have hnR : 1 ≤ (n : ℝ) := by exact_mod_cast hn
  have hχpow : 1 ≤ (n : ℝ) ^ (P.χ : ℝ) := Real.one_le_rpow hnR hχR.le
  let center := Lane_q_s09_map.chosenCenterOfGoodHeights Pp A hgood
  have hcenter v :
      (center v).slice = specialWord9 (P.m n) v ∧
        _root_.hammingDist (center v).location (residualWord9 (P.m n) v) ≤ P.radius n ∧
        (center v).level.val = height9 Pp A v ∧ activeAt9 Pp A (center v) := by
    simpa [center] using
      (Lane_q_s09_map.chosenCenterOfGoodHeights_spec (P := P) (hc := hc) (n := n)
        Pp A hgood v)
  let core : CubeVertex n → Finset (CenterID9 (P.m n) (n - P.m n) (hc.levels n)) :=
    fun v => {center v}
  refine ⟨⟨hc.levels n, center, ?_, ?_, ?_, core, ?_, ?_, ?_⟩⟩
  · intro v
    exact (hcenter v).1
  · intro v
    exact (hcenter v).2.1
  · intro b hbOdd
    sorry
  · intro v hvEven
    simp [core]
  · intro v hvEven
    simpa [core] using hχpow
  · intro v hvEven id hid
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
