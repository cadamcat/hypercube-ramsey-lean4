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
  rcases hadm with ⟨_, _, _, _, _, _, _, _, hbpos, hbε, hε, _⟩
  rcases hP with ⟨hcommon, _, _, hσ, _, _, _⟩
  rcases hσ with ⟨_, hσsmall⟩
  have hσlt1 : (P.σ : ℝ) < 1 := by
    have hxS : P.xS < 1 := lt_trans hcommon.2.1 (lt_trans hcommon.2.2 (by norm_num))
    have hσlt1q : P.σ < 1 := by linarith
    exact_mod_cast hσlt1q
  have hεlt1 : P.eps < 1 := by
    cases hbranch : P.case with
    | sub yS yD yM =>
        simp [Params9.eps, hbranch]
        have hmin : min (P.σ : ℝ) ((yD : ℝ) - (1 - (P.σ : ℝ))) ≤ (P.σ : ℝ) := min_le_left _ _
        nlinarith
    | lin αS αD hB yB =>
        simp [Params9.eps, hbranch]
        linarith
  have hb0lt1 : hc.b₀ < 1 := lt_trans hbε (lt_trans hε hεlt1)
  refine ⟨hc.b₀ / 2, div_pos hbpos (by norm_num), 2, ?_⟩
  intro n hn
  have hn2 : 2 ≤ n := by omega
  have hnreal : 0 < (n : ℝ) := by exact_mod_cast (show 0 < n by omega)
  have hnR : 1 ≤ (n : ℝ) := by exact_mod_cast (show 1 ≤ n by omega)
  have hqexp : hc.b₀ - 10 ≤ 0 := by linarith
  have hq0 : 0 ≤ (n : ℝ) ^ (hc.b₀ - 10) := Real.rpow_nonneg hnreal.le _
  have hq1 : (n : ℝ) ^ (hc.b₀ - 10) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos hnR hqexp
  have hqpow : (n : ℝ) ^ (hc.b₀ - 10) * (n : ℝ) ^ (10 : ℝ) = (n : ℝ) ^ hc.b₀ := by
    rw [← Real.rpow_add hnreal]
    congr 1
    ring
  have _hHoleBound (C : Finset (Pos9 P hc n)) (s : ℝ) (hs : 0 ≤ s)
      (v : CubeVertex n) (j : Fin (hc.levels n + 1)) :=
    Lane_q_s09_map.height_hole_probability_bound C s hs v j hq0 hq1 hqpow
  -- `hHoleBound` proves the activation tail uniformly in `C`, conditional on its eligible
  -- set size. The remaining work is the three crowd upper tails and their union estimate.
  have hFinal : HeightBase9 P hc n (hc.b₀ / 2) := by
    sorry
  exact hFinal

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
  obtain ⟨nGeom, hGeom⟩ := Lane_q_s09_map.height_counts9_special_le_n P hP
  refine ⟨16, by norm_num, 1, by norm_num, max 2 nGeom, ?_⟩
  intro n hn v v' R' j hR hsep
  have hn2 : 2 ≤ n := le_trans (le_max_left 2 nGeom) hn
  have hnGeom : nGeom ≤ n := le_trans (le_max_right 2 nGeom) hn
  have hmle : P.m n ≤ n := hGeom n hnGeom
  have hlocal : ∀ c : Pos9 P hc n,
      c ∈ consulted9 (P := P) (hc := hc) (n := n) v R' ∩ consulted9 v' R' →
        _root_.hammingDist c.slice (specialWord9 (P.m n) v) ≤ 2 * R' + 1 ∧
        _root_.hammingDist c.slice (specialWord9 (P.m n) v') ≤ 2 * R' + 1 ∧
        _root_.hammingDist c.location (residualWord9 (P.m n) v) ≤ P.radius n + 2 * R' + 1 ∧
        _root_.hammingDist c.location (residualWord9 (P.m n) v') ≤ P.radius n + 2 * R' + 1 := by
    intro c hc
    exact Lane_q_s09_map.sharedConsulted_local_bounds v v' R' c hc
  have _hresidualSeparation (c : Pos9 P hc n)
      (hshared : c ∈ consulted9 (P := P) (hc := hc) (n := n) v R' ∩ consulted9 v' R') :
      12 * R' - 2 ≤
        _root_.hammingDist (residualWord9 (P.m n) v) (residualWord9 (P.m n) v') :=
    Lane_q_s09_map.sharedConsulted_residual_separation hmle v v' R' hsep c hshared
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
  obtain ⟨nGeom, hGeom⟩ := Lane_q_s09_map.height_counts9_special_le_n P hP
  obtain ⟨nBudget, hBudget⟩ := Lane_q_s09_map.height_counts9_budget_slack P hc hadm
  obtain ⟨nCore, hCoreSlack⟩ := Lane_q_s09_map.height_counts9_core_slack P hP
  rcases hP with ⟨_, _, _, _, ⟨hχpos, _⟩, _, _⟩
  have hχR : 0 < (P.χ : ℝ) := by exact_mod_cast hχpos
  refine ⟨max 1 (max nGeom (max nBudget nCore)), ?_⟩
  intro n hn Pp A hgood
  have houter : max nGeom (max nBudget nCore) ≤ n := le_trans (le_max_right 1 _) hn
  have hinner : max nBudget nCore ≤ n := le_trans (le_max_right nGeom _) houter
  have hnGeom : nGeom ≤ n := le_trans (le_max_left nGeom _) houter
  have hnBudget : nBudget ≤ n := le_trans (le_max_left nBudget nCore) hinner
  have hnCore : nCore ≤ n := le_trans (le_max_right nBudget nCore) hinner
  have hmle : P.m n ≤ n := hGeom n hnGeom
  have hbudget : 3 * (n : ℝ) ^ (1 - (P.σ : ℝ) + hc.eps') ≤ P.idBudget n :=
    hBudget n hnBudget
  have hcoreSlack := hCoreSlack n hnCore
  have hn1 : 1 ≤ n := le_trans (le_max_left 1 _) hn
  have hnR : 1 ≤ (n : ℝ) := by exact_mod_cast hn1
  have hχpow : 1 ≤ (n : ℝ) ^ (P.χ : ℝ) := Real.one_le_rpow hnR hχR.le
  let center := Lane_q_s09_map.chosenCenterOfGoodHeights Pp A hgood
  have hcenter v :
      (center v).slice = specialWord9 (P.m n) v ∧
        _root_.hammingDist (center v).location (residualWord9 (P.m n) v) ≤ P.radius n ∧
        (center v).level.val = height9 Pp A v ∧ activeAt9 Pp A (center v) := by
    simpa [center] using
      (Lane_q_s09_map.chosenCenterOfGoodHeights_spec (P := P) (hc := hc) (n := n)
        Pp A hgood v)
  let sameLayer : CubeVertex n → Fin (hc.levels n + 1) → Finset (Pos9 P hc n) :=
    fun v j => Finset.univ.filter (fun c => activeAt9 Pp A c ∧
      c.slice = specialWord9 (P.m n) v ∧
      _root_.hammingDist c.location (residualWord9 (P.m n) v) ≤ P.radius n ∧ c.level = j)
  let adjLayer : CubeVertex n → Fin (hc.levels n + 1) → Finset (Pos9 P hc n) :=
    fun v j => Finset.univ.filter (fun c => activeAt9 Pp A c ∧
      _root_.hammingDist c.slice (specialWord9 (P.m n) v) = 1 ∧
      _root_.hammingDist c.location (residualWord9 (P.m n) v) ≤ P.radius n - 1 ∧ c.level = j)
  let levelWindow : CubeVertex n → Finset (Fin (hc.levels n + 1)) :=
    fun v => Finset.univ.filter (fun j => Nat.dist j.val (height9 Pp A v) ≤ 1)
  let core : CubeVertex n → Finset (CenterID9 (P.m n) (n - P.m n) (hc.levels n)) :=
    fun v => (levelWindow v).biUnion (fun j => sameLayer v j ∪ adjLayer v j)
  refine ⟨⟨hc.levels n, center, ?_, ?_, ?_, core, ?_, ?_, ?_⟩⟩
  · intro v
    exact (hcenter v).1
  · intro v
    exact (hcenter v).2.1
  · intro b hbOdd
    classical
    let m := P.m n
    let special := specialWord9 m b
    let residual := residualWord9 m b
    let N : Finset (CubeVertex n) := Finset.univ.filter fun w => (cube n).Adj b w
    let Special : Finset (CubeVertex n) := Finset.univ.filter fun w =>
      _root_.hammingDist b w = 1 ∧
        _root_.hammingDist special (specialWord9 m w) = 1
    let Residual : Finset (CubeVertex n) := Finset.univ.filter fun w =>
      _root_.hammingDist b w = 1 ∧
        _root_.hammingDist special (specialWord9 m w) = 0
    have hcover : N ⊆ Special ∪ Residual := by
      intro w hw
      have hfull : _root_.hammingDist b w = 1 := by
        have hadj := (Finset.mem_filter.mp hw).2
        simpa [OAI.HypercubeRamsey.cube] using hadj
      have hproj := Lane_q_s09_map.specialProjectionDist_le hmle b w
      have hprojle : _root_.hammingDist special (specialWord9 m w) ≤ 1 := by
        dsimp [special, m]
        omega
      by_cases hs : _root_.hammingDist special (specialWord9 m w) = 1
      · apply Finset.mem_union_left
        exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, ⟨hfull, hs⟩⟩
      · have hs0 : _root_.hammingDist special (specialWord9 m w) = 0 := by omega
        apply Finset.mem_union_right
        exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, ⟨hfull, hs0⟩⟩
    have hSeenEq : seenIDs9 center b = N.image center := by
      rfl
    have hSeenSubset : seenIDs9 center b ⊆ Special.image center ∪ Residual.image center := by
      rw [hSeenEq]
      apply Finset.image_subset_iff.mpr
      intro w hw
      rcases Finset.mem_union.mp (hcover hw) with hS | hR
      · exact Finset.mem_union_left _ (Finset.mem_image.mpr ⟨w, hS, rfl⟩)
      · exact Finset.mem_union_right _ (Finset.mem_image.mpr ⟨w, hR, rfl⟩)
    have hSpecialCard : Special.card ≤ m := by
      simpa [Special, special, m] using
        (Lane_q_s09_map.special_neighbor_count_le hmle b)
    have hSpecialIDs : (Special.image center).card ≤ m :=
      (Finset.card_image_le).trans hSpecialCard
    rcases hgood b with ⟨hbelow, hgoodNoBad, hregular⟩
    let j₀ : Fin (hc.levels n + 1) := ⟨height9 Pp A b, by omega⟩
    have hnotbad : ¬ badAt9 Pp A b j₀ := by simpa [j₀] using hgoodNoBad
    let J : Finset (Fin (hc.levels n + 1)) := Finset.univ.filter fun j =>
      Nat.dist j.val (height9 Pp A b) ≤ 1
    let values : Finset ℕ := {height9 Pp A b - 1, height9 Pp A b, height9 Pp A b + 1}
    have hJimage : J.image Fin.val ⊆ values := by
      intro k hk
      rcases Finset.mem_image.mp hk with ⟨j, hj, rfl⟩
      have hwindow := (Finset.mem_filter.mp hj).2
      unfold Nat.dist at hwindow
      simp only [values, Finset.mem_insert, Finset.mem_singleton]
      omega
    have hJcard : J.card ≤ 3 := by
      calc
        J.card = (J.image Fin.val).card :=
          (Finset.card_image_of_injective _ Fin.val_injective).symm
        _ ≤ values.card := Finset.card_le_card hJimage
        _ ≤ 3 := by
          simpa [values] using
            (Finset.card_le_three : ({height9 Pp A b - 1, height9 Pp A b,
              height9 Pp A b + 1} : Finset ℕ).card ≤ 3)
    let crowdAt : Fin (hc.levels n + 1) → Finset (Pos9 P hc n) := fun j =>
      Finset.univ.filter (fun c => activeAt9 Pp A c ∧ c.slice = special ∧
        _root_.hammingDist c.location residual ≤ P.radius n + 1 ∧ c.level = j)
    have hcrowd (j : Fin (hc.levels n + 1)) (hj : j ∈ J) :
        ((crowdAt j).card : ℝ) ≤ (n : ℝ) ^ (1 - (P.σ : ℝ) + hc.eps') := by
      by_contra hlarge
      have hstrict : (n : ℝ) ^ (1 - (P.σ : ℝ) + hc.eps') <
          ((crowdAt j).card : ℝ) := lt_of_not_ge hlarge
      have hstrict' : (n : ℝ) ^ (1 - (P.σ : ℝ) + hc.eps') <
          (crowdSame9 Finset.univ Pp A b j (P.radius n + 1) : ℝ) := by
        simpa [crowdAt, special, residual, crowdSame9] using hstrict
      have hdist : Nat.dist j₀.val j.val ≤ 2 := by
        have hwin := (Finset.mem_filter.mp hj).2
        simpa [j₀, Nat.dist_comm] using (le_trans hwin (by omega : 1 ≤ 2))
      have hbad : badAt9 Pp A b j₀ := by
        apply (show badIn9 Finset.univ 1 Pp A b j₀ from ?_)
        exact Or.inr ⟨j, hdist, Or.inr (Or.inr (by simpa [one_mul] using hstrict'))⟩
      exact hnotbad hbad
    have hResidualSubset : Residual.image center ⊆ J.biUnion crowdAt := by
      intro id hid
      rcases Finset.mem_image.mp hid with ⟨w, hw, rfl⟩
      rcases Finset.mem_filter.mp hw with ⟨_, ⟨hfull, hspecial0⟩⟩
      rcases Lane_q_s09_map.adjacent_projection_classification hmle b w hfull with hspecial | hresidual
      · have hs0 : _root_.hammingDist special (specialWord9 m w) = 0 := by
          simpa [special, m] using hspecial0
        have hs1 : _root_.hammingDist special (specialWord9 m w) = 1 := by
          simpa [special, m] using hspecial.1
        omega
      · have hslice : (center w).slice = special := by
          exact (hcenter w).1.trans hresidual.1.symm
        have hloc : _root_.hammingDist (center w).location residual ≤ P.radius n + 1 := by
          have hres1 : _root_.hammingDist (residualWord9 m b) (residualWord9 m w) = 1 := by
            simpa [m] using hresidual.2
          have hflip : _root_.hammingDist (residualWord9 m w) residual ≤ 1 := by
            simpa [residual, hammingDist_comm] using hres1.le
          calc
            _ ≤ _ := _root_.hammingDist_triangle (center w).location
              (residualWord9 m w) residual
            _ ≤ P.radius n + 1 := Nat.add_le_add (hcenter w).2.1 hflip
        let j : Fin (hc.levels n + 1) := (center w).level
        have hlev : Nat.dist j.val (height9 Pp A b) ≤ 1 := by
          have hreg := hregular w (by rw [hfull]; omega)
          simpa [j, (hcenter w).2.2.1, Nat.dist_comm] using hreg
        have hj : j ∈ J := Finset.mem_filter.mpr ⟨Finset.mem_univ _, hlev⟩
        have hc : center w ∈ crowdAt j := by
          simp only [crowdAt, Finset.mem_filter, Finset.mem_univ, true_and]
          exact ⟨(hcenter w).2.2.2, hslice, hloc, rfl⟩
        exact Finset.mem_biUnion.mpr ⟨j, hj, hc⟩
    have hResidualCard : ((Residual.image center).card : ℝ) ≤
        3 * (n : ℝ) ^ (1 - (P.σ : ℝ) + hc.eps') := by
      calc
        ((Residual.image center).card : ℝ) ≤ ((J.biUnion crowdAt).card : ℝ) := by
          exact_mod_cast Finset.card_le_card hResidualSubset
        _ ≤ ∑ j ∈ J, (crowdAt j).card := by exact_mod_cast Finset.card_biUnion_le
        _ = ∑ j ∈ J, ((crowdAt j).card : ℝ) := by norm_cast
        _ ≤ ∑ _j ∈ J, (n : ℝ) ^ (1 - (P.σ : ℝ) + hc.eps') := by
          apply Finset.sum_le_sum
          intro j hj
          exact hcrowd j hj
        _ = (J.card : ℝ) * (n : ℝ) ^ (1 - (P.σ : ℝ) + hc.eps') := by simp
        _ ≤ 3 * (n : ℝ) ^ (1 - (P.σ : ℝ) + hc.eps') := by
          gcongr
          exact_mod_cast hJcard
    have hseenCard : (seenIDs9 center b).card ≤
        (Special.image center).card + (Residual.image center).card := by
      calc
        (seenIDs9 center b).card ≤ (Special.image center ∪ Residual.image center).card :=
          Finset.card_le_card hSeenSubset
        _ ≤ (Special.image center).card + (Residual.image center).card :=
          Finset.card_union_le _ _
    have hseenReal : ((seenIDs9 center b).card : ℝ) ≤
        (P.m n : ℝ) + 3 * (n : ℝ) ^ (1 - (P.σ : ℝ) + hc.eps') := by
      calc
        ((seenIDs9 center b).card : ℝ) ≤
            ((Special.image center).card : ℝ) + ((Residual.image center).card : ℝ) := by
              exact_mod_cast hseenCard
        _ ≤ (P.m n : ℝ) + 3 * (n : ℝ) ^ (1 - (P.σ : ℝ) + hc.eps') :=
          add_le_add (by exact_mod_cast hSpecialIDs) hResidualCard
    calc
      ((seenIDs9 center b).card : ℝ) ≤
          (P.m n : ℝ) + 3 * (n : ℝ) ^ (1 - (P.σ : ℝ) + hc.eps') := hseenReal
      _ = 3 * (n : ℝ) ^ (1 - (P.σ : ℝ) + hc.eps') + (P.m n : ℝ) := by ring
      _ ≤ P.idBudget n + (P.m n : ℝ) := by nlinarith [hbudget]
  · intro v hvEven
    let j : Fin (hc.levels n + 1) := (center v).level
    have hlevel : j.val = height9 Pp A v := (hcenter v).2.2.1
    have hj : j ∈ levelWindow v := by simp [levelWindow, j, hlevel]
    have hsame : center v ∈ sameLayer v j := by
      simp only [sameLayer, Finset.mem_filter, Finset.mem_univ, true_and]
      exact ⟨(hcenter v).2.2.2, (hcenter v).1, (hcenter v).2.1, rfl⟩
    exact Finset.mem_biUnion.mpr ⟨j, hj, Finset.mem_union_left _ hsame⟩
  · intro v hvEven
    classical
    rcases hgood v with ⟨hbelow, hgoodNoBad, hregular⟩
    let j₀ : Fin (hc.levels n + 1) := ⟨height9 Pp A v, by omega⟩
    have hnotbad : ¬ badAt9 Pp A v j₀ := by simpa [j₀] using hgoodNoBad
    let J := levelWindow v
    have hJcard : J.card ≤ 3 := by
      simpa [J, levelWindow] using
        (Lane_q_s09_map.level_window_card_le_three (hc.levels n) (height9 Pp A v))
    have hsameBound (j : Fin (hc.levels n + 1)) (hj : j ∈ J) :
        ((sameLayer v j).card : ℝ) ≤ (n : ℝ) ^ ((P.χ : ℝ) / 2) := by
      by_contra hlarge
      have hstrict : (n : ℝ) ^ ((P.χ : ℝ) / 2) < ((sameLayer v j).card : ℝ) :=
        lt_of_not_ge hlarge
      have hstrict' : (n : ℝ) ^ ((P.χ : ℝ) / 2) <
          (crowdSame9 Finset.univ Pp A v j (P.radius n) : ℝ) := by
        simpa [sameLayer, crowdSame9] using hstrict
      have hdist : Nat.dist j₀.val j.val ≤ 2 := by
        have hwin := (Finset.mem_filter.mp hj).2
        simpa [j₀, Nat.dist_comm] using (le_trans hwin (by omega : 1 ≤ 2))
      have hbadIn : badIn9 Finset.univ 1 Pp A v j₀ :=
        Or.inr ⟨j, hdist, Or.inl (by simpa [one_mul] using hstrict')⟩
      exact hnotbad (by simpa [badAt9] using hbadIn)
    have hadjBound (j : Fin (hc.levels n + 1)) (hj : j ∈ J) :
        ((adjLayer v j).card : ℝ) ≤ (n : ℝ) ^ ((P.χ : ℝ) / 2) := by
      by_contra hlarge
      have hstrict : (n : ℝ) ^ ((P.χ : ℝ) / 2) < ((adjLayer v j).card : ℝ) :=
        lt_of_not_ge hlarge
      have hstrict' : (n : ℝ) ^ ((P.χ : ℝ) / 2) <
          (crowdAdj9 Finset.univ Pp A v j : ℝ) := by
        simpa [adjLayer, crowdAdj9] using hstrict
      have hdist : Nat.dist j₀.val j.val ≤ 2 := by
        have hwin := (Finset.mem_filter.mp hj).2
        simpa [j₀, Nat.dist_comm] using (le_trans hwin (by omega : 1 ≤ 2))
      have hbadIn : badIn9 Finset.univ 1 Pp A v j₀ :=
        Or.inr ⟨j, hdist, Or.inr (Or.inl (by simpa [one_mul] using hstrict'))⟩
      exact hnotbad (by simpa [badAt9] using hbadIn)
    have hcoreNat : (core v).card ≤
        ∑ j ∈ J, (sameLayer v j ∪ adjLayer v j).card := by
      simpa [core, J] using (Finset.card_biUnion_le)
    have hcoreNat' : (core v).card ≤
        ∑ j ∈ J, ((sameLayer v j).card + (adjLayer v j).card) := by
      calc
        (core v).card ≤ ∑ j ∈ J, (sameLayer v j ∪ adjLayer v j).card := hcoreNat
        _ ≤ ∑ j ∈ J, ((sameLayer v j).card + (adjLayer v j).card) := by
          apply Finset.sum_le_sum
          intro j hj
          exact Finset.card_union_le _ _
    have hcoreReal : ((core v).card : ℝ) ≤ 6 * (n : ℝ) ^ ((P.χ : ℝ) / 2) := by
      calc
        ((core v).card : ℝ) ≤
            ∑ j ∈ J, (((sameLayer v j).card : ℝ) + ((adjLayer v j).card : ℝ)) := by
          exact_mod_cast hcoreNat'
        _ ≤ ∑ _j ∈ J, 2 * (n : ℝ) ^ ((P.χ : ℝ) / 2) := by
          apply Finset.sum_le_sum
          intro j hj
          calc
            ((sameLayer v j).card : ℝ) + ((adjLayer v j).card : ℝ) ≤
                (n : ℝ) ^ ((P.χ : ℝ) / 2) + (n : ℝ) ^ ((P.χ : ℝ) / 2) :=
              add_le_add (hsameBound j hj) (hadjBound j hj)
            _ = 2 * (n : ℝ) ^ ((P.χ : ℝ) / 2) := by ring
        _ = (J.card : ℝ) * (2 * (n : ℝ) ^ ((P.χ : ℝ) / 2)) := by simp
        _ ≤ 3 * (2 * (n : ℝ) ^ ((P.χ : ℝ) / 2)) := by
          exact mul_le_mul_of_nonneg_right (by exact_mod_cast hJcard) (by positivity)
        _ = 6 * (n : ℝ) ^ ((P.χ : ℝ) / 2) := by ring
    exact hcoreReal.trans hcoreSlack
  · intro v hvEven id hid
    classical
    let B : Finset (CubeVertex n) := Finset.univ.filter fun b =>
      (cube n).Adj v b ∧ id ∈ seenIDs9 center b
    let DeltaS : Finset (Fin (P.m n)) := Finset.univ.filter fun k =>
      id.slice k ≠ specialWord9 (P.m n) v k
    let DeltaR : Finset (Fin (n - P.m n)) := Finset.univ.filter fun k =>
      id.location k ≠ residualWord9 (P.m n) v k
    let toS : Fin (P.m n) → Fin n := fun k => ⟨k.val, by omega⟩
    let toR : Fin (n - P.m n) → Fin n := fun k => ⟨P.m n + k.val, by omega⟩
    let DeltaSFull := DeltaS.image toS
    let DeltaRFull := DeltaR.image toR
    have hSCard : DeltaS.card = _root_.hammingDist id.slice (specialWord9 (P.m n) v) := by
      simp [DeltaS, _root_.hammingDist]
    have hRCard : DeltaR.card = _root_.hammingDist id.location (residualWord9 (P.m n) v) := by
      simp [DeltaR, _root_.hammingDist]
    have htoSInj : Function.Injective toS := by
      intro k l h
      have hv : (toS k).val = (toS l).val := congrArg Fin.val h
      apply Fin.ext
      simpa [toS] using hv
    have htoRInj : Function.Injective toR := by
      intro k l h
      apply Fin.ext
      have hv := congrArg Fin.val h
      dsimp [toR] at hv
      omega
    have hSFullCard : DeltaSFull.card = DeltaS.card := by
      exact Finset.card_image_of_injective DeltaS htoSInj
    have hRFullCard : DeltaRFull.card = DeltaR.card := by
      exact Finset.card_image_of_injective DeltaR htoRInj
    have hmemS (k : Fin (P.m n)) (hk : id.slice k ≠ specialWord9 (P.m n) v k) :
        toS k ∈ DeltaSFull := by
      apply Finset.mem_image.mpr
      exact ⟨k, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hk⟩, rfl⟩
    have hmemR (k : Fin (n - P.m n))
        (hk : id.location k ≠ residualWord9 (P.m n) v k) : toR k ∈ DeltaRFull := by
      apply Finset.mem_image.mpr
      exact ⟨k, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hk⟩, rfl⟩
    have hcenterMem : center v ∈ core v := by
      let j : Fin (hc.levels n + 1) := (center v).level
      have hlevel : j.val = height9 Pp A v := (hcenter v).2.2.1
      have hj : j ∈ levelWindow v := by simp [levelWindow, j, hlevel]
      have hsame : center v ∈ sameLayer v j := by
        simp only [sameLayer, Finset.mem_filter, Finset.mem_univ, true_and]
        exact ⟨(hcenter v).2.2.2, (hcenter v).1, (hcenter v).2.1, rfl⟩
      exact Finset.mem_biUnion.mpr ⟨j, hj, Finset.mem_union_left _ hsame⟩
    have hself : center v ≠ id := by
      intro heq
      subst id
      exact hid hcenterMem
    have hpath (b : CubeVertex n) (hb : b ∈ B) :
        ∃ i j a, cubeFlip v i = b ∧
          (cube n).Adj b a ∧ a = cubeFlip (cubeFlip v i) j ∧ center a = id ∧ i ≠ j := by
      rcases Finset.mem_filter.mp hb with ⟨_, ⟨hvb, hseen⟩⟩
      obtain ⟨i, hbi⟩ := Lane_q_s09_map.cubeAdj_exists_flip v b hvb
      change id ∈ (Finset.univ.filter fun a : CubeVertex n => (cube n).Adj b a).image center at hseen
      rcases Finset.mem_image.mp hseen with ⟨a, ha, hca⟩
      have hba : (cube n).Adj b a := (Finset.mem_filter.mp ha).2
      obtain ⟨j, hbj⟩ := Lane_q_s09_map.cubeAdj_exists_flip b a hba
      have haneqv : a ≠ v := by
        intro hav
        apply hself
        calc
          center v = center a := (congrArg center hav).symm
          _ = id := hca
      have hformula : a = cubeFlip (cubeFlip v i) j := by
        calc
          a = cubeFlip b j := hbj.symm
          _ = cubeFlip (cubeFlip v i) j := by rw [hbi]
      have hij : i ≠ j := by
        intro heq
        subst j
        rw [Lane_q_s09_map.cubeFlip_involutive] at hformula
        exact haneqv hformula
      exact ⟨i, j, a, hbi, hba, hformula, hca, hij⟩
    have hcoreSame (ha : activeAt9 Pp A id)
        (hs : id.slice = specialWord9 (P.m n) v)
        (hd : _root_.hammingDist id.location (residualWord9 (P.m n) v) ≤ P.radius n)
        (hl : Nat.dist id.level.val (height9 Pp A v) ≤ 1) : id ∈ core v := by
      let j := id.level
      have hj : j ∈ levelWindow v := by
        apply Finset.mem_filter.mpr
        refine ⟨Finset.mem_univ _, ?_⟩
        simpa [j, Nat.dist_comm] using hl
      have hsame : id ∈ sameLayer v j := by
        simp only [sameLayer, Finset.mem_filter, Finset.mem_univ, true_and]
        exact ⟨ha, hs, hd, rfl⟩
      exact Finset.mem_biUnion.mpr ⟨j, hj, Finset.mem_union_left _ hsame⟩
    have hcoreAdj (ha : activeAt9 Pp A id)
        (hs : _root_.hammingDist id.slice (specialWord9 (P.m n) v) = 1)
        (hd : _root_.hammingDist id.location (residualWord9 (P.m n) v) ≤ P.radius n - 1)
        (hl : Nat.dist id.level.val (height9 Pp A v) ≤ 1) : id ∈ core v := by
      let j := id.level
      have hj : j ∈ levelWindow v := by
        apply Finset.mem_filter.mpr
        refine ⟨Finset.mem_univ _, ?_⟩
        simpa [j, Nat.dist_comm] using hl
      have hadj : id ∈ adjLayer v j := by
        simp only [adjLayer, Finset.mem_filter, Finset.mem_univ, true_and]
        exact ⟨ha, hs, hd, rfl⟩
      exact Finset.mem_biUnion.mpr ⟨j, hj, Finset.mem_union_right _ hadj⟩
    by_cases hBne : B.Nonempty
    · obtain ⟨b₀, hb₀⟩ := hBne
      obtain ⟨i₀, j₀, a₀, hbi₀, hba₀, hformula₀, hca₀, hij₀⟩ := hpath b₀ hb₀
      have htwo₀ : _root_.hammingDist v a₀ = 2 := by
        rw [hformula₀]
        exact Lane_q_s09_map.hammingDist_two_cubeFlips v i₀ j₀ hij₀
      have hsliceLe : _root_.hammingDist id.slice (specialWord9 (P.m n) v) ≤ 2 := by
        have hida₀ := by simpa [hca₀] using hcenter a₀
        calc
          _ = _root_.hammingDist (specialWord9 (P.m n) a₀) (specialWord9 (P.m n) v) := by
            rw [hida₀.1]
          _ ≤ _root_.hammingDist a₀ v := Lane_q_s09_map.specialProjectionDist_le hmle a₀ v
          _ = 2 := by rw [_root_.hammingDist_comm]; exact htwo₀
      have hRle2 : _root_.hammingDist id.location (residualWord9 (P.m n) v) ≤
          P.radius n + 2 := by
        have hida₀ := by simpa [hca₀] using hcenter a₀
        have hresdist := (Lane_q_s09_map.residualProjectionDist_le hmle a₀ v).trans
          (by simpa [_root_.hammingDist_comm] using (le_of_eq htwo₀))
        calc
          _ ≤ _root_.hammingDist id.location (residualWord9 (P.m n) a₀) +
              _root_.hammingDist (residualWord9 (P.m n) a₀) (residualWord9 (P.m n) v) :=
                _root_.hammingDist_triangle _ _ _
          _ ≤ P.radius n + 2 := Nat.add_le_add hida₀.2.1 hresdist
      by_cases hs0 : _root_.hammingDist id.slice (specialWord9 (P.m n) v) = 0
      · have hsliceEq : id.slice = specialWord9 (P.m n) v :=
          (_root_.hammingDist_lt_one).mp (by omega)
        have hSupport (b : CubeVertex n) (hb : b ∈ B) :
            ∃ k ∈ DeltaRFull, cubeFlip v k = b := by
          rcases hpath b hb with ⟨i, j, a, hbi, hba, hformula, hca, hij⟩
          have htwo : _root_.hammingDist v a = 2 := by
            rw [hformula]
            exact Lane_q_s09_map.hammingDist_two_cubeFlips v i j hij
          have hida := by simpa [hca] using hcenter a
          have hregular : ∀ w, _root_.hammingDist v w ≤ 2 →
              Nat.dist (height9 Pp A v) (height9 Pp A w) ≤ 1 := (hgood v).choose_spec.2
          have hlevelClose : Nat.dist id.level.val (height9 Pp A v) ≤ 1 := by
            rw [hida.2.2.1]
            have hreg := hregular a (by rw [htwo])
            simpa [Nat.dist_comm] using hreg
          have hRgt : P.radius n < _root_.hammingDist id.location (residualWord9 (P.m n) v) := by
            by_contra hnot
            have hd : _root_.hammingDist id.location (residualWord9 (P.m n) v) ≤ P.radius n := by omega
            exact hid (hcoreSame hida.2.2.2 hsliceEq hd hlevelClose)
          have hiResidual : P.m n ≤ i.val := by
            by_contra hnot
            have hiSpecial : i.val < P.m n := by omega
            have hcoord := Lane_q_s09_map.specialWord9_doubleFlip_at_first hmle v i j hij hiSpecial
            have hcoord' : specialWord9 (P.m n) a ⟨i.val, hiSpecial⟩ ≠
                specialWord9 (P.m n) v ⟨i.val, hiSpecial⟩ := by
              simpa [hformula] using hcoord
            have hidcoord : id.slice ⟨i.val, hiSpecial⟩ ≠
                specialWord9 (P.m n) v ⟨i.val, hiSpecial⟩ := by
              rw [hida.1]
              exact hcoord'
            exact hidcoord (congrArg (fun s : CubeVertex (P.m n) => s ⟨i.val, hiSpecial⟩) hsliceEq)
          let k : Fin (n - P.m n) := ⟨i.val - P.m n, by omega⟩
          have htoR : toR k = i := by
            apply Fin.ext
            dsimp [toR, k]
            omega
          have hresb : residualWord9 (P.m n) b =
              cubeFlip (residualWord9 (P.m n) v) k := by
            rw [← hbi]
            simpa [k] using
              (Lane_q_s09_map.residualWord9_cubeFlip_residual hmle v i hiResidual)
          by_cases hmatch : id.location k = residualWord9 (P.m n) v k
          · have hflipDist := Lane_q_s09_map.hammingDist_cubeFlip_of_eq id.location
              (residualWord9 (P.m n) v) k hmatch
            have hbaDist : _root_.hammingDist b a = 1 := by
              simpa [OAI.HypercubeRamsey.cube] using hba
            have hresab : _root_.hammingDist (residualWord9 (P.m n) a)
                (residualWord9 (P.m n) b) ≤ 1 :=
              (Lane_q_s09_map.residualProjectionDist_le hmle a b).trans (by
                rw [_root_.hammingDist_comm]
                exact hbaDist.le)
            have himpossible : _root_.hammingDist id.location (residualWord9 (P.m n) v) + 1 ≤
                P.radius n + 1 := by
              calc
                _ = _root_.hammingDist id.location (residualWord9 (P.m n) b) := by
                  rw [hresb]
                  exact hflipDist.symm
                _ ≤ _root_.hammingDist id.location (residualWord9 (P.m n) a) +
                      _root_.hammingDist (residualWord9 (P.m n) a) (residualWord9 (P.m n) b) :=
                    _root_.hammingDist_triangle _ _ _
                _ ≤ P.radius n + 1 := Nat.add_le_add hida.2.1 hresab
            omega
          · have hkD : k ∈ DeltaR :=
              Finset.mem_filter.mpr ⟨Finset.mem_univ _, hmatch⟩
            refine ⟨toR k, ?_, ?_⟩
            · exact Finset.mem_image.mpr ⟨k, hkD, rfl⟩
            · rw [htoR]
              exact hbi
        have hcount := Lane_q_s09_map.card_flip_neighbors_bound v B DeltaRFull hSupport
        calc
          B.card ≤ DeltaRFull.card := hcount
          _ = DeltaR.card := hRFullCard
          _ = _root_.hammingDist id.location (residualWord9 (P.m n) v) := hRCard
          _ ≤ P.radius n + 2 := hRle2
          _ ≤ P.radius n + 3 := by omega
      · by_cases hs1 : _root_.hammingDist id.slice (specialWord9 (P.m n) v) = 1
        · have hresAV_le_one (a : CubeVertex n) (hca : center a = id)
              (htwo : _root_.hammingDist v a = 2) :
              _root_.hammingDist (residualWord9 (P.m n) a)
                (residualWord9 (P.m n) v) ≤ 1 := by
            have hida := by simpa [hca] using hcenter a
            have hspeca : _root_.hammingDist (specialWord9 (P.m n) a)
                (specialWord9 (P.m n) v) = 1 := by
              rw [← hida.1]
              exact hs1
            have hsplit := Lane_q_s09_map.splitProjectionDist_add_le hmle a v
            have hsum : _root_.hammingDist (specialWord9 (P.m n) a)
                (specialWord9 (P.m n) v) +
                  _root_.hammingDist (residualWord9 (P.m n) a)
                    (residualWord9 (P.m n) v) ≤ 2 := by
              calc
                _ ≤ _root_.hammingDist a v := hsplit
                _ = 2 := by rw [_root_.hammingDist_comm]; exact htwo
            rw [hspeca] at hsum
            omega
          have hSupport (b : CubeVertex n) (hb : b ∈ B) :
              ∃ k ∈ DeltaRFull ∪ DeltaSFull, cubeFlip v k = b := by
            rcases hpath b hb with ⟨i, j, a, hbi, hba, hformula, hca, hij⟩
            have htwo : _root_.hammingDist v a = 2 := by
              rw [hformula]
              exact Lane_q_s09_map.hammingDist_two_cubeFlips v i j hij
            have hida := by simpa [hca] using hcenter a
            have hregular : ∀ w, _root_.hammingDist v w ≤ 2 →
                Nat.dist (height9 Pp A v) (height9 Pp A w) ≤ 1 := (hgood v).choose_spec.2
            have hlevelClose : Nat.dist id.level.val (height9 Pp A v) ≤ 1 := by
              rw [hida.2.2.1]
              have hreg := hregular a (by rw [htwo])
              simpa [Nat.dist_comm] using hreg
            have hRge : P.radius n ≤ _root_.hammingDist id.location (residualWord9 (P.m n) v) := by
              by_contra hnot
              have hd : _root_.hammingDist id.location (residualWord9 (P.m n) v) ≤ P.radius n - 1 := by omega
              exact hid (hcoreAdj hida.2.2.2 hs1 hd hlevelClose)
            by_cases hiSpecial : i.val < P.m n
            · have hcoord := Lane_q_s09_map.specialWord9_doubleFlip_at_first hmle v i j hij hiSpecial
              have hcoord' : specialWord9 (P.m n) a ⟨i.val, hiSpecial⟩ ≠
                  specialWord9 (P.m n) v ⟨i.val, hiSpecial⟩ := by
                simpa [hformula] using hcoord
              have hidcoord : id.slice ⟨i.val, hiSpecial⟩ ≠
                  specialWord9 (P.m n) v ⟨i.val, hiSpecial⟩ := by
                rw [hida.1]
                exact hcoord'
              refine ⟨toS ⟨i.val, hiSpecial⟩,
                Finset.mem_union_right _ (hmemS _ hidcoord), ?_⟩
              · rw [show toS ⟨i.val, hiSpecial⟩ = i from Fin.ext rfl]
                exact hbi
            · have hiResidual : P.m n ≤ i.val := by omega
              have hjSpecial : j.val < P.m n := by
                by_contra hjnot
                have hjResidual : P.m n ≤ j.val := by omega
                have hspeca : specialWord9 (P.m n) a = specialWord9 (P.m n) v := by
                  rw [hformula]
                  exact (Lane_q_s09_map.specialWord9_cubeFlip_residual hmle
                    (cubeFlip v i) j hjResidual).trans
                    (Lane_q_s09_map.specialWord9_cubeFlip_residual hmle v i hiResidual)
                have hEq : id.slice = specialWord9 (P.m n) v := hida.1.trans hspeca
                have hzero : _root_.hammingDist id.slice (specialWord9 (P.m n) v) = 0 := by
                  rw [hEq]
                  simp
                omega
              let k : Fin (n - P.m n) := ⟨i.val - P.m n, by omega⟩
              have htoR : toR k = i := by
                apply Fin.ext
                dsimp [toR, k]
                omega
              have hresb : residualWord9 (P.m n) b =
                  cubeFlip (residualWord9 (P.m n) v) k := by
                rw [← hbi]
                simpa [k] using
                  (Lane_q_s09_map.residualWord9_cubeFlip_residual hmle v i hiResidual)
              have hresa : residualWord9 (P.m n) a = residualWord9 (P.m n) b := by
                rw [hformula, ← hbi]
                exact Lane_q_s09_map.residualWord9_cubeFlip_special hmle
                  (cubeFlip v i) j hjSpecial
              have hresav := hresAV_le_one a hca htwo
              have hRle : _root_.hammingDist id.location (residualWord9 (P.m n) v) ≤
                  P.radius n + 1 := by
                calc
                  _ ≤ _root_.hammingDist id.location (residualWord9 (P.m n) a) +
                      _root_.hammingDist (residualWord9 (P.m n) a) (residualWord9 (P.m n) v) :=
                        _root_.hammingDist_triangle _ _ _
                  _ ≤ P.radius n + 1 := Nat.add_le_add hida.2.1 hresav
              by_cases hmatch : id.location k = residualWord9 (P.m n) v k
              · have hflipDist := Lane_q_s09_map.hammingDist_cubeFlip_of_eq id.location
                  (residualWord9 (P.m n) v) k hmatch
                have himpossible : _root_.hammingDist id.location (residualWord9 (P.m n) v) + 1 ≤
                    P.radius n := by
                  calc
                    _ = _root_.hammingDist id.location (residualWord9 (P.m n) b) := by
                      rw [hresb]
                      exact hflipDist.symm
                    _ = _root_.hammingDist id.location (residualWord9 (P.m n) a) := by rw [hresa]
                    _ ≤ P.radius n := hida.2.1
                omega
              · have hkD : k ∈ DeltaR :=
                  Finset.mem_filter.mpr ⟨Finset.mem_univ _, hmatch⟩
                refine ⟨toR k, Finset.mem_union_left _
                  (Finset.mem_image.mpr ⟨k, hkD, rfl⟩), ?_⟩
                · rw [htoR]
                  exact hbi
          have hcount := Lane_q_s09_map.card_flip_neighbors_bound v B
            (DeltaRFull ∪ DeltaSFull) hSupport
          have hRle : _root_.hammingDist id.location (residualWord9 (P.m n) v) ≤
              P.radius n + 1 := by
            rcases hpath b₀ hb₀ with ⟨i, j, a, _, _, hformula, hca, hij⟩
            have hida := by simpa [hca] using hcenter a
            have htwo : _root_.hammingDist v a = 2 := by
              rw [hformula]
              exact Lane_q_s09_map.hammingDist_two_cubeFlips v i j hij
            have hresav := hresAV_le_one a hca htwo
            calc
              _ ≤ _root_.hammingDist id.location (residualWord9 (P.m n) a) +
                  _root_.hammingDist (residualWord9 (P.m n) a) (residualWord9 (P.m n) v) :=
                    _root_.hammingDist_triangle _ _ _
              _ ≤ P.radius n + 1 := Nat.add_le_add hida.2.1 hresav
          calc
            B.card ≤ (DeltaRFull ∪ DeltaSFull).card := hcount
            _ ≤ DeltaRFull.card + DeltaSFull.card := Finset.card_union_le _ _
            _ = DeltaR.card + DeltaS.card := by rw [hRFullCard, hSFullCard]
            _ = _root_.hammingDist id.location (residualWord9 (P.m n) v) + 1 := by
              rw [hRCard, hSCard, hs1]
            _ ≤ P.radius n + 2 := Nat.add_le_add_right hRle 1
            _ ≤ P.radius n + 3 := by omega
        · have hs2 : _root_.hammingDist id.slice (specialWord9 (P.m n) v) = 2 := by omega
          have hSupport (b : CubeVertex n) (hb : b ∈ B) :
              ∃ k ∈ DeltaSFull, cubeFlip v k = b := by
            rcases hpath b hb with ⟨i, j, a, hbi, hba, hformula, hca, hij⟩
            by_contra hiNot
            have hiResidual : P.m n ≤ i.val := by
              by_contra hi
              have hiSpecial : i.val < P.m n := by omega
              have hcoord := Lane_q_s09_map.specialWord9_doubleFlip_at_first hmle v i j hij hiSpecial
              have hcoord' : specialWord9 (P.m n) a ⟨i.val, hiSpecial⟩ ≠
                  specialWord9 (P.m n) v ⟨i.val, hiSpecial⟩ := by
                simpa [hformula] using hcoord
              have hidcoord : id.slice ⟨i.val, hiSpecial⟩ ≠
                  specialWord9 (P.m n) v ⟨i.val, hiSpecial⟩ := by
                have hida := by simpa [hca] using hcenter a
                rw [hida.1]
                exact hcoord'
              have hmem : toS ⟨i.val, hiSpecial⟩ ∈ DeltaSFull := hmemS _ hidcoord
              exact hiNot ⟨toS ⟨i.val, hiSpecial⟩, hmem, by
                rw [show toS ⟨i.val, hiSpecial⟩ = i from Fin.ext rfl]
                exact hbi⟩
            have hida := by simpa [hca] using hcenter a
            have hspecb : specialWord9 (P.m n) b = specialWord9 (P.m n) v := by
              rw [← hbi]
              exact Lane_q_s09_map.specialWord9_cubeFlip_residual hmle v i hiResidual
            have hbaDist : _root_.hammingDist a b = 1 := by
              rw [_root_.hammingDist_comm]
              simpa [OAI.HypercubeRamsey.cube] using hba
            have hsliceLe' : _root_.hammingDist id.slice (specialWord9 (P.m n) v) ≤ 1 := by
              calc
                _ = _root_.hammingDist (specialWord9 (P.m n) a)
                      (specialWord9 (P.m n) b) := by rw [hida.1, ← hspecb]
                _ ≤ _root_.hammingDist a b := Lane_q_s09_map.specialProjectionDist_le hmle a b
                _ = 1 := hbaDist
            omega
          have hcount := Lane_q_s09_map.card_flip_neighbors_bound v B DeltaSFull hSupport
          calc
            B.card ≤ DeltaSFull.card := hcount
            _ = DeltaS.card := hSFullCard
            _ = _root_.hammingDist id.slice (specialWord9 (P.m n) v) := hSCard
            _ = 2 := hs2
            _ ≤ P.radius n + 3 := by omega
    · have hBempty : B = ∅ := Finset.not_nonempty_iff_eq_empty.mp hBne
      change B.card ≤ P.radius n + 3
      rw [hBempty]
      exact Nat.zero_le _

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
