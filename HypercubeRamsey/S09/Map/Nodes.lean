import HypercubeRamsey.S09.Map.Device
import HypercubeRamsey.S09.Map.Nodes_q_s09_hind
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
  obtain ⟨n₀, hbase⟩ :=
    Lane_q_s09_map.height_base_probability_bound9 P hP hc hadm
  rcases hadm with ⟨_, _, _, _, _, _, _, _, hbpos, _, _, _⟩
  exact ⟨hc.b₀ / 4, div_pos hbpos (by norm_num), n₀, hbase⟩

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

set_option maxHeartbeats 800000

/-- P9.2-map1, cross-slice overlap (09:86–92): a child domain of radius `R'` consults slices within `O(R')` and
residual locations within `r + O(R')`; for starts separated by `K R'` either the consulted slice ranges are
disjoint or the residual separation is `Ω(K R')`; if the residual balls meet, `R' = O(r)` and the shell and
hypergeometric estimates (`hypergeometric_intersection_tail`) bound the residual overlap fraction by
`exp(-Ω(K R' log n))`, while enumerating slices and enlarging balls costs `exp(O(R' log n))`; for large fixed `K`
the overlap at one level is at most `V e^{-c₀ R'}`. -/
theorem p92_height_overlap (P : Params9) (hP : P.Valid) (hc : HeightChoice9 P) (hadm : hc.Admissible) :
    ∃ K > (0 : ℝ), ∃ c₀ > (0 : ℝ), ∃ n₀ : ℕ, ∀ n ≥ n₀, HeightOverlap9 P hc n K c₀ := by
  obtain ⟨nSmall, hSmall⟩ := Lane_q_s09_map.height_base_small_scales9 P hP
  obtain ⟨nVol, hVol⟩ := Lane_q_s09_map.height_counts9_volume_bounds P hP
  obtain ⟨n40, h40⟩ := Lane_q_s09_map.height_rpow_eventually_ge9
    (1 / 40 : ℝ) 2 (by norm_num) (by norm_num)
  obtain ⟨n8, h8⟩ := Lane_q_s09_map.height_rpow_eventually_ge9
    (1 / 8 : ℝ) 2 (by norm_num) (by norm_num)
  obtain ⟨nQuarter, hQuarter⟩ := Lane_q_s09_map.height_rpow_eventually_ge9
    (1 / 4 : ℝ) 3 (by norm_num) (by norm_num)
  refine ⟨1024, by norm_num, Real.log 2, Real.log_pos (by norm_num),
    max nSmall (max nVol (max n40 (max n8 nQuarter))), ?_⟩
  intro n hn v v' R' j hR hsep
  have hnA : max nVol (max n40 (max n8 nQuarter)) ≤ n :=
    le_trans (le_max_right _ _) hn
  have hnSmall : nSmall ≤ n := le_trans (le_max_left _ _) hn
  have hnVol : nVol ≤ n := le_trans (le_max_left _ _) hnA
  have hnB : max n40 (max n8 nQuarter) ≤ n := le_trans (le_max_right _ _) hnA
  have hn40 : n40 ≤ n := le_trans (le_max_left _ _) hnB
  have hnC : max n8 nQuarter ≤ n := le_trans (le_max_right _ _) hnB
  have hn8 : n8 ≤ n := le_trans (le_max_left _ _) hnC
  have hnQuarter : nQuarter ≤ n := le_trans (le_max_right _ _) hnC
  have hsmall := hSmall n hnSmall
  have hvolume := hVol n hnVol
  have hr11R : (11 : ℝ) ≤ (P.radius n : ℝ) := by exact_mod_cast hsmall.2.2
  have hn44R : (44 : ℝ) ≤ (n : ℝ) := by nlinarith [hsmall.2.1, hr11R]
  have hn44 : 44 ≤ n := by exact_mod_cast hn44R
  have hmle : P.m n ≤ n := by
    have h : (P.m n : ℝ) ≤ (n : ℝ) := by linarith [hsmall.1]
    exact_mod_cast h
  have hrd : P.radius n ≤ n - P.m n := hvolume.2.1
  let U : Finset (Pos9 P hc n) := consulted9 (P := P) v R' ∩ consulted9 v' R'
  let T : Finset (Pos9 P hc n) := U.filter (fun c => c.level = j)
  let sliceRadius : ℕ := 2 * R' + 1
  let residualRadius : ℕ := P.radius n + 2 * R' + 1
  let sliceBall : Finset (CubeVertex (P.m n)) :=
    Finset.univ.filter (fun z =>
      _root_.hammingDist z (specialWord9 (P.m n) v) ≤ sliceRadius ∧
        _root_.hammingDist z (specialWord9 (P.m n) v') ≤ sliceRadius)
  let residualIntersection : Finset (CubeVertex (n - P.m n)) :=
    Finset.univ.filter (fun z =>
      _root_.hammingDist z (residualWord9 (P.m n) v) ≤ residualRadius ∧
        _root_.hammingDist z (residualWord9 (P.m n) v') ≤ residualRadius)
  change (T.card : ℝ) ≤
    (residualBall9 P n : ℝ) * Real.exp (-(Real.log 2 * (R' : ℝ)))
  have hlocal : ∀ c : Pos9 P hc n,
      c ∈ consulted9 (P := P) (hc := hc) (n := n) v R' ∩ consulted9 v' R' →
        _root_.hammingDist c.slice (specialWord9 (P.m n) v) ≤ 2 * R' + 1 ∧
        _root_.hammingDist c.slice (specialWord9 (P.m n) v') ≤ 2 * R' + 1 ∧
        _root_.hammingDist c.location (residualWord9 (P.m n) v) ≤ P.radius n + 2 * R' + 1 ∧
        _root_.hammingDist c.location (residualWord9 (P.m n) v') ≤ P.radius n + 2 * R' + 1 := by
    intro c hc
    exact Lane_q_s09_map.sharedConsulted_local_bounds v v' R' c hc
  have hresidualSeparation (c : Pos9 P hc n)
      (hshared : c ∈ consulted9 (P := P) (hc := hc) (n := n) v R' ∩ consulted9 v' R') :
      (1020 : ℝ) * R' - 2 ≤
        (_root_.hammingDist (residualWord9 (P.m n) v)
          (residualWord9 (P.m n) v') : ℝ) := by
    have hsepR := Lane_q_s09_map.sharedConsulted_residual_separation_general9
      hmle v v' R' 1024 hsep c hshared
    norm_num at hsepR
    linarith [hsepR]
  by_cases hTempty : T = ∅
  · rw [hTempty]
    simp
    positivity
  · have hTne : T.Nonempty := Finset.nonempty_iff_ne_empty.mpr hTempty
    obtain ⟨c, hcT⟩ := hTne
    have hcU : c ∈ U := (Finset.mem_filter.mp hcT).1
    have hsmallConsult : 100 * R' ≤ P.radius n := by
      have hsepRes := hresidualSeparation c hcU
      have hl := hlocal c hcU
      have hupperNat :
          _root_.hammingDist (residualWord9 (P.m n) v)
              (residualWord9 (P.m n) v') ≤
            2 * (P.radius n + 2 * R' + 1) := by
        calc
          _ ≤ _root_.hammingDist (residualWord9 (P.m n) v) c.location +
              _root_.hammingDist c.location (residualWord9 (P.m n) v') :=
                _root_.hammingDist_triangle _ _ _
          _ ≤ (P.radius n + 2 * R' + 1) +
              (P.radius n + 2 * R' + 1) := by
                exact Nat.add_le_add
                  (by simpa [_root_.hammingDist_comm] using hl.2.2.1) hl.2.2.2
          _ = 2 * (P.radius n + 2 * R' + 1) := by omega
      have hupperR :
          (_root_.hammingDist (residualWord9 (P.m n) v)
            (residualWord9 (P.m n) v') : ℝ) ≤
            2 * ((P.radius n + 2 * R' + 1 : ℕ) : ℝ) := by exact_mod_cast hupperNat
      have hRle : (100 : ℝ) * R' ≤ (P.radius n : ℝ) := by
        have hRpos : (1 : ℝ) ≤ R' := by exact_mod_cast hR
        have hlow : (1020 : ℝ) * R' - 2 ≤
            (_root_.hammingDist (residualWord9 (P.m n) v)
              (residualWord9 (P.m n) v') : ℝ) := hsepRes
        have hupr : (_root_.hammingDist (residualWord9 (P.m n) v)
            (residualWord9 (P.m n) v') : ℝ) ≤
              2 * ((P.radius n : ℝ) + 2 * R' + 1) := by
          have hcast : ((P.radius n + 2 * R' + 1 : ℕ) : ℝ) =
              (P.radius n : ℝ) + 2 * R' + 1 := by norm_num
          rw [hcast] at hupperR
          exact hupperR
        nlinarith [hlow, hupr, hRpos]
      exact_mod_cast hRle
    have hconsultRadius : (P.radius n + 2 * R' + 1 : ℕ) ≤ n - P.m n := by
      have hrr : (P.radius n : ℝ) ≤ (n : ℝ) / 4 := hsmall.2.1
      have hm : (P.m n : ℝ) ≤ (n : ℝ) / 4 := hsmall.1
      have hd : ((n - P.m n : ℕ) : ℝ) = (n : ℝ) - (P.m n : ℝ) :=
        Nat.cast_sub hmle
      have hReal : (P.radius n : ℝ) + 2 * R' + 1 ≤
          ((n - P.m n : ℕ) : ℝ) := by
        have hr11 : 11 ≤ (P.radius n : ℝ) := by exact_mod_cast hsmall.2.2
        have hRcast : (100 : ℝ) * R' ≤ (P.radius n : ℝ) := by exact_mod_cast hsmallConsult
        rw [hd]
        nlinarith [hrr, hm, hr11, hRcast]
      exact_mod_cast hReal
    let sliceBallOne : Finset (CubeVertex (P.m n)) :=
      Finset.univ.filter (fun z : CubeVertex (P.m n) =>
        _root_.hammingDist z (specialWord9 (P.m n) v) ≤ sliceRadius)
    have hsliceSub : sliceBall ⊆ sliceBallOne := by
      intro z hz
      simp only [sliceBall, Finset.mem_filter, Finset.mem_univ, true_and] at hz
      exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, hz.1⟩
    have hsliceCard : sliceBall.card ≤
        ∑ i ∈ Finset.range (sliceRadius + 1), Nat.choose (P.m n) i := by
      calc
        sliceBall.card ≤ sliceBallOne.card := Finset.card_le_card hsliceSub
        _ = _ := Lane_q_s09_map.height_hamming_ball_card9 (P.m n) sliceRadius
          (specialWord9 (P.m n) v)
    have hresidualCard : residualIntersection.card ≤
        (Finset.univ.filter (fun z : CubeVertex (n - P.m n) =>
          _root_.hammingDist z (residualWord9 (P.m n) v) ≤ residualRadius)).card := by
      apply Finset.card_le_card
      intro z hz
      simp only [residualIntersection, Finset.mem_filter, Finset.mem_univ, true_and] at hz
      exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, hz.1⟩
    have hmap : ∀ z, z ∈ T → (z.slice, z.location) ∈ sliceBall ×ˢ residualIntersection := by
      intro z hz
      have hzU : z ∈ U := (Finset.mem_filter.mp hz).1
      have hzLocal := hlocal z hzU
      rw [Finset.mem_product]
      constructor
      · simp only [sliceBall, Finset.mem_filter, Finset.mem_univ, true_and]
        exact ⟨hzLocal.1, hzLocal.2.1⟩
      · simp only [residualIntersection, Finset.mem_filter, Finset.mem_univ, true_and]
        exact ⟨hzLocal.2.2.1, hzLocal.2.2.2⟩
    have hinj : Set.InjOn (fun z : Pos9 P hc n => (z.slice, z.location)) T := by
      intro z hz z' hz' hpair
      have hzlev := (Finset.mem_filter.mp hz).2
      have hz'lev := (Finset.mem_filter.mp hz').2
      have hslice : z.slice = z'.slice := congrArg Prod.fst hpair
      have hloc : z.location = z'.location := congrArg Prod.snd hpair
      cases z with
      | mk sl lc lv =>
        cases z' with
        | mk sl' lc' lv' =>
          simp_all
    have himage : T.card = (T.image (fun z : Pos9 P hc n => (z.slice, z.location))).card :=
      (Finset.card_image_of_injOn hinj).symm
    have himageSub : T.image (fun z : Pos9 P hc n => (z.slice, z.location)) ⊆
        sliceBall ×ˢ residualIntersection := by
      intro p hp
      rcases Finset.mem_image.mp hp with ⟨z, hz, rfl⟩
      exact hmap z hz
    have hcardReduction : T.card ≤ sliceBall.card * residualIntersection.card := by
      calc
        T.card = (T.image (fun z : Pos9 P hc n => (z.slice, z.location))).card := himage
        _ ≤ (sliceBall ×ˢ residualIntersection).card := Finset.card_le_card himageSub
        _ = sliceBall.card * residualIntersection.card := by rw [Finset.card_product]
    have hsliceVolume : (sliceBall.card : ℝ) ≤
        (∑ i ∈ Finset.range (sliceRadius + 1), (Nat.choose (P.m n) i : ℝ)) := by
      exact_mod_cast hsliceCard
    have hresidualVolume : (residualIntersection.card : ℝ) ≤
        (∑ i ∈ Finset.range (residualRadius + 1),
          (Nat.choose (n - P.m n) i : ℝ)) := by
      have hcardBall := Lane_q_s09_map.height_hamming_ball_card9 (n - P.m n) residualRadius
        (residualWord9 (P.m n) v)
      exact_mod_cast hresidualCard.trans (by simpa using le_of_eq hcardBall)
    let d : ℕ := n - P.m n
    let r : ℕ := P.radius n
    let R : ℕ := residualRadius
    let x : CubeVertex d := residualWord9 (P.m n) v
    let y : CubeVertex d := residualWord9 (P.m n) v'
    let D : ℕ := _root_.hammingDist x y
    let q : ℝ := (R : ℝ) / (d : ℝ)
    let B : ℝ := (2 : ℝ) ^ D * q ^ (D / 4) + (2 * q) ^ (D / 2)
    have hD : _root_.hammingDist x y = D := rfl
    have hDle : D ≤ d := by
      have h := _root_.hammingDist_le_card_fintype (x := x) (y := y)
      dsimp [D]
      simpa using h
    have hRpos : 1 ≤ R := by dsimp [R, residualRadius]; omega
    have hRhalfReal : 2 * (R : ℝ) ≤ (d : ℝ) := by
      have h100R : (100 : ℝ) * R' ≤ (P.radius n : ℝ) := by
        exact_mod_cast hsmallConsult
      rw [show (d : ℝ) = (n : ℝ) - (P.m n : ℝ) by
        dsimp [d]
        rw [Nat.cast_sub hmle]]
      dsimp [R, residualRadius]
      push_cast
      nlinarith [hsmall.1, hsmall.2.1, h100R, hn44]
    have hRhalf : 2 * R ≤ d := by exact_mod_cast hRhalfReal
    have hDstrongReal : (1018 : ℝ) * R' ≤ (D : ℝ) := by
      have hsepD := hresidualSeparation c hcU
      have hR'pos : (1 : ℝ) ≤ R' := by exact_mod_cast hR
      have hsepD' : (1020 : ℝ) * R' - 2 ≤ (D : ℝ) := by
        simpa [D, x, y, d] using hsepD
      nlinarith
    have hDstrong : 1018 * R' ≤ D := by exact_mod_cast hDstrongReal
    have hk : 1 ≤ D / 4 := by omega
    have hk5 : D ≤ 5 * (D / 4) := by omega
    have hk4 : 4 * (D / 4) ≤ D := by omega
    have hshellGeom := Lane_q_s09_map.height_ball_intersection_shell_sum9
      (d := d) (R := R) (D := D) (k := D / 4) x y hD hDle hRhalf hRpos hk hk4
    have hshell : (residualIntersection.card : ℝ) ≤
        ((R + 1 : ℕ) : ℝ) * (Nat.choose d R : ℝ) * B := by
      have hshell' : (residualIntersection.card : ℝ) ≤
          ((R + 1 : ℕ) : ℝ) * (Nat.choose d R : ℝ) *
            ((2 : ℝ) ^ D * ((R : ℝ) / (d : ℝ)) ^ (D / 4) +
              ((2 * (R : ℝ)) / (d : ℝ)) ^ (D / 2)) := by
        simpa [residualIntersection, R, residualRadius, d, x, y] using hshellGeom
      have hbracket :
          (2 : ℝ) ^ D * ((R : ℝ) / (d : ℝ)) ^ (D / 4) +
            ((2 * (R : ℝ)) / (d : ℝ)) ^ (D / 2) = B := by
        dsimp [B, q]
        ring
      rw [hbracket] at hshell'
      exact hshell'
    have hsmallRadius : R ≤ 2 * r := by
      dsimp [R, r, residualRadius]
      omega
    rcases hP with ⟨hcommon, _, _, hσ, _, _, _⟩
    have hσlt : (P.σ : ℝ) < 1 / 2 := by
      have hxS : P.xS < 1 / 10 := lt_trans hcommon.2.1 hcommon.2.2
      have hσq : P.σ < 1 / 100 := lt_trans hσ.2 (by nlinarith [hxS])
      have hσR : (P.σ : ℝ) < 1 / 100 := by
        simpa using (Rat.cast_lt (K := ℝ)).2 hσq
      linarith
    have hnreal : 0 < (n : ℝ) := by exact_mod_cast (show 0 < n by omega)
    have hnreal1 : 1 ≤ (n : ℝ) := by exact_mod_cast (show 1 ≤ n by omega)
    have hradiusPow : (r : ℝ) ≤ (n : ℝ) ^ (P.σ : ℝ) := by
      simpa [r, Params9.radius] using
        (Nat.floor_le (show (0 : ℝ) ≤ (n : ℝ) ^ (P.σ : ℝ) by positivity))
    have hradiusRoot : (r : ℝ) ≤ (n : ℝ) ^ (1 / 2 : ℝ) :=
      hradiusPow.trans (Real.rpow_le_rpow_of_exponent_le hnreal1 hσlt.le)
    have hRroot : (R : ℝ) ≤ 2 * (n : ℝ) ^ (1 / 2 : ℝ) := by
      have hRcast : (R : ℝ) ≤ 2 * (r : ℝ) := by exact_mod_cast hsmallRadius
      linarith
    have hdLower : (3 : ℝ) * (n : ℝ) / 4 ≤ (d : ℝ) := by
      rw [show (d : ℝ) = (n : ℝ) - (P.m n : ℝ) by
        dsimp [d]
        rw [Nat.cast_sub hmle]]
      linarith [hsmall.1]
    have hnQuarter3 : (3 : ℝ) ≤ (n : ℝ) ^ (1 / 4 : ℝ) := hQuarter n hnQuarter
    have hratioPow : (n : ℝ) ^ (1 / 2 : ℝ) / (n : ℝ) =
        (n : ℝ) ^ (-(1 / 2 : ℝ)) := by
      calc
        (n : ℝ) ^ (1 / 2 : ℝ) / (n : ℝ) =
            (n : ℝ) ^ (1 / 2 : ℝ) / (n : ℝ) ^ (1 : ℝ) := by rw [Real.rpow_one]
        _ = (n : ℝ) ^ ((1 / 2 : ℝ) - 1) :=
          (Real.rpow_sub hnreal (1 / 2 : ℝ) 1).symm
        _ = (n : ℝ) ^ (-(1 / 2 : ℝ)) := by congr 1 <;> norm_num
    have hqBound : q ≤ (n : ℝ) ^ (-(1 / 4 : ℝ)) := by
      have hdpos : 0 < (d : ℝ) := by nlinarith [hdLower, hnreal]
      have hqStep : q ≤ (8 / 3 : ℝ) * (n : ℝ) ^ (-(1 / 2 : ℝ)) := by
        have hratio : q ≤
            (2 * (n : ℝ) ^ (1 / 2 : ℝ)) / (3 * (n : ℝ) / 4) := by
          apply (div_le_iff₀ hdpos).2
          have hdenpos : 0 < (3 : ℝ) * (n : ℝ) / 4 := by positivity
          calc
            (R : ℝ) ≤ 2 * (n : ℝ) ^ (1 / 2 : ℝ) := hRroot
            _ = ((2 * (n : ℝ) ^ (1 / 2 : ℝ)) / (3 * (n : ℝ) / 4)) *
                ((3 : ℝ) * (n : ℝ) / 4) := by field_simp [ne_of_gt hdenpos]
            _ ≤ ((2 * (n : ℝ) ^ (1 / 2 : ℝ)) / (3 * (n : ℝ) / 4)) * (d : ℝ) :=
              mul_le_mul_of_nonneg_left hdLower (by positivity)
        calc
          q ≤ (2 * (n : ℝ) ^ (1 / 2 : ℝ)) / (3 * (n : ℝ) / 4) := hratio
          _ = (8 / 3 : ℝ) * ((n : ℝ) ^ (1 / 2 : ℝ) / (n : ℝ)) := by
            field_simp [ne_of_gt hnreal]
            <;> ring
          _ = (8 / 3 : ℝ) * (n : ℝ) ^ (-(1 / 2 : ℝ)) := by rw [hratioPow]
      have hconst : (8 / 3 : ℝ) ≤ (n : ℝ) ^ (1 / 4 : ℝ) := by nlinarith [hnQuarter3]
      calc
        q ≤ (8 / 3 : ℝ) * (n : ℝ) ^ (-(1 / 2 : ℝ)) := hqStep
        _ ≤ (n : ℝ) ^ (1 / 4 : ℝ) * (n : ℝ) ^ (-(1 / 2 : ℝ)) :=
          mul_le_mul_of_nonneg_right hconst (by positivity)
        _ = (n : ℝ) ^ (-(1 / 4 : ℝ)) := by
          rw [← Real.rpow_add hnreal]
          congr 1
          norm_num
    have hqnonneg : 0 ≤ q := by dsimp [q]; positivity
    have hpow40 : 2 ≤ (n : ℝ) ^ (1 / 40 : ℝ) := h40 n hn40
    have hpow8 : 2 ≤ (n : ℝ) ^ (1 / 8 : ℝ) := h8 n hn8
    have hbinomial := Lane_q_s09_map.height_binomial_ball_power_bound9
      (P.m n) n sliceRadius hmle (by omega : 1 ≤ n)
    have hslicePower : (sliceBall.card : ℝ) ≤ (n : ℝ) ^ (6 * R') := by
      have hsliceBase : (sliceBall.card : ℝ) ≤
          ((sliceRadius + 1 : ℕ) : ℝ) * (n : ℝ) ^ sliceRadius := by
        calc
          (sliceBall.card : ℝ) ≤
              ∑ i ∈ Finset.range (sliceRadius + 1), (Nat.choose (P.m n) i : ℝ) :=
            hsliceVolume
          _ ≤ _ := by simpa [sliceRadius] using hbinomial
      have hsliceSmall : sliceRadius + 1 ≤ n := by
        have h400 : 400 * R' ≤ n := by
          have hmult := Nat.mul_le_mul_right 4 hsmallConsult
          have h4r : 4 * P.radius n ≤ n := by
            have h4rR : 4 * (P.radius n : ℝ) ≤ (n : ℝ) := by linarith [hsmall.2.1]
            exact_mod_cast h4rR
          omega
        dsimp [sliceRadius]
        omega
      have hfactor : ((sliceRadius + 1 : ℕ) : ℝ) ≤ (n : ℝ) ^ sliceRadius := by
        have hfactCast : ((sliceRadius + 1 : ℕ) : ℝ) ≤ (n : ℝ) := by exact_mod_cast hsliceSmall
        have hpower : (n : ℝ) ≤ (n : ℝ) ^ (sliceRadius : ℝ) := by
          calc
            (n : ℝ) = (n : ℝ) ^ (1 : ℝ) := by rw [Real.rpow_one]
            _ ≤ (n : ℝ) ^ (sliceRadius : ℝ) :=
              Real.rpow_le_rpow_of_exponent_le hnreal1 (by exact_mod_cast (show 1 ≤ sliceRadius by dsimp [sliceRadius]; omega))
        simpa [Real.rpow_natCast] using hfactCast.trans hpower
      have hexpNat : 2 * sliceRadius ≤ 6 * R' := by dsimp [sliceRadius]; omega
      calc
        (sliceBall.card : ℝ) ≤
            ((sliceRadius + 1 : ℕ) : ℝ) * (n : ℝ) ^ sliceRadius := hsliceBase
        _ ≤ (n : ℝ) ^ sliceRadius * (n : ℝ) ^ sliceRadius :=
          mul_le_mul_of_nonneg_right hfactor (by positivity)
        _ = (n : ℝ) ^ (2 * sliceRadius) := by rw [show 2 * sliceRadius = sliceRadius + sliceRadius by omega, ← pow_add]
        _ ≤ (n : ℝ) ^ (6 * R') := pow_le_pow_right₀ hnreal1 hexpNat
    have hRplusNat : R + 1 ≤ n ^ 2 := by
      have hRleN : R ≤ n := le_trans hconsultRadius (Nat.sub_le _ _)
      have hn2 : 2 ≤ n := by omega
      have hmul : n + 1 ≤ n * n := by
        have hleft : n + 1 ≤ 2 * n := by omega
        have hright : 2 * n ≤ n * n := by
          have h := Nat.mul_le_mul_left n hn2
          simpa [Nat.mul_comm] using h
        exact hleft.trans hright
      have hpow : n + 1 ≤ n ^ 2 := by simpa [pow_two] using hmul
      exact (Nat.add_le_add_right hRleN 1).trans hpow
    have hRplusPower : ((R + 1 : ℕ) : ℝ) ≤ (n : ℝ) ^ (2 * R') := by
      have hcast : ((R + 1 : ℕ) : ℝ) ≤ (n : ℝ) ^ (2 : ℕ) := by exact_mod_cast hRplusNat
      have hpow : (n : ℝ) ^ (2 : ℕ) ≤ (n : ℝ) ^ (2 * R') :=
        pow_le_pow_right₀ hnreal1 (by omega : 2 ≤ 2 * R')
      exact hcast.trans hpow
    have hrNat : 1 ≤ r := by dsimp [r]; omega
    have ht : 2 * R' + 1 ≤ 3 * R' := by omega
    have hRsplit : r + (2 * R' + 1) = R := by dsimp [r, R, residualRadius]; omega
    have hrplusd : r + (2 * R' + 1) ≤ d := by rw [hRsplit]; exact hconsultRadius
    have hchooseRatio := Lane_q_s09_map.choose_upper_layer_ratio9
      d r (2 * R' + 1) hrNat hrplusd
    have hchooseRpos : 0 < (Nat.choose d r : ℝ) := by
      exact_mod_cast Nat.choose_pos (by omega : r ≤ d)
    have hchooseScaled : (Nat.choose d R : ℝ) ≤
        ((d : ℝ) / (r : ℝ)) ^ (2 * R' + 1) * (Nat.choose d r : ℝ) := by
      have hscaled := (div_le_iff₀ hchooseRpos).1 hchooseRatio
      simpa [hRsplit] using hscaled
    have hdleN : d ≤ n := by dsimp [d]; exact Nat.sub_le _ _
    have hquot : (d : ℝ) / (r : ℝ) ≤ (n : ℝ) := by
      apply (div_le_iff₀ (by exact_mod_cast hrNat : (0 : ℝ) < (r : ℝ))).2
      have hnr : 0 ≤ (n : ℝ) := by positivity
      have hmul := mul_le_mul_of_nonneg_left (by exact_mod_cast hrNat : (1 : ℝ) ≤ (r : ℝ)) hnr
      have hdle : (d : ℝ) ≤ (n : ℝ) := by exact_mod_cast hdleN
      nlinarith
    have hquotPow : ((d : ℝ) / (r : ℝ)) ^ (2 * R' + 1) ≤ (n : ℝ) ^ (2 * R' + 1) := by
      exact pow_le_pow_left₀ (by positivity) hquot (2 * R' + 1)
    have hquotPower : ((d : ℝ) / (r : ℝ)) ^ (2 * R' + 1) ≤ (n : ℝ) ^ (3 * R') :=
      hquotPow.trans (pow_le_pow_right₀ hnreal1 ht)
    have hchooseNat : Nat.choose d r ≤ residualBall9 P n := by
      unfold residualBall9
      simpa [d, r] using
        (Finset.single_le_sum (fun i hi => Nat.zero_le _)
          (Finset.mem_range.mpr (Nat.lt_succ_self (P.radius n))))
    have hchooseLeV : (Nat.choose d R : ℝ) ≤
        (residualBall9 P n : ℝ) * (n : ℝ) ^ (3 * R') := by
      calc
        (Nat.choose d R : ℝ) ≤
            ((d : ℝ) / (r : ℝ)) ^ (2 * R' + 1) * (Nat.choose d r : ℝ) := hchooseScaled
        _ ≤ (n : ℝ) ^ (3 * R') * (residualBall9 P n : ℝ) := by
          exact mul_le_mul hquotPower (by exact_mod_cast hchooseNat)
            (by positivity) (by positivity)
        _ = (residualBall9 P n : ℝ) * (n : ℝ) ^ (3 * R') := by ring
    have hlevelFactor : (((R + 1 : ℕ) : ℝ) * (Nat.choose d R : ℝ)) ≤
        (residualBall9 P n : ℝ) * (n : ℝ) ^ (5 * R') := by
      calc
        _ ≤ (n : ℝ) ^ (2 * R') *
            ((residualBall9 P n : ℝ) * (n : ℝ) ^ (3 * R')) :=
          mul_le_mul hRplusPower hchooseLeV (by positivity) (by positivity)
        _ = (residualBall9 P n : ℝ) * (n : ℝ) ^ (5 * R') := by
          calc
            _ = (residualBall9 P n : ℝ) *
                ((n : ℝ) ^ (2 * R') * (n : ℝ) ^ (3 * R')) := by ring
            _ = (residualBall9 P n : ℝ) * (n : ℝ) ^ (2 * R' + 3 * R') := by rw [← pow_add]
            _ = _ := by congr 2 <;> omega
    have hresidualFinal : (residualIntersection.card : ℝ) ≤
        (residualBall9 P n : ℝ) * (n : ℝ) ^ (5 * R') * B := by
      calc
        (residualIntersection.card : ℝ) ≤
            ((R + 1 : ℕ) : ℝ) * (Nat.choose d R : ℝ) * B := hshell
        _ ≤ (residualBall9 P n : ℝ) * (n : ℝ) ^ (5 * R') * B :=
          mul_le_mul_of_nonneg_right hlevelFactor (by positivity)
    have hcardReductionReal : (T.card : ℝ) ≤
        (sliceBall.card : ℝ) * (residualIntersection.card : ℝ) := by exact_mod_cast hcardReduction
    have htotal : (T.card : ℝ) ≤
        (residualBall9 P n : ℝ) * (n : ℝ) ^ (11 * R') * B := by
      calc
        (T.card : ℝ) ≤
            (sliceBall.card : ℝ) * (residualIntersection.card : ℝ) := hcardReductionReal
        _ ≤ (n : ℝ) ^ (6 * R') *
            ((residualBall9 P n : ℝ) * (n : ℝ) ^ (5 * R') * B) :=
          mul_le_mul hslicePower hresidualFinal
            (by positivity) (by positivity)
        _ = (residualBall9 P n : ℝ) * (n : ℝ) ^ (11 * R') * B := by
          calc
            _ = (residualBall9 P n : ℝ) *
                ((n : ℝ) ^ (6 * R') * (n : ℝ) ^ (5 * R')) * B := by ring
            _ = (residualBall9 P n : ℝ) * (n : ℝ) ^ (6 * R' + 5 * R') * B := by rw [← pow_add]
            _ = _ := by rw [show 6 * R' + 5 * R' = 11 * R' by omega]
    have hpowCast : (n : ℝ) ^ (11 * R' : ℕ) =
        (n : ℝ) ^ ((11 : ℝ) * (R' : ℝ)) := by
      rw [← Real.rpow_natCast]
      congr 1
      norm_num
    have htotalReal : (T.card : ℝ) ≤
        (residualBall9 P n : ℝ) * (n : ℝ) ^ ((11 : ℝ) * (R' : ℝ)) * B := by
      calc
        (T.card : ℝ) ≤ (residualBall9 P n : ℝ) * (n : ℝ) ^ (11 * R') * B := htotal
        _ = (residualBall9 P n : ℝ) *
            (n : ℝ) ^ ((11 : ℝ) * (R' : ℝ)) * B := by rw [hpowCast]
    have hdecay := Lane_q_s09_map.height_overlap_shell_decay9
      (n := n) (R' := R') (D := D) (k := D / 4) q
      (by omega : 2 ≤ n) hR hpow40 hpow8 (by positivity)
      hqBound hk5 hDstrong
    have hdecayNat : (n : ℝ) ^ ((11 : ℝ) * (R' : ℝ)) * B ≤
        Real.exp (-(Real.log 2 * (R' : ℝ))) := by
      simpa [B] using hdecay
    have hVnonneg : (0 : ℝ) ≤ (residualBall9 P n : ℝ) := Nat.cast_nonneg _
    calc
      (T.card : ℝ) ≤ (residualBall9 P n : ℝ) *
          (n : ℝ) ^ ((11 : ℝ) * (R' : ℝ)) * B := htotalReal
      _ ≤ (residualBall9 P n : ℝ) *
          Real.exp (-(Real.log 2 * (R' : ℝ))) :=
        by simpa [mul_assoc] using mul_le_mul_of_nonneg_left hdecayNat hVnonneg

set_option maxHeartbeats 200000

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
