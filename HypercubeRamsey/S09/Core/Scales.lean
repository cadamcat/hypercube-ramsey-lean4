import HypercubeRamsey.S09.Defs
import HypercubeRamsey.S09.Core.Scales_q_s09_misc
import HypercubeRamsey.Framework.Embedding
import Mathlib.Analysis.Complex.ExponentialBounds

/-!
# Section 9: internal scales, special and residual coordinates, the ID map

Source: `sections/09-intermediate-powers-of-bias.tex`, lines 32–39 (constants), 63–118 (the ID map);
blueprint `research/blueprint/PART-B.md` §3.9, P9.2c "Internal constants".

Every internal constant of Proposition 9.2's one-dimension core is an explicit function of the parameter record
`P : Params9` and the dimension `n`:

* `u = x_s/2`, `a_* = n^{-h_+}/2`, `b_* = n^{-h_-}` (09:32–35);
* the number of special bits `m = ⌊n^{y_m}⌋` (sublinear) or `⌊α_d n/10⌋` (linear) (09:37–39);
* the residual radius `r = ⌊n^σ⌋` (09:66) and the crowd slack `ε` with `0 < ε < σ` and, in the sublinear case,
  `1 - σ + ε < y_d` (09:83, 114–118), so that the ID budget `T = n^{1-σ+ε}` fits the filter budget;
* the exponential tail `exp(-c n^u)` and the gain constant `c₄ = 1/2` (09:150).

The ID map (09:63–118) is the coloring-independent output of the adapted height experiment: a map from cube
sites to center IDs `(slice, residual location, level)` with the odd-row ID bound `T + m`, a core of size at
most `n^χ` at every even site, and read multiplicity `r + 3` outside the core.  `IDMap9 P n` records exactly
these properties, with `m`, `r` and `T` fixed by the definitions above.
-/

namespace HypercubeRamsey

open OAI.HypercubeRamsey Classical Filter
open scoped BigOperators

namespace Params9

/-- `u = x_s/2` (09:32). -/
noncomputable def u (P : Params9) : ℝ := (P.xS : ℝ) / 2

/-- `a_* = n^{-h_+}/2` (09:35): half the available shallow bias. -/
noncomputable def aStar (P : Params9) (n : ℕ) : ℝ := (n : ℝ) ^ (-(P.hPlus : ℝ)) / 2

/-- `b_* = n^{-h_-}` (09:35): the deep discrepancy error. -/
noncomputable def bStar (P : Params9) (n : ℕ) : ℝ := (n : ℝ) ^ (-(P.hMinus : ℝ))

/-- The number of special bits (09:37, 09:39): `⌊n^{y_m}⌋` in the sublinear case and `⌊α_d n/10⌋` in the
linear case. -/
noncomputable def m (P : Params9) (n : ℕ) : ℕ :=
  match P.case with
  | .sub _ _ yM => ⌊(n : ℝ) ^ (yM : ℝ)⌋₊
  | .lin _ αD _ _ => ⌊(αD : ℝ) * n / 10⌋₊

/-- The residual radius `r = ⌊n^σ⌋` (09:66). -/
noncomputable def radius (P : Params9) (n : ℕ) : ℕ := ⌊(n : ℝ) ^ (P.σ : ℝ)⌋₊

/-- The crowd slack `ε` of the radius-`(r+1)` crowd test (09:76–83) and of the ID budget (09:114–118).  It
satisfies `0 < ε < σ` and, in the sublinear case, `1 - σ + ε < y_d` (node `eps_bounds9`), which is the "filter
budget slack" of 09:83. -/
noncomputable def eps (P : Params9) : ℝ :=
  match P.case with
  | .sub _ yD _ => min (P.σ : ℝ) ((yD : ℝ) - (1 - (P.σ : ℝ))) / 2
  | .lin _ _ _ _ => (P.σ : ℝ) / 2

/-- The ID budget `T = n^{1-σ+ε}` at an odd row (09:68–69, 09:104–105). -/
noncomputable def idBudget (P : Params9) (n : ℕ) : ℝ := (n : ℝ) ^ (1 - (P.σ : ℝ) + P.eps)

/-- The width budget of a filtered second law whose hits each retained at least `.49` (09:162, 09:118):
`S_s + n^u + log 2 + log(1/.49)(T + m)`; the masked starting law costs `n^u + log 2` (mask mass
`≥ ½ e^{-n^u}`). -/
noncomputable def filterBudget (P : Params9) (n : ℕ) : ℝ :=
  P.Ss (n : ℝ) + (n : ℝ) ^ P.u + Real.log 2 +
    Real.log (100 / 49) * (P.idBudget n + (P.m n : ℝ))

/-- The tail `exp(-c n^u)`; the paper's `exp(-Ω(n^u))` is this for some fixed `c > 0`. -/
noncomputable def tail (P : Params9) (c : ℝ) (n : ℕ) : ℝ := Real.exp (-(c * (n : ℝ) ^ P.u))

/-- The extra parameter condition used by the core in the sublinear case (09:122–124): `x_s < y_m`, so that the
first-law cap `e^{n^{x_s} + O(log n)}` of the tag loads is below `2^m`.  The paper's selection has `y` close to
`1` (09:44–46), and any valid sublinear selection can be upgraded by raising `y_m` inside `(y_s, 1 - σ)` (node
`p92_admissible_sublinear`); the linear case needs nothing (`m = ⌊α_d n/10⌋`). -/
def CoreAdmissible (P : Params9) : Prop :=
  match P.case with
  | .sub _ _ yM => P.xS < yM
  | .lin _ _ _ _ => True

end Params9

/-- The gain constant `c₄` of (9.1) (09:150).  The paper only needs some small absolute constant; `1/2` leaves
room in every estimate of 09:270–294 (ordinary neighbours give `(1-o(1))(n-m)a_*`, special neighbours lose at
most `.06 n a_*`, the concentration loses `.1 n a_*`, and the quadratic loss is `o(n a_*)`). -/
noncomputable def gainConst9 : ℝ := 1 / 2

/-! ## Special and residual coordinates -/

/-- The special word of a site: its first `m` coordinates (09:63; coordinates beyond `n` read `false`, which
never happens once `m ≤ n`). -/
def specialWord9 (m : ℕ) {n : ℕ} (v : CubeVertex n) : CubeVertex m :=
  fun j => if h : (j : ℕ) < n then v ⟨j, h⟩ else false

/-- The residual word of a site: its coordinates `m, …, n-1` (09:63). -/
def residualWord9 (m : ℕ) {n : ℕ} (v : CubeVertex n) : CubeVertex (n - m) :=
  fun j => v ⟨m + j, by have := j.isLt; omega⟩

/-- Flip one special bit of a special word (09:126, `z^j`). -/
def flipWord9 {m : ℕ} (z : CubeVertex m) (j : Fin m) : CubeVertex m :=
  Function.update z j (!z j)

/-- A center ID (09:63–65): a slice (special word), a residual location and a level. -/
structure CenterID9 (m k H : ℕ) where
  slice : CubeVertex m
  location : CubeVertex k
  level : Fin (H + 1)
  deriving DecidableEq

private def centerIDEquiv9 (m k H : ℕ) :
    CenterID9 m k H ≃ CubeVertex m × CubeVertex k × Fin (H + 1) where
  toFun c := (c.slice, c.location, c.level)
  invFun p := ⟨p.1, p.2.1, p.2.2⟩
  left_inv c := by cases c; rfl
  right_inv p := by rcases p with ⟨a, b, c⟩; rfl

noncomputable instance instFintypeCenterID9 (m k H : ℕ) : Fintype (CenterID9 m k H) :=
  Fintype.ofEquiv (CubeVertex m × CubeVertex k × Fin (H + 1)) (centerIDEquiv9 m k H).symm

/-- The even sites of the cube (placed on the first host side). -/
abbrev EvenSites9 (n : ℕ) := {v : CubeVertex n // IsEvenRole v}

/-- The odd sites of the cube (placed on the second host side); their rows carry the filters. -/
abbrev OddSites9 (n : ℕ) := {v : CubeVertex n // ¬ IsEvenRole v}

/-- `I_b`: the IDs of the sites adjacent to `b` under a site-to-ID map (09:68). -/
noncomputable def seenIDs9 {n : ℕ} {α : Type*} [DecidableEq α] (c : CubeVertex n → α)
    (b : CubeVertex n) : Finset α :=
  (Finset.univ.filter (fun a : CubeVertex n => (cube n).Adj b a)).image c

/-- P9.2-map2 output (09:63–118): the fixed coloring-independent ID map with its read structure.

* `center v` lies in the slice of `v` at residual distance at most `r` (09:63–64);
* an odd row sees at most `T + m` distinct IDs (09:68, 09:104–105);
* every even site `v` has a core containing its own ID, of size at most `n^χ`, and every ID outside the core is
  seen at no more than `r + 3` odd neighbours of `v` (09:69, 09:106–112).

The core is stored for every site; only even sites use it. -/
structure IDMap9 (P : Params9) (n : ℕ) where
  levels : ℕ
  center : CubeVertex n → CenterID9 (P.m n) (n - P.m n) levels
  center_slice : ∀ v, (center v).slice = specialWord9 (P.m n) v
  center_near : ∀ v, _root_.hammingDist (center v).location (residualWord9 (P.m n) v) ≤ P.radius n
  odd_ids : ∀ b : CubeVertex n, ¬ IsEvenRole b →
    ((seenIDs9 center b).card : ℝ) ≤ P.idBudget n + (P.m n : ℝ)
  core : CubeVertex n → Finset (CenterID9 (P.m n) (n - P.m n) levels)
  center_mem_core : ∀ v, IsEvenRole v → center v ∈ core v
  core_card : ∀ v, IsEvenRole v → ((core v).card : ℝ) ≤ (n : ℝ) ^ (P.χ : ℝ)
  read_bound : ∀ v, IsEvenRole v → ∀ id, id ∉ core v →
    (Finset.univ.filter (fun b : CubeVertex n =>
      (cube n).Adj v b ∧ id ∈ seenIDs9 center b)).card ≤ P.radius n + 3

/-- The ID type of an ID map. -/
abbrev IDMap9.ID {P : Params9} {n : ℕ} (I : IDMap9 P n) := CenterID9 (P.m n) (n - P.m n) I.levels

/-- The IDs seen at an odd row. -/
noncomputable def IDMap9.seen {P : Params9} {n : ℕ} (I : IDMap9 P n) (b : CubeVertex n) :
    Finset I.ID :=
  seenIDs9 I.center b

/-- The exponent facts of 09:32–39 used throughout the core: `0 < ε < σ < u` and `χ < u/50`. -/
def ScaleExps9 (P : Params9) : Prop :=
  0 < P.eps ∧ P.eps < (P.σ : ℝ) ∧ 0 < P.u ∧ (P.σ : ℝ) < P.u ∧ (P.χ : ℝ) < P.u / 50

/-- The per-dimension scale facts used by the core nodes (09:32–39, 09:83, 09:114–118, 09:163, 09:249, 09:316,
09:334): `m ≤ n`, `r ≥ 1`, `S_s + log n < m log 2` (the second-law tag loads, 09:122–124), the filter budget fits
the deep second width with room `n^u` (09:118, 09:162), the first deep width has room `n^{u+8χ}` over the anchor
width (09:163, 09:249), `b_* ≤ 1/200` (so `1/2 - 2b_* ≥ .49`), and `r log n`, `n^{x_s}`, `n^u` are `o(n a_*)`
(09:316, 09:334). -/
def ScalesAt9 (P : Params9) (n : ℕ) : Prop :=
  1 ≤ n ∧ P.m n ≤ n ∧ 1 ≤ P.radius n ∧
  P.Ss (n : ℝ) + Real.log (n : ℝ) < (P.m n : ℝ) * Real.log 2 ∧
  P.filterBudget n + (n : ℝ) ^ P.u ≤ P.Sd (n : ℝ) ∧
  (n : ℝ) ^ (P.xS : ℝ) + (P.hPlus : ℝ) * Real.log (n : ℝ) + 1 + (n : ℝ) ^ (P.u + 8 * (P.χ : ℝ)) ≤
    (n : ℝ) ^ (P.xD : ℝ) ∧
  P.bStar n ≤ 1 / 200 ∧
  ((P.radius n : ℝ) + 8) * Real.log ((n : ℝ) + 1) + (n : ℝ) ^ (P.xS : ℝ) + 4 * (n : ℝ) ^ P.u ≤
    gainConst9 * (n : ℝ) * P.aStar n / 100

set_option maxHeartbeats 0 in
/-- Arithmetic consequences of `Params9.Valid` for the internal scales: the exponent facts, and the
per-dimension facts for all large `n`.  (In the sublinear case `y_s < y_m < 1 - σ < y_d` and `1 - σ + ε < y_d`;
in the linear case `S_s + log(100/49)(T + m) ≈ (α_s + .0713 α_d) n + o(n) < α_d n`.) -/
theorem scales_eventually9 (P : Params9) (hP : P.Valid) :
    ScaleExps9 P ∧ ∃ n₀ : ℕ, ∀ n ≥ n₀, ScalesAt9 P n := by
  classical
  cases hcase : P.case with
  | sub yS yD yM =>
      simp only [Params9.Valid, hcase] at hP
      rcases hP with ⟨⟨hxs0, hxsxd, hxd010⟩, ⟨hm0, hmm, hmp1⟩, hmargin,
        ⟨hsig0, hsigxs⟩, ⟨hchi0, hchibound⟩, hgap,
        hys0, hsym, hymupper, hysigd, hyd1, hchiSig⟩
      have hxs0R : 0 < (P.xS : ℝ) := by
        simpa using Lane_q_s09_misc.ratCast_lt hxs0
      have hxsxdR : (P.xS : ℝ) < (P.xD : ℝ) :=
        Lane_q_s09_misc.ratCast_lt hxsxd
      have hxd010R : (P.xD : ℝ) < (1 / 10 : ℝ) := by
        simpa using Lane_q_s09_misc.ratCast_lt hxd010
      have hminusPosR : 0 < (P.hMinus : ℝ) := by
        simpa using Lane_q_s09_misc.ratCast_lt hm0
      have hmmR : (P.hMinus : ℝ) < (P.hPlus : ℝ) :=
        Lane_q_s09_misc.ratCast_lt hmm
      have hplusPosR : 0 < (P.hPlus : ℝ) := lt_trans hminusPosR hmmR
      have hplusOneR : (P.hPlus : ℝ) < 1 := by
        simpa using Lane_q_s09_misc.ratCast_lt hmp1
      have hmarginR : (P.xD : ℝ) < (1 - (P.hPlus : ℝ)) / 10 := by
        simpa using Lane_q_s09_misc.ratCast_lt hmargin
      have hsigPosR : 0 < (P.σ : ℝ) := by
        simpa using Lane_q_s09_misc.ratCast_lt hsig0
      have hsigXsR : (P.σ : ℝ) < (P.xS : ℝ) / 10 := by
        simpa using Lane_q_s09_misc.ratCast_lt hsigxs
      have hchiPosR : 0 < (P.χ : ℝ) := by
        simpa using Lane_q_s09_misc.ratCast_lt hchi0
      have hchiBoundR : (P.χ : ℝ) <
          min (P.xS : ℝ) (min (P.hMinus : ℝ) (1 - (P.hPlus : ℝ))) / 100 := by
        simpa using Lane_q_s09_misc.ratCast_lt hchibound
      have hys0R : 0 < (yS : ℝ) := by
        simpa using Lane_q_s09_misc.ratCast_lt hys0
      have hsymR : (yS : ℝ) < (yM : ℝ) :=
        Lane_q_s09_misc.ratCast_lt hsym
      have hymUpperR : (yM : ℝ) < 1 - (P.σ : ℝ) := by
        simpa using Lane_q_s09_misc.ratCast_lt hymupper
      have hysigdR : 1 - (P.σ : ℝ) < (yD : ℝ) := by
        simpa using Lane_q_s09_misc.ratCast_lt hysigd
      have hyd1R : (yD : ℝ) < 1 := by
        simpa using Lane_q_s09_misc.ratCast_lt hyd1
      have hepsPos : 0 < P.eps := by
        rw [Params9.eps, hcase]
        exact div_pos (lt_min hsigPosR (sub_pos.mpr hysigdR)) (by norm_num)
      have hepsSigma : P.eps < (P.σ : ℝ) := by
        rw [Params9.eps, hcase]
        have hmin : min (P.σ : ℝ) ((yD : ℝ) - (1 - (P.σ : ℝ))) ≤ P.σ :=
          min_le_left _ _
        nlinarith [hsigPosR]
      have huPos : 0 < P.u := by
        rw [Params9.u]
        exact div_pos hxs0R (by norm_num)
      have hsigU : (P.σ : ℝ) < P.u := by
        rw [Params9.u]
        linarith
      have hchiXsR : (P.χ : ℝ) < (P.xS : ℝ) / 100 :=
        lt_of_lt_of_le hchiBoundR
          (div_le_div_of_nonneg_right (min_le_left _ _) (by norm_num))
      have hchiU : (P.χ : ℝ) < P.u / 50 := by
        rw [Params9.u]
        nlinarith [hchiXsR]
      have hExps : ScaleExps9 P :=
        ⟨hepsPos, hepsSigma, huPos, hsigU, hchiU⟩
      have hysydR : (yS : ℝ) < (yD : ℝ) :=
        lt_trans hsymR (lt_trans hymUpperR hysigdR)
      have hymydR : (yM : ℝ) < (yD : ℝ) :=
        lt_trans hymUpperR hysigdR
      have huYd : P.u < (yD : ℝ) := by
        have hxsSmall : (P.xS : ℝ) < 1 / 10 := lt_trans hxsxdR hxd010R
        rw [Params9.u]
        linarith [hysigdR]
      have hidYd : 1 - (P.σ : ℝ) + P.eps < (yD : ℝ) := by
        rw [Params9.eps, hcase]
        have hgapY : 0 < (yD : ℝ) - (1 - (P.σ : ℝ)) := sub_pos.mpr hysigdR
        have hmin : min (P.σ : ℝ) ((yD : ℝ) - (1 - (P.σ : ℝ))) ≤
            (yD : ℝ) - (1 - (P.σ : ℝ)) := min_le_right _ _
        nlinarith [hgapY]
      have hxsPlus : (P.xS : ℝ) < (1 - (P.hPlus : ℝ)) := by
        linarith [hmarginR, hxsxdR]
      have huChiXd : P.u + 8 * (P.χ : ℝ) < (P.xD : ℝ) := by
        rw [Params9.u]
        have hchiSmall : 8 * (P.χ : ℝ) < 8 * ((P.xS : ℝ) / 100) := by
          nlinarith [hchiXsR]
        nlinarith [hchiXsR, hchiSmall, hxsxdR]
      let δS : ℝ := (yM : ℝ) / 2
      have hδSpos : 0 < δS := by
        dsimp [δS]
        linarith [hsymR, hys0R]
      have hδSlt : δS < (yM : ℝ) := by dsimp [δS]; linarith [hδSpos]
      have hCpos : 0 < Real.log (100 / 49 : ℝ) :=
        Real.log_pos (by norm_num : (1 : ℝ) < 100 / 49)
      have hCtwo : Real.log (100 / 49 : ℝ) < 2 := by
        have hlog := Real.log_lt_sub_one_of_pos (by norm_num : (0 : ℝ) < 100 / 49)
          (by norm_num : (100 / 49 : ℝ) ≠ 1)
        norm_num at hlog ⊢
        linarith
      have hShallowPow : ∀ᶠ n : ℕ in atTop,
          8 * (n : ℝ) ^ (yS : ℝ) ≤ (n : ℝ) ^ (yM : ℝ) :=
        Lane_q_s09_misc.eventually_nat_rpow_const_mul_le
          (a := (yS : ℝ)) (b := (yM : ℝ)) (c := 8) hsymR
      have hShallowLog : ∀ᶠ n : ℕ in atTop,
          (8 / δS) * (n : ℝ) ^ δS ≤ (n : ℝ) ^ (yM : ℝ) :=
        Lane_q_s09_misc.eventually_nat_rpow_const_mul_le
          (a := δS) (b := (yM : ℝ)) (c := 8 / δS) hδSlt
      have hLogEvent : ∀ᶠ n : ℕ in atTop,
          Real.log (n : ℝ) ≤ (n : ℝ) ^ δS / δS :=
        Lane_q_s09_misc.eventually_nat_log_le_rpow_div hδSpos
      have hPowBig : ∀ᶠ n : ℕ in atTop, 2 ≤ (n : ℝ) ^ (yM : ℝ) := by
        have ht : Tendsto (fun n : ℕ => (n : ℝ) ^ (yM : ℝ)) atTop atTop :=
          (tendsto_rpow_atTop (by linarith [hys0R, hsymR])).comp tendsto_natCast_atTop_atTop
        exact ht.eventually (eventually_ge_atTop 2)
      have hFiltYs : ∀ᶠ n : ℕ in atTop,
          6 * (n : ℝ) ^ (yS : ℝ) ≤ (n : ℝ) ^ (yD : ℝ) :=
        Lane_q_s09_misc.eventually_nat_rpow_const_mul_le
          (a := (yS : ℝ)) (b := (yD : ℝ)) (c := 6) hysydR
      have hFiltU : ∀ᶠ n : ℕ in atTop,
          12 * (n : ℝ) ^ P.u ≤ (n : ℝ) ^ (yD : ℝ) :=
        Lane_q_s09_misc.eventually_nat_rpow_const_mul_le
          (a := P.u) (b := (yD : ℝ)) (c := 12) huYd
      have hFiltConst : ∀ᶠ n : ℕ in atTop,
          6 * Real.log 2 ≤ (n : ℝ) ^ (yD : ℝ) := by
        have he := Lane_q_s09_misc.eventually_nat_rpow_const_mul_le
          (a := 0) (b := (yD : ℝ)) (c := 6 * Real.log 2)
          (by linarith [hys0R, hsymR, hymydR])
        filter_upwards [he] with n hn
        simpa using hn
      have hFiltId : ∀ᶠ n : ℕ in atTop,
          (6 * Real.log (100 / 49 : ℝ)) *
            (n : ℝ) ^ (1 - (P.σ : ℝ) + P.eps) ≤ (n : ℝ) ^ (yD : ℝ) :=
        Lane_q_s09_misc.eventually_nat_rpow_const_mul_le
          (a := 1 - (P.σ : ℝ) + P.eps) (b := (yD : ℝ))
          (c := 6 * Real.log (100 / 49 : ℝ)) hidYd
      have hFiltM : ∀ᶠ n : ℕ in atTop,
          (6 * Real.log (100 / 49 : ℝ)) * (n : ℝ) ^ (yM : ℝ) ≤ (n : ℝ) ^ (yD : ℝ) :=
        Lane_q_s09_misc.eventually_nat_rpow_const_mul_le
          (a := (yM : ℝ)) (b := (yD : ℝ)) (c := 6 * Real.log (100 / 49 : ℝ)) hymydR
      have hAnchorXs : ∀ᶠ n : ℕ in atTop,
          4 * (n : ℝ) ^ (P.xS : ℝ) ≤ (n : ℝ) ^ (P.xD : ℝ) :=
        Lane_q_s09_misc.eventually_nat_rpow_const_mul_le
          (a := (P.xS : ℝ)) (b := (P.xD : ℝ)) (c := 4) hxsxdR
      let δA : ℝ := (P.xD : ℝ) / 2
      have hδApos : 0 < δA := by dsimp [δA]; linarith [hxs0R, hxsxdR]
      have hδAxd : δA < (P.xD : ℝ) := by dsimp [δA]; linarith [hδApos]
      have hAnchorLog : ∀ᶠ n : ℕ in atTop,
          (4 * (P.hPlus : ℝ) / δA) * (n : ℝ) ^ δA ≤ (n : ℝ) ^ (P.xD : ℝ) :=
        Lane_q_s09_misc.eventually_nat_rpow_const_mul_le
          (a := δA) (b := (P.xD : ℝ)) (c := 4 * (P.hPlus : ℝ) / δA) hδAxd
      have hLogAnchorEvent : ∀ᶠ n : ℕ in atTop,
          Real.log (n : ℝ) ≤ (n : ℝ) ^ δA / δA :=
        Lane_q_s09_misc.eventually_nat_log_le_rpow_div hδApos
      have hAnchorConst : ∀ᶠ n : ℕ in atTop,
          4 ≤ (n : ℝ) ^ (P.xD : ℝ) := by
        have he := Lane_q_s09_misc.eventually_nat_rpow_const_mul_le
          (a := 0) (b := (P.xD : ℝ)) (c := 4) (by linarith [hxs0R, hxsxdR])
        filter_upwards [he] with n hn
        simpa using hn
      have hAnchorDeep : ∀ᶠ n : ℕ in atTop,
          4 * (n : ℝ) ^ (P.u + 8 * (P.χ : ℝ)) ≤ (n : ℝ) ^ (P.xD : ℝ) :=
        Lane_q_s09_misc.eventually_nat_rpow_const_mul_le
          (a := P.u + 8 * (P.χ : ℝ)) (b := (P.xD : ℝ)) (c := 4) huChiXd
      have hBStar : ∀ᶠ n : ℕ in atTop,
          200 * (n : ℝ) ^ (-(P.hMinus : ℝ)) ≤ 1 := by
        have he := Lane_q_s09_misc.eventually_nat_rpow_const_mul_le
          (a := -(P.hMinus : ℝ)) (b := 0) (c := 200) (by linarith [hminusPosR])
        filter_upwards [he] with n hn
        simpa using hn
      have hGainRpos : 0 < 1 - (P.hPlus : ℝ) := by linarith [hplusOneR]
      have hSigmaGain : (P.σ : ℝ) < 1 - (P.hPlus : ℝ) := by
        linarith [hsigXsR, hxsxdR, hmarginR]
      let δG : ℝ := (1 - (P.hPlus : ℝ) - (P.σ : ℝ)) / 2
      have hδGpos : 0 < δG := by dsimp [δG]; linarith [hSigmaGain]
      have hδGone : δG ≤ 1 := by
        dsimp [δG]
        linarith [hplusPosR, hsigPosR]
      have hGainPow : (P.σ : ℝ) + δG < 1 - (P.hPlus : ℝ) := by
        dsimp [δG]
        linarith [hSigmaGain]
      have hGainFirst : ∀ᶠ n : ℕ in atTop,
          (1200 * (18 / δG)) * (n : ℝ) ^ ((P.σ : ℝ) + δG) ≤
            (n : ℝ) ^ (1 - (P.hPlus : ℝ)) :=
        Lane_q_s09_misc.eventually_nat_rpow_const_mul_le
          (a := (P.σ : ℝ) + δG) (b := 1 - (P.hPlus : ℝ))
          (c := 1200 * (18 / δG)) hGainPow
      have hGainXs : ∀ᶠ n : ℕ in atTop,
          1200 * (n : ℝ) ^ (P.xS : ℝ) ≤ (n : ℝ) ^ (1 - (P.hPlus : ℝ)) :=
        Lane_q_s09_misc.eventually_nat_rpow_const_mul_le
          (a := (P.xS : ℝ)) (b := 1 - (P.hPlus : ℝ)) (c := 1200) (by
            linarith [hmarginR, hxsxdR])
      have hGainU : ∀ᶠ n : ℕ in atTop,
          4800 * (n : ℝ) ^ P.u ≤ (n : ℝ) ^ (1 - (P.hPlus : ℝ)) :=
        Lane_q_s09_misc.eventually_nat_rpow_const_mul_le
          (a := P.u) (b := 1 - (P.hPlus : ℝ)) (c := 4800) (by
            rw [Params9.u]
            linarith [hmarginR, hxsxdR])
      have hLogGainEvent : ∀ᶠ n : ℕ in atTop,
          Real.log ((n : ℝ) + 1) ≤ (2 / δG) * (n : ℝ) ^ δG :=
        Lane_q_s09_misc.eventually_nat_log_succ_le_rpow hδGpos hδGone
      have hLarge : ∀ᶠ n : ℕ in atTop, 2 ≤ n := eventually_ge_atTop 2
      have hScales : ∀ᶠ n : ℕ in atTop, ScalesAt9 P n := by
        filter_upwards [hLarge, hShallowPow, hShallowLog, hLogEvent, hPowBig,
          hFiltYs, hFiltU, hFiltConst, hFiltId, hFiltM, hAnchorXs, hAnchorLog,
          hLogAnchorEvent, hAnchorConst, hAnchorDeep, hBStar, hGainFirst,
          hGainXs, hGainU, hLogGainEvent] with n hn hsy hslog hlogS hpowS
          hfys hfu hfc hfi hfm haxs halog hlogA hac had hb hg1 hgx hgu hlogG
        have hnR : 1 ≤ (n : ℝ) := by exact_mod_cast (by omega : 1 ≤ n)
        have hnPos : 0 < (n : ℝ) := lt_of_lt_of_le zero_lt_one hnR
        have hyMpos : 0 < (n : ℝ) ^ (yM : ℝ) := Real.rpow_pos_of_pos hnPos _
        have hmFloorU : (P.m n : ℝ) ≤ (n : ℝ) ^ (yM : ℝ) := by
          simpa [Params9.m, hcase] using Nat.floor_le (by positivity :
            0 ≤ (n : ℝ) ^ (yM : ℝ))
        have hmFloorL : (n : ℝ) ^ (yM : ℝ) - 1 < (P.m n : ℝ) := by
          have hf := Nat.lt_floor_add_one ((n : ℝ) ^ (yM : ℝ))
          have hf' : (n : ℝ) ^ (yM : ℝ) < (P.m n : ℝ) + 1 := by
            simpa [Params9.m, hcase] using hf
          linarith
        have hymOne : (yM : ℝ) < 1 := lt_trans hymUpperR (by linarith [hsigPosR])
        have hmLeNreal : (P.m n : ℝ) ≤ (n : ℝ) := by
          calc
            (P.m n : ℝ) ≤ (n : ℝ) ^ (yM : ℝ) := hmFloorU
            _ ≤ (n : ℝ) ^ (1 : ℝ) := Real.rpow_le_rpow_of_exponent_le hnR hymOne.le
            _ = (n : ℝ) := by simp
        have hmLeN : P.m n ≤ n := by exact_mod_cast hmLeNreal
        have hradiusBase : 1 ≤ (n : ℝ) ^ (P.σ : ℝ) := by
          calc
            1 = (n : ℝ) ^ (0 : ℝ) := by simp
            _ ≤ (n : ℝ) ^ (P.σ : ℝ) :=
              Real.rpow_le_rpow_of_exponent_le hnR hsigPosR.le
        have hradius : 1 ≤ P.radius n := by
          change 1 ≤ Nat.floor ((n : ℝ) ^ (P.σ : ℝ))
          exact (Nat.one_le_floor_iff _).2 hradiusBase
        have hShallowLeft : (n : ℝ) ^ (yS : ℝ) + Real.log (n : ℝ) <
            (P.m n : ℝ) * Real.log 2 := by
          have hysSmall : (n : ℝ) ^ (yS : ℝ) ≤ (n : ℝ) ^ (yM : ℝ) / 8 := by
            linarith only [hsy]
          have hlogSmall : Real.log (n : ℝ) ≤ (n : ℝ) ^ (yM : ℝ) / 8 := by
            calc
              Real.log (n : ℝ) ≤ (n : ℝ) ^ δS / δS := hlogS
              _ = (1 / 8 : ℝ) * ((8 / δS) * (n : ℝ) ^ δS) := by ring
              _ ≤ (1 / 8 : ℝ) * (n : ℝ) ^ (yM : ℝ) :=
                mul_le_mul_of_nonneg_left hslog (by norm_num)
              _ = (n : ℝ) ^ (yM : ℝ) / 8 := by ring
          have hcoef : (1 / 4 : ℝ) < Real.log 2 / 2 := by
            linarith only [Real.log_two_gt_d9]
          have hcoefPow : (1 / 4 : ℝ) * (n : ℝ) ^ (yM : ℝ) <
              (Real.log 2 / 2) * (n : ℝ) ^ (yM : ℝ) :=
            mul_lt_mul_of_pos_right hcoef hyMpos
          have hfloorHalf : (n : ℝ) ^ (yM : ℝ) / 2 ≤ (P.m n : ℝ) := by
            have hhalf : (n : ℝ) ^ (yM : ℝ) / 2 ≤ (n : ℝ) ^ (yM : ℝ) - 1 := by
              linarith only [hpowS]
            exact le_trans hhalf hmFloorL.le
          have hfloorLog : (Real.log 2 / 2) * (n : ℝ) ^ (yM : ℝ) ≤
              (P.m n : ℝ) * Real.log 2 := by
            calc
              (Real.log 2 / 2) * (n : ℝ) ^ (yM : ℝ) =
                  Real.log 2 * ((n : ℝ) ^ (yM : ℝ) / 2) := by ring
              _ ≤ Real.log 2 * (P.m n : ℝ) :=
                mul_le_mul_of_nonneg_left hfloorHalf (by positivity)
              _ = (P.m n : ℝ) * Real.log 2 := by ring
          linarith only [hysSmall, hlogSmall, hcoefPow, hfloorLog]
        have hFilterEq : P.filterBudget n + (n : ℝ) ^ P.u =
            (n : ℝ) ^ (yS : ℝ) + (n : ℝ) ^ P.u + Real.log 2 +
              Real.log (100 / 49 : ℝ) *
                ((n : ℝ) ^ (1 - (P.σ : ℝ) + P.eps) + (P.m n : ℝ)) +
              (n : ℝ) ^ P.u := by
          simp [Params9.filterBudget, Params9.Ss, Params9.idBudget, hcase]
        have hFilter : P.filterBudget n + (n : ℝ) ^ P.u ≤ (n : ℝ) ^ (yD : ℝ) := by
          rw [hFilterEq]
          have hf1 : (n : ℝ) ^ (yS : ℝ) ≤ (n : ℝ) ^ (yD : ℝ) / 6 := by nlinarith [hfys]
          have hfu' : (n : ℝ) ^ P.u ≤ (n : ℝ) ^ (yD : ℝ) / 12 := by nlinarith [hfu]
          have hfc' : Real.log 2 ≤ (n : ℝ) ^ (yD : ℝ) / 6 := by nlinarith [hfc]
          have hfi' : Real.log (100 / 49 : ℝ) *
              (n : ℝ) ^ (1 - (P.σ : ℝ) + P.eps) ≤ (n : ℝ) ^ (yD : ℝ) / 6 := by
            nlinarith [hfi]
          have hfm' : Real.log (100 / 49 : ℝ) * (n : ℝ) ^ (yM : ℝ) ≤
              (n : ℝ) ^ (yD : ℝ) / 6 := by nlinarith [hfm]
          have hfmCast : Real.log (100 / 49 : ℝ) * (P.m n : ℝ) ≤
              Real.log (100 / 49 : ℝ) * (n : ℝ) ^ (yM : ℝ) :=
            mul_le_mul_of_nonneg_left hmFloorU (le_of_lt hCpos)
          have htwoU : 2 * (n : ℝ) ^ P.u ≤ (n : ℝ) ^ (yD : ℝ) / 6 := by
            nlinarith [hfu']
          have hyDpos : 0 < (n : ℝ) ^ (yD : ℝ) := Real.rpow_pos_of_pos hnPos _
          ring_nf
          nlinarith [hf1, htwoU, hfc', hfi', hfm', hfmCast, hyDpos]
        have hAnchor :
            (n : ℝ) ^ (P.xS : ℝ) + (P.hPlus : ℝ) * Real.log (n : ℝ) + 1 +
                (n : ℝ) ^ (P.u + 8 * (P.χ : ℝ)) ≤ (n : ℝ) ^ (P.xD : ℝ) := by
          have hax : (n : ℝ) ^ (P.xS : ℝ) ≤ (n : ℝ) ^ (P.xD : ℝ) / 4 := by nlinarith [haxs]
          have halog' : (P.hPlus : ℝ) * Real.log (n : ℝ) ≤
              (n : ℝ) ^ (P.xD : ℝ) / 4 := by
            calc
              (P.hPlus : ℝ) * Real.log (n : ℝ) ≤
                  (P.hPlus : ℝ) * ((n : ℝ) ^ δA / δA) :=
                mul_le_mul_of_nonneg_left hlogA (le_of_lt hplusPosR)
              _ = ((P.hPlus : ℝ) / δA) * (n : ℝ) ^ δA := by ring
              _ ≤ (n : ℝ) ^ (P.xD : ℝ) / 4 := by
                have hhalog : 4 * (((P.hPlus : ℝ) / δA) * (n : ℝ) ^ δA) ≤
                    (n : ℝ) ^ (P.xD : ℝ) := by
                  calc
                    4 * (((P.hPlus : ℝ) / δA) * (n : ℝ) ^ δA) =
                        (4 * (P.hPlus : ℝ) / δA) * (n : ℝ) ^ δA := by ring
                    _ ≤ (n : ℝ) ^ (P.xD : ℝ) := halog
                apply (le_div_iff₀ (by norm_num : (0 : ℝ) < 4)).2
                nlinarith only [hhalog]
          have hac' : (1 : ℝ) ≤ (n : ℝ) ^ (P.xD : ℝ) / 4 := by nlinarith [hac]
          have had' : (n : ℝ) ^ (P.u + 8 * (P.χ : ℝ)) ≤
              (n : ℝ) ^ (P.xD : ℝ) / 4 := by nlinarith [had]
          linarith only [hax, halog', hac', had']
        have hbStar : P.bStar n ≤ 1 / 200 := by
          have hb : (n : ℝ) ^ (-(P.hMinus : ℝ)) ≤ 1 / 200 := by nlinarith only [hb]
          simpa [Params9.bStar] using hb
        have hGain :
            ((P.radius n : ℝ) + 8) * Real.log ((n : ℝ) + 1) +
                (n : ℝ) ^ (P.xS : ℝ) + 4 * (n : ℝ) ^ P.u ≤
              gainConst9 * (n : ℝ) * P.aStar n / 100 := by
          have hradU : (P.radius n : ℝ) ≤ (n : ℝ) ^ (P.σ : ℝ) := by
            simpa [Params9.radius] using Nat.floor_le (by positivity :
              0 ≤ (n : ℝ) ^ (P.σ : ℝ))
          have hpowSigma : 1 ≤ (n : ℝ) ^ (P.σ : ℝ) := hradiusBase
          have hradPlus : (P.radius n : ℝ) + 8 ≤ 9 * (n : ℝ) ^ (P.σ : ℝ) := by
            nlinarith [hradU, hpowSigma]
          have hlogNonneg : 0 ≤ Real.log ((n : ℝ) + 1) :=
            Real.log_nonneg (by linarith : (1 : ℝ) ≤ (n : ℝ) + 1)
          have hfirst : ((P.radius n : ℝ) + 8) * Real.log ((n : ℝ) + 1) ≤
              (18 / δG) * (n : ℝ) ^ ((P.σ : ℝ) + δG) := by
            calc
              ((P.radius n : ℝ) + 8) * Real.log ((n : ℝ) + 1) ≤
                  9 * (n : ℝ) ^ (P.σ : ℝ) * Real.log ((n : ℝ) + 1) :=
                mul_le_mul_of_nonneg_right hradPlus hlogNonneg
              _ ≤ 9 * (n : ℝ) ^ (P.σ : ℝ) * ((2 / δG) * (n : ℝ) ^ δG) := by
                gcongr
              _ = (18 / δG) * ((n : ℝ) ^ (P.σ : ℝ) * (n : ℝ) ^ δG) := by ring
              _ = (18 / δG) * (n : ℝ) ^ ((P.σ : ℝ) + δG) := by
                rw [← Real.rpow_add hnPos]
          have hg1 : (18 / δG) * (n : ℝ) ^ ((P.σ : ℝ) + δG) ≤
              (n : ℝ) ^ (1 - (P.hPlus : ℝ)) / 1200 := by nlinarith [hg1]
          have hgx : (n : ℝ) ^ (P.xS : ℝ) ≤
              (n : ℝ) ^ (1 - (P.hPlus : ℝ)) / 1200 := by nlinarith [hgx]
          have hgu : 4 * (n : ℝ) ^ P.u ≤
              (n : ℝ) ^ (1 - (P.hPlus : ℝ)) / 1200 := by nlinarith [hgu]
          have hgainPow : (n : ℝ) ^ (1 - (P.hPlus : ℝ)) > 0 :=
            Real.rpow_pos_of_pos hnPos _
          have hgainIdentity :
              gainConst9 * (n : ℝ) * P.aStar n / 100 =
                (n : ℝ) ^ (1 - (P.hPlus : ℝ)) / 400 := by
            simp only [gainConst9, Params9.aStar]
            calc
              (1 / 2 : ℝ) * (n : ℝ) * ((n : ℝ) ^ (-(P.hPlus : ℝ)) / 2) / 100 =
                  (1 / 400 : ℝ) * ((n : ℝ) ^ (1 : ℝ) * (n : ℝ) ^ (-(P.hPlus : ℝ))) := by
                rw [show (n : ℝ) ^ (1 : ℝ) = (n : ℝ) by simp]
                ring
              _ = (1 / 400 : ℝ) * (n : ℝ) ^ (1 - (P.hPlus : ℝ)) := by
                rw [← Real.rpow_add hnPos]
                rw [show (1 : ℝ) + (-(P.hPlus : ℝ)) = 1 - (P.hPlus : ℝ) by ring]
              _ = (n : ℝ) ^ (1 - (P.hPlus : ℝ)) / 400 := by
                rw [div_eq_mul_inv]
                <;> ring
          rw [hgainIdentity]
          linarith only [hfirst, hg1, hgx, hgu]
        have hShallow : P.Ss (n : ℝ) + Real.log (n : ℝ) <
            (P.m n : ℝ) * Real.log 2 := by
          simpa [Params9.Ss, hcase] using hShallowLeft
        have hFilterSd : P.filterBudget n + (n : ℝ) ^ P.u ≤ P.Sd (n : ℝ) := by
          simpa [Params9.Sd, hcase] using hFilter
        refine ⟨by omega, hmLeN, hradius, hShallow, hFilterSd, hAnchor, hbStar, hGain⟩
      obtain ⟨n₀, hn₀⟩ := Filter.eventually_atTop.1 hScales
      refine ⟨hExps, n₀, ?_⟩
      intro n hn
      exact hn₀ n hn
  | lin αS αD hB yB =>
      simp only [Params9.Valid, hcase] at hP
      rcases hP with ⟨⟨hxs0, hxsxd, hxd010⟩, ⟨hm0, hmm, hmp1⟩, hmargin,
        ⟨hsig0, hsigxs⟩, ⟨hchi0, hchibound⟩, hgap,
        hαSpos, h100αS, hαD010, hσχ, hPlusB, hB1, hyBpos, hyB1⟩
      have hxs0R : 0 < (P.xS : ℝ) := by
        simpa using Lane_q_s09_misc.ratCast_lt hxs0
      have hxsxdR : (P.xS : ℝ) < (P.xD : ℝ) :=
        Lane_q_s09_misc.ratCast_lt hxsxd
      have hxd010R : (P.xD : ℝ) < (1 / 10 : ℝ) := by
        simpa using Lane_q_s09_misc.ratCast_lt hxd010
      have hminusPosR : 0 < (P.hMinus : ℝ) := by
        simpa using Lane_q_s09_misc.ratCast_lt hm0
      have hmmR : (P.hMinus : ℝ) < (P.hPlus : ℝ) :=
        Lane_q_s09_misc.ratCast_lt hmm
      have hplusPosR : 0 < (P.hPlus : ℝ) := lt_trans hminusPosR hmmR
      have hplusOneR : (P.hPlus : ℝ) < 1 := by
        simpa using Lane_q_s09_misc.ratCast_lt hmp1
      have hmarginR : (P.xD : ℝ) < (1 - (P.hPlus : ℝ)) / 10 := by
        simpa using Lane_q_s09_misc.ratCast_lt hmargin
      have hsigPosR : 0 < (P.σ : ℝ) := by
        simpa using Lane_q_s09_misc.ratCast_lt hsig0
      have hsigXsR : (P.σ : ℝ) < (P.xS : ℝ) / 10 := by
        simpa using Lane_q_s09_misc.ratCast_lt hsigxs
      have hchiPosR : 0 < (P.χ : ℝ) := by
        simpa using Lane_q_s09_misc.ratCast_lt hchi0
      have hchiBoundR : (P.χ : ℝ) <
          min (P.xS : ℝ) (min (P.hMinus : ℝ) (1 - (P.hPlus : ℝ))) / 100 := by
        simpa using Lane_q_s09_misc.ratCast_lt hchibound
      have hαSposR : 0 < (αS : ℝ) := by
        have h := Lane_q_s09_misc.ratCast_lt hαSpos
        norm_num at h ⊢
        linarith
      have h100αSR : 100 * (αS : ℝ) < (αD : ℝ) := by
        simpa using Lane_q_s09_misc.ratCast_lt h100αS
      have hαD010R : (αD : ℝ) < 1 / 100 := by
        simpa using Lane_q_s09_misc.ratCast_lt hαD010
      have hαDposR : 0 < (αD : ℝ) := by linarith [hαSposR, h100αSR]
      have hαSsmallR : (αS : ℝ) < (αD : ℝ) / 100 := by linarith [h100αSR]
      have hepsPos : 0 < P.eps := by
        rw [Params9.eps, hcase]
        exact div_pos hsigPosR (by norm_num)
      have hepsSigma : P.eps < (P.σ : ℝ) := by
        rw [Params9.eps, hcase]
        linarith [hsigPosR]
      have huPos : 0 < P.u := by
        rw [Params9.u]
        exact div_pos hxs0R (by norm_num)
      have hsigU : (P.σ : ℝ) < P.u := by
        rw [Params9.u]
        linarith
      have hchiXsR : (P.χ : ℝ) < (P.xS : ℝ) / 100 :=
        lt_of_lt_of_le hchiBoundR
          (div_le_div_of_nonneg_right (min_le_left _ _) (by norm_num))
      have hchiU : (P.χ : ℝ) < P.u / 50 := by
        rw [Params9.u]
        nlinarith [hchiXsR]
      have hExps : ScaleExps9 P :=
        ⟨hepsPos, hepsSigma, huPos, hsigU, hchiU⟩
      have hxSmall : (P.xS : ℝ) < 1 / 10 := lt_trans hxsxdR hxd010R
      have huChiXd : P.u + 8 * (P.χ : ℝ) < (P.xD : ℝ) := by
        rw [Params9.u]
        have hchiSmall : 8 * (P.χ : ℝ) < 8 * ((P.xS : ℝ) / 100) := by
          nlinarith [hchiXsR]
        nlinarith [hchiXsR, hchiSmall, hxsxdR]
      have hCpos : 0 < Real.log (100 / 49 : ℝ) :=
        Real.log_pos (by norm_num : (1 : ℝ) < 100 / 49)
      have hCtwo : Real.log (100 / 49 : ℝ) < 2 := by
        have hlog := Real.log_lt_sub_one_of_pos (by norm_num : (0 : ℝ) < 100 / 49)
          (by norm_num : (100 / 49 : ℝ) ≠ 1)
        norm_num at hlog ⊢
        linarith
      have hLeadRest : (αS : ℝ) + Real.log (100 / 49 : ℝ) * (αD : ℝ) / 10 < (αD : ℝ) := by
        have hCα : Real.log (100 / 49 : ℝ) * (αD : ℝ) < 2 * (αD : ℝ) :=
          mul_lt_mul_of_pos_right hCtwo hαDposR
        nlinarith [hCα, hαSsmallR, hαDposR]
      let margin : ℝ := (αD : ℝ) -
        ((αS : ℝ) + Real.log (100 / 49 : ℝ) * (αD : ℝ) / 10)
      have hMarginPos : 0 < margin := by dsimp [margin]; linarith [hLeadRest]
      have hIdOne : 1 - (P.σ : ℝ) + P.eps < 1 := by
        rw [Params9.eps, hcase]
        linarith [hsigPosR]
      have hδL : 0 < (1 / 2 : ℝ) := by norm_num
      have hLogDom : ∀ᶠ n : ℕ in atTop,
          (200 / (αD : ℝ)) * (n : ℝ) ^ (1 / 2 : ℝ) ≤ (n : ℝ) := by
        have he := Lane_q_s09_misc.eventually_nat_rpow_const_mul_le
          (a := 1 / 2) (b := 1) (c := 200 / (αD : ℝ)) (by norm_num)
        filter_upwards [he] with n hn
        simpa using hn
      have hLogEvent : ∀ᶠ n : ℕ in atTop,
          Real.log (n : ℝ) ≤ (n : ℝ) ^ (1 / 2 : ℝ) / (1 / 2 : ℝ) :=
        Lane_q_s09_misc.eventually_nat_log_le_rpow_div hδL
      have hConstDom : ∀ᶠ n : ℕ in atTop,
          100 * Real.log 2 / (αD : ℝ) ≤ (n : ℝ) := by
        have he := Lane_q_s09_misc.eventually_nat_rpow_const_mul_le
          (a := 0) (b := 1) (c := 100 * Real.log 2 / (αD : ℝ)) (by norm_num)
        filter_upwards [he] with n hn
        simpa using hn
      have hFiltU : ∀ᶠ n : ℕ in atTop,
          (4 / margin) * (n : ℝ) ^ P.u ≤ (n : ℝ) := by
        have he := Lane_q_s09_misc.eventually_nat_rpow_const_mul_le
          (a := P.u) (b := 1) (c := 4 / margin) (by
            rw [Params9.u]
            linarith [hxSmall])
        filter_upwards [he] with n hn
        simpa using hn
      have hFiltConst : ∀ᶠ n : ℕ in atTop,
          4 * Real.log 2 / margin ≤ (n : ℝ) := by
        have he := Lane_q_s09_misc.eventually_nat_rpow_const_mul_le
          (a := 0) (b := 1) (c := 4 * Real.log 2 / margin) (by norm_num)
        filter_upwards [he] with n hn
        simpa using hn
      have hFiltId : ∀ᶠ n : ℕ in atTop,
          (4 * Real.log (100 / 49 : ℝ) / margin) *
            (n : ℝ) ^ (1 - (P.σ : ℝ) + P.eps) ≤ (n : ℝ) := by
        have he := Lane_q_s09_misc.eventually_nat_rpow_const_mul_le
          (a := 1 - (P.σ : ℝ) + P.eps) (b := 1)
          (c := 4 * Real.log (100 / 49 : ℝ) / margin) hIdOne
        filter_upwards [he] with n hn
        simpa using hn
      have hAnchorXs : ∀ᶠ n : ℕ in atTop,
          4 * (n : ℝ) ^ (P.xS : ℝ) ≤ (n : ℝ) ^ (P.xD : ℝ) :=
        Lane_q_s09_misc.eventually_nat_rpow_const_mul_le
          (a := (P.xS : ℝ)) (b := (P.xD : ℝ)) (c := 4) hxsxdR
      let δA : ℝ := (P.xD : ℝ) / 2
      have hδApos : 0 < δA := by dsimp [δA]; linarith [hxs0R, hxsxdR]
      have hδAxd : δA < (P.xD : ℝ) := by dsimp [δA]; linarith [hδApos]
      have hAnchorLog : ∀ᶠ n : ℕ in atTop,
          (4 * (P.hPlus : ℝ) / δA) * (n : ℝ) ^ δA ≤ (n : ℝ) ^ (P.xD : ℝ) :=
        Lane_q_s09_misc.eventually_nat_rpow_const_mul_le
          (a := δA) (b := (P.xD : ℝ)) (c := 4 * (P.hPlus : ℝ) / δA) hδAxd
      have hLogAnchorEvent : ∀ᶠ n : ℕ in atTop,
          Real.log (n : ℝ) ≤ (n : ℝ) ^ δA / δA :=
        Lane_q_s09_misc.eventually_nat_log_le_rpow_div hδApos
      have hAnchorConst : ∀ᶠ n : ℕ in atTop,
          4 ≤ (n : ℝ) ^ (P.xD : ℝ) := by
        have he := Lane_q_s09_misc.eventually_nat_rpow_const_mul_le
          (a := 0) (b := (P.xD : ℝ)) (c := 4) (by linarith [hxs0R, hxsxdR])
        filter_upwards [he] with n hn
        simpa using hn
      have hAnchorDeep : ∀ᶠ n : ℕ in atTop,
          4 * (n : ℝ) ^ (P.u + 8 * (P.χ : ℝ)) ≤ (n : ℝ) ^ (P.xD : ℝ) :=
        Lane_q_s09_misc.eventually_nat_rpow_const_mul_le
          (a := P.u + 8 * (P.χ : ℝ)) (b := (P.xD : ℝ)) (c := 4) huChiXd
      have hBStar : ∀ᶠ n : ℕ in atTop,
          200 * (n : ℝ) ^ (-(P.hMinus : ℝ)) ≤ 1 := by
        have he := Lane_q_s09_misc.eventually_nat_rpow_const_mul_le
          (a := -(P.hMinus : ℝ)) (b := 0) (c := 200) (by linarith [hminusPosR])
        filter_upwards [he] with n hn
        simpa using hn
      have hGainRpos : 0 < 1 - (P.hPlus : ℝ) := by linarith [hplusOneR]
      have hSigmaGain : (P.σ : ℝ) < 1 - (P.hPlus : ℝ) := by
        linarith [hsigXsR, hxsxdR, hmarginR]
      let δG : ℝ := (1 - (P.hPlus : ℝ) - (P.σ : ℝ)) / 2
      have hδGpos : 0 < δG := by dsimp [δG]; linarith [hSigmaGain]
      have hδGone : δG ≤ 1 := by
        dsimp [δG]
        linarith [hplusPosR, hsigPosR]
      have hGainPow : (P.σ : ℝ) + δG < 1 - (P.hPlus : ℝ) := by
        dsimp [δG]
        linarith [hSigmaGain]
      have hGainFirst : ∀ᶠ n : ℕ in atTop,
          (1200 * (18 / δG)) * (n : ℝ) ^ ((P.σ : ℝ) + δG) ≤
            (n : ℝ) ^ (1 - (P.hPlus : ℝ)) :=
        Lane_q_s09_misc.eventually_nat_rpow_const_mul_le
          (a := (P.σ : ℝ) + δG) (b := 1 - (P.hPlus : ℝ))
          (c := 1200 * (18 / δG)) hGainPow
      have hGainXs : ∀ᶠ n : ℕ in atTop,
          1200 * (n : ℝ) ^ (P.xS : ℝ) ≤ (n : ℝ) ^ (1 - (P.hPlus : ℝ)) :=
        Lane_q_s09_misc.eventually_nat_rpow_const_mul_le
          (a := (P.xS : ℝ)) (b := 1 - (P.hPlus : ℝ)) (c := 1200) (by
            linarith [hmarginR, hxsxdR])
      have hGainU : ∀ᶠ n : ℕ in atTop,
          4800 * (n : ℝ) ^ P.u ≤ (n : ℝ) ^ (1 - (P.hPlus : ℝ)) :=
        Lane_q_s09_misc.eventually_nat_rpow_const_mul_le
          (a := P.u) (b := 1 - (P.hPlus : ℝ)) (c := 4800) (by
            rw [Params9.u]
            linarith [hmarginR, hxsxdR])
      have hLogGainEvent : ∀ᶠ n : ℕ in atTop,
          Real.log ((n : ℝ) + 1) ≤ (2 / δG) * (n : ℝ) ^ δG :=
        Lane_q_s09_misc.eventually_nat_log_succ_le_rpow hδGpos hδGone
      have hLarge : ∀ᶠ n : ℕ in atTop, 2 ≤ n := eventually_ge_atTop 2
      have hScales : ∀ᶠ n : ℕ in atTop, ScalesAt9 P n := by
        filter_upwards [hLarge, hLogDom, hLogEvent, hConstDom, hFiltU, hFiltConst,
          hFiltId, hAnchorXs, hAnchorLog, hLogAnchorEvent, hAnchorConst, hAnchorDeep,
          hBStar, hGainFirst, hGainXs, hGainU, hLogGainEvent] with n hn hld hlog hlc
          hfu hfc hfi haxs halog hlogA hac had hb hg hgx hgu hlogG
        have hnR : 1 ≤ (n : ℝ) := by exact_mod_cast (by omega : 1 ≤ n)
        have hnPos : 0 < (n : ℝ) := lt_of_lt_of_le zero_lt_one hnR
        have hmFloorU : (P.m n : ℝ) ≤ (αD : ℝ) * (n : ℝ) / 10 := by
          simpa [Params9.m, hcase] using Nat.floor_le (by positivity :
            0 ≤ (αD : ℝ) * (n : ℝ) / 10)
        have hmFloorL : (αD : ℝ) * (n : ℝ) / 10 - 1 < (P.m n : ℝ) := by
          have hf := Nat.lt_floor_add_one ((αD : ℝ) * (n : ℝ) / 10)
          have hf' : (αD : ℝ) * (n : ℝ) / 10 < (P.m n : ℝ) + 1 := by
            simpa [Params9.m, hcase] using hf
          linarith
        have hmLeNreal : (P.m n : ℝ) ≤ (n : ℝ) := by
          calc
            (P.m n : ℝ) ≤ (αD : ℝ) * (n : ℝ) / 10 := hmFloorU
            _ ≤ (n : ℝ) := by nlinarith [hαD010R, hnR]
        have hmLeN : P.m n ≤ n := by exact_mod_cast hmLeNreal
        have hradiusBase : 1 ≤ (n : ℝ) ^ (P.σ : ℝ) := by
          calc
            1 = (n : ℝ) ^ (0 : ℝ) := by simp
            _ ≤ (n : ℝ) ^ (P.σ : ℝ) :=
              Real.rpow_le_rpow_of_exponent_le hnR hsigPosR.le
        have hradius : 1 ≤ P.radius n := by
          change 1 ≤ Nat.floor ((n : ℝ) ^ (P.σ : ℝ))
          exact (Nat.one_le_floor_iff _).2 hradiusBase
        have hLogRoot : (n : ℝ) ^ (1 / 2 : ℝ) ≤ (αD : ℝ) / 200 * (n : ℝ) := by
          have hfactor : (αD : ℝ) / 200 * (200 / (αD : ℝ)) = 1 := by
            field_simp [ne_of_gt hαDposR]
          calc
            (n : ℝ) ^ (1 / 2 : ℝ) =
                ((αD : ℝ) / 200 * (200 / (αD : ℝ))) * (n : ℝ) ^ (1 / 2 : ℝ) := by
              rw [hfactor]
              ring
            _ = (αD : ℝ) / 200 *
                ((200 / (αD : ℝ)) * (n : ℝ) ^ (1 / 2 : ℝ)) := by ring
            _ ≤ (αD : ℝ) / 200 * (n : ℝ) :=
              mul_le_mul_of_nonneg_left hld (by positivity)
        have hLogAbs : Real.log (n : ℝ) ≤ (αD : ℝ) / 100 * (n : ℝ) := by
          calc
            Real.log (n : ℝ) ≤ (n : ℝ) ^ (1 / 2 : ℝ) / (1 / 2 : ℝ) := hlog
            _ = 2 * (n : ℝ) ^ (1 / 2 : ℝ) := by ring
            _ ≤ (αD : ℝ) / 100 * (n : ℝ) := by nlinarith [hLogRoot]
        have hConstAbs : Real.log 2 ≤ (αD : ℝ) / 100 * (n : ℝ) := by
          have hfactor : (αD : ℝ) / 100 * (100 * Real.log 2 / (αD : ℝ)) =
              Real.log 2 := by
            field_simp [ne_of_gt hαDposR]
          calc
            Real.log 2 =
                ((αD : ℝ) / 100) *
                  (100 * Real.log 2 / (αD : ℝ)) := by rw [hfactor]
            _ ≤ ((αD : ℝ) / 100) * (n : ℝ) :=
              mul_le_mul_of_nonneg_left hlc (by positivity)
        have hLeadCoef : (αS : ℝ) + (αD : ℝ) / 50 <
            Real.log 2 * (αD : ℝ) / 10 := by
          have hlog2Half : (1 / 2 : ℝ) < Real.log 2 := by
            linarith [Real.log_two_gt_d9]
          have hlogAlpha : (αD : ℝ) / 2 < Real.log 2 * (αD : ℝ) := by
            convert mul_lt_mul_of_pos_right hlog2Half hαDposR using 1 <;> ring
          nlinarith [hαSsmallR, hlogAlpha, hαDposR]
        have hShallow : P.Ss (n : ℝ) + Real.log (n : ℝ) <
            (P.m n : ℝ) * Real.log 2 := by
          have hleft : (αS : ℝ) * (n : ℝ) + Real.log (n : ℝ) +
              Real.log 2 ≤ ((αS : ℝ) + (αD : ℝ) / 50) * (n : ℝ) := by
            nlinarith [hLogAbs, hConstAbs]
          have hmiddle : ((αS : ℝ) + (αD : ℝ) / 50) * (n : ℝ) <
              Real.log 2 * (αD : ℝ) / 10 * (n : ℝ) :=
            mul_lt_mul_of_pos_right hLeadCoef hnPos
          have hfloor : Real.log 2 * ((αD : ℝ) * (n : ℝ) / 10 - 1) <
              (P.m n : ℝ) * Real.log 2 :=
            by
              simpa [mul_comm] using
                mul_lt_mul_of_pos_left hmFloorL (Real.log_pos (by norm_num : (1 : ℝ) < 2))
          have hleftFloor : (αS : ℝ) * (n : ℝ) + Real.log (n : ℝ) <
              Real.log 2 * ((αD : ℝ) * (n : ℝ) / 10 - 1) := by
            nlinarith [hleft, hmiddle]
          rw [Params9.Ss, hcase]
          nlinarith [hleftFloor, hfloor]
        have hFilterEq : P.filterBudget n + (n : ℝ) ^ P.u =
            (αS : ℝ) * (n : ℝ) + (n : ℝ) ^ P.u + Real.log 2 +
              Real.log (100 / 49 : ℝ) *
                ((n : ℝ) ^ (1 - (P.σ : ℝ) + P.eps) + (P.m n : ℝ)) +
              (n : ℝ) ^ P.u := by
          simp [Params9.filterBudget, Params9.Ss, Params9.idBudget, hcase]
        have hFilter : P.filterBudget n + (n : ℝ) ^ P.u ≤
            (αD : ℝ) * (n : ℝ) := by
          rw [hFilterEq]
          have hfactor : margin / 4 * (4 / margin) = 1 := by
            field_simp [ne_of_gt hMarginPos]
          have hUbound : (n : ℝ) ^ P.u ≤ margin / 4 * (n : ℝ) := by
            calc
              (n : ℝ) ^ P.u = (margin / 4 * (4 / margin)) * (n : ℝ) ^ P.u := by
                rw [hfactor]
                ring
              _ = margin / 4 * ((4 / margin) * (n : ℝ) ^ P.u) := by ring
              _ ≤ margin / 4 * (n : ℝ) := mul_le_mul_of_nonneg_left hfu (by positivity)
          have hfactorC : margin / 4 * (4 * Real.log 2 / margin) = Real.log 2 := by
            field_simp [ne_of_gt hMarginPos]
          have hCbound : Real.log 2 ≤ margin / 4 * (n : ℝ) := by
            calc
              Real.log 2 = (margin / 4 * (4 * Real.log 2 / margin)) := by rw [hfactorC]
              _ ≤ margin / 4 * (n : ℝ) := mul_le_mul_of_nonneg_left hfc (by positivity)
          have hfactorI : margin / 4 *
              (4 * Real.log (100 / 49 : ℝ) / margin) = Real.log (100 / 49 : ℝ) := by
            field_simp [ne_of_gt hMarginPos]
          have hIbound : Real.log (100 / 49 : ℝ) *
              (n : ℝ) ^ (1 - (P.σ : ℝ) + P.eps) ≤ margin / 4 * (n : ℝ) := by
            calc
              Real.log (100 / 49 : ℝ) * (n : ℝ) ^ (1 - (P.σ : ℝ) + P.eps) =
                  (margin / 4 * (4 * Real.log (100 / 49 : ℝ) / margin)) *
                    (n : ℝ) ^ (1 - (P.σ : ℝ) + P.eps) := by rw [hfactorI]
              _ = margin / 4 * ((4 * Real.log (100 / 49 : ℝ) / margin) *
                  (n : ℝ) ^ (1 - (P.σ : ℝ) + P.eps)) := by ring
              _ ≤ margin / 4 * (n : ℝ) := mul_le_mul_of_nonneg_left hfi (by positivity)
          have hMbound : Real.log (100 / 49 : ℝ) * (P.m n : ℝ) ≤
              Real.log (100 / 49 : ℝ) * ((αD : ℝ) * (n : ℝ) / 10) :=
            mul_le_mul_of_nonneg_left hmFloorU (le_of_lt hCpos)
          have hLead : (αS : ℝ) * (n : ℝ) +
              Real.log (100 / 49 : ℝ) * ((αD : ℝ) * (n : ℝ) / 10) ≤
                ((αS : ℝ) + Real.log (100 / 49 : ℝ) * (αD : ℝ) / 10) * (n : ℝ) := by
            ring_nf
            exact le_rfl
          have hMarginEq :
              ((αS : ℝ) + Real.log (100 / 49 : ℝ) * (αD : ℝ) / 10) + margin =
                (αD : ℝ) := by dsimp [margin]; ring
          nlinarith [hUbound, hCbound, hIbound, hMbound, hMarginEq]
        have hAnchor :
            (n : ℝ) ^ (P.xS : ℝ) + (P.hPlus : ℝ) * Real.log (n : ℝ) + 1 +
                (n : ℝ) ^ (P.u + 8 * (P.χ : ℝ)) ≤ (n : ℝ) ^ (P.xD : ℝ) := by
          have hax : (n : ℝ) ^ (P.xS : ℝ) ≤ (n : ℝ) ^ (P.xD : ℝ) / 4 := by nlinarith [haxs]
          have halog' : (P.hPlus : ℝ) * Real.log (n : ℝ) ≤
              (n : ℝ) ^ (P.xD : ℝ) / 4 := by
            calc
              (P.hPlus : ℝ) * Real.log (n : ℝ) ≤
                  (P.hPlus : ℝ) * ((n : ℝ) ^ δA / δA) :=
                mul_le_mul_of_nonneg_left hlogA (le_of_lt hplusPosR)
              _ = ((P.hPlus : ℝ) / δA) * (n : ℝ) ^ δA := by ring
              _ ≤ (n : ℝ) ^ (P.xD : ℝ) / 4 := by
                have hhalog : 4 * (((P.hPlus : ℝ) / δA) * (n : ℝ) ^ δA) ≤
                    (n : ℝ) ^ (P.xD : ℝ) := by
                  calc
                    4 * (((P.hPlus : ℝ) / δA) * (n : ℝ) ^ δA) =
                        (4 * (P.hPlus : ℝ) / δA) * (n : ℝ) ^ δA := by ring
                    _ ≤ (n : ℝ) ^ (P.xD : ℝ) := halog
                apply (le_div_iff₀ (by norm_num : (0 : ℝ) < 4)).2
                simpa [mul_assoc, mul_left_comm, mul_comm] using hhalog
          have hac' : (1 : ℝ) ≤ (n : ℝ) ^ (P.xD : ℝ) / 4 := by nlinarith [hac]
          have had' : (n : ℝ) ^ (P.u + 8 * (P.χ : ℝ)) ≤
              (n : ℝ) ^ (P.xD : ℝ) / 4 := by nlinarith [had]
          nlinarith
        have hbStar : P.bStar n ≤ 1 / 200 := by
          have hb : (n : ℝ) ^ (-(P.hMinus : ℝ)) ≤ 1 / 200 := by nlinarith [hg]
          simpa [Params9.bStar] using hb
        have hGain :
            ((P.radius n : ℝ) + 8) * Real.log ((n : ℝ) + 1) +
                (n : ℝ) ^ (P.xS : ℝ) + 4 * (n : ℝ) ^ P.u ≤
              gainConst9 * (n : ℝ) * P.aStar n / 100 := by
          have hradU : (P.radius n : ℝ) ≤ (n : ℝ) ^ (P.σ : ℝ) := by
            simpa [Params9.radius] using Nat.floor_le (by positivity :
              0 ≤ (n : ℝ) ^ (P.σ : ℝ))
          have hradPlus : (P.radius n : ℝ) + 8 ≤ 9 * (n : ℝ) ^ (P.σ : ℝ) := by
            nlinarith [hradU, hradiusBase]
          have hlogNonneg : 0 ≤ Real.log ((n : ℝ) + 1) :=
            Real.log_nonneg (by linarith : (1 : ℝ) ≤ (n : ℝ) + 1)
          have hfirst : ((P.radius n : ℝ) + 8) * Real.log ((n : ℝ) + 1) ≤
              (18 / δG) * (n : ℝ) ^ ((P.σ : ℝ) + δG) := by
            calc
              ((P.radius n : ℝ) + 8) * Real.log ((n : ℝ) + 1) ≤
                  9 * (n : ℝ) ^ (P.σ : ℝ) * Real.log ((n : ℝ) + 1) :=
                mul_le_mul_of_nonneg_right hradPlus hlogNonneg
              _ ≤ 9 * (n : ℝ) ^ (P.σ : ℝ) * ((2 / δG) * (n : ℝ) ^ δG) := by
                gcongr
              _ = (18 / δG) * ((n : ℝ) ^ (P.σ : ℝ) * (n : ℝ) ^ δG) := by ring
              _ = (18 / δG) * (n : ℝ) ^ ((P.σ : ℝ) + δG) := by
                rw [← Real.rpow_add hnPos]
          have hg1 : (18 / δG) * (n : ℝ) ^ ((P.σ : ℝ) + δG) ≤
              (n : ℝ) ^ (1 - (P.hPlus : ℝ)) / 1200 := by nlinarith [hg]
          have hgx : (n : ℝ) ^ (P.xS : ℝ) ≤
              (n : ℝ) ^ (1 - (P.hPlus : ℝ)) / 1200 := by nlinarith [hgx]
          have hgu : 4 * (n : ℝ) ^ P.u ≤
              (n : ℝ) ^ (1 - (P.hPlus : ℝ)) / 1200 := by nlinarith [hgu]
          have hgainIdentity :
              gainConst9 * (n : ℝ) * P.aStar n / 100 =
                (n : ℝ) ^ (1 - (P.hPlus : ℝ)) / 400 := by
            simp only [gainConst9, Params9.aStar]
            calc
              (1 / 2 : ℝ) * (n : ℝ) * ((n : ℝ) ^ (-(P.hPlus : ℝ)) / 2) / 100 =
                  (1 / 400 : ℝ) * ((n : ℝ) ^ (1 : ℝ) *
                    (n : ℝ) ^ (-(P.hPlus : ℝ))) := by
                rw [show (n : ℝ) ^ (1 : ℝ) = (n : ℝ) by simp]
                ring
              _ = (1 / 400 : ℝ) * (n : ℝ) ^ (1 - (P.hPlus : ℝ)) := by
                rw [← Real.rpow_add hnPos]
                rw [show (1 : ℝ) + (-(P.hPlus : ℝ)) = 1 - (P.hPlus : ℝ) by ring]
              _ = (n : ℝ) ^ (1 - (P.hPlus : ℝ)) / 400 := by
                rw [div_eq_mul_inv]
                <;> ring
          rw [hgainIdentity]
          nlinarith
        have hMarginNat : P.m n ≤ n := by exact_mod_cast hmLeNreal
        have hFilterSd : P.filterBudget n + (n : ℝ) ^ P.u ≤ P.Sd (n : ℝ) := by
          simpa [Params9.Sd, hcase] using hFilter
        refine ⟨by omega, hMarginNat, hradius, hShallow, hFilterSd, hAnchor, hbStar, hGain⟩
      obtain ⟨n₀, hn₀⟩ := Filter.eventually_atTop.1 hScales
      refine ⟨hExps, n₀, ?_⟩
      intro n hn
      exact hn₀ n hn

end HypercubeRamsey
