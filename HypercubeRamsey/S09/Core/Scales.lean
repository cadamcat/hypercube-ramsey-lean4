import HypercubeRamsey.S09.Defs
import HypercubeRamsey.Framework.Embedding

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

open OAI.HypercubeRamsey Classical
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

/-- Arithmetic consequences of `Params9.Valid` for the internal scales: the exponent facts, and the
per-dimension facts for all large `n`.  (In the sublinear case `y_s < y_m < 1 - σ < y_d` and `1 - σ + ε < y_d`;
in the linear case `S_s + log(100/49)(T + m) ≈ (α_s + .0713 α_d) n + o(n) < α_d n`.) -/
theorem scales_eventually9 (P : Params9) (hP : P.Valid) :
    ScaleExps9 P ∧ ∃ n₀ : ℕ, ∀ n ≥ n₀, ScalesAt9 P n := by
  sorry

end HypercubeRamsey
