import HypercubeRamsey.S09.Core.Scales
import HypercubeRamsey.S03.Height.Scale

/-!
# Proposition 9.2: the adapted height experiment (P9.2-map1)

Source: `sections/09-intermediate-powers-of-bias.tex`, lines 72–100 (the adapted height construction), with the
path rule and scales of Lemma 3.8 (`sections/03-…tex`, lines 283–330).

Positions are center IDs `(slice, residual location, level)`.  Independently at every position a prospective
center is present with probability `n^{10}/V` (`V` the volume of a radius-`r` residual ball) and active with
probability `n^{b₀-10}`.  All prospective centers of a site's slice in its residual radius-`r` ball are eligible.
A site-level is bad if its eligible set has no active center or, at a level within `2`, one of the three crowd
tests of 09:76–80 fails.  Heights follow Lemma 3.8's path rule with steps of full-cube distance at most `2`
(`D = 2`, consultation radius `2DH`), and `H` is Lemma 3.8's first scale at least `n^{1-ζ}` (`topScale`).
The internal exponents `b₀, ε', ζ, σ_h, θ, a` are a `HeightChoice9`; 09:82–83 and 09:96–98 fix their constraints
(`HeightChoice9.Admissible`).
-/

namespace HypercubeRamsey

open OAI.HypercubeRamsey Classical
open scoped BigOperators

/-- The internal exponents of the adapted height experiment (09:72–98): activation exponent `b₀`, crowd slack
`ε'`, and Lemma 3.8's scale exponents `ζ`, `σ_h`, `θ`, `a`. -/
structure HeightChoice9 (P : Params9) where
  b₀ : ℝ
  eps' : ℝ
  ζ : ℝ
  σh : ℝ
  θ : ℝ
  a : ℝ

namespace HeightChoice9

variable {P : Params9}

/-- The constraints of 09:82–83 and 09:96–98: `0 < σ_h < ζ < 1`, `0 < θ < 1`,
`ζ + σ_h + (1 - θ) < a < b₀`, `a + 4σ_h < χ/2`, `0 < b₀ < ε' < ε` (each crowd threshold a fixed power above its
mean, and the ID budget above the radius-`(r+1)` crowd), and `b₀ + σ < χ/2` in the linear case (`b₀ < χ/2` in the
sublinear case, where `y_m + σ < 1`). -/
def Admissible (hc : HeightChoice9 P) : Prop :=
  0 < hc.σh ∧ hc.σh < hc.ζ ∧ hc.ζ < 1 ∧ 0 < hc.θ ∧ hc.θ < 1 ∧
  hc.ζ + hc.σh + (1 - hc.θ) < hc.a ∧ hc.a < hc.b₀ ∧ hc.a + 4 * hc.σh < (P.χ : ℝ) / 2 ∧
  0 < hc.b₀ ∧ hc.b₀ < hc.eps' ∧ hc.eps' < P.eps ∧
  (match P.case with
   | .sub _ _ _ => hc.b₀ < (P.χ : ℝ) / 2
   | .lin _ _ _ _ => hc.b₀ + (P.σ : ℝ) < (P.χ : ℝ) / 2)

/-- The number of levels `H`: Lemma 3.8's first scale at least `n^{1-ζ}`. -/
noncomputable def levels (hc : HeightChoice9 P) (n : ℕ) : ℕ := topScale n hc.σh hc.ζ

end HeightChoice9

/-- The positions of the adapted experiment at dimension `n`. -/
abbrev Pos9 (P : Params9) (hc : HeightChoice9 P) (n : ℕ) :=
  CenterID9 (P.m n) (n - P.m n) (hc.levels n)

/-- The volume of a radius-`r` ball in the residual cube `Q_{n-m}` (09:72). -/
noncomputable def residualBall9 (P : Params9) (n : ℕ) : ℕ :=
  ∑ i ∈ Finset.range (P.radius n + 1), Nat.choose (n - P.m n) i

/-- Independent prospective positions, each present with probability `n^{10}/V` (09:73). -/
noncomputable def heightPosLaw9 (P : Params9) (hc : HeightChoice9 P) (n : ℕ) : FinProb (Pos9 P hc n → Bool) :=
  FinProb.pi (fun _ => FinProb.bernoulli ((n : ℝ) ^ (10 : ℝ) / (residualBall9 P n : ℝ)))

/-- Independent activations, each with probability `n^{b₀-10}` (09:73). -/
noncomputable def heightActLaw9 (P : Params9) (hc : HeightChoice9 P) (n : ℕ) : FinProb (Pos9 P hc n → Bool) :=
  FinProb.pi (fun _ => FinProb.bernoulli ((n : ℝ) ^ (hc.b₀ - 10)))

/-- The joint law of positions and activations. -/
noncomputable def heightLaw9 (P : Params9) (hc : HeightChoice9 P) (n : ℕ) :
    FinProb ((Pos9 P hc n → Bool) × (Pos9 P hc n → Bool)) :=
  (heightPosLaw9 P hc n).prod (heightActLaw9 P hc n)

variable {P : Params9} {hc : HeightChoice9 P} {n : ℕ}

/-- An active center: prospective and activated. -/
def activeAt9 (Pp A : Pos9 P hc n → Bool) (c : Pos9 P hc n) : Prop := Pp c = true ∧ A c = true

/-- The eligible set of a site-level, with centers restricted to the location-level domain `C`, has no active
center (09:74–75): no active center of `C` in the site's slice at that level lies in the residual radius-`r` ball.
Lemma 3.8's induction (Step 1) restricts centers to a deterministic domain; the actual experiment uses
`C = univ`. -/
def holeIn9 (C : Finset (Pos9 P hc n)) (Pp A : Pos9 P hc n → Bool) (v : CubeVertex n)
    (j : Fin (hc.levels n + 1)) : Prop :=
  ∀ c ∈ C, c.slice = specialWord9 (P.m n) v →
    _root_.hammingDist c.location (residualWord9 (P.m n) v) ≤ P.radius n → c.level = j →
      ¬ activeAt9 Pp A c

/-- The size of the eligible set within `C`: prospective centers of the site's slice at level `j` in the residual
radius-`r` ball (09:74). -/
noncomputable def eligCount9 (C : Finset (Pos9 P hc n)) (Pp : Pos9 P hc n → Bool) (v : CubeVertex n)
    (j : Fin (hc.levels n + 1)) : ℕ :=
  (C.filter (fun c => Pp c = true ∧ c.slice = specialWord9 (P.m n) v ∧
    _root_.hammingDist c.location (residualWord9 (P.m n) v) ≤ P.radius n ∧ c.level = j)).card

/-- Active centers of `C` in the site's slice at level `j` within residual radius `R` (09:77, 09:79). -/
noncomputable def crowdSame9 (C : Finset (Pos9 P hc n)) (Pp A : Pos9 P hc n → Bool) (v : CubeVertex n)
    (j : Fin (hc.levels n + 1)) (R : ℕ) : ℕ :=
  (C.filter (fun c => activeAt9 Pp A c ∧ c.slice = specialWord9 (P.m n) v ∧
    _root_.hammingDist c.location (residualWord9 (P.m n) v) ≤ R ∧ c.level = j)).card

/-- Active centers of `C` in the adjacent slices at level `j` within residual radius `r - 1` (09:78). -/
noncomputable def crowdAdj9 (C : Finset (Pos9 P hc n)) (Pp A : Pos9 P hc n → Bool) (v : CubeVertex n)
    (j : Fin (hc.levels n + 1)) : ℕ :=
  (C.filter (fun c => activeAt9 Pp A c ∧
    _root_.hammingDist c.slice (specialWord9 (P.m n) v) = 1 ∧
    _root_.hammingDist c.location (residualWord9 (P.m n) v) ≤ P.radius n - 1 ∧ c.level = j)).card

/-- A bad site-level with centers restricted to `C` and crowd thresholds scaled by `t` (09:74–81; the actual
experiment has `C = univ`, `t = 1`; Lemma 3.8's degraded thresholds use `t ∈ [1/3, 1]`): a hole, or at a level
within `2` (clipped) one of the crowd tests `same slice, radius r: t n^{χ/2}`,
`adjacent slices, radius r-1: t n^{χ/2}`, `same slice, radius r+1: t n^{1-σ+ε'}` fails. -/
def badIn9 (C : Finset (Pos9 P hc n)) (t : ℝ) (Pp A : Pos9 P hc n → Bool) (v : CubeVertex n)
    (j : Fin (hc.levels n + 1)) : Prop :=
  holeIn9 C Pp A v j ∨ ∃ j' : Fin (hc.levels n + 1), Nat.dist j.val j'.val ≤ 2 ∧
    (t * (n : ℝ) ^ ((P.χ : ℝ) / 2) < (crowdSame9 C Pp A v j' (P.radius n) : ℝ) ∨
      t * (n : ℝ) ^ ((P.χ : ℝ) / 2) < (crowdAdj9 C Pp A v j' : ℝ) ∨
      t * (n : ℝ) ^ (1 - (P.σ : ℝ) + hc.eps') < (crowdSame9 C Pp A v j' (P.radius n + 1) : ℝ))

/-- A bad site-level of the actual experiment. -/
def badAt9 (Pp A : Pos9 P hc n → Bool) (v : CubeVertex n) (j : Fin (hc.levels n + 1)) : Prop :=
  badIn9 Finset.univ 1 Pp A v j

/-- Lemma 3.8's path rule with full-cube steps of length at most `2` (09:84): from any level-zero start in the
consultation ball, an upward step from a bad site-level, or a downward step of one level together with a step of
full-cube distance at most `2`. -/
inductive Reach9 (Pp A : Pos9 P hc n → Bool) (vq : CubeVertex n) (R : ℕ) : CubeVertex n → ℕ → Prop
  | start (v : CubeVertex n) : _root_.hammingDist v vq ≤ R → Reach9 Pp A vq R v 0
  | up (v : CubeVertex n) (j : ℕ) (hj : j < hc.levels n) :
      Reach9 Pp A vq R v j → badAt9 Pp A v ⟨j, by omega⟩ → Reach9 Pp A vq R v (j + 1)
  | down (v v' : CubeVertex n) (j : ℕ) :
      Reach9 Pp A vq R v (j + 1) → _root_.hammingDist v' vq ≤ R → _root_.hammingDist v v' ≤ 2 →
        Reach9 Pp A vq R v' j

/-- The long height (consultation radius `2DH = 4H`). -/
noncomputable def height9 (Pp A : Pos9 P hc n → Bool) (v : CubeVertex n) : ℕ :=
  ((Finset.range (hc.levels n + 1)).filter (fun j => Reach9 Pp A v (4 * hc.levels n) v j)).sup id

/-- Good heights (09:99–100): every height is below `H` with a good site-level, and heights differ by at most one
at full-cube distance at most `2`. -/
def GoodHeights9 (Pp A : Pos9 P hc n → Bool) : Prop :=
  ∀ v : CubeVertex n, ∃ h : height9 Pp A v < hc.levels n,
    ¬ badAt9 Pp A v ⟨height9 Pp A v, by omega⟩ ∧
    ∀ v' : CubeVertex n, _root_.hammingDist v v' ≤ 2 → Nat.dist (height9 Pp A v) (height9 Pp A v') ≤ 1

/-- The positions consulted by a child domain of metric radius `R'` around a site (09:86–87): slices within special
distance `2R' + 1` and residual locations within `r + 2R' + 1`, at every level. -/
noncomputable def consulted9 (v : CubeVertex n) (R' : ℕ) : Finset (Pos9 P hc n) :=
  Finset.univ.filter (fun c => _root_.hammingDist c.slice (specialWord9 (P.m n) v) ≤ 2 * R' + 1 ∧
    _root_.hammingDist c.location (residualWord9 (P.m n) v) ≤ P.radius n + 2 * R' + 1)

/-- The base estimate (09:84–85, Lemma 3.8 Steps 1–2), uniform in the center domain `C` as Lemma 3.8's induction
requires: at every crowd-threshold factor `t ∈ [1/3, 1]` and eligible-size factor `s ≥ 1/8`, a fixed site-level is
bad with an eligible set of size at least `s n^{10}` with probability at most `exp(-n^c)`. -/
def HeightBase9 (P : Params9) (hc : HeightChoice9 P) (n : ℕ) (c : ℝ) : Prop :=
  ∀ (C : Finset (Pos9 P hc n)) (t s : ℝ), 1 / 3 ≤ t → t ≤ 1 → 1 / 8 ≤ s →
    ∀ (v : CubeVertex n) (j : Fin (hc.levels n + 1)),
      (heightLaw9 P hc n).pr (fun ω => badIn9 C t ω.1 ω.2 v j ∧
        s * (n : ℝ) ^ (10 : ℝ) ≤ (eligCount9 C ω.1 v j : ℝ)) ≤ Real.exp (-(n : ℝ) ^ c)

/-- Position counts (09:85, as Lemma 3.8(j)): every eligible set of the actual experiment has at least `n^{10}/2`
prospective centers, except with probability `e^{-n}`. -/
def HeightCounts9 (P : Params9) (hc : HeightChoice9 P) (n : ℕ) : Prop :=
  (heightPosLaw9 P hc n).pr (fun Pp => ∃ (v : CubeVertex n) (j : Fin (hc.levels n + 1)),
    (eligCount9 Finset.univ Pp v j : ℝ) < (n : ℝ) ^ (10 : ℝ) / 2) ≤ Real.exp (-(n : ℝ))

/-- The cross-slice overlap estimate (09:86–92): for starts at full-cube distance at least `K R'`, the positions
consulted by both child domains at one level number at most `V e^{-c₀ R'}`. -/
def HeightOverlap9 (P : Params9) (hc : HeightChoice9 P) (n : ℕ) (K c₀ : ℝ) : Prop :=
  ∀ (v v' : CubeVertex n) (R' : ℕ) (j : Fin (hc.levels n + 1)), 1 ≤ R' →
    K * R' ≤ (_root_.hammingDist v v' : ℝ) →
    (((consulted9 (hc := hc) v R' ∩ consulted9 v' R').filter (fun c => c.level = j)).card : ℝ) ≤
      (residualBall9 P n : ℝ) * Real.exp (-(c₀ * R'))

end HypercubeRamsey
