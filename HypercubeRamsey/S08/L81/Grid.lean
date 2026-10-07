import HypercubeRamsey.Framework.Props
import HypercubeRamsey.Framework.Embedding
import HypercubeRamsey.Tools.CubeGeometry
import HypercubeRamsey.S08.L81.Grid_q_s08_grid
import HypercubeRamsey.S07.GeometryNodes
import HypercubeRamsey.S03.Height.Selection

/-!
# Lemma 8.1, Step 1: constants, the key grid and residual cells

Source: `sections/08-asymmetric-pure-patches-under-2.tex`, lines 4–6, 15–21, 126–131, 345–347, 356–361; blueprint
`research/blueprint/PART-B.md` §3.8 (constants paragraph, L8.1a).

The first `m = s ℓ` coordinates form `s = ⌈n^τ⌉` chunks of length `ℓ = ⌊n^{.2}⌋`; the bin of a chunk is its count of
`true` bits (singleton bins: every Binomial(ℓ, 1/2) atom is `O(n^{-.1}) ≤ 2n^{-.04}` for large `n`, so singletons are
admissible consecutive bins of mass at most `2n^{-.04}`, 08:16).  A cube vertex reads the cell `(g, a)`: its key
`g` (the vector of chunk counts) and its residual word `a ∈ Q_{n-m}`.  The padded even neighbours of the odd task
at `(g, a)` are the ordinary cells `(g, b)`, `d_H(a, b) ≤ 1`, and the cross cells `(u, a)`, `u ∈ E(g)` (08:17–21).

The height device (Lemma 3.8, `S03/Height`) runs in every grid slice on `Q_{n-m}` with step `D = 2`, radius
`r = ⌊n/100⌋`, `λ = n^{10}`, `b = τ/16`, `b₀ = b/4` and `ζ, σ, 1-θ, a` small in terms of `b₀` (08:126–130).
-/

noncomputable section

namespace HypercubeRamsey.S08

open Classical OAI.HypercubeRamsey
open scoped BigOperators

/-! ## Constants (08:4–6, 08:16, 08:126–131, 08:160–161) -/

/-- `η = min(η₀/2, .04)` (08:5).  The repository's `tau8 η₀` is `η/4` (`tau8_eq`). -/
def eta8 (η₀ : ℝ) : ℝ := min (η₀ / 2) (4 / 100)

theorem tau8_eq (η₀ : ℝ) : tau8 η₀ = eta8 η₀ / 4 := rfl

/-- The number of special chunks, `s = ⌈n^τ⌉` (08:16). -/
def sC (η₀ : ℝ) (n : ℕ) : ℕ := ⌈(n : ℝ) ^ tau8 η₀⌉₊

/-- The chunk length, `⌊n^{.2}⌋` (08:16). -/
def lC (n : ℕ) : ℕ := ⌊(n : ℝ) ^ ((1 : ℝ) / 5)⌋₊

/-- The number of special bits, `m = s ⌊n^{.2}⌋`. -/
def mC (η₀ : ℝ) (n : ℕ) : ℕ := sC η₀ n * lC n

/-- The residual dimension `n - m`. -/
def dC (η₀ : ℝ) (n : ℕ) : ℕ := n - mC η₀ n

/-- The fan bound `T = ⌈n^{τ/8}⌉` (08:131). -/
def TC (η₀ : ℝ) (n : ℕ) : ℕ := ⌈(n : ℝ) ^ (tau8 η₀ / 8)⌉₊

/-- A grid key: one bin (chunk count) per special chunk. -/
abbrev Key (η₀ : ℝ) (n : ℕ) := Fin (sC η₀ n) → Fin (lC n + 1)

/-- A residual word. -/
abbrev Res (η₀ : ℝ) (n : ℕ) := CubeVertex (dC η₀ n)

/-- A cell `(g, a)`. -/
abbrev Cell (η₀ : ℝ) (n : ℕ) := Key η₀ n × Res η₀ n

/-! ## Cube vertices to cells -/

/-- The number of `true` bits of `v` in chunk `r` (coordinates `rℓ, …, rℓ + ℓ - 1`). -/
def chunkWeight (η₀ : ℝ) {n : ℕ} (v : CubeVertex n) (r : Fin (sC η₀ n)) : ℕ :=
  (Finset.univ.filter fun i : Fin n => i.val < mC η₀ n ∧ i.val / lC n = r.val ∧ v i = true).card

/-- The grid key of a cube vertex.  The `min` only makes the value total; a chunk has `ℓ` coordinates once
`m ≤ n`. -/
def keyOf (η₀ : ℝ) {n : ℕ} (v : CubeVertex n) : Key η₀ n :=
  fun r => ⟨min (chunkWeight η₀ v r) (lC n), Nat.lt_succ_of_le (min_le_right _ _)⟩

/-- The residual word of a cube vertex: its last `n - m` coordinates. -/
def resOf (η₀ : ℝ) {n : ℕ} (v : CubeVertex n) : Res η₀ n :=
  fun j => v ⟨mC η₀ n + j.val, by have hj := j.isLt; unfold dC at hj; omega⟩

/-- The cell of a cube vertex. -/
def cellOf (η₀ : ℝ) {n : ℕ} (v : CubeVertex n) : Cell η₀ n := (keyOf η₀ v, resOf η₀ v)

/-! ## Distances, neighbours and balls -/

section Dist

variable {η₀ : ℝ} {n : ℕ}

/-- Grid distance: the number of one-bin moves. -/
def keyDist (g u : Key η₀ n) : ℕ := ∑ r, Nat.dist (g r).val (u r).val

/-- `E(g)`: the keys one bin-step from `g` (08:16). -/
def crossKeys (g : Key η₀ n) : Finset (Key η₀ n) := Finset.univ.filter fun u => keyDist g u = 1

/-- `B_grid(g, R)`. -/
def keyBall (g : Key η₀ n) (R : ℕ) : Finset (Key η₀ n) := Finset.univ.filter fun u => keyDist g u ≤ R

/-- The residual words at Hamming distance at most one. -/
def ordNbrs (a : Res η₀ n) : Finset (Res η₀ n) := Finset.univ.filter fun b => _root_.hammingDist a b ≤ 1

/-- Distance in the cell graph with grid or residual one-step moves (08:387). -/
def cellDist (c e : Cell η₀ n) : ℕ := keyDist c.1 e.1 + _root_.hammingDist c.2 e.2

/-- Cells within cell distance `R`. -/
def cellBall (c : Cell η₀ n) (R : ℕ) : Finset (Cell η₀ n) := Finset.univ.filter fun e => cellDist c e ≤ R

/-- `e` is a padded even neighbour of the odd task at `c` (08:17–20): ordinary `(g, b)`, `d_H(a, b) ≤ 1`, or
cross `(u, a)`, `u ∈ E(g)`. -/
def PadNbr (c e : Cell η₀ n) : Prop :=
  (e.1 = c.1 ∧ e.2 ∈ ordNbrs c.2) ∨ (e.2 = c.2 ∧ e.1 ∈ crossKeys c.1)

end Dist

/-! ## Parity roles -/

/-- Even roles (placed on the first side). -/
abbrev EvenRole (n : ℕ) := {v : CubeVertex n // IsEvenRole v}

/-- Odd roles (placed on the second side). -/
abbrev OddRole (n : ℕ) := {v : CubeVertex n // ¬ IsEvenRole v}

/-- The odd neighbour of an even role across coordinate `j`. -/
def oddNbr {n : ℕ} (a : EvenRole n) (j : Fin n) : OddRole n :=
  ⟨cubeFlip a.1 j, fun h => ((cubeFlip_parity a.1 j).mp h) a.2⟩

/-- The odd labels seen by an even role, indexed by the flipped coordinate. -/
def nbrLabels {n N : ℕ} (f : OddRole n → Fin N) (a : EvenRole n) : Fin n → Fin N :=
  fun j => f (oddNbr a j)

/-! ## Height-device parameters (08:126–131) -/

/-- `b = τ/16`. -/
def bH (η₀ : ℝ) : ℝ := tau8 η₀ / 16

/-- `b₀ = b/4`. -/
def b0H (η₀ : ℝ) : ℝ := bH η₀ / 4

/-- `ζ = b₀/8`. -/
def zetaH (η₀ : ℝ) : ℝ := b0H η₀ / 8

/-- `σ = b₀/16`. -/
def sigmaH (η₀ : ℝ) : ℝ := b0H η₀ / 16

/-- `θ = 1 - b₀/8`. -/
def thetaH (η₀ : ℝ) : ℝ := 1 - b0H η₀ / 8

/-- `a = b₀/2` (so `ζ + σ + (1-θ) < a < b₀` and `a + 4σ < b`). -/
def aH (η₀ : ℝ) : ℝ := b0H η₀ / 2

/-- `r = ⌊ρ n⌋`, `ρ = .01`. -/
def rH (n : ℕ) : ℕ := ⌊(n : ℝ) / 100⌋₊

/-- The top height `H`, the first scale at least `n^{1-ζ}`. -/
def HH (η₀ : ℝ) (n : ℕ) : ℕ := topScale n (sigmaH η₀) (zetaH η₀)

/-- The height device in one grid slice: `Q_{n-m}`, `D = 2`, `r`, `H`, `λ = n^{10}`, `b₀`, `b`. -/
abbrev hdP (η₀ : ℝ) (n : ℕ) : HDParams where
  n := n
  d := dC η₀ n
  D := 2
  r := rH n
  H := HH η₀ n
  lam := (n : ℝ) ^ (10 : ℝ)
  b₀ := b0H η₀
  b := bH η₀

/-- The linear-radius regime of the height device, `c_r = 1/200`. -/
def hdRegime (η₀ : ℝ) : HDRegime (b0H η₀) (bH η₀) 2 :=
  .lin (1 / 200) ⟨by norm_num, by norm_num⟩

/-- L8.1d's height admissibility (08:128–130): `J₀ = 10`, `b₀ < b < 1`, `D = 2`, the small exponents above, and
the linear dimension window `n/2 ≤ n - m ≤ n`. -/
theorem hd_admissible (η₀ : ℝ) (hη₀ : 0 < η₀) :
    HDAdmissible 10 (b0H η₀) (bH η₀) (sigmaH η₀) (zetaH η₀) (thetaH η₀) (aH η₀) (1 / 2) 1 2 := by
  have hτpos : 0 < tau8 η₀ := by
    unfold tau8
    apply div_pos
    · exact lt_min (by linarith) (by norm_num)
    · norm_num
  have hτle : tau8 η₀ ≤ (1 : ℝ) / 100 := by
    unfold tau8
    calc
      min (η₀ / 2) (4 / 100) / 4 ≤ (4 / 100 : ℝ) / 4 :=
        div_le_div_of_nonneg_right (min_le_right _ _) (by norm_num)
      _ = 1 / 100 := by norm_num
  refine ⟨by norm_num, ?_, by norm_num, ?_, ?_, ?_⟩
  ·
    constructor
    · simp [b0H, bH]
      positivity
    · constructor
      · simp [b0H, bH]
        nlinarith [hτpos]
      · simp [bH]
        nlinarith [hτle]
  · refine ⟨?_, ?_, ?_, ?_, ?_⟩
    · simp [sigmaH, b0H, bH]
      positivity
    · simp [sigmaH, zetaH, b0H, bH]
      nlinarith [hτpos]
    · simp [zetaH, b0H, bH]
      nlinarith [hτle]
    · simp [thetaH, b0H, bH]
      nlinarith [hτle]
    · simp [thetaH, b0H, bH]
      nlinarith [hτpos]
  · refine ⟨?_, ?_, ?_⟩
    · simp [zetaH, sigmaH, thetaH, aH, b0H, bH]
      ring_nf
      nlinarith
    · simp [aH, b0H, bH]
      nlinarith [hτpos]
    · simp [aH, sigmaH, bH, b0H]
      ring_nf
      nlinarith [hτpos]
  · constructor <;> norm_num

/-! ## Near fractions for the scattered-moment estimates (08:345–347, 08:356–361, 08:415–421, 08:450–453) -/

/-- Even roles whose grid key is within distance `R` of that of `a`. -/
def evenKeyNear (η₀ : ℝ) {n : ℕ} (R : ℕ) (a : EvenRole n) : Finset (EvenRole n) :=
  Finset.univ.filter fun a' => keyDist (keyOf η₀ a'.1) (keyOf η₀ a.1) ≤ R

/-- Odd roles whose grid key is within distance `R` of that of `u`. -/
def oddKeyNear (η₀ : ℝ) {n : ℕ} (R : ℕ) (u : OddRole n) : Finset (OddRole n) :=
  Finset.univ.filter fun u' => keyDist (keyOf η₀ u'.1) (keyOf η₀ u.1) ≤ R

/-- Even roles whose residual word is within Hamming distance `R` of that of `a`. -/
def evenResNear (η₀ : ℝ) {n : ℕ} (R : ℕ) (a : EvenRole n) : Finset (EvenRole n) :=
  Finset.univ.filter fun a' => _root_.hammingDist (resOf η₀ a'.1) (resOf η₀ a.1) ≤ R

/-- `f_grid = n^9 (2n^{-.04})^s` (08:346). -/
def fGrid (η₀ : ℝ) (n : ℕ) : ℝ := (n : ℝ) ^ (9 : ℕ) * (2 * (n : ℝ) ^ (-(4 / 100 : ℝ))) ^ sC η₀ n

/-- `f_res(R) = 2 · 2^{-(n-m)} Σ_{j ≤ R} C(n-m, j)` (08:358–361, with the parity factor two). -/
def fRes (η₀ : ℝ) (n R : ℕ) : ℝ :=
  2 * (∑ j ∈ Finset.range (R + 1), (Nat.choose (dC η₀ n) j : ℝ)) / (2 : ℝ) ^ dC η₀ n

/-- The geometric facts of L8.1a at one dimension. -/
structure GridFacts (η₀ : ℝ) (n : ℕ) : Prop where
  pos : 1 ≤ n ∧ 1 ≤ lC n ∧ 1 ≤ sC η₀ n
  split : 2 * mC η₀ n ≤ n
  hd_ok : (hdRegime η₀).ok n (dC η₀ n) (rH n) ∧ (1 / 2 : ℝ) * n ≤ dC η₀ n ∧ (dC η₀ n : ℝ) ≤ 1 * n
  crossKeys_card : ∀ g : Key η₀ n, (crossKeys g).card ≤ 2 * sC η₀ n
  edge : ∀ v w : CubeVertex n, (cube n).Adj v w → PadNbr (cellOf η₀ v) (cellOf η₀ w)
  even_card : Fintype.card (EvenRole n) = 2 ^ (n - 1)
  odd_card : Fintype.card (OddRole n) = 2 ^ (n - 1)
  near_even : ∀ a : EvenRole n,
    ((evenKeyNear η₀ 8 a).card : ℝ) ≤ fGrid η₀ n * Fintype.card (EvenRole n)
  near_odd : ∀ u : OddRole n,
    ((oddKeyNear η₀ 8 u).card : ℝ) ≤ fGrid η₀ n * Fintype.card (OddRole n)
  res_near : ∀ (R : ℕ) (a : EvenRole n),
    ((evenResNear η₀ R a).card : ℝ) ≤ fRes η₀ n R * Fintype.card (EvenRole n)

/-! ## L8.1a nodes -/

/-- L8.1a(i) (08:16, 08:126–131): for large `n`, `ℓ, s ≥ 1`, `2m ≤ n` (as `m ≤ n^{τ+.2}+n^{.2}`), the residual
dimension lies in the linear window of the height regime (`n/200 ≤ ⌊n/100⌋`, `4⌊n/100⌋ ≤ n - m`), and every key
has at most `2s` one-bin-step neighbours. -/
theorem grid_basic (η₀ : ℝ) (hη₀ : 0 < η₀) :
    ∃ n₀ : ℕ, ∀ n ≥ n₀, (1 ≤ n ∧ 1 ≤ lC n ∧ 1 ≤ sC η₀ n) ∧ 2 * mC η₀ n ≤ n ∧
      ((hdRegime η₀).ok n (dC η₀ n) (rH n) ∧ (1 / 2 : ℝ) * n ≤ dC η₀ n ∧ (dC η₀ n : ℝ) ≤ 1 * n) ∧
      ∀ g : Key η₀ n, (crossKeys g).card ≤ 2 * sC η₀ n := by
  have hτpos : 0 < tau8 η₀ := by
    unfold tau8
    apply div_pos
    · exact lt_min (by linarith) (by norm_num)
    · norm_num
  have hτle : tau8 η₀ ≤ (1 : ℝ) / 100 := by
    unfold tau8
    calc
      min (η₀ / 2) (4 / 100) / 4 ≤ (4 / 100 : ℝ) / 4 :=
        div_le_div_of_nonneg_right (min_le_right _ _) (by norm_num)
      _ = 1 / 100 := by norm_num
  have hpow79 : Filter.Tendsto (fun n : ℕ => (n : ℝ) ^ ((79 : ℝ) / 100))
      Filter.atTop Filter.atTop :=
    (_root_.tendsto_rpow_atTop (by norm_num)).comp tendsto_natCast_atTop_atTop
  have hpow80 : Filter.Tendsto (fun n : ℕ => (n : ℝ) ^ ((4 : ℝ) / 5))
      Filter.atTop Filter.atTop :=
    (_root_.tendsto_rpow_atTop (by norm_num)).comp tendsto_natCast_atTop_atTop
  have hlarge79 : ∀ᶠ n : ℕ in Filter.atTop, (4 : ℝ) ≤ (n : ℝ) ^ ((79 : ℝ) / 100) :=
    hpow79.eventually (Filter.eventually_ge_atTop (4 : ℝ))
  have hlarge80 : ∀ᶠ n : ℕ in Filter.atTop, (4 : ℝ) ≤ (n : ℝ) ^ ((4 : ℝ) / 5) :=
    hpow80.eventually (Filter.eventually_ge_atTop (4 : ℝ))
  have hlarge : ∀ᶠ n : ℕ in Filter.atTop,
      200 ≤ n ∧ (4 : ℝ) ≤ (n : ℝ) ^ ((79 : ℝ) / 100) ∧
        (4 : ℝ) ≤ (n : ℝ) ^ ((4 : ℝ) / 5) := by
    filter_upwards [Filter.eventually_atTop.2 ⟨200, fun _ hn => hn⟩, hlarge79, hlarge80]
      with n hn h79 h80
    exact ⟨hn, h79, h80⟩
  obtain ⟨n₀, hn₀⟩ := Filter.eventually_atTop.1 hlarge
  refine ⟨n₀, ?_⟩
  intro n hn
  have hN := hn₀ n hn
  have hn200 : 200 ≤ n := hN.1
  have hn1 : 1 ≤ n := by omega
  have hnR : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn1
  have hnPos : 0 < (n : ℝ) := lt_of_lt_of_le zero_lt_one hnR
  have hτcomp : (n : ℝ) ^ tau8 η₀ ≤ (n : ℝ) ^ ((1 : ℝ) / 100) :=
    Real.rpow_le_rpow_of_exponent_le hnR hτle
  have hsUpper : (sC η₀ n : ℝ) < (n : ℝ) ^ tau8 η₀ + 1 :=
    Nat.ceil_lt_add_one (Real.rpow_nonneg hnPos.le _)
  have hsUpper' : (sC η₀ n : ℝ) ≤ (n : ℝ) ^ ((1 : ℝ) / 100) + 1 :=
    le_trans hsUpper.le (by linarith [hτcomp])
  have hsLowerPow : 1 ≤ (n : ℝ) ^ tau8 η₀ := Real.one_le_rpow hnR hτpos.le
  have hsLower : 1 ≤ sC η₀ n := by
    have hsReal : (1 : ℝ) ≤ (sC η₀ n : ℝ) := hsLowerPow.trans (Nat.le_ceil _)
    exact_mod_cast hsReal
  have hlowerPow : 1 < (n : ℝ) ^ ((1 : ℝ) / 5) :=
    Real.one_lt_rpow (by exact_mod_cast (show 1 < n by omega)) (by norm_num)
  have hfloorUpper : (n : ℝ) ^ ((1 : ℝ) / 5) < (lC n : ℝ) + 1 :=
    Nat.lt_floor_add_one _
  have hlower : 1 ≤ lC n := by
    by_contra h
    have hz : lC n = 0 := by omega
    rw [hz] at hfloorUpper
    nlinarith
  have hlUpper : (lC n : ℝ) ≤ (n : ℝ) ^ ((1 : ℝ) / 5) :=
    Nat.floor_le (Real.rpow_nonneg hnPos.le _)
  have hmul : (mC η₀ n : ℝ) = (sC η₀ n : ℝ) * (lC n : ℝ) := by simp [mC]
  have hpowProd : (n : ℝ) ^ ((1 : ℝ) / 100) *
      (n : ℝ) ^ ((1 : ℝ) / 5) = (n : ℝ) ^ ((21 : ℝ) / 100) := by
    rw [← Real.rpow_add hnPos]
    congr 1 <;> norm_num
  have hmBound : 2 * (mC η₀ n : ℝ) ≤ (n : ℝ) := by
    have hprod : (sC η₀ n : ℝ) * (lC n : ℝ) ≤
        ((n : ℝ) ^ ((1 : ℝ) / 100) + 1) * (n : ℝ) ^ ((1 : ℝ) / 5) :=
      mul_le_mul hsUpper' hlUpper (by positivity) (by positivity)
    have hpow21 : 4 * (n : ℝ) ^ ((21 : ℝ) / 100) ≤ (n : ℝ) := by
      calc
        4 * (n : ℝ) ^ ((21 : ℝ) / 100) ≤
            (n : ℝ) ^ ((79 : ℝ) / 100) * (n : ℝ) ^ ((21 : ℝ) / 100) :=
          mul_le_mul_of_nonneg_right hN.2.1 (Real.rpow_nonneg hnPos.le _)
        _ = (n : ℝ) := by
          rw [← Real.rpow_add hnPos]
          norm_num
    have hpow20 : 4 * (n : ℝ) ^ ((1 : ℝ) / 5) ≤ (n : ℝ) := by
      calc
        4 * (n : ℝ) ^ ((1 : ℝ) / 5) ≤
            (n : ℝ) ^ ((4 : ℝ) / 5) * (n : ℝ) ^ ((1 : ℝ) / 5) :=
          mul_le_mul_of_nonneg_right hN.2.2 (Real.rpow_nonneg hnPos.le _)
        _ = (n : ℝ) := by
          rw [← Real.rpow_add hnPos]
          norm_num
    calc
      2 * (mC η₀ n : ℝ) = 2 * ((sC η₀ n : ℝ) * (lC n : ℝ)) := by rw [hmul]
      _ ≤ 2 * (((n : ℝ) ^ ((1 : ℝ) / 100) + 1) * (n : ℝ) ^ ((1 : ℝ) / 5)) :=
        mul_le_mul_of_nonneg_left hprod (by norm_num)
      _ = 2 * (n : ℝ) ^ ((21 : ℝ) / 100) + 2 * (n : ℝ) ^ ((1 : ℝ) / 5) := by
        rw [add_mul, hpowProd]
        ring
      _ ≤ (n : ℝ) := by linarith
  have hsplit : 2 * mC η₀ n ≤ n := by exact_mod_cast hmBound
  have hdim2 : n ≤ 2 * dC η₀ n := by
    dsimp [dC]
    omega
  have hdimLo : (1 / 2 : ℝ) * n ≤ (dC η₀ n : ℝ) := by
    have hdim2R : (n : ℝ) ≤ 2 * (dC η₀ n : ℝ) := by exact_mod_cast hdim2
    linarith
  have hdimHi : (dC η₀ n : ℝ) ≤ 1 * (n : ℝ) := by
    have hdimNat : dC η₀ n ≤ n := by dsimp [dC]; omega
    have hdimR : (dC η₀ n : ℝ) ≤ (n : ℝ) := by exact_mod_cast hdimNat
    simpa using hdimR
  have hrUpper : (rH n : ℝ) ≤ (n : ℝ) / 100 := Nat.floor_le (by positivity)
  have hrFloor : (n : ℝ) / 100 < (rH n : ℝ) + 1 := Nat.lt_floor_add_one _
  have hn200R : (200 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn200
  have hrLower : (n : ℝ) / 200 ≤ (rH n : ℝ) := by nlinarith
  have hok : (hdRegime η₀).ok n (dC η₀ n) (rH n) := by
    change (1 / 200 : ℝ) * (dC η₀ n : ℝ) ≤ (rH n : ℝ) ∧
      4 * rH n ≤ dC η₀ n
    constructor
    · have h1 : (1 / 200 : ℝ) * (dC η₀ n : ℝ) ≤ (n : ℝ) / 200 := by
        nlinarith [hdimHi]
      exact h1.trans hrLower
    · have h4 : (4 : ℝ) * (rH n : ℝ) ≤ (dC η₀ n : ℝ) := by nlinarith [hrUpper, hdimLo]
      exact_mod_cast h4
  have hcross (g : Key η₀ n) : (crossKeys g).card ≤ 2 * sC η₀ n := by
    change (Finset.univ.filter (fun u : Fin (sC η₀ n) → Fin (lC n + 1) =>
      (∑ r : Fin (sC η₀ n), Nat.dist (g r).val (u r).val) = 1)).card ≤
        2 * sC η₀ n
    exact keyDistOne_card_bound (s := sC η₀ n) (q := lC n + 1) g
  exact ⟨⟨by omega, hlower, hsLower⟩, hsplit, ⟨hok, hdimLo, hdimHi⟩, hcross⟩

/-- L8.1a(ii) (08:21): the ordinary and cross lists contain every cube edge.  Flipping a residual bit changes only
the residual word, by one; flipping a bit of chunk `r` changes only its count, by one. -/
theorem grid_edge_cover (η₀ : ℝ) (n : ℕ) (hm : mC η₀ n ≤ n) :
    ∀ v w : CubeVertex n, (cube n).Adj v w → PadNbr (cellOf η₀ v) (cellOf η₀ w) := by
  classical
  intro v w hadj
  change _root_.hammingDist v w = 1 at hadj
  obtain ⟨i, hdiffSet⟩ := Finset.card_eq_one.mp hadj
  have hdiff : v i ≠ w i := by
    have hi : i ∈ Finset.univ.filter (fun j : Fin n => v j ≠ w j) := by
      rw [hdiffSet]
      simp
    exact (Finset.mem_filter.mp hi).2
  have hsame : ∀ j : Fin n, j ≠ i → v j = w j := by
    intro j hji
    by_contra hne
    have hj : j ∈ Finset.univ.filter (fun k : Fin n => v k ≠ w k) :=
      Finset.mem_filter.mpr ⟨Finset.mem_univ _, hne⟩
    rw [hdiffSet] at hj
    exact hji (Finset.mem_singleton.mp hj)
  let m := mC η₀ n
  let l := lC n
  have hmn : m ≤ n := by dsimp [m]; exact hm
  by_cases hspecial : i.val < m
  · have hmpos : 0 < m := by omega
    have hlpos : 0 < l := by
      by_contra h
      have hlzero : l = 0 := by omega
      have : m = 0 := by simp [m, mC, l, hlzero]
      omega
    have hiChunk : i.val < sC η₀ n * l := by
      simpa [m, mC] using hspecial
    have hquot : i.val / l < sC η₀ n :=
      (Nat.div_lt_iff_lt_mul hlpos).2 (by simpa [Nat.mul_comm] using hiChunk)
    let r : Fin (sC η₀ n) := ⟨i.val / l, hquot⟩
    have hiq : i.val / l = r.val := rfl
    let A : CubeVertex n → Finset (Fin n) := fun u =>
      Finset.univ.filter (fun j => j.val < m ∧ j.val / l = r.val ∧ u j = true)
    let C : Finset (Fin n) :=
      Finset.univ.filter (fun j => j.val < m ∧ j.val / l = r.val)
    have hiC : i ∈ C := by
      simp [C, hspecial, hiq]
    have hCcard : C.card ≤ l := by
      let rem : {j : Fin n // j ∈ C} → Fin l := fun j =>
        ⟨j.1.val % l, Nat.mod_lt _ hlpos⟩
      have hrem : Function.Injective rem := by
        intro x y hxy
        apply Subtype.ext
        apply Fin.ext
        have hxq : x.1.val / l = r.val := (Finset.mem_filter.mp x.2).2.2
        have hyq : y.1.val / l = r.val := (Finset.mem_filter.mp y.2).2.2
        have hmod : x.1.val % l = y.1.val % l := congrArg Fin.val hxy
        have hxrep : x.1.val % l + l * (x.1.val / l) = x.1.val := Nat.mod_add_div _ _
        have hyrep : y.1.val % l + l * (y.1.val / l) = y.1.val := Nat.mod_add_div _ _
        calc
          x.1.val = x.1.val % l + l * (x.1.val / l) := hxrep.symm
          _ = y.1.val % l + l * (y.1.val / l) := by rw [hmod, hxq, hyq]
          _ = y.1.val := hyrep
      calc
        C.card = Fintype.card {j : Fin n // j ∈ C} := by
          symm
          exact Fintype.card_of_subtype C (by intro j; simp)
        _ ≤ Fintype.card (Fin l) := Fintype.card_le_of_injective rem hrem
        _ = l := by simp
    have hAway (q : Fin (sC η₀ n)) (hq : q ≠ r) :
        chunkWeight η₀ v q = chunkWeight η₀ w q := by
      unfold chunkWeight
      congr 1
      ext j
      simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      constructor
      · rintro ⟨hjm, hjq, hv⟩
        refine ⟨hjm, hjq, ?_⟩
        have hji : j ≠ i := by
          intro h
          apply hq
          apply Fin.ext
          calc
            q.val = j.val / l := hjq.symm
            _ = i.val / l := by rw [h]
            _ = r.val := hiq
        rw [hsame j hji] at hv
        exact hv
      · rintro ⟨hjm, hjq, hw⟩
        refine ⟨hjm, hjq, ?_⟩
        have hji : j ≠ i := by
          intro h
          apply hq
          apply Fin.ext
          calc
            q.val = j.val / l := hjq.symm
            _ = i.val / l := by rw [h]
            _ = r.val := hiq
        rw [← hsame j hji] at hw
        exact hw
    have hkeyAway (q : Fin (sC η₀ n)) (hq : q ≠ r) :
        keyOf η₀ v q = keyOf η₀ w q := by
      apply Fin.ext
      simp [keyOf, hAway q hq]
    have hresEq : resOf η₀ v = resOf η₀ w := by
      funext j
      apply hsame
      intro heq
      have hv := congrArg Fin.val heq
      dsimp [m] at hspecial
      simp only [resOf] at hv
      omega
    have hbit : (v i = false ∧ w i = true) ∨ (v i = true ∧ w i = false) := by
      cases hv : v i <;> cases hw : w i <;> simp_all
    have hkeydist : keyDist (keyOf η₀ v) (keyOf η₀ w) = 1 := by
      have hcoord : Nat.dist (keyOf η₀ v r).val (keyOf η₀ w r).val = 1 := by
        rcases hbit with ⟨hv, hw⟩ | ⟨hv, hw⟩
        · have hset : A w = insert i (A v) := by
            ext j
            by_cases hji : j = i
            · subst j
              simp [A, hspecial, hiq, hv, hw]
            · simp [A, hji, hsame j hji]
          have hnot : i ∉ A v := by simp [A, hv]
          have hweight : chunkWeight η₀ w r = chunkWeight η₀ v r + 1 := by
            unfold chunkWeight
            have hh : (Finset.univ.filter
                (fun j : Fin n => j.val < m ∧ j.val / l = r.val ∧ w j = true)) =
                insert i (Finset.univ.filter
                  (fun j : Fin n => j.val < m ∧ j.val / l = r.val ∧ v j = true)) := by
              simpa [A] using hset
            rw [hh, Finset.card_insert_of_notMem hnot]
          have hrawV : chunkWeight η₀ v r ≤ C.card - 1 := by
            have hsub : A v ⊆ C.erase i := by
              intro j hj
              have hj' := Finset.mem_filter.mp hj
              have hjcoord : j.val < m ∧ j.val / l = r.val :=
                ⟨hj'.2.1, hj'.2.2.1⟩
              refine Finset.mem_erase.mpr ⟨?_, Finset.mem_filter.mpr ⟨hj'.1, hjcoord⟩⟩
              intro hji
              subst j
              simp [A, hv] at hj
            have hcardSub : (A v).card ≤ (C.erase i).card := Finset.card_le_card hsub
            have herase : (C.erase i).card = C.card - 1 := Finset.card_erase_of_mem hiC
            simpa [A, chunkWeight, herase] using hcardSub
          have hrawVle : chunkWeight η₀ v r ≤ l := by
            have hle : chunkWeight η₀ v r ≤ C.card :=
              le_trans hrawV (Nat.sub_le _ _)
            exact hle.trans hCcard
          have hrawW : chunkWeight η₀ w r ≤ l := by
            rw [hweight]
            have hCpos : 1 ≤ C.card := Finset.card_pos.mpr ⟨i, hiC⟩
            have hle : chunkWeight η₀ v r + 1 ≤ C.card := by omega
            exact hle.trans hCcard
          have hvKey : (keyOf η₀ v r).val = chunkWeight η₀ v r := by
            change min (chunkWeight η₀ v r) (lC n) = chunkWeight η₀ v r
            exact Nat.min_eq_left (by simpa [l] using hrawVle)
          have hwKey : (keyOf η₀ w r).val = chunkWeight η₀ w r := by
            change min (chunkWeight η₀ w r) (lC n) = chunkWeight η₀ w r
            exact Nat.min_eq_left (by simpa [l] using hrawW)
          rw [hvKey, hwKey, hweight]
          rw [Nat.dist_eq_sub_of_le (by omega)]
          omega
        · have hset : A v = insert i (A w) := by
            ext j
            by_cases hji : j = i
            · subst j
              simp [A, hspecial, hiq, hv, hw]
            · simp [A, hji, hsame j hji]
          have hnot : i ∉ A w := by simp [A, hw]
          have hweight : chunkWeight η₀ v r = chunkWeight η₀ w r + 1 := by
            unfold chunkWeight
            have hh : (Finset.univ.filter
                (fun j : Fin n => j.val < m ∧ j.val / l = r.val ∧ v j = true)) =
                insert i (Finset.univ.filter
                  (fun j : Fin n => j.val < m ∧ j.val / l = r.val ∧ w j = true)) := by
              simpa [A] using hset
            rw [hh, Finset.card_insert_of_notMem hnot]
          have hrawW : chunkWeight η₀ w r ≤ C.card - 1 := by
            have hsub : A w ⊆ C.erase i := by
              intro j hj
              have hj' := Finset.mem_filter.mp hj
              have hjcoord : j.val < m ∧ j.val / l = r.val :=
                ⟨hj'.2.1, hj'.2.2.1⟩
              refine Finset.mem_erase.mpr ⟨?_, Finset.mem_filter.mpr ⟨hj'.1, hjcoord⟩⟩
              intro hji
              subst j
              simp [A, hw] at hj
            have hcardSub : (A w).card ≤ (C.erase i).card := Finset.card_le_card hsub
            have herase : (C.erase i).card = C.card - 1 := Finset.card_erase_of_mem hiC
            simpa [A, chunkWeight, herase] using hcardSub
          have hrawWle : chunkWeight η₀ w r ≤ l := by
            have hle : chunkWeight η₀ w r ≤ C.card :=
              le_trans hrawW (Nat.sub_le _ _)
            exact hle.trans hCcard
          have hrawV : chunkWeight η₀ v r ≤ l := by
            rw [hweight]
            have hCpos : 1 ≤ C.card := Finset.card_pos.mpr ⟨i, hiC⟩
            have hle : chunkWeight η₀ w r + 1 ≤ C.card := by omega
            exact hle.trans hCcard
          have hvKey : (keyOf η₀ v r).val = chunkWeight η₀ v r := by
            change min (chunkWeight η₀ v r) (lC n) = chunkWeight η₀ v r
            exact Nat.min_eq_left (by simpa [l] using hrawV)
          have hwKey : (keyOf η₀ w r).val = chunkWeight η₀ w r := by
            change min (chunkWeight η₀ w r) (lC n) = chunkWeight η₀ w r
            exact Nat.min_eq_left (by simpa [l] using hrawWle)
          rw [hvKey, hwKey, hweight]
          rw [Nat.dist_comm]
          rw [Nat.dist_eq_sub_of_le (by omega)]
          omega
      have hsum : keyDist (keyOf η₀ v) (keyOf η₀ w) =
          ∑ q : Fin (sC η₀ n), if q = r then 1 else 0 := by
        unfold keyDist
        apply Finset.sum_congr rfl
        intro q hq
        by_cases hqr : q = r
        · subst q
          simp [hcoord]
        · simp [hkeyAway q hqr, hqr]
      rw [hsum]
      simp
    refine Or.inr ⟨hresEq.symm, ?_⟩
    change keyOf η₀ w ∈ crossKeys (keyOf η₀ v)
    simp [crossKeys, hkeydist]
  · let j : Fin (dC η₀ n) := ⟨i.val - m, by dsimp [m, dC]; omega⟩
    have hkeyEq : keyOf η₀ v = keyOf η₀ w := by
      funext r
      apply Fin.ext
      have hweight : chunkWeight η₀ v r = chunkWeight η₀ w r := by
        unfold chunkWeight
        congr 1
        ext k
        simp only [Finset.mem_filter, Finset.mem_univ, true_and]
        constructor
        · rintro ⟨hkm, hkr, hv⟩
          refine ⟨hkm, hkr, ?_⟩
          have hki : k ≠ i := by
            intro heq
            have := congrArg Fin.val heq
            omega
          rw [hsame k hki] at hv
          exact hv
        · rintro ⟨hkm, hkr, hw⟩
          refine ⟨hkm, hkr, ?_⟩
          have hki : k ≠ i := by
            intro heq
            have := congrArg Fin.val heq
            omega
          rw [← hsame k hki] at hw
          exact hw
      simp [keyOf, hweight]
    have hdistRes : _root_.hammingDist (resOf η₀ v) (resOf η₀ w) = 1 := by
      change (Finset.univ.filter fun k : Fin (dC η₀ n) =>
        resOf η₀ v k ≠ resOf η₀ w k).card = 1
      have hset : (Finset.univ.filter fun k : Fin (dC η₀ n) =>
          resOf η₀ v k ≠ resOf η₀ w k) = {j} := by
        ext k
        by_cases hkj : k = j
        · subst k
          have hidx : (⟨m + j.val, by have hj := j.isLt; dsimp [m, dC] at hj ⊢; omega⟩ : Fin n) = i := by
            apply Fin.ext
            dsimp [j]
            omega
          have hneq : resOf η₀ v j ≠ resOf η₀ w j := by
            intro heq
            apply hdiff
            simpa [resOf, m, hidx] using heq
          simp [hneq]
        · have hidx : (⟨m + k.val, by have hk := k.isLt; dsimp [m, dC] at hk ⊢; omega⟩ : Fin n) ≠ i := by
            intro heq
            apply hkj
            apply Fin.ext
            dsimp [j]
            have hv := congrArg Fin.val heq
            dsimp [j] at hv
            omega
          have hsame' := hsame _ hidx
          simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_singleton]
          change (resOf η₀ v k ≠ resOf η₀ w k) ↔ k = j
          have heq : resOf η₀ v k = resOf η₀ w k := by
            simpa [resOf, m] using hsame'
          simp [heq, hkj]
      rw [hset]
      simp
    refine Or.inl ⟨hkeyEq.symm, ?_⟩
    change resOf η₀ w ∈ ordNbrs (resOf η₀ v)
    simp [ordNbrs, hdistRes]

/-- L8.1a(iii) (08:345–347, 08:415–419): for large `n`, the roles of either parity whose grid key is within
distance eight of a given one form a fraction at most `f_grid`.  At most `(2s+1)^8` keys are that near, each key
is read by at most `2^n max_k C(ℓ,k)^s / 2^{ℓ s}` vertices, and a Binomial(ℓ,1/2) atom is at most `2n^{-.04}`. -/
theorem grid_near (η₀ : ℝ) (hη₀ : 0 < η₀) :
    ∃ n₀ : ℕ, ∀ n ≥ n₀,
      (∀ a : EvenRole n, ((evenKeyNear η₀ 8 a).card : ℝ) ≤ fGrid η₀ n * Fintype.card (EvenRole n)) ∧
      (∀ u : OddRole n, ((oddKeyNear η₀ 8 u).card : ℝ) ≤ fGrid η₀ n * Fintype.card (OddRole n)) := by
  classical
  obtain ⟨n₁, hbasic⟩ := grid_basic η₀ hη₀
  have hpow12 : Filter.Tendsto (fun n : ℕ => (n : ℝ) ^ ((3 : ℝ) / 25))
      Filter.atTop Filter.atTop :=
    (_root_.tendsto_rpow_atTop (by norm_num)).comp tendsto_natCast_atTop_atTop
  have hlarge12 : ∀ᶠ n : ℕ in Filter.atTop, (2 : ℝ) ≤ (n : ℝ) ^ ((3 : ℝ) / 25) :=
    hpow12.eventually (Filter.eventually_ge_atTop (2 : ℝ))
  obtain ⟨n₂, hn₂⟩ := Filter.eventually_atTop.1 hlarge12
  have hpow99 : Filter.Tendsto (fun n : ℕ => (n : ℝ) ^ ((99 : ℝ) / 100))
      Filter.atTop Filter.atTop :=
    (_root_.tendsto_rpow_atTop (by norm_num)).comp tendsto_natCast_atTop_atTop
  have hlarge99 : ∀ᶠ n : ℕ in Filter.atTop, (2 : ℝ) ≤ (n : ℝ) ^ ((99 : ℝ) / 100) :=
    hpow99.eventually (Filter.eventually_ge_atTop (2 : ℝ))
  obtain ⟨n₃, hn₃⟩ := Filter.eventually_atTop.1 hlarge99
  refine ⟨max (max (max n₁ n₂) n₃) 100000, ?_⟩
  intro n hn
  have hn₁ : n₁ ≤ n := le_trans (le_max_left _ _)
    (le_trans (le_max_left _ _) (le_trans (le_max_left _ _) hn))
  have hn₂' : n₂ ≤ n := le_trans (le_max_right _ _)
    (le_trans (le_max_left _ _) (le_trans (le_max_left _ _) hn))
  have hn₃' : n₃ ≤ n := le_trans (le_max_right _ _)
    (le_trans (le_max_left _ _) hn)
  have hn100k : 100000 ≤ n := le_trans (le_max_right _ _) hn
  have hB := hbasic n hn₁
  have h12 := hn₂ n hn₂'
  have h99 := hn₃ n hn₃'
  obtain ⟨hpos, hsplit, _, _⟩ := hB
  have hnR : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hpos.1
  have hnPos : 0 < (n : ℝ) := lt_of_lt_of_le zero_lt_one hnR
  let s := sC η₀ n
  let l := lC n
  let m := s * l
  have hmEq : mC η₀ n = m := by simp [m, s, l, mC]
  have hml : m ≤ n := by rw [← hmEq]; omega
  have hmLt : m < n := by
    rw [← hmEq]
    omega
  have hlpos : 0 < l := by dsimp [l]; omega
  have hpow08 : 1 ≤ (n : ℝ) ^ ((2 : ℝ) / 25) :=
    Real.one_le_rpow hnR (by norm_num)
  have hpowProd08 : (n : ℝ) ^ ((2 : ℝ) / 25) *
      (n : ℝ) ^ ((3 : ℝ) / 25) = (n : ℝ) ^ ((1 : ℝ) / 5) := by
    rw [← Real.rpow_add hnPos]
    congr 1 <;> norm_num
  have hfloor : (n : ℝ) ^ ((1 : ℝ) / 5) < (l : ℝ) + 1 := Nat.lt_floor_add_one _
  have hlower : (n : ℝ) ^ ((2 : ℝ) / 25) ≤ (l : ℝ) := by
    have hdouble : 2 * (n : ℝ) ^ ((2 : ℝ) / 25) ≤
        (n : ℝ) ^ ((1 : ℝ) / 5) := by
      calc
        2 * (n : ℝ) ^ ((2 : ℝ) / 25) ≤
            (n : ℝ) ^ ((2 : ℝ) / 25) * (n : ℝ) ^ ((3 : ℝ) / 25) :=
          by
            simpa [mul_comm] using
              (mul_le_mul_of_nonneg_right h12
                (Real.rpow_nonneg (x := (n : ℝ)) (by positivity) ((2 : ℝ) / 25)))
        _ = (n : ℝ) ^ ((1 : ℝ) / 5) := hpowProd08
    nlinarith [hpow08]
  have hsquare : Real.sqrt ((n : ℝ) ^ ((2 : ℝ) / 25)) =
      (n : ℝ) ^ ((1 : ℝ) / 25) := by
    rw [Real.sqrt_eq_rpow]
    rw [← Real.rpow_mul (by positivity : (0 : ℝ) ≤ (n : ℝ)) ((2 : ℝ) / 25) (1 / 2 : ℝ)]
    congr 1 <;> norm_num
  have hroot : (n : ℝ) ^ ((1 : ℝ) / 25) ≤ Real.sqrt (l : ℝ) := by
    rw [← hsquare]
    exact Real.sqrt_le_sqrt hlower
  have hinv : 1 / Real.sqrt (l : ℝ) ≤
      1 / ((n : ℝ) ^ ((1 : ℝ) / 25)) := by
    apply (div_le_div_iff₀ (Real.sqrt_pos.2 (by exact_mod_cast hlpos))
      (Real.rpow_pos_of_pos hnPos _)).2
    simpa using hroot
  have hbinMass (b : Fin (l + 1)) :
      (∑ k : Fin (l + 1), if k = b then
        (Nat.choose l k.val : ℝ) / (2 : ℝ) ^ l else 0) ≤
          2 * (n : ℝ) ^ (-(1 : ℝ) / 25) := by
    have hcentral := centralBinomialUpper l hlpos b.val (Nat.le_of_lt_succ b.isLt)
    have hsum : (∑ k : Fin (l + 1), if k = b then
        (Nat.choose l k.val : ℝ) / (2 : ℝ) ^ l else 0) =
          (Nat.choose l b.val : ℝ) / (2 : ℝ) ^ l := by simp
    rw [hsum]
    calc
      (Nat.choose l b.val : ℝ) / (2 : ℝ) ^ l ≤ 2 / Real.sqrt (l : ℝ) := hcentral
      _ = 2 * (1 / Real.sqrt (l : ℝ)) := by ring
      _ ≤ 2 * (1 / ((n : ℝ) ^ ((1 : ℝ) / 25))) :=
        mul_le_mul_of_nonneg_left hinv (by norm_num)
      _ = 2 * (n : ℝ) ^ (-(1 : ℝ) / 25) := by
        rw [show (-(1 : ℝ) / 25) = -((1 : ℝ) / 25) by ring]
        rw [Real.rpow_neg (by positivity : (0 : ℝ) ≤ (n : ℝ)) ((1 : ℝ) / 25)]
        ring
  let idx : Fin s → Fin l → Fin n := fun r j =>
    Fin.castLE hml (finProdFinEquiv (r, j))
  let chunks : Fin s → Finset (Fin n) := fun r =>
    (Finset.univ : Finset (Fin l)).image (idx r)
  have hidxlt (r : Fin s) (j : Fin l) : (idx r j).val < m := by
    change (finProdFinEquiv (r, j)).val < s * l
    exact (finProdFinEquiv (r, j)).isLt
  have hidxInj (r : Fin s) : Function.Injective (idx r) := by
    intro j k hjk
    apply Fin.ext
    have hcast : finProdFinEquiv (r, j) = finProdFinEquiv (r, k) := by
      apply Fin.ext
      simpa [idx] using congrArg Fin.val hjk
    have hpair := finProdFinEquiv.injective hcast
    exact congrArg Fin.val (congrArg Prod.snd hpair)
  have hchunksDisj : Pairwise fun r r' => Disjoint (chunks r) (chunks r') := by
    intro r r' hrr'
    apply Finset.disjoint_left.mpr
    intro i hi hi'
    rcases Finset.mem_image.mp hi with ⟨j, _, hij⟩
    rcases Finset.mem_image.mp hi' with ⟨j', _, hij'⟩
    have hidx : idx r j = idx r' j' := hij.trans hij'.symm
    have hprod : finProdFinEquiv (r, j) = finProdFinEquiv (r', j') := by
      apply Fin.ext
      simpa [idx] using congrArg Fin.val hidx
    exact hrr' (congrArg Prod.fst (finProdFinEquiv.injective hprod))
  let bins : Fin s → ℕ := fun _ => l + 1
  let bin : ∀ r : Fin s, Fin (l + 1) → Fin (l + 1) := fun _ k => k
  let Γ : HypercubeRamsey.S07.GridGeom (4 / 25 : ℝ) n s l 0 := by
    refine ⟨chunks, ∅, ?_, hchunksDisj, ?_, ?_, ?_, bins, bin, ?_, ?_, ?_⟩
    · intro r
      change (Finset.univ.image (idx r)).card = l
      rw [Finset.card_image_of_injective _ (hidxInj r)]
      simp
    · simp
    · intro r
      simp
    · refine ⟨⟨m, hmLt⟩, by simp, ?_⟩
      intro r hi
      rcases Finset.mem_image.mp hi with ⟨j, _, hij⟩
      have hlt := hidxlt r j
      rw [hij] at hlt
      simp at hlt
    · intro r k k' h
      exact h
    · intro r b
      exact ⟨b, rfl⟩
    · intro r b
      have hrat : (-(1 : ℝ) / 25) = -(4 / 25 / 4) := by norm_num
      simpa [bin, bins, hrat.symm] using hbinMass b
  let t0 : HypercubeRamsey.S07.GridGeom.AuxWord Γ := fun _ => false
  have hchunkSet (r : Fin s) : chunks r =
      Finset.univ.filter (fun i : Fin n => i.val < m ∧ i.val / l = r.val) := by
    ext i
    constructor
    · intro hi
      rcases Finset.mem_image.mp hi with ⟨j, _, hij⟩
      have hv := congrArg Fin.val hij
      change (finProdFinEquiv (r, j)).val = i.val at hv
      have hlt : i.val < m := by rw [← hv]; exact hidxlt r j
      have hquot : i.val / l = r.val := by
        calc
          i.val / l = (idx r j).val / l := by
            rw [← hv]
            rfl
          _ = r.val := by
            change (j.val + l * r.val) / l = r.val
            rw [Nat.add_mul_div_left _ _ hlpos, Nat.div_eq_of_lt j.isLt]
            omega
      exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, ⟨hlt, hquot⟩⟩
    · intro hi
      rcases Finset.mem_filter.mp hi with ⟨_, ⟨_, hq⟩⟩
      let j : Fin l := ⟨i.val % l, Nat.mod_lt _ hlpos⟩
      apply Finset.mem_image.mpr ⟨j, Finset.mem_univ _, ?_⟩
      apply Fin.ext
      change (finProdFinEquiv (r, j)).val = i.val
      calc
        (finProdFinEquiv (r, j)).val = j.val + l * r.val := rfl
        _ = i.val % l + l * (i.val / l) := by simp [j, hq]
        _ = i.val := Nat.mod_add_div _ _
  have hchunkWeight (v : CubeVertex n) (r : Fin s) :
      chunkWeight η₀ v r = ((chunks r).filter (fun i => v i = true)).card := by
    unfold chunkWeight
    rw [hchunkSet r]
    rw [hmEq]
    simp [Finset.filter_filter, and_assoc, and_left_comm, and_comm, m, s, l]
  have hΓkey (v : CubeVertex n) :
      HypercubeRamsey.S07.GridGeom.key Γ v = (keyOf η₀ v, t0) := by
    apply Prod.ext
    · funext r
      apply Fin.ext
      have hle : chunkWeight η₀ v r ≤ l := by
        rw [hchunkWeight]
        calc
          ((chunks r).filter (fun i => v i = true)).card ≤ (chunks r).card :=
            Finset.card_filter_le _ _
          _ = l := by simpa [Γ] using Γ.chunk_card r
      have hle' : chunkWeight η₀ v r ≤ lC n := by simpa [l] using hle
      change ((chunks r).filter (fun i => v i = true)).card =
        min (chunkWeight η₀ v r) (lC n)
      calc
        ((chunks r).filter (fun i => v i = true)).card = chunkWeight η₀ v r :=
          (hchunkWeight v r).symm
        _ = min (chunkWeight η₀ v r) (lC n) := (Nat.min_eq_left hle').symm
    · funext j
      have haux : Γ.aux = (∅ : Finset (Fin n)) := rfl
      have hj : j.1 ∈ (∅ : Finset (Fin n)) := by simpa [haux] using j.2
      exfalso
      exact (Finset.notMem_empty j.1) hj
  let atom : ℝ := (2 * (n : ℝ) ^ (-(4 / 100 : ℝ))) ^ s
  have hCounts : HypercubeRamsey.S07.GeomCounts Γ :=
    HypercubeRamsey.S07.grid_counts Γ
  have hBalls : HypercubeRamsey.S07.GeomBalls Γ :=
    HypercubeRamsey.S07.grid_balls Γ
  have hτle : tau8 η₀ ≤ (1 : ℝ) / 100 := by
    unfold tau8
    calc
      min (η₀ / 2) (4 / 100) / 4 ≤ (4 / 100 : ℝ) / 4 :=
        div_le_div_of_nonneg_right (min_le_right _ _) (by norm_num)
      _ = 1 / 100 := by norm_num
  have hτcomp : (n : ℝ) ^ tau8 η₀ ≤ (n : ℝ) ^ ((1 : ℝ) / 100) :=
    Real.rpow_le_rpow_of_exponent_le hnR hτle
  have hsUpper : (s : ℝ) < (n : ℝ) ^ tau8 η₀ + 1 :=
    Nat.ceil_lt_add_one (Real.rpow_nonneg hnPos.le _)
  have hsSplit : (n : ℝ) ^ ((1 : ℝ) / 100) *
      (n : ℝ) ^ ((99 : ℝ) / 100) = (n : ℝ) := by
    rw [← Real.rpow_add hnPos]
    congr 1 <;> norm_num
  have hsPowLe : (n : ℝ) ^ ((1 : ℝ) / 100) ≤ (n : ℝ) / 2 := by
    have hmul : 2 * (n : ℝ) ^ ((1 : ℝ) / 100) ≤
        (n : ℝ) ^ ((99 : ℝ) / 100) * (n : ℝ) ^ ((1 : ℝ) / 100) := by
      simpa [mul_comm] using
        (mul_le_mul_of_nonneg_right h99
          (Real.rpow_nonneg (x := (n : ℝ)) (by positivity) ((1 : ℝ) / 100)))
    have hmul' : 2 * (n : ℝ) ^ ((1 : ℝ) / 100) ≤ (n : ℝ) := by
      calc
        2 * (n : ℝ) ^ ((1 : ℝ) / 100) ≤
            (n : ℝ) ^ ((99 : ℝ) / 100) * (n : ℝ) ^ ((1 : ℝ) / 100) := hmul
        _ = (n : ℝ) ^ ((1 : ℝ) / 100) *
            (n : ℝ) ^ ((99 : ℝ) / 100) := by ring
        _ = (n : ℝ) := hsSplit
    linarith
  have hsBound : (s : ℝ) ≤ (n : ℝ) := by
    have hsUpper' : (s : ℝ) < (n : ℝ) ^ ((1 : ℝ) / 100) + 1 := by linarith
    have hn2Nat : 2 ≤ n := by omega
    have hn2R : (2 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn2Nat
    linarith
  have hbase3 : (3 : ℝ) ^ 8 ≤ (n : ℝ) := by
    have h3Nat : (3 : ℕ) ^ 8 ≤ 100000 := by norm_num
    exact_mod_cast (le_trans h3Nat hn100k)
  have hFiberEven (k : Key η₀ n) :
      ((Finset.univ.filter fun a' : EvenRole n => keyOf η₀ a'.1 = k).card : ℝ) ≤
        (Fintype.card (EvenRole n) : ℝ) * atom := by
    let c : HypercubeRamsey.S07.GridGeom.Cell Γ := (k, t0)
    have hset : (Finset.univ.filter fun a' : EvenRole n =>
        HypercubeRamsey.S07.GridGeom.key Γ a'.1 = c) =
        (Finset.univ.filter fun a' : EvenRole n => keyOf η₀ a'.1 = k) := by
      ext a'
      simp [c, hΓkey]
    have hc := hCounts.even_count c
    rw [hset] at hc
    have hceq :
        ((Finset.univ.filter fun a' : EvenRole n => keyOf η₀ a'.1 = k).card : ℝ) =
          (Fintype.card (EvenRole n) : ℝ) * HypercubeRamsey.S07.GridGeom.keyMass Γ k := by
      simpa [c, Γ] using hc
    have hmass : HypercubeRamsey.S07.GridGeom.keyMass Γ k ≤ atom := by
      have h := hCounts.keyMass_le k
      have hexp : -(4 / 25 / 4 : ℝ) = -(4 / 100 : ℝ) := by norm_num
      simpa [atom, s, hexp] using h
    rw [hceq]
    exact mul_le_mul_of_nonneg_left hmass (by positivity)
  have hFiberOdd (k : Key η₀ n) :
      ((Finset.univ.filter fun u' : OddRole n => keyOf η₀ u'.1 = k).card : ℝ) ≤
        (Fintype.card (OddRole n) : ℝ) * atom := by
    let c : HypercubeRamsey.S07.GridGeom.Cell Γ := (k, t0)
    have hset : (Finset.univ.filter fun u' : OddRole n =>
        HypercubeRamsey.S07.GridGeom.key Γ u'.1 = c) =
        (Finset.univ.filter fun u' : OddRole n => keyOf η₀ u'.1 = k) := by
      ext u'
      simp [c, hΓkey]
    have hc := hCounts.odd_count c
    rw [hset] at hc
    have hceq :
        ((Finset.univ.filter fun u' : OddRole n => keyOf η₀ u'.1 = k).card : ℝ) =
          (Fintype.card (OddRole n) : ℝ) * HypercubeRamsey.S07.GridGeom.keyMass Γ k := by
      simpa [c, Γ] using hc
    have hmass : HypercubeRamsey.S07.GridGeom.keyMass Γ k ≤ atom := by
      have h := hCounts.keyMass_le k
      have hexp : -(4 / 25 / 4 : ℝ) = -(4 / 100 : ℝ) := by norm_num
      simpa [atom, s, hexp] using h
    rw [hceq]
    exact mul_le_mul_of_nonneg_left hmass (by positivity)
  have hnearBound {Role : Type} [Fintype Role] (V : Role → CubeVertex n)
      (hfiber : ∀ k : Key η₀ n,
        ((Finset.univ.filter fun a : Role => keyOf η₀ (V a) = k).card : ℝ) ≤
          (Fintype.card Role : ℝ) * atom) (v : CubeVertex n) :
      ((Finset.univ.filter fun a : Role =>
        keyDist (keyOf η₀ (V a)) (keyOf η₀ v) ≤ 8).card : ℝ) ≤
          fGrid η₀ n * Fintype.card Role := by
    let S := Finset.univ.filter fun a : Role =>
      keyDist (keyOf η₀ (V a)) (keyOf η₀ v) ≤ 8
    let K := HypercubeRamsey.S07.GridGeom.keyBall Γ
      (HypercubeRamsey.S07.GridGeom.key Γ v).1 8
    let f : Role → Key η₀ n := fun a => keyOf η₀ (V a)
    have hdist (a : Role) :
        HypercubeRamsey.S07.GridGeom.keyDist Γ
          (HypercubeRamsey.S07.GridGeom.key Γ v).1
          (f a) =
        keyDist (keyOf η₀ (V a)) (keyOf η₀ v) := by
      simp [HypercubeRamsey.S07.GridGeom.keyDist, keyDist, f, hΓkey, Nat.dist_comm]
      rfl
    have hmaps : (S : Set Role).MapsTo f K := by
      intro a ha
      have h := (Finset.mem_filter.mp ha).2
      apply Finset.mem_filter.mpr
      refine ⟨Finset.mem_univ _, ?_⟩
      change HypercubeRamsey.S07.GridGeom.keyDist Γ
        (HypercubeRamsey.S07.GridGeom.key Γ v).1 (f a) ≤ 8
      rw [hdist a]
      exact h
    have hcardEq : S.card = ∑ k ∈ K, (S.filter fun a => f a = k).card :=
      Finset.card_eq_sum_card_fiberwise hmaps
    have hterm (k : Key η₀ n) (hk : k ∈ K) :
        ((S.filter fun a => f a = k).card : ℝ) ≤
          (Fintype.card Role : ℝ) * atom := by
      have hsubset : S.filter (fun a => f a = k) ⊆
          Finset.univ.filter (fun a : Role => keyOf η₀ (V a) = k) := by
        intro a ha
        exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, (Finset.mem_filter.mp ha).2⟩
      have hnat := Finset.card_le_card hsubset
      have hreal : ((S.filter fun a => f a = k).card : ℝ) ≤
          ((Finset.univ.filter fun a : Role => keyOf η₀ (V a) = k).card : ℝ) := by
        exact_mod_cast hnat
      exact hreal.trans (hfiber k)
    have hsumReal : (S.card : ℝ) =
        ∑ k ∈ K, ((S.filter fun a => f a = k).card : ℝ) := by exact_mod_cast hcardEq
    have hball : (K.card : ℝ) ≤ (2 * (s : ℝ) + 1) ^ 8 := by
      simpa [K, Γ, s] using hBalls.keyBall_card
        (HypercubeRamsey.S07.GridGeom.key Γ v).1 8
    have hsmall : (2 * (s : ℝ) + 1) ≤ 3 * (n : ℝ) := by nlinarith [hsBound, hnR]
    have hK : (K.card : ℝ) ≤ (n : ℝ) ^ 9 := by
      calc
        (K.card : ℝ) ≤ (2 * (s : ℝ) + 1) ^ 8 := hball
        _ ≤ (3 * (n : ℝ)) ^ 8 := by gcongr
        _ = (3 : ℝ) ^ 8 * (n : ℝ) ^ 8 := by ring
        _ ≤ (n : ℝ) * (n : ℝ) ^ 8 :=
          mul_le_mul_of_nonneg_right hbase3 (by positivity)
        _ = (n : ℝ) ^ 9 := by ring
    calc
      (S.card : ℝ) =
          ∑ k ∈ K, ((S.filter fun a => f a = k).card : ℝ) := hsumReal
      _ ≤ ∑ k ∈ K, ((Fintype.card Role : ℝ) * atom) := by
        apply Finset.sum_le_sum
        intro k hk
        exact hterm k hk
      _ = (K.card : ℝ) * (Fintype.card Role : ℝ) * atom := by simp [mul_assoc]
      _ ≤ (n : ℝ) ^ 9 * (Fintype.card Role : ℝ) * atom := by
        calc
          (K.card : ℝ) * (Fintype.card Role : ℝ) * atom =
              (K.card : ℝ) * ((Fintype.card Role : ℝ) * atom) := by ring
          _ ≤ (n : ℝ) ^ 9 * ((Fintype.card Role : ℝ) * atom) :=
            mul_le_mul_of_nonneg_right hK (by positivity)
          _ = (n : ℝ) ^ 9 * (Fintype.card Role : ℝ) * atom := by ring
      _ = fGrid η₀ n * Fintype.card Role := by
        simp [fGrid, atom, s, mul_assoc, mul_comm, mul_left_comm]
  refine ⟨?_, ?_⟩
  · intro a
    simpa [evenKeyNear] using
      (hnearBound (Role := EvenRole n) (fun a' => a'.1) hFiberEven a.1)
  · intro u
    simpa [oddKeyNear] using
      (hnearBound (Role := OddRole n) (fun u' => u'.1) hFiberOdd u.1)

/-- L8.1a(iv) (08:358–360): the even roles with residual word within distance `R` of a given one are at most
`2^m Σ_{j ≤ R} C(n-m, j) = f_res(R) |A|` (exact count once `m < n`, `|A| = 2^{n-1}`). -/
theorem res_near_count (η₀ : ℝ) (n : ℕ) (hn : 1 ≤ n) (hm : 2 * mC η₀ n ≤ n) :
    ∀ (R : ℕ) (a : EvenRole n),
      ((evenResNear η₀ R a).card : ℝ) ≤ fRes η₀ n R * Fintype.card (EvenRole n) := by
  classical
  intro R a
  let m := mC η₀ n
  let d := dC η₀ n
  have hmn : m ≤ n := by dsimp [m]; omega
  have hdm : d + m = n := by
    dsimp [d, m, dC]
    omega
  let S := evenResNear η₀ R a
  let B := hammingBall (resOf η₀ a.1) R
  let preword : CubeVertex n → CubeVertex m := fun v i => v (Fin.castLE hmn i)
  let encode : {x : EvenRole n // x ∈ S} →
      CubeVertex m × {b : Res η₀ n // b ∈ B} := fun x =>
    (preword x.1.1, ⟨resOf η₀ x.1.1, by
      have hxroot : _root_.hammingDist (resOf η₀ x.1.1) (resOf η₀ a.1) ≤ R := by
        simpa [S, evenResNear] using x.2
      have hx : hammingDist (resOf η₀ x.1.1) (resOf η₀ a.1) ≤ R := by
        simpa [hammingDist, _root_.hammingDist, ne_comm] using hxroot
      have hsym : hammingDist (resOf η₀ a.1) (resOf η₀ x.1.1) =
          hammingDist (resOf η₀ x.1.1) (resOf η₀ a.1) := by
        simp [hammingDist, ne_comm]
      change resOf η₀ x.1.1 ∈ hammingBall (resOf η₀ a.1) R
      unfold hammingBall
      simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      rw [hsym]
      exact hx⟩)
  have hencode : Function.Injective encode := by
    intro x y hxy
    apply Subtype.ext
    apply Subtype.ext
    apply cubeVertex_eq_of_prefix_suffix hmn
    · intro i
      exact congrFun (congrArg Prod.fst hxy) i
    · intro j
      have hres : (resOf η₀ x.1.1) = (resOf η₀ y.1.1) :=
        congrArg (fun z => z.2.1) hxy
      exact congrFun hres j
  have hsource : Fintype.card {x : EvenRole n // x ∈ S} = S.card :=
    Fintype.card_of_subtype S (by intro x; simp)
  have htarget : Fintype.card (CubeVertex m × {b : Res η₀ n // b ∈ B}) =
      2 ^ m * B.card := by
    rw [Fintype.card_prod, Fintype.card_of_subtype B (by intro b; simp)]
    simp
  have hcard : S.card ≤ 2 ^ m * B.card := by
    calc
      S.card = Fintype.card {x : EvenRole n // x ∈ S} := hsource.symm
      _ ≤ Fintype.card (CubeVertex m × {b : Res η₀ n // b ∈ B}) :=
        Fintype.card_le_of_injective encode hencode
      _ = 2 ^ m * B.card := htarget
  have hball := hammingBall_card_le_sum_choose (v := resOf η₀ a.1) (R := R)
  have hcount : (S.card : ℝ) ≤ (2 : ℝ) ^ m * B.card := by
    exact_mod_cast hcard
  have hballReal : (B.card : ℝ) ≤
      ∑ j ∈ Finset.range (R + 1), (Nat.choose d j : ℝ) := by
    exact_mod_cast hball
  have hEven : Fintype.card (EvenRole n) = 2 ^ (n - 1) := by
    have hp := parity_class_card (n := n) (by omega)
    calc
      Fintype.card (EvenRole n) = (evenRoleSet n).card :=
        Fintype.card_of_subtype (evenRoleSet n) (by intro v; simp [evenRoleSet])
      _ = 2 ^ (n - 1) := hp.1
  have hpow : (2 : ℝ) ^ d * (2 : ℝ) ^ m = (2 : ℝ) ^ n := by
    rw [← pow_add, hdm]
  have hpow' : (2 : ℝ) * (2 : ℝ) ^ (n - 1) = (2 : ℝ) ^ n := by
    calc
      (2 : ℝ) * (2 : ℝ) ^ (n - 1) = (2 : ℝ) ^ (n - 1) * 2 := by ring
      _ = (2 : ℝ) ^ n := by
        conv_rhs => rw [show n = (n - 1) + 1 by omega, pow_succ]
  have hfac : (2 : ℝ) * (2 : ℝ) ^ (n - 1) = (2 : ℝ) ^ m * (2 : ℝ) ^ d := by
    calc
      (2 : ℝ) * (2 : ℝ) ^ (n - 1) = (2 : ℝ) ^ n := hpow'
      _ = (2 : ℝ) ^ d * (2 : ℝ) ^ m := hpow.symm
      _ = (2 : ℝ) ^ m * (2 : ℝ) ^ d := by ring
  have hfactor :
      fRes η₀ n R * (Fintype.card (EvenRole n) : ℝ) =
        (2 : ℝ) ^ m * (∑ j ∈ Finset.range (R + 1), (Nat.choose d j : ℝ)) := by
    have hEvenR : (Fintype.card (EvenRole n) : ℝ) = (2 : ℝ) ^ (n - 1) := by
      exact_mod_cast hEven
    rw [hEvenR]
    unfold fRes
    calc
      (2 * (∑ j ∈ Finset.range (R + 1), (Nat.choose (dC η₀ n) j : ℝ)) /
          (2 : ℝ) ^ dC η₀ n) * (2 : ℝ) ^ (n - 1) =
        (∑ j ∈ Finset.range (R + 1), (Nat.choose d j : ℝ)) *
          ((2 : ℝ) * (2 : ℝ) ^ (n - 1) / (2 : ℝ) ^ d) := by
            dsimp [d]
            ring
      _ = (∑ j ∈ Finset.range (R + 1), (Nat.choose d j : ℝ)) *
          ((2 : ℝ) ^ m * (2 : ℝ) ^ d / (2 : ℝ) ^ d) := by rw [hfac]
      _ = (2 : ℝ) ^ m * (∑ j ∈ Finset.range (R + 1), (Nat.choose d j : ℝ)) := by
            have hden : (2 : ℝ) ^ d ≠ 0 := by positivity
            field_simp [hden]
  calc
    (S.card : ℝ) ≤ (2 : ℝ) ^ m * B.card := hcount
    _ ≤ (2 : ℝ) ^ m *
        (∑ j ∈ Finset.range (R + 1), (Nat.choose d j : ℝ)) :=
      mul_le_mul_of_nonneg_left hballReal (by positivity)
    _ = fRes η₀ n R * Fintype.card (EvenRole n) := hfactor.symm

/-- L8.1a(v) (08:357–363): the residual-near fraction at radius `2r + 8H + 4` is exponentially small, since
`r = .01n + O(1)`, `H = o(n)` and the binomial entropy at `.0201` is below `log 2` (`binomialEntropyBound`). -/
theorem res_near_small (η₀ : ℝ) (hη₀ : 0 < η₀) :
    ∃ c > (0 : ℝ), ∃ n₀ : ℕ, ∀ n ≥ n₀,
      fRes η₀ n (2 * rH n + 8 * HH η₀ n + 4) ≤ Real.exp (-c * n) := by
  have hτpos : 0 < tau8 η₀ := by
    unfold tau8
    apply div_pos
    · exact lt_min (by linarith) (by norm_num)
    · norm_num
  have hτle : tau8 η₀ ≤ (1 : ℝ) / 100 := by
    unfold tau8
    calc
      min (η₀ / 2) (4 / 100) / 4 ≤ (4 / 100 : ℝ) / 4 :=
        div_le_div_of_nonneg_right (min_le_right _ _) (by norm_num)
      _ = 1 / 100 := by norm_num
  have hσpos : 0 < sigmaH η₀ := by
    unfold sigmaH b0H bH
    positivity
  have hζeq : zetaH η₀ = 2 * sigmaH η₀ := by
    unfold zetaH sigmaH
    ring
  have hζlt : zetaH η₀ < 1 := by
    unfold zetaH b0H bH
    nlinarith [hτle]
  let σ := sigmaH η₀
  let ζ := zetaH η₀
  let α := (1 - ζ) / 4
  have hαpos : 0 < α := by dsimp [α, ζ]; linarith
  have hσeq : ζ = 2 * σ := by simpa [ζ, σ] using hζeq
  have hpowNeg : Filter.Tendsto (fun n : ℕ => (n : ℝ) ^ (-σ))
      Filter.atTop (nhds 0) := by
    have h := (tendsto_rpow_neg_atTop hσpos).comp tendsto_natCast_atTop_atTop
    simpa [Function.comp_def, σ] using h
  have hpowSmall : ∀ᶠ n : ℕ in Filter.atTop, (n : ℝ) ^ (-σ) < 1 / 4000 := by
    filter_upwards [Metric.tendsto_nhds.1 hpowNeg (1 / 4000 : ℝ) (by norm_num)] with n hn
    have hn' : |(n : ℝ) ^ (-σ)| < 1 / 4000 := by
      simpa [Real.dist_eq] using hn
    exact (abs_lt.mp hn').2
  have hpowGrow : Filter.Tendsto (fun n : ℕ => (n : ℝ) ^ α)
      Filter.atTop Filter.atTop :=
    (_root_.tendsto_rpow_atTop hαpos).comp tendsto_natCast_atTop_atTop
  have hpowLarge : ∀ᶠ n : ℕ in Filter.atTop, 1 / α ≤ (n : ℝ) ^ α :=
    hpowGrow.eventually (Filter.eventually_ge_atTop (1 / α))
  have hnLarge : ∀ᶠ n : ℕ in Filter.atTop, 2 ≤ n :=
    Filter.eventually_atTop.2 ⟨2, fun _ hn => hn⟩
  have hbaseScale : ∀ᶠ n : ℕ in Filter.atTop,
      max 1 ⌈Real.log (n : ℝ) ^ 2⌉₊ ≤ ⌈(n : ℝ) ^ (1 - ζ)⌉₊ := by
    filter_upwards [hnLarge, hpowLarge] with n hn2 hlarge
    have hnR : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast (by omega : 1 ≤ n)
    have hnPos : 0 < (n : ℝ) := lt_of_lt_of_le zero_lt_one hnR
    have hlog : Real.log (n : ℝ) ≤ (n : ℝ) ^ α / α :=
      Real.log_natCast_le_rpow_div n hαpos
    have hlog0 : 0 ≤ Real.log (n : ℝ) := Real.log_nonneg hnR
    have hpow0 : 0 ≤ (n : ℝ) ^ α := Real.rpow_nonneg (by positivity) _
    have hlogBound : Real.log (n : ℝ) ≤ (n : ℝ) ^ (2 * α) := by
      calc
        Real.log (n : ℝ) ≤ (n : ℝ) ^ α / α := hlog
        _ = (n : ℝ) ^ α * (1 / α) := by ring
        _ ≤ (n : ℝ) ^ α * (n : ℝ) ^ α :=
          mul_le_mul_of_nonneg_left hlarge hpow0
        _ = (n : ℝ) ^ (2 * α) := by
          rw [← Real.rpow_add hnPos]
          congr 1 <;> ring
    have hlogSq : (Real.log (n : ℝ)) ^ 2 ≤ (n : ℝ) ^ (1 - ζ) := by
      have hsq : (Real.log (n : ℝ)) ^ 2 ≤ ((n : ℝ) ^ (2 * α)) ^ 2 :=
        (sq_le_sq₀ hlog0 (Real.rpow_nonneg (by positivity) _)).2 hlogBound
      calc
        (Real.log (n : ℝ)) ^ 2 ≤ ((n : ℝ) ^ (2 * α)) ^ 2 := hsq
        _ = (n : ℝ) ^ (2 * α) * (n : ℝ) ^ (2 * α) := by rw [pow_two]
        _ = (n : ℝ) ^ (1 - ζ) := by
          rw [← Real.rpow_add hnPos]
          congr 1
          dsimp [α]
          ring
    have hceilLog : ⌈Real.log (n : ℝ) ^ 2⌉₊ ≤ ⌈(n : ℝ) ^ (1 - ζ)⌉₊ :=
      Nat.ceil_le_ceil hlogSq
    have hpowOne : (1 : ℝ) ≤ (n : ℝ) ^ (1 - ζ) :=
      Real.one_le_rpow hnR (by linarith [hζlt])
    have hceilOneR : (1 : ℝ) ≤ (⌈(n : ℝ) ^ (1 - ζ)⌉₊ : ℝ) :=
      le_trans hpowOne (Nat.le_ceil _)
    have hceilOne : 1 ≤ ⌈(n : ℝ) ^ (1 - ζ)⌉₊ := by exact_mod_cast hceilOneR
    exact max_le hceilOne hceilLog
  have hHHsmall : ∀ᶠ n : ℕ in Filter.atTop,
      (HH η₀ n : ℝ) ≤ (n : ℝ) / 1000 := by
    filter_upwards [hnLarge, hpowSmall, hbaseScale] with n hn2 hsmall hbase
    have hnR : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast (by omega : 1 ≤ n)
    have hnPos : 0 < (n : ℝ) := lt_of_lt_of_le zero_lt_one hnR
    have hσpow : 1 ≤ (n : ℝ) ^ σ := Real.one_le_rpow hnR (by dsimp [σ]; exact hσpos.le)
    have hζpow : 1 ≤ (n : ℝ) ^ (1 - ζ) :=
      Real.one_le_rpow hnR (by dsimp [ζ]; linarith [hζlt])
    have hceilσ : (⌈(n : ℝ) ^ σ⌉₊ : ℝ) < (n : ℝ) ^ σ + 1 :=
      Nat.ceil_lt_add_one (Real.rpow_nonneg (by positivity) _)
    have hceilζ : (⌈(n : ℝ) ^ (1 - ζ)⌉₊ : ℝ) < (n : ℝ) ^ (1 - ζ) + 1 :=
      Nat.ceil_lt_add_one (Real.rpow_nonneg (by positivity) _)
    have hM : max (2 : ℝ) (⌈(n : ℝ) ^ σ⌉₊ : ℝ) ≤ 2 * (n : ℝ) ^ σ := by
      apply max_le
      · nlinarith [hσpow]
      · linarith [hceilσ, hσpow]
    have hTarget : (⌈(n : ℝ) ^ (1 - ζ)⌉₊ : ℝ) ≤ 2 * (n : ℝ) ^ (1 - ζ) := by
      linarith [hceilζ, hζpow]
    have hscaleNat := topScale_le_mul_target n σ ζ hbase
    have hscale : (HH η₀ n : ℝ) ≤
        max (2 : ℝ) (⌈(n : ℝ) ^ σ⌉₊ : ℝ) * (⌈(n : ℝ) ^ (1 - ζ)⌉₊ : ℝ) := by
      exact_mod_cast hscaleNat
    have hscalePow : (HH η₀ n : ℝ) ≤ 4 * (n : ℝ) ^ (1 - σ) := by
      calc
        (HH η₀ n : ℝ) ≤
            (max 2 ⌈(n : ℝ) ^ σ⌉₊ : ℝ) * (⌈(n : ℝ) ^ (1 - ζ)⌉₊ : ℝ) := hscale
        _ ≤ (2 * (n : ℝ) ^ σ) * (2 * (n : ℝ) ^ (1 - ζ)) :=
          mul_le_mul hM hTarget (by positivity) (by positivity)
        _ = 4 * ((n : ℝ) ^ σ * (n : ℝ) ^ (1 - ζ)) := by ring
        _ = 4 * (n : ℝ) ^ (1 - σ) := by
          rw [← Real.rpow_add hnPos]
          congr 1
          rw [hσeq]
          ring
    have hpowSplit : (n : ℝ) ^ (1 - σ) = (n : ℝ) * (n : ℝ) ^ (-σ) := by
      have hexp : 1 - σ = 1 + (-σ) := by ring
      rw [hexp, Real.rpow_add hnPos]
      norm_num
    calc
      (HH η₀ n : ℝ) ≤ 4 * (n : ℝ) ^ (1 - σ) := hscalePow
      _ = 4 * (n : ℝ) * (n : ℝ) ^ (-σ) := by rw [hpowSplit]; ring
      _ ≤ 4 * (n : ℝ) * (1 / 4000) :=
        mul_le_mul_of_nonneg_left hsmall.le (by positivity)
      _ = (n : ℝ) / 1000 := by ring
  obtain ⟨nH, hH⟩ := Filter.eventually_atTop.1 hHHsmall
  obtain ⟨nGrid, hGrid⟩ := grid_basic η₀ hη₀
  let n₀ := max nH (max nGrid 4000)
  refine ⟨1 / 80, by norm_num, n₀, ?_⟩
  intro n hn
  change max nH (max nGrid 4000) ≤ n at hn
  have hnH : nH ≤ n := le_trans (le_max_left _ _) hn
  have hnInner : max nGrid 4000 ≤ n := le_trans (le_max_right _ _) hn
  have hnGrid : nGrid ≤ n := le_trans (le_max_left _ _) hnInner
  have hn4000 : 4000 ≤ n := le_trans (le_max_right _ _) hnInner
  have hbasic := hGrid n hnGrid
  rcases hbasic with ⟨_, hsplit, _, _⟩
  have hdimNat : n ≤ 2 * dC η₀ n := by
    dsimp [dC]
    omega
  have hdimCast : (n : ℝ) ≤ 2 * (dC η₀ n : ℝ) := by exact_mod_cast hdimNat
  have hdim : (n : ℝ) / 2 ≤ (dC η₀ n : ℝ) := by linarith
  have hrUpper : (rH n : ℝ) ≤ (n : ℝ) / 100 := by
    dsimp [rH]
    exact Nat.floor_le (by positivity)
  have hRadius :
      (2 * rH n + 8 * HH η₀ n + 4 : ℕ) ≤ (dC η₀ n : ℝ) / 4 := by
    push_cast
    have hnCast : (4000 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn4000
    nlinarith [hrUpper, hH n hnH, hdim]
  let R := 2 * rH n + 8 * HH η₀ n + 4
  have hsum := Lane_q_s08_grid.choose_range_entropy_quarter
    (d := dC η₀ n) (R := R) (by simpa [R] using hRadius)
  have hgap := Lane_q_s08_grid.binEntropy_quarter_gap
  have hpowExp (k : ℕ) : (2 : ℝ) ^ k = Real.exp (Real.log 2 * (k : ℝ)) := by
    induction k with
    | zero => simp
    | succ k ih =>
      calc
        (2 : ℝ) ^ (k + 1) = (2 : ℝ) ^ k * 2 := by rw [pow_succ]
        _ = Real.exp (Real.log 2 * (k : ℝ)) * Real.exp (Real.log 2) := by
          rw [ih, Real.exp_log (by norm_num : (0 : ℝ) < 2)]
        _ = Real.exp (Real.log 2 * (k : ℝ) + Real.log 2) := by
          rw [← Real.exp_add]
        _ = Real.exp (Real.log 2 * ((k + 1 : ℕ) : ℝ)) := by
          congr 1
          push_cast
          ring
  have hden : (2 : ℝ) ^ dC η₀ n = Real.exp (Real.log 2 * (dC η₀ n : ℝ)) :=
    hpowExp (dC η₀ n)
  have hfrac : fRes η₀ n R ≤ 2 * Real.exp (-((dC η₀ n : ℝ) / 20)) := by
    unfold fRes
    rw [hden]
    have hnum : 2 * (∑ j ∈ Finset.range (R + 1),
        (Nat.choose (dC η₀ n) j : ℝ)) ≤
          2 * Real.exp (Real.binEntropy (1 / 4 : ℝ) * (dC η₀ n : ℝ)) :=
      mul_le_mul_of_nonneg_left hsum (by norm_num)
    calc
      2 * (∑ j ∈ Finset.range (R + 1),
          (Nat.choose (dC η₀ n) j : ℝ)) /
          Real.exp (Real.log 2 * (dC η₀ n : ℝ)) ≤
        2 * Real.exp (Real.binEntropy (1 / 4 : ℝ) * (dC η₀ n : ℝ)) /
          Real.exp (Real.log 2 * (dC η₀ n : ℝ)) :=
            div_le_div_of_nonneg_right hnum (by positivity)
      _ = 2 * Real.exp
          ((Real.binEntropy (1 / 4 : ℝ) - Real.log 2) * (dC η₀ n : ℝ)) := by
        have hfactor :
            2 * (Real.exp (Real.binEntropy (1 / 4 : ℝ) * (dC η₀ n : ℝ)) /
              Real.exp (Real.log 2 * (dC η₀ n : ℝ))) =
            2 * Real.exp (Real.binEntropy (1 / 4 : ℝ) * (dC η₀ n : ℝ)) /
              Real.exp (Real.log 2 * (dC η₀ n : ℝ)) := by ring
        rw [← hfactor, ← Real.exp_sub]
        congr 1
        ring
      _ ≤ 2 * Real.exp (-((dC η₀ n : ℝ) / 20)) := by
        apply mul_le_mul_of_nonneg_left _ (by norm_num)
        apply Real.exp_le_exp.mpr
        have hdnonneg : 0 ≤ (dC η₀ n : ℝ) := by positivity
        nlinarith [mul_le_mul_of_nonneg_right hgap hdnonneg]
  have hlog2le : Real.log 2 ≤ 1 := by
    have h := Real.log_two_lt_d9
    linarith
  have hn80 : (80 : ℝ) ≤ (n : ℝ) := by exact_mod_cast (show 80 ≤ n by omega)
  have harg : Real.log 2 - (dC η₀ n : ℝ) / 20 ≤ -(n : ℝ) / 80 := by
    nlinarith [hdim, hlog2le, hn80]
  have hfinal : fRes η₀ n R ≤ Real.exp (-(n : ℝ) / 80) := by
    calc
      fRes η₀ n R ≤ 2 * Real.exp (-((dC η₀ n : ℝ) / 20)) := hfrac
      _ = Real.exp (Real.log 2) * Real.exp (-((dC η₀ n : ℝ) / 20)) := by
        rw [Real.exp_log (by norm_num : (0 : ℝ) < 2)]
      _ = Real.exp (Real.log 2 - (dC η₀ n : ℝ) / 20) := by
        rw [← Real.exp_add]
        congr 1
      _ ≤ Real.exp (-(n : ℝ) / 80) := Real.exp_le_exp.mpr harg
  have hfinalExp : -(n : ℝ) / 80 = -(1 / 80 : ℝ) * n := by ring
  simpa only [R, hfinalExp] using hfinal

/-- The parity classes of `Q_n`, `n ≥ 1`, have `2^{n-1}` vertices each (`parity_class_card`). -/
theorem role_card (n : ℕ) (hn : 1 ≤ n) :
    Fintype.card (EvenRole n) = 2 ^ (n - 1) ∧ Fintype.card (OddRole n) = 2 ^ (n - 1) := by
  classical
  have hp := parity_class_card (n := n) (by omega)
  have he : Fintype.card (EvenRole n) = (evenRoleSet n).card := by
    exact Fintype.card_of_subtype (evenRoleSet n) (by intro v; simp [evenRoleSet])
  have ho : Fintype.card (OddRole n) = (Finset.univ \ evenRoleSet n).card := by
    exact Fintype.card_of_subtype (Finset.univ \ evenRoleSet n) (by intro v; simp [evenRoleSet])
  exact ⟨he.trans hp.1, ho.trans hp.2⟩

/-- L8.1a assembled (08:15–21, 345–347, 356–361): all geometric facts hold for large `n`. -/
theorem grid_facts (η₀ : ℝ) (hη₀ : 0 < η₀) : ∃ n₀ : ℕ, ∀ n ≥ n₀, GridFacts η₀ n := by
  obtain ⟨n₁, hbasic⟩ := grid_basic η₀ hη₀
  obtain ⟨n₂, hnear⟩ := grid_near η₀ hη₀
  refine ⟨max n₁ n₂, fun n hn => ?_⟩
  obtain ⟨hpos, hsplit, hok, hcross⟩ := hbasic n (le_trans (le_max_left _ _) hn)
  obtain ⟨hne, hno⟩ := hnear n (le_trans (le_max_right _ _) hn)
  have hmn : mC η₀ n ≤ n := by omega
  exact ⟨hpos, hsplit, hok, hcross, grid_edge_cover η₀ n hmn, (role_card n hpos.1).1,
    (role_card n hpos.1).2, hne, hno, res_near_count η₀ n hpos.1 hsplit⟩

end HypercubeRamsey.S08
