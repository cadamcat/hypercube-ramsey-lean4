import HypercubeRamsey.Framework.Props
import HypercubeRamsey.Framework.Embedding
import HypercubeRamsey.Tools.CubeGeometry
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
  sorry

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
  sorry

/-- L8.1a(ii) (08:21): the ordinary and cross lists contain every cube edge.  Flipping a residual bit changes only
the residual word, by one; flipping a bit of chunk `r` changes only its count, by one. -/
theorem grid_edge_cover (η₀ : ℝ) (n : ℕ) (hm : mC η₀ n ≤ n) :
    ∀ v w : CubeVertex n, (cube n).Adj v w → PadNbr (cellOf η₀ v) (cellOf η₀ w) := by
  sorry

/-- L8.1a(iii) (08:345–347, 08:415–419): for large `n`, the roles of either parity whose grid key is within
distance eight of a given one form a fraction at most `f_grid`.  At most `(2s+1)^8` keys are that near, each key
is read by at most `2^n max_k C(ℓ,k)^s / 2^{ℓ s}` vertices, and a Binomial(ℓ,1/2) atom is at most `2n^{-.04}`. -/
theorem grid_near (η₀ : ℝ) (hη₀ : 0 < η₀) :
    ∃ n₀ : ℕ, ∀ n ≥ n₀,
      (∀ a : EvenRole n, ((evenKeyNear η₀ 8 a).card : ℝ) ≤ fGrid η₀ n * Fintype.card (EvenRole n)) ∧
      (∀ u : OddRole n, ((oddKeyNear η₀ 8 u).card : ℝ) ≤ fGrid η₀ n * Fintype.card (OddRole n)) := by
  sorry

/-- L8.1a(iv) (08:358–360): the even roles with residual word within distance `R` of a given one are at most
`2^m Σ_{j ≤ R} C(n-m, j) = f_res(R) |A|` (exact count once `m < n`, `|A| = 2^{n-1}`). -/
theorem res_near_count (η₀ : ℝ) (n : ℕ) (hn : 1 ≤ n) (hm : 2 * mC η₀ n ≤ n) :
    ∀ (R : ℕ) (a : EvenRole n),
      ((evenResNear η₀ R a).card : ℝ) ≤ fRes η₀ n R * Fintype.card (EvenRole n) := by
  sorry

/-- L8.1a(v) (08:357–363): the residual-near fraction at radius `2r + 8H + 4` is exponentially small, since
`r = .01n + O(1)`, `H = o(n)` and the binomial entropy at `.0201` is below `log 2` (`binomialEntropyBound`). -/
theorem res_near_small (η₀ : ℝ) (hη₀ : 0 < η₀) :
    ∃ c > (0 : ℝ), ∃ n₀ : ℕ, ∀ n ≥ n₀,
      fRes η₀ n (2 * rH n + 8 * HH η₀ n + 4) ≤ Real.exp (-c * n) := by
  sorry

/-- The parity classes of `Q_n`, `n ≥ 1`, have `2^{n-1}` vertices each (`parity_class_card`). -/
theorem role_card (n : ℕ) (hn : 1 ≤ n) :
    Fintype.card (EvenRole n) = 2 ^ (n - 1) ∧ Fintype.card (OddRole n) = 2 ^ (n - 1) := by
  sorry

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
