import HypercubeRamsey.Framework.Embedding
import HypercubeRamsey.Tools.CubeGeometry
import HypercubeRamsey.Tools.Binomial

/-!
# L7.1a: grid geometry

Source: `sections/07-…tex`, lines 55–68 and 77–82.  The geometry records disjoint special chunks, auxiliary
coordinates, a residual coordinate, and monotone binning maps whose binomial masses are small.  A cube vertex
reads the cell `(g, t)`: `g` is the vector of bin indices of its chunk counts (the grid key), `t` its bits on
the auxiliary coordinates (the auxiliary word).

Grid distance is the number of one-bin moves (`keyDist`), auxiliary distance is Hamming distance (`auxDist`);
their sum is the distance in the grid-times-auxiliary graph used by the local lemma (07:250–253).  The cross
names of a cell `(g, t)` are `(h, t)` for the keys `h` at grid distance one; its own names are `(g, t')` for
the words `t'` at auxiliary distance at most one (07:73–82).
-/

namespace HypercubeRamsey.S07

open OAI.HypercubeRamsey

/-- A grid partition of cube coordinates with small binomial mass in every bin. -/
structure GridGeom (d : ℝ) (n s ℓ q : ℕ) where
  chunk : Fin s → Finset (Fin n)
  aux : Finset (Fin n)
  chunk_card : ∀ r, (chunk r).card = ℓ
  chunks_disjoint : Pairwise fun r r' => Disjoint (chunk r) (chunk r')
  aux_card : aux.card = q
  aux_disjoint : ∀ r, Disjoint aux (chunk r)
  residual_nonempty : ∃ j : Fin n, j ∉ aux ∧ ∀ r, j ∉ chunk r
  bins : Fin s → ℕ
  bin : ∀ r, Fin (ℓ + 1) → Fin (bins r)
  bin_monotone : ∀ r k k', k.val ≤ k'.val → (bin r k).val ≤ (bin r k').val
  bin_surjective : ∀ r, Function.Surjective (bin r)
  bin_mass : ∀ r b,
    (∑ k : Fin (ℓ + 1),
      if bin r k = b then ((Nat.choose ℓ k.val : ℕ) : ℝ) / (2 : ℝ) ^ ℓ else 0) ≤
        2 * (n : ℝ) ^ (-(d / 4))

/-- A key is one bin index for each special chunk. -/
abbrev GridGeom.Key {d : ℝ} {n s ℓ q : ℕ} (Γ : GridGeom d n s ℓ q) :=
  ∀ r, Fin (Γ.bins r)

/-- An auxiliary word records the bits on the auxiliary coordinate set. -/
abbrev GridGeom.AuxWord {d : ℝ} {n s ℓ q : ℕ} (Γ : GridGeom d n s ℓ q) :=
  Γ.aux → Bool

/-- A grid cell pairs a key with an auxiliary word. -/
abbrev GridGeom.Cell {d : ℝ} {n s ℓ q : ℕ} (Γ : GridGeom d n s ℓ q) :=
  GridGeom.Key Γ × GridGeom.AuxWord Γ

/-- The grid key read by a cube vertex: one bin index per special chunk and the auxiliary bits. -/
noncomputable def GridGeom.key {d : ℝ} {n s ℓ q : ℕ} (Γ : GridGeom d n s ℓ q)
    (v : CubeVertex n) : (∀ r, Fin (Γ.bins r)) × (Γ.aux → Bool) := by
  classical
  let b : ∀ r, Fin (ℓ + 1) := fun r =>
    ⟨((Γ.chunk r).filter (fun j => v j = true)).card,
      Nat.lt_succ_of_le (by
        calc
          ((Γ.chunk r).filter (fun j => v j = true)).card ≤ (Γ.chunk r).card :=
            Finset.card_filter_le _ _
          _ = ℓ := Γ.chunk_card r)⟩
  exact (fun r => Γ.bin r (b r), fun j => v j)

/-- The number of special chunks, `s = ⌈n^d⌉` (07:55). -/
noncomputable def gS (d : ℝ) (n : ℕ) : ℕ := Nat.ceil ((n : ℝ) ^ d)

/-- The chunk length, `⌊n^d⌋` (07:56). -/
noncomputable def gL (d : ℝ) (n : ℕ) : ℕ := ⌊(n : ℝ) ^ d⌋₊

/-- The number of auxiliary bits, `q = ⌈n^{4d}⌉` (07:57). -/
noncomputable def gQ (d : ℝ) (n : ℕ) : ℕ := Nat.ceil ((n : ℝ) ^ (4 * d))

/-- The Section 7 geometry at dimension `n`. -/
abbrev Geom (d : ℝ) (n : ℕ) := GridGeom d n (gS d n) (gL d n) (gQ d n)

/-- L7.1a (07:55–68): for large `n` the prescribed chunks, auxiliary bits, residual coordinate and bins exist.
The bound `d < 1/8` (the paper has `d < D₀/1000 < 10⁻⁴`) makes `sℓ + q + 1 ≤ n` for large `n`; each bin has
`Binomial(ℓ, 1/2)`-mass at most `2n^{-d/4}` because every atom is `O(n^{-d/2})`. -/
theorem gridGeom_exists (d : ℝ) (hd : 0 < d) (hd' : d < 1 / 8) :
    ∃ n₀ : ℕ, ∀ n ≥ n₀, Nonempty (Geom d n) := by
  sorry

namespace GridGeom

variable {d : ℝ} {n s ℓ q : ℕ} (Γ : GridGeom d n s ℓ q)

/-- Grid distance: the number of one-bin moves between two keys. -/
def keyDist (g h : Γ.Key) : ℕ := ∑ r, Nat.dist (g r : ℕ) (h r : ℕ)

/-- Auxiliary distance: Hamming distance of auxiliary words. -/
def auxDist (t t' : Γ.AuxWord) : ℕ := (Finset.univ.filter fun j => t j ≠ t' j).card

/-- Distance in the grid-times-auxiliary graph (07:250–253). -/
def cellDist (c c' : Γ.Cell) : ℕ := Γ.keyDist c.1 c'.1 + Γ.auxDist c.2 c'.2

/-- Keys within grid distance `R`. -/
def keyBall (g : Γ.Key) (R : ℕ) : Finset Γ.Key := Finset.univ.filter fun h => Γ.keyDist g h ≤ R

/-- Auxiliary words within auxiliary distance `R`. -/
def auxBall (t : Γ.AuxWord) (R : ℕ) : Finset Γ.AuxWord :=
  Finset.univ.filter fun t' => Γ.auxDist t t' ≤ R

/-- Cells within distance `R`. -/
def cellBall (c : Γ.Cell) (R : ℕ) : Finset Γ.Cell := Finset.univ.filter fun c' => Γ.cellDist c c' ≤ R

/-- `E(g)`: the keys obtained by one bin move in one coordinate (07:61–63). -/
def keyNbrs (g : Γ.Key) : Finset Γ.Key := Finset.univ.filter fun h => Γ.keyDist g h = 1

/-- The fixed order of the cross keys of `g`; it does not depend on the auxiliary word (07:85–86). -/
noncomputable def crossKeys (g : Γ.Key) : List Γ.Key := (Γ.keyNbrs g).toList

/-- The cross order with the key `h₀` last (07:85–87). -/
noncomputable def crossOrder (g h₀ : Γ.Key) : List Γ.Key := (Γ.crossKeys g).erase h₀ ++ [h₀]

/-- The auxiliary words at distance at most one, in a fixed order. -/
noncomputable def ownWords (t : Γ.AuxWord) : List Γ.AuxWord := (Γ.auxBall t 1).toList

/-- Cross names `W_{h,t}`, `h ∈ E(g)` (07:76). -/
noncomputable def crossNames (g : Γ.Key) (t : Γ.AuxWord) : List Γ.Cell :=
  (Γ.crossKeys g).map fun h => (h, t)

/-- Own names `W_{g,t'}`, `d_H(t,t') ≤ 1` (07:77). -/
noncomputable def ownNames (g : Γ.Key) (t : Γ.AuxWord) : List Γ.Cell :=
  (Γ.ownWords t).map fun t' => (g, t')

/-- All listed names of the odd cell `c`: the cross list followed by the own list. -/
noncomputable def fullNames (c : Γ.Cell) : List Γ.Cell := Γ.crossNames c.1 c.2 ++ Γ.ownNames c.1 c.2

/-- The `Binomial(ℓ, 1/2)` mass of bin `b` in chunk `r`. -/
noncomputable def binMass (r : Fin s) (b : Fin (Γ.bins r)) : ℝ :=
  ∑ k : Fin (ℓ + 1), if Γ.bin r k = b then ((Nat.choose ℓ k.val : ℕ) : ℝ) / (2 : ℝ) ^ ℓ else 0

/-- The product mass of a key: the fraction of chunk patterns reading it (07:65–66). -/
noncomputable def keyMass (g : Γ.Key) : ℝ := ∏ r, Γ.binMass r (g r)

end GridGeom

end HypercubeRamsey.S07
