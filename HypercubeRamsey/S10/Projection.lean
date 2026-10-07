import Mathlib

/-!
# Section 10.1a: the reusable Hamming syndrome projection

The construction is stated for any finite elementary abelian 2-group.  This is the
coordinate group of a binary chunk; taking a product over chunks gives the residual
projection used in Section 10 and the same algebraic statement is available to Part C.
-/

namespace HypercubeRamsey.S10

open scoped BigOperators

/-- The syndrome of a binary word indexed by a finite elementary abelian 2-group. -/
def chunkSyndrome {G : Type*} [Fintype G] [AddCommGroup G] (s : G → Bool) : G :=
  ∑ g : G, if s g then g else 0

/-- Flip one indexed bit. -/
def flipChunkBit {G : Type*} [DecidableEq G] (s : G → Bool) (g : G) : G → Bool :=
  fun i => if i = g then !s i else s i

/-- Correct a word by flipping the bit named by its syndrome. -/
def chunkProject {G : Type*} [Fintype G] [DecidableEq G] [AddCommGroup G]
    (s : G → Bool) : G → Bool :=
  flipChunkBit s (chunkSyndrome s)

/-- Hamming distance between two words on one chunk. -/
def chunkHammingDistance {G : Type*} [Fintype G] [DecidableEq G]
    (s t : G → Bool) : ℕ :=
  (Finset.univ.filter fun g => s g ≠ t g).card

/-- P10.1a's generic one-chunk theorem. -/
def P10_1aProjectionStatement : Prop :=
  ∀ {G : Type} [Fintype G] [DecidableEq G] [AddCommGroup G]
    (h₂ : ∀ g : G, g + g = 0),
    (∀ s : G → Bool, chunkSyndrome (chunkProject s) = 0 ∧
      chunkHammingDistance s (chunkProject s) = 1) ∧
    (∀ t : G → Bool, chunkSyndrome t = 0 →
      (Finset.univ.filter fun s : G → Bool => chunkProject s = t).card = Fintype.card G)

/-- P10.1a (10:30–41): syndrome correction lands in the zero-syndrome class, flips
exactly one coordinate, and every zero-syndrome word has exactly one preimage per
coordinate. The statement is uniform in the finite binary coordinate group. -/
theorem p10_1a_hamming_projection : P10_1aProjectionStatement := by
  intro G hF hD hA h₂
  sorry

/-- Project the ordinary neighbor obtained by flipping coordinate `l`. -/
def projectedNeighbor {G : Type*} [Fintype G] [DecidableEq G] [AddCommGroup G]
    (s : G → Bool) (l : G) : G → Bool :=
  chunkProject (flipChunkBit s l)

/-- Coordinates whose ordinary neighbors project to the same site. -/
noncomputable def projectedNeighborFiber {G : Type*} [Fintype G] [DecidableEq G]
    [AddCommGroup G] (s t : G → Bool) : Finset G := by
  classical
  exact Finset.univ.filter fun l => projectedNeighbor s l = t

/-- Number of ordinary incidences in a projected-neighbor group. -/
noncomputable def projectedNeighborMultiplicity {G : Type*} [Fintype G] [DecidableEq G]
    [AddCommGroup G] (s t : G → Bool) : ℕ :=
  (projectedNeighborFiber s t).card

/-- P10.1a neighbor multiplicities: if the center syndrome is zero, all ordinary
neighbors project to one group; otherwise every nonempty group has multiplicity two. -/
theorem p10_1a_neighbour_multiplicities {G : Type*} [Fintype G] [DecidableEq G]
    [AddCommGroup G] (h₂ : ∀ g : G, g + g = 0) (s t : G → Bool) :
    projectedNeighborMultiplicity s t = 0 ∨
      (chunkSyndrome s = 0 ∧ projectedNeighborMultiplicity s t = Fintype.card G) ∨
      (chunkSyndrome s ≠ 0 ∧ projectedNeighborMultiplicity s t = 2) := by
  sorry

/-- A single chunk fiber has diameter at most two: each source differs from its
projected word in one coordinate. -/
theorem p10_1a_chunk_fiber_diameter {G : Type*} [Fintype G] [DecidableEq G]
    [AddCommGroup G] (h₂ : ∀ g : G, g + g = 0) (s t : G → Bool)
    (hproj : chunkProject s = chunkProject t) :
    chunkHammingDistance s t ≤ 2 := by
  sorry

variable {C : Type*} [Fintype C] [DecidableEq C]
variable {G : C → Type*} [∀ c, Fintype (G c)] [∀ c, DecidableEq (G c)]
  [∀ c, AddCommGroup (G c)]

/-- Apply the one-chunk projection independently in every chunk. -/
def productProject (s : ∀ c, G c → Bool) : ∀ c, G c → Bool :=
  fun c => chunkProject (s c)

/-- Total number of set bits across a chunked word. -/
def productTrueCount (s : ∀ c, G c → Bool) : ℕ :=
  ∑ c : C, (Finset.univ.filter fun g : G c => s c g).card

/-- Total Hamming distance across a chunked word. -/
def productHammingDistance (s t : ∀ c, G c → Bool) : ℕ :=
  ∑ c : C, chunkHammingDistance (s c) (t c)

/-- P10.1a, product parity clause: one bit is corrected in each chunk, so parity
changes exactly when the number of chunks is odd. -/
theorem p10_1a_product_parity
    (h₂ : ∀ c (g : G c), g + g = 0) (s : ∀ c, G c → Bool) :
    (Even (Fintype.card C) →
      (Even (productTrueCount s) ↔ Even (productTrueCount (productProject s)))) ∧
    (Odd (Fintype.card C) →
      (Even (productTrueCount s) ↔ ¬ Even (productTrueCount (productProject s)))) := by
  sorry

/-- The product projection flips exactly one bit per chunk. This cardinality form
is useful when a later argument only needs the total Hamming displacement. -/
theorem p10_1a_product_distance
    (h₂ : ∀ c (g : G c), g + g = 0) (s : ∀ c, G c → Bool) :
    productHammingDistance s (productProject s) = Fintype.card C := by
  sorry

/-- Product fibers have diameter at most two coordinates per chunk. -/
theorem p10_1a_product_fiber_diameter
    (h₂ : ∀ c (g : G c), g + g = 0) (s t : ∀ c, G c → Bool)
    (hproj : productProject s = productProject t) :
    productHammingDistance s t ≤ 2 * Fintype.card C := by
  sorry

end HypercubeRamsey.S10
