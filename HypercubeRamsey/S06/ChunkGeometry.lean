import HypercubeRamsey.S06.Defs

/-!
# Section 6 coarse and fine chunk geometry

L6.1b (06:67–92, with 05:81–109).  A chunk layout fixes the `300` coarse chunks of length `⌊n^{1/5}⌋`, the
`m = ⌈n^α⌉` fine chunks of a common odd length `~ n^{.3}`, the nonempty residual set, and consecutive bins of
binomial probability `≤ 2n^{-.04}` with few endpoints.  Keys, signs, flippable sets and severities are
defined from the layout; `ChunkGeometry6` adds the probabilistic and flip facts.

Repair note.  The frozen `L6_1b` claimed a geometry with `m ≥ n^α` and at most `n^{1/2}` occupied coordinates
for every `α > 0`; it was refuted at `α = 1/2` (`runs/lanes/p-s06-b/REPORT.md`).  The paper takes `α` small
(06:163); `Pr(j ≥ q) ≤ n^{-.13q}` needs `α < .02` (union over `q`-subsets of chunks, atom `O(n^{-.15})`).  The
statement now assumes `α ≤ 1/100`.  The old record also allowed singleton bins (every role boundary) and bin
jumps of more than one; the layout now requires consecutive bins and at most `n^{.04} + 1` of them.
-/

namespace HypercubeRamsey
namespace S06

open OAI.HypercubeRamsey
open Classical
open scoped BigOperators

noncomputable section

/-- `d_c = 300` coarse chunks (06:68). -/
def coarseChunkCount : ℕ := 300

/-- A coarse bin vector `w`. -/
abbrev BinVector6 (n : ℕ) := Fin coarseChunkCount → Fin (n + 1)

/-- Flip one coordinate. -/
def flipVertex6 {n : ℕ} (x : CubeVertex n) (a : Fin n) : CubeVertex n :=
  Function.update x a (!x a)

/-- Adjacent bin vectors: they differ in exactly one coordinate, by exactly one (06:88). -/
def binAdjacent6 {n : ℕ} (u w : BinVector6 n) : Prop :=
  ∃ i, (∀ j, j ≠ i → u j = w j) ∧ Nat.dist (u i).val (w i).val = 1

/-- The chunk layout and the coarse bins (05:81–103, 06:67–73). -/
structure ChunkLayout6 (n : ℕ) where
  m : ℕ
  fineLength : ℕ
  coarseChunks : Fin coarseChunkCount → Finset (Fin n)
  fineChunks : Fin m → Finset (Fin n)
  residual : Finset (Fin n)
  bin : Fin coarseChunkCount → ℕ → Fin (n + 1)
  chunks_disjoint : (∀ i j, i ≠ j → Disjoint (coarseChunks i) (coarseChunks j)) ∧
    (∀ i j, Disjoint (coarseChunks i) (fineChunks j)) ∧
    (∀ i j, i ≠ j → Disjoint (fineChunks i) (fineChunks j)) ∧
    (∀ i, Disjoint (coarseChunks i) residual) ∧
    (∀ i, Disjoint (fineChunks i) residual)
  chunks_cover : (Finset.univ.biUnion coarseChunks) ∪ (Finset.univ.biUnion fineChunks) ∪ residual =
    Finset.univ
  occupied_sublinear :
    (((Finset.univ.biUnion coarseChunks) ∪ (Finset.univ.biUnion fineChunks)).card : ℝ) ≤
      (n : ℝ) ^ (1 / 2 : ℝ)
  coarse_length : ∀ i, (coarseChunks i).card = ⌊(n : ℝ) ^ (1 / 5 : ℝ)⌋₊
  fine_length_odd : Odd fineLength
  fine_length_lower : (n : ℝ) ^ (3 / 10 : ℝ) ≤ fineLength
  fine_length_upper : (fineLength : ℝ) ≤ 2 * (n : ℝ) ^ (3 / 10 : ℝ)
  fine_chunk_length : ∀ i, (fineChunks i).card = fineLength
  residual_nonempty : residual.Nonempty
  bin_monotone : ∀ i a b, a ≤ b → (bin i a).val ≤ (bin i b).val
  bin_step : ∀ i a, (bin i (a + 1)).val ≤ (bin i a).val + 1
  bin_probability : ∀ i j,
    (∑ q ∈ Finset.range ((coarseChunks i).card + 1),
      if bin i q = j then (Nat.choose (coarseChunks i).card q : ℝ) else 0) ≤
        2 * (n : ℝ) ^ (-(1 / 25 : ℝ)) * (2 : ℝ) ^ (coarseChunks i).card
  bin_count : ∀ i,
    (((Finset.range ((coarseChunks i).card + 1)).image (bin i)).card : ℝ) ≤ (n : ℝ) ^ (1 / 25 : ℝ) + 1

namespace ChunkLayout6

variable {n : ℕ} (L : ChunkLayout6 n)

def coarseCount (x : CubeVertex n) (i : Fin coarseChunkCount) : ℕ :=
  ((L.coarseChunks i).filter fun a => x a = true).card

/-- The bin vector `w(x)` (05:86–87). -/
def coarseBin (x : CubeVertex n) : BinVector6 n := fun i => L.bin i (L.coarseCount x i)

def fineCount (x : CubeVertex n) (i : Fin L.m) : ℕ :=
  ((L.fineChunks i).filter fun a => x a = true).card

/-- Majority signs `t ∈ Q_m` (06:71). -/
def sign (x : CubeVertex n) : CubeVertex L.m := fun i => decide (L.fineLength < 2 * L.fineCount x i)

/-- Exactly flippable chunks `F`: count at distance `1/2` from mid-weight (06:71–72). -/
def flippable (x : CubeVertex n) : Finset (Fin L.m) :=
  Finset.univ.filter fun i => Nat.dist (2 * L.fineCount x i) L.fineLength = 1

/-- Severity `j`: chunks with count within `R_f = 5.5` of mid-weight (06:72–73). -/
def severity (x : CubeVertex n) : ℕ :=
  (Finset.univ.filter fun i : Fin L.m => Nat.dist (2 * L.fineCount x i) L.fineLength ≤ 11).card

/-- Boundary flag: some single coarse flip changes the bin vector (05:88–89). -/
def boundary (x : CubeVertex n) : Prop :=
  ∃ i a, a ∈ L.coarseChunks i ∧ L.coarseBin (flipVertex6 x a) ≠ L.coarseBin x

/-- The coarse key `h_x = (w, int/bdy)` (06:78). -/
def key (x : CubeVertex n) : CoarseKey6 (BinVector6 n) :=
  (L.coarseBin x, if L.boundary x then .boundary else .interior)

/-- The fine count with distances `5.5` and `6.5` merged on each side of mid-weight (06:231–233). -/
def mergedCount (x : CubeVertex n) (i : Fin L.m) : ℕ :=
  let c := L.fineCount x i
  if 2 * c = L.fineLength + 13 then c - 1 else if 2 * c + 13 = L.fineLength then c + 1 else c

/-- The residual Hamming distance of two roles. -/
def residualDist (x y : CubeVertex n) : ℕ := (L.residual.filter fun a => x a ≠ y a).card

end ChunkLayout6

/-- The sign fiber of a parity class (05:104–105). -/
def signFiber6 {n : ℕ} (L : ChunkLayout6 n) (p : Bool) (t : CubeVertex L.m) : Finset (CubeVertex n) :=
  Finset.univ.filter fun x => (if p then IsEvenRole x else ¬ IsEvenRole x) ∧ L.sign x = t

def parityFiber6 {n : ℕ} (p : Bool) : Finset (CubeVertex n) :=
  Finset.univ.filter fun x => if p then IsEvenRole x else ¬ IsEvenRole x

/-- The deterministic flip facts (06:74–91, 05:88–109). -/
structure ChunkFlips6 {n : ℕ} (L : ChunkLayout6 n) : Prop where
  fine_flip_sign : ∀ x y i, (cube n).Adj x y → (∃ a ∈ L.fineChunks i, x a ≠ y a) →
    ∀ j, j ≠ i → L.sign x j = L.sign y j
  fine_flip_severity : ∀ x y, (cube n).Adj x y → (∃ i a, a ∈ L.fineChunks i ∧ x a ≠ y a) →
    Nat.dist (L.severity x) (L.severity y) ≤ 1
  nonfine_flip_fine : ∀ x y, (cube n).Adj x y → (∀ i a, a ∈ L.fineChunks i → x a = y a) →
    L.sign x = L.sign y ∧ L.flippable x = L.flippable y ∧ L.severity x = L.severity y
  noncoarse_flip_key : ∀ x y, (cube n).Adj x y → (∀ i a, a ∈ L.coarseChunks i → x a = y a) →
    L.key x = L.key y
  coarse_flip_key : ∀ x y, (cube n).Adj x y → (∃ i a, a ∈ L.coarseChunks i ∧ x a ≠ y a) →
    keyAdjacent6 binAdjacent6 (L.key x) (L.key y)
  changing_bin_boundary : ∀ x y, (cube n).Adj x y → L.coarseBin x ≠ L.coarseBin y →
    L.boundary x ∧ L.boundary y
  key_neighborhood_card : ∀ h : CoarseKey6 (BinVector6 n), (keyNeighborhood6 binAdjacent6 h).card ≤ 602

/-- L6.1b output: a layout with `m = ⌈n^α⌉` and the probabilistic facts (06:74–76). -/
structure ChunkGeometry6 (n : ℕ) (α : ℝ) where
  L : ChunkLayout6 n
  m_eq : L.m = ⌈(n : ℝ) ^ α⌉₊
  sign_uniform : ∀ p t, ((signFiber6 L p t).card : ℝ) * (2 : ℝ) ^ L.m = ((parityFiber6 (n := n) p).card : ℝ)
  severity_tail : ∀ q, 1 ≤ q → q ≤ L.m →
    ((Finset.univ.filter fun x : CubeVertex n => q ≤ L.severity x).card : ℝ) / (2 : ℝ) ^ n ≤
      (n : ℝ) ^ (-(13 / 100 : ℝ) * q)
  boundary_fraction :
    ((Finset.univ.filter fun x : CubeVertex n => L.boundary x).card : ℝ) / (2 : ℝ) ^ n ≤
      (n : ℝ) ^ (-(1 / 20 : ℝ))
  flips : ChunkFlips6 L

/-- L6.1b (layout): for `0 < α ≤ 1/100` and `n` large there is a chunk layout with `m = ⌈n^α⌉` (06:67–73; uses
F-Bins `exists_consecutive_bin_partition` with `ε = n^{-.04}`). -/
theorem L6_1b_layout (α : ℝ) (hα : 0 < α) (hα' : α ≤ 1 / 100) :
    ∃ n₀ : ℕ, ∀ n ≥ n₀, ∃ L : ChunkLayout6 n, L.m = ⌈(n : ℝ) ^ α⌉₊ := by
  sorry

/-- L6.1b (signs): on each parity class the majority signs are uniform (06:74; complement one fine chunk and
flip one residual coordinate). -/
theorem L6_1b_signs {n : ℕ} (L : ChunkLayout6 n) (p : Bool) (t : CubeVertex L.m) :
    ((signFiber6 L p t).card : ℝ) * (2 : ℝ) ^ L.m = ((parityFiber6 (n := n) p).card : ℝ) := by
  sorry

/-- L6.1b (severity tail): `Pr(j ≥ q) ≤ n^{-.13q}` for `1 ≤ q ≤ m` (06:75; atom `O(n^{-.15})` per chunk,
union over `q`-subsets, needs `α < .02`). -/
theorem L6_1b_tail (α : ℝ) (hα : 0 < α) (hα' : α ≤ 1 / 100) :
    ∃ n₀ : ℕ, ∀ n ≥ n₀, ∀ L : ChunkLayout6 n, L.m = ⌈(n : ℝ) ^ α⌉₊ → ∀ q, 1 ≤ q → q ≤ L.m →
      ((Finset.univ.filter fun x : CubeVertex n => q ≤ L.severity x).card : ℝ) / (2 : ℝ) ^ n ≤
        (n : ℝ) ^ (-(13 / 100 : ℝ) * q) := by
  sorry

/-- L6.1b (boundary): the coarse boundary fraction is at most `n^{-.05}` (06:75–76; at most `n^{.04}+1` bins
per chunk, atoms `≤ 2/√⌊n^{1/5}⌋`, union over `300` chunks). -/
theorem L6_1b_boundary :
    ∃ n₀ : ℕ, ∀ n ≥ n₀, ∀ L : ChunkLayout6 n,
      ((Finset.univ.filter fun x : CubeVertex n => L.boundary x).card : ℝ) / (2 : ℝ) ^ n ≤
        (n : ℝ) ^ (-(1 / 20 : ℝ)) := by
  sorry

/-- L6.1b (flips): coarse flips stay in the key relation, a bin change has boundary ends, fine flips change
one sign and the severity by at most one, `|C(h)| ≤ 602` (06:86–91, 05:88–109). -/
theorem L6_1b_flips {n : ℕ} (L : ChunkLayout6 n) : ChunkFlips6 L := by
  sorry

/-- L6.1b, assembled from its sub-nodes. -/
theorem L6_1b (α : ℝ) (hα : 0 < α) (hα' : α ≤ 1 / 100) :
    ∃ n₀ : ℕ, ∀ n ≥ n₀, Nonempty (ChunkGeometry6 n α) := by
  obtain ⟨n₁, h₁⟩ := L6_1b_layout α hα hα'
  obtain ⟨n₂, h₂⟩ := L6_1b_tail α hα hα'
  obtain ⟨n₃, h₃⟩ := L6_1b_boundary
  refine ⟨max n₁ (max n₂ n₃), fun n hn => ?_⟩
  obtain ⟨L, hL⟩ := h₁ n (le_trans (le_max_left _ _) hn)
  exact ⟨{
    L := L
    m_eq := hL
    sign_uniform := L6_1b_signs L
    severity_tail := h₂ n (le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) hn) L hL
    boundary_fraction := h₃ n (le_trans (le_trans (le_max_right _ _) (le_max_right _ _)) hn) L
    flips := L6_1b_flips L }⟩

end

end S06
end HypercubeRamsey
