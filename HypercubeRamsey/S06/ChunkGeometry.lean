import HypercubeRamsey.S06.Defs

/-!
# Section 6 coarse and fine chunk geometry

L6.1b (06:67–92).  The record fixes the reused Section 5 chunk construction
with the Section 6 severity cutoff `J = floor(m^.04)`.  Its estimate fields
are the exact quantitative interface consumed by the Section 6 history and
height stages.
-/

namespace HypercubeRamsey
namespace S06

open OAI.HypercubeRamsey
open Classical

abbrev BinVector6 (n : ℕ) := Fin coarseChunkCount → Fin (n + 1)

noncomputable def parityFiber6 {n : ℕ} (p : Bool) : Finset (CubeVertex n) :=
  Finset.univ.filter fun x => if p then IsEvenRole x else ¬ IsEvenRole x

noncomputable def signFiber6 {n m : ℕ} (p : Bool) (t : CubeVertex m)
    (sign : CubeVertex n → CubeVertex m) : Finset (CubeVertex n) :=
  Finset.univ.filter fun x => (if p then IsEvenRole x else ¬ IsEvenRole x) ∧ sign x = t

noncomputable def severityTail6 {n : ℕ} (q : ℕ) (severity : CubeVertex n → ℕ) : Finset (CubeVertex n) :=
  Finset.univ.filter fun x => q ≤ severity x

noncomputable def boundarySet6 {n : ℕ} (key : CubeVertex n → CoarseKey6 (BinVector6 n)) :
    Finset (CubeVertex n) :=
  Finset.univ.filter fun x => (key x).2 = .boundary

def flipVertex6 {n : ℕ} (x : CubeVertex n) (a : Fin n) : CubeVertex n :=
  Function.update x a (!x a)

structure ChunkGeometry6 (n : ℕ) (α : ℝ) where
  m : ℕ
  fineLength : ℕ
  coarseChunks : Fin coarseChunkCount → Finset (Fin n)
  fineChunks : Fin m → Finset (Fin n)
  residual : Finset (Fin n)
  chunks_disjoint : (∀ i j, i ≠ j → Disjoint (coarseChunks i) (coarseChunks j)) ∧
    (∀ i j, Disjoint (coarseChunks i) (fineChunks j)) ∧
    (∀ i j, i ≠ j → Disjoint (fineChunks i) (fineChunks j)) ∧
    (∀ i, Disjoint (coarseChunks i) residual) ∧
    (∀ i, Disjoint (fineChunks i) residual)
  chunks_cover : (Finset.univ.biUnion coarseChunks) ∪
    (Finset.univ.biUnion fineChunks) ∪ residual = Finset.univ
  occupied_coordinates_sublinear :
    (((Finset.univ.biUnion coarseChunks) ∪ (Finset.univ.biUnion fineChunks)).card : ℝ) ≤
      (n : ℝ) ^ (1 / 2 : ℝ)
  coarse_length : ∀ i, (coarseChunks i).card = Nat.floor ((n : ℝ) ^ (1 / 5 : ℝ))
  coarse_count : CubeVertex n → Fin coarseChunkCount → ℕ
  coarse_count_eq : ∀ x i, coarse_count x i =
    ((coarseChunks i).filter fun a => x a = true).card
  bin : Fin coarseChunkCount → ℕ → Fin (n + 1)
  bin_monotone : ∀ i a b, a ≤ b → (bin i a).val ≤ (bin i b).val
  bin_fibers_are_intervals : ∀ i a b c, a ≤ b → b ≤ c →
    bin i a = bin i c → bin i a = bin i b
  bin_probability_bound : ∀ i j,
    (∑ q ∈ Finset.range ((coarseChunks i).card + 1),
      if bin i q = j then (Nat.choose (coarseChunks i).card q : ℝ) else 0) ≤
        2 * (n : ℝ) ^ (-0.04 : ℝ) * (2 : ℝ) ^ (coarseChunks i).card
  fine_length_odd : Odd fineLength
  fine_length_lower : (n : ℝ) ^ (3 / 10 : ℝ) ≤ fineLength
  fine_length_upper : (fineLength : ℝ) ≤ 2 * (n : ℝ) ^ (3 / 10 : ℝ)
  fine_chunk_length : ∀ i, (fineChunks i).card = fineLength
  residual_nonempty : residual.Nonempty
  fine_count : CubeVertex n → Fin m → ℕ
  fine_count_eq : ∀ x i, fine_count x i =
    ((fineChunks i).filter fun a => x a = true).card
  coarse_bin : CubeVertex n → BinVector6 n
  sign : CubeVertex n → CubeVertex m
  flippable : CubeVertex n → Finset (Fin m)
  severity : CubeVertex n → ℕ
  boundary : CubeVertex n → Prop
  key : CubeVertex n → CoarseKey6 (BinVector6 n)
  binAdjacent : BinVector6 n → BinVector6 n → Prop
  binAdjacent_symm : ∀ a b, binAdjacent a b → binAdjacent b a
  key_is_bin_and_flag : ∀ x, (key x).1 = coarse_bin x ∧ ((key x).2 = .boundary ↔ boundary x)
  coarse_bin_is_binned_count : ∀ x i, coarse_bin x i = bin i (coarse_count x i)
  boundary_detects_bin_flip : ∀ x, boundary x ↔
    ∃ i a, a ∈ coarseChunks i ∧ coarse_bin (flipVertex6 x a) ≠ coarse_bin x
  sign_uniform : ∀ p t,
    ((signFiber6 (n := n) (m := m) p t sign).card : ℝ) * (2 : ℝ) ^ m =
      ((parityFiber6 (n := n) p).card : ℝ)
  severity_tail : ∀ q, 1 ≤ q → q ≤ m →
    ((severityTail6 (n := n) q severity).card : ℝ) / (2 : ℝ) ^ n ≤
      (n : ℝ) ^ (-(0.13 : ℝ) * q)
  boundary_fraction : ((boundarySet6 (n := n) key).card : ℝ) / (2 : ℝ) ^ n ≤
    (n : ℝ) ^ (-0.05 : ℝ)
  flippable_exact : ∀ x i, i ∈ flippable x ↔
    Nat.dist (2 * fine_count x i) fineLength = 1
  severity_exact : ∀ x, severity x =
    (Finset.univ.filter fun i : Fin m => Nat.dist (2 * fine_count x i) fineLength ≤ 11).card
  sign_majority : ∀ x i, sign x i = true ↔ 2 * fine_count x i > fineLength
  fine_flip_sign : ∀ x y i, (cube n).Adj x y →
    (∃ a ∈ fineChunks i, x a ≠ y a) →
      ∀ j, j ≠ i → sign x j = sign y j
  fine_flip_severity : ∀ x y, (cube n).Adj x y →
    (∃ i a, a ∈ fineChunks i ∧ x a ≠ y a) → Nat.dist (severity x) (severity y) ≤ 1
  coarse_flip_key : ∀ x y, (cube n).Adj x y →
    (∃ i a, a ∈ coarseChunks i ∧ x a ≠ y a) →
    keyAdjacent6 binAdjacent (key x) (key y)
  coarse_flip_changes_one_bin : ∀ x y, (cube n).Adj x y →
    (∃ i a, a ∈ coarseChunks i ∧ x a ≠ y a) →
      (Finset.univ.filter fun i : Fin coarseChunkCount =>
        coarse_bin x i ≠ coarse_bin y i).card ≤ 1 ∧
      (∀ i, Nat.dist (coarse_bin x i).val (coarse_bin y i).val ≤ 1)
  changing_coarse_bin_has_boundary_ends : ∀ x y, (cube n).Adj x y →
    (∃ i a, a ∈ coarseChunks i ∧ x a ≠ y a) →
      coarse_bin x ≠ coarse_bin y → boundary x ∧ boundary y
  key_neighborhood_card : ∀ h,
    (keyNeighborhood6 binAdjacent h).card ≤ 602

noncomputable def ChunkGeometry6.J {n : ℕ} {α : ℝ} (g : ChunkGeometry6 n α) : ℕ :=
  Nat.floor ((g.m : ℝ) ^ (0.04 : ℝ))

def ChunkGeometry6.low {n : ℕ} {α : ℝ} (g : ChunkGeometry6 n α)
    (x : CubeVertex n) : Prop := g.severity x ≤ g.J

noncomputable def oneHotDistance6 {d : ℕ} (x y : CubeVertex d) : ℕ :=
  (Finset.univ.filter fun i => x i ≠ y i).card

/--
The Section 5 state encoding reused in Section 6: a site retains the residual
bits, exact coarse counts, the merged 5.5/6.5 fine-count fields, and severity
`j`; `oneHot` is its embedding in an auxiliary cube of dimension `d=(1+o(1))n`.
-/
structure StateEncoding6 {n : ℕ} {α : ℝ} (g : ChunkGeometry6 n α) where
  Site : Type
  [siteFintype : Fintype Site]
  [siteDecEq : DecidableEq Site]
  d : ℕ
  stateOf : CubeVertex n → Site
  representative : Site → CubeVertex n
  stateOf_representative : ∀ s, stateOf (representative s) = s
  oneHot : Site → CubeVertex d
  oneHot_injective : Function.Injective oneHot
  evenRole : Site → Bool
  key : Site → CoarseKey6 (BinVector6 n)
  sign : Site → CubeVertex g.m
  severity : Site → ℕ
  mode : Site → Mode6
  primaryName : Site → ParentName6 (BinVector6 n)
  state_fields_exact : ∀ s,
    key s = g.key (representative s) ∧ sign s = g.sign (representative s) ∧
      severity s = g.severity (representative s) ∧
      evenRole s = decide (IsEvenRole (representative s))
  mode_exact : ∀ s,
    mode s = if severity s ≤ g.J then Mode6.low else Mode6.high
  neighbors : Site → Finset Site
  edge_maps_to_neighbors : ∀ x y, (cube n).Adj x y →
    stateOf y ∈ neighbors (stateOf x)
  neighbor_count_constant : ℕ
  neighbor_count_bound : ∀ s, (neighbors s).card ≤ neighbor_count_constant * n
  even_neighbor_distance : ∀ b a a', evenRole b = false →
    a ∈ neighbors b → a' ∈ neighbors b → evenRole a = true → evenRole a' = true →
      oneHotDistance6 (oneHot a) (oneHot a') ≤ 10
  low_neighbor_state_count : ∀ b, evenRole b = false →
    ((neighbors b).filter (fun s => evenRole s = true ∧ mode s = Mode6.low)).card ≤ 1
  high_neighbor_state_count : ∀ b, evenRole b = false →
    ((neighbors b).filter (fun s => evenRole s = true ∧ mode s = Mode6.high)).card ≤ 1
  nonmatching_primary_state_count : ∀ b p, evenRole b = false →
    ((neighbors b).filter fun s => evenRole s = true ∧ primaryName s ≠ p).card ≤ 1
  dimension_lower : n ≤ d
  dimension_bound : (d : ℝ) ≤ (n : ℝ) + (coarseChunkCount : ℝ) *
    (Nat.floor ((n : ℝ) ^ (1 / 5 : ℝ)) : ℝ) +
    (g.m : ℝ) * ((g.fineLength : ℝ) + 2) + 1

attribute [instance] StateEncoding6.siteFintype StateEncoding6.siteDecEq

/-- L6.1e, shared with Section 5: state coding and the local neighborhood bounds. -/
theorem L6_1e {n : ℕ} {α : ℝ} (g : ChunkGeometry6 n α) :
    Nonempty (StateEncoding6 g) := by
  sorry

/-- L6.1b: the binning/entropy tools give this geometry for all sufficiently large dimensions. -/
theorem L6_1b (α : ℝ) (hα : 0 < α) :
    ∃ n₀ : ℕ, ∀ n ≥ n₀, ∃ g : ChunkGeometry6 n α,
      (n : ℝ) ^ α ≤ g.m ∧ (g.m : ℝ) < (n : ℝ) ^ α + 1 := by
  sorry

end S06
end HypercubeRamsey
