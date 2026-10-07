import HypercubeRamsey.S05.Parents

/-!
# D5.3, D5.5, L5.1b, L5.1e0: chunks, keys, even types and states

The cube coordinates are split into 300 coarse chunks, `m` odd fine chunks and residual coordinates
(05:81–109).  Counts, bins, majority signs, the flippable set `F` and the severity `j` are *definitions* from
the layout; `ChunkGeometry5` records the layout and the three probability estimates of L5.1b.  Hidden-column
keys and even types (05:111–149) are definitions from the geometry.  `CubeStates5` is the state quotient with
its one-hot embedding (05:291–329); every role in a state has the same key, sign, severity, parity, type and
residual bits.
-/

namespace HypercubeRamsey

open Classical OAI.HypercubeRamsey

/-- Even cube roles (embedded on the first side `X`). -/
abbrev EvenRole5 (n : ℕ) := {v : CubeVertex n // IsEvenRole v}

/-- Odd cube roles (embedded on the second side `Y`). -/
abbrev OddRole5 (n : ℕ) := {v : CubeVertex n // ¬ IsEvenRole v}

/-- Number of coarse chunks, `d_c = 300` (05:81). -/
def coarseChunkCount5 : ℕ := 300

/-- A vector of coarse bins, one per coarse chunk. -/
abbrev BinVector5 (n : ℕ) := Fin coarseChunkCount5 → Fin (n + 1)

/-- A coarse key `i(P)`: the bin vector and the boundary flag (`true` = boundary) (05:84–90). -/
abbrev CoarseKey5 (n : ℕ) := BinVector5 n × Bool

/-- Flip one coordinate of a cube vertex. -/
def flipVertex5 {n : ℕ} (x : CubeVertex n) (a : Fin n) : CubeVertex n :=
  Function.update x a (!x a)

/-- Grid neighbours of bin vectors: exactly one coordinate differs, by one. -/
def binAdjacent5 {n : ℕ} (w w' : BinVector5 n) : Prop :=
  (Finset.univ.filter (fun i => w i ≠ w' i)).card = 1 ∧ ∀ i, Nat.dist (w i).val (w' i).val ≤ 1

/-- D5.3 layout (05:81–109): disjoint coarse chunks of length `⌊n^{1/5}⌋`, `m` fine chunks of a common odd
length `≍ n^{.3}`, residual coordinates, and consecutive count bins of binomial probability `≤ 2n^{-.04}`.
The fields `sign_uniform`, `severity_tail` and `boundary_fraction` are the probability estimates of L5.1b. -/
structure ChunkGeometry5 (n m : ℕ) where
  fineLength : ℕ
  coarseChunks : Fin coarseChunkCount5 → Finset (Fin n)
  fineChunks : Fin m → Finset (Fin n)
  residual : Finset (Fin n)
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
  bin : Fin coarseChunkCount5 → ℕ → Fin (n + 1)
  bin_monotone : ∀ i a b, a ≤ b → (bin i a).val ≤ (bin i b).val
  bin_consecutive : ∀ i a, (bin i (a + 1)).val ≤ (bin i a).val + 1
  bin_probability_bound : ∀ i j,
    (∑ q ∈ Finset.range ((coarseChunks i).card + 1),
      if bin i q = j then (Nat.choose (coarseChunks i).card q : ℝ) else 0) ≤
        2 * (n : ℝ) ^ (-(4 / 100 : ℝ)) * (2 : ℝ) ^ (coarseChunks i).card
  fine_length_odd : Odd fineLength
  fine_length_lower : (n : ℝ) ^ (3 / 10 : ℝ) ≤ fineLength
  fine_length_upper : (fineLength : ℝ) ≤ 2 * (n : ℝ) ^ (3 / 10 : ℝ)
  fine_chunk_length : ∀ i, (fineChunks i).card = fineLength
  residual_nonempty : residual.Nonempty

namespace ChunkGeometry5

variable {n m : ℕ} (g : ChunkGeometry5 n m)

/-- Count of ones in a coarse chunk. -/
noncomputable def coarseCount (x : CubeVertex n) (i : Fin coarseChunkCount5) : ℕ :=
  ((g.coarseChunks i).filter fun a => x a = true).card

/-- Bin vector `w(P)`. -/
noncomputable def coarseBin (x : CubeVertex n) : BinVector5 n := fun i => g.bin i (g.coarseCount x i)

/-- Boundary flag: some single coarse bit flip changes a bin. -/
def boundary (x : CubeVertex n) : Prop :=
  ∃ i, ∃ a ∈ g.coarseChunks i, g.coarseBin (flipVertex5 x a) ≠ g.coarseBin x

/-- Coarse key `i(P)`. -/
noncomputable def key (x : CubeVertex n) : CoarseKey5 n := (g.coarseBin x, decide (g.boundary x))

/-- Count of ones in a fine chunk. -/
noncomputable def fineCount (x : CubeVertex n) (i : Fin m) : ℕ :=
  ((g.fineChunks i).filter fun a => x a = true).card

/-- Majority signs `t ∈ Q_m`. -/
noncomputable def sign (x : CubeVertex n) : CubeVertex m := fun i => decide (g.fineLength < 2 * g.fineCount x i)

/-- The flippable chunks `F`: count at distance `1/2` from mid-weight. -/
noncomputable def flippable (x : CubeVertex n) : Finset (Fin m) :=
  Finset.univ.filter fun i => Nat.dist (2 * g.fineCount x i) g.fineLength = 1

/-- Severity `j`: the number of fine chunks within `R_f = 5.5` of mid-weight. -/
noncomputable def severity (x : CubeVertex n) : ℕ :=
  (Finset.univ.filter fun i : Fin m => Nat.dist (2 * g.fineCount x i) g.fineLength ≤ 11).card

/-- Coarse coordinates. -/
noncomputable def coarseCoords : Finset (Fin n) := Finset.univ.biUnion g.coarseChunks

/-- Residual Hamming distance between two roles. -/
noncomputable def residualDist (x y : CubeVertex n) : ℕ :=
  (g.residual.filter fun a => x a ≠ y a).card

end ChunkGeometry5

/-- The candidate bin list `C_i` of a coarse key: `{w}` at interior keys, `w` and its grid neighbours at
boundary keys (05:88–91). -/
noncomputable def binList5 {n : ℕ} (i : CoarseKey5 n) : Finset (BinVector5 n) :=
  if i.2 then Finset.univ.filter (fun w => w = i.1 ∨ binAdjacent5 i.1 w) else {i.1}

/-- L5.1b (05:81–109): the layout exists for large `n`, with the three probability estimates: signs uniform on
each parity class, `Pr(j ≥ h) ≤ n^{-.13h}` for `1 ≤ h ≤ m`, and `Pr(boundary) ≤ n^{-.05}`. -/
structure ChunkEstimates5 {n m : ℕ} (g : ChunkGeometry5 n m) : Prop where
  sign_uniform : ∀ (b : Bool) (t : CubeVertex m),
    ((Finset.univ.filter fun x : CubeVertex n => decide (IsEvenRole x) = b ∧ g.sign x = t).card : ℝ) *
        (2 : ℝ) ^ m =
      ((Finset.univ.filter fun x : CubeVertex n => decide (IsEvenRole x) = b).card : ℝ)
  severity_tail : ∀ h : ℕ, 1 ≤ h → h ≤ m →
    ((Finset.univ.filter fun x : CubeVertex n => h ≤ g.severity x).card : ℝ) / (2 : ℝ) ^ n ≤
      (n : ℝ) ^ (-(13 / 100 : ℝ) * h)
  boundary_fraction :
    ((Finset.univ.filter fun x : CubeVertex n => g.boundary x).card : ℝ) / (2 : ℝ) ^ n ≤
      (n : ℝ) ^ (-(5 / 100 : ℝ))

/-- L5.1b (05:81–109): for every fixed `0 < α < 1/50`, the D5.3 layout with `m = ⌈n^α⌉` fine chunks exists
for all large `n` and has the L5.1b estimates. -/
theorem L5_1b (α : ℝ) (hα : 0 < α) (hα' : α < 1 / 50) :
    ∃ n₀ : ℕ, ∀ n ≥ n₀, ∃ g : ChunkGeometry5 n ⌈(n : ℝ) ^ α⌉₊, ChunkEstimates5 g := by
  sorry

/-! ### Keys and even types (05:111–149) -/

/-- Hidden-column keys: low keys `(i, t, j)` with `j ≤ J`, and high keys `(i, *)`. -/
abbrev HiddenKey5 (n m J : ℕ) := (CoarseKey5 n × CubeVertex m × Fin (J + 1)) ⊕ CoarseKey5 n

/-- Coarse key of a hidden key. -/
def HiddenKey5.coarse {n m J : ℕ} : HiddenKey5 n m J → CoarseKey5 n
  | .inl k => k.1
  | .inr i => i

/-- Severity level read by a key's posterior: `j` at low keys, `J` at high keys (05:127–130). -/
def HiddenKey5.level {n m J : ℕ} : HiddenKey5 n m J → ℕ
  | .inl k => k.2.2.val
  | .inr _ => J

/-- An even type: coarse key, the padded key list `S`, and the severity (`some j`, low) or `none` (high). -/
abbrev EvenType5 (n m J : ℕ) := CoarseKey5 n × Finset (HiddenKey5 n m J) × Option (Fin (J + 1))

/-- The low key at coarse key `i`, signs `t` and severity `j'`, replaced by the high key above `J`. -/
noncomputable def keyAt5 {n m : ℕ} (J : ℕ) (i : CoarseKey5 n) (t : CubeVertex m) (j' : ℕ) :
    HiddenKey5 n m J :=
  if h : j' ≤ J then .inl (i, t, ⟨j', Nat.lt_succ_of_le h⟩) else .inr i

namespace ChunkGeometry5

variable {n m : ℕ} (g : ChunkGeometry5 n m) (J : ℕ)

/-- Low/high split at `J`. -/
def low (x : CubeVertex n) : Prop := g.severity x ≤ J

/-- The key of a role (05:118–122). -/
noncomputable def roleKey (x : CubeVertex n) : HiddenKey5 n m J :=
  if h : g.severity x ≤ J then .inl (g.key x, g.sign x, ⟨g.severity x, Nat.lt_succ_of_le h⟩)
  else .inr (g.key x)

/-- Coarse keys of `x` and of its single coarse flips. -/
noncomputable def coarseRange (x : CubeVertex n) : Finset (CoarseKey5 n) :=
  insert (g.key x) (g.coarseCoords.image fun a => g.key (flipVertex5 x a))


/-- The padded key list `S(v)` of an even role (05:133–144). -/
noncomputable def typeKeys (x : CubeVertex n) : Finset (HiddenKey5 n m J) :=
  if g.severity x ≤ J then
    (g.coarseRange x).image (fun i => keyAt5 J i (g.sign x) (g.severity x)) ∪
      (g.flippable x).image (fun h => keyAt5 J (g.key x) (Function.update (g.sign x) h
        (!g.sign x h)) (g.severity x)) ∪
      Finset.image (fun j' => keyAt5 J (g.key x) (g.sign x) j')
        (({g.severity x + 1} : Finset ℕ) ∪ (if 0 < g.severity x then {g.severity x - 1} else ∅))
  else (g.coarseRange x).image (fun i => (.inr i : HiddenKey5 n m J))

/-- The even type `K(v)` (05:138–141). -/
noncomputable def evenType (x : CubeVertex n) : EvenType5 n m J :=
  (g.key x, g.typeKeys J x,
    if h : g.severity x ≤ J then some ⟨g.severity x, Nat.lt_succ_of_le h⟩ else none)

/-- The optional low key `(i(P), t, J)` of a high even role with `j = J + 1` (05:141–144). -/
noncomputable def optionalKey (x : CubeVertex n) : Option (HiddenKey5 n m J) :=
  if g.severity x = J + 1 then some (.inl (g.key x, g.sign x, ⟨J, Nat.lt_succ_self J⟩)) else none

end ChunkGeometry5

/-- L5.1e, coverage part (05:144–147): the padded list and the optional key cover the keys of all actual odd
neighbours of an even role, and every key in a type list has the role's bin in its candidate list. -/
theorem L5_1e_cover {n m : ℕ} (g : ChunkGeometry5 n m) (J : ℕ) :
    (∀ x y : CubeVertex n, (cube n).Adj x y →
      g.roleKey J y ∈ g.typeKeys J x ∨ g.optionalKey J x = some (g.roleKey J y)) ∧
    (∀ x : CubeVertex n, ∀ ℓ ∈ g.typeKeys J x, (g.key x).1 ∈ binList5 ℓ.coarse) := by
  sorry

/-! ### D5.5: states and the one-hot embedding (05:291–313) -/

/-- The state quotient (05:291–313).  Roles in one state share key, signs, severity, parity, even type and
residual bits; the one-hot embedding is injective, reproduces the residual bits, has dimension
`n + O(√n)`, and two even states adjacent to one odd state are at ambient distance at most `8`. -/
structure CubeStates5 {n m : ℕ} (g : ChunkGeometry5 n m) (J : ℕ) where
  Site : Type
  [siteFintype : Fintype Site]
  [siteDecEq : DecidableEq Site]
  d : ℕ
  stateOf : CubeVertex n → Site
  oneHot : Site → CubeVertex d
  oneHot_injective : Function.Injective oneHot
  resCoord : g.residual → Fin d
  resCoord_injective : Function.Injective resCoord
  oneHot_residual : ∀ x (a : g.residual), oneHot (stateOf x) (resCoord a) = x a.1
  state_determines : ∀ x y, stateOf x = stateOf y →
    g.key x = g.key y ∧ g.sign x = g.sign y ∧ g.severity x = g.severity y ∧
      (IsEvenRole x ↔ IsEvenRole y) ∧ g.evenType J x = g.evenType J y ∧
        g.optionalKey J x = g.optionalKey J y ∧ g.roleKey J x = g.roleKey J y
  neighbors : Site → Finset Site
  mem_neighbors : ∀ s t, t ∈ neighbors s ↔
    ∃ x y, stateOf x = s ∧ stateOf y = t ∧ (cube n).Adj x y
  degree_bound : ∀ s, (neighbors s).card ≤ 2 * n
  even_distance : ∀ b a a', a ∈ neighbors b → a' ∈ neighbors b →
    (∃ x, stateOf x = a ∧ IsEvenRole x) → (∃ x, stateOf x = a' ∧ IsEvenRole x) →
      hammingDist (oneHot a) (oneHot a') ≤ 8
  dimension_upper : (d : ℝ) ≤ n + 3 * (n : ℝ) ^ (1 / 2 : ℝ) + 301

attribute [instance] CubeStates5.siteFintype CubeStates5.siteDecEq

/-- L5.1e0 (05:291–313), with the constants in the order `∀ ε, ∃ n₀`: the state quotient exists at every
layout, and its dimension is at most `(1 + ε) n` once `n ≥ n₀(ε)`. -/
theorem L5_1e0 : ∀ ε : ℝ, 0 < ε → ∃ n₀ : ℕ, ∀ n ≥ n₀, ∀ (m J : ℕ) (g : ChunkGeometry5 n m),
    ∃ S : CubeStates5 g J, (S.d : ℝ) ≤ (1 + ε) * n := by
  sorry

end HypercubeRamsey
