import HypercubeRamsey.S05.Parents
import HypercubeRamsey.S05.Geometry_q_s05_1b

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

set_option maxRecDepth 4096 in
set_option maxHeartbeats 1000000 in
/-- L5.1b (05:81–109): for every fixed `0 < α < 1/50`, the D5.3 layout with `m = ⌈n^α⌉` fine chunks exists
for all large `n` and has the L5.1b estimates. -/
theorem L5_1b (α : ℝ) (hα : 0 < α) (hα' : α < 1 / 50) :
    ∃ n₀ : ℕ, ∀ n ≥ n₀, ∃ g : ChunkGeometry5 n ⌈(n : ℝ) ^ α⌉₊, ChunkEstimates5 g := by
  classical
  have hK_event : ∀ᶠ n : ℕ in Filter.atTop, 4 < (n : ℝ) ^ (1 / 5 : ℝ) := by
    have ht := (tendsto_rpow_atTop (by norm_num : (0 : ℝ) < 1 / 5)).comp
      tendsto_natCast_atTop_atTop
    exact ht.eventually (Filter.eventually_gt_atTop 4)
  have hL_event : ∀ᶠ n : ℕ in Filter.atTop, 3 < (n : ℝ) ^ (3 / 10 : ℝ) := by
    have ht := (tendsto_rpow_atTop (by norm_num : (0 : ℝ) < 3 / 10)).comp
      tendsto_natCast_atTop_atTop
    exact ht.eventually (Filter.eventually_gt_atTop 3)
  have hOcc_event : ∀ᶠ n : ℕ in Filter.atTop, 304 < (n : ℝ) ^ (9 / 50 : ℝ) := by
    have ht := (tendsto_rpow_atTop (by norm_num : (0 : ℝ) < 9 / 50)).comp
      tendsto_natCast_atTop_atTop
    exact ht.eventually (Filter.eventually_gt_atTop 304)
  have hBin_event : ∀ᶠ n : ℕ in Filter.atTop, 4 < (n : ℝ) ^ (3 / 50 : ℝ) := by
    have ht := (tendsto_rpow_atTop (by norm_num : (0 : ℝ) < 3 / 50)).comp
      tendsto_natCast_atTop_atTop
    exact ht.eventually (Filter.eventually_gt_atTop 4)
  have hBoundary_event : ∀ᶠ n : ℕ in Filter.atTop, 4800 < (n : ℝ) ^ (1 / 100 : ℝ) := by
    have ht := (tendsto_rpow_atTop (by norm_num : (0 : ℝ) < 1 / 100)).comp
      tendsto_natCast_atTop_atTop
    exact ht.eventually (Filter.eventually_gt_atTop 4800)
  have hAll : ∀ᶠ n : ℕ in Filter.atTop,
      2 ≤ n ∧ 4 < (n : ℝ) ^ (1 / 5 : ℝ) ∧ 3 < (n : ℝ) ^ (3 / 10 : ℝ) ∧
        304 < (n : ℝ) ^ (9 / 50 : ℝ) ∧ 4 < (n : ℝ) ^ (3 / 50 : ℝ) ∧
          4800 < (n : ℝ) ^ (1 / 100 : ℝ) := by
    filter_upwards [Filter.eventually_ge_atTop 2, hK_event, hL_event, hOcc_event,
      hBin_event, hBoundary_event] with n hn hK hL hOcc hBin hBoundary
    exact ⟨hn, hK, hL, hOcc, hBin, hBoundary⟩
  obtain ⟨n₀, hn₀⟩ := Filter.eventually_atTop.1 hAll
  obtain ⟨nTail, hTail⟩ := Lane_q_s05_1b.fineSeverityTail α hα hα'
  obtain ⟨nBoundary, hBoundaryProof⟩ := Lane_q_s05_1b.coarseBoundaryFraction
  refine ⟨max n₀ (max nTail nBoundary), ?_⟩
  intro n hn
  have hnLayout : n₀ ≤ n := le_trans (Nat.le_max_left n₀ (max nTail nBoundary)) hn
  have hnTail : nTail ≤ n := by
    have hinner : nTail ≤ max nTail nBoundary := Nat.le_max_left nTail nBoundary
    have houter : max nTail nBoundary ≤ max n₀ (max nTail nBoundary) :=
      Nat.le_max_right n₀ (max nTail nBoundary)
    exact hinner.trans (houter.trans hn)
  have hnBoundary : nBoundary ≤ n := by
    have hinner : nBoundary ≤ max nTail nBoundary := Nat.le_max_right nTail nBoundary
    have houter : max nTail nBoundary ≤ max n₀ (max nTail nBoundary) :=
      Nat.le_max_right n₀ (max nTail nBoundary)
    exact hinner.trans (houter.trans hn)
  have hlarge := hn₀ n hnLayout
  have hn2 : 2 ≤ n := hlarge.1
  have hnR : 1 ≤ (n : ℝ) := by exact_mod_cast (by omega : 1 ≤ n)
  have hnRpos : 0 < (n : ℝ) := by positivity
  have hK : 4 < (n : ℝ) ^ (1 / 5 : ℝ) := hlarge.2.1
  have hL : 3 < (n : ℝ) ^ (3 / 10 : ℝ) := hlarge.2.2.1
  have hOcc : 304 < (n : ℝ) ^ (9 / 50 : ℝ) := hlarge.2.2.2.1
  have hBin : 4 < (n : ℝ) ^ (3 / 50 : ℝ) := hlarge.2.2.2.2.1
  have hBoundary : 4800 < (n : ℝ) ^ (1 / 100 : ℝ) := hlarge.2.2.2.2.2
  let m : ℕ := ⌈(n : ℝ) ^ α⌉₊
  let k : ℕ := ⌊(n : ℝ) ^ (1 / 5 : ℝ)⌋₊
  let ell : ℕ := 2 * ⌈(n : ℝ) ^ (3 / 10 : ℝ) / 2⌉₊ + 1
  have hm_cast : (m : ℝ) ≤ 2 * (n : ℝ) ^ (1 / 50 : ℝ) := by
    have hαpow : (n : ℝ) ^ α ≤ (n : ℝ) ^ (1 / 50 : ℝ) :=
      Real.rpow_le_rpow_of_exponent_le hnR hα'.le
    have hpowOne : 1 ≤ (n : ℝ) ^ (1 / 50 : ℝ) :=
      Real.one_le_rpow hnR (by norm_num)
    have hceil : (m : ℝ) < (n : ℝ) ^ α + 1 := by
      dsimp [m]
      exact Nat.ceil_lt_add_one (by positivity)
    linarith
  have hk_cast : (k : ℝ) ≤ (n : ℝ) ^ (1 / 5 : ℝ) := by
    dsimp [k]
    exact Nat.floor_le (by positivity)
  have hk_pos : 0 < k := by
    dsimp [k]
    exact Nat.floor_pos.mpr (by linarith)
  have hk_lower : (n : ℝ) ^ (1 / 5 : ℝ) / 2 ≤ (k : ℝ) := by
    have hfloor : (k : ℝ) = ⌊(n : ℝ) ^ (1 / 5 : ℝ)⌋₊ := by
      exact_mod_cast (show k = ⌊(n : ℝ) ^ (1 / 5 : ℝ)⌋₊ by rfl)
    rw [hfloor]
    have hlt := Nat.lt_floor_add_one ((n : ℝ) ^ (1 / 5 : ℝ))
    linarith
  have hell_lower : (n : ℝ) ^ (3 / 10 : ℝ) ≤ (ell : ℝ) := by
    have hc : (n : ℝ) ^ (3 / 10 : ℝ) / 2 ≤
        (⌈(n : ℝ) ^ (3 / 10 : ℝ) / 2⌉₊ : ℝ) := Nat.le_ceil _
    dsimp [ell]
    norm_num
    linarith
  have hell_upper : (ell : ℝ) ≤ 2 * (n : ℝ) ^ (3 / 10 : ℝ) := by
    have hc : (⌈(n : ℝ) ^ (3 / 10 : ℝ) / 2⌉₊ : ℝ) <
        (n : ℝ) ^ (3 / 10 : ℝ) / 2 + 1 :=
      Nat.ceil_lt_add_one (by positivity)
    dsimp [ell]
    norm_num
    linarith
  have hell_odd : Odd ell := by
    exact ⟨⌈(n : ℝ) ^ (3 / 10 : ℝ) / 2⌉₊, rfl⟩
  have husedCast : (300 * (k : ℝ) + (m : ℝ) * (ell : ℝ)) ≤ (n : ℝ) ^ (1 / 2 : ℝ) := by
    have hpowSmall : (n : ℝ) ^ (1 / 5 : ℝ) ≤ (n : ℝ) ^ (8 / 25 : ℝ) :=
      Real.rpow_le_rpow_of_exponent_le hnR (by norm_num)
    have hproduct : (n : ℝ) ^ (1 / 50 : ℝ) * (n : ℝ) ^ (3 / 10 : ℝ) =
        (n : ℝ) ^ (8 / 25 : ℝ) := by
      rw [← Real.rpow_add hnRpos]
      congr 1 <;> norm_num
    have hproduct4 :
        (2 * (n : ℝ) ^ (1 / 50 : ℝ)) * (2 * (n : ℝ) ^ (3 / 10 : ℝ)) =
          4 * (n : ℝ) ^ (8 / 25 : ℝ) := by
      calc
        (2 * (n : ℝ) ^ (1 / 50 : ℝ)) * (2 * (n : ℝ) ^ (3 / 10 : ℝ)) =
            4 * ((n : ℝ) ^ (1 / 50 : ℝ) * (n : ℝ) ^ (3 / 10 : ℝ)) := by ring
        _ = 4 * (n : ℝ) ^ (8 / 25 : ℝ) := by rw [hproduct]
    have hrough : 300 * (k : ℝ) + (m : ℝ) * (ell : ℝ) ≤
        304 * (n : ℝ) ^ (8 / 25 : ℝ) := by
      calc
        300 * (k : ℝ) + (m : ℝ) * (ell : ℝ) ≤
            300 * (n : ℝ) ^ (1 / 5 : ℝ) +
              (2 * (n : ℝ) ^ (1 / 50 : ℝ)) * (2 * (n : ℝ) ^ (3 / 10 : ℝ)) :=
          add_le_add (mul_le_mul_of_nonneg_left hk_cast (by norm_num))
            (mul_le_mul hm_cast hell_upper (by positivity) (by positivity))
        _ = 300 * (n : ℝ) ^ (1 / 5 : ℝ) + 4 * (n : ℝ) ^ (8 / 25 : ℝ) := by
          rw [hproduct4]
        _ ≤ 304 * (n : ℝ) ^ (8 / 25 : ℝ) := by nlinarith [hpowSmall]
    have hexp : (n : ℝ) ^ (8 / 25 : ℝ) * (n : ℝ) ^ (9 / 50 : ℝ) =
        (n : ℝ) ^ (1 / 2 : ℝ) := by
      rw [← Real.rpow_add hnRpos]
      congr 1 <;> norm_num
    calc
      300 * (k : ℝ) + (m : ℝ) * (ell : ℝ) ≤ 304 * (n : ℝ) ^ (8 / 25 : ℝ) := hrough
      _ ≤ (n : ℝ) ^ (9 / 50 : ℝ) * (n : ℝ) ^ (8 / 25 : ℝ) :=
        mul_le_mul_of_nonneg_right (le_of_lt hOcc) (by positivity)
      _ = (n : ℝ) ^ (1 / 2 : ℝ) := by rw [mul_comm, hexp]
  have husedNat : 300 * k + m * ell < n := by
    have hpowlt : (n : ℝ) ^ (1 / 2 : ℝ) < (n : ℝ) := by
      have hstrict : (n : ℝ) ^ (1 / 2 : ℝ) < (n : ℝ) ^ (1 : ℝ) :=
        Real.rpow_lt_rpow_of_exponent_lt
          (by exact_mod_cast (by omega : 1 < n)) (by norm_num)
      simpa [Real.rpow_one] using hstrict
    have hcast : ((300 * k + m * ell : ℕ) : ℝ) < (n : ℝ) := by
      calc
        ((300 * k + m * ell : ℕ) : ℝ) = 300 * (k : ℝ) + (m : ℝ) * (ell : ℝ) := by
          simp [Nat.cast_add, Nat.cast_mul]
        _ ≤ (n : ℝ) ^ (1 / 2 : ℝ) := husedCast
        _ < (n : ℝ) := hpowlt
    exact_mod_cast hcast
  let r := n - (300 * k + m * ell)
  have hparts : n = 300 * k + (m * ell + r) := by
    dsimp [r]
    omega
  let e := Lane_q_s05_1b.coordinateEquiv n k m ell r hparts
  let coarse := Lane_q_s05_1b.coarseBlock e
  let fine := Lane_q_s05_1b.fineBlock e
  let residual := Lane_q_s05_1b.residualBlock e
  have hrpos : 0 < r := by
    dsimp [r]
    omega
  have hεpos : 0 < (n : ℝ) ^ (-(4 / 100 : ℝ)) := by positivity
  have hεinv : 1 / (n : ℝ) ^ (-(4 / 100 : ℝ)) = (n : ℝ) ^ (4 / 100 : ℝ) := by
    rw [Real.rpow_neg hnRpos.le]
    simp [one_div]
  have hεpow_le : (n : ℝ) ^ (4 / 100 : ℝ) ≤ (n : ℝ) := by
    have h := Real.rpow_le_rpow_of_exponent_le hnR (by norm_num : (4 / 100 : ℝ) ≤ 1)
    simpa [Real.rpow_one] using h
  have hfloorLe : Nat.floor (1 / (n : ℝ) ^ (-(4 / 100 : ℝ))) ≤ n := by
    have hf : (Nat.floor (1 / (n : ℝ) ^ (-(4 / 100 : ℝ))) : ℝ) ≤ (n : ℝ) := by
      rw [hεinv]
      exact (Nat.floor_le (by positivity)).trans hεpow_le
    exact_mod_cast hf
  have hEpsSq : 4 ≤ (n : ℝ) ^ (-(4 / 100 : ℝ)) *
      (n : ℝ) ^ (-(4 / 100 : ℝ)) * (k : ℝ) := by
    have hpowMul : (n : ℝ) ^ (-(8 / 100 : ℝ)) *
        (n : ℝ) ^ (1 / 5 : ℝ) = (n : ℝ) ^ (12 / 100 : ℝ) := by
      rw [← Real.rpow_add hnRpos]
      congr 1 <;> norm_num
    have hpow : (n : ℝ) ^ (-(8 / 100 : ℝ)) *
        ((n : ℝ) ^ (1 / 5 : ℝ) / 2) =
          (n : ℝ) ^ (12 / 100 : ℝ) / 2 := by
      calc
        (n : ℝ) ^ (-(8 / 100 : ℝ)) * ((n : ℝ) ^ (1 / 5 : ℝ) / 2) =
            ((n : ℝ) ^ (-(8 / 100 : ℝ)) * (n : ℝ) ^ (1 / 5 : ℝ)) / 2 := by ring
        _ = (n : ℝ) ^ (12 / 100 : ℝ) / 2 := by rw [hpowMul]
    have hsquare : (n : ℝ) ^ (12 / 100 : ℝ) =
        ((n : ℝ) ^ (3 / 50 : ℝ)) ^ 2 := by
      calc
        (n : ℝ) ^ (12 / 100 : ℝ) =
            (n : ℝ) ^ ((3 / 50 : ℝ) + (3 / 50 : ℝ)) := by congr 1 <;> norm_num
        _ = (n : ℝ) ^ (3 / 50 : ℝ) * (n : ℝ) ^ (3 / 50 : ℝ) :=
          Real.rpow_add hnRpos _ _
        _ = ((n : ℝ) ^ (3 / 50 : ℝ)) ^ 2 := by ring
    have hlargePow : 8 ≤ (n : ℝ) ^ (12 / 100 : ℝ) := by
      rw [hsquare]
      nlinarith [hBin]
    have hεsq : (n : ℝ) ^ (-(4 / 100 : ℝ)) *
        (n : ℝ) ^ (-(4 / 100 : ℝ)) = (n : ℝ) ^ (-(8 / 100 : ℝ)) := by
      rw [← Real.rpow_add hnRpos]
      congr 1 <;> norm_num
    have hmono := mul_le_mul_of_nonneg_left hk_lower
      (sq_nonneg ((n : ℝ) ^ (-(4 / 100 : ℝ))))
    have hsq : ((n : ℝ) ^ (-(4 / 100 : ℝ))) ^ 2 =
        (n : ℝ) ^ (-(4 / 100 : ℝ)) * (n : ℝ) ^ (-(4 / 100 : ℝ)) := by ring
    rw [hsq, hεsq, hpow] at hmono
    nlinarith [hmono, hlargePow]
  have hCentral : 2 / Real.sqrt (k : ℝ) ≤ (n : ℝ) ^ (-(4 / 100 : ℝ)) := by
    have hsqrtPos : 0 < Real.sqrt (k : ℝ) := Real.sqrt_pos.2 (by exact_mod_cast hk_pos)
    have hsqrtSq : Real.sqrt (k : ℝ) ^ 2 = (k : ℝ) :=
      Real.sq_sqrt (by exact_mod_cast Nat.zero_le k)
    have hmul : 2 ≤ (n : ℝ) ^ (-(4 / 100 : ℝ)) * Real.sqrt (k : ℝ) := by
      apply le_of_sq_le_sq
      · rw [mul_pow, hsqrtSq]
        nlinarith [hEpsSq]
      · positivity
    exact (div_le_iff₀ hsqrtPos).2 hmul
  have hAtom : ∀ q : Fin (k + 1), halfBinomialMass k q ≤
      (n : ℝ) ^ (-(4 / 100 : ℝ)) := by
    intro q
    exact (centralBinomialUpper k hk_pos q.val (Nat.le_of_lt_succ q.isLt)).trans hCentral
  have hLabels := Lane_q_s06_front.quantileLabel_properties k
    ((n : ℝ) ^ (-(4 / 100 : ℝ))) hεpos hAtom
  let bin : Fin 300 → ℕ → Fin (n + 1) := fun i q =>
    ⟨Lane_q_s06_front.quantileLabel k ((n : ℝ) ^ (-(4 / 100 : ℝ))) q,
      Nat.lt_succ_of_le ((hLabels.2.2.1 q).trans hfloorLe)⟩
  have hbinTag (i : Fin 300) (q : ℕ) : (bin i q).val =
      Lane_q_s06_front.quantileLabel k ((n : ℝ) ^ (-(4 / 100 : ℝ))) q := rfl
  have hBinCount (i : Fin 300) :
      (((Finset.range (k + 1)).image (bin i)).card : ℝ) ≤
        (n : ℝ) ^ (4 / 100 : ℝ) + 1 := by
    let values := (Finset.range (k + 1)).image
      (Lane_q_s06_front.quantileLabel k ((n : ℝ) ^ (-(4 / 100 : ℝ))))
    have himage : ((Finset.range (k + 1)).image (bin i)).image Fin.val = values := by
      ext q
      simp [values, bin]
    have hcard : ((Finset.range (k + 1)).image (bin i)).card = values.card := by
      calc
        ((Finset.range (k + 1)).image (bin i)).card =
            (((Finset.range (k + 1)).image (bin i)).image Fin.val).card := by
              symm
              exact Finset.card_image_of_injective _ Fin.val_injective
        _ = values.card := congrArg Finset.card himage
    change (((Finset.range (k + 1)).image (bin i)).card : ℝ) ≤
      (n : ℝ) ^ (4 / 100 : ℝ) + 1
    calc
      (((Finset.range (k + 1)).image (bin i)).card : ℝ) = (values.card : ℝ) := by
        exact_mod_cast hcard
      _ ≤ ((n : ℝ) ^ (-(4 / 100 : ℝ)))⁻¹ + 1 := by
        simpa [one_div] using hLabels.2.2.2.2
      _ = (n : ℝ) ^ (4 / 100 : ℝ) + 1 := by
        rw [Real.rpow_neg hnRpos.le]
        simp [one_div]
  have hoccupied :
      (((Finset.univ.biUnion coarse) ∪ (Finset.univ.biUnion fine)).card : ℝ) ≤
        (n : ℝ) ^ (1 / 2 : ℝ) := by
    let C := Finset.univ.biUnion coarse
    let F := Finset.univ.biUnion fine
    have hC : C.card ≤ 300 * k := by
      calc
        C.card ≤ ∑ i : Fin 300, (coarse i).card := Finset.card_biUnion_le
        _ = 300 * k := by simp [coarse, Lane_q_s05_1b.coarseBlock_card]
    have hF : F.card ≤ m * ell := by
      calc
        F.card ≤ ∑ i : Fin m, (fine i).card := Finset.card_biUnion_le
        _ = m * ell := by simp [fine, Lane_q_s05_1b.fineBlock_card]
    have hnat : (C ∪ F).card ≤ 300 * k + m * ell := by
      calc
        (C ∪ F).card ≤ C.card + F.card := Finset.card_union_le _ _
        _ ≤ 300 * k + m * ell := Nat.add_le_add hC hF
    have hreal : ((C ∪ F).card : ℝ) ≤
        300 * (k : ℝ) + (m : ℝ) * (ell : ℝ) := by
      exact_mod_cast hnat
    change ((C ∪ F).card : ℝ) ≤ (n : ℝ) ^ (1 / 2 : ℝ)
    exact hreal.trans husedCast
  let g : ChunkGeometry5 n m := {
    fineLength := ell
    coarseChunks := coarse
    fineChunks := fine
    residual := residual
    chunks_disjoint := by
      refine ⟨?_, ?_, ?_, ?_, ?_⟩
      · intro i j hij
        exact Lane_q_s05_1b.coarseBlocks_disjoint e i j hij
      · intro i j
        exact Lane_q_s05_1b.coarseFine_disjoint e i j
      · intro i j hij
        exact Lane_q_s05_1b.fineBlocks_disjoint e i j hij
      · intro i
        exact Lane_q_s05_1b.coarseResidual_disjoint e i
      · intro i
        exact Lane_q_s05_1b.fineResidual_disjoint e i
    chunks_cover := Lane_q_s05_1b.blocks_cover e
    occupied_sublinear := hoccupied
    coarse_length := by
      intro i
      rw [show (coarse i).card = k from Lane_q_s05_1b.coarseBlock_card e i]
    bin := bin
    bin_monotone := by
      intro i a b hab
      change Lane_q_s06_front.quantileLabel k ((n : ℝ) ^ (-(4 / 100 : ℝ))) a ≤
        Lane_q_s06_front.quantileLabel k ((n : ℝ) ^ (-(4 / 100 : ℝ))) b
      exact hLabels.1 a b hab
    bin_consecutive := by
      intro i a
      change Lane_q_s06_front.quantileLabel k ((n : ℝ) ^ (-(4 / 100 : ℝ))) (a + 1) ≤
        Lane_q_s06_front.quantileLabel k ((n : ℝ) ^ (-(4 / 100 : ℝ))) a + 1
      exact hLabels.2.1 a
    bin_probability_bound := by
      intro i j
      rw [show (coarse i).card = k from Lane_q_s05_1b.coarseBlock_card e i]
      simpa [bin, Fin.ext_iff] using hLabels.2.2.2.1 j.val
    fine_length_odd := by simpa [ell] using hell_odd
    fine_length_lower := hell_lower
    fine_length_upper := hell_upper
    fine_chunk_length := by
      intro i
      simp [fine, ell, Lane_q_s05_1b.fineBlock_card]
    residual_nonempty := by
      let j : Fin r := ⟨0, hrpos⟩
      refine ⟨e.symm (.inr (.inr j)), ?_⟩
      exact Finset.mem_image.mpr ⟨j, Finset.mem_univ _, rfl⟩
  }
  let fineLayout : Lane_q_s05_1b.FineLayout n := {
    m := m
    fineLength := ell
    coarseChunks := coarse
    fineChunks := fine
    residual := residual
    chunks_disjoint := by
      refine ⟨?_, ?_, ?_, ?_, ?_⟩
      · intro i j hij
        exact Lane_q_s05_1b.coarseBlocks_disjoint e i j hij
      · intro i j
        exact Lane_q_s05_1b.coarseFine_disjoint e i j
      · intro i j hij
        exact Lane_q_s05_1b.fineBlocks_disjoint e i j hij
      · intro i
        exact Lane_q_s05_1b.coarseResidual_disjoint e i
      · intro i
        exact Lane_q_s05_1b.fineResidual_disjoint e i
    fine_length_lower := hell_lower
    fine_chunk_length := by
      intro i
      simp [fine, ell, Lane_q_s05_1b.fineBlock_card]
  }
  let coarseLayout : Lane_q_s05_1b.CoarseLayout n := {
    coarseChunks := coarse
    bin := bin
    coarseChunks_disjoint := by
      intro i j hij
      exact Lane_q_s05_1b.coarseBlocks_disjoint e i j hij
    coarse_length := by
      intro i
      rw [show (coarse i).card = k from Lane_q_s05_1b.coarseBlock_card e i]
    bin_monotone := by
      intro i a b hab
      change Lane_q_s06_front.quantileLabel k ((n : ℝ) ^ (-(4 / 100 : ℝ))) a ≤
        Lane_q_s06_front.quantileLabel k ((n : ℝ) ^ (-(4 / 100 : ℝ))) b
      exact hLabels.1 a b hab
    bin_count := by
      intro i
      rw [show (coarse i).card = k from Lane_q_s05_1b.coarseBlock_card e i]
      have hexp : (1 / 25 : ℝ) = 4 / 100 := by norm_num
      simpa only [hexp] using hBinCount i
  }
  have hSignUniform (b : Bool) (t : CubeVertex m) :
      ((Finset.univ.filter fun x : CubeVertex n =>
        decide (IsEvenRole x) = b ∧ g.sign x = t).card : ℝ) * (2 : ℝ) ^ m =
        ((Finset.univ.filter fun x : CubeVertex n => decide (IsEvenRole x) = b).card : ℝ) := by
    let signFiber (u : CubeVertex m) : Finset (CubeVertex n) :=
      Finset.univ.filter fun x => decide (IsEvenRole x) = b ∧ g.sign x = u
    let parityFiber : Finset (CubeVertex n) :=
      Finset.univ.filter fun x => decide (IsEvenRole x) = b
    have hFineLength : g.fineLength = ell := rfl
    have hFineChunkLength (i : Fin m) : (g.fineChunks i).card = ell := by
      simpa [hFineLength] using g.fine_chunk_length i
    obtain ⟨pivot, hpivot⟩ := g.residual_nonempty
    have fiberCardEq (u v : CubeVertex m) : (signFiber u).card = (signFiber v).card := by
      let D := Finset.univ.filter fun i : Fin m => u i ≠ v i
      let U := D.biUnion g.fineChunks
      let S := U ∪ if Odd D.card then {pivot} else ∅
      let toggle : CubeVertex n → CubeVertex n := fun x a => if a ∈ S then !x a else x a
      have hDisjoint : (D : Set (Fin m)).PairwiseDisjoint g.fineChunks := by
        intro i hi j hj hij
        exact g.chunks_disjoint.2.2.1 i j hij
      have hUcard : U.card = D.card * ell := by
        calc
          U.card = ∑ i ∈ D, (g.fineChunks i).card := Finset.card_biUnion hDisjoint
          _ = ∑ i ∈ D, ell := by
            apply Finset.sum_congr rfl
            intro i hi
            exact hFineChunkLength i
          _ = D.card * ell := by simp
      have hnotPivot : pivot ∉ U := by
        intro hp
        rcases Finset.mem_biUnion.mp hp with ⟨i, hi, hip⟩
        exact (Finset.disjoint_left.mp (g.chunks_disjoint.2.2.2.2 i)) hip hpivot
      have hdisjPivot : Disjoint U {pivot} := by
        apply Finset.disjoint_left.mpr
        intro a ha hap
        have hEq : a = pivot := Finset.mem_singleton.mp hap
        subst a
        exact hnotPivot ha
      have hScard : S.card = D.card * ell + (if Odd D.card then 1 else 0) := by
        by_cases ho : Odd D.card
        · calc
            S.card = (U ∪ ({pivot} : Finset (Fin n))).card := by simp [S, ho]
            _ = U.card + ({pivot} : Finset (Fin n)).card := Finset.card_union_of_disjoint hdisjPivot
            _ = D.card * ell + (if Odd D.card then 1 else 0) := by simp [hUcard, ho]
        · calc
            S.card = U.card := by simp [S, ho]
            _ = D.card * ell := hUcard
            _ = D.card * ell + (if Odd D.card then 1 else 0) := by simp [ho]
      have hSeven : Even S.card := by
        rcases Nat.even_or_odd D.card with hEven | hOdd
        · have hnotOdd : ¬ Odd D.card := by
            intro ho
            rcases hEven with ⟨a, ha⟩
            rcases ho with ⟨c, hc⟩
            omega
          rw [hScard]
          simp [hnotOdd]
          exact Even.mul_right hEven ell
        · have hOddProof := hOdd
          rcases hOdd with ⟨a, ha⟩
          rcases hell_odd with ⟨c, hc⟩
          rw [hScard]
          simp [hOddProof]
          refine ⟨2 * a * c + a + c + 1, ?_⟩
          rw [ha, hc]
          ring
      have toggleInvol (x : CubeVertex n) : toggle (toggle x) = x := by
        funext a
        by_cases ha : a ∈ S <;> simp [toggle, ha]
      have parityToggle (x : CubeVertex n) : IsEvenRole (toggle x) ↔ IsEvenRole x := by
        let A := Finset.univ.filter fun a : Fin n => x a = true
        let B := A ∩ S
        let C := A \ S
        let T := S \ A
        let A' := Finset.univ.filter fun a : Fin n => toggle x a = true
        have hA' : A' = C ∪ T := by
          ext a
          by_cases haS : a ∈ S <;> by_cases hax : x a = true <;>
            simp [A', A, C, T, toggle, haS, hax]
        have hdisj : Disjoint C T := by
          apply Finset.disjoint_left.mpr
          intro a ha hb
          exact (Finset.mem_sdiff.mp ha).2 (Finset.mem_sdiff.mp hb).1
        have hAparts : A.card = B.card + C.card := by
          dsimp [B, C]
          exact (Finset.card_inter_add_card_sdiff A S).symm
        have hSparts : S.card = B.card + T.card := by
          have hSA : S ∩ A = B := by
            rw [Finset.inter_comm]
          have hST : S \ A = T := rfl
          calc
            S.card = (S ∩ A).card + (S \ A).card :=
              (Finset.card_inter_add_card_sdiff S A).symm
            _ = B.card + T.card := by rw [hSA, hST]
        have hAnew : A'.card = C.card + T.card := by
          calc
            A'.card = (C ∪ T).card := congrArg Finset.card hA'
            _ = C.card + T.card := Finset.card_union_of_disjoint hdisj
        have hSEvenParts : Even (B.card + T.card) := by
          rw [← hSparts]
          exact hSeven
        change Even A'.card ↔ Even A.card
        rw [hAnew, hAparts]
        constructor
        · rintro ⟨q, hq⟩
          rcases hSEvenParts with ⟨s, hs⟩
          refine ⟨q + s - T.card, ?_⟩
          omega
        · rintro ⟨q, hq⟩
          rcases hSEvenParts with ⟨s, hs⟩
          refine ⟨q + s - B.card, ?_⟩
          omega
      have chunkInS (i : Fin m) (hi : i ∈ D) (a : Fin n)
          (ha : a ∈ g.fineChunks i) : a ∈ S := by
        exact Finset.mem_union_left _ (Finset.mem_biUnion.mpr ⟨i, hi, ha⟩)
      have chunkNotS (i : Fin m) (hi : i ∉ D) (a : Fin n)
          (ha : a ∈ g.fineChunks i) : a ∉ S := by
        intro has
        rcases Finset.mem_union.mp has with hu | hp
        · rcases Finset.mem_biUnion.mp hu with ⟨j, hj, haj⟩
          by_cases hji : j = i
          · subst j
            exact hi hj
          · exact (Finset.disjoint_left.mp
              (g.chunks_disjoint.2.2.1 i j (Ne.symm hji))) ha haj
        · by_cases ho : Odd D.card
          · have har : a = pivot := by simpa [ho] using hp
            subst a
            exact (Finset.disjoint_left.mp (g.chunks_disjoint.2.2.2.2 i)) ha hpivot
          · simp [ho] at hp
      have countComplement (x : CubeVertex n) (i : Fin m) (hi : i ∈ D) :
          g.fineCount (toggle x) i = ell - g.fineCount x i := by
        have hfilter : (g.fineChunks i).filter (fun a => toggle x a = true) =
            (g.fineChunks i).filter (fun a => x a = false) := by
          ext a
          by_cases ha : a ∈ g.fineChunks i
          · simp [toggle, chunkInS i hi a ha, ha]
          · simp [ha]
        have hfalseEq : (g.fineChunks i).filter (fun a => x a = false) =
            (g.fineChunks i).filter (fun a => ¬ x a = true) := by
          ext a
          simp
        have hsplit := Finset.card_filter_add_card_filter_not
          (s := g.fineChunks i) (fun a => x a = true)
        rw [← hfalseEq] at hsplit
        have hfalse : ((g.fineChunks i).filter (fun a => x a = false)).card +
            g.fineCount x i = (g.fineChunks i).card := by
          simpa [ChunkGeometry5.fineCount, add_comm] using hsplit
        unfold ChunkGeometry5.fineCount
        rw [hfilter]
        have hlen := hFineChunkLength i
        rw [hlen] at hfalse
        omega
      have countSame (x : CubeVertex n) (i : Fin m) (hi : i ∉ D) :
          g.fineCount (toggle x) i = g.fineCount x i := by
        unfold ChunkGeometry5.fineCount
        apply congrArg Finset.card
        ext a
        by_cases ha : a ∈ g.fineChunks i
        · simp [toggle, chunkNotS i hi a ha, ha]
        · simp [ha]
      have signFlipChunk (x : CubeVertex n) (i : Fin m) (hi : i ∈ D) :
          g.sign (toggle x) i = !g.sign x i := by
        have hc := countComplement x i hi
        have hcBound : g.fineCount x i ≤ ell := by
          calc
            g.fineCount x i ≤ (g.fineChunks i).card := Finset.card_filter_le _ _
            _ = ell := hFineChunkLength i
        change decide (ell < 2 * g.fineCount (toggle x) i) =
          !decide (ell < 2 * g.fineCount x i)
        rw [hc]
        by_cases hmajor : ell < 2 * g.fineCount x i
        · have hnot : ¬ ell < 2 * (ell - g.fineCount x i) := by omega
          simp [hmajor, hnot]
        · have hcomp : ell < 2 * (ell - g.fineCount x i) := by
            rcases hell_odd with ⟨c, hc⟩
            have hmajor' : ¬ 2 * c + 1 < 2 * g.fineCount x i := by
              simpa [hc] using hmajor
            have hcountle : g.fineCount x i ≤ c := by omega
            rw [hc]
            omega
          simp [hmajor, hcomp]
      have signSameChunk (x : CubeVertex n) (i : Fin m) (hi : i ∉ D) :
          g.sign (toggle x) i = g.sign x i := by
        simp [ChunkGeometry5.sign, countSame x i hi]
      have signToggle (x : CubeVertex n) :
          g.sign (toggle x) = fun i => if i ∈ D then !g.sign x i else g.sign x i := by
        funext i
        by_cases hi : i ∈ D
        · simp [hi, signFlipChunk x i hi]
        · simp [hi, signSameChunk x i hi]
      have signChange (a c : CubeVertex m) (x : CubeVertex n)
          (hx : g.sign x = a) (hD : ∀ i, i ∈ D ↔ a i ≠ c i) :
          g.sign (toggle x) = c := by
        funext i
        have hs := congrFun hx i
        by_cases hi : i ∈ D
        · have hneq := (hD i).mp hi
          cases ha : a i <;> cases hc : c i <;> simp_all [signToggle]
        · have heq : a i = c i := by
            by_contra hneq
            exact hi ((hD i).mpr hneq)
          simp [signToggle, hi, hs, heq]
      have hDuv : ∀ i, i ∈ D ↔ u i ≠ v i := by
        intro i
        simp [D]
      have hDvu : ∀ i, i ∈ D ↔ v i ≠ u i := by
        intro i
        simp [D, ne_comm]
      have mapTo' (x : CubeVertex n) (hx : x ∈ signFiber u) : toggle x ∈ signFiber v := by
        rcases (Finset.mem_filter.mp hx).2 with ⟨hp, hs⟩
        apply Finset.mem_filter.mpr
        refine ⟨Finset.mem_univ _, ?_⟩
        constructor
        · cases b
          · simp only [decide_eq_false_iff_not]
            intro he
            have hnot : ¬ IsEvenRole x := by simpa using hp
            exact hnot ((parityToggle x).mp he)
          · simp only [decide_eq_true_eq]
            have heven : IsEvenRole x := by simpa using hp
            exact (parityToggle x).mpr heven
        · exact signChange u v x hs hDuv
      have mapFrom' (x : CubeVertex n) (hx : x ∈ signFiber v) : toggle x ∈ signFiber u := by
        rcases (Finset.mem_filter.mp hx).2 with ⟨hp, hs⟩
        apply Finset.mem_filter.mpr
        refine ⟨Finset.mem_univ _, ?_⟩
        constructor
        · cases b
          · simp only [decide_eq_false_iff_not]
            intro he
            have hnot : ¬ IsEvenRole x := by simpa using hp
            exact hnot ((parityToggle x).mp he)
          · simp only [decide_eq_true_eq]
            have heven : IsEvenRole x := by simpa using hp
            exact (parityToggle x).mpr heven
        · exact signChange v u x hs hDvu
      exact Finset.card_bij'
        (fun x _ => toggle x) (fun x _ => toggle x)
        mapTo' mapFrom' (fun x _ => toggleInvol x) (fun x _ => toggleInvol x)
    have hsum : parityFiber.card =
        ∑ u ∈ (Finset.univ : Finset (CubeVertex m)), (signFiber u).card := by
      calc
        parityFiber.card =
            ∑ u ∈ (Finset.univ : Finset (CubeVertex m)),
              (parityFiber.filter (fun x => g.sign x = u)).card :=
          Finset.card_eq_sum_card_fiberwise (f := g.sign) (s := parityFiber)
            (t := Finset.univ) (by intro x hx; exact Finset.mem_univ _)
        _ = ∑ u ∈ (Finset.univ : Finset (CubeVertex m)), (signFiber u).card := by
          apply Finset.sum_congr rfl
          intro u hu
          congr 1
          ext x
          simp only [Finset.mem_filter, Finset.mem_univ, true_and, signFiber, parityFiber]
    have hNat : parityFiber.card = 2 ^ m * (signFiber t).card := by
      calc
        parityFiber.card =
            ∑ u ∈ (Finset.univ : Finset (CubeVertex m)), (signFiber u).card := hsum
        _ = ∑ u ∈ (Finset.univ : Finset (CubeVertex m)), (signFiber t).card := by
          apply Finset.sum_congr rfl
          intro u hu
          exact (fiberCardEq t u).symm
        _ = Fintype.card (CubeVertex m) * (signFiber t).card := by simp
        _ = 2 ^ m * (signFiber t).card := by simp [OAI.HypercubeRamsey.card_cubeVertex]
    have hreal : (parityFiber.card : ℝ) =
        (2 : ℝ) ^ m * ((signFiber t).card : ℝ) := by exact_mod_cast hNat
    rw [hreal]
    dsimp [signFiber, parityFiber]
    ring
  have estimates : ChunkEstimates5 g := {
    sign_uniform := hSignUniform
    severity_tail := by
      intro h hh₁ hhm
      change ((Finset.univ.filter fun x : CubeVertex n => h ≤ fineLayout.severity x).card : ℝ) /
        (2 : ℝ) ^ n ≤ (n : ℝ) ^ (-(13 / 100 : ℝ) * h)
      exact hTail n hnTail fineLayout rfl h hh₁ hhm
    boundary_fraction := by
      change ((Finset.univ.filter fun x : CubeVertex n => coarseLayout.boundary x).card : ℝ) /
        (2 : ℝ) ^ n ≤ (n : ℝ) ^ (-(5 / 100 : ℝ))
      have hb := hBoundaryProof n hnBoundary coarseLayout
      have hexp : (-(1 / 20 : ℝ)) = -(5 / 100 : ℝ) := by norm_num
      simpa only [hexp] using hb
  }
  exact ⟨g, estimates⟩

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
  classical
  constructor
  · intro x y hadj
    have hadj_card : (Finset.univ.filter (fun a : Fin n => x a ≠ y a)).card = 1 := by
      change _root_.hammingDist x y = 1 at hadj
      simpa [_root_.hammingDist] using hadj
    obtain ⟨a, ha_eq⟩ := Finset.card_eq_one.mp hadj_card
    have hneq : x a ≠ y a := by
      have ha : a ∈ Finset.univ.filter (fun i : Fin n => x i ≠ y i) := by
        rw [ha_eq]
        simp
      exact (Finset.mem_filter.mp ha).2
    have hbits : ∀ b, b ≠ a → x b = y b := by
      intro b hba
      by_contra hne
      have hb : b ∈ Finset.univ.filter (fun i : Fin n => x i ≠ y i) := by
        simp [hne]
      rw [ha_eq] at hb
      exact hba (Finset.mem_singleton.mp hb)
    have hyflip : y = flipVertex5 x a := by
      funext b
      by_cases hba : b = a
      · subst b
        cases hx : x a <;> cases hy : y a <;> simp_all [flipVertex5]
      · simp only [flipVertex5, Function.update_of_ne hba]
        exact (hbits b hba).symm
    have hcategory (b : Fin n) :
        (∃ i, b ∈ g.coarseChunks i) ∨ (∃ i, b ∈ g.fineChunks i) ∨ b ∈ g.residual := by
      have hb : b ∈ Finset.univ := Finset.mem_univ _
      rw [← g.chunks_cover] at hb
      simpa [Finset.mem_biUnion] using hb
    have hfilter_eq {C : Finset (Fin n)} {u v : CubeVertex n}
        (h : ∀ b ∈ C, u b = v b) :
        C.filter (fun b => u b = true) = C.filter (fun b => v b = true) := by
      ext b
      simp only [Finset.mem_filter]
      constructor
      · rintro ⟨hb, hu⟩
        exact ⟨hb, (h b hb).symm ▸ hu⟩
      · rintro ⟨hb, hv⟩
        exact ⟨hb, (h b hb) ▸ hv⟩
    have hchunk_mem_coarseCoords (i : Fin coarseChunkCount5) (b : Fin n)
        (hb : b ∈ g.coarseChunks i) : b ∈ g.coarseCoords := by
      change b ∈ Finset.univ.biUnion g.coarseChunks
      exact Finset.mem_biUnion.mpr ⟨i, Finset.mem_univ _, hb⟩
    have hcoarseBin_eq_of_agree {u v : CubeVertex n}
        (h : ∀ b ∈ g.coarseCoords, u b = v b) :
        g.coarseBin u = g.coarseBin v := by
      funext i
      simp only [ChunkGeometry5.coarseBin]
      have hc : g.coarseCount u i = g.coarseCount v i := by
        unfold ChunkGeometry5.coarseCount
        congr 1
        apply hfilter_eq
        intro b hb
        exact h b (hchunk_mem_coarseCoords i b hb)
      rw [hc]
    have hkey_eq_of_agree {u v : CubeVertex n}
        (h : ∀ b ∈ g.coarseCoords, u b = v b) : g.key u = g.key v := by
      have hbin := hcoarseBin_eq_of_agree h
      have hboundary : g.boundary u ↔ g.boundary v := by
        unfold ChunkGeometry5.boundary
        constructor
        · rintro ⟨i, b, hb, hne'⟩
          have hbcoarse : b ∈ g.coarseCoords := by
            exact hchunk_mem_coarseCoords i b hb
          have hflipbits : ∀ c ∈ g.coarseCoords,
              flipVertex5 u b c = flipVertex5 v b c := by
            intro c hc
            by_cases hcb : c = b
            · subst c
              simp [flipVertex5, h b hbcoarse]
            · simp [flipVertex5, hcb, h c hc]
          have hflipbin := hcoarseBin_eq_of_agree hflipbits
          refine ⟨i, b, hb, ?_⟩
          intro heq
          apply hne'
          calc
            g.coarseBin (flipVertex5 u b) = g.coarseBin (flipVertex5 v b) := hflipbin
            _ = g.coarseBin v := heq
            _ = g.coarseBin u := hbin.symm
        · rintro ⟨i, b, hb, hne'⟩
          have hbcoarse : b ∈ g.coarseCoords := by
            exact hchunk_mem_coarseCoords i b hb
          have hflipbits : ∀ c ∈ g.coarseCoords,
              flipVertex5 u b c = flipVertex5 v b c := by
            intro c hc
            by_cases hcb : c = b
            · subst c
              simp [flipVertex5, h b hbcoarse]
            · simp [flipVertex5, hcb, h c hc]
          have hflipbin := hcoarseBin_eq_of_agree hflipbits
          refine ⟨i, b, hb, ?_⟩
          intro heq
          apply hne'
          calc
            g.coarseBin (flipVertex5 v b) = g.coarseBin (flipVertex5 u b) := hflipbin.symm
            _ = g.coarseBin u := heq
            _ = g.coarseBin v := hbin
      change (g.coarseBin u, decide (g.boundary u)) =
        (g.coarseBin v, decide (g.boundary v))
      have hprop : g.boundary u = g.boundary v := propext hboundary
      have hdec : decide (g.boundary u) = decide (g.boundary v) := by rw [hprop]
      exact Prod.ext hbin hdec
    have hrole_eq_keyAt (z : CubeVertex n) :
        g.roleKey J z = keyAt5 J (g.key z) (g.sign z) (g.severity z) := by
      by_cases hz : g.severity z ≤ J <;>
        simp [ChunkGeometry5.roleKey, keyAt5, hz]
    have hcount_eq_of_notMem (C : Finset (Fin n)) (hnot : a ∉ C) :
        ((C.filter fun b => x b = true).card =
          (C.filter fun b => y b = true).card) := by
      have hset : C.filter (fun b => x b = true) = C.filter (fun b => y b = true) :=
        hfilter_eq (by
          intro b hb
          have hba : b ≠ a := by
            intro h
            subst b
            exact hnot hb
          exact hbits b hba)
      exact congrArg Finset.card hset
    have hcount_step (C : Finset (Fin n)) (haC : a ∈ C) :
        (C.filter (fun b => x b = true)).card + 1 =
            (C.filter (fun b => y b = true)).card ∨
        (C.filter (fun b => y b = true)).card + 1 =
            (C.filter (fun b => x b = true)).card := by
      have hcases : (x a = false ∧ y a = true) ∨ (x a = true ∧ y a = false) := by
        cases hx : x a <;> cases hy : y a <;> simp_all
      rcases hcases with ⟨hx, hy⟩ | ⟨hx, hy⟩
      · have hset : C.filter (fun b => y b = true) =
            insert a (C.filter (fun b => x b = true)) := by
          ext b
          by_cases hba : b = a
          · subst b
            simp [haC, hx, hy]
          · simp only [Finset.mem_filter, Finset.mem_insert]
            simp [hba, hbits b hba]
        have hnot : a ∉ C.filter (fun b => x b = true) := by
          simp [Finset.mem_filter, haC, hx]
        left
        have hc := congrArg Finset.card hset
        rw [Finset.card_insert_of_notMem hnot] at hc
        omega
      · have hset : C.filter (fun b => x b = true) =
            insert a (C.filter (fun b => y b = true)) := by
          ext b
          by_cases hba : b = a
          · subst b
            simp [haC, hx, hy]
          · simp only [Finset.mem_filter, Finset.mem_insert]
            simp [hba, hbits b hba]
        have hnot : a ∉ C.filter (fun b => y b = true) := by
          simp [Finset.mem_filter, haC, hy]
        right
        have hc := congrArg Finset.card hset
        rw [Finset.card_insert_of_notMem hnot] at hc
        omega
    have hstep_center (c d L : ℕ) (hL : Odd L)
        (hstep : c + 1 = d ∨ d + 1 = c) :
        (L < 2 * c ↔ L < 2 * d) ∨
          ((Nat.dist (2 * c) L = 1 ∧ Nat.dist (2 * d) L = 1) ∧
            ((¬ L < 2 * c ∧ L < 2 * d) ∨ (L < 2 * c ∧ ¬ L < 2 * d))) := by
      obtain ⟨k, hk⟩ := hL
      rcases hstep with hstep | hstep
      · by_cases hc : L < 2 * c <;> by_cases hd : L < 2 * d
        · exact Or.inl ⟨fun _ => hd, fun _ => hc⟩
        · exfalso
          omega
        · right
          have hdist : Nat.dist (2 * c) L = 1 ∧ Nat.dist (2 * d) L = 1 := by
            constructor <;> simp [Nat.dist, hk] <;> omega
          exact ⟨hdist, Or.inl ⟨hc, hd⟩⟩
        · exact Or.inl ⟨fun h => (hc h).elim, fun h => (hd h).elim⟩
      · by_cases hd : L < 2 * d <;> by_cases hc : L < 2 * c
        · exact Or.inl ⟨fun _ => hd, fun _ => hc⟩
        · exfalso
          omega
        · right
          have hdist : Nat.dist (2 * c) L = 1 ∧ Nat.dist (2 * d) L = 1 := by
            constructor <;> simp [Nat.dist, hk] <;> omega
          exact ⟨hdist, Or.inr ⟨hc, hd⟩⟩
        · exact Or.inl ⟨fun h => (hc h).elim, fun h => (hd h).elim⟩
    have hseverity_relation (i₀ : Fin m)
        (hcounts : ∀ i, i ≠ i₀ → g.fineCount x i = g.fineCount y i) :
        g.severity x = g.severity y ∨
          g.severity y = g.severity x + 1 ∨
          g.severity x = g.severity y + 1 := by
      let FX := Finset.univ.filter (fun i : Fin m =>
        Nat.dist (2 * g.fineCount x i) g.fineLength ≤ 11)
      let FY := Finset.univ.filter (fun i : Fin m =>
        Nat.dist (2 * g.fineCount y i) g.fineLength ≤ 11)
      have hrest : FX.erase i₀ = FY.erase i₀ := by
        ext i
        by_cases hii : i = i₀
        · subst i
          simp
        · simp [FX, FY, hii, hcounts i hii]
      have hrestcard : (FX.erase i₀).card = (FY.erase i₀).card := congrArg Finset.card hrest
      have hcardX : FX.card = (FX.erase i₀).card + if i₀ ∈ FX then 1 else 0 := by
        by_cases hmem : i₀ ∈ FX
        · simpa [hmem] using (Finset.card_erase_add_one hmem).symm
        · simp [hmem, Finset.erase_eq_of_notMem hmem]
      have hcardY : FY.card = (FY.erase i₀).card + if i₀ ∈ FY then 1 else 0 := by
        by_cases hmem : i₀ ∈ FY
        · simpa [hmem] using (Finset.card_erase_add_one hmem).symm
        · simp [hmem, Finset.erase_eq_of_notMem hmem]
      have hseverityX : g.severity x = FX.card := by rfl
      have hseverityY : g.severity y = FY.card := by rfl
      rw [hseverityX, hseverityY, hcardX, hcardY, hrestcard]
      by_cases hx : i₀ ∈ FX <;> by_cases hy : i₀ ∈ FY <;> simp [hx, hy] <;> omega
    have hseverity_eq_of_center (i₀ : Fin m)
        (hcenter : Nat.dist (2 * g.fineCount x i₀) g.fineLength = 1 ∧
          Nat.dist (2 * g.fineCount y i₀) g.fineLength = 1)
        (hcounts : ∀ i, i ≠ i₀ → g.fineCount x i = g.fineCount y i) :
        g.severity x = g.severity y := by
      unfold ChunkGeometry5.severity
      congr 1
      ext i
      by_cases hii : i = i₀
      · subst i
        simp [hcenter]
      · simp [hcounts i hii]
    have hsign_ne_of_center (i₀ : Fin m)
        (horient : ((¬ g.fineLength < 2 * g.fineCount x i₀ ∧
          g.fineLength < 2 * g.fineCount y i₀) ∨
          (g.fineLength < 2 * g.fineCount x i₀ ∧
            ¬ g.fineLength < 2 * g.fineCount y i₀))) :
        g.sign x i₀ ≠ g.sign y i₀ := by
      intro heq
      change decide (g.fineLength < 2 * g.fineCount x i₀) =
        decide (g.fineLength < 2 * g.fineCount y i₀) at heq
      rcases horient with ⟨hx, hy⟩ | ⟨hx, hy⟩ <;> simp [hx, hy] at heq
    have hrole_mem_of_coarseRange (z : CubeVertex n)
        (hkeyRange : g.key z ∈ g.coarseRange x)
        (hsign : g.sign z = g.sign x) (hsev : g.severity z = g.severity x) :
        g.roleKey J z ∈ g.typeKeys J x := by
      rw [hrole_eq_keyAt z, hsign, hsev]
      by_cases hlow : g.severity x ≤ J
      · simp [ChunkGeometry5.typeKeys, hlow, keyAt5, hkeyRange]
      · simp [ChunkGeometry5.typeKeys, hlow, keyAt5, hkeyRange]
    have hrole_mem_of_severity (hlow : g.severity x ≤ J)
        (hkey : g.key x = g.key y) (hsign : g.sign x = g.sign y)
        (hsev : g.severity y = g.severity x + 1 ∨
          g.severity x = g.severity y + 1) :
        g.roleKey J y ∈ g.typeKeys J x := by
      rw [hrole_eq_keyAt y, hkey.symm, hsign.symm]
      have hjmem : g.severity y ∈
          ({g.severity x + 1} : Finset ℕ) ∪
            (if 0 < g.severity x then {g.severity x - 1} else ∅) := by
        rcases hsev with h | h
        · simp [h]
        · have hpos : 0 < g.severity x := by omega
          simp [h, hpos]
      unfold ChunkGeometry5.typeKeys
      rw [if_pos hlow]
      apply Finset.mem_union.mpr
      right
      apply Finset.mem_image.mpr
      exact ⟨g.severity y, hjmem, rfl⟩
    have hrole_mem_high (hkeyRange : g.key y ∈ g.coarseRange x)
        (hhighX : ¬ g.severity x ≤ J) (hhighY : ¬ g.severity y ≤ J) :
        g.roleKey J y ∈ g.typeKeys J x := by
      simp only [ChunkGeometry5.roleKey, dif_neg hhighY, ChunkGeometry5.typeKeys,
        if_neg hhighX, Finset.mem_image]
      exact ⟨g.key y, hkeyRange, rfl⟩
    have hrole_eq_optional (hkey : g.key x = g.key y)
        (hsign : g.sign x = g.sign y) (hxsev : g.severity x = J + 1)
        (hysev : g.severity y = J) :
        g.optionalKey J x = some (g.roleKey J y) := by
      simp [ChunkGeometry5.optionalKey, ChunkGeometry5.roleKey, hkey, hsign, hxsev, hysev]
    rcases hcategory a with hcoarse | hrest
    · obtain ⟨ic, haic⟩ := hcoarse
      rcases g.chunks_disjoint with ⟨_, hcf, _, _, _⟩
      have hcounts : ∀ i, g.fineCount x i = g.fineCount y i := by
        intro i
        have hnot : a ∉ g.fineChunks i := by
          intro hi
          exact (Finset.disjoint_left.mp (hcf ic i) haic hi).elim
        unfold ChunkGeometry5.fineCount
        exact hcount_eq_of_notMem (g.fineChunks i) hnot
      have hsign : g.sign y = g.sign x := by
        funext i
        simp [ChunkGeometry5.sign, hcounts i]
      have hsev : g.severity y = g.severity x := by
        simp [ChunkGeometry5.severity, hcounts]
      have hkeyRange : g.key y ∈ g.coarseRange x := by
        rw [hyflip]
        simp only [ChunkGeometry5.coarseRange, Finset.mem_insert]
        right
        exact Finset.mem_image.mpr
          ⟨a, hchunk_mem_coarseCoords ic a haic, rfl⟩
      exact Or.inl (hrole_mem_of_coarseRange y hkeyRange hsign hsev)
    · rcases hrest with hfine | haResidual
      · obtain ⟨i₀, hai₀⟩ := hfine
        rcases g.chunks_disjoint with ⟨_, hcf, hff, _, _⟩
        have haNotCoarse : a ∉ g.coarseCoords := by
          intro haC
          change a ∈ Finset.univ.biUnion g.coarseChunks at haC
          obtain ⟨i, hi, hai⟩ := Finset.mem_biUnion.mp haC
          exact (Finset.disjoint_left.mp (hcf i i₀) hai hai₀).elim
        have hagree : ∀ b ∈ g.coarseCoords, x b = y b := by
          intro b hb
          by_cases hba : b = a
          · subst b
            exact (haNotCoarse hb).elim
          · exact hbits b hba
        have hkey : g.key x = g.key y := hkey_eq_of_agree hagree
        have hkeyRange : g.key y ∈ g.coarseRange x := by
          rw [← hkey]
          simp [ChunkGeometry5.coarseRange]
        have hcounts : ∀ i, i ≠ i₀ → g.fineCount x i = g.fineCount y i := by
          intro i hii
          have hnot : a ∉ g.fineChunks i := by
            intro hai
            exact (Finset.disjoint_left.mp (hff i₀ i hii.symm) hai₀ hai).elim
          unfold ChunkGeometry5.fineCount
          exact hcount_eq_of_notMem (g.fineChunks i) hnot
        have hstep : g.fineCount x i₀ + 1 = g.fineCount y i₀ ∨
            g.fineCount y i₀ + 1 = g.fineCount x i₀ := by
          simpa [ChunkGeometry5.fineCount] using hcount_step (g.fineChunks i₀) hai₀
        have hcenterOrSame := hstep_center (g.fineCount x i₀) (g.fineCount y i₀)
          g.fineLength g.fine_length_odd hstep
        have hsignRel : g.sign x = g.sign y ∨
            (Nat.dist (2 * g.fineCount x i₀) g.fineLength = 1 ∧
              Nat.dist (2 * g.fineCount y i₀) g.fineLength = 1 ∧
              ((¬ g.fineLength < 2 * g.fineCount x i₀ ∧
                  g.fineLength < 2 * g.fineCount y i₀) ∨
                (g.fineLength < 2 * g.fineCount x i₀ ∧
                  ¬ g.fineLength < 2 * g.fineCount y i₀))) := by
          rcases hcenterOrSame with hiff | ⟨hcenter, horient⟩
          · left
            have hdec : decide (g.fineLength < 2 * g.fineCount x i₀) =
                decide (g.fineLength < 2 * g.fineCount y i₀) := by
              by_cases hx : g.fineLength < 2 * g.fineCount x i₀
              · have hy : g.fineLength < 2 * g.fineCount y i₀ := hiff.mp hx
                simp [hx, hy]
              · have hy : ¬ g.fineLength < 2 * g.fineCount y i₀ := by
                  intro hy
                  exact hx (hiff.mpr hy)
                simp [hx, hy]
            have hsignAt : g.sign x i₀ = g.sign y i₀ := by
              change decide (g.fineLength < 2 * g.fineCount x i₀) =
                decide (g.fineLength < 2 * g.fineCount y i₀)
              exact hdec
            funext i
            by_cases hii : i = i₀
            · subst i
              exact hsignAt
            · simp [ChunkGeometry5.sign, hcounts i hii]
          · exact Or.inr ⟨hcenter.1, hcenter.2, horient⟩
        have hsevRel := hseverity_relation i₀ hcounts
        by_cases hlowX : g.severity x ≤ J
        · rcases hsignRel with hsign | ⟨hcenterX, hcenterY, horient⟩
          · rcases hsevRel with hsev | hsevUp | hsevDown
            · exact Or.inl (hrole_mem_of_coarseRange y hkeyRange hsign.symm hsev.symm)
            · exact Or.inl (hrole_mem_of_severity hlowX hkey hsign (Or.inl hsevUp))
            · exact Or.inl (hrole_mem_of_severity hlowX hkey hsign (Or.inr hsevDown))
          · have hcenter :
                Nat.dist (2 * g.fineCount x i₀) g.fineLength = 1 ∧
                  Nat.dist (2 * g.fineCount y i₀) g.fineLength = 1 :=
              ⟨hcenterX, hcenterY⟩
            have hsev : g.severity x = g.severity y :=
              hseverity_eq_of_center i₀ hcenter hcounts
            have hflip : i₀ ∈ g.flippable x := by
              simp [ChunkGeometry5.flippable, hcenterX]
            have hsignNe : g.sign x i₀ ≠ g.sign y i₀ := by
              exact hsign_ne_of_center i₀ horient
            have hsignUpdate : g.sign y =
                Function.update (g.sign x) i₀ (!g.sign x i₀) := by
              funext i
              by_cases hii : i = i₀
              · subst i
                cases hx : g.sign x i₀ <;> cases hy : g.sign y i₀ <;>
                  simp_all [hsignNe, Function.update]
              · have hc := hcounts i hii
                simp [ChunkGeometry5.sign, hc, Function.update_of_ne hii]
            have hmem : g.roleKey J y ∈ g.typeKeys J x := by
              rw [hrole_eq_keyAt y, hkey.symm, hsignUpdate, hsev.symm]
              unfold ChunkGeometry5.typeKeys
              rw [if_pos hlowX]
              apply Finset.mem_union.mpr
              left
              apply Finset.mem_union.mpr
              right
              apply Finset.mem_image.mpr
              exact ⟨i₀, hflip, rfl⟩
            exact Or.inl hmem
        · by_cases hlowY : g.severity y ≤ J
          · rcases hsevRel with hsev | hsevUp | hsevDown
            · omega
            · omega
            · have hxsev : g.severity x = J + 1 := by omega
              have hysev : g.severity y = J := by omega
              have hsign : g.sign x = g.sign y := by
                rcases hsignRel with hsign | ⟨hcenterX, hcenterY, _⟩
                · exact hsign
                · have hsevEq := hseverity_eq_of_center i₀ ⟨hcenterX, hcenterY⟩ hcounts
                  omega
              exact Or.inr (hrole_eq_optional hkey hsign hxsev hysev)
          · exact Or.inl (hrole_mem_high hkeyRange hlowX hlowY)
      · rcases g.chunks_disjoint with ⟨_, _, _, hcr, hfr⟩
        have haNotCoarse : a ∉ g.coarseCoords := by
          intro haC
          change a ∈ Finset.univ.biUnion g.coarseChunks at haC
          obtain ⟨i, hi, hai⟩ := Finset.mem_biUnion.mp haC
          exact (Finset.disjoint_left.mp (hcr i) hai haResidual).elim
        have hagree : ∀ b ∈ g.coarseCoords, x b = y b := by
          intro b hb
          by_cases hba : b = a
          · subst b
            exact (haNotCoarse hb).elim
          · exact hbits b hba
        have hkey : g.key x = g.key y := hkey_eq_of_agree hagree
        have hkeyRange : g.key y ∈ g.coarseRange x := by
          rw [← hkey]
          simp [ChunkGeometry5.coarseRange]
        have hcounts : ∀ i, g.fineCount x i = g.fineCount y i := by
          intro i
          have hnot : a ∉ g.fineChunks i := by
            intro hai
            exact (Finset.disjoint_left.mp (hfr i) hai haResidual).elim
          unfold ChunkGeometry5.fineCount
          exact hcount_eq_of_notMem (g.fineChunks i) hnot
        have hsign : g.sign y = g.sign x := by
          funext i
          simp [ChunkGeometry5.sign, hcounts i]
        have hsev : g.severity y = g.severity x := by
          simp [ChunkGeometry5.severity, hcounts]
        exact Or.inl (hrole_mem_of_coarseRange y hkeyRange hsign hsev)
  · intro x ℓ hℓ
    have hflip_invol (v : CubeVertex n) (a : Fin n) :
        flipVertex5 (flipVertex5 v a) a = v := by
      funext i
      by_cases hia : i = a
      · subst i
        simp [flipVertex5]
      · simp [flipVertex5, hia]
    have hcoarse_flip_step (v : CubeVertex n) (a : Fin n)
        (ha : a ∈ g.coarseCoords) :
        g.coarseBin v = g.coarseBin (flipVertex5 v a) ∨
          binAdjacent5 (g.coarseBin v) (g.coarseBin (flipVertex5 v a)) := by
      obtain ⟨k, hak⟩ := by
        simpa [ChunkGeometry5.coarseCoords, Finset.mem_biUnion] using ha
      rcases g.chunks_disjoint with ⟨hcc, hcf, hff, hcr, hfr⟩
      have hcount_eq (i : Fin coarseChunkCount5) (hik : i ≠ k) :
          g.coarseCount v i = g.coarseCount (flipVertex5 v a) i := by
        have hai : a ∉ g.coarseChunks i := by
          intro hmem
          exact (Finset.disjoint_left.mp (hcc k i hik.symm) hak hmem).elim
        unfold ChunkGeometry5.coarseCount
        have hset :
            (g.coarseChunks i).filter (fun b => v b = true) =
              (g.coarseChunks i).filter (fun b => flipVertex5 v a b = true) := by
          ext b
          by_cases hb : b ∈ g.coarseChunks i
          · have hba : b ≠ a := by
              intro h
              subst b
              exact hai hb
            simp only [Finset.mem_filter]
            simp only [flipVertex5, Function.update_of_ne hba]
          · simp [hb]
        exact congrArg Finset.card hset
      have hcount_step :
          g.coarseCount v k + 1 = g.coarseCount (flipVertex5 v a) k ∨
          g.coarseCount (flipVertex5 v a) k + 1 = g.coarseCount v k := by
        unfold ChunkGeometry5.coarseCount
        by_cases hva : v a = true
        · have hset :
              (g.coarseChunks k).filter (fun b => v b = true) =
                insert a ((g.coarseChunks k).filter
                  (fun b => flipVertex5 v a b = true)) := by
            ext b
            by_cases hba : b = a
            · subst b
              simp [hak, hva, flipVertex5]
            · simp only [Finset.mem_filter, Finset.mem_insert]
              simp only [flipVertex5, Function.update_of_ne hba]
              simp [hba]
          have hnot : a ∉ (g.coarseChunks k).filter (fun b => flipVertex5 v a b = true) := by
            simp [Finset.mem_filter, flipVertex5, hak, hva]
          right
          have hc := congrArg Finset.card hset
          rw [Finset.card_insert_of_notMem hnot] at hc
          omega
        · have hset :
              (g.coarseChunks k).filter (fun b => flipVertex5 v a b = true) =
                insert a ((g.coarseChunks k).filter (fun b => v b = true)) := by
            ext b
            by_cases hba : b = a
            · subst b
              simp [hak, hva, flipVertex5]
            · simp only [Finset.mem_filter, Finset.mem_insert]
              simp only [flipVertex5, Function.update_of_ne hba]
              simp [hba]
          have hnot : a ∉ (g.coarseChunks k).filter (fun b => v b = true) := by
            simp [Finset.mem_filter, hva, hak]
          left
          have hc := congrArg Finset.card hset
          rw [Finset.card_insert_of_notMem hnot] at hc
          omega
      have hval_pair :
          (g.bin k (g.coarseCount v k)).val ≤
              (g.bin k (g.coarseCount (flipVertex5 v a) k)).val + 1 ∧
            (g.bin k (g.coarseCount (flipVertex5 v a) k)).val ≤
              (g.bin k (g.coarseCount v k)).val + 1 := by
        rcases hcount_step with hstep | hstep
        · have hmono := g.bin_monotone k (g.coarseCount v k)
            (g.coarseCount (flipVertex5 v a) k) (by omega)
          have hcon := g.bin_consecutive k (g.coarseCount v k)
          rw [hstep] at hcon
          exact ⟨by omega, by omega⟩
        · have hmono := g.bin_monotone k (g.coarseCount (flipVertex5 v a) k)
            (g.coarseCount v k) (by omega)
          have hcon := g.bin_consecutive k (g.coarseCount (flipVertex5 v a) k)
          rw [hstep] at hcon
          exact ⟨by omega, by omega⟩
      have hdist : Nat.dist (g.bin k (g.coarseCount v k)).val
          (g.bin k (g.coarseCount (flipVertex5 v a) k)).val ≤ 1 := by
        rcases hval_pair with ⟨h1, h2⟩
        simp only [Nat.dist]
        omega
      by_cases heq : g.coarseBin v = g.coarseBin (flipVertex5 v a)
      · exact Or.inl heq
      · right
        have hkdiff :
            g.bin k (g.coarseCount v k) ≠
              g.bin k (g.coarseCount (flipVertex5 v a) k) := by
          intro hk
          apply heq
          funext i
          by_cases hik : i = k
          · subst i
            exact hk
          · simp [ChunkGeometry5.coarseBin, hcount_eq i hik]
        have hdiffSet :
            (Finset.univ.filter (fun i : Fin coarseChunkCount5 =>
              g.coarseBin v i ≠ g.coarseBin (flipVertex5 v a) i)) = {k} := by
          ext i
          simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_singleton]
          constructor
          · intro hi
            by_contra hik
            have heq' : g.coarseBin v i = g.coarseBin (flipVertex5 v a) i := by
              simp [ChunkGeometry5.coarseBin, hcount_eq i hik]
            exact hi heq'
          · intro hik
            subst i
            exact hkdiff
        refine ⟨?_, ?_⟩
        · rw [hdiffSet]
          simp
        · intro i
          by_cases hik : i = k
          · subst i
            exact hdist
          · have heq' : g.coarseBin v i = g.coarseBin (flipVertex5 v a) i := by
              simp [ChunkGeometry5.coarseBin, hcount_eq i hik]
            rw [heq']
            simp
    have hcoarseBin_compatible : ∀ v (i : CoarseKey5 n),
        i ∈ g.coarseRange v → (g.key v).1 ∈ binList5 i := by
      intro v i hi
      simp only [ChunkGeometry5.coarseRange, Finset.mem_insert, Finset.mem_image] at hi
      rcases hi with hbase | ⟨a, ha, rfl⟩
      · subst i
        by_cases hb : (g.key v).2 = true <;> simp [binList5, hb]
      · by_cases hb : g.boundary (flipVertex5 v a)
        · have hbin := hcoarse_flip_step v a ha
          have hi2 : (g.key (flipVertex5 v a)).2 = true := by
            simp [ChunkGeometry5.key, hb]
          simp only [binList5, hi2, if_pos, Finset.mem_filter, Finset.mem_univ, true_and]
          rcases hbin with heq | hadj
          · left
            exact (by simpa [ChunkGeometry5.key] using heq)
          · right
            have hsymm : binAdjacent5 (g.coarseBin (flipVertex5 v a)) (g.coarseBin v) := by
              unfold binAdjacent5 at hadj ⊢
              refine ⟨?_, ?_⟩
              · simpa [ne_comm] using hadj.1
              · intro i
                simpa [Nat.dist_comm] using hadj.2 i
            exact (by simpa [ChunkGeometry5.key] using hsymm)
        · have haChunks : ∃ k, a ∈ g.coarseChunks k := by
            simpa [ChunkGeometry5.coarseCoords, Finset.mem_biUnion] using ha
          obtain ⟨k, hak⟩ := haChunks
          have hbin : g.coarseBin v = g.coarseBin (flipVertex5 v a) := by
            by_contra hne
            apply hb
            exact ⟨k, a, hak, by simpa [hflip_invol] using hne⟩
          simp [binList5, ChunkGeometry5.key, hb, hbin]
    have hcoarse_keyAt (i : CoarseKey5 n) (t : CubeVertex m) (j : ℕ) :
        (keyAt5 J i t j).coarse = i := by
      by_cases hj : j ≤ J <;> simp [HiddenKey5.coarse, keyAt5, hj]
    have hsource : ℓ.coarse ∈ g.coarseRange x ∨ ℓ.coarse = g.key x := by
      unfold ChunkGeometry5.typeKeys at hℓ
      by_cases hlow : g.severity x ≤ J
      · rw [if_pos hlow] at hℓ
        simp only [Finset.mem_union, Finset.mem_image] at hℓ
        rcases hℓ with (⟨i, hi, heq⟩ | ⟨i, hi, heq⟩) | htail
        · left
          have heq' := congrArg HiddenKey5.coarse heq
          have hci : i = ℓ.coarse := by
            rw [hcoarse_keyAt] at heq'
            exact heq'
          rw [← hci]
          exact hi
        · right
          have heq' := congrArg HiddenKey5.coarse heq
          rw [hcoarse_keyAt] at heq'
          exact heq'.symm
        · right
          obtain ⟨j, hj, heq⟩ := htail
          have heq' := congrArg HiddenKey5.coarse heq
          rw [hcoarse_keyAt] at heq'
          exact heq'.symm
      · rw [if_neg hlow] at hℓ
        simp only [Finset.mem_image] at hℓ
        obtain ⟨i, hi, heq⟩ := hℓ
        left
        have heq' := congrArg HiddenKey5.coarse heq
        have hci : i = ℓ.coarse := by simpa [HiddenKey5.coarse] using heq'
        rw [← hci]
        exact hi
    rcases hsource with hrange | hkey
    · exact hcoarseBin_compatible x ℓ.coarse hrange
    · rw [hkey]
      exact hcoarseBin_compatible x (g.key x) (by simp [ChunkGeometry5.coarseRange])

/-! ### D5.5: states and the one-hot embedding (05:291–313) -/

/-- The outer representative of a fine count: merge distances `5.5` and `6.5` on the same side
of mid-weight (05:291–303). -/
def mergedFineCount5 (L q : ℕ) : ℕ :=
  if Nat.dist (2 * q) L = 11 then (if 2 * q < L then q - 1 else q + 1) else q

/-- The state quotient (05:291–313). Equal residual bits, coarse counts, merged fine counts and severity
determine a state. Roles in one state share key, signs, severity, parity and even type;
the one-hot embedding is injective, reproduces the residual bits, has dimension
`n + O(√n)`, and two even states adjacent to one odd state are at ambient distance at most `8`. -/
structure CubeStates5 {n m : ℕ} (g : ChunkGeometry5 n m) (J : ℕ) where
  Site : Type
  [siteFintype : Fintype Site]
  [siteDecEq : DecidableEq Site]
  d : ℕ
  stateOf : CubeVertex n → Site
  oneHot : Site → CubeVertex d
  oneHot_injective : Function.Injective oneHot
  /-- The one-hot fine-count coordinates separate different majority signs (05:291–313,
  978–985), so short state tubes consult only nearby low-key signs. -/
  sign_distance : ∀ x y, hammingDist (g.sign x) (g.sign y) ≤
    hammingDist (oneHot (stateOf x)) (oneHot (stateOf y))
  resCoord : g.residual → Fin d
  resCoord_injective : Function.Injective resCoord
  oneHot_residual : ∀ x (a : g.residual), oneHot (stateOf x) (resCoord a) = x a.1
  state_determines : ∀ x y, stateOf x = stateOf y →
    g.key x = g.key y ∧ g.sign x = g.sign y ∧ g.severity x = g.severity y ∧
      (IsEvenRole x ↔ IsEvenRole y) ∧ g.evenType J x = g.evenType J y ∧
        g.optionalKey J x = g.optionalKey J y ∧ g.roleKey J x = g.roleKey J y
  data_determine_state : ∀ x y,
    (∀ a ∈ g.residual, x a = y a) →
    (∀ i, g.coarseCount x i = g.coarseCount y i) →
    (∀ i, mergedFineCount5 g.fineLength (g.fineCount x i) =
      mergedFineCount5 g.fineLength (g.fineCount y i)) →
    g.severity x = g.severity y → stateOf x = stateOf y
  neighbors : Site → Finset Site
  mem_neighbors : ∀ s t, t ∈ neighbors s ↔
    ∃ x y, stateOf x = s ∧ stateOf y = t ∧ (cube n).Adj x y
  degree_bound : ∀ s, (neighbors s).card ≤ 2 * n
  even_distance : ∀ b a a', a ∈ neighbors b → a' ∈ neighbors b →
    (∃ x, stateOf x = a ∧ IsEvenRole x) → (∃ x, stateOf x = a' ∧ IsEvenRole x) →
      hammingDist (oneHot a) (oneHot a') ≤ 8
  dimension_upper : (d : ℝ) ≤ n + 3 * (n : ℝ) ^ (1 / 2 : ℝ) + 301

attribute [instance] CubeStates5.siteFintype CubeStates5.siteDecEq

set_option maxHeartbeats 1000000 in
/-- L5.1e0 (05:291–313), with the constants in the order `∀ ε, ∃ n₀`: the state quotient exists at every
layout, and its dimension is at most `(1 + ε) n` once `n ≥ n₀(ε)`. -/
theorem L5_1e0 : ∀ ε : ℝ, 0 < ε → ∃ n₀ : ℕ, ∀ n ≥ n₀, ∀ (m J : ℕ) (g : ChunkGeometry5 n m),
    ∃ S : CubeStates5 g J, (S.d : ℝ) ≤ (1 + ε) * n := by
  intro ε hε
  obtain ⟨n₀, hn₀⟩ := exists_nat_gt (max ((8 / ε) ^ 2) (602 / ε))
  refine ⟨max n₀ 100000, ?_⟩
  intro n hn m J g
  have hnlarge : (max n₀ 100000 : ℝ) ≤ n := by exact_mod_cast hn
  have hdimNeed : 3 * Real.sqrt (n : ℝ) + 301 ≤ ε * n := by
    have hn0 : max ((8 / ε) ^ 2) (602 / ε) < (n₀ : ℝ) := hn₀
    have hsqrt : 8 / ε ≤ Real.sqrt (n : ℝ) := by
      apply Real.le_sqrt_of_sq_le
      have hthreshold := le_trans (le_max_left ((8 / ε) ^ 2) (602 / ε)) (le_of_lt hn0)
      have hnCast : (n₀ : ℝ) ≤ n := by
        exact_mod_cast le_trans (le_max_left n₀ 100000) hn
      nlinarith [hthreshold]
    have hlarge : 602 / ε ≤ n := by
      have : (602 / ε) < (n₀ : ℝ) := lt_of_le_of_lt
        (le_max_right ((8 / ε) ^ 2) (602 / ε)) hn0
      have hn0le : (n₀ : ℝ) ≤ n := le_trans (le_max_left (n₀ : ℝ) 100000) hnlarge
      linarith
    have h1 : 3 * Real.sqrt (n : ℝ) ≤ (3 / 8) * ε * n := by
      have hscaled : (3 : ℝ) ≤ (3 / 8) * ε * Real.sqrt (n : ℝ) := by
        have h := (div_le_iff₀ hε).mp hsqrt
        nlinarith
      have hmul := mul_le_mul_of_nonneg_right hscaled (Real.sqrt_nonneg (n : ℝ))
      have hsq : (Real.sqrt (n : ℝ)) ^ 2 = n := Real.sq_sqrt (by positivity)
      nlinarith [hsq]
    have h2 : (301 : ℝ) ≤ (1 / 2) * ε * n := by
      have hepsn := (div_le_iff₀ hε).mp hlarge
      have hepsn' : (602 : ℝ) ≤ ε * n := by nlinarith [hepsn]
      nlinarith
    nlinarith
  classical
  let SiteData : Type :=
    (((g.residual → Bool) × (∀ i : Fin coarseChunkCount5,
        Fin ((g.coarseChunks i).card + 1))) ×
      ((∀ i : Fin m, Fin ((g.fineChunks i).card + 2)) × Fin (m + 1)))
  letI : Fintype SiteData := inferInstance
  let CoarseCoord : Type := Σ i : Fin coarseChunkCount5, Fin ((g.coarseChunks i).card + 1)
  let FineCoord : Type := Σ i : Fin m, Fin ((g.fineChunks i).card + 2)
  let Coord : Type := ((g.residual ⊕ CoarseCoord) ⊕ (FineCoord ⊕ Fin (m + 1)))
  letI : Fintype CoarseCoord := inferInstance
  letI : Fintype FineCoord := inferInstance
  letI : Fintype Coord := inferInstance
  let d : ℕ := Fintype.card Coord
  let coordEquiv : Coord ≃ Fin d := Fintype.equivFin Coord
  let dataOf : CubeVertex n → SiteData := fun x =>
    ((fun a => x a.1,
      fun i => ⟨g.coarseCount x i, by
        have h := Finset.card_filter_le (g.coarseChunks i) (fun a => x a = true)
        simpa [ChunkGeometry5.coarseCount] using h⟩),
      (fun i => ⟨mergedFineCount5 g.fineLength (g.fineCount x i), by
        have hcount : g.fineCount x i ≤ (g.fineChunks i).card := by
          exact Finset.card_filter_le _ _
        unfold mergedFineCount5
        by_cases hd : Nat.dist (2 * g.fineCount x i) g.fineLength = 11
        · split_ifs <;> omega
        · simp [hd]
          omega⟩,
        ⟨g.severity x, by
          have h := Finset.card_le_univ (s := Finset.univ.filter
            (fun i : Fin m => Nat.dist (2 * g.fineCount x i) g.fineLength ≤ 11))
          simpa [ChunkGeometry5.severity] using h⟩))
  let coordBit : SiteData → Coord → Bool := fun s c =>
    match c with
    | .inl (.inl a) => s.1.1 a
    | .inl (.inr c) => decide (s.1.2 c.1 = c.2)
    | .inr (.inl f) => decide (s.2.1 f.1 = f.2)
    | .inr (.inr j) => decide (s.2.2 = j)
  have cat_injective : ∀ {k : ℕ} (a b : Fin k),
      (∀ q : Fin k, decide (a = q) = decide (b = q)) → a = b := by
    intro k a b h
    by_contra hab
    have hh := h a
    simp [hab] at hh
    exact hab hh.symm
  let diffCoord : SiteData → SiteData → Finset Coord := fun s t =>
    Finset.univ.filter fun c => coordBit s c ≠ coordBit t c
  have hamming_code_eq (s t : SiteData) :
      _root_.hammingDist (fun k : Fin d => coordBit s (coordEquiv.symm k))
          (fun k : Fin d => coordBit t (coordEquiv.symm k)) = (diffCoord s t).card := by
    classical
    let e := coordEquiv
    let fromFinEq :
        {j : Fin d // (fun k : Fin d => coordBit s (e.symm k)) j =
          (fun k : Fin d => coordBit t (e.symm k)) j} ≃
        {c : Coord // coordBit s c = coordBit t c} := {
      toFun := fun j => ⟨e.symm j.1, by simpa using j.2⟩
      invFun := fun c => ⟨e c.1, by simpa using c.2⟩
      left_inv := by intro j; apply Subtype.ext; simp
      right_inv := by intro c; apply Subtype.ext; simp }
    have hEqCard := Fintype.card_congr fromFinEq
    have hroot :
        _root_.hammingDist (fun k : Fin d => coordBit s (e.symm k))
            (fun k : Fin d => coordBit t (e.symm k)) =
            (Finset.univ.filter fun k : Fin d =>
            coordBit s (e.symm k) ≠ coordBit t (e.symm k)).card := by
      unfold _root_.hammingDist
      rfl
    have hFinSum :
        _root_.hammingDist (fun k : Fin d => coordBit s (e.symm k))
            (fun k : Fin d => coordBit t (e.symm k)) +
          Fintype.card {j : Fin d //
            (fun k : Fin d => coordBit s (e.symm k)) j =
              (fun k : Fin d => coordBit t (e.symm k)) j} = Fintype.card (Fin d) := by
      have hsum := Finset.card_filter_add_card_filter_not (s := Finset.univ)
        (fun j : Fin d => (fun k => coordBit s (e.symm k)) j =
          (fun k => coordBit t (e.symm k)) j)
      let p : Fin d → Prop := fun j =>
        (fun k => coordBit s (e.symm k)) j = (fun k => coordBit t (e.symm k)) j
      have hsub : Fintype.card {j : Fin d // p j} = (Finset.univ.filter p).card :=
        Fintype.card_of_subtype (Finset.univ.filter p) (by intro j; simp)
      have hsumNe :
          (Finset.univ.filter (fun j : Fin d => ¬ p j)).card +
            (Finset.univ.filter p).card = (Finset.univ : Finset (Fin d)).card := by
        have hsum := Finset.card_filter_add_card_filter_not
          (s := (Finset.univ : Finset (Fin d))) p
        calc
          _ = (Finset.univ.filter p).card +
                (Finset.univ.filter (fun j : Fin d => ¬ p j)).card := Nat.add_comm _ _
          _ = (Finset.univ : Finset (Fin d)).card := hsum
      rw [hroot, hsub]
      change (Finset.univ.filter (fun j : Fin d => ¬ p j)).card +
        (Finset.univ.filter p).card = Fintype.card (Fin d)
      calc
        _ = (Finset.univ : Finset (Fin d)).card := hsumNe
        _ = Fintype.card (Fin d) := by simp
    have hCoordSum : (diffCoord s t).card +
        Fintype.card {c : Coord // coordBit s c = coordBit t c} = Fintype.card Coord := by
      have hsum := Finset.card_filter_add_card_filter_not (s := Finset.univ)
        (fun c : Coord => coordBit s c = coordBit t c)
      let p : Coord → Prop := fun c => coordBit s c = coordBit t c
      have hsub : Fintype.card {c : Coord // p c} = (Finset.univ.filter p).card :=
        Fintype.card_of_subtype (Finset.univ.filter p) (by intro c; simp)
      have hsumNe :
          (Finset.univ.filter (fun c : Coord => ¬ p c)).card +
            (Finset.univ.filter p).card = (Finset.univ : Finset Coord).card := by
        have hsum := Finset.card_filter_add_card_filter_not
          (s := (Finset.univ : Finset Coord)) p
        calc
          _ = (Finset.univ.filter p).card +
                (Finset.univ.filter (fun c : Coord => ¬ p c)).card := Nat.add_comm _ _
          _ = (Finset.univ : Finset Coord).card := hsum
      rw [hsub]
      change (Finset.univ.filter (fun c : Coord => ¬ p c)).card +
        (Finset.univ.filter p).card = Fintype.card Coord
      calc
        _ = (Finset.univ : Finset Coord).card := hsumNe
        _ = Fintype.card Coord := by simp
    have hTotal : Fintype.card (Fin d) = Fintype.card Coord := by
      change Fintype.card (Fin (Fintype.card Coord)) = Fintype.card Coord
      exact Fintype.card_fin _
    have hFinSum' := hFinSum
    rw [hEqCard, hTotal] at hFinSum'
    exact Nat.add_right_cancel (hFinSum'.trans hCoordSum.symm)
  have merged_side (q : ℕ) :
      (g.fineLength < 2 * q) =
        (g.fineLength < 2 * mergedFineCount5 g.fineLength q) := by
    unfold mergedFineCount5
    by_cases hd : Nat.dist (2 * q) g.fineLength = 11
    · by_cases hlow : 2 * q < g.fineLength
      · have hdist : g.fineLength - 2 * q = 11 := by
          simpa [Nat.dist_eq_sub_of_le (Nat.le_of_lt hlow)] using hd
        simp [hd, hlow] <;> omega
      · have hle : g.fineLength ≤ 2 * q := Nat.le_of_not_gt hlow
        have hdist : 2 * q - g.fineLength = 11 := by
          simpa [Nat.dist_eq_sub_of_le_right hle] using hd
        simp [hd, hlow] <;> omega
    · simp [hd]
  have signCode (z : CubeVertex n) (i : Fin m) :
      g.sign z i = decide (g.fineLength < 2 * mergedFineCount5 g.fineLength (g.fineCount z i)) := by
    change decide (g.fineLength < 2 * g.fineCount z i) = _
    have hProp := merged_side (g.fineCount z i)
    have hiff : (g.fineLength < 2 * g.fineCount z i) ↔
        g.fineLength < 2 * mergedFineCount5 g.fineLength (g.fineCount z i) := Iff.of_eq hProp
    by_cases hleft : g.fineLength < 2 * g.fineCount z i
    · have hright := hiff.mp hleft
      simp [hleft, hright]
    · have hright : ¬g.fineLength <
          2 * mergedFineCount5 g.fineLength (g.fineCount z i) :=
        fun hh => hleft (hiff.mpr hh)
      simp [hleft, hright]
  have hfilterOutside (A : Finset (Fin n)) (u : CubeVertex n) (a : Fin n)
      (ha : a ∉ A) :
      A.filter (fun b => flipVertex5 u a b = true) = A.filter (fun b => u b = true) := by
    ext b
    by_cases hba : b = a
    · subst b
      simp [ha]
    · have hf : flipVertex5 u a b = u b := by
        change Function.update u a (!u a) b = u b
        exact Function.update_of_ne hba _ _
      simp [hf]
  have hfineCountOutside (u : CubeVertex n) (a : Fin n) (i : Fin m)
      (ha : a ∉ g.fineChunks i) :
      g.fineCount (flipVertex5 u a) i = g.fineCount u i := by
    unfold ChunkGeometry5.fineCount
    rw [hfilterOutside (g.fineChunks i) u a ha]
  have hseveritySame {u v : CubeVertex n}
      (hcount : ∀ i : Fin m, g.fineCount u i = g.fineCount v i) :
      g.severity u = g.severity v := by
    unfold ChunkGeometry5.severity
    congr 1
    ext i
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    rw [hcount i]
  have hcategory (a : Fin n) :
      a ∈ g.residual ∨ (∃ i, a ∈ g.coarseChunks i) ∨ (∃ i, a ∈ g.fineChunks i) := by
    have ha : a ∈ (Finset.univ : Finset (Fin n)) := Finset.mem_univ _
    rw [← g.chunks_cover] at ha
    rcases Finset.mem_union.mp ha with hchunk | hres
    · rcases Finset.mem_union.mp hchunk with hcoarse | hfine
      · rcases Finset.mem_biUnion.mp hcoarse with ⟨i, _, hai⟩
        exact Or.inr (Or.inl ⟨i, hai⟩)
      · rcases Finset.mem_biUnion.mp hfine with ⟨i, _, hai⟩
        exact Or.inr (Or.inr ⟨i, hai⟩)
    · exact Or.inl hres
  have hcardFour (a b c d : Coord) :
      (insert a (insert b (insert c ({d} : Finset Coord)))).card ≤ 4 := by
    have h1 := Finset.card_insert_le a (insert b (insert c ({d} : Finset Coord)))
    have h2 := Finset.card_insert_le b (insert c ({d} : Finset Coord))
    have h3 := Finset.card_insert_le c ({d} : Finset Coord)
    have h4 : ({d} : Finset Coord).card = 1 := by simp
    omega
  have hflipCodeBound (u : CubeVertex n) (a : Fin n) :
      _root_.hammingDist (fun k : Fin d => coordBit (dataOf u) (coordEquiv.symm k))
          (fun k : Fin d => coordBit (dataOf (flipVertex5 u a)) (coordEquiv.symm k)) ≤ 4 := by
    rw [hamming_code_eq]
    rcases hcategory a with haRes | haCoarse | haFine
    · let c₀ : Coord := .inl (.inl ⟨a, haRes⟩)
      let Cand : Finset Coord := {c₀}
      have hsubset : diffCoord (dataOf u) (dataOf (flipVertex5 u a)) ⊆ Cand := by
        intro c hc
        simp only [diffCoord, Finset.mem_filter, Finset.mem_univ, true_and] at hc
        cases c with
        | inl left =>
          cases left with
          | inl r =>
            by_cases hr : r.1 = a
            · have hrEq : (⟨a, haRes⟩ : g.residual) = r := Subtype.ext hr.symm
              have hcEq : Sum.inl (Sum.inl r) = c₀ := by
                dsimp [c₀]
                exact congrArg (fun r : g.residual => (Sum.inl (Sum.inl r) : Coord)) hrEq.symm
              exact Finset.mem_singleton.mpr hcEq
            · have hsame : flipVertex5 u a r.1 = u r.1 := by
                change Function.update u a (!u a) r.1 = u r.1
                exact Function.update_of_ne hr _ _
              have heq : coordBit (dataOf u) (.inl (.inl r)) =
                  coordBit (dataOf (flipVertex5 u a)) (.inl (.inl r)) := by
                simp [coordBit, dataOf, hsame]
              exact (hc heq).elim
          | inr c' =>
            have hnot : a ∉ g.coarseChunks c'.1 := by
              intro hai
              exact (Finset.disjoint_left.mp (g.chunks_disjoint.2.2.2.1 c'.1))
                hai haRes
            have hcnt := hfilterOutside (g.coarseChunks c'.1) u a hnot
            have hcnt' : g.coarseCount (flipVertex5 u a) c'.1 = g.coarseCount u c'.1 := by
              unfold ChunkGeometry5.coarseCount
              exact congrArg Finset.card hcnt
            have heq : coordBit (dataOf u) (.inl (.inr c')) =
                coordBit (dataOf (flipVertex5 u a)) (.inl (.inr c')) := by
              simp [coordBit, dataOf, hcnt']
            exact (hc heq).elim
        | inr right =>
          cases right with
          | inl f =>
            have hnot : a ∉ g.fineChunks f.1 := by
              intro hai
              exact (Finset.disjoint_left.mp (g.chunks_disjoint.2.2.2.2 f.1))
                hai haRes
            have hcnt := hfineCountOutside u a f.1 hnot
            have hmergedEq :
                mergedFineCount5 g.fineLength (g.fineCount (flipVertex5 u a) f.1) =
                  mergedFineCount5 g.fineLength (g.fineCount u f.1) := by rw [hcnt]
            have heq : coordBit (dataOf u) (.inr (.inl f)) =
                coordBit (dataOf (flipVertex5 u a)) (.inr (.inl f)) := by
              simp [coordBit, dataOf, hmergedEq]
            exact (hc heq).elim
          | inr j =>
            have hcnt : ∀ i : Fin m, g.fineCount (flipVertex5 u a) i = g.fineCount u i := by
              intro i
              have hnot : a ∉ g.fineChunks i := by
                intro hai
                exact (Finset.disjoint_left.mp (g.chunks_disjoint.2.2.2.2 i)) hai haRes
              exact hfineCountOutside u a i hnot
            have hsev := hseveritySame (fun i => (hcnt i).symm)
            have heq : coordBit (dataOf u) (.inr (.inr j)) =
                coordBit (dataOf (flipVertex5 u a)) (.inr (.inr j)) := by
              simp [coordBit, dataOf, hsev]
            exact (hc heq).elim
      calc
        _ ≤ Cand.card := Finset.card_le_card hsubset
        _ ≤ 4 := by simp [Cand]
    · obtain ⟨i, hai⟩ := haCoarse
      let c₀ : Coord := .inl (.inr ⟨i, (dataOf u).1.2 i⟩)
      let c₁ : Coord := .inl (.inr ⟨i, (dataOf (flipVertex5 u a)).1.2 i⟩)
      let Cand : Finset Coord := insert c₀ {c₁}
      have hsubset : diffCoord (dataOf u) (dataOf (flipVertex5 u a)) ⊆ Cand := by
        intro c hc
        simp only [diffCoord, Finset.mem_filter, Finset.mem_univ, true_and] at hc
        cases c with
        | inl left =>
          cases left with
          | inl r =>
            have hnot : a ∉ g.residual := by
              intro har
              exact (Finset.disjoint_left.mp (g.chunks_disjoint.2.2.2.1 i)) hai har
            have hsame : flipVertex5 u a r.1 = u r.1 := by
              have hne : r.1 ≠ a := fun he => hnot (he ▸ r.2)
              change Function.update u a (!u a) r.1 = u r.1
              exact Function.update_of_ne hne _ _
            have heq : coordBit (dataOf u) (.inl (.inl r)) =
                coordBit (dataOf (flipVertex5 u a)) (.inl (.inl r)) := by
              simp [coordBit, dataOf, hsame]
            exact (hc heq).elim
          | inr c' =>
            rcases c' with ⟨j, q⟩
            by_cases hji : j = i
            · subst j
              change decide ((dataOf u).1.2 i = q) ≠
                decide ((dataOf (flipVertex5 u a)).1.2 i = q) at hc
              by_cases hq : (dataOf u).1.2 i = q
              · exact Finset.mem_insert.mpr (Or.inl (by simp [Cand, c₀, hq]))
              · have hq' : (dataOf (flipVertex5 u a)).1.2 i = q := by
                  by_contra hq'
                  exact hc (by simp [hq, hq'])
                exact Finset.mem_insert.mpr (Or.inr (by simp [Cand, c₁, hq']))
            · have hnot : a ∉ g.coarseChunks j := by
                intro haj
                exact (Finset.disjoint_left.mp (g.chunks_disjoint.1 i j (Ne.symm hji))) hai haj
              have hcnt := hfilterOutside (g.coarseChunks j) u a hnot
              have hcnt' : g.coarseCount (flipVertex5 u a) j = g.coarseCount u j := by
                unfold ChunkGeometry5.coarseCount
                exact congrArg Finset.card hcnt
              have heq : coordBit (dataOf u) (.inl (.inr ⟨j, q⟩)) =
                  coordBit (dataOf (flipVertex5 u a)) (.inl (.inr ⟨j, q⟩)) := by
                simp [coordBit, dataOf, hcnt']
              exact (hc heq).elim
        | inr right =>
          cases right with
          | inl f =>
            have hnot : a ∉ g.fineChunks f.1 := by
              intro haf
              exact (Finset.disjoint_left.mp (g.chunks_disjoint.2.1 i f.1)) hai haf
            have hcnt := hfineCountOutside u a f.1 hnot
            have hmergedEq :
                mergedFineCount5 g.fineLength (g.fineCount (flipVertex5 u a) f.1) =
                  mergedFineCount5 g.fineLength (g.fineCount u f.1) := by rw [hcnt]
            have heq : coordBit (dataOf u) (.inr (.inl f)) =
                coordBit (dataOf (flipVertex5 u a)) (.inr (.inl f)) := by
              simp [coordBit, dataOf, hmergedEq]
            exact (hc heq).elim
          | inr j =>
            have hcnt : ∀ k : Fin m, g.fineCount (flipVertex5 u a) k = g.fineCount u k := by
              intro k
              have hnot : a ∉ g.fineChunks k := by
                intro haf
                exact (Finset.disjoint_left.mp (g.chunks_disjoint.2.1 i k)) hai haf
              exact hfineCountOutside u a k hnot
            have hsev := hseveritySame (fun k => (hcnt k).symm)
            have heq : coordBit (dataOf u) (.inr (.inr j)) =
                coordBit (dataOf (flipVertex5 u a)) (.inr (.inr j)) := by
              simp [coordBit, dataOf, hsev]
            exact (hc heq).elim
      calc
        _ ≤ Cand.card := Finset.card_le_card hsubset
        _ ≤ 4 := by
          have hcard := Finset.card_insert_le c₀ ({c₁} : Finset Coord)
          simp [Cand] at hcard ⊢
          omega
    · obtain ⟨i, hai⟩ := haFine
      let f₀ : Coord := .inr (.inl ⟨i, (dataOf u).2.1 i⟩)
      let f₁ : Coord := .inr (.inl ⟨i, (dataOf (flipVertex5 u a)).2.1 i⟩)
      let j₀ : Coord := .inr (.inr (dataOf u).2.2)
      let j₁ : Coord := .inr (.inr (dataOf (flipVertex5 u a)).2.2)
      let Cand : Finset Coord := insert f₀ (insert f₁ (insert j₀ {j₁}))
      have hsubset : diffCoord (dataOf u) (dataOf (flipVertex5 u a)) ⊆ Cand := by
        intro c hc
        simp only [diffCoord, Finset.mem_filter, Finset.mem_univ, true_and] at hc
        cases c with
        | inl left =>
          cases left with
          | inl r =>
            have hnot : a ∉ g.residual := by
              intro har
              exact (Finset.disjoint_left.mp (g.chunks_disjoint.2.2.2.2 i)) hai har
            have hsame : flipVertex5 u a r.1 = u r.1 := by
              have hne : r.1 ≠ a := fun he => hnot (he ▸ r.2)
              change Function.update u a (!u a) r.1 = u r.1
              exact Function.update_of_ne hne _ _
            have heq : coordBit (dataOf u) (.inl (.inl r)) =
                coordBit (dataOf (flipVertex5 u a)) (.inl (.inl r)) := by
              simp [coordBit, dataOf, hsame]
            exact (hc heq).elim
          | inr c' =>
            have hnot : a ∉ g.coarseChunks c'.1 := by
              intro hac
              exact (Finset.disjoint_left.mp (g.chunks_disjoint.2.1 c'.1 i)) hac hai
            have hcnt := hfilterOutside (g.coarseChunks c'.1) u a hnot
            have hcnt' : g.coarseCount (flipVertex5 u a) c'.1 = g.coarseCount u c'.1 := by
              unfold ChunkGeometry5.coarseCount
              exact congrArg Finset.card hcnt
            have heq : coordBit (dataOf u) (.inl (.inr c')) =
                coordBit (dataOf (flipVertex5 u a)) (.inl (.inr c')) := by
              simp [coordBit, dataOf, hcnt']
            exact (hc heq).elim
        | inr right =>
          cases right with
          | inl f =>
            rcases f with ⟨j, q⟩
            by_cases hji : j = i
            · subst j
              change decide ((dataOf u).2.1 i = q) ≠
                decide ((dataOf (flipVertex5 u a)).2.1 i = q) at hc
              by_cases hq : (dataOf u).2.1 i = q
              · exact Finset.mem_insert.mpr (Or.inl (by simp [Cand, f₀, hq]))
              · have hq' : (dataOf (flipVertex5 u a)).2.1 i = q := by
                  by_contra hq'
                  exact hc (by simp [hq, hq'])
                exact Finset.mem_insert.mpr (Or.inr (Finset.mem_insert.mpr
                  (Or.inl (by simp [Cand, f₁, hq']))))
            · have hnot : a ∉ g.fineChunks j := by
                intro haf
                exact (Finset.disjoint_left.mp (g.chunks_disjoint.2.2.1 i j (Ne.symm hji))) hai haf
              have hcnt := hfineCountOutside u a j hnot
              have hmergedEq :
                  mergedFineCount5 g.fineLength (g.fineCount (flipVertex5 u a) j) =
                    mergedFineCount5 g.fineLength (g.fineCount u j) := by rw [hcnt]
              have heq : coordBit (dataOf u) (.inr (.inl ⟨j, q⟩)) =
                  coordBit (dataOf (flipVertex5 u a)) (.inr (.inl ⟨j, q⟩)) := by
                simp [coordBit, dataOf, hmergedEq]
              exact (hc heq).elim
          | inr j =>
            by_cases hj : j = (dataOf u).2.2
            · simp [Cand, j₀, hj]
            · have hj' : j = (dataOf (flipVertex5 u a)).2.2 := by
                by_contra hn
                apply hc
                simp [coordBit, dataOf, Ne.symm hj, Ne.symm hn]
              simp [Cand, j₁, hj']
      calc
        _ ≤ Cand.card := Finset.card_le_card hsubset
        _ ≤ 4 := by simpa [Cand] using hcardFour f₀ f₁ j₀ j₁
  have hflipSet (A : Finset (Fin n)) (u : CubeVertex n) (a : Fin n)
      (ha : a ∈ A) :
      A.filter (fun b => flipVertex5 u a b = true) =
        if u a then (A.filter fun b => u b = true).erase a
        else insert a (A.filter fun b => u b = true) := by
    ext b
    by_cases hba : b = a
    · subst b
      cases hbit : u a <;> simp [flipVertex5, hbit, ha]
    · cases hbit : u a <;> simp [flipVertex5, hbit, hba]
  have hcountFlipBlock (A : Finset (Fin n)) (u : CubeVertex n) (a : Fin n)
      (ha : a ∈ A) :
      (A.filter (fun b => flipVertex5 u a b = true)).card =
        if u a then (A.filter fun b => u b = true).card - 1
        else (A.filter fun b => u b = true).card + 1 := by
    rw [hflipSet A u a ha]
    by_cases hbit : u a = true
    · have hmem : a ∈ A.filter fun b => u b = true := Finset.mem_filter.mpr ⟨ha, hbit⟩
      simp only [if_pos hbit, Finset.card_erase_of_mem hmem]
    · have hfalse : u a = false := by
        cases hu : u a with
        | false => rfl
        | true => exact False.elim (hbit hu)
      have hnot : a ∉ A.filter fun b => u b = true := by simp [hfalse]
      rw [if_neg hbit, Finset.card_insert_of_notMem hnot]
      simp [hfalse]
  have hcountFlipSame (A : Finset (Fin n)) (u v : CubeVertex n) (a b : Fin n)
      (ha : a ∈ A) (hb : b ∈ A)
      (hcount : (A.filter fun c => u c = true).card = (A.filter fun c => v c = true).card)
      (hbit : u a = v b) :
      (A.filter (fun c => flipVertex5 u a c = true)).card =
        (A.filter (fun c => flipVertex5 v b c = true)).card := by
    rw [hcountFlipBlock A u a ha, hcountFlipBlock A v b hb, hbit, hcount]
  have hdataDetermine {u v : CubeVertex n}
      (hres : ∀ a ∈ g.residual, u a = v a)
      (hcoarse : ∀ i, g.coarseCount u i = g.coarseCount v i)
      (hmerged : ∀ i, mergedFineCount5 g.fineLength (g.fineCount u i) =
        mergedFineCount5 g.fineLength (g.fineCount v i))
      (hsev : g.severity u = g.severity v) : dataOf u = dataOf v := by
    apply Prod.ext
    · apply Prod.ext
      · funext a
        exact hres a.1 a.2
      · funext i
        exact Fin.ext (hcoarse i)
    · apply Prod.ext
      · funext i
        exact Fin.ext (hmerged i)
      · exact Fin.ext hsev
  have hbaseParts {u v : CubeVertex n} (hbase : dataOf u = dataOf v) :
      (∀ a ∈ g.residual, u a = v a) ∧
      (∀ i, g.coarseCount u i = g.coarseCount v i) ∧
      (∀ i, mergedFineCount5 g.fineLength (g.fineCount u i) =
        mergedFineCount5 g.fineLength (g.fineCount v i)) ∧
      g.severity u = g.severity v := by
    refine ⟨?_, ?_, ?_, ?_⟩
    · intro a ha
      exact congrArg (fun s : SiteData => s.1.1 ⟨a, ha⟩) hbase
    · intro i
      exact congrArg Fin.val (congrArg (fun s : SiteData => s.1.2 i) hbase)
    · intro i
      exact congrArg Fin.val (congrArg (fun s : SiteData => s.2.1 i) hbase)
    · exact congrArg Fin.val (congrArg (fun s : SiteData => s.2.2) hbase)
  have hresFlipDataEq {u v : CubeVertex n} (hbase : dataOf u = dataOf v)
      (a : g.residual) : dataOf (flipVertex5 u a.1) = dataOf (flipVertex5 v a.1) := by
    rcases hbaseParts hbase with ⟨hres, hcoarse, hmerged, hsev⟩
    apply hdataDetermine
    · intro b hb
      by_cases hba : b = a.1
      · subst b
        have hbit : u a.1 = v a.1 := hres a.1 a.2
        change Function.update u a.1 (!u a.1) a.1 =
          Function.update v a.1 (!v a.1) a.1
        rw [Function.update_self, Function.update_self]
        exact congrArg Bool.not hbit
      · have hbit := hres b hb
        have hu : flipVertex5 u a.1 b = u b := by
          change Function.update u a.1 (!u a.1) b = u b
          exact Function.update_of_ne hba _ _
        have hv : flipVertex5 v a.1 b = v b := by
          change Function.update v a.1 (!v a.1) b = v b
          exact Function.update_of_ne hba _ _
        simpa [hu, hv] using hbit
    · intro i
      have hnot : a.1 ∉ g.coarseChunks i := by
        intro hai
        exact (Finset.disjoint_left.mp (g.chunks_disjoint.2.2.2.1 i)) hai a.2
      have hu : g.coarseCount (flipVertex5 u a.1) i = g.coarseCount u i := by
        unfold ChunkGeometry5.coarseCount
        exact congrArg Finset.card (hfilterOutside (g.coarseChunks i) u a.1 hnot)
      have hv : g.coarseCount (flipVertex5 v a.1) i = g.coarseCount v i := by
        unfold ChunkGeometry5.coarseCount
        exact congrArg Finset.card (hfilterOutside (g.coarseChunks i) v a.1 hnot)
      rw [hu, hv]
      exact hcoarse i
    · intro i
      have hnot : a.1 ∉ g.fineChunks i := by
        intro hai
        exact (Finset.disjoint_left.mp (g.chunks_disjoint.2.2.2.2 i)) hai a.2
      rw [hfineCountOutside u a.1 i hnot, hfineCountOutside v a.1 i hnot]
      exact hmerged i
    · have hu : g.severity (flipVertex5 u a.1) = g.severity u :=
        hseveritySame (fun i => hfineCountOutside u a.1 i (by
          intro hai
          exact (Finset.disjoint_left.mp (g.chunks_disjoint.2.2.2.2 i)) hai a.2))
      have hv : g.severity (flipVertex5 v a.1) = g.severity v :=
        hseveritySame (fun i => hfineCountOutside v a.1 i (by
          intro hai
          exact (Finset.disjoint_left.mp (g.chunks_disjoint.2.2.2.2 i)) hai a.2))
      exact hu.trans (hsev.trans hv.symm)
  have hseverityFlipBalance (u : CubeVertex n) (i : Fin m) (a : Fin n)
      (ha : a ∈ g.fineChunks i) :
      g.severity (flipVertex5 u a) +
          (if Nat.dist (2 * g.fineCount u i) g.fineLength ≤ 11 then 1 else 0) =
        g.severity u +
          (if Nat.dist (2 * g.fineCount (flipVertex5 u a) i) g.fineLength ≤ 11 then 1 else 0) := by
    let weight (z : CubeVertex n) (j : Fin m) : ℕ :=
      if Nat.dist (2 * g.fineCount z j) g.fineLength ≤ 11 then 1 else 0
    have hseverityWeight (z : CubeVertex n) : g.severity z = ∑ j, weight z j := by
      simp [weight, ChunkGeometry5.severity]
    have hweightOther (j : Fin m) (hji : j ≠ i) :
        weight (flipVertex5 u a) j = weight u j := by
      have hnot : a ∉ g.fineChunks j := by
        intro haj
        exact (Finset.disjoint_left.mp (g.chunks_disjoint.2.2.1 j i hji)) haj ha
      simp [weight, hfineCountOutside u a j hnot]
    have hsumAfter :
        (∑ j, weight (flipVertex5 u a) j) = weight (flipVertex5 u a) i +
          ∑ j ∈ (Finset.univ.erase i), weight (flipVertex5 u a) j := by
      calc
        _ = (∑ j ∈ (Finset.univ.erase i), weight (flipVertex5 u a) j) +
              weight (flipVertex5 u a) i :=
            (Finset.sum_erase_add Finset.univ (fun j => weight (flipVertex5 u a) j)
              (Finset.mem_univ i)).symm
        _ = _ := by ac_rfl
    have hsumBefore :
        (∑ j, weight u j) = weight u i + ∑ j ∈ (Finset.univ.erase i), weight u j := by
      calc
        _ = (∑ j ∈ (Finset.univ.erase i), weight u j) + weight u i :=
            (Finset.sum_erase_add Finset.univ (fun j => weight u j) (Finset.mem_univ i)).symm
        _ = _ := by ac_rfl
    have hotherSum :
        (∑ j ∈ (Finset.univ.erase i), weight (flipVertex5 u a) j) =
          ∑ j ∈ (Finset.univ.erase i), weight u j := by
      apply Finset.sum_congr rfl
      intro j hj
      exact hweightOther j (Finset.mem_erase.mp hj).1
    rw [hseverityWeight (flipVertex5 u a), hseverityWeight u, hsumAfter, hsumBefore, hotherSum]
    ring
  have hcoarseFlipDataEq {u v : CubeVertex n} (hbase : dataOf u = dataOf v)
      (i : Fin coarseChunkCount5) (a b : Fin n)
      (ha : a ∈ g.coarseChunks i) (hb : b ∈ g.coarseChunks i) (hbit : u a = v b) :
      dataOf (flipVertex5 u a) = dataOf (flipVertex5 v b) := by
    rcases hbaseParts hbase with ⟨hres, hcoarse, hmerged, hsev⟩
    apply hdataDetermine
    · intro r hr
      have hnotA : a ∉ g.residual := fun har =>
        (Finset.disjoint_left.mp (g.chunks_disjoint.2.2.2.1 i)) ha har
      have hnotB : b ∉ g.residual := fun har =>
        (Finset.disjoint_left.mp (g.chunks_disjoint.2.2.2.1 i)) hb har
      have hsameA : flipVertex5 u a r = u r := by
        change Function.update u a (!u a) r = u r
        have hne : r ≠ a := by
          intro he
          subst r
          exact hnotA hr
        exact Function.update_of_ne hne _ _
      have hsameB : flipVertex5 v b r = v r := by
        change Function.update v b (!v b) r = v r
        have hne : r ≠ b := by
          intro he
          subst r
          exact hnotB hr
        exact Function.update_of_ne hne _ _
      simpa [hsameA, hsameB] using hres r hr
    · intro j
      by_cases hji : j = i
      · subst j
        unfold ChunkGeometry5.coarseCount
        exact hcountFlipSame (g.coarseChunks i) u v a b ha hb (hcoarse i) hbit
      · have hnotA : a ∉ g.coarseChunks j := by
          intro haj
          exact (Finset.disjoint_left.mp (g.chunks_disjoint.1 i j (Ne.symm hji))) ha haj
        have hnotB : b ∉ g.coarseChunks j := by
          intro hbj
          exact (Finset.disjoint_left.mp (g.chunks_disjoint.1 i j (Ne.symm hji))) hb hbj
        have hca := hfilterOutside (g.coarseChunks j) u a hnotA
        have hcb := hfilterOutside (g.coarseChunks j) v b hnotB
        have hca' : g.coarseCount (flipVertex5 u a) j = g.coarseCount u j := by
          unfold ChunkGeometry5.coarseCount
          exact congrArg Finset.card hca
        have hcb' : g.coarseCount (flipVertex5 v b) j = g.coarseCount v j := by
          unfold ChunkGeometry5.coarseCount
          exact congrArg Finset.card hcb
        rw [hca', hcb']
        exact hcoarse j
    · intro j
      have hnotA : a ∉ g.fineChunks j := by
        intro haj
        exact (Finset.disjoint_left.mp (g.chunks_disjoint.2.1 i j)) ha haj
      have hnotB : b ∉ g.fineChunks j := by
        intro hbj
        exact (Finset.disjoint_left.mp (g.chunks_disjoint.2.1 i j)) hb hbj
      rw [hfineCountOutside u a j hnotA, hfineCountOutside v b j hnotB]
      exact hmerged j
    · have hsevU : g.severity (flipVertex5 u a) = g.severity u :=
        hseveritySame (fun j => hfineCountOutside u a j (by
          intro haj
          exact (Finset.disjoint_left.mp (g.chunks_disjoint.2.1 i j)) ha haj))
      have hsevV : g.severity (flipVertex5 v b) = g.severity v :=
        hseveritySame (fun j => hfineCountOutside v b j (by
          intro hbj
          exact (Finset.disjoint_left.mp (g.chunks_disjoint.2.1 i j)) hb hbj))
      exact hsevU.trans (hsev.trans hsevV.symm)
  have hfineFlipDataEq {u v : CubeVertex n} (hbase : dataOf u = dataOf v)
      (i : Fin m) (a b : Fin n) (ha : a ∈ g.fineChunks i) (hb : b ∈ g.fineChunks i)
      (hcount : g.fineCount u i = g.fineCount v i) (hbit : u a = v b) :
      dataOf (flipVertex5 u a) = dataOf (flipVertex5 v b) := by
    rcases hbaseParts hbase with ⟨hres, hcoarse, hmerged, hsev⟩
    have hcountAfter : g.fineCount (flipVertex5 u a) i = g.fineCount (flipVertex5 v b) i := by
      unfold ChunkGeometry5.fineCount
      exact hcountFlipSame (g.fineChunks i) u v a b ha hb hcount hbit
    apply hdataDetermine
    · intro r hr
      have hnotA : a ∉ g.residual := fun har =>
        (Finset.disjoint_left.mp (g.chunks_disjoint.2.2.2.2 i)) ha har
      have hnotB : b ∉ g.residual := fun har =>
        (Finset.disjoint_left.mp (g.chunks_disjoint.2.2.2.2 i)) hb har
      have hsameA : flipVertex5 u a r = u r := by
        change Function.update u a (!u a) r = u r
        have hne : r ≠ a := by
          intro he
          subst r
          exact hnotA hr
        exact Function.update_of_ne hne _ _
      have hsameB : flipVertex5 v b r = v r := by
        change Function.update v b (!v b) r = v r
        have hne : r ≠ b := by
          intro he
          subst r
          exact hnotB hr
        exact Function.update_of_ne hne _ _
      simpa [hsameA, hsameB] using hres r hr
    · intro j
      have hnotA : a ∉ g.coarseChunks j := by
        intro haj
        exact (Finset.disjoint_left.mp (g.chunks_disjoint.2.1 j i)) haj ha
      have hnotB : b ∉ g.coarseChunks j := by
        intro hbj
        exact (Finset.disjoint_left.mp (g.chunks_disjoint.2.1 j i)) hbj hb
      have hca := hfilterOutside (g.coarseChunks j) u a hnotA
      have hcb := hfilterOutside (g.coarseChunks j) v b hnotB
      have hca' : g.coarseCount (flipVertex5 u a) j = g.coarseCount u j := by
        unfold ChunkGeometry5.coarseCount
        exact congrArg Finset.card hca
      have hcb' : g.coarseCount (flipVertex5 v b) j = g.coarseCount v j := by
        unfold ChunkGeometry5.coarseCount
        exact congrArg Finset.card hcb
      rw [hca', hcb']
      exact hcoarse j
    · intro j
      by_cases hji : j = i
      · subst j
        rw [hcountAfter]
      · have hnotA : a ∉ g.fineChunks j := by
          intro haj
          exact (Finset.disjoint_left.mp (g.chunks_disjoint.2.2.1 i j (Ne.symm hji))) ha haj
        have hnotB : b ∉ g.fineChunks j := by
          intro hbj
          exact (Finset.disjoint_left.mp (g.chunks_disjoint.2.2.1 i j (Ne.symm hji))) hb hbj
        rw [hfineCountOutside u a j hnotA, hfineCountOutside v b j hnotB]
        exact hmerged j
    · have hOld :
          (Nat.dist (2 * g.fineCount u i) g.fineLength ≤ 11) ↔
            Nat.dist (2 * g.fineCount v i) g.fineLength ≤ 11 := by rw [hcount]
      have hNew :
          (Nat.dist (2 * g.fineCount (flipVertex5 u a) i) g.fineLength ≤ 11) ↔
            Nat.dist (2 * g.fineCount (flipVertex5 v b) i) g.fineLength ≤ 11 := by
        rw [hcountAfter]
      have hOldIte :
          (if Nat.dist (2 * g.fineCount u i) g.fineLength ≤ 11 then 1 else 0) =
            (if Nat.dist (2 * g.fineCount v i) g.fineLength ≤ 11 then 1 else 0) := by
        by_cases h : Nat.dist (2 * g.fineCount u i) g.fineLength ≤ 11
        · have h' := hOld.mp h
          simp [h, h']
        · have h' : ¬ Nat.dist (2 * g.fineCount v i) g.fineLength ≤ 11 :=
            fun hh => h (hOld.mpr hh)
          simp [h, h']
      have hNewIte :
          (if Nat.dist (2 * g.fineCount (flipVertex5 u a) i) g.fineLength ≤ 11 then 1 else 0) =
            (if Nat.dist (2 * g.fineCount (flipVertex5 v b) i) g.fineLength ≤ 11 then 1 else 0) := by
        by_cases h : Nat.dist (2 * g.fineCount (flipVertex5 u a) i) g.fineLength ≤ 11
        · have h' := hNew.mp h
          simp [h, h']
        · have h' : ¬ Nat.dist (2 * g.fineCount (flipVertex5 v b) i) g.fineLength ≤ 11 :=
            fun hh => h (hNew.mpr hh)
          simp [h, h']
      have hbalU := hseverityFlipBalance u i a ha
      have hbalV := hseverityFlipBalance v i b hb
      omega
  have hnNat : 100000 ≤ n := by
    exact le_trans (le_max_right n₀ 100000) hn
  have hnR : (100000 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hnNat
  have hsqrtN : 144 ≤ Real.sqrt (n : ℝ) := by
    apply Real.le_sqrt_of_sq_le
    nlinarith
  have hsqrtSqrtN : 12 ≤ Real.sqrt (Real.sqrt (n : ℝ)) := by
    apply Real.le_sqrt_of_sq_le
    nlinarith [hsqrtN]
  have hquarter : Real.sqrt (Real.sqrt (n : ℝ)) = (n : ℝ) ^ (1 / 4 : ℝ) := by
    rw [Real.sqrt_eq_rpow, Real.sqrt_eq_rpow]
    rw [← Real.rpow_mul (by positivity : 0 ≤ (n : ℝ))]
    norm_num
  have hFineLengthBig : 11 < g.fineLength := by
    have hpowQuarter : 11 < (n : ℝ) ^ (1 / 4 : ℝ) := by
      calc
        (11 : ℝ) < 12 := by norm_num
        _ ≤ Real.sqrt (Real.sqrt (n : ℝ)) := hsqrtSqrtN
        _ = (n : ℝ) ^ (1 / 4 : ℝ) := hquarter
    have hpowLarge : 11 < (n : ℝ) ^ (3 / 10 : ℝ) := by
      exact lt_of_lt_of_le hpowQuarter
        (Real.rpow_le_rpow_of_exponent_le (by linarith) (by norm_num))
    have hreal : (11 : ℝ) < (g.fineLength : ℝ) :=
      lt_of_lt_of_le hpowLarge g.fine_length_lower
    exact_mod_cast hreal
  have hfindBit (A : Finset (Fin n)) (u v : CubeVertex n)
      (hcount : (A.filter fun c => u c = true).card =
        (A.filter fun c => v c = true).card)
      (a : Fin n) (ha : a ∈ A) : ∃ b ∈ A, u b = v a := by
    cases hbit : v a with
    | true =>
        have hposV : 0 < (A.filter fun c => v c = true).card :=
          Finset.card_pos.mpr ⟨a, Finset.mem_filter.mpr ⟨ha, hbit⟩⟩
        rw [← hcount] at hposV
        obtain ⟨b, hb⟩ := Finset.card_pos.mp hposV
        exact ⟨b, (Finset.mem_filter.mp hb).1, (Finset.mem_filter.mp hb).2⟩
    | false =>
        have hltV : (A.filter fun c => v c = true).card < A.card := by
          apply Finset.card_lt_card
          refine ⟨Finset.filter_subset _ _, ?_⟩
          intro hsubset
          have hmem : a ∈ A.filter fun c => v c = true := hsubset ha
          have : v a = true := (Finset.mem_filter.mp hmem).2
          rw [hbit] at this
          cases this
        have hltU : (A.filter fun c => u c = true).card < A.card := by
          rw [hcount]
          exact hltV
        have hparts := Finset.card_filter_add_card_filter_not (s := A)
          (fun c => u c = true)
        have hfalseCard : 0 < (A.filter fun c => u c = false).card := by
          have hnotCard : (A.filter fun c => ¬ u c = true).card =
              (A.filter fun c => u c = false).card := by
            congr 1
            ext c
            simp
          rw [← hnotCard]
          omega
        obtain ⟨b, hb⟩ := Finset.card_pos.mp hfalseCard
        exact ⟨b, (Finset.mem_filter.mp hb).1, (Finset.mem_filter.mp hb).2⟩
  have hrawCountSameMode {u v : CubeVertex n} (i : Fin m)
      (hmerged : mergedFineCount5 g.fineLength (g.fineCount u i) =
        mergedFineCount5 g.fineLength (g.fineCount v i))
      (hedge : (Nat.dist (2 * g.fineCount u i) g.fineLength = 11) ↔
        (Nat.dist (2 * g.fineCount v i) g.fineLength = 11)) :
      g.fineCount u i = g.fineCount v i := by
    by_cases hdu : Nat.dist (2 * g.fineCount u i) g.fineLength = 11
    · have hdv := hedge.mp hdu
      have hsideU : (g.fineLength < 2 * g.fineCount u i) ↔
          (g.fineLength < 2 * mergedFineCount5 g.fineLength (g.fineCount u i)) :=
        Iff.of_eq (merged_side (g.fineCount u i))
      have hsideV : (g.fineLength < 2 * g.fineCount v i) ↔
          (g.fineLength < 2 * mergedFineCount5 g.fineLength (g.fineCount v i)) :=
        Iff.of_eq (merged_side (g.fineCount v i))
      have hside : (g.fineLength < 2 * g.fineCount u i) ↔
          (g.fineLength < 2 * g.fineCount v i) := by
        have hmid : (g.fineLength < 2 * mergedFineCount5 g.fineLength (g.fineCount u i)) ↔
            (g.fineLength < 2 * mergedFineCount5 g.fineLength (g.fineCount v i)) := by
          rw [hmerged]
        exact hsideU.trans (hmid.trans hsideV.symm)
      obtain ⟨k, hk⟩ := g.fine_length_odd
      by_cases hlowU : 2 * g.fineCount u i < g.fineLength
      · have hlowV : 2 * g.fineCount v i < g.fineLength := by
          by_contra hnotV
          have hpropV : g.fineLength < 2 * g.fineCount v i := by omega
          have hpropU : g.fineLength < 2 * g.fineCount u i := hside.mpr hpropV
          omega
        have hqposU : 0 < g.fineCount u i := by
          by_contra hq
          have hq0 : g.fineCount u i = 0 := Nat.eq_zero_of_not_pos hq
          rw [hq0] at hdu
          simp [Nat.dist] at hdu
          omega
        have hqposV : 0 < g.fineCount v i := by
          by_contra hq
          have hq0 : g.fineCount v i = 0 := Nat.eq_zero_of_not_pos hq
          rw [hq0] at hdv
          simp [Nat.dist] at hdv
          omega
        simp [mergedFineCount5, hdu, hdv, hlowU, hlowV] at hmerged
        omega
      · have hlowV : ¬ 2 * g.fineCount v i < g.fineLength := by
          have hpropU : g.fineLength < 2 * g.fineCount u i := by omega
          have hpropV : g.fineLength < 2 * g.fineCount v i := hside.mp hpropU
          omega
        simp [mergedFineCount5, hdu, hdv, hlowU, hlowV] at hmerged
        omega
    · have hdv : Nat.dist (2 * g.fineCount v i) g.fineLength ≠ 11 := by
        intro hv
        exact hdu (hedge.mpr hv)
      simpa [mergedFineCount5, hdu, hdv] using hmerged
  let S : CubeStates5 g J := {
    Site := SiteData
    siteFintype := inferInstance
    siteDecEq := inferInstance
    d := d
    stateOf := dataOf
    oneHot := fun s k => coordBit s (coordEquiv.symm k)
    oneHot_injective := by
      intro s t hst
      have hcode : ∀ c : Coord, coordBit s c = coordBit t c := by
        intro c
        have h := congrFun hst (coordEquiv c)
        simpa [coordBit] using h
      apply Prod.ext
      · apply Prod.ext
        · funext a
          exact hcode (.inl (.inl a))
        · funext i
          exact cat_injective (s.1.2 i) (t.1.2 i) (fun q => hcode (.inl (.inr ⟨i, q⟩)))
      · apply Prod.ext
        · funext i
          exact cat_injective (s.2.1 i) (t.2.1 i) (fun q => hcode (.inr (.inl ⟨i, q⟩)))
        · exact cat_injective s.2.2 t.2.2 (fun q => hcode (.inr (.inr q)))
    sign_distance := by
      intro x y
      classical
      let A : Finset (Fin m) := Finset.univ.filter fun i => g.sign x i ≠ g.sign y i
      let f : Fin m → Coord := fun i => .inr (.inl ⟨i, (dataOf x).2.1 i⟩)
      have hmem (i : Fin m) (hi : i ∈ A) : f i ∈ diffCoord (dataOf x) (dataOf y) := by
        have hsign : g.sign x i ≠ g.sign y i := (Finset.mem_filter.mp hi).2
        have hval : (dataOf x).2.1 i ≠ (dataOf y).2.1 i := by
          intro heq
          apply hsign
          have hx : g.sign x i = decide
              (g.fineLength < 2 * ((dataOf x).2.1 i).val) := by
            change decide (g.fineLength < 2 * g.fineCount x i) =
              decide (g.fineLength < 2 * mergedFineCount5 g.fineLength (g.fineCount x i))
            have hProp := merged_side (g.fineCount x i)
            have hiff : (g.fineLength < 2 * g.fineCount x i) ↔
                g.fineLength < 2 * mergedFineCount5 g.fineLength (g.fineCount x i) := Iff.of_eq hProp
            by_cases hleft : g.fineLength < 2 * g.fineCount x i
            · have hright := hiff.mp hleft
              simp [hleft, hright]
            · have hright : ¬g.fineLength <
                  2 * mergedFineCount5 g.fineLength (g.fineCount x i) :=
                fun hh => hleft (hiff.mpr hh)
              simp [hleft, hright]
          have hy : g.sign y i = decide
              (g.fineLength < 2 * ((dataOf y).2.1 i).val) := by
            change decide (g.fineLength < 2 * g.fineCount y i) =
              decide (g.fineLength < 2 * mergedFineCount5 g.fineLength (g.fineCount y i))
            have hProp := merged_side (g.fineCount y i)
            have hiff : (g.fineLength < 2 * g.fineCount y i) ↔
                g.fineLength < 2 * mergedFineCount5 g.fineLength (g.fineCount y i) := Iff.of_eq hProp
            by_cases hleft : g.fineLength < 2 * g.fineCount y i
            · have hright := hiff.mp hleft
              simp [hleft, hright]
            · have hright : ¬g.fineLength <
                  2 * mergedFineCount5 g.fineLength (g.fineCount y i) :=
                fun hh => hleft (hiff.mpr hh)
              simp [hleft, hright]
          rw [hx, hy, heq]
        unfold diffCoord
        simp only [Finset.mem_filter, Finset.mem_univ, true_and]
        have hval' : (dataOf y).2.1 i ≠ (dataOf x).2.1 i := Ne.symm hval
        simp [f, coordBit, hval, hval']
      have hinj : Set.InjOn f A := by
        intro i hi j hj hEq
        have houter := Sum.inr.inj hEq
        have hSigma := Sum.inl.inj houter
        exact congrArg Sigma.fst hSigma
      have hcard := Finset.card_le_card_of_injOn f hmem hinj
      have hleft : _root_.hammingDist (g.sign x) (g.sign y) = A.card := by
        simp [A, _root_.hammingDist]
      rw [hleft, hamming_code_eq]
      exact hcard
    resCoord := fun a => coordEquiv (.inl (.inl a))
    resCoord_injective := by
      intro a b hab
      have h := coordEquiv.injective hab
      exact Sum.inl.inj (Sum.inl.inj h)
    oneHot_residual := by
      intro x a
      simp [coordBit, dataOf]
    state_determines := by
      intro x y hxy
      have hres (a : g.residual) : x a.1 = y a.1 := by
        have h := congrArg (fun s : SiteData => s.1.1 a) hxy
        simpa [dataOf] using h
      have hcoarseCount (i : Fin coarseChunkCount5) :
          g.coarseCount x i = g.coarseCount y i := by
        have h := congrArg (fun s : SiteData => s.1.2 i) hxy
        exact congrArg Fin.val h
      have hmerged (i : Fin m) :
          mergedFineCount5 g.fineLength (g.fineCount x i) =
            mergedFineCount5 g.fineLength (g.fineCount y i) := by
        have h := congrArg (fun s : SiteData => s.2.1 i) hxy
        exact congrArg Fin.val h
      have hseverity : g.severity x = g.severity y := by
        have h := congrArg (fun s : SiteData => s.2.2) hxy
        exact congrArg Fin.val h
      have hcoarseBin : g.coarseBin x = g.coarseBin y := by
        funext i
        simp [ChunkGeometry5.coarseBin, hcoarseCount i]
      have hcountFlip (u : CubeVertex n) (i : Fin coarseChunkCount5)
          (a : Fin n) (ha : a ∈ g.coarseChunks i) :
          g.coarseCount (flipVertex5 u a) i =
            if u a then g.coarseCount u i - 1 else g.coarseCount u i + 1 := by
        classical
        let T := (g.coarseChunks i).filter fun b => u b = true
        by_cases hbit : u a = true
        · have hset :
              (g.coarseChunks i).filter (fun b => flipVertex5 u a b = true) = T.erase a := by
            ext b
            by_cases hba : b = a
            · subst b
              simp [T, ha, flipVertex5, hbit]
            · have hf : flipVertex5 u a b = u b := by
                simpa only [flipVertex5, Function.update_of_ne hba]
              constructor
              · intro hh
                have hm := Finset.mem_filter.mp hh
                exact Finset.mem_erase.mpr ⟨hba, Finset.mem_filter.mpr ⟨hm.1, hf.symm.trans hm.2⟩⟩
              · intro hh
                have hm := Finset.mem_filter.mp (Finset.mem_erase.mp hh).2
                exact Finset.mem_filter.mpr ⟨hm.1, hf.trans hm.2⟩
          have hmem : a ∈ T := by simp [T, ha, hbit]
          unfold ChunkGeometry5.coarseCount
          rw [hset, Finset.card_erase_of_mem hmem]
          simp [T, hbit, ChunkGeometry5.coarseCount]
        · have hset :
              (g.coarseChunks i).filter (fun b => flipVertex5 u a b = true) = insert a T := by
            ext b
            by_cases hba : b = a
            · subst b
              simp [T, ha, flipVertex5, hbit]
            · have hf : flipVertex5 u a b = u b := by
                simpa only [flipVertex5, Function.update_of_ne hba]
              constructor
              · intro hh
                have hm := Finset.mem_filter.mp hh
                exact Finset.mem_insert.mpr (Or.inr (Finset.mem_filter.mpr ⟨hm.1, hf.symm.trans hm.2⟩))
              · intro hh
                rcases Finset.mem_insert.mp hh with heq | hm
                · exact (hba heq).elim
                · have hm' := Finset.mem_filter.mp hm
                  exact Finset.mem_filter.mpr ⟨hm'.1, hf.trans hm'.2⟩
          have hnot : a ∉ T := by simp [T, ha, hbit]
          unfold ChunkGeometry5.coarseCount
          rw [hset, Finset.card_insert_of_notMem hnot]
          simp [T, hbit, ChunkGeometry5.coarseCount]
      have hcountFlipOther (u : CubeVertex n) (a : Fin n)
          (j : Fin coarseChunkCount5) (hnot : a ∉ g.coarseChunks j) :
          g.coarseCount (flipVertex5 u a) j = g.coarseCount u j := by
        unfold ChunkGeometry5.coarseCount
        have hset :
            (g.coarseChunks j).filter (fun b => flipVertex5 u a b = true) =
              (g.coarseChunks j).filter (fun b => u b = true) := by
          ext b
          by_cases hba : b = a
          · subst b
            simp [hnot]
          · have hf : flipVertex5 u a b = u b := by
              change Function.update u a (!u a) b = u b
              exact Function.update_of_ne hba _ _
            simp only [Finset.mem_filter]
            rw [hf]
        rw [hset]
      have hcoarseBinFlipEq (u v : CubeVertex n)
          (hcounts : ∀ j, g.coarseCount u j = g.coarseCount v j)
          (i : Fin coarseChunkCount5) (a b : Fin n)
          (ha : a ∈ g.coarseChunks i) (hb : b ∈ g.coarseChunks i)
          (hbit : u a = v b) :
          g.coarseBin (flipVertex5 u a) = g.coarseBin (flipVertex5 v b) := by
        funext j
        change g.bin j (g.coarseCount (flipVertex5 u a) j) =
          g.bin j (g.coarseCount (flipVertex5 v b) j)
        by_cases hji : j = i
        · subst j
          rw [hcountFlip u i a ha, hcountFlip v i b hb, hbit, hcounts i]
        · have hnotA : a ∉ g.coarseChunks j := by
            intro haj
            exact (Finset.disjoint_left.mp (g.chunks_disjoint.1 i j (Ne.symm hji))) ha haj
          have hnotB : b ∉ g.coarseChunks j := by
            intro hbj
            exact (Finset.disjoint_left.mp (g.chunks_disjoint.1 i j (Ne.symm hji))) hb hbj
          rw [hcountFlipOther u a j hnotA, hcountFlipOther v b j hnotB, hcounts j]
      have hmatchingBit (u v : CubeVertex n)
          (hcounts : ∀ j, g.coarseCount u j = g.coarseCount v j)
          (i : Fin coarseChunkCount5) (a : Fin n) (ha : a ∈ g.coarseChunks i) :
          ∃ b ∈ g.coarseChunks i, v b = u a := by
        by_cases hbit : u a = true
        · have hcountPos : 0 < g.coarseCount u i := by
            unfold ChunkGeometry5.coarseCount
            exact Finset.card_pos.mpr ⟨a, Finset.mem_filter.mpr ⟨ha, hbit⟩⟩
          have hcountPosV : 0 < g.coarseCount v i := by simpa [hcounts i] using hcountPos
          have hfilterPos : 0 <
              ((g.coarseChunks i).filter fun b => v b = true).card := by
            simpa [ChunkGeometry5.coarseCount] using hcountPosV
          obtain ⟨b, hb⟩ := Finset.card_pos.mp hfilterPos
          have hvb := (Finset.mem_filter.mp hb).2
          exact ⟨b, (Finset.mem_filter.mp hb).1, hvb.trans hbit.symm⟩
        · have hstrict :
              ((g.coarseChunks i).filter fun b => u b = true) ⊂ g.coarseChunks i := by
            apply Finset.ssubset_iff_subset_ne.mpr
            constructor
            · exact Finset.filter_subset _ _
            · intro heq
              have ha' : a ∈ (g.coarseChunks i).filter fun b => u b = true := by
                rw [heq]
                exact ha
              exact hbit (Finset.mem_filter.mp ha').2
          have hcountLtU : g.coarseCount u i < (g.coarseChunks i).card := by
            unfold ChunkGeometry5.coarseCount
            exact Finset.card_lt_card hstrict
          have hcountLtV : g.coarseCount v i < (g.coarseChunks i).card := by
            simpa [hcounts i] using hcountLtU
          have hzeros : ((g.coarseChunks i).filter fun b => v b = false).Nonempty := by
            by_contra hne
            have hall : ∀ b ∈ g.coarseChunks i, v b = true := by
              intro b hb
              cases hv : v b with
              | false =>
                  have hbzero : b ∈ (g.coarseChunks i).filter fun c => v c = false :=
                    Finset.mem_filter.mpr ⟨hb, hv⟩
                  exact (hne ⟨b, hbzero⟩).elim
              | true => rfl
            have hfilter :
                (g.coarseChunks i).filter (fun b => v b = true) = g.coarseChunks i := by
              ext b
              simp only [Finset.mem_filter]
              constructor
              · rintro ⟨hb, _⟩
                exact hb
              · intro hb
                exact ⟨hb, hall b hb⟩
            have hfull : g.coarseCount v i = (g.coarseChunks i).card := by
              unfold ChunkGeometry5.coarseCount
              rw [hfilter]
            rw [hfull] at hcountLtV
            exact (Nat.lt_irrefl _) hcountLtV
          obtain ⟨b, hb⟩ := hzeros
          have hbitFalse : u a = false := by
            cases hua : u a with
            | false => rfl
            | true => exact (hbit hua).elim
          have hvb := (Finset.mem_filter.mp hb).2
          exact ⟨b, (Finset.mem_filter.mp hb).1, hvb.trans hbitFalse.symm⟩
      have hboundaryTransport {u v : CubeVertex n}
          (hcounts : ∀ i, g.coarseCount u i = g.coarseCount v i)
          (hbin : g.coarseBin u = g.coarseBin v) (hu : g.boundary u) : g.boundary v := by
        rcases hu with ⟨i, a, ha, hflipNe⟩
        obtain ⟨b, hb, hbit⟩ := hmatchingBit u v hcounts i a ha
        have hflipEq := hcoarseBinFlipEq u v hcounts i a b ha hb hbit.symm
        have hflipNe' : g.coarseBin (flipVertex5 v b) ≠ g.coarseBin v := by
          intro heq
          apply hflipNe
          calc
            g.coarseBin (flipVertex5 u a) = g.coarseBin (flipVertex5 v b) := hflipEq
            _ = g.coarseBin v := heq
            _ = g.coarseBin u := hbin.symm
        exact ⟨i, b, hb, hflipNe'⟩
      have hboundary : g.boundary x ↔ g.boundary y := by
        constructor
        · exact hboundaryTransport hcoarseCount hcoarseBin
        · exact hboundaryTransport (fun i => (hcoarseCount i).symm) hcoarseBin.symm
      have hkey : g.key x = g.key y := by
        change (g.coarseBin x, decide (g.boundary x)) =
          (g.coarseBin y, decide (g.boundary y))
        exact Prod.ext hcoarseBin
          (congrArg (fun P : Prop => decide P) (propext hboundary))
      have hkeyFlip (a b : Fin n) (i : Fin coarseChunkCount5)
          (ha : a ∈ g.coarseChunks i) (hb : b ∈ g.coarseChunks i)
          (hbit : x a = y b) :
          g.key (flipVertex5 x a) = g.key (flipVertex5 y b) := by
        have hcounts : ∀ j, g.coarseCount (flipVertex5 x a) j =
            g.coarseCount (flipVertex5 y b) j := by
          intro j
          by_cases hji : j = i
          · subst j
            rw [hcountFlip x i a ha, hcountFlip y i b hb, hbit, hcoarseCount i]
          · have hnotA : a ∉ g.coarseChunks j := by
              intro haj
              exact (Finset.disjoint_left.mp (g.chunks_disjoint.1 i j (Ne.symm hji))) ha haj
            have hnotB : b ∉ g.coarseChunks j := by
              intro hbj
              exact (Finset.disjoint_left.mp (g.chunks_disjoint.1 i j (Ne.symm hji))) hb hbj
            rw [hcountFlipOther x a j hnotA, hcountFlipOther y b j hnotB, hcoarseCount j]
        have hbin := hcoarseBinFlipEq x y hcoarseCount i a b ha hb hbit
        have hbound : g.boundary (flipVertex5 x a) ↔ g.boundary (flipVertex5 y b) :=
          ⟨hboundaryTransport hcounts hbin,
            hboundaryTransport (fun j => (hcounts j).symm) hbin.symm⟩
        change (g.coarseBin (flipVertex5 x a), decide (g.boundary (flipVertex5 x a))) =
          (g.coarseBin (flipVertex5 y b), decide (g.boundary (flipVertex5 y b)))
        exact Prod.ext hbin
          (congrArg (fun P : Prop => decide P) (propext hbound))
      have hcoarseRange : g.coarseRange x = g.coarseRange y := by
        classical
        ext k
        simp only [ChunkGeometry5.coarseRange, Finset.mem_insert, Finset.mem_image]
        constructor
        · rintro (hk | ⟨a, ha, hk⟩)
          · exact Or.inl (hkey.symm ▸ hk)
          · obtain ⟨i, _, hai⟩ := Finset.mem_biUnion.mp ha
            obtain ⟨b, hb, hbit⟩ := hmatchingBit x y hcoarseCount i a hai
            apply Or.inr
            refine ⟨b, Finset.mem_biUnion.mpr ⟨i, Finset.mem_univ _, hb⟩, ?_⟩
            exact (hkeyFlip a b i hai hb hbit.symm).symm.trans hk
        · rintro (hk | ⟨b, hb, hk⟩)
          · exact Or.inl (hkey ▸ hk)
          · obtain ⟨i, _, hbi⟩ := Finset.mem_biUnion.mp hb
            obtain ⟨a, ha, hbit⟩ :=
              hmatchingBit y x (fun j => (hcoarseCount j).symm) i b hbi
            apply Or.inr
            refine ⟨a, Finset.mem_biUnion.mpr ⟨i, Finset.mem_univ _, ha⟩, ?_⟩
            exact (hkeyFlip a b i ha hbi hbit).trans hk
      have hnNat : 100000 ≤ n := by
        exact le_trans (le_max_right n₀ 100000) hn
      have hnR : (100000 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hnNat
      have hnRpos : 0 < (n : ℝ) := by linarith
      have hsqrtN : 144 ≤ Real.sqrt (n : ℝ) := by
        apply Real.le_sqrt_of_sq_le
        nlinarith
      have hsqrtSqrtN : 12 ≤ Real.sqrt (Real.sqrt (n : ℝ)) := by
        apply Real.le_sqrt_of_sq_le
        nlinarith [hsqrtN]
      have hquarter : Real.sqrt (Real.sqrt (n : ℝ)) = (n : ℝ) ^ (1 / 4 : ℝ) := by
        rw [Real.sqrt_eq_rpow, Real.sqrt_eq_rpow]
        rw [← Real.rpow_mul hnRpos.le]
        norm_num
      have hpowQuarter : 11 < (n : ℝ) ^ (1 / 4 : ℝ) := by
        calc
          (11 : ℝ) < 12 := by norm_num
          _ ≤ Real.sqrt (Real.sqrt (n : ℝ)) := hsqrtSqrtN
          _ = (n : ℝ) ^ (1 / 4 : ℝ) := hquarter
      have hpowLarge : 11 < (n : ℝ) ^ (3 / 10 : ℝ) := by
        exact lt_of_lt_of_le hpowQuarter
          (Real.rpow_le_rpow_of_exponent_le (by linarith) (by norm_num))
      have hFineLengthBig : 11 < g.fineLength := by
        have hreal : (11 : ℝ) < (g.fineLength : ℝ) :=
          lt_of_lt_of_le hpowLarge g.fine_length_lower
        exact_mod_cast hreal
      have hmergedDistOne (q : ℕ) :
          (Nat.dist (2 * q) g.fineLength = 1) ↔
            Nat.dist (2 * mergedFineCount5 g.fineLength q) g.fineLength = 1 := by
        unfold mergedFineCount5
        by_cases hd : Nat.dist (2 * q) g.fineLength = 11
        · by_cases hlow : 2 * q < g.fineLength
          · have hdist : g.fineLength - 2 * q = 11 := by
              simpa [Nat.dist_eq_sub_of_le (Nat.le_of_lt hlow)] using hd
            have hnewle : 2 * (q - 1) ≤ g.fineLength :=
              (Nat.mul_le_mul_left 2 (Nat.sub_le q 1)).trans (Nat.le_of_lt hlow)
            have hnewNe : Nat.dist (2 * (q - 1)) g.fineLength ≠ 1 := by
              intro hnew
              have hqpos : 0 < q := by
                by_contra hq
                have hq0 : q = 0 := Nat.eq_zero_of_not_pos hq
                subst q
                simp [Nat.dist] at hdist
                omega
              have hnewEq : g.fineLength - 2 * (q - 1) = 1 := by
                simpa [Nat.dist_eq_sub_of_le hnewle] using hnew
              omega
            simp [hd, hlow, hnewNe]
          · have hle : g.fineLength ≤ 2 * q := Nat.le_of_not_gt hlow
            have hdist : 2 * q - g.fineLength = 11 := by
              simpa [Nat.dist_eq_sub_of_le_right hle] using hd
            have hnewle : g.fineLength ≤ 2 * (q + 1) := by omega
            have hnewNe : Nat.dist (2 * (q + 1)) g.fineLength ≠ 1 := by
              intro hnew
              have hnewEq : 2 * (q + 1) - g.fineLength = 1 := by
                simpa [Nat.dist_eq_sub_of_le_right hnewle] using hnew
              omega
            simp [hd, hlow, hnewNe]
        · simp [hd]
      have hflippable : g.flippable x = g.flippable y := by
        ext i
        simp only [ChunkGeometry5.flippable, Finset.mem_filter, Finset.mem_univ, true_and]
        constructor
        · intro hx
          have hx' := (hmergedDistOne (g.fineCount x i)).mp hx
          have hy' : Nat.dist (2 * mergedFineCount5 g.fineLength (g.fineCount y i))
              g.fineLength = 1 := by
            rw [← hmerged i]
            exact hx'
          exact (hmergedDistOne (g.fineCount y i)).mpr hy'
        · intro hy
          have hy' := (hmergedDistOne (g.fineCount y i)).mp hy
          have hx' : Nat.dist (2 * mergedFineCount5 g.fineLength (g.fineCount x i))
              g.fineLength = 1 := by
            rw [hmerged i]
            exact hy'
          exact (hmergedDistOne (g.fineCount x i)).mpr hx'
      let edgeSet (z : CubeVertex n) : Finset (Fin m) :=
        Finset.univ.filter fun i => Nat.dist (2 * g.fineCount z i) g.fineLength = 11
      let innerSet (z : CubeVertex n) : Finset (Fin m) :=
        Finset.univ.filter fun i =>
          Nat.dist (2 * mergedFineCount5 g.fineLength (g.fineCount z i)) g.fineLength ≤ 9
      let edgeCount (z : CubeVertex n) : ℕ := (edgeSet z).card
      have hdistNeTen (q : ℕ) : Nat.dist (2 * q) g.fineLength ≠ 10 := by
        obtain ⟨k, hk⟩ := g.fine_length_odd
        by_cases hlow : 2 * q < g.fineLength
        · have hdist : g.fineLength - 2 * q ≠ 10 := by
            intro h
            omega
          simpa [Nat.dist_eq_sub_of_le (Nat.le_of_lt hlow)] using hdist
        · have hle : g.fineLength ≤ 2 * q := Nat.le_of_not_gt hlow
          have hdist : 2 * q - g.fineLength ≠ 10 := by
            intro h
            omega
          simpa [Nat.dist_eq_sub_of_le_right hle] using hdist
      have hdistSplit (q : ℕ) :
          Nat.dist (2 * q) g.fineLength ≤ 11 ↔
            Nat.dist (2 * q) g.fineLength ≤ 9 ∨ Nat.dist (2 * q) g.fineLength = 11 := by
        constructor
        · intro h
          by_cases h11 : Nat.dist (2 * q) g.fineLength = 11
          · exact Or.inr h11
          · left
            have h10 := hdistNeTen q
            omega
        · rintro (h | h)
          · exact h.trans (by norm_num)
          · rw [h]
      have hmergedOuter (q : ℕ) (hed : Nat.dist (2 * q) g.fineLength = 11) :
          9 < Nat.dist (2 * mergedFineCount5 g.fineLength q) g.fineLength := by
        by_cases hlow : 2 * q < g.fineLength
        · have hdist : g.fineLength - 2 * q = 11 := by
            simpa [Nat.dist_eq_sub_of_le (Nat.le_of_lt hlow)] using hed
          have hqpos : 0 < q := by
            by_contra hq
            have hq0 : q = 0 := Nat.eq_zero_of_not_pos hq
            subst q
            have hL : g.fineLength = 11 := by
              simpa [Nat.dist_eq_sub_of_le (Nat.zero_le _)] using hed
            omega
          have hnewle : 2 * (q - 1) ≤ g.fineLength :=
            (Nat.mul_le_mul_left 2 (Nat.sub_le q 1)).trans (Nat.le_of_lt hlow)
          have hnewEq : g.fineLength - 2 * (q - 1) = 13 := by omega
          have hnew : Nat.dist (2 * (q - 1)) g.fineLength = 13 := by
            rw [Nat.dist_eq_sub_of_le hnewle]
            exact hnewEq
          have hmergedEq : mergedFineCount5 g.fineLength q = q - 1 := by
            simp [mergedFineCount5, hed, hlow]
          rw [hmergedEq, hnew]
          norm_num
        · have hle : g.fineLength ≤ 2 * q := Nat.le_of_not_gt hlow
          have hdist : 2 * q - g.fineLength = 11 := by
            simpa [Nat.dist_eq_sub_of_le_right hle] using hed
          have hnewle : g.fineLength ≤ 2 * (q + 1) := by omega
          have hnewEq : 2 * (q + 1) - g.fineLength = 13 := by omega
          have hnew : Nat.dist (2 * (q + 1)) g.fineLength = 13 := by
            rw [Nat.dist_eq_sub_of_le_right hnewle]
            exact hnewEq
          have hmergedEq : mergedFineCount5 g.fineLength q = q + 1 := by
            simp [mergedFineCount5, hed, hlow]
          rw [hmergedEq, hnew]
          norm_num
      have hpredSplit (z : CubeVertex n) (i : Fin m) :
          Nat.dist (2 * g.fineCount z i) g.fineLength ≤ 11 ↔
            i ∈ innerSet z ∨ i ∈ edgeSet z := by
        by_cases hed : Nat.dist (2 * g.fineCount z i) g.fineLength = 11
        · simp [innerSet, edgeSet, hed, hmergedOuter _ hed]
        · have hmergedEq :
              mergedFineCount5 g.fineLength (g.fineCount z i) = g.fineCount z i := by
            simp [mergedFineCount5, hed]
          simp only [innerSet, edgeSet, Finset.mem_filter, Finset.mem_univ, true_and]
          rw [hmergedEq]
          exact hdistSplit (g.fineCount z i)
      have hseverityFormula (z : CubeVertex n) :
          g.severity z = (innerSet z).card + (edgeSet z).card := by
        have hfilter :
            (Finset.univ.filter fun i : Fin m =>
              Nat.dist (2 * g.fineCount z i) g.fineLength ≤ 11) = innerSet z ∪ edgeSet z := by
          ext i
          simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_union]
          exact hpredSplit z i
        have hdisj : Disjoint (innerSet z) (edgeSet z) := by
          apply Finset.disjoint_left.mpr
          intro i hi he
          have hi' := (Finset.mem_filter.mp hi).2
          have he' := (Finset.mem_filter.mp he).2
          have houter := hmergedOuter (g.fineCount z i) he'
          exact (not_lt_of_ge hi') houter
        unfold ChunkGeometry5.severity
        rw [hfilter, Finset.card_union_of_disjoint hdisj]
      have hinnerEq : (innerSet x).card = (innerSet y).card := by
        apply congrArg Finset.card
        ext i
        simp only [innerSet, Finset.mem_filter, Finset.mem_univ, true_and]
        rw [hmerged i]
      have hedgeEq : edgeCount x = edgeCount y := by
        have hx := hseverityFormula x
        have hy := hseverityFormula y
        dsimp [edgeCount] at *
        omega
      have hrawMergedMod (q : ℕ) :
          Nat.ModEq 2 q
            (mergedFineCount5 g.fineLength q +
              if Nat.dist (2 * q) g.fineLength = 11 then 1 else 0) := by
        by_cases hed : Nat.dist (2 * q) g.fineLength = 11
        · by_cases hlow : 2 * q < g.fineLength
          · have hqpos : 0 < q := by
              by_contra hq
              have hq0 : q = 0 := Nat.eq_zero_of_not_pos hq
              subst q
              have hL : g.fineLength = 11 := by
                simpa [Nat.dist_eq_sub_of_le (Nat.zero_le _)] using hed
              omega
            have hqle : 1 ≤ q := Nat.one_le_iff_ne_zero.mpr (Nat.ne_of_gt hqpos)
            simp [Nat.ModEq, mergedFineCount5, hed, hlow, Nat.sub_add_cancel hqle]
          · simp [Nat.ModEq, mergedFineCount5, hed, hlow]
            omega
        · simp [Nat.ModEq, mergedFineCount5, hed]
      have hindicator (z : CubeVertex n) :
          (∑ i : Fin m, if Nat.dist (2 * g.fineCount z i) g.fineLength = 11 then 1 else 0) =
            edgeCount z := by
        simp [edgeCount, edgeSet]
      have hFineParity (z : CubeVertex n) :
          (∑ i : Fin m, g.fineCount z i) % 2 =
            ((∑ i : Fin m, mergedFineCount5 g.fineLength (g.fineCount z i)) +
              edgeCount z) % 2 := by
        let f : Fin m → ℕ := fun i => g.fineCount z i
        let q : Fin m → ℕ := fun i =>
          mergedFineCount5 g.fineLength (g.fineCount z i) +
            (if Nat.dist (2 * g.fineCount z i) g.fineLength = 11 then 1 else 0)
        have hmodSum : Nat.ModEq 2 (∑ i ∈ (Finset.univ : Finset (Fin m)), f i)
            (∑ i ∈ (Finset.univ : Finset (Fin m)), q i) := by
          exact Nat.ModEq.sum (s := Finset.univ)
            (fun i hi => hrawMergedMod (g.fineCount z i))
        have hqsum : (∑ i : Fin m, q i) =
            (∑ i : Fin m, mergedFineCount5 g.fineLength (g.fineCount z i)) + edgeCount z := by
          dsimp [q]
          rw [Finset.sum_add_distrib, hindicator z]
        have hmod : Nat.ModEq 2 (∑ i : Fin m, g.fineCount z i)
            ((∑ i : Fin m, mergedFineCount5 g.fineLength (g.fineCount z i)) + edgeCount z) := by
          rw [hqsum] at hmodSum
          simpa [f] using hmodSum
        exact hmod
      let C : Finset (Fin n) := Finset.univ.biUnion g.coarseChunks
      let F : Finset (Fin n) := Finset.univ.biUnion g.fineChunks
      have hCOnes (z : CubeVertex n) :
          (C.filter fun a => z a = true).card = ∑ i, g.coarseCount z i := by
        have hdisj : ((Finset.univ : Finset (Fin coarseChunkCount5)) : Set _).PairwiseDisjoint
            (fun i => (g.coarseChunks i).filter fun a => z a = true) := by
          intro i hi j hj hij
          apply Finset.disjoint_left.mpr
          intro a ha hb
          exact (Finset.disjoint_left.mp (g.chunks_disjoint.1 i j hij))
            (Finset.mem_filter.mp ha).1 (Finset.mem_filter.mp hb).1
        have hunion : C.filter (fun a => z a = true) =
            Finset.univ.biUnion (fun i => (g.coarseChunks i).filter fun a => z a = true) := by
          ext a
          simp [C, Finset.mem_biUnion, Finset.mem_filter]
        rw [hunion]
        simpa [ChunkGeometry5.coarseCount] using Finset.card_biUnion hdisj
      have hFOnes (z : CubeVertex n) :
          (F.filter fun a => z a = true).card = ∑ i, g.fineCount z i := by
        have hdisj : ((Finset.univ : Finset (Fin m)) : Set _).PairwiseDisjoint
            (fun i => (g.fineChunks i).filter fun a => z a = true) := by
          intro i hi j hj hij
          apply Finset.disjoint_left.mpr
          intro a ha hb
          exact (Finset.disjoint_left.mp (g.chunks_disjoint.2.2.1 i j hij))
            (Finset.mem_filter.mp ha).1 (Finset.mem_filter.mp hb).1
        have hunion : F.filter (fun a => z a = true) =
            Finset.univ.biUnion (fun i => (g.fineChunks i).filter fun a => z a = true) := by
          ext a
          simp [F, Finset.mem_biUnion, Finset.mem_filter]
        rw [hunion]
        simpa [ChunkGeometry5.fineCount] using Finset.card_biUnion hdisj
      have hcoverClass (a : Fin n) : a ∈ C ∨ a ∈ F ∨ a ∈ g.residual := by
        have ha : a ∈ (Finset.univ : Finset (Fin n)) := Finset.mem_univ _
        rw [← g.chunks_cover] at ha
        simpa [C, F, Finset.mem_biUnion] using ha
      have htrueUnion (z : CubeVertex n) :
          (Finset.univ.filter fun a : Fin n => z a = true) =
            ((C.filter fun a => z a = true) ∪ (F.filter fun a => z a = true)) ∪
              (g.residual.filter fun a => z a = true) := by
        ext a
        simp only [Finset.mem_filter, Finset.mem_union, Finset.mem_univ, true_and]
        constructor
        · intro hbit
          rcases hcoverClass a with ha | ha | ha
          · exact Or.inl (Or.inl ⟨ha, hbit⟩)
          · exact Or.inl (Or.inr ⟨ha, hbit⟩)
          · exact Or.inr ⟨ha, hbit⟩
        · rintro ((⟨ha, hbit⟩ | ⟨ha, hbit⟩) | ⟨ha, hbit⟩)
          · exact hbit
          · exact hbit
          · exact hbit
      have hCF : Disjoint C F := by
        apply Finset.disjoint_left.mpr
        intro a haC haF
        rcases Finset.mem_biUnion.mp haC with ⟨i, _, hai⟩
        rcases Finset.mem_biUnion.mp haF with ⟨j, _, haj⟩
        exact (Finset.disjoint_left.mp (g.chunks_disjoint.2.1 i j)) hai haj
      have hCR : Disjoint (C ∪ F) g.residual := by
        apply Finset.disjoint_left.mpr
        intro a ha hres'
        rcases Finset.mem_union.mp ha with haC | haF
        · rcases Finset.mem_biUnion.mp haC with ⟨i, _, hai⟩
          exact (Finset.disjoint_left.mp (g.chunks_disjoint.2.2.2.1 i)) hai hres'
        · rcases Finset.mem_biUnion.mp haF with ⟨i, _, hai⟩
          exact (Finset.disjoint_left.mp (g.chunks_disjoint.2.2.2.2 i)) hai hres'
      have hCFtrue (z : CubeVertex n) :
          Disjoint (C.filter fun a => z a = true) (F.filter fun a => z a = true) := by
        apply Finset.disjoint_left.mpr
        intro a ha hb
        exact (Finset.disjoint_left.mp hCF) (Finset.mem_filter.mp ha).1
          (Finset.mem_filter.mp hb).1
      have hCRtrue (z : CubeVertex n) :
          Disjoint ((C.filter fun a => z a = true) ∪ (F.filter fun a => z a = true))
            (g.residual.filter fun a => z a = true) := by
        apply Finset.disjoint_left.mpr
        intro a ha hb
        rcases Finset.mem_union.mp ha with haC | haF
        · exact (Finset.disjoint_left.mp hCR)
            (Finset.mem_union.mpr (Or.inl (Finset.mem_filter.mp haC).1))
            (Finset.mem_filter.mp hb).1
        · exact (Finset.disjoint_left.mp hCR)
            (Finset.mem_union.mpr (Or.inr (Finset.mem_filter.mp haF).1))
            (Finset.mem_filter.mp hb).1
      have honesDecomp (z : CubeVertex n) :
          (Finset.univ.filter fun a : Fin n => z a = true).card =
            (∑ i, g.coarseCount z i) + (∑ i, g.fineCount z i) +
              (g.residual.filter fun a => z a = true).card := by
        rw [htrueUnion z, Finset.card_union_of_disjoint (hCRtrue z),
          Finset.card_union_of_disjoint (hCFtrue z), hCOnes z, hFOnes z]
      have hresOnes : (g.residual.filter fun a => x a = true).card =
          (g.residual.filter fun a => y a = true).card := by
        congr 1
        ext a
        by_cases ha : a ∈ g.residual
        · simp [ha, hres ⟨a, ha⟩]
        · simp [ha]
      have hcoarseSum : (∑ i, g.coarseCount x i) = ∑ i, g.coarseCount y i :=
        Finset.sum_congr rfl (fun i hi => hcoarseCount i)
      have hmergedSum :
          (∑ i, mergedFineCount5 g.fineLength (g.fineCount x i)) =
            ∑ i, mergedFineCount5 g.fineLength (g.fineCount y i) :=
        Finset.sum_congr rfl (fun i hi => hmerged i)
      have hmodTriple (a b c : ℕ) :
          (a + b + c) % 2 = ((a % 2 + b % 2) % 2 + c % 2) % 2 := by omega
      have htotalMod :
          ((Finset.univ.filter fun a : Fin n => x a = true).card) % 2 =
            ((Finset.univ.filter fun a : Fin n => y a = true).card) % 2 := by
        rw [honesDecomp x, honesDecomp y]
        rw [hmodTriple, hmodTriple, hresOnes, hcoarseSum,
          hFineParity x, hFineParity y, hmergedSum, hedgeEq] <;> omega
      have hsign : g.sign x = g.sign y := by
        funext i
        rw [signCode x i, signCode y i, hmerged i]
      refine ⟨?_, hsign, hseverity, ?_, ?_, ?_, ?_⟩
      · change (g.coarseBin x, decide (g.boundary x)) =
          (g.coarseBin y, decide (g.boundary y))
        exact hkey
      · change Even (Finset.univ.filter (fun i => x i = true)).card ↔
          Even (Finset.univ.filter (fun i => y i = true)).card
        rw [Nat.even_iff, Nat.even_iff, htotalMod]
      · simp [ChunkGeometry5.evenType, ChunkGeometry5.typeKeys, hkey, hcoarseRange,
          hflippable, hsign, hseverity]
      · simp [ChunkGeometry5.optionalKey, hkey, hsign, hseverity]
      · simp [ChunkGeometry5.roleKey, hkey, hsign, hseverity]
    data_determine_state := by
      intro x y hres hcoarse hmerged hsev
      apply Prod.ext
      · apply Prod.ext
        · funext a
          exact hres a.1 a.2
        · funext i
          exact Fin.ext (hcoarse i)
      · apply Prod.ext
        · funext i
          exact Fin.ext (hmerged i)
        · exact Fin.ext hsev
    neighbors := fun s => Finset.univ.filter (fun t : SiteData =>
      ∃ x y, dataOf x = s ∧ dataOf y = t ∧ (cube n).Adj x y)
    mem_neighbors := by
      intro s t
      simp [Finset.mem_filter, dataOf]
    degree_bound := by
        all_goals
          intro s
          classical
          let N : Finset SiteData := Finset.univ.filter (fun t : SiteData =>
            ∃ x y, dataOf x = s ∧ dataOf y = t ∧ (cube n).Adj x y)
          change N.card ≤ 2 * n
          by_cases hs : ∃ u, dataOf u = s
          · obtain ⟨u, hus⟩ := hs
            have hnPos : 0 < n := by omega
            let defaultCoord : Fin n := ⟨0, hnPos⟩
            let pickCoord (A : Finset (Fin n)) (z : CubeVertex n) (b : Bool) : Fin n :=
              if h : ∃ a, a ∈ A ∧ z a = b then Classical.choose h else defaultCoord
            have hpickCoord (A : Finset (Fin n)) (z : CubeVertex n) (b : Bool)
                (h : ∃ a, a ∈ A ∧ z a = b) :
                pickCoord A z b ∈ A ∧ z (pickCoord A z b) = b := by
              dsimp [pickCoord]
              rw [dif_pos h]
              exact Classical.choose_spec h
            let fineSource (i : Fin m) (e : Bool) : CubeVertex n :=
              if e then
                if h : ∃ z, dataOf z = s ∧
                    Nat.dist (2 * g.fineCount z i) g.fineLength = 11 then Classical.choose h
                else u
              else
                if h : ∃ z, dataOf z = s ∧
                    Nat.dist (2 * g.fineCount z i) g.fineLength ≠ 11 then Classical.choose h
                else u
            have hfineSourcePos (i : Fin m)
                (h : ∃ z, dataOf z = s ∧ Nat.dist (2 * g.fineCount z i) g.fineLength = 11) :
                dataOf (fineSource i true) = s ∧
                  Nat.dist (2 * g.fineCount (fineSource i true) i) g.fineLength = 11 := by
              dsimp [fineSource]
              rw [dif_pos h]
              exact Classical.choose_spec h
            have hfineSourceNeg (i : Fin m)
                (h : ∃ z, dataOf z = s ∧ Nat.dist (2 * g.fineCount z i) g.fineLength ≠ 11) :
                dataOf (fineSource i false) = s ∧
                  Nat.dist (2 * g.fineCount (fineSource i false) i) g.fineLength ≠ 11 := by
              dsimp [fineSource]
              rw [dif_pos h]
              exact Classical.choose_spec h
            let CoarseLabel : Type := Fin coarseChunkCount5 × Bool
            let FineLabel : Type := Fin m × (Bool × Bool)
            let Labels : Type := g.residual ⊕ (CoarseLabel ⊕ FineLabel)
            let output : Labels → SiteData := fun label =>
              match label with
              | .inl a => dataOf (flipVertex5 u a.1)
              | .inr (.inl (i, b)) =>
                  dataOf (flipVertex5 u (pickCoord (g.coarseChunks i) u b))
              | .inr (.inr (i, (e, b))) =>
                  dataOf (flipVertex5 (fineSource i e)
                    (pickCoord (g.fineChunks i) (fineSource i e) b))
            have hsubset : N ⊆ Finset.univ.image output := by
              intro t ht
              rcases (Finset.mem_filter.mp ht).2 with ⟨v, w, hv, hw, hadj⟩
              have hbase : dataOf u = dataOf v := hus.trans hv.symm
              have adjFlip (p q : CubeVertex n) (hpq : (cube n).Adj p q) :
                  ∃ a : Fin n, q = flipVertex5 p a := by
                have hcard : (Finset.univ.filter fun i : Fin n => p i ≠ q i).card = 1 := by
                  change _root_.hammingDist p q = 1 at hpq
                  simpa [_root_.hammingDist] using hpq
                obtain ⟨c, hc⟩ := Finset.card_eq_one.mp hcard
                have hdiff (i : Fin n)
                    (hi : i ∈ Finset.univ.filter (fun j : Fin n => p j ≠ q j)) : p i ≠ q i :=
                  (Finset.mem_filter.mp hi).2
                have hcMem : c ∈ Finset.univ.filter (fun i : Fin n => p i ≠ q i) := by
                  rw [hc]
                  simp
                have hbit : p c ≠ q c := hdiff c hcMem
                have hsame (i : Fin n) (hic : i ≠ c) : p i = q i := by
                  by_contra hne
                  have hi : i ∈ Finset.univ.filter (fun j : Fin n => p j ≠ q j) := by simp [hne]
                  rw [hc] at hi
                  exact hic (Finset.mem_singleton.mp hi)
                refine ⟨c, ?_⟩
                funext i
                by_cases hic : i = c
                · subst i
                  cases hp : p c <;> cases hq : q c
                  · exact (hbit (by rw [hp, hq])).elim
                  · simp [flipVertex5, hp, hq]
                  · simp [flipVertex5, hp, hq]
                  · exact (hbit (by rw [hp, hq])).elim
                · have hs := hsame i hic
                  simpa only [flipVertex5, Function.update_of_ne hic] using hs.symm
              obtain ⟨a, hwa⟩ := adjFlip v w hadj
              have hwt : dataOf (flipVertex5 v a) = t := by
                rw [← hwa]
                exact hw
              rcases hcategory a with hres | hcoarse | hfine
              · let r : g.residual := ⟨a, hres⟩
                refine Finset.mem_image.mpr ⟨Sum.inl r, Finset.mem_univ _, ?_⟩
                change dataOf (flipVertex5 u a) = t
                exact (hresFlipDataEq hbase r).trans hwt
              · rcases hcoarse with ⟨i, ha⟩
                rcases hbaseParts hbase with ⟨_, hcounts, _, _⟩
                have hmatch : ∃ b ∈ g.coarseChunks i, u b = v a :=
                  hfindBit (g.coarseChunks i) u v (by
                    simpa [ChunkGeometry5.coarseCount] using hcounts i) a ha
                have hpick := hpickCoord (g.coarseChunks i) u (v a) hmatch
                refine Finset.mem_image.mpr
                  ⟨Sum.inr (Sum.inl (i, v a)), Finset.mem_univ _, ?_⟩
                change dataOf (flipVertex5 u (pickCoord (g.coarseChunks i) u (v a))) = t
                exact (hcoarseFlipDataEq hbase i (pickCoord (g.coarseChunks i) u (v a)) a
                  hpick.1 ha hpick.2).trans hwt
              · rcases hfine with ⟨i, ha⟩
                by_cases hedge : Nat.dist (2 * g.fineCount v i) g.fineLength = 11
                · have hsource := hfineSourcePos i ⟨v, hv, hedge⟩
                  have hbaseSource : dataOf (fineSource i true) = dataOf v :=
                    hsource.1.trans hv.symm
                  rcases hbaseParts hbaseSource with ⟨_, _, hmerged, _⟩
                  have hmode :
                      (Nat.dist (2 * g.fineCount (fineSource i true) i) g.fineLength = 11) ↔
                        (Nat.dist (2 * g.fineCount v i) g.fineLength = 11) :=
                    ⟨fun _ => hedge, fun _ => hsource.2⟩
                  have hraw := hrawCountSameMode i (hmerged i) hmode
                  have hmatch : ∃ b ∈ g.fineChunks i, fineSource i true b = v a :=
                    hfindBit (g.fineChunks i) (fineSource i true) v (by
                      simpa [ChunkGeometry5.fineCount] using hraw) a ha
                  have hpick := hpickCoord (g.fineChunks i) (fineSource i true) (v a) hmatch
                  refine Finset.mem_image.mpr
                    ⟨Sum.inr (Sum.inr (i, (true, v a))), Finset.mem_univ _, ?_⟩
                  change dataOf (flipVertex5 (fineSource i true)
                    (pickCoord (g.fineChunks i) (fineSource i true) (v a))) = t
                  exact (hfineFlipDataEq hbaseSource i
                    (pickCoord (g.fineChunks i) (fineSource i true) (v a)) a
                    hpick.1 ha hraw hpick.2).trans hwt
                · have hsource := hfineSourceNeg i ⟨v, hv, hedge⟩
                  have hbaseSource : dataOf (fineSource i false) = dataOf v :=
                    hsource.1.trans hv.symm
                  rcases hbaseParts hbaseSource with ⟨_, _, hmerged, _⟩
                  have hmode :
                      (Nat.dist (2 * g.fineCount (fineSource i false) i) g.fineLength = 11) ↔
                        (Nat.dist (2 * g.fineCount v i) g.fineLength = 11) :=
                    ⟨fun hh => False.elim (hsource.2 hh), fun hh => False.elim (hedge hh)⟩
                  have hraw := hrawCountSameMode i (hmerged i) hmode
                  have hmatch : ∃ b ∈ g.fineChunks i, fineSource i false b = v a :=
                    hfindBit (g.fineChunks i) (fineSource i false) v (by
                      simpa [ChunkGeometry5.fineCount] using hraw) a ha
                  have hpick := hpickCoord (g.fineChunks i) (fineSource i false) (v a) hmatch
                  refine Finset.mem_image.mpr
                    ⟨Sum.inr (Sum.inr (i, (false, v a))), Finset.mem_univ _, ?_⟩
                  change dataOf (flipVertex5 (fineSource i false)
                    (pickCoord (g.fineChunks i) (fineSource i false) (v a))) = t
                  exact (hfineFlipDataEq hbaseSource i
                    (pickCoord (g.fineChunks i) (fineSource i false) (v a)) a
                    hpick.1 ha hraw hpick.2).trans hwt
            have hLabelCard : Fintype.card Labels =
                g.residual.card + 2 * coarseChunkCount5 + 4 * m := by
              simp [Labels, CoarseLabel, FineLabel, Fintype.card_bool]
              ring
            let fineUnion : Finset (Fin n) := Finset.univ.biUnion g.fineChunks
            let occupied : Finset (Fin n) :=
              (Finset.univ.biUnion g.coarseChunks) ∪ fineUnion
            have hfinePair : ((Finset.univ : Finset (Fin m)) : Set (Fin m)).PairwiseDisjoint
                g.fineChunks := by
              intro i _ j _ hij
              exact g.chunks_disjoint.2.2.1 i j hij
            have hFineCard : fineUnion.card = ∑ i : Fin m, (g.fineChunks i).card := by
              simpa [fineUnion] using Finset.card_biUnion hfinePair
            have hFinePos : 1 ≤ g.fineLength := by omega
            have hFineSum : (∑ i : Fin m, (g.fineChunks i).card) = m * g.fineLength := by
              simp [g.fine_chunk_length]
            have hmFine : m ≤ fineUnion.card := by
              rw [hFineCard, hFineSum]
              nlinarith
            have hfineSub : fineUnion ⊆ occupied := by
              intro a ha
              exact Finset.mem_union_right _ ha
            have hmOcc : m ≤ occupied.card := hmFine.trans (Finset.card_le_card hfineSub)
            have hoccReal : (occupied.card : ℝ) ≤ Real.sqrt (n : ℝ) := by
              simpa [occupied, fineUnion, Real.sqrt_eq_rpow] using g.occupied_sublinear
            have hmReal : (m : ℝ) ≤ Real.sqrt (n : ℝ) := by
              have hmOccReal : (m : ℝ) ≤ (occupied.card : ℝ) := by exact_mod_cast hmOcc
              exact hmOccReal.trans hoccReal
            have hrootSq : (Real.sqrt (n : ℝ)) ^ 2 = n :=
              Real.sq_sqrt (by positivity)
            have hroot100 : (100 : ℝ) ≤ Real.sqrt (n : ℝ) := by
              exact (by norm_num : (100 : ℝ) ≤ 144).trans hsqrtN
            have hrootSmall : Real.sqrt (n : ℝ) ≤ (n : ℝ) / 100 := by
              apply (le_div_iff₀ (by norm_num : (0 : ℝ) < 100)).2
              nlinarith [hrootSq, hroot100]
            have hbudget : (600 : ℝ) + 4 * (m : ℝ) ≤ (n : ℝ) := by
              nlinarith [hmReal, hrootSmall, hnR]
            have hresNat : g.residual.card ≤ n := by
              simpa using (Finset.card_le_univ g.residual)
            have hbudgetNat : 600 + 4 * m ≤ n := by exact_mod_cast hbudget
            have hboundNat : g.residual.card + 2 * coarseChunkCount5 + 4 * m ≤ 2 * n := by
              have htemp : g.residual.card + 600 + 4 * m ≤ 2 * n := by omega
              simpa [coarseChunkCount5] using htemp
            calc
              N.card ≤ (Finset.univ.image output).card := Finset.card_le_card hsubset
              _ ≤ Fintype.card Labels := by
                calc
                  _ ≤ (Finset.univ : Finset Labels).card := Finset.card_image_le
                  _ = Fintype.card Labels := by simp
              _ = g.residual.card + 2 * coarseChunkCount5 + 4 * m := hLabelCard
              _ ≤ 2 * n := hboundNat
          · have hempty : N = ∅ := by
              apply Finset.eq_empty_of_forall_notMem
              intro t ht
              rcases (Finset.mem_filter.mp ht).2 with ⟨x, y, hx, hy, hadj⟩
              exact hs ⟨x, hx⟩
            rw [hempty, Finset.card_empty]
            exact Nat.zero_le _
    even_distance := by
      intro b a a' ha ha' hEven hEven'
      classical
      change a ∈ Finset.univ.filter (fun t : SiteData =>
        ∃ x y, dataOf x = b ∧ dataOf y = t ∧ (cube n).Adj x y) at ha
      change a' ∈ Finset.univ.filter (fun t : SiteData =>
        ∃ x y, dataOf x = b ∧ dataOf y = t ∧ (cube n).Adj x y) at ha'
      obtain ⟨u, x, hub, hxa, hux⟩ := (Finset.mem_filter.mp ha).2
      obtain ⟨v, y, hvb, hya, hvy⟩ := (Finset.mem_filter.mp ha').2
      have adjFlip (p q : CubeVertex n) (hpq : (cube n).Adj p q) :
          ∃ c : Fin n, q = flipVertex5 p c := by
        have hcard : (Finset.univ.filter fun i : Fin n => p i ≠ q i).card = 1 := by
          change _root_.hammingDist p q = 1 at hpq
          simpa [_root_.hammingDist] using hpq
        obtain ⟨c, hc⟩ := Finset.card_eq_one.mp hcard
        have hdiff (i : Fin n) (hi : i ∈ Finset.univ.filter (fun j : Fin n => p j ≠ q j)) :
            p i ≠ q i := (Finset.mem_filter.mp hi).2
        have hcMem : c ∈ Finset.univ.filter (fun i : Fin n => p i ≠ q i) := by
          rw [hc]
          simp
        have hbit : p c ≠ q c := hdiff c hcMem
        have hsame (i : Fin n) (hic : i ≠ c) : p i = q i := by
          by_contra hne
          have hi : i ∈ Finset.univ.filter (fun j : Fin n => p j ≠ q j) := by
            simp [hne]
          rw [hc] at hi
          exact hic (Finset.mem_singleton.mp hi)
        refine ⟨c, ?_⟩
        funext i
        by_cases hic : i = c
        · subst i
          cases hp : p c <;> cases hq : q c
          · exact (hbit (by rw [hp, hq])).elim
          · simp [flipVertex5, hp, hq]
          · simp [flipVertex5, hp, hq]
          · exact (hbit (by rw [hp, hq])).elim
        · have hs := hsame i hic
          simpa only [flipVertex5, Function.update_of_ne hic] using hs.symm
      obtain ⟨ca, hxaFlip⟩ := adjFlip u x hux
      obtain ⟨ca', hyaFlip⟩ := adjFlip v y hvy
      let code : SiteData → CubeVertex d := fun s k => coordBit s (coordEquiv.symm k)
      have hstepUX : _root_.hammingDist (code (dataOf u)) (code (dataOf x)) ≤ 4 := by
        rw [hxaFlip]
        exact hflipCodeBound u ca
      have hstepXU : _root_.hammingDist (code (dataOf x)) (code (dataOf u)) ≤ 4 := by
        rw [hxaFlip]
        calc
          _ = _ := _root_.hammingDist_comm _ _
          _ ≤ 4 := hflipCodeBound u ca
      have hstepVY : _root_.hammingDist (code (dataOf v)) (code (dataOf y)) ≤ 4 := by
        rw [hyaFlip]
        exact hflipCodeBound v ca'
      have hcodeUV : code (dataOf u) = code (dataOf v) := by
        funext k
        change coordBit (dataOf u) (coordEquiv.symm k) =
          coordBit (dataOf v) (coordEquiv.symm k)
        rw [hub, hvb]
      have hstepUV : _root_.hammingDist (code (dataOf u)) (code (dataOf v)) = 0 := by
        rw [hcodeUV]
        simp [_root_.hammingDist]
      have htriXY : _root_.hammingDist (code (dataOf x)) (code (dataOf y)) ≤
          _root_.hammingDist (code (dataOf x)) (code (dataOf u)) +
            _root_.hammingDist (code (dataOf u)) (code (dataOf y)) :=
        _root_.hammingDist_triangle (code (dataOf x)) (code (dataOf u)) (code (dataOf y))
      have htriUY : _root_.hammingDist (code (dataOf u)) (code (dataOf y)) ≤
          _root_.hammingDist (code (dataOf u)) (code (dataOf v)) +
            _root_.hammingDist (code (dataOf v)) (code (dataOf y)) :=
        _root_.hammingDist_triangle (code (dataOf u)) (code (dataOf v)) (code (dataOf y))
      change _root_.hammingDist (code a) (code a') ≤ 8
      calc
        _ = _ := by rw [← hxa, ← hya]
        _ ≤ _ := htriXY
        _ ≤ _ := Nat.add_le_add_left htriUY _
        _ ≤ 8 := by omega
    dimension_upper := by
      let C : Finset (Fin n) := Finset.univ.biUnion g.coarseChunks
      let F : Finset (Fin n) := Finset.univ.biUnion g.fineChunks
      have hcc : ((Finset.univ : Finset (Fin coarseChunkCount5)) : Set _).PairwiseDisjoint
          g.coarseChunks := by
        intro i hi j hj hij
        exact g.chunks_disjoint.1 i j hij
      have hff : ((Finset.univ : Finset (Fin m)) : Set _).PairwiseDisjoint
          g.fineChunks := by
        intro i hi j hj hij
        exact g.chunks_disjoint.2.2.1 i j hij
      have hC : C.card = ∑ i, (g.coarseChunks i).card := by
        simpa [C] using Finset.card_biUnion hcc
      have hF : F.card = ∑ i, (g.fineChunks i).card := by
        simpa [F] using Finset.card_biUnion hff
      have hCF : Disjoint C F := by
        apply Finset.disjoint_left.mpr
        intro a haC haF
        rcases Finset.mem_biUnion.mp haC with ⟨i, _, hai⟩
        rcases Finset.mem_biUnion.mp haF with ⟨j, _, haj⟩
        exact (Finset.disjoint_left.mp (g.chunks_disjoint.2.1 i j)) hai haj
      have hCR : Disjoint (C ∪ F) g.residual := by
        apply Finset.disjoint_left.mpr
        intro a ha hres
        rcases Finset.mem_union.mp ha with haC | haF
        · rcases Finset.mem_biUnion.mp haC with ⟨i, _, hai⟩
          exact (Finset.disjoint_left.mp (g.chunks_disjoint.2.2.2.1 i)) hai hres
        · rcases Finset.mem_biUnion.mp haF with ⟨i, _, hai⟩
          exact (Finset.disjoint_left.mp (g.chunks_disjoint.2.2.2.2 i)) hai hres
      have hcover : C.card + F.card + g.residual.card = n := by
        have h := congrArg Finset.card g.chunks_cover
        rw [Finset.card_union_of_disjoint hCR, Finset.card_union_of_disjoint hCF] at h
        simpa [C, F] using h
      have hlen : 1 ≤ g.fineLength := by
        obtain ⟨k, hk⟩ := g.fine_length_odd
        omega
      have hFsize : F.card = m * g.fineLength := by
        calc
          F.card = ∑ i, (g.fineChunks i).card := hF
          _ = ∑ _i : Fin m, g.fineLength := by simp [g.fine_chunk_length]
          _ = m * g.fineLength := by simp
      have hmNat : m ≤ (C ∪ F).card := by
        have hmono : F.card ≤ (C ∪ F).card := Finset.card_mono Finset.subset_union_right
        calc
          m ≤ m * g.fineLength := by simpa using Nat.mul_le_mul_left m hlen
          _ = F.card := hFsize.symm
          _ ≤ (C ∪ F).card := hmono
      have hmReal : (m : ℝ) ≤ Real.sqrt (n : ℝ) := by
        have hmCast : (m : ℝ) ≤ ((C ∪ F).card : ℝ) := by exact_mod_cast hmNat
        have hocc : ((C ∪ F).card : ℝ) ≤ Real.sqrt (n : ℝ) := by
          simpa [C, F, Real.sqrt_eq_rpow] using g.occupied_sublinear
        exact hmCast.trans hocc
      have hCoarseDim : Fintype.card CoarseCoord =
          (∑ i : Fin coarseChunkCount5, (g.coarseChunks i).card) + coarseChunkCount5 := by
        simp [CoarseCoord, Fintype.card_sigma, Fintype.card_fin, Finset.sum_add_distrib]
      have hFineDim : Fintype.card FineCoord =
          (∑ i : Fin m, (g.fineChunks i).card) + 2 * m := by
        simp [FineCoord, Fintype.card_sigma, Fintype.card_fin, Finset.sum_add_distrib]
        ring
      have hdFormula : d = g.residual.card +
          (∑ i, (g.coarseChunks i).card) +
          (∑ i, (g.fineChunks i).card) + 3 * m + 301 := by
        dsimp [d, Coord]
        simp only [Fintype.card_sum, Fintype.card_coe, hCoarseDim, hFineDim, Fintype.card_fin]
        norm_num [coarseChunkCount5]
        ring
      have hdNat : d ≤ n + 3 * m + 301 := by
        rw [hdFormula, ← hC, ← hF]
        omega
      have hdReal : (d : ℝ) ≤ n + 3 * (m : ℝ) + 301 := by exact_mod_cast hdNat
      change (d : ℝ) ≤ n + 3 * (n : ℝ) ^ (1 / 2 : ℝ) + 301
      have hsqrt : Real.sqrt (n : ℝ) = (n : ℝ) ^ (1 / 2 : ℝ) := by rw [Real.sqrt_eq_rpow]
      rw [← hsqrt]
      have hscale : 3 * (m : ℝ) ≤ 3 * Real.sqrt (n : ℝ) :=
        mul_le_mul_of_nonneg_left hmReal (by norm_num)
      linarith [hdReal, hscale]
  }
  refine ⟨S, ?_⟩
  have hdim : (S.d : ℝ) ≤ n + 3 * Real.sqrt (n : ℝ) + 301 := by
    simpa [Real.sqrt_eq_rpow] using S.dimension_upper
  change (S.d : ℝ) ≤ (1 + ε) * n
  calc
    (S.d : ℝ) ≤ n + 3 * Real.sqrt (n : ℝ) + 301 := hdim
    _ ≤ n + ε * n := by nlinarith [hdimNeed]
    _ = (1 + ε) * n := by ring

end HypercubeRamsey
