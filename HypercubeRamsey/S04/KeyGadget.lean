import HypercubeRamsey.S04.CoreParams

/-!
# D4.2: the coordinate key gadget

Source: `sections/04-…tex`, lines 89–143; blueprint D4.2.  `S` is the least power of two with `S ≥ n^{2ω}`
(for large `n`, `n^{2ω} ≤ S < 2n^{2ω}`), `s' = S - 1` chunks of `ℓ = s'^6` bits per gadget, and
`G_n = ⌊n^{γ-ω}⌋` gadgets on the first `G_n s' ℓ` coordinates.  In each gadget the chunk counts are clipped to a
central interval of `S²` unit steps (translated to `[0, S²]`), ranked, and a binary search over rank intervals
`[a, b]` (start `[0, S]`, sentinels `0`, `S²` at ranks `0`, `S`) compares the middle rank's value with
`(a+b)S/2`, going left iff the value is at least it.  The gadget outputs the leaf index `a` and the labelled set
of chunks above the leaf midpoint `aS + S/2`; the key is the vector of gadget outputs.

The definitions follow the unmerged lane `skel-s04` (`HypercubeRamsey/S04/Core/KeyGadget.lean` there), audited
against the TeX.  When the special block is longer than `n` (small `n`) the chunk coordinate sets are truncated by
`Fin n`; every Section 4 fact is asserted only for large `n`.
-/

namespace HypercubeRamsey.S04

open Classical OAI.HypercubeRamsey

/-- D4.2: the least power of two at least `n^{2ω}` (and at least `2`). -/
noncomputable def gadgetPower (β γ : ℝ) (n : ℕ) : ℕ :=
  2 ^ max 1 (⌈Real.log ((n : ℝ) ^ (2 * omega4 β γ)) / Real.log 2⌉₊)

/-- D4.2: `s' = S - 1` chunks per gadget. -/
noncomputable def chunkNum (β γ : ℝ) (n : ℕ) : ℕ := gadgetPower β γ n - 1

/-- D4.2: chunk length `ℓ = s'^6`. -/
noncomputable def chunkLen (β γ : ℝ) (n : ℕ) : ℕ := chunkNum β γ n ^ 6

/-- D4.2: the number `G_n = ⌊n^{γ-ω}⌋` of gadgets. -/
noncomputable def gadgetNum (β γ : ℝ) (n : ℕ) : ℕ := ⌊(n : ℝ) ^ (γ - omega4 β γ)⌋₊

/-- D4.2: the key space `Fin G_n → Fin S × Finset (Fin s')`. -/
abbrev Key (β γ : ℝ) (n : ℕ) :=
  Fin (gadgetNum β γ n) → Fin (gadgetPower β γ n) × Finset (Fin (chunkNum β γ n))

/-- D4.2: the number `m = G_n s' ℓ` of special coordinates. -/
noncomputable def specialNum (β γ : ℝ) (n : ℕ) : ℕ :=
  gadgetNum β γ n * chunkNum β γ n * chunkLen β γ n

/-- D4.2: the first index of chunk `j` of gadget `g`. -/
noncomputable def chunkStart (β γ : ℝ) (n : ℕ) (g : Fin (gadgetNum β γ n))
    (j : Fin (chunkNum β γ n)) : ℕ :=
  (g.val * chunkNum β γ n + j.val) * chunkLen β γ n

/-- D4.2: the coordinates of chunk `j` of gadget `g` (consecutive blocks of length `ℓ`). -/
noncomputable def chunkCoords (β γ : ℝ) (n : ℕ) (g : Fin (gadgetNum β γ n))
    (j : Fin (chunkNum β γ n)) : Finset (Fin n) :=
  Finset.univ.filter fun i =>
    chunkStart β γ n g j ≤ i.val ∧ i.val < chunkStart β γ n g j + chunkLen β γ n

/-- The number of ones of `v` in a chunk. -/
noncomputable def chunkCount (β γ : ℝ) (n : ℕ) (g : Fin (gadgetNum β γ n))
    (j : Fin (chunkNum β γ n)) (v : CubeVertex n) : ℕ :=
  ((chunkCoords β γ n g j).filter fun i => v i = true).card

/-- D4.2: the clipped count `min (max (count - lo) 0) S²`, `lo = ⌊ℓ/2⌋ - S²/2` (04:100–102). -/
noncomputable def clipped (β γ : ℝ) (n : ℕ) (g : Fin (gadgetNum β γ n))
    (j : Fin (chunkNum β γ n)) (v : CubeVertex n) : ℕ :=
  min (chunkCount β γ n g j v - (chunkLen β γ n / 2 - gadgetPower β γ n ^ 2 / 2))
    (gadgetPower β γ n ^ 2)

/-- D4.2: the clipped counts of gadget `g` in nondecreasing order. -/
noncomputable def sortedCounts (β γ : ℝ) (n : ℕ) (g : Fin (gadgetNum β γ n))
    (v : CubeVertex n) : List ℕ :=
  (List.ofFn fun j : Fin (chunkNum β γ n) => clipped β γ n g j v).mergeSort
    (fun a b => decide (a ≤ b))

/-- D4.2: the value at rank `t`, with sentinels `0` at rank `0` and `S²` at rank `S` (04:108–109). -/
noncomputable def rankValue (β γ : ℝ) (n : ℕ) (g : Fin (gadgetNum β γ n)) (v : CubeVertex n)
    (t : ℕ) : ℕ :=
  if t = 0 then 0 else
    if t = gadgetPower β γ n then gadgetPower β γ n ^ 2
    else (sortedCounts β γ n g v).getD (t - 1) 0

/-- D4.2: one binary-search step on the rank interval `[a, b]` (04:109–113). -/
noncomputable def searchStep (β γ : ℝ) (n : ℕ) (g : Fin (gadgetNum β γ n)) (v : CubeVertex n)
    (ab : ℕ × ℕ) : ℕ × ℕ :=
  if (ab.1 + ab.2) / 2 * gadgetPower β γ n ≤ rankValue β γ n g v ((ab.1 + ab.2) / 2)
  then (ab.1, (ab.1 + ab.2) / 2) else ((ab.1 + ab.2) / 2, ab.2)

/-- D4.2: the leaf of the binary search from `[0, S]`; `S = 2^e` and `e = log₂ S` steps reach length one. -/
noncomputable def searchLeaf (β γ : ℝ) (n : ℕ) (g : Fin (gadgetNum β γ n)) (v : CubeVertex n) :
    ℕ × ℕ :=
  (List.range (Nat.log2 (gadgetPower β γ n))).foldl (fun ab _ => searchStep β γ n g v ab)
    (0, gadgetPower β γ n)

theorem gadgetPower_pos (β γ : ℝ) (n : ℕ) : 0 < gadgetPower β γ n := by
  unfold gadgetPower
  positivity

/-- D4.2: the output of gadget `g`: the leaf index and the labelled chunks above `aS + S/2` (04:114–116). -/
noncomputable def gadgetOut (β γ : ℝ) (n : ℕ) (g : Fin (gadgetNum β γ n)) (v : CubeVertex n) :
    Fin (gadgetPower β γ n) × Finset (Fin (chunkNum β γ n)) :=
  haveI : NeZero (gadgetPower β γ n) := ⟨(gadgetPower_pos β γ n).ne'⟩
  (Fin.ofNat (gadgetPower β γ n) (searchLeaf β γ n g v).1,
    Finset.univ.filter fun j =>
      (searchLeaf β γ n g v).1 * gadgetPower β γ n + gadgetPower β γ n / 2 < clipped β γ n g j v)

/-- D4.2: the key `g(v)`, the vector of gadget outputs (04:134). -/
noncomputable def key (β γ : ℝ) (n : ℕ) (v : CubeVertex n) : Key β γ n :=
  fun g => gadgetOut β γ n g v

end HypercubeRamsey.S04
