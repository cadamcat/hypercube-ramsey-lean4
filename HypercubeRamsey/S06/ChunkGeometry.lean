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
  classical
  obtain ⟨r, hr⟩ := L.residual_nonempty
  have fiberCardEq (u v : CubeVertex L.m) :
      (signFiber6 L p u).card = (signFiber6 L p v).card := by
    let D := Finset.univ.filter fun i : Fin L.m => u i ≠ v i
    let U := D.biUnion L.fineChunks
    let S := U ∪ if Odd D.card then {r} else ∅
    let toggle : CubeVertex n → CubeVertex n := fun x a => if a ∈ S then !x a else x a
    have hDisjoint : (D : Set (Fin L.m)).PairwiseDisjoint L.fineChunks := by
      intro i hi j hj hij
      exact L.chunks_disjoint.2.2.1 i j hij
    have hUcard : U.card = D.card * L.fineLength := by
      calc
        U.card = ∑ i ∈ D, (L.fineChunks i).card := Finset.card_biUnion hDisjoint
        _ = ∑ i ∈ D, L.fineLength := by
          apply Finset.sum_congr rfl
          intro i hi
          exact L.fine_chunk_length i
        _ = D.card * L.fineLength := by simp
    have hnotPivot : r ∉ U := by
      intro hrU
      rcases Finset.mem_biUnion.mp hrU with ⟨i, hiD, hir⟩
      have hdisj := L.chunks_disjoint.2.2.2.2 i
      exact (Finset.disjoint_left.mp hdisj) hir hr
    have hdisjPivot : Disjoint U {r} := by
      apply Finset.disjoint_left.mpr
      intro a ha hara
      have : a = r := Finset.mem_singleton.mp hara
      subst a
      exact hnotPivot ha
    have hScard : S.card = D.card * L.fineLength + (if Odd D.card then 1 else 0) := by
      by_cases ho : Odd D.card
      · calc
          S.card = (U ∪ ({r} : Finset (Fin n))).card := by simp [S, ho]
          _ = U.card + ({r} : Finset (Fin n)).card := Finset.card_union_of_disjoint hdisjPivot
          _ = D.card * L.fineLength + (if Odd D.card then 1 else 0) := by simp [hUcard, ho]
      · calc
          S.card = U.card := by simp [S, ho]
          _ = D.card * L.fineLength := hUcard
          _ = D.card * L.fineLength + (if Odd D.card then 1 else 0) := by simp [ho]
    have hSeven : Even S.card := by
      rcases Nat.even_or_odd D.card with hEven | hOdd
      · have hnotOdd : ¬ Odd D.card := by
          intro ho
          rcases hEven with ⟨a, ha⟩
          rcases ho with ⟨b, hb⟩
          omega
        rw [hScard]
        simp [hnotOdd]
        exact Even.mul_right hEven L.fineLength
      · have hOddProof := hOdd
        rcases hOdd with ⟨a, ha⟩
        rcases L.fine_length_odd with ⟨b, hb⟩
        rw [hScard]
        simp [hOddProof]
        refine ⟨2 * a * b + a + b + 1, ?_⟩
        rw [ha, hb]
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
        calc
          S.card = (S ∩ A).card + (S \ A).card :=
            (Finset.card_inter_add_card_sdiff S A).symm
          _ = B.card + T.card := by simp [B, T, Finset.inter_comm]
      have hAnew : A'.card = C.card + T.card := by
        rw [hA', Finset.card_union_of_disjoint hdisj]
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
    have chunkInS (i : Fin L.m) (hi : i ∈ D) (a : Fin n)
        (ha : a ∈ L.fineChunks i) : a ∈ S := by
      apply Finset.mem_union_left
      exact Finset.mem_biUnion.mpr ⟨i, hi, ha⟩
    have chunkNotS (i : Fin L.m) (hi : i ∉ D) (a : Fin n)
        (ha : a ∈ L.fineChunks i) : a ∉ S := by
      intro has
      rcases Finset.mem_union.mp has with hU | htail
      · rcases Finset.mem_biUnion.mp hU with ⟨j, hjD, haj⟩
        by_cases hji : j = i
        · subst j
          exact hi hjD
        · have hdisj := L.chunks_disjoint.2.2.1 i j (Ne.symm hji)
          exact (Finset.disjoint_left.mp hdisj) ha haj
      · have hrest : a ∈ (if Odd D.card then {r} else ∅) := htail
        by_cases ho : Odd D.card
        · have har : a = r := by simpa [ho] using hrest
          subst a
          exact (Finset.disjoint_left.mp (L.chunks_disjoint.2.2.2.2 i)) ha hr
        · simp [ho] at hrest
    have countComplement (x : CubeVertex n) (i : Fin L.m) (hi : i ∈ D) :
        L.fineCount (toggle x) i = L.fineLength - L.fineCount x i := by
      have hfilter : (L.fineChunks i).filter (fun a => toggle x a = true) =
          (L.fineChunks i).filter (fun a => x a = false) := by
        ext a
        by_cases ha : a ∈ L.fineChunks i
        · simp [toggle, chunkInS i hi a ha, ha]
        · simp [ha]
      have hfalseEq : (L.fineChunks i).filter (fun a => x a = false) =
          (L.fineChunks i).filter (fun a => ¬ x a = true) := by
        ext a
        simp
      have hsplit := Finset.card_filter_add_card_filter_not
        (s := L.fineChunks i) (fun a => x a = true)
      rw [← hfalseEq] at hsplit
      have hfalse : ((L.fineChunks i).filter (fun a => x a = false)).card +
          L.fineCount x i = (L.fineChunks i).card := by
        simpa [ChunkLayout6.fineCount, add_comm] using hsplit
      unfold ChunkLayout6.fineCount
      rw [hfilter]
      have hlen := L.fine_chunk_length i
      omega
    have countSame (x : CubeVertex n) (i : Fin L.m) (hi : i ∉ D) :
        L.fineCount (toggle x) i = L.fineCount x i := by
      unfold ChunkLayout6.fineCount
      apply congrArg Finset.card
      ext a
      by_cases ha : a ∈ L.fineChunks i
      · simp [toggle, chunkNotS i hi a ha, ha]
      · simp [ha]
    have signFlipChunk (x : CubeVertex n) (i : Fin L.m) (hi : i ∈ D) :
        L.sign (toggle x) i = !L.sign x i := by
      have hc := countComplement x i hi
      have hcBound : L.fineCount x i ≤ L.fineLength := by
        calc
          L.fineCount x i ≤ (L.fineChunks i).card := Finset.card_filter_le _ _
          _ = L.fineLength := L.fine_chunk_length i
      rcases L.fine_length_odd with ⟨q, hq⟩
      change decide (L.fineLength < 2 * L.fineCount (toggle x) i) =
        !decide (L.fineLength < 2 * L.fineCount x i)
      rw [hc]
      by_cases hmajor : L.fineLength < 2 * L.fineCount x i
      · have hnot : ¬ L.fineLength < 2 * (L.fineLength - L.fineCount x i) := by omega
        simp [hmajor, hnot]
      · have hcomp : L.fineLength < 2 * (L.fineLength - L.fineCount x i) := by omega
        simp [hmajor, hcomp]
    have signSameChunk (x : CubeVertex n) (i : Fin L.m) (hi : i ∉ D) :
        L.sign (toggle x) i = L.sign x i := by
      simp [ChunkLayout6.sign, countSame x i hi]
    have signToggle (x : CubeVertex n) :
        L.sign (toggle x) = fun i => if i ∈ D then !L.sign x i else L.sign x i := by
      funext i
      by_cases hi : i ∈ D
      · simp [hi, signFlipChunk x i hi]
      · simp [hi, signSameChunk x i hi]
    have signChange (a b : CubeVertex L.m) (x : CubeVertex n)
        (hx : L.sign x = a) (hD : ∀ i, i ∈ D ↔ a i ≠ b i) :
        L.sign (toggle x) = b := by
      funext i
      have hs := congrFun hx i
      by_cases hi : i ∈ D
      · have hneq := (hD i).mp hi
        cases ha : a i <;> cases hb : b i <;> simp_all [signToggle]
      · have heq : a i = b i := by
          by_contra hneq
          exact hi ((hD i).mpr hneq)
        simp [signToggle, hi, hs, heq]
    have hDuv : ∀ i, i ∈ D ↔ u i ≠ v i := by
      intro i
      simp [D]
    have hDvu : ∀ i, i ∈ D ↔ v i ≠ u i := by
      intro i
      simp [D, ne_comm]
    have mapTo (x : CubeVertex n) (hx : x ∈ signFiber6 L p u) :
        toggle x ∈ signFiber6 L p v := by
      rcases (Finset.mem_filter.mp hx).2 with ⟨hp, hs⟩
      apply Finset.mem_filter.mpr
      refine ⟨Finset.mem_univ _, ?_⟩
      constructor
      · cases p with
        | false =>
            change ¬ IsEvenRole (toggle x)
            intro h
            exact hp ((parityToggle x).mp h)
        | true =>
            change IsEvenRole (toggle x)
            exact (parityToggle x).mpr hp
      · exact signChange u v x hs hDuv
    have mapFrom (x : CubeVertex n) (hx : x ∈ signFiber6 L p v) :
        toggle x ∈ signFiber6 L p u := by
      rcases (Finset.mem_filter.mp hx).2 with ⟨hp, hs⟩
      apply Finset.mem_filter.mpr
      refine ⟨Finset.mem_univ _, ?_⟩
      constructor
      · cases p with
        | false =>
            change ¬ IsEvenRole (toggle x)
            intro h
            exact hp ((parityToggle x).mp h)
        | true =>
            change IsEvenRole (toggle x)
            exact (parityToggle x).mpr hp
      · exact signChange v u x hs hDvu
    exact Finset.card_bij'
      (fun x _ => toggle x) (fun x _ => toggle x)
      mapTo mapFrom (fun x _ => toggleInvol x) (fun x _ => toggleInvol x)
  have hsum : (parityFiber6 (n := n) p).card =
      ∑ u ∈ (Finset.univ : Finset (CubeVertex L.m)), (signFiber6 L p u).card := by
    calc
      (parityFiber6 (n := n) p).card =
          ∑ u ∈ (Finset.univ : Finset (CubeVertex L.m)),
            ((parityFiber6 (n := n) p).filter (fun x => L.sign x = u)).card :=
        Finset.card_eq_sum_card_fiberwise
          (f := L.sign) (s := parityFiber6 (n := n) p)
          (t := Finset.univ) (by intro x hx; exact Finset.mem_univ _)
      _ = ∑ u ∈ (Finset.univ : Finset (CubeVertex L.m)),
            (signFiber6 L p u).card := by
        apply Finset.sum_congr rfl
        intro u hu
        congr 1
        ext x
        simp [signFiber6, parityFiber6]
  have hNat : (parityFiber6 (n := n) p).card =
      2 ^ L.m * (signFiber6 L p t).card := by
    calc
      (parityFiber6 (n := n) p).card =
          ∑ u ∈ (Finset.univ : Finset (CubeVertex L.m)), (signFiber6 L p u).card := hsum
      _ = ∑ u ∈ (Finset.univ : Finset (CubeVertex L.m)), (signFiber6 L p t).card := by
        apply Finset.sum_congr rfl
        intro u hu
        exact (fiberCardEq t u).symm
      _ = Fintype.card (CubeVertex L.m) * (signFiber6 L p t).card := by simp
      _ = 2 ^ L.m * (signFiber6 L p t).card := by simp [OAI.HypercubeRamsey.card_cubeVertex]
  have hreal : ((parityFiber6 (n := n) p).card : ℝ) =
      (2 : ℝ) ^ L.m * ((signFiber6 L p t).card : ℝ) := by
    exact_mod_cast hNat
  rw [hreal]
  ring

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

set_option maxRecDepth 4096
/-- L6.1b (flips): coarse flips stay in the key relation, a bin change has boundary ends, fine flips change
one sign and the severity by at most one, `|C(h)| ≤ 602` (06:86–91, 05:88–109). -/
theorem L6_1b_flips {n : ℕ} (L : ChunkLayout6 n) : ChunkFlips6 L := by
  classical
  have adjData {x y : CubeVertex n} (hxy : (cube n).Adj x y) :
      ∃ k, x k ≠ y k ∧ ∀ j, j ≠ k → x j = y j := by
    have hcard : (Finset.univ.filter (fun j : Fin n => x j ≠ y j)).card = 1 := hxy
    obtain ⟨k, hk⟩ := Finset.card_eq_one.mp hcard
    have hmem : k ∈ Finset.univ.filter (fun j : Fin n => x j ≠ y j) := by
      rw [hk]
      simp
    refine ⟨k, (Finset.mem_filter.mp hmem).2, ?_⟩
    intro j hj
    by_contra hne
    have hjmem : j ∈ Finset.univ.filter (fun t : Fin n => x t ≠ y t) :=
      Finset.mem_filter.mpr ⟨Finset.mem_univ _, hne⟩
    rw [hk] at hjmem
    exact hj (Finset.mem_singleton.mp hjmem)
  have filterCardEq {x y : CubeVertex n} (S : Finset (Fin n))
      (hag : ∀ a, a ∈ S → x a = y a) :
      (S.filter (fun a => x a = true)).card = (S.filter (fun a => y a = true)).card := by
    apply congrArg Finset.card
    ext a
    by_cases ha : a ∈ S
    · simp [ha, hag a ha]
    · simp [ha]
  have filterCardStep {x y : CubeVertex n} (S : Finset (Fin n)) (k : Fin n)
      (hk : k ∈ S) (hxy : x k ≠ y k) (hsame : ∀ a, a ≠ k → x a = y a) :
      ((S.filter (fun a => x a = true)).card + 1 =
          (S.filter (fun a => y a = true)).card) ∨
        ((S.filter (fun a => y a = true)).card + 1 =
          (S.filter (fun a => x a = true)).card) := by
    cases hx : x k <;> cases hy : y k
    · simp_all
    · left
      have hset : S.filter (fun a => y a = true) =
          insert k (S.filter (fun a => x a = true)) := by
        ext a
        by_cases hak : a = k
        · subst a
          simp [hk, hx, hy]
        · simp [hak, hsame a hak]
      have hnot : k ∉ S.filter (fun a => x a = true) := by simp [hk, hx]
      rw [hset, Finset.card_insert_of_notMem hnot]
    · right
      have hset : S.filter (fun a => x a = true) =
          insert k (S.filter (fun a => y a = true)) := by
        ext a
        by_cases hak : a = k
        · subst a
          simp [hk, hx, hy]
        · simp [hak, hsame a hak]
      have hnot : k ∉ S.filter (fun a => y a = true) := by simp [hk, hy]
      rw [hset, Finset.card_insert_of_notMem hnot]
    · simp_all
  have changing {x y : CubeVertex n} (hxy : (cube n).Adj x y)
      (hbin : L.coarseBin x ≠ L.coarseBin y) : L.boundary x ∧ L.boundary y := by
    obtain ⟨k, hneq, hsame⟩ := adjData hxy
    have hkset : Finset.univ.filter (fun j : Fin n => x j ≠ y j) = {k} := by
      have hcard : (Finset.univ.filter (fun j : Fin n => x j ≠ y j)).card = 1 := hxy
      obtain ⟨k', hk'⟩ := Finset.card_eq_one.mp hcard
      have hkmem : k ∈ Finset.univ.filter (fun j : Fin n => x j ≠ y j) :=
        Finset.mem_filter.mpr ⟨Finset.mem_univ _, hneq⟩
      have hkEq : k' = k := by
        rw [hk'] at hkmem
        exact (Finset.mem_singleton.mp hkmem).symm
      rw [hkEq] at hk'
      exact hk'
    have hchunk : ∃ i, k ∈ L.coarseChunks i := by
      by_contra hnone
      have hnone' : ∀ i, k ∉ L.coarseChunks i := by
        intro i
        by_contra hk
        exact hnone ⟨i, hk⟩
      apply hbin
      funext i
      have hcount : L.coarseCount x i = L.coarseCount y i := by
        apply filterCardEq
        intro a ha
        by_cases hak : a = k
        · subst a
          exact (hnone' i ha).elim
        · exact hsame a hak
      simp [ChunkLayout6.coarseBin, hcount]
    obtain ⟨i, hk⟩ := hchunk
    have hflipxy : flipVertex6 x k = y := by
      funext j
      by_cases hj : j = k
      · subst j
        cases hx : x k <;> cases hy : y k <;> simp_all [flipVertex6]
      · simp [flipVertex6, hj, hsame j hj]
    have hflipyx : flipVertex6 y k = x := by
      funext j
      by_cases hj : j = k
      · subst j
        cases hx : x k <;> cases hy : y k <;> simp_all [flipVertex6]
      · simp [flipVertex6, hj, hsame j hj]
    constructor
    · exact ⟨i, k, hk, by simpa [hflipxy] using Ne.symm hbin⟩
    · exact ⟨i, k, hk, by simpa [hflipyx] using hbin⟩
  refine {
    fine_flip_sign := ?_
    fine_flip_severity := ?_
    nonfine_flip_fine := ?_
    noncoarse_flip_key := ?_
    coarse_flip_key := ?_
    changing_bin_boundary := by
      intro x y hxy hbin
      exact changing hxy hbin
    key_neighborhood_card := by
      intro h
      let w := h.1
      let sameKeys : Finset (CoarseKey6 (BinVector6 n)) :=
        {(w, KeyFlag6.interior), (w, KeyFlag6.boundary)}
      let stepValue (z : Fin coarseChunkCount × Bool) : Fin (n + 1) :=
        if z.2 then ⟨min n ((w z.1).val + 1), by omega⟩
        else ⟨(w z.1).val - 1, by omega⟩
      let stepKeys : Finset (CoarseKey6 (BinVector6 n)) :=
        Finset.univ.image fun z => (Function.update w z.1 (stepValue z), KeyFlag6.boundary)
      let candidate := sameKeys ∪ stepKeys
      have hsubset : keyNeighborhood6 binAdjacent6 h ⊆ candidate := by
        intro k hk
        change k ∈ sameKeys ∪ stepKeys
        have hrel : keyAdjacent6 binAdjacent6 h k := (Finset.mem_filter.mp hk).2
        rcases hrel with heq | hsame | ⟨_, hkflag, hadj⟩
        · subst k
          change h ∈ sameKeys ∪ stepKeys
          apply Finset.mem_union_left
          cases h with
          | mk bits flag =>
            cases flag <;> simp [sameKeys, w]
        · have hfirst : k.1 = w := hsame.symm
          have hkEq : k = (w, k.2) := Prod.ext hfirst rfl
          rw [hkEq]
          apply Finset.mem_union_left
          cases k.2 <;> simp [sameKeys]
        · rcases hadj with ⟨i, hother, hdist⟩
          have hcase : (k.1 i).val = (w i).val + 1 ∨
              (w i).val = (k.1 i).val + 1 := by
            by_cases hle : (w i).val ≤ (k.1 i).val
            · rw [Nat.dist_eq_sub_of_le hle] at hdist
              omega
            · have hle' : (k.1 i).val ≤ (w i).val := le_of_not_ge hle
              rw [Nat.dist_eq_sub_of_le_right hle'] at hdist
              omega
          rcases hcase with hup | hdown
          · have hn : (w i).val + 1 ≤ n := by
              have ht : (w i).val + 1 < n + 1 := by simpa [hup] using (k.1 i).isLt
              omega
            have hval : stepValue (i, true) = k.1 i := by
              apply Fin.ext
              simp [stepValue, min_eq_left hn]
              omega
            have hvec : Function.update w i (stepValue (i, true)) = k.1 := by
              funext j
              by_cases hji : j = i
              · subst j
                simpa using hval
              · calc
                  Function.update w i (stepValue (i, true)) j = w j :=
                    Function.update_of_ne hji _ _
                  _ = k.1 j := by simpa [w] using hother j hji
            have hkey : (Function.update w i (stepValue (i, true)), KeyFlag6.boundary) = k :=
              Prod.ext hvec hkflag.symm
            apply Finset.mem_union_right
            apply Finset.mem_image.mpr
            exact ⟨(i, true), Finset.mem_univ _, hkey⟩
          · have hval : stepValue (i, false) = k.1 i := by
              apply Fin.ext
              simp [stepValue]
              omega
            have hvec : Function.update w i (stepValue (i, false)) = k.1 := by
              funext j
              by_cases hji : j = i
              · subst j
                simpa using hval
              · calc
                  Function.update w i (stepValue (i, false)) j = w j :=
                    Function.update_of_ne hji _ _
                  _ = k.1 j := by simpa [w] using hother j hji
            have hkey : (Function.update w i (stepValue (i, false)), KeyFlag6.boundary) = k :=
              Prod.ext hvec hkflag.symm
            apply Finset.mem_union_right
            apply Finset.mem_image.mpr
            exact ⟨(i, false), Finset.mem_univ _, hkey⟩
      have hsameCard : sameKeys.card ≤ 2 := by simp [sameKeys]
      have hstepCard : stepKeys.card ≤ 2 * coarseChunkCount := by
        calc
          stepKeys.card ≤ (Finset.univ : Finset (Fin coarseChunkCount × Bool)).card :=
            Finset.card_image_le
          _ = 2 * coarseChunkCount := by simp; ring
      have hcandidate : candidate.card ≤ 602 := by
        calc
          candidate.card ≤ sameKeys.card + stepKeys.card := Finset.card_union_le _ _
          _ ≤ 2 + 2 * coarseChunkCount := Nat.add_le_add hsameCard hstepCard
          _ = 602 := by norm_num [coarseChunkCount]
      exact (Finset.card_le_card hsubset).trans hcandidate }
  · intro x y i hxy hflip j hji
    obtain ⟨k, hneq, hsame⟩ := adjData hxy
    rcases hflip with ⟨a, ha, haxy⟩
    have hak : a = k := by
      have hmem : a ∈ Finset.univ.filter (fun t : Fin n => x t ≠ y t) :=
        Finset.mem_filter.mpr ⟨Finset.mem_univ _, haxy⟩
      have hsingle : Finset.univ.filter (fun t : Fin n => x t ≠ y t) = {k} := by
        have hcard : (Finset.univ.filter (fun t : Fin n => x t ≠ y t)).card = 1 := hxy
        obtain ⟨k', hk'⟩ := Finset.card_eq_one.mp hcard
        have hkmem : k ∈ Finset.univ.filter (fun t : Fin n => x t ≠ y t) :=
          Finset.mem_filter.mpr ⟨Finset.mem_univ _, hneq⟩
        have hkEq : k' = k := by
          rw [hk'] at hkmem
          exact (Finset.mem_singleton.mp hkmem).symm
        rw [hkEq] at hk'
        exact hk'
      rw [hsingle] at hmem
      exact Finset.mem_singleton.mp hmem
    have hknot : k ∉ L.fineChunks j := by
      intro hkj
      subst a
      have hdisj := L.chunks_disjoint.2.2.1 i j (Ne.symm hji)
      exact (Finset.disjoint_left.mp hdisj) ha hkj
    have hagree : ∀ b, b ∈ L.fineChunks j → x b = y b := by
      intro b hb
      by_cases hbk : b = k
      · subst b
        exact (hknot hb).elim
      · exact hsame b hbk
    have hcount : L.fineCount x j = L.fineCount y j := by
      exact filterCardEq (L.fineChunks j) hagree
    simpa [ChunkLayout6.sign, hcount]
  · intro x y hxy hflip
    obtain ⟨k, hneq, hsame⟩ := adjData hxy
    rcases hflip with ⟨i, a, ha, haxy⟩
    have hak : a = k := by
      have hmem : a ∈ Finset.univ.filter (fun t : Fin n => x t ≠ y t) :=
        Finset.mem_filter.mpr ⟨Finset.mem_univ _, haxy⟩
      have hcard : (Finset.univ.filter (fun t : Fin n => x t ≠ y t)).card = 1 := hxy
      obtain ⟨k', hk'⟩ := Finset.card_eq_one.mp hcard
      have hkmem : k ∈ Finset.univ.filter (fun t : Fin n => x t ≠ y t) :=
        Finset.mem_filter.mpr ⟨Finset.mem_univ _, hneq⟩
      have hkEq : k' = k := by
        rw [hk'] at hkmem
        exact (Finset.mem_singleton.mp hkmem).symm
      rw [hkEq] at hk'
      rw [hk'] at hmem
      exact Finset.mem_singleton.mp hmem
    subst a
    have hknot (j : Fin L.m) (hji : j ≠ i) : k ∉ L.fineChunks j := by
      intro hkj
      have hdisj := L.chunks_disjoint.2.2.1 i j (Ne.symm hji)
      exact (Finset.disjoint_left.mp hdisj) ha hkj
    have hcount (j : Fin L.m) (hji : j ≠ i) :
        L.fineCount x j = L.fineCount y j := by
      apply filterCardEq
      intro b hb
      by_cases hbk : b = k
      · subst b
        exact (hknot j hji hb).elim
      · exact hsame b hbk
    let A := Finset.univ.filter fun j : Fin L.m =>
      Nat.dist (2 * L.fineCount x j) L.fineLength ≤ 11
    let B := Finset.univ.filter fun j : Fin L.m =>
      Nat.dist (2 * L.fineCount y j) L.fineLength ≤ 11
    have hErase : A.erase i = B.erase i := by
      ext j
      by_cases hji : j = i
      · subst j
        simp [A, B]
      · simp only [Finset.mem_erase, A, B, Finset.mem_filter, Finset.mem_univ, true_and]
        rw [hcount j hji]
    have hcardErase (S : Finset (Fin L.m)) :
        S.card = (S.erase i).card + if i ∈ S then 1 else 0 := by
      by_cases hi : i ∈ S
      · rw [← Finset.insert_erase hi, Finset.card_insert_of_notMem (by simp)]
        simp [hi]
      · simp [hi]
    have hAcard := hcardErase A
    have hBcard := hcardErase B
    have hab : A.card ≤ B.card + 1 := by
      simp only [hAcard, hBcard, hErase]
      by_cases hiA : i ∈ A <;> by_cases hiB : i ∈ B <;> simp [hiA, hiB] <;> omega
    have hba : B.card ≤ A.card + 1 := by
      simp only [hAcard, hBcard, hErase]
      by_cases hiA : i ∈ A <;> by_cases hiB : i ∈ B <;> simp [hiA, hiB] <;> omega
    change Nat.dist A.card B.card ≤ 1
    by_cases hle : A.card ≤ B.card
    · rw [Nat.dist_eq_sub_of_le hle]
      omega
    · have hle' : B.card ≤ A.card := le_of_not_ge hle
      rw [Nat.dist_eq_sub_of_le_right hle']
      omega
  · intro x y hxy hnonfine
    have hcount : ∀ i : Fin L.m, L.fineCount x i = L.fineCount y i := by
      intro i
      apply filterCardEq
      intro a ha
      exact hnonfine i a ha
    refine ⟨?_, ?_, ?_⟩
    · funext i
      simp [ChunkLayout6.sign, hcount i]
    · ext i
      simp [ChunkLayout6.flippable, hcount i]
    · simp [ChunkLayout6.severity, hcount]
  · intro x y hxy hnoncoarse
    have hcount : ∀ i : Fin coarseChunkCount, L.coarseCount x i = L.coarseCount y i := by
      intro i
      apply filterCardEq
      intro a ha
      exact hnoncoarse i a ha
    have hbin : L.coarseBin x = L.coarseBin y := by
      funext i
      simp [ChunkLayout6.coarseBin, hcount i]
    have hcountFlip : ∀ i : Fin coarseChunkCount, ∀ a : Fin n,
        L.coarseCount (flipVertex6 x a) i = L.coarseCount (flipVertex6 y a) i := by
      intro i a
      apply filterCardEq
      intro b hb
      by_cases hba : b = a
      · subst b
        simp [flipVertex6, hnoncoarse i a hb]
      · simp [flipVertex6, hba, hnoncoarse i b hb]
    have hbinFlip : ∀ i : Fin coarseChunkCount, ∀ a : Fin n,
        L.coarseBin (flipVertex6 x a) = L.coarseBin (flipVertex6 y a) := by
      intro i a
      funext j
      simp [ChunkLayout6.coarseBin, hcountFlip j a]
    have hboundary : L.boundary x ↔ L.boundary y := by
      unfold ChunkLayout6.boundary
      constructor
      · rintro ⟨i, a, ha, hneq⟩
        refine ⟨i, a, ha, ?_⟩
        simpa [hbinFlip i a, hbin] using hneq
      · rintro ⟨i, a, ha, hneq⟩
        refine ⟨i, a, ha, ?_⟩
        simpa [hbinFlip i a, hbin] using hneq
    simp [ChunkLayout6.key, hbin, hboundary]
  · intro x y hxy hflip
    by_cases hvec : L.coarseBin x = L.coarseBin y
    · change keyAdjacent6 binAdjacent6 (L.key x) (L.key y)
      unfold keyAdjacent6
      exact Or.inr (Or.inl (by simpa [ChunkLayout6.key] using hvec))
    · obtain ⟨k, hneq, hsame⟩ := adjData hxy
      rcases hflip with ⟨i, a, ha, haxy⟩
      have hak : a = k := by
        by_contra hne
        exact haxy (hsame a hne)
      subst a
      have hk : k ∈ L.coarseChunks i := ha
      have hcount (j : Fin coarseChunkCount) (hji : j ≠ i) :
          L.coarseCount x j = L.coarseCount y j := by
        apply filterCardEq
        intro b hb
        by_cases hbk : b = k
        · subst b
          have hdisj := L.chunks_disjoint.1 j i hji
          exact False.elim ((Finset.disjoint_left.mp hdisj) hb hk)
        · exact hsame b hbk
      have hcountStep :
          L.coarseCount x i + 1 = L.coarseCount y i ∨
            L.coarseCount y i + 1 = L.coarseCount x i := by
        simpa [ChunkLayout6.coarseCount] using
          filterCardStep (L.coarseChunks i) k hk hneq hsame
      have hvalueNe : (L.coarseBin x i).val ≠ (L.coarseBin y i).val := by
        intro heq
        apply hvec
        funext j
        by_cases hji : j = i
        · subst j
          exact Fin.ext heq
        · simp [ChunkLayout6.coarseBin, hcount j hji]
      have hdistle : Nat.dist (L.coarseBin x i).val (L.coarseBin y i).val ≤ 1 := by
        change Nat.dist (L.bin i (L.coarseCount x i)).val
          (L.bin i (L.coarseCount y i)).val ≤ 1
        rcases hcountStep with hxyc | hyxc
        · rw [← hxyc]
          have hmono := L.bin_monotone i (L.coarseCount x i)
            (L.coarseCount x i + 1) (Nat.le_succ _)
          have hstep := L.bin_step i (L.coarseCount x i)
          rw [Nat.dist_eq_sub_of_le hmono]
          omega
        · rw [← hyxc]
          have hmono := L.bin_monotone i (L.coarseCount y i)
            (L.coarseCount y i + 1) (Nat.le_succ _)
          have hstep := L.bin_step i (L.coarseCount y i)
          rw [Nat.dist_eq_sub_of_le_right hmono]
          omega
      have hdist : Nat.dist (L.coarseBin x i).val (L.coarseBin y i).val = 1 := by
        have hne : Nat.dist (L.coarseBin x i).val (L.coarseBin y i).val ≠ 0 := by
          intro hz
          exact hvalueNe (Nat.eq_of_dist_eq_zero hz)
        omega
      have hbinAdj : binAdjacent6 (L.coarseBin x) (L.coarseBin y) := by
        refine ⟨i, ?_, hdist⟩
        intro j hji
        simp [ChunkLayout6.coarseBin, hcount j hji]
      have hends := changing hxy hvec
      change keyAdjacent6 binAdjacent6 (L.key x) (L.key y)
      unfold keyAdjacent6
      refine Or.inr (Or.inr ⟨?_, ?_, hbinAdj⟩)
      · simp [ChunkLayout6.key, hends.1]
      · simp [ChunkLayout6.key, hends.2]
set_option maxRecDepth 1000

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
