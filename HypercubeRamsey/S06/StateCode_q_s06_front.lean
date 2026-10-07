import HypercubeRamsey.S06.ChunkGeometry
import HypercubeRamsey.Tools.CubeGeometry

namespace HypercubeRamsey.Lane_q_s06_front

open Classical
open OAI.HypercubeRamsey
open scoped BigOperators

noncomputable section

variable {n : ℕ}

abbrev StateTuple6 (L : S06.ChunkLayout6 n) :=
  ({a // a ∈ L.residual} → Bool) × S06.BinVector6 n × S06.KeyFlag6 ×
    (Fin L.m → Fin (n + 1)) × Fin (L.m + 1)

def stateOfTuple6 (L : S06.ChunkLayout6 n) (x : CubeVertex n) : StateTuple6 L :=
  (fun a => x a.1, L.coarseBin x, (L.key x).2,
    fun i => ⟨min (L.mergedCount x i) n, by omega⟩,
    S06.sevFin6 L.m (L.severity x))

def binImage6 (L : S06.ChunkLayout6 n) (i : Fin S06.coarseChunkCount) : Finset (Fin (n + 1)) :=
  (Finset.range ((L.coarseChunks i).card + 1)).image (L.bin i)

abbrev BinCoord6 (L : S06.ChunkLayout6 n) :=
  Σ i : Fin S06.coarseChunkCount, {w : Fin (n + 1) // w ∈ binImage6 L i}

abbrev CodeCoord6 (L : S06.ChunkLayout6 n) :=
  Sum {a : Fin n // a ∈ L.residual}
    (Sum (BinCoord6 L)
      (Sum Unit (Sum (Fin L.m × Fin (L.fineLength + 1)) (Fin (L.m + 1)))))

def residualCoord6 (L : S06.ChunkLayout6 n) (a : {j : Fin n // j ∈ L.residual}) : CodeCoord6 L :=
  .inl a

def binCoord6 (L : S06.ChunkLayout6 n) (i : Fin S06.coarseChunkCount)
    (w : {w : Fin (n + 1) // w ∈ binImage6 L i}) : CodeCoord6 L :=
  .inr (.inl ⟨i, w⟩)

def flagCoord6 (L : S06.ChunkLayout6 n) : CodeCoord6 L := .inr (.inr (.inl ()))

def fineCoord6 (L : S06.ChunkLayout6 n) (i : Fin L.m) (q : Fin (L.fineLength + 1)) : CodeCoord6 L :=
  .inr (.inr (.inr (.inl ⟨i, q⟩)))

def severityCoord6 (L : S06.ChunkLayout6 n) (q : Fin (L.m + 1)) : CodeCoord6 L :=
  .inr (.inr (.inr (.inr q)))

def codeBit6 (L : S06.ChunkLayout6 n) (s : StateTuple6 L) : CodeCoord6 L → Bool
  | .inl a => s.1 a
  | .inr (.inl ⟨i, w⟩) => decide (s.2.1 i = w.1)
  | .inr (.inr (.inl _)) => decide (s.2.2.1 = .boundary)
  | .inr (.inr (.inr (.inl ⟨i, t⟩))) => decide (t.val = (s.2.2.2.1 i).val)
  | .inr (.inr (.inr (.inr t))) => decide (t.val = (s.2.2.2.2).val)

noncomputable def coordEquiv6 (L : S06.ChunkLayout6 n) :
    CodeCoord6 L ≃ Fin (Fintype.card (CodeCoord6 L)) := Fintype.equivFin _

def encodeTuple6 (L : S06.ChunkLayout6 n) (s : StateTuple6 L) :
    CubeVertex (Fintype.card (CodeCoord6 L)) :=
  fun j => codeBit6 L s ((coordEquiv6 L).symm j)

theorem encodeTuple6_at (L : S06.ChunkLayout6 n) (s : StateTuple6 L) (c : CodeCoord6 L) :
    encodeTuple6 L s (coordEquiv6 L c) = codeBit6 L s c := by
  simp [encodeTuple6]

def stNbrTuple6 (L : S06.ChunkLayout6 n) (b : StateTuple6 L) : Finset (StateTuple6 L) :=
  Finset.univ.filter fun a => ∃ u v : CubeVertex n, ¬ IsEvenRole u ∧ IsEvenRole v ∧
    stateOfTuple6 L u = b ∧ stateOfTuple6 L v = a ∧ (cube n).Adj u v

def residualDistTuple6 (L : S06.ChunkLayout6 n) (x y : CubeVertex n) : ℕ :=
  (L.residual.filter fun a => x a ≠ y a).card

/-- Lane-local form of the code data, kept separate from the frozen Section 6 declaration. -/
structure StateCodeAux6 (L : S06.ChunkLayout6 n) where
  d : ℕ
  enc : StateTuple6 L → CubeVertex d
  enc_injective : ∀ x y, enc (stateOfTuple6 L x) = enc (stateOfTuple6 L y) →
    stateOfTuple6 L x = stateOfTuple6 L y
  nbr_dist : ∀ b, ∀ a ∈ stNbrTuple6 L b, ∀ a' ∈ stNbrTuple6 L b,
    hammingDist (enc a) (enc a') ≤ S06.D₀₆
  residual_dist : ∀ x y, residualDistTuple6 L x y ≤
    hammingDist (enc (stateOfTuple6 L x)) (enc (stateOfTuple6 L y))
  d_lower : S06.cd₆ * n ≤ d
  d_upper : (d : ℝ) ≤ S06.Cd₆ * n

def diffCoords6 (L : S06.ChunkLayout6 n) (s t : StateTuple6 L) : Finset (CodeCoord6 L) :=
  Finset.univ.filter fun c => codeBit6 L s c ≠ codeBit6 L t c

theorem hammingDist_encode_eq (L : S06.ChunkLayout6 n) (s t : StateTuple6 L) :
    hammingDist (encodeTuple6 L s) (encodeTuple6 L t) = (diffCoords6 L s t).card := by
  classical
  let e := coordEquiv6 L
  let fromFinEq : {j : Fin (Fintype.card (CodeCoord6 L)) //
      (encodeTuple6 L s) j = (encodeTuple6 L t) j} ≃
      {c : CodeCoord6 L // codeBit6 L s c = codeBit6 L t c} := {
    toFun := fun j => ⟨e.symm j.1, by
      simpa [encodeTuple6] using j.2⟩
    invFun := fun c => ⟨e c.1, by
      simpa [encodeTuple6, e] using c.2⟩
    left_inv := by intro j; apply Subtype.ext; simp
    right_inv := by intro c; apply Subtype.ext; simp }
  have hEqCard := Fintype.card_congr fromFinEq
  have hFinSum : hammingDist (encodeTuple6 L s) (encodeTuple6 L t) +
      Fintype.card {j : Fin (Fintype.card (CodeCoord6 L)) //
        (encodeTuple6 L s) j = (encodeTuple6 L t) j} =
      Fintype.card (Fin (Fintype.card (CodeCoord6 L))) := by
    have hsum := Finset.card_filter_add_card_filter_not
      (s := Finset.univ) (fun j : Fin (Fintype.card (CodeCoord6 L)) =>
        (encodeTuple6 L s) j = (encodeTuple6 L t) j)
    simpa [HypercubeRamsey.hammingDist, Fintype.card_subtype, ne_eq, add_comm] using hsum
  have hCoordSum : (diffCoords6 L s t).card +
      Fintype.card {c : CodeCoord6 L // codeBit6 L s c = codeBit6 L t c} =
      Fintype.card (CodeCoord6 L) := by
    have hsum := Finset.card_filter_add_card_filter_not
      (s := Finset.univ) (fun c : CodeCoord6 L => codeBit6 L s c ≠ codeBit6 L t c)
    simpa [diffCoords6, Fintype.card_subtype, ne_eq] using hsum
  have hTotal : Fintype.card (Fin (Fintype.card (CodeCoord6 L))) =
      Fintype.card (CodeCoord6 L) := by simp
  omega

theorem hammingDist_encode_le_support (L : S06.ChunkLayout6 n) (s t : StateTuple6 L)
    (S : Finset (CodeCoord6 L)) (hS : diffCoords6 L s t ⊆ S) :
    hammingDist (encodeTuple6 L s) (encodeTuple6 L t) ≤ S.card := by
  rw [hammingDist_encode_eq]
  exact Finset.card_le_card hS

theorem binValue_mem6 (L : S06.ChunkLayout6 n) (x : CubeVertex n)
    (i : Fin S06.coarseChunkCount) : L.coarseBin x i ∈ binImage6 L i := by
  apply Finset.mem_image.mpr
  refine ⟨L.coarseCount x i, ?_, rfl⟩
  simp only [Finset.mem_range]
  exact Nat.lt_succ_of_le (Finset.card_filter_le _ _)

theorem mergedCount_le_fineLength6 (L : S06.ChunkLayout6 n) (x : CubeVertex n)
    (i : Fin L.m) : L.mergedCount x i ≤ L.fineLength := by
  have hcount : L.fineCount x i ≤ L.fineLength := by
    calc
      L.fineCount x i ≤ (L.fineChunks i).card := Finset.card_filter_le _ _
      _ = L.fineLength := L.fine_chunk_length i
  dsimp [S06.ChunkLayout6.mergedCount]
  split_ifs <;> omega

theorem codeBit_eq_of_encode_eq6 (L : S06.ChunkLayout6 n)
    (s t : StateTuple6 L) (h : encodeTuple6 L s = encodeTuple6 L t) :
    ∀ c, codeBit6 L s c = codeBit6 L t c := by
  intro c
  have hc := congrFun h (coordEquiv6 L c)
  simpa only [encodeTuple6_at] using hc

theorem stateOfTuple_injective6 (L : S06.ChunkLayout6 n) (hLen : L.fineLength ≤ n)
    {x y : CubeVertex n}
    (h : encodeTuple6 L (stateOfTuple6 L x) = encodeTuple6 L (stateOfTuple6 L y)) :
    stateOfTuple6 L x = stateOfTuple6 L y := by
  classical
  let sx := stateOfTuple6 L x
  let sy := stateOfTuple6 L y
  have hbit := codeBit_eq_of_encode_eq6 L sx sy h
  have hres : sx.1 = sy.1 := by
    funext a
    simpa [codeBit6] using hbit (.inl a)
  have hbin : sx.2.1 = sy.2.1 := by
    funext i
    let w := L.coarseBin x i
    have hw := binValue_mem6 L x i
    let c : CodeCoord6 L := .inr (.inl ⟨i, ⟨w, by simpa [w] using hw⟩⟩)
    have hc := hbit c
    have hcx : sx.2.1 i = w := by simp [sx, w, stateOfTuple6]
    have hdec : decide (sy.2.1 i = w) = true := by
      simpa [codeBit6, c, hcx] using hc.symm
    have hcy : sy.2.1 i = w := of_decide_eq_true hdec
    exact hcx.trans hcy.symm
  have hflag : sx.2.2.1 = sy.2.2.1 := by
    let c : CodeCoord6 L := .inr (.inr (.inl ()))
    have hc := hbit c
    cases hx : sx.2.2.1 <;> cases hy : sy.2.2.1 <;>
      simp_all [codeBit6, c]
  have hcounts : sx.2.2.2.1 = sy.2.2.2.1 := by
    funext i
    let vx := L.mergedCount x i
    let vy := L.mergedCount y i
    have hvxEll : vx ≤ L.fineLength := mergedCount_le_fineLength6 L x i
    have hvyEll : vy ≤ L.fineLength := mergedCount_le_fineLength6 L y i
    have hvxN : vx ≤ n := hvxEll.trans hLen
    have hvyN : vy ≤ n := hvyEll.trans hLen
    have hsx : (sx.2.2.2.1 i).val = vx := by
      simp [sx, vx, stateOfTuple6, Nat.min_eq_left hvxN]
    have hsy : (sy.2.2.2.1 i).val = vy := by
      simp [sy, vy, stateOfTuple6, Nat.min_eq_left hvyN]
    let q : Fin (L.fineLength + 1) := ⟨vx, Nat.lt_succ_of_le hvxEll⟩
    let c : CodeCoord6 L := .inr (.inr (.inr (.inl ⟨i, q⟩)))
    have hc := hbit c
    have hdec : decide (vx = vy) = true := by
      simpa [codeBit6, c, q, hsx, hsy] using hc.symm
    have hvy : vx = vy := of_decide_eq_true hdec
    apply Fin.ext
    omega
  have hsev : sx.2.2.2.2 = sy.2.2.2.2 := by
    let q := sx.2.2.2.2
    let c : CodeCoord6 L := .inr (.inr (.inr (.inr q)))
    have hc := hbit c
    have hdec : decide (q.val = sy.2.2.2.2.val) = true := by
      simpa [codeBit6, c, q] using hc.symm
    apply Fin.ext
    exact of_decide_eq_true hdec
  change sx = sy
  apply Prod.ext
  · exact hres
  · apply Prod.ext
    · exact hbin
    · apply Prod.ext
      · exact hflag
      · apply Prod.ext
        · exact hcounts
        · exact hsev

theorem residualDist_le_encode6 (L : S06.ChunkLayout6 n) (x y : CubeVertex n) :
    residualDistTuple6 L x y ≤
      hammingDist (encodeTuple6 L (stateOfTuple6 L x)) (encodeTuple6 L (stateOfTuple6 L y)) := by
  classical
  let A := L.residual.filter fun a => x a ≠ y a
  let R := A.attach
  let f (a : {j : Fin n // j ∈ A}) : Fin (Fintype.card (CodeCoord6 L)) :=
    coordEquiv6 L (.inl ⟨a.1, (Finset.mem_filter.mp a.2).1⟩)
  have hf : Function.Injective f := by
    intro a b hab
    have hcoord := (coordEquiv6 L).injective hab
    have hval := Sum.inl.inj hcoord
    have hbase : a.1 = b.1 :=
      congrArg (fun z : {j : Fin n // j ∈ L.residual} => z.1) hval
    exact Subtype.ext hbase
  have hImage : R.image f ⊆ Finset.univ.filter fun j =>
      encodeTuple6 L (stateOfTuple6 L x) j ≠ encodeTuple6 L (stateOfTuple6 L y) j := by
    intro j hj
    rcases Finset.mem_image.mp hj with ⟨a, ha, rfl⟩
    have hxy : x a.1 ≠ y a.1 := (Finset.mem_filter.mp a.2).2
    have hx : encodeTuple6 L (stateOfTuple6 L x) (f a) = x a.1 := by
      simp [f, encodeTuple6_at, codeBit6, stateOfTuple6]
    have hy : encodeTuple6 L (stateOfTuple6 L y) (f a) = y a.1 := by
      simp [f, encodeTuple6_at, codeBit6, stateOfTuple6]
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, by simpa [hx, hy] using hxy⟩
  have hR : residualDistTuple6 L x y = R.card := by
    simp [residualDistTuple6, R, A]
  calc
    residualDistTuple6 L x y = R.card := hR
    _ = (R.image f).card := (Finset.card_image_of_injective _ hf).symm
    _ ≤ (Finset.univ.filter fun j =>
        encodeTuple6 L (stateOfTuple6 L x) j ≠ encodeTuple6 L (stateOfTuple6 L y) j).card :=
          Finset.card_le_card hImage
    _ = hammingDist (encodeTuple6 L (stateOfTuple6 L x))
        (encodeTuple6 L (stateOfTuple6 L y)) := by rfl

theorem countOn_eq_of_agree6 {ι : Type*} [DecidableEq ι] [Fintype ι] (S : Finset ι)
    (x y : ι → Bool) (h : ∀ a ∈ S, x a = y a) :
    (S.filter fun a => x a = true).card = (S.filter fun a => y a = true).card := by
  apply congrArg Finset.card
  ext a
  by_cases ha : a ∈ S
  · simp [ha, h a ha]
  · simp [ha]

theorem adjData6 {x y : CubeVertex n} (hxy : (cube n).Adj x y) :
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

theorem residual_edge_distance6 (L : S06.ChunkLayout6 n) (hflips : S06.ChunkFlips6 L)
    {x y : CubeVertex n} (hxy : (cube n).Adj x y) (k : Fin n)
    (hk : k ∈ L.residual) (hneq : x k ≠ y k) (hsame : ∀ j, j ≠ k → x j = y j) :
    hammingDist (encodeTuple6 L (stateOfTuple6 L x))
        (encodeTuple6 L (stateOfTuple6 L y)) ≤ 1 := by
  classical
  have hcoarse : ∀ i a, a ∈ L.coarseChunks i → x a = y a := by
    intro i a ha
    by_contra hne
    have hak : a = k := by
      by_contra hak
      exact hne (hsame a hak)
    subst a
    exact (Finset.disjoint_left.mp (L.chunks_disjoint.2.2.2.1 i)) ha hk
  have hfine : ∀ i a, a ∈ L.fineChunks i → x a = y a := by
    intro i a ha
    by_contra hne
    have hak : a = k := by
      by_contra hak
      exact hne (hsame a hak)
    subst a
    exact (Finset.disjoint_left.mp (L.chunks_disjoint.2.2.2.2 i)) ha hk
  have hkey := hflips.noncoarse_flip_key x y hxy hcoarse
  have hfacts := hflips.nonfine_flip_fine x y hxy hfine
  have hcount (i : Fin L.m) : L.fineCount x i = L.fineCount y i :=
    countOn_eq_of_agree6 (L.fineChunks i) x y (hfine i)
  let sx := stateOfTuple6 L x
  let sy := stateOfTuple6 L y
  have hbin : sx.2.1 = sy.2.1 := by
    simpa [sx, sy, stateOfTuple6, S06.ChunkLayout6.key] using congrArg Prod.fst hkey
  have hflag : sx.2.2.1 = sy.2.2.1 := by
    simpa [sx, sy, stateOfTuple6] using congrArg Prod.snd hkey
  have hcounts : sx.2.2.2.1 = sy.2.2.2.1 := by
    funext i
    simp [sx, sy, stateOfTuple6, S06.ChunkLayout6.mergedCount, hcount i]
  have hsev : sx.2.2.2.2 = sy.2.2.2.2 := by
    simpa [sx, sy, stateOfTuple6] using congrArg (S06.sevFin6 L.m) hfacts.2.2
  let c : CodeCoord6 L := residualCoord6 L ⟨k, hk⟩
  have hsub : diffCoords6 L sx sy ⊆ {c} := by
    intro q hq
    have hq' : codeBit6 L sx q ≠ codeBit6 L sy q := by simpa [diffCoords6] using hq
    rcases q with a | q
    · by_cases hak : a.1 = k
      · have ha : a = ⟨k, hk⟩ := Subtype.ext hak
        subst a
        simp [c, residualCoord6]
      · have heq : sx.1 a = sy.1 a := by
          simp [sx, sy, stateOfTuple6, hsame a.1 hak]
        exact False.elim (hq' heq)
    · rcases q with b | q
      · exact False.elim (hq' (by simp [codeBit6, sx, sy, hbin]))
      · rcases q with _ | q
        · exact False.elim (hq' (by simp [codeBit6, sx, sy, hflag]))
        · rcases q with f | q
          · exact False.elim (hq' (by simp [codeBit6, sx, sy, hcounts]))
          · exact False.elim (hq' (by simp [codeBit6, sx, sy, hsev]))
  exact hammingDist_encode_le_support L sx sy {c} hsub |>.trans (by simp)

theorem coordinateClass6 (L : S06.ChunkLayout6 n) (k : Fin n) :
    k ∈ L.residual ∨ (∃ i, k ∈ L.coarseChunks i) ∨ (∃ i, k ∈ L.fineChunks i) := by
  have hk : k ∈ (Finset.univ : Finset (Fin n)) := Finset.mem_univ k
  rw [← L.chunks_cover] at hk
  simp only [Finset.mem_union, Finset.mem_biUnion, Finset.mem_univ, true_and] at hk
  rcases hk with ((⟨i, hi⟩ | ⟨i, hi⟩) | hr)
  · exact Or.inr (Or.inl ⟨i, hi⟩)
  · exact Or.inr (Or.inr ⟨i, hi⟩)
  · exact Or.inl hr

theorem coarse_edge_distance6 (L : S06.ChunkLayout6 n) (hflips : S06.ChunkFlips6 L)
    {x y : CubeVertex n} (hxy : (cube n).Adj x y) (i : Fin S06.coarseChunkCount)
    (k : Fin n) (hk : k ∈ L.coarseChunks i) (hneq : x k ≠ y k)
    (hsame : ∀ j, j ≠ k → x j = y j)
    (hkeyrel : S06.keyAdjacent6 S06.binAdjacent6 (L.key x) (L.key y)) :
    hammingDist (encodeTuple6 L (stateOfTuple6 L x))
        (encodeTuple6 L (stateOfTuple6 L y)) ≤ 3 := by
  classical
  have hresBits : ∀ a ∈ L.residual, x a = y a := by
    intro a ha
    by_contra hne
    have hak : a = k := by
      by_contra hak
      exact hne (hsame a hak)
    subst a
    exact (Finset.disjoint_left.mp (L.chunks_disjoint.2.2.2.1 i)) hk ha
  have hfineBits : ∀ j a, a ∈ L.fineChunks j → x a = y a := by
    intro j a ha
    by_contra hne
    have hak : a = k := by
      by_contra hak
      exact hne (hsame a hak)
    subst a
    exact (Finset.disjoint_left.mp (L.chunks_disjoint.2.1 i j)) hk ha
  have hfacts := hflips.nonfine_flip_fine x y hxy hfineBits
  have hcount (j : Fin L.m) : L.fineCount x j = L.fineCount y j :=
    countOn_eq_of_agree6 (L.fineChunks j) x y (hfineBits j)
  let sx := stateOfTuple6 L x
  let sy := stateOfTuple6 L y
  have hres : sx.1 = sy.1 := by
    funext a
    simp [sx, sy, stateOfTuple6, hresBits a.1 a.2]
  have hcounts : sx.2.2.2.1 = sy.2.2.2.1 := by
    funext j
    simp [sx, sy, stateOfTuple6, S06.ChunkLayout6.mergedCount, hcount j]
  have hsev : sx.2.2.2.2 = sy.2.2.2.2 := by
    simpa [sx, sy, stateOfTuple6] using congrArg (S06.sevFin6 L.m) hfacts.2.2
  have hbinX : sx.2.1 = L.coarseBin x := by rfl
  have hbinY : sy.2.1 = L.coarseBin y := by rfl
  have hflagX : sx.2.2.1 = (L.key x).2 := by rfl
  have hflagY : sy.2.2.1 = (L.key y).2 := by rfl
  rcases hkeyrel with hkeys | hbins | hbdry
  · have hbin : sx.2.1 = sy.2.1 := by
      simpa [hbinX, hbinY, S06.ChunkLayout6.key] using congrArg Prod.fst hkeys
    have hflag : sx.2.2.1 = sy.2.2.1 := by
      simpa [hflagX, hflagY] using congrArg Prod.snd hkeys
    have hbits : ∀ c, codeBit6 L sx c = codeBit6 L sy c := by
      intro c
      rcases c with a | c
      · simp [codeBit6, hres]
      · rcases c with b | c
        · simp [codeBit6, hbin]
        · rcases c with _ | c
          · simp [codeBit6, hflag]
          · rcases c with f | c
            · simp [codeBit6, hcounts]
            · simp [codeBit6, hsev]
    change hammingDist (encodeTuple6 L sx) (encodeTuple6 L sy) ≤ 3
    rw [hammingDist_encode_eq]
    simp [diffCoords6, hbits]
  · have hbin : sx.2.1 = sy.2.1 := by
      simpa [hbinX, hbinY, S06.ChunkLayout6.key] using hbins
    let c : CodeCoord6 L := flagCoord6 L
    have hsub : diffCoords6 L sx sy ⊆ {c} := by
      intro q hq
      have hq' : codeBit6 L sx q ≠ codeBit6 L sy q := by simpa [diffCoords6] using hq
      rcases q with a | q
      · exact False.elim (hq' (by simp [codeBit6, hres]))
      · rcases q with b | q
        · exact False.elim (hq' (by simp [codeBit6, hbin]))
        · rcases q with _ | q
          · simp [c, flagCoord6]
          · rcases q with f | q
            · exact False.elim (hq' (by simp [codeBit6, hcounts]))
            · exact False.elim (hq' (by simp [codeBit6, hsev]))
    exact (hammingDist_encode_le_support L sx sy {c} hsub).trans (by simp)
  · obtain ⟨j, hsameBins, _hstep⟩ := hbdry.2.2
    let wx : Fin (n + 1) := L.coarseBin x j
    let wy : Fin (n + 1) := L.coarseBin y j
    let cx : CodeCoord6 L := binCoord6 L j ⟨wx, by
      simpa [binImage6] using binValue_mem6 L x j⟩
    let cy : CodeCoord6 L := binCoord6 L j ⟨wy, by
      simpa [binImage6] using binValue_mem6 L y j⟩
    have hbinJX : sx.2.1 j = wx := by simp [sx, wx, stateOfTuple6]
    have hbinJY : sy.2.1 j = wy := by simp [sy, wy, stateOfTuple6]
    have hflag : sx.2.2.1 = sy.2.2.1 := by
      cases hx : (L.key x).2 <;> cases hy : (L.key y).2 <;>
        simp_all [hflagX, hflagY]
    have hsub : diffCoords6 L sx sy ⊆ {cx, cy} := by
      intro q hq
      have hq' : codeBit6 L sx q ≠ codeBit6 L sy q := by simpa [diffCoords6] using hq
      rcases q with a | q
      · exact False.elim (hq' (by simp [codeBit6, hres]))
      · rcases q with b | q
        · rcases b with ⟨j', w⟩
          by_cases hj : j' = j
          · subst j'
            by_cases hxw : sx.2.1 j = w.1
            · have hwx : w.1 = wx := hxw.symm.trans hbinJX
              have heq : binCoord6 L j w = cx := by
                apply congrArg (binCoord6 L j)
                exact Subtype.ext hwx
              exact Finset.mem_insert.mpr (Or.inl heq)
            · have hyw : sy.2.1 j = w.1 := by
                by_contra hyw
                exact hq' (by simp [codeBit6, hxw, hyw])
              have hwy : w.1 = wy := hyw.symm.trans hbinJY
              have heq : binCoord6 L j w = cy := by
                apply congrArg (binCoord6 L j)
                exact Subtype.ext hwy
              exact Finset.mem_insert.mpr (Or.inr (Finset.mem_singleton.mpr heq))
          · have hsame := hsameBins j' hj
            have hsame' : sx.2.1 j' = sy.2.1 j' := by
              simpa [hbinX, hbinY, S06.ChunkLayout6.key] using hsame
            exact False.elim (hq' (by simp [codeBit6, hsame']))
        · rcases q with _ | q
          · exact False.elim (hq' (by simp [codeBit6, hflag]))
          · rcases q with f | q
            · exact False.elim (hq' (by simp [codeBit6, hcounts]))
            · exact False.elim (hq' (by simp [codeBit6, hsev]))
    have hcard : ({cx, cy} : Finset (CodeCoord6 L)).card ≤ 2 := by
      change (insert cx ({cy} : Finset (CodeCoord6 L))).card ≤ 2
      calc
        _ ≤ ({cy} : Finset (CodeCoord6 L)).card + 1 := Finset.card_insert_le cx {cy}
        _ = 2 := by simp
    exact (hammingDist_encode_le_support L sx sy {cx, cy} hsub).trans (by omega)

end

end HypercubeRamsey.Lane_q_s06_front
