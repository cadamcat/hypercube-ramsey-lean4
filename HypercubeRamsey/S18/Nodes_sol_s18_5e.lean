import HypercubeRamsey.S18.Nodes_q_s18_n6
import HypercubeRamsey.S18.Nodes_q_s18_n5
import HypercubeRamsey.S18.Independence_sol_s18_n5
import HypercubeRamsey.S18.Nodes_sol_split_d18l_sol_d18l_pal

namespace HypercubeRamsey.Lane_sol_s18_5e

set_option maxHeartbeats 400000

open Classical Filter
open HypercubeRamsey.S18
open HypercubeRamsey.Lane_q_s18_n6
open scoped BigOperators

variable {κ : CConsts} {T : Stage} {k : ℕ}
  {PT : ProfiledTiling κ T k} {hPT : PT.Valid}

lemma row_patch (D : LateData hPT) (A : InitialPairData D)
    {v : Pos T k} (hv : v ∈ A.rows) : D.geom.patchOf v = A.paletteIndex.1 := by
  have h := (Finset.mem_filter.mp (A.rows_subset hv)).2.2
  exact congrArg Sigma.fst h


lemma paletteScale_pos (D : LateData hPT) (p : PaletteIndex D) :
    0 < D.paletteScale p := by
  unfold LateData.paletteScale
  have hM : (0 : ℝ) < (PT.tiling.P p.1).M := by
    rw [← (PT.tiling.P p.1).cardX]
    exact_mod_cast Finset.card_pos.mpr (hPT.tiling_valid.patch_nonempty p.1).1
  have hchi : (0 : ℝ) < D.chi p.1 := by exact_mod_cast D.chi_pos p.1
  exact div_pos hM hchi

lemma nonisolated_row_mem (D : LateData hPT) (A : InitialPairData D)
    {v : Pos T k} (hv : v ∈ D.nonisolates A.rows) : v ∈ A.rows :=
  (Finset.mem_filter.mp hv).1

lemma mask_flip (D : LateData hPT) (v : Pos T k) (a : Fin (T.S.n k))
    (ha : a ∈ PT.tiling.bulkCoords (D.geom.patchOf v)) :
    pairQueryOuterMask D (flipPos v a) = flipPos (pairQueryOuterMask D v) a := by
  have hp := patchOf_flipPos_of_bulk D v a ha
  have hn := (Finset.mem_filter.mp ha).2.2
  unfold pairQueryOuterMask
  rw [hp]
  funext j
  by_cases hj : j = a
  · subst j
    simp [hn, flipPos]
  · simp [flipPos, hj]

noncomputable def sliceCandidates (D : LateData hPT) (A : InitialPairData D) :=
  (pairQueryCandidateSet D A).filter fun q =>
    ∀ q' ∈ pairQueryCandidateSet D A,
      pairQueryOuterMask D (flipPos q.1 q.2) =
        pairQueryOuterMask D (flipPos q'.1 q'.2) →
      pairQueryOuterFamilyCode D q.1 ≤ pairQueryOuterFamilyCode D q'.1

lemma sliceCandidates_sameFamily (D : LateData hPT) (A : InitialPairData D)
    {q q' : Pos T k × Fin (T.S.n k)}
    (hq : q ∈ sliceCandidates D A) (hq' : q' ∈ sliceCandidates D A)
    (hs : pairQueryOuterMask D (flipPos q.1 q.2) =
      pairQueryOuterMask D (flipPos q'.1 q'.2)) :
    pairQueryOuterFamilyCode D q.1 = pairQueryOuterFamilyCode D q'.1 := by
  rcases Finset.mem_filter.mp hq with ⟨hqc, hq⟩
  rcases Finset.mem_filter.mp hq' with ⟨hq'c, hq'⟩
  exact le_antisymm (hq q' hq'c hs) (hq' q hqc hs.symm)

lemma flip_eq_of_same_mask (D : LateData hPT)
    {v w : Pos T k} {a b : Fin (T.S.n k)}
    (ha : a ∈ PT.tiling.bulkCoords (D.geom.patchOf v))
    (hb : b ∈ PT.tiling.bulkCoords (D.geom.patchOf w))
    (hm : pairQueryOuterMask D v = pairQueryOuterMask D w)
    (he : flipPos v a = flipPos w b) : v = w ∧ a = b := by
  have ho := congrArg (pairQueryOuterMask D) he
  rw [mask_flip D v a ha, mask_flip D w b hb, hm] at ho
  have hab : a = b := by
    by_contra hn
    have h := congrFun ho a
    simp only [flipPos, Function.update_self, Function.update_of_ne hn] at h
    cases hval : pairQueryOuterMask D w a <;> simp [hval] at h
  subst b
  constructor
  · funext j
    have h := congrFun he j
    by_cases hj : j = a
    · subst j
      simpa [flipPos] using h
    · simpa [flipPos, hj] using h
  · rfl

lemma sliceCandidates_injective (D : LateData hPT) (A : InitialPairData D) :
    Function.Injective (fun q : {q // q ∈ sliceCandidates D A} =>
      flipPos q.1.1 q.1.2) := by
  intro q q' he
  have hcode := sliceCandidates_sameFamily D A q.2 q'.2
    (congrArg (pairQueryOuterMask D) he)
  have hm := (pairQueryOuterFamily_eq_of_code_eq D hcode).2
  have hc := (mem_pairQueryCandidateSet D A q.1).mp (Finset.mem_filter.mp q.2).1
  have hc' := (mem_pairQueryCandidateSet D A q'.1).mp (Finset.mem_filter.mp q'.2).1
  rcases flip_eq_of_same_mask D hc.2.2 hc'.2.2 hm he with ⟨hv, ha⟩
  exact Subtype.ext (Prod.ext hv ha)

/-- Every discarded incidence has a witness from a different even outer word
in the same observed slice. The selection uses positions alone. -/
lemma discarded_witness (D : LateData hPT) (A : InitialPairData D)
    {q : Pos T k × Fin (T.S.n k)}
    (hq : q ∈ pairQueryCandidateSet D A \ sliceCandidates D A) :
    ∃ q' ∈ pairQueryCandidateSet D A,
      pairQueryOuterMask D (flipPos q.1 q.2) =
        pairQueryOuterMask D (flipPos q'.1 q'.2) ∧
      pairQueryOuterMask D q.1 ≠ pairQueryOuterMask D q'.1 := by
  rcases Finset.mem_sdiff.mp hq with ⟨hc, hn⟩
  have hn' : ¬ ∀ q' ∈ pairQueryCandidateSet D A,
      pairQueryOuterMask D (flipPos q.1 q.2) =
        pairQueryOuterMask D (flipPos q'.1 q'.2) →
      pairQueryOuterFamilyCode D q.1 ≤ pairQueryOuterFamilyCode D q'.1 := by
    intro h
    exact hn (Finset.mem_filter.mpr ⟨hc, h⟩)
  push_neg at hn'
  obtain ⟨q', hc', hs, hlt⟩ := hn'
  refine ⟨q', hc', hs, ?_⟩
  intro hm
  have hp : D.geom.patchOf q.1 = D.geom.patchOf q'.1 := by
    exact (row_patch D A (nonisolated_row_mem D A
      ((mem_pairQueryCandidateSet D A q).mp hc).1)).trans
      (row_patch D A (nonisolated_row_mem D A
        ((mem_pairQueryCandidateSet D A q').mp hc').1)).symm
  have hcode : pairQueryOuterFamilyCode D q.1 = pairQueryOuterFamilyCode D q'.1 := by
    unfold pairQueryOuterFamilyCode
    rw [hp, hm]
  exact (lt_irrefl _) (hlt.trans_eq hcode)

lemma flip_disagreement {n : ℕ} {u w : Fin n → Bool} {a b : Fin n}
    (hn : u ≠ w) (he : flipPos u a = flipPos w b) :
    a ≠ b ∧ u a ≠ w a ∧
      (Finset.univ.filter fun j => u j ≠ w j) ⊆ {a, b} := by
  have hab : a ≠ b := by
    intro hab
    subst b
    apply hn
    funext j
    have h := congrFun he j
    by_cases hj : j = a
    · subst j; simpa [flipPos] using h
    · simpa [flipPos, hj] using h
  refine ⟨hab, ?_, ?_⟩
  · intro heq
    have h := congrFun he a
    simp [flipPos, Function.update_of_ne hab, heq] at h
  · intro j hj
    have hne := (Finset.mem_filter.mp hj).2
    by_cases hja : j = a
    · simp [hja]
    by_cases hjb : j = b
    · simp [hjb]
    exact (hne (by simpa [flipPos, hja, hjb] using congrFun he j)).elim

noncomputable def outerDisagreements (D : LateData hPT) (v w : Pos T k) :=
  Finset.univ.filter fun a =>
    pairQueryOuterMask D v a ≠ pairQueryOuterMask D w a

noncomputable def chargedCoordinates (D : LateData hPT) (v w : Pos T k) :=
  if (outerDisagreements D v w).card ≤ 2 then outerDisagreements D v w else ∅

lemma chargedCoordinates_card (D : LateData hPT) (v w : Pos T k) :
    (chargedCoordinates D v w).card ≤ 2 := by
  unfold chargedCoordinates
  split_ifs with h
  · exact h
  · simp

lemma discarded_charged (D : LateData hPT) (A : InitialPairData D)
    {q : Pos T k × Fin (T.S.n k)}
    (hq : q ∈ pairQueryCandidateSet D A \ sliceCandidates D A) :
    ∃ w ∈ D.nonisolates A.rows, q.2 ∈ chargedCoordinates D q.1 w := by
  obtain ⟨q', hc', hs, hn⟩ := discarded_witness D A hq
  have hc := (mem_pairQueryCandidateSet D A q).mp (Finset.mem_sdiff.mp hq).1
  have hc' := (mem_pairQueryCandidateSet D A q').mp hc'
  rw [mask_flip D q.1 q.2 hc.2.2, mask_flip D q'.1 q'.2 hc'.2.2] at hs
  rcases flip_disagreement hn hs with ⟨hab, hdiff, hsub⟩
  have hcard : (outerDisagreements D q.1 q'.1).card ≤ 2 := by
    exact (Finset.card_le_card hsub).trans Finset.card_le_two
  refine ⟨q'.1, hc'.1, ?_⟩
  unfold chargedCoordinates
  rw [if_pos hcard]
  exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, hdiff⟩

lemma discarded_count (D : LateData hPT) (A : InitialPairData D) :
    (pairQueryCandidateSet D A \ sliceCandidates D A).card ≤
      4 * A.rows.card * D.rank A.rows := by
  let N := D.nonisolates A.rows
  let charges := N.biUnion fun v => N.biUnion fun w =>
    (chargedCoordinates D v w).image fun a => (v, a)
  have hsub : pairQueryCandidateSet D A \ sliceCandidates D A ⊆ charges := by
    intro q hq
    have hv := ((mem_pairQueryCandidateSet D A q).mp (Finset.mem_sdiff.mp hq).1).1
    obtain ⟨w, hw, ha⟩ := discarded_charged D A hq
    exact Finset.mem_biUnion.mpr ⟨q.1, hv, Finset.mem_biUnion.mpr
      ⟨w, hw, Finset.mem_image.mpr ⟨q.2, ha, rfl⟩⟩⟩
  have hcount : charges.card ≤ N.card * (N.card * 2) := by
    apply (Finset.card_biUnion_le).trans
    calc
      (∑ v ∈ N, (N.biUnion fun w =>
        (chargedCoordinates D v w).image fun a => (v, a)).card) ≤
          ∑ _v ∈ N, N.card * 2 := by
        apply Finset.sum_le_sum
        intro v hv
        apply Finset.card_biUnion_le.trans
        calc
          (∑ w ∈ N, ((chargedCoordinates D v w).image fun a => (v, a)).card) ≤
              ∑ _w ∈ N, 2 := by
            apply Finset.sum_le_sum
            intro w hw
            exact Finset.card_image_le.trans (chargedCoordinates_card D v w)
          _ = N.card * 2 := by simp
      _ = N.card * (N.card * 2) := by simp
  have hm : N.card ≤ A.rows.card := Finset.card_le_card (Finset.filter_subset _ _)
  have hr : N.card ≤ 2 * D.rank A.rows :=
    S18.Lane_q_s18_n5.nonisolates_le_twice_rank D A.rows
  calc
    _ ≤ charges.card := Finset.card_le_card hsub
    _ ≤ N.card * (N.card * 2) := hcount
    _ ≤ A.rows.card * ((2 * D.rank A.rows) * 2) :=
      Nat.mul_le_mul hm (Nat.mul_le_mul_right 2 hr)
    _ = 4 * A.rows.card * D.rank A.rows := by ring


lemma sliceCandidates_separated (hκ : κ.Admissible)
    (D : LateData hPT) (hD : D.Spec) (A : InitialPairData D)
    (hmargin : (2 : ℝ) < Real.log (T.S.n k : ℝ) ^ 3)
    (hcellMargin : 50 * κ.ρ * (PT.tiling.P A.paletteIndex.1).h ≤
      Real.log (T.S.n k : ℝ) ^ 3) :
    ∀ q q' : {q // q ∈ sliceCandidates D A}, q ≠ q' →
      D.geom.cellOf (flipPos q.1.1 q.1.2) = D.geom.cellOf (flipPos q'.1.1 q'.1.2) →
      hammingDist (flipPos q.1.1 q.1.2) (flipPos q'.1.1 q'.1.2) >
        50 * κ.ρ * (PT.tiling.P A.paletteIndex.1).h := by
  intro q q' hne hcell
  let x := q.1
  let y := q'.1
  have hxCand := (Finset.mem_filter.mp q.2).1
  have hyCand := (Finset.mem_filter.mp q'.2).1
  have hxFacts := (mem_pairQueryCandidateSet D A x).mp hxCand
  have hyFacts := (mem_pairQueryCandidateSet D A y).mp hyCand
  have hroleInj := sliceCandidates_injective D A
  by_cases hs : pairQueryOuterMask D (flipPos x.1 x.2) =
      pairQueryOuterMask D (flipPos y.1 y.2)
  ·
      have hcode := sliceCandidates_sameFamily D A q.2 q'.2 hs
      rcases pairQueryOuterFamily_eq_of_code_eq D hcode with ⟨hpatch, hmask⟩
      change D.geom.patchOf x.1 = D.geom.patchOf y.1 at hpatch
      change pairQueryOuterMask D x.1 = pairQueryOuterMask D y.1 at hmask
      have hOuter : ∀ z, z ∉ PT.tiling.Icoord (D.geom.patchOf x.1) → x.1 z = y.1 z := by
        intro z hz
        have hm := congrFun hmask z
        have hz' : z ∉ PT.tiling.Icoord (D.geom.patchOf y.1) := by
          rw [← hpatch]
          exact hz
        change (if z ∈ PT.tiling.Icoord (D.geom.patchOf x.1) then false else x.1 z) =
          (if z ∈ PT.tiling.Icoord (D.geom.patchOf y.1) then false else y.1 z) at hm
        rw [if_neg hz, if_neg hz'] at hm
        exact hm
      have hxRows : x.1 ∈ A.rows := by
        have hn := hxFacts.1
        change x.1 ∈ A.rows.filter _ at hn
        exact (Finset.mem_filter.mp hn).1
      have hyRows : y.1 ∈ A.rows := by
        have hn := hyFacts.1
        change y.1 ∈ A.rows.filter _ at hn
        exact (Finset.mem_filter.mp hn).1
      have hxPalette : x.1 ∈ D.paletteRows A.paletteIndex := A.rows_subset hxRows
      have hyPalette : y.1 ∈ D.paletteRows A.paletteIndex := A.rows_subset hyRows
      change x.1 ∈ Finset.univ.filter (fun v => IsEvenRole v ∧
        D.rolePalette v = A.paletteIndex) at hxPalette
      change y.1 ∈ Finset.univ.filter (fun v => IsEvenRole v ∧
        D.rolePalette v = A.paletteIndex) at hyPalette
      rcases Finset.mem_filter.mp hxPalette with ⟨_, ⟨hxEven, hxRole⟩⟩
      rcases Finset.mem_filter.mp hyPalette with ⟨_, ⟨hyEven, hyRole⟩⟩
      have hroleEq : D.rolePalette x.1 = D.rolePalette y.1 := hxRole.trans hyRole.symm
      have hpatchPalette : D.geom.patchOf x.1 = A.paletteIndex.1 := by
        have h := congrArg Sigma.fst hxRole
        simpa [LateData.rolePalette] using h
      have hpalette : D.palette x.1 = D.palette y.1 := by
        unfold LateData.palette
        have h := congrArg (fun p : PaletteIndex D => D.palettes p.1 p.2) hroleEq
        simpa [LateData.rolePalette] using h
      have hrowNe : x.1 ≠ y.1 := by
        intro hxy
        have hab : x.2 ≠ y.2 := by
          intro hab
          apply hne
          apply Subtype.ext
          exact Prod.ext hxy hab
        let bx := flipPos x.1 x.2
        let byWord := flipPos y.1 y.2
        have hbit : bx x.2 ≠ byWord x.2 := by
          have hxa : flipPos x.1 x.2 x.2 = !x.1 x.2 := by simp [flipPos]
          have hxb : flipPos y.1 y.2 x.2 = x.1 x.2 := by
            rw [hxy]
            simp [flipPos, Function.update_of_ne hab]
          change flipPos x.1 x.2 x.2 ≠ flipPos y.1 y.2 x.2
          rw [hxa, hxb]
          cases hval : x.1 x.2 <;> simp [hval]
        have hpatchBx := patchOf_flipPos_of_bulk D x.1 x.2 hxFacts.2.2
        have hnotI : x.2 ∉ PT.tiling.Icoord (D.geom.patchOf bx) := by
          simpa only [bx, hpatchBx] using (Finset.mem_filter.mp hxFacts.2.2).2.2
        have hspacing := D.l16_valid.cell_spacing bx byWord hcell ⟨x.2,
          hnotI, hbit⟩
        have hdist : hammingDist bx byWord ≤ 2 := by
          have ht := hammingDist_triangle bx x.1 byWord
          dsimp [byWord] at ht
          rw [← hxy] at ht
          rw [hammingDist_symm_local bx x.1,
            hammingDist_flipPos_eq_one x.1 x.2,
            hammingDist_flipPos_eq_one x.1 y.2] at ht
          dsimp [byWord]
          rw [← hxy]
          exact ht
        have hdistReal : (hammingDist bx byWord : ℝ) ≤ 2 := by exact_mod_cast hdist
        exact (lt_irrefl (2 : ℝ)) (lt_trans hmargin (hspacing.trans_le hdistReal))
      have hrowSep0 := hD.palette_separation x.1 y.1 hxEven hyEven hrowNe hpalette hOuter
      have hrowSep : 500 * κ.ρ * (PT.tiling.P A.paletteIndex.1).h <
          (hammingDist x.1 y.1 : ℝ) := by simpa [hpatchPalette] using hrowSep0
      by_cases hlarge : 1 / 225 ≤ κ.ρ * (PT.tiling.P A.paletteIndex.1).h
      · have htri1 := hammingDist_triangle x.1 (flipPos x.1 x.2) y.1
        have htri2 := hammingDist_triangle (flipPos x.1 x.2) (flipPos y.1 y.2) y.1
        have hflip1 : hammingDist x.1 (flipPos x.1 x.2) = 1 :=
          hammingDist_flipPos_eq_one x.1 x.2
        have hflip2 : hammingDist (flipPos y.1 y.2) y.1 = 1 := by
          rw [hammingDist_symm_local]
          exact hammingDist_flipPos_eq_one y.1 y.2
        have htri : hammingDist x.1 y.1 ≤ hammingDist (flipPos x.1 x.2) (flipPos y.1 y.2) + 2 := by
          omega
        have htriR : (hammingDist x.1 y.1 : ℝ) ≤
            (hammingDist (flipPos x.1 x.2) (flipPos y.1 y.2) : ℝ) + 2 := by exact_mod_cast htri
        have : (50 : ℝ) * κ.ρ * (PT.tiling.P A.paletteIndex.1).h <
            hammingDist (flipPos x.1 x.2) (flipPos y.1 y.2) := by
          nlinarith [hrowSep, htriR, hlarge]
        exact this
      · have hoddNe : flipPos x.1 x.2 ≠ flipPos y.1 y.2 := by
          intro heq
          exact hne (hroleInj heq)
        have hdistPos : 0 < hammingDist (flipPos x.1 x.2) (flipPos y.1 y.2) := by
          unfold hammingDist
          apply Finset.card_pos.mpr
          by_contra hnonempty
          have heq : flipPos x.1 x.2 = flipPos y.1 y.2 := by
            funext z
            by_contra hz
            have : z ∈ Finset.univ.filter
                (fun i => flipPos x.1 x.2 i ≠ flipPos y.1 y.2 i) :=
              Finset.mem_filter.mpr ⟨Finset.mem_univ _, hz⟩
            exact hnonempty ⟨z, this⟩
          exact hoddNe heq
        have hdistOne : (1 : ℝ) ≤ hammingDist (flipPos x.1 x.2) (flipPos y.1 y.2) := by
          exact_mod_cast (Nat.succ_le_iff.mpr hdistPos)
        have hsmall : (50 : ℝ) * κ.ρ * (PT.tiling.P A.paletteIndex.1).h < 1 := by
          have ht : κ.ρ * (PT.tiling.P A.paletteIndex.1).h < 1 / 225 := lt_of_not_ge hlarge
          nlinarith
        exact lt_of_lt_of_le hsmall hdistOne
  · have hp : D.geom.patchOf (flipPos x.1 x.2) =
        D.geom.patchOf (flipPos y.1 y.2) := by
      rw [patchOf_flipPos_of_bulk D _ _ hxFacts.2.2,
        patchOf_flipPos_of_bulk D _ _ hyFacts.2.2,
        row_patch D A (nonisolated_row_mem D A hxFacts.1),
        row_patch D A (nonisolated_row_mem D A hyFacts.1)]
    have hd : ∃ a, a ∉ PT.tiling.Icoord (D.geom.patchOf (flipPos x.1 x.2)) ∧
        flipPos x.1 x.2 a ≠ flipPos y.1 y.2 a := by
      by_contra hn
      apply hs
      push_neg at hn
      funext a
      by_cases ha : a ∈ PT.tiling.Icoord (D.geom.patchOf (flipPos x.1 x.2))
      · simp [pairQueryOuterMask, ← hp, ha]
      · simp only [pairQueryOuterMask, ← hp, if_neg ha]
        exact hn a ha
    exact hcellMargin.trans_lt (D.l16_valid.cell_spacing _ _ hcell hd)

noncomputable def queries (hκ : κ.Admissible)
    (D : LateData hPT) (hD : D.Spec) (A : InitialPairData D)
    (hmargin : (2 : ℝ) < Real.log (T.S.n k : ℝ) ^ 3)
    (hcellMargin : 50 * κ.ρ * (PT.tiling.P A.paletteIndex.1).h ≤
      Real.log (T.S.n k : ℝ) ^ 3) : PairQueries D A :=
  pairQueriesOfCandidateFinset D A (sliceCandidates D A)
    (fun q hq => ((mem_pairQueryCandidateSet D A q).mp (Finset.mem_filter.mp hq).1).1)
    (fun q hq => ((mem_pairQueryCandidateSet D A q).mp (Finset.mem_filter.mp hq).1).2.1)
    (fun q hq => ((mem_pairQueryCandidateSet D A q).mp (Finset.mem_filter.mp hq).1).2.2)
    (sliceCandidates_injective D A)
    (sliceCandidates_separated hκ D hD A hmargin hcellMargin)

lemma queries_count (hκ : κ.Admissible)
    (D : LateData hPT) (hD : D.Spec) (A : InitialPairData D)
    (hmargin : (2 : ℝ) < Real.log (T.S.n k : ℝ) ^ 3)
    (hcellMargin : 50 * κ.ρ * (PT.tiling.P A.paletteIndex.1).h ≤
      Real.log (T.S.n k : ℝ) ^ 3) :
    (queries hκ D hD A hmargin hcellMargin).count = (sliceCandidates D A).card := by
  simp [queries, pairQueriesOfCandidateFinset]

lemma cluster_q_power (hκ : κ.Admissible) (D : LateData hPT)
    (hm : PT.tiling.mode = .lowCluster) (hlog : 1 ≤ Real.log (T.S.n k : ℝ))
    (i : Fin PT.tiling.m) :
    Real.rpow (PT.tiling.P i).q κ.Cb ≤ Real.log (T.S.n k : ℝ) := by
  rcases hPT.tiling_valid.cluster_data (Or.inl hm) i with
    ⟨_hthreshold, _hg, _hmass, _hsmall, _hlarge, _hcodegree, _hh, _hlo, _hup,
      hlow, _hsmallMode, _hlargeMode⟩
  have hqBound : (PT.tiling.P i).q ≤
      Real.rpow (Real.log (T.S.n k : ℝ)) κ.cq := hlow.mp hm
  have hCb : 0 < κ.Cb := by
    have hdiv : 0 < κ.aC / κ.aB := div_pos hκ.aC_rng.1 hκ.aB_rng.1
    have hEq : 100 * (κ.aC / κ.aB) = 100 * κ.aC / κ.aB := by
      field_simp [ne_of_gt hκ.aB_rng.1]
      <;> ring
    have hlower : 0 < 100 * κ.aC / κ.aB + 100 := by
      rw [← hEq]
      nlinarith
    exact lt_trans hlower hκ.Cb_big
  have hMlo : (κ.Cb + 100 : ℝ) < κ.Mlo := hκ.Mlo_big
  have hcqCb : 0 < κ.cq * κ.Cb := mul_pos hκ.cq_rng.1 hCb
  have hcqCbLt : κ.cq * κ.Cb < 1 := by
    have hmul := mul_lt_mul_of_pos_right hκ.cq_rng.2 hCb
    have hMloPos : 0 < (κ.Mlo : ℝ) := by linarith [hMlo, hCb]
    have hden : 0 < 20 * (κ.Mlo : ℝ) := mul_pos (by norm_num) hMloPos
    have hfrac : (1 / (20 * (κ.Mlo : ℝ))) * κ.Cb =
        κ.Cb / (20 * (κ.Mlo : ℝ)) := by field_simp
    rw [hfrac] at hmul
    have hratio : κ.Cb / (20 * (κ.Mlo : ℝ)) < 1 := by
      apply (div_lt_one hden).2
      nlinarith [hMlo]
    exact lt_trans hmul hratio
  have hqPower :
      Real.rpow (PT.tiling.P i).q κ.Cb ≤ Real.log (T.S.n k : ℝ) := by
    have hbase : 0 ≤ Real.log (T.S.n k : ℝ) := by linarith [hlog]
    have hbasePow := Real.rpow_le_rpow (Nat.cast_nonneg _) hqBound hCb.le
    have hcomp :
        (Real.rpow (Real.log (T.S.n k : ℝ)) κ.cq) ^ κ.Cb =
          Real.rpow (Real.log (T.S.n k : ℝ)) (κ.cq * κ.Cb) := by
      exact (Real.rpow_mul hbase κ.cq κ.Cb).symm
    calc
      Real.rpow (PT.tiling.P i).q κ.Cb ≤
          (Real.rpow (Real.log (T.S.n k : ℝ)) κ.cq) ^ κ.Cb := hbasePow
      _ = Real.rpow (Real.log (T.S.n k : ℝ)) (κ.cq * κ.Cb) := hcomp
      _ ≤ Real.rpow (Real.log (T.S.n k : ℝ)) 1 :=
          Real.rpow_le_rpow_of_exponent_le hlog hcqCbLt.le
      _ = Real.log (T.S.n k : ℝ) := Real.rpow_one _
  exact hqPower

lemma envelope_degree_lower (hκ : κ.Admissible) (D : LateData hPT)
    (hK : κ.Kbd / (T.S.n k : ℝ) ≤ 1 / 10000)
    (hL : 10 * Real.log (T.S.n k : ℝ) / (T.S.n k : ℝ) ≤ 1 / 10000)
    (hlog : 1 ≤ Real.log (T.S.n k : ℝ)) (hn : 0 < (T.S.n k : ℝ))
    (hb : 3 * bstar T k ≤ 1 / 10000)
    (i j : Fin PT.tiling.m) (x : Fin (T.S.N k)) (hx : x ∈ PT.envelope i) :
    1 / 2 - 1 / 10000 ≤ rowDeg (T.S.E k) PT.tiling.c x (PT.π j) := by
  change 1 / 2 - 1 / 10000 ≤ deg (T.S.E k) PT.tiling.c (PT.π j).w x
  by_cases hij : j = i
  · subst j
    have hd := hPT.envelope_degree i x hx
    cases hm : PT.tiling.mode with
    | bounded =>
      simp only [OwnDegOK, hm] at hd
      linarith [(abs_le.mp hd).1]
    | lowDirect =>
      simp only [OwnDegOK, hm] at hd
      have hg : 0 ≤ ((PT.tiling.P i).g : ℝ) / (4 * (T.S.n k : ℝ)) := by positivity
      linarith [hd.1]
    | lowCluster =>
      simp only [OwnDegOK, hm] at hd
      have hq := cluster_q_power hκ D hm hlog i
      have he : 10 * Real.rpow (PT.tiling.P i).q κ.Cb / (T.S.n k : ℝ) ≤
          10 * Real.log (T.S.n k : ℝ) / (T.S.n k : ℝ) := by
        exact div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hq (by norm_num)) hn.le
      linarith [(abs_le.mp hd).1]
    | highSmall =>
      have hbad := D.low_mode
      simp [Mode.isLow, hm] at hbad
    | highDirect =>
      have hbad := D.low_mode
      simp [Mode.isLow, hm] at hbad
    | highLarge =>
      have hbad := D.low_mode
      simp [Mode.isLow, hm] at hbad
  · have hd := (abs_le.mp (hPT.envelope_other_degree i j hij x hx)).1
    linarith

lemma internal_prior_cap (hκ : κ.Admissible) (D : LateData hPT)
    (v : Pos T k) (s : Config D.fresh) (hv : D.internalValid v s)
    (x : Fin (T.S.N k)) :
    D.sigma v s x ≤ (2 : ℝ) ^ ((PT.tiling.P (D.geom.patchOf v)).h + 1) /
      (PT.tiling.P (D.geom.patchOf v)).M := by
  let i := D.geom.patchOf v
  have hM : (0 : ℝ) < (PT.tiling.P i).M := by
    rw [← (PT.tiling.P i).cardX]
    exact_mod_cast Finset.card_pos.mpr (hPT.tiling_valid.patch_nonempty i).1
  have hN : (0 : ℝ) < T.S.N k := by exact_mod_cast T.S.N_pos k
  have hMN : ((PT.tiling.P i).M : ℝ) ≤ T.S.N k := by
    rw [← (PT.tiling.P i).cardX]
    have hc : (PT.tiling.P i).X.card ≤ T.S.N k := by
      simpa only [Fintype.card_fin] using Finset.card_le_univ (PT.tiling.P i).X
    exact_mod_cast hc
  have hpow : (1 : ℝ) ≤ 2 ^ (PT.tiling.P i).h := one_le_pow₀ (by norm_num)
  have hshape := hv.2.2.1
  by_cases hc : PT.tiling.mode.isCluster
  · rw [if_pos hc] at hshape
    have hgain := S18.Lane_sol_d18l_pal.gain_nonneg hκ i
    have hexp : Real.exp (-500 * PT.tiling.gain i) ≤ 1 :=
      Real.exp_le_one_iff.mpr (by nlinarith)
    have hraw : D.sigma v s x ≤ (2 : ℝ) ^ (PT.tiling.P i).h / (T.S.N k : ℝ) := by
      apply (le_div_iff₀ hN).mpr
      have hbound := (hshape x).trans (by
        simpa only [mul_one] using mul_le_mul_of_nonneg_left hexp
          (by positivity : 0 ≤ (2 : ℝ) ^ (PT.tiling.P i).h))
      simpa only [mul_comm] using hbound
    calc
      D.sigma v s x ≤ (2 : ℝ) ^ (PT.tiling.P i).h / (T.S.N k : ℝ) := hraw
      _ ≤ (2 : ℝ) ^ (PT.tiling.P i).h / (PT.tiling.P i).M :=
        div_le_div_of_nonneg_left (by positivity) hM hMN
      _ ≤ (2 : ℝ) ^ ((PT.tiling.P i).h + 1) / (PT.tiling.P i).M := by
        apply div_le_div_of_nonneg_right _ hM.le
        rw [pow_succ]
        nlinarith [pow_nonneg (by norm_num : (0 : ℝ) ≤ 2) (PT.tiling.P i).h]
  · rw [if_neg hc] at hshape
    obtain ⟨q, hq, hσ⟩ := hshape
    have hcard := (hPT.corner_clean i q hq).card_lower
    have hcardpos : (0 : ℝ) < (PT.mesh.corner q i).card := by linarith
    have hcap : 1 / ((PT.mesh.corner q i).card : ℝ) ≤ 2 / (PT.tiling.P i).M := by
      apply (div_le_div_iff₀ hcardpos hM).mpr
      linarith
    have htwo : 2 / ((PT.tiling.P i).M : ℝ) ≤
        (2 : ℝ) ^ ((PT.tiling.P i).h + 1) / (PT.tiling.P i).M := by
      apply div_le_div_of_nonneg_right _ hM.le
      rw [pow_succ]
      nlinarith
    rw [hσ x]
    split_ifs
    · exact hcap.trans htwo
    · positivity

noncomputable def freshE (D : LateData hPT)
    (f : (∀ C, D.fresh.Pool C) → Config D.fresh → ℝ) : ℝ :=
  D.encoding.iidLaw.E fun pools => (D.freshConfigLaw pools).E (f pools)

lemma E_mono {Ω : Type*} [Fintype Ω] (P : FinLaw Ω)
    {f g : Ω → ℝ} (hfg : ∀ ω, f ω ≤ g ω) : P.E f ≤ P.E g :=
  Finset.sum_le_sum fun ω _ => mul_le_mul_of_nonneg_left (hfg ω) (P.nonneg ω)

lemma E_nonneg {Ω : Type*} [Fintype Ω] (P : FinLaw Ω)
    {f : Ω → ℝ} (hf : ∀ ω, 0 ≤ f ω) : 0 ≤ P.E f :=
  Finset.sum_nonneg fun ω _ => mul_nonneg (P.nonneg ω) (hf ω)

lemma E_mul_const {Ω : Type*} [Fintype Ω] (P : FinLaw Ω)
    (f : Ω → ℝ) (c : ℝ) : P.E (fun ω => f ω * c) = P.E f * c := by
  unfold FinLaw.E
  simp_rw [← mul_assoc]
  rw [Finset.sum_mul]

lemma E_const_mul {Ω : Type*} [Fintype Ω] (P : FinLaw Ω)
    (f : Ω → ℝ) (c : ℝ) : P.E (fun ω => c * f ω) = c * P.E f := by
  simp only [FinLaw.E, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro ω _
  ring

lemma freshE_mono (D : LateData hPT)
    {f g : (∀ C, D.fresh.Pool C) → Config D.fresh → ℝ}
    (hfg : ∀ pools s, f pools s ≤ g pools s) : freshE D f ≤ freshE D g :=
  E_mono _ fun pools => E_mono _ (hfg pools)

lemma freshE_const_mul (D : LateData hPT)
    (f : (∀ C, D.fresh.Pool C) → Config D.fresh → ℝ) (c : ℝ) :
    freshE D (fun pools s => c * f pools s) = c * freshE D f := by
  unfold freshE
  simp only [E_const_mul]

lemma freshE_product_local (D : LateData hPT)
    {J : Type*} [Fintype J] [DecidableEq J] (S : Finset J)
    (F : J → (∀ C, D.fresh.Pool C) → Config D.fresh → ℝ)
    (scope : J → Finset D.geom.Cell)
    (hdep : ∀ j pools pools' s s',
      (∀ C ∈ scope j, pools C = pools' C ∧ s C = s' C) →
        F j pools s = F j pools' s')
    (hdisj : ∀ i j, i ≠ j → Disjoint (scope i) (scope j)) :
    freshE D (fun pools s => ∏ j ∈ S, F j pools s) =
      ∏ j ∈ S, freshE D (F j) := by
  let g := fun j pools => (D.freshConfigLaw pools).E (F j pools)
  have hinner : ∀ pools,
      (D.freshConfigLaw pools).E (fun s => ∏ j ∈ S, F j pools s) =
        ∏ j ∈ S, g j pools := by
    intro pools
    apply S18.Lane_sol_s18_n5.pi_product_local _ S (fun j s => F j pools s) scope
    · intro j s s' hss
      exact hdep j pools pools s s' (fun C hC => ⟨rfl, hss C hC⟩)
    · exact hdisj
  have hg : ∀ j pools pools', (∀ C ∈ scope j, pools C = pools' C) →
      g j pools = g j pools' := by
    intro j pools pools' hpp
    have hF : F j pools = F j pools' := by
      funext s
      exact hdep j pools pools' s s (fun C hC => ⟨hpp C hC, rfl⟩)
    dsimp [g]
    rw [hF]
    letI : ∀ C, Nonempty (D.fresh.State C) := fun C => ⟨D.fresh.fallback C⟩
    apply S18.Lane_sol_s18_n5.pi_E_local _ _ (scope j) (F j pools')
    · intro s s' hss
      exact hdep j pools' pools' s s' (fun C hC => ⟨rfl, hss C hC⟩)
    · intro C hC
      rw [hpp C hC]
  unfold freshE
  simp_rw [hinner]
  rw [S18.Lane_sol_s18_n5.iidLaw_pi]
  exact S18.Lane_sol_s18_n5.pi_product_local _ S g scope hg hdisj

noncomputable def pairHit (D : LateData hPT) (assignment : PairAssignment T k)
    (v : Pos T k) (a : Fin (T.S.n k)) (s : Config D.fresh) : ℝ :=
  if Hits (T.S.E k) PT.tiling.c (assignment v).1 (D.earlyLabel s (flipPos v a)) ∧
    Hits (T.S.E k) PT.tiling.c (assignment v).2 (D.earlyLabel s (flipPos v a)) then 1 else 0

lemma pairHit_range (D : LateData hPT) (assignment : PairAssignment T k)
    (v : Pos T k) (a : Fin (T.S.n k)) (s : Config D.fresh) :
    0 ≤ pairHit D assignment v a s ∧ pairHit D assignment v a s ≤ 1 := by
  unfold pairHit
  split_ifs <;> norm_num

noncomputable def pairCore (D : LateData hPT) (assignment : PairAssignment T k)
    (v : Pos T k) (s : Config D.fresh) : ℝ :=
  D.sigma v s (assignment v).1 * D.sigma v s (assignment v).2 *
    ∏ a ∈ D.externalEarly v, pairHit D assignment v a s /
      (rowDeg (T.S.E k) PT.tiling.c (assignment v).1 (PT.π (D.geom.patchOf (flipPos v a))) *
       rowDeg (T.S.E k) PT.tiling.c (assignment v).2 (PT.π (D.geom.patchOf (flipPos v a))))

lemma pairCore_eq (D : LateData hPT) (assignment : PairAssignment T k)
    (v : Pos T k) (s : Config D.fresh) :
    pairCore D assignment v s =
      D.initialWeight v s (assignment v).1 * D.initialWeight v s (assignment v).2 := by
  have hpoint : ∀ a ∈ D.externalEarly v,
      pairHit D assignment v a s /
        (rowDeg (T.S.E k) PT.tiling.c (assignment v).1 (PT.π (D.geom.patchOf (flipPos v a))) *
         rowDeg (T.S.E k) PT.tiling.c (assignment v).2 (PT.π (D.geom.patchOf (flipPos v a)))) =
      ((if Hits (T.S.E k) PT.tiling.c (assignment v).1 (D.earlyLabel s (flipPos v a)) then 1 else 0) /
        rowDeg (T.S.E k) PT.tiling.c (assignment v).1 (PT.π (D.geom.patchOf (flipPos v a)))) *
      ((if Hits (T.S.E k) PT.tiling.c (assignment v).2 (D.earlyLabel s (flipPos v a)) then 1 else 0) /
        rowDeg (T.S.E k) PT.tiling.c (assignment v).2 (PT.π (D.geom.patchOf (flipPos v a)))) := by
    intro a ha
    by_cases hx : Hits (T.S.E k) PT.tiling.c (assignment v).1 (D.earlyLabel s (flipPos v a)) <;>
      by_cases hz : Hits (T.S.E k) PT.tiling.c (assignment v).2 (D.earlyLabel s (flipPos v a)) <;>
      simp [pairHit, hx, hz, div_eq_mul_inv, mul_inv, mul_comm]
  unfold pairCore LateData.initialWeight
  rw [Finset.prod_congr rfl hpoint, Finset.prod_mul_distrib]
  ring

lemma pairCore_nonneg (D : LateData hPT) (assignment : PairAssignment T k)
    (v : Pos T k) (s : Config D.fresh) : 0 ≤ pairCore D assignment v s := by
  rw [pairCore_eq]
  exact mul_nonneg (S18.Lane_sol_s18_n5.initialWeight_nonneg D _ _ _)
    (S18.Lane_sol_s18_n5.initialWeight_nonneg D _ _ _)

noncomputable def isolateTest (D : LateData hPT) (assignment : PairAssignment T k)
    (v : Pos T k) (pools : ∀ C, D.fresh.Pool C) (s : Config D.fresh) : ℝ :=
  if ∀ C ∈ D.directCells v, D.fresh.typical C (pools C) then
    (D.chi (D.geom.patchOf v) : ℝ) ^ 2 * pairCore D assignment v s else 0

lemma isolateTest_nonneg (D : LateData hPT) (assignment : PairAssignment T k)
    (v : Pos T k) (pools : ∀ C, D.fresh.Pool C) (s : Config D.fresh) :
    0 ≤ isolateTest D assignment v pools s := by
  unfold isolateTest
  split_ifs
  · exact mul_nonneg (sq_nonneg _) (pairCore_nonneg D assignment v s)
  · exact le_rfl

lemma isolateTest_local (D : LateData hPT) (hD : D.Spec) (assignment : PairAssignment T k)
    (v : Pos T k) (pools pools' : ∀ C, D.fresh.Pool C) (s s' : Config D.fresh)
    (h : ∀ C ∈ D.directCells v, pools C = pools' C ∧ s C = s' C) :
    isolateTest D assignment v pools s = isolateTest D assignment v pools' s' := by
  have htyp : (∀ C ∈ D.directCells v, D.fresh.typical C (pools C)) ↔
      ∀ C ∈ D.directCells v, D.fresh.typical C (pools' C) := by
    apply forall_congr'
    intro C
    apply imp_congr_right
    intro hC
    rw [(h C hC).1]
  have hcore : pairCore D assignment v s = pairCore D assignment v s' := by
    simp only [pairCore_eq, hD.prior_local v s s' (fun C hC => (h C hC).2)]
  simp only [isolateTest, htyp, hcore]

lemma isolateTest_integral (D : LateData hPT) (A : InitialPairData D)
    (assignment : PairAssignment T k) {v : Pos T k}
    (hv : A.validPair v (assignment v).1 (assignment v).2) :
    freshE D (isolateTest D assignment v) =
      isolatedWeight D v (assignment v).1 (assignment v).2 := by
  dsimp only [InitialPairData.validPair] at hv
  unfold isolatedWeight
  rw [if_pos hv]
  change D.encoding.iidLaw.E (fun pools => (D.freshConfigLaw pools).E (fun s =>
      if ∀ C ∈ D.directCells v, D.fresh.typical C (pools C) then
        (D.chi (D.geom.patchOf v) : ℝ) ^ 2 * pairCore D assignment v s else 0)) =
    (D.chi (D.geom.patchOf v) : ℝ) ^ 2 * D.encoding.iidLaw.E (fun pools =>
      if ∀ C ∈ D.directCells v, D.fresh.typical C (pools C) then
        (D.freshConfigLaw pools).E (pairCore D assignment v) else 0)
  have hin (pools : ∀ C, D.fresh.Pool C) :
      (D.freshConfigLaw pools).E (fun s =>
        if ∀ C ∈ D.directCells v, D.fresh.typical C (pools C) then
          (D.chi (D.geom.patchOf v) : ℝ) ^ 2 * pairCore D assignment v s else 0) =
      (D.chi (D.geom.patchOf v) : ℝ) ^ 2 *
        (if ∀ C ∈ D.directCells v, D.fresh.typical C (pools C) then
          (D.freshConfigLaw pools).E (pairCore D assignment v) else 0) := by
    split_ifs <;> simp only [E_const_mul, S18.Lane_sol_s18_n5.E_const, mul_zero]
  simp_rw [hin]
  rw [E_const_mul]

lemma isolated_disjoint (D : LateData hPT) (A : InitialPairData D)
    {v w : Pos T k} (hv : v ∈ A.rows \ D.nonisolates A.rows)
    (hw : w ∈ A.rows) (hne : v ≠ w) : Disjoint (D.directCells v) (D.directCells w) := by
  have hv' := (Finset.mem_sdiff.mp hv).2
  by_contra hn
  apply hv'
  exact Finset.mem_filter.mpr ⟨(Finset.mem_sdiff.mp hv).1, w, hw, hne, Or.inl hn⟩

noncomputable def queryCells (D : LateData hPT) (A : InitialPairData D) :=
  (sliceCandidates D A).image fun q => D.geom.cellOf (flipPos q.1 q.2)

noncomputable def queryTest (D : LateData hPT) (A : InitialPairData D)
    (assignment : PairAssignment T k) (pools : ∀ C, D.fresh.Pool C) (s : Config D.fresh) : ℝ :=
  if ∀ C ∈ queryCells D A, D.fresh.typical C (pools C) then
    ∏ q ∈ sliceCandidates D A, pairHit D assignment q.1 q.2 s else 0

lemma queryTest_nonneg (D : LateData hPT) (A : InitialPairData D)
    (assignment : PairAssignment T k) (pools : ∀ C, D.fresh.Pool C) (s : Config D.fresh) :
    0 ≤ queryTest D A assignment pools s := by
  unfold queryTest
  split_ifs
  · exact Finset.prod_nonneg fun q _ => (pairHit_range D assignment q.1 q.2 s).1
  · exact le_rfl

lemma queryTest_local (D : LateData hPT) (A : InitialPairData D)
    (assignment : PairAssignment T k) (pools pools' : ∀ C, D.fresh.Pool C)
    (s s' : Config D.fresh)
    (h : ∀ C ∈ queryCells D A, pools C = pools' C ∧ s C = s' C) :
    queryTest D A assignment pools s = queryTest D A assignment pools' s' := by
  have ht : (∀ C ∈ queryCells D A, D.fresh.typical C (pools C)) ↔
      ∀ C ∈ queryCells D A, D.fresh.typical C (pools' C) := by
    apply forall_congr'
    intro C
    apply imp_congr_right
    intro hC
    rw [(h C hC).1]
  have hh : ∀ q ∈ sliceCandidates D A,
      pairHit D assignment q.1 q.2 s = pairHit D assignment q.1 q.2 s' := by
    intro q hq
    have hc : D.geom.cellOf (flipPos q.1 q.2) ∈ queryCells D A :=
      Finset.mem_image.mpr ⟨q, hq, rfl⟩
    have hl : D.earlyLabel s (flipPos q.1 q.2) = D.earlyLabel s' (flipPos q.1 q.2) := by
      unfold LateData.earlyLabel
      rw [(h _ hc).2]
    by_cases hp : Hits (T.S.E k) PT.tiling.c (assignment q.1).1
        (D.earlyLabel s' (flipPos q.1 q.2)) ∧
      Hits (T.S.E k) PT.tiling.c (assignment q.1).2 (D.earlyLabel s' (flipPos q.1 q.2))
    · simp [pairHit, hl, hp]
    · simp [pairHit, hl, hp]
  simp only [queryTest, ht, Finset.prod_congr rfl hh]

lemma queryCells_disjoint (D : LateData hPT) (A : InitialPairData D)
    {v : Pos T k} (hv : v ∈ A.rows \ D.nonisolates A.rows) :
    Disjoint (D.directCells v) (queryCells D A) := by
  apply Finset.disjoint_left.mpr
  intro C hC hquery
  obtain ⟨q, hq, rfl⟩ := Finset.mem_image.mp hquery
  have hqc := (mem_pairQueryCandidateSet D A q).mp (Finset.mem_filter.mp hq).1
  have hvne : v ≠ q.1 := by
    intro he
    subst v
    exact (Finset.mem_sdiff.mp hv).2 hqc.1
  have hdisj := isolated_disjoint D A hv (nonisolated_row_mem D A hqc.1) hvne
  apply Finset.disjoint_left.mp hdisj hC
  exact Finset.mem_union.mpr (Or.inr (Finset.mem_image.mpr ⟨q.2, hqc.2.1, rfl⟩))

lemma query_isolate_factorization (D : LateData hPT) (hD : D.Spec)
    (A : InitialPairData D) (assignment : PairAssignment T k)
    (hvalid : ∀ v ∈ A.rows, A.validPair v (assignment v).1 (assignment v).2) :
    freshE D (fun pools s => queryTest D A assignment pools s *
      ∏ v ∈ A.rows \ D.nonisolates A.rows, isolateTest D assignment v pools s) =
    freshE D (queryTest D A assignment) *
      ∏ v ∈ A.rows \ D.nonisolates A.rows,
        isolatedWeight D v (assignment v).1 (assignment v).2 := by
  let I := A.rows \ D.nonisolates A.rows
  let J := Option {v // v ∈ I}
  let F : J → (∀ C, D.fresh.Pool C) → Config D.fresh → ℝ := fun j =>
    match j with
    | none => queryTest D A assignment
    | some v => isolateTest D assignment v.1
  let scopes : J → Finset D.geom.Cell := fun j =>
    match j with
    | none => queryCells D A
    | some v => D.directCells v.1
  have hlocal : ∀ j pools pools' s s',
      (∀ C ∈ scopes j, pools C = pools' C ∧ s C = s' C) → F j pools s = F j pools' s' := by
    intro j pools pools' s s' h
    cases j with
    | none => exact queryTest_local D A assignment pools pools' s s' h
    | some v => exact isolateTest_local D hD assignment v.1 pools pools' s s' h
  have hdisj : ∀ i j : J, i ≠ j → Disjoint (scopes i) (scopes j) := by
    intro i j hne
    cases i with
    | none =>
      cases j with
      | none => exact (hne rfl).elim
      | some v => exact (queryCells_disjoint D A v.2).symm
    | some v =>
      cases j with
      | none => exact queryCells_disjoint D A v.2
      | some w =>
        apply isolated_disjoint D A v.2 (Finset.mem_sdiff.mp w.2).1
        intro he
        exact hne (congrArg some (Subtype.ext he))
  have h := freshE_product_local D Finset.univ F scopes hlocal hdisj
  have hprod : ∀ pools s, (∏ j : J, F j pools s) =
      queryTest D A assignment pools s * ∏ v ∈ I, isolateTest D assignment v pools s := by
    intro pools s
    simp only [J, F, Fintype.prod_option]
    rw [Finset.prod_coe_sort I (fun v : Pos T k => isolateTest D assignment v pools s)]
  have hout : (∏ j : J, freshE D (F j)) =
      freshE D (queryTest D A assignment) *
        ∏ v ∈ I, isolatedWeight D v (assignment v).1 (assignment v).2 := by
    simp only [J, F, Fintype.prod_option]
    rw [Finset.prod_coe_sort I (fun v : Pos T k => freshE D (isolateTest D assignment v))]
    congr 1
    apply Finset.prod_congr rfl
    intro v hv
    exact isolateTest_integral D A assignment (hvalid v (Finset.mem_sdiff.mp hv).1)
  simpa only [hprod, hout, I] using h

noncomputable def allCandidates (D : LateData hPT) (A : InitialPairData D) :=
  (D.nonisolates A.rows).biUnion fun v =>
    (D.externalEarly v).image fun a => (v, a)

lemma mem_allCandidates (D : LateData hPT) (A : InitialPairData D)
    (q : Pos T k × Fin (T.S.n k)) : q ∈ allCandidates D A ↔
    q.1 ∈ D.nonisolates A.rows ∧ q.2 ∈ D.externalEarly q.1 := by
  simp only [allCandidates, Finset.mem_biUnion, Finset.mem_image]
  constructor
  · rintro ⟨v, hv, a, ha, he⟩
    cases he
    exact ⟨hv, ha⟩
  · rintro ⟨hv, ha⟩
    exact ⟨q.1, hv, q.2, ha, rfl⟩

lemma candidates_subset_all (D : LateData hPT) (A : InitialPairData D) :
    pairQueryCandidateSet D A ⊆ allCandidates D A := by
  intro q hq
  have h := (mem_pairQueryCandidateSet D A q).mp hq
  exact (mem_allCandidates D A q).mpr ⟨h.1, h.2.1⟩

lemma allCandidates_prod (D : LateData hPT) (A : InitialPairData D)
    (f : Pos T k × Fin (T.S.n k) → ℝ) :
    (∏ q ∈ allCandidates D A, f q) =
      ∏ v ∈ D.nonisolates A.rows, ∏ a ∈ D.externalEarly v, f (v, a) := by
  unfold allCandidates
  rw [Finset.prod_biUnion]
  · apply Finset.prod_congr rfl
    intro v hv
    rw [Finset.prod_image]
    intro a ha b hb he
    exact Prod.mk.inj he |>.2
  · intro v hv w hw hne
    apply Finset.disjoint_left.mpr
    intro q hq hq'
    obtain ⟨a, ha, he⟩ := Finset.mem_image.mp hq
    obtain ⟨b, hb, he'⟩ := Finset.mem_image.mp hq'
    exact hne (congrArg Prod.fst (he.trans he'.symm))

lemma allCandidates_card (D : LateData hPT) (A : InitialPairData D) :
    (allCandidates D A).card = ∑ v ∈ D.nonisolates A.rows, (D.externalEarly v).card := by
  unfold allCandidates
  rw [Finset.card_biUnion]
  · apply Finset.sum_congr rfl
    intro v hv
    rw [Finset.card_image_of_injective]
    intro a b he
    exact Prod.mk.inj he |>.2
  · intro v hv w hw hne
    apply Finset.disjoint_left.mpr
    intro q hq hq'
    obtain ⟨a, ha, he⟩ := Finset.mem_image.mp hq
    obtain ⟨b, hb, he'⟩ := Finset.mem_image.mp hq'
    exact hne (congrArg Prod.fst (he.trans he'.symm))

lemma allCandidates_count (D : LateData hPT) (A : InitialPairData D) :
    (allCandidates D A).card ≤ (D.nonisolates A.rows).card * T.S.n k := by
  rw [allCandidates_card]
  calc
    (∑ v ∈ D.nonisolates A.rows, (D.externalEarly v).card) ≤
        ∑ _v ∈ D.nonisolates A.rows, T.S.n k := by
      apply Finset.sum_le_sum
      intro v hv
      simpa only [Fintype.card_fin] using Finset.card_le_univ (D.externalEarly v)
    _ = (D.nonisolates A.rows).card * T.S.n k := by simp

lemma crossing_candidates_count (D : LateData hPT) (A : InitialPairData D) :
    (allCandidates D A \ pairQueryCandidateSet D A).card ≤
      (PT.tiling.P A.paletteIndex.1).ℓ * (D.nonisolates A.rows).card := by
  let ell := (PT.tiling.P A.paletteIndex.1).ℓ
  let crossings := Finset.univ.filter fun a : Fin (T.S.n k) => a.val < ell
  have hsub : allCandidates D A \ pairQueryCandidateSet D A ⊆
      D.nonisolates A.rows ×ˢ crossings := by
    intro q hq
    rcases Finset.mem_sdiff.mp hq with ⟨hall, hn⟩
    rcases (mem_allCandidates D A q).mp hall with ⟨hv, ha⟩
    have hb : q.2 ∉ PT.tiling.bulkCoords (D.geom.patchOf q.1) := by
      intro hb
      exact hn ((mem_pairQueryCandidateSet D A q).mpr ⟨hv, ha, hb⟩)
    have he : q.2.val < ell := by
      by_contra hnot
      apply hb
      apply Finset.mem_filter.mpr
      refine ⟨Finset.mem_univ _, ?_, (Finset.mem_filter.mp ha).2.1⟩
      simpa only [row_patch D A (nonisolated_row_mem D A hv), ell] using Nat.le_of_not_gt hnot
    exact Finset.mem_product.mpr ⟨hv, Finset.mem_filter.mpr ⟨Finset.mem_univ _, he⟩⟩
  have hcard : crossings.card ≤ ell := by
    dsimp [crossings]
    rw [Fin.card_filter_val_lt]
    exact Nat.min_le_right _ _
  calc
    _ ≤ (D.nonisolates A.rows ×ˢ crossings).card := Finset.card_le_card hsub
    _ = (D.nonisolates A.rows).card * crossings.card := Finset.card_product _ _
    _ ≤ (D.nonisolates A.rows).card * ell := Nat.mul_le_mul_left _ hcard
    _ = (PT.tiling.P A.paletteIndex.1).ℓ * (D.nonisolates A.rows).card := by ring

lemma total_discard_count (D : LateData hPT) (A : InitialPairData D) :
    (allCandidates D A).card ≤ (sliceCandidates D A).card +
      (PT.tiling.P A.paletteIndex.1).ℓ * (D.nonisolates A.rows).card +
        4 * A.rows.card * D.rank A.rows := by
  have hc := Finset.card_sdiff_add_card_eq_card (candidates_subset_all D A)
  have hs := Finset.card_sdiff_add_card_eq_card
    (show sliceCandidates D A ⊆ pairQueryCandidateSet D A from Finset.filter_subset _ _)
  have hcross := crossing_candidates_count D A
  have hdiscard := discarded_count D A
  omega

lemma pair_denominator_bound (dx dz : ℝ)
    (hx : 1 / 2 - 1 / 10000 ≤ dx) (hz : 1 / 2 - 1 / 10000 ≤ dz) :
    1 / (dx * dz) ≤ 4 * Real.exp (0.0008) := by
  have hx' := S18.Lane_sol_d18l_pal.inverse_degree_lower dx (1 / 10000) hx
    (by norm_num) (by norm_num)
  have hz' := S18.Lane_sol_d18l_pal.inverse_degree_lower dz (1 / 10000) hz
    (by norm_num) (by norm_num)
  calc
    1 / (dx * dz) = (1 / dx) * (1 / dz) := by simp [one_div, mul_inv, mul_comm]
    _ ≤ (2 * Real.exp (4 * (1 / 10000))) * (2 * Real.exp (4 * (1 / 10000))) :=
      mul_le_mul hx'.2 hz'.2 (div_nonneg (by norm_num) hz'.1.le) (by positivity)
    _ = 4 * Real.exp (0.0008) := by
      rw [mul_mul_mul_comm, ← Real.exp_add]
      norm_num

lemma row_core_bound (hκ : κ.Admissible) (D : LateData hPT)
    (A : InitialPairData D) (assignment : PairAssignment T k)
    {v : Pos T k} (hv : v ∈ A.rows) (s : Config D.fresh)
    (hvalid : D.internalValid v s)
    (hdegree : ∀ a ∈ D.externalEarly v,
      1 / 2 - 1 / 10000 ≤ rowDeg (T.S.E k) PT.tiling.c (assignment v).1
        (PT.π (D.geom.patchOf (flipPos v a))) ∧
      1 / 2 - 1 / 10000 ≤ rowDeg (T.S.E k) PT.tiling.c (assignment v).2
        (PT.π (D.geom.patchOf (flipPos v a)))) :
    (D.chi (D.geom.patchOf v) : ℝ) ^ 2 * pairCore D assignment v s ≤
      (D.paletteScale A.paletteIndex)⁻¹ ^ 2 *
        (4 : ℝ) ^ ((PT.tiling.P A.paletteIndex.1).h + 1) *
          (4 * Real.exp (0.0008)) ^ (D.externalEarly v).card *
            ∏ a ∈ D.externalEarly v, pairHit D assignment v a s := by
  have hp := row_patch D A hv
  let i := D.geom.patchOf v
  have hM : (0 : ℝ) < (PT.tiling.P i).M := by
    rw [← (PT.tiling.P i).cardX]
    exact_mod_cast Finset.card_pos.mpr (hPT.tiling_valid.patch_nonempty i).1
  have hchi : (0 : ℝ) < D.chi i := by exact_mod_cast D.chi_pos i
  have hσx := internal_prior_cap hκ D v s hvalid (assignment v).1
  have hσz := internal_prior_cap hκ D v s hvalid (assignment v).2
  have hprod : (∏ a ∈ D.externalEarly v, pairHit D assignment v a s /
      (rowDeg (T.S.E k) PT.tiling.c (assignment v).1 (PT.π (D.geom.patchOf (flipPos v a))) *
       rowDeg (T.S.E k) PT.tiling.c (assignment v).2 (PT.π (D.geom.patchOf (flipPos v a))))) ≤
      (4 * Real.exp (0.0008)) ^ (D.externalEarly v).card *
        ∏ a ∈ D.externalEarly v, pairHit D assignment v a s := by
    rw [← Finset.prod_const, ← Finset.prod_mul_distrib]
    apply Finset.prod_le_prod₀
    · intro a ha
      exact div_nonneg (pairHit_range D assignment v a s).1
        (mul_nonneg (S18.Lane_sol_s18_n5.rowDeg_nonneg D _ _)
          (S18.Lane_sol_s18_n5.rowDeg_nonneg D _ _))
    · intro a ha
      have hden := pair_denominator_bound _ _ (hdegree a ha).1 (hdegree a ha).2
      have h := mul_le_mul_of_nonneg_left hden (pairHit_range D assignment v a s).1
      simpa only [div_eq_mul_inv, one_div, one_mul, mul_comm] using h
  have hprior : D.sigma v s (assignment v).1 * D.sigma v s (assignment v).2 ≤
      ((2 : ℝ) ^ ((PT.tiling.P i).h + 1) / (PT.tiling.P i).M) ^ 2 := by
    simpa only [pow_two] using mul_le_mul hσx hσz (hvalid.1 _) (by positivity)
  have hscale : (D.chi i : ℝ) ^ 2 *
      ((2 : ℝ) ^ ((PT.tiling.P i).h + 1) / (PT.tiling.P i).M) ^ 2 =
      (D.paletteScale A.paletteIndex)⁻¹ ^ 2 * (4 : ℝ) ^ ((PT.tiling.P A.paletteIndex.1).h + 1) := by
    have htwo : ((2 : ℝ) ^ ((PT.tiling.P i).h + 1)) ^ 2 =
        (4 : ℝ) ^ ((PT.tiling.P i).h + 1) := by
      rw [← pow_mul, Nat.mul_comm, pow_mul]
      norm_num
    dsimp [i] at *
    dsimp [LateData.paletteScale]
    rw [← hp, div_pow, htwo]
    field_simp [ne_of_gt hM, ne_of_gt hchi]
    <;> ring
  calc
    _ ≤ (D.chi i : ℝ) ^ 2 *
        ((((2 : ℝ) ^ ((PT.tiling.P i).h + 1) / (PT.tiling.P i).M) ^ 2) *
          ((4 * Real.exp (0.0008)) ^ (D.externalEarly v).card *
            ∏ a ∈ D.externalEarly v, pairHit D assignment v a s)) := by
      apply mul_le_mul_of_nonneg_left _ (sq_nonneg _)
      apply mul_le_mul hprior hprod
      · apply Finset.prod_nonneg
        intro a ha
        exact div_nonneg (pairHit_range D assignment v a s).1
          (mul_nonneg (S18.Lane_sol_s18_n5.rowDeg_nonneg D _ _)
            (S18.Lane_sol_s18_n5.rowDeg_nonneg D _ _))
      · positivity
    _ = _ := by rw [← mul_assoc, hscale]; ring

noncomputable def reductionConstant (D : LateData hPT) (A : InitialPairData D) : ℝ :=
  (D.paletteScale A.paletteIndex)⁻¹ ^ (2 * (D.nonisolates A.rows).card) *
    (4 : ℝ) ^ (((PT.tiling.P A.paletteIndex.1).h + 1) * (D.nonisolates A.rows).card) *
      (4 * Real.exp (0.0008)) ^ (allCandidates D A).card

lemma phi_le_cores (D : LateData hPT) (A : InitialPairData D)
    (assignment : PairAssignment T k) (s : Config D.fresh) :
    A.phi assignment s ≤
      ∏ v ∈ A.rows, (D.chi (D.geom.patchOf v) : ℝ) ^ 2 * pairCore D assignment v s := by
  have hχ : (∏ v ∈ A.rows, (D.chi (D.geom.patchOf v) : ℝ) ^ 2) =
      (D.chi A.paletteIndex.1 : ℝ) ^ (2 * A.rows.card) := by
    calc
      _ = ∏ _v ∈ A.rows, (D.chi A.paletteIndex.1 : ℝ) ^ 2 := by
        apply Finset.prod_congr rfl
        intro v hv
        rw [row_patch D A hv]
      _ = _ := by simp [← pow_mul]
  rw [Finset.prod_mul_distrib, hχ]
  unfold InitialPairData.phi
  split_ifs with hvalid
  · apply mul_le_mul_of_nonneg_left _ (by positivity)
    apply Finset.prod_le_prod₀
    · intro v hv
      split_ifs
      · exact mul_nonneg (S18.Lane_sol_s18_n5.initialWeight_nonneg D _ _ _)
          (S18.Lane_sol_s18_n5.initialWeight_nonneg D _ _ _)
      · exact le_rfl
    · intro v hv
      split_ifs
      · rw [pairCore_eq]
      · exact pairCore_nonneg D assignment v s
  · exact mul_nonneg (by positivity) (Finset.prod_nonneg
      fun v hv => pairCore_nonneg D assignment v s)

lemma nonisolated_cores_bound (hκ : κ.Admissible) (D : LateData hPT)
    (A : InitialPairData D) (assignment : PairAssignment T k) (s : Config D.fresh)
    (hv : ∀ v ∈ A.rows, D.internalValid v s)
    (hdegree : ∀ v ∈ A.rows, ∀ a ∈ D.externalEarly v,
      1 / 2 - 1 / 10000 ≤ rowDeg (T.S.E k) PT.tiling.c (assignment v).1
        (PT.π (D.geom.patchOf (flipPos v a))) ∧
      1 / 2 - 1 / 10000 ≤ rowDeg (T.S.E k) PT.tiling.c (assignment v).2
        (PT.π (D.geom.patchOf (flipPos v a)))) :
    (∏ v ∈ D.nonisolates A.rows,
      (D.chi (D.geom.patchOf v) : ℝ) ^ 2 * pairCore D assignment v s) ≤
      reductionConstant D A * ∏ q ∈ sliceCandidates D A, pairHit D assignment q.1 q.2 s := by
  have hScale := paletteScale_pos D A.paletteIndex
  have hprod : (∏ v ∈ D.nonisolates A.rows,
      (D.chi (D.geom.patchOf v) : ℝ) ^ 2 * pairCore D assignment v s) ≤
      ∏ v ∈ D.nonisolates A.rows,
        (D.paletteScale A.paletteIndex)⁻¹ ^ 2 *
          (4 : ℝ) ^ ((PT.tiling.P A.paletteIndex.1).h + 1) *
            (4 * Real.exp (0.0008)) ^ (D.externalEarly v).card *
              ∏ a ∈ D.externalEarly v, pairHit D assignment v a s := by
    apply Finset.prod_le_prod₀
    · intro v hvm
      exact mul_nonneg (sq_nonneg _) (pairCore_nonneg D assignment v s)
    · intro v hvm
      have hrow := nonisolated_row_mem D A hvm
      exact row_core_bound hκ D A assignment hrow s (hv v hrow) (hdegree v hrow)
  have heq : (∏ v ∈ D.nonisolates A.rows,
        (D.paletteScale A.paletteIndex)⁻¹ ^ 2 *
          (4 : ℝ) ^ ((PT.tiling.P A.paletteIndex.1).h + 1) *
            (4 * Real.exp (0.0008)) ^ (D.externalEarly v).card *
              ∏ a ∈ D.externalEarly v, pairHit D assignment v a s) =
      reductionConstant D A * ∏ q ∈ allCandidates D A, pairHit D assignment q.1 q.2 s := by
    simp only [Finset.prod_mul_distrib, Finset.prod_const,
      Finset.prod_pow_eq_pow_sum, reductionConstant, allCandidates_prod,
      allCandidates_card, ← pow_mul] <;> ring
  rw [heq] at hprod
  apply hprod.trans
  apply mul_le_mul_of_nonneg_left _ (by unfold reductionConstant; positivity)
  exact Finset.prod_le_prod_of_subset_of_le_one₀
    ((Finset.filter_subset _ _).trans (candidates_subset_all D A))
    (fun q _ => (pairHit_range D assignment q.1 q.2 s).1)
    (fun q _ _ => (pairHit_range D assignment q.1 q.2 s).2)

lemma gated_phi_bound (hκ : κ.Admissible) (D : LateData hPT)
    (A : InitialPairData D) (assignment : PairAssignment T k)
    (hdegree : ∀ v ∈ A.rows, ∀ a ∈ D.externalEarly v,
      1 / 2 - 1 / 10000 ≤ rowDeg (T.S.E k) PT.tiling.c (assignment v).1
        (PT.π (D.geom.patchOf (flipPos v a))) ∧
      1 / 2 - 1 / 10000 ≤ rowDeg (T.S.E k) PT.tiling.c (assignment v).2
        (PT.π (D.geom.patchOf (flipPos v a))))
    (pools : ∀ C, D.fresh.Pool C) (s : Config D.fresh) :
    (if ∀ C ∈ A.scope, D.fresh.typical C (pools C) then A.phi assignment s else 0) ≤
      reductionConstant D A * (queryTest D A assignment pools s *
        ∏ v ∈ A.rows \ D.nonisolates A.rows, isolateTest D assignment v pools s) := by
  have hScale := paletteScale_pos D A.paletteIndex
  have hnonneg : 0 ≤ reductionConstant D A * (queryTest D A assignment pools s *
      ∏ v ∈ A.rows \ D.nonisolates A.rows, isolateTest D assignment v pools s) := by
    apply mul_nonneg (by unfold reductionConstant; positivity)
    exact mul_nonneg (queryTest_nonneg D A assignment pools s)
      (Finset.prod_nonneg fun v _ => isolateTest_nonneg D assignment v pools s)
  by_cases ht : ∀ C ∈ A.scope, D.fresh.typical C (pools C)
  · rw [if_pos ht]
    by_cases hv : ∀ v ∈ A.rows, D.initialValid v s
    · have hvi : ∀ v ∈ A.rows, D.internalValid v s := fun v hvm => (hv v hvm).1
      have htyp (v : Pos T k) (hvm : v ∈ A.rows) :
          ∀ C ∈ D.directCells v, D.fresh.typical C (pools C) := by
        intro C hC
        exact ht C (Finset.mem_biUnion.mpr ⟨v, hvm, hC⟩)
      have hNsub : D.nonisolates A.rows ⊆ A.rows := Finset.filter_subset _ _
      have hi : (∏ v ∈ A.rows \ D.nonisolates A.rows,
          (D.chi (D.geom.patchOf v) : ℝ) ^ 2 * pairCore D assignment v s) =
          ∏ v ∈ A.rows \ D.nonisolates A.rows, isolateTest D assignment v pools s := by
        apply Finset.prod_congr rfl
        intro v hvm
        simp only [isolateTest, if_pos (htyp v (Finset.mem_sdiff.mp hvm).1)]
      have hquery : queryTest D A assignment pools s =
          ∏ q ∈ sliceCandidates D A, pairHit D assignment q.1 q.2 s := by
        unfold queryTest
        rw [if_pos]
        intro C hC
        obtain ⟨q, hq, rfl⟩ := Finset.mem_image.mp hC
        have hc := (mem_pairQueryCandidateSet D A q).mp (Finset.mem_filter.mp hq).1
        exact htyp q.1 (nonisolated_row_mem D A hc.1) _
          (Finset.mem_union.mpr (Or.inr (Finset.mem_image.mpr ⟨q.2, hc.2.1, rfl⟩)))
      calc
        A.phi assignment s ≤ ∏ v ∈ A.rows,
            (D.chi (D.geom.patchOf v) : ℝ) ^ 2 * pairCore D assignment v s :=
          phi_le_cores D A assignment s
        _ = (∏ v ∈ D.nonisolates A.rows,
            (D.chi (D.geom.patchOf v) : ℝ) ^ 2 * pairCore D assignment v s) *
            ∏ v ∈ A.rows \ D.nonisolates A.rows, isolateTest D assignment v pools s := by
          rw [← Finset.prod_sdiff hNsub, hi, mul_comm]
        _ ≤ (reductionConstant D A * ∏ q ∈ sliceCandidates D A,
            pairHit D assignment q.1 q.2 s) *
              ∏ v ∈ A.rows \ D.nonisolates A.rows, isolateTest D assignment v pools s :=
          mul_le_mul_of_nonneg_right
            (nonisolated_cores_bound hκ D A assignment s hvi hdegree)
            (Finset.prod_nonneg fun v _ => isolateTest_nonneg D assignment v pools s)
        _ = _ := by rw [hquery]; ring
    · simpa only [InitialPairData.phi, if_neg hv] using hnonneg
  · simpa only [if_neg ht] using hnonneg

lemma iidFreshTest_reduction (hκ : κ.Admissible) (D : LateData hPT) (hD : D.Spec)
    (A : InitialPairData D) (assignment : PairAssignment T k)
    (hvalid : ∀ v ∈ A.rows, A.validPair v (assignment v).1 (assignment v).2)
    (hdegree : ∀ v ∈ A.rows, ∀ a ∈ D.externalEarly v,
      1 / 2 - 1 / 10000 ≤ rowDeg (T.S.E k) PT.tiling.c (assignment v).1
        (PT.π (D.geom.patchOf (flipPos v a))) ∧
      1 / 2 - 1 / 10000 ≤ rowDeg (T.S.E k) PT.tiling.c (assignment v).2
        (PT.π (D.geom.patchOf (flipPos v a)))) :
    A.iidFreshTest assignment ≤ reductionConstant D A * freshE D (queryTest D A assignment) *
      ∏ v ∈ A.rows \ D.nonisolates A.rows,
        isolatedWeight D v (assignment v).1 (assignment v).2 := by
  have heq : A.iidFreshTest assignment = freshE D (fun pools s =>
      if ∀ C ∈ A.scope, D.fresh.typical C (pools C) then A.phi assignment s else 0) := by
    unfold InitialPairData.iidFreshTest freshE
    apply congrArg D.encoding.iidLaw.E
    funext pools
    by_cases ht : ∀ C ∈ A.scope, D.fresh.typical C (pools C)
    · simp only [if_pos ht]
    · simp only [if_neg ht, S18.Lane_sol_s18_n5.E_const]
  rw [heq]
  calc
    _ ≤ freshE D (fun pools s => reductionConstant D A *
        (queryTest D A assignment pools s *
          ∏ v ∈ A.rows \ D.nonisolates A.rows, isolateTest D assignment v pools s)) :=
      freshE_mono D (gated_phi_bound hκ D A assignment hdegree)
    _ = _ := by
      rw [freshE_const_mul, query_isolate_factorization D hD A assignment hvalid]
      ring

lemma queryTest_integral (hκ : κ.Admissible) (D : LateData hPT) (hD : D.Spec)
    (A : InitialPairData D)
    (hmargin : (2 : ℝ) < Real.log (T.S.n k : ℝ) ^ 3)
    (hcellMargin : 50 * κ.ρ * (PT.tiling.P A.paletteIndex.1).h ≤
      Real.log (T.S.n k : ℝ) ^ 3) (assignment : PairAssignment T k) :
    freshE D (queryTest D A assignment) =
      (queries hκ D hD A hmargin hcellMargin).integral assignment := by
  let S := sliceCandidates D A
  let e : Fin (Fintype.card {q // q ∈ S}) ≃ {q // q ∈ S} :=
    (Fintype.equivFin {q // q ∈ S}).symm
  have hprod : ∀ s, (∏ i, pairHit D assignment (e i).1.1 (e i).1.2 s) =
      ∏ q ∈ S, pairHit D assignment q.1 q.2 s := by
    intro s
    rw [e.prod_comp (fun q => pairHit D assignment q.1.1 q.1.2 s),
      Finset.prod_coe_sort S (fun q : Pos T k × Fin (T.S.n k) => pairHit D assignment q.1 q.2 s)]
  have htyp : ∀ pools : (∀ C, D.fresh.Pool C), (∀ i, D.fresh.typical (D.geom.cellOf (flipPos (e i).1.1 (e i).1.2))
      (pools (D.geom.cellOf (flipPos (e i).1.1 (e i).1.2)))) ↔
      ∀ C ∈ queryCells D A, D.fresh.typical C (pools C) := by
    intro pools
    constructor
    · intro ht C hC
      obtain ⟨q, hq, rfl⟩ := Finset.mem_image.mp hC
      obtain ⟨i, hi⟩ := e.surjective ⟨q, hq⟩
      have hti := ht i
      rw [hi] at hti
      exact hti
    · intro ht i
      exact ht _ (Finset.mem_image.mpr ⟨(e i).1, (e i).2, rfl⟩)
  unfold freshE queries pairQueriesOfCandidateFinset PairQueries.integral
  change D.encoding.iidLaw.E (fun pools => (D.freshConfigLaw pools).E
      (queryTest D A assignment pools)) =
    D.encoding.iidLaw.E (fun pools =>
      if ∀ i, D.fresh.typical (D.geom.cellOf (flipPos (e i).1.1 (e i).1.2))
          (pools (D.geom.cellOf (flipPos (e i).1.1 (e i).1.2))) then
        (D.freshConfigLaw pools).E (fun s => ∏ i,
          pairHit D assignment (e i).1.1 (e i).1.2 s) else 0)
  apply congrArg D.encoding.iidLaw.E
  funext pools
  unfold queryTest
  by_cases ht : ∀ C ∈ queryCells D A, D.fresh.typical C (pools C)
  · have hq : ∀ i, D.fresh.typical (D.geom.cellOf (flipPos (e i).1.1 (e i).1.2))
        (pools (D.geom.cellOf (flipPos (e i).1.1 (e i).1.2))) := (htyp pools).mpr ht
    simp only [if_pos ht, if_pos hq]
    apply congrArg (D.freshConfigLaw pools).E
    funext s
    exact (hprod s).symm
  · have hq : ¬ ∀ i, D.fresh.typical (D.geom.cellOf (flipPos (e i).1.1 (e i).1.2))
        (pools (D.geom.cellOf (flipPos (e i).1.1 (e i).1.2))) := fun hq => ht ((htyp pools).mp hq)
    simp only [if_neg ht, if_neg hq, S18.Lane_sol_s18_n5.E_const]

lemma four_pow_le_exp (j : ℕ) : (4 : ℝ) ^ j ≤ Real.exp (2 * j) := by
  have hlog2 : Real.log (2 : ℝ) ≤ 1 := by
    have h := Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 2)
    linarith
  have hlog4 : Real.log (4 : ℝ) ≤ 2 := by
    have heq : Real.log (4 : ℝ) = 2 * Real.log 2 := by
      have h := Real.log_pow (2 : ℝ) 2
      norm_num at h
      exact h
    linarith
  calc
    (4 : ℝ) ^ j = Real.exp (j * Real.log 4) := by
      rw [Real.exp_nat_mul, Real.exp_log (by norm_num : (0 : ℝ) < 4)]
    _ ≤ Real.exp (2 * j) := Real.exp_le_exp.mpr (by
      have h := mul_le_mul_of_nonneg_left hlog4 (Nat.cast_nonneg j)
      nlinarith)

lemma reductionConstant_bound (D : LateData hPT) (A : InitialPairData D)
    (hn : (1000000 : ℝ) ≤ T.S.n k)
    (hsmall : ((PT.tiling.P A.paletteIndex.1).ℓ : ℝ) +
      (PT.tiling.P A.paletteIndex.1).h + 1 ≤ Real.sqrt (T.S.n k : ℝ)) :
    reductionConstant D A ≤
      Real.exp (0.005 * (T.S.n k : ℝ) * (D.nonisolates A.rows).card +
        8 * A.rows.card * D.rank A.rows) *
          (4 : ℝ) ^ (sliceCandidates D A).card *
            (D.paletteScale A.paletteIndex)⁻¹ ^ (2 * (D.nonisolates A.rows).card) := by
  have hScale := paletteScale_pos D A.paletteIndex
  let m := (D.nonisolates A.rows).card
  let p := A.rows.card
  let r := D.rank A.rows
  let ell := (PT.tiling.P A.paletteIndex.1).ℓ
  let h := (PT.tiling.P A.paletteIndex.1).h
  let q := (sliceCandidates D A).card
  let t := (allCandidates D A).card
  have ht : t ≤ q + ell * m + 4 * p * r := total_discard_count D A
  have htn : t ≤ m * T.S.n k := allCandidates_count D A
  have hpow : (4 : ℝ) ^ t ≤ (4 : ℝ) ^ q * 4 ^ (ell * m + 4 * p * r) := by
    rw [← pow_add]
    apply pow_le_pow_right₀ (by norm_num)
    omega
  have he : (Real.exp (0.0008)) ^ t ≤ Real.exp (0.0008 * (T.S.n k : ℝ) * m) := by
    rw [← Real.exp_nat_mul]
    apply Real.exp_le_exp.mpr
    have htn' : (t : ℝ) ≤ (m : ℝ) * (T.S.n k : ℝ) := by exact_mod_cast htn
    nlinarith
  have hs := Real.sqrt_nonneg (T.S.n k : ℝ)
  have hs2 := Real.sq_sqrt (show (0 : ℝ) ≤ T.S.n k by positivity)
  have hs1000 : (1000 : ℝ) ≤ Real.sqrt (T.S.n k : ℝ) := by nlinarith
  have hroot : 2 * Real.sqrt (T.S.n k : ℝ) ≤ 0.002 * (T.S.n k : ℝ) := by
    nlinarith [mul_nonneg (sub_nonneg.mpr hs1000) hs]
  have hbudget : 2 * (((h + 1) * m + (ell * m + 4 * p * r) : ℕ) : ℝ) +
      0.0008 * (T.S.n k : ℝ) * m ≤
        0.005 * (T.S.n k : ℝ) * m + 8 * p * r := by
    have hm : (0 : ℝ) ≤ m := Nat.cast_nonneg _
    have hnm : 0 ≤ (T.S.n k : ℝ) * (m : ℝ) := mul_nonneg (Nat.cast_nonneg _) hm
    have hsm : 2 * ((ell : ℝ) + h + 1) * m ≤
        0.002 * (T.S.n k : ℝ) * m := by
      exact mul_le_mul_of_nonneg_right
        ((mul_le_mul_of_nonneg_left hsmall (by norm_num)).trans hroot) hm
    push_cast
    nlinarith
  unfold reductionConstant
  change (D.paletteScale A.paletteIndex)⁻¹ ^ (2 * m) *
      (4 : ℝ) ^ ((h + 1) * m) * (4 * Real.exp (0.0008)) ^ t ≤ _
  rw [mul_pow, ← mul_assoc]
  calc
    _ ≤ (D.paletteScale A.paletteIndex)⁻¹ ^ (2 * m) *
        (4 : ℝ) ^ ((h + 1) * m) *
          ((4 : ℝ) ^ q * 4 ^ (ell * m + 4 * p * r)) *
            Real.exp (0.0008 * (T.S.n k : ℝ) * m) := by
      apply mul_le_mul
      · apply mul_le_mul_of_nonneg_left hpow (by positivity)
      · exact he
      · positivity
      · positivity
    _ = (D.paletteScale A.paletteIndex)⁻¹ ^ (2 * m) * (4 : ℝ) ^ q *
        (4 : ℝ) ^ ((h + 1) * m + (ell * m + 4 * p * r)) *
          Real.exp (0.0008 * (T.S.n k : ℝ) * m) := by rw [pow_add]; ring
    _ ≤ (D.paletteScale A.paletteIndex)⁻¹ ^ (2 * m) * (4 : ℝ) ^ q *
        Real.exp (2 * (((h + 1) * m + (ell * m + 4 * p * r) : ℕ) : ℝ)) *
          Real.exp (0.0008 * (T.S.n k : ℝ) * m) := by
      exact mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left (four_pow_le_exp _) (by positivity)) (by positivity)
    _ ≤ (D.paletteScale A.paletteIndex)⁻¹ ^ (2 * m) * (4 : ℝ) ^ q *
        Real.exp (0.005 * (T.S.n k : ℝ) * m + 8 * p * r) := by
      convert mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr hbudget)
        (show 0 ≤ (D.paletteScale A.paletteIndex)⁻¹ ^ (2 * m) * (4 : ℝ) ^ q by positivity)
        using 1 <;> simp only [Real.exp_add] <;> ring
    _ = _ := by ring

lemma eventual_numeric (hκ : κ.Admissible) (T : Stage) :
    ∀ᶠ k in atTop,
      (1000000 : ℝ) ≤ T.S.n k ∧
      3 ≤ Real.log (T.S.n k : ℝ) ∧
      50 * κ.ρ + 1 ≤ Real.log (T.S.n k : ℝ) ∧
      3 * bstar T k ≤ 1 / 10000 := by
  have hn : Tendsto (fun k : ℕ => (T.S.n k : ℝ)) atTop atTop :=
    tendsto_natCast_atTop_atTop.comp T.S.n_tendsto
  have hlog := Real.tendsto_log_atTop.comp hn
  have hb : Tendsto (fun k : ℕ => 3 * bstar T k) atTop (nhds 0) := by
    have hp := (tendsto_rpow_neg_atTop (by norm_num : (0 : ℝ) < 0.96)).comp hn
    convert (tendsto_const_nhds.mul hp : Tendsto
      (fun k : ℕ => (3 : ℝ) * (T.S.n k : ℝ) ^ (-(0.96 : ℝ))) atTop (nhds (3 * 0)))
      using 1 <;> norm_num [bstar, Function.comp_def]
  filter_upwards [hn.eventually_ge_atTop 1000000,
    hlog.eventually_ge_atTop 3, hlog.eventually_ge_atTop (50 * κ.ρ + 1),
    hb.eventually (eventually_le_nhds (by norm_num : (0 : ℝ) < 1 / 10000))]
    with k hn hl hρ hb
  exact ⟨hn, hl, hρ, hb⟩

/-- The slice-level incidence deletion, deterministic caps, and isolate
factorization give the integral reduction uniformly before the stage index. -/
theorem pair_query_reduction (hκ : κ.Admissible) (T : Stage) :
    ∃ CQ : ℝ, 0 < CQ ∧ ∀ᶠ k in atTop, ∀ PT : ProfiledTiling κ T k, ∀ hPT : PT.Valid,
      ∀ D : LateData hPT, D.Spec → ∀ A : InitialPairData D, ∃ Q : PairQueries D A,
        ∀ assignment, (∀ v ∈ A.rows, A.validPair v (assignment v).1 (assignment v).2) →
          A.iidFreshTest assignment ≤
            Real.exp (0.005 * (T.S.n k : ℝ) * (D.nonisolates A.rows).card +
              CQ * A.rows.card * D.rank A.rows) * (4 : ℝ) ^ Q.count * Q.integral assignment *
                (D.paletteScale A.paletteIndex)⁻¹ ^ (2 * (D.nonisolates A.rows).card) *
                ∏ v ∈ A.rows \ D.nonisolates A.rows,
                  isolatedWeight D v (assignment v).1 (assignment v).2 := by
  refine ⟨8, by norm_num, ?_⟩
  filter_upwards [eventual_numeric hκ T, eventually_endpoint_numeric_bounds hκ T,
    S18.Lane_sol_d18l_pal.small_prefix_height T] with k hnum hdeg hsmall
  intro PT hPT D hD A
  rcases hnum with ⟨hn, hlog, hρ, hb⟩
  rcases hdeg with ⟨hK, _hDirect, hL, _hError, _hLog, _hN⟩
  obtain ⟨physical⟩ := D.l16_valid.physical
  have hh := physical.quantitative.height_bound
  have hell := physical.quantitative.prefix_bound
  have hlog1 : 1 ≤ Real.log (T.S.n k : ℝ) := by linarith
  have hheight (i : Fin PT.tiling.m) :
      ((PT.tiling.P i).h : ℝ) ≤ Real.log (T.S.n k : ℝ) := by
    calc
      _ ≤ (Real.log (T.S.n k : ℝ)) ^ (1 / 10 : ℝ) := hh i
      _ ≤ (Real.log (T.S.n k : ℝ)) ^ (1 : ℝ) :=
        Real.rpow_le_rpow_of_exponent_le hlog1 (by norm_num)
      _ = Real.log (T.S.n k : ℝ) := Real.rpow_one _
  have hmargin : (2 : ℝ) < Real.log (T.S.n k : ℝ) ^ 3 := by
    have hc := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 3) hlog 3
    norm_num at hc
    linarith
  have hρpos : 0 < κ.ρ := hκ.ρ_rng.1
  have hcellMargin : 50 * κ.ρ * (PT.tiling.P A.paletteIndex.1).h ≤
      Real.log (T.S.n k : ℝ) ^ 3 := by
    have hm := mul_le_mul_of_nonneg_left (hheight A.paletteIndex.1)
      (show 0 ≤ 50 * κ.ρ by positivity)
    have hsq : 50 * κ.ρ ≤ Real.log (T.S.n k : ℝ) ^ 2 := by
      nlinarith [sq_nonneg (Real.log (T.S.n k : ℝ) - 1)]
    have hc := mul_le_mul_of_nonneg_right hsq (by linarith : 0 ≤ Real.log (T.S.n k : ℝ))
    nlinarith
  let Q := queries hκ D hD A hmargin hcellMargin
  refine ⟨Q, ?_⟩
  intro assignment hvalid
  have hdegree : ∀ v ∈ A.rows, ∀ a ∈ D.externalEarly v,
      1 / 2 - 1 / 10000 ≤ rowDeg (T.S.E k) PT.tiling.c (assignment v).1
        (PT.π (D.geom.patchOf (flipPos v a))) ∧
      1 / 2 - 1 / 10000 ≤ rowDeg (T.S.E k) PT.tiling.c (assignment v).2
        (PT.π (D.geom.patchOf (flipPos v a))) := by
    intro v hv a ha
    have hnpos : 0 < (T.S.n k : ℝ) := by linarith
    exact ⟨envelope_degree_lower hκ D hK.le hL.le hlog1 hnpos hb _ _ _ (hvalid v hv).2.2.1,
      envelope_degree_lower hκ D hK.le hL.le hlog1 hnpos hb _ _ _ (hvalid v hv).2.2.2.1⟩
  have hred := iidFreshTest_reduction hκ D hD A assignment hvalid hdegree
  rw [queryTest_integral hκ D hD A hmargin hcellMargin assignment] at hred
  have hconst := reductionConstant_bound D A hn
    (hsmall _ _ (hell A.paletteIndex.1) (hh A.paletteIndex.1)).1
  have hqnonneg : 0 ≤ Q.integral assignment := by
    rw [← queryTest_integral hκ D hD A hmargin hcellMargin assignment]
    apply E_nonneg
    intro pools
    exact E_nonneg _ (queryTest_nonneg D A assignment pools)
  have hisononneg : 0 ≤ ∏ v ∈ A.rows \ D.nonisolates A.rows,
      isolatedWeight D v (assignment v).1 (assignment v).2 := by
    apply Finset.prod_nonneg
    intro v hv
    exact S18.Lane_q_s18_n5.isolatedWeight_nonneg D _ _ _
  have hbound := mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_right hconst hqnonneg) hisononneg
  rw [← queries_count hκ D hD A hmargin hcellMargin] at hbound
  exact hred.trans (by convert hbound using 1 <;> ring)

end HypercubeRamsey.Lane_sol_s18_5e
