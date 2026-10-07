import HypercubeRamsey.S18.Locality_sol_s18_n5

namespace HypercubeRamsey.S18.Lane_sol_s18_n5
open Classical
open scoped BigOperators
variable {κ : CConsts} {T : Stage} {k : ℕ} {PT : ProfiledTiling κ T k} {hPT : PT.Valid}

def HistoryTestLocal (D : LateData hPT) (t : Fin (D.geom.r + 1))
    (cells : Finset D.geom.Cell) (rows : Finset (Pos T k))
    (F : D.encoding.base.History t → ℝ) : Prop :=
  ∀ h h', (∀ C ∈ cells, h.1 C = h'.1 C) →
    (∀ b : D.encoding.base.ProcessedRole t, b.1 ∈ rows →
      D.encoding.base.rowLabel (h.2 b) = D.encoding.base.rowLabel (h'.2 b)) → F h = F h'

noncomputable def rowCells (D : LateData hPT) (rows : Finset (Pos T k)) : Finset D.geom.Cell :=
  rows.biUnion (rowInitialCells D)

noncomputable def pastPositions (D : LateData hPT) (j : Fin D.geom.r)
    (rows : Finset (Pos T k)) : Finset (Pos T k) :=
  rows.biUnion fun b => (rowPredecessors D j b).image Subtype.val

private theorem law_nonempty {Ω : Type*} [Fintype Ω] (P : FinLaw Ω) : Nonempty Ω := by
  have hs : (∑ x, P.w x) ≠ 0 := by rw [P.sum_one]; norm_num
  obtain ⟨x, _, _⟩ := Finset.exists_ne_zero_of_sum_ne_zero hs
  exact ⟨x⟩

/-- Integrating one reference class pulls a label-local test back to exactly
the earlier rows and initial cells read by the queried reference kernels. -/
theorem reference_pullback_local (D : LateData hPT) (hD : D.Spec) (hT : TransitionData D)
    (j : Fin D.geom.r) (cells : Finset D.geom.Cell) (rows : Finset (Pos T k))
    (F : D.encoding.base.History j.succ → ℝ)
    (hF : HistoryTestLocal D j.succ cells rows F) :
    HistoryTestLocal D j.castSucc (cells ∪ rowCells D rows) (rows ∪ pastPositions D j rows)
      (fun h => (D.encoding.kernels.referenceTransition j h).E
        (fun out => F (D.encoding.base.extend j h out))) := by
  intro h h' hcells hrows
  let S : Finset {b : Pos T k // b ∈ D.encoding.base.classes j} :=
    Finset.univ.filter fun b => b.1 ∈ rows
  let f := fun out : D.encoding.base.ClassRows j => F (D.encoding.base.extend j h out)
  letI : ∀ b : {b : Pos T k // b ∈ D.encoding.base.classes j},
      Nonempty (D.encoding.base.RowOut b.1) :=
    fun b => law_nonempty (D.encoding.kernels.refK j b h)
  have hf : ∀ out out', (∀ b ∈ S, out b = out' b) → f out = f out' := by
    intro out out' hout
    apply hF
    · intro C _
      rfl
    · intro b hb
      by_cases hp : b.1 ∈ D.encoding.base.processed j.castSucc
      · simp only [LateProcessBase.extend, dif_pos hp]
      · have hc : b.1 ∈ D.encoding.base.classes j := by
          have hm : b.1 ∈ D.encoding.base.processed j.castSucc ∪ D.encoding.base.classes j :=
            (congrArg (fun R : Finset (Pos T k) => b.1 ∈ R)
              (D.encoding.base.processed_step j)).mpr b.2
          exact (Finset.mem_union.mp hm).resolve_left hp
        have heq := hout ⟨b.1, hc⟩ (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hb⟩)
        simpa only [LateProcessBase.extend, dif_neg hp] using
          congrArg D.encoding.base.rowLabel heq
  have hkernel : ∀ b ∈ S, D.encoding.kernels.refK j b h = D.encoding.kernels.refK j b h' := by
    intro b hb
    have hbrows := (Finset.mem_filter.mp hb).2
    apply S16.Lane_q_s16_comp2.finLaw_ext
    intro out
    apply referenceRow_weight_local D hD hT j b h h'
    · intro C hC
      exact hcells C (Finset.mem_union.mpr (Or.inr
        (Finset.mem_biUnion.mpr ⟨b.1, hbrows, hC⟩)))
    · intro u hu
      apply hrows
      apply Finset.mem_union.mpr
      right
      exact Finset.mem_biUnion.mpr ⟨b.1, hbrows,
        Finset.mem_image.mpr ⟨u, hu, rfl⟩⟩
  have hpoint : ∀ out, F (D.encoding.base.extend j h out) = F (D.encoding.base.extend j h' out) := by
    intro out
    apply hF
    · intro C hC
      exact hcells C (Finset.mem_union.mpr (Or.inl hC))
    · intro b hb
      by_cases hp : b.1 ∈ D.encoding.base.processed j.castSucc
      · simpa only [LateProcessBase.extend, dif_pos hp] using
          hrows ⟨b.1, hp⟩ (Finset.mem_union.mpr (Or.inl hb))
      · simp only [LateProcessBase.extend, dif_neg hp]
  change (FinLaw.pi (fun b => D.encoding.kernels.refK j b h)).E f = _
  rw [pi_E_local (fun b => D.encoding.kernels.refK j b h)
    (fun b => D.encoding.kernels.refK j b h') S f hf hkernel]
  exact congrArg (D.encoding.kernels.referenceTransition j h').E (funext hpoint)

theorem column_product_local (D : LateData hPT) (hD : D.Spec) (hT : TransitionData D)
    (j : Fin D.geom.r) (m : ℕ)
    (s : Fin m → {b : Pos T k // b ∈ D.encoding.base.classes j}) (y : Fin (T.S.N k)) :
    let rows := Finset.univ.image (fun i => (s i).1)
    HistoryTestLocal D j.castSucc (rowCells D rows) (pastPositions D j rows)
      (fun h => ∏ i, (D.encoding.kernels.refK j (s i) h).pr
        (fun out => D.encoding.base.rowLabel out = y)) := by
  intro rows h h' hcells hrows
  apply Finset.prod_congr rfl
  intro i _
  apply referenceRow_label_local D hD hT
  · intro C hC
    exact hcells C (Finset.mem_biUnion.mpr ⟨(s i).1,
      Finset.mem_image.mpr ⟨i, Finset.mem_univ _, rfl⟩, hC⟩)
  · intro u hu
    exact hrows u (Finset.mem_biUnion.mpr ⟨(s i).1,
      Finset.mem_image.mpr ⟨i, Finset.mem_univ _, rfl⟩,
        Finset.mem_image.mpr ⟨u, hu, rfl⟩⟩)

end HypercubeRamsey.S18.Lane_sol_s18_n5
