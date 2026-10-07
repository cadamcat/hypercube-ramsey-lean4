import HypercubeRamsey.S18.Ancestors_sol_s18_n5
import HypercubeRamsey.S18.Backward_sol_s18_n5
import HypercubeRamsey.S18.InitialScope_sol_s18_n5

namespace HypercubeRamsey.S18.Lane_sol_s18_n5
open Classical
open scoped BigOperators
variable {κ : CConsts} {T : Stage} {k : ℕ} {PT : ProfiledTiling κ T k} {hPT : PT.Valid}

noncomputable def referenceTests (D : LateData hPT)
    (F : D.encoding.base.History (Fin.last D.geom.r) → ℝ) :
    ∀ t : Fin (D.geom.r + 1), D.encoding.base.History t → ℝ :=
  Fin.reverseInduction F (fun j next h => (D.encoding.kernels.referenceTransition j h).E
    (fun out => next (D.encoding.base.extend j h out)))

theorem referenceTests_last (D : LateData hPT)
    (F : D.encoding.base.History (Fin.last D.geom.r) → ℝ) :
    referenceTests D F (Fin.last D.geom.r) = F := by
  simp only [referenceTests, Fin.reverseInduction_last]

theorem referenceTests_step (D : LateData hPT)
    (F : D.encoding.base.History (Fin.last D.geom.r) → ℝ) (j : Fin D.geom.r) :
    referenceTests D F j.castSucc = fun h => (D.encoding.kernels.referenceTransition j h).E
      (fun out => referenceTests D F j.succ (D.encoding.base.extend j h out)) := by
  simp only [referenceTests, Fin.reverseInduction_castSucc]

theorem referenceTests_nonneg (D : LateData hPT)
    (F : D.encoding.base.History (Fin.last D.geom.r) → ℝ) (hF : ∀ h, 0 ≤ F h)
    (t : Fin (D.geom.r + 1)) : ∀ h, 0 ≤ referenceTests D F t h := by
  induction t using Fin.reverseInduction with
  | last => simpa only [referenceTests_last] using hF
  | @cast j ih =>
    intro h
    rw [referenceTests_step]
    unfold FinLaw.E
    exact Finset.sum_nonneg fun out _ =>
      mul_nonneg (FinLaw.nonneg _ out) (ih _)

theorem HistoryTestLocal.mono (D : LateData hPT) (t : Fin (D.geom.r + 1))
    (C C' : Finset D.geom.Cell) (R R' : Finset (Pos T k))
    (F : D.encoding.base.History t → ℝ) (hF : HistoryTestLocal D t C R F)
    (hC : C ⊆ C') (hR : R ⊆ R') : HistoryTestLocal D t C' R' F := by
  intro h h' hc hr
  exact hF h h' (fun c hm => hc c (hC hm)) (fun b hm => hr b (hR hm))

theorem ancestors_step_subset (rows : Finset (Pos T k)) (m : ℕ) :
    ancestors rows m ⊆ ancestors rows (m + 1) := fun _ hm => Finset.mem_union.mpr (Or.inl hm)

theorem rowCells_mono (D : LateData hPT) {R R' : Finset (Pos T k)} (hR : R ⊆ R') :
    rowCells D R ⊆ rowCells D R' := by
  intro C hC
  obtain ⟨b, hb, hCb⟩ := Finset.mem_biUnion.mp hC
  exact Finset.mem_biUnion.mpr ⟨b, hR hb, hCb⟩

/-- Reference pullbacks accumulate at most one two-edge predecessor step
per class. The scope counts concern actual kernels and remain explicit. -/
theorem referenceTests_local (D : LateData hPT) (hD : D.Spec) (hT : TransitionData D)
    (roots : Finset (Pos T k)) (F : D.encoding.base.History (Fin.last D.geom.r) → ℝ)
    (hF : HistoryTestLocal D (Fin.last D.geom.r)
      (rowCells D (ancestors roots 1)) (ancestors roots 1) F) (t : Fin (D.geom.r + 1)) :
    HistoryTestLocal D t (rowCells D (ancestors roots (D.geom.r - t.val + 1)))
      (ancestors roots (D.geom.r - t.val + 1)) (referenceTests D F t) := by
  induction t using Fin.reverseInduction with
  | last => simpa only [referenceTests_last, Fin.val_last, Nat.sub_self, zero_add] using hF
  | @cast j ih =>
    rw [referenceTests_step]
    have hs := reference_pullback_local D hD hT j _ _ _ ih
    rw [Finset.union_self] at hs
    have hd : D.geom.r - j.castSucc.val + 1 = (D.geom.r - j.succ.val + 1) + 1 := by
      simp only [Fin.val_castSucc, Fin.val_succ]
      omega
    rw [hd]
    apply HistoryTestLocal.mono D _ _ _ _ _ _ hs
    · exact rowCells_mono D (ancestors_step_subset roots _)
    · intro b hb
      rcases Finset.mem_union.mp hb with hb | hb
      · exact Finset.mem_union.mpr (Or.inl hb)
      · exact Finset.mem_union.mpr (Or.inr (pastPositions_subset_twoStep D j _ hb))

theorem HistoryTestLocal.beforeHistory (D : LateData hPT)
    (j t : Fin (D.geom.r + 1)) (hjt : j.val ≤ t.val)
    (C : Finset D.geom.Cell) (R : Finset (Pos T k)) (F : D.encoding.base.History j → ℝ)
    (hF : HistoryTestLocal D j C R F) :
    HistoryTestLocal D t C R (fun h => F (D.beforeHistory h j hjt)) := by
  intro h h' hc hr
  apply hF _ _ hc
  intro b hb
  exact hr ⟨b.1, D.processed_mono j t hjt b.2⟩ hb

/-- The pullback of a prefix-only terminal test agrees with that same test
at every later prefix; future reference classes integrate to one. -/
theorem referenceTests_prefix (D : LateData hPT) (j : Fin (D.geom.r + 1))
    (G : D.encoding.base.History j → ℝ) (t : Fin (D.geom.r + 1))
    (hjt : j.val ≤ t.val) (h : D.encoding.base.History t) :
    referenceTests D (fun full => G (D.beforeHistory full j (Nat.le_of_lt_succ j.isLt))) t h =
      G (D.beforeHistory h j hjt) := by
  induction t using Fin.reverseInduction with
  | last => rw [referenceTests_last]
  | @cast s ih =>
    rw [referenceTests_step]
    have hnext : ∀ out,
        referenceTests D (fun full => G (D.beforeHistory full j (Nat.le_of_lt_succ j.isLt)))
          s.succ (D.encoding.base.extend s h out) = G (D.beforeHistory h j hjt) := by
      intro out
      rw [ih (show j.val ≤ s.succ.val from by
        simp only [Fin.val_castSucc] at hjt
        simp only [Fin.val_succ]
        omega)]
      rw [beforeHistory_extend D s h out j hjt]
    calc
      _ = (D.encoding.kernels.referenceTransition s h).E (fun _ => G (D.beforeHistory h j hjt)) :=
        congrArg (D.encoding.kernels.referenceTransition s h).E (funext hnext)
      _ = _ := E_const _ _

/-- The initial reference test reads the complete deterministic resampling
horizon of the accumulated queried cells, including pools and tapes. -/
theorem referenceTests_initial_input_local (D : LateData hPT) (hD : D.Spec)
    (hT : TransitionData D) (roots : Finset (Pos T k))
    (F : D.encoding.base.History (Fin.last D.geom.r) → ℝ)
    (hF : HistoryTestLocal D (Fin.last D.geom.r)
      (rowCells D (ancestors roots 1)) (ancestors roots 1) F)
    (x x' : D.encoding.InitInput)
    (hinput : ∀ C ∈ D.expandCells (rowCells D (ancestors roots (D.geom.r + 1))),
      x.1 C = x'.1 C ∧ x.2 C = x'.2 C) :
    referenceTests D F 0 (D.encoding.base.initialHistory (D.encoding.initialState x)) =
      referenceTests D F 0 (D.encoding.base.initialHistory (D.encoding.initialState x')) := by
  apply referenceTests_local D hD hT roots F hF 0
  · exact initialState_input_local D _ x x' hinput
  · intro b _
    have hf : False := by simpa only [D.encoding.base.processed_zero, Finset.notMem_empty] using b.2
    exact hf.elim

end HypercubeRamsey.S18.Lane_sol_s18_n5
