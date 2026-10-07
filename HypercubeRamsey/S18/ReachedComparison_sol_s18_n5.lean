import HypercubeRamsey.S18.ReferenceTests_sol_s18_n5
import HypercubeRamsey.S18.QueryBudget_sol_s18_n5
import HypercubeRamsey.S18.Tower_sol_s18_n4

namespace HypercubeRamsey.S18.Lane_sol_s18_n5
open Classical
open scoped BigOperators
variable {κ : CConsts} {T : Stage} {k : ℕ} {PT : ProfiledTiling κ T k} {hPT : PT.Valid}

theorem extend_test_depends (D : LateData hPT) (j : Fin D.geom.r)
    (cells : Finset D.geom.Cell) (rows : Finset (Pos T k))
    (F : D.encoding.base.History j.succ → ℝ) (hF : HistoryTestLocal D j.succ cells rows F)
    (h : D.encoding.base.History j.castSucc) :
    DependsOn (fun out => F (D.encoding.base.extend j h out))
      ((Finset.univ.filter fun b : {b : Pos T k // b ∈ D.encoding.base.classes j} => b.1 ∈ rows) : Set _) := by
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
      have he := hout ⟨b.1, hc⟩ (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hb⟩)
      simpa only [LateProcessBase.extend, dif_neg hp] using congrArg D.encoding.base.rowLabel he

private theorem class_filter_card (D : LateData hPT) (j : Fin D.geom.r) (rows : Finset (Pos T k)) :
    (Finset.univ.filter fun b : {b : Pos T k // b ∈ D.encoding.base.classes j} => b.1 ∈ rows).card ≤ rows.card := by
  let S := Finset.univ.filter fun b : {b : Pos T k // b ∈ D.encoding.base.classes j} => b.1 ∈ rows
  have hs : S.image Subtype.val ⊆ rows := by
    intro b hb
    obtain ⟨b', hb', rfl⟩ := Finset.mem_image.mp hb
    exact (Finset.mem_filter.mp hb').2
  have he : (S.image Subtype.val).card = S.card := Finset.card_image_of_injective _ Subtype.val_injective
  rw [← he]
  exact Finset.card_le_card hs

private theorem reachedAt_beforeHistory (D : LateData hPT) (δ : ℝ) (j : Fin D.geom.r)
    (h : D.encoding.base.History (Fin.last D.geom.r)) :
    reachedAt D δ j.castSucc (D.beforeHistory h j.castSucc (Nat.le_of_lt j.isLt)) ↔
      reached D δ j h := by
  rfl

private theorem E_mul_const {Ω : Type*} [Fintype Ω] (P : FinLaw Ω) (f : Ω → ℝ) (c : ℝ) :
    P.E (fun x => c * f x) = c * P.E f := by
  unfold FinLaw.E
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro x _
  ring

/-- Actual reached prefix tests compare to their whole reference pullback.
All earlier entering checks remain in the guarded integral until compared. -/
theorem guarded_prefix_comparison (D : LateData hPT) (hD : D.Spec) (hT : TransitionData D)
    {δ ε : ℝ} (C : TerminalCertificate D δ ε) (A : ClassSamplerData D δ)
    (j : Fin D.geom.r) (roots : Finset (Pos T k))
    (G : D.encoding.base.History j.castSucc → ℝ) (hG : ∀ h, 0 ≤ G h)
    (hlocalG : HistoryTestLocal D j.castSucc
      (rowCells D (ancestors roots 1)) (ancestors roots 1) G)
    (hquery : ∀ m, m ≤ D.geom.r + 1 →
      ((ancestors roots m).card : ℝ) ≤ Real.exp (Real.log (T.S.n k) ^ 3)) :
    (FinLaw.bind (D.encoding.terminalLaw (terminalSet D δ) C.positive)
      (fun x => D.encoding.base.runFull A.act (D.encoding.initialState x))).E
        (fun z => if reached D δ j z.2 then
          G (D.beforeHistory z.2 j.castSucc (Nat.le_of_lt j.isLt)) else 0) ≤
      (2 : ℝ) ^ D.geom.r *
        (D.encoding.terminalLaw (terminalSet D δ) C.positive).E (fun x =>
          referenceTests D (fun full => G (D.beforeHistory full j.castSucc (Nat.le_of_lt j.isLt)))
            0 (D.encoding.base.initialHistory (D.encoding.initialState x))) := by
  let F := fun full : D.encoding.base.History (Fin.last D.geom.r) =>
    G (D.beforeHistory full j.castSucc (Nat.le_of_lt j.isLt))
  have hF : ∀ h, 0 ≤ F h := fun _ => hG _
  have hlocalF : HistoryTestLocal D (Fin.last D.geom.r)
      (rowCells D (ancestors roots 1)) (ancestors roots 1) F :=
    HistoryTestLocal.beforeHistory D j.castSucc _ _ _ _ G hlocalG
  have htests := referenceTests_nonneg D F hF
  have hlocal : ∀ s h, D.enter δ s h →
      ∃ S : Finset {b : Pos T k // b ∈ D.encoding.base.classes s},
        (S.card : ℝ) ≤ Real.exp (Real.log (T.S.n k) ^ 3) ∧
        DependsOn (fun out => referenceTests D F s.succ (D.encoding.base.extend s h out)) (S : Set _) := by
    intro s h _
    let rows := ancestors roots (D.geom.r - s.succ.val + 1)
    let S := Finset.univ.filter fun b : {b : Pos T k // b ∈ D.encoding.base.classes s} => b.1 ∈ rows
    refine ⟨S, ?_, extend_test_depends D s _ rows _ (referenceTests_local D hD hT roots F hlocalF s.succ) h⟩
    have hc : (S.card : ℝ) ≤ rows.card := by exact_mod_cast class_filter_card D s rows
    exact hc.trans (hquery _ (by omega))
  have hpoint : ∀ x : D.encoding.InitInput,
      (D.encoding.base.runFull A.act (D.encoding.initialState x)).E
        (fun h => if reached D δ j h then G (D.beforeHistory h j.castSucc (Nat.le_of_lt j.isLt)) else 0) ≤
      (2 : ℝ) ^ D.geom.r * referenceTests D F 0
        (D.encoding.base.initialHistory (D.encoding.initialState x)) := by
    intro x
    let g := fun h : D.encoding.base.History j.castSucc => if reachedAt D δ j.castSucc h then G h else 0
    have hrestrict : (D.encoding.base.runFull A.act (D.encoding.initialState x)).E
        (fun h => if reached D δ j h then G (D.beforeHistory h j.castSucc (Nat.le_of_lt j.isLt)) else 0) =
      (D.encoding.base.runFrom A.act (D.encoding.initialState x) j.val (Nat.le_of_lt j.isLt)).E g := by
      calc
        _ = (D.encoding.base.runFull A.act (D.encoding.initialState x)).E
          (fun h => g (D.beforeHistory h j.castSucc (Nat.le_of_lt j.isLt))) := by
            apply congrArg (D.encoding.base.runFull A.act (D.encoding.initialState x)).E
            funext h
            simp only [g, reachedAt_beforeHistory]
        _ = _ := HypercubeRamsey.Lane_sol_s18_n4.runFromBeforeExpectation D A.act
          (D.encoding.initialState x) j.castSucc g D.geom.r le_rfl (Nat.le_of_lt j.isLt)
    rw [hrestrict]
    have hc := guarded_run_comparison D δ A (referenceTests D F) htests
      (fun s h => (congrFun (referenceTests_step D F s) h).symm) hlocal
      (D.encoding.initialState x) j.val (Nat.le_of_lt j.isLt)
    have hprefix : referenceTests D F j.castSucc = G := by
      funext h
      have hp := referenceTests_prefix D j.castSucc G j.castSucc le_rfl h
      simpa only [beforeHistory_self] using hp
    change (D.encoding.base.runFrom A.act (D.encoding.initialState x) j.val (Nat.le_of_lt j.isLt)).E
      (fun h => if reachedAt D δ j.castSucc h then referenceTests D F j.castSucc h else 0) ≤
        (2 : ℝ) ^ j.val * referenceTests D F 0
          (D.encoding.base.initialHistory (D.encoding.initialState x)) at hc
    rw [hprefix] at hc
    calc
      _ ≤ (2 : ℝ) ^ j.val * referenceTests D F 0
          (D.encoding.base.initialHistory (D.encoding.initialState x)) := hc
      _ ≤ _ := mul_le_mul_of_nonneg_right
        (pow_le_pow_right₀ (by norm_num) (Nat.le_of_lt j.isLt)) (htests 0 _)
  rw [bind_E]
  calc
    _ ≤ (D.encoding.terminalLaw (terminalSet D δ) C.positive).E (fun x =>
        (2 : ℝ) ^ D.geom.r * referenceTests D F 0
          (D.encoding.base.initialHistory (D.encoding.initialState x))) :=
      S16.Lane_q_s16_comp2.expect_le _ _ _ hpoint
    _ = _ := E_mul_const _ _ _

end HypercubeRamsey.S18.Lane_sol_s18_n5
