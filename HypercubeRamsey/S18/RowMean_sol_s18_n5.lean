import HypercubeRamsey.S18.ReferenceProduct_sol_s18_n5
import HypercubeRamsey.S18.Tower_sol_s18_n4

namespace HypercubeRamsey.S18.Lane_sol_s18_n5
open Classical
open scoped BigOperators
variable {κ : CConsts} {T : Stage} {k : ℕ} {PT : ProfiledTiling κ T k} {hPT : PT.Valid}

private theorem mean_pr_E {Ω : Type*} [Fintype Ω] (P : FinLaw Ω) (A : Ω → Prop) :
    P.pr A = P.E (fun x => if A x then 1 else 0) := by
  unfold FinLaw.pr FinLaw.E
  apply Finset.sum_congr rfl
  intro x _
  by_cases hx : A x <;> simp [hx]

private theorem mean_map_E {α β : Type*} [Fintype α] [Fintype β] [DecidableEq β]
    (P : FinLaw α) (f : α → β) (g : β → ℝ) :
    (FinLaw.map P f).E g = P.E (fun a => g (f a)) := by
  unfold FinLaw.E FinLaw.map
  simp_rw [Finset.sum_mul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro a _
  simp

/-- Averaging the conditional mass in the full reference run gives its
actual label marginal, including all later classes. -/
theorem reference_row_mean (D : LateData hPT) (s : Config D.fresh) (j : Fin D.geom.r)
    (b : {b : Pos T k // b ∈ D.encoding.base.classes j}) (y : Fin (T.S.N k)) :
    (D.encoding.kernels.refRun s).E (fun h =>
      (D.encoding.kernels.refK j b
        (D.beforeHistory h j.castSucc (Nat.le_of_lt j.isLt))).pr
        (fun out => D.encoding.base.rowLabel out = y)) =
    (D.encoding.kernels.refRun s).pr (fun h =>
      D.encoding.base.rowLabel (D.pastRows h j j.isLt b) = y) := by
  classical
  let G := fun h : D.encoding.base.History j.castSucc =>
    (D.encoding.kernels.refK j b h).pr (fun out => D.encoding.base.rowLabel out = y)
  let F := fun h : D.encoding.base.History j.succ =>
    if D.encoding.base.rowLabel (D.pastRows h j (by simp) b) = y then (1 : ℝ) else 0
  have hpre := HypercubeRamsey.Lane_sol_s18_n4.runFromBeforeExpectation D
    D.encoding.kernels.referenceTransition s j.castSucc G D.geom.r le_rfl (Nat.le_of_lt j.isLt)
  have hpost := HypercubeRamsey.Lane_sol_s18_n4.runFromBeforeExpectation D
    D.encoding.kernels.referenceTransition s j.succ F D.geom.r le_rfl (Nat.succ_le_of_lt j.isLt)
  have hpost' : (D.encoding.kernels.refRun s).pr (fun h =>
      D.encoding.base.rowLabel (D.pastRows h j j.isLt b) = y) =
      (D.encoding.base.runFrom D.encoding.kernels.referenceTransition s j.succ.val
        (Nat.succ_le_of_lt j.isLt)).E F := by
    calc
      _ = (D.encoding.kernels.refRun s).E (fun h =>
          F (D.beforeHistory h j.succ (Nat.succ_le_of_lt j.isLt))) := by
        unfold FinLaw.pr FinLaw.E
        apply Finset.sum_congr rfl
        intro h _
        simp only [F, HypercubeRamsey.Lane_sol_s18_n4.pastRows_beforeHistory]
        by_cases hp : D.encoding.base.rowLabel (D.pastRows h j j.isLt b) = y <;> simp [hp]
      _ = _ := hpost
  rw [hpost']
  change (D.encoding.base.runFrom D.encoding.kernels.referenceTransition s D.geom.r le_rfl).E
    (fun h => G (D.beforeHistory h j.castSucc (Nat.le_of_lt j.isLt))) = _
  rw [hpre]
  change _ = (D.encoding.base.runFrom D.encoding.kernels.referenceTransition s (j.val + 1)
    (Nat.succ_le_of_lt j.isLt)).E F
  rw [LateProcessBase.runFrom, mean_map_E, bind_E]
  apply congrArg (D.encoding.base.runFrom D.encoding.kernels.referenceTransition s j.val
    (Nat.le_of_lt j.isLt)).E
  funext h
  change G h = (D.encoding.kernels.referenceTransition j h).E
    (fun out => if D.encoding.base.rowLabel
      (D.pastRows (D.encoding.base.extend j h out) j (by simp) b) = y then 1 else 0)
  simp only [pastRows_extend_current]
  have he := pi_expect_coord (fun b => D.encoding.kernels.refK j b h)
    b (fun out => if D.encoding.base.rowLabel out = y then (1 : ℝ) else 0)
  calc
    G h = (D.encoding.kernels.refK j b h).E
        (fun out => if D.encoding.base.rowLabel out = y then 1 else 0) := by
      unfold G FinLaw.pr FinLaw.E
      apply Finset.sum_congr rfl
      intro out _
      by_cases hp : D.encoding.base.rowLabel out = y <;> simp [hp]
    _ = _ := he.symm

theorem baseline_row_mean (D : LateData hPT) (j : Fin D.geom.r)
    (b : {b : Pos T k // b ∈ D.encoding.base.classes j}) (y : Fin (T.S.N k)) :
    D.encoding.baseline.E (fun z =>
      (D.encoding.kernels.refK j b
        (D.beforeHistory z.2 j.castSucc (Nat.le_of_lt j.isLt))).pr
        (fun out => D.encoding.base.rowLabel out = y)) =
    D.encoding.baseline.pr (fun z =>
      D.encoding.base.rowLabel (D.pastRows z.2 j j.isLt b) = y) := by
  rw [mean_pr_E, LateEncoding.baseline, bind_E, bind_E]
  apply congrArg (D.encoding.initialLaw D.encoding.iidLaw).E
  funext x
  exact (reference_row_mean D (D.encoding.initialState x) j b y).trans (mean_pr_E _ _)

theorem baseline_row_mean_le (D : LateData hPT) (hBalance : MaskBalance D)
    (j : Fin D.geom.r) (b : {b : Pos T k // b ∈ D.encoding.base.classes j})
    (y : Fin (T.S.N k)) :
    D.encoding.baseline.E (fun z =>
      (D.encoding.kernels.refK j b
        (D.beforeHistory z.2 j.castSucc (Nat.le_of_lt j.isLt))).pr
        (fun out => D.encoding.base.rowLabel out = y)) ≤
      2 / (D.encoding.base.latePool j).card := by
  rw [baseline_row_mean]
  exact hBalance j b y

end HypercubeRamsey.S18.Lane_sol_s18_n5
