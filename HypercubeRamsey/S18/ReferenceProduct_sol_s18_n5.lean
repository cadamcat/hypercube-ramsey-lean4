import HypercubeRamsey.S18.ColumnComparison_sol_s18_n5
import HypercubeRamsey.S18.Independence_sol_s18_n5

namespace HypercubeRamsey.S18.Lane_sol_s18_n5
open Classical
open scoped BigOperators
variable {κ : CConsts} {T : Stage} {k : ℕ} {PT : ProfiledTiling κ T k} {hPT : PT.Valid}

private theorem ancestors_mono (roots : Finset (Pos T k)) {a b : ℕ} (hab : a ≤ b) :
    ancestors roots a ⊆ ancestors roots b := by
  induction b, hab using Nat.le_induction with
  | base => exact Finset.Subset.refl _
  | succ b _ ih => exact ih.trans (ancestors_step_subset roots b)

/-- Disjoint complete ancestor row sets make each class integral factor.
The evolving tests are the recursively defined reference pullbacks. -/
theorem referenceTests_product (D : LateData hPT) (hD : D.Spec) (hT : TransitionData D)
    {J : Type*} [Fintype J] [DecidableEq J]
    (roots : J → Finset (Pos T k)) (F : J → D.encoding.base.History (Fin.last D.geom.r) → ℝ)
    (hlocal : ∀ i, HistoryTestLocal D (Fin.last D.geom.r)
      (rowCells D (ancestors (roots i) 1)) (ancestors (roots i) 1) (F i))
    (hdisj : ∀ i i', i ≠ i' → Disjoint
      (ancestors (roots i) (D.geom.r + 1)) (ancestors (roots i') (D.geom.r + 1)))
    (t : Fin (D.geom.r + 1)) : ∀ h,
    referenceTests D (fun h => ∏ i, F i h) t h = ∏ i, referenceTests D (F i) t h := by
  induction t using Fin.reverseInduction with
  | last => intro h; simp only [referenceTests_last]
  | @cast s ih =>
    intro h
    let R := fun i => ancestors (roots i) (D.geom.r - s.succ.val + 1)
    let S := fun i => Finset.univ.filter
      (fun b : {b : Pos T k // b ∈ D.encoding.base.classes s} => b.1 ∈ R i)
    have hdep : ∀ i out out', (∀ b ∈ S i, out b = out' b) →
        referenceTests D (F i) s.succ (D.encoding.base.extend s h out) =
          referenceTests D (F i) s.succ (D.encoding.base.extend s h out') := by
      intro i
      exact extend_test_depends D s _ (R i) _
        (referenceTests_local D hD hT (roots i) (F i) (hlocal i) s.succ) h
    have hSdisj : ∀ i i', i ≠ i' → Disjoint (S i) (S i') := by
      intro i i' hii'
      apply Finset.disjoint_left.mpr
      intro b hb hb'
      apply Finset.disjoint_left.mp (hdisj i i' hii')
      · exact ancestors_mono (roots i) (by omega) (Finset.mem_filter.mp hb).2
      · exact ancestors_mono (roots i') (by omega) (Finset.mem_filter.mp hb').2
    have hfactor := pi_product_local (fun b => D.encoding.kernels.refK s b h) Finset.univ
      (fun i out => referenceTests D (F i) s.succ (D.encoding.base.extend s h out)) S hdep hSdisj
    have hnext : referenceTests D (fun h => ∏ i, F i h) s.succ =
        fun h => ∏ i, referenceTests D (F i) s.succ h := funext ih
    rw [referenceTests_step, hnext]
    change (D.encoding.kernels.referenceTransition s h).E
      (fun out => ∏ i, referenceTests D (F i) s.succ (D.encoding.base.extend s h out)) =
      ∏ i, referenceTests D (F i) s.castSucc h
    rw [show (D.encoding.kernels.referenceTransition s h).E
      (fun out => ∏ i, referenceTests D (F i) s.succ (D.encoding.base.extend s h out)) =
      ∏ i, (D.encoding.kernels.referenceTransition s h).E
        (fun out => referenceTests D (F i) s.succ (D.encoding.base.extend s h out)) from hfactor]
    apply Finset.prod_congr rfl
    intro i _
    exact (congrFun (referenceTests_step D (F i) s) h).symm

private theorem map_E {α β : Type*} [Fintype α] [Fintype β] [DecidableEq β]
    (P : FinLaw α) (f : α → β) (g : β → ℝ) :
    (FinLaw.map P f).E g = P.E (fun a => g (f a)) := by
  unfold FinLaw.E FinLaw.map
  simp_rw [Finset.sum_mul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro a _
  simp

theorem referenceTests_runFrom (D : LateData hPT)
    (F : D.encoding.base.History (Fin.last D.geom.r) → ℝ) (s : Config D.fresh)
    (m : ℕ) (hm : m ≤ D.geom.r) :
    (D.encoding.base.runFrom D.encoding.kernels.referenceTransition s m hm).E
      (referenceTests D F ⟨m, Nat.lt_succ_of_le hm⟩) =
      referenceTests D F 0 (D.encoding.base.initialHistory s) := by
  induction m with
  | zero =>
    change (FinLaw.dirac (D.encoding.base.initialHistory s)).E (referenceTests D F 0) = _
    unfold FinLaw.E FinLaw.dirac
    rw [Finset.sum_eq_single (D.encoding.base.initialHistory s)]
    · simp
    · intro h _ hne
      simp [hne]
    · intro hn
      exact False.elim (hn (Finset.mem_univ _))
  | succ m ih =>
    rw [LateProcessBase.runFrom, map_E, bind_E]
    have hs : ∀ h : D.encoding.base.History ⟨m, Nat.lt_succ_of_le (Nat.le_of_succ_le hm)⟩,
        (D.encoding.kernels.referenceTransition ⟨m, hm⟩ h).E
          (fun out => referenceTests D F ⟨m + 1, Nat.lt_succ_of_le hm⟩
            (D.encoding.base.extend ⟨m, hm⟩ h out)) =
        referenceTests D F ⟨m, Nat.lt_succ_of_le (Nat.le_of_succ_le hm)⟩ h := by
      intro h
      exact (congrFun (referenceTests_step D F ⟨m, hm⟩) h).symm
    simp_rw [hs]
    exact ih (Nat.le_of_succ_le hm)

theorem baseline_reference_test (D : LateData hPT)
    (F : D.encoding.base.History (Fin.last D.geom.r) → ℝ) :
    D.encoding.baseline.E (fun z => F z.2) =
      (D.encoding.initialLaw D.encoding.iidLaw).E (fun x =>
        referenceTests D F 0 (D.encoding.base.initialHistory (D.encoding.initialState x))) := by
  rw [LateEncoding.baseline, bind_E]
  apply congrArg (D.encoding.initialLaw D.encoding.iidLaw).E
  funext x
  have h := referenceTests_runFrom D F (D.encoding.initialState x) D.geom.r le_rfl
  change (D.encoding.base.runFrom D.encoding.kernels.referenceTransition
    (D.encoding.initialState x) D.geom.r le_rfl).E (referenceTests D F (Fin.last D.geom.r)) = _ at h
  rw [referenceTests_last] at h
  exact h

/-- Separation of the complete row ancestors and complete input horizons
factors computations in the full iid-slot/resampling/reference baseline. -/
theorem baseline_product_local (D : LateData hPT) (hD : D.Spec) (hT : TransitionData D)
    {J : Type*} [Fintype J] [DecidableEq J]
    (roots : J → Finset (Pos T k)) (F : J → D.encoding.base.History (Fin.last D.geom.r) → ℝ)
    (hlocal : ∀ i, HistoryTestLocal D (Fin.last D.geom.r)
      (rowCells D (ancestors (roots i) 1)) (ancestors (roots i) 1) (F i))
    (hrows : ∀ i i', i ≠ i' → Disjoint
      (ancestors (roots i) (D.geom.r + 1)) (ancestors (roots i') (D.geom.r + 1)))
    (hcells : ∀ i i', i ≠ i' → Disjoint
      (D.expandCells (rowCells D (ancestors (roots i) (D.geom.r + 1))))
      (D.expandCells (rowCells D (ancestors (roots i') (D.geom.r + 1))))) :
    D.encoding.baseline.E (fun z => ∏ i, F i z.2) = ∏ i, D.encoding.baseline.E (fun z => F i z.2) := by
  rw [baseline_reference_test D (fun h => ∏ i, F i h)]
  have hprod : ∀ x : D.encoding.InitInput,
      referenceTests D (fun h => ∏ i, F i h) 0
        (D.encoding.base.initialHistory (D.encoding.initialState x)) =
      ∏ i, referenceTests D (F i) 0 (D.encoding.base.initialHistory (D.encoding.initialState x)) :=
    fun x => referenceTests_product D hD hT roots F hlocal hrows 0 _
  simp_rw [hprod]
  have hf := iid_input_product_local D Finset.univ
    (fun i x => referenceTests D (F i) 0 (D.encoding.base.initialHistory (D.encoding.initialState x)))
    (fun i => D.expandCells (rowCells D (ancestors (roots i) (D.geom.r + 1))))
    (fun i => referenceTests_initial_input_local D hD hT (roots i) (F i) (hlocal i)) hcells
  rw [hf]
  apply Finset.prod_congr rfl
  intro i _
  exact (baseline_reference_test D (F i)).symm

end HypercubeRamsey.S18.Lane_sol_s18_n5
