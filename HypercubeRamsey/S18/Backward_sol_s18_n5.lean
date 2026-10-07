import HypercubeRamsey.S18.Completion_sol_s18_n5

namespace HypercubeRamsey.S18.Lane_sol_s18_n5
open Classical
open scoped BigOperators
variable {κ : CConsts} {T : Stage} {k : ℕ} {PT : ProfiledTiling κ T k} {hPT : PT.Valid}

noncomputable def reachedAt (D : LateData hPT) (δ : ℝ) (t : Fin (D.geom.r + 1))
    (h : D.encoding.base.History t) : Prop :=
  ∀ j : Fin D.geom.r, ∀ hj : j.val < t.val,
    D.enter δ j (D.beforeHistory h j.castSucc (Nat.le_of_lt hj))

theorem reachedAt_extend (D : LateData hPT) (δ : ℝ) (t : Fin D.geom.r)
    (h : D.encoding.base.History t.castSucc) (out : D.encoding.base.ClassRows t) :
    reachedAt D δ t.succ (D.encoding.base.extend t h out) ↔
      reachedAt D δ t.castSucc h ∧ D.enter δ t h := by
  constructor
  · intro hr
    constructor
    · intro j hj
      have hres := hr j (by
        simp only [Fin.val_castSucc] at hj
        simpa only [Fin.val_succ] using Nat.lt_succ_of_lt hj)
      rwa [beforeHistory_extend D t h out j.castSucc (show j.castSucc.val ≤ t.val from hj.le)] at hres
    · have hres := hr t (by simp)
      rwa [beforeHistory_extend D t h out t.castSucc le_rfl, beforeHistory_self] at hres
  · rintro ⟨hr, he⟩ j hj
    by_cases hlt : j.val < t.val
    · rw [beforeHistory_extend D t h out j.castSucc (show j.castSucc.val ≤ t.val from hlt.le)]
      exact hr j hlt
    · have heq : j = t := Fin.ext (by simp only [Fin.val_succ] at hj; omega)
      subst j
      rw [beforeHistory_extend D t h out t.castSucc le_rfl, beforeHistory_self]
      exact he

private theorem map_E {α β : Type*} [Fintype α] [Fintype β] [DecidableEq β]
    (P : FinLaw α) (f : α → β) (g : β → ℝ) :
    (FinLaw.map P f).E g = P.E (fun a => g (f a)) := by
  unfold FinLaw.E FinLaw.map
  simp_rw [Finset.sum_mul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro a _
  simp

private theorem dirac_E {Ω : Type*} [Fintype Ω] [DecidableEq Ω] (x : Ω) (f : Ω → ℝ) :
    (FinLaw.dirac x).E f = f x := by
  classical
  simp [FinLaw.E, FinLaw.dirac]

/-- Backward integration at a reached history. Each stage compares the
entire queried set once, and later reach restrictions have already been
removed from the test being compared. The row scope remains explicit. -/
theorem guarded_run_comparison (D : LateData hPT) (δ : ℝ) (A : ClassSamplerData D δ)
    (tests : ∀ t : Fin (D.geom.r + 1), D.encoding.base.History t → ℝ)
    (htests : ∀ t h, 0 ≤ tests t h)
    (hstep : ∀ (j : Fin D.geom.r) (h : D.encoding.base.History j.castSucc),
      (D.encoding.kernels.referenceTransition j h).E
        (fun out => tests j.succ (D.encoding.base.extend j h out)) = tests j.castSucc h)
    (hlocal : ∀ (j : Fin D.geom.r) (h : D.encoding.base.History j.castSucc), D.enter δ j h →
      ∃ S : Finset {b : Pos T k // b ∈ D.encoding.base.classes j},
        (S.card : ℝ) ≤ Real.exp (Real.log (T.S.n k) ^ 3) ∧
        DependsOn (fun out => tests j.succ (D.encoding.base.extend j h out)) (S : Set _))
    (s : Config D.fresh) (m : ℕ) (hm : m ≤ D.geom.r) :
    (D.encoding.base.runFrom A.act s m hm).E
      (fun h => if reachedAt D δ ⟨m, Nat.lt_succ_of_le hm⟩ h then
        tests ⟨m, Nat.lt_succ_of_le hm⟩ h else 0) ≤
      (2 : ℝ) ^ m * tests 0 (D.encoding.base.initialHistory s) := by
  classical
  induction m with
  | zero =>
    let init : D.encoding.base.History ⟨0, Nat.lt_succ_of_le hm⟩ := D.encoding.base.initialHistory s
    have hLaw : D.encoding.base.runFrom A.act s 0 hm = FinLaw.dirac init := by rfl
    rw [hLaw, dirac_E, pow_zero, one_mul]
    split_ifs
    · rfl
    · exact htests 0 _
  | succ m ih =>
    rw [LateProcessBase.runFrom, map_E, bind_E]
    have hpoint : ∀ h : D.encoding.base.History ⟨m, Nat.lt_succ_of_le (Nat.le_of_succ_le hm)⟩,
        (A.act ⟨m, hm⟩ h).E
          (fun out => if reachedAt D δ ⟨m + 1, Nat.lt_succ_of_le hm⟩
            (D.encoding.base.extend ⟨m, hm⟩ h out) then
              tests ⟨m + 1, Nat.lt_succ_of_le hm⟩ (D.encoding.base.extend ⟨m, hm⟩ h out) else 0) ≤
        2 * (if reachedAt D δ ⟨m, Nat.lt_succ_of_le (Nat.le_of_succ_le hm)⟩ h then
          tests ⟨m, Nat.lt_succ_of_le (Nat.le_of_succ_le hm)⟩ h else 0) := by
      intro h
      have hreach (out : D.encoding.base.ClassRows ⟨m, hm⟩) :
          reachedAt D δ ⟨m + 1, Nat.lt_succ_of_le hm⟩ (D.encoding.base.extend ⟨m, hm⟩ h out) ↔
          reachedAt D δ ⟨m, Nat.lt_succ_of_le (Nat.le_of_succ_le hm)⟩ h ∧ D.enter δ ⟨m, hm⟩ h := by
        simpa only [Fin.succ, Fin.castSucc, Fin.castAdd, Fin.castLE] using reachedAt_extend D δ ⟨m, hm⟩ h out
      by_cases hr : reachedAt D δ ⟨m, Nat.lt_succ_of_le (Nat.le_of_succ_le hm)⟩ h
      · by_cases he : D.enter δ ⟨m, hm⟩ h
        · obtain ⟨S, hS, hdep⟩ := hlocal ⟨m, hm⟩ h he
          have hcomp := (A.sampler ⟨m, hm⟩ h he).2 S hS
            (fun out => tests (⟨m, hm⟩ : Fin D.geom.r).succ (D.encoding.base.extend ⟨m, hm⟩ h out))
            (fun out => htests _ _) hdep
          rw [hstep] at hcomp
          simp only [hreach, hr, he, and_self, if_true]
          simpa only [Fin.succ, Fin.castSucc, Fin.castAdd, Fin.castLE] using hcomp
        · simp only [hreach, he, and_false, if_false, E_const, hr, if_true]
          exact mul_nonneg (by norm_num) (htests _ _)
      · simp only [hreach, hr, false_and, if_false, E_const, mul_zero]
        exact le_rfl
    calc
      _ ≤ (D.encoding.base.runFrom A.act s m (Nat.le_of_succ_le hm)).E
          (fun h => 2 * (if reachedAt D δ ⟨m, Nat.lt_succ_of_le (Nat.le_of_succ_le hm)⟩ h then
            tests ⟨m, Nat.lt_succ_of_le (Nat.le_of_succ_le hm)⟩ h else 0)) :=
        S16.Lane_q_s16_comp2.expect_le _ _ _ hpoint
      _ = 2 * (D.encoding.base.runFrom A.act s m (Nat.le_of_succ_le hm)).E
          (fun h => if reachedAt D δ ⟨m, Nat.lt_succ_of_le (Nat.le_of_succ_le hm)⟩ h then
            tests ⟨m, Nat.lt_succ_of_le (Nat.le_of_succ_le hm)⟩ h else 0) := by
        unfold FinLaw.E
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro h _
        ring
      _ ≤ 2 * ((2 : ℝ) ^ m * tests 0 (D.encoding.base.initialHistory s)) :=
        mul_le_mul_of_nonneg_left (ih _) (by norm_num)
      _ = _ := by rw [pow_succ]; ring

end HypercubeRamsey.S18.Lane_sol_s18_n5
