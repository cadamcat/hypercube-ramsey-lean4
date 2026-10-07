import HypercubeRamsey.S18.Defs
import HypercubeRamsey.Framework.FinProbLemmas

namespace HypercubeRamsey.Lane_sol_s18_n4
open Classical
open scoped BigOperators

private theorem lawMapE {α β : Type*} [Fintype α] [Fintype β]
    [DecidableEq β] (P : FinLaw α) (f : α → β) (g : β → ℝ) :
    (FinLaw.map P f).E g = P.E (fun x => g (f x)) := by
  unfold FinLaw.E FinLaw.map
  simp_rw [Finset.sum_mul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro x hx
  simp only [ite_mul, zero_mul]
  simp

private theorem lawBindE {α β : Type*} [Fintype α] [Fintype β]
    (P : FinLaw α) (K : α → FinLaw β) (g : α × β → ℝ) :
    (FinLaw.bind P K).E g = P.E (fun x => (K x).E (fun y => g (x, y))) := by
  simp only [FinLaw.E, FinLaw.bind, Fintype.sum_prod_type, Finset.mul_sum, mul_assoc]

private theorem lawPrE {α : Type*} [Fintype α] (P : FinLaw α) (A : α → Prop) :
    P.pr A = P.E (fun x => if A x then 1 else 0) := by
  unfold FinLaw.pr FinLaw.E
  apply Finset.sum_congr rfl
  intro x hx
  by_cases h : A x <;> simp [h]

private theorem lawEConst {α : Type*} [Fintype α] (P : FinLaw α) (c : ℝ) :
    P.E (fun _ => c) = c := by
  simp [FinLaw.E, ← Finset.sum_mul, P.sum_one]

variable {κ : CConsts} {T : Stage} {k : ℕ} {PT : ProfiledTiling κ T k}
    {hPT : PT.Valid} (D : S18.LateData hPT)

 theorem beforeHistory_extend
    (i : Fin (D.geom.r + 1)) (j : Fin D.geom.r) (hij : i.val ≤ j.val)
    (h : D.encoding.base.History j.castSucc) (out : D.encoding.base.ClassRows j) :
    D.beforeHistory (D.encoding.base.extend j h out) i (by simpa using hij.trans (Nat.le_succ j.val)) =
      D.beforeHistory h i hij := by
  apply Prod.ext
  · rfl
  funext b
  have hb : b.1 ∈ D.encoding.base.processed j.castSucc :=
    D.processed_mono i j.castSucc hij b.2
  simp [S18.LateData.beforeHistory, LateProcessBase.extend, hb]

 theorem pastRows_extend_self
    (j : Fin D.geom.r) (h : D.encoding.base.History j.castSucc)
    (out : D.encoding.base.ClassRows j) :
    D.pastRows (D.encoding.base.extend j h out) j (by simp) = out := by
  funext b
  have hb : b.1 ∉ D.encoding.base.processed j.castSucc :=
    Finset.disjoint_left.mp (D.encoding.base.class_fresh j) b.2
  simp [S18.LateData.pastRows, LateProcessBase.extend, hb]

 theorem beforeHistory_extend_self
    (j : Fin D.geom.r) (h : D.encoding.base.History j.castSucc)
    (out : D.encoding.base.ClassRows j) :
    D.beforeHistory (D.encoding.base.extend j h out) j.castSucc (by simp) = h := by
  apply Prod.ext
  · rfl
  funext b
  simp [S18.LateData.beforeHistory, LateProcessBase.extend, b.2]

 theorem pastRows_extend_earlier
    (i j : Fin D.geom.r) (hij : i.val < j.val)
    (h : D.encoding.base.History j.castSucc) (out : D.encoding.base.ClassRows j) :
    D.pastRows (D.encoding.base.extend j h out) i (by simp; omega) =
      D.pastRows h i hij := by
  funext b
  have hb : b.1 ∈ D.encoding.base.processed j.castSucc := D.class_before i j.castSucc hij b.2
  simp [S18.LateData.pastRows, LateProcessBase.extend, hb]

private theorem lawELeConst {α : Type*} [Fintype α] (P : FinLaw α)
    (g : α → ℝ) (c : ℝ) (hg : ∀ x, g x ≤ c) : P.E g ≤ c := by
  rw [← lawEConst P c]
  unfold FinLaw.E
  exact Finset.sum_le_sum (fun x _ => mul_le_mul_of_nonneg_left (hg x) (P.nonneg x))

/-- A bound on one class experiment remains valid after every later class. -/
theorem runFromClassBound (D : S18.LateData hPT)
    (step : ∀ j : Fin D.geom.r, D.encoding.base.History j.castSucc →
      FinLaw (D.encoding.base.ClassRows j))
    (s : Config D.fresh) (j : Fin D.geom.r)
    (A : D.encoding.base.History j.castSucc → D.encoding.base.ClassRows j → Prop)
    (c : ℝ) (hA : ∀ h, (step j h).pr (A h) ≤ c) :
    ∀ m (hm : m ≤ D.geom.r) (hj : j.val < m),
      (D.encoding.base.runFrom step s m hm).pr (fun full =>
        A (D.beforeHistory full j.castSucc (Nat.le_of_lt hj)) (D.pastRows full j hj)) ≤ c := by
  intro m
  induction m with
  | zero => intro hm hj; omega
  | succ m ih =>
    intro hm hj
    rw [LateProcessBase.runFrom, lawPrE, lawMapE, lawBindE]
    by_cases heq : j.val = m
    · have hjEq : (⟨m, hm⟩ : Fin D.geom.r) = j := Fin.ext heq.symm
      subst m
      have hjEq : (⟨j.val, hm⟩ : Fin D.geom.r) = j := rfl
      simp only [hjEq]
      simp_rw [beforeHistory_extend_self, pastRows_extend_self, ← lawPrE]
      exact lawELeConst _ _ c hA
    · have hjm : j.val < m := by omega
      have hsame (h : D.encoding.base.History ⟨m, Nat.lt_succ_of_le (Nat.le_of_succ_le hm)⟩)
          (out : D.encoding.base.ClassRows ⟨m, hm⟩) :
          A (D.beforeHistory (D.encoding.base.extend ⟨m, hm⟩ h out) j.castSucc (Nat.le_of_lt hj))
            (D.pastRows (D.encoding.base.extend ⟨m, hm⟩ h out) j hj) =
          A (D.beforeHistory h j.castSucc (Nat.le_of_lt hjm)) (D.pastRows h j hjm) := by
        rw [beforeHistory_extend D j.castSucc ⟨m, hm⟩ (Nat.le_of_lt hjm),
          pastRows_extend_earlier D j ⟨m, hm⟩ hjm]
      simp_rw [hsame, lawEConst, ← lawPrE]
      exact ih (Nat.le_of_succ_le hm) hjm

 theorem refRunClassBound (D : S18.LateData hPT) (s : Config D.fresh)
    (j : Fin D.geom.r)
    (A : D.encoding.base.History j.castSucc → D.encoding.base.ClassRows j → Prop)
    (c : ℝ) (hA : ∀ h, (D.encoding.kernels.referenceTransition j h).pr (A h) ≤ c) :
    (D.encoding.kernels.refRun s).pr (fun full =>
      A (D.beforeHistory full j.castSucc (Nat.le_of_lt j.isLt)) (D.pastRows full j j.isLt)) ≤ c :=
  runFromClassBound D _ s j A c hA _ le_rfl j.isLt

private theorem lawPiPrProjection {I : Type*} [Fintype I] [DecidableEq I]
    {Ω : I → Type*} [∀ i, Fintype (Ω i)] (P : ∀ i, FinLaw (Ω i))
    (i : I) (A : Ω i → Prop) :
    (FinLaw.pi P).pr (fun out => A (out i)) = (P i).pr A := by
  let p : ∀ i, FinProb (Ω i) := fun i => ⟨(P i).w, (P i).nonneg, (P i).sum_one⟩
  let J := {j : I // j ∈ ({i} : Finset I)}
  letI : Unique J := {
    default := ⟨i, Finset.mem_singleton_self i⟩
    uniq := by intro j; exact Subtype.ext (Finset.mem_singleton.mp j.2) }
  let e : (∀ j : J, Ω j.1) ≃ Ω i := Equiv.piUnique (fun j : J => Ω j.1)
  have h := FinProb.pi_marginal_expect p {i} (fun a => if A (a default) then 1 else 0)
  have hleft : (FinProb.pi p).expect (fun out => if A (out i) then 1 else 0) =
      (FinLaw.pi P).pr (fun out => A (out i)) := by
    unfold FinProb.expect FinProb.pi FinLaw.pr FinLaw.pi
    apply Finset.sum_congr rfl
    intro out hout
    by_cases ha : A (out i) <;> simp [ha, p]
  have hright : (FinProb.pi (fun j : J => p j.1)).expect
        (fun a => if A (a default) then 1 else 0) = (P i).pr A := by
    unfold FinProb.expect FinProb.pi
    simp only [Fintype.prod_unique]
    rw [← e.symm.sum_comp]
    unfold FinLaw.pr
    apply Finset.sum_congr rfl
    intro out hout
    change (P i).w out * (if A out then 1 else 0) = (if A out then (P i).w out else 0)
    by_cases ha : A out <;> simp [ha]
  rw [← hleft, ← hright]
  exact h

/-- The supplied local tail bounds integrate through the complete reference run. -/
theorem nonPrefixLateProbabilityBound (D : S18.LateData hPT)
    (K27 : ℝ) (hlocal : S18.LocalTransitionFacts D K27)
    (s : Config D.fresh) (F : S18.LateEvent D) (hkind : F.1.val ≠ 1) :
    (D.encoding.kernels.refRun s).pr (S18.lateFailure D F) ≤
      Real.exp (-Real.rpow (T.S.n k : ℝ) 0.04) := by
  let j := F.2.1
  let b := F.2.2.1
  let A := fun (h : D.encoding.base.History j.castSucc) (out : D.encoding.base.ClassRows j) =>
    D.gate j b.1 h ∧ if F.1.val = 0 then ¬ D.R1 j (out b)
      else D.R1 j (out b) ∧ D.R2 j h (out b) ∧ ¬ D.R3 j h (out b)
  have hevent : S18.lateFailure D F = fun full : D.encoding.base.History (Fin.last D.geom.r) =>
      A (D.beforeHistory full j.castSucc (Nat.le_of_lt j.isLt)) (D.pastRows full j j.isLt) := by
    funext full
    simp only [S18.lateFailure, if_neg hkind]
    rfl
  rw [hevent]
  apply refRunClassBound D s j A
  intro h
  by_cases hgate : D.gate j b.1 h
  · dsimp [A]
    simp only [hgate, true_and]
    rw [LateKernels.referenceTransition]
    by_cases hzero : F.1.val = 0
    · simp only [if_pos hzero]
      rw [lawPiPrProjection (fun b => D.encoding.kernels.refK j b h) b (fun out => ¬ D.R1 j out)]
      exact hlocal.2.2.1 j b h hgate
    · simp only [if_neg hzero]
      rw [lawPiPrProjection (fun b => D.encoding.kernels.refK j b h) b
        (fun out => D.R1 j out ∧ D.R2 j h out ∧ ¬ D.R3 j h out)]
      exact hlocal.2.2.2 j b h hgate
  · have hz : (D.encoding.kernels.referenceTransition j h).pr (A h) = 0 := by
      unfold FinLaw.pr
      apply Finset.sum_eq_zero
      intro out hout
      simp [A, hgate]
    rw [hz]
    exact (Real.exp_pos _).le

 theorem nonPrefixTerminalFailureImpossible (D : S18.LateData hPT)
    (K27 δ : ℝ) (hlocal : S18.LocalTransitionFacts D K27)
    (hn : 1 ≤ T.S.n k) (hδ : δ ≤ 0.04)
    (F : S18.LateEvent D) (hkind : F.1.val ≠ 1) (x : D.encoding.InitInput) :
    ¬ S18.terminalFailure D δ (.inr (.inr F)) x := by
  intro hbad
  have hle := nonPrefixLateProbabilityBound D K27 hlocal (D.encoding.initialState x) F hkind
  have hpow : Real.rpow (T.S.n k : ℝ) δ ≤ Real.rpow (T.S.n k : ℝ) 0.04 :=
    Real.rpow_le_rpow_of_exponent_le (by exact_mod_cast hn) hδ
  have hexp : Real.exp (-Real.rpow (T.S.n k : ℝ) 0.04) ≤
      Real.exp (-Real.rpow (T.S.n k : ℝ) δ) := Real.exp_le_exp.mpr (by linarith)
  exact (not_lt_of_ge (hle.trans hexp)) hbad.2

 theorem nonPrefixTerminalPinnedBound (D : S18.LateData hPT)
    (K27 δ : ℝ) (hlocal : S18.LocalTransitionFacts D K27)
    (hn : 1 ≤ T.S.n k) (hδ : δ ≤ 0.04)
    (F : S18.LateEvent D) (hkind : F.1.val ≠ 1) (pin : Option (S18.SlotPin D)) :
    S18.initialProbability D pin (S18.terminalFailure D δ (.inr (.inr F))) ≤
      Real.rpow (T.S.n k : ℝ) (-((κ.P : ℝ) * D.encoding.Ts / 3)) := by
  have hfalse : ∀ x, ¬ S18.terminalFailure D δ (.inr (.inr F)) x :=
    nonPrefixTerminalFailureImpossible D K27 δ hlocal hn hδ F hkind
  have hz : ∀ P : FinLaw D.encoding.InitInput,
      P.pr (S18.terminalFailure D δ (.inr (.inr F))) = 0 := by
    intro P
    simp [FinLaw.pr, hfalse]
  cases pin with
  | none => simp [S18.initialProbability, hz, Real.rpow_nonneg]
  | some p =>
    have hnumerator : D.encoding.permLaw.pr
        (fun x => S18.pinEvent D p x ∧ S18.terminalFailure D δ (.inr (.inr F)) x) = 0 := by
      simp [FinLaw.pr, hfalse]
    simp [S18.initialProbability, hnumerator, Real.rpow_nonneg]

end HypercubeRamsey.Lane_sol_s18_n4
