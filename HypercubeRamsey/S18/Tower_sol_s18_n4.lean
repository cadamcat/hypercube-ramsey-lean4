import HypercubeRamsey.S18.Run_sol_s18_n4

namespace HypercubeRamsey.Lane_sol_s18_n4
open Classical
open scoped BigOperators

private theorem towerMapE {α β : Type*} [Fintype α] [Fintype β]
    [DecidableEq β] (P : FinLaw α) (f : α → β) (g : β → ℝ) :
    (FinLaw.map P f).E g = P.E (fun x => g (f x)) := by
  unfold FinLaw.E FinLaw.map
  simp_rw [Finset.sum_mul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro x hx
  simp only [ite_mul, zero_mul]
  simp

private theorem towerBindE {α β : Type*} [Fintype α] [Fintype β]
    (P : FinLaw α) (K : α → FinLaw β) (g : α × β → ℝ) :
    (FinLaw.bind P K).E g = P.E (fun x => (K x).E (fun y => g (x, y))) := by
  simp only [FinLaw.E, FinLaw.bind, Fintype.sum_prod_type, Finset.mul_sum, mul_assoc]

private theorem towerEConst {α : Type*} [Fintype α] (P : FinLaw α) (c : ℝ) :
    P.E (fun _ => c) = c := by
  simp [FinLaw.E, ← Finset.sum_mul, P.sum_one]

private theorem towerPrNonneg {Ω : Type*} [Fintype Ω]
    (P : FinLaw Ω) (A : Ω → Prop) : 0 ≤ P.pr A := by
  unfold FinLaw.pr
  exact Finset.sum_nonneg (fun x _ => by split_ifs <;> simp [P.nonneg])

private theorem towerPrMono {Ω : Type*} [Fintype Ω]
    (P : FinLaw Ω) {A B : Ω → Prop} (h : ∀ x, A x → B x) : P.pr A ≤ P.pr B := by
  unfold FinLaw.pr
  apply Finset.sum_le_sum
  intro x hx
  by_cases ha : A x
  · simp [ha, h x ha]
  · by_cases hb : B x <;> simp [ha, hb, P.nonneg]

variable {κ : CConsts} {T : Stage} {k : ℕ} {PT : ProfiledTiling κ T k}
    {hPT : PT.Valid} (D : S18.LateData hPT)

theorem beforeHistory_self (i : Fin (D.geom.r + 1))
    (h : D.encoding.base.History i) : D.beforeHistory h i le_rfl = h := by
  apply Prod.ext
  · rfl
  funext b
  rfl

theorem beforeHistory_comp (i j m : Fin (D.geom.r + 1))
    (hij : i.val ≤ j.val) (hjm : j.val ≤ m.val) (h : D.encoding.base.History m) :
    D.beforeHistory (D.beforeHistory h j hjm) i hij =
      D.beforeHistory h i (hij.trans hjm) := by
  apply Prod.ext
  · rfl
  funext b
  rfl

theorem extend_beforeHistory_pastRows (j : Fin D.geom.r)
    (h : D.encoding.base.History j.succ) :
    D.encoding.base.extend j (D.beforeHistory h j.castSucc (by simp))
      (D.pastRows h j (by simp)) = h := by
  apply Prod.ext
  · rfl
  funext b
  dsimp [LateProcessBase.extend, S18.LateData.beforeHistory, S18.LateData.pastRows]
  split_ifs <;> rfl

theorem extend_injective (j : Fin D.geom.r) :
    Function.Injective (fun z : D.encoding.base.History j.castSucc × D.encoding.base.ClassRows j =>
      D.encoding.base.extend j z.1 z.2) := by
  intro x y hxy
  apply Prod.ext
  · have h := congrArg (fun h => D.beforeHistory h j.castSucc (by simp)) hxy
    simpa only [beforeHistory_extend_self] using h
  · have h := congrArg (fun h => D.pastRows h j (by simp)) hxy
    simpa only [pastRows_extend_self] using h

/-- Restricting a full sequential experiment gives its actual earlier-stage law. -/
theorem runFromBeforeExpectation
    (step : ∀ j : Fin D.geom.r, D.encoding.base.History j.castSucc →
      FinLaw (D.encoding.base.ClassRows j)) (s : Config D.fresh)
    (i : Fin (D.geom.r + 1)) (g : D.encoding.base.History i → ℝ) :
    ∀ m (hm : m ≤ D.geom.r) (him : i.val ≤ m),
      (D.encoding.base.runFrom step s m hm).E
        (fun h => g (D.beforeHistory h i him)) =
      (D.encoding.base.runFrom step s i.val (Nat.le_of_lt_succ i.isLt)).E g := by
  intro m
  induction m with
  | zero =>
      intro hm him
      have hi : i = 0 := Fin.ext (by simpa using him)
      subst i
      rfl
  | succ m ih =>
      intro hm him
      by_cases heq : i.val = m + 1
      · have hi : (⟨m + 1, Nat.lt_succ_of_le hm⟩ : Fin (D.geom.r + 1)) = i := Fin.ext heq.symm
        have hg : (fun h : D.encoding.base.History ⟨m + 1, Nat.lt_succ_of_le hm⟩ =>
            g (D.beforeHistory h i him)) = fun h => g (hi ▸ h) := by
          subst i
          simp only [beforeHistory_self]
        subst i
        simp only [beforeHistory_self]
      · have him' : i.val ≤ m := by omega
        rw [LateProcessBase.runFrom, towerMapE, towerBindE]
        simp_rw [beforeHistory_extend D i ⟨m, hm⟩ him', towerEConst]
        exact ih (Nat.le_of_succ_le hm) him'

theorem refRunHistoryMass (i : Fin (D.geom.r + 1))
    (h : D.encoding.base.History i) :
    (D.encoding.kernels.refRun h.1).pr (D.agreesWithHistory h) =
      (D.encoding.base.runFrom D.encoding.kernels.referenceTransition h.1 i.val
        (Nat.le_of_lt_succ i.isLt)).w h := by
  have he := runFromBeforeExpectation D D.encoding.kernels.referenceTransition h.1 i
    (fun x => if x = h then 1 else 0) D.geom.r le_rfl (Nat.le_of_lt_succ i.isLt)
  change _ = _ at he
  have hleft : (D.encoding.kernels.refRun h.1).pr (D.agreesWithHistory h) =
      (D.encoding.base.runFrom D.encoding.kernels.referenceTransition h.1 D.geom.r le_rfl).E
        (fun full => if D.beforeHistory full i (Nat.le_of_lt_succ i.isLt) = h then 1 else 0) := by
    unfold FinLaw.pr FinLaw.E
    apply Finset.sum_congr rfl
    intro full hfull
    by_cases hx : D.beforeHistory full i (Nat.le_of_lt_succ i.isLt) = h <;>
      simp [S18.LateData.agreesWithHistory, LateKernels.refRun, LateProcessBase.runFull, hx]
  rw [hleft, he]
  simp [FinLaw.E]

theorem refRunExtendedHistoryMass (j : Fin D.geom.r)
    (h : D.encoding.base.History j.castSucc) (out : D.encoding.base.ClassRows j) :
    (D.encoding.kernels.refRun h.1).pr
        (D.agreesWithHistory (D.encoding.base.extend j h out)) =
      (D.encoding.kernels.refRun h.1).pr (D.agreesWithHistory h) *
        (D.encoding.kernels.referenceTransition j h).w out := by
  rw [refRunHistoryMass D j.castSucc h]
  have hm := refRunHistoryMass D j.succ (D.encoding.base.extend j h out)
  change (D.encoding.kernels.refRun h.1).pr
      (D.agreesWithHistory (D.encoding.base.extend j h out)) = _ at hm
  rw [hm]
  change (D.encoding.base.runFrom D.encoding.kernels.referenceTransition h.1 (j.val + 1)
    (Nat.succ_le_of_lt j.isLt)).w (D.encoding.base.extend j h out) = _
  rw [LateProcessBase.runFrom]
  unfold FinLaw.map
  have heq : ∀ x : D.encoding.base.History j.castSucc × D.encoding.base.ClassRows j,
      D.encoding.base.extend j x.1 x.2 = D.encoding.base.extend j h out ↔ x = (h, out) := by
    intro x
    constructor
    · intro hx
      exact (extend_injective D j) hx
    · intro hx
      rw [hx]
  simp_rw [heq]
  have hpoint : ∀ x,
      (if x = (h, out) then
        (FinLaw.bind (D.encoding.base.runFrom D.encoding.kernels.referenceTransition h.1 j.val
          (by omega)) (D.encoding.kernels.referenceTransition j)).w x else 0) =
      if x = (h, out) then
        (D.encoding.base.runFrom D.encoding.kernels.referenceTransition h.1 j.val (by omega)).w h *
          (D.encoding.kernels.referenceTransition j h).w out else 0 := by
    intro x
    by_cases hx : x = (h, out)
    · subst x
      rfl
    · simp [hx]
  have hsum : (∑ x : D.encoding.base.History j.castSucc × D.encoding.base.ClassRows j,
      if x = (h, out) then
        (D.encoding.base.runFrom D.encoding.kernels.referenceTransition h.1 j.val (by omega)).w h *
          (D.encoding.kernels.referenceTransition j h).w out else 0) =
      (D.encoding.base.runFrom D.encoding.kernels.referenceTransition h.1 j.val (by omega)).w h *
        (D.encoding.kernels.referenceTransition j h).w out := by
    rw [Finset.sum_eq_single (h, out)]
    · simp
    · intro x hx hne
      simp [hne]
    · intro hx
      exact False.elim (hx (Finset.mem_univ _))
  exact (Finset.sum_congr rfl (fun x _ => hpoint x)).trans hsum

theorem pastRows_beforeHistory (i : Fin D.geom.r) (j m : Fin (D.geom.r + 1))
    (hij : i.val < j.val) (hjm : j.val ≤ m.val) (h : D.encoding.base.History m) :
    D.pastRows (D.beforeHistory h j hjm) i hij = D.pastRows h i (hij.trans_le hjm) := by
  funext b
  rfl

theorem agreesWithHistory_extend_iff (j : Fin D.geom.r)
    (h : D.encoding.base.History j.castSucc) (out : D.encoding.base.ClassRows j)
    (full : D.encoding.base.History (Fin.last D.geom.r)) :
    D.agreesWithHistory (D.encoding.base.extend j h out) full ↔
      D.agreesWithHistory h full ∧ D.pastRows full j j.isLt = out := by
  constructor
  · intro he
    have hb := congrArg (fun g => D.beforeHistory g j.castSucc (by simp)) he
    have hp := congrArg (fun g => D.pastRows g j (by simp)) he
    change D.beforeHistory (D.beforeHistory full j.succ _) j.castSucc _ = _ at hb
    change D.pastRows (D.beforeHistory full j.succ _) j _ = _ at hp
    rw [beforeHistory_comp, beforeHistory_extend_self] at hb
    rw [pastRows_beforeHistory, pastRows_extend_self] at hp
    exact ⟨hb, hp⟩
  · rintro ⟨hb, hp⟩
    have he := extend_beforeHistory_pastRows D j (D.beforeHistory full j.succ (by simp))
    rw [beforeHistory_comp, pastRows_beforeHistory] at he
    rw [hb, hp] at he
    exact he.symm

private theorem refNumeratorPartition (j : Fin D.geom.r)
    (h : D.encoding.base.History j.castSucc)
    (A : D.encoding.base.History (Fin.last D.geom.r) → Prop) :
    (∑ out, (D.encoding.kernels.refRun h.1).pr (fun full =>
      D.agreesWithHistory (D.encoding.base.extend j h out) full ∧ A full)) =
      (D.encoding.kernels.refRun h.1).pr (fun full => D.agreesWithHistory h full ∧ A full) := by
  unfold FinLaw.pr
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro full hfull
  simp_rw [agreesWithHistory_extend_iff]
  by_cases hb : D.agreesWithHistory h full
  · by_cases ha : A full
    · simp only [hb, ha, true_and, and_true, ite_true]
      rw [Finset.sum_eq_single (D.pastRows full j j.isLt)]
      · simp
      · intro out hout hne
        simp [Ne.symm hne]
      · intro hnot
        exact False.elim (hnot (Finset.mem_univ _))
    · simp [ha]
  · simp [hb]

/-- The next class under the reference law conditioned on an entering history
is exactly its product transition, rather than an additional assumed law. -/
theorem referenceConditionalClassTest (j : Fin D.geom.r)
    (h : D.encoding.base.History j.castSucc)
    (hpos : 0 < (D.encoding.kernels.refRun h.1).pr (D.agreesWithHistory h))
    (A : D.encoding.base.ClassRows j → Prop) :
    (D.encoding.kernels.refRun h.1).pr (fun full =>
      D.agreesWithHistory h full ∧ A (D.pastRows full j j.isLt)) /
        (D.encoding.kernels.refRun h.1).pr (D.agreesWithHistory h) =
      (D.encoding.kernels.referenceTransition j h).pr A := by
  have hterm : ∀ out,
      (D.encoding.kernels.refRun h.1).pr (fun full =>
        D.agreesWithHistory (D.encoding.base.extend j h out) full ∧
          A (D.pastRows full j j.isLt)) =
      if A out then (D.encoding.kernels.refRun h.1).pr
        (D.agreesWithHistory (D.encoding.base.extend j h out)) else 0 := by
    intro out
    unfold FinLaw.pr
    by_cases ha : A out
    · simp only [ha, ite_true]
      apply Finset.sum_congr rfl
      intro full hfull
      by_cases hb : D.agreesWithHistory (D.encoding.base.extend j h out) full
      · have hp := (agreesWithHistory_extend_iff D j h out full).1 hb
        simp [hb, hp.2, ha]
      · simp [hb]
    · simp only [ha, ite_false]
      apply Finset.sum_eq_zero
      intro full hfull
      by_cases hb : D.agreesWithHistory (D.encoding.base.extend j h out) full
      · have hp := (agreesWithHistory_extend_iff D j h out full).1 hb
        simp [hb, hp.2, ha]
      · simp [hb]
  rw [← refNumeratorPartition D j h (fun full => A (D.pastRows full j j.isLt))]
  simp_rw [hterm, refRunExtendedHistoryMass D j h]
  have heq : (∑ out, if A out then
      (D.encoding.kernels.refRun h.1).pr (D.agreesWithHistory h) *
        (D.encoding.kernels.referenceTransition j h).w out else 0) =
      (D.encoding.kernels.refRun h.1).pr (D.agreesWithHistory h) *
        (D.encoding.kernels.referenceTransition j h).pr A := by
    unfold FinLaw.pr
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro out hout
    by_cases ha : A out <;> simp [ha]
  rw [heq]
  exact mul_div_cancel_left₀ _ (ne_of_gt hpos)

/-- Conditional risk is a martingale under the actual reference class transition,
including the zero convention for extensions outside reference support. -/
theorem futureRiskTower (j : Fin D.geom.r)
    (h : D.encoding.base.History j.castSucc)
    (hpos : 0 < (D.encoding.kernels.refRun h.1).pr (D.agreesWithHistory h))
    (f : S18.LateEvent D) :
    (D.encoding.kernels.referenceTransition j h).E
      (fun out => D.futureRisk f (D.encoding.base.extend j h out)) = D.futureRisk f h := by
  let P := D.encoding.kernels.refRun h.1
  let K := D.encoding.kernels.referenceTransition j h
  let d := P.pr (D.agreesWithHistory h)
  let n := fun out => P.pr (fun full =>
    D.agreesWithHistory (D.encoding.base.extend j h out) full ∧ S18.lateFailure D f full)
  have hn0 : ∀ out, 0 ≤ n out := fun out => towerPrNonneg P _
  have hnd : ∀ out, n out ≤ d * K.w out := by
    intro out
    have hm := towerPrMono P (A := fun full =>
      D.agreesWithHistory (D.encoding.base.extend j h out) full ∧ S18.lateFailure D f full)
      (B := D.agreesWithHistory (D.encoding.base.extend j h out)) (fun _ hx => hx.1)
    exact hm.trans_eq (refRunExtendedHistoryMass D j h out)
  have hd : d ≠ 0 := ne_of_gt hpos
  have hterm : ∀ out, K.w out * (n out / (d * K.w out)) = n out / d := by
    intro out
    by_cases hk : K.w out = 0
    · have hn : n out = 0 := by
        have hh := hnd out
        rw [hk, mul_zero] at hh
        exact le_antisymm hh (hn0 out)
      simp [hk, hn]
    · field_simp
  change (∑ out, K.w out * (n out / P.pr
    (D.agreesWithHistory (D.encoding.base.extend j h out)))) = _
  dsimp only [P]
  simp_rw [refRunExtendedHistoryMass D j h]
  change (∑ out, K.w out * (n out / (d * K.w out))) = _
  simp_rw [hterm]
  rw [← Finset.sum_div]
  change (∑ out, n out) / d = _
  rw [refNumeratorPartition]
  rfl

private theorem towerMarkov {Ω : Type*} [Fintype Ω] (P : FinLaw Ω)
    (f : Ω → ℝ) (hf : ∀ x, 0 ≤ f x) (t : ℝ) (ht : 0 < t) :
    P.pr (fun x => t < f x) ≤ P.E f / t := by
  apply (le_div_iff₀ ht).2
  unfold FinLaw.pr FinLaw.E
  rw [Finset.sum_mul]
  apply Finset.sum_le_sum
  intro x hx
  by_cases hf' : t < f x
  · simp only [hf', ite_true]
    exact mul_le_mul_of_nonneg_left hf'.le (P.nonneg x)
  · simp only [hf', ite_false, zero_mul]
    exact mul_nonneg (P.nonneg x) (hf x)

theorem futureAlarmProbabilityBound (δ : ℝ) (j : Fin D.geom.r)
    (h : D.encoding.base.History j.castSucc) (he : D.enter δ j h)
    (f : S18.LateEvent D) :
    (D.encoding.kernels.referenceTransition j h).pr (fun out =>
      j.val < f.2.1.val ∧ D.threshold δ (j.val + 1) <
        D.futureRisk f (D.encoding.base.extend j h out)) ≤
      Real.exp (-Real.rpow (T.S.n k : ℝ) δ / (2 * D.geom.r)) := by
  by_cases hf : j.val < f.2.1.val
  · simp only [hf, true_and]
    have hnonneg : ∀ out, 0 ≤ D.futureRisk f (D.encoding.base.extend j h out) := by
      intro out
      unfold S18.LateData.futureRisk
      exact div_nonneg (towerPrNonneg _ _) (towerPrNonneg _ _)
    have ht : 0 < D.threshold δ (j.val + 1) := Real.exp_pos _
    calc
      _ ≤ (D.encoding.kernels.referenceTransition j h).E
          (fun out => D.futureRisk f (D.encoding.base.extend j h out)) /
          D.threshold δ (j.val + 1) := towerMarkov _ _ hnonneg _ ht
      _ = D.futureRisk f h / D.threshold δ (j.val + 1) := by rw [futureRiskTower D j h he.1]
      _ ≤ D.threshold δ j.val / D.threshold δ (j.val + 1) :=
        div_le_div_of_nonneg_right (he.2.1 f hf.le) ht.le
      _ = _ := by
        unfold S18.LateData.threshold
        rw [← Real.exp_sub]
        congr 1
        push_cast
        ring
  · simp only [hf, false_and]
    simp [FinLaw.pr, (Real.exp_pos _).le]

end HypercubeRamsey.Lane_sol_s18_n4
