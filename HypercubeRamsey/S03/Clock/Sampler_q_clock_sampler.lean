import HypercubeRamsey.S03.Clock.Branching

namespace HypercubeRamsey.Clock

/-- Every output produced by the greedy matching comes from the arrival on its assigned edge. -/
theorem greedyMatching_assignment_origin {T : ℕ} {R : Type*} [Fintype R] [DecidableEq R]
    {g : ℕ} {Ω : R → Type*} [∀ a, Fintype (Ω a)] [∀ a, DecidableEq (Ω a)]
    (ξ : ClockField T R g Ω) (a : R) (y : Fin g) (o : Ω a)
    (ha : (greedyMatching ξ).assignment a = some (y, o)) :
    ∃ t, ξ (a, y) = MeshClockValue.tick t o := by
  classical
  let Origin : GreedyState R g Ω → Prop := fun s =>
    ∀ a y o, s.assignment a = some (y, o) → ∃ t, ξ (a, y) = MeshClockValue.tick t o
  have hstep (s : GreedyState R g Ω) (hs : Origin s) (e : ClockCandidate T R g Ω) :
      Origin (processArrival ξ s e) := by
    dsimp [Origin] at hs ⊢
    by_cases hacc : candidateIsArrival ξ e ∧ s.assignment e.1 = none ∧ ¬ labelUsed s e.2.1
    · simp only [processArrival, if_pos hacc]
      intro a y o h
      by_cases ha : e.1 = a
      · subst a
        simp only [dif_pos rfl] at h
        have hy : e.2.1 = y := congrArg Prod.fst (Option.some.inj h)
        have ho : e.2.2.2 = o := congrArg Prod.snd (Option.some.inj h)
        refine ⟨e.2.2.1, ?_⟩
        have harr := hacc.1
        change ξ (e.1, e.2.1) = MeshClockValue.tick e.2.2.1 e.2.2.2 at harr
        rw [hy, ho] at harr
        exact harr
      · simp only [dif_neg ha] at h
        exact hs a y o h
    · simpa [processArrival, hacc] using hs
  have hfold : ∀ (events : List (ClockCandidate T R g Ω))
      (s : GreedyState R g Ω), Origin s →
      Origin (events.foldl (fun s e => processArrival ξ s e) s) := by
    intro events
    induction events with
    | nil =>
        intro s hs
        exact hs
    | cons e events ih =>
        intro s hs
        simpa only [List.foldl_cons] using ih (processArrival ξ s e) (hstep s hs e)
  have hmatch : Origin (greedyMatching ξ) := by
    change Origin (runGreedy ξ (clockEventList ξ))
    exact hfold (clockEventList ξ) emptyGreedyState (by
      intro a y o h
      simp [emptyGreedyState] at h)
  exact hmatch a y o ha

end HypercubeRamsey.Clock

namespace HypercubeRamsey.Lane_q_clock_sampler

open Filter

theorem exp_sub_one_le_mul_exp (x : ℝ) (hx : 0 ≤ x) :
    Real.exp x - 1 ≤ x * Real.exp x := by
  have hneg := Real.add_one_le_exp (-x)
  have hsmall : 1 - Real.exp (-x) ≤ x := by linarith
  have hprod : Real.exp x * Real.exp (-x) = 1 := by
    rw [← Real.exp_add]
    simp
  have heq : Real.exp x - 1 = Real.exp x * (1 - Real.exp (-x)) := by
    calc
      Real.exp x - 1 = Real.exp x - Real.exp x * Real.exp (-x) := by rw [hprod]
      _ = Real.exp x * (1 - Real.exp (-x)) := by ring
  calc
    Real.exp x - 1 = Real.exp x * (1 - Real.exp (-x)) := heq
    _ ≤ Real.exp x * x := mul_le_mul_of_nonneg_left hsmall (Real.exp_nonneg _)
    _ = x * Real.exp x := by ring

theorem rpow_neg_tendsto_zero (p : ℝ) (hp : 0 < p) :
    Tendsto (fun n : ℕ => (n : ℝ) ^ (-p)) atTop (nhds 0) := by
  exact (tendsto_rpow_neg_atTop hp).comp tendsto_natCast_atTop_atTop

theorem rpow_tendsto_top (p : ℝ) (hp : 0 < p) :
    Tendsto (fun n : ℕ => (n : ℝ) ^ p) atTop atTop :=
  (tendsto_rpow_atTop hp).comp tendsto_natCast_atTop_atTop

theorem pi_pr_depends_eq_subtype {ι : Type*} [Fintype ι] [DecidableEq ι]
    {Ω : ι → Type*} [∀ i, Fintype (Ω i)]
    (P : ∀ i, FinProb (Ω i)) (s : Finset ι) (F : (∀ i, Ω i) → Prop)
    (hF : FinProb.DependsOn F s) (base : ∀ i, Ω i) :
    (FinProb.pi (fun i : {i // i ∈ s} => P i.1)).pr
        (fun a => F ((Equiv.piEquivPiSubtypeProd (fun i => i ∈ s) Ω).symm
          (a, fun i => base i.1))) = (FinProb.pi P).pr F := by
  classical
  let indicator : (∀ i, Ω i) → ℝ := fun ω => if F ω then 1 else 0
  have hdep : FinProb.DependsOn indicator s := by
    intro ω ω' hagree
    simp only [indicator]
    rw [hF ω ω' hagree]
  have hexpect := FinProb.pi_expect_depends P s indicator base hdep
  have hprob : (FinProb.pi P).pr F =
      (FinProb.pi (fun i : {i // i ∈ s} => P i.1)).pr
        (fun a => F ((Equiv.piEquivPiSubtypeProd (fun i => i ∈ s) Ω).symm
          (a, fun i => base i.1))) := by
    simpa [FinProb.pr, FinProb.expect, indicator] using hexpect
  exact hprob.symm

theorem finProb_pr_congr {α : Type*} [Fintype α] (P : FinProb α)
    {A B : α → Prop} (hAB : ∀ x, A x ↔ B x) : P.pr A = P.pr B := by
  classical
  unfold FinProb.pr
  apply Finset.sum_congr rfl
  intro x hx
  by_cases hA : A x
  · have hB := (hAB x).mp hA
    simp [hA, hB]
  · have hB : ¬ B x := by
      intro h
      exact hA ((hAB x).mpr h)
    simp [hA, hB]

def pinCoordinate {ι : Type*} [DecidableEq ι] {Ω : ι → Type*}
    (i : ι) (o : Ω i) (x : ∀ j, Ω j) : ∀ j, Ω j :=
  fun j => if h : j = i then cast (congrArg Ω h.symm) o else x j

def pinCoordinateRest {ι : Type*} [DecidableEq ι] {Ω : ι → Type*}
    (i : ι) (o : Ω i) (y : ∀ j : {j // j ≠ i}, Ω j.1) : ∀ j, Ω j :=
  fun j => if h : j = i then cast (congrArg Ω h.symm) o else y ⟨j, h⟩

theorem pi_pr_pinned_eq_rest {ι : Type*} [Fintype ι] [DecidableEq ι]
    {Ω : ι → Type*} [∀ i, Fintype (Ω i)] [∀ i, DecidableEq (Ω i)]
    (P : ∀ i, FinProb (Ω i)) (F : (∀ i, Ω i) → Prop) (i : ι) (o : Ω i)
    (hpos : 0 < (P i).w o) :
    (FinProb.pi P).pr (fun x => F x ∧ x i = o) / (P i).w o =
      (FinProb.pi (fun j : {j // j ≠ i} => P j.1)).pr
        (fun y => F (pinCoordinateRest i o y)) := by
  classical
  let C : ∀ j, Ω j → Prop := fun j x => if h : j = i then x = cast (congrArg Ω h.symm) o else True
  let E : (∀ j, Ω j) → Prop := fun x => ∀ j, C j (x j)
  let Pcond : ∀ j, FinProb (Ω j) := fun j => (P j).cond (C j) (by
    by_cases hji : j = i
    · subst j
      simpa [C, HypercubeRamsey.FinProb.pr_singleton] using hpos
    · have htrue : (P j).pr (fun _ => True) = 1 := by
        unfold FinProb.pr
        simp [(P j).sum_eq_one]
      rw [show C j = (fun _ => True) by funext x; simp [C, hji], htrue]
      norm_num)
  let Fpin : (∀ j, Ω j) → Prop := fun x => F (pinCoordinate i o x)
  let split : (∀ j, Ω j) ≃ Ω i × (∀ j : {j // j ≠ i}, Ω j.1) := Equiv.piSplitAt i Ω
  have hE : ∀ x, E x ↔ x i = o := by
    intro x
    constructor
    · intro hx
      simpa [E, C] using hx i
    · intro hx j
      by_cases hji : j = i
      · subst j
        simpa [C] using hx
      · simp [C, hji]
  have hcoord : ∀ j, 0 < (P j).pr (C j) := by
    intro j
    by_cases hji : j = i
    · subst j
      simpa [C, HypercubeRamsey.FinProb.pr_singleton] using hpos
    · have htrue : (P j).pr (fun _ => True) = 1 := by
        unfold FinProb.pr
        simp [(P j).sum_eq_one]
      rw [show C j = (fun _ => True) by funext x; simp [C, hji], htrue]
      norm_num
  have hEprob : 0 < (FinProb.pi P).pr E := by
    have hfactor : (FinProb.pi P).pr E = ∏ j, (P j).pr (C j) := by
      simpa [E] using (HypercubeRamsey.FinProb.pi_pr_forall P C)
    rw [hfactor]
    exact Finset.prod_pos fun j hj => hcoord j
  have hcoordprob : (FinProb.pi P).pr E = (P i).w o := by
    rw [finProb_pr_congr (FinProb.pi P) hE]
    exact HypercubeRamsey.Clock.pi_pr_coordinate P i o
  have hcond := HypercubeRamsey.FinProb.pi_cond_forall P C hcoord hEprob
  have hFpinDep : FinProb.DependsOn Fpin (Finset.univ.erase i) := by
    intro x y hxy
    apply congrArg F
    funext j
    by_cases hji : j = i
    · subst j
      simp [pinCoordinate]
    · have hj : j ∈ Finset.univ.erase i := Finset.mem_erase.mpr ⟨hji, Finset.mem_univ _⟩
      simp [pinCoordinate, hji, hxy j hj]
  have hcondF : (FinProb.pi Pcond).pr F = (FinProb.pi Pcond).pr Fpin := by
    unfold FinProb.pr FinProb.pi
    apply Finset.sum_congr rfl
    intro x hx
    by_cases hxi : x i = o
    · have hpin : pinCoordinate i o x = x := by
        funext j
        by_cases hji : j = i
        · subst j
          simpa [pinCoordinate] using hxi.symm
        · simp [pinCoordinate, hji]
      simp [Fpin, hpin]
    · have hzero : (Pcond i).w (x i) = 0 := by
        simp [Pcond, C, FinProb.cond, hxi]
      have hprod : ∏ j, (Pcond j).w (x j) = 0 :=
        Finset.prod_eq_zero (Finset.mem_univ i) hzero
      simp [Fpin, FinProb.pr, hprod]
  have hpinSplit (a : Ω i) (b : ∀ j : {j // j ≠ i}, Ω j.1) :
      pinCoordinate i o (split.symm (a, b)) = pinCoordinateRest i o b := by
    funext j
    by_cases hji : j = i
    · subst j
      simp [pinCoordinate, pinCoordinateRest, split]
    · simp [pinCoordinate, pinCoordinateRest, split, hji]
  have hrestProd (f : ι → ℝ) :
      (∏ j : {j // j ≠ i}, f j.1) = ∏ j ∈ Finset.univ.erase i, f j := by
    let e : {j // j ≠ i} ≃ {j // j ∈ Finset.univ.erase i} := {
      toFun := fun j => ⟨j.1, Finset.mem_erase.mpr ⟨j.2, Finset.mem_univ _⟩⟩
      invFun := fun j => ⟨j.1, (Finset.mem_erase.mp j.2).1⟩
      left_inv := by intro j; rfl
      right_inv := by intro j; rfl }
    calc
      _ = ∏ j : {j // j ∈ Finset.univ.erase i}, f j.1 := by
        exact Fintype.prod_equiv e (fun j => f j.1) (fun j => f j.1) (by intro j; rfl)
      _ = ∏ j ∈ Finset.univ.erase i, f j := by rw [Finset.prod_coe_sort]
  have hweightSplit (a : Ω i) (b : ∀ j : {j // j ≠ i}, Ω j.1) :
      (∏ j, (Pcond j).w (split.symm (a, b) j)) =
        (Pcond i).w a * ∏ j : {j // j ≠ i}, (Pcond j.1).w (b j) := by
    let f : ι → ℝ := fun j => (Pcond j).w (split.symm (a, b) j)
    have hfull : (∏ j, f j) = f i * ∏ j ∈ Finset.univ.erase i, f j := by
      calc
        _ = ∏ j ∈ Finset.univ, f j := by simp
        _ = f i * ∏ j ∈ Finset.univ.erase i, f j :=
          (Finset.mul_prod_erase Finset.univ f (Finset.mem_univ i)).symm
    calc
      _ = f i * ∏ j : {j // j ≠ i}, f j.1 := by
        calc
          _ = f i * ∏ j ∈ Finset.univ.erase i, f j := hfull
          _ = f i * ∏ j : {j // j ≠ i}, f j.1 := by rw [hrestProd]
      _ = (Pcond i).w a * ∏ j : {j // j ≠ i}, (Pcond j.1).w (b j) := by
        have hfi : f i = (Pcond i).w a := by
          simp [f, split, Equiv.piSplitAt]
        have hfr : ∏ j : {j // j ≠ i}, f j.1 =
            ∏ j : {j // j ≠ i}, (Pcond j.1).w (b j) := by
          apply Finset.prod_congr rfl
          intro j hj
          simp [f, split, Equiv.piSplitAt, j.2]
        rw [hfi, hfr]
  have hrestSplit : (FinProb.pi Pcond).pr Fpin =
      (FinProb.pi (fun j : {j // j ≠ i} => Pcond j.1)).pr
        (fun b => F (pinCoordinateRest i o b)) := by
    unfold FinProb.pr FinProb.pi
    calc
      _ = ∑ z : Ω i × (∀ j : {j // j ≠ i}, Ω j.1),
          if Fpin (split.symm z) then
            ∏ j, (Pcond j).w (split.symm z j) else 0 := by
              exact Fintype.sum_equiv split _ _ (by intro z; simp)
      _ = ∑ a : Ω i, ∑ b : ∀ j : {j // j ≠ i}, Ω j.1,
          if F (pinCoordinateRest i o b) then
            (Pcond i).w a * ∏ j : {j // j ≠ i}, (Pcond j.1).w (b j) else 0 := by
              rw [Fintype.sum_prod_type]
              apply Finset.sum_congr rfl
              intro a ha
              apply Finset.sum_congr rfl
              intro b hb
              simp only [Fpin]
              simp only [hpinSplit a b, hweightSplit a b]
      _ = ∑ b : ∀ j : {j // j ≠ i}, Ω j.1,
          if F (pinCoordinateRest i o b) then
            ∏ j : {j // j ≠ i}, (Pcond j.1).w (b j) else 0 := by
              rw [Finset.sum_comm]
              apply Finset.sum_congr rfl
              intro b hb
              by_cases hFb : F (pinCoordinateRest i o b)
              · simp [hFb]
                rw [← Finset.sum_mul, (Pcond i).sum_eq_one]
                ring
              · simp [hFb]
      _ = (FinProb.pi (fun j : {j // j ≠ i} => Pcond j.1)).pr
          (fun b => F (pinCoordinateRest i o b)) := by rfl
  have hPcondRest (j : {j // j ≠ i}) : Pcond j.1 = P j.1 := by
    apply FinProb.ext
    intro x
    have htrue : (P j.1).pr (fun _ => True) = 1 := by
      unfold FinProb.pr
      simp [(P j.1).sum_eq_one]
    simp [Pcond, C, FinProb.cond, j.2, htrue]
  have hrestLaw :
      FinProb.pi (fun j : {j // j ≠ i} => Pcond j.1) =
        FinProb.pi (fun j : {j // j ≠ i} => P j.1) := by
    apply FinProb.ext
    intro y
    change (∏ j : {j // j ≠ i}, (Pcond j.1).w (y j)) =
      ∏ j : {j // j ≠ i}, (P j.1).w (y j)
    apply Finset.prod_congr rfl
    intro j hj
    exact congrArg (fun Q : FinProb (Ω j.1) => Q.w (y j)) (hPcondRest j)
  have hcondPr : ((FinProb.pi P).cond E hEprob).pr F =
      (FinProb.pi P).pr (fun x => E x ∧ F x) / (FinProb.pi P).pr E :=
    HypercubeRamsey.FinProb.cond_pr (FinProb.pi P) E F hEprob
  have hjoint : (FinProb.pi P).pr (fun x => E x ∧ F x) =
      (FinProb.pi P).pr (fun x => F x ∧ x i = o) := by
    apply finProb_pr_congr
    intro x
    simp [hE x, and_comm]
  have hcondPr' : ((FinProb.pi P).cond E hEprob).pr F =
      (FinProb.pi P).pr (fun x => F x ∧ x i = o) / (P i).w o := by
    rw [hcondPr, hjoint, hcoordprob]
  calc
    (FinProb.pi P).pr (fun x => F x ∧ x i = o) / (P i).w o =
        ((FinProb.pi P).cond E hEprob).pr F := hcondPr'.symm
    _ = (FinProb.pi Pcond).pr F := by rw [hcond]
    _ = (FinProb.pi Pcond).pr Fpin := hcondF
    _ = (FinProb.pi (fun j : {j // j ≠ i} => Pcond j.1)).pr
        (fun b => F (pinCoordinateRest i o b)) := hrestSplit
    _ = (FinProb.pi (fun j : {j // j ≠ i} => P j.1)).pr
        (fun b => F (pinCoordinateRest i o b)) := by rw [hrestLaw]
end HypercubeRamsey.Lane_q_clock_sampler
