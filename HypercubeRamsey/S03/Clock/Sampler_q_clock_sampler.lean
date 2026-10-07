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

end HypercubeRamsey.Lane_q_clock_sampler
