import HypercubeRamsey.S03.Clock.Model

/-!
# Fixed-order greedy clock matching

Every finite first arrival is represented once by a candidate.  The key orders candidates first by mesh tick,
then by the fixed `Fintype.equivFin` row order, then by label.  The matching is the left fold that accepts an
arrival exactly when both its row and label are still free.
-/

namespace HypercubeRamsey.Clock

open scoped BigOperators

/-- Candidate data for one possible first-arrival event. -/
abbrev ClockCandidate (T : ℕ) (R : Type*) (g : ℕ) (Ω : R → Type*) :=
  Σ a : R, Fin g × (Fin T × Ω a)

/-- Whether candidate data is the actual first arrival recorded by the clock field. -/
def candidateIsArrival {T : ℕ} {R : Type*} {g : ℕ} {Ω : R → Type*}
    (ξ : ClockField T R g Ω) (e : ClockCandidate T R g Ω) : Prop :=
  ξ (e.1, e.2.1) = .tick e.2.2.1 e.2.2.2

/-- The fixed integer key: time, then the row's `Fintype.equivFin` rank, then label. -/
noncomputable def eventPriority {T : ℕ} {R : Type*} [Fintype R] [DecidableEq R] {g : ℕ}
    {Ω : R → Type*} (e : ClockCandidate T R g Ω) : ℕ :=
  e.2.2.1.val * (Fintype.card R * g) +
    ((Fintype.equivFin R) e.1).val * g + e.2.1.val

/-- All realized arrivals in the fixed tie-breaking order. -/
noncomputable def clockEventList {T : ℕ} {R : Type*} [Fintype R] [DecidableEq R]
    {g : ℕ} {Ω : R → Type*} [∀ a, Fintype (Ω a)] [∀ a, DecidableEq (Ω a)]
    (ξ : ClockField T R g Ω) : List (ClockCandidate T R g Ω) := by
  classical
  exact ((Finset.univ : Finset (ClockCandidate T R g Ω)).filter (candidateIsArrival ξ)).toList.mergeSort
    (fun e f => decide (eventPriority e ≤ eventPriority f))

/-- The partial matching state; a real row stores its matched label and full output. -/
structure GreedyState (R : Type*) (g : ℕ) (Ω : R → Type*) where
  assignment : ∀ a, Option (Fin g × Ω a)

/-- Initially every row is unmatched. -/
def emptyGreedyState {R : Type*} {g : ℕ} {Ω : R → Type*} : GreedyState R g Ω :=
  ⟨fun _ => none⟩

/-- Whether a label is already occupied in a partial matching. -/
def labelUsed {R : Type*} {g : ℕ} {Ω : R → Type*}
    (s : GreedyState R g Ω) (y : Fin g) : Prop :=
  ∃ a o, s.assignment a = some (y, o)

/-- Process one arrival, accepting it precisely if both endpoints are free. -/
noncomputable def processArrival {T : ℕ} {R : Type*} [DecidableEq R] {g : ℕ}
    {Ω : R → Type*} [∀ a, DecidableEq (Ω a)]
    (ξ : ClockField T R g Ω) (s : GreedyState R g Ω)
    (e : ClockCandidate T R g Ω) : GreedyState R g Ω := by
  classical
  exact if candidateIsArrival ξ e ∧ s.assignment e.1 = none ∧ ¬ labelUsed s e.2.1 then
    ⟨fun a => if h : e.1 = a then some (e.2.1, h ▸ e.2.2.2) else s.assignment a⟩
  else s

/-- Run the greedy algorithm in the supplied event order. -/
noncomputable def runGreedy {T : ℕ} {R : Type*} [DecidableEq R] {g : ℕ}
    {Ω : R → Type*} [∀ a, DecidableEq (Ω a)]
    (ξ : ClockField T R g Ω) (events : List (ClockCandidate T R g Ω)) : GreedyState R g Ω :=
  events.foldl (fun s e => processArrival ξ s e) emptyGreedyState

/-- The matching produced by the fixed-order greedy algorithm. -/
noncomputable def greedyMatching {T : ℕ} {R : Type*} [Fintype R] [DecidableEq R]
    {g : ℕ} {Ω : R → Type*} [∀ a, Fintype (Ω a)] [∀ a, DecidableEq (Ω a)]
    (ξ : ClockField T R g Ω) : GreedyState R g Ω := by
  classical
  exact runGreedy ξ (clockEventList ξ)

/-- No label is assigned to two distinct rows by the greedy matching. -/
theorem greedyMatching_label_injective {T : ℕ} {R : Type*} [Fintype R] [DecidableEq R]
    {g : ℕ} {Ω : R → Type*} [∀ a, Fintype (Ω a)] [∀ a, DecidableEq (Ω a)]
    (ξ : ClockField T R g Ω) (a b : R) (y : Fin g) (oa : Ω a) (ob : Ω b)
    (ha : (greedyMatching ξ).assignment a = some (y, oa))
    (hb : (greedyMatching ξ).assignment b = some (y, ob)) : a = b := by
  sorry

/-- The fixed ordering processes all realized candidates in nondecreasing key order. -/
theorem clockEventList_sorted {T : ℕ} {R : Type*} [Fintype R] [DecidableEq R]
    {g : ℕ} {Ω : R → Type*} [∀ a, Fintype (Ω a)] [∀ a, DecidableEq (Ω a)]
    (ξ : ClockField T R g Ω) :
    (clockEventList ξ).Pairwise (fun e f => eventPriority e ≤ eventPriority f) := by
  sorry

end HypercubeRamsey.Clock
