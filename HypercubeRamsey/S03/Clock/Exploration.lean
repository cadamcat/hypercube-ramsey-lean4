import HypercubeRamsey.S03.Clock.Matching

/-!
# Backward exploration and the two test types

An exploration point stores an endpoint and the largest horizon still requested there. Horizons live in the
fixed event order used by the greedy matching (`eventPriority`: mesh tick, then row rank, then label), not in
mesh ticks alone: on the finite mesh several arrivals share a tick, and the greedy decision of an arrival
depends on the arrivals that precede it in the tie order at the same tick (TeX 03:863–864 "a time strictly
before `t`", discretized with the fixed tie order of 03:877–878). An arrival with key `κ` sends a request to
the opposite endpoint at horizon `κ`; hence every transition strictly lowers the horizon. The finite
reachability closure is the semantic version of processing pending requests in decreasing-horizon order.
-/

namespace HypercubeRamsey.Clock

/-- A graph endpoint is either a row or a label. -/
abbrev Endpoint (R : Type*) (g : ℕ) := Sum R (Fin g)

/-- The tests used by the clock sampler: a predicate test or a real-row singleton test. -/
inductive SamplingTest (R K : Type*) where
  | predicate (k : K)
  | singleton (a : R)
  deriving DecidableEq

/-- The roots of a predicate test are its scope rows; a singleton test has one root. -/
def testRoots {R K : Type*} [DecidableEq R]
    (scope : K → Finset R) : SamplingTest R K → Finset R
  | .predicate k => scope k
  | .singleton a => {a}

/-- A test's root endpoints in the row/label graph are rows. -/
def testRootEndpoints {R K : Type*} [DecidableEq R] {g : ℕ}
    (scope : K → Finset R) (t : SamplingTest R K) : Finset (Endpoint R g) :=
  (testRoots scope t).image Sum.inl

/-- Endpoint-horizon pairs. The horizon is a bound on the event key `eventPriority`: the endpoint's status is
requested just before the first event whose key is at least the horizon. Every key of a candidate is below
`T * (Fintype.card R * g)`, the root horizon. -/
abbrev BackwardPoint (_T : ℕ) (R : Type*) (g : ℕ) := Endpoint R g × ℕ

/-- The two endpoints of a row-label candidate. -/
def candidateEndpoints {T : ℕ} {R : Type*} {g : ℕ} {Ω : R → Type*}
    (e : ClockCandidate T R g Ω) : Endpoint R g × Endpoint R g :=
  (Sum.inl e.1, Sum.inr e.2.1)

/-- A single backward-exploration step across an arrival strictly earlier than the current horizon in the
fixed event order. -/
def backwardStep {T : ℕ} {R : Type*} [Fintype R] [DecidableEq R] {g : ℕ} {Ω : R → Type*}
    (ξ : ClockField T R g Ω) (u v : BackwardPoint T R g) : Prop :=
  ∃ e : ClockCandidate T R g Ω,
    candidateIsArrival ξ e ∧ eventPriority e < u.2 ∧ v.2 = eventPriority e ∧
      ((u.1 = Sum.inl e.1 ∧ v.1 = Sum.inr e.2.1) ∨
       (u.1 = Sum.inr e.2.1 ∧ v.1 = Sum.inl e.1))

/-- A row starts its exploration with the full horizon, above every event key. -/
def rootBackwardPoint {T : ℕ} {R : Type*} [Fintype R] {g : ℕ} (a : R) : BackwardPoint T R g :=
  (Sum.inl a, T * (Fintype.card R * g))

/-- Reachability closure from the scope rows, including the roots themselves. -/
def inBackwardClosure {T : ℕ} {R K : Type*} [Fintype R] [DecidableEq R] {g : ℕ} {Ω : R → Type*}
    (ξ : ClockField T R g Ω) (scope : K → Finset R) (t : SamplingTest R K)
    (u : BackwardPoint T R g) : Prop :=
  ∃ a ∈ testRoots scope t,
    Relation.ReflTransGen (backwardStep ξ) (rootBackwardPoint (T := T) a) u

/-- The endpoints reached by the complete backward closure of a test. -/
noncomputable def activeEndpoints {T : ℕ} {R K : Type*} [Fintype R] [DecidableEq R]
    [Fintype K] {g : ℕ} [Fintype (Fin g)] {Ω : R → Type*}
    (ξ : ClockField T R g Ω) (scope : K → Finset R) (t : SamplingTest R K) : Finset (Endpoint R g) := by
  classical
  exact Finset.univ.filter fun e => ∃ h : ℕ, inBackwardClosure ξ scope t (e, h)

/-- The active-endpoint cutoff used to declare a giant exploration. -/
def explorationIsNongiant {T : ℕ} {R K : Type*} [Fintype R] [DecidableEq R]
    [Fintype K] {g : ℕ} [Fintype (Fin g)] {Ω : R → Type*}
    (ξ : ClockField T R g Ω) (scope : K → Finset R) (t : SamplingTest R K) (L : ℕ) : Prop :=
  (activeEndpoints ξ scope t).card < L

/-- A predicate test fails exactly when the scope is matched with outputs violating the predicate. -/
def testFails {R K : Type*} [DecidableEq R] {g : ℕ} {Ω : R → Type*}
    (F : K → (∀ a, Ω a) → Prop) (scope : K → Finset R)
    (M : GreedyState R g Ω) : SamplingTest R K → Prop
  | .predicate k => ∃ ω : ∀ a, Ω a, F k ω ∧
      ∀ a ∈ scope k, ∃ y : Fin g, M.assignment a = some (y, ω a)
  | .singleton a => M.assignment a = none

/-- Agreement on every edge incident to an endpoint in a backward closure. -/
def agreesOnActiveEdges {T : ℕ} {R K : Type*} [Fintype R] [DecidableEq R]
    [Fintype K] {g : ℕ} [Fintype (Fin g)] {Ω : R → Type*}
    (scope : K → Finset R) (t : SamplingTest R K)
    (ξ ξ' : ClockField T R g Ω) : Prop :=
  ∀ e : RowLabel R g,
    (Sum.inl e.1 ∈ activeEndpoints ξ scope t ∨ Sum.inr e.2 ∈ activeEndpoints ξ scope t) →
      ξ e = ξ' e

/-- Backward closure contains every root row at full horizon. -/
theorem root_mem_backwardClosure {T : ℕ} {R K : Type*} [Fintype R] [DecidableEq R] {g : ℕ}
    {Ω : R → Type*} (ξ : ClockField T R g Ω) (scope : K → Finset R)
    (t : SamplingTest R K) (a : R) (ha : a ∈ testRoots scope t) :
    inBackwardClosure ξ scope t (rootBackwardPoint (T := T) a) := by
  exact ⟨a, ha, Relation.ReflTransGen.refl⟩

/-- The backward exploration records enough clock data to determine its root test (TeX 03:866–867: the
inspections determine the root decisions by backward closure). -/
theorem backwardClosure_determines_test {T : ℕ} {R K : Type*} [Fintype R] [DecidableEq R]
    [Fintype K] {g : ℕ} [Fintype (Fin g)] {Ω : R → Type*}
    [∀ a, Fintype (Ω a)] [∀ a, DecidableEq (Ω a)]
    (F : K → (∀ a, Ω a) → Prop) (scope : K → Finset R)
    (ξ ξ' : ClockField T R g Ω) (t : SamplingTest R K)
    (h : agreesOnActiveEdges scope t ξ ξ') :
    testFails F scope (greedyMatching ξ) t ↔ testFails F scope (greedyMatching ξ') t := by
  sorry

end HypercubeRamsey.Clock
