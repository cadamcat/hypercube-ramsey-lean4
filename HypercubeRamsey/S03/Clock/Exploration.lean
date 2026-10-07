import HypercubeRamsey.S03.Clock.Matching

/-!
# Backward exploration and the two test types

An exploration point stores an endpoint and the largest mesh horizon still requested there.  An arrival at
tick `t` sends a request to the opposite endpoint at horizon `t.val`; hence every transition strictly lowers
the horizon.  The finite reachability closure is the semantic version of processing pending requests in
decreasing-horizon order.
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

/-- Endpoint-time pairs. The horizon ranges from zero through all `T` mesh ticks. -/
abbrev BackwardPoint (T : ℕ) (R : Type*) (g : ℕ) := Endpoint R g × Fin (T + 1)

/-- The two endpoints of a row-label candidate. -/
def candidateEndpoints {T : ℕ} {R : Type*} {g : ℕ} {Ω : R → Type*}
    (e : ClockCandidate T R g Ω) : Endpoint R g × Endpoint R g :=
  (Sum.inl e.1, Sum.inr e.2.1)

/-- A single backward-exploration step across an arrival strictly earlier than the current horizon. -/
def backwardStep {T : ℕ} {R : Type*} {g : ℕ} {Ω : R → Type*}
    (ξ : ClockField T R g Ω) (u v : BackwardPoint T R g) : Prop :=
  ∃ e : ClockCandidate T R g Ω,
    candidateIsArrival ξ e ∧ e.2.2.1.val < u.2.val ∧ v.2.val = e.2.2.1.val ∧
      ((u.1 = Sum.inl e.1 ∧ v.1 = Sum.inr e.2.1) ∨
       (u.1 = Sum.inr e.2.1 ∧ v.1 = Sum.inl e.1))

/-- A row starts its exploration with the full mesh horizon. -/
def rootBackwardPoint {T : ℕ} {R : Type*} {g : ℕ} (a : R) : BackwardPoint T R g :=
  (Sum.inl a, Fin.last T)

/-- Reachability closure from the scope rows, including the roots themselves. -/
def inBackwardClosure {T : ℕ} {R K : Type*} [DecidableEq R] {g : ℕ} {Ω : R → Type*}
    (ξ : ClockField T R g Ω) (scope : K → Finset R) (t : SamplingTest R K)
    (u : BackwardPoint T R g) : Prop :=
  ∃ a ∈ testRoots scope t,
    Relation.ReflTransGen (backwardStep ξ) (rootBackwardPoint a) u

/-- The endpoints reached by the complete backward closure of a test. -/
noncomputable def activeEndpoints {T : ℕ} {R K : Type*} [Fintype R] [DecidableEq R]
    [Fintype K] {g : ℕ} [Fintype (Fin g)] {Ω : R → Type*}
    (ξ : ClockField T R g Ω) (scope : K → Finset R) (t : SamplingTest R K) : Finset (Endpoint R g) := by
  classical
  exact Finset.univ.filter fun e => ∃ h : Fin (T + 1), inBackwardClosure ξ scope t (e, h)

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
theorem root_mem_backwardClosure {T : ℕ} {R K : Type*} [DecidableEq R] {g : ℕ}
    {Ω : R → Type*} (ξ : ClockField T R g Ω) (scope : K → Finset R)
    (t : SamplingTest R K) (a : R) (ha : a ∈ testRoots scope t) :
    inBackwardClosure ξ scope t (rootBackwardPoint a) := by
  exact ⟨a, ha, Relation.ReflTransGen.refl⟩

/-- The backward exploration records enough clock data to determine its root test. -/
theorem backwardClosure_determines_test {T : ℕ} {R K : Type*} [Fintype R] [DecidableEq R]
    [Fintype K] {g : ℕ} [Fintype (Fin g)] {Ω : R → Type*}
    [∀ a, Fintype (Ω a)] [∀ a, DecidableEq (Ω a)]
    (F : K → (∀ a, Ω a) → Prop) (scope : K → Finset R)
    (ξ ξ' : ClockField T R g Ω) (t : SamplingTest R K)
    (h : agreesOnActiveEdges scope t ξ ξ') :
    testFails F scope (greedyMatching ξ) t ↔ testFails F scope (greedyMatching ξ') t := by
  sorry

end HypercubeRamsey.Clock
