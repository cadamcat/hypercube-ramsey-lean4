import HypercubeRamsey.S03.Clock.Inputs

/-!
# The truncated backward exploration and its leaves (Lemma 3.10, Steps 2–3)

Source: `sections/03-…tex`, lines 857–905. The exploration of a test starts from its root endpoints, each
requesting its history through the full horizon `T * (|R| g)` (a bound on every event key, `eventPriority`). It
repeatedly processes the pending endpoint with the largest requested horizon (ties by the fixed
`Fintype.equivFin` rank), inspecting its incident edges in the fixed order of `incidentEdges`. An inspection of an
edge at horizon `h` asks whether the edge's first arrival has key `< h`; a hit at key `k` requests the other
endpoint through horizon `k` unless that endpoint is already processed (the largest request is retained). The
exploration stops with a *giant* failure as soon as the number of active endpoints (roots and endpoints reached
by a hit) reaches `L`; the endpoint of the last hit is registered first (03:870–874).

The leaf of a run records, per edge, the outcome of its inspection at the largest horizon at which it was
inspected: the exact arrival tick and mark for a hit, the absence condition "no arrival, or tick at least the
cutoff" otherwise (03:880–884). Its active set is the run's active set.

Horizons are event keys, not mesh ticks (see `Exploration.lean`): on the mesh several arrivals share a tick and
the fixed tie order decides between them.
-/

namespace HypercubeRamsey.Clock

open scoped BigOperators

/-! ### Tests as a finite type -/

/-- Tests correspond to `K ⊕ R`. -/
def samplingTestEquiv (R K : Type*) : SamplingTest R K ≃ K ⊕ R where
  toFun
    | .predicate k => .inl k
    | .singleton a => .inr a
  invFun
    | .inl k => .predicate k
    | .inr a => .singleton a
  left_inv t := by cases t <;> rfl
  right_inv x := by cases x <;> rfl

/-- The finitely many tests of an instance. -/
noncomputable instance instFintypeSamplingTest (R K : Type*) [Fintype R] [Fintype K] :
    Fintype (SamplingTest R K) :=
  Fintype.ofEquiv (K ⊕ R) (samplingTestEquiv R K).symm

/-! ### Edges, endpoints and keys -/

/-- The other endpoint of a row-label edge, seen from the endpoint `u` (meaningful when `u` is incident). -/
def edgeOther {R : Type*} {g : ℕ} (u : Endpoint R g) (e : RowLabel R g) : Endpoint R g :=
  match u with
  | .inl _ => .inr e.2
  | .inr _ => .inl e.1

/-- The edge `e` is incident to the endpoint `u`. -/
def EdgeIncident {R : Type*} {g : ℕ} (u : Endpoint R g) (e : RowLabel R g) : Prop :=
  u = Sum.inl e.1 ∨ u = Sum.inr e.2

/-- The incident edges of an endpoint in the fixed inspection order (TeX 03:863, "in a fixed order"): labels in
`Fin` order at a row, rows in `Fintype.equivFin` order at a label. -/
noncomputable def incidentEdges {R : Type*} [Fintype R] {g : ℕ} :
    Endpoint R g → List (RowLabel R g)
  | .inl a => List.ofFn fun y : Fin g => (a, y)
  | .inr y => List.ofFn fun i : Fin (Fintype.card R) => ((Fintype.equivFin R).symm i, y)

/-- The key (`eventPriority`) of the first arrival on an edge, if there is one. -/
noncomputable def edgeArrivalKey {T : ℕ} {R : Type*} [Fintype R] [DecidableEq R] {g : ℕ}
    {Ω : R → Type*} (ξ : ClockField T R g Ω) (e : RowLabel R g) : Option ℕ :=
  match ξ e with
  | .noArrival => none
  | .tick t o => some (eventPriority (⟨e.1, e.2, t, o⟩ : ClockCandidate T R g Ω))

/-- The root horizon `T * (|R| g)`: every event key is below it (the horizon of `rootBackwardPoint`). -/
def rootHorizon (T : ℕ) (R : Type*) [Fintype R] (g : ℕ) : ℕ := T * (Fintype.card R * g)

/-! ### The exploration algorithm -/

/-- State of a truncated exploration: the requested horizon of each active endpoint (`none` for inactive
endpoints), the processed endpoints, the largest horizon at which each edge has been inspected, and the giant
flag. -/
structure ExploreState (R : Type*) (g : ℕ) where
  request : Endpoint R g → Option ℕ
  processed : Finset (Endpoint R g)
  inspectedAt : RowLabel R g → Option ℕ
  giant : Bool

/-- The active endpoints: roots and endpoints reached by a hit (TeX 03:870–871). -/
noncomputable def ExploreState.active {R : Type*} [Fintype R] {g : ℕ} (s : ExploreState R g) :
    Finset (Endpoint R g) := by
  classical
  exact Finset.univ.filter fun u => (s.request u).isSome

/-- The initial state: every root requests the full horizon; giant at once if there are at least `L` roots. -/
noncomputable def initExploreState (T : ℕ) {R : Type*} [Fintype R] [DecidableEq R] {g : ℕ}
    (roots : Finset (Endpoint R g)) (L : ℕ) : ExploreState R g where
  request u := if u ∈ roots then some (rootHorizon T R g) else none
  processed := ∅
  inspectedAt _ := none
  giant := decide (L ≤ roots.card)

/-- Inspect the edge `e` from the endpoint `u` processed at horizon `h` (TeX 03:862–866). Nothing happens after a
giant stop. The inspection horizon of `e` is raised to `h`; a first arrival with key `k < h` is a hit, which
requests the other endpoint `w` through `k` unless `w` is already processed (the largest request is retained).
If the hit activates the `L`-th endpoint, the giant flag is set, with `w` registered (03:872–874). -/
noncomputable def inspectEdge {T : ℕ} {R : Type*} [Fintype R] [DecidableEq R] {g : ℕ} {Ω : R → Type*}
    (ξ : ClockField T R g Ω) (L : ℕ) (u : Endpoint R g) (h : ℕ)
    (s : ExploreState R g) (e : RowLabel R g) : ExploreState R g :=
  if s.giant then s else
    let s₁ : ExploreState R g :=
      { s with inspectedAt := Function.update s.inspectedAt e (some (max ((s.inspectedAt e).getD 0) h)) }
    match edgeArrivalKey ξ e with
    | none => s₁
    | some k =>
      if k < h then
        if edgeOther u e ∈ s.processed then s₁ else
          let s₂ : ExploreState R g :=
            { s₁ with
              request := Function.update s.request (edgeOther u e)
                (some (max ((s.request (edgeOther u e)).getD 0) k)) }
          if L ≤ s₂.active.card then { s₂ with giant := true } else s₂
      else s₁

/-- Process an endpoint: mark it processed, then inspect its incident edges in the fixed order at its requested
horizon. -/
noncomputable def processEndpoint {T : ℕ} {R : Type*} [Fintype R] [DecidableEq R] {g : ℕ}
    {Ω : R → Type*} (ξ : ClockField T R g Ω) (L : ℕ) (u : Endpoint R g)
    (s : ExploreState R g) : ExploreState R g :=
  (incidentEdges u).foldl (inspectEdge ξ L u ((s.request u).getD 0))
    { s with processed := insert u s.processed }

/-- Active endpoints that are not yet processed. -/
noncomputable def pendingEndpoints {R : Type*} [Fintype R] [DecidableEq R] {g : ℕ}
    (s : ExploreState R g) : Finset (Endpoint R g) := by
  classical
  exact Finset.univ.filter fun u => (s.request u).isSome ∧ u ∉ s.processed

/-- The selection key: requested horizon first, then the fixed `Fintype.equivFin` rank (injective). -/
noncomputable def pendingKey {R : Type*} [Fintype R] [DecidableEq R] {g : ℕ}
    (s : ExploreState R g) (u : Endpoint R g) : ℕ :=
  (s.request u).getD 0 * Fintype.card (Endpoint R g) + (Fintype.equivFin (Endpoint R g) u).val

/-- The pending endpoint with the largest requested horizon (TeX 03:862, "Process the pending endpoint with
largest horizon"), ties broken by the fixed rank. -/
noncomputable def nextPending {R : Type*} [Fintype R] [DecidableEq R] {g : ℕ}
    (s : ExploreState R g) : Option (Endpoint R g) :=
  if h : (pendingEndpoints s).Nonempty then
    some ((pendingEndpoints s).exists_max_image (pendingKey s) h).choose
  else none

/-- Run the exploration with a fuel bound: stop on a giant flag or when nothing is pending. -/
noncomputable def exploreRun {T : ℕ} {R : Type*} [Fintype R] [DecidableEq R] {g : ℕ}
    {Ω : R → Type*} (ξ : ClockField T R g Ω) (L : ℕ) : ℕ → ExploreState R g → ExploreState R g
  | 0, s => s
  | f + 1, s =>
    if s.giant then s else
      match nextPending s with
      | none => s
      | some u => exploreRun ξ L f (processEndpoint ξ L u s)

/-- The truncated exploration from a set of root endpoints, with giant cutoff `L`. Each round processes a new
endpoint, so the fuel `|Endpoint|` suffices. -/
noncomputable def truncatedExploration {T : ℕ} {R : Type*} [Fintype R] [DecidableEq R] {g : ℕ}
    {Ω : R → Type*} (ξ : ClockField T R g Ω) (roots : Finset (Endpoint R g)) (L : ℕ) :
    ExploreState R g :=
  exploreRun ξ L (Fintype.card (Endpoint R g)) (initExploreState T roots L)

/-- The truncated exploration of a test (roots: its scope rows). -/
noncomputable def testExploration {T : ℕ} {R K : Type*} [Fintype R] [DecidableEq R] {g : ℕ}
    {Ω : R → Type*} (ξ : ClockField T R g Ω) (scope : K → Finset R) (t : SamplingTest R K) (L : ℕ) :
    ExploreState R g :=
  truncatedExploration ξ (testRootEndpoints scope t) L

/-! ### Leaves -/

/-- The first tick at which an arrival on `e` has key at least `H`, capped at `T`: the edge has no arrival with
key `< H` exactly when it has no arrival or its arrival tick is at least this cutoff. -/
noncomputable def edgeCutoff (T : ℕ) {R : Type*} [Fintype R] [DecidableEq R] {g : ℕ}
    (H : ℕ) (e : RowLabel R g) : Fin (T + 1) :=
  ⟨min T ((H - ((Fintype.equivFin R e.1).val * g + e.2.val) + Fintype.card R * g - 1) /
      (Fintype.card R * g)), Nat.lt_succ_of_le (min_le_left _ _)⟩

/-- The leaf constraint of an edge in a run (TeX 03:880–884): unrestricted if never inspected; otherwise, at the
largest inspection horizon `H`, the exact arrival tick and mark for a hit, and absence before the cutoff of `H`
for a miss. -/
noncomputable def leafConstraint {T : ℕ} {R : Type*} [Fintype R] [DecidableEq R] {g : ℕ}
    {Ω : R → Type*} (ξ : ClockField T R g Ω) (s : ExploreState R g) (e : RowLabel R g) :
    EdgeConstraint T (Ω e.1) :=
  match s.inspectedAt e with
  | none => .unrestricted
  | some H =>
    match ξ e with
    | .noArrival => .absentBefore (edgeCutoff T H e)
    | .tick t o =>
      if eventPriority (⟨e.1, e.2, t, o⟩ : ClockCandidate T R g Ω) < H then .exactArrival t o
      else .absentBefore (edgeCutoff T H e)

/-- L3.10b-wf1 (03:880–884): every inspected edge has an active endpoint (it was inspected from a processed
endpoint). -/
theorem truncatedExploration_inspected_touches {T : ℕ} {R : Type*} [Fintype R] [DecidableEq R]
    {g : ℕ} {Ω : R → Type*} (ξ : ClockField T R g Ω) (roots : Finset (Endpoint R g)) (L : ℕ) :
    ∀ e, (leafConstraint ξ (truncatedExploration ξ roots L) e).inspected →
      Sum.inl e.1 ∈ (truncatedExploration ξ roots L).active ∨
        Sum.inr e.2 ∈ (truncatedExploration ξ roots L).active := by
  sorry

/-- L3.10b-wf2 (03:873–874, 03:880–881): every inspected hit has both endpoints active, also on a giant leaf (the
endpoint of the last hit is registered before stopping). -/
theorem truncatedExploration_hits_active {T : ℕ} {R : Type*} [Fintype R] [DecidableEq R]
    {g : ℕ} {Ω : R → Type*} (ξ : ClockField T R g Ω) (roots : Finset (Endpoint R g)) (L : ℕ) :
    ∀ e, (leafConstraint ξ (truncatedExploration ξ roots L) e).isHit →
      Sum.inl e.1 ∈ (truncatedExploration ξ roots L).active ∧
        Sum.inr e.2 ∈ (truncatedExploration ξ roots L).active := by
  sorry

/-- D3.10c (03:878–884): the leaf reached by the truncated exploration from `roots` on the clock field `ξ`. -/
noncomputable def explorationLeaf {T : ℕ} {R : Type*} [Fintype R] [DecidableEq R] {g : ℕ}
    {Ω : R → Type*} (ξ : ClockField T R g Ω) (roots : Finset (Endpoint R g)) (L : ℕ) :
    ClockLeaf T R g Ω where
  constraint := leafConstraint ξ (truncatedExploration ξ roots L)
  active := (truncatedExploration ξ roots L).active
  inspected_touches_active := truncatedExploration_inspected_touches ξ roots L
  hits_activate_both := truncatedExploration_hits_active ξ roots L

/-- The leaf of a test's exploration. -/
noncomputable def testLeaf {T : ℕ} {R K : Type*} [Fintype R] [DecidableEq R] {g : ℕ}
    {Ω : R → Type*} (ξ : ClockField T R g Ω) (scope : K → Finset R) (t : SamplingTest R K) (L : ℕ) :
    ClockLeaf T R g Ω :=
  explorationLeaf ξ (testRootEndpoints scope t) L

/-! ### The full backward closure from a root set -/

/-- Reachability from a set of root endpoints at the full horizon (`inBackwardClosure` for arbitrary roots). -/
def inClosureFrom {T : ℕ} {R : Type*} [Fintype R] [DecidableEq R] {g : ℕ} {Ω : R → Type*}
    (ξ : ClockField T R g Ω) (roots : Finset (Endpoint R g)) (u : BackwardPoint T R g) : Prop :=
  ∃ r ∈ roots, Relation.ReflTransGen (backwardStep ξ) (r, rootHorizon T R g) u

/-- The endpoints of the full (untruncated) backward closure from a set of roots. -/
noncomputable def closureFrom {T : ℕ} {R : Type*} [Fintype R] [DecidableEq R] {g : ℕ}
    {Ω : R → Type*} (ξ : ClockField T R g Ω) (roots : Finset (Endpoint R g)) :
    Finset (Endpoint R g) := by
  classical
  exact Finset.univ.filter fun u => ∃ h : ℕ, inClosureFrom ξ roots (u, h)

/-- The closure of a test is the closure from its root endpoints. -/
theorem activeEndpoints_eq_closureFrom {T : ℕ} {R K : Type*} [Fintype R] [DecidableEq R]
    [Fintype K] {g : ℕ} {Ω : R → Type*} (ξ : ClockField T R g Ω) (scope : K → Finset R)
    (t : SamplingTest R K) :
    activeEndpoints ξ scope t = closureFrom ξ (testRootEndpoints scope t) := by
  sorry

/-- `ξ'` has the same arrivals as `ξ` with key below `h` on every edge at `u`. -/
def agreesBelow {T : ℕ} {R : Type*} [Fintype R] [DecidableEq R] {g : ℕ} {Ω : R → Type*}
    (ξ ξ' : ClockField T R g Ω) (u : Endpoint R g) (h : ℕ) : Prop :=
  ∀ c : ClockCandidate T R g Ω, EdgeIncident u (c.1, c.2.1) → eventPriority c < h →
    (candidateIsArrival ξ c ↔ candidateIsArrival ξ' c)

/-- `ξ'` agrees with `ξ` below every horizon of the closure of `ξ` from `roots` (the data the backward closure
reads, TeX 03:866–867). -/
def agreesBelowClosure {T : ℕ} {R : Type*} [Fintype R] [DecidableEq R] {g : ℕ} {Ω : R → Type*}
    (roots : Finset (Endpoint R g)) (ξ ξ' : ClockField T R g Ω) : Prop :=
  ∀ u h, inClosureFrom ξ roots (u, h) → agreesBelow ξ ξ' u h

/-! ### Exploration properties (Step 2) -/

/-- L3.10b-sound (03:868–871): roots are active, processed endpoints are active, and every active endpoint lies in
the full backward closure. -/
theorem truncatedExploration_sound {T : ℕ} {R : Type*} [Fintype R] [DecidableEq R] {g : ℕ}
    {Ω : R → Type*} (ξ : ClockField T R g Ω) (roots : Finset (Endpoint R g)) (L : ℕ) :
    roots ⊆ (truncatedExploration ξ roots L).active ∧
      (truncatedExploration ξ roots L).processed ⊆ (truncatedExploration ξ roots L).active ∧
      (truncatedExploration ξ roots L).active ⊆ closureFrom ξ roots := by
  sorry

/-- L3.10b-complete (03:861–867): without a giant stop the exploration is the full closure, processed in
decreasing horizon order: every closure point `(u, h)` has `u` processed and every edge at `u` inspected at a
horizon at least `h`. -/
theorem truncatedExploration_complete {T : ℕ} {R : Type*} [Fintype R] [DecidableEq R] {g : ℕ}
    {Ω : R → Type*} (ξ : ClockField T R g Ω) (roots : Finset (Endpoint R g)) (L : ℕ)
    (hng : (truncatedExploration ξ roots L).giant = false) :
    ∀ u h, inClosureFrom ξ roots (u, h) → u ∈ (truncatedExploration ξ roots L).processed ∧
      ∀ e, EdgeIncident u e → ∃ H, (truncatedExploration ξ roots L).inspectedAt e = some H ∧ h ≤ H := by
  sorry

/-- L3.10b-card (03:872–874): a giant run has at least `L` active endpoints, a non-giant run fewer than `L`, and
with at most `L` roots never more than `L`. -/
theorem truncatedExploration_card {T : ℕ} {R : Type*} [Fintype R] [DecidableEq R] {g : ℕ}
    {Ω : R → Type*} (ξ : ClockField T R g Ω) (roots : Finset (Endpoint R g)) (L : ℕ) :
    ((truncatedExploration ξ roots L).giant = true → L ≤ (truncatedExploration ξ roots L).active.card) ∧
      ((truncatedExploration ξ roots L).giant = false →
        (truncatedExploration ξ roots L).active.card < L) ∧
      (roots.card ≤ L → (truncatedExploration ξ roots L).active.card ≤ L) := by
  sorry

/-- L3.10b-giant (03:872): the truncated run is giant exactly when the full closure has at least `L`
endpoints. Assembled from soundness, completeness and the count. -/
theorem truncatedExploration_giant_iff {T : ℕ} {R : Type*} [Fintype R] [DecidableEq R] {g : ℕ}
    {Ω : R → Type*} (ξ : ClockField T R g Ω) (roots : Finset (Endpoint R g)) (L : ℕ) :
    (truncatedExploration ξ roots L).giant = true ↔ L ≤ (closureFrom ξ roots).card := by
  obtain ⟨_, hproc, hcl⟩ := truncatedExploration_sound ξ roots L
  obtain ⟨hg, hng, _⟩ := truncatedExploration_card ξ roots L
  constructor
  · intro h
    exact le_trans (hg h) (Finset.card_le_card hcl)
  · intro h
    by_contra hb
    have hb' : (truncatedExploration ξ roots L).giant = false := by simpa using hb
    have hsub : closureFrom ξ roots ⊆ (truncatedExploration ξ roots L).active := by
      intro u hu
      classical
      have hu' : ∃ h : ℕ, inClosureFrom ξ roots (u, h) := by
        simpa [closureFrom] using hu
      obtain ⟨k, hk⟩ := hu'
      exact hproc ((truncatedExploration_complete ξ roots L hb' u k hk).1)
    have := lt_of_le_of_lt (Finset.card_le_card hsub) (hng hb')
    omega

/-- L3.10c-rect (03:878–884, "Every realization in this rectangle follows the same inspections and reaches the
same leaf"): a clock field lies in the leaf of `ξ` exactly when its own run equals the run of `ξ` and it reaches
the same leaf. -/
theorem explorationLeaf_event_iff {T : ℕ} {R : Type*} [Fintype R] [DecidableEq R] {g : ℕ}
    {Ω : R → Type*} (ξ ξ' : ClockField T R g Ω) (roots : Finset (Endpoint R g)) (L : ℕ) :
    (explorationLeaf ξ roots L).Event ξ' ↔
      truncatedExploration ξ' roots L = truncatedExploration ξ roots L ∧
        explorationLeaf ξ' roots L = explorationLeaf ξ roots L := by
  sorry

/-- L3.10b-agree (03:866–867): on a non-giant leaf every clock field of the leaf agrees with `ξ` below every
closure horizon (the run inspected every edge at each closure endpoint at its largest horizon). -/
theorem nongiant_leaf_agreesBelow {T : ℕ} {R : Type*} [Fintype R] [DecidableEq R] {g : ℕ}
    {Ω : R → Type*} (ξ ξ' : ClockField T R g Ω) (roots : Finset (Endpoint R g)) (L : ℕ)
    (hng : (truncatedExploration ξ roots L).giant = false)
    (hev : (explorationLeaf ξ roots L).Event ξ') :
    agreesBelowClosure roots ξ ξ' := by
  sorry

/-- L3.10b-closure (03:866–867, "These inspections determine the matching decisions at the roots by backward
closure through all earlier events they require"): agreement below the closure horizons determines the greedy
assignment of every root row. Strengthens `backwardClosure_determines_test` (agreement only below the horizons,
and the full assignment, including the matched label and output). -/
theorem closure_determines_root_assignment {T : ℕ} {R : Type*} [Fintype R] [DecidableEq R] {g : ℕ}
    {Ω : R → Type*} [∀ a, Fintype (Ω a)] [∀ a, DecidableEq (Ω a)]
    (ξ ξ' : ClockField T R g Ω) (roots : Finset (Endpoint R g))
    (h : agreesBelowClosure roots ξ ξ') :
    ∀ a, Sum.inl a ∈ roots → (greedyMatching ξ).assignment a = (greedyMatching ξ').assignment a := by
  sorry

/-- L3.10c-meet (03:1123–1124, "Their intersections are product rectangles"): the intersection of finitely many
leaves with a common point is the event of one leaf whose active set is the union of theirs. -/
theorem clockLeaf_meet {T : ℕ} {R : Type*} [DecidableEq R] {g : ℕ} {Ω : R → Type*}
    {ι : Type*} [Fintype ι] (τ : ι → ClockLeaf T R g Ω) (ξ₀ : ClockField T R g Ω)
    (h₀ : ∀ i, (τ i).Event ξ₀) :
    ∃ M : ClockLeaf T R g Ω, (∀ ξ, M.Event ξ ↔ ∀ i, (τ i).Event ξ) ∧
      M.active = Finset.univ.biUnion fun i => (τ i).active := by
  sorry

/-! ### Bad outcomes and bad leaves -/

/-- The bad outcome of a test in a matching (TeX 03:853–856): a predicate test fails when its scope is matched
with outputs violating the predicate (`testFails`); a singleton test fails unless its row is matched with an
output carrying the matched label. On the clock law every arrival mark carries its edge's label, so the second
clause differs from `testFails` only on a null event; it makes avoidance give distinct output labels pointwise. -/
def sampleTestBad {R K : Type*} [DecidableEq R] {g : ℕ} {Ω : R → Type*}
    (lab : ∀ a, Ω a → Fin g) (F : K → (∀ a, Ω a) → Prop) (scope : K → Finset R)
    (M : GreedyState R g Ω) : SamplingTest R K → Prop
  | .predicate k => testFails F scope M (.predicate k)
  | .singleton a => ¬ ∃ y o, M.assignment a = some (y, o) ∧ lab a o = y

/-- A leaf of a test is bad when the run is giant or the test has a bad outcome (TeX 03:878–879, 03:886). On a
non-giant leaf the outcome is a function of the leaf (`leafBad_leaf_invariant`). -/
def leafBad {T : ℕ} {R K : Type*} [Fintype R] [DecidableEq R] {g : ℕ} {Ω : R → Type*}
    [∀ a, Fintype (Ω a)] [∀ a, DecidableEq (Ω a)]
    (lab : ∀ a, Ω a → Fin g) (F : K → (∀ a, Ω a) → Prop) (scope : K → Finset R) (L : ℕ)
    (ξ : ClockField T R g Ω) (t : SamplingTest R K) : Prop :=
  (testExploration ξ scope t L).giant = true ∨ sampleTestBad lab F scope (greedyMatching ξ) t

/-- The closure form of a bad test: its full closure has at least `L` endpoints, or it has a bad outcome. A bad
leaf is closure-bad (`truncatedExploration_giant_iff`). -/
def closureBad {T : ℕ} {R K : Type*} [Fintype R] [DecidableEq R] [Fintype K] {g : ℕ}
    {Ω : R → Type*} [∀ a, Fintype (Ω a)] [∀ a, DecidableEq (Ω a)]
    (lab : ∀ a, Ω a → Fin g) (F : K → (∀ a, Ω a) → Prop) (scope : K → Finset R) (L : ℕ)
    (ξ : ClockField T R g Ω) (t : SamplingTest R K) : Prop :=
  L ≤ (activeEndpoints ξ scope t).card ∨ sampleTestBad lab F scope (greedyMatching ξ) t

/-- D3.10c-bad (03:886): the bad leaves of a test, i.e. the leaves of the clock fields with a bad leaf. -/
noncomputable def badLeaves {T : ℕ} {R K : Type*} [Fintype R] [DecidableEq R] {g : ℕ}
    {Ω : R → Type*} [∀ a, Fintype (Ω a)] [∀ a, DecidableEq (Ω a)]
    (lab : ∀ a, Ω a → Fin g) (F : K → (∀ a, Ω a) → Prop) (scope : K → Finset R) (L : ℕ)
    (t : SamplingTest R K) : Finset (ClockLeaf T R g Ω) := by
  classical
  exact (Finset.univ.filter fun ξ : ClockField T R g Ω => leafBad lab F scope L ξ t).image
    fun ξ => testLeaf ξ scope t L

/-- L3.10c-inv (03:884–886): badness is constant on a leaf: the giant flag is a function of the run, and on a
non-giant leaf the root assignments are determined (`nongiant_leaf_agreesBelow`,
`closure_determines_root_assignment`). -/
theorem leafBad_leaf_invariant {T : ℕ} {R K : Type*} [Fintype R] [DecidableEq R] {g : ℕ}
    {Ω : R → Type*} [∀ a, Fintype (Ω a)] [∀ a, DecidableEq (Ω a)]
    (lab : ∀ a, Ω a → Fin g) (F : K → (∀ a, Ω a) → Prop) (scope : K → Finset R) (L : ℕ)
    (ξ ξ' : ClockField T R g Ω) (t : SamplingTest R K) (h : (testLeaf ξ scope t L).Event ξ') :
    leafBad lab F scope L ξ' t ↔ leafBad lab F scope L ξ t := by
  sorry

/-- L3.10c-inc (03:897–902, first reduction): the bad leaves of a test containing an endpoint `v` are disjoint
events (`explorationLeaf_event_iff`) contained in the closure-bad event with `v` in the closure. -/
theorem badLeaves_incidence_le {T : ℕ} {R K : Type*} [Fintype R] [DecidableEq R] [Fintype K] {g : ℕ}
    {Ω : R → Type*} [∀ a, Fintype (Ω a)] [∀ a, DecidableEq (Ω a)]
    (edgeLaw : ∀ e : RowLabel R g, FinProb (MeshClockValue T (Ω e.1)))
    (lab : ∀ a, Ω a → Fin g) (F : K → (∀ a, Ω a) → Prop) (scope : K → Finset R) (L : ℕ)
    (t : SamplingTest R K) (v : Endpoint R g) :
    ∑ ℓ ∈ (badLeaves lab F scope L t).filter (fun ℓ => v ∈ ℓ.active),
        (clockFieldLaw edgeLaw).pr ℓ.Event ≤
      (clockFieldLaw edgeLaw).pr
        (fun ξ => closureBad lab F scope L ξ t ∧ v ∈ activeEndpoints ξ scope t) := by
  sorry

end HypercubeRamsey.Clock
