import HypercubeRamsey.S03.Clock.Inputs
import HypercubeRamsey.S03.Clock.Truncated_q_clock_trunc

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
  classical
  have hactiveInspect (u : Endpoint R g) (h : ℕ) (s : ExploreState R g) (e : RowLabel R g) :
      s.active ⊆ (inspectEdge ξ L u h s e).active := by
    intro v hv
    have hv' : (s.request v).isSome := by simpa [ExploreState.active] using hv
    have hout : ((inspectEdge ξ L u h s e).request v).isSome := by
      by_cases hg : s.giant
      · simpa [inspectEdge, hg] using hv'
      · cases hk : edgeArrivalKey ξ e with
        | none => simpa [inspectEdge, hg, hk] using hv'
        | some k =>
            by_cases hkh : k < h
            · by_cases hproc : edgeOther u e ∈ s.processed
              · simpa [inspectEdge, hg, hk, hkh, hproc] using hv'
              · by_cases hw : edgeOther u e = v
                · subst v
                  simp [inspectEdge, hg, hk, hkh, hproc] <;> split_ifs <;> simp [Function.update]
                · simp only [inspectEdge, if_neg hg, hk, if_pos hkh, if_neg hproc]
                  have hvw : v ≠ edgeOther u e := by
                    intro hvw
                    exact hw hvw.symm
                  split_ifs <;> simpa [Function.update_of_ne hvw] using hv'
            · simpa [inspectEdge, hg, hk, hkh] using hv'
    simpa [ExploreState.active] using hout
  have hactiveFold : ∀ (u : Endpoint R g) (h : ℕ) (es : List (RowLabel R g))
      (s : ExploreState R g),
      s.active ⊆ (es.foldl (inspectEdge ξ L u h) s).active := by
    intro u h es
    induction es with
    | nil =>
        intro s
        exact Finset.Subset.rfl
    | cons e es ih =>
        intro s
        rw [List.foldl_cons]
        exact Finset.Subset.trans (hactiveInspect u h s e) (ih (inspectEdge ξ L u h s e))
  have hactiveProcess (u : Endpoint R g) (s : ExploreState R g) :
      s.active ⊆ (processEndpoint ξ L u s).active := by
    unfold processEndpoint
    exact hactiveFold u ((s.request u).getD 0) (incidentEdges u)
      { s with processed := insert u s.processed }
  have hinspect (u : Endpoint R g) (h : ℕ) (s : ExploreState R g)
      (e x : RowLabel R g) :
      ((inspectEdge ξ L u h s e).inspectedAt x).isSome →
        (s.inspectedAt x).isSome ∨ x = e := by
    intro hx
    by_cases hxe : x = e
    · exact Or.inr hxe
    · left
      by_cases hg : s.giant
      · simpa [inspectEdge, hg] using hx
      · cases hk : edgeArrivalKey ξ e with
        | none =>
            simpa [inspectEdge, hg, hk, Function.update_of_ne hxe] using hx
        | some k =>
            by_cases hkh : k < h
            · by_cases hproc : edgeOther u e ∈ s.processed
              · simpa [inspectEdge, hg, hk, hkh, hproc,
                  Function.update_of_ne hxe] using hx
              · simp only [inspectEdge, if_neg hg, hk, if_pos hkh, if_neg hproc] at hx
                split_ifs at hx <;>
                  simpa [Function.update_of_ne hxe] using hx
            · simpa [inspectEdge, hg, hk, hkh, Function.update_of_ne hxe] using hx
  have hprovFold : ∀ (u : Endpoint R g) (h : ℕ) (es : List (RowLabel R g))
      (s : ExploreState R g) (x : RowLabel R g),
      ((es.foldl (inspectEdge ξ L u h) s).inspectedAt x).isSome →
        (s.inspectedAt x).isSome ∨ x ∈ es := by
    intro u h es
    induction es with
    | nil =>
        intro s x hx
        exact Or.inl hx
    | cons e es ih =>
        intro s x hx
        rw [List.foldl_cons] at hx
        rcases ih (inspectEdge ξ L u h s e) x hx with hold | hmem
        · rcases hinspect u h s e x hold with hold | heq
          · exact Or.inl hold
          · exact Or.inr (by simp [heq])
        · exact Or.inr (by simp [hmem])
  have hprovProcess (u : Endpoint R g) (s : ExploreState R g) (x : RowLabel R g) :
      ((processEndpoint ξ L u s).inspectedAt x).isSome →
        (s.inspectedAt x).isSome ∨ x ∈ incidentEdges u := by
    intro hx
    unfold processEndpoint at hx
    rcases hprovFold u ((s.request u).getD 0) (incidentEdges u)
        { s with processed := insert u s.processed } x hx with hold | hmem
    · exact Or.inl (by simpa using hold)
    · exact Or.inr hmem
  have hinspectProcessed (u : Endpoint R g) (h : ℕ) (s : ExploreState R g)
      (e : RowLabel R g) : (inspectEdge ξ L u h s e).processed = s.processed := by
    by_cases hg : s.giant
    · simp [inspectEdge, hg]
    · cases hk : edgeArrivalKey ξ e with
      | none => simp [inspectEdge, hg, hk]
      | some k =>
          by_cases hkh : k < h
          · by_cases hproc : edgeOther u e ∈ s.processed
            · simp [inspectEdge, hg, hk, hkh, hproc]
            · simp [inspectEdge, hg, hk, hkh, hproc] <;> split_ifs <;> rfl
          · simp [inspectEdge, hg, hk, hkh]
  have hprocessedFold : ∀ (u : Endpoint R g) (h : ℕ) (es : List (RowLabel R g))
      (s : ExploreState R g), (es.foldl (inspectEdge ξ L u h) s).processed = s.processed := by
    intro u h es
    induction es with
    | nil => intro s; rfl
    | cons e es ih =>
        intro s
        rw [List.foldl_cons, ih]
        exact hinspectProcessed u h s e
  have hincident (u : Endpoint R g) (e : RowLabel R g) (he : e ∈ incidentEdges u) :
      EdgeIncident u e := by
    cases u with
    | inl a =>
        have he' : e ∈ List.ofFn (fun y : Fin g => (a, y)) := by simpa [incidentEdges] using he
        rcases List.mem_ofFn.mp he' with ⟨y, heq⟩
        cases e with
        | mk b z =>
            simp only [Prod.mk.injEq] at heq
            rcases heq with ⟨rfl, rfl⟩
            exact Or.inl rfl
    | inr y =>
        have he' : e ∈ List.ofFn (fun i : Fin (Fintype.card R) =>
            ((Fintype.equivFin R).symm i, y)) := by simpa [incidentEdges] using he
        rcases List.mem_ofFn.mp he' with ⟨i, heq⟩
        cases e with
        | mk a z =>
            simp only [Prod.mk.injEq] at heq
            rcases heq with ⟨_, rfl⟩
            exact Or.inr rfl
  let Inv : ExploreState R g → Prop := fun s =>
    s.processed ⊆ s.active ∧
      ∀ e, (s.inspectedAt e).isSome →
        ∃ u, u ∈ s.processed ∧ EdgeIncident u e
  have hprocessInv (s : ExploreState R g) (u : Endpoint R g) (hs : Inv s)
      (hu : u ∈ s.active) : Inv (processEndpoint ξ L u s) := by
    have hprocessed : (processEndpoint ξ L u s).processed = insert u s.processed := by
      simpa [processEndpoint] using hprocessedFold u ((s.request u).getD 0) (incidentEdges u)
        { s with processed := insert u s.processed }
    constructor
    · intro v hv
      rw [hprocessed] at hv
      simp only [Finset.mem_insert] at hv
      rcases hv with hEq | hv
      · subst v
        exact hactiveProcess u s hu
      · exact hactiveProcess u s (hs.1 hv)
    · intro e he
      rcases hprovProcess u s e he with heOld | heNew
      · rcases hs.2 e heOld with ⟨v, hv, hve⟩
        exact ⟨v, by rw [hprocessed]; exact Finset.mem_insert_of_mem hv, hve⟩
      · exact ⟨u, by rw [hprocessed]; exact Finset.mem_insert_self u s.processed,
          hincident u e heNew⟩
  have hnextMem (s : ExploreState R g) (u : Endpoint R g)
      (hn : nextPending s = some u) : u ∈ pendingEndpoints s := by
    by_cases hp : (pendingEndpoints s).Nonempty
    · have hmax := (pendingEndpoints s).exists_max_image (pendingKey s) hp
      have heq : ((pendingEndpoints s).exists_max_image (pendingKey s) hp).choose = u := by
        simpa [nextPending, hp] using hn
      rw [← heq]
      exact hmax.choose_spec.1
    · simp [nextPending, hp] at hn
  have hrun : ∀ f (s : ExploreState R g), Inv s → Inv (exploreRun ξ L f s) := by
    intro f
    induction f with
    | zero =>
        intro s hs
        simpa [exploreRun] using hs
    | succ f ih =>
        intro s hs
        by_cases hg : s.giant
        · simpa [exploreRun, hg] using hs
        · cases hp : nextPending s with
          | none => simpa [exploreRun, hg, hp] using hs
          | some u =>
              have hmem := hnextMem s u hp
              have hmem' : (s.request u).isSome ∧ u ∉ s.processed := by
                simpa [pendingEndpoints] using hmem
              have hu : u ∈ s.active := by
                simpa [ExploreState.active] using hmem'.1
              simpa [exploreRun, hg, hp] using ih (processEndpoint ξ L u s) (hprocessInv s u hs hu)
  have hinit : Inv (initExploreState T roots L) := by
    constructor
    · exact Finset.empty_subset _
    · intro e he
      simp [initExploreState] at he
  have hfinal := hrun (Fintype.card (Endpoint R g)) (initExploreState T roots L) hinit
  intro e hins
  have hins' : ((truncatedExploration ξ roots L).inspectedAt e).isSome := by
    cases hi : (truncatedExploration ξ roots L).inspectedAt e with
    | none => exact False.elim (by simpa [leafConstraint, EdgeConstraint.inspected, hi] using hins)
    | some H => simp [hi]
  rcases hfinal.2 e hins' with ⟨u, hu, hedge⟩
  rcases hedge with hrow | hlabel
  · left
    simpa [hrow, truncatedExploration] using hfinal.1 hu
  · right
    simpa [hlabel, truncatedExploration] using hfinal.1 hu

/-- L3.10b-wf2 (03:873–874, 03:880–881): every inspected hit has both endpoints active, also on a giant leaf (the
endpoint of the last hit is registered before stopping). -/
theorem truncatedExploration_hits_active {T : ℕ} {R : Type*} [Fintype R] [DecidableEq R]
    {g : ℕ} {Ω : R → Type*} (ξ : ClockField T R g Ω) (roots : Finset (Endpoint R g)) (L : ℕ) :
    ∀ e, (leafConstraint ξ (truncatedExploration ξ roots L) e).isHit →
      Sum.inl e.1 ∈ (truncatedExploration ξ roots L).active ∧
        Sum.inr e.2 ∈ (truncatedExploration ξ roots L).active := by
  classical
  have hactiveInspect (u : Endpoint R g) (h : ℕ) (s : ExploreState R g) (e : RowLabel R g) :
      s.active ⊆ (inspectEdge ξ L u h s e).active := by
    intro v hv
    have hv' : (s.request v).isSome := by simpa [ExploreState.active] using hv
    have hout : ((inspectEdge ξ L u h s e).request v).isSome := by
      by_cases hg : s.giant
      · simpa [inspectEdge, hg] using hv'
      · cases hk : edgeArrivalKey ξ e with
        | none => simpa [inspectEdge, hg, hk] using hv'
        | some k =>
            by_cases hkh : k < h
            · by_cases hproc : edgeOther u e ∈ s.processed
              · simpa [inspectEdge, hg, hk, hkh, hproc] using hv'
              · by_cases hw : edgeOther u e = v
                · subst v
                  simp [inspectEdge, hg, hk, hkh, hproc] <;> split_ifs <;> simp [Function.update]
                · simp only [inspectEdge, if_neg hg, hk, if_pos hkh, if_neg hproc]
                  have hvw : v ≠ edgeOther u e := by
                    intro hvw
                    exact hw hvw.symm
                  split_ifs <;> simpa [Function.update_of_ne hvw] using hv'
            · simpa [inspectEdge, hg, hk, hkh] using hv'
    simpa [ExploreState.active] using hout
  have hactiveFold : ∀ (u : Endpoint R g) (h : ℕ) (es : List (RowLabel R g))
      (s : ExploreState R g),
      s.active ⊆ (es.foldl (inspectEdge ξ L u h) s).active := by
    intro u h es
    induction es with
    | nil => intro s; exact Finset.Subset.rfl
    | cons e es ih =>
        intro s
        rw [List.foldl_cons]
        exact Finset.Subset.trans (hactiveInspect u h s e) (ih (inspectEdge ξ L u h s e))
  have hprocessedInspect (u : Endpoint R g) (h : ℕ) (s : ExploreState R g)
      (e : RowLabel R g) : (inspectEdge ξ L u h s e).processed = s.processed := by
    by_cases hg : s.giant
    · simp [inspectEdge, hg]
    · cases hk : edgeArrivalKey ξ e with
      | none => simp [inspectEdge, hg, hk]
      | some k =>
          by_cases hkh : k < h
          · by_cases hproc : edgeOther u e ∈ s.processed
            · simp [inspectEdge, hg, hk, hkh, hproc]
            · simp [inspectEdge, hg, hk, hkh, hproc] <;> split_ifs <;> rfl
          · simp [inspectEdge, hg, hk, hkh]
  have hprocessedFold : ∀ (u : Endpoint R g) (h : ℕ) (es : List (RowLabel R g))
      (s : ExploreState R g), (es.foldl (inspectEdge ξ L u h) s).processed = s.processed := by
    intro u h es
    induction es with
    | nil => intro s; rfl
    | cons e es ih =>
        intro s
        rw [List.foldl_cons, ih]
        exact hprocessedInspect u h s e
  have hinspectedAtSelf (u : Endpoint R g) (h : ℕ) (s : ExploreState R g)
      (e : RowLabel R g) :
      (inspectEdge ξ L u h s e).inspectedAt e =
        if s.giant then s.inspectedAt e else some (max ((s.inspectedAt e).getD 0) h) := by
    by_cases hg : s.giant
    · simp [inspectEdge, hg]
    · cases hk : edgeArrivalKey ξ e with
      | none => simp [inspectEdge, hg, hk]
      | some k =>
          by_cases hkh : k < h
          · by_cases hproc : edgeOther u e ∈ s.processed
            · simp [inspectEdge, hg, hk, hkh, hproc]
            · simp only [inspectEdge, if_neg hg, hk, if_pos hkh, if_neg hproc]
              split_ifs
              all_goals
                change Function.update s.inspectedAt e (some (max ((s.inspectedAt e).getD 0) h)) e =
                  some (max ((s.inspectedAt e).getD 0) h)
                simp
          · simp [inspectEdge, hg, hk, hkh]
  have hinspectedAtOther (u : Endpoint R g) (h : ℕ) (s : ExploreState R g)
      (e x : RowLabel R g) (hxe : x ≠ e) :
      (inspectEdge ξ L u h s e).inspectedAt x = s.inspectedAt x := by
    by_cases hg : s.giant
    · simp [inspectEdge, hg]
    · cases hk : edgeArrivalKey ξ e with
      | none => simp [inspectEdge, hg, hk, Function.update_of_ne hxe]
      | some k =>
          by_cases hkh : k < h
          · by_cases hproc : edgeOther u e ∈ s.processed
            · simp [inspectEdge, hg, hk, hkh, hproc, Function.update_of_ne hxe]
            · simp only [inspectEdge, if_neg hg, hk, if_pos hkh, if_neg hproc]
              split_ifs
              all_goals
                change Function.update s.inspectedAt e (some (max ((s.inspectedAt e).getD 0) h)) x =
                  s.inspectedAt x
                exact Function.update_of_ne hxe _ _
          · simp [inspectEdge, hg, hk, hkh, Function.update_of_ne hxe]
  have hotherAfter (u : Endpoint R g) (h : ℕ) (s : ExploreState R g)
      (e : RowLabel R g) (k : ℕ) (hg : s.giant = false)
      (hk : edgeArrivalKey ξ e = some k) (hkh : k < h)
      (hproc : edgeOther u e ∉ s.processed) :
      edgeOther u e ∈ (inspectEdge ξ L u h s e).active := by
    have hout : ((inspectEdge ξ L u h s e).request (edgeOther u e)).isSome := by
      simp [inspectEdge, hg, hk, hkh, hproc] <;> split_ifs <;> simp [Function.update]
    simpa [ExploreState.active] using hout
  have hpairActive (s : ExploreState R g) (u : Endpoint R g) (e : RowLabel R g)
      (he : EdgeIncident u e) (hu : u ∈ s.active) (hw : edgeOther u e ∈ s.active) :
      Sum.inl e.1 ∈ s.active ∧ Sum.inr e.2 ∈ s.active := by
    rcases he with hrow | hlabel
    · subst u
      exact ⟨hu, by simpa [edgeOther] using hw⟩
    · subst u
      exact ⟨by simpa [edgeOther] using hw, hu⟩
  let Inv : ExploreState R g → Prop := fun s =>
    s.processed ⊆ s.active ∧
      ∀ e H, s.inspectedAt e = some H → ∀ k, edgeArrivalKey ξ e = some k → k < H →
        Sum.inl e.1 ∈ s.active ∧ Sum.inr e.2 ∈ s.active
  have hinspectInv (u : Endpoint R g) (h : ℕ) (s : ExploreState R g) (e : RowLabel R g)
      (hs : Inv s) (hu : u ∈ s.active) (he : EdgeIncident u e) :
      Inv (inspectEdge ξ L u h s e) := by
    constructor
    · intro v hv
      have hv' : v ∈ s.processed := by
        rw [hprocessedInspect u h s e] at hv
        exact hv
      exact hactiveInspect u h s e (hs.1 hv')
    · intro x H hAt k hkey hkh
      by_cases hxe : x = e
      · subst x
        by_cases hg : s.giant
        · have hOld : s.inspectedAt e = some H := by simpa [inspectEdge, hg] using hAt
          rcases hs.2 e H hOld k hkey hkh with ⟨hr, hy⟩
          exact ⟨hactiveInspect u h s e hr, hactiveInspect u h s e hy⟩
        · have hAtH : H = max ((s.inspectedAt e).getD 0) h := by
            have hgFalse : s.giant = false := by cases hgiant : s.giant <;> simp_all
            rw [hinspectedAtSelf u h s e, hgFalse] at hAt
            exact (Option.some.inj hAt).symm
          cases hi : s.inspectedAt e with
          | none =>
              have hkh' : k < h := by simpa [hi, hAtH] using hkh
              have hw : edgeOther u e ∈ (inspectEdge ξ L u h s e).active := by
                by_cases hp : edgeOther u e ∈ s.processed
                · exact hactiveInspect u h s e (hs.1 hp)
                · exact hotherAfter u h s e k (by cases hgiant : s.giant <;> simp_all)
                    hkey hkh' hp
              exact hpairActive (inspectEdge ξ L u h s e) u e he
                (hactiveInspect u h s e hu) hw
          | some H₀ =>
              by_cases hOldKey : k < H₀
              · rcases hs.2 e H₀ hi k hkey hOldKey with ⟨hr, hy⟩
                exact ⟨hactiveInspect u h s e hr, hactiveInspect u h s e hy⟩
              · have hH₀ : H₀ ≤ k := Nat.le_of_not_gt hOldKey
                have hmax : H = max H₀ h := by simpa [hi] using hAtH
                have hkh' : k < h := by rw [hmax] at hkh; omega
                have hw : edgeOther u e ∈ (inspectEdge ξ L u h s e).active := by
                  by_cases hp : edgeOther u e ∈ s.processed
                  · exact hactiveInspect u h s e (hs.1 hp)
                  · exact hotherAfter u h s e k (by cases hgiant : s.giant <;> simp_all)
                      hkey hkh' hp
                exact hpairActive (inspectEdge ξ L u h s e) u e he
                  (hactiveInspect u h s e hu) hw
      · have hOld : s.inspectedAt x = some H := by
          rw [hinspectedAtOther u h s e x hxe] at hAt
          exact hAt
        rcases hs.2 x H hOld k hkey hkh with ⟨hr, hy⟩
        exact ⟨hactiveInspect u h s e hr, hactiveInspect u h s e hy⟩
  have hincident (u : Endpoint R g) (e : RowLabel R g) (he : e ∈ incidentEdges u) :
      EdgeIncident u e := by
    cases u with
    | inl a =>
        have he' : e ∈ List.ofFn (fun y : Fin g => (a, y)) := by simpa [incidentEdges] using he
        rcases List.mem_ofFn.mp he' with ⟨y, heq⟩
        cases e with
        | mk b z =>
            simp only [Prod.mk.injEq] at heq
            rcases heq with ⟨rfl, rfl⟩
            exact Or.inl rfl
    | inr y =>
        have he' : e ∈ List.ofFn (fun i : Fin (Fintype.card R) =>
            ((Fintype.equivFin R).symm i, y)) := by simpa [incidentEdges] using he
        rcases List.mem_ofFn.mp he' with ⟨i, heq⟩
        cases e with
        | mk a z =>
            simp only [Prod.mk.injEq] at heq
            rcases heq with ⟨_, rfl⟩
            exact Or.inr rfl
  have hfoldInv (u : Endpoint R g) (h : ℕ) (es : List (RowLabel R g))
      (s : ExploreState R g) (hinc : ∀ e ∈ es, EdgeIncident u e)
      (hs : Inv s) (hu : u ∈ s.active) : Inv (es.foldl (inspectEdge ξ L u h) s) := by
    induction es generalizing s hs hu with
    | nil => simpa using hs
    | cons e es ih =>
        rw [List.foldl_cons]
        have hs' := hinspectInv u h s e hs hu (hinc e (by simp))
        have hu' := hactiveInspect u h s e hu
        exact ih (inspectEdge ξ L u h s e) (fun x hx => hinc x (by simp [hx])) hs' hu'
  have hprocessInv (s : ExploreState R g) (u : Endpoint R g) (hs : Inv s)
      (hu : u ∈ s.active) : Inv (processEndpoint ξ L u s) := by
    have hs₀ : Inv { s with processed := insert u s.processed } := by
      constructor
      · intro v hv
        simp only [Finset.mem_insert] at hv
        rcases hv with hEq | hv
        · subst v
          simpa [ExploreState.active] using hu
        · exact hs.1 hv
      · intro e H hAt k hk hkh
        exact hs.2 e H (by simpa using hAt) k hk hkh
    unfold processEndpoint
    exact hfoldInv u ((s.request u).getD 0) (incidentEdges u)
      { s with processed := insert u s.processed } (by
        intro e he
        exact hincident u e he) hs₀ hu
  have hnextMem (s : ExploreState R g) (u : Endpoint R g)
      (hn : nextPending s = some u) : u ∈ pendingEndpoints s := by
    by_cases hp : (pendingEndpoints s).Nonempty
    · have hmax := (pendingEndpoints s).exists_max_image (pendingKey s) hp
      have heq : ((pendingEndpoints s).exists_max_image (pendingKey s) hp).choose = u := by
        simpa [nextPending, hp] using hn
      rw [← heq]
      exact hmax.choose_spec.1
    · simp [nextPending, hp] at hn
  have hrun : ∀ f (s : ExploreState R g), Inv s → Inv (exploreRun ξ L f s) := by
    intro f
    induction f with
    | zero => intro s hs; simpa [exploreRun] using hs
    | succ f ih =>
        intro s hs
        by_cases hg : s.giant
        · simpa [exploreRun, hg] using hs
        · cases hp : nextPending s with
          | none => simpa [exploreRun, hg, hp] using hs
          | some u =>
              have hmem := hnextMem s u hp
              have hmem' : (s.request u).isSome ∧ u ∉ s.processed := by
                simpa [pendingEndpoints] using hmem
              have hu : u ∈ s.active := by simpa [ExploreState.active] using hmem'.1
              simpa [exploreRun, hg, hp] using ih (processEndpoint ξ L u s) (hprocessInv s u hs hu)
  have hinit : Inv (initExploreState T roots L) := by
    constructor
    · exact Finset.empty_subset _
    · intro e H hAt k hk hkh
      simp [initExploreState] at hAt
  have hfinal := hrun (Fintype.card (Endpoint R g)) (initExploreState T roots L) hinit
  intro e hhit
  have hdata : ∃ H k, (truncatedExploration ξ roots L).inspectedAt e = some H ∧
      edgeArrivalKey ξ e = some k ∧ k < H := by
    unfold leafConstraint at hhit
    cases hi : (truncatedExploration ξ roots L).inspectedAt e with
    | none => simp [hi, EdgeConstraint.isHit] at hhit
    | some H =>
        cases he : ξ e with
        | noArrival => simp [hi, he, EdgeConstraint.isHit] at hhit
        | tick t o =>
            by_cases hk : eventPriority (⟨e.1, e.2, t, o⟩ : ClockCandidate T R g Ω) < H
            · refine ⟨H, eventPriority (⟨e.1, e.2, t, o⟩ : ClockCandidate T R g Ω), rfl, ?_, hk⟩
              simp [edgeArrivalKey, he]
            · simp [hi, he, hk, EdgeConstraint.isHit] at hhit
  obtain ⟨H, k, hi, hk, hkh⟩ := hdata
  exact (hfinal.2 e H (by simpa [truncatedExploration] using hi) k hk hkh)

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
  classical
  cases t with
  | predicate k =>
      unfold activeEndpoints closureFrom
      apply Finset.filter_congr
      intro u hu
      simp [inBackwardClosure, inClosureFrom, testRootEndpoints, testRoots,
        rootBackwardPoint, rootHorizon]
  | singleton a =>
      unfold activeEndpoints closureFrom
      apply Finset.filter_congr
      intro u hu
      simp [inBackwardClosure, inClosureFrom, testRootEndpoints, testRoots,
        rootBackwardPoint, rootHorizon]

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
  classical
  have hactiveInspect (u : Endpoint R g) (h : ℕ) (s : ExploreState R g) (e : RowLabel R g) :
      s.active ⊆ (inspectEdge ξ L u h s e).active := by
    intro v hv
    have hv' : (s.request v).isSome := by simpa [ExploreState.active] using hv
    have hout : ((inspectEdge ξ L u h s e).request v).isSome := by
      by_cases hg : s.giant
      · simpa [inspectEdge, hg] using hv'
      · cases hk : edgeArrivalKey ξ e with
        | none => simpa [inspectEdge, hg, hk] using hv'
        | some k =>
            by_cases hkh : k < h
            · by_cases hproc : edgeOther u e ∈ s.processed
              · simpa [inspectEdge, hg, hk, hkh, hproc] using hv'
              · by_cases hw : edgeOther u e = v
                · subst v
                  simp [inspectEdge, hg, hk, hkh, hproc] <;> split_ifs <;> simp [Function.update]
                · simp only [inspectEdge, if_neg hg, hk, if_pos hkh, if_neg hproc]
                  have hvw : v ≠ edgeOther u e := by
                    intro hvw
                    exact hw hvw.symm
                  split_ifs <;> simpa [Function.update_of_ne hvw] using hv'
            · simpa [inspectEdge, hg, hk, hkh] using hv'
    simpa [ExploreState.active] using hout
  have hactiveFold : ∀ (u : Endpoint R g) (h : ℕ) (es : List (RowLabel R g))
      (s : ExploreState R g), s.active ⊆ (es.foldl (inspectEdge ξ L u h) s).active := by
    intro u h es
    induction es with
    | nil => intro s; exact Finset.Subset.rfl
    | cons e es ih =>
        intro s
        rw [List.foldl_cons]
        exact Finset.Subset.trans (hactiveInspect u h s e) (ih (inspectEdge ξ L u h s e))
  have hprocessedInspect (u : Endpoint R g) (h : ℕ) (s : ExploreState R g)
      (e : RowLabel R g) : (inspectEdge ξ L u h s e).processed = s.processed := by
    by_cases hg : s.giant
    · simp [inspectEdge, hg]
    · cases hk : edgeArrivalKey ξ e with
      | none => simp [inspectEdge, hg, hk]
      | some k =>
          by_cases hkh : k < h
          · by_cases hproc : edgeOther u e ∈ s.processed
            · simp [inspectEdge, hg, hk, hkh, hproc]
            · simp [inspectEdge, hg, hk, hkh, hproc] <;> split_ifs <;> rfl
          · simp [inspectEdge, hg, hk, hkh]
  have hprocessedFold : ∀ (u : Endpoint R g) (h : ℕ) (es : List (RowLabel R g))
      (s : ExploreState R g), (es.foldl (inspectEdge ξ L u h) s).processed = s.processed := by
    intro u h es
    induction es with
    | nil => intro s; rfl
    | cons e es ih =>
        intro s
        rw [List.foldl_cons, ih]
        exact hprocessedInspect u h s e
  have hincident (u : Endpoint R g) (e : RowLabel R g) (he : e ∈ incidentEdges u) :
      EdgeIncident u e := by
    cases u with
    | inl a =>
        have he' : e ∈ List.ofFn (fun y : Fin g => (a, y)) := by simpa [incidentEdges] using he
        rcases List.mem_ofFn.mp he' with ⟨y, heq⟩
        cases e with
        | mk b z =>
            simp only [Prod.mk.injEq] at heq
            rcases heq with ⟨rfl, rfl⟩
            exact Or.inl rfl
    | inr y =>
        have he' : e ∈ List.ofFn (fun i : Fin (Fintype.card R) =>
            ((Fintype.equivFin R).symm i, y)) := by simpa [incidentEdges] using he
        rcases List.mem_ofFn.mp he' with ⟨i, heq⟩
        cases e with
        | mk a z =>
            simp only [Prod.mk.injEq] at heq
            rcases heq with ⟨_, rfl⟩
            exact Or.inr rfl
  have hback {u : Endpoint R g} {e : RowLabel R g} {k h : ℕ}
      (he : EdgeIncident u e) (hk : edgeArrivalKey ξ e = some k) (hkh : k < h) :
      backwardStep ξ (u, h) (edgeOther u e, k) := by
    cases hξ : ξ e with
    | noArrival => simp [edgeArrivalKey, hξ] at hk
    | tick t o =>
        have hpri : eventPriority (⟨e.1, e.2, t, o⟩ : ClockCandidate T R g Ω) = k := by
          simpa [edgeArrivalKey, hξ] using hk
        refine ⟨(⟨e.1, e.2, t, o⟩ : ClockCandidate T R g Ω), ?_, ?_, hpri.symm, ?_⟩
        · simp [candidateIsArrival, hξ]
        · simpa [hpri] using hkh
        · rcases he with hrow | hlabel
          · subst u
            simp [edgeOther]
          · subst u
            simp [edgeOther]
  have hnewClosure {u : Endpoint R g} {e : RowLabel R g} {k h : ℕ}
      (hsrc : inClosureFrom ξ roots (u, h)) (he : EdgeIncident u e)
      (hk : edgeArrivalKey ξ e = some k) (hkh : k < h) :
      inClosureFrom ξ roots (edgeOther u e, k) := by
    rcases hsrc with ⟨r, hr, path⟩
    exact ⟨r, hr, Relation.ReflTransGen.tail path (hback he hk hkh)⟩
  let Inv : ExploreState R g → Prop := fun s =>
    roots ⊆ s.active ∧ s.processed ⊆ s.active ∧
      ∀ u h, s.request u = some h → inClosureFrom ξ roots (u, h)
  have hinspectInv (u : Endpoint R g) (h : ℕ) (s : ExploreState R g) (e : RowLabel R g)
      (hs : Inv s) (hsrc : inClosureFrom ξ roots (u, h)) (he : EdgeIncident u e) :
      Inv (inspectEdge ξ L u h s e) := by
    constructor
    · intro v hv
      exact hactiveInspect u h s e (hs.1 hv)
    constructor
    · intro v hv
      have hv' : v ∈ s.processed := by rw [hprocessedInspect u h s e] at hv; exact hv
      exact hactiveInspect u h s e (hs.2.1 hv')
    · intro v H hreq
      by_cases hg : s.giant
      · have hOld : s.request v = some H := by simpa [inspectEdge, hg] using hreq
        exact hs.2.2 v H hOld
      · cases hk : edgeArrivalKey ξ e with
        | none =>
            have hOld : s.request v = some H := by simpa [inspectEdge, hg, hk] using hreq
            exact hs.2.2 v H hOld
        | some k =>
            by_cases hkh : k < h
            · by_cases hproc : edgeOther u e ∈ s.processed
              · have hOld : s.request v = some H := by
                  simpa [inspectEdge, hg, hk, hkh, hproc] using hreq
                exact hs.2.2 v H hOld
              · by_cases hvw : v = edgeOther u e
                · subst v
                  cases hr : s.request (edgeOther u e) with
                  | none =>
                      have hval : (inspectEdge ξ L u h s e).request (edgeOther u e) = some k := by
                        have hgFalse : s.giant = false := by cases hbool : s.giant <;> simp_all
                        simp [inspectEdge, hgFalse, hk, hkh, hproc, hr] <;>
                          split_ifs <;> simp [Function.update]
                      rw [hval] at hreq
                      have hH : H = k := (Option.some.inj hreq).symm
                      subst H
                      exact hnewClosure hsrc he hk hkh
                  | some r =>
                      have hval : (inspectEdge ξ L u h s e).request (edgeOther u e) =
                          some (max r k) := by
                        have hgFalse : s.giant = false := by cases hbool : s.giant <;> simp_all
                        simp [inspectEdge, hgFalse, hk, hkh, hproc, hr] <;>
                          split_ifs <;> simp [Function.update]
                      rw [hval] at hreq
                      have hH : H = max r k := (Option.some.inj hreq).symm
                      by_cases hrk : r ≤ k
                      · have hH' : H = k := by
                          simpa [Nat.max_eq_right hrk] using hH
                        rw [hH']
                        exact hnewClosure hsrc he hk hkh
                      · have hkr : k ≤ r := Nat.le_of_not_ge hrk
                        have hH' : H = r := by
                          simpa [Nat.max_eq_left hkr] using hH
                        rw [hH']
                        exact hs.2.2 (edgeOther u e) r hr
                · have hOld : s.request v = some H := by
                    simp only [inspectEdge, if_neg hg, hk, if_pos hkh, if_neg hproc] at hreq
                    split_ifs at hreq <;>
                      simpa [Function.update_of_ne (by simpa [eq_comm] using hvw)] using hreq
                  exact hs.2.2 v H hOld
            · have hOld : s.request v = some H := by simpa [inspectEdge, hg, hk, hkh] using hreq
              exact hs.2.2 v H hOld
  have hfoldInv (u : Endpoint R g) (h : ℕ) (es : List (RowLabel R g))
      (s : ExploreState R g) (hinc : ∀ e ∈ es, EdgeIncident u e)
      (hs : Inv s) (hsrc : inClosureFrom ξ roots (u, h)) : Inv (es.foldl (inspectEdge ξ L u h) s) := by
    induction es generalizing s hs with
    | nil => simpa using hs
    | cons e es ih =>
        rw [List.foldl_cons]
        have hs' := hinspectInv u h s e hs hsrc (hinc e (by simp))
        exact ih (inspectEdge ξ L u h s e) (fun x hx => hinc x (by simp [hx])) hs'
  have hprocessInv (s : ExploreState R g) (u : Endpoint R g) (hs : Inv s)
      (hu : u ∈ s.active) : Inv (processEndpoint ξ L u s) := by
    have hreq : ∃ H, s.request u = some H := by
      have hSome : (s.request u).isSome := by simpa [ExploreState.active] using hu
      cases hr : s.request u with
      | none => simp [hr] at hSome
      | some H => exact ⟨H, rfl⟩
    obtain ⟨H, hrequest⟩ := hreq
    have hsrc := hs.2.2 u H hrequest
    have hs₀ : Inv { s with processed := insert u s.processed } := by
      constructor
      · simpa [ExploreState.active] using hs.1
      constructor
      · intro v hv
        simp only [Finset.mem_insert] at hv
        rcases hv with hEq | hv
        · subst v
          exact hu
        · exact hs.2.1 hv
      · exact hs.2.2
    unfold processEndpoint
    have hH : (s.request u).getD 0 = H := by simp [hrequest]
    simpa [hH] using hfoldInv u H (incidentEdges u)
      { s with processed := insert u s.processed } (by
        intro e he
        exact hincident u e he) hs₀ hsrc
  have hnextMem (s : ExploreState R g) (u : Endpoint R g)
      (hn : nextPending s = some u) : u ∈ pendingEndpoints s := by
    by_cases hp : (pendingEndpoints s).Nonempty
    · have hmax := (pendingEndpoints s).exists_max_image (pendingKey s) hp
      have heq : ((pendingEndpoints s).exists_max_image (pendingKey s) hp).choose = u := by
        simpa [nextPending, hp] using hn
      rw [← heq]
      exact hmax.choose_spec.1
    · simp [nextPending, hp] at hn
  have hrun : ∀ f (s : ExploreState R g), Inv s → Inv (exploreRun ξ L f s) := by
    intro f
    induction f with
    | zero => intro s hs; simpa [exploreRun] using hs
    | succ f ih =>
        intro s hs
        by_cases hg : s.giant
        · simpa [exploreRun, hg] using hs
        · cases hp : nextPending s with
          | none => simpa [exploreRun, hg, hp] using hs
          | some u =>
              have hmem := hnextMem s u hp
              have hmem' : (s.request u).isSome ∧ u ∉ s.processed := by
                simpa [pendingEndpoints] using hmem
              have hu : u ∈ s.active := by simpa [ExploreState.active] using hmem'.1
              simpa [exploreRun, hg, hp] using ih (processEndpoint ξ L u s) (hprocessInv s u hs hu)
  have hinit : Inv (initExploreState T roots L) := by
    constructor
    · intro u hu
      have hsome : (initExploreState T roots L).request u = some (rootHorizon T R g) := by
        simp [initExploreState, hu]
      have hIsSome : ((initExploreState T roots L).request u).isSome := by
        rw [hsome]
        simp
      simpa [ExploreState.active] using hIsSome
    constructor
    · exact Finset.empty_subset _
    · intro u H hreq
      by_cases hu : u ∈ roots
      · have hreq' : some (rootHorizon T R g) = some H := by simpa [initExploreState, hu] using hreq
        have hH : H = rootHorizon T R g := (Option.some.inj hreq').symm
        subst H
        exact ⟨u, hu, Relation.ReflTransGen.refl⟩
      · simp [initExploreState, hu] at hreq
  have hfinal := hrun (Fintype.card (Endpoint R g)) (initExploreState T roots L) hinit
  refine ⟨?_, ?_, ?_⟩
  · simpa [truncatedExploration] using hfinal.1
  · simpa [truncatedExploration] using hfinal.2.1
  · intro u hu
    cases hreq : (truncatedExploration ξ roots L).request u with
    | none => simp [ExploreState.active, hreq] at hu
    | some H =>
        have hReach := hfinal.2.2 u H (by simpa [truncatedExploration] using hreq)
        have hmem : ∃ h, inClosureFrom ξ roots (u, h) := ⟨H, hReach⟩
        simpa [closureFrom] using hmem

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
  classical
  let Inv : ExploreState R g → Prop := fun s =>
    (s.giant = true ↔ L ≤ s.active.card) ∧ (roots.card ≤ L → s.active.card ≤ L)
  have hactiveUpdateSome (s : ExploreState R g) (w : Endpoint R g) (q : ℕ)
      (hSome : (s.request w).isSome) :
      ({ s with request := Function.update s.request w (some q) } : ExploreState R g).active = s.active := by
    ext v
    by_cases hv : v = w
    · subst v
      simp [ExploreState.active, hSome]
    · simp [ExploreState.active, Function.update_of_ne hv]
  have hactiveUpdateNone (s : ExploreState R g) (w : Endpoint R g) (q : ℕ)
      (hNone : s.request w = none) :
      ({ s with request := Function.update s.request w (some q) } : ExploreState R g).active =
        insert w s.active := by
    ext v
    simp only [ExploreState.active, Finset.mem_filter, Finset.mem_univ, true_and]
    by_cases hv : v = w
    · subst v
      simp [ExploreState.active, Function.update, hNone]
    · rw [Function.update_of_ne hv]
      simp [hv]
  have hinspectInv (s : ExploreState R g) (u : Endpoint R g) (h : ℕ) (e : RowLabel R g)
      (hs : Inv s) : Inv (inspectEdge ξ L u h s e) := by
    by_cases hgiant : s.giant = true
    · simpa [Inv, inspectEdge, hgiant] using hs
    · have hfalse : s.giant = false := by cases hb : s.giant <;> simp_all
      cases hk : edgeArrivalKey ξ e with
      | none =>
          let s₁ : ExploreState R g :=
            { s with inspectedAt := Function.update s.inspectedAt e (some (max ((s.inspectedAt e).getD 0) h)) }
          have hstate : inspectEdge ξ L u h s e = s₁ := by simp [inspectEdge, hfalse, hk, s₁]
          rw [hstate]
          change Inv s
          exact hs
      | some k =>
          by_cases hkh : k < h
          · by_cases hproc : edgeOther u e ∈ s.processed
            · have hA : (inspectEdge ξ L u h s e).active = s.active := by
                ext v
                simp [ExploreState.active, inspectEdge, hfalse, hk, hkh, hproc]
              let s₁ : ExploreState R g :=
                { s with inspectedAt := Function.update s.inspectedAt e (some (max ((s.inspectedAt e).getD 0) h)) }
              have hstate : inspectEdge ξ L u h s e = s₁ := by
                simp [inspectEdge, hfalse, hk, hkh, hproc, s₁]
              rw [hstate]
              change Inv s
              exact hs
            · cases hr : s.request (edgeOther u e) with
              | some r =>
                  let s₁ : ExploreState R g :=
                    { s with inspectedAt := Function.update s.inspectedAt e (some (max ((s.inspectedAt e).getD 0) h)) }
                  let s₂ : ExploreState R g :=
                    { s₁ with request := Function.update s.request (edgeOther u e) (some (max r k)) }
                  have hAct₂ : s₂.active = s.active := by
                    have h₁ : s₁.active = s.active := rfl
                    calc
                      s₂.active = s₁.active := hactiveUpdateSome s₁ (edgeOther u e) (max r k)
                        (by simpa [s₁, hr] using (show (s₁.request (edgeOther u e)).isSome from by simp [s₁, hr]))
                      _ = s.active := h₁
                  have hNo : ¬ L ≤ s.active.card := by
                    intro hL
                    exact hgiant (hs.1.mpr hL)
                  have hNotThreshold : ¬ L ≤ s₂.active.card := by
                    simpa [hAct₂] using hNo
                  have hOutEq : inspectEdge ξ L u h s e =
                      if L ≤ s₂.active.card then { s₂ with giant := true } else s₂ := by
                    simp [inspectEdge, hfalse, hk, hkh, hproc, hr, s₁, s₂]
                  have hOutActive : (inspectEdge ξ L u h s e).active = s₂.active := by
                    rw [hOutEq]
                    split_ifs <;> rfl
                  have hOutGiant : (inspectEdge ξ L u h s e).giant = false := by
                    rw [hOutEq]
                    simp only [if_neg hNotThreshold]
                    change s₂.giant = false
                    simp [s₂, s₁, hfalse]
                  have hOut : Inv (inspectEdge ξ L u h s e) := by
                    constructor
                    · rw [hOutGiant, hOutActive]
                      simp [hNotThreshold]
                    · intro hroots
                      rw [hOutActive]
                      rw [hAct₂]
                      exact hs.2 hroots
                  exact hOut
              | none =>
                  let s₁ : ExploreState R g :=
                    { s with inspectedAt := Function.update s.inspectedAt e (some (max ((s.inspectedAt e).getD 0) h)) }
                  let s₂ : ExploreState R g :=
                    { s₁ with request := Function.update s.request (edgeOther u e) (some k) }
                  have hNotActive : edgeOther u e ∉ s.active := by
                    simpa [ExploreState.active, hr]
                  have hAct₂ : s₂.active = insert (edgeOther u e) s.active := by
                    have h₁ : s₁.active = s.active := rfl
                    calc
                      s₂.active = insert (edgeOther u e) s₁.active :=
                        hactiveUpdateNone s₁ (edgeOther u e) k (by simp [s₁, hr])
                      _ = insert (edgeOther u e) s.active := by rw [h₁]
                  have hCard₂ : s₂.active.card = s.active.card + 1 := by
                    rw [hAct₂]
                    simp [hNotActive]
                  have hOutEq : inspectEdge ξ L u h s e =
                      if L ≤ s₂.active.card then { s₂ with giant := true } else s₂ := by
                    simp [inspectEdge, hfalse, hk, hkh, hproc, hr, s₁, s₂]
                  have hOutActive : (inspectEdge ξ L u h s e).active = s₂.active := by
                    rw [hOutEq]
                    split_ifs <;> rfl
                  by_cases hThreshold : L ≤ s₂.active.card
                  · have hOutGiant : (inspectEdge ξ L u h s e).giant = true := by
                      rw [hOutEq]
                      simp only [if_pos hThreshold]
                    have hBound₂ (hroots : roots.card ≤ L) : s₂.active.card ≤ L := by
                      have hOld := hs.2 hroots
                      have hOldLt : s.active.card < L := by
                        by_contra hlt
                        exact hgiant ((hs.1).2 (by omega))
                      rw [hCard₂]
                      omega
                    have hOut : Inv (inspectEdge ξ L u h s e) := by
                      constructor
                      · rw [hOutGiant, hOutActive]
                        simp [hThreshold]
                      · intro hroots
                        rw [hOutActive]
                        exact hBound₂ hroots
                    exact hOut
                  · have hOutGiant : (inspectEdge ξ L u h s e).giant = false := by
                      rw [hOutEq]
                      simp only [if_neg hThreshold]
                      change s₂.giant = false
                      simp [s₂, s₁, hfalse]
                    have hBound₂ (hroots : roots.card ≤ L) : s₂.active.card ≤ L := by
                      have hOld := hs.2 hroots
                      have hOldLt : s.active.card < L := by
                        by_contra hlt
                        exact hgiant ((hs.1).2 (by omega))
                      rw [hCard₂]
                      omega
                    have hOut : Inv (inspectEdge ξ L u h s e) := by
                      constructor
                      · rw [hOutGiant, hOutActive]
                        simp [hThreshold]
                      · intro hroots
                        rw [hOutActive]
                        exact hBound₂ hroots
                    exact hOut
          · let s₁ : ExploreState R g :=
              { s with inspectedAt := Function.update s.inspectedAt e (some (max ((s.inspectedAt e).getD 0) h)) }
            have hstate : inspectEdge ξ L u h s e = s₁ := by simp [inspectEdge, hfalse, hk, hkh, s₁]
            rw [hstate]
            change Inv s
            exact hs
  have hfoldInv (u : Endpoint R g) (h : ℕ) (es : List (RowLabel R g))
      (s : ExploreState R g) (hs : Inv s) : Inv (es.foldl (inspectEdge ξ L u h) s) := by
    induction es generalizing s hs with
    | nil => simpa using hs
    | cons e es ih =>
        rw [List.foldl_cons]
        exact ih (inspectEdge ξ L u h s e) (hinspectInv s u h e hs)
  have hprocessInv (s : ExploreState R g) (u : Endpoint R g) (hs : Inv s) :
      Inv (processEndpoint ξ L u s) := by
    have hs₀ : Inv { s with processed := insert u s.processed } := by
      change Inv s
      exact hs
    unfold processEndpoint
    exact hfoldInv u ((s.request u).getD 0) (incidentEdges u)
      { s with processed := insert u s.processed } hs₀
  have hrun : ∀ f (s : ExploreState R g), Inv s → Inv (exploreRun ξ L f s) := by
    intro f
    induction f with
    | zero => intro s hs; simpa [exploreRun] using hs
    | succ f ih =>
        intro s hs
        by_cases hg : s.giant = true
        · simpa [exploreRun, hg] using hs
        · have hfalse : s.giant = false := by cases hb : s.giant <;> simp_all
          cases hp : nextPending s with
          | none => simpa [exploreRun, hfalse, hp] using hs
          | some u =>
              simpa [exploreRun, hfalse, hp] using ih (processEndpoint ξ L u s) (hprocessInv s u hs)
  have hinit : Inv (initExploreState T roots L) := by
    have hAct : (initExploreState T roots L).active = roots := by
      ext u
      simp [ExploreState.active, initExploreState]
    constructor
    · change (initExploreState T roots L).giant = true ↔
        L ≤ (initExploreState T roots L).active.card
      rw [hAct]
      simp [initExploreState]
    · intro hroots
      rw [hAct]
      exact hroots
  have hfinal := hrun (Fintype.card (Endpoint R g)) (initExploreState T roots L) hinit
  have hG := hfinal.1
  have hB := hfinal.2
  refine ⟨?_, ?_, hB⟩
  · intro hg
    exact hG.mp hg
  · intro hg
    have hnot : ¬ L ≤ (truncatedExploration ξ roots L).active.card := by
      intro hL
      have ht := hG.mpr hL
      have hne : (truncatedExploration ξ roots L).giant = true → False := by
        intro ht'
        rw [hg] at ht'
        cases ht'
      exact hne ht
    exact Nat.lt_of_not_ge hnot

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
  classical
  let foldAt (e : RowLabel R g) (l : List ι) (C : EdgeConstraint T (Ω e.1)) :
      EdgeConstraint T (Ω e.1) :=
    l.foldl (fun A i => qClockConstraintMeet A ((τ i).constraint e)) C
  have hfoldAllows (e : RowLabel R g) :
      ∀ (l : List ι) (C : EdgeConstraint T (Ω e.1)),
        C.Allows (ξ₀ e) → (∀ i ∈ l, ((τ i).constraint e).Allows (ξ₀ e)) →
        ∀ x, (foldAt e l C).Allows x ↔
          C.Allows x ∧ ∀ i ∈ l, ((τ i).constraint e).Allows x := by
    intro l
    induction l with
    | nil =>
        intro C hC hAll x
        simp [foldAt]
    | cons i l ih =>
        intro C hC hAll x
        have hCi₀ : ((τ i).constraint e).Allows (ξ₀ e) := hAll i (by simp)
        have hTail₀ : ∀ j ∈ l, ((τ j).constraint e).Allows (ξ₀ e) := by
          intro j hj
          exact hAll j (by simp [hj])
        have hMerge₀ : (qClockConstraintMeet C ((τ i).constraint e)).Allows (ξ₀ e) :=
          (qClockConstraintMeet_allows C ((τ i).constraint e) (ξ₀ e) (ξ₀ e) hC hCi₀).2 ⟨hC, hCi₀⟩
        have hrec := ih (qClockConstraintMeet C ((τ i).constraint e)) hMerge₀ hTail₀ x
        simp only [foldAt, List.foldl_cons] at hrec ⊢
        rw [hrec, qClockConstraintMeet_allows C ((τ i).constraint e) (ξ₀ e) x hC hCi₀]
        simp [List.mem_cons, and_assoc, and_left_comm, and_comm]
  have hfoldInspected (e : RowLabel R g) :
      ∀ (l : List ι) (C : EdgeConstraint T (Ω e.1)),
        (foldAt e l C).inspected ↔
          C.inspected ∨ ∃ i ∈ l, ((τ i).constraint e).inspected := by
    intro l
    induction l with
    | nil => intro C; simp [foldAt]
    | cons i l ih =>
        intro C
        simp only [foldAt, List.foldl_cons]
        rw [ih, qClockConstraintMeet_inspected]
        simp [List.mem_cons, or_assoc, or_left_comm, or_comm]
  have hfoldHit (e : RowLabel R g) :
      ∀ (l : List ι) (C : EdgeConstraint T (Ω e.1)),
        (foldAt e l C).isHit ↔
          C.isHit ∨ ∃ i ∈ l, ((τ i).constraint e).isHit := by
    intro l
    induction l with
    | nil => intro C; simp [foldAt]
    | cons i l ih =>
        intro C
        simp only [foldAt, List.foldl_cons]
        rw [ih, qClockConstraintMeet_isHit]
        simp [List.mem_cons, or_assoc, or_left_comm, or_comm]
  let inds : List ι := Finset.univ.toList
  let active := Finset.univ.biUnion fun i => (τ i).active
  let M : ClockLeaf T R g Ω :=
    { constraint := fun e => foldAt e inds .unrestricted
      active := active
      inspected_touches_active := by
        intro e he
        have hsome : ∃ i ∈ inds, ((τ i).constraint e).inspected := by
          have h := (hfoldInspected e inds .unrestricted).mp he
          simpa [inds, EdgeConstraint.inspected] using h
        obtain ⟨i, hi, hiIns⟩ := hsome
        rcases (τ i).inspected_touches_active e hiIns with hrow | hlabel
        · exact Or.inl (Finset.mem_biUnion.mpr ⟨i, Finset.mem_univ i, hrow⟩)
        · exact Or.inr (Finset.mem_biUnion.mpr ⟨i, Finset.mem_univ i, hlabel⟩)
      hits_activate_both := by
        intro e he
        have hsome : ∃ i ∈ inds, ((τ i).constraint e).isHit := by
          have h := (hfoldHit e inds .unrestricted).mp he
          simpa [inds, EdgeConstraint.isHit] using h
        obtain ⟨i, hi, hiHit⟩ := hsome
        rcases (τ i).hits_activate_both e hiHit with ⟨hrow, hlabel⟩
        exact ⟨Finset.mem_biUnion.mpr ⟨i, Finset.mem_univ i, hrow⟩,
          Finset.mem_biUnion.mpr ⟨i, Finset.mem_univ i, hlabel⟩⟩ }
  refine ⟨M, ?_, rfl⟩
  intro ξ
  change (∀ e, (foldAt e inds .unrestricted).Allows (ξ e)) ↔
    (∀ i, ∀ e, ((τ i).constraint e).Allows (ξ e))
  constructor
  · intro h i e
    have hf := (hfoldAllows e inds .unrestricted (by simp [EdgeConstraint.Allows])
      (by intro j hj; exact h₀ j e) (ξ e)).mp (h e)
    exact hf.2 i (by simp [inds])
  · intro h e
    apply (hfoldAllows e inds .unrestricted (by simp [EdgeConstraint.Allows])
      (by intro j hj; exact h₀ j e) (ξ e)).mpr
    constructor
    · simp [EdgeConstraint.Allows]
    · intro i hi
      exact h i e

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
  classical
  let roots : Finset (Endpoint R g) := testRootEndpoints (g := g) scope t
  have hev : (explorationLeaf ξ roots L).Event ξ' := by
    simpa [roots, testLeaf] using h
  have hrunLeaf := (explorationLeaf_event_iff ξ ξ' roots L).mp hev
  have hrun : truncatedExploration ξ' roots L = truncatedExploration ξ roots L := hrunLeaf.1
  have hgiant : (testExploration ξ' scope t L).giant =
      (testExploration ξ scope t L).giant := by
    simpa [testExploration, roots] using congrArg ExploreState.giant hrun
  have hassignAll :
      ∀ t0, (testExploration ξ scope t0 L).giant = false →
        (testLeaf ξ scope t0 L).Event ξ' →
        ∀ a, Sum.inl a ∈ testRootEndpoints (g := g) scope t0 →
          (greedyMatching ξ).assignment a = (greedyMatching ξ').assignment a := by
    intro t0 hng0 hev0 a ha
    let roots0 : Finset (Endpoint R g) := testRootEndpoints (g := g) scope t0
    have hev0' : (explorationLeaf ξ roots0 L).Event ξ' := by
      simpa [roots0, testLeaf] using hev0
    have hbelow : agreesBelowClosure roots0 ξ ξ' :=
      nongiant_leaf_agreesBelow ξ ξ' roots0 L (by simpa [testExploration, roots0] using hng0) hev0'
    exact closure_determines_root_assignment ξ ξ' roots0 hbelow a ha
  have hsample :
      ∀ t0, (testExploration ξ scope t0 L).giant = false →
        (testLeaf ξ scope t0 L).Event ξ' →
        (sampleTestBad lab F scope (greedyMatching ξ') t0 ↔
          sampleTestBad lab F scope (greedyMatching ξ) t0) := by
    intro t0
    cases t0 with
    | predicate k =>
        dsimp [sampleTestBad, testFails]
        exact fun hng0 hev0 => by
          constructor
          · rintro ⟨ω, hF, hm⟩
            refine ⟨ω, hF, ?_⟩
            intro a ha
            rcases hm a ha with ⟨y, hy⟩
            have haroot : Sum.inl a ∈ testRootEndpoints (g := g) scope (.predicate k) := by
              simp [testRootEndpoints, testRoots, ha]
            exact ⟨y, (hassignAll (.predicate k) hng0 hev0 a haroot).trans hy⟩
          · rintro ⟨ω, hF, hm⟩
            refine ⟨ω, hF, ?_⟩
            intro a ha
            rcases hm a ha with ⟨y, hy⟩
            have haroot : Sum.inl a ∈ testRootEndpoints (g := g) scope (.predicate k) := by
              simp [testRootEndpoints, testRoots, ha]
            exact ⟨y, (hassignAll (.predicate k) hng0 hev0 a haroot).symm.trans hy⟩
    | singleton a =>
        dsimp [sampleTestBad]
        exact fun hng0 hev0 => by
          have haroot : Sum.inl a ∈ testRootEndpoints (g := g) scope (.singleton a) := by
            simp [testRootEndpoints, testRoots]
          have hA := hassignAll (.singleton a) hng0 hev0 a haroot
          change (¬ ∃ y o, (greedyMatching ξ').assignment a = some (y, o) ∧ lab a o = y) ↔
            (¬ ∃ y o, (greedyMatching ξ).assignment a = some (y, o) ∧ lab a o = y)
          simp only [← hA]
  by_cases hg : (testExploration ξ scope t L).giant = true
  · simp [leafBad, hgiant, hg]
  · have hng : (testExploration ξ scope t L).giant = false := by
      cases hh : (testExploration ξ scope t L).giant with
      | false => rfl
      | true => exact False.elim (hg hh)
    have hbad := hsample (t0 := t) hng h
    unfold leafBad
    rw [hgiant]
    simpa [hg] using hbad

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
