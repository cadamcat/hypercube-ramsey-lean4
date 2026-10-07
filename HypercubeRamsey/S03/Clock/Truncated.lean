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
  have hnextMaxReq (s : ExploreState R g) (u : Endpoint R g)
      (hn : nextPending s = some u) :
      ∀ v ∈ pendingEndpoints s, (s.request v).getD 0 ≤ (s.request u).getD 0 := by
    classical
    by_cases hp : (pendingEndpoints s).Nonempty
    · have hmax := (pendingEndpoints s).exists_max_image (pendingKey s) hp
      have heq : ((pendingEndpoints s).exists_max_image (pendingKey s) hp).choose = u := by
        simpa [nextPending, hp] using hn
      intro v hv
      have hkey : pendingKey s v ≤ pendingKey s u := by
        have h := hmax.choose_spec.2 v hv
        calc
          pendingKey s v ≤ pendingKey s ((pendingEndpoints s).exists_max_image (pendingKey s) hp).choose := h
          _ = pendingKey s u := by rw [heq]
      let N := Fintype.card (Endpoint R g)
      let qv := (s.request v).getD 0
      let qu := (s.request u).getD 0
      by_contra hnot
      have hlt : qu < qv := Nat.lt_of_not_ge hnot
      have hN : 0 < N := Fintype.card_pos_iff.mpr ⟨u⟩
      have hRankV : (Fintype.equivFin (Endpoint R g) v).val < N := (Fintype.equivFin (Endpoint R g) v).isLt
      have hRankU : (Fintype.equivFin (Endpoint R g) u).val < N := (Fintype.equivFin (Endpoint R g) u).isLt
      have hkeyU : pendingKey s u < (qu + 1) * N := by
        dsimp [pendingKey, N, qu]
        calc
          (s.request u).getD 0 * Fintype.card (Endpoint R g) +
              (Fintype.equivFin (Endpoint R g) u).val <
              (s.request u).getD 0 * Fintype.card (Endpoint R g) + Fintype.card (Endpoint R g) :=
            Nat.add_lt_add_left hRankU _
          _ = ((s.request u).getD 0 + 1) * Fintype.card (Endpoint R g) := by
            rw [Nat.add_mul, Nat.one_mul]
      have hmul : (qu + 1) * N ≤ qv * N :=
        Nat.mul_le_mul_right N (Nat.succ_le_of_lt hlt)
      have hkeyV : qv * N ≤ pendingKey s v := by
        dsimp [pendingKey, N, qv]
        omega
      have hcontra : pendingKey s u < pendingKey s v := lt_of_lt_of_le hkeyU (le_trans hmul hkeyV)
      exact (not_lt_of_ge hkey) hcontra
    · simp [nextPending, hp] at hn
  have hnextMaxReq (s : ExploreState R g) (u : Endpoint R g)
      (hn : nextPending s = some u) :
      ∀ v ∈ pendingEndpoints s, (s.request v).getD 0 ≤ (s.request u).getD 0 := by
    classical
    by_cases hp : (pendingEndpoints s).Nonempty
    · have hmax := (pendingEndpoints s).exists_max_image (pendingKey s) hp
      have heq : ((pendingEndpoints s).exists_max_image (pendingKey s) hp).choose = u := by
        simpa [nextPending, hp] using hn
      intro v hv
      have hkey : pendingKey s v ≤ pendingKey s u := by
        have h := hmax.choose_spec.2 v hv
        calc
          pendingKey s v ≤ pendingKey s ((pendingEndpoints s).exists_max_image (pendingKey s) hp).choose := h
          _ = pendingKey s u := by rw [heq]
      let N := Fintype.card (Endpoint R g)
      let qv := (s.request v).getD 0
      let qu := (s.request u).getD 0
      by_contra hnot
      have hlt : qu < qv := Nat.lt_of_not_ge hnot
      have hN : 0 < N := Fintype.card_pos_iff.mpr ⟨u⟩
      have hRankV : (Fintype.equivFin (Endpoint R g) v).val < N := (Fintype.equivFin (Endpoint R g) v).isLt
      have hRankU : (Fintype.equivFin (Endpoint R g) u).val < N := (Fintype.equivFin (Endpoint R g) u).isLt
      have hkeyU : pendingKey s u < (qu + 1) * N := by
        dsimp [pendingKey, N, qu]
        calc
          (s.request u).getD 0 * Fintype.card (Endpoint R g) +
              (Fintype.equivFin (Endpoint R g) u).val <
              (s.request u).getD 0 * Fintype.card (Endpoint R g) + Fintype.card (Endpoint R g) :=
            Nat.add_lt_add_left hRankU _
          _ = ((s.request u).getD 0 + 1) * Fintype.card (Endpoint R g) := by
            rw [Nat.add_mul, Nat.one_mul]
      have hmul : (qu + 1) * N ≤ qv * N :=
        Nat.mul_le_mul_right N (Nat.succ_le_of_lt hlt)
      have hkeyV : qv * N ≤ pendingKey s v := by
        dsimp [pendingKey, N, qv]
        omega
      have hcontra : pendingKey s u < pendingKey s v := lt_of_lt_of_le hkeyU (le_trans hmul hkeyV)
      exact (not_lt_of_ge hkey) hcontra
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

set_option maxHeartbeats 1000000
/-- L3.10b-complete (03:861–867): without a giant stop the exploration is the full closure, processed in
decreasing horizon order: every closure point `(u, h)` has `u` processed and every edge at `u` inspected at a
horizon at least `h`. -/
theorem truncatedExploration_complete {T : ℕ} {R : Type*} [Fintype R] [DecidableEq R] {g : ℕ}
    {Ω : R → Type*} (ξ : ClockField T R g Ω) (roots : Finset (Endpoint R g)) (L : ℕ)
    (hng : (truncatedExploration ξ roots L).giant = false) :
    ∀ u h, inClosureFrom ξ roots (u, h) → u ∈ (truncatedExploration ξ roots L).processed ∧
      ∀ e, EdgeIncident u e → ∃ H, (truncatedExploration ξ roots L).inspectedAt e = some H ∧ h ≤ H := by
  classical
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
  have hprocessedEndpoint (u : Endpoint R g) (s : ExploreState R g) :
      (processEndpoint ξ L u s).processed = insert u s.processed := by
    unfold processEndpoint
    rw [hprocessedFold]
  have hnextMem (s : ExploreState R g) (u : Endpoint R g)
      (hn : nextPending s = some u) : u ∈ pendingEndpoints s := by
    by_cases hp : (pendingEndpoints s).Nonempty
    · have hmax := (pendingEndpoints s).exists_max_image (pendingKey s) hp
      have heq : ((pendingEndpoints s).exists_max_image (pendingKey s) hp).choose = u := by
        simpa [nextPending, hp] using hn
      rw [← heq]
      exact hmax.choose_spec.1
    · simp [nextPending, hp] at hn
  have hnextMaxReq (s : ExploreState R g) (u : Endpoint R g)
      (hn : nextPending s = some u) :
      ∀ v ∈ pendingEndpoints s, (s.request v).getD 0 ≤ (s.request u).getD 0 := by
    classical
    by_cases hp : (pendingEndpoints s).Nonempty
    · have hmax := (pendingEndpoints s).exists_max_image (pendingKey s) hp
      have heq : ((pendingEndpoints s).exists_max_image (pendingKey s) hp).choose = u := by
        simpa [nextPending, hp] using hn
      intro v hv
      have hkey : pendingKey s v ≤ pendingKey s u := by
        calc
          pendingKey s v ≤ pendingKey s ((pendingEndpoints s).exists_max_image (pendingKey s) hp).choose :=
            hmax.choose_spec.2 v hv
          _ = pendingKey s u := by rw [heq]
      let N := Fintype.card (Endpoint R g)
      let qv := (s.request v).getD 0
      let qu := (s.request u).getD 0
      by_contra hnot
      have hlt : qu < qv := Nat.lt_of_not_ge hnot
      have hN : 0 < N := Fintype.card_pos_iff.mpr ⟨u⟩
      have hRankV : (Fintype.equivFin (Endpoint R g) v).val < N := (Fintype.equivFin _ v).isLt
      have hRankU : (Fintype.equivFin (Endpoint R g) u).val < N := (Fintype.equivFin _ u).isLt
      have hkeyU : pendingKey s u < (qu + 1) * N := by
        dsimp [pendingKey, N, qu]
        calc
          (s.request u).getD 0 * Fintype.card (Endpoint R g) +
              (Fintype.equivFin (Endpoint R g) u).val <
              (s.request u).getD 0 * Fintype.card (Endpoint R g) + Fintype.card (Endpoint R g) :=
            Nat.add_lt_add_left hRankU _
          _ = ((s.request u).getD 0 + 1) * Fintype.card (Endpoint R g) := by
            rw [Nat.add_mul, Nat.one_mul]
      have hmul : (qu + 1) * N ≤ qv * N := Nat.mul_le_mul_right N (Nat.succ_le_of_lt hlt)
      have hkeyV : qv * N ≤ pendingKey s v := by dsimp [pendingKey, N, qv]; omega
      exact (not_lt_of_ge hkey) (lt_of_lt_of_le hkeyU (le_trans hmul hkeyV))
    · simp [nextPending, hp] at hn
  have hrunNoPending : ∀ f (s : ExploreState R g),
      Fintype.card (Endpoint R g) ≤ s.processed.card + f →
      (exploreRun ξ L f s).giant = false →
      pendingEndpoints (exploreRun ξ L f s) = ∅ := by
    intro f
    induction f with
    | zero =>
        intro s hcard hng
        by_contra hne
        have hnon : (pendingEndpoints s).Nonempty := Finset.nonempty_iff_ne_empty.mpr hne
        rcases hnon with ⟨u, hu⟩
        have huNot : u ∉ s.processed := by
          have hu' : (s.request u).isSome ∧ u ∉ s.processed := by
            simpa [pendingEndpoints] using hu
          exact hu'.2
        have hsub : insert u s.processed ⊆ (Finset.univ : Finset (Endpoint R g)) := Finset.subset_univ _
        have hcardIns : (insert u s.processed).card = s.processed.card + 1 :=
          Finset.card_insert_of_notMem huNot
        have hcardAll := Finset.card_le_card hsub
        rw [Finset.card_univ, hcardIns] at hcardAll
        have hcard' : Fintype.card (Endpoint R g) ≤ s.processed.card := by
          simpa [exploreRun] using hcard
        omega
    | succ f ih =>
        intro s hcard hng
        by_cases hg : s.giant = true
        · simp [exploreRun, hg] at hng
        · have hfalse : s.giant = false := by cases hb : s.giant <;> simp_all
          cases hp : nextPending s with
          | none =>
              have hEmpty : pendingEndpoints s = ∅ := by
                by_contra hne
                have hnon : (pendingEndpoints s).Nonempty := Finset.nonempty_iff_ne_empty.mpr hne
                have hnext : nextPending s ≠ none := by simp [nextPending, hnon]
                exact hnext hp
              simpa [exploreRun, hfalse, hp] using hEmpty
          | some u =>
              have hmem := hnextMem s u hp
              have hmem' : (s.request u).isSome ∧ u ∉ s.processed := by
                simpa [pendingEndpoints] using hmem
              have hproc : u ∉ s.processed := hmem'.2
              have hcardStep :
                  (processEndpoint ξ L u s).processed.card = s.processed.card + 1 := by
                rw [hprocessedEndpoint]
                exact Finset.card_insert_of_notMem hproc
              have hcard' : Fintype.card (Endpoint R g) ≤
                  (processEndpoint ξ L u s).processed.card + f := by
                rw [hcardStep]
                omega
              have hng' : (exploreRun ξ L f (processEndpoint ξ L u s)).giant = false := by
                simpa [exploreRun, hfalse, hp] using hng
              have hEmpty := ih (processEndpoint ξ L u s) hcard' hng'
              simpa [exploreRun, hfalse, hp] using hEmpty
  have hNoPending : pendingEndpoints (truncatedExploration ξ roots L) = ∅ := by
    have hcard : Fintype.card (Endpoint R g) ≤
        (initExploreState T roots L).processed.card + Fintype.card (Endpoint R g) := by simp
    simpa [truncatedExploration] using hrunNoPending (Fintype.card (Endpoint R g))
      (initExploreState T roots L) hcard hng
  have hactiveProcessed :
      (truncatedExploration ξ roots L).active ⊆ (truncatedExploration ξ roots L).processed := by
    intro u hu
    by_contra hnot
    have hPending : u ∈ pendingEndpoints (truncatedExploration ξ roots L) := by
      have hReq : ((truncatedExploration ξ roots L).request u).isSome := by
        simpa [ExploreState.active] using hu
      have hmem : ((truncatedExploration ξ roots L).request u).isSome ∧
          u ∉ (truncatedExploration ξ roots L).processed := ⟨hReq, hnot⟩
      simpa [pendingEndpoints] using hmem
    rw [hNoPending] at hPending
    simp at hPending
  have hrequestGrowInspect (u : Endpoint R g) (h : ℕ) (s : ExploreState R g)
      (e : RowLabel R g) (v : Endpoint R g) (H : ℕ) (hv : s.request v = some H) :
      ∃ H', (inspectEdge ξ L u h s e).request v = some H' ∧ H ≤ H' := by
    by_cases hg : s.giant
    · exact ⟨H, by simpa [inspectEdge, hg] using hv, le_rfl⟩
    · have hgf : s.giant = false := by cases hb : s.giant <;> simp_all
      cases hk : edgeArrivalKey ξ e with
      | none => exact ⟨H, by simpa [inspectEdge, hgf, hk] using hv, le_rfl⟩
      | some k =>
          by_cases hkh : k < h
          · by_cases hproc : edgeOther u e ∈ s.processed
            · exact ⟨H, by simpa [inspectEdge, hgf, hk, hkh, hproc] using hv, le_rfl⟩
            · by_cases hvw : v = edgeOther u e
              · subst v
                refine ⟨max H k, ?_, le_max_left _ _⟩
                simp [inspectEdge, hgf, hk, hkh, hproc, hv, Function.update]
                split_ifs <;> simp_all [Function.update]
              · refine ⟨H, ?_, le_rfl⟩
                simp [inspectEdge, hgf, hk, hkh, hproc, hvw, hv]
                split_ifs <;> simp_all [Function.update]
          · exact ⟨H, by simpa [inspectEdge, hgf, hk, hkh] using hv, le_rfl⟩
  have hrequestGrowFold (u : Endpoint R g) (h : ℕ) (es : List (RowLabel R g))
      (s : ExploreState R g) (v : Endpoint R g) (H : ℕ) (hv : s.request v = some H) :
      ∃ H', (es.foldl (inspectEdge ξ L u h) s).request v = some H' ∧ H ≤ H' := by
    induction es generalizing s H with
    | nil => exact ⟨H, by simpa, le_rfl⟩
    | cons e es ih =>
        rw [List.foldl_cons]
        obtain ⟨H₁, h₁, hle₁⟩ := hrequestGrowInspect u h s e v H hv
        obtain ⟨H₂, h₂, hle₂⟩ := ih (inspectEdge ξ L u h s e) H₁ h₁
        exact ⟨H₂, h₂, le_trans hle₁ hle₂⟩
  have hrequestGrowProcess (s : ExploreState R g) (u : Endpoint R g) (v : Endpoint R g)
      (H : ℕ) (hv : s.request v = some H) :
      ∃ H', (processEndpoint ξ L u s).request v = some H' ∧ H ≤ H' := by
    unfold processEndpoint
    exact hrequestGrowFold u ((s.request u).getD 0) (incidentEdges u)
      { s with processed := insert u s.processed } v H hv
  have hrequestGrowRun : ∀ f (s : ExploreState R g) (v : Endpoint R g) (H : ℕ),
      s.request v = some H →
      ∃ H', (exploreRun ξ L f s).request v = some H' ∧ H ≤ H' := by
    intro f
    induction f with
    | zero => intro s v H hv; exact ⟨H, by simpa [exploreRun] using hv, le_rfl⟩
    | succ f ih =>
        intro s v H hv
        by_cases hg : s.giant
        · exact ⟨H, by simpa [exploreRun, hg] using hv, le_rfl⟩
        · cases hp : nextPending s with
          | none => exact ⟨H, by simpa [exploreRun, hg, hp] using hv, le_rfl⟩
          | some u =>
              obtain ⟨H₁, h₁, hle₁⟩ := hrequestGrowProcess s u v H hv
              obtain ⟨H₂, h₂, hle₂⟩ := ih (processEndpoint ξ L u s) v H₁ h₁
              exact ⟨H₂, by simpa [exploreRun, hg, hp] using h₂, le_trans hle₁ hle₂⟩
  have hrootRequest : ∀ r ∈ roots, ∃ H,
      (truncatedExploration ξ roots L).request r = some H ∧ rootHorizon T R g ≤ H := by
    intro r hr
    have hinit : (initExploreState T roots L).request r = some (rootHorizon T R g) := by
      simp [initExploreState, hr]
    obtain ⟨H, hH, hle⟩ := hrequestGrowRun (Fintype.card (Endpoint R g))
      (initExploreState T roots L) r (rootHorizon T R g) hinit
    exact ⟨H, by simpa [truncatedExploration] using hH, hle⟩
  have hrequestStableProcessedInspect (u : Endpoint R g) (h : ℕ) (s : ExploreState R g)
      (e : RowLabel R g) (v : Endpoint R g) (hv : v ∈ s.processed) :
      (inspectEdge ξ L u h s e).request v = s.request v := by
    by_cases hg : s.giant
    · simp [inspectEdge, hg]
    · have hgf : s.giant = false := by cases hb : s.giant <;> simp_all
      cases hk : edgeArrivalKey ξ e with
      | none => simp [inspectEdge, hgf, hk]
      | some k =>
          by_cases hkh : k < h
          · by_cases hproc : edgeOther u e ∈ s.processed
            · simp [inspectEdge, hg, hk, hkh, hproc]
            · by_cases hvw : v = edgeOther u e
              · subst v
                exact False.elim (hproc hv)
              · have hne : v ≠ edgeOther u e := hvw
                simp only [inspectEdge, hgf, hk, if_pos hkh, if_neg hproc]
                split_ifs <;>
                  simp only [ExploreState.request, Function.update_of_ne hne]
          · simp [inspectEdge, hgf, hk, hkh]
  have hrequestStableProcessedFold (u : Endpoint R g) (h : ℕ) (es : List (RowLabel R g))
      (s : ExploreState R g) (v : Endpoint R g) (hv : v ∈ s.processed) :
      (es.foldl (inspectEdge ξ L u h) s).request v = s.request v := by
    induction es generalizing s with
    | nil => rfl
    | cons e es ih =>
        rw [List.foldl_cons]
        have hv' : v ∈ (inspectEdge ξ L u h s e).processed := by
          rw [hprocessedInspect]
          exact hv
        rw [ih (inspectEdge ξ L u h s e) hv']
        exact hrequestStableProcessedInspect u h s e v hv
  have hrequestStableProcessedProcess (s : ExploreState R g) (u v : Endpoint R g)
      (hv : v ∈ s.processed) :
      (processEndpoint ξ L u s).request v = s.request v := by
    unfold processEndpoint
    exact hrequestStableProcessedFold u ((s.request u).getD 0) (incidentEdges u)
      { s with processed := insert u s.processed } v (Finset.mem_insert_of_mem hv)
  have hinspectAtGrow (u : Endpoint R g) (h : ℕ) (s : ExploreState R g)
      (e : RowLabel R g) (q : RowLabel R g) (H : ℕ) (hq : s.inspectedAt q = some H) :
      ∃ H', (inspectEdge ξ L u h s e).inspectedAt q = some H' ∧ H ≤ H' := by
    by_cases hg : s.giant
    · exact ⟨H, by simpa [inspectEdge, hg] using hq, le_rfl⟩
    · have hgf : s.giant = false := by cases hb : s.giant <;> simp_all
      by_cases hqe : q = e
      · subst q
        refine ⟨max H h, ?_, le_max_left _ _⟩
        cases hk : edgeArrivalKey ξ e <;>
          simp [inspectEdge, hgf, hk, hq] <;> split_ifs <;> simp [Function.update, hq]
      · refine ⟨H, ?_, le_rfl⟩
        cases hk : edgeArrivalKey ξ e <;>
          simp [inspectEdge, hgf, hk, hq, hqe] <;> split_ifs <;> simp [Function.update, hqe, hq]
  have hinspectAtGrowFold (u : Endpoint R g) (h : ℕ) (es : List (RowLabel R g))
      (s : ExploreState R g) (q : RowLabel R g) (H : ℕ) (hq : s.inspectedAt q = some H) :
      ∃ H', (es.foldl (inspectEdge ξ L u h) s).inspectedAt q = some H' ∧ H ≤ H' := by
    induction es generalizing s H with
    | nil => exact ⟨H, by simpa, le_rfl⟩
    | cons e es ih =>
        rw [List.foldl_cons]
        obtain ⟨H₁, h₁, hle₁⟩ := hinspectAtGrow u h s e q H hq
        obtain ⟨H₂, h₂, hle₂⟩ := ih (inspectEdge ξ L u h s e) H₁ h₁
        exact ⟨H₂, h₂, le_trans hle₁ hle₂⟩
  have hinspectAtGrowProcess (s : ExploreState R g) (u : Endpoint R g)
      (q : RowLabel R g) (H : ℕ) (hq : s.inspectedAt q = some H) :
      ∃ H', (processEndpoint ξ L u s).inspectedAt q = some H' ∧ H ≤ H' := by
    unfold processEndpoint
    exact hinspectAtGrowFold u ((s.request u).getD 0) (incidentEdges u)
      { s with processed := insert u s.processed } q H hq
  have hfoldFalseImp (u : Endpoint R g) (h : ℕ) (es : List (RowLabel R g))
      (s : ExploreState R g) (hout : (es.foldl (inspectEdge ξ L u h) s).giant = false) :
      s.giant = false := by
    induction es generalizing s with
    | nil => simpa using hout
    | cons e es ih =>
        rw [List.foldl_cons] at hout
        have hmid : (inspectEdge ξ L u h s e).giant = false :=
          ih (inspectEdge ξ L u h s e) hout
        cases hb : s.giant with
        | false => rfl
        | true => simp [inspectEdge, hb] at hmid
  have hfoldInspects (u : Endpoint R g) (h : ℕ) (es : List (RowLabel R g))
      (s : ExploreState R g) (hout : (es.foldl (inspectEdge ξ L u h) s).giant = false) :
      ∀ e ∈ es, ∃ H, (es.foldl (inspectEdge ξ L u h) s).inspectedAt e = some H ∧ h ≤ H := by
    induction es generalizing s with
    | nil => intro e he; simp at he
    | cons e es ih =>
        intro q hq
        rw [List.foldl_cons] at hout ⊢
        have hmid : (inspectEdge ξ L u h s e).giant = false := hfoldFalseImp u h es
          (inspectEdge ξ L u h s e) hout
        have hstart : s.giant = false := by
          cases hb : s.giant with
          | false => rfl
          | true => simp [inspectEdge, hb] at hmid
        rcases List.mem_cons.mp hq with heq | htail
        · subst q
          have hset : (inspectEdge ξ L u h s e).inspectedAt e =
              some (max ((s.inspectedAt e).getD 0) h) := by
            cases hk : edgeArrivalKey ξ e <;>
              simp [inspectEdge, hstart, hk] <;> split_ifs <;> simp [Function.update]
          obtain ⟨H, hH, hle⟩ := hinspectAtGrowFold u h es
            (inspectEdge ξ L u h s e) e (max ((s.inspectedAt e).getD 0) h) hset
          exact ⟨H, hH, le_trans (le_max_right _ _) hle⟩
        · exact ih (inspectEdge ξ L u h s e) hout q htail
  have hrequestBoundInspect (u : Endpoint R g) (h B : ℕ) (s : ExploreState R g)
      (e : RowLabel R g) (hB : h ≤ B)
      (hb : ∀ v, v ∉ s.processed → (s.request v).getD 0 ≤ B) :
      ∀ v, v ∉ (inspectEdge ξ L u h s e).processed →
        ((inspectEdge ξ L u h s e).request v).getD 0 ≤ B := by
    intro v hv
    rw [hprocessedInspect] at hv
    by_cases hg : s.giant
    · simpa [inspectEdge, hg] using hb v hv
    · have hfalse : s.giant = false := by cases hs : s.giant <;> simp_all
      cases hk : edgeArrivalKey ξ e with
      | none => simpa [inspectEdge, hfalse, hk] using hb v hv
      | some k =>
          by_cases hkh : k < h
          · by_cases hproc : edgeOther u e ∈ s.processed
            · simpa [inspectEdge, hfalse, hk, hkh, hproc] using hb v hv
            · by_cases hvw : v = edgeOther u e
              · subst v
                have hOld := hb (edgeOther u e) hproc
                have hmax : max ((s.request (edgeOther u e)).getD 0) k ≤ B :=
                  Nat.max_le.mpr ⟨hOld, by omega⟩
                simp [inspectEdge, hfalse, hk, hkh, hproc, Function.update, hmax]
                split_ifs <;> simp [Function.update, hmax]
              · simp only [inspectEdge, hfalse, hk, if_pos hkh, if_neg hproc]
                split_ifs <;>
                  simpa only [ExploreState.request, Function.update_of_ne hvw] using hb v hv
          · simpa [inspectEdge, hfalse, hk, hkh] using hb v hv
  have hrequestBoundFold (u : Endpoint R g) (h B : ℕ) (es : List (RowLabel R g))
      (s : ExploreState R g) (hB : h ≤ B)
      (hb : ∀ v, v ∉ s.processed → (s.request v).getD 0 ≤ B) :
      ∀ v, v ∉ (es.foldl (inspectEdge ξ L u h) s).processed →
        ((es.foldl (inspectEdge ξ L u h) s).request v).getD 0 ≤ B := by
    induction es generalizing s with
    | nil => exact hb
    | cons e es ih =>
        rw [List.foldl_cons]
        apply ih
        exact hrequestBoundInspect u h B s e hB hb
  have hrequestBoundProcess (s : ExploreState R g) (u : Endpoint R g) (H : ℕ)
      (hreq : s.request u = some H) (hn : nextPending s = some u) :
      ∀ v, v ∈ pendingEndpoints (processEndpoint ξ L u s) →
        ((processEndpoint ξ L u s).request v).getD 0 ≤ H := by
    have hstart : ∀ v,
        v ∉ ({ s with processed := insert u s.processed } : ExploreState R g).processed →
          (({ s with processed := insert u s.processed } : ExploreState R g).request v).getD 0 ≤ H := by
      intro v hv
      have hvnot : v ∉ s.processed := by
        simp only [ExploreState.processed, Finset.mem_insert, not_or] at hv
        exact hv.2
      cases hrv : s.request v with
      | none => simp [hrv]
      | some q =>
          have hpending : v ∈ pendingEndpoints s := by
            simp [pendingEndpoints, hrv, hvnot]
          have hmax := hnextMaxReq s u hn v hpending
          simpa [hrv, hreq] using hmax
    have hbound := hrequestBoundFold u H H (incidentEdges u)
      { s with processed := insert u s.processed } le_rfl hstart
    intro v hv
    have hvnotOut : v ∉ (processEndpoint ξ L u s).processed :=
      (Finset.mem_filter.mp hv).2.2
    have hprocEq := hprocessedEndpoint u s
    have hvnot : v ∉ (insert u s.processed) := by simpa [hprocEq] using hvnotOut
    have hvfold : v ∉
        ((incidentEdges u).foldl (inspectEdge ξ L u H)
          { s with processed := insert u s.processed }).processed := by
      rw [hprocessedFold]
      exact hvnot
    simpa [processEndpoint, hreq] using hbound v hvfold
  have hincidentMem (u : Endpoint R g) (e : RowLabel R g)
      (he : EdgeIncident u e) : e ∈ incidentEdges u := by
    cases u with
    | inl a =>
        cases e with
        | mk b y =>
            rcases he with hrow | hlabel
            · have hab : a = b := Sum.inl.inj hrow
              subst b
              exact List.mem_ofFn.mpr ⟨y, rfl⟩
            · cases hlabel
    | inr y =>
        cases e with
        | mk a z =>
            rcases he with hrow | hlabel
            · cases hrow
            · have hyz : y = z := Sum.inr.inj hlabel
              subst z
              refine List.mem_ofFn.mpr ⟨(Fintype.equivFin R a), ?_⟩
              simp [incidentEdges]
  have hfoldHitTarget (u : Endpoint R g) (h : ℕ) (es : List (RowLabel R g))
      (s : ExploreState R g) (targetEdge : RowLabel R g) (k : ℕ)
      (hm : targetEdge ∈ es) (hk : edgeArrivalKey ξ targetEdge = some k)
      (hkh : k < h) (hproc : edgeOther u targetEdge ∉ s.processed)
      (hout : (es.foldl (inspectEdge ξ L u h) s).giant = false) :
      ∃ H, (es.foldl (inspectEdge ξ L u h) s).request (edgeOther u targetEdge) = some H ∧ k ≤ H := by
    induction es generalizing s with
    | nil => simp at hm
    | cons e es ih =>
        rw [List.foldl_cons] at hout ⊢
        have hmid : (inspectEdge ξ L u h s e).giant = false :=
          hfoldFalseImp u h es (inspectEdge ξ L u h s e) hout
        have hstart : s.giant = false := by
          cases hb : s.giant with
          | false => rfl
          | true => simp [inspectEdge, hb] at hmid
        rcases List.mem_cons.mp hm with heq | htail
        · subst e
          have hstep : (inspectEdge ξ L u h s targetEdge).request (edgeOther u targetEdge) =
              some (max ((s.request (edgeOther u targetEdge)).getD 0) k) := by
            simp [inspectEdge, hstart, hk, hkh, hproc, Function.update]
            split_ifs <;> simp [Function.update]
          obtain ⟨H, hH, hle⟩ := hrequestGrowFold u h es
            (inspectEdge ξ L u h s targetEdge) (edgeOther u targetEdge)
            (max ((s.request (edgeOther u targetEdge)).getD 0) k) hstep
          exact ⟨H, hH, le_trans (le_max_right _ _) hle⟩
        · have hproc' : edgeOther u targetEdge ∉ (inspectEdge ξ L u h s e).processed := by
            simpa [hprocessedInspect] using hproc
          exact ih (inspectEdge ξ L u h s e) htail hproc' hout
  have hrequestStableProcessSelf (s : ExploreState R g) (u : Endpoint R g) :
      (processEndpoint ξ L u s).request u = s.request u := by
    unfold processEndpoint
    exact hrequestStableProcessedFold u ((s.request u).getD 0) (incidentEdges u)
      { s with processed := insert u s.processed } u (Finset.mem_insert_self u s.processed)
  have hprocessHitTarget (s : ExploreState R g) (u : Endpoint R g) (H : ℕ)
      (hreq : s.request u = some H) (hn : nextPending s = some u)
      (hOrder : ∀ p ∈ s.processed, ∀ q ∈ pendingEndpoints s,
        (s.request q).getD 0 ≤ (s.request p).getD 0)
      (hProcSome : ∀ p ∈ s.processed, ∃ Q, s.request p = some Q)
      (hout : (processEndpoint ξ L u s).giant = false) :
      ∀ e, EdgeIncident u e → ∀ k, edgeArrivalKey ξ e = some k → k < H →
        ∃ Q, (processEndpoint ξ L u s).request (edgeOther u e) = some Q ∧ k ≤ Q := by
    intro e he k hk hkh
    let target := edgeOther u e
    by_cases htarget : target ∈ s.processed
    · obtain ⟨Q, hQ⟩ := hProcSome target htarget
      have huPending : u ∈ pendingEndpoints s := hnextMem s u hn
      have horder := hOrder target htarget u huPending
      have hstable := hrequestStableProcessedProcess s u target htarget
      refine ⟨Q, ?_, ?_⟩
      · rw [hstable]
        exact hQ
      · have hUget : (s.request u).getD 0 = H := by simp [hreq]
        have hTget : (s.request target).getD 0 = Q := by simp [hQ]
        omega
    · have htargetNe : target ≠ u := by
        dsimp [target]
        cases u <;> simp [edgeOther]
      have htargetStart : target ∉ insert u s.processed := by
        simp only [Finset.mem_insert]
        intro hmem
        rcases hmem with heq | hmem
        · exact htargetNe heq
        · exact htarget hmem
      have heMem : e ∈ incidentEdges u := hincidentMem u e he
      have houtFold :
          ((incidentEdges u).foldl (inspectEdge ξ L u H)
            { s with processed := insert u s.processed }).giant = false := by
        simpa [processEndpoint, hreq] using hout
      obtain ⟨Q, hQ, hle⟩ := hfoldHitTarget u H (incidentEdges u)
        { s with processed := insert u s.processed } e k heMem hk hkh htargetStart houtFold
      exact ⟨Q, by simpa [processEndpoint, hreq] using hQ, hle⟩
  let runInv : ExploreState R g → Prop := fun s =>
    (∀ r, r ∈ roots → ∃ H, s.request r = some H ∧ rootHorizon T R g ≤ H) ∧
    (∀ p, p ∈ s.processed → ∃ H, s.request p = some H) ∧
    (∀ p, p ∈ s.processed → ∀ q, q ∈ pendingEndpoints s →
      (s.request q).getD 0 ≤ (s.request p).getD 0) ∧
    (s.giant = false → ∀ p, p ∈ s.processed → ∀ e, EdgeIncident p e →
      ∀ k, edgeArrivalKey ξ e = some k → k < (s.request p).getD 0 →
        ∃ Q, s.request (edgeOther p e) = some Q ∧ k ≤ Q) ∧
    (s.giant = false → ∀ p, p ∈ s.processed → ∀ e, EdgeIncident p e →
      ∃ H, s.inspectedAt e = some H ∧ (s.request p).getD 0 ≤ H)
  have hrequestStableProcessSelf (s : ExploreState R g) (u : Endpoint R g) :
      (processEndpoint ξ L u s).request u = s.request u := by
    unfold processEndpoint
    exact hrequestStableProcessedFold u ((s.request u).getD 0) (incidentEdges u)
      { s with processed := insert u s.processed } u (Finset.mem_insert_self u s.processed)
  have hprocessInv (s : ExploreState R g) (u : Endpoint R g) (H : ℕ)
      (hreq : s.request u = some H) (hn : nextPending s = some u) (hs : runInv s) :
      runInv (processEndpoint ξ L u s) := by
    dsimp [runInv]
    have huPending : u ∈ pendingEndpoints s := hnextMem s u hn
    have hprocEq := hprocessedEndpoint u s
    refine ⟨?_, ?_, ?_, ?_, ?_⟩
    · intro r hr
      obtain ⟨H₀, h₀, hle₀⟩ := hs.1 r hr
      obtain ⟨H₁, h₁, hle₁⟩ := hrequestGrowProcess s u r H₀ h₀
      exact ⟨H₁, h₁, le_trans hle₀ hle₁⟩
    · intro p hp
      have hp' : p ∈ insert u s.processed := by simpa [hprocEq] using hp
      simp only [Finset.mem_insert] at hp'
      rcases hp' with hpEq | hpOld
      · subst p
        exact ⟨H, by rw [hrequestStableProcessSelf]; exact hreq⟩
      · obtain ⟨Q, hQ⟩ := hs.2.1 p hpOld
        exact ⟨Q, by rw [hrequestStableProcessedProcess s u p hpOld]; exact hQ⟩
    · intro p hp q hq
      have hp' : p ∈ insert u s.processed := by simpa [hprocEq] using hp
      simp only [Finset.mem_insert] at hp'
      have hBound : ((processEndpoint ξ L u s).request q).getD 0 ≤ H :=
        hrequestBoundProcess s u H hreq hn q hq
      rcases hp' with hpEq | hpOld
      · subst p
        have hSelf := hrequestStableProcessSelf s u
        simpa [hSelf, hreq] using hBound
      · have hOldOrd := hs.2.2.1 p hpOld u huPending
        have hStable := hrequestStableProcessedProcess s u p hpOld
        have hEqGet : (s.request p).getD 0 =
            ((processEndpoint ξ L u s).request p).getD 0 :=
          congrArg (fun q : Option ℕ => q.getD 0) hStable.symm
        have hOld : H ≤ (s.request p).getD 0 := by simpa [hreq] using hOldOrd
        exact le_trans hBound (le_trans hOld (le_of_eq hEqGet))
    · intro houtFalse p hp e he k hk hkh
      have hfoldFalse :
          ((incidentEdges u).foldl (inspectEdge ξ L u ((s.request u).getD 0))
            { s with processed := insert u s.processed }).giant = false := by
        simpa [processEndpoint] using houtFalse
      have hsFalse : s.giant = false := by
        have := hfoldFalseImp u ((s.request u).getD 0) (incidentEdges u)
          { s with processed := insert u s.processed } hfoldFalse
        simpa using this
      have hp' : p ∈ insert u s.processed := by simpa [hprocEq] using hp
      simp only [Finset.mem_insert] at hp'
      rcases hp' with hpEq | hpOld
      · subst p
        have hSelf := hrequestStableProcessSelf s u
        have hkh' : k < H := by simpa [hSelf, hreq] using hkh
        exact hprocessHitTarget s u H hreq hn hs.2.2.1 hs.2.1 houtFalse e he k hk hkh'
      · have hStable := hrequestStableProcessedProcess s u p hpOld
        have hkh' : k < (s.request p).getD 0 := by simpa [hStable] using hkh
        obtain ⟨Q, hQ, hleQ⟩ := hs.2.2.2.1 hsFalse p hpOld e he k hk hkh'
        obtain ⟨Q', hQ', hle'⟩ := hrequestGrowProcess s u (edgeOther p e) Q hQ
        exact ⟨Q', hQ', le_trans hleQ hle'⟩
    · intro houtFalse p hp e he
      have hfoldFalse :
          ((incidentEdges u).foldl (inspectEdge ξ L u ((s.request u).getD 0))
            { s with processed := insert u s.processed }).giant = false := by
        simpa [processEndpoint] using houtFalse
      have hsFalse : s.giant = false := by
        have := hfoldFalseImp u ((s.request u).getD 0) (incidentEdges u)
          { s with processed := insert u s.processed } hfoldFalse
        simpa using this
      have hp' : p ∈ insert u s.processed := by simpa [hprocEq] using hp
      simp only [Finset.mem_insert] at hp'
      rcases hp' with hpEq | hpOld
      · subst p
        have hReqSelf := hrequestStableProcessSelf s u
        have hReqSome : (processEndpoint ξ L u s).request u = some H := by rw [hReqSelf, hreq]
        have hMem : e ∈ incidentEdges u := hincidentMem u e he
        have hfoldFalseH :
            ((incidentEdges u).foldl (inspectEdge ξ L u H)
              { s with processed := insert u s.processed }).giant = false := by
          simpa [hreq] using hfoldFalse
        obtain ⟨H₁, hAt, hle⟩ := hfoldInspects u H (incidentEdges u)
          { s with processed := insert u s.processed } hfoldFalseH e hMem
        have hAt' : (processEndpoint ξ L u s).inspectedAt e = some H₁ := by
          simpa [processEndpoint, hreq] using hAt
        have hle' : H ≤ H₁ := by simpa [hreq] using hle
        exact ⟨H₁, hAt', by simpa [hReqSome] using hle'⟩
      · obtain ⟨H₁, hAt, hle⟩ := hs.2.2.2.2 hsFalse p hpOld e he
        obtain ⟨H₂, hAt₂, hle₂⟩ := hinspectAtGrowProcess s u e H₁ hAt
        have hStable := hrequestStableProcessedProcess s u p hpOld
        exact ⟨H₂, hAt₂, le_trans (by simpa [hStable] using hle) hle₂⟩
  have hRunAll : ∀ f (s : ExploreState R g), runInv s → runInv (exploreRun ξ L f s) := by
    intro f
    induction f with
    | zero => intro s hs; simpa [exploreRun] using hs
    | succ f ih =>
        intro s hs
        by_cases hg : s.giant = true
        · simpa [exploreRun, hg] using hs
        · have hfalse : s.giant = false := by
            cases hb : s.giant with
            | false => rfl
            | true => exact False.elim (hg hb)
          cases hp : nextPending s with
          | none => simpa [exploreRun, hfalse, hp] using hs
          | some u =>
              have hu := hnextMem s u hp
              have hu' : (s.request u).isSome ∧ u ∉ s.processed := by
                simpa [pendingEndpoints] using hu
              cases hreq : s.request u with
              | none => simp [hreq] at hu'
              | some H =>
                  have hmid := hprocessInv s u H hreq hp hs
                  have htail := ih (processEndpoint ξ L u s) hmid
                  simpa [exploreRun, hfalse, hp] using htail
  have hInitInv : runInv (initExploreState T roots L) := by
    dsimp [runInv]
    constructor
    · intro r hr
      exact ⟨rootHorizon T R g, by simp [initExploreState, hr], le_rfl⟩
    constructor
    · intro p hp
      simp [initExploreState] at hp
    constructor
    · intro p hp
      simp [initExploreState] at hp
    constructor
    · intro hg p hp
      simp [initExploreState] at hp
    · intro hg p hp
      simp [initExploreState] at hp
  have hFinalInv : runInv (truncatedExploration ξ roots L) := by
    simpa [truncatedExploration] using
      hRunAll (Fintype.card (Endpoint R g)) (initExploreState T roots L) hInitInv
  have harrivalKey (c : ClockCandidate T R g Ω) (hc : candidateIsArrival ξ c) :
      edgeArrivalKey ξ (c.1, c.2.1) = some (eventPriority c) := by
    rcases c with ⟨a, y, t, o⟩
    cases hξ : ξ (a, y) with
    | noArrival => simp [candidateIsArrival, hξ] at hc
    | tick t' o' =>
        have hEq : MeshClockValue.tick t' o' = MeshClockValue.tick t o := by
          simpa [candidateIsArrival, hξ] using hc
        rcases MeshClockValue.tick.inj hEq with ⟨rfl, rfl⟩
        simp [edgeArrivalKey, hξ, eventPriority]
  have hPathBound (r : Endpoint R g) (hr : r ∈ roots) :
      ∀ z : BackwardPoint T R g,
        Relation.ReflTransGen (backwardStep ξ) (r, rootHorizon T R g) z →
          ∃ H, (truncatedExploration ξ roots L).request z.1 = some H ∧ z.2 ≤ H := by
    intro z path
    induction path with
    | refl =>
        obtain ⟨H, hReq, hLe⟩ := hFinalInv.1 r hr
        exact ⟨H, by simpa using hReq, by simpa using hLe⟩
    | @tail b c path hstep ih =>
        obtain ⟨Hsrc, hSrcReq, hSrcLe⟩ := ih
        rcases hstep with ⟨cand, hcand, hkey, hdest, hends⟩
        have hsrcSome : (truncatedExploration ξ roots L).request b.1 = some Hsrc := hSrcReq
        have hsrcActive : b.1 ∈ (truncatedExploration ξ roots L).active := by
          simpa [ExploreState.active, hsrcSome]
        have hsrcProcessed := hactiveProcessed hsrcActive
        have hkeySource : eventPriority cand < Hsrc := by omega
        have hkeyTarget : c.2 = eventPriority cand := by simpa using hdest
        have hArrival := harrivalKey cand hcand
        rcases hends with ⟨hSrc, hDst⟩ | ⟨hSrc, hDst⟩
        · have hsource : b.1 = Sum.inl cand.1 := hSrc
          have htarget : c.1 = Sum.inr cand.2.1 := hDst
          have hSourceReq :
              (truncatedExploration ξ roots L).request (Sum.inl cand.1) = some Hsrc := by
            simpa [hsource] using hSrcReq
          have hSourceProc : Sum.inl cand.1 ∈ (truncatedExploration ξ roots L).processed := by
            simpa [hsource] using hsrcProcessed
          have hkeyLeReq : eventPriority cand <
              ((truncatedExploration ξ roots L).request (Sum.inl cand.1)).getD 0 := by
            simpa [hSourceReq] using hkeySource
          have hCov := hFinalInv.2.2.2.1 hng (Sum.inl cand.1) hSourceProc
            (cand.1, cand.2.1) (Or.inl rfl) (eventPriority cand) hArrival
            hkeyLeReq
          rcases hCov with ⟨Q, hQ, hQle⟩
          have hQtarget :
              (truncatedExploration ξ roots L).request c.1 = some Q := by
            simpa [htarget, edgeOther] using hQ
          exact ⟨Q, hQtarget, by omega⟩
        · have hsource : b.1 = Sum.inr cand.2.1 := hSrc
          have htarget : c.1 = Sum.inl cand.1 := hDst
          have hSourceProc : Sum.inr cand.2.1 ∈ (truncatedExploration ξ roots L).processed := by
            simpa [hsource] using hsrcProcessed
          have hSourceReq :
              (truncatedExploration ξ roots L).request (Sum.inr cand.2.1) = some Hsrc := by
            simpa [hsource] using hSrcReq
          have hkeyLeReq : eventPriority cand <
              ((truncatedExploration ξ roots L).request (Sum.inr cand.2.1)).getD 0 := by
            simpa [hSourceReq] using hkeySource
          have hCov := hFinalInv.2.2.2.1 hng (Sum.inr cand.2.1) hSourceProc
            (cand.1, cand.2.1) (Or.inr rfl) (eventPriority cand) hArrival
            hkeyLeReq
          rcases hCov with ⟨Q, hQ, hQle⟩
          have hQtarget :
              (truncatedExploration ξ roots L).request c.1 = some Q := by
            simpa [htarget, edgeOther] using hQ
          exact ⟨Q, hQtarget, by omega⟩
  have hReachBound (u : Endpoint R g) (h : ℕ)
      (hcl : inClosureFrom ξ roots (u, h)) :
      ∃ H, (truncatedExploration ξ roots L).request u = some H ∧ h ≤ H := by
    rcases hcl with ⟨r, hr, path⟩
    exact hPathBound r hr (u, h) path
  intro u h hcl
  obtain ⟨Hreq, hReq, hReqLe⟩ := hReachBound u h hcl
  have hActive : u ∈ (truncatedExploration ξ roots L).active := by
    simpa [ExploreState.active, hReq]
  have hProcessed := hactiveProcessed hActive
  refine ⟨hProcessed, ?_⟩
  intro e he
  obtain ⟨Hins, hAt, hAtLe⟩ := hFinalInv.2.2.2.2 hng u hProcessed e he
  exact ⟨Hins, hAt, le_trans hReqLe (by simpa [hReq] using hAtLe)⟩

set_option maxHeartbeats 200000

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

set_option maxHeartbeats 1000000 in
/-- L3.10c-rect (03:878–884, "Every realization in this rectangle follows the same inspections and reaches the
same leaf"): a clock field lies in the leaf of `ξ` exactly when its own run equals the run of `ξ` and it reaches
the same leaf. -/
theorem explorationLeaf_event_iff {T : ℕ} {R : Type*} [Fintype R] [DecidableEq R] {g : ℕ}
    {Ω : R → Type*} (ξ ξ' : ClockField T R g Ω) (roots : Finset (Endpoint R g)) (L : ℕ) :
    (explorationLeaf ξ roots L).Event ξ' ↔
      truncatedExploration ξ' roots L = truncatedExploration ξ roots L ∧
        explorationLeaf ξ' roots L = explorationLeaf ξ roots L := by
  classical
  have hself (ζ : ClockField T R g Ω) : (explorationLeaf ζ roots L).Event ζ := by
    intro e
    cases hAt : (truncatedExploration ζ roots L).inspectedAt e with
    | none => simp [explorationLeaf, leafConstraint, hAt, EdgeConstraint.Allows]
    | some H =>
        cases hζ : ζ e with
        | noArrival => simp [explorationLeaf, leafConstraint, hAt, hζ, EdgeConstraint.Allows]
        | tick t o =>
            by_cases hkey : eventPriority (⟨e.1, e.2, t, o⟩ : ClockCandidate T R g Ω) < H
            · simp [explorationLeaf, leafConstraint, hAt, hζ, hkey, EdgeConstraint.Allows]
            · have hcut : (edgeCutoff T H e).val ≤ t.val ↔
                  H ≤ eventPriority (⟨e.1, e.2, t, o⟩ : ClockCandidate T R g Ω) := by
                simpa [edgeCutoff, qClockCutoffValue] using
                  (qClockCutoffValue_le_iff (T := T) (R := R) (g := g) (H := H)
                    e.1 e.2 t o)
              have hle : H ≤ eventPriority (⟨e.1, e.2, t, o⟩ : ClockCandidate T R g Ω) :=
                Nat.le_of_not_gt hkey
              simp [explorationLeaf, leafConstraint, hAt, hζ, hkey, EdgeConstraint.Allows,
                hcut.mpr hle]
  let finalState := truncatedExploration ξ roots L
  have hNoEarly (H : ℕ) (e : RowLabel R g) (ζ : ClockField T R g Ω)
      (hall : (EdgeConstraint.absentBefore (edgeCutoff T H e)).Allows (ζ e))
      (t : Fin T) (o : Ω e.1)
      (hkey : eventPriority (⟨e.1, e.2, t, o⟩ : ClockCandidate T R g Ω) < H) :
      ζ e ≠ .tick t o := by
    intro heq
    have hcut : (edgeCutoff T H e).val ≤ t.val ↔
        H ≤ eventPriority (⟨e.1, e.2, t, o⟩ : ClockCandidate T R g Ω) := by
      simpa [edgeCutoff, qClockCutoffValue] using
        (qClockCutoffValue_le_iff (T := T) (R := R) (g := g) (H := H) e.1 e.2 t o)
    have hcutTick : (edgeCutoff T H e).val ≤ t.val := by
      simpa [EdgeConstraint.Allows, heq] using hall
    omega
  have hinspectAtGrow (u : Endpoint R g) (h : ℕ) (s : ExploreState R g)
      (e q : RowLabel R g) (H : ℕ) (hq : s.inspectedAt q = some H) :
      ∃ H', (inspectEdge ξ L u h s e).inspectedAt q = some H' ∧ H ≤ H' := by
    by_cases hg : s.giant
    · exact ⟨H, by simpa [inspectEdge, hg] using hq, le_rfl⟩
    · have hgf : s.giant = false := by cases hb : s.giant <;> simp_all
      by_cases hqe : q = e
      · subst q
        refine ⟨max H h, ?_, le_max_left _ _⟩
        cases hk : edgeArrivalKey ξ e <;>
          simp [inspectEdge, hgf, hk, hq] <;> split_ifs <;> simp [Function.update, hq]
      · refine ⟨H, ?_, le_rfl⟩
        cases hk : edgeArrivalKey ξ e <;>
          simp [inspectEdge, hgf, hk, hq, hqe] <;> split_ifs <;> simp [Function.update, hqe, hq]
  have hinspectAtGrowFold (u : Endpoint R g) (h : ℕ) (es : List (RowLabel R g))
      (s : ExploreState R g) (q : RowLabel R g) (H : ℕ) (hq : s.inspectedAt q = some H) :
      ∃ H', (es.foldl (inspectEdge ξ L u h) s).inspectedAt q = some H' ∧ H ≤ H' := by
    induction es generalizing s H with
    | nil => exact ⟨H, by simpa, le_rfl⟩
    | cons e es ih =>
        rw [List.foldl_cons]
        obtain ⟨H₁, h₁, hle₁⟩ := hinspectAtGrow u h s e q H hq
        obtain ⟨H₂, h₂, hle₂⟩ := ih (inspectEdge ξ L u h s e) H₁ h₁
        exact ⟨H₂, h₂, le_trans hle₁ hle₂⟩
  have hinspectAtGrowProcess (s : ExploreState R g) (u : Endpoint R g)
      (q : RowLabel R g) (H : ℕ) (hq : s.inspectedAt q = some H) :
      ∃ H', (processEndpoint ξ L u s).inspectedAt q = some H' ∧ H ≤ H' := by
    unfold processEndpoint
    exact hinspectAtGrowFold u ((s.request u).getD 0) (incidentEdges u)
      { s with processed := insert u s.processed } q H hq
  have hinspectAtGrowRun : ∀ f (s : ExploreState R g) (q : RowLabel R g) (H : ℕ),
      s.inspectedAt q = some H →
      ∃ H', (exploreRun ξ L f s).inspectedAt q = some H' ∧ H ≤ H' := by
    intro f
    induction f with
    | zero => intro s q H hq; exact ⟨H, by simpa [exploreRun] using hq, le_rfl⟩
    | succ f ih =>
        intro s q H hq
        by_cases hg : s.giant
        · exact ⟨H, by simpa [exploreRun, hg] using hq, le_rfl⟩
        · cases hp : nextPending s with
          | none => exact ⟨H, by simpa [exploreRun, hg, hp] using hq, le_rfl⟩
          | some u =>
              obtain ⟨H₁, h₁, hle₁⟩ := hinspectAtGrowProcess s u q H hq
              obtain ⟨H₂, h₂, hle₂⟩ := ih (processEndpoint ξ L u s) q H₁ h₁
              exact ⟨H₂, by simpa [exploreRun, hg, hp] using h₂, le_trans hle₁ hle₂⟩
  have hinspectEdgeEq (u : Endpoint R g) (h : ℕ) (s : ExploreState R g)
      (e : RowLabel R g) (hs : s.giant = false) (H : ℕ)
      (hAt : finalState.inspectedAt e = some H) (hle : h ≤ H)
      (hev : (explorationLeaf ξ roots L).Event ξ') :
      inspectEdge ξ L u h s e = inspectEdge ξ' L u h s e := by
    have hbaseEvent := hself ξ e
    have hotherEvent := hev e
    cases hξ : ξ e with
    | noArrival =>
        have hBaseAbs : (EdgeConstraint.absentBefore (edgeCutoff T H e)).Allows (ξ e) := by
          simp [hξ, EdgeConstraint.Allows]
        have hConstraint : (explorationLeaf ξ roots L).constraint e =
            .absentBefore (edgeCutoff T H e) := by
          simp [explorationLeaf, leafConstraint, finalState, hAt, hξ]
        have hPrimeAbs : (EdgeConstraint.absentBefore (edgeCutoff T H e)).Allows (ξ' e) := by
          simpa [hConstraint] using hotherEvent
        cases hξ' : ξ' e with
        | noArrival => simp [inspectEdge, hs, edgeArrivalKey, hξ, hξ']
        | tick t o =>
            have hnot : ¬ eventPriority (⟨e.1, e.2, t, o⟩ : ClockCandidate T R g Ω) < h := by
              intro hkey
              have hkeyH := lt_of_lt_of_le hkey hle
              exact (hNoEarly H e ξ' hPrimeAbs t o hkeyH) hξ'
            simp [inspectEdge, hs, edgeArrivalKey, hξ, hξ', hnot]
    | tick t o =>
        let c : ClockCandidate T R g Ω := ⟨e.1, e.2, t, o⟩
        by_cases hkey : eventPriority c < H
        · have hConstraint : (explorationLeaf ξ roots L).constraint e = .exactArrival t o := by
            simp [explorationLeaf, leafConstraint, finalState, hAt, hξ, c, hkey]
          have hξ' : ξ' e = .tick t o := by
            simpa [hConstraint, EdgeConstraint.Allows] using hotherEvent
          simp [inspectEdge, hs, edgeArrivalKey, hξ, hξ', c]
        · have hBaseAbs : (EdgeConstraint.absentBefore (edgeCutoff T H e)).Allows (ξ e) := by
            have hConstraint : (explorationLeaf ξ roots L).constraint e =
                .absentBefore (edgeCutoff T H e) := by
              simp [explorationLeaf, leafConstraint, finalState, hAt, hξ, c, hkey]
            simpa [hConstraint] using hbaseEvent
          have hConstraint : (explorationLeaf ξ roots L).constraint e =
              .absentBefore (edgeCutoff T H e) := by
            simp [explorationLeaf, leafConstraint, finalState, hAt, hξ, c, hkey]
          have hPrimeAbs : (EdgeConstraint.absentBefore (edgeCutoff T H e)).Allows (ξ' e) := by
            simpa [hConstraint] using hotherEvent
          have hnotBase : ¬ eventPriority c < h := by omega
          have hnotBase' :
              ¬ eventPriority (⟨e.1, e.2, t, o⟩ : ClockCandidate T R g Ω) < h := by
            simpa [c] using hnotBase
          cases hξ' : ξ' e with
          | noArrival =>
              simp [inspectEdge, hs, edgeArrivalKey, hξ, hξ', hnotBase', c]
          | tick t' o' =>
              have hnotPrime :
                  ¬ eventPriority (⟨e.1, e.2, t', o'⟩ : ClockCandidate T R g Ω) < h := by
                intro hkey'
                have hkeyH' := lt_of_lt_of_le hkey' hle
                exact (hNoEarly H e ξ' hPrimeAbs t' o' hkeyH') hξ'
              simp [inspectEdge, hs, edgeArrivalKey, hξ, hξ', hnotBase', hnotPrime, c]
  have hFoldSim (u : Endpoint R g) (h : ℕ) (es : List (RowLabel R g))
      (s : ExploreState R g) (f : ℕ)
      (hev : (explorationLeaf ξ roots L).Event ξ')
      (hfuture : exploreRun ξ L f (es.foldl (inspectEdge ξ L u h) s) = finalState) :
      es.foldl (inspectEdge ξ L u h) s = es.foldl (inspectEdge ξ' L u h) s := by
    induction es generalizing s with
    | nil => rfl
    | cons e es ih =>
        rw [List.foldl_cons] at hfuture ⊢
        by_cases hg : s.giant = true
        · have hfuture' : exploreRun ξ L f (es.foldl (inspectEdge ξ L u h) s) = finalState := by
            simpa [inspectEdge, hg] using hfuture
          have htail := ih s hfuture'
          simpa [inspectEdge, hg] using htail
        · have hfalse : s.giant = false := by
            cases hb : s.giant with
            | false => rfl
            | true => exact False.elim (hg hb)
          have hset : (inspectEdge ξ L u h s e).inspectedAt e =
              some (max ((s.inspectedAt e).getD 0) h) := by
            cases hk : edgeArrivalKey ξ e <;>
              simp [inspectEdge, hfalse, hk] <;> split_ifs <;> simp [Function.update]
          obtain ⟨Hmid, hAtMid, hleMid⟩ := hinspectAtGrowFold u h es
            (inspectEdge ξ L u h s e) e (max ((s.inspectedAt e).getD 0) h) hset
          obtain ⟨H, hAtRun, hleRun⟩ := hinspectAtGrowRun f
            (es.foldl (inspectEdge ξ L u h) (inspectEdge ξ L u h s e)) e Hmid hAtMid
          have hAt : finalState.inspectedAt e = some H := by
            rw [← hfuture]
            exact hAtRun
          have hHoriz : h ≤ H := le_trans (le_max_right _ _) (le_trans hleMid hleRun)
          have hEq := hinspectEdgeEq u h s e hfalse H hAt hHoriz hev
          have hfuture' :
              exploreRun ξ L f (es.foldl (inspectEdge ξ L u h) (inspectEdge ξ' L u h s e)) =
                finalState := by
            rw [← hEq]
            exact hfuture
          have htail := ih (inspectEdge ξ' L u h s e) hfuture'
          rw [List.foldl_cons, hEq]
          exact htail
  have hProcessSim (u : Endpoint R g) (s : ExploreState R g) (f : ℕ)
      (hev : (explorationLeaf ξ roots L).Event ξ')
      (hfuture : exploreRun ξ L f (processEndpoint ξ L u s) = finalState) :
      processEndpoint ξ L u s = processEndpoint ξ' L u s := by
    have hfuture' :
        exploreRun ξ L f
          ((incidentEdges u).foldl (inspectEdge ξ L u ((s.request u).getD 0))
            { s with processed := insert u s.processed }) = finalState := by
      change exploreRun ξ L f (processEndpoint ξ L u s) = finalState
      exact hfuture
    exact hFoldSim u ((s.request u).getD 0) (incidentEdges u)
      { s with processed := insert u s.processed } f hev hfuture'
  have hRunSim : ∀ f (s : ExploreState R g), (explorationLeaf ξ roots L).Event ξ' →
      exploreRun ξ L f s = finalState → exploreRun ξ' L f s = finalState := by
    intro f
    induction f with
    | zero => intro s hev hf; simpa [exploreRun] using hf
    | succ f ih =>
        intro s hev hf
        by_cases hg : s.giant = true
        · simpa [exploreRun, hg] using hf
        · have hfalse : s.giant = false := by
            cases hb : s.giant with
            | false => rfl
            | true => exact False.elim (hg hb)
          cases hp : nextPending s with
          | none => simpa [exploreRun, hfalse, hp] using hf
          | some u =>
              have hfuture : exploreRun ξ L f (processEndpoint ξ L u s) = finalState := by
                simpa [exploreRun, hfalse, hp] using hf
              have hprocEq := hProcessSim u s f hev hfuture
              have htail := ih (processEndpoint ξ L u s) hev hfuture
              rw [hprocEq] at htail
              simpa [exploreRun, hfalse, hp] using htail
  have hLeafConstraintEq (e : RowLabel R g)
      (hev : (explorationLeaf ξ roots L).Event ξ') :
      leafConstraint ξ finalState e = leafConstraint ξ' finalState e := by
    cases hAt : finalState.inspectedAt e with
    | none => simp [leafConstraint, hAt]
    | some H =>
        cases hξ : ξ e with
        | noArrival =>
            have hAbs : (EdgeConstraint.absentBefore (edgeCutoff T H e)).Allows (ξ' e) := by
              simpa [explorationLeaf, leafConstraint, finalState, hAt, hξ] using hev e
            cases hξ' : ξ' e with
            | noArrival => simp [leafConstraint, hAt, hξ, hξ']
            | tick t o =>
                have hnot : ¬ eventPriority (⟨e.1, e.2, t, o⟩ : ClockCandidate T R g Ω) < H := by
                  intro hkey
                  exact (hNoEarly H e ξ' hAbs t o hkey) hξ'
                simp [leafConstraint, hAt, hξ, hξ', hnot]
        | tick t o =>
            by_cases hkey : eventPriority (⟨e.1, e.2, t, o⟩ : ClockCandidate T R g Ω) < H
            · have hξ' : ξ' e = .tick t o := by
                simpa [explorationLeaf, leafConstraint, finalState, hAt, hξ, hkey,
                  EdgeConstraint.Allows] using hev e
              simp [leafConstraint, hAt, hξ, hξ', hkey]
            · have hAbs : (EdgeConstraint.absentBefore (edgeCutoff T H e)).Allows (ξ' e) := by
                simpa [explorationLeaf, leafConstraint, finalState, hAt, hξ, hkey] using hev e
              have hge : H ≤ eventPriority (⟨e.1, e.2, t, o⟩ : ClockCandidate T R g Ω) :=
                Nat.le_of_not_gt hkey
              cases hξ' : ξ' e with
              | noArrival => simp [leafConstraint, hAt, hξ, hξ', hge]
              | tick t' o' =>
                  have hnot :
                      ¬ eventPriority (⟨e.1, e.2, t', o'⟩ : ClockCandidate T R g Ω) < H := by
                    intro hkey'
                    exact (hNoEarly H e ξ' hAbs t' o' hkey') hξ'
                  simp [leafConstraint, hAt, hξ, hξ', hge, hnot]
  constructor
  · intro hev
    have hrunEq : truncatedExploration ξ' roots L = finalState := by
      have h := hRunSim (Fintype.card (Endpoint R g)) (initExploreState T roots L) hev
        (by simp [truncatedExploration, finalState])
      simpa [truncatedExploration, finalState] using h
    refine ⟨hrunEq, ?_⟩
    simp only [explorationLeaf, hrunEq, ClockLeaf.mk.injEq]
    constructor
    · funext e
      exact (hLeafConstraintEq e hev).symm
    · rfl
  · rintro ⟨_, hleaf⟩
    rw [← hleaf]
    exact hself ξ'

/-- L3.10b-agree (03:866–867): on a non-giant leaf every clock field of the leaf agrees with `ξ` below every
closure horizon (the run inspected every edge at each closure endpoint at its largest horizon). -/
theorem nongiant_leaf_agreesBelow {T : ℕ} {R : Type*} [Fintype R] [DecidableEq R] {g : ℕ}
    {Ω : R → Type*} (ξ ξ' : ClockField T R g Ω) (roots : Finset (Endpoint R g)) (L : ℕ)
    (hng : (truncatedExploration ξ roots L).giant = false)
    (hev : (explorationLeaf ξ roots L).Event ξ') :
    agreesBelowClosure roots ξ ξ' := by
  classical
  intro u h hreach c hinc hkey
  let e : RowLabel R g := (c.1, c.2.1)
  have hinc' : EdgeIncident u e := by simpa [e] using hinc
  obtain ⟨H, hins, hle⟩ :=
    (truncatedExploration_complete ξ roots L hng u h hreach).2 e hinc'
  have hkeyH : eventPriority c < H := lt_of_lt_of_le hkey hle
  have hcut : (edgeCutoff T H e).val ≤ c.2.2.1.val ↔ H ≤ eventPriority c := by
    simpa [edgeCutoff, qClockCutoffValue, e] using
      (qClockCutoffValue_le_iff (T := T) (R := R) (g := g) (H := H)
        c.1 c.2.1 c.2.2.1 c.2.2.2)
  have hnotAbsent (hall : (EdgeConstraint.absentBefore (edgeCutoff T H e)).Allows (ξ' e)) :
      ¬ candidateIsArrival ξ' c := by
    intro hc
    have hvalue : ξ' e = .tick c.2.2.1 c.2.2.2 := by
      simpa [candidateIsArrival, e] using hc
    cases hx : ξ' e with
    | noArrival => simp [hx] at hvalue
    | tick t o =>
        have hEq : MeshClockValue.tick t o = MeshClockValue.tick c.2.2.1 c.2.2.2 :=
          hx.symm.trans hvalue
        have ht : t = c.2.2.1 := (MeshClockValue.tick.inj hEq).1
        have hcutTick : (edgeCutoff T H e).val ≤ t.val := by
          simpa [EdgeConstraint.Allows, hx] using hall
        have hHkey : H ≤ eventPriority c := hcut.mp (by simpa [ht] using hcutTick)
        omega
  have hall := hev e
  cases hξ : ξ e with
  | noArrival =>
      have hbase : ¬ candidateIsArrival ξ c := by
        simp [candidateIsArrival, e, hξ]
      have hleaf : (explorationLeaf ξ roots L).constraint e =
          .absentBefore (edgeCutoff T H e) := by
        simp [explorationLeaf, leafConstraint, hins, hξ]
      rw [hleaf] at hall
      have hother := hnotAbsent hall
      constructor
      · exact False.elim ∘ hbase
      · exact False.elim ∘ hother
  | tick t o =>
      let c₀ : ClockCandidate T R g Ω := ⟨e.1, e.2, t, o⟩
      by_cases h₀ : eventPriority c₀ < H
      · have hleaf : (explorationLeaf ξ roots L).constraint e = .exactArrival t o := by
          simp [explorationLeaf, leafConstraint, hins, hξ, c₀, h₀]
        rw [hleaf] at hall
        have hξ' : ξ' e = .tick t o := by
          simpa [EdgeConstraint.Allows] using hall
        have heq : ξ e = ξ' e := by rw [hξ, hξ']
        unfold candidateIsArrival
        rw [heq]
      · have hleaf : (explorationLeaf ξ roots L).constraint e =
            .absentBefore (edgeCutoff T H e) := by
          simp [explorationLeaf, leafConstraint, hins, hξ, c₀, h₀]
        have hbase : ¬ candidateIsArrival ξ c := by
          intro hc
          have hvalue : ξ e = .tick c.2.2.1 c.2.2.2 := by
            simpa [candidateIsArrival, e] using hc
          have hEq : MeshClockValue.tick t o = MeshClockValue.tick c.2.2.1 c.2.2.2 :=
            hξ.symm.trans hvalue
          have ht : t = c.2.2.1 := (MeshClockValue.tick.inj hEq).1
          have hkeyEq : eventPriority c₀ = eventPriority c := by
            simp [c₀, eventPriority, e, ht]
          apply h₀
          simpa [hkeyEq] using hkeyH
        rw [hleaf] at hall
        have hother := hnotAbsent hall
        constructor
        · exact False.elim ∘ hbase
        · exact False.elim ∘ hother

/-- L3.10b-closure (03:866–867, "These inspections determine the matching decisions at the roots by backward
closure through all earlier events they require"): agreement below the closure horizons determines the greedy
assignment of every root row. Strengthens `backwardClosure_determines_test` (agreement only below the horizons,
and the full assignment, including the matched label and output). -/
theorem closure_determines_root_assignment {T : ℕ} {R : Type*} [Fintype R] [DecidableEq R] {g : ℕ}
    {Ω : R → Type*} [∀ a, Fintype (Ω a)] [∀ a, DecidableEq (Ω a)]
    (ξ ξ' : ClockField T R g Ω) (roots : Finset (Endpoint R g))
    (h : agreesBelowClosure roots ξ ξ') :
    ∀ a, Sum.inl a ∈ roots → (greedyMatching ξ).assignment a = (greedyMatching ξ').assignment a := by
  classical
  have hpriority_inj (ζ : ClockField T R g Ω) (e f : ClockCandidate T R g Ω)
      (he : candidateIsArrival ζ e) (hf : candidateIsArrival ζ f)
      (hkey : eventPriority e = eventPriority f) : e = f := by
    rcases e with ⟨a, y, i, oa⟩
    rcases f with ⟨b, z, j, ob⟩
    have hRpos : 0 < Fintype.card R := Fintype.card_pos_iff.mpr ⟨a⟩
    have hylt : y.val < g := y.isLt
    have hgpos : 0 < g := by omega
    let base : ℕ := Fintype.card R * g
    let low₁ : ℕ := ((Fintype.equivFin R) a).val * g + y.val
    let low₂ : ℕ := ((Fintype.equivFin R) b).val * g + z.val
    have hbase : 0 < base := Nat.mul_pos hRpos hgpos
    have hlow₁ : low₁ < base := by
      dsimp [low₁, base]
      calc
        ((Fintype.equivFin R) a).val * g + y.val <
            ((Fintype.equivFin R) a).val * g + g := Nat.add_lt_add_left y.isLt _
        _ = Nat.succ ((Fintype.equivFin R) a).val * g := by rw [Nat.succ_mul]
        _ ≤ Fintype.card R * g := Nat.mul_le_mul_right g
          (Nat.succ_le_of_lt ((Fintype.equivFin R a).isLt))
    have hlow₂ : low₂ < base := by
      dsimp [low₂, base]
      calc
        ((Fintype.equivFin R) b).val * g + z.val <
            ((Fintype.equivFin R) b).val * g + g := Nat.add_lt_add_left z.isLt _
        _ = Nat.succ ((Fintype.equivFin R) b).val * g := by rw [Nat.succ_mul]
        _ ≤ Fintype.card R * g := Nat.mul_le_mul_right g
          (Nat.succ_le_of_lt ((Fintype.equivFin R b).isLt))
    have hkey' : i.val * base + low₁ = j.val * base + low₂ := by
      simpa [eventPriority, base, low₁, low₂, Nat.add_assoc] using hkey
    have hdiv₁ : (i.val * base + low₁) / base = i.val := by
      rw [Nat.mul_comm i.val base, Nat.mul_add_div hbase]
      simp [Nat.div_eq_of_lt hlow₁]
    have hdiv₂ : (j.val * base + low₂) / base = j.val := by
      rw [Nat.mul_comm j.val base, Nat.mul_add_div hbase]
      simp [Nat.div_eq_of_lt hlow₂]
    have hij : i.val = j.val := by
      have hd := congrArg (fun n : ℕ => n / base) hkey'
      rw [hdiv₁, hdiv₂] at hd
      exact hd
    have hmod₁ : (i.val * base + low₁) % base = low₁ := by
      rw [Nat.mul_comm i.val base, Nat.mul_add_mod_self_left, Nat.mod_eq_of_lt hlow₁]
    have hmod₂ : (j.val * base + low₂) % base = low₂ := by
      rw [Nat.mul_comm j.val base, Nat.mul_add_mod_self_left, Nat.mod_eq_of_lt hlow₂]
    have hlowEq : low₁ = low₂ := by
      have hm := congrArg (fun n : ℕ => n % base) hkey'
      rw [hmod₁, hmod₂] at hm
      exact hm
    have hyz : y.val = z.val := by
      have hm := congrArg (fun n : ℕ => n % g) hlowEq
      simpa [low₁, low₂, Nat.mul_add_mod_self_right, Nat.mod_eq_of_lt y.isLt,
        Nat.mod_eq_of_lt z.isLt] using hm
    have hrowRank : ((Fintype.equivFin R) a).val = ((Fintype.equivFin R) b).val := by
      have hcancel : ((Fintype.equivFin R) a).val * g =
          ((Fintype.equivFin R) b).val * g := by
        dsimp [low₁, low₂] at hlowEq
        rw [hyz] at hlowEq
        exact Nat.add_right_cancel hlowEq
      exact Nat.mul_right_cancel hgpos hcancel
    have hab : a = b := by
      apply (Fintype.equivFin R).injective
      exact Fin.ext hrowRank
    have hy : y = z := Fin.ext hyz
    have hi : i = j := Fin.ext hij
    subst b
    subst z
    subst j
    have hoa : oa = ob := by
      have hmarks : MeshClockValue.tick i oa = MeshClockValue.tick i ob := he.symm.trans hf
      exact (MeshClockValue.tick.inj hmarks).2
    subst ob
    rfl
  have hstrictList (ζ : ClockField T R g Ω) : ∀ {l : List (ClockCandidate T R g Ω)},
      l.Pairwise (fun e f => eventPriority e ≤ eventPriority f) → l.Nodup →
      (∀ e, e ∈ l → candidateIsArrival ζ e) →
      l.Pairwise (fun e f => eventPriority e < eventPriority f) := by
    intro l hle hnd harr
    induction l with
    | nil => exact List.Pairwise.nil
    | cons e es ih =>
        simp only [List.pairwise_cons] at hle ⊢
        simp only [List.nodup_cons] at hnd
        refine ⟨?_, ih hle.2 hnd.2 ?_⟩
        · intro f hf
          have hne : e ≠ f := by
            intro hef
            subst f
            exact hnd.1 hf
          have hkeyNe : eventPriority e ≠ eventPriority f := by
            intro heq
            apply hne
            exact hpriority_inj ζ e f (harr e (by simp))
              (harr f (List.mem_cons_of_mem e hf)) heq
          have hleEF := hle.1 f hf
          omega
        · intro f hf
          exact harr f (List.mem_cons_of_mem e hf)
  have hstrict (ζ : ClockField T R g Ω) :
      (clockEventList ζ).Pairwise (fun e f => eventPriority e < eventPriority f) := by
    have hnd : (clockEventList ζ).Nodup := by
      unfold clockEventList
      exact List.Nodup.mergeSort (Finset.nodup_toList _)
    have harr : ∀ e, e ∈ clockEventList ζ → candidateIsArrival ζ e := by
      intro e he
      simpa [clockEventList] using he
    exact hstrictList ζ (clockEventList_sorted ζ) hnd harr
  let relevant : ClockCandidate T R g Ω → Prop := fun e =>
    (∃ H, inClosureFrom ξ roots (Sum.inl e.1, H) ∧ eventPriority e < H) ∨
      (∃ H, inClosureFrom ξ roots (Sum.inr e.2.1, H) ∧ eventPriority e < H)
  have harrivalRelevant (e : ClockCandidate T R g Ω) (hr : relevant e) :
      candidateIsArrival ξ e ↔ candidateIsArrival ξ' e := by
    rcases hr with ⟨H, hr, hkey⟩ | ⟨H, hr, hkey⟩
    · exact h (Sum.inl e.1) H hr e (Or.inl rfl) hkey
    · exact h (Sum.inr e.2.1) H hr e (Or.inr rfl) hkey
  have hreachLabelOfRow (e : ClockCandidate T R g Ω) {H : ℕ}
      (hr : inClosureFrom ξ roots (Sum.inl e.1, H))
      (hp : eventPriority e < H) (he : candidateIsArrival ξ e) :
      inClosureFrom ξ roots (Sum.inr e.2.1, eventPriority e) := by
    rcases hr with ⟨r, hr, path⟩
    exact ⟨r, hr, Relation.ReflTransGen.tail path
      ⟨e, he, hp, rfl, Or.inl ⟨rfl, rfl⟩⟩⟩
  have hreachRowOfLabel (e : ClockCandidate T R g Ω) {H : ℕ}
      (hr : inClosureFrom ξ roots (Sum.inr e.2.1, H))
      (hp : eventPriority e < H) (he : candidateIsArrival ξ e) :
      inClosureFrom ξ roots (Sum.inl e.1, eventPriority e) := by
    rcases hr with ⟨r, hr, path⟩
    exact ⟨r, hr, Relation.ReflTransGen.tail path
      ⟨e, he, hp, rfl, Or.inr ⟨rfl, rfl⟩⟩⟩
  have hlistMem (ζ : ClockField T R g Ω) (e : ClockCandidate T R g Ω) :
      e ∈ clockEventList ζ ↔ candidateIsArrival ζ e := by
    simp [clockEventList]
  have hrelMem (e : ClockCandidate T R g Ω) :
      (e ∈ clockEventList ξ ∧ relevant e) ↔ (e ∈ clockEventList ξ' ∧ relevant e) := by
    constructor
    · rintro ⟨he, hr⟩
      exact ⟨hlistMem ξ' e |>.mpr ((harrivalRelevant e hr).mp (hlistMem ξ e |>.mp he)), hr⟩
    · rintro ⟨he, hr⟩
      exact ⟨hlistMem ξ e |>.mpr ((harrivalRelevant e hr).mpr (hlistMem ξ' e |>.mp he)), hr⟩
  have hrelLists :
      (clockEventList ξ).filter (fun e => decide (relevant e)) =
        (clockEventList ξ').filter (fun e => decide (relevant e)) := by
    apply List.Pairwise.eq_of_mem_iff
      ((hstrict ξ).filter (fun e => decide (relevant e)))
      ((hstrict ξ').filter (fun e => decide (relevant e)))
    intro e
    simp only [List.mem_filter, decide_eq_true_eq]
    exact hrelMem e
  let acceptCond (ζ : ClockField T R g Ω) (s : GreedyState R g Ω)
      (e : ClockCandidate T R g Ω) : Prop :=
    candidateIsArrival ζ e ∧ s.assignment e.1 = none ∧ ¬ labelUsed s e.2.1
  let statusEq (s s' : GreedyState R g Ω) (u : Endpoint R g) : Prop :=
    match u with
    | .inl a => s.assignment a = s'.assignment a
    | .inr y => labelUsed s y ↔ labelUsed s' y
  have hacceptCond (ζ ζ' : ClockField T R g Ω) (s s' : GreedyState R g Ω)
      (e : ClockCandidate T R g Ω)
      (ha : candidateIsArrival ζ e ↔ candidateIsArrival ζ' e)
      (hr : s.assignment e.1 = s'.assignment e.1)
      (hy : labelUsed s e.2.1 ↔ labelUsed s' e.2.1) :
      acceptCond ζ s e ↔ acceptCond ζ' s' e := by simp [acceptCond, ha, hr, hy]
  have hprocessRow (ζ ζ' : ClockField T R g Ω) (s s' : GreedyState R g Ω)
      (e : ClockCandidate T R g Ω)
      (hc : acceptCond ζ s e ↔ acceptCond ζ' s' e)
      (hr : s.assignment e.1 = s'.assignment e.1) :
      (processArrival ζ s e).assignment e.1 = (processArrival ζ' s' e).assignment e.1 := by
    by_cases hacc : acceptCond ζ s e
    · have hacc' := hc.mp hacc
      simp [processArrival, acceptCond, hacc, hacc']
    · have hacc' : ¬ acceptCond ζ' s' e := fun h' => hacc (hc.mpr h')
      simpa [processArrival, acceptCond, hacc, hacc'] using hr
  have hprocessLabel (ζ ζ' : ClockField T R g Ω) (s s' : GreedyState R g Ω)
      (e : ClockCandidate T R g Ω)
      (hc : acceptCond ζ s e ↔ acceptCond ζ' s' e)
      (hy : labelUsed s e.2.1 ↔ labelUsed s' e.2.1) :
      labelUsed (processArrival ζ s e) e.2.1 ↔ labelUsed (processArrival ζ' s' e) e.2.1 := by
    by_cases hacc : acceptCond ζ s e
    · have hacc' := hc.mp hacc
      have hused : labelUsed (processArrival ζ s e) e.2.1 := by
        refine ⟨e.1, e.2.2.2, ?_⟩
        simp [processArrival, acceptCond, hacc]
      have hused' : labelUsed (processArrival ζ' s' e) e.2.1 := by
        refine ⟨e.1, e.2.2.2, ?_⟩
        simp [processArrival, acceptCond, hacc']
      exact ⟨fun _ => hused', fun _ => hused⟩
    · have hacc' : ¬ acceptCond ζ' s' e := fun h' => hacc (hc.mpr h')
      simpa [processArrival, acceptCond, hacc, hacc'] using hy
  have hlabelStutter (ζ : ClockField T R g Ω) (s : GreedyState R g Ω)
      (e : ClockCandidate T R g Ω) (y : Fin g) (hy : y ≠ e.2.1) :
      labelUsed (processArrival ζ s e) y ↔ labelUsed s y := by
    classical
    by_cases hacc : candidateIsArrival ζ e ∧ s.assignment e.1 = none ∧ ¬ labelUsed s e.2.1
    · rw [processArrival, if_pos hacc]
      unfold labelUsed
      constructor
      · rintro ⟨a, o, ha⟩
        by_cases hrow : e.1 = a
        · subst a
          have hEq : some (e.2.1, e.2.2.2) = some (y, o) := by simpa using ha
          have hlabel := congrArg Prod.fst (Option.some.inj hEq)
          exact False.elim (hy hlabel.symm)
        · exact ⟨a, o, by simpa only [dif_neg hrow] using ha⟩
      · rintro ⟨a, o, ha⟩
        by_cases hrow : e.1 = a
        · subst a
          have hsnone : s.assignment e.1 = none := hacc.2.1
          rw [hsnone] at ha
          simp at ha
        · exact ⟨a, o, by simpa only [dif_neg hrow] using ha⟩
    · rw [processArrival, if_neg hacc]
  have hstatusStutter (ζ : ClockField T R g Ω) (s : GreedyState R g Ω)
      (e : ClockCandidate T R g Ω) (u : Endpoint R g)
      (hrow : u ≠ Sum.inl e.1) (hlabel : u ≠ Sum.inr e.2.1) :
      statusEq (processArrival ζ s e) s u := by
    cases u with
    | inl a =>
        have ha : a ≠ e.1 := by intro heq; apply hrow; simp [heq]
        have hs : (processArrival ζ s e).assignment a = s.assignment a := by
          by_cases hacc : acceptCond ζ s e
          · simp [processArrival, acceptCond, hacc, ha, eq_comm]
          · simp [processArrival, acceptCond, hacc]
        simpa [statusEq] using hs
    | inr y =>
        have hy : y ≠ e.2.1 := by intro heq; apply hlabel; simp [heq]
        exact hlabelStutter ζ s e y hy
  have hstatusSymm (s s' : GreedyState R g Ω) (u : Endpoint R g)
      (hs : statusEq s s' u) : statusEq s' s u := by cases u <;> exact hs.symm
  have hstatusTrans (s₁ s₂ s₃ : GreedyState R g Ω) (u : Endpoint R g)
      (h₁ : statusEq s₁ s₂ u) (h₂ : statusEq s₂ s₃ u) : statusEq s₁ s₃ u := by
    cases u <;> exact h₁.trans h₂
  have hfoldFilter (ζ ζ' : ClockField T R g Ω) :
      ∀ (events : List (ClockCandidate T R g Ω)) (s s' : GreedyState R g Ω) (lo : ℕ),
        events.Pairwise (fun e f => eventPriority e < eventPriority f) →
        (∀ e, e ∈ events → lo ≤ eventPriority e) →
        (∀ e, e ∈ events → candidateIsArrival ζ e) →
        (∀ e, e ∈ events → relevant e → candidateIsArrival ξ e) →
        (∀ e, relevant e → (candidateIsArrival ζ e ↔ candidateIsArrival ζ' e)) →
        (∀ u H, inClosureFrom ξ roots (u, H) → lo ≤ H → statusEq s s' u) →
        ∀ u H, inClosureFrom ξ roots (u, H) → lo ≤ H →
          (∀ e, e ∈ events → eventPriority e < H) →
          statusEq (events.foldl (fun st e => processArrival ζ st e) s)
            ((events.filter (fun e => decide (relevant e))).foldl
              (fun st e => processArrival ζ' st e) s') u := by
    intro events
    induction events with
    | nil =>
        intro s s' lo hsorted hlo harr harrXi harrEq hinv u H hr hloH hall
        exact hinv u H hr hloH
    | cons e es ih =>
        intro s s' lo hsorted hlo harr harrXi harrEq hinv u H hr hloH hall
        simp only [List.pairwise_cons] at hsorted
        have hpLo : lo ≤ eventPriority e := hlo e (by simp)
        have hpH : eventPriority e < H := hall e (by simp)
        let sNext := processArrival ζ s e
        let s'Next := if relevant e then processArrival ζ' s' e else s'
        have hinvNext : ∀ v k, inClosureFrom ξ roots (v, k) →
            eventPriority e + 1 ≤ k → statusEq sNext s'Next v := by
          intro v k hv hpk
          have hpre : statusEq s s' v := hinv v k hv (by omega)
          by_cases hrel : relevant e
          · have heXi := harrXi e (by simp) hrel
            have hrowReach : ∃ kr, inClosureFrom ξ roots (Sum.inl e.1, kr) ∧ lo ≤ kr := by
              rcases hrel with ⟨H₀, hreq, hlt⟩ | ⟨H₀, hreq, hlt⟩
              · exact ⟨H₀, hreq, by omega⟩
              · have hr := hreachRowOfLabel e hreq hlt heXi
                exact ⟨eventPriority e, hr, by omega⟩
            have hlabelReach : ∃ ky, inClosureFrom ξ roots (Sum.inr e.2.1, ky) ∧ lo ≤ ky := by
              rcases hrel with ⟨H₀, hreq, hlt⟩ | ⟨H₀, hreq, hlt⟩
              · have hr := hreachLabelOfRow e hreq hlt heXi
                exact ⟨eventPriority e, hr, by omega⟩
              · exact ⟨H₀, hreq, by omega⟩
            rcases hrowReach with ⟨kr, hr, hloKr⟩
            rcases hlabelReach with ⟨ky, hy, hloKy⟩
            have hrowEq : s.assignment e.1 = s'.assignment e.1 := by
              have hs := hinv (Sum.inl e.1) kr hr hloKr
              simpa [statusEq] using hs
            have hlabelEq : labelUsed s e.2.1 ↔ labelUsed s' e.2.1 := by
              have hs := hinv (Sum.inr e.2.1) ky hy hloKy
              simpa [statusEq] using hs
            have hc := hacceptCond ζ ζ' s s' e (harrEq e hrel) hrowEq hlabelEq
            by_cases hvRow : v = Sum.inl e.1
            · subst v
              simpa [sNext, s'Next, statusEq, hrel] using hprocessRow ζ ζ' s s' e hc hrowEq
            · by_cases hvLabel : v = Sum.inr e.2.1
              · subst v
                simpa [sNext, s'Next, statusEq, hrel] using
                  hprocessLabel ζ ζ' s s' e hc hlabelEq
              · have hs := hstatusStutter ζ s e v hvRow hvLabel
                have hs' := hstatusStutter ζ' s' e v hvRow hvLabel
                have hs' := hstatusSymm (processArrival ζ' s' e) s' v hs'
                simpa [sNext, s'Next, hrel] using
                  hstatusTrans (processArrival ζ s e) s' (processArrival ζ' s' e) v
                    (hstatusTrans (processArrival ζ s e) s s' v hs hpre) hs'
          · have hvRow : v ≠ Sum.inl e.1 := by
              intro hveq
              subst v
              exact hrel (Or.inl ⟨k, hv, by omega⟩)
            have hvLabel : v ≠ Sum.inr e.2.1 := by
              intro hveq
              subst v
              exact hrel (Or.inr ⟨k, hv, by omega⟩)
            have hs := hstatusStutter ζ s e v hvRow hvLabel
            simpa [sNext, s'Next, hrel] using
              hstatusTrans (processArrival ζ s e) s s' v hs hpre
        have hloTail : ∀ f, f ∈ es → eventPriority e + 1 ≤ eventPriority f := by
          intro f hf
          have hlt := hsorted.1 f hf
          omega
        have harrTail : ∀ f, f ∈ es → candidateIsArrival ζ f := by
          intro f hf
          exact harr f (List.mem_cons_of_mem e hf)
        have harrXiTail : ∀ f, f ∈ es → relevant f → candidateIsArrival ξ f := by
          intro f hf hrelf
          exact harrXi f (List.mem_cons_of_mem e hf) hrelf
        have hallTail : ∀ f, f ∈ es → eventPriority f < H := by
          intro f hf
          exact hall f (List.mem_cons_of_mem e hf)
        by_cases hrel : relevant e
        · have hresult := ih sNext s'Next (eventPriority e + 1) hsorted.2
            hloTail harrTail harrXiTail harrEq hinvNext
          have hresult' := hresult u H hr (by omega) hallTail
          simpa [sNext, s'Next, hrel, List.foldl_cons, List.filter] using hresult'
        · have hresult := ih sNext s'Next (eventPriority e + 1) hsorted.2
            hloTail harrTail harrXiTail harrEq hinvNext
          have hresult' := hresult u H hr (by omega) hallTail
          simpa [sNext, s'Next, hrel, List.foldl_cons, List.filter] using hresult'
  have hkeyBound (e : ClockCandidate T R g Ω) :
      eventPriority e < rootHorizon T R g := by
    have hRpos : 0 < Fintype.card R := Fintype.card_pos_iff.mpr ⟨e.1⟩
    have hgy : e.2.1.val < g := e.2.1.isLt
    have hgpos : 0 < g := by omega
    let base : ℕ := Fintype.card R * g
    let low : ℕ := ((Fintype.equivFin R) e.1).val * g + e.2.1.val
    have hlow : low < base := by
      dsimp [low, base]
      calc
        ((Fintype.equivFin R) e.1).val * g + e.2.1.val <
            ((Fintype.equivFin R) e.1).val * g + g := Nat.add_lt_add_left e.2.1.isLt _
        _ = Nat.succ ((Fintype.equivFin R) e.1).val * g := by rw [Nat.succ_mul]
        _ ≤ Fintype.card R * g := Nat.mul_le_mul_right g
          (Nat.succ_le_of_lt ((Fintype.equivFin R e.1).isLt))
    calc
      eventPriority e = e.2.2.1.val * base + low := by
        simp [eventPriority, base, low, Nat.add_assoc]
      _ < e.2.2.1.val * base + base := Nat.add_lt_add_left hlow _
      _ = Nat.succ e.2.2.1.val * base := by rw [Nat.succ_mul]
      _ ≤ T * base := Nat.mul_le_mul_right base (Nat.succ_le_of_lt e.2.2.1.isLt)
  let common : List (ClockCandidate T R g Ω) :=
    (clockEventList ξ).filter (fun e => decide (relevant e))
  have hcommonStrict : common.Pairwise (fun e f => eventPriority e < eventPriority f) := by
    dsimp [common]
    exact (hstrict ξ).filter _
  have hcommonArrival : ∀ e, e ∈ common → candidateIsArrival ξ e := by
    intro e he
    exact (hlistMem ξ e).mp (List.mem_filter.mp he).1
  have hcommonFilter : common.filter (fun e => decide (relevant e)) = common := by
    simp [common, List.filter_filter]
  have hempty : ∀ u H, inClosureFrom ξ roots (u, H) → 0 ≤ H →
      statusEq emptyGreedyState emptyGreedyState u := by
    intro u H hr hle
    cases u <;> simp [statusEq, emptyGreedyState, labelUsed]
  have hrootReach (a : R) (ha : Sum.inl a ∈ roots) :
      inClosureFrom ξ roots (Sum.inl a, rootHorizon T R g) :=
    ⟨Sum.inl a, ha, Relation.ReflTransGen.refl⟩
  have hfullXi (a : R) (ha : Sum.inl a ∈ roots) :
      statusEq (greedyMatching ξ) (runGreedy ξ' common) (Sum.inl a) := by
    have hres := hfoldFilter ξ ξ' (clockEventList ξ) emptyGreedyState emptyGreedyState 0
      (hstrict ξ)
      (by intro e he; exact Nat.zero_le _)
      (by intro e he; exact (hlistMem ξ e).mp he)
      (by intro e he hr; exact (hlistMem ξ e).mp he)
      (fun e hr => harrivalRelevant e hr)
      hempty
      (Sum.inl a) (rootHorizon T R g) (hrootReach a ha) (Nat.zero_le _)
      (by intro e he; exact hkeyBound e)
    simpa [greedyMatching, runGreedy, common] using hres
  have hfullXi' (a : R) (ha : Sum.inl a ∈ roots) :
      statusEq (greedyMatching ξ') (runGreedy ξ common) (Sum.inl a) := by
    have hres := hfoldFilter ξ' ξ (clockEventList ξ') emptyGreedyState emptyGreedyState 0
      (hstrict ξ')
      (by intro e he; exact Nat.zero_le _)
      (by intro e he; exact (hlistMem ξ' e).mp he)
      (by intro e he hr; exact (harrivalRelevant e hr).mpr ((hlistMem ξ' e).mp he))
      (fun e hr => (harrivalRelevant e hr).symm)
      hempty
      (Sum.inl a) (rootHorizon T R g) (hrootReach a ha) (Nat.zero_le _)
      (by intro e he; exact hkeyBound e)
    simpa [greedyMatching, runGreedy, common, hrelLists] using hres
  have hcommonFold (a : R) (ha : Sum.inl a ∈ roots) :
      statusEq (runGreedy ξ common) (runGreedy ξ' common) (Sum.inl a) := by
    have hres := hfoldFilter ξ ξ' common emptyGreedyState emptyGreedyState 0
      hcommonStrict
      (by intro e he; exact Nat.zero_le _)
      hcommonArrival
      (by intro e he hr; exact hcommonArrival e he)
      (fun e hr => harrivalRelevant e hr)
      hempty
      (Sum.inl a) (rootHorizon T R g) (hrootReach a ha) (Nat.zero_le _)
      (by intro e he; exact hkeyBound e)
    simpa [runGreedy, common, hcommonFilter] using hres
  have hrootAssignment (a : R) (ha : Sum.inl a ∈ roots) :
      (greedyMatching ξ).assignment a = (greedyMatching ξ').assignment a := by
    have hmid := hstatusTrans (greedyMatching ξ') (runGreedy ξ common)
      (runGreedy ξ' common) (Sum.inl a) (hfullXi' a ha) (hcommonFold a ha)
    have hroot := hstatusTrans (greedyMatching ξ) (runGreedy ξ' common)
      (greedyMatching ξ') (Sum.inl a) (hfullXi a ha)
      (hstatusSymm (greedyMatching ξ') (runGreedy ξ' common) (Sum.inl a) hmid)
    simpa [statusEq] using hroot
  intro a ha
  exact hrootAssignment a ha

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
  classical
  let roots : Finset (Endpoint R g) := testRootEndpoints scope t
  let P := clockFieldLaw edgeLaw
  let S : Finset (ClockLeaf T R g Ω) :=
    (badLeaves lab F scope L t).filter (fun ℓ : ClockLeaf T R g Ω => v ∈ ℓ.active)
  let badEvent : ClockField T R g Ω → Prop :=
    fun ξ => closureBad lab F scope L ξ t ∧ v ∈ activeEndpoints ξ scope t
  have hmemWitness (ℓ : ClockLeaf T R g Ω) (hℓ : ℓ ∈ S) :
      ∃ ξ₀, leafBad lab F scope L ξ₀ t ∧ testLeaf ξ₀ scope t L = ℓ := by
    have hbadLeaf : ℓ ∈ badLeaves lab F scope L t := (Finset.mem_filter.mp hℓ).1
    have hbadLeaf' :
        ℓ ∈ ((Finset.univ.filter fun ξ₀ : ClockField T R g Ω =>
          leafBad lab F scope L ξ₀ t).image fun ξ₀ => testLeaf ξ₀ scope t L) := by
      simpa [badLeaves] using hbadLeaf
    rcases Finset.mem_image.mp hbadLeaf' with ⟨ξ₀, hξ₀, hEq⟩
    exact ⟨ξ₀, (Finset.mem_filter.mp hξ₀).2, hEq⟩
  have hleafEq (ℓ : ClockLeaf T R g Ω) (hℓ : ℓ ∈ S) (ξ : ClockField T R g Ω)
      (hEvent : ℓ.Event ξ) : ℓ = testLeaf ξ scope t L := by
    obtain ⟨ξ₀, _, hEq⟩ := hmemWitness ℓ hℓ
    have hEvent₀ : (testLeaf ξ₀ scope t L).Event ξ := by
      simpa [hEq] using hEvent
    have hRunLeaf :=
      (explorationLeaf_event_iff ξ₀ ξ roots L).mp (by simpa [roots, testLeaf] using hEvent₀)
    have hLeaf : testLeaf ξ₀ scope t L = testLeaf ξ scope t L := by
      simpa [testLeaf, roots] using hRunLeaf.2.symm
    exact hEq.symm.trans hLeaf
  have hsubset (ℓ : ClockLeaf T R g Ω) (hℓ : ℓ ∈ S)
      (ξ : ClockField T R g Ω) (hEvent : ℓ.Event ξ) : badEvent ξ := by
    obtain ⟨ξ₀, hbad₀, hEq⟩ := hmemWitness ℓ hℓ
    have hEvent₀ : (testLeaf ξ₀ scope t L).Event ξ := by
      simpa [hEq] using hEvent
    have hbadInv := leafBad_leaf_invariant lab F scope L ξ₀ ξ t hEvent₀
    have hbadξ : leafBad lab F scope L ξ t := hbadInv.mpr hbad₀
    have hLeaf : testLeaf ξ scope t L = ℓ := (hleafEq ℓ hℓ ξ hEvent).symm
    have hvState : v ∈ (truncatedExploration ξ roots L).active := by
      have hvLeaf : v ∈ (testLeaf ξ scope t L).active := by
        rw [hLeaf]
        exact (Finset.mem_filter.mp hℓ).2
      simpa [testLeaf, explorationLeaf, roots] using hvLeaf
    have hSound := truncatedExploration_sound ξ roots L
    have hvClosure : v ∈ closureFrom ξ roots := hSound.2.2 hvState
    have hActiveEq : activeEndpoints ξ scope t = closureFrom ξ roots := by
      simpa [roots] using activeEndpoints_eq_closureFrom ξ scope t
    have hvActive : v ∈ activeEndpoints ξ scope t := by
      rw [hActiveEq]
      exact hvClosure
    have hClosureBad : closureBad lab F scope L ξ t := by
      rcases hbadξ with hgiant | hbadOutcome
      · have hgiant' : (truncatedExploration ξ roots L).giant = true := by
          simpa [testExploration, roots] using hgiant
        have hcard := (truncatedExploration_giant_iff ξ roots L).mp hgiant'
        have hActiveEq' : activeEndpoints ξ scope t = closureFrom ξ roots := by
          simpa [roots] using activeEndpoints_eq_closureFrom ξ scope t
        change L ≤ (activeEndpoints ξ scope t).card ∨ _
        left
        rw [hActiveEq']
        exact hcard
      · exact Or.inr hbadOutcome
    exact ⟨hClosureBad, hvActive⟩
  have hunique (ξ : ClockField T R g Ω) (ℓ₁ ℓ₂ : ClockLeaf T R g Ω)
      (h₁ : ℓ₁ ∈ S) (h₂ : ℓ₂ ∈ S) (he₁ : ℓ₁.Event ξ) (he₂ : ℓ₂.Event ξ) :
      ℓ₁ = ℓ₂ := by
    calc
      ℓ₁ = testLeaf ξ scope t L := hleafEq ℓ₁ h₁ ξ he₁
      _ = ℓ₂ := (hleafEq ℓ₂ h₂ ξ he₂).symm
  have hcount (ξ : ClockField T R g Ω) :
      (∑ ℓ ∈ S, if ℓ.Event ξ then (1 : ℝ) else 0) ≤ if badEvent ξ then 1 else 0 := by
    by_cases hbad : badEvent ξ
    · simp only [if_pos hbad]
      by_cases hex : ∃ ℓ ∈ S, ℓ.Event ξ
      · obtain ⟨ℓ₀, hℓ₀, he₀⟩ := hex
        calc
          (∑ ℓ ∈ S, if ℓ.Event ξ then (1 : ℝ) else 0) ≤
              ∑ ℓ ∈ S, if ℓ = ℓ₀ then (1 : ℝ) else 0 := by
                apply Finset.sum_le_sum
                intro ℓ hℓ
                by_cases he : ℓ.Event ξ
                · have : ℓ = ℓ₀ := hunique ξ ℓ ℓ₀ hℓ hℓ₀ he he₀
                  simp [this, he, he₀]
                · split_ifs <;> norm_num
          _ = 1 := by simp [hℓ₀]
      · have hnone : ∀ ℓ ∈ S, ¬ ℓ.Event ξ := by
          intro ℓ hℓ he
          exact hex ⟨ℓ, hℓ, he⟩
        have hsum0 : (∑ ℓ ∈ S, if ℓ.Event ξ then (1 : ℝ) else 0) = 0 := by
          apply Finset.sum_eq_zero
          intro ℓ hℓ
          simp [hnone ℓ hℓ]
        simp [hsum0]
    · have hnone : ∀ ℓ ∈ S, ¬ ℓ.Event ξ := by
        intro ℓ hℓ he
        exact hbad (hsubset ℓ hℓ ξ he)
      have hsum0 : (∑ ℓ ∈ S, if ℓ.Event ξ then (1 : ℝ) else 0) = 0 := by
        apply Finset.sum_eq_zero
        intro ℓ hℓ
        simp [hnone ℓ hℓ]
      simp [hsum0, hbad]
  have hsumLeft :
      (∑ ℓ ∈ S, P.pr ℓ.Event) =
        ∑ ξ : ClockField T R g Ω, P.w ξ * (∑ ℓ ∈ S, if ℓ.Event ξ then (1 : ℝ) else 0) := by
    simp only [FinProb.pr]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro ξ hξ
    calc
      (∑ ℓ ∈ S, if ℓ.Event ξ then P.w ξ else 0) =
          ∑ ℓ ∈ S, P.w ξ * (if ℓ.Event ξ then (1 : ℝ) else 0) := by
            apply Finset.sum_congr rfl
            intro ℓ hℓ
            split_ifs <;> simp
      _ = P.w ξ * (∑ ℓ ∈ S, if ℓ.Event ξ then (1 : ℝ) else 0) := by
            rw [Finset.mul_sum]
  calc
    (∑ ℓ ∈ (badLeaves lab F scope L t).filter (fun ℓ => v ∈ ℓ.active),
        (clockFieldLaw edgeLaw).pr ℓ.Event) =
      ∑ ξ : ClockField T R g Ω, P.w ξ *
        (∑ ℓ ∈ S, if ℓ.Event ξ then (1 : ℝ) else 0) := by
          simpa [S, P] using hsumLeft
    _ ≤ ∑ ξ : ClockField T R g Ω, P.w ξ * (if badEvent ξ then 1 else 0) := by
          apply Finset.sum_le_sum
          intro ξ hξ
          exact mul_le_mul_of_nonneg_left (hcount ξ) (P.nonneg ξ)
    _ = P.pr badEvent := by
          unfold FinProb.pr
          apply Finset.sum_congr rfl
          intro ξ hξ
          by_cases hb : badEvent ξ <;> simp [hb]
    _ = (clockFieldLaw edgeLaw).pr
        (fun ξ => closureBad lab F scope L ξ t ∧ v ∈ activeEndpoints ξ scope t) := by
          rfl

end HypercubeRamsey.Clock
