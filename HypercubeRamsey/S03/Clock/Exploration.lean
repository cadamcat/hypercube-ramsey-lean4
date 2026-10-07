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
  classical
  have hpriority_inj (ζ : ClockField T R g Ω) (e f : ClockCandidate T R g Ω)
      (he : candidateIsArrival ζ e) (hf : candidateIsArrival ζ f)
      (hkey : eventPriority e = eventPriority f) : e = f := by
    rcases e with ⟨a, y, i, oa⟩
    rcases f with ⟨b, z, j, ob⟩
    have hRpos : 0 < Fintype.card R := Fintype.card_pos_iff.mpr ⟨a⟩
    have hylt := y.isLt
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
        _ ≤ Fintype.card R * g := Nat.mul_le_mul_right g (Nat.succ_le_of_lt ((Fintype.equivFin R a).isLt))
    have hlow₂ : low₂ < base := by
      dsimp [low₂, base]
      calc
        ((Fintype.equivFin R) b).val * g + z.val <
            ((Fintype.equivFin R) b).val * g + g := Nat.add_lt_add_left z.isLt _
        _ = Nat.succ ((Fintype.equivFin R) b).val * g := by rw [Nat.succ_mul]
        _ ≤ Fintype.card R * g := Nat.mul_le_mul_right g (Nat.succ_le_of_lt ((Fintype.equivFin R b).isLt))
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
      have hmarks : MeshClockValue.tick i oa = MeshClockValue.tick i ob := by
        exact he.symm.trans hf
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
    (∃ h₀, inBackwardClosure ξ scope t (Sum.inl e.1, h₀) ∧ eventPriority e < h₀) ∨
    (∃ h₀, inBackwardClosure ξ scope t (Sum.inr e.2.1, h₀) ∧ eventPriority e < h₀)
  have hactive_of_reach {u : Endpoint R g} {h₀ : ℕ}
      (hr : inBackwardClosure ξ scope t (u, h₀)) :
      u ∈ activeEndpoints ξ scope t := by
    simpa [activeEndpoints] using (show ∃ h, inBackwardClosure ξ scope t (u, h) from ⟨h₀, hr⟩)
  have hclockRow (e : ClockCandidate T R g Ω) {h₀ : ℕ}
      (hr : inBackwardClosure ξ scope t (Sum.inl e.1, h₀)) :
      ξ (e.1, e.2.1) = ξ' (e.1, e.2.1) :=
    h (e.1, e.2.1) (Or.inl (hactive_of_reach hr))
  have hclockLabel (e : ClockCandidate T R g Ω) {h₀ : ℕ}
      (hr : inBackwardClosure ξ scope t (Sum.inr e.2.1, h₀)) :
      ξ (e.1, e.2.1) = ξ' (e.1, e.2.1) :=
    h (e.1, e.2.1) (Or.inr (hactive_of_reach hr))
  have hclockRelevant (e : ClockCandidate T R g Ω) (hr : relevant e) :
      ξ (e.1, e.2.1) = ξ' (e.1, e.2.1) := by
    rcases hr with ⟨h₀, hr, _⟩ | ⟨h₀, hr, _⟩
    · exact hclockRow e hr
    · exact hclockLabel e hr
  have harrivalRelevant (e : ClockCandidate T R g Ω) (hr : relevant e) :
      candidateIsArrival ξ e ↔ candidateIsArrival ξ' e := by
    have hc := hclockRelevant e hr
    unfold candidateIsArrival
    rw [hc]
  have hreachLabelOfRow (e : ClockCandidate T R g Ω) {h₀ : ℕ}
      (hr : inBackwardClosure ξ scope t (Sum.inl e.1, h₀))
      (hp : eventPriority e < h₀) (he : candidateIsArrival ξ e) :
      inBackwardClosure ξ scope t (Sum.inr e.2.1, eventPriority e) := by
    rcases hr with ⟨a, ha, path⟩
    refine ⟨a, ha, Relation.ReflTransGen.tail path ?_⟩
    exact ⟨e, he, hp, rfl, Or.inl ⟨rfl, rfl⟩⟩
  have hreachRowOfLabel (e : ClockCandidate T R g Ω) {h₀ : ℕ}
      (hr : inBackwardClosure ξ scope t (Sum.inr e.2.1, h₀))
      (hp : eventPriority e < h₀) (he : candidateIsArrival ξ e) :
      inBackwardClosure ξ scope t (Sum.inl e.1, eventPriority e) := by
    rcases hr with ⟨a, ha, path⟩
    refine ⟨a, ha, Relation.ReflTransGen.tail path ?_⟩
    exact ⟨e, he, hp, rfl, Or.inr ⟨rfl, rfl⟩⟩
  have hlistMem (ζ : ClockField T R g Ω) (e : ClockCandidate T R g Ω) :
      e ∈ clockEventList ζ ↔ candidateIsArrival ζ e := by
    simp [clockEventList]
  have hrelMem (e : ClockCandidate T R g Ω) :
      (e ∈ clockEventList ξ ∧ relevant e) ↔ (e ∈ clockEventList ξ' ∧ relevant e) := by
    constructor
    · rintro ⟨he, hr⟩
      have har := hlistMem ξ e |>.mp he
      have har' := (harrivalRelevant e hr).mp har
      exact ⟨hlistMem ξ' e |>.mpr har', hr⟩
    · rintro ⟨he, hr⟩
      have har := hlistMem ξ' e |>.mp he
      have har' := (harrivalRelevant e hr).mpr har
      exact ⟨hlistMem ξ e |>.mpr har', hr⟩
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
      acceptCond ζ s e ↔ acceptCond ζ' s' e := by
    simp [acceptCond, ha, hr, hy]
  have hprocessRow (ζ ζ' : ClockField T R g Ω) (s s' : GreedyState R g Ω)
      (e : ClockCandidate T R g Ω)
      (hc : acceptCond ζ s e ↔ acceptCond ζ' s' e)
      (hr : s.assignment e.1 = s'.assignment e.1) :
      (processArrival ζ s e).assignment e.1 =
        (processArrival ζ' s' e).assignment e.1 := by
    by_cases hacc : acceptCond ζ s e
    · have hacc' := hc.mp hacc
      simp [processArrival, acceptCond, hacc, hacc']
    · have hacc' : ¬ acceptCond ζ' s' e := fun h' => hacc (hc.mpr h')
      simpa [processArrival, acceptCond, hacc, hacc'] using hr
  have hprocessLabel (ζ ζ' : ClockField T R g Ω) (s s' : GreedyState R g Ω)
      (e : ClockCandidate T R g Ω)
      (hc : acceptCond ζ s e ↔ acceptCond ζ' s' e)
      (hy : labelUsed s e.2.1 ↔ labelUsed s' e.2.1) :
      labelUsed (processArrival ζ s e) e.2.1 ↔
        labelUsed (processArrival ζ' s' e) e.2.1 := by
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
    by_cases hacc : candidateIsArrival ζ e ∧ s.assignment e.1 = none ∧
        ¬ labelUsed s e.2.1
    · rw [processArrival, if_pos hacc]
      unfold labelUsed
      constructor
      · rintro ⟨a, o, ha⟩
        by_cases hrow : e.1 = a
        · subst a
          have hEq : some (e.2.1, e.2.2.2) = some (y, o) := by
            simpa using ha
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
      (hs : statusEq s s' u) : statusEq s' s u := by
    cases u with
    | inl a => exact hs.symm
    | inr y => exact hs.symm
  have hstatusTrans (s₁ s₂ s₃ : GreedyState R g Ω) (u : Endpoint R g)
      (h₁ : statusEq s₁ s₂ u) (h₂ : statusEq s₂ s₃ u) :
      statusEq s₁ s₃ u := by
    cases u with
    | inl a => exact h₁.trans h₂
    | inr y => exact h₁.trans h₂
  have hfoldFilter (ζ ζ' : ClockField T R g Ω) :
      ∀ (events : List (ClockCandidate T R g Ω)) (s s' : GreedyState R g Ω) (lo : ℕ),
        events.Pairwise (fun e f => eventPriority e < eventPriority f) →
        (∀ e, e ∈ events → lo ≤ eventPriority e) →
        (∀ e, e ∈ events → candidateIsArrival ζ e) →
        (∀ e, e ∈ events → relevant e → candidateIsArrival ξ e) →
        (∀ e, relevant e → (candidateIsArrival ζ e ↔ candidateIsArrival ζ' e)) →
        (∀ u h₀, inBackwardClosure ξ scope t (u, h₀) → lo ≤ h₀ → statusEq s s' u) →
        ∀ u h₀, inBackwardClosure ξ scope t (u, h₀) → lo ≤ h₀ →
          (∀ e, e ∈ events → eventPriority e < h₀) →
          statusEq (events.foldl (fun st e => processArrival ζ st e) s)
            ((events.filter (fun e => decide (relevant e))).foldl
              (fun st e => processArrival ζ' st e) s') u := by
    intro events
    induction events with
    | nil =>
        intro s s' lo hsorted hlo harr harrXi harrEq hinv u h₀ hr hloh hall
        exact hinv u h₀ hr hloh
    | cons e es ih =>
        intro s s' lo hsorted hlo harr harrXi harrEq hinv u h₀ hr hloh hall
        simp only [List.pairwise_cons] at hsorted
        have hpLo : lo ≤ eventPriority e := hlo e (by simp)
        have hpH : eventPriority e < h₀ := hall e (by simp)
        let sNext := processArrival ζ s e
        let s'Next := if relevant e then processArrival ζ' s' e else s'
        have hinvNext : ∀ v k,
            inBackwardClosure ξ scope t (v, k) → eventPriority e + 1 ≤ k →
              statusEq sNext s'Next v := by
          intro v k hv hpk
          have hpre : statusEq s s' v := hinv v k hv (by omega)
          by_cases hrel : relevant e
          · have heXi := harrXi e (by simp) hrel
            have hrowReach : ∃ kr, inBackwardClosure ξ scope t (Sum.inl e.1, kr) ∧ lo ≤ kr := by
              rcases hrel with ⟨hreq, hreqr, hlt⟩ | ⟨hreq, hreqr, hlt⟩
              · exact ⟨hreq, hreqr, by omega⟩
              · have hr := hreachRowOfLabel e hreqr hlt heXi
                exact ⟨eventPriority e, hr, by omega⟩
            have hlabelReach : ∃ ky, inBackwardClosure ξ scope t (Sum.inr e.2.1, ky) ∧ lo ≤ ky := by
              rcases hrel with ⟨hreq, hreqr, hlt⟩ | ⟨hreq, hreqr, hlt⟩
              · have hr := hreachLabelOfRow e hreqr hlt heXi
                exact ⟨eventPriority e, hr, by omega⟩
              · exact ⟨hreq, hreqr, by omega⟩
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
        by_cases hrel : relevant e
        · have hresult := ih sNext s'Next (eventPriority e + 1) hsorted.2
            hloTail harrTail harrXiTail harrEq hinvNext
          have hallTail : ∀ f, f ∈ es → eventPriority f < h₀ := by
            intro f hf
            exact hall f (List.mem_cons_of_mem e hf)
          have hresult' := hresult u h₀ hr (by omega) hallTail
          simpa [sNext, s'Next, hrel, List.foldl_cons, List.filter] using hresult'
        · have hresult := ih sNext s'Next (eventPriority e + 1) hsorted.2
            hloTail harrTail harrXiTail harrEq hinvNext
          have hallTail : ∀ f, f ∈ es → eventPriority f < h₀ := by
            intro f hf
            exact hall f (List.mem_cons_of_mem e hf)
          have hresult' := hresult u h₀ hr (by omega) hallTail
          simpa [sNext, s'Next, hrel, List.foldl_cons, List.filter] using hresult'
  have hkeyBound (e : ClockCandidate T R g Ω) :
      eventPriority e < T * (Fintype.card R * g) := by
    have hRpos : 0 < Fintype.card R := Fintype.card_pos_iff.mpr ⟨e.1⟩
    have hegy := e.2.1.isLt
    have hgpos : 0 < g := by omega
    let base : ℕ := Fintype.card R * g
    let low : ℕ := ((Fintype.equivFin R) e.1).val * g + e.2.1.val
    have hlow : low < base := by
      dsimp [low, base]
      calc
        ((Fintype.equivFin R) e.1).val * g + e.2.1.val <
            ((Fintype.equivFin R) e.1).val * g + g := Nat.add_lt_add_left e.2.1.isLt _
        _ = Nat.succ ((Fintype.equivFin R) e.1).val * g := by rw [Nat.succ_mul]
        _ ≤ Fintype.card R * g :=
          Nat.mul_le_mul_right g (Nat.succ_le_of_lt ((Fintype.equivFin R e.1).isLt))
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
  have hcommonRelevant : ∀ e, e ∈ common → relevant e := by
    intro e he
    exact of_decide_eq_true (List.mem_filter.mp he).2
  have hcommonFilter : common.filter (fun e => decide (relevant e)) = common := by
    simp [common, List.filter_filter]
  have hempty : ∀ u h₀, inBackwardClosure ξ scope t (u, h₀) →
      0 ≤ h₀ → statusEq emptyGreedyState emptyGreedyState u := by
    intro u h₀ hr hlo
    cases u <;> simp [statusEq, emptyGreedyState, labelUsed]
  have hfullXi (a : R) (ha : a ∈ testRoots scope t) :
      statusEq (greedyMatching ξ) (runGreedy ξ' common) (Sum.inl a) := by
    have hres := hfoldFilter ξ ξ' (clockEventList ξ) emptyGreedyState emptyGreedyState 0
      (hstrict ξ)
      (by intro e he; exact Nat.zero_le _)
      (by intro e he; exact (hlistMem ξ e).mp he)
      (by intro e he hr; exact (hlistMem ξ e).mp he)
      (fun e hr => harrivalRelevant e hr)
      hempty
      (Sum.inl a) (T * (Fintype.card R * g))
      (root_mem_backwardClosure ξ scope t a ha) (Nat.zero_le _)
      (by intro e he; exact hkeyBound e)
    simpa [greedyMatching, runGreedy, common] using hres
  have hfullXi' (a : R) (ha : a ∈ testRoots scope t) :
      statusEq (greedyMatching ξ') (runGreedy ξ common) (Sum.inl a) := by
    have hres := hfoldFilter ξ' ξ (clockEventList ξ') emptyGreedyState emptyGreedyState 0
      (hstrict ξ')
      (by intro e he; exact Nat.zero_le _)
      (by intro e he; exact (hlistMem ξ' e).mp he)
      (by intro e he hr; exact (harrivalRelevant e hr).mpr ((hlistMem ξ' e).mp he))
      (fun e hr => (harrivalRelevant e hr).symm)
      hempty
      (Sum.inl a) (T * (Fintype.card R * g))
      (root_mem_backwardClosure ξ scope t a ha) (Nat.zero_le _)
      (by intro e he; exact hkeyBound e)
    simpa [greedyMatching, runGreedy, common, hrelLists] using hres
  have hcommonFold (a : R) (ha : a ∈ testRoots scope t) :
      statusEq (runGreedy ξ common) (runGreedy ξ' common) (Sum.inl a) := by
    have hres := hfoldFilter ξ ξ' common emptyGreedyState emptyGreedyState 0
      hcommonStrict
      (by intro e he; exact Nat.zero_le _)
      hcommonArrival
      (by intro e he hr; exact hcommonArrival e he)
      (fun e hr => harrivalRelevant e hr)
      hempty
      (Sum.inl a) (T * (Fintype.card R * g))
      (root_mem_backwardClosure ξ scope t a ha) (Nat.zero_le _)
      (by intro e he; exact hkeyBound e)
    simpa [runGreedy, common, hcommonFilter] using hres
  have hrootAssignment (a : R) (ha : a ∈ testRoots scope t) :
      (greedyMatching ξ).assignment a = (greedyMatching ξ').assignment a := by
    have hmid := hstatusTrans (greedyMatching ξ') (runGreedy ξ common)
      (runGreedy ξ' common) (Sum.inl a) (hfullXi' a ha) (hcommonFold a ha)
    have hroot := hstatusTrans (greedyMatching ξ) (runGreedy ξ' common)
      (greedyMatching ξ') (Sum.inl a) (hfullXi a ha)
      (hstatusSymm (greedyMatching ξ') (runGreedy ξ' common) (Sum.inl a) hmid)
    simpa [statusEq] using hroot
  cases t with
  | predicate k =>
      simp only [testFails]
      constructor
      · rintro ⟨ω, hF, hm⟩
        refine ⟨ω, hF, ?_⟩
        intro a ha
        rcases hm a ha with ⟨y, hy⟩
        have haRoot : a ∈ testRoots scope (SamplingTest.predicate k) := by
          simpa [testRoots] using ha
        exact ⟨y, (hrootAssignment a haRoot).symm.trans hy⟩
      · rintro ⟨ω, hF, hm⟩
        refine ⟨ω, hF, ?_⟩
        intro a ha
        rcases hm a ha with ⟨y, hy⟩
        have haRoot : a ∈ testRoots scope (SamplingTest.predicate k) := by
          simpa [testRoots] using ha
        exact ⟨y, (hrootAssignment a haRoot).trans hy⟩
  | singleton a =>
      change ((greedyMatching ξ).assignment a = none) ↔
        ((greedyMatching ξ').assignment a = none)
      rw [hrootAssignment a (by simp [testRoots])]

end HypercubeRamsey.Clock
