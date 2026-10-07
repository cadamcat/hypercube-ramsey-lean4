import HypercubeRamsey.S03.Clock.Steps_p_clock_r4
import HypercubeRamsey.Tools.Concentration
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics

namespace HypercubeRamsey.Lane_sol_clock_s6

open scoped BigOperators
open HypercubeRamsey.Clock
open Classical

/-- What has been observed of one first-arrival clock before tick `t`. -/
def clockPrefix {T : ℕ} {α : Type*} (t : ℕ) : MeshClockValue T α → MeshClockValue T α
  | .noArrival => .noArrival
  | .tick s a => if s.val < t then .tick s a else .noArrival

theorem clockPrefix_noArrival_probability {T : ℕ} {α : Type*}
    [Fintype α] [DecidableEq α]
    (δ r : ℝ) (μ : α → ℝ) (hδ : 0 ≤ δ) (hbase : 0 ≤ 1 - δ * r)
    (hr : 0 ≤ r) (hμ : ∀ a, 0 ≤ μ a) (hsum : ∑ a, μ a = r)
    (t : ℕ) (ht : t ≤ T) :
    (markedClockLaw (T := T) δ r μ hδ hbase hr hμ hsum).pr
      (fun x => clockPrefix t x = .noArrival) = survival δ r t := by
  classical
  rw [FinProb.pr]
  convert markedClockLaw_survival δ r μ hδ hbase hr hμ hsum t ht using 1
  apply Finset.sum_congr rfl
  intro x _
  cases x with
  | noArrival => simp [clockPrefix]
  | tick s a =>
      by_cases h : s.val < t <;> simp [clockPrefix, h]

theorem clock_tick_probability {T : ℕ} {α : Type*}
    [Fintype α] [DecidableEq α]
    (δ r : ℝ) (μ : α → ℝ) (hδ : 0 ≤ δ) (hbase : 0 ≤ 1 - δ * r)
    (hr : 0 ≤ r) (hμ : ∀ a, 0 ≤ μ a) (hsum : ∑ a, μ a = r)
    (t : Fin T) :
    (markedClockLaw (T := T) δ r μ hδ hbase hr hμ hsum).pr
      (fun x => ∃ a, x = .tick t a) = survival δ r t.val * (δ * r) := by
  classical
  let e : MeshClockValue T α ≃ Unit ⊕ (Fin T × α) := {
    toFun := fun x => match x with
      | .noArrival => .inl ()
      | .tick s a => .inr (s, a)
    invFun := fun x => match x with
      | .inl _ => .noArrival
      | .inr p => .tick p.1 p.2
    left_inv := by intro x; cases x <;> rfl
    right_inv := by intro x; cases x <;> rfl
  }
  unfold FinProb.pr
  rw [← Equiv.sum_comp e.symm]
  simp [e, Fintype.sum_sum_type, Fintype.sum_prod_type,
    markedClockLaw, markedClockWeight, ← Finset.mul_sum, hsum, mul_assoc]

/-- The exact geometric hazard, written without conditional division. -/
theorem clock_prefix_hazard {T : ℕ} {α : Type*}
    [Fintype α] [DecidableEq α]
    (δ r : ℝ) (μ : α → ℝ) (hδ : 0 ≤ δ) (hbase : 0 ≤ 1 - δ * r)
    (hr : 0 ≤ r) (hμ : ∀ a, 0 ≤ μ a) (hsum : ∑ a, μ a = r)
    (t : Fin T) :
    (markedClockLaw (T := T) δ r μ hδ hbase hr hμ hsum).pr
      (fun x => clockPrefix t.val x = .noArrival ∧ ∃ a, x = .tick t a) =
      δ * r * (markedClockLaw (T := T) δ r μ hδ hbase hr hμ hsum).pr
        (fun x => clockPrefix t.val x = .noArrival) := by
  have hevent : (fun x : MeshClockValue T α =>
      clockPrefix t.val x = .noArrival ∧ ∃ a, x = .tick t a) =
      (fun x => ∃ a, x = .tick t a) := by
    funext x
    apply propext
    constructor
    · exact And.right
    · rintro ⟨a, rfl⟩
      exact ⟨by simp [clockPrefix], ⟨a, rfl⟩⟩
  rw [hevent, clock_tick_probability, clockPrefix_noArrival_probability]
  · ring
  · exact Nat.le_of_lt t.isLt

/-- Adding one coordinate restriction to a product rectangle preserves an
exact one-coordinate hazard factor. -/
theorem rectangle_coordinate_factor {ι : Type*} [Fintype ι] [DecidableEq ι]
    {α : ι → Type*} [∀ i, Fintype (α i)]
    (P : ∀ i, FinProb (α i)) (A : ∀ i, α i → Prop)
    (e : ι) (J : α e → Prop) (q : ℝ)
    (hJ : (P e).pr (fun x => A e x ∧ J x) = q * (P e).pr (A e)) :
    (FinProb.pi P).pr (fun x => (∀ i, A i (x i)) ∧ J (x e)) =
      q * (FinProb.pi P).pr (fun x => ∀ i, A i (x i)) := by
  classical
  let C : ∀ i, α i → Prop := Function.update A e (fun x => A e x ∧ J x)
  have hevent : (fun x : ∀ i, α i => (∀ i, A i (x i)) ∧ J (x e)) =
      (fun x => ∀ i, C i (x i)) := by
    funext x
    apply propext
    constructor
    · rintro ⟨hA, hJ⟩ i
      by_cases hi : i = e
      · subst i; simpa [C] using And.intro (hA e) hJ
      · simpa [C, hi] using hA i
    · intro hC
      refine ⟨?_, ?_⟩
      · intro i
        by_cases hi : i = e
        · subst i; exact (by simpa [C] using hC e : A e (x e) ∧ J (x e)).1
        · simpa [C, hi] using hC i
      · exact (by simpa [C] using hC e : A e (x e) ∧ J (x e)).2
  rw [hevent, pi_pr_forall_coordinates, pi_pr_forall_coordinates]
  have hfactor (i : ι) : (P i).pr (C i) =
      (if i = e then q else 1) * (P i).pr (A i) := by
    by_cases hi : i = e
    · subst i; simpa [C] using hJ
    · simp [C, hi]
  simp_rw [hfactor]
  rw [Finset.prod_mul_distrib]
  simp

/-- A sorted list splits into its strict prefix and its events at the next key. -/
theorem sorted_filter_successor {α : Type*} (key : α → ℕ) (xs : List α)
    (hs : xs.Pairwise (fun a b => key a ≤ key b)) (k : ℕ) :
    xs.filter (fun a => key a < k + 1) =
      xs.filter (fun a => key a < k) ++ xs.filter (fun a => key a = k) := by
  classical
  induction xs with
  | nil => simp
  | cons a xs ih =>
      rcases List.pairwise_cons.mp hs with ⟨hhead, htail⟩
      by_cases ha : key a < k
      · simp only [List.filter_cons, decide_eq_true (show key a < k + 1 by omega),
          decide_eq_true ha, decide_eq_false (show key a ≠ k by omega),
          Bool.false_eq_true, ↓reduceIte, List.cons_append]
        rw [ih htail]
      · by_cases heq : key a = k
        · have hnil : xs.filter (fun b => key b < k) = [] := by
            apply List.filter_eq_nil_iff.mpr
            intro b hb
            simp only [decide_eq_true_eq]
            have hle := hhead b hb
            omega
          simp only [List.filter_cons, decide_eq_true (show key a < k + 1 by omega),
            decide_eq_false ha, decide_eq_true heq, Bool.false_eq_true, ↓reduceIte]
          rw [ih htail, hnil]
          rfl
        · have hnil₁ : xs.filter (fun b => key b < k) = [] := by
            apply List.filter_eq_nil_iff.mpr
            intro b hb
            simp only [decide_eq_true_eq]
            have hle := hhead b hb
            omega
          have hnil₂ : xs.filter (fun b => key b = k) = [] := by
            apply List.filter_eq_nil_iff.mpr
            intro b hb
            simp only [decide_eq_true_eq]
            have hle := hhead b hb
            omega
          have hnil₃ : xs.filter (fun b => key b < k + 1) = [] := by
            apply List.filter_eq_nil_iff.mpr
            intro b hb
            simp only [decide_eq_true_eq]
            have hle := hhead b hb
            omega
          simp only [List.filter_cons, decide_eq_false ha, decide_eq_false heq,
            decide_eq_false (show ¬ key a < k + 1 by omega), Bool.false_eq_true, ↓reduceIte,
            hnil₁, hnil₂, hnil₃, List.nil_append]

noncomputable def edgeRank {R : Type*} [Fintype R] [DecidableEq R] {g : ℕ}
    (e : RowLabel R g) : ℕ :=
  ((Fintype.equivFin R) e.1).val * g + e.2.val

noncomputable def edgeKey {R : Type*} [Fintype R] [DecidableEq R] {g : ℕ}
    (e : RowLabel R g) (t : ℕ) : ℕ := t * (Fintype.card R * g) + edgeRank e

noncomputable def edgeEquiv {R : Type*} [Fintype R] [DecidableEq R] {g : ℕ} :
    RowLabel R g ≃ Fin (Fintype.card R * g) :=
  (Equiv.prodCongr (Fintype.equivFin R) (Equiv.refl (Fin g))).trans finProdFinEquiv

theorem edgeEquiv_val {R : Type*} [Fintype R] [DecidableEq R] {g : ℕ}
    (e : RowLabel R g) : (edgeEquiv e).val = edgeRank e := by
  simp [edgeEquiv, edgeRank, finProdFinEquiv, Nat.add_comm, Nat.mul_comm]

noncomputable def timeEdgeEquiv {T : ℕ} {R : Type*} [Fintype R] [DecidableEq R] {g : ℕ} :
    Fin T × RowLabel R g ≃ Fin (T * (Fintype.card R * g)) :=
  (Equiv.prodCongr (Equiv.refl (Fin T)) edgeEquiv).trans finProdFinEquiv

theorem timeEdgeEquiv_val {T : ℕ} {R : Type*} [Fintype R] [DecidableEq R] {g : ℕ}
    (t : Fin T) (e : RowLabel R g) : (timeEdgeEquiv (t, e)).val = edgeKey e t.val := by
  simp [timeEdgeEquiv, finProdFinEquiv, edgeEquiv_val, edgeKey, Nat.add_comm, Nat.mul_comm]

theorem edgeKey_injective {T : ℕ} {R : Type*} [Fintype R] [DecidableEq R] {g : ℕ}
    {t s : Fin T} {e f : RowLabel R g} (h : edgeKey e t.val = edgeKey f s.val) :
    (t, e) = (s, f) := by
  apply timeEdgeEquiv.injective
  apply Fin.ext
  simpa [timeEdgeEquiv_val] using h

noncomputable def observeClock {T : ℕ} {R : Type*} [Fintype R] [DecidableEq R]
    {g : ℕ} {Ω : R → Type*} (k : ℕ) (e : RowLabel R g) :
    MeshClockValue T (Ω e.1) → MeshClockValue T (Ω e.1)
  | .noArrival => .noArrival
  | .tick t a => if edgeKey e t.val < k then .tick t a else .noArrival

noncomputable def observedField {T : ℕ} {R : Type*} [Fintype R] [DecidableEq R]
    {g : ℕ} {Ω : R → Type*} (k : ℕ) (ξ : ClockField T R g Ω) : ClockField T R g Ω :=
  fun e => observeClock k e (ξ e)

theorem observeClock_at_edgeKey {T : ℕ} {R : Type*} [Fintype R] [DecidableEq R]
    {g : ℕ} {Ω : R → Type*} (e : RowLabel R g) (t : ℕ)
    (x : MeshClockValue T (Ω e.1)) :
    observeClock (edgeKey e t) e x = clockPrefix t x := by
  have hM : 0 < Fintype.card R * g :=
    Nat.mul_pos (Fintype.card_pos_iff.mpr ⟨e.1⟩) (by have h := e.2.isLt; omega)
  cases x with
  | noArrival => rfl
  | tick s a =>
      have hkey : edgeKey e s.val < edgeKey e t ↔ s.val < t := by
        unfold edgeKey
        constructor
        · intro h
          have hmul : s.val * (Fintype.card R * g) < t * (Fintype.card R * g) := by omega
          nlinarith
        · intro h
          have hmul := Nat.mul_lt_mul_of_pos_right h hM
          omega
      simp [observeClock, clockPrefix, hkey]

/-- A complete observed history is a product rectangle. Its next ordinary
arrival has the same exact hazard as its one-edge geometric clock. -/
theorem observedField_fiber_hazard {T : ℕ} {R : Type*} [Fintype R] [DecidableEq R]
    {g : ℕ} {Ω : R → Type*} [∀ a, Fintype (Ω a)] [∀ a, DecidableEq (Ω a)]
    (δ : ℝ) (r : RowLabel R g → ℝ) (μ : ∀ e : RowLabel R g, Ω e.1 → ℝ)
    (hδ : 0 ≤ δ) (hbase : ∀ e, 0 ≤ 1 - δ * r e)
    (hr : ∀ e, 0 ≤ r e) (hμ : ∀ e a, 0 ≤ μ e a)
    (hsum : ∀ e, ∑ a, μ e a = r e)
    (e : RowLabel R g) (t : Fin T) (h : ClockField T R g Ω)
    (he : h e = .noArrival) :
    (clockFieldLaw (fun f => markedClockLaw δ (r f) (μ f) hδ (hbase f)
      (hr f) (hμ f) (hsum f))).pr
      (fun ξ => observedField (edgeKey e t.val) ξ = h ∧ ∃ a, ξ e = .tick t a) =
      δ * r e * (clockFieldLaw (fun f => markedClockLaw δ (r f) (μ f) hδ (hbase f)
        (hr f) (hμ f) (hsum f))).pr
        (fun ξ => observedField (edgeKey e t.val) ξ = h) := by
  let A : ∀ f : RowLabel R g, MeshClockValue T (Ω f.1) → Prop :=
    fun f x => observeClock (edgeKey e t.val) f x = h f
  have hfiber (ξ : ClockField T R g Ω) :
      observedField (edgeKey e t.val) ξ = h ↔ ∀ f, A f (ξ f) := by
    exact ⟨fun hx f => congrFun hx f, fun hx => funext hx⟩
  simp_rw [hfiber]
  unfold clockFieldLaw
  apply rectangle_coordinate_factor
    (fun f => markedClockLaw (T := T) δ (r f) (μ f) hδ (hbase f) (hr f) (hμ f) (hsum f))
    A e (fun x => ∃ a, x = .tick t a) (δ * r e)
  simp only [A, he, observeClock_at_edgeKey]
  exact clock_prefix_hazard δ (r e) (μ e) hδ (hbase e) (hr e) (hμ e) (hsum e) t

noncomputable def keyEvents {T : ℕ} {R : Type*} [Fintype R] [DecidableEq R]
    {g : ℕ} {Ω : R → Type*} [∀ a, Fintype (Ω a)] [∀ a, DecidableEq (Ω a)]
    (ξ : ClockField T R g Ω) (removedRows : Finset R)
    (removedLabels : Finset (Fin g)) (k : ℕ) : List (ClockCandidate T R g Ω) := by
  classical
  exact (clockEventList ξ).filter (fun e => eventPriority e < k ∧
    e.1 ∉ removedRows ∧ e.2.1 ∉ removedLabels)

noncomputable def keyMatching {T : ℕ} {R : Type*} [Fintype R] [DecidableEq R]
    {g : ℕ} {Ω : R → Type*} [∀ a, Fintype (Ω a)] [∀ a, DecidableEq (Ω a)]
    (ξ : ClockField T R g Ω) (removedRows : Finset R)
    (removedLabels : Finset (Fin g)) (k : ℕ) : GreedyState R g Ω :=
  runGreedy ξ (keyEvents ξ removedRows removedLabels k)

theorem keyEvents_observed {T : ℕ} {R : Type*} [Fintype R] [DecidableEq R]
    {g : ℕ} {Ω : R → Type*} [∀ a, Fintype (Ω a)] [∀ a, DecidableEq (Ω a)]
    (ξ : ClockField T R g Ω) (removedRows : Finset R)
    (removedLabels : Finset (Fin g)) (k : ℕ) :
    keyEvents (observedField k ξ) removedRows removedLabels k =
      keyEvents ξ removedRows removedLabels k := by
  classical
  have harr (e : ClockCandidate T R g Ω) (he : eventPriority e < k) :
      candidateIsArrival (observedField k ξ) e ↔ candidateIsArrival ξ e := by
    have hekey : edgeKey (e.1, e.2.1) e.2.2.1.val < k := by
      simpa [edgeKey, edgeRank, eventPriority, Nat.add_assoc] using he
    unfold candidateIsArrival observedField
    cases hval : ξ (e.1, e.2.1) with
    | noArrival => simp [observeClock]
    | tick t a =>
        by_cases ht : edgeKey (e.1, e.2.1) t.val < k
        · simp [observeClock, ht]
        · have hn : MeshClockValue.tick t a ≠ MeshClockValue.tick e.2.2.1 e.2.2.2 := by
            intro h
            have htime : t = e.2.2.1 := by injection h
            subst t
            exact ht hekey
          simp [observeClock, ht, hn]
  have hnodup (ζ : ClockField T R g Ω) :
      (keyEvents ζ removedRows removedLabels k).Nodup := by
    unfold keyEvents clockEventList
    exact ((List.mergeSort_perm _ _).nodup_iff.mpr (Finset.nodup_toList _)).filter _
  have hsort (ζ : ClockField T R g Ω) :
      (keyEvents ζ removedRows removedLabels k).Pairwise
        (fun e f => eventPriority e ≤ eventPriority f) := by
    exact (clockEventList_sorted ζ).filter _
  have hmem (ζ : ClockField T R g Ω) (e : ClockCandidate T R g Ω) :
      e ∈ keyEvents ζ removedRows removedLabels k ↔
        candidateIsArrival ζ e ∧ eventPriority e < k ∧
          e.1 ∉ removedRows ∧ e.2.1 ∉ removedLabels := by
    simp [keyEvents, List.mem_filter, clockEventList_mem_iff_p_clock_r4, and_assoc]
  have hset : (keyEvents (observedField k ξ) removedRows removedLabels k).toFinset =
      (keyEvents ξ removedRows removedLabels k).toFinset := by
    ext e
    simp only [List.mem_toFinset, hmem]
    by_cases he : eventPriority e < k
    · rw [harr e he]
    · simp [he]
  have hperm := List.perm_of_nodup_nodup_toFinset_eq
    (hnodup (observedField k ξ)) (hnodup ξ) hset
  apply hperm.eq_of_pairwise ?_ (hsort (observedField k ξ)) (hsort ξ)
  intro e f he hf hef hfe
  apply clockCandidate_eq_of_priority_eq ξ e f
  · have he' := (hmem (observedField k ξ) e).mp he
    exact (harr e he'.2.1).mp he'.1
  · exact ((hmem ξ f).mp hf).1
  · omega

theorem keyMatching_observed {T : ℕ} {R : Type*} [Fintype R] [DecidableEq R]
    {g : ℕ} {Ω : R → Type*} [∀ a, Fintype (Ω a)] [∀ a, DecidableEq (Ω a)]
    (ξ : ClockField T R g Ω) (removedRows : Finset R)
    (removedLabels : Finset (Fin g)) (k : ℕ) :
    keyMatching (observedField k ξ) removedRows removedLabels k =
      keyMatching ξ removedRows removedLabels k := by
  classical
  unfold keyMatching
  rw [keyEvents_observed]
  have hfold : ∀ (events : List (ClockCandidate T R g Ω))
      (hs : ∀ e ∈ events, candidateIsArrival (observedField k ξ) e ∧ candidateIsArrival ξ e)
      (s : GreedyState R g Ω),
      events.foldl (fun s e => processArrival (observedField k ξ) s e) s =
        events.foldl (fun s e => processArrival ξ s e) s := by
    intro events
    induction events with
    | nil => intro _ _; rfl
    | cons e events ih =>
        intro hs s
        have he := hs e (by simp)
        have hstep : processArrival (observedField k ξ) s e = processArrival ξ s e := by
          simp [processArrival, he.1, he.2]
        simp only [List.foldl_cons, hstep]
        exact ih (by intro f hf; exact hs f (by simp [hf])) _
  apply hfold
  intro e he
  have hobs : e ∈ keyEvents (observedField k ξ) removedRows removedLabels k := by
    rw [keyEvents_observed]; exact he
  exact ⟨(clockEventList_mem_iff_p_clock_r4 _ _).mp (List.mem_filter.mp hobs).1,
    (clockEventList_mem_iff_p_clock_r4 _ _).mp (List.mem_filter.mp he).1⟩

def keyFree {T : ℕ} {R : Type*} [Fintype R] [DecidableEq R]
    {g : ℕ} {Ω : R → Type*} [∀ a, Fintype (Ω a)] [∀ a, DecidableEq (Ω a)]
    (ξ : ClockField T R g Ω) (removedRows : Finset R)
    (removedLabels : Finset (Fin g)) (k : ℕ) (e : RowLabel R g) : Prop :=
  e.1 ∉ removedRows ∧ e.2 ∉ removedLabels ∧
    (keyMatching ξ removedRows removedLabels k).assignment e.1 = none ∧
      ¬ labelUsed (keyMatching ξ removedRows removedLabels k) e.2

/-- A free edge cannot have an already observed arrival: that arrival would
have matched the two endpoints while they were free. -/
theorem keyFree_prefix_empty {T : ℕ} {R : Type*} [Fintype R] [DecidableEq R]
    {g : ℕ} {Ω : R → Type*} [∀ a, Fintype (Ω a)] [∀ a, DecidableEq (Ω a)]
    (ξ : ClockField T R g Ω) (removedRows : Finset R)
    (removedLabels : Finset (Fin g)) (k : ℕ) (e : RowLabel R g)
    (hfree : keyFree ξ removedRows removedLabels k e) :
    observeClock k e (ξ e) = .noArrival := by
  classical
  rcases hfree with ⟨hr, hy, hrow, hlabel⟩
  cases hξ : ξ e with
  | noArrival => simp [observeClock]
  | tick t a =>
      by_cases ht : edgeKey e t.val < k
      · have harr : candidateIsArrival ξ ⟨e.1, e.2, t, a⟩ := hξ
        have hmem : (⟨e.1, e.2, t, a⟩ : ClockCandidate T R g Ω) ∈
            keyEvents ξ removedRows removedLabels k := by
          simp only [keyEvents, List.mem_filter, clockEventList_mem_iff_p_clock_r4,
            decide_eq_true_eq]
          refine ⟨harr, ?_, hr, hy⟩
          simpa [eventPriority, edgeKey, edgeRank, Nat.add_assoc] using ht
        have heq := runGreedy_filter_unmatched_row ξ
          (keyEvents ξ removedRows removedLabels k) e.1 hrow
        have hfree' : ¬ labelUsed
            (runGreedy ξ ((keyEvents ξ removedRows removedLabels k).filter
              (fun f => f.1 ≠ e.1))) e.2 := by
          rw [← heq]
          exact hlabel
        exact False.elim (runGreedy_unmatched_row_no_arrival_to_free_label ξ
          (keyEvents ξ removedRows removedLabels k) e.1 e.2 hrow hfree'
          (by
            intro f hf
            exact (clockEventList_mem_iff_p_clock_r4 _ _).mp (List.mem_filter.mp hf).1)
          ⟨e.1, e.2, t, a⟩ hmem rfl rfl)
      · simp [observeClock, ht]

theorem observedField_project {T : ℕ} {R : Type*} [Fintype R] [DecidableEq R]
    {g : ℕ} {Ω : R → Type*} (k : ℕ) (ξ : ClockField T R g Ω) :
    observedField k (observedField (k + 1) ξ) = observedField k ξ := by
  funext e
  unfold observedField
  cases ξ e with
  | noArrival => rfl
  | tick t a =>
      by_cases h : edgeKey e t.val < k
      · simp [observeClock, h, show edgeKey e t.val < k + 1 by omega]
      · by_cases h' : edgeKey e t.val < k + 1 <;> simp [observeClock, h, h']

theorem keyMatching_depends_on_observation {T : ℕ} {R : Type*}
    [Fintype R] [DecidableEq R] {g : ℕ} {Ω : R → Type*}
    [∀ a, Fintype (Ω a)] [∀ a, DecidableEq (Ω a)]
    (ξ ξ' : ClockField T R g Ω) (removedRows : Finset R)
    (removedLabels : Finset (Fin g)) (k : ℕ)
    (h : observedField k ξ = observedField k ξ') :
    keyMatching ξ removedRows removedLabels k =
      keyMatching ξ' removedRows removedLabels k := by
  rw [← keyMatching_observed ξ, ← keyMatching_observed ξ', h]

/-- The conditional first and second moments of a gated Bernoulli decrement. -/
theorem gated_indicator_moments {α H : Type*} [Fintype α] [Fintype H] [DecidableEq H]
    (P : FinProb α) (history : α → H) (gate J : α → Prop)
    [DecidablePred gate] [DecidablePred J]
    (w q : ℝ) (hw : 0 ≤ w) (hq0 : 0 ≤ q) (hq1 : q ≤ 1)
    (hgate : ∀ x x', history x = history x' → (gate x ↔ gate x'))
    (hhazard : ∀ h, (∃ x, history x = h ∧ gate x) →
      P.pr (fun x => history x = h ∧ J x) =
        q * P.pr (fun x => history x = h)) :
    let Δ : α → ℝ := fun x => if gate x then w * ((if J x then 1 else 0) - q) else 0
    (∀ x, |Δ x| ≤ w) ∧
    (∀ h, (∑ x, if history x = h then P.w x * Δ x else 0) = 0) ∧
    (∀ h, (∑ x, if history x = h then P.w x * (Δ x) ^ 2 else 0) ≤
      w ^ 2 * q * P.pr (fun x => history x = h)) := by
  classical
  dsimp only
  let Δ : α → ℝ := fun x => if gate x then w * ((if J x then 1 else 0) - q) else 0
  have hΔ : ∀ x, |Δ x| ≤ w := by
    intro x
    dsimp [Δ]
    by_cases hg : gate x
    · rw [if_pos hg, abs_mul, abs_of_nonneg hw]
      have hcenter : |(if J x then 1 else 0) - q| ≤ 1 := by
        apply abs_le.mpr
        by_cases hj : J x <;> simp [hj] <;> constructor <;> linarith
      simpa using mul_le_mul_of_nonneg_left hcenter hw
    · simp [hg, hw]
  have hfiber (h : H) :
      (∑ x, if history x = h then P.w x * Δ x else 0) = 0 ∧
      (∑ x, if history x = h then P.w x * (Δ x) ^ 2 else 0) ≤
        w ^ 2 * q * P.pr (fun x => history x = h) := by
    by_cases hex : ∃ x, history x = h ∧ gate x
    · obtain ⟨x₀, hx₀, hg₀⟩ := hex
      have hg : ∀ x, history x = h → gate x := by
        intro x hx
        exact (hgate x x₀ (hx.trans hx₀.symm)).mpr hg₀
      have hJ := hhazard h ⟨x₀, hx₀, hg₀⟩
      have hmean : (∑ x, if history x = h then P.w x * Δ x else 0) =
          w * (P.pr (fun x => history x = h ∧ J x) -
            q * P.pr (fun x => history x = h)) := by
        unfold FinProb.pr
        rw [Finset.mul_sum, ← Finset.sum_sub_distrib, Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro x _
        by_cases hx : history x = h
        · by_cases hj : J x <;> simp [Δ, hx, hg x hx, hj] <;> ring
        · simp [hx]
      have hsecond : (∑ x, if history x = h then P.w x * (Δ x) ^ 2 else 0) =
          w ^ 2 * ((1 - 2 * q) * P.pr (fun x => history x = h ∧ J x) +
            q ^ 2 * P.pr (fun x => history x = h)) := by
        unfold FinProb.pr
        simp only [Finset.mul_sum, Finset.sum_add_distrib]
        rw [← Finset.sum_add_distrib]
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro x _
        by_cases hx : history x = h
        · by_cases hj : J x <;> simp [Δ, hx, hg x hx, hj] <;> ring
        · simp [hx]
      constructor
      · rw [hmean, hJ]; ring
      · rw [hsecond, hJ]
        have hprob : 0 ≤ P.pr (fun x => history x = h) := by
          unfold FinProb.pr
          exact Finset.sum_nonneg fun x _ => by split_ifs <;> simp [P.nonneg x]
        have hq : (1 - 2 * q) * (q * P.pr (fun x => history x = h)) +
            q ^ 2 * P.pr (fun x => history x = h) ≤ q * P.pr (fun x => history x = h) := by
          nlinarith [mul_nonneg (sq_nonneg q) hprob]
        exact (mul_le_mul_of_nonneg_left hq (sq_nonneg w)).trans_eq (by ring)
    · have hz : ∀ x, history x = h → Δ x = 0 := by
        intro x hx
        have hg : ¬ gate x := by intro hg; exact hex ⟨x, hx, hg⟩
        simp [Δ, hg]
      have hzero (f : ℝ → ℝ) (hf : f 0 = 0) :
          (∑ x, if history x = h then P.w x * f (Δ x) else 0) = 0 := by
        apply Finset.sum_eq_zero
        intro x _
        by_cases hx : history x = h
        · simp [hx, hz x hx, hf]
        · simp [hx]
      refine ⟨hzero id rfl, ?_⟩
      rw [hzero (fun z => z ^ 2) (by simp)]
      have hprob : 0 ≤ P.pr (fun x => history x = h) := by
        unfold FinProb.pr
        exact Finset.sum_nonneg fun x _ => by split_ifs <;> simp [P.nonneg x]
      exact mul_nonneg (mul_nonneg (sq_nonneg w) hq0) hprob
  exact ⟨hΔ, fun h => (hfiber h).1, fun h => (hfiber h).2⟩

theorem freedman_absolute {α : Type*} [Fintype α] {k : ℕ}
    (H : Fin (k + 1) → Type*) [∀ t, Fintype (H t)] [∀ t, DecidableEq (H t)]
    (P : FinProb α) (history : ∀ t, α → H t)
    (project : ∀ i : Fin k, H i.succ → H i.castSucc)
    (hfiltration : ∀ i x, history i.castSucc x = project i (history i.succ x))
    (Δ : Fin k → α → ℝ)
    (hadapted : ∀ (m : ℕ) (hm : m ≤ k) (i : Fin k), i.val < m →
      ∀ x x', history ⟨m, Nat.lt_succ_of_le hm⟩ x =
        history ⟨m, Nat.lt_succ_of_le hm⟩ x' → Δ i x = Δ i x')
    (c : ℝ) (hc : 0 < c) (v : Fin k → ℝ) (hv : ∀ i, 0 ≤ v i)
    (hbound : ∀ i x, |Δ i x| ≤ c)
    (hmean : ∀ i (h : H i.castSucc),
      (∑ x, if history i.castSucc x = h then P.w x * Δ i x else 0) = 0)
    (hvariance : ∀ i (h : H i.castSucc),
      (∑ x, if history i.castSucc x = h then P.w x * (Δ i x) ^ 2 else 0) ≤
        v i * P.pr (fun x => history i.castSucc x = h))
    (t : ℝ) (ht : 0 < t) :
    P.pr (fun x => t ≤ |∑ i, Δ i x|) ≤
      2 * Real.exp (-t ^ 2 / (2 * (∑ i, v i + c * t / 3))) := by
  classical
  have hpositive := xFreedman H P history project hfiltration Δ hadapted
    c hc v hv hbound hmean hvariance t ht
  have hnegative := xFreedman H P history project hfiltration
    (fun i x => -Δ i x)
    (by intro m hm i hi x x' hh; rw [hadapted m hm i hi x x' hh])
    c hc v hv (by intro i x; simpa using hbound i x)
    (by
      intro i h
      have heq : (∑ x, if history i.castSucc x = h then P.w x * -Δ i x else 0) =
          -(∑ x, if history i.castSucc x = h then P.w x * Δ i x else 0) := by
        rw [← Finset.sum_neg_distrib]
        apply Finset.sum_congr rfl
        intro x _
        by_cases hx : history i.castSucc x = h <;> simp [hx]
      rw [heq, hmean]; simp)
    (by intro i h; simpa using hvariance i h) t ht
  have hcover : P.pr (fun x => t ≤ |∑ i, Δ i x|) ≤
      P.pr (fun x => t ≤ ∑ i, Δ i x) +
        P.pr (fun x => t ≤ ∑ i, -Δ i x) := by
    apply (finProb_pr_mono P ?_).trans (FinProb.pr_union P _ _)
    intro x hx
    rw [Finset.sum_neg_distrib]
    by_cases hs : 0 ≤ ∑ i, Δ i x
    · left; simpa [abs_of_nonneg hs] using hx
    · right; simpa [abs_of_neg (lt_of_not_ge hs)] using hx
  linarith

theorem completed_row_card {R : Type*} [Fintype R] {g : ℕ}
    {Ω : R → Type*} [∀ a, Fintype (Ω a)]
    (p : ∀ a, FinProb (Ω a)) (lab : ∀ a, Ω a → Fin g) (θ : ℝ)
    (hcol : ∀ y, ∑ a, labMarg (p a) (lab a) y = θ) :
    (Fintype.card R : ℝ) = θ * (g : ℝ) := by
  calc
    (Fintype.card R : ℝ) = ∑ a : R, (1 : ℝ) := by simp
    _ = ∑ a : R, ∑ y, labMarg (p a) (lab a) y := by
      simp_rw [labMarg_sum_one]
    _ = ∑ y : Fin g, ∑ a, labMarg (p a) (lab a) y := Finset.sum_comm
    _ = θ * (g : ℝ) := by simp [hcol, mul_comm]

noncomputable def atKeyEvents {T : ℕ} {R : Type*} [Fintype R] [DecidableEq R]
    {g : ℕ} {Ω : R → Type*} [∀ a, Fintype (Ω a)] [∀ a, DecidableEq (Ω a)]
    (ξ : ClockField T R g Ω) (removedRows : Finset R)
    (removedLabels : Finset (Fin g)) (k : ℕ) : List (ClockCandidate T R g Ω) := by
  classical
  exact (clockEventList ξ).filter (fun e => eventPriority e = k ∧
    e.1 ∉ removedRows ∧ e.2.1 ∉ removedLabels)

theorem keyEvents_successor {T : ℕ} {R : Type*} [Fintype R] [DecidableEq R]
    {g : ℕ} {Ω : R → Type*} [∀ a, Fintype (Ω a)] [∀ a, DecidableEq (Ω a)]
    (ξ : ClockField T R g Ω) (removedRows : Finset R)
    (removedLabels : Finset (Fin g)) (k : ℕ) :
    keyEvents ξ removedRows removedLabels (k + 1) =
      keyEvents ξ removedRows removedLabels k ++ atKeyEvents ξ removedRows removedLabels k := by
  classical
  let xs := (clockEventList ξ).filter (fun e =>
    e.1 ∉ removedRows ∧ e.2.1 ∉ removedLabels)
  have hsort : xs.Pairwise (fun e f => eventPriority e ≤ eventPriority f) :=
    (clockEventList_sorted ξ).filter _
  have h := sorted_filter_successor eventPriority xs hsort k
  simpa [xs, keyEvents, atKeyEvents, List.filter_filter,
    and_assoc, and_comm, and_left_comm, Bool.and_assoc, Bool.and_comm, Bool.and_left_comm] using h

theorem atKeyEvents_tick {T : ℕ} {R : Type*} [Fintype R] [DecidableEq R]
    {g : ℕ} {Ω : R → Type*} [∀ a, Fintype (Ω a)] [∀ a, DecidableEq (Ω a)]
    (ξ : ClockField T R g Ω) (removedRows : Finset R)
    (removedLabels : Finset (Fin g)) (e : RowLabel R g) (t : Fin T) (a : Ω e.1)
    (hξ : ξ e = .tick t a) (hr : e.1 ∉ removedRows) (hy : e.2 ∉ removedLabels) :
    atKeyEvents ξ removedRows removedLabels (edgeKey e t.val) = [⟨e.1, e.2, t, a⟩] := by
  classical
  let cand : ClockCandidate T R g Ω := ⟨e.1, e.2, t, a⟩
  have harr : candidateIsArrival ξ cand := hξ
  have hkey : eventPriority cand = edgeKey e t.val := by
    simp [cand, eventPriority, edgeKey, edgeRank, Nat.add_assoc]
  have hn : (atKeyEvents ξ removedRows removedLabels (edgeKey e t.val)).Nodup := by
    unfold atKeyEvents clockEventList
    exact ((List.mergeSort_perm _ _).nodup_iff.mpr (Finset.nodup_toList _)).filter _
  have hset : (atKeyEvents ξ removedRows removedLabels (edgeKey e t.val)).toFinset =
      ([cand] : List (ClockCandidate T R g Ω)).toFinset := by
    ext f
    simp only [List.mem_toFinset, List.mem_singleton]
    constructor
    · intro hf
      rcases List.mem_filter.mp hf with ⟨hf, hcond⟩
      have hcond' : eventPriority f = edgeKey e t.val ∧
          f.1 ∉ removedRows ∧ f.2.1 ∉ removedLabels := of_decide_eq_true hcond
      exact clockCandidate_eq_of_priority_eq ξ f cand
        ((clockEventList_mem_iff_p_clock_r4 _ _).mp hf) harr (hcond'.1.trans hkey.symm)
    · intro hf
      subst f
      simp [atKeyEvents, clockEventList_mem_iff_p_clock_r4, harr, hkey, cand, hr, hy]
  exact (List.perm_of_nodup_nodup_toFinset_eq hn (by simp) hset).eq_singleton

theorem atKeyEvents_empty {T : ℕ} {R : Type*} [Fintype R] [DecidableEq R]
    {g : ℕ} {Ω : R → Type*} [∀ a, Fintype (Ω a)] [∀ a, DecidableEq (Ω a)]
    (ξ : ClockField T R g Ω) (removedRows : Finset R)
    (removedLabels : Finset (Fin g)) (e : RowLabel R g) (t : Fin T)
    (h : ¬ ((∃ a, ξ e = .tick t a) ∧ e.1 ∉ removedRows ∧ e.2 ∉ removedLabels)) :
    atKeyEvents ξ removedRows removedLabels (edgeKey e t.val) = [] := by
  classical
  apply List.eq_nil_iff_forall_not_mem.mpr
  intro f hf
  rcases List.mem_filter.mp hf with ⟨hf, hcond⟩
  have hcond' : eventPriority f = edgeKey e t.val ∧
      f.1 ∉ removedRows ∧ f.2.1 ∉ removedLabels := of_decide_eq_true hcond
  have harr := (clockEventList_mem_iff_p_clock_r4 ξ f).mp hf
  have hkey : edgeKey (f.1, f.2.1) f.2.2.1.val = edgeKey e t.val := by
    simpa [eventPriority, edgeKey, edgeRank, Nat.add_assoc] using hcond'.1
  have hcoords := edgeKey_injective hkey
  have ht : f.2.2.1 = t := congrArg Prod.fst hcoords
  have he : (f.1, f.2.1) = e := congrArg Prod.snd hcoords
  rcases e with ⟨a, y⟩
  rcases f with ⟨b, z, s, o⟩
  dsimp only at ht he harr hcond'
  have hb : b = a := congrArg Prod.fst he
  have hz : z = y := congrArg Prod.snd he
  subst b
  subst z
  subst s
  exact h ⟨⟨o, harr⟩, hcond'.2⟩

theorem keyMatching_next_tick {T : ℕ} {R : Type*} [Fintype R] [DecidableEq R]
    {g : ℕ} {Ω : R → Type*} [∀ a, Fintype (Ω a)] [∀ a, DecidableEq (Ω a)]
    (ξ : ClockField T R g Ω) (removedRows : Finset R)
    (removedLabels : Finset (Fin g)) (e : RowLabel R g) (t : Fin T) (a : Ω e.1)
    (hξ : ξ e = .tick t a) (hr : e.1 ∉ removedRows) (hy : e.2 ∉ removedLabels) :
    keyMatching ξ removedRows removedLabels (edgeKey e t.val + 1) =
      processArrival ξ (keyMatching ξ removedRows removedLabels (edgeKey e t.val))
        ⟨e.1, e.2, t, a⟩ := by
  unfold keyMatching
  rw [keyEvents_successor, atKeyEvents_tick ξ removedRows removedLabels e t a hξ hr hy]
  simp [runGreedy, List.foldl_append]

theorem keyMatching_next_empty {T : ℕ} {R : Type*} [Fintype R] [DecidableEq R]
    {g : ℕ} {Ω : R → Type*} [∀ a, Fintype (Ω a)] [∀ a, DecidableEq (Ω a)]
    (ξ : ClockField T R g Ω) (removedRows : Finset R)
    (removedLabels : Finset (Fin g)) (e : RowLabel R g) (t : Fin T)
    (h : ¬ ((∃ a, ξ e = .tick t a) ∧ e.1 ∉ removedRows ∧ e.2 ∉ removedLabels)) :
    keyMatching ξ removedRows removedLabels (edgeKey e t.val + 1) =
      keyMatching ξ removedRows removedLabels (edgeKey e t.val) := by
  unfold keyMatching
  rw [keyEvents_successor, atKeyEvents_empty ξ removedRows removedLabels e t h]
  simp

theorem keyMatching_preserves_assignment {T : ℕ} {R : Type*} [Fintype R] [DecidableEq R]
    {g : ℕ} {Ω : R → Type*} [∀ a, Fintype (Ω a)] [∀ a, DecidableEq (Ω a)]
    (ξ : ClockField T R g Ω) (removedRows : Finset R) (removedLabels : Finset (Fin g))
    {k m : ℕ} (hkm : k ≤ m) (a : R) (v : Fin g × Ω a)
    (ha : (keyMatching ξ removedRows removedLabels k).assignment a = some v) :
    (keyMatching ξ removedRows removedLabels m).assignment a = some v := by
  induction m, hkm using Nat.le_induction with
  | base => exact ha
  | succ m hkm ih =>
      unfold keyMatching at ih ⊢
      rw [keyEvents_successor]
      unfold runGreedy
      rw [List.foldl_append]
      exact runGreedy_preserves_existing_assignment ξ
        (atKeyEvents ξ removedRows removedLabels m) _ a v ih

theorem keyMatching_preserves_used_label {T : ℕ} {R : Type*} [Fintype R] [DecidableEq R]
    {g : ℕ} {Ω : R → Type*} [∀ a, Fintype (Ω a)] [∀ a, DecidableEq (Ω a)]
    (ξ : ClockField T R g Ω) (removedRows : Finset R) (removedLabels : Finset (Fin g))
    {k m : ℕ} (hkm : k ≤ m) (y : Fin g)
    (hy : labelUsed (keyMatching ξ removedRows removedLabels k) y) :
    labelUsed (keyMatching ξ removedRows removedLabels m) y := by
  obtain ⟨a, o, ha⟩ := hy
  exact ⟨a, o, keyMatching_preserves_assignment ξ removedRows removedLabels hkm a (y, o) ha⟩

theorem keyFree_antitone {T : ℕ} {R : Type*} [Fintype R] [DecidableEq R]
    {g : ℕ} {Ω : R → Type*} [∀ a, Fintype (Ω a)] [∀ a, DecidableEq (Ω a)]
    (ξ : ClockField T R g Ω) (removedRows : Finset R) (removedLabels : Finset (Fin g))
    {k m : ℕ} (hkm : k ≤ m) (e : RowLabel R g)
    (hf : keyFree ξ removedRows removedLabels m e) :
    keyFree ξ removedRows removedLabels k e := by
  refine ⟨hf.1, hf.2.1, ?_, ?_⟩
  · cases h : (keyMatching ξ removedRows removedLabels k).assignment e.1 with
    | none => rfl
    | some v =>
        have hp := keyMatching_preserves_assignment ξ removedRows removedLabels hkm e.1 v h
        rw [hf.2.2.1] at hp
        contradiction
  · exact fun h => hf.2.2.2 (keyMatching_preserves_used_label ξ removedRows removedLabels hkm e.2 h)

noncomputable def rowMass {R : Type*} [Fintype R] {g : ℕ} {Ω : R → Type*}
    (r : R → Fin g → ℝ) (s : GreedyState R g Ω) (removedLabels : Finset (Fin g))
    (a : R) : ℝ :=
  ∑ y, if y ∉ removedLabels ∧ ¬ labelUsed s y then r a y else 0

noncomputable def labelMass {R : Type*} [Fintype R] [DecidableEq R] {g : ℕ} {Ω : R → Type*}
    (r : R → Fin g → ℝ) (s : GreedyState R g Ω) (removedRows : Finset R)
    (y : Fin g) : ℝ :=
  ∑ a, if a ∉ removedRows ∧ s.assignment a = none then r a y else 0

theorem processArrival_used_labels {T : ℕ} {R : Type*} [DecidableEq R] {g : ℕ}
    {Ω : R → Type*} [∀ a, DecidableEq (Ω a)]
    (ξ : ClockField T R g Ω) (s : GreedyState R g Ω) (e : ClockCandidate T R g Ω)
    (hacc : candidateIsArrival ξ e ∧ s.assignment e.1 = none ∧ ¬ labelUsed s e.2.1)
    (y : Fin g) :
    labelUsed (processArrival ξ s e) y ↔ labelUsed s y ∨ y = e.2.1 := by
  classical
  constructor
  · rintro ⟨a, o, ha⟩
    by_cases he : e.1 = a
    · subst a
      simp only [processArrival, if_pos hacc, dif_pos rfl] at ha
      right
      exact (congrArg Prod.fst (Option.some.inj ha)).symm
    · left
      exact ⟨a, o, by simpa [processArrival, hacc, he] using ha⟩
  · rintro (⟨a, o, ha⟩ | rfl)
    · have he : e.1 ≠ a := by
        intro he
        subst a
        rw [hacc.2.1] at ha
        contradiction
      exact ⟨a, o, by simpa [processArrival, hacc, he] using ha⟩
    · exact ⟨e.1, e.2.2.2, by simp [processArrival, hacc]⟩

theorem processArrival_free_rows {T : ℕ} {R : Type*} [DecidableEq R] {g : ℕ}
    {Ω : R → Type*} [∀ a, DecidableEq (Ω a)]
    (ξ : ClockField T R g Ω) (s : GreedyState R g Ω) (e : ClockCandidate T R g Ω)
    (hacc : candidateIsArrival ξ e ∧ s.assignment e.1 = none ∧ ¬ labelUsed s e.2.1)
    (a : R) :
    (processArrival ξ s e).assignment a = none ↔ s.assignment a = none ∧ a ≠ e.1 := by
  by_cases he : e.1 = a
  · subst a
    simp [processArrival, hacc]
  · simp [processArrival, hacc, he, Ne.symm he]

theorem rowMass_accepted_decrement {T : ℕ} {R : Type*} [Fintype R] [DecidableEq R]
    {g : ℕ} {Ω : R → Type*} [∀ a, DecidableEq (Ω a)]
    (r : R → Fin g → ℝ) (ξ : ClockField T R g Ω) (s : GreedyState R g Ω)
    (e : ClockCandidate T R g Ω) (removedLabels : Finset (Fin g))
    (hacc : candidateIsArrival ξ e ∧ s.assignment e.1 = none ∧ ¬ labelUsed s e.2.1)
    (hy : e.2.1 ∉ removedLabels) (a : R) :
    rowMass r (processArrival ξ s e) removedLabels a =
      rowMass r s removedLabels a - r a e.2.1 := by
  have hterm (y : Fin g) :
      (if y ∉ removedLabels ∧ ¬ labelUsed (processArrival ξ s e) y then r a y else 0) =
        (if y ∉ removedLabels ∧ ¬ labelUsed s y then r a y else 0) -
          (if y = e.2.1 then r a e.2.1 else 0) := by
    rw [processArrival_used_labels ξ s e hacc]
    by_cases he : y = e.2.1
    · subst y; simp [hy, hacc.2.2]
    · simp [he]
  unfold rowMass
  simp_rw [hterm]
  rw [Finset.sum_sub_distrib]
  simp

theorem labelMass_accepted_decrement {T : ℕ} {R : Type*} [Fintype R] [DecidableEq R]
    {g : ℕ} {Ω : R → Type*} [∀ a, DecidableEq (Ω a)]
    (r : R → Fin g → ℝ) (ξ : ClockField T R g Ω) (s : GreedyState R g Ω)
    (e : ClockCandidate T R g Ω) (removedRows : Finset R)
    (hacc : candidateIsArrival ξ e ∧ s.assignment e.1 = none ∧ ¬ labelUsed s e.2.1)
    (ha : e.1 ∉ removedRows) (y : Fin g) :
    labelMass r (processArrival ξ s e) removedRows y =
      labelMass r s removedRows y - r e.1 y := by
  have hterm (a : R) :
      (if a ∉ removedRows ∧ (processArrival ξ s e).assignment a = none then r a y else 0) =
        (if a ∉ removedRows ∧ s.assignment a = none then r a y else 0) -
          (if a = e.1 then r e.1 y else 0) := by
    simp only [processArrival_free_rows ξ s e hacc]
    by_cases he : a = e.1
    · subst a; simp [ha, hacc.2.1]
    · simp [he]
  unfold labelMass
  calc
    _ = ∑ a, ((if a ∉ removedRows ∧ s.assignment a = none then r a y else 0) -
        (if a = e.1 then r e.1 y else 0)) :=
      Finset.sum_congr rfl (fun a _ => hterm a)
    _ = _ := by rw [Finset.sum_sub_distrib]; simp

/-- One accepted edge removes exactly its label weight from every queried
row and exactly its row weight from every queried label. -/
theorem keyMass_next {T : ℕ} {R : Type*} [Fintype R] [DecidableEq R]
    {g : ℕ} {Ω : R → Type*} [∀ a, Fintype (Ω a)] [∀ a, DecidableEq (Ω a)]
    (r : R → Fin g → ℝ) (ξ : ClockField T R g Ω) (removedRows : Finset R)
    (removedLabels : Finset (Fin g)) (e : RowLabel R g) (t : Fin T) :
    (∀ a, rowMass r (keyMatching ξ removedRows removedLabels (edgeKey e t.val + 1))
        removedLabels a = rowMass r (keyMatching ξ removedRows removedLabels (edgeKey e t.val))
          removedLabels a -
        (if keyFree ξ removedRows removedLabels (edgeKey e t.val) e ∧
          (∃ o, ξ e = .tick t o) then r a e.2 else 0)) ∧
    (∀ y, labelMass r (keyMatching ξ removedRows removedLabels (edgeKey e t.val + 1))
        removedRows y = labelMass r (keyMatching ξ removedRows removedLabels (edgeKey e t.val))
          removedRows y -
        (if keyFree ξ removedRows removedLabels (edgeKey e t.val) e ∧
          (∃ o, ξ e = .tick t o) then r e.1 y else 0)) := by
  classical
  by_cases hcurrent : (∃ o, ξ e = .tick t o) ∧ e.1 ∉ removedRows ∧ e.2 ∉ removedLabels
  · obtain ⟨⟨o, ho⟩, hr, hy⟩ := hcurrent
    rw [keyMatching_next_tick ξ removedRows removedLabels e t o ho hr hy]
    by_cases hf : keyFree ξ removedRows removedLabels (edgeKey e t.val) e
    · have hacc : candidateIsArrival ξ ⟨e.1, e.2, t, o⟩ ∧
          (keyMatching ξ removedRows removedLabels (edgeKey e t.val)).assignment e.1 = none ∧
          ¬ labelUsed (keyMatching ξ removedRows removedLabels (edgeKey e t.val)) e.2 :=
        ⟨ho, hf.2.2⟩
      constructor
      · intro a
        rw [rowMass_accepted_decrement r ξ _ _ _ hacc hy]
        simp [hf, ho]
      · intro y
        rw [labelMass_accepted_decrement r ξ _ _ _ hacc hr]
        simp [hf, ho]
    · have hacc : ¬ (candidateIsArrival ξ ⟨e.1, e.2, t, o⟩ ∧
          (keyMatching ξ removedRows removedLabels (edgeKey e t.val)).assignment e.1 = none ∧
          ¬ labelUsed (keyMatching ξ removedRows removedLabels (edgeKey e t.val)) e.2) := by
        intro hacc
        exact hf ⟨hr, hy, hacc.2⟩
      simp [processArrival, hacc, hf]
  · rw [keyMatching_next_empty ξ removedRows removedLabels e t hcurrent]
    have hf : ¬ (keyFree ξ removedRows removedLabels (edgeKey e t.val) e ∧
        ∃ o, ξ e = .tick t o) := by
      rintro ⟨hfree, ho⟩
      exact hcurrent ⟨ho, hfree.1, hfree.2.1⟩
    simp [hf]

def endpointWeight {R : Type*} {g : ℕ} (r : R → Fin g → ℝ)
    (u : Endpoint R g) (e : RowLabel R g) : ℝ :=
  match u with
  | .inl a => r a e.2
  | .inr y => r e.1 y

noncomputable def endpointMass {T : ℕ} {R : Type*} [Fintype R] [DecidableEq R]
    {g : ℕ} {Ω : R → Type*} [∀ a, Fintype (Ω a)] [∀ a, DecidableEq (Ω a)]
    (r : R → Fin g → ℝ) (ξ : ClockField T R g Ω) (removedRows : Finset R)
    (removedLabels : Finset (Fin g)) (k : ℕ) (u : Endpoint R g) : ℝ :=
  match u with
  | .inl a => rowMass r (keyMatching ξ removedRows removedLabels k) removedLabels a
  | .inr y => labelMass r (keyMatching ξ removedRows removedLabels k) removedRows y

theorem endpointMass_next {T : ℕ} {R : Type*} [Fintype R] [DecidableEq R]
    {g : ℕ} {Ω : R → Type*} [∀ a, Fintype (Ω a)] [∀ a, DecidableEq (Ω a)]
    (r : R → Fin g → ℝ) (ξ : ClockField T R g Ω) (removedRows : Finset R)
    (removedLabels : Finset (Fin g)) (e : RowLabel R g) (t : Fin T) (u : Endpoint R g) :
    endpointMass r ξ removedRows removedLabels (edgeKey e t.val + 1) u =
      endpointMass r ξ removedRows removedLabels (edgeKey e t.val) u -
        (if keyFree ξ removedRows removedLabels (edgeKey e t.val) e ∧ ∃ o, ξ e = .tick t o then
          endpointWeight r u e else 0) := by
  rcases u with a | y
  · exact (keyMass_next r ξ removedRows removedLabels e t).1 a
  · exact (keyMass_next r ξ removedRows removedLabels e t).2 y

def prescribedField {T : ℕ} {R : Type*} {g : ℕ} {Ω : R → Type*}
    (ins : ∀ e : RowLabel R g, Option (MeshClockValue T (Ω e.1)))
    (ξ : ClockField T R g Ω) : ClockField T R g Ω := fun e => (ins e).getD (ξ e)

noncomputable def fullDrift {T : ℕ} {R : Type*} [Fintype R] [DecidableEq R]
    {g : ℕ} {Ω : R → Type*} [∀ a, Fintype (Ω a)] [∀ a, DecidableEq (Ω a)]
    (r : R → Fin g → ℝ) (ξ : ClockField T R g Ω) (removedRows : Finset R)
    (removedLabels : Finset (Fin g)) (k : ℕ) (u : Endpoint R g) : ℝ :=
  ∑ e : RowLabel R g, if keyFree ξ removedRows removedLabels k e then
    r e.1 e.2 * endpointWeight r u e else 0

noncomputable def prescribedCount {T : ℕ} {R : Type*} [Fintype R] {g : ℕ} {Ω : R → Type*}
    (ins : ∀ e : RowLabel R g, Option (MeshClockValue T (Ω e.1))) : ℕ :=
  (Finset.univ.filter (fun e => (ins e).isSome)).card

noncomputable def tickDrift {T : ℕ} {R : Type*} [Fintype R] [DecidableEq R]
    {g : ℕ} {Ω : R → Type*} [∀ a, Fintype (Ω a)] [∀ a, DecidableEq (Ω a)]
    (r : R → Fin g → ℝ)
    (ins : ∀ e : RowLabel R g, Option (MeshClockValue T (Ω e.1)))
    (ξ : ClockField T R g Ω) (removedRows : Finset R)
    (removedLabels : Finset (Fin g)) (j : ℕ) (u : Endpoint R g) : ℝ :=
  ∑ e : RowLabel R g, if ins e = none ∧
      keyFree (prescribedField ins ξ) removedRows removedLabels (edgeKey e j) e then
    r e.1 e.2 * endpointWeight r u e else 0

theorem edgeKey_bounds {R : Type*} [Fintype R] [DecidableEq R] {g : ℕ}
    (e : RowLabel R g) (j : ℕ) :
    j * (Fintype.card R * g) ≤ edgeKey e j ∧
      edgeKey e j < (j + 1) * (Fintype.card R * g) := by
  have hrank : edgeRank e < Fintype.card R * g := by
    simpa [edgeEquiv_val] using (edgeEquiv e).isLt
  constructor
  · exact Nat.le_add_right _ _
  · dsimp [edgeKey]
    nlinarith

/-- The micro-edge drifts in a tick lie between the endpoint drifts at its
two boundaries, with the prescribed coordinates charged separately. -/
theorem tickDrift_sandwich {T : ℕ} {R : Type*} [Fintype R] [DecidableEq R]
    {g : ℕ} {Ω : R → Type*} [∀ a, Fintype (Ω a)] [∀ a, DecidableEq (Ω a)]
    (r : R → Fin g → ℝ) (hr : ∀ a y, 0 ≤ r a y)
    (atom : ℝ) (hAtom : 0 ≤ atom) (hrAtom : ∀ a y, r a y ≤ atom)
    (ins : ∀ e : RowLabel R g, Option (MeshClockValue T (Ω e.1)))
    (ξ : ClockField T R g Ω) (removedRows : Finset R)
    (removedLabels : Finset (Fin g)) (j : ℕ) (u : Endpoint R g) :
    fullDrift r (prescribedField ins ξ) removedRows removedLabels
        ((j + 1) * (Fintype.card R * g)) u - (prescribedCount ins : ℝ) * atom ^ 2 ≤
      tickDrift r ins ξ removedRows removedLabels j u ∧
    tickDrift r ins ξ removedRows removedLabels j u ≤
      fullDrift r (prescribedField ins ξ) removedRows removedLabels
        (j * (Fintype.card R * g)) u := by
  classical
  have hw (e : RowLabel R g) : 0 ≤ endpointWeight r u e ∧ endpointWeight r u e ≤ atom := by
    rcases u with a | y
    · exact ⟨hr a e.2, hrAtom a e.2⟩
    · exact ⟨hr e.1 y, hrAtom e.1 y⟩
  have hprod (e : RowLabel R g) : 0 ≤ r e.1 e.2 * endpointWeight r u e :=
    mul_nonneg (hr _ _) (hw e).1
  let removedWeight := ∑ e : RowLabel R g,
    if (ins e).isSome then r e.1 e.2 * endpointWeight r u e else 0
  have hremoved : removedWeight ≤ (prescribedCount ins : ℝ) * atom ^ 2 := by
    dsimp [removedWeight]
    rw [← Finset.sum_filter]
    calc
      _ ≤ ∑ e ∈ Finset.univ.filter (fun e => (ins e).isSome), atom ^ 2 := by
        apply Finset.sum_le_sum
        intro e _
        simpa [pow_two] using mul_le_mul (hrAtom _ _) (hw e).2 (hw e).1 hAtom
      _ = _ := by simp [prescribedCount]
  have hlower : fullDrift r (prescribedField ins ξ) removedRows removedLabels
        ((j + 1) * (Fintype.card R * g)) u - removedWeight ≤
      tickDrift r ins ξ removedRows removedLabels j u := by
    unfold fullDrift tickDrift
    dsimp [removedWeight]
    rw [← Finset.sum_sub_distrib]
    apply Finset.sum_le_sum
    intro e _
    have hfree := keyFree_antitone (prescribedField ins ξ) removedRows removedLabels
      (edgeKey_bounds e j).2.le e
    cases hi : ins e with
    | none =>
        by_cases hf : keyFree (prescribedField ins ξ) removedRows removedLabels
            ((j + 1) * (Fintype.card R * g)) e
        · simp [hi, hf, hfree hf]
        · simp only [hi, Option.isSome_none, Bool.false_eq_true, ite_false, zero_sub,
            eq_self_iff_true, true_and]
          split_ifs <;> linarith [hprod e]
    | some z =>
        simp only [hi, Option.isSome_some, ite_true, Option.some_ne_none, false_and, ite_false]
        split_ifs <;> linarith [hprod e]
  constructor
  · linarith
  · unfold tickDrift fullDrift
    apply Finset.sum_le_sum
    intro e _
    have hfree := keyFree_antitone (prescribedField ins ξ) removedRows removedLabels
      (edgeKey_bounds e j).1 e
    by_cases hf : ins e = none ∧ keyFree (prescribedField ins ξ) removedRows removedLabels (edgeKey e j) e
    · simp [hf, hfree hf.2]
    · simp only [if_neg hf]
      split_ifs <;> linarith [hprod e]

theorem fullDrift_row {T : ℕ} {R : Type*} [Fintype R] [DecidableEq R]
    {g : ℕ} {Ω : R → Type*} [∀ a, Fintype (Ω a)] [∀ a, DecidableEq (Ω a)]
    (r : R → Fin g → ℝ) (ξ : ClockField T R g Ω) (removedRows : Finset R)
    (removedLabels : Finset (Fin g)) (k : ℕ) (a : R) :
    fullDrift r ξ removedRows removedLabels k (.inl a) =
      ∑ y, (if y ∉ removedLabels ∧ ¬ labelUsed (keyMatching ξ removedRows removedLabels k) y
        then r a y else 0) * labelMass r (keyMatching ξ removedRows removedLabels k) removedRows y := by
  classical
  unfold fullDrift endpointWeight labelMass
  rw [Fintype.sum_prod_type, Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro y _
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro b _
  have hfree : keyFree ξ removedRows removedLabels k (b, y) ↔
      (b ∉ removedRows ∧ (keyMatching ξ removedRows removedLabels k).assignment b = none) ∧
      (y ∉ removedLabels ∧ ¬ labelUsed (keyMatching ξ removedRows removedLabels k) y) := by
    simp [keyFree, and_assoc, and_left_comm, and_comm]
  rw [hfree]
  by_cases hb : b ∉ removedRows ∧ (keyMatching ξ removedRows removedLabels k).assignment b = none
  <;> by_cases hy : y ∉ removedLabels ∧ ¬ labelUsed (keyMatching ξ removedRows removedLabels k) y
  <;> simp [hb, hy, mul_comm]

theorem fullDrift_label {T : ℕ} {R : Type*} [Fintype R] [DecidableEq R]
    {g : ℕ} {Ω : R → Type*} [∀ a, Fintype (Ω a)] [∀ a, DecidableEq (Ω a)]
    (r : R → Fin g → ℝ) (ξ : ClockField T R g Ω) (removedRows : Finset R)
    (removedLabels : Finset (Fin g)) (k : ℕ) (y : Fin g) :
    fullDrift r ξ removedRows removedLabels k (.inr y) =
      ∑ a, (if a ∉ removedRows ∧ (keyMatching ξ removedRows removedLabels k).assignment a = none
        then r a y else 0) * rowMass r (keyMatching ξ removedRows removedLabels k) removedLabels a := by
  classical
  unfold fullDrift endpointWeight rowMass
  rw [Fintype.sum_prod_type]
  apply Finset.sum_congr rfl
  intro a _
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro z _
  have hfree : keyFree ξ removedRows removedLabels k (a, z) ↔
      (a ∉ removedRows ∧ (keyMatching ξ removedRows removedLabels k).assignment a = none) ∧
      (z ∉ removedLabels ∧ ¬ labelUsed (keyMatching ξ removedRows removedLabels k) z) := by
    simp [keyFree, and_assoc, and_left_comm, and_comm]
  rw [hfree]
  by_cases ha : a ∉ removedRows ∧ (keyMatching ξ removedRows removedLabels k).assignment a = none
  <;> by_cases hz : z ∉ removedLabels ∧ ¬ labelUsed (keyMatching ξ removedRows removedLabels k) z
  <;> simp [ha, hz, mul_comm]


theorem observedField_project_le {T : ℕ} {R : Type*} [Fintype R] [DecidableEq R]
    {g : ℕ} {Ω : R → Type*} {k m : ℕ} (hkm : k ≤ m) (ξ : ClockField T R g Ω) :
    observedField k (observedField m ξ) = observedField k ξ := by
  funext e
  unfold observedField
  cases ξ e with
  | noArrival => rfl
  | tick t a =>
      by_cases h : edgeKey e t.val < k
      · simp [observeClock, h, lt_of_lt_of_le h hkm]
      · by_cases h' : edgeKey e t.val < m <;> simp [observeClock, h, h']

theorem prescribedMatching_depends {T : ℕ} {R : Type*} [Fintype R] [DecidableEq R]
    {g : ℕ} {Ω : R → Type*} [∀ a, Fintype (Ω a)] [∀ a, DecidableEq (Ω a)]
    (ins : ∀ e : RowLabel R g, Option (MeshClockValue T (Ω e.1)))
    (ξ ξ' : ClockField T R g Ω) (removedRows : Finset R)
    (removedLabels : Finset (Fin g)) {k m : ℕ} (hkm : k ≤ m)
    (h : observedField m ξ = observedField m ξ') :
    keyMatching (prescribedField ins ξ) removedRows removedLabels k =
      keyMatching (prescribedField ins ξ') removedRows removedLabels k := by
  apply keyMatching_depends_on_observation
  have hk : observedField k ξ = observedField k ξ' := by
    have hk := congrArg (observedField k) h
    simpa [observedField_project_le hkm] using hk
  funext e
  have hke := congrFun hk e
  cases hins : ins e with
  | none => simpa [observedField, prescribedField, hins] using hke
  | some z => simp [observedField, prescribedField, hins]

theorem observed_arrival_iff {T : ℕ} {R : Type*} [Fintype R] [DecidableEq R]
    {g : ℕ} {Ω : R → Type*} (ξ : ClockField T R g Ω) (e : RowLabel R g)
    (t : Fin T) {m : ℕ} (ht : edgeKey e t.val < m) :
    (∃ a, ξ e = .tick t a) ↔ ∃ a, observedField m ξ e = .tick t a := by
  cases hξ : ξ e with
  | noArrival => simp [observedField, observeClock, hξ]
  | tick s a =>
      by_cases hs : edgeKey e s.val < m
      · simp [observedField, observeClock, hξ, hs]
      · have hn : ¬ ∃ b, MeshClockValue.tick s a = MeshClockValue.tick t b := by
          rintro ⟨b, hb⟩
          have hst : s = t := by injection hb
          subst s
          exact hs ht
        have hst : s ≠ t := by
          intro hst
          subst s
          exact hs ht
        simp [observedField, observeClock, hξ, hs, hst]

noncomputable def ordinaryIncrement {T : ℕ} {R : Type*} [Fintype R] [DecidableEq R]
    {g : ℕ} {Ω : R → Type*} [∀ a, Fintype (Ω a)] [∀ a, DecidableEq (Ω a)]
    (δ : ℝ) (r : RowLabel R g → ℝ)
    (ins : ∀ e : RowLabel R g, Option (MeshClockValue T (Ω e.1)))
    (removedRows : Finset R) (removedLabels : Finset (Fin g))
    (e : RowLabel R g) (t : Fin T) (w : ℝ) (ξ : ClockField T R g Ω) : ℝ :=
  if ins e = none ∧ keyFree (prescribedField ins ξ) removedRows removedLabels (edgeKey e t.val) e then
    w * ((if ∃ a, ξ e = .tick t a then 1 else 0) - δ * r e) else 0

theorem ordinaryIncrement_moments {T : ℕ} {R : Type*} [Fintype R] [DecidableEq R]
    {g : ℕ} {Ω : R → Type*} [∀ a, Fintype (Ω a)] [∀ a, DecidableEq (Ω a)]
    (δ : ℝ) (r : RowLabel R g → ℝ) (μ : ∀ e : RowLabel R g, Ω e.1 → ℝ)
    (hδ : 0 ≤ δ) (hbase : ∀ e, 0 ≤ 1 - δ * r e)
    (hr : ∀ e, 0 ≤ r e) (hμ : ∀ e a, 0 ≤ μ e a)
    (hsum : ∀ e, ∑ a, μ e a = r e)
    (ins : ∀ e : RowLabel R g, Option (MeshClockValue T (Ω e.1)))
    (removedRows : Finset R) (removedLabels : Finset (Fin g))
    (e : RowLabel R g) (t : Fin T) (w : ℝ) (hw : 0 ≤ w) :
    let P := clockFieldLaw (fun f => markedClockLaw (T := T) δ (r f) (μ f) hδ
      (hbase f) (hr f) (hμ f) (hsum f))
    let Δ := ordinaryIncrement δ r ins removedRows removedLabels e t w
    (∀ ξ, |Δ ξ| ≤ w) ∧
    (∀ h, (∑ ξ, if observedField (edgeKey e t.val) ξ = h then P.w ξ * Δ ξ else 0) = 0) ∧
    (∀ h, (∑ ξ, if observedField (edgeKey e t.val) ξ = h then P.w ξ * (Δ ξ) ^ 2 else 0) ≤
      w ^ 2 * (δ * r e) * P.pr (fun ξ => observedField (edgeKey e t.val) ξ = h)) := by
  classical
  dsimp only
  let P := clockFieldLaw (fun f => markedClockLaw (T := T) δ (r f) (μ f) hδ
    (hbase f) (hr f) (hμ f) (hsum f))
  let gate := fun ξ : ClockField T R g Ω => ins e = none ∧
    keyFree (prescribedField ins ξ) removedRows removedLabels (edgeKey e t.val) e
  let J := fun ξ : ClockField T R g Ω => ∃ a, ξ e = .tick t a
  have hgate : ∀ ξ ξ', observedField (edgeKey e t.val) ξ =
      observedField (edgeKey e t.val) ξ' → (gate ξ ↔ gate ξ') := by
    intro ξ ξ' h
    have hM := prescribedMatching_depends ins ξ ξ' removedRows removedLabels (le_refl _) h
    dsimp [gate, keyFree]
    rw [hM]
  have hhazard : ∀ h, (∃ ξ, observedField (edgeKey e t.val) ξ = h ∧ gate ξ) →
      P.pr (fun ξ => observedField (edgeKey e t.val) ξ = h ∧ J ξ) =
        (δ * r e) * P.pr (fun ξ => observedField (edgeKey e t.val) ξ = h) := by
    intro h hex
    obtain ⟨ξ, hξ, hins, hfree⟩ := hex
    have he : h e = .noArrival := by
      rw [← hξ]
      have he := keyFree_prefix_empty (prescribedField ins ξ) removedRows removedLabels
        (edgeKey e t.val) e hfree
      simpa [observedField, prescribedField, hins] using he
    exact observedField_fiber_hazard δ r μ hδ hbase hr hμ hsum e t h he
  have hMom := gated_indicator_moments P (observedField (edgeKey e t.val)) gate J
    w (δ * r e) hw (mul_nonneg hδ (hr e)) (by linarith [hbase e]) hgate hhazard
  have hΔ : (fun ξ => if gate ξ then w * ((if J ξ then 1 else 0) - δ * r e) else 0) =
      ordinaryIncrement δ r ins removedRows removedLabels e t w := by
    funext ξ
    dsimp [gate, J, ordinaryIncrement]
  change (∀ ξ, |(ordinaryIncrement δ r ins removedRows removedLabels e t w) ξ| ≤ w) ∧
    (∀ h, (∑ ξ, if observedField (edgeKey e t.val) ξ = h then
      P.w ξ * ordinaryIncrement δ r ins removedRows removedLabels e t w ξ else 0) = 0) ∧
    (∀ h, (∑ ξ, if observedField (edgeKey e t.val) ξ = h then P.w ξ *
      (ordinaryIncrement δ r ins removedRows removedLabels e t w ξ) ^ 2 else 0) ≤
      w ^ 2 * (δ * r e) * P.pr (fun ξ => observedField (edgeKey e t.val) ξ = h))
  rw [← hΔ]
  exact hMom

theorem ordinaryIncrement_adapted {T : ℕ} {R : Type*} [Fintype R] [DecidableEq R]
    {g : ℕ} {Ω : R → Type*} [∀ a, Fintype (Ω a)] [∀ a, DecidableEq (Ω a)]
    (δ : ℝ) (r : RowLabel R g → ℝ)
    (ins : ∀ e : RowLabel R g, Option (MeshClockValue T (Ω e.1)))
    (removedRows : Finset R) (removedLabels : Finset (Fin g))
    (e : RowLabel R g) (t : Fin T) (w : ℝ) {m : ℕ} (hm : edgeKey e t.val < m)
    (ξ ξ' : ClockField T R g Ω) (h : observedField m ξ = observedField m ξ') :
    ordinaryIncrement δ r ins removedRows removedLabels e t w ξ =
      ordinaryIncrement δ r ins removedRows removedLabels e t w ξ' := by
  have hM := prescribedMatching_depends ins ξ ξ' removedRows removedLabels hm.le h
  have hJ : (∃ a, ξ e = .tick t a) ↔ ∃ a, ξ' e = .tick t a := by
    rw [observed_arrival_iff ξ e t hm, observed_arrival_iff ξ' e t hm, h]
  have hgate : (ins e = none ∧ keyFree (prescribedField ins ξ) removedRows removedLabels
      (edgeKey e t.val) e) ↔ (ins e = none ∧ keyFree (prescribedField ins ξ')
        removedRows removedLabels (edgeKey e t.val) e) := by
    simp only [keyFree, hM]
  by_cases hg : ins e = none ∧ keyFree (prescribedField ins ξ) removedRows removedLabels
      (edgeKey e t.val) e
  · have hg' := hgate.mp hg
    simp [ordinaryIncrement, hg, hg', hJ]
  · have hg' := mt hgate.mpr hg
    simp [ordinaryIncrement, hg, hg']

noncomputable def prefixCoordinate {T : ℕ} {R : Type*} [Fintype R] [DecidableEq R]
    {g N : ℕ} (hN : N ≤ T * (Fintype.card R * g)) (i : Fin N) : Fin T × RowLabel R g :=
  timeEdgeEquiv.symm (i.castLE hN)

theorem prefixCoordinate_key {T : ℕ} {R : Type*} [Fintype R] [DecidableEq R]
    {g N : ℕ} (hN : N ≤ T * (Fintype.card R * g)) (i : Fin N) :
    edgeKey (prefixCoordinate hN i).2 (prefixCoordinate hN i).1.val = i.val := by
  rw [← timeEdgeEquiv_val]
  simp [prefixCoordinate]

theorem prefixCoordinate_castSucc {T : ℕ} {R : Type*} [Fintype R] [DecidableEq R]
    {g N : ℕ} (hN : N + 1 ≤ T * (Fintype.card R * g)) (i : Fin N) :
    prefixCoordinate hN i.castSucc = prefixCoordinate (Nat.le_of_succ_le hN) i := by
  unfold prefixCoordinate
  congr 1

/-- All accepted mass decrements telescope, including prescribed arrivals. -/
theorem prefix_mass_loss {T : ℕ} {R : Type*} [Fintype R] [DecidableEq R]
    {g : ℕ} {Ω : R → Type*} [∀ a, Fintype (Ω a)] [∀ a, DecidableEq (Ω a)]
    (r : R → Fin g → ℝ) (ξ : ClockField T R g Ω) (removedRows : Finset R)
    (removedLabels : Finset (Fin g)) (u : Endpoint R g) :
    ∀ (N : ℕ) (hN : N ≤ T * (Fintype.card R * g)),
      endpointMass r ξ removedRows removedLabels N u =
        endpointMass r ξ removedRows removedLabels 0 u -
          ∑ i : Fin N, if keyFree ξ removedRows removedLabels i.val (prefixCoordinate hN i).2 ∧
            (∃ o, ξ (prefixCoordinate hN i).2 = .tick (prefixCoordinate hN i).1 o) then
              endpointWeight r u (prefixCoordinate hN i).2 else 0 := by
  intro N
  induction N with
  | zero => intro _; simp
  | succ N ih =>
      intro hN
      have hprev := ih (Nat.le_of_succ_le hN)
      let p := prefixCoordinate hN (Fin.last N)
      have hp : edgeKey p.2 p.1.val = N := by
        simpa [p] using prefixCoordinate_key hN (Fin.last N)
      have hstep := endpointMass_next r ξ removedRows removedLabels p.2 p.1 u
      rw [hp] at hstep
      rw [Fin.sum_univ_castSucc]
      simp only [Fin.val_castSucc, prefixCoordinate_castSucc, Fin.val_last]
      change endpointMass r ξ removedRows removedLabels (N + 1) u =
        endpointMass r ξ removedRows removedLabels 0 u -
          ((∑ i : Fin N, if keyFree ξ removedRows removedLabels i.val
            (prefixCoordinate (Nat.le_of_succ_le hN) i).2 ∧
              (∃ o, ξ (prefixCoordinate (Nat.le_of_succ_le hN) i).2 =
                .tick (prefixCoordinate (Nat.le_of_succ_le hN) i).1 o) then
                  endpointWeight r u (prefixCoordinate (Nat.le_of_succ_le hN) i).2 else 0) +
            (if keyFree ξ removedRows removedLabels N p.2 ∧ ∃ o, ξ p.2 = .tick p.1 o then
              endpointWeight r u p.2 else 0))
      rw [hstep, hprev]
      ring

noncomputable def prescribedLoss {T : ℕ} {R : Type*} [Fintype R] [DecidableEq R]
    {g : ℕ} {Ω : R → Type*} [∀ a, Fintype (Ω a)] [∀ a, DecidableEq (Ω a)]
    (ins : ∀ e : RowLabel R g, Option (MeshClockValue T (Ω e.1)))
    (ξ : ClockField T R g Ω) (removedRows : Finset R) (removedLabels : Finset (Fin g))
    (e : RowLabel R g) (t : Fin T) (w : ℝ) : ℝ :=
  if (ins e).isSome ∧ keyFree (prescribedField ins ξ) removedRows removedLabels (edgeKey e t.val) e ∧
      (∃ o, prescribedField ins ξ e = .tick t o) then w else 0

theorem accepted_loss_decomposition {T : ℕ} {R : Type*} [Fintype R] [DecidableEq R]
    {g : ℕ} {Ω : R → Type*} [∀ a, Fintype (Ω a)] [∀ a, DecidableEq (Ω a)]
    (δ : ℝ) (r : RowLabel R g → ℝ)
    (ins : ∀ e : RowLabel R g, Option (MeshClockValue T (Ω e.1)))
    (ξ : ClockField T R g Ω) (removedRows : Finset R) (removedLabels : Finset (Fin g))
    (e : RowLabel R g) (t : Fin T) (w : ℝ) :
    (if keyFree (prescribedField ins ξ) removedRows removedLabels (edgeKey e t.val) e ∧
      (∃ o, prescribedField ins ξ e = .tick t o) then w else 0) =
      ordinaryIncrement δ r ins removedRows removedLabels e t w ξ +
        δ * (if ins e = none ∧ keyFree (prescribedField ins ξ) removedRows removedLabels
          (edgeKey e t.val) e then r e * w else 0) +
        prescribedLoss ins ξ removedRows removedLabels e t w := by
  cases hi : ins e with
  | none =>
      simp only [ordinaryIncrement, prescribedLoss, hi, Option.isSome_none, Bool.false_eq_true,
        false_and, ite_false, eq_self_iff_true, true_and]
      have hval : prescribedField ins ξ e = ξ e := by simp [prescribedField, hi]
      rw [hval]
      split_ifs <;> simp_all <;> ring
  | some z =>
      simp only [ordinaryIncrement, prescribedLoss, hi, Option.isSome_some, Option.some_ne_none,
        false_and, true_and, ite_false, zero_add, mul_zero]

/-- Each prescribed edge has only one first-arrival value, so its total
mass loss is charged once over the whole horizon. -/
theorem prescribed_loss_total {T : ℕ} {R : Type*} [Fintype R] [DecidableEq R]
    {g : ℕ} {Ω : R → Type*} [∀ a, Fintype (Ω a)] [∀ a, DecidableEq (Ω a)]
    (ins : ∀ e : RowLabel R g, Option (MeshClockValue T (Ω e.1)))
    (ξ : ClockField T R g Ω) (removedRows : Finset R) (removedLabels : Finset (Fin g))
    (w : RowLabel R g → ℝ) (atom : ℝ) (hAtom : 0 ≤ atom)
    (hw0 : ∀ e, 0 ≤ w e) (hwAtom : ∀ e, w e ≤ atom) :
    (∑ p : Fin T × RowLabel R g,
      prescribedLoss ins ξ removedRows removedLabels p.2 p.1 (w p.2)) ≤
        (prescribedCount ins : ℝ) * atom := by
  classical
  rw [Fintype.sum_prod_type, Finset.sum_comm]
  calc
    _ ≤ ∑ e : RowLabel R g, if (ins e).isSome then atom else 0 := by
      apply Finset.sum_le_sum
      intro e _
      cases hi : ins e with
      | none => simp [prescribedLoss, hi]
      | some z =>
          simp only [hi, Option.isSome_some, ite_true]
          have hpoint (t : Fin T) :
              prescribedLoss ins ξ removedRows removedLabels e t (w e) ≤
                if ∃ o, z = .tick t o then atom else 0 := by
            unfold prescribedLoss
            have hval : prescribedField ins ξ e = z := by simp [prescribedField, hi]
            rw [hval]
            by_cases h : ∃ o, z = .tick t o
            · simp only [if_pos h]
              split_ifs <;> linarith [hwAtom e]
            · simp [h, hAtom]
          apply (Finset.sum_le_sum fun t _ => hpoint t).trans
          cases z with
          | noArrival => simp [hAtom]
          | tick s o => simp
    _ = _ := by
      rw [← Finset.sum_filter]
      simp [prescribedCount]

theorem prefixCoordinate_tick {T : ℕ} {R : Type*} [Fintype R] [DecidableEq R]
    {g k : ℕ} (hk : k ≤ T) (t : Fin k) (e : RowLabel R g) :
    prefixCoordinate (Nat.mul_le_mul_right (Fintype.card R * g) hk)
      (timeEdgeEquiv (t, e)) = (t.castLE hk, e) := by
  have hkey : edgeKey
      (prefixCoordinate (Nat.mul_le_mul_right (Fintype.card R * g) hk) (timeEdgeEquiv (t, e))).2
      (prefixCoordinate (Nat.mul_le_mul_right (Fintype.card R * g) hk) (timeEdgeEquiv (t, e))).1.val =
        edgeKey e (t.castLE hk).val := by
    rw [prefixCoordinate_key]
    simpa only [Fin.val_castLE] using timeEdgeEquiv_val t e
  exact edgeKey_injective hkey

theorem prefix_tick_sum {T : ℕ} {R : Type*} [Fintype R] [DecidableEq R]
    {g k : ℕ} (hk : k ≤ T) (f : Fin T → RowLabel R g → ℝ) :
    (∑ i : Fin (k * (Fintype.card R * g)),
      f (prefixCoordinate (Nat.mul_le_mul_right (Fintype.card R * g) hk) i).1
        (prefixCoordinate (Nat.mul_le_mul_right (Fintype.card R * g) hk) i).2) =
      ∑ t : Fin k, ∑ e : RowLabel R g, f (t.castLE hk) e := by
  calc
    _ = ∑ p : Fin k × RowLabel R g, f (p.1.castLE hk) p.2 := by
      symm
      apply Fintype.sum_equiv timeEdgeEquiv
      intro p
      rw [prefixCoordinate_tick hk]
    _ = _ := Fintype.sum_prod_type (fun p : Fin k × RowLabel R g => f (p.1.castLE hk) p.2)


/-- Two-sided concentration of the ordinary compensated mass decrements
through any fixed prefix of the prescribed background matching. -/
theorem ordinary_prefix_tail {T : ℕ} {R : Type*} [Fintype R] [DecidableEq R]
    {g : ℕ} {Ω : R → Type*} [∀ a, Fintype (Ω a)] [∀ a, DecidableEq (Ω a)]
    (δ : ℝ) (r : RowLabel R g → ℝ) (μ : ∀ e : RowLabel R g, Ω e.1 → ℝ)
    (hδ : 0 ≤ δ) (hbase : ∀ e, 0 ≤ 1 - δ * r e)
    (hr : ∀ e, 0 ≤ r e) (hμ : ∀ e a, 0 ≤ μ e a)
    (hsum : ∀ e, ∑ a, μ e a = r e)
    (ins : ∀ e : RowLabel R g, Option (MeshClockValue T (Ω e.1)))
    (removedRows : Finset R) (removedLabels : Finset (Fin g))
    (w : RowLabel R g → ℝ) (atom : ℝ) (hAtom : 0 < atom)
    (hw0 : ∀ e, 0 ≤ w e) (hwAtom : ∀ e, w e ≤ atom)
    {N : ℕ} (hN : N ≤ T * (Fintype.card R * g)) (ε : ℝ) (hε : 0 < ε) :
    let P := clockFieldLaw (fun f => markedClockLaw (T := T) δ (r f) (μ f) hδ
      (hbase f) (hr f) (hμ f) (hsum f))
    P.pr (fun ξ => ε ≤ |∑ i : Fin N,
      ordinaryIncrement δ r ins removedRows removedLabels
        (prefixCoordinate hN i).2 (prefixCoordinate hN i).1 (w (prefixCoordinate hN i).2) ξ|) ≤
      2 * Real.exp (-ε ^ 2 / (2 * ((∑ i : Fin N,
        (w (prefixCoordinate hN i).2) ^ 2 * (δ * r (prefixCoordinate hN i).2)) + atom * ε / 3))) := by
  classical
  dsimp only
  let P := clockFieldLaw (fun f => markedClockLaw (T := T) δ (r f) (μ f) hδ
    (hbase f) (hr f) (hμ f) (hsum f))
  let H : Fin (N + 1) → Type _ := fun _ => ClockField T R g Ω
  let history : ∀ i : Fin (N + 1), ClockField T R g Ω → H i := fun i => observedField i.val
  let project : ∀ i : Fin N, H i.succ → H i.castSucc := fun i => observedField i.val
  let Δ := fun (i : Fin N) => ordinaryIncrement δ r ins removedRows removedLabels
    (prefixCoordinate hN i).2 (prefixCoordinate hN i).1 (w (prefixCoordinate hN i).2)
  let v := fun (i : Fin N) => (w (prefixCoordinate hN i).2) ^ 2 * (δ * r (prefixCoordinate hN i).2)
  have hmom (i : Fin N) := ordinaryIncrement_moments δ r μ hδ hbase hr hμ hsum
    ins removedRows removedLabels (prefixCoordinate hN i).2 (prefixCoordinate hN i).1
      (w (prefixCoordinate hN i).2) (hw0 _)
  have hmean : ∀ i (h : H i.castSucc),
      (∑ ξ, if history i.castSucc ξ = h then P.w ξ * Δ i ξ else 0) = 0 := by
    intro i h
    simpa [P, Δ, history, prefixCoordinate_key] using (hmom i).2.1 h
  have hvariance : ∀ i (h : H i.castSucc),
      (∑ ξ, if history i.castSucc ξ = h then P.w ξ * (Δ i ξ) ^ 2 else 0) ≤
        v i * P.pr (fun ξ => history i.castSucc ξ = h) := by
    intro i h
    simpa [P, Δ, history, v, prefixCoordinate_key] using (hmom i).2.2 h
  apply freedman_absolute H P history project ?_ Δ ?_ atom hAtom v ?_ ?_ hmean hvariance ε hε
  · intro i ξ
    exact (observedField_project i.val ξ).symm
  · intro m hm i hi ξ ξ' h
    apply ordinaryIncrement_adapted δ r ins removedRows removedLabels
      (prefixCoordinate hN i).2 (prefixCoordinate hN i).1 (w (prefixCoordinate hN i).2)
    · simpa [prefixCoordinate_key] using hi
    · exact h
  · intro i
    exact mul_nonneg (sq_nonneg _) (mul_nonneg hδ (hr _))
  · intro i ξ
    exact ((hmom i).1 ξ).trans (hwAtom _)

theorem prefix_sum_le {N M : ℕ} (hNM : N ≤ M) (f : Fin M → ℝ)
    (hf : ∀ i, 0 ≤ f i) :
    (∑ i : Fin N, f (i.castLE hNM)) ≤ ∑ i : Fin M, f i := by
  classical
  calc
    _ = ∑ j ∈ Finset.univ.image (fun i : Fin N => i.castLE hNM), f j := by
      rw [Finset.sum_image]
      intro i _ j _ hij
      exact Fin.ext (congrArg (fun x : Fin M => x.val) hij)
    _ ≤ ∑ i : Fin M, f i := by
      apply Finset.sum_le_sum_of_subset_of_nonneg
      · intro i _; exact Finset.mem_univ i
      · intro i _ _; exact hf i

theorem prescribed_prefix_loss_bound {T : ℕ} {R : Type*} [Fintype R] [DecidableEq R]
    {g : ℕ} {Ω : R → Type*} [∀ a, Fintype (Ω a)] [∀ a, DecidableEq (Ω a)]
    (ins : ∀ e : RowLabel R g, Option (MeshClockValue T (Ω e.1)))
    (ξ : ClockField T R g Ω) (removedRows : Finset R) (removedLabels : Finset (Fin g))
    (w : RowLabel R g → ℝ) (atom : ℝ) (hAtom : 0 ≤ atom)
    (hw0 : ∀ e, 0 ≤ w e) (hwAtom : ∀ e, w e ≤ atom)
    {N : ℕ} (hN : N ≤ T * (Fintype.card R * g)) :
    0 ≤ (∑ i : Fin N, prescribedLoss ins ξ removedRows removedLabels
        (prefixCoordinate hN i).2 (prefixCoordinate hN i).1 (w (prefixCoordinate hN i).2)) ∧
    (∑ i : Fin N, prescribedLoss ins ξ removedRows removedLabels
        (prefixCoordinate hN i).2 (prefixCoordinate hN i).1 (w (prefixCoordinate hN i).2)) ≤
      (prescribedCount ins : ℝ) * atom := by
  have hnonneg (t : Fin T) (e : RowLabel R g) :
      0 ≤ prescribedLoss ins ξ removedRows removedLabels e t (w e) := by
    unfold prescribedLoss
    split_ifs <;> simp [hw0 e]
  constructor
  · exact Finset.sum_nonneg fun i _ => hnonneg _ _
  · calc
      _ ≤ ∑ i : Fin (T * (Fintype.card R * g)), prescribedLoss ins ξ removedRows removedLabels
            (timeEdgeEquiv.symm i).2 (timeEdgeEquiv.symm i).1 (w (timeEdgeEquiv.symm i).2) := by
        simpa only [prefixCoordinate] using prefix_sum_le hN
          (fun i => prescribedLoss ins ξ removedRows removedLabels
            (timeEdgeEquiv.symm i).2 (timeEdgeEquiv.symm i).1 (w (timeEdgeEquiv.symm i).2))
          (fun i => hnonneg _ _)
      _ = ∑ p : Fin T × RowLabel R g, prescribedLoss ins ξ removedRows removedLabels p.2 p.1 (w p.2) := by
        symm
        apply Fintype.sum_equiv timeEdgeEquiv
        intro p
        simp
      _ ≤ _ := prescribed_loss_total ins ξ removedRows removedLabels w atom hAtom hw0 hwAtom

/-- Summing the edgewise predictable-variance allowances uses the weighted
rate load, rather than the number of edge coordinates. -/
theorem prefix_variance_bound {T : ℕ} {R : Type*} [Fintype R] [DecidableEq R]
    {g N : ℕ} (hN : N ≤ T * (Fintype.card R * g))
    (δ atom : ℝ) (r w : RowLabel R g → ℝ)
    (hδ : 0 ≤ δ) (hAtom : 0 ≤ atom) (hr : ∀ e, 0 ≤ r e)
    (hw0 : ∀ e, 0 ≤ w e) (hwAtom : ∀ e, w e ≤ atom)
    (hload : (∑ e, r e * w e) ≤ 1) :
    (∑ i : Fin N, (w (prefixCoordinate hN i).2) ^ 2 * (δ * r (prefixCoordinate hN i).2)) ≤
      (T : ℝ) * δ * atom := by
  classical
  have hinner : (∑ e : RowLabel R g, w e ^ 2 * (δ * r e)) ≤ δ * atom := by
    calc
      _ ≤ ∑ e : RowLabel R g, δ * atom * (r e * w e) := by
        apply Finset.sum_le_sum
        intro e _
        have hs : w e ^ 2 ≤ atom * w e := by
          nlinarith [mul_nonneg (hw0 e) (sub_nonneg.mpr (hwAtom e))]
        have h := mul_le_mul_of_nonneg_right hs (mul_nonneg hδ (hr e))
        nlinarith
      _ = δ * atom * ∑ e : RowLabel R g, r e * w e := by rw [Finset.mul_sum]
      _ ≤ δ * atom := by
        simpa using mul_le_mul_of_nonneg_left hload (mul_nonneg hδ hAtom)
  calc
    _ ≤ ∑ i : Fin (T * (Fintype.card R * g)),
          (w (timeEdgeEquiv.symm i).2) ^ 2 * (δ * r (timeEdgeEquiv.symm i).2) := by
      simpa only [prefixCoordinate] using prefix_sum_le hN
        (fun i => (w (timeEdgeEquiv.symm i).2) ^ 2 * (δ * r (timeEdgeEquiv.symm i).2))
        (fun i => mul_nonneg (sq_nonneg _) (mul_nonneg hδ (hr _)))
    _ = ∑ p : Fin T × RowLabel R g, w p.2 ^ 2 * (δ * r p.2) := by
      symm
      apply Fintype.sum_equiv timeEdgeEquiv
      intro p
      simp
    _ = (T : ℝ) * ∑ e : RowLabel R g, w e ^ 2 * (δ * r e) := by
      rw [Fintype.sum_prod_type]
      simp
    _ ≤ (T : ℝ) * (δ * atom) := mul_le_mul_of_nonneg_left hinner (Nat.cast_nonneg T)
    _ = _ := by ring

theorem ordinary_prefix_tail_bound {T : ℕ} {R : Type*} [Fintype R] [DecidableEq R]
    {g : ℕ} {Ω : R → Type*} [∀ a, Fintype (Ω a)] [∀ a, DecidableEq (Ω a)]
    (δ : ℝ) (r : RowLabel R g → ℝ) (μ : ∀ e : RowLabel R g, Ω e.1 → ℝ)
    (hδ : 0 ≤ δ) (hbase : ∀ e, 0 ≤ 1 - δ * r e)
    (hr : ∀ e, 0 ≤ r e) (hμ : ∀ e a, 0 ≤ μ e a)
    (hsum : ∀ e, ∑ a, μ e a = r e)
    (ins : ∀ e : RowLabel R g, Option (MeshClockValue T (Ω e.1)))
    (removedRows : Finset R) (removedLabels : Finset (Fin g))
    (w : RowLabel R g → ℝ) (atom : ℝ) (hAtom : 0 < atom)
    (hw0 : ∀ e, 0 ≤ w e) (hwAtom : ∀ e, w e ≤ atom)
    (hload : (∑ e, r e * w e) ≤ 1)
    {N : ℕ} (hN : N ≤ T * (Fintype.card R * g)) (ε : ℝ) (hε : 0 < ε) :
    let P := clockFieldLaw (fun f => markedClockLaw (T := T) δ (r f) (μ f) hδ
      (hbase f) (hr f) (hμ f) (hsum f))
    P.pr (fun ξ => ε ≤ |∑ i : Fin N,
      ordinaryIncrement δ r ins removedRows removedLabels
        (prefixCoordinate hN i).2 (prefixCoordinate hN i).1 (w (prefixCoordinate hN i).2) ξ|) ≤
      2 * Real.exp (-ε ^ 2 / (2 * ((T : ℝ) * δ * atom + atom * ε / 3))) := by
  classical
  dsimp only
  have htail := ordinary_prefix_tail δ r μ hδ hbase hr hμ hsum ins removedRows removedLabels
    w atom hAtom hw0 hwAtom hN ε hε
  have hV := prefix_variance_bound hN δ atom r w hδ hAtom.le hr hw0 hwAtom hload
  have hV0 : 0 ≤ ∑ i : Fin N,
      (w (prefixCoordinate hN i).2) ^ 2 * (δ * r (prefixCoordinate hN i).2) :=
    Finset.sum_nonneg fun i _ => mul_nonneg (sq_nonneg _) (mul_nonneg hδ (hr _))
  have hden : 0 < 2 * ((∑ i : Fin N,
      (w (prefixCoordinate hN i).2) ^ 2 * (δ * r (prefixCoordinate hN i).2)) + atom * ε / 3) := by
    have hp := mul_pos hAtom hε
    linarith
  have hden' : 2 * ((∑ i : Fin N,
      (w (prefixCoordinate hN i).2) ^ 2 * (δ * r (prefixCoordinate hN i).2)) + atom * ε / 3) ≤
      2 * ((T : ℝ) * δ * atom + atom * ε / 3) := by linarith
  have hquot := div_le_div_of_nonneg_left (sq_nonneg ε) hden hden'
  have hexp : Real.exp (-ε ^ 2 / (2 * ((∑ i : Fin N,
      (w (prefixCoordinate hN i).2) ^ 2 * (δ * r (prefixCoordinate hN i).2)) + atom * ε / 3))) ≤
      Real.exp (-ε ^ 2 / (2 * ((T : ℝ) * δ * atom + atom * ε / 3))) := by
    apply Real.exp_le_exp.mpr
    simpa only [neg_div] using neg_le_neg hquot
  exact htail.trans (mul_le_mul_of_nonneg_left hexp (by norm_num))

theorem boundaryPrefix_le {T : ℕ} {R : Type*} [Fintype R] {g : ℕ}
    (t : Fin (T + 1)) : t.val * (Fintype.card R * g) ≤ T * (Fintype.card R * g) :=
  Nat.mul_le_mul_right _ (Nat.le_of_lt_succ t.isLt)

noncomputable def massNoise {T : ℕ} {R : Type*} [Fintype R] [DecidableEq R]
    {g : ℕ} {Ω : R → Type*} [∀ a, Fintype (Ω a)] [∀ a, DecidableEq (Ω a)]
    (δ : ℝ) (r : RowLabel R g → ℝ)
    (ins : ∀ e : RowLabel R g, Option (MeshClockValue T (Ω e.1)))
    (removedRows : Finset R) (removedLabels : Finset (Fin g))
    (w : RowLabel R g → ℝ) (t : Fin (T + 1)) (ξ : ClockField T R g Ω) : ℝ :=
  ∑ i : Fin (t.val * (Fintype.card R * g)),
    ordinaryIncrement δ r ins removedRows removedLabels
      (prefixCoordinate (boundaryPrefix_le t) i).2 (prefixCoordinate (boundaryPrefix_le t) i).1
      (w (prefixCoordinate (boundaryPrefix_le t) i).2) ξ

/-- The mesh-boundary mass identity separates compensated ordinary noise,
ordinary drift, and the total prescribed loss. -/
theorem prefix_mass_balance {T : ℕ} {R : Type*} [Fintype R] [DecidableEq R]
    {g : ℕ} {Ω : R → Type*} [∀ a, Fintype (Ω a)] [∀ a, DecidableEq (Ω a)]
    (δ : ℝ) (r : R → Fin g → ℝ)
    (ins : ∀ e : RowLabel R g, Option (MeshClockValue T (Ω e.1)))
    (ξ : ClockField T R g Ω) (removedRows : Finset R) (removedLabels : Finset (Fin g))
    (t : Fin (T + 1)) (u : Endpoint R g) :
    endpointMass r (prescribedField ins ξ) removedRows removedLabels
        (t.val * (Fintype.card R * g)) u =
      endpointMass r (prescribedField ins ξ) removedRows removedLabels 0 u -
        massNoise δ (fun e => r e.1 e.2) ins removedRows removedLabels (endpointWeight r u) t ξ -
        δ * (∑ j : Fin t.val, tickDrift r ins ξ removedRows removedLabels j.val u) -
        (∑ i : Fin (t.val * (Fintype.card R * g)),
          prescribedLoss ins ξ removedRows removedLabels (prefixCoordinate (boundaryPrefix_le t) i).2
            (prefixCoordinate (boundaryPrefix_le t) i).1
            (endpointWeight r u (prefixCoordinate (boundaryPrefix_le t) i).2)) := by
  classical
  let hN := boundaryPrefix_le (R := R) (g := g) t
  have hm := prefix_mass_loss r (prescribedField ins ξ) removedRows removedLabels u
    (t.val * (Fintype.card R * g)) hN
  have hsplit (i : Fin (t.val * (Fintype.card R * g))) :
      (if keyFree (prescribedField ins ξ) removedRows removedLabels i.val (prefixCoordinate hN i).2 ∧
          (∃ o, prescribedField ins ξ (prefixCoordinate hN i).2 = .tick (prefixCoordinate hN i).1 o)
        then endpointWeight r u (prefixCoordinate hN i).2 else 0) =
      ordinaryIncrement δ (fun e => r e.1 e.2) ins removedRows removedLabels
        (prefixCoordinate hN i).2 (prefixCoordinate hN i).1
          (endpointWeight r u (prefixCoordinate hN i).2) ξ +
      δ * (if ins (prefixCoordinate hN i).2 = none ∧
          keyFree (prescribedField ins ξ) removedRows removedLabels i.val (prefixCoordinate hN i).2 then
        r (prefixCoordinate hN i).2.1 (prefixCoordinate hN i).2.2 *
          endpointWeight r u (prefixCoordinate hN i).2 else 0) +
      prescribedLoss ins ξ removedRows removedLabels (prefixCoordinate hN i).2
        (prefixCoordinate hN i).1 (endpointWeight r u (prefixCoordinate hN i).2) := by
    simpa only [prefixCoordinate_key] using accepted_loss_decomposition δ (fun e => r e.1 e.2)
      ins ξ removedRows removedLabels (prefixCoordinate hN i).2 (prefixCoordinate hN i).1
        (endpointWeight r u (prefixCoordinate hN i).2)
  simp_rw [hsplit] at hm
  rw [Finset.sum_add_distrib, Finset.sum_add_distrib, ← Finset.mul_sum] at hm
  have hsum : (∑ i : Fin (t.val * (Fintype.card R * g)),
      if ins (prefixCoordinate hN i).2 = none ∧
          keyFree (prescribedField ins ξ) removedRows removedLabels i.val (prefixCoordinate hN i).2 then
        r (prefixCoordinate hN i).2.1 (prefixCoordinate hN i).2.2 *
          endpointWeight r u (prefixCoordinate hN i).2 else 0) =
      ∑ j : Fin t.val, tickDrift r ins ξ removedRows removedLabels j.val u := by
    have h := prefix_tick_sum (Nat.le_of_lt_succ t.isLt)
      (fun (s : Fin T) (e : RowLabel R g) =>
        if ins e = none ∧ keyFree (prescribedField ins ξ) removedRows removedLabels (edgeKey e s.val) e
          then r e.1 e.2 * endpointWeight r u e else 0)
    simpa only [prefixCoordinate_key, tickDrift, Fin.val_castLE, hN] using h
  rw [hsum] at hm
  dsimp only [massNoise]
  linarith

/-- Simultaneous compensated-noise control at all mesh boundaries and all
members of a finite family of queried masses. -/
theorem ordinary_noise_good {T : ℕ} {R U : Type*} [Fintype R] [DecidableEq R] [Fintype U]
    {g : ℕ} {Ω : R → Type*} [∀ a, Fintype (Ω a)] [∀ a, DecidableEq (Ω a)]
    (δ : ℝ) (r : RowLabel R g → ℝ) (μ : ∀ e : RowLabel R g, Ω e.1 → ℝ)
    (hδ : 0 ≤ δ) (hbase : ∀ e, 0 ≤ 1 - δ * r e)
    (hr : ∀ e, 0 ≤ r e) (hμ : ∀ e a, 0 ≤ μ e a)
    (hsum : ∀ e, ∑ a, μ e a = r e)
    (ins : ∀ e : RowLabel R g, Option (MeshClockValue T (Ω e.1)))
    (removedRows : Finset R) (removedLabels : Finset (Fin g))
    (w : U → RowLabel R g → ℝ) (atom : ℝ) (hAtom : 0 < atom)
    (hw0 : ∀ u e, 0 ≤ w u e) (hwAtom : ∀ u e, w u e ≤ atom)
    (hload : ∀ u, (∑ e, r e * w u e) ≤ 1) (ε : ℝ) (hε : 0 < ε) :
    let P := clockFieldLaw (fun f => markedClockLaw (T := T) δ (r f) (μ f) hδ
      (hbase f) (hr f) (hμ f) (hsum f))
    P.pr (fun ξ => ∀ t : Fin (T + 1), ∀ u : U,
      |massNoise δ r ins removedRows removedLabels (w u) t ξ| ≤ ε) ≥
      1 - ((T + 1 : ℕ) : ℝ) * (Fintype.card U : ℝ) *
        (2 * Real.exp (-ε ^ 2 / (2 * ((T : ℝ) * δ * atom + atom * ε / 3)))) := by
  classical
  dsimp only
  let P := clockFieldLaw (fun f => markedClockLaw (T := T) δ (r f) (μ f) hδ
    (hbase f) (hr f) (hμ f) (hsum f))
  let bad : (Fin (T + 1) × U) → ClockField T R g Ω → Prop :=
    fun k ξ => ε < |massNoise δ r ins removedRows removedLabels (w k.2) k.1 ξ|
  let tail := 2 * Real.exp (-ε ^ 2 / (2 * ((T : ℝ) * δ * atom + atom * ε / 3)))
  have htail (k : Fin (T + 1) × U) : P.pr (bad k) ≤ tail := by
    have h := ordinary_prefix_tail_bound δ r μ hδ hbase hr hμ hsum ins removedRows removedLabels
      (w k.2) atom hAtom (hw0 k.2) (hwAtom k.2) (hload k.2) (boundaryPrefix_le k.1) ε hε
    apply (finProb_pr_mono P ?_).trans h
    intro ξ hξ
    exact hξ.le
  let good : ClockField T R g Ω → Prop := fun ξ =>
    ∀ t : Fin (T + 1), ∀ u : U, |massNoise δ r ins removedRows removedLabels (w u) t ξ| ≤ ε
  have hbad : P.pr (fun ξ => ¬ good ξ) ≤ ((T + 1 : ℕ) : ℝ) * (Fintype.card U : ℝ) * tail := by
    have hevent : (fun ξ => ¬ good ξ) =
        (fun ξ => ∃ k ∈ (Finset.univ : Finset (Fin (T + 1) × U)), bad k ξ) := by
      funext ξ
      simp [good, bad, not_forall, not_le, Prod.exists]
    rw [hevent]
    calc
      _ ≤ ∑ k : Fin (T + 1) × U, P.pr (bad k) := finProb_pr_biUnion_le_sum P Finset.univ bad
      _ ≤ ∑ k : Fin (T + 1) × U, tail := Finset.sum_le_sum fun k _ => htail k
      _ = _ := by simp [Fintype.card_prod, mul_assoc]
  have hcomp := finProb_pr_compl P good
  change 1 - ((T + 1 : ℕ) : ℝ) * (Fintype.card U : ℝ) * tail ≤ P.pr good
  linarith

theorem row_weighted_load {R : Type*} [Fintype R] {g : ℕ}
    (r : R → Fin g → ℝ) (θ : ℝ) (hrow : ∀ a, ∑ y, r a y = 1)
    (hcol : ∀ y, ∑ a, r a y = θ) (hθ : θ ≤ 1) (a : R) :
    (∑ e : RowLabel R g, r e.1 e.2 * r a e.2) ≤ 1 := by
  calc
    _ = ∑ y : Fin g, (∑ b : R, r b y) * r a y := by
      rw [Fintype.sum_prod_type, Finset.sum_comm]
      simp only [Finset.sum_mul]
    _ = θ := by
      simp_rw [hcol]
      rw [← Finset.mul_sum, hrow, mul_one]
    _ ≤ 1 := hθ

theorem label_weighted_load {R : Type*} [Fintype R] {g : ℕ}
    (r : R → Fin g → ℝ) (θ : ℝ) (hrow : ∀ a, ∑ y, r a y = 1)
    (hcol : ∀ y, ∑ a, r a y = θ) (hθ : θ ≤ 1) (y : Fin g) :
    (∑ e : RowLabel R g, r e.1 e.2 * r e.1 y) ≤ 1 := by
  calc
    _ = ∑ a : R, (∑ z : Fin g, r a z) * r a y := by
      rw [Fintype.sum_prod_type]
      simp only [Finset.sum_mul]
    _ = θ := by simp [hrow, hcol]
    _ ≤ 1 := hθ

/-- Discrete Gronwall for cumulative errors. The noise allowance is paid once,
instead of once at every mesh tick. -/
theorem cumulative_gronwall {T : ℕ} (E : ℕ → ℝ) (ε c : ℝ)
    (hε : 0 ≤ ε) (hc : 0 ≤ c)
    (hrec : ∀ k ≤ T, E k ≤ ε + c * ∑ j ∈ Finset.range k, E j) :
    ∀ k ≤ T, E k ≤ ε * (1 + c) ^ k := by
  have hgeom (k : ℕ) :
      1 + c * (∑ j ∈ Finset.range k, (1 + c) ^ j) = (1 + c) ^ k := by
    induction k with
    | zero => simp
    | succ k ih =>
        rw [Finset.sum_range_succ, mul_add, ← add_assoc, ih, pow_succ]
        ring
  intro k
  induction k using Nat.strong_induction_on with
  | h k ih =>
      intro hk
      calc
        E k ≤ ε + c * ∑ j ∈ Finset.range k, E j := hrec k hk
        _ ≤ ε + c * ∑ j ∈ Finset.range k, ε * (1 + c) ^ j := by
          apply add_le_add_right
          apply mul_le_mul_of_nonneg_left _ hc
          apply Finset.sum_le_sum
          intro j hj
          have hjk := Finset.mem_range.mp hj
          exact ih j hjk (le_trans hjk.le hk)
        _ = ε * (1 + c) ^ k := by
          rw [← Finset.mul_sum]
          nlinarith [hgeom k]

/-- Exponential form of the same estimate. -/
theorem cumulative_gronwall_exp {T : ℕ} (E : ℕ → ℝ) (ε c : ℝ)
    (hε : 0 ≤ ε) (hc : 0 ≤ c)
    (hrec : ∀ k ≤ T, E k ≤ ε + c * ∑ j ∈ Finset.range k, E j) :
    ∀ k ≤ T, E k ≤ ε * Real.exp (c * (k : ℝ)) := by
  intro k hk
  have hpow : (1 + c) ^ k ≤ Real.exp (c * (k : ℝ)) := by
    calc
      (1 + c) ^ k ≤ (Real.exp c) ^ k := by
        apply pow_le_pow_left₀ (by linarith)
        simpa [add_comm] using Real.add_one_le_exp c
      _ = Real.exp (c * (k : ℝ)) := by rw [← Real.exp_nat_mul]; congr 1; ring
  exact (cumulative_gronwall E ε c hε hc hrec k hk).trans
    (mul_le_mul_of_nonneg_left hpow hε)

/-- Gronwall also absorbs a right-endpoint error in the drift sandwich. -/
theorem cumulative_gronwall_implicit {T : ℕ} (E : ℕ → ℝ) (ε δ : ℝ)
    (hε : 0 ≤ ε) (hδ : 0 ≤ δ) (hδsmall : δ ≤ 1 / 6)
    (hrec : ∀ k ≤ T, E k ≤ ε + 2 * δ * ∑ j ∈ Finset.range (k + 1), E j) :
    ∀ k ≤ T, E k ≤ 2 * ε * Real.exp (3 * δ * (k : ℝ)) := by
  have hden : 0 < 1 - 2 * δ := by linarith
  let c := 2 * δ / (1 - 2 * δ)
  let ε' := ε / (1 - 2 * δ)
  have hc : 0 ≤ c := by dsimp [c]; positivity
  have hε' : 0 ≤ ε' := by dsimp [ε']; positivity
  have hrec' : ∀ k ≤ T, E k ≤ ε' + c * ∑ j ∈ Finset.range k, E j := by
    intro k hk
    have h := hrec k hk
    rw [Finset.sum_range_succ] at h
    have hE : E k * (1 - 2 * δ) ≤ ε + 2 * δ * ∑ j ∈ Finset.range k, E j := by
      nlinarith
    have heq : ε' + c * ∑ j ∈ Finset.range k, E j =
        (ε + 2 * δ * ∑ j ∈ Finset.range k, E j) / (1 - 2 * δ) := by
      dsimp [ε', c]
      field_simp
    rw [heq]
    exact (le_div_iff₀ hden).mpr hE
  have hc3 : c ≤ 3 * δ := by
    dsimp [c]
    apply (div_le_iff₀ hden).mpr
    nlinarith [mul_nonneg hδ (sub_nonneg.mpr hδsmall)]
  have hε2 : ε' ≤ 2 * ε := by
    dsimp [ε']
    apply (div_le_iff₀ hden).mpr
    nlinarith [mul_nonneg hε (sub_nonneg.mpr hδsmall)]
  intro k hk
  have h := cumulative_gronwall_exp E ε' c hε' hc hrec' k hk
  calc
    E k ≤ ε' * Real.exp (c * (k : ℝ)) := h
    _ ≤ (2 * ε) * Real.exp (3 * δ * (k : ℝ)) := by
      apply mul_le_mul hε2
      · apply Real.exp_le_exp.mpr
        exact mul_le_mul_of_nonneg_right hc3 (Nat.cast_nonneg k)
      · exact Real.exp_nonneg _
      · exact mul_nonneg (by norm_num) hε

noncomputable def trackingError {T : ℕ} {R : Type*} [Fintype R] [DecidableEq R]
    {g : ℕ} {Ω : R → Type*} [∀ a, Fintype (Ω a)] [∀ a, DecidableEq (Ω a)]
    (r : R → Fin g → ℝ) (ξ : ClockField T R g Ω) (removedRows : Finset R)
    (removedLabels : Finset (Fin g)) (target : ℕ → Endpoint R g → ℝ) (k : ℕ) : ℝ :=
  Finset.univ.sup' (Finset.univ_nonempty :
    (Finset.univ : Finset (Option (Fin (T + 1) × Endpoint R g))).Nonempty)
    (fun p => match p with
      | none => 0
      | some (t, u) => if t.val ≤ k then
          |endpointMass r ξ removedRows removedLabels (t.val * (Fintype.card R * g)) u - target t.val u|
        else 0)

theorem trackingError_nonneg {T : ℕ} {R : Type*} [Fintype R] [DecidableEq R]
    {g : ℕ} {Ω : R → Type*} [∀ a, Fintype (Ω a)] [∀ a, DecidableEq (Ω a)]
    (r : R → Fin g → ℝ) (ξ : ClockField T R g Ω) (removedRows : Finset R)
    (removedLabels : Finset (Fin g)) (target : ℕ → Endpoint R g → ℝ) (k : ℕ) :
    0 ≤ trackingError r ξ removedRows removedLabels target k := by
  unfold trackingError
  apply (Finset.le_sup'_iff _).mpr
  exact ⟨none, Finset.mem_univ _, le_refl 0⟩

theorem trackingError_ge {T : ℕ} {R : Type*} [Fintype R] [DecidableEq R]
    {g : ℕ} {Ω : R → Type*} [∀ a, Fintype (Ω a)] [∀ a, DecidableEq (Ω a)]
    (r : R → Fin g → ℝ) (ξ : ClockField T R g Ω) (removedRows : Finset R)
    (removedLabels : Finset (Fin g)) (target : ℕ → Endpoint R g → ℝ)
    (t : Fin (T + 1)) (u : Endpoint R g) {k : ℕ} (ht : t.val ≤ k) :
    |endpointMass r ξ removedRows removedLabels (t.val * (Fintype.card R * g)) u - target t.val u| ≤
      trackingError r ξ removedRows removedLabels target k := by
  unfold trackingError
  apply (Finset.le_sup'_iff _).mpr
  refine ⟨some (t, u), Finset.mem_univ _, ?_⟩
  simp [ht]

theorem trackingError_mono {T : ℕ} {R : Type*} [Fintype R] [DecidableEq R]
    {g : ℕ} {Ω : R → Type*} [∀ a, Fintype (Ω a)] [∀ a, DecidableEq (Ω a)]
    (r : R → Fin g → ℝ) (ξ : ClockField T R g Ω) (removedRows : Finset R)
    (removedLabels : Finset (Fin g)) (target : ℕ → Endpoint R g → ℝ) :
    Monotone (trackingError r ξ removedRows removedLabels target) := by
  intro k m hkm
  unfold trackingError
  apply Finset.sup'_mono_fun
  intro p _
  cases p with
  | none => exact le_refl 0
  | some p =>
      rcases p with ⟨t, u⟩
      by_cases ht : t.val ≤ k
      · simp [ht, ht.trans hkm]
      · simp only [if_neg ht]
        split_ifs <;> simp [abs_nonneg]

theorem trackingError_le {T : ℕ} {R : Type*} [Fintype R] [DecidableEq R]
    {g : ℕ} {Ω : R → Type*} [∀ a, Fintype (Ω a)] [∀ a, DecidableEq (Ω a)]
    (r : R → Fin g → ℝ) (ξ : ClockField T R g Ω) (removedRows : Finset R)
    (removedLabels : Finset (Fin g)) (target : ℕ → Endpoint R g → ℝ)
    (k : ℕ) (b : ℝ) (hb : 0 ≤ b)
    (hpoint : ∀ (t : Fin (T + 1)) u, t.val ≤ k →
      |endpointMass r ξ removedRows removedLabels (t.val * (Fintype.card R * g)) u - target t.val u| ≤ b) :
    trackingError r ξ removedRows removedLabels target k ≤ b := by
  apply Finset.sup'_le
  intro p _
  cases p with
  | none => exact hb
  | some p =>
      rcases p with ⟨t, u⟩
      by_cases ht : t.val ≤ k
      · simp only [if_pos ht]; exact hpoint t u ht
      · simp only [if_neg ht]; exact hb

theorem target_telescope {T : ℕ} (target d : ℕ → ℝ) (δ : ℝ)
    (hstep : ∀ j < T, target (j + 1) = target j - δ * d j) :
    ∀ k ≤ T, target k = target 0 - δ * ∑ j ∈ Finset.range k, d j := by
  intro k
  induction k with
  | zero => intro _; simp
  | succ k ih =>
      intro hk
      rw [hstep k (by omega), ih (by omega), Finset.sum_range_succ]
      ring

theorem tracking_error_recurrence {T : ℕ} {R : Type*} [Fintype R] [DecidableEq R]
    {g : ℕ} {Ω : R → Type*} [∀ a, Fintype (Ω a)] [∀ a, DecidableEq (Ω a)]
    (r : R → Fin g → ℝ) (hr : ∀ a y, 0 ≤ r a y)
    (atom : ℝ) (hAtom : 0 ≤ atom) (hrAtom : ∀ a y, r a y ≤ atom)
    (δ : ℝ) (hδ : 0 ≤ δ)
    (ins : ∀ e : RowLabel R g, Option (MeshClockValue T (Ω e.1)))
    (ξ : ClockField T R g Ω) (removedRows : Finset R) (removedLabels : Finset (Fin g))
    (target : ℕ → Endpoint R g → ℝ) (d : ℕ → ℝ)
    (initial ε : ℝ) (hinitial : 0 ≤ initial) (hε : 0 ≤ ε)
    (htarget : ∀ j < T, ∀ u, target (j + 1) u = target j u - δ * d j)
    (hdstep : ∀ j < T, |d (j + 1) - d j| ≤ 2 * δ)
    (hinit : ∀ u, |endpointMass r (prescribedField ins ξ) removedRows removedLabels 0 u - target 0 u| ≤ initial)
    (happrox : ∀ j ≤ T, ∀ u,
      |fullDrift r (prescribedField ins ξ) removedRows removedLabels
          (j * (Fintype.card R * g)) u - d j| ≤
        2 * trackingError r (prescribedField ins ξ) removedRows removedLabels target j)
    (hnoise : ∀ (t : Fin (T + 1)) u,
      |massNoise δ (fun e => r e.1 e.2) ins removedRows removedLabels (endpointWeight r u) t ξ| ≤ ε) :
    ∀ k ≤ T, trackingError r (prescribedField ins ξ) removedRows removedLabels target k ≤
      initial + ε + (prescribedCount ins : ℝ) * atom +
        (T : ℝ) * δ * ((prescribedCount ins : ℝ) * atom ^ 2 + 2 * δ) +
        2 * δ * ∑ j ∈ Finset.range (k + 1),
          trackingError r (prescribedField ins ξ) removedRows removedLabels target j := by
  classical
  let E := trackingError r (prescribedField ins ξ) removedRows removedLabels target
  let skip := (prescribedCount ins : ℝ) * atom ^ 2 + 2 * δ
  have hskip : 0 ≤ skip := by dsimp [skip]; positivity
  have hE : ∀ j, 0 ≤ E j := trackingError_nonneg r (prescribedField ins ξ) removedRows removedLabels target
  have hmono : Monotone E := trackingError_mono r (prescribedField ins ξ) removedRows removedLabels target
  intro k hk
  apply trackingError_le
  · exact add_nonneg (by positivity)
      (mul_nonneg (mul_nonneg (by norm_num) hδ) (Finset.sum_nonneg fun j _ => hE j))
  · intro t u ht
    have htT : t.val ≤ T := Nat.le_of_lt_succ t.isLt
    have hmass := prefix_mass_balance δ r ins ξ removedRows removedLabels t u
    have htargetSum := target_telescope (fun j => target j u) d δ
      (by intro j hj; exact htarget j hj u) t.val htT
    rw [← Fin.sum_univ_eq_sum_range] at htargetSum
    have hw0 (e : RowLabel R g) : 0 ≤ endpointWeight r u e := by
      rcases u with a | y
      · exact hr a e.2
      · exact hr e.1 y
    have hwAtom (e : RowLabel R g) : endpointWeight r u e ≤ atom := by
      rcases u with a | y
      · exact hrAtom a e.2
      · exact hrAtom e.1 y
    have hpres := prescribed_prefix_loss_bound ins ξ removedRows removedLabels
      (endpointWeight r u) atom hAtom hw0 hwAtom (boundaryPrefix_le t)
    have hdiff (j : Fin t.val) :
        |tickDrift r ins ξ removedRows removedLabels j.val u - d j.val| ≤ 2 * E (j.val + 1) + skip := by
      have hjT : j.val < T := lt_of_lt_of_le j.isLt htT
      have hj1 : j.val + 1 ≤ T := Nat.succ_le_of_lt hjT
      have hs := tickDrift_sandwich r hr atom hAtom hrAtom ins ξ removedRows removedLabels j.val u
      have hstart := abs_le.mp (happrox j.val hjT.le u)
      have hend := abs_le.mp (happrox (j.val + 1) hj1 u)
      have hd := abs_le.mp (hdstep j.val hjT)
      have hmon := hmono (Nat.le_succ j.val)
      apply abs_le.mpr
      dsimp [skip, E] at *
      constructor <;> linarith
    have hsumErr : (∑ j : Fin t.val, E (j.val + 1)) ≤ ∑ j ∈ Finset.range (k + 1), E j := by
      calc
        _ ≤ ∑ j : Fin (t.val + 1), E j.val := by
          rw [Fin.sum_univ_succ]
          simp only [Fin.val_zero, Fin.val_succ]
          linarith [hE 0]
        _ ≤ ∑ j : Fin (k + 1), E j.val := by
          simpa only [Fin.val_castLE] using prefix_sum_le (Nat.succ_le_succ ht)
            (fun j : Fin (k + 1) => E j.val) (fun j => hE j.val)
        _ = _ := Fin.sum_univ_eq_sum_range E (k + 1)
    have hsumDiff : |δ * (∑ j : Fin t.val,
        (tickDrift r ins ξ removedRows removedLabels j.val u - d j.val))| ≤
        2 * δ * (∑ j ∈ Finset.range (k + 1), E j) + (T : ℝ) * δ * skip := by
      calc
        _ = δ * |∑ j : Fin t.val, (tickDrift r ins ξ removedRows removedLabels j.val u - d j.val)| := by
          rw [abs_mul, abs_of_nonneg hδ]
        _ ≤ δ * ∑ j : Fin t.val, |(tickDrift r ins ξ removedRows removedLabels j.val u - d j.val)| :=
          mul_le_mul_of_nonneg_left (Finset.abs_sum_le_sum_abs _ _) hδ
        _ ≤ δ * ∑ j : Fin t.val, (2 * E (j.val + 1) + skip) :=
          mul_le_mul_of_nonneg_left (Finset.sum_le_sum fun j _ => hdiff j) hδ
        _ = 2 * δ * (∑ j : Fin t.val, E (j.val + 1)) + (t.val : ℝ) * δ * skip := by
          rw [Finset.sum_add_distrib, ← Finset.mul_sum]
          simp
          ring
        _ ≤ 2 * δ * (∑ j ∈ Finset.range (k + 1), E j) + (T : ℝ) * δ * skip := by
          apply add_le_add
          · exact mul_le_mul_of_nonneg_left hsumErr (mul_nonneg (by norm_num) hδ)
          · have htR : (t.val : ℝ) ≤ (T : ℝ) := by exact_mod_cast htT
            simpa only [mul_assoc] using mul_le_mul_of_nonneg_right htR (mul_nonneg hδ hskip)
    have hsum : (∑ j : Fin t.val, (tickDrift r ins ξ removedRows removedLabels j.val u - d j.val)) =
        (∑ j : Fin t.val, tickDrift r ins ξ removedRows removedLabels j.val u) - ∑ j : Fin t.val, d j.val := by
      rw [Finset.sum_sub_distrib]
    have herrEq : endpointMass r (prescribedField ins ξ) removedRows removedLabels
          (t.val * (Fintype.card R * g)) u - target t.val u =
        ((endpointMass r (prescribedField ins ξ) removedRows removedLabels 0 u - target 0 u) -
          massNoise δ (fun e => r e.1 e.2) ins removedRows removedLabels (endpointWeight r u) t ξ) -
          (∑ i : Fin (t.val * (Fintype.card R * g)), prescribedLoss ins ξ removedRows removedLabels
            (prefixCoordinate (boundaryPrefix_le t) i).2 (prefixCoordinate (boundaryPrefix_le t) i).1
            (endpointWeight r u (prefixCoordinate (boundaryPrefix_le t) i).2)) -
          δ * (∑ j : Fin t.val, (tickDrift r ins ξ removedRows removedLabels j.val u - d j.val)) := by
      rw [hmass, htargetSum, hsum]
      ring
    rw [herrEq]
    have hAbs (x y : ℝ) : |x - y| ≤ |x| + |y| := by
      simpa [sub_eq_add_neg] using abs_add_le x (-y)
    have h1 := hAbs
      (endpointMass r (prescribedField ins ξ) removedRows removedLabels 0 u - target 0 u)
      (massNoise δ (fun e => r e.1 e.2) ins removedRows removedLabels (endpointWeight r u) t ξ)
    have h2 := hAbs
      ((endpointMass r (prescribedField ins ξ) removedRows removedLabels 0 u - target 0 u) -
        massNoise δ (fun e => r e.1 e.2) ins removedRows removedLabels (endpointWeight r u) t ξ)
      (∑ i : Fin (t.val * (Fintype.card R * g)), prescribedLoss ins ξ removedRows removedLabels
        (prefixCoordinate (boundaryPrefix_le t) i).2 (prefixCoordinate (boundaryPrefix_le t) i).1
        (endpointWeight r u (prefixCoordinate (boundaryPrefix_le t) i).2))
    have h3 := hAbs
      (((endpointMass r (prescribedField ins ξ) removedRows removedLabels 0 u - target 0 u) -
        massNoise δ (fun e => r e.1 e.2) ins removedRows removedLabels (endpointWeight r u) t ξ) -
        (∑ i : Fin (t.val * (Fintype.card R * g)), prescribedLoss ins ξ removedRows removedLabels
          (prefixCoordinate (boundaryPrefix_le t) i).2 (prefixCoordinate (boundaryPrefix_le t) i).1
          (endpointWeight r u (prefixCoordinate (boundaryPrefix_le t) i).2)))
      (δ * (∑ j : Fin t.val, (tickDrift r ins ξ removedRows removedLabels j.val u - d j.val)))
    rw [abs_of_nonneg hpres.1] at h2
    have hi := hinit u
    have hn := hnoise t u
    dsimp [skip, E] at hsumDiff
    linarith

theorem finite_tracking_bound {T : ℕ} {R : Type*} [Fintype R] [DecidableEq R]
    {g : ℕ} {Ω : R → Type*} [∀ a, Fintype (Ω a)] [∀ a, DecidableEq (Ω a)]
    (r : R → Fin g → ℝ) (hr : ∀ a y, 0 ≤ r a y)
    (atom : ℝ) (hAtom : 0 ≤ atom) (hrAtom : ∀ a y, r a y ≤ atom)
    (δ : ℝ) (hδ : 0 ≤ δ) (hδsmall : δ ≤ 1 / 6)
    (ins : ∀ e : RowLabel R g, Option (MeshClockValue T (Ω e.1)))
    (ξ : ClockField T R g Ω) (removedRows : Finset R) (removedLabels : Finset (Fin g))
    (target : ℕ → Endpoint R g → ℝ) (d : ℕ → ℝ)
    (initial ε : ℝ) (hinitial : 0 ≤ initial) (hε : 0 ≤ ε)
    (htarget : ∀ j < T, ∀ u, target (j + 1) u = target j u - δ * d j)
    (hdstep : ∀ j < T, |d (j + 1) - d j| ≤ 2 * δ)
    (hinit : ∀ u, |endpointMass r (prescribedField ins ξ) removedRows removedLabels 0 u - target 0 u| ≤ initial)
    (happrox : ∀ j ≤ T, ∀ u,
      |fullDrift r (prescribedField ins ξ) removedRows removedLabels
          (j * (Fintype.card R * g)) u - d j| ≤
        2 * trackingError r (prescribedField ins ξ) removedRows removedLabels target j)
    (hnoise : ∀ (t : Fin (T + 1)) u,
      |massNoise δ (fun e => r e.1 e.2) ins removedRows removedLabels (endpointWeight r u) t ξ| ≤ ε) :
    ∀ t : Fin (T + 1), ∀ u : Endpoint R g,
      |endpointMass r (prescribedField ins ξ) removedRows removedLabels
          (t.val * (Fintype.card R * g)) u - target t.val u| ≤
        2 * (initial + ε + (prescribedCount ins : ℝ) * atom +
          (T : ℝ) * δ * ((prescribedCount ins : ℝ) * atom ^ 2 + 2 * δ)) *
          Real.exp (3 * δ * (T : ℝ)) := by
  let E := trackingError r (prescribedField ins ξ) removedRows removedLabels target
  let b := initial + ε + (prescribedCount ins : ℝ) * atom +
    (T : ℝ) * δ * ((prescribedCount ins : ℝ) * atom ^ 2 + 2 * δ)
  have hb : 0 ≤ b := by dsimp [b]; positivity
  have hrec := tracking_error_recurrence r hr atom hAtom hrAtom δ hδ ins ξ
    removedRows removedLabels target d initial ε hinitial hε htarget hdstep hinit happrox hnoise
  have hbound := cumulative_gronwall_implicit E b δ hb hδ hδsmall hrec T (le_refl T)
  intro t u
  exact (trackingError_ge r (prescribedField ins ξ) removedRows removedLabels target t u
    (Nat.le_of_lt_succ t.isLt)).trans hbound

/-- A weighted drift differs from its deterministic comparison by at most
the mass error plus the uniform error in the neighboring masses. -/
theorem weighted_drift_error {ι : Type*} [Fintype ι]
    (w Y : ι → ℝ) (m q z ε : ℝ)
    (hw : ∀ i, 0 ≤ w i) (hm : (∑ i, w i) = m)
    (hm1 : m ≤ 1) (hz : |z| ≤ 1) (hε : 0 ≤ ε)
    (hY : ∀ i, |Y i - z| ≤ ε) (hq : |m - q| ≤ ε) :
    |(∑ i, w i * Y i) - z * q| ≤ 2 * ε := by
  have hm0 : 0 ≤ m := by rw [← hm]; exact Finset.sum_nonneg fun i _ => hw i
  have hsum : |∑ i, w i * (Y i - z)| ≤ ε := by
    calc
      |∑ i, w i * (Y i - z)| ≤ ∑ i, |w i * (Y i - z)| :=
        Finset.abs_sum_le_sum_abs _ _
      _ = ∑ i, w i * |Y i - z| := by
        simp_rw [abs_mul, abs_of_nonneg (hw _)]
      _ ≤ ∑ i, w i * ε :=
        Finset.sum_le_sum fun i _ => mul_le_mul_of_nonneg_left (hY i) (hw i)
      _ = m * ε := by rw [← Finset.sum_mul, hm]
      _ ≤ ε := by simpa using mul_le_mul_of_nonneg_right hm1 hε
  have hdiff : (∑ i, w i * Y i) - z * q =
      (∑ i, w i * (Y i - z)) + z * (m - q) := by
    simp_rw [mul_sub]
    rw [Finset.sum_sub_distrib, ← Finset.sum_mul, hm]
    ring
  rw [hdiff]
  calc
    _ ≤ |∑ i, w i * (Y i - z)| + |z * (m - q)| := abs_add_le _ _
    _ ≤ ε + ε := by
      apply add_le_add hsum
      rw [abs_mul]
      exact (mul_le_mul_of_nonneg_left hq (abs_nonneg z)).trans
        (by simpa using mul_le_mul_of_nonneg_right hz hε)
    _ = 2 * ε := by ring

theorem fullDrift_error {T : ℕ} {R : Type*} [Fintype R] [DecidableEq R]
    {g : ℕ} {Ω : R → Type*} [∀ a, Fintype (Ω a)] [∀ a, DecidableEq (Ω a)]
    (r : R → Fin g → ℝ) (hr : ∀ a y, 0 ≤ r a y)
    (θ : ℝ) (hθ0 : 0 ≤ θ) (hθ1 : θ ≤ 1)
    (hrow : ∀ a, ∑ y, r a y = 1) (hcol : ∀ y, ∑ a, r a y = θ)
    (ξ : ClockField T R g Ω) (removedRows : Finset R) (removedLabels : Finset (Fin g))
    (k : ℕ) (Q Z E : ℝ) (hQ0 : 0 ≤ Q) (hQ1 : Q ≤ 1)
    (hZ0 : 0 ≤ Z) (hZ1 : Z ≤ 1) (hE : 0 ≤ E)
    (hrowErr : ∀ a, |endpointMass r ξ removedRows removedLabels k (.inl a) - Q| ≤ E)
    (hlabelErr : ∀ y, |endpointMass r ξ removedRows removedLabels k (.inr y) - θ * Z| ≤ E) :
    ∀ u : Endpoint R g, |fullDrift r ξ removedRows removedLabels k u - θ * Z * Q| ≤ 2 * E := by
  classical
  have hθZ0 : 0 ≤ θ * Z := mul_nonneg hθ0 hZ0
  have hθZ1 : θ * Z ≤ 1 := mul_le_one₀ hθ1 hZ0 hZ1
  intro u
  rcases u with a | y
  · rw [fullDrift_row]
    apply weighted_drift_error
      (fun y => if y ∉ removedLabels ∧ ¬ labelUsed (keyMatching ξ removedRows removedLabels k) y
        then r a y else 0)
      (fun y => labelMass r (keyMatching ξ removedRows removedLabels k) removedRows y)
      (rowMass r (keyMatching ξ removedRows removedLabels k) removedLabels a)
      Q (θ * Z) E
    · intro y; split_ifs <;> simp [hr a y]
    · rfl
    · calc
        _ ≤ ∑ y, r a y := by
          apply Finset.sum_le_sum
          intro y _
          split_ifs <;> simp [hr a y]
        _ = 1 := hrow a
    · simpa [abs_of_nonneg hθZ0] using hθZ1
    · exact hE
    · exact hlabelErr
    · exact hrowErr a
  · have hm1 : labelMass r (keyMatching ξ removedRows removedLabels k) removedRows y ≤ 1 := by
      calc
        _ ≤ ∑ a, r a y := by
          apply Finset.sum_le_sum
          intro a _
          split_ifs <;> simp [hr a y]
        _ = θ := hcol y
        _ ≤ 1 := hθ1
    have h := weighted_drift_error
      (fun a => if a ∉ removedRows ∧ (keyMatching ξ removedRows removedLabels k).assignment a = none
        then r a y else 0)
      (fun a => rowMass r (keyMatching ξ removedRows removedLabels k) removedLabels a)
      (labelMass r (keyMatching ξ removedRows removedLabels k) removedRows y)
      (θ * Z) Q E
      (by intro a; split_ifs <;> simp [hr a y]) rfl hm1
      (by simpa [abs_of_nonneg hQ0] using hQ1) hE hrowErr (hlabelErr y)
    rw [fullDrift_label]
    simpa only [mul_assoc, mul_left_comm, mul_comm] using h

theorem removed_mass_bound {ι : Type*} [Fintype ι] [DecidableEq ι]
    (w : ι → ℝ) (s : Finset ι) (atom : ℝ) (hw0 : ∀ i, 0 ≤ w i)
    (hwAtom : ∀ i, w i ≤ atom) :
    |(∑ i, if i ∉ s then w i else 0) - ∑ i, w i| ≤ (s.card : ℝ) * atom := by
  classical
  have hsplit : (∑ i, if i ∉ s then w i else 0) + (∑ i ∈ s, w i) = ∑ i, w i := by
    have hmem : (∑ i ∈ s, w i) = ∑ i, if i ∈ s then w i else 0 := by simp
    rw [hmem, ← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro i _
    by_cases hi : i ∈ s <;> simp [hi]
  have h0 : 0 ≤ ∑ i ∈ s, w i := Finset.sum_nonneg fun i _ => hw0 i
  have heq : (∑ i, if i ∉ s then w i else 0) - ∑ i, w i = -(∑ i ∈ s, w i) := by linarith
  rw [heq, abs_neg, abs_of_nonneg h0]
  calc
    _ ≤ ∑ i ∈ s, atom := Finset.sum_le_sum fun i _ => hwAtom i
    _ = _ := by simp

theorem keyMatching_zero {T : ℕ} {R : Type*} [Fintype R] [DecidableEq R]
    {g : ℕ} {Ω : R → Type*} [∀ a, Fintype (Ω a)] [∀ a, DecidableEq (Ω a)]
    (ξ : ClockField T R g Ω) (removedRows : Finset R) (removedLabels : Finset (Fin g)) :
    keyMatching ξ removedRows removedLabels 0 = emptyGreedyState := by
  simp [keyMatching, keyEvents, runGreedy]

theorem endpointMass_initial_error {T : ℕ} {R : Type*} [Fintype R] [DecidableEq R]
    {g : ℕ} {Ω : R → Type*} [∀ a, Fintype (Ω a)] [∀ a, DecidableEq (Ω a)]
    (r : R → Fin g → ℝ) (hr : ∀ a y, 0 ≤ r a y)
    (atom : ℝ) (hAtom : 0 ≤ atom) (hrAtom : ∀ a y, r a y ≤ atom)
    (θ : ℝ) (hrow : ∀ a, ∑ y, r a y = 1) (hcol : ∀ y, ∑ a, r a y = θ)
    (ξ : ClockField T R g Ω) (removedRows : Finset R) (removedLabels : Finset (Fin g)) :
    ∀ u : Endpoint R g,
      |endpointMass r ξ removedRows removedLabels 0 u -
        (match u with | .inl _ => 1 | .inr _ => θ)| ≤
        ((removedRows.card + removedLabels.card : ℕ) : ℝ) * atom := by
  classical
  intro u
  rcases u with a | y
  · have h := removed_mass_bound (r a) removedLabels atom (hr a) (hrAtom a)
    simp only [hrow] at h
    have hm : endpointMass r ξ removedRows removedLabels 0 (.inl a) =
        ∑ y, if y ∉ removedLabels then r a y else 0 := by
      simp [endpointMass, rowMass, keyMatching_zero, labelUsed, emptyGreedyState]
    rw [hm]
    have hc : (removedLabels.card : ℝ) ≤ ((removedRows.card + removedLabels.card : ℕ) : ℝ) := by
      norm_cast; omega
    exact h.trans (mul_le_mul_of_nonneg_right hc hAtom)

  · have h := removed_mass_bound (fun a => r a y) removedRows atom (fun a => hr a y) (fun a => hrAtom a y)
    simp only [hcol] at h
    have hm : endpointMass r ξ removedRows removedLabels 0 (.inr y) =
        ∑ a, if a ∉ removedRows then r a y else 0 := by
      simp [endpointMass, labelMass, keyMatching_zero, emptyGreedyState]
    rw [hm]
    have hc : (removedRows.card : ℝ) ≤ ((removedRows.card + removedLabels.card : ℕ) : ℝ) := by
      norm_cast; omega
    exact h.trans (mul_le_mul_of_nonneg_right hc hAtom)


theorem eventPriority_horizon {T : ℕ} {R : Type*} [Fintype R] [DecidableEq R]
    {g : ℕ} {Ω : R → Type*} (e : ClockCandidate T R g Ω) (t : ℕ) :
    eventPriority e < t * (Fintype.card R * g) ↔ e.2.2.1.val < t := by
  have hb := edgeKey_bounds (e.1, e.2.1) e.2.2.1.val
  have hkey : eventPriority e = edgeKey (e.1, e.2.1) e.2.2.1.val := by
    simp [eventPriority, edgeKey, edgeRank, Nat.add_assoc]
  rw [hkey]
  constructor
  · intro h
    by_contra ht
    have hmul := Nat.mul_le_mul_right (Fintype.card R * g) (Nat.le_of_not_gt ht)
    omega
  · intro ht
    exact lt_of_lt_of_le hb.2 (Nat.mul_le_mul_right _ (Nat.succ_le_of_lt ht))

theorem euler_unit_square (q z : ℕ → ℝ) (δ θ : ℝ)
    (hδ0 : 0 ≤ δ) (hδ1 : δ ≤ 1) (hθ0 : 0 ≤ θ) (hθ1 : θ ≤ 1)
    (hq0 : q 0 = 1) (hz0 : z 0 = 1)
    (hqstep : ∀ k, q (k + 1) = q k - δ * θ * z k * q k)
    (hzstep : ∀ k, z (k + 1) = z k - δ * q k * z k) :
    ∀ k, 0 ≤ q k ∧ q k ≤ 1 ∧ 0 ≤ z k ∧ z k ≤ 1 := by
  intro k
  induction k with
  | zero => simp [hq0, hz0]
  | succ k ih =>
      rcases ih with ⟨hqlo, hqhi, hzlo, hzhi⟩
      have hdθ0 : 0 ≤ δ * θ := mul_nonneg hδ0 hθ0
      have hdθ1 : δ * θ ≤ 1 := mul_le_one₀ hδ1 hθ0 hθ1
      have hdθz0 : 0 ≤ δ * θ * z k := mul_nonneg hdθ0 hzlo
      have hdθz1 : δ * θ * z k ≤ 1 := mul_le_one₀ hdθ1 hzlo hzhi
      have hdq0 : 0 ≤ δ * q k := mul_nonneg hδ0 hqlo
      have hdq1 : δ * q k ≤ 1 := mul_le_one₀ hδ1 hqlo hqhi
      have hqnext : q (k + 1) = q k * (1 - δ * θ * z k) := by rw [hqstep]; ring
      have hznext : z (k + 1) = z k * (1 - δ * q k) := by rw [hzstep]; ring
      rw [hqnext, hznext]
      refine ⟨mul_nonneg hqlo (by linarith), ?_, mul_nonneg hzlo (by linarith), ?_⟩
      · exact (mul_le_mul_of_nonneg_left (by linarith : 1 - δ * θ * z k ≤ 1) hqlo).trans
          (by simpa using hqhi)
      · exact (mul_le_mul_of_nonneg_left (by linarith : 1 - δ * q k ≤ 1) hzlo).trans
          (by simpa using hzhi)

theorem bounded_product_change (q z q' z' θ δ : ℝ)
    (hq0 : 0 ≤ q) (hq1 : q ≤ 1) (hz'0 : 0 ≤ z') (hz'1 : z' ≤ 1)
    (hθ0 : 0 ≤ θ) (hθ1 : θ ≤ 1) (hδ : 0 ≤ δ)
    (hq : |q' - q| ≤ δ) (hz : |z' - z| ≤ δ) :
    |θ * z' * q' - θ * z * q| ≤ 2 * δ := by
  have hid : θ * z' * q' - θ * z * q = θ * ((q' - q) * z' + q * (z' - z)) := by ring
  rw [hid, abs_mul, abs_of_nonneg hθ0]
  have hinner : |(q' - q) * z' + q * (z' - z)| ≤ 2 * δ := by
    calc
      _ ≤ |(q' - q) * z'| + |q * (z' - z)| := abs_add_le _ _
      _ = |q' - q| * z' + q * |z' - z| := by
        rw [abs_mul, abs_mul, abs_of_nonneg hq0, abs_of_nonneg hz'0]
      _ ≤ δ * z' + q * δ := add_le_add
        (mul_le_mul_of_nonneg_right hq hz'0) (mul_le_mul_of_nonneg_left hz hq0)
      _ ≤ 2 * δ := by
        have h1 := mul_le_mul_of_nonneg_left hz'1 hδ
        have h2 := mul_le_mul_of_nonneg_right hq1 hδ
        nlinarith
  exact (mul_le_mul_of_nonneg_left hinner hθ0).trans
    (by simpa using mul_le_mul_of_nonneg_right hθ1 (mul_nonneg (by norm_num) hδ))

theorem euler_tracking_bound {T : ℕ} {R : Type*} [Fintype R] [DecidableEq R]
    {g : ℕ} {Ω : R → Type*} [∀ a, Fintype (Ω a)] [∀ a, DecidableEq (Ω a)]
    (r : R → Fin g → ℝ) (hr : ∀ a y, 0 ≤ r a y)
    (atom : ℝ) (hAtom : 0 ≤ atom) (hrAtom : ∀ a y, r a y ≤ atom)
    (δ θ : ℝ) (hδ : 0 ≤ δ) (hδsmall : δ ≤ 1 / 6) (hθ0 : 0 ≤ θ) (hθ1 : θ ≤ 1)
    (hrow : ∀ a, ∑ y, r a y = 1) (hcol : ∀ y, ∑ a, r a y = θ)
    (q z : ℕ → ℝ) (hq0 : q 0 = 1) (hz0 : z 0 = 1)
    (hqstep : ∀ k, q (k + 1) = q k - δ * θ * z k * q k)
    (hzstep : ∀ k, z (k + 1) = z k - δ * q k * z k)
    (ins : ∀ e : RowLabel R g, Option (MeshClockValue T (Ω e.1)))
    (ξ : ClockField T R g Ω) (removedRows : Finset R) (removedLabels : Finset (Fin g))
    (ε : ℝ) (hε : 0 ≤ ε)
    (hnoise : ∀ (t : Fin (T + 1)) u,
      |massNoise δ (fun e => r e.1 e.2) ins removedRows removedLabels (endpointWeight r u) t ξ| ≤ ε) :
    ∀ t : Fin (T + 1), ∀ u : Endpoint R g,
      |endpointMass r (prescribedField ins ξ) removedRows removedLabels
          (t.val * (Fintype.card R * g)) u -
        (match u with | .inl _ => q t.val | .inr _ => θ * z t.val)| ≤
        2 * (((removedRows.card + removedLabels.card : ℕ) : ℝ) * atom + ε +
          (prescribedCount ins : ℝ) * atom +
          (T : ℝ) * δ * ((prescribedCount ins : ℝ) * atom ^ 2 + 2 * δ)) *
          Real.exp (3 * δ * (T : ℝ)) := by
  classical
  let target : ℕ → Endpoint R g → ℝ := fun k u =>
    match u with | .inl _ => q k | .inr _ => θ * z k
  let d := fun k => θ * z k * q k
  have hbounds := euler_unit_square q z δ θ hδ (by linarith) hθ0 hθ1 hq0 hz0 hqstep hzstep
  have htstep : ∀ k < T, ∀ u, target (k + 1) u = target k u - δ * d k := by
    intro k _ u
    rcases u with a | y
    · dsimp [target, d]; rw [hqstep]; ring
    · dsimp [target, d]; rw [hzstep]; ring
  have hdstep : ∀ k < T, |d (k + 1) - d k| ≤ 2 * δ := by
    intro k _
    have hb := hbounds k
    have hb' := hbounds (k + 1)
    have hzq0 : 0 ≤ θ * z k * q k := mul_nonneg (mul_nonneg hθ0 hb.2.2.1) hb.1
    have hzq1 : θ * z k * q k ≤ 1 :=
      mul_le_one₀ (mul_le_one₀ hθ1 hb.2.2.1 hb.2.2.2) hb.1 hb.2.1
    have hqz0 : 0 ≤ q k * z k := mul_nonneg hb.1 hb.2.2.1
    have hqz1 : q k * z k ≤ 1 := mul_le_one₀ hb.2.1 hb.2.2.1 hb.2.2.2
    have hqdiff : q (k + 1) - q k = -(δ * (θ * z k * q k)) := by rw [hqstep]; ring
    have hzdiff : z (k + 1) - z k = -(δ * (q k * z k)) := by rw [hzstep]; ring
    have hq : |q (k + 1) - q k| ≤ δ := by
      rw [hqdiff, abs_neg, abs_of_nonneg (mul_nonneg hδ hzq0)]
      simpa using mul_le_mul_of_nonneg_left hzq1 hδ
    have hz : |z (k + 1) - z k| ≤ δ := by
      rw [hzdiff, abs_neg, abs_of_nonneg (mul_nonneg hδ hqz0)]
      simpa using mul_le_mul_of_nonneg_left hqz1 hδ
    exact bounded_product_change (q k) (z k) (q (k + 1)) (z (k + 1)) θ δ
      hb.1 hb.2.1 hb'.2.2.1 hb'.2.2.2 hθ0 hθ1 hδ hq hz
  have hinit : ∀ u, |endpointMass r (prescribedField ins ξ) removedRows removedLabels 0 u - target 0 u| ≤
      ((removedRows.card + removedLabels.card : ℕ) : ℝ) * atom := by
    simpa [target, hq0, hz0] using endpointMass_initial_error r hr atom hAtom hrAtom θ hrow hcol
      (prescribedField ins ξ) removedRows removedLabels
  have happrox : ∀ k ≤ T, ∀ u,
      |fullDrift r (prescribedField ins ξ) removedRows removedLabels (k * (Fintype.card R * g)) u - d k| ≤
        2 * trackingError r (prescribedField ins ξ) removedRows removedLabels target k := by
    intro k hk u
    have hb := hbounds k
    apply fullDrift_error r hr θ hθ0 hθ1 hrow hcol (prescribedField ins ξ) removedRows removedLabels
      (k * (Fintype.card R * g)) (q k) (z k)
      (trackingError r (prescribedField ins ξ) removedRows removedLabels target k)
      hb.1 hb.2.1 hb.2.2.1 hb.2.2.2 (trackingError_nonneg _ _ _ _ _ _) ?_ ?_ u
    · intro a
      exact trackingError_ge r (prescribedField ins ξ) removedRows removedLabels target
        ⟨k, Nat.lt_succ_of_le hk⟩ (.inl a) (le_refl k)
    · intro y
      exact trackingError_ge r (prescribedField ins ξ) removedRows removedLabels target
        ⟨k, Nat.lt_succ_of_le hk⟩ (.inr y) (le_refl k)
  exact finite_tracking_bound r hr atom hAtom hrAtom δ hδ hδsmall ins ξ removedRows removedLabels
    target d (((removedRows.card + removedLabels.card : ℕ) : ℝ) * atom) ε
    (by positivity) hε htstep hdstep hinit happrox hnoise

end HypercubeRamsey.Lane_sol_clock_s6
