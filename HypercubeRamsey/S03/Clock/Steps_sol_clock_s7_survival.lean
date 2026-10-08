import HypercubeRamsey.S03.Clock.Steps_sol_clock_s7

set_option autoImplicit false

namespace HypercubeRamsey.Lane_sol_clock_s7

open Clock
open Classical

/-- A finite downward-closed set of mesh indices is the initial segment of its cardinality. -/
theorem nat_initial_segment (s : Finset ℕ)
    (hdown : ∀ i j, i ≤ j → j ∈ s → i ∈ s) :
    ∀ i, i ∈ s ↔ i < s.card := by
  intro i
  constructor
  · intro hi
    have hsub : Finset.range (i + 1) ⊆ s := by
      intro j hj
      exact hdown j i (by simpa using Finset.mem_range.mp hj) hi
    have hcard := Finset.card_le_card hsub
    rw [Finset.card_range] at hcard
    omega
  · intro hi
    by_contra hmem
    have hsub : s ⊆ Finset.range i := by
      intro j hj
      apply Finset.mem_range.mpr
      by_contra hji
      exact hmem (hdown i j (Nat.le_of_not_gt hji) hj)
    have hcard := Finset.card_le_card hsub
    rw [Finset.card_range] at hcard
    omega

theorem fin_initial_segment {T : ℕ} (H : Fin T → Prop)
    (hdown : ∀ i j, i.val ≤ j.val → H j → H i) :
    ∀ i, H i ↔ i.val < (Finset.univ.filter H).card := by
  classical
  let s := Finset.univ.filter H
  let sNat := s.image Fin.val
  have hcard : sNat.card = s.card := Finset.card_image_iff.mpr (by
    intro i _ j _ hij
    exact Fin.ext hij)
  have hNatDown : ∀ i j, i ≤ j → j ∈ sNat → i ∈ sNat := by
    intro i j hij hj
    obtain ⟨t, ht, hval⟩ := Finset.mem_image.mp hj
    have hiT : i < T := lt_of_le_of_lt (hij.trans_eq hval.symm) t.isLt
    let u : Fin T := ⟨i, hiT⟩
    have hu : H u := hdown u t (by simpa [u, hval] using hij) (Finset.mem_filter.mp ht).2
    exact Finset.mem_image.mpr ⟨u, by simp [s, hu], rfl⟩
  intro i
  have hmem : i.val ∈ sNat ↔ H i := by
    constructor
    · intro h
      obtain ⟨j, hj, hji⟩ := Finset.mem_image.mp h
      have hji' : j = i := Fin.ext hji
      simpa [hji'] using (Finset.mem_filter.mp hj).2
    · intro h
      exact Finset.mem_image.mpr ⟨i, by simp [s, h], rfl⟩
  rw [← hmem, nat_initial_segment sNat hNatDown, hcard]

/-- Avoiding first arrivals while an outside endpoint is free is exactly a survival event. -/
theorem downward_closed_survival_probability {T : ℕ} {α : Type*}
    [Fintype α] [DecidableEq α] {g : ℕ}
    (δ : ℝ) (hδ : 0 ≤ δ) (hδ1 : δ ≤ 1)
    (p : FinProb α) (lab : α → Fin g) (y : Fin g)
    (H : Fin T → Prop) (hdown : ∀ i j, i.val ≤ j.val → H j → H i) :
    (edgeLaw (T := T) (R := Unit) (Ω := fun _ => α)
      δ hδ hδ1 (fun _ => p) (fun _ => lab) ((), y)).pr
      (fun x => match x with
        | .noArrival => True
        | .tick t _ => ¬ H t) =
      survival δ (labMarg p lab y) (Finset.univ.filter H).card := by
  classical
  have hcard : (Finset.univ.filter H).card ≤ T := by
    simpa using Finset.card_le_card (Finset.filter_subset (p := H) Finset.univ)
  have hevent : (fun x : MeshClockValue T α => match x with
        | .noArrival => True
        | .tick t _ => ¬ H t) = NoEarlyArrival (Finset.univ.filter H).card := by
    funext x
    apply propext
    cases x with
    | noArrival => simp [NoEarlyArrival]
    | tick t mark => simp [NoEarlyArrival, fin_initial_segment H hdown t, Nat.not_lt]
  rw [hevent]
  exact noEarlyArrival_probability δ hδ hδ1 p lab y _ hcard

/-- For time-ordered events, the smaller horizon is a prefix of the larger one. -/
theorem filter_time_split {α : Type*} (time : α → ℕ) (events : List α)
    (hsort : events.Pairwise (fun a b => time a ≤ time b))
    (n m : ℕ) (hnm : n ≤ m) :
    events.filter (fun a => time a < m) =
      events.filter (fun a => time a < n) ++
        events.filter (fun a => n ≤ time a ∧ time a < m) := by
  classical
  induction events with
  | nil => simp
  | cons a events ih =>
    obtain ⟨hhead, htail⟩ := List.pairwise_cons.mp hsort
    have ht := ih htail
    by_cases han : time a < n
    · have ham : time a < m := lt_of_lt_of_le han hnm
      simp [han, ham, Nat.not_le.mpr han, ht]
    · by_cases ham : time a < m
      · have hnil : events.filter (fun b => time b < n) = [] := by
          apply List.filter_eq_nil_iff.mpr
          intro b hb
          simp only [decide_eq_true_eq]
          exact not_lt.mpr ((Nat.le_of_not_lt han).trans (hhead b hb))
        simp [han, ham, Nat.le_of_not_lt han, ht, hnil]
      · simp [han, ham, ht]

/-- The matching restricted to a fixed set of edges, up to a mesh horizon. -/
noncomputable def edgeMatchingThrough {T : ℕ} {R : Type*}
    [Fintype R] [DecidableEq R] {g : ℕ} {Ω : R → Type*}
    [∀ a, Fintype (Ω a)] [∀ a, DecidableEq (Ω a)]
    (ξ : ClockField T R g Ω) (D : Finset (RowLabel R g)) (h : ℕ) : GreedyState R g Ω :=
  runGreedy ξ (((clockEventList ξ).filter (fun e => (e.1, e.2.1) ∈ D)).filter
    (fun e => e.2.2.1.val < h))

theorem edgeMatchingThrough_label_free {T : ℕ} {R : Type*}
    [Fintype R] [DecidableEq R] {g : ℕ} {Ω : R → Type*}
    [∀ a, Fintype (Ω a)] [∀ a, DecidableEq (Ω a)]
    (ξ : ClockField T R g Ω) (D : Finset (RowLabel R g)) (n m : ℕ) (hnm : n ≤ m)
    (y : Fin g) (hfree : ¬ labelUsed (edgeMatchingThrough ξ D m) y) :
    ¬ labelUsed (edgeMatchingThrough ξ D n) y := by
  classical
  let events := (clockEventList ξ).filter (fun e => (e.1, e.2.1) ∈ D)
  have hsort : events.Pairwise (fun e f => e.2.2.1.val ≤ f.2.2.1.val) := by
    apply List.Pairwise.imp (fun {e f} h => tick_le_of_priority_le e f h)
    exact (clockEventList_sorted ξ).filter _
  have hsplit := filter_time_split (fun e : ClockCandidate T R g Ω => e.2.2.1.val)
    events hsort n m hnm
  rintro ⟨a, o, ha⟩
  apply hfree
  refine ⟨a, o, ?_⟩
  have hpres := runGreedy_preserves_existing_assignment ξ
    (events.filter (fun e => n ≤ e.2.2.1.val ∧ e.2.2.1.val < m))
    (edgeMatchingThrough ξ D n) a (y, o) ha
  simpa [edgeMatchingThrough, runGreedy, hsplit, List.foldl_append, events] using hpres

theorem edgeMatchingThrough_row_free {T : ℕ} {R : Type*}
    [Fintype R] [DecidableEq R] {g : ℕ} {Ω : R → Type*}
    [∀ a, Fintype (Ω a)] [∀ a, DecidableEq (Ω a)]
    (ξ : ClockField T R g Ω) (D : Finset (RowLabel R g)) (n m : ℕ) (hnm : n ≤ m)
    (a : R) (hfree : (edgeMatchingThrough ξ D m).assignment a = none) :
    (edgeMatchingThrough ξ D n).assignment a = none := by
  classical
  let events := (clockEventList ξ).filter (fun e => (e.1, e.2.1) ∈ D)
  have hsort : events.Pairwise (fun e f => e.2.2.1.val ≤ f.2.2.1.val) := by
    apply List.Pairwise.imp (fun {e f} h => tick_le_of_priority_le e f h)
    exact (clockEventList_sorted ξ).filter _
  have hsplit := filter_time_split (fun e : ClockCandidate T R g Ω => e.2.2.1.val)
    events hsort n m hnm
  by_contra ha
  have hpres := runGreedy_preserves_assignment ξ
    (events.filter (fun e => n ≤ e.2.2.1.val ∧ e.2.2.1.val < m))
    (edgeMatchingThrough ξ D n) a ha
  apply hpres
  simpa [edgeMatchingThrough, runGreedy, hsplit, List.foldl_append, events] using hfree

end HypercubeRamsey.Lane_sol_clock_s7
