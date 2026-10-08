import HypercubeRamsey.S03.Clock.Steps_p_clock_r4

set_option autoImplicit false

namespace HypercubeRamsey.Lane_sol_clock_s7

open Clock
open scoped BigOperators

/-- The edge law expressed using the model layer, for helpers imported before Step 7. -/
noncomputable def edgeLaw {T : ℕ} {R : Type*} {g : ℕ} {Ω : R → Type*}
    [∀ a, Fintype (Ω a)] [∀ a, DecidableEq (Ω a)]
    (δ : ℝ) (hδ : 0 ≤ δ) (hδ1 : δ ≤ 1)
    (p : ∀ a, FinProb (Ω a)) (lab : ∀ a, Ω a → Fin g) :
    ∀ e : RowLabel R g, FinProb (MeshClockValue T (Ω e.1)) := by
  classical
  exact fun e => outputEdgeClockLaw δ hδ (p e.1) (lab e.1) e.2 (by
    have hmul : δ * labMarg (p e.1) (lab e.1) e.2 ≤ δ := by
      simpa using mul_le_mul_of_nonneg_left (labMarg_le_one (p e.1) (lab e.1) e.2) hδ
    exact sub_nonneg.mpr (hmul.trans hδ1))

/-- Events on disjoint sets of edge coordinates are independent. -/
theorem pi_pr_inter_of_disjoint {ι : Type*} [Fintype ι] [DecidableEq ι]
    {α : ι → Type*} [∀ i, Fintype (α i)]
    (P : ∀ i, FinProb (α i)) (E F : (∀ i, α i) → Prop) (s t : Finset ι)
    (hE : FinProb.DependsOn E s) (hF : FinProb.DependsOn F t) (hst : Disjoint s t) :
    (FinProb.pi P).pr (fun x => E x ∧ F x) =
      (FinProb.pi P).pr E * (FinProb.pi P).pr F := by
  classical
  let e : (∀ i, α i) → ℝ := fun x => if E x then 1 else 0
  let f : (∀ i, α i) → ℝ := fun x => if F x then 1 else 0
  have he : FinProb.DependsOn e s := by
    intro x x' h
    simp only [e, hE x x' h]
  have hf : FinProb.DependsOn f t := by
    intro x x' h
    simp only [f, hF x x' h]
  have h := FinProb.pi_expect_mul_of_disjoint P e f s t he hf hst
  calc
    _ = (FinProb.pi P).expect (fun x => e x * f x) := by
      unfold FinProb.pr FinProb.expect
      apply Finset.sum_congr rfl
      intro x _
      by_cases hEx : E x <;> by_cases hFx : F x <;> simp [e, f, hEx, hFx]
    _ = (FinProb.pi P).expect e * (FinProb.pi P).expect f := h
    _ = _ := by simp only [FinProb.expect, FinProb.pr, e, f, mul_ite, mul_one, mul_zero]

/-- A prescribed zero-mass mark cannot be an ordinary accepted arrival. -/
theorem clock_weight_zero_of_zero_mark {T : ℕ} {R : Type*}
    [Fintype R] [DecidableEq R] {g : ℕ} {Ω : R → Type*}
    [∀ a, Fintype (Ω a)] [∀ a, DecidableEq (Ω a)]
    (δ : ℝ) (hδ : 0 ≤ δ) (hδ1 : δ ≤ 1)
    (p : ∀ a, FinProb (Ω a)) (lab : ∀ a, Ω a → Fin g)
    (ξ : ClockField T R g Ω) (a : R) (y : Fin g) (t : Fin T) (o : Ω a)
    (harrival : ξ (a, y) = .tick t o) (hzero : (p a).w o = 0) :
    (clockFieldLaw (edgeLaw δ hδ hδ1 p lab)).w ξ = 0 := by
  classical
  change (∏ e : RowLabel R g, (edgeLaw δ hδ hδ1 p lab e).w (ξ e)) = 0
  apply Finset.prod_eq_zero (Finset.mem_univ (a, y))
  rw [harrival]
  simp [edgeLaw, outputEdgeClockLaw, markedClockLaw,
    markedClockWeight, outputMarkMass, hzero]

/-- The same support calculation identifies the label of every positive-weight ordinary arrival. -/
theorem arrival_label_of_weight_ne_zero {T : ℕ} {R : Type*}
    [Fintype R] [DecidableEq R] {g : ℕ} {Ω : R → Type*}
    [∀ a, Fintype (Ω a)] [∀ a, DecidableEq (Ω a)]
    (δ : ℝ) (hδ : 0 ≤ δ) (hδ1 : δ ≤ 1)
    (p : ∀ a, FinProb (Ω a)) (lab : ∀ a, Ω a → Fin g)
    (ξ : ClockField T R g Ω) (a : R) (y : Fin g) (t : Fin T) (o : Ω a)
    (harrival : ξ (a, y) = .tick t o)
    (hweight : (clockFieldLaw (edgeLaw δ hδ hδ1 p lab)).w ξ ≠ 0) :
    lab a o = y := by
  classical
  by_contra hlabel
  apply hweight
  change (∏ e : RowLabel R g, (edgeLaw δ hδ hδ1 p lab e).w (ξ e)) = 0
  apply Finset.prod_eq_zero (Finset.mem_univ (a, y))
  rw [harrival]
  simp [edgeLaw, outputEdgeClockLaw, markedClockLaw,
    markedClockWeight, outputMarkMass, hlabel]

/-- Joint prescribed arrival weights factor before imposing any matching or background condition. -/
theorem joint_target_arrival_probability {T : ℕ} {R : Type*}
    [Fintype R] [DecidableEq R] {g : ℕ} {Ω : R → Type*}
    [∀ a, Fintype (Ω a)] [∀ a, DecidableEq (Ω a)]
    (δ : ℝ) (hδ : 0 ≤ δ) (hδ1 : δ ≤ 1)
    (p : ∀ a, FinProb (Ω a)) (lab : ∀ a, Ω a → Fin g)
    (S : Finset R) (o : ∀ a, Ω a) (times : R → Fin T) :
    (clockFieldLaw (edgeLaw δ hδ hδ1 p lab)).pr
        (fun ξ => ∀ a ∈ S, ξ (a, lab a (o a)) = .tick (times a) (o a)) =
      (∏ a ∈ S, (p a).w (o a)) *
        ∏ a ∈ S, survival δ (labMarg (p a) (lab a) (lab a (o a))) (times a).val * δ := by
  classical
  let required : RowLabel R g → Prop := fun e => e.1 ∈ S ∧ e.2 = lab e.1 (o e.1)
  let z : ClockField T R g Ω := fun e => .tick (times e.1) (o e.1)
  have hevent :
      (fun ξ : ClockField T R g Ω => ∀ a ∈ S,
        ξ (a, lab a (o a)) = .tick (times a) (o a)) =
        (fun ξ : ClockField T R g Ω => ∀ e, required e → ξ e = z e) := by
    funext ξ
    apply propext
    constructor
    · intro h e he
      rcases e with ⟨a, y⟩
      rcases he with ⟨ha, hy⟩
      change y = lab a (o a) at hy
      subst y
      exact h a ha
    · intro h a ha
      exact h (a, lab a (o a)) ⟨ha, rfl⟩
  rw [hevent]
  change (FinProb.pi (edgeLaw δ hδ hδ1 p lab)).pr _ = _
  rw [pi_pr_required_coordinate_eq]
  have hpoint (e : RowLabel R g) :
      (edgeLaw δ hδ hδ1 p lab e).pr (fun x => x = z e) =
        (edgeLaw δ hδ hδ1 p lab e).w (z e) := by
    unfold FinProb.pr
    rw [Fintype.sum_eq_single (z e)]
    · simp
    · intro x hx
      simp [hx]
  simp_rw [hpoint]
  rw [Fintype.prod_prod_type]
  have hrow (a : R) :
      (∏ y : Fin g, if required (a, y) then
          (edgeLaw δ hδ hδ1 p lab (a, y)).w (z (a, y)) else 1) =
        if a ∈ S then
          (p a).w (o a) *
            (survival δ (labMarg (p a) (lab a) (lab a (o a))) (times a).val * δ)
        else 1 := by
    by_cases ha : a ∈ S
    · simp [required, ha, z, edgeLaw, outputEdgeClockLaw, markedClockLaw,
        markedClockWeight, outputMarkMass, eq_comm, mul_assoc, mul_comm, mul_left_comm]
    · simp [required, ha]
  simp_rw [hrow]
  rw [← Finset.prod_filter]
  have hfilter : (Finset.univ.filter fun a : R => a ∈ S) = S := by ext a; simp
  rw [hfilter, Finset.prod_mul_distrib]

/-- A background exception on disjoint clocks retains the entire target product. -/
theorem joint_target_arrival_and_disjoint_probability {T : ℕ} {R : Type*}
    [Fintype R] [DecidableEq R] {g : ℕ} {Ω : R → Type*}
    [∀ a, Fintype (Ω a)] [∀ a, DecidableEq (Ω a)]
    (δ : ℝ) (hδ : 0 ≤ δ) (hδ1 : δ ≤ 1)
    (p : ∀ a, FinProb (Ω a)) (lab : ∀ a, Ω a → Fin g)
    (S : Finset R) (o : ∀ a, Ω a) (times : R → Fin T)
    (F : ClockField T R g Ω → Prop) (D : Finset (RowLabel R g))
    (hF : FinProb.DependsOn F D)
    (hD : Disjoint (S.image fun a => (a, lab a (o a))) D) :
    (clockFieldLaw (edgeLaw δ hδ hδ1 p lab)).pr
      (fun ξ => (∀ a ∈ S, ξ (a, lab a (o a)) = .tick (times a) (o a)) ∧ F ξ) =
      ((∏ a ∈ S, (p a).w (o a)) *
        ∏ a ∈ S, survival δ (labMarg (p a) (lab a) (lab a (o a))) (times a).val * δ) *
      (clockFieldLaw (edgeLaw δ hδ hδ1 p lab)).pr F := by
  classical
  have hE : FinProb.DependsOn
      (fun ξ : ClockField T R g Ω => ∀ a ∈ S,
        ξ (a, lab a (o a)) = .tick (times a) (o a))
      (S.image fun a => (a, lab a (o a))) := by
    intro ξ ξ' hξ
    apply propext
    constructor
    · intro h a ha
      rw [← hξ (a, lab a (o a)) (Finset.mem_image.mpr ⟨a, ha, rfl⟩)]
      exact h a ha
    · intro h a ha
      rw [hξ (a, lab a (o a)) (Finset.mem_image.mpr ⟨a, ha, rfl⟩)]
      exact h a ha
  rw [clockFieldLaw, pi_pr_inter_of_disjoint _ _ _ _ _ hE hF hD]
  rw [← clockFieldLaw, joint_target_arrival_probability]

/-- Remove the assignments of the queried rows from a partial matching. -/
def projectState {R : Type*} [DecidableEq R] {g : ℕ} {Ω : R → Type*}
    (S : Finset R) (s : GreedyState R g Ω) : GreedyState R g Ω :=
  ⟨fun a => if a ∈ S then none else s.assignment a⟩

/-- All accepted edges lie wholly inside or wholly outside the removed endpoints. -/
def Separated {R : Type*} {g : ℕ} {Ω : R → Type*}
    (S : Finset R) (L : Finset (Fin g)) (s : GreedyState R g Ω) : Prop :=
  ∀ a y o, s.assignment a = some (y, o) → (a ∈ S ↔ y ∈ L)

private theorem state_eq_of_assignment_eq {R : Type*} {g : ℕ} {Ω : R → Type*}
    {s s' : GreedyState R g Ω} (h : ∀ a, s.assignment a = s'.assignment a) : s = s' := by
  cases s with
  | mk f =>
    cases s' with
    | mk f' =>
      congr 1
      exact funext h

/-- Separation of the final matching also holds at every earlier state. -/
theorem separated_before_fold {T : ℕ} {R : Type*} [DecidableEq R]
    {g : ℕ} {Ω : R → Type*} [∀ a, DecidableEq (Ω a)]
    (ξ : ClockField T R g Ω) (events : List (ClockCandidate T R g Ω))
    (S : Finset R) (L : Finset (Fin g)) (s : GreedyState R g Ω)
    (hfinal : Separated S L (events.foldl (fun s e => processArrival ξ s e) s)) :
    Separated S L s := by
  intro a y o ha
  exact hfinal a y o (runGreedy_preserves_existing_assignment ξ events s a (y, o) ha)

theorem labelUsed_projectState {R : Type*} [DecidableEq R]
    {g : ℕ} {Ω : R → Type*} (S : Finset R) (L : Finset (Fin g))
    (s : GreedyState R g Ω) (hsep : Separated S L s)
    (y : Fin g) (hy : y ∉ L) :
    labelUsed (projectState S s) y ↔ labelUsed s y := by
  constructor
  · rintro ⟨a, o, ha⟩
    by_cases hS : a ∈ S
    · simp [projectState, hS] at ha
    · exact ⟨a, o, by simpa [projectState, hS] using ha⟩
  · rintro ⟨a, o, ha⟩
    have hS : a ∉ S := fun h => hy ((hsep a y o ha).mp h)
    exact ⟨a, o, by simpa [projectState, hS] using ha⟩

private theorem project_process_outside {T : ℕ} {R : Type*} [DecidableEq R]
    {g : ℕ} {Ω : R → Type*} [∀ a, DecidableEq (Ω a)]
    (ξ : ClockField T R g Ω) (S : Finset R) (L : Finset (Fin g))
    (s : GreedyState R g Ω) (e : ClockCandidate T R g Ω)
    (hsep : Separated S L s) (ha : e.1 ∉ S) (hy : e.2.1 ∉ L) :
    projectState S (processArrival ξ s e) = processArrival ξ (projectState S s) e := by
  classical
  have hrow : (projectState S s).assignment e.1 = s.assignment e.1 := by
    simp [projectState, ha]
  have hused := labelUsed_projectState S L s hsep e.2.1 hy
  have hacc :
      (candidateIsArrival ξ e ∧ s.assignment e.1 = none ∧ ¬ labelUsed s e.2.1) ↔
        (candidateIsArrival ξ e ∧ (projectState S s).assignment e.1 = none ∧
          ¬ labelUsed (projectState S s) e.2.1) := by
    rw [hrow, hused]
  by_cases h : candidateIsArrival ξ e ∧ s.assignment e.1 = none ∧ ¬ labelUsed s e.2.1
  · have h' := hacc.mp h
    simp only [processArrival, if_pos h, if_pos h']
    apply state_eq_of_assignment_eq
    intro a
    by_cases hea : e.1 = a
    · subst a
      simp [projectState, ha]
    · simp [projectState, hea]
  · have h' := mt hacc.mpr h
    simp [processArrival, h, h']

private theorem project_process_inside {T : ℕ} {R : Type*} [DecidableEq R]
    {g : ℕ} {Ω : R → Type*} [∀ a, DecidableEq (Ω a)]
    (ξ : ClockField T R g Ω) (S : Finset R) (s : GreedyState R g Ω)
    (e : ClockCandidate T R g Ω) (ha : e.1 ∈ S) :
    projectState S (processArrival ξ s e) = projectState S s := by
  classical
  apply state_eq_of_assignment_eq
  intro a
  by_cases hS : a ∈ S
  · simp [projectState, hS]
  · have hea : e.1 ≠ a := fun h => hS (h ▸ ha)
    by_cases h : candidateIsArrival ξ e ∧ s.assignment e.1 = none ∧ ¬ labelUsed s e.2.1
    · simp [projectState, hS, processArrival, h, hea]
    · simp [projectState, hS, processArrival, h]

private theorem process_cross_rejected {T : ℕ} {R : Type*} [DecidableEq R]
    {g : ℕ} {Ω : R → Type*} [∀ a, DecidableEq (Ω a)]
    (ξ : ClockField T R g Ω) (S : Finset R) (L : Finset (Fin g))
    (s : GreedyState R g Ω) (e : ClockCandidate T R g Ω)
    (hsep : Separated S L (processArrival ξ s e)) (ha : e.1 ∉ S) (hy : e.2.1 ∈ L) :
    processArrival ξ s e = s := by
  classical
  by_cases h : candidateIsArrival ξ e ∧ s.assignment e.1 = none ∧ ¬ labelUsed s e.2.1
  · have he : (processArrival ξ s e).assignment e.1 = some (e.2.1, e.2.2.2) := by
      simp [processArrival, h]
    exact False.elim (ha ((hsep e.1 e.2.1 e.2.2.2 he).mpr hy))
  · simp [processArrival, h]

/-- For a matching with sealed target endpoints, projection commutes with running the outside events. -/
theorem project_fold_eq_outside_fold {T : ℕ} {R : Type*} [DecidableEq R]
    {g : ℕ} {Ω : R → Type*} [∀ a, DecidableEq (Ω a)]
    (ξ : ClockField T R g Ω) (S : Finset R) (L : Finset (Fin g))
    (events : List (ClockCandidate T R g Ω)) (s : GreedyState R g Ω)
    (hfinal : Separated S L (events.foldl (fun s e => processArrival ξ s e) s)) :
    projectState S (events.foldl (fun s e => processArrival ξ s e) s) =
      (events.filter (fun e => e.1 ∉ S ∧ e.2.1 ∉ L)).foldl
        (fun s e => processArrival ξ s e) (projectState S s) := by
  classical
  induction events generalizing s with
  | nil => rfl
  | cons e events ih =>
    have htail : Separated S L
        (events.foldl (fun s e => processArrival ξ s e) (processArrival ξ s e)) := hfinal
    have hs := separated_before_fold ξ (e :: events) S L s hfinal
    have hs' := separated_before_fold ξ events S L (processArrival ξ s e) htail
    rw [List.foldl_cons, ih (processArrival ξ s e) htail]
    by_cases ha : e.1 ∈ S
    · rw [project_process_inside ξ S s e ha]
      simp [List.filter_cons, ha]
    · by_cases hy : e.2.1 ∈ L
      · rw [process_cross_rejected ξ S L s e hs' ha hy]
        simp [List.filter_cons, hy]
      · rw [project_process_outside ξ S L s e hs ha hy]
        simp [List.filter_cons, ha, hy]

theorem target_matching_separated {T : ℕ} {R : Type*}
    [Fintype R] [DecidableEq R] {g : ℕ} {Ω : R → Type*}
    [∀ a, Fintype (Ω a)] [∀ a, DecidableEq (Ω a)]
    (ξ : ClockField T R g Ω) (S : Finset R) (o : ∀ a, Ω a)
    (lab : ∀ a, Ω a → Fin g)
    (htarget : ∀ a ∈ S, (greedyMatching ξ).assignment a = some (lab a (o a), o a)) :
    Separated S (S.image fun a => lab a (o a)) (greedyMatching ξ) := by
  classical
  intro a y oa ha
  constructor
  · intro hS
    have hp := Option.some.inj (ha.symm.trans (htarget a hS))
    have hy : y = lab a (o a) := congrArg Prod.fst hp
    exact Finset.mem_image.mpr ⟨a, hS, hy.symm⟩
  · intro hL
    obtain ⟨b, hb, hy⟩ := Finset.mem_image.mp hL
    have hab : a = b := greedyMatching_label_injective ξ a b y oa (o b) ha (by
      simpa [hy] using htarget b hb)
    simpa [hab] using hb

private theorem process_assignment_source_event {T : ℕ} {R : Type*} [DecidableEq R]
    {g : ℕ} {Ω : R → Type*} [∀ a, DecidableEq (Ω a)]
    (ξ : ClockField T R g Ω) (s : GreedyState R g Ω)
    (e : ClockCandidate T R g Ω) (a : R) (y : Fin g) (o : Ω a)
    (h : (processArrival ξ s e).assignment a = some (y, o)) :
    s.assignment a = some (y, o) ∨
      ∃ t, e = ⟨a, y, t, o⟩ ∧ ξ (a, y) = .tick t o := by
  classical
  by_cases hacc : candidateIsArrival ξ e ∧ s.assignment e.1 = none ∧ ¬ labelUsed s e.2.1
  · by_cases hrow : e.1 = a
    · subst a
      simp only [processArrival, if_pos hacc, dif_pos rfl] at h
      have hpair : (e.2.1, e.2.2.2) = (y, o) := by simpa using h
      rcases Prod.mk.inj hpair with ⟨rfl, rfl⟩
      right
      refine ⟨e.2.2.1, ?_, ?_⟩
      · cases e; rfl
      · exact hacc.1
    · exact Or.inl (by simpa [processArrival, hacc, hrow] using h)
  · exact Or.inl (by simpa [processArrival, hacc] using h)

/-- An assigned mark either was present initially or came from an event actually processed. -/
theorem fold_assignment_source_event {T : ℕ} {R : Type*} [DecidableEq R]
    {g : ℕ} {Ω : R → Type*} [∀ a, DecidableEq (Ω a)]
    (ξ : ClockField T R g Ω) (events : List (ClockCandidate T R g Ω))
    (s : GreedyState R g Ω) (a : R) (y : Fin g) (o : Ω a)
    (h : (events.foldl (fun s e => processArrival ξ s e) s).assignment a = some (y, o)) :
    s.assignment a = some (y, o) ∨
      ∃ t, (⟨a, y, t, o⟩ : ClockCandidate T R g Ω) ∈ events ∧ ξ (a, y) = .tick t o := by
  induction events generalizing s with
  | nil => exact Or.inl h
  | cons e events ih =>
    obtain h' | ⟨t, ht, hξ⟩ := ih (processArrival ξ s e) h
    · obtain hs | ⟨t, he, hξ⟩ := process_assignment_source_event ξ s e a y o h'
      · exact Or.inl hs
      · exact Or.inr ⟨t, by simp [← he], hξ⟩
    · exact Or.inr ⟨t, by simp [ht], hξ⟩

/-- The endpoint ordering cannot place a later tick before an earlier tick. -/
theorem tick_le_of_priority_le {T : ℕ} {R : Type*} [Fintype R] [DecidableEq R]
    {g : ℕ} {Ω : R → Type*} (e f : ClockCandidate T R g Ω)
    (h : eventPriority e ≤ eventPriority f) : e.2.2.1.val ≤ f.2.2.1.val := by
  classical
  have hg : 0 < g := lt_of_le_of_lt (Nat.zero_le e.2.1.val) e.2.1.isLt
  let base : ℕ := Fintype.card R * g
  have hbase : 0 < base := Nat.mul_pos (Fintype.card_pos_iff.mpr ⟨e.1⟩) hg
  have hdiv (c : ClockCandidate T R g Ω) : eventPriority c / base = c.2.2.1.val := by
    let rank := ((Fintype.equivFin R) c.1).val
    have hrank : rank + 1 ≤ Fintype.card R :=
      Nat.succ_le_of_lt (Fintype.equivFin R c.1).isLt
    have hpart : rank * g + c.2.1.val < base := by
      calc
        rank * g + c.2.1.val < rank * g + g := Nat.add_lt_add_left c.2.1.isLt _
        _ = (rank + 1) * g := by simp [Nat.add_mul]
        _ ≤ base := Nat.mul_le_mul_right g hrank
    simp only [eventPriority, Nat.add_assoc]
    change (c.2.2.1.val * base + (rank * g + c.2.1.val)) / base = _
    rw [Nat.mul_comm c.2.2.1.val base, Nat.mul_add_div hbase, Nat.div_eq_of_lt hpart,
      Nat.add_zero]
  have h' := Nat.div_le_div_right (c := base) h
  rw [hdiv e, hdiv f] at h'
  exact h'

/-- No first arrival occurs strictly before the specified mesh index. -/
def NoEarlyArrival {T : ℕ} {α : Type*} (h : ℕ) : MeshClockValue T α → Prop
  | .noArrival => True
  | .tick t _ => h ≤ t.val

/-- The exact finite-mesh survival probability, including the no-arrival atom. -/
theorem noEarlyArrival_probability {T : ℕ} {α : Type*}
    [Fintype α] [DecidableEq α] {g : ℕ}
    (δ : ℝ) (hδ : 0 ≤ δ) (hδ1 : δ ≤ 1)
    (p : FinProb α) (lab : α → Fin g) (y : Fin g) (h : ℕ) (hh : h ≤ T) :
    (edgeLaw (T := T) (R := Unit) (Ω := fun _ => α) δ hδ hδ1 (fun _ => p) (fun _ => lab) ((), y)).pr
      (NoEarlyArrival h) = survival δ (labMarg p lab y) h := by
  classical
  have hbase : 0 ≤ 1 - δ * labMarg p lab y := by
    have hm := mul_le_mul_of_nonneg_left (labMarg_le_one p lab y) hδ
    nlinarith
  have hs := markedClockLaw_survival δ (labMarg p lab y) (outputMarkMass p lab y)
    hδ hbase (labMarg_nonneg p lab y)
    (fun o => by
      unfold outputMarkMass
      split_ifs
      · exact p.nonneg o
      · exact le_rfl)
    (outputMarkMass_sum p lab y) h hh
  calc
    _ = ∑ x : MeshClockValue T α,
        if x = .noArrival then
          (markedClockLaw δ (labMarg p lab y) (outputMarkMass p lab y)
            hδ hbase (labMarg_nonneg p lab y)
            (fun o => by
              unfold outputMarkMass
              split_ifs
              · exact p.nonneg o
              · exact le_rfl)
            (outputMarkMass_sum p lab y)).w x
        else match x with
          | .noArrival => 0
          | .tick t _ => if t.val < h then 0 else
            (markedClockLaw δ (labMarg p lab y) (outputMarkMass p lab y)
              hδ hbase (labMarg_nonneg p lab y)
              (fun o => by
                unfold outputMarkMass
                split_ifs
                · exact p.nonneg o
                · exact le_rfl)
              (outputMarkMass_sum p lab y)).w x := by
      unfold FinProb.pr
      apply Finset.sum_congr rfl
      intro x _
      cases x with
      | noArrival => simp [NoEarlyArrival, edgeLaw, outputEdgeClockLaw]
      | tick t o =>
        by_cases ht : t.val < h
        · simp [NoEarlyArrival, ht, Nat.not_le.mpr ht]
        · simp [NoEarlyArrival, ht, Nat.le_of_not_lt ht, edgeLaw, outputEdgeClockLaw]
    _ = _ := hs

/-- Cross-edge survival constraints are independent once their cutoffs are fixed. -/
theorem pi_noEarlyArrival_probability {T : ℕ} {R : Type*}
    [Fintype R] [DecidableEq R] {g : ℕ} {Ω : R → Type*}
    [∀ a, Fintype (Ω a)] [∀ a, DecidableEq (Ω a)]
    (δ : ℝ) (hδ : 0 ≤ δ) (hδ1 : δ ≤ 1)
    (p : ∀ a, FinProb (Ω a)) (lab : ∀ a, Ω a → Fin g)
    (cutoff : RowLabel R g → ℕ) (hcut : ∀ e, cutoff e ≤ T) :
    (clockFieldLaw (edgeLaw (T := T) δ hδ hδ1 p lab)).pr
      (fun ξ => ∀ e, NoEarlyArrival (cutoff e) (ξ e)) =
        ∏ e : RowLabel R g, survival δ (labMarg (p e.1) (lab e.1) e.2) (cutoff e) := by
  classical
  rw [clockFieldLaw, pi_pr_forall_coordinates]
  apply Finset.prod_congr rfl
  intro e _
  exact noEarlyArrival_probability δ hδ hδ1 (p e.1) (lab e.1) e.2 (cutoff e) (hcut e)

private theorem clockEventList_strict {T : ℕ} {R : Type*}
    [Fintype R] [DecidableEq R] {g : ℕ} {Ω : R → Type*}
    [∀ a, Fintype (Ω a)] [∀ a, DecidableEq (Ω a)]
    (ξ : ClockField T R g Ω) :
    (clockEventList ξ).Pairwise (fun e f => eventPriority e < eventPriority f) := by
  classical
  have hstrict (events : List (ClockCandidate T R g Ω))
      (hsort : events.Pairwise (fun e f => eventPriority e ≤ eventPriority f))
      (hnd : events.Nodup) (harr : ∀ e ∈ events, candidateIsArrival ξ e) :
      events.Pairwise (fun e f => eventPriority e < eventPriority f) := by
    induction events with
    | nil => simp
    | cons e events ih =>
      simp only [List.pairwise_cons, List.nodup_cons] at hsort hnd ⊢
      refine ⟨?_, ih hsort.2 hnd.2 ?_⟩
      · intro f hf
        have hne : eventPriority e ≠ eventPriority f := by
          intro hkey
          have heq := clockCandidate_eq_of_priority_eq ξ e f
            (harr e (by simp)) (harr f (by simp [hf])) hkey
          exact hnd.1 (by simpa [heq])
        exact lt_of_le_of_ne (hsort.1 f hf) hne
      · intro f hf
        exact harr f (by simp [hf])
  apply hstrict _ (clockEventList_sorted ξ)
  · unfold clockEventList
    exact List.Nodup.mergeSort (Finset.nodup_toList _)
  · intro e he
    exact (clockEventList_mem_iff_p_clock_r4 ξ e).mp he

/-- Restricting the event list to a set of edges depends only on those edges. -/
theorem clockEventList_filter_edges_eq {T : ℕ} {R : Type*}
    [Fintype R] [DecidableEq R] {g : ℕ} {Ω : R → Type*}
    [∀ a, Fintype (Ω a)] [∀ a, DecidableEq (Ω a)]
    (ξ ξ' : ClockField T R g Ω) (D : Finset (RowLabel R g)) (horizon : ℕ)
    (hξ : ∀ e ∈ D, ξ e = ξ' e) :
    (clockEventList ξ).filter (fun e => (e.1, e.2.1) ∈ D ∧ e.2.2.1.val < horizon) =
      (clockEventList ξ').filter (fun e => (e.1, e.2.1) ∈ D ∧ e.2.2.1.val < horizon) := by
  classical
  apply List.Pairwise.eq_of_mem_iff
    ((clockEventList_strict ξ).filter _)
    ((clockEventList_strict ξ').filter _)
  intro e
  simp only [List.mem_filter, decide_eq_true_eq, clockEventList_mem_iff_p_clock_r4]
  by_cases hD : (e.1, e.2.1) ∈ D
  · have he : candidateIsArrival ξ e ↔ candidateIsArrival ξ' e := by
      unfold candidateIsArrival
      rw [hξ (e.1, e.2.1) hD]
    rw [he]
  · simp [hD]

/-- The outside matching is measurable using only outside clocks, at every horizon. -/
theorem runGreedy_filter_edges_eq {T : ℕ} {R : Type*}
    [Fintype R] [DecidableEq R] {g : ℕ} {Ω : R → Type*}
    [∀ a, Fintype (Ω a)] [∀ a, DecidableEq (Ω a)]
    (ξ ξ' : ClockField T R g Ω) (D : Finset (RowLabel R g)) (horizon : ℕ)
    (hξ : ∀ e ∈ D, ξ e = ξ' e) :
    runGreedy ξ ((clockEventList ξ).filter
        (fun e => (e.1, e.2.1) ∈ D ∧ e.2.2.1.val < horizon)) =
      runGreedy ξ' ((clockEventList ξ').filter
        (fun e => (e.1, e.2.1) ∈ D ∧ e.2.2.1.val < horizon)) := by
  classical
  rw [clockEventList_filter_edges_eq ξ ξ' D horizon hξ]
  let events := (clockEventList ξ').filter
    (fun e => (e.1, e.2.1) ∈ D ∧ e.2.2.1.val < horizon)
  have hfold (es : List (ClockCandidate T R g Ω)) (s : GreedyState R g Ω)
      (hes : ∀ e ∈ es, (e.1, e.2.1) ∈ D) :
      es.foldl (fun s e => processArrival ξ s e) s =
        es.foldl (fun s e => processArrival ξ' s e) s := by
    induction es generalizing s with
    | nil => rfl
    | cons e es ih =>
      have he : candidateIsArrival ξ e ↔ candidateIsArrival ξ' e := by
        unfold candidateIsArrival
        rw [hξ (e.1, e.2.1) (hes e (by simp))]
      have hstep : processArrival ξ s e = processArrival ξ' s e := by
        unfold processArrival
        rw [he]
      simp only [List.foldl_cons]
      rw [hstep]
      exact ih _ (by intro f hf; exact hes f (by simp [hf]))
  apply hfold events emptyGreedyState
  intro e he
  exact ((List.mem_filter.mp he).2 |> of_decide_eq_true).1

/-- A target row is still free in a prefix which has not processed its distinguished arrival. -/
theorem prefix_target_row_free {T : ℕ} {R : Type*} [DecidableEq R]
    {g : ℕ} {Ω : R → Type*} [∀ a, DecidableEq (Ω a)]
    (ξ : ClockField T R g Ω) (pre suffix : List (ClockCandidate T R g Ω))
    (a : R) (y : Fin g) (t : Fin T) (o : Ω a)
    (hfinal : (runGreedy ξ (pre ++ suffix)).assignment a = some (y, o))
    (hclock : ξ (a, y) = .tick t o)
    (habsent : (⟨a, y, t, o⟩ : ClockCandidate T R g Ω) ∉ pre) :
    (runGreedy ξ pre).assignment a = none := by
  classical
  cases hp : (runGreedy ξ pre).assignment a with
  | none => rfl
  | some v =>
    obtain ⟨y', o'⟩ := v
    have hpres := runGreedy_preserves_existing_assignment ξ suffix (runGreedy ξ pre)
      a (y', o') hp
    have hp' : (runGreedy ξ (pre ++ suffix)).assignment a = some (y', o') := by
      simpa [runGreedy, List.foldl_append] using hpres
    have hpair := Option.some.inj (hp'.symm.trans hfinal)
    have hy := congrArg Prod.fst hpair
    have ho := congrArg Prod.snd hpair
    change y' = y at hy
    change o' = o at ho
    subst y'
    subst o'
    obtain hinit | ⟨t', ht', hclock'⟩ :=
      fold_assignment_source_event ξ pre emptyGreedyState a y o hp
    · simp [emptyGreedyState] at hinit
    · have ht : t' = t := (MeshClockValue.tick.inj (hclock'.symm.trans hclock)).1
      exact False.elim (habsent (by simpa [ht] using ht'))

/-- A target label is free whenever its uniquely assigned target row is free in the pre. -/
theorem prefix_target_label_free {T : ℕ} {R : Type*} [DecidableEq R]
    {g : ℕ} {Ω : R → Type*} [∀ a, DecidableEq (Ω a)]
    (ξ : ClockField T R g Ω) (pre suffix : List (ClockCandidate T R g Ω))
    (a : R) (y : Fin g)
    (hunique : ∀ b ob, (runGreedy ξ (pre ++ suffix)).assignment b = some (y, ob) → b = a)
    (hfree : (runGreedy ξ pre).assignment a = none) :
    ¬ labelUsed (runGreedy ξ pre) y := by
  rintro ⟨b, ob, hb⟩
  have hpres := runGreedy_preserves_existing_assignment ξ suffix (runGreedy ξ pre)
    b (y, ob) hb
  have hb' : (runGreedy ξ (pre ++ suffix)).assignment b = some (y, ob) := by
    simpa [runGreedy, List.foldl_append] using hpres
  have hba := hunique b ob hb'
  subst b
  rw [hfree] at hb
  contradiction

/-- A crossing arrival with both endpoints free would violate final target separation. -/
theorem crossing_arrival_forbidden {T : ℕ} {R : Type*} [DecidableEq R]
    {g : ℕ} {Ω : R → Type*} [∀ a, DecidableEq (Ω a)]
    (ξ : ClockField T R g Ω) (S : Finset R) (L : Finset (Fin g))
    (pre suffix : List (ClockCandidate T R g Ω)) (e : ClockCandidate T R g Ω)
    (hfinal : Separated S L (runGreedy ξ (pre ++ e :: suffix)))
    (harrival : candidateIsArrival ξ e)
    (hrow : (runGreedy ξ pre).assignment e.1 = none)
    (hlabel : ¬ labelUsed (runGreedy ξ pre) e.2.1)
    (hcross : ¬ (e.1 ∈ S ↔ e.2.1 ∈ L)) : False := by
  classical
  have hsep : Separated S L (processArrival ξ (runGreedy ξ pre) e) := by
    apply separated_before_fold ξ suffix S L
    simpa [runGreedy, List.foldl_append, List.foldl_cons] using hfinal
  have hacc := And.intro harrival (And.intro hrow hlabel)
  have ha : (processArrival ξ (runGreedy ξ pre) e).assignment e.1 =
      some (e.2.1, e.2.2.2) := by
    simp [processArrival, hacc]
  exact hcross (hsep e.1 e.2.1 e.2.2.2 ha)

end HypercubeRamsey.Lane_sol_clock_s7
