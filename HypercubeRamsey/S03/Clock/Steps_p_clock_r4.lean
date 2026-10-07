import HypercubeRamsey.S03.Clock.Inputs
import HypercubeRamsey.Framework.FinProbLemmas

namespace HypercubeRamsey.Clock

theorem pi_pr_forall_coordinates {ι : Type*} [Fintype ι] [DecidableEq ι]
    {α : ι → Type*} [∀ i, Fintype (α i)]
    (P : ∀ i, FinProb (α i)) (A : ∀ i, α i → Prop) :
    (FinProb.pi P).pr (fun x => ∀ i, A i (x i)) =
      ∏ i, (P i).pr (A i) := by
  classical
  unfold FinProb.pr FinProb.pi
  have hprod (x : ∀ i, α i) :
      (if ∀ i, A i (x i) then ∏ i, (P i).w (x i) else 0) =
        ∏ i, if A i (x i) then (P i).w (x i) else 0 := by
    by_cases h : ∀ i, A i (x i)
    · simp [h]
    · obtain ⟨i, hi⟩ := not_forall.mp h
      rw [if_neg h, Finset.prod_eq_zero (Finset.mem_univ i)]
      · simp [hi]
  simp_rw [hprod]
  calc
    (∑ x : ∀ i, α i, ∏ i, if A i (x i) then (P i).w (x i) else 0) =
        ∏ i, ∑ x : α i, if A i x then (P i).w x else 0 := by
          exact (Fintype.prod_sum (fun i x => if A i x then (P i).w x else 0)).symm
    _ = ∏ i, (P i).pr (A i) := by simp [FinProb.pr]

theorem pi_pr_required_coordinate_eq {ι : Type*} [Fintype ι] [DecidableEq ι]
    {α : ι → Type*} [∀ i, Fintype (α i)] [∀ i, DecidableEq (α i)]
    (P : ∀ i, FinProb (α i)) (required : ι → Prop) [DecidablePred required]
    (z : ∀ i, α i) :
  (FinProb.pi P).pr (fun x => ∀ i, required i → x i = z i) =
      ∏ i, if required i then (P i).pr (fun y => y = z i) else 1 := by
  classical
  calc
    (FinProb.pi P).pr (fun x => ∀ i, required i → x i = z i) =
        ∏ i, (P i).pr (fun y => required i → y = z i) :=
          pi_pr_forall_coordinates P (fun i y => required i → y = z i)
    _ = ∏ i, if required i then (P i).pr (fun y => y = z i) else 1 := by
          apply Finset.prod_congr rfl
          intro i hi
          by_cases h : required i
          · have hpoint : (P i).pr (fun y => y = z i) = (P i).w (z i) := by
              rw [FinProb.pr, Fintype.sum_eq_single (z i)]
              · simp
              · intro y hy
                simp [hy]
            simp [h, hpoint]
          · simp [h, FinProb.pr, (P i).sum_eq_one]

theorem outputEdgeClockLaw_noArrival_prob {α : Type*} [Fintype α] [DecidableEq α]
    {g T : ℕ} (δ : ℝ) (hδ : 0 ≤ δ) (p : FinProb α) (lab : α → Fin g)
    (y : Fin g) (hbase : 0 ≤ 1 - δ * labMarg p lab y) :
    (outputEdgeClockLaw (T := T) δ hδ p lab y hbase).pr
      (fun x => x = .noArrival) = survival δ (labMarg p lab y) T := by
  classical
  rw [FinProb.pr, Fintype.sum_eq_single MeshClockValue.noArrival]
  · simp [outputEdgeClockLaw, markedClockLaw, markedClockWeight]
  · intro x hx
    simp [hx]

theorem survival_le_exp {δ r : ℝ} {T : ℕ}
    (hδ0 : 0 ≤ δ) (hδ1 : δ ≤ 1) (hr0 : 0 ≤ r) (hr1 : r ≤ 1) :
    survival δ r T ≤ Real.exp (-δ * r * (T : ℝ)) := by
  let x : ℝ := δ * r
  have hx0 : 0 ≤ x := mul_nonneg hδ0 hr0
  have hx1 : x ≤ 1 := mul_le_one₀ hδ1 hr0 hr1
  have hbase : 0 ≤ 1 - x := sub_nonneg.mpr hx1
  have hstep : 1 - x ≤ Real.exp (-x) := Real.one_sub_le_exp_neg x
  have hpow : ∀ n : ℕ, (1 - x) ^ n ≤ Real.exp (-x * (n : ℝ)) := by
    intro n
    induction n with
    | zero => simp
    | succ n ih =>
        rw [pow_succ]
        calc
          (1 - x) ^ n * (1 - x) ≤ Real.exp (-x * (n : ℝ)) * Real.exp (-x) :=
            mul_le_mul ih hstep hbase (Real.exp_nonneg _)
          _ = Real.exp (-x * ((n : ℝ) + 1)) := by
            rw [← Real.exp_add]
            congr 1 <;> ring
          _ = Real.exp (-x * ((n + 1 : ℕ) : ℝ)) := by
            rw [Nat.cast_succ]
  simpa [survival, x, mul_assoc, mul_left_comm, mul_comm] using hpow T

private theorem pi_weight_split {ι : Type*} [Fintype ι] [DecidableEq ι]
    {α : ι → Type*} [∀ i, Fintype (α i)] (P : ∀ i, FinProb (α i))
    (s : Finset ι)
    (a : ∀ i : {i // i ∈ s}, α i.1) (b : ∀ i : {i // i ∉ s}, α i.1) :
    (∏ i, (P i).w ((Equiv.piEquivPiSubtypeProd (fun i => i ∈ s) α).symm (a, b) i)) =
      (∏ i : {i // i ∈ s}, (P i.1).w (a i)) *
        ∏ i : {i // i ∉ s}, (P i.1).w (b i) := by
  classical
  let e := Equiv.piEquivPiSubtypeProd (fun i => i ∈ s) α
  let f : ι → ℝ := fun i => (P i).w (e.symm (a, b) i)
  let t : Finset ι := Finset.univ.filter (fun i => i ∉ s)
  have hs : (∏ i : {i // i ∈ s}, f i.1) =
      ∏ i ∈ Finset.univ with i ∈ s, f i := by
    rw [Finset.univ_eq_attach]
    simpa [f] using Finset.prod_attach s f
  let ecomp : {i // i ∉ s} ≃ {i // i ∈ t} := {
    toFun := fun i => ⟨i.1, by simp [t, i.2]⟩
    invFun := fun i => ⟨i.1, (Finset.mem_filter.mp i.2).2⟩
    left_inv := by intro i; apply Subtype.ext; rfl
    right_inv := by intro i; apply Subtype.ext; rfl
  }
  have hnot : (∏ i : {i // i ∉ s}, f i.1) =
      ∏ i ∈ Finset.univ with i ∉ s, f i := by
    calc
      (∏ i : {i // i ∉ s}, f i.1) = ∏ i : {i // i ∈ t}, f i.1 := by
        exact Fintype.prod_equiv ecomp _ _ (by intro i; rfl)
      _ = ∏ i ∈ t.attach, f i.1 := by rw [Finset.univ_eq_attach]
      _ = ∏ i ∈ t, f i := Finset.prod_attach t f
      _ = ∏ i ∈ Finset.univ with i ∉ s, f i := by simp [t]
  rw [(Finset.prod_filter_mul_prod_filter_not (Finset.univ : Finset ι)
    (fun i : ι => i ∈ s) f).symm]
  rw [← hs, ← hnot]
  have hleft : ∀ i : {i // i ∈ s}, e.symm (a, b) i.1 = a i := by
    intro i
    simp [e, Equiv.piEquivPiSubtypeProd]
  have hright : ∀ i : {i // i ∉ s}, e.symm (a, b) i.1 = b i := by
    intro i
    simp only [e, Equiv.piEquivPiSubtypeProd_symm_apply, dif_neg i.2]
  simp_rw [f, hleft, hright]

theorem pi_expect_split_p_clock_r4 {ι : Type*} [Fintype ι] [DecidableEq ι]
    {α : ι → Type*} [∀ i, Fintype (α i)] (P : ∀ i, FinProb (α i))
    (s : Finset ι) (f : (∀ i, α i) → ℝ) :
    (FinProb.pi P).expect f =
      ∑ a : (∀ i : {i // i ∈ s}, α i.1),
        ∑ b : (∀ i : {i // i ∉ s}, α i.1),
          (FinProb.pi (fun i : {i // i ∈ s} => P i.1)).w a *
            (FinProb.pi (fun i : {i // i ∉ s} => P i.1)).w b *
            f ((Equiv.piEquivPiSubtypeProd (fun i => i ∈ s) α).symm (a, b)) := by
  classical
  let e := Equiv.piEquivPiSubtypeProd (fun i => i ∈ s) α
  change (∑ ω, (∏ i, (P i).w (ω i)) * f ω) = _
  rw [← Equiv.sum_comp e.symm (fun ω => (∏ i, (P i).w (ω i)) * f ω)]
  rw [Fintype.sum_prod_type]
  apply Fintype.sum_congr
  intro a
  apply Fintype.sum_congr
  intro b
  rw [pi_weight_split P s a b]
  simp only [e, Equiv.piEquivPiSubtypeProd_symm_apply]
  simp [FinProb.pi]

private theorem processArrival_assignment_source {T : ℕ} {R : Type*} [DecidableEq R]
    {g : ℕ} {Ω : R → Type*} [∀ a, DecidableEq (Ω a)]
    (ξ : ClockField T R g Ω) (s : GreedyState R g Ω)
    (e : ClockCandidate T R g Ω) (a : R) (y : Fin g) (o : Ω a)
    (h : (processArrival ξ s e).assignment a = some (y, o)) :
    s.assignment a = some (y, o) ∨ ∃ t, ξ (a, y) = .tick t o := by
  classical
  by_cases hacc : candidateIsArrival ξ e ∧ s.assignment e.1 = none ∧ ¬ labelUsed s e.2.1
  · by_cases hrow : e.1 = a
    · subst a
      simp only [processArrival, if_pos hacc, dif_pos rfl] at h
      have hpair : (e.2.1, e.2.2.2) = (y, o) := by
        simpa using h
      rcases Prod.mk.inj hpair with ⟨rfl, rfl⟩
      right
      refine ⟨e.2.2.1, ?_⟩
      simpa [candidateIsArrival] using hacc.1
    · simp only [processArrival, if_pos hacc, dif_neg hrow] at h
      exact Or.inl h
  · have hs : s.assignment a = some (y, o) := by
      simpa [processArrival, hacc] using h
    exact Or.inl hs

private theorem runGreedy_assignment_source {T : ℕ} {R : Type*} [DecidableEq R]
    {g : ℕ} {Ω : R → Type*} [∀ a, DecidableEq (Ω a)]
    (ξ : ClockField T R g Ω) (events : List (ClockCandidate T R g Ω))
    (s : GreedyState R g Ω) (a : R) (y : Fin g) (o : Ω a)
    (h : (events.foldl (fun s e => processArrival ξ s e) s).assignment a = some (y, o)) :
    s.assignment a = some (y, o) ∨ ∃ t, ξ (a, y) = .tick t o := by
  induction events generalizing s with
  | nil => exact Or.inl h
  | cons e events ih =>
      have h' := ih (processArrival ξ s e) h
      rcases h' with h' | h'
      · exact processArrival_assignment_source ξ s e a y o h'
      · exact Or.inr h'

theorem greedyMatching_assignment_source {T : ℕ} {R : Type*} [Fintype R] [DecidableEq R]
    {g : ℕ} {Ω : R → Type*} [∀ a, Fintype (Ω a)] [∀ a, DecidableEq (Ω a)]
    (ξ : ClockField T R g Ω) (a : R) (y : Fin g) (o : Ω a)
    (h : (greedyMatching ξ).assignment a = some (y, o)) :
    ∃ t, ξ (a, y) = .tick t o := by
  have h' := runGreedy_assignment_source ξ (clockEventList ξ) emptyGreedyState a y o (by
    simpa [greedyMatching, runGreedy] using h)
  rcases h' with h0 | h0
  · simpa [emptyGreedyState] using h0
  · exact h0

theorem clockCandidate_eq_of_priority_eq {T : ℕ} {R : Type*} [Fintype R] [DecidableEq R]
    {g : ℕ} {Ω : R → Type*}
    (ξ : ClockField T R g Ω) (e f : ClockCandidate T R g Ω)
    (he : candidateIsArrival ξ e) (hf : candidateIsArrival ξ f)
    (hkey : eventPriority e = eventPriority f) : e = f := by
  classical
  rcases e with ⟨a, y, t, o⟩
  rcases f with ⟨b, z, s, p⟩
  have he' : ξ (a, y) = .tick t o := he
  have hf' : ξ (b, z) = .tick s p := hf
  have hg : 0 < g := by have h := y.isLt; omega
  let base : ℕ := Fintype.card R * g
  let ra : ℕ := (Fintype.equivFin R a).val
  let rb : ℕ := (Fintype.equivFin R b).val
  let pa : ℕ := ra * g + y.val
  let pb : ℕ := rb * g + z.val
  have hbase : 0 < base := Nat.mul_pos (Fintype.card_pos_iff.mpr ⟨a⟩) hg
  have hpa : pa < base := by
    have hinner : ra * g + y.val < (ra + 1) * g := by
      calc
        ra * g + y.val < ra * g + g := Nat.add_lt_add_left y.isLt _
        _ = (ra + 1) * g := by simp [Nat.add_mul]
    have hra : ra + 1 ≤ Fintype.card R := Nat.succ_le_of_lt (Fintype.equivFin R a).isLt
    dsimp [pa, base]
    exact lt_of_lt_of_le hinner (Nat.mul_le_mul_right g hra)
  have hpb : pb < base := by
    have hinner : rb * g + z.val < (rb + 1) * g := by
      calc
        rb * g + z.val < rb * g + g := Nat.add_lt_add_left z.isLt _
        _ = (rb + 1) * g := by simp [Nat.add_mul]
    have hrb : rb + 1 ≤ Fintype.card R := Nat.succ_le_of_lt (Fintype.equivFin R b).isLt
    dsimp [pb, base]
    exact lt_of_lt_of_le hinner (Nat.mul_le_mul_right g hrb)
  have hdecomp : t.val * base + pa = s.val * base + pb := by
    simpa [eventPriority, base, ra, rb, pa, pb, Nat.add_assoc] using hkey
  have hdivA : (t.val * base + pa) / base = t.val := by
    apply Nat.div_eq_of_lt_le
    · exact Nat.le_add_right _ _
    · calc
        t.val * base + pa < t.val * base + base := Nat.add_lt_add_left hpa _
        _ = (t.val + 1) * base := by simp [Nat.add_mul]
  have hdivB : (s.val * base + pb) / base = s.val := by
    apply Nat.div_eq_of_lt_le
    · exact Nat.le_add_right _ _
    · calc
        s.val * base + pb < s.val * base + base := Nat.add_lt_add_left hpb _
        _ = (s.val + 1) * base := by simp [Nat.add_mul]
  have htval : t.val = s.val := by
    have h := congrArg (fun n : ℕ => n / base) hdecomp
    rw [hdivA, hdivB] at h
    exact h
  have hmodA : (t.val * base + pa) % base = pa := Nat.mul_add_mod_of_lt hpa
  have hmodB : (s.val * base + pb) % base = pb := Nat.mul_add_mod_of_lt hpb
  have hpart : pa = pb := by
    have h := congrArg (fun n : ℕ => n % base) hdecomp
    rw [hmodA, hmodB] at h
    exact h
  have hdivRA : pa / g = ra := by
    apply Nat.div_eq_of_lt_le
    · dsimp [pa]
      exact Nat.le_add_right _ _
    · calc
        pa < ra * g + g := by
          dsimp [pa]
          exact Nat.add_lt_add_left y.isLt _
        _ = (ra + 1) * g := by simp [Nat.add_mul]
  have hdivRB : pb / g = rb := by
    apply Nat.div_eq_of_lt_le
    · dsimp [pb]
      exact Nat.le_add_right _ _
    · calc
        pb < rb * g + g := by
          dsimp [pb]
          exact Nat.add_lt_add_left z.isLt _
        _ = (rb + 1) * g := by simp [Nat.add_mul]
  have hrank : ra = rb := by
    have h := congrArg (fun n : ℕ => n / g) hpart
    rw [hdivRA, hdivRB] at h
    exact h
  have hmodRA : pa % g = y.val := by
    dsimp [pa]
    exact Nat.mul_add_mod_of_lt y.isLt
  have hmodRB : pb % g = z.val := by
    dsimp [pb]
    exact Nat.mul_add_mod_of_lt z.isLt
  have hyval : y.val = z.val := by
    have h := congrArg (fun n : ℕ => n % g) hpart
    rw [hmodRA, hmodRB] at h
    exact h
  have hrow : a = b := (Fintype.equivFin R).injective (Fin.ext hrank)
  have hy : y = z := Fin.ext hyval
  have ht : t = s := Fin.ext htval
  subst b
  subst z
  subst s
  have hout : o = p := by
    have hclock : MeshClockValue.tick t o = MeshClockValue.tick t p := he'.symm.trans hf'
    injection hclock with _ hout
  subst p
  rfl

theorem clockEventList_mem_iff_p_clock_r4 {T : ℕ} {R : Type*} [Fintype R] [DecidableEq R]
    {g : ℕ} {Ω : R → Type*} [∀ a, Fintype (Ω a)] [∀ a, DecidableEq (Ω a)]
    (ξ : ClockField T R g Ω) (e : ClockCandidate T R g Ω) :
    e ∈ clockEventList ξ ↔ candidateIsArrival ξ e := by
  classical
  unfold clockEventList
  have hp := List.mergeSort_perm
    ((Finset.univ.filter (candidateIsArrival ξ)).toList)
    (fun e f => decide (eventPriority e ≤ eventPriority f))
  rw [hp.mem_iff]
  simp [Finset.mem_filter]

theorem clockEventList_filter_row_eq {T : ℕ} {R : Type*} [Fintype R] [DecidableEq R]
    {g : ℕ} {Ω : R → Type*} [∀ a, Fintype (Ω a)] [∀ a, DecidableEq (Ω a)]
    (ξ ξ' : ClockField T R g Ω) (a : R)
    (hξ : ∀ b y, b ≠ a → ξ (b, y) = ξ' (b, y)) :
    (clockEventList ξ).filter (fun e => e.1 ≠ a) =
      (clockEventList ξ').filter (fun e => e.1 ≠ a) := by
  classical
  let pred : ClockCandidate T R g Ω → Prop := fun e => e.1 ≠ a
  let l := (clockEventList ξ).filter pred
  let l' := (clockEventList ξ').filter pred
  have harr (e : ClockCandidate T R g Ω) (he : e.1 ≠ a) :
      candidateIsArrival ξ e ↔ candidateIsArrival ξ' e := by
    unfold candidateIsArrival
    rw [hξ e.1 e.2.1 he]
  have hset : l.toFinset = l'.toFinset := by
    apply Finset.ext
    intro e
    simp only [List.mem_toFinset, l, l', pred, List.mem_filter,
      clockEventList_mem_iff_p_clock_r4]
    by_cases he : e.1 = a
    · simp [he]
    · rw [harr e he]
  have hnodup (ζ : ClockField T R g Ω) : (clockEventList ζ).Nodup := by
    unfold clockEventList
    exact (List.mergeSort_perm _ _).nodup_iff.mpr (Finset.nodup_toList _)
  have hsort (ζ : ClockField T R g Ω) :
      (clockEventList ζ).Pairwise (fun e f => eventPriority e ≤ eventPriority f) :=
    clockEventList_sorted ζ
  have hlNodup : l.Nodup := by
    dsimp [l, pred]
    exact (hnodup ξ).filter _
  have hl'Nodup : l'.Nodup := by
    dsimp [l', pred]
    exact (hnodup ξ').filter _
  have strict (ζ : ClockField T R g Ω) (xs : List (ClockCandidate T R g Ω))
      (hsort : xs.Pairwise (fun e f => eventPriority e ≤ eventPriority f))
      (hnodup : xs.Nodup) (hmem : ∀ e ∈ xs, candidateIsArrival ζ e) :
      xs.Pairwise (fun e f => eventPriority e < eventPriority f) := by
    induction xs with
    | nil => simp
    | cons e xs ih =>
        simp only [List.pairwise_cons, List.nodup_cons] at hsort hnodup
        rcases hsort with ⟨hhead, htail⟩
        rcases hnodup with ⟨hnot, htailNodup⟩
        refine List.Pairwise.cons ?_ (ih htail htailNodup ?_)
        · intro f hf
          have hle := hhead f hf
          have hne : eventPriority e ≠ eventPriority f := by
            intro heq
            have hevent := clockCandidate_eq_of_priority_eq ζ e f
              (hmem e (by simp)) (hmem f (by simp [hf])) heq
            exact hnot (by simpa [hevent])
          exact lt_of_le_of_ne hle hne
        · intro f hf
          exact hmem f (by simp [hf])
  have hlStrict : l.Pairwise (fun e f => eventPriority e < eventPriority f) := by
    apply strict ξ l
    · simpa [l, pred] using (hsort ξ).filter pred
    · exact hlNodup
    · intro e he
      have he' := (List.mem_filter.mp he).1
      exact (clockEventList_mem_iff_p_clock_r4 ξ e).1 he'
  have hl'Strict : l'.Pairwise (fun e f => eventPriority e < eventPriority f) := by
    apply strict ξ' l'
    · simpa [l', pred] using (hsort ξ').filter pred
    · exact hl'Nodup
    · intro e he
      have he' := (List.mem_filter.mp he).1
      exact (clockEventList_mem_iff_p_clock_r4 ξ' e).1 he'
  have hperm : l.Perm l' :=
    List.perm_of_nodup_nodup_toFinset_eq hlNodup hl'Nodup hset
  apply hperm.eq_of_pairwise (by
    intro e f he hf h₁ h₂
    omega) hlStrict hl'Strict

private theorem processArrival_preserves_assignment {T : ℕ} {R : Type*} [DecidableEq R]
    {g : ℕ} {Ω : R → Type*} [∀ a, DecidableEq (Ω a)]
    (ξ : ClockField T R g Ω) (s : GreedyState R g Ω)
    (e : ClockCandidate T R g Ω) (a : R)
    (h : s.assignment a ≠ none) : (processArrival ξ s e).assignment a ≠ none := by
  classical
  by_cases hacc : candidateIsArrival ξ e ∧ s.assignment e.1 = none ∧ ¬ labelUsed s e.2.1
  · by_cases hrow : e.1 = a
    · subst a
      simp [processArrival, hacc]
    · simpa [processArrival, hacc, hrow] using h
  · simpa [processArrival, hacc] using h

private theorem processArrival_preserves_existing_assignment {T : ℕ} {R : Type*} [DecidableEq R]
    {g : ℕ} {Ω : R → Type*} [∀ a, DecidableEq (Ω a)]
    (ξ : ClockField T R g Ω) (s : GreedyState R g Ω)
    (e : ClockCandidate T R g Ω) (a : R) (v : Fin g × Ω a)
    (h : s.assignment a = some v) :
    (processArrival ξ s e).assignment a = some v := by
  classical
  by_cases hacc : candidateIsArrival ξ e ∧ s.assignment e.1 = none ∧ ¬ labelUsed s e.2.1
  · by_cases hrow : e.1 = a
    · subst a
      simp [processArrival, hacc, h] at *
    · simpa [processArrival, hacc, hrow] using h
  · simpa [processArrival, hacc] using h

theorem runGreedy_preserves_assignment {T : ℕ} {R : Type*} [DecidableEq R]
    {g : ℕ} {Ω : R → Type*} [∀ a, DecidableEq (Ω a)]
    (ξ : ClockField T R g Ω) (events : List (ClockCandidate T R g Ω))
    (s : GreedyState R g Ω) (a : R) (h : s.assignment a ≠ none) :
    (events.foldl (fun s e => processArrival ξ s e) s).assignment a ≠ none := by
  induction events generalizing s with
  | nil => exact h
  | cons e events ih =>
      simp only [List.foldl_cons]
      exact ih (processArrival ξ s e) (processArrival_preserves_assignment ξ s e a h)

theorem runGreedy_preserves_existing_assignment {T : ℕ} {R : Type*} [DecidableEq R]
    {g : ℕ} {Ω : R → Type*} [∀ a, DecidableEq (Ω a)]
    (ξ : ClockField T R g Ω) (events : List (ClockCandidate T R g Ω))
    (s : GreedyState R g Ω) (a : R) (v : Fin g × Ω a)
    (h : s.assignment a = some v) :
    (events.foldl (fun s e => processArrival ξ s e) s).assignment a = some v := by
  induction events generalizing s with
  | nil => exact h
  | cons e events ih =>
      simp only [List.foldl_cons]
      exact ih (processArrival ξ s e)
        (processArrival_preserves_existing_assignment ξ s e a v h)

theorem runGreedy_filter_unmatched_row {T : ℕ} {R : Type*} [DecidableEq R]
    {g : ℕ} {Ω : R → Type*} [∀ a, DecidableEq (Ω a)]
    (ξ : ClockField T R g Ω) (events : List (ClockCandidate T R g Ω))
    (a : R)
    (h : (runGreedy ξ events).assignment a = none) :
    runGreedy ξ events = runGreedy ξ (events.filter (fun e => e.1 ≠ a)) := by
  classical
  let process := fun s e => processArrival ξ s e
  have hfold (events : List (ClockCandidate T R g Ω)) (s : GreedyState R g Ω)
      (hfinal : (events.foldl process s).assignment a = none) :
      events.foldl process s = (events.filter (fun e => e.1 ≠ a)).foldl process s := by
    induction events generalizing s with
    | nil => rfl
    | cons e events ih =>
        simp only [List.foldl_cons] at hfinal ⊢
        by_cases he : e.1 = a
        · have hproc : process s e = s := by
            by_cases hacc : candidateIsArrival ξ e ∧ s.assignment e.1 = none ∧ ¬ labelUsed s e.2.1
            · have hassigned : (process s e).assignment a ≠ none := by
                subst a
                simp [process, processArrival, hacc]
              have htail := runGreedy_preserves_assignment ξ events (process s e) a hassigned
              exact False.elim (htail hfinal)
            · simp [process, processArrival, hacc]
          rw [hproc] at hfinal
          rw [hproc]
          simpa [List.filter_cons, he, process] using ih s hfinal
        · have htail : (events.foldl process (process s e)).assignment a = none := hfinal
          have h := ih (process s e) htail
          simpa [List.filter_cons, he, process] using h
  simpa [runGreedy, process] using hfold events emptyGreedyState h

theorem runGreedy_unmatched_row_no_arrival_to_free_label {T : ℕ} {R : Type*} [DecidableEq R]
    {g : ℕ} {Ω : R → Type*} [∀ a, DecidableEq (Ω a)]
    (ξ : ClockField T R g Ω) (events : List (ClockCandidate T R g Ω))
    (a : R) (y : Fin g)
    (hrow : (runGreedy ξ events).assignment a = none)
    (hfree : ¬ labelUsed (runGreedy ξ (events.filter (fun e => e.1 ≠ a))) y)
    (harr : ∀ e ∈ events, candidateIsArrival ξ e) :
    ∀ e ∈ events, e.1 = a → e.2.1 = y → False := by
  classical
  have hstateEq := runGreedy_filter_unmatched_row ξ events a hrow
  have hfreeFull : ¬ labelUsed (runGreedy ξ events) y := by
    rw [hstateEq]
    exact hfree
  intro e he heRow heLabel
  obtain ⟨pre, post, hlist⟩ := List.mem_iff_append.mp he
  subst events
  let st := runGreedy ξ pre
  have hstRow : st.assignment a = none := by
    by_cases hs : st.assignment a = none
    · exact hs
    · obtain ⟨v, hv⟩ := Option.ne_none_iff_exists'.mp hs
      have hp := runGreedy_preserves_existing_assignment ξ (e :: post) st a v hv
      have hp' : (runGreedy ξ (pre ++ e :: post)).assignment a = some v := by
        simpa [st, runGreedy, List.foldl_append] using hp
      rw [hp'] at hrow
      cases hrow
  have hstFree : ¬ labelUsed st y := by
    intro hs
    obtain ⟨b, o, hb⟩ := hs
    have hp := runGreedy_preserves_existing_assignment ξ (e :: post) st b (y, o) hb
    have hp' : (runGreedy ξ (pre ++ e :: post)).assignment b = some (y, o) := by
      simpa [st, runGreedy, List.foldl_append] using hp
    exact hfreeFull ⟨b, o, by simpa using hp'⟩
  have hrowState : st.assignment e.1 = none := by
    rw [heRow]
    exact hstRow
  have hfreeState : ¬ labelUsed st e.2.1 := by simpa [heLabel] using hstFree
  have hacc : candidateIsArrival ξ e ∧ st.assignment e.1 = none ∧
      ¬ labelUsed st e.2.1 := ⟨harr e (by simp), hrowState, hfreeState⟩
  have hassigned : (processArrival ξ st e).assignment a ≠ none := by
    simp [processArrival, hacc, heRow]
  have hfinal := runGreedy_preserves_assignment ξ post (processArrival ξ st e) a hassigned
  have hfinal' : (runGreedy ξ (pre ++ e :: post)).assignment a ≠ none := by
    simpa [st, runGreedy, List.foldl_append] using hfinal
  exact hfinal' hrow

end HypercubeRamsey.Clock
