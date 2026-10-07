import HypercubeRamsey.S16.Producers_sol_s16_prod1

/-! Finite group-bin certificates. Capacity events fix a subset of groups
to one physical bin, within a dyadic contribution bucket. Their scopes have
at most d groups. The total charge at each group is at most d^(-2)/8, so
every neighboring reciprocal product is at most 2. Thus twice the product
mass suffices as a capacity charge. Singleton pins retain only their own
bin's capacity events. -/

namespace HypercubeRamsey.S16.Lane_sol_s16_group

open Classical
open scoped BigOperators
open Lane_sol_s16_prod1

variable {I O : Type} [Fintype I] [DecidableEq I] [Fintype O] [DecidableEq O]
variable {safe : (I → O) → Prop}

theorem rpow_nonneg {x : ℝ} (hx : 0 ≤ x) (a : ℝ) : 0 ≤ Real.rpow x a :=
  Real.rpow_nonneg hx a

theorem product_coordinate (q : I → FinLaw O) (i : I) (o : O) :
    (FinLaw.pi q).pr (fun a => a i = o) = (q i).w o := by
  exact (Lane_q_s16_calib.finLaw_pi_pr_coordinate q i (fun y => y = o)).trans
    (Lane_q_s16_calib.finLaw_pr_eq_weight _ _)

theorem product_cylinder (q : I → FinLaw O) (S : Finset I) (o : I → O) :
    (FinLaw.pi q).pr (fun a => ∀ i ∈ S, a i = o i) = ∏ i ∈ S, (q i).w (o i) := by
  let C : I → O → Prop := fun i y => i ∈ S → y = o i
  change (FinLaw.pi q).pr (fun a => ∀ i, C i (a i)) = _
  rw [Lane_q_s16_calib.finLaw_pi_pr_forall]
  have hrow : ∀ i, (q i).pr (C i) = if i ∈ S then (q i).w (o i) else 1 := by
    intro i
    by_cases hi : i ∈ S
    · simp only [C, hi, true_implies, if_true]
      exact Lane_q_s16_calib.finLaw_pr_eq_weight _ _
    · simp [C, hi, FinLaw.pr, (q i).sum_one]
  simp_rw [hrow]
  simp [Finset.prod_ite_mem]

theorem product_avoid_local
    (A : AvoidanceData (fun a : I → O => a) (fun i : I => i) safe)
    (hlocal : ∀ e a a', (∀ i ∈ A.scope e, a i = a' i) →
      (a ∈ A.bad e ↔ a' ∈ A.bad e))
    (R : Finset A.Event) (a a' : I → O)
    (haa : ∀ i ∈ R.biUnion A.scope, a i = a' i) :
    a ∈ A.avoid R ↔ a' ∈ A.avoid R := by
  have hEq : ∀ e ∈ R, a ∈ A.bad e ↔ a' ∈ A.bad e := by
    intro e he
    exact hlocal e a a' (fun i hi => haa i (Finset.mem_biUnion.mpr ⟨e, he, hi⟩))
  simp only [AvoidanceData.avoid, Finset.mem_filter, Finset.mem_univ, true_and]
  constructor
  · intro h e he hb
    exact h e he ((hEq e he).mpr hb)
  · intro h e he hb
    exact h e he ((hEq e he).mp hb)

theorem product_query_outside
    (A : AvoidanceData (fun a : I → O => a) (fun i : I => i) safe)
    (q : I → FinLaw O) (hbase : A.base = FinLaw.pi q)
    (hlocal : ∀ e a a', (∀ i ∈ A.scope e, a i = a' i) →
      (a ∈ A.bad e ↔ a' ∈ A.bad e))
    (S : Finset I) (o : I → O) (R : Finset A.Event)
    (hR : Disjoint R (A.touching S)) :
    A.base.pr (fun a => (∀ i ∈ S, a i = o i) ∧ a ∈ A.avoid R) =
      A.base.pr (fun a => ∀ i ∈ S, a i = o i) *
        A.base.pr (fun a => a ∈ A.avoid R) := by
  rw [hbase]
  apply pi_pr_disjoint q _ _ S (R.biUnion A.scope)
  · intro a a' haa
    constructor <;> intro h i hi
    · rw [← haa i hi]; exact h i hi
    · rw [haa i hi]; exact h i hi
  · exact product_avoid_local A hlocal R
  · simpa only [Finset.image_id'] using
      disjoint_touching_scopes (fun i : I => i) A.scope S R hR

theorem product_nonneighbor
    (A : AvoidanceData (fun a : I → O => a) (fun i : I => i) safe)
    (q : I → FinLaw O) (hbase : A.base = FinLaw.pi q)
    (hlocal : ∀ e a a', (∀ i ∈ A.scope e, a i = a' i) →
      (a ∈ A.bad e ↔ a' ∈ A.bad e))
    (e : A.Event) (R : Finset A.Event) (he : e ∉ R)
    (hR : ∀ f ∈ R, f ∉ A.neighbors e) :
    A.base.pr (fun a => a ∈ A.bad e ∧ a ∈ A.avoid R) =
      A.base.pr (fun a => a ∈ A.bad e) * A.base.pr (fun a => a ∈ A.avoid R) := by
  rw [hbase]
  exact pi_pr_disjoint q _ _ (A.scope e) (R.biUnion A.scope)
    (hlocal e) (product_avoid_local A hlocal R)
    (nonneighbor_scopes A.scope e R he hR)

theorem product_pinned_nonneighbor
    (A : AvoidanceData (fun a : I → O => a) (fun i : I => i) safe)
    (q : I → FinLaw O) (hbase : A.base = FinLaw.pi q)
    (hlocal : ∀ e a a', (∀ i ∈ A.scope e, a i = a' i) →
      (a ∈ A.bad e ↔ a' ∈ A.bad e))
    (e : A.Event) (i : I) (o : O) (R : Finset A.Event) (he : e ∉ R)
    (hR : ∀ f ∈ R, f ∉ A.neighbors e)
    (hBad : i ∉ A.scope e → A.base.pr (fun a => a ∈ A.bad e) ≤ A.pinnedBound e i o)
    (hPin : A.base.pr (fun a => a i = o ∧ a ∈ A.bad e) ≤
      A.pinnedBound e i o * (q i).w o) :
    A.base.pr (fun a => a i = o ∧ a ∈ A.bad e ∧ a ∈ A.avoid R) ≤
      A.pinnedBound e i o * A.base.pr (fun a => a i = o ∧ a ∈ A.avoid R) := by
  rw [hbase] at hBad hPin ⊢
  let V := A.scope e
  let U := R.biUnion A.scope
  have hVU : Disjoint V U := nonneighbor_scopes A.scope e R he hR
  by_cases hi : i ∈ V
  · have h1 := pi_pr_disjoint q
      (fun a => a i = o ∧ a ∈ A.bad e) (fun a => a ∈ A.avoid R) V U
      (by intro a a' haa; exact and_congr (by rw [haa i hi]) (hlocal e a a' haa))
      (product_avoid_local A hlocal R) hVU
    have h2 := pi_pr_disjoint q (fun a => a i = o) (fun a => a ∈ A.avoid R) {i} U
      (by intro a a' haa; rw [haa i (Finset.mem_singleton_self _)])
      (product_avoid_local A hlocal R)
      (Finset.disjoint_left.mpr (by
        intro j hj hj'; rw [Finset.mem_singleton.mp hj] at hj'
        exact Finset.disjoint_left.mp hVU hi hj'))
    rw [product_coordinate q i o] at h2
    simp only [and_assoc] at h1
    rw [h1, h2]
    simpa only [mul_assoc] using mul_le_mul_of_nonneg_right hPin
      (pr_range (FinLaw.pi q) _).1
  · have hdis : Disjoint V (U ∪ {i}) := by
      apply Finset.disjoint_left.mpr
      intro j hj hju
      rcases Finset.mem_union.mp hju with hU | hs
      · exact Finset.disjoint_left.mp hVU hj hU
      · exact hi (by rwa [Finset.mem_singleton.mp hs] at hj)
    have h1 := pi_pr_disjoint q (fun a => a ∈ A.bad e)
      (fun a => a i = o ∧ a ∈ A.avoid R) V (U ∪ {i}) (hlocal e)
      (by
        intro a a' haa
        exact and_congr (by rw [haa i (Finset.mem_union.mpr
          (Or.inr (Finset.mem_singleton_self _)))])
          (product_avoid_local A hlocal R a a'
            (fun j hj => haa j (Finset.mem_union.mpr (Or.inl hj))))) hdis
    have heq : (FinLaw.pi q).pr (fun a => a i = o ∧ a ∈ A.bad e ∧ a ∈ A.avoid R) =
        (FinLaw.pi q).pr (fun a => a ∈ A.bad e ∧ (a i = o ∧ a ∈ A.avoid R)) := by
      congr 1; funext a; exact propext (by tauto)
    rw [heq, h1]
    exact mul_le_mul_of_nonneg_right (hBad hi) (pr_range (FinLaw.pi q) _).1

def capacity_bad (S : Finset I) (b : O) (a : I → O) : Prop := ∀ i ∈ S, a i = b

noncomputable def capacity_pin (q : I → FinLaw O) (S : Finset I) (b : O)
    (i : I) (o : O) : ℝ :=
  if i ∈ S then if o = b then ∏ j ∈ S.erase i, (q j).w b else 0
  else ∏ j ∈ S, (q j).w b

theorem capacity_bad_local (S : Finset I) (b : O) (a a' : I → O)
    (haa : ∀ i ∈ S, a i = a' i) : capacity_bad S b a ↔ capacity_bad S b a' := by
  constructor <;> intro h i hi
  · rw [← haa i hi]; exact h i hi
  · rw [haa i hi]; exact h i hi

theorem capacity_probability (q : I → FinLaw O) (S : Finset I) (b : O) :
    (FinLaw.pi q).pr (capacity_bad S b) = ∏ i ∈ S, (q i).w b :=
  product_cylinder q S (fun _ => b)

theorem capacity_pin_nonneg (q : I → FinLaw O) (S : Finset I) (b : O) (i : I) (o : O) :
    0 ≤ capacity_pin q S b i o := by
  unfold capacity_pin
  split_ifs <;> first | exact Finset.prod_nonneg (fun j _ => (q j).nonneg b) | exact le_rfl

theorem capacity_pin_probability (q : I → FinLaw O) (S : Finset I) (b : O) (i : I) (o : O) :
    (FinLaw.pi q).pr (fun a => a i = o ∧ capacity_bad S b a) =
      capacity_pin q S b i o * (q i).w o := by
  by_cases hi : i ∈ S
  · by_cases ho : o = b
    · subst o
      have heq : (fun a : I → O => a i = b ∧ capacity_bad S b a) = capacity_bad S b := by
        funext a
        exact propext ⟨And.right, fun h => ⟨h i hi, h⟩⟩
      rw [heq, capacity_probability]
      simp only [capacity_pin, hi, if_true]
      rw [← Finset.mul_prod_erase S (fun j => (q j).w b) hi]
      ring
    · have heq : (fun a : I → O => a i = o ∧ capacity_bad S b a) = fun _ => False := by
        funext a
        apply propext
        simp only [iff_false]
        rintro ⟨ha, hS⟩
        exact ho (ha.symm.trans (hS i hi))
      rw [heq]
      simp [FinLaw.pr, capacity_pin, hi, ho]
  · have hd : Disjoint ({i} : Finset I) S := Finset.disjoint_singleton_left.mpr hi
    rw [pi_pr_disjoint q _ _ {i} S
      (by intro a a' haa; rw [haa i (Finset.mem_singleton_self _)])
      (capacity_bad_local S b) hd, product_coordinate, capacity_probability]
    simp only [capacity_pin, hi, if_false]
    ring

theorem capacity_inflated_touch (q : I → FinLaw O) (S : Finset I) (b : O) (i : I)
    (hi : i ∈ S) :
    (2 : ℝ) ^ S.card * (∏ j ∈ S, (q j).w b) ≤
      (q i).w b * ((4 : ℝ) ^ S.card * ∏ j ∈ S.erase i, (q j).w b) := by
  rw [← Finset.mul_prod_erase S (fun j => (q j).w b) hi]
  have hp : (2 : ℝ) ^ S.card ≤ (4 : ℝ) ^ S.card :=
    pow_le_pow_left₀ (by norm_num) (by norm_num) _
  have hm := mul_le_mul_of_nonneg_right hp
    (mul_nonneg ((q i).nonneg b) (Finset.prod_nonneg (s := S.erase i) fun j _ => (q j).nonneg b))
  nlinarith only [hm]

theorem capacity_weighted_charge_sum (q : I → FinLaw O) (S : Finset I) (b : O)
    (i : I) (hi : i ∈ S) (t : ℕ)
    (hsum : (∑ j ∈ S.erase i, 4 * (q j).w b) ≤ (t : ℝ) / 5) :
    (∑ A ∈ (S.powersetCard (t + 1)).filter (fun A => i ∈ A),
      (2 : ℝ) ^ A.card * ∏ j ∈ A, (q j).w b) ≤
      (q i).w b * (4 * (3 / 5 : ℝ) ^ t) := by
  calc
    _ ≤ ∑ A ∈ (S.powersetCard (t + 1)).filter (fun A => i ∈ A),
        (q i).w b * ((4 : ℝ) ^ A.card * ∏ j ∈ A.erase i, (q j).w b) :=
      Finset.sum_le_sum fun A hA => capacity_inflated_touch q A b i (Finset.mem_filter.mp hA).2
    _ = (q i).w b * (∑ A ∈ (S.powersetCard (t + 1)).filter (fun A => i ∈ A),
        (4 : ℝ) ^ A.card * ∏ j ∈ A.erase i, (q j).w b) := (Finset.mul_sum _ _ _).symm
    _ ≤ _ := mul_le_mul_of_nonneg_left
      (capacity_pinned_inflated_bound S (fun j => (q j).w b) i hi t
        (fun j _ => (q j).nonneg b) hsum) ((q i).nonneg b)

variable {Y Star : Type} [Fintype Y] [DecidableEq Y] [Fintype Star]

abbrev CapacityEvent (d : ℕ) (columns : O → Finset Y)
    (bucket : O → Y → Fin d → Finset I) (t : O → Y → Fin d → ℕ) :=
  Σ b : O, Σ y : {y // y ∈ columns b}, Σ j : Fin d,
    {S : Finset I // S ∈ (bucket b y.1 j).powersetCard (t b y.1 j + 1)}

noncomputable def group_data
    (P : GroupBinProblem I O Star Y) (q : I → FinLaw O)
    (columns : O → Finset Y) (bucket : O → Y → Fin P.d → Finset I)
    (t : O → Y → Fin P.d → ℕ) (x : ℝ) :
    AvoidanceData (fun a : I → O => a) (fun i : I => i) P.safe where
  base := FinLaw.pi q
  Event := Star ⊕ CapacityEvent P.d columns bucket t
  eventFin := inferInstance
  eventDec := Classical.decEq _
  bad := fun e => Finset.univ.filter fun a => match e with
    | .inl s => group_star_bad P s a
    | .inr c => capacity_bad c.2.2.2.1 c.1 a
  scope := fun e => match e with
    | .inl s => P.participants s
    | .inr c => c.2.2.2.1
  charge := fun e => match e with
    | .inl _ => x
    | .inr c => 2 * ∏ i ∈ c.2.2.2.1, (q i).w c.1
  pinnedBound := fun e i o => match e with
    | .inl _ => x / 2
    | .inr c => capacity_pin q c.2.2.2.1 c.1 i o
  baseJointRate := 0
  touchRate := Real.rpow (P.d : ℝ) (-2)

theorem group_data_local
    (P : GroupBinProblem I O Star Y) (q : I → FinLaw O)
    (columns : O → Finset Y) (bucket : O → Y → Fin P.d → Finset I)
    (t : O → Y → Fin P.d → ℕ) (x : ℝ)
    (hlocal : ∀ s, DependsOn (P.failureMass s) (P.participants s : Set I))
    (e : (group_data P q columns bucket t x).Event) (a a' : I → O)
    (haa : ∀ i ∈ (group_data P q columns bucket t x).scope e, a i = a' i) :
    a ∈ (group_data P q columns bucket t x).bad e ↔
      a' ∈ (group_data P q columns bucket t x).bad e := by
  cases e with
  | inl s =>
    simpa only [group_data, Finset.mem_filter, Finset.mem_univ, true_and] using
      group_star_bad_local P hlocal s a a' haa
  | inr c =>
    simpa only [group_data, Finset.mem_filter, Finset.mem_univ, true_and] using
      capacity_bad_local c.2.2.2.1 c.1 a a' haa

theorem capacity_event_nonempty
    (d : ℕ) (columns : O → Finset Y) (bucket : O → Y → Fin d → Finset I)
    (t : O → Y → Fin d → ℕ) (c : CapacityEvent d columns bucket t) :
    c.2.2.2.1.Nonempty := by
  apply Finset.card_pos.mp
  rw [(Finset.mem_powersetCard.mp c.2.2.2.2).2]
  omega

theorem capacity_event_probability
    (P : GroupBinProblem I O Star Y) (q : I → FinLaw O)
    (columns : O → Finset Y) (bucket : O → Y → Fin P.d → Finset I)
    (t : O → Y → Fin P.d → ℕ) (x : ℝ) (c : CapacityEvent P.d columns bucket t) :
    (group_data P q columns bucket t x).base.pr
      (fun a => a ∈ (group_data P q columns bucket t x).bad (.inr c)) =
      ∏ i ∈ c.2.2.2.1, (q i).w c.1 := by
  simpa only [group_data, Finset.mem_filter, Finset.mem_univ, true_and] using
    capacity_probability q c.2.2.2.1 c.1

theorem capacity_pin_sum (q : I → FinLaw O) (S : Finset I) (b : O) (i : I)
    (t : ℕ) (hsum : (∑ j ∈ S.erase i, 4 * (q j).w b) ≤ (t : ℝ) / 5) :
    (∑ A ∈ (S.powersetCard (t + 1)).filter (fun A => i ∈ A),
      2 * ∏ j ∈ A.erase i, (q j).w b) ≤ 4 * (3 / 5 : ℝ) ^ t := by
  by_cases hi : i ∈ S
  · calc
      _ ≤ ∑ A ∈ (S.powersetCard (t + 1)).filter (fun A => i ∈ A),
          (4 : ℝ) ^ A.card * ∏ j ∈ A.erase i, (q j).w b := by
        apply Finset.sum_le_sum
        intro A hA
        have hc : 1 ≤ A.card := Finset.one_le_card.mpr ⟨i, (Finset.mem_filter.mp hA).2⟩
        have hp : (2 : ℝ) ≤ 4 ^ A.card := by
          have hh := pow_le_pow_right₀ (by norm_num : (1 : ℝ) ≤ 4) hc
          norm_num only [pow_one] at hh
          linarith
        exact mul_le_mul_of_nonneg_right hp (Finset.prod_nonneg fun j _ => (q j).nonneg b)
      _ ≤ _ := capacity_pinned_inflated_bound S (fun j => (q j).w b) i hi t
        (fun j _ => (q j).nonneg b) hsum
  · have hempty : (S.powersetCard (t + 1)).filter (fun A => i ∈ A) = ∅ := by
      apply Finset.eq_empty_iff_forall_notMem.mpr
      intro A hA
      obtain ⟨hAS, hiA⟩ := Finset.mem_filter.mp hA
      exact hi ((Finset.mem_powersetCard.mp hAS).1 hiA)
    rw [hempty, Finset.sum_empty]
    positivity

theorem subtype_sum {α : Type*} [Fintype α] [DecidableEq α] (S : Finset α) (f : α → ℝ) :
    (∑ a : {a // a ∈ S}, f a.1) = ∑ a ∈ S, f a := by
  simpa using (Finset.sum_subtype_eq_sum_filter (s := (Finset.univ : Finset α))
    (p := fun a => a ∈ S) (f := f))

theorem capacity_simple_charge_sum (q : I → FinLaw O) (S : Finset I) (b : O) (i : I)
    (t : ℕ) (hsum : (∑ j ∈ S.erase i, 4 * (q j).w b) ≤ (t : ℝ) / 5) :
    (∑ A ∈ (S.powersetCard (t + 1)).filter (fun A => i ∈ A),
      2 * ∏ j ∈ A, (q j).w b) ≤ (q i).w b * (4 * (3 / 5 : ℝ) ^ t) := by
  have heq : (∑ A ∈ (S.powersetCard (t + 1)).filter (fun A => i ∈ A),
      2 * ∏ j ∈ A, (q j).w b) =
      (q i).w b * (∑ A ∈ (S.powersetCard (t + 1)).filter (fun A => i ∈ A),
        2 * ∏ j ∈ A.erase i, (q j).w b) := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro A hA
    rw [← Finset.mul_prod_erase A (fun j => (q j).w b) (Finset.mem_filter.mp hA).2]
    ring
  rw [heq]
  exact mul_le_mul_of_nonneg_left (capacity_pin_sum q S b i t hsum) ((q i).nonneg b)

theorem capacity_touch_charge
    (d : ℕ) (q : I → FinLaw O) (columns : O → Finset Y)
    (bucket : O → Y → Fin d → Finset I) (t : O → Y → Fin d → ℕ)
    (G : ℝ) (hG : 0 ≤ G) (hcol : ∀ b, (columns b).card ≤ d)
    (hbudget : ∀ b y j i, (∑ g ∈ (bucket b y j).erase i, 4 * (q g).w b) ≤
      (t b y j : ℝ) / 5)
    (hsmall : ∀ b y j, 4 * (3 / 5 : ℝ) ^ t b y j ≤ G)
    (i : I) :
    (∑ c : CapacityEvent d columns bucket t,
      if i ∈ c.2.2.2.1 then 2 * ∏ g ∈ c.2.2.2.1, (q g).w c.1 else 0) ≤
      (d : ℝ) ^ 2 * G := by
  rw [Fintype.sum_sigma]
  calc
    _ ≤ ∑ b : O, (q i).w b * ((d : ℝ) ^ 2 * G) := by
      apply Finset.sum_le_sum
      intro b _
      rw [Fintype.sum_sigma]
      have hy : ∀ y : {y // y ∈ columns b},
          (∑ c : Σ j : Fin d, {A : Finset I // A ∈
            (bucket b y.1 j).powersetCard (t b y.1 j + 1)},
            if i ∈ c.2.1 then 2 * ∏ g ∈ c.2.1, (q g).w b else 0) ≤
          (d : ℝ) * ((q i).w b * G) := by
        intro y
        rw [Fintype.sum_sigma]
        calc
          _ ≤ ∑ _j : Fin d, (q i).w b * G := by
            apply Finset.sum_le_sum
            intro j _
            dsimp only
            rw [subtype_sum ((bucket b y.1 j).powersetCard (t b y.1 j + 1))
              (fun A => if i ∈ A then 2 * ∏ g ∈ A, (q g).w b else 0), ← Finset.sum_filter]
            exact (capacity_simple_charge_sum q _ b i _ (hbudget b y.1 j i)).trans
              (mul_le_mul_of_nonneg_left (hsmall b y.1 j) ((q i).nonneg b))
          _ = _ := by simp
      have hh := Finset.sum_le_sum (s := Finset.univ) (fun y _ => hy y)
      simp only [Finset.sum_const, nsmul_eq_mul, Finset.card_univ, Fintype.card_coe] at hh
      have hc : ((columns b).card : ℝ) ≤ d := by exact_mod_cast hcol b
      have hm := mul_le_mul_of_nonneg_right hc
        (mul_nonneg (Nat.cast_nonneg (α := ℝ) d) (mul_nonneg ((q i).nonneg b) hG))
      exact hh.trans (by nlinarith only [hm])
    _ = _ := by rw [← Finset.sum_mul, (q i).sum_one, one_mul]

theorem capacity_touch_pin
    (d : ℕ) (q : I → FinLaw O) (columns : O → Finset Y)
    (bucket : O → Y → Fin d → Finset I) (t : O → Y → Fin d → ℕ)
    (G : ℝ) (hG : 0 ≤ G) (hcol : ∀ b, (columns b).card ≤ d)
    (hbudget : ∀ b y j i, (∑ g ∈ (bucket b y j).erase i, 4 * (q g).w b) ≤
      (t b y j : ℝ) / 5)
    (hsmall : ∀ b y j, 4 * (3 / 5 : ℝ) ^ t b y j ≤ G)
    (i : I) (o : O) :
    (∑ c : CapacityEvent d columns bucket t,
      if i ∈ c.2.2.2.1 then 2 * capacity_pin q c.2.2.2.1 c.1 i o else 0) ≤
      (d : ℝ) ^ 2 * G := by
  rw [Fintype.sum_sigma]
  calc
    _ ≤ ∑ b : O, if o = b then (d : ℝ) ^ 2 * G else 0 := by
      apply Finset.sum_le_sum
      intro b _
      by_cases ho : o = b
      · rw [if_pos ho, Fintype.sum_sigma]
        have hy : ∀ y : {y // y ∈ columns b},
            (∑ c : Σ j : Fin d, {A : Finset I // A ∈
              (bucket b y.1 j).powersetCard (t b y.1 j + 1)},
              if i ∈ c.2.1 then 2 * capacity_pin q c.2.1 b i o else 0) ≤ (d : ℝ) * G := by
          intro y
          rw [Fintype.sum_sigma]
          calc
            _ ≤ ∑ _j : Fin d, G := by
              apply Finset.sum_le_sum
              intro j _
              dsimp only
              rw [subtype_sum ((bucket b y.1 j).powersetCard (t b y.1 j + 1))
                (fun A => if i ∈ A then 2 * capacity_pin q A b i o else 0)]
              have heq : (∑ A ∈ (bucket b y.1 j).powersetCard (t b y.1 j + 1),
                  if i ∈ A then 2 * capacity_pin q A b i o else 0) =
                  ∑ A ∈ ((bucket b y.1 j).powersetCard (t b y.1 j + 1)).filter
                    (fun A => i ∈ A), 2 * ∏ g ∈ A.erase i, (q g).w b := by
                rw [Finset.sum_filter]
                apply Finset.sum_congr rfl
                intro A _
                by_cases hi : i ∈ A <;> simp [capacity_pin, hi, ho]
              rw [heq]
              exact (capacity_pin_sum q _ b i _ (hbudget b y.1 j i)).trans (hsmall b y.1 j)
            _ = _ := by simp
        have hh := Finset.sum_le_sum (s := Finset.univ) (fun y _ => hy y)
        simp only [Finset.sum_const, nsmul_eq_mul, Finset.card_univ, Fintype.card_coe] at hh
        have hc : ((columns b).card : ℝ) ≤ d := by exact_mod_cast hcol b
        have hm := mul_le_mul_of_nonneg_right hc (mul_nonneg (Nat.cast_nonneg (α := ℝ) d) hG)
        exact hh.trans (by nlinarith only [hm])
      · rw [if_neg ho]
        apply le_of_eq
        apply Finset.sum_eq_zero
        intro c _
        simp only [capacity_pin]
        split_ifs <;> simp_all
    _ = _ := by simp

set_option maxHeartbeats 800000 in
theorem group_certificates
    (P : GroupBinProblem I O Star Y) (q : I → FinLaw O)
    (columns : O → Finset Y) (bucket : O → Y → Fin P.d → Finset I)
    (t : O → Y → Fin P.d → ℕ) (x G : ℝ)
    (hd : 2 ≤ P.d) (hG : 0 ≤ G) (hGbudget : (P.d : ℝ) ^ 2 * G ≤ Real.rpow (P.d : ℝ) (-2) / 16)
    (hrate : Real.log ((1 + Real.rpow (P.d : ℝ) (-0.1)) /
      (1 - Real.rpow (P.d : ℝ) (-0.1))) + Real.rpow (P.d : ℝ) (-2) ≤ Real.rpow (P.d : ℝ) (-0.05))
    (hρ : Real.rpow (P.d : ℝ) (-0.1) ≤ 1 / 3)
    (hq : RelativePerturbation P.target q (Real.rpow (P.d : ℝ) (-0.1)))
    (hlocal : ∀ s, DependsOn (P.failureMass s) (P.participants s : Set I))
    (hcover : ∀ a, (FinLaw.pi q).w a ≠ 0 →
      (∀ e, a ∉ (group_data P q columns bucket t x).bad e) → P.safe a)
    (hx : 0 ≤ x ∧ x ≤ 1 / 2)
    (hstar : ∀ s, (FinLaw.pi q).pr (group_star_bad P s) ≤ x / 2)
    (hstarPin : ∀ s i o, (FinLaw.pi q).pr (fun a => a i = o ∧ group_star_bad P s a) ≤
      (x / 2) * (q i).w o)
    (hstarOne : ∀ i, (∑ s ∈ Finset.univ.filter (fun s => i ∈ P.participants s), x) ≤
      Real.rpow (P.d : ℝ) (-2) / 16)
    (hscope : ∀ e, ((group_data P q columns bucket t x).scope e).card ≤ P.d)
    (hcol : ∀ b, (columns b).card ≤ P.d)
    (hbudget : ∀ b y j i, (∑ g ∈ (bucket b y j).erase i, 4 * (q g).w b) ≤ (t b y j : ℝ) / 5)
    (hsmall : ∀ b y j, 4 * (3 / 5 : ℝ) ^ t b y j ≤ G) :
    ∃ A : AvoidanceData (fun a : I → O => a) (fun i : I => i) P.safe,
      A.base = FinLaw.pi q ∧ AvoidanceHypotheses A P.target q (fun _ => True)
        (Real.rpow (P.d : ℝ) (-0.1)) (Real.rpow (P.d : ℝ) (-2))
        (Real.rpow (P.d : ℝ) (-0.05)) := by
  let A := group_data P q columns bucket t x
  let η := Real.rpow (P.d : ℝ) (-2)
  have hdp : (0 : ℝ) < P.d := by exact_mod_cast (by omega : 0 < P.d)
  have hη : 0 < η := Real.rpow_pos_of_pos hdp _
  have hηquarter : η ≤ 1 / 4 := by
    calc
      _ ≤ Real.rpow (2 : ℝ) (-2) := Real.rpow_le_rpow_of_nonpos (by norm_num)
        (by exact_mod_cast hd) (by norm_num)
      _ = _ := by norm_num [Real.rpow_neg, Real.rpow_natCast]
  have hchargeNonneg : ∀ e, 0 ≤ A.charge e := by
    intro e
    cases e with
    | inl s => exact hx.1
    | inr c => exact mul_nonneg (by norm_num) (Finset.prod_nonneg fun g _ => (q g).nonneg c.1)
  have hOne : ∀ i, (∑ e ∈ Finset.univ.filter (fun e => i ∈ A.scope e), A.charge e) ≤ η / 8 := by
    intro i
    rw [Finset.sum_filter]
    change (∑ e : Star ⊕ CapacityEvent P.d columns bucket t, if i ∈ A.scope e then A.charge e else 0) ≤ η / 8
    rw [Fintype.sum_sum_type]
    change (∑ s : Star, if i ∈ P.participants s then x else 0) +
      (∑ c : CapacityEvent P.d columns bucket t,
        if i ∈ c.2.2.2.1 then 2 * ∏ g ∈ c.2.2.2.1, (q g).w c.1 else 0) ≤ η / 8
    have hs := hstarOne i
    rw [Finset.sum_filter] at hs
    have hc := (capacity_touch_charge P.d q columns bucket t G hG hcol hbudget hsmall i).trans hGbudget
    dsimp only [η] at *
    linarith
  have hTouch : ∀ S : Finset I, (∑ e ∈ A.touching S, A.charge e) ≤ (S.card : ℝ) * (η / 8) :=
    fun S => scope_touching_sum A.scope A.charge (η / 8) hchargeNonneg hOne S
  have hCharge : ∀ e, 0 ≤ A.charge e ∧ A.charge e ≤ 1 / 2 := by
    intro e
    refine ⟨hchargeNonneg e, ?_⟩
    cases e with
    | inl s => exact hx.2
    | inr c =>
      obtain ⟨i, hi⟩ := capacity_event_nonempty P.d columns bucket t c
      have hm : 2 * (∏ g ∈ c.2.2.2.1, (q g).w c.1) ≤
          ∑ f : CapacityEvent P.d columns bucket t,
            if i ∈ f.2.2.2.1 then 2 * ∏ g ∈ f.2.2.2.1, (q g).w f.1 else 0 := by
        have hh := Finset.single_le_sum (s := Finset.univ)
          (f := fun f : CapacityEvent P.d columns bucket t =>
            if i ∈ f.2.2.2.1 then 2 * ∏ g ∈ f.2.2.2.1, (q g).w f.1 else 0)
          (by
            intro f _
            split_ifs
            · exact mul_nonneg (by norm_num) (Finset.prod_nonneg fun g _ => (q g).nonneg f.1)
            · exact le_rfl) (Finset.mem_univ c)
        simpa only [if_pos hi] using hh
      have hc := (capacity_touch_charge P.d q columns bucket t G hG hcol hbudget hsmall i).trans hGbudget
      exact (hm.trans hc).trans (by linarith)
  have hNeighbor : ∀ e, (∑ f ∈ A.neighbors e, A.charge f) ≤ 1 / 2 := by
    intro e
    have hs := scope_neighbor_sum A.scope A.charge (η / 8) hchargeNonneg hOne e
    have hc : ((A.scope e).card : ℝ) ≤ P.d := by exact_mod_cast hscope e
    have hm := mul_le_mul_of_nonneg_right hc (by positivity : 0 ≤ η / 8)
    have hde : (P.d : ℝ) * η ≤ 1 := by
      dsimp only [η]
      norm_num [Real.rpow_neg, Real.rpow_natCast]
      have hd1 : (1 : ℝ) ≤ P.d := by exact_mod_cast (by omega : 1 ≤ P.d)
      rw [inv_eq_one_div, mul_one_div, div_le_one (sq_pos_of_pos hdp)]
      nlinarith
    exact (hs.trans hm).trans (by nlinarith only [hde])
  have hRecip : ∀ e, (∏ f ∈ A.neighbors e, (1 - A.charge f)⁻¹) ≤ 2 := by
    intro e
    have hh := avoidance_reciprocal_bound (A.neighbors e) A.charge (1 / 2)
      (by norm_num) (fun f _ => ⟨(hCharge f).1, by linarith [(hCharge f).2]⟩) (hNeighbor e)
    norm_num only [inv_div, inv_one, div_one] at hh
    exact hh
  have hBad : ∀ e, A.base.pr (fun a => a ∈ A.bad e) ≤ A.charge e / 2 := by
    intro e
    cases e with
    | inl s => simpa only [A, group_data, Finset.mem_filter, Finset.mem_univ, true_and] using hstar s
    | inr c => rw [capacity_event_probability]; dsimp only [A, group_data]; linarith
  have hPin : ∀ e i o, A.base.pr (fun a => a i = o ∧ a ∈ A.bad e) ≤ A.pinnedBound e i o * (q i).w o := by
    intro e i o
    cases e with
    | inl s => simpa only [A, group_data, Finset.mem_filter, Finset.mem_univ, true_and] using hstarPin s i o
    | inr c =>
      simpa only [A, group_data, Finset.mem_filter, Finset.mem_univ, true_and] using
        (capacity_pin_probability q c.2.2.2.1 c.1 i o).le
  refine ⟨A, rfl, {
    rho_range := ⟨Real.rpow_pos_of_pos hdp _, hρ⟩
    eta_range := ⟨hη.le, by linarith⟩
    perturbation := hq
    base_marginals := product_coordinate q
    safe_cover := hcover
    charge_range := fun e => ⟨(hCharge e).1, by linarith [(hCharge e).2]⟩
    nonneighbor := fun e R he hR => (product_nonneighbor A q rfl (group_data_local P q columns bucket t x hlocal) e R he hR).le
    charge_dominates := ?_
    pinned_nonneighbor := ?_
    pinned_outside := ?_
    pinned_bounds_nonneg := ?_
    pinned_touch_budget := ?_
    singleton_cost := ?_
    base_joint := ?_
    query_outside := ?_
    joint_cost := ?_
    rate_budget := ?_ }⟩
  · intro e
    have hl := avoidance_product_lower (A.neighbors e) A.charge
      (fun f _ => ⟨(hCharge f).1, by linarith [(hCharge f).2]⟩)
    have hp : 1 / 2 ≤ ∏ f ∈ A.neighbors e, (1 - A.charge f) := by linarith [hNeighbor e]
    have hm := mul_le_mul_of_nonneg_left hp (hCharge e).1
    exact (hBad e).trans (by nlinarith only [hm])
  · intro e i o R he hR
    apply product_pinned_nonneighbor A q rfl (group_data_local P q columns bucket t x hlocal) e i o R he hR
    · intro hi
      cases e with
      | inl s => exact hBad (.inl s)
      | inr c =>
        rw [capacity_event_probability]
        change i ∉ c.2.2.2.1 at hi
        simp only [A, group_data, capacity_pin, hi, if_false, le_refl]
    · exact hPin e i o
  · intro i o R hR
    have hh := product_query_outside A q rfl (group_data_local P q columns bucket t x hlocal) {i} (fun _ => o) R hR
    simp only [Finset.mem_singleton, forall_eq] at hh
    rw [show A.base.pr (fun a => a i = o) = (q i).w o from product_coordinate q i o] at hh
    exact hh
  · intro e i o
    cases e with
    | inl s => change 0 ≤ x / 2; exact div_nonneg hx.1 (by norm_num)
    | inr c => exact capacity_pin_nonneg q c.2.2.2.1 c.1 i o
  · intro i o
    have hm : (∑ e ∈ A.touching {i}, A.pinnedBound e i o *
        ∏ f ∈ A.neighbors e, (1 - A.charge f)⁻¹) ≤
        ∑ e ∈ A.touching {i}, 2 * A.pinnedBound e i o := by
      apply Finset.sum_le_sum
      intro e _
      have hn : 0 ≤ A.pinnedBound e i o := by
        cases e with
        | inl s => change 0 ≤ x / 2; exact div_nonneg hx.1 (by norm_num)
        | inr c => exact capacity_pin_nonneg q c.2.2.2.1 c.1 i o
      simpa only [mul_comm] using mul_le_mul_of_nonneg_left (hRecip e) hn
    apply hm.trans
    rw [AvoidanceData.touching, Finset.sum_filter]
    change (∑ e : Star ⊕ CapacityEvent P.d columns bucket t,
      if (∃ j ∈ ({i} : Finset I), j ∈ A.scope e) then 2 * A.pinnedBound e i o else 0) ≤ η
    rw [Fintype.sum_sum_type]
    simp only [Finset.mem_singleton, exists_eq_left]
    change (∑ s : Star, if i ∈ P.participants s then 2 * (x / 2) else 0) +
      (∑ c : CapacityEvent P.d columns bucket t,
        if i ∈ c.2.2.2.1 then 2 * capacity_pin q c.2.2.2.1 c.1 i o else 0) ≤ η
    have hs := hstarOne i
    rw [Finset.sum_filter] at hs
    have hc := (capacity_touch_pin P.d q columns bucket t G hG hcol hbudget hsmall i o).trans hGbudget
    have htwo : 2 * (x / 2) = x := by ring
    simp only [htwo]
    dsimp only [η] at *
    linarith
  · intro i
    apply avoidance_singleton_cost (A.touching {i}) A.charge η ⟨hη.le, by linarith⟩
      (fun e _ => ⟨(hCharge e).1, by linarith [(hCharge e).2]⟩)
    have hh := hTouch {i}
    simp only [Finset.card_singleton, Nat.cast_one, one_mul] at hh
    linarith
  · intro S o _
    change (FinLaw.pi q).pr (fun a => ∀ i ∈ S, a i = o i) ≤
      Real.exp (0 * (S.card : ℝ)) * ∏ i ∈ S, (q i).w (o i)
    rw [product_cylinder q S o]
    simp only [zero_mul, Real.exp_zero, one_mul, le_refl]
  · intro S o R _ hR
    exact product_query_outside A q rfl (group_data_local P q columns bucket t x hlocal) S o R hR
  · intro S _
    apply (avoidance_joint_cost (A.touching S) A.charge (fun e _ => hCharge e)).trans
    apply Real.exp_le_exp.mpr
    have hh := hTouch S
    change 2 * _ ≤ η * S.card
    nlinarith [Nat.cast_nonneg (α := ℝ) S.card]
  · simpa only [A, group_data, zero_add] using hrate

theorem group_star_charge_room (d h : ℕ) (ε : ℝ) (hd : 2 ≤ d) (hε : 0 < ε)
    (hroom : 16 * (d : ℝ) ^ 2 * (h + 1 : ℝ) ^ 2 * Real.rpow ε (1 / 16 : ℝ) ≤
      Real.rpow (d : ℝ) (-20)) :
    let x := Real.rpow ε (1 / 16 : ℝ) + Real.rpow (d : ℝ) (-20)
    0 ≤ x ∧ x ≤ 1 / 2 ∧ (d : ℝ) * x ≤ Real.rpow (d : ℝ) (-2) / 16 ∧
      4 * Real.rpow ε (1 / 8 : ℝ) + 2 * (d : ℝ) ^ 2 * Real.rpow (d : ℝ) (-40) ≤ x / 2 := by
  have hd' : (2 : ℝ) ≤ d := by exact_mod_cast hd
  have hp : (0 : ℝ) < d := by linarith
  have epos : 0 ≤ Real.rpow ε (1 / 16 : ℝ) := (Real.rpow_pos_of_pos hε _).le
  have zpos : 0 ≤ Real.rpow (d : ℝ) (-20) := (Real.rpow_pos_of_pos hp _).le
  have hfac : 1 ≤ 16 * (d : ℝ) ^ 2 * (h + 1 : ℝ) ^ 2 := by
    have hh : (1 : ℝ) ≤ (h + 1 : ℝ) ^ 2 := by nlinarith [Nat.cast_nonneg (α := ℝ) h]
    nlinarith
  have he : Real.rpow ε (1 / 16 : ℝ) ≤ Real.rpow (d : ℝ) (-20) := by
    nlinarith only [hroom, mul_le_mul_of_nonneg_right hfac epos]
  have hsmall (a : ℝ) (ha : a ≤ 0) : Real.rpow (d : ℝ) a ≤ Real.rpow (2 : ℝ) a :=
    Real.rpow_le_rpow_of_nonpos (by norm_num) hd' ha
  have hz : Real.rpow (d : ℝ) (-20) ≤ 1 / 16 := by
    exact (hsmall (-20) (by norm_num)).trans (by norm_num [Real.rpow_neg, Real.rpow_natCast])
  have h17 : Real.rpow (d : ℝ) (-17) ≤ 1 / 32 := by
    exact (hsmall (-17) (by norm_num)).trans (by norm_num [Real.rpow_neg, Real.rpow_natCast])
  have h18 : Real.rpow (d : ℝ) (-18) ≤ 1 / 8 := by
    exact (hsmall (-18) (by norm_num)).trans (by norm_num [Real.rpow_neg, Real.rpow_natCast])
  have hm (a b : ℝ) : Real.rpow (d : ℝ) a * Real.rpow (d : ℝ) b =
      Real.rpow (d : ℝ) (a + b) := (Real.rpow_add hp a b).symm
  have hdecay : 2 * Real.rpow (d : ℝ) (-19) ≤ Real.rpow (d : ℝ) (-2) / 16 := by
    have hh := mul_le_mul_of_nonneg_right h17 (rpow_nonneg hp.le (-2))
    rw [hm] at hh
    norm_num only at hh
    linarith
  have hdx : (d : ℝ) * (Real.rpow ε (1 / 16 : ℝ) + Real.rpow (d : ℝ) (-20)) ≤
      Real.rpow (d : ℝ) (-2) / 16 := by
    have hh := mul_le_mul_of_nonneg_left he hp.le
    have hid : (d : ℝ) * Real.rpow (d : ℝ) (-20) = Real.rpow (d : ℝ) (-19) := by
      convert hm 1 (-20) using 1 <;> norm_num
    rw [hid] at hh
    nlinarith only [hh, hid, hdecay]
  have hsq : Real.rpow ε (1 / 16 : ℝ) * Real.rpow ε (1 / 16 : ℝ) = Real.rpow ε (1 / 8 : ℝ) := by
    convert (Real.rpow_add hε (1 / 16 : ℝ) (1 / 16 : ℝ)).symm using 1 <;> norm_num
  have hrepeat : 2 * (d : ℝ) ^ 2 * Real.rpow (d : ℝ) (-40) ≤ Real.rpow (d : ℝ) (-20) / 4 := by
    have hh := mul_le_mul_of_nonneg_right h18 zpos
    rw [hm] at hh
    have hid : (d : ℝ) ^ 2 * Real.rpow (d : ℝ) (-40) = Real.rpow (d : ℝ) (-38) := by
      rw [← Real.rpow_natCast]
      convert hm 2 (-40) using 1 <;> norm_num
    norm_num only at hh
    rw [mul_assoc, hid]
    linarith
  dsimp only
  refine ⟨add_nonneg epos zpos, by linarith, hdx, ?_⟩
  rw [← hsq]
  have hMarkov := mul_le_mul_of_nonneg_right (he.trans hz) epos
  nlinarith only [hMarkov, hrepeat, epos, zpos]

noncomputable def bucket_width (d : ℕ) (j : Fin d) : ℝ :=
  Real.rpow (d : ℝ) (-0.5) / (2 : ℝ) ^ (j : ℕ)

noncomputable def dyadic_bucket (P : GroupBinProblem I O Star Y)
    (index : I → O → Y → Fin P.d) (b : O) (y : Y) (j : Fin P.d) : Finset I :=
  Finset.univ.filter fun i => P.contribution i b y ≠ 0 ∧ index i b y = j

noncomputable def bucket_mean (P : GroupBinProblem I O Star Y)
    (index : I → O → Y → Fin P.d) (b : O) (y : Y) (j : Fin P.d) : ℝ :=
  ∑ i ∈ dyadic_bucket P index b y j, (P.target i).w b * P.contribution i b y

noncomputable def bucket_ratio (P : GroupBinProblem I O Star Y)
    (index : I → O → Y → Fin P.d) (b : O) (y : Y) (j : Fin P.d) : ℝ :=
  80 * bucket_mean P index b y j / bucket_width P.d j +
    (1 / 100 : ℝ) * Real.rpow (P.d : ℝ) 0.5

theorem bucket_width_pos (d : ℕ) (hd : 0 < d) (j : Fin d) : 0 < bucket_width d j := by
  unfold bucket_width
  apply div_pos (Real.rpow_pos_of_pos (by exact_mod_cast hd) _)
  positivity

theorem dyadic_index_exists (P : GroupBinProblem I O Star Y) (hd : 1 ≤ P.d)
    (hcap : ∀ i b y, P.contribution i b y ≤ Real.rpow (P.d : ℝ) (-0.5))
    (hmin : ∀ i b y, P.contribution i b y ≠ 0 → 1 / (P.d : ℝ) ≤ P.contribution i b y) :
    ∃ index : I → O → Y → Fin P.d, ∀ i b y, P.contribution i b y ≠ 0 →
      bucket_width P.d (index i b y) / 2 ≤ P.contribution i b y ∧
      P.contribution i b y ≤ bucket_width P.d (index i b y) := by
  have hdp : (0 : ℝ) < P.d := by exact_mod_cast (by omega : 0 < P.d)
  have hδ : 0 < Real.rpow (P.d : ℝ) (-0.5) ∧ Real.rpow (P.d : ℝ) (-0.5) ≤ 1 :=
    ⟨Real.rpow_pos_of_pos hdp _, Real.rpow_le_one_of_one_le_of_nonpos
      (by exact_mod_cast hd) (by norm_num)⟩
  have hex : ∀ i b y, ∃ j : Fin P.d, P.contribution i b y ≠ 0 →
      bucket_width P.d j / 2 ≤ P.contribution i b y ∧ P.contribution i b y ≤ bucket_width P.d j := by
    intro i b y
    by_cases hu : P.contribution i b y = 0
    · exact ⟨⟨0, by omega⟩, by simp [hu]⟩
    · obtain ⟨j, hj, hlo, hhi⟩ := capacity_dyadic_bucket_cover P.d _ _ hd hδ ⟨hmin i b y hu, hcap i b y⟩
      refine ⟨⟨j, hj⟩, fun _ => ⟨?_, hhi⟩⟩
      have heq : bucket_width P.d ⟨j, hj⟩ / 2 = Real.rpow (P.d : ℝ) (-0.5) / (2 : ℝ) ^ (j + 1) := by
        unfold bucket_width
        rw [pow_succ, div_div]
      rw [heq]
      exact hlo.le
  choose index hindex using hex
  exact ⟨index, hindex⟩

theorem bucket_mean_nonneg (P : GroupBinProblem I O Star Y)
    (index : I → O → Y → Fin P.d)
    (hu : ∀ i b y, 0 ≤ P.contribution i b y) (b : O) (y : Y) (j : Fin P.d) :
    0 ≤ bucket_mean P index b y j :=
  Finset.sum_nonneg fun i _ => mul_nonneg ((P.target i).nonneg b) (hu i b y)

theorem bucket_mean_sum (P : GroupBinProblem I O Star Y)
    (index : I → O → Y → Fin P.d) (b : O) (y : Y) :
    (∑ j : Fin P.d, bucket_mean P index b y j) = ∑ i, (P.target i).w b * P.contribution i b y := by
  simp only [bucket_mean, dyadic_bucket, Finset.sum_filter]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i _
  by_cases hu : P.contribution i b y = 0
  · simp [hu]
  · simp [hu]

theorem nominal_column_sum (P : GroupBinProblem I O Star Y) (y : Y) :
    P.nominalColumnLoad y = ∑ i, ∑ b, (P.target i).w b * P.contribution i b y := by
  unfold GroupBinProblem.nominalColumnLoad GroupBinProblem.independentLaw GroupBinProblem.columnLoad FinLaw.E
  simp_rw [Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i _
  exact pi_coordinate_E P.target i (fun b => P.contribution i b y)

theorem bucket_mean_le_nominal (P : GroupBinProblem I O Star Y)
    (index : I → O → Y → Fin P.d) (hu : ∀ i b y, 0 ≤ P.contribution i b y)
    (b : O) (y : Y) (j : Fin P.d) : bucket_mean P index b y j ≤ P.nominalColumnLoad y := by
  rw [nominal_column_sum]
  calc
    _ ≤ ∑ i, (P.target i).w b * P.contribution i b y :=
      Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _)
        (fun i _ _ => mul_nonneg ((P.target i).nonneg b) (hu i b y))
    _ ≤ _ := Finset.sum_le_sum fun i _ => Finset.single_le_sum
      (fun b _ => mul_nonneg ((P.target i).nonneg b) (hu i b y)) (Finset.mem_univ b)

theorem bucket_ratio_nonneg (P : GroupBinProblem I O Star Y) (hd : 0 < P.d)
    (index : I → O → Y → Fin P.d) (hu : ∀ i b y, 0 ≤ P.contribution i b y)
    (b : O) (y : Y) (j : Fin P.d) : 0 ≤ bucket_ratio P index b y j := by
  unfold bucket_ratio
  exact add_nonneg (div_nonneg (mul_nonneg (by norm_num) (bucket_mean_nonneg P index hu b y j))
    (bucket_width_pos P.d hd j).le) (mul_nonneg (by norm_num) (rpow_nonneg (Nat.cast_nonneg P.d) _))

theorem bucket_ratio_lower (P : GroupBinProblem I O Star Y) (hd : (10 ^ 100 : ℕ) ≤ P.d)
    (index : I → O → Y → Fin P.d) (hu : ∀ i b y, 0 ≤ P.contribution i b y)
    (b : O) (y : Y) (j : Fin P.d) :
    Real.rpow (P.d : ℝ) 0.4 ≤ (⌊bucket_ratio P index b y j⌋₊ : ℝ) := by
  apply capacity_size_lower P.d _ hd
  unfold bucket_ratio
  have hn : 0 ≤ 80 * bucket_mean P index b y j / bucket_width P.d j :=
    div_nonneg (mul_nonneg (by norm_num) (bucket_mean_nonneg P index hu b y j))
      (bucket_width_pos P.d (by omega) j).le
  linarith

theorem bucket_ratio_budget (P : GroupBinProblem I O Star Y) (hd : (10 ^ 100 : ℕ) ≤ P.d)
    (index : I → O → Y → Fin P.d) (hu : ∀ i b y, 0 ≤ P.contribution i b y)
    (hindex : ∀ i b y, P.contribution i b y ≠ 0 →
      bucket_width P.d (index i b y) / 2 ≤ P.contribution i b y ∧
      P.contribution i b y ≤ bucket_width P.d (index i b y))
    (q : I → FinLaw O) (hq : ∀ i b, (q i).w b ≤ 2 * (P.target i).w b)
    (b : O) (y : Y) (j : Fin P.d) (i : I) :
    (∑ g ∈ (dyadic_bucket P index b y j).erase i, 4 * (q g).w b) ≤
      (⌊bucket_ratio P index b y j⌋₊ : ℝ) / 5 := by
  have hp : 0 < bucket_width P.d j := bucket_width_pos P.d (by omega) j
  have hmean := capacity_bucket_mean_bound (dyadic_bucket P index b y j)
    (fun g => (P.target g).w b) (fun g => (q g).w b) (fun g => P.contribution g b y)
    (bucket_width P.d j) (bucket_mean P index b y j) hp
    (fun g _ => (P.target g).nonneg b) (fun g _ => ⟨(q g).nonneg b, hq g b⟩)
    (by
      intro g hg
      obtain ⟨hcon, hgj⟩ := (Finset.mem_filter.mp hg).2
      simpa only [hgj] using (hindex g b y hcon).1) (le_refl _)
  have hbase : 1 ≤ (1 / 100 : ℝ) * Real.rpow (P.d : ℝ) 0.5 := by
    have hh := capacity_size_lower P.d ((1 / 100 : ℝ) * Real.rpow (P.d : ℝ) 0.5) hd (le_refl _)
    have hl := Nat.floor_le (mul_nonneg (by norm_num : (0 : ℝ) ≤ 1 / 100) (rpow_nonneg (Nat.cast_nonneg P.d) 0.5))
    have h1 : 1 ≤ Real.rpow (P.d : ℝ) 0.4 := Real.one_le_rpow
      (by exact_mod_cast (by omega : 1 ≤ P.d)) (by norm_num)
    linarith
  have hfloor := Nat.sub_one_lt_floor (bucket_ratio P index b y j)
  have hratio : 80 * bucket_mean P index b y j / bucket_width P.d j ≤
      (⌊bucket_ratio P index b y j⌋₊ : ℝ) := by
    unfold bucket_ratio at hfloor ⊢
    linarith
  have herase : (∑ g ∈ (dyadic_bucket P index b y j).erase i, 4 * (q g).w b) ≤
      ∑ g ∈ dyadic_bucket P index b y j, 4 * (q g).w b :=
    Finset.sum_le_sum_of_subset_of_nonneg (Finset.erase_subset _ _)
      (fun g _ _ => mul_nonneg (by norm_num) ((q g).nonneg b))
  have hid : 80 * bucket_mean P index b y j / bucket_width P.d j =
      5 * (16 * bucket_mean P index b y j / bucket_width P.d j) := by ring
  rw [hid] at hratio
  exact (herase.trans hmean).trans (by linarith only [hratio])

theorem bucket_ratio_upper (P : GroupBinProblem I O Star Y) (hd : 2 ≤ P.d)
    (index : I → O → Y → Fin P.d) (hu : ∀ i b y, 0 ≤ P.contribution i b y)
    (hindex : ∀ i b y, P.contribution i b y ≠ 0 →
      P.contribution i b y ≤ bucket_width P.d (index i b y))
    (hmin : ∀ i b y, P.contribution i b y ≠ 0 → 1 / (P.d : ℝ) ≤ P.contribution i b y)
    (hload : ∀ y, P.nominalColumnLoad y ≤ 1 / 1000)
    (b : O) (y : Y) (j : Fin P.d) (hne : (dyadic_bucket P index b y j).Nonempty) :
    ⌊bucket_ratio P index b y j⌋₊ + 1 ≤ P.d := by
  have hp : (0 : ℝ) < P.d := by exact_mod_cast (by omega : 0 < P.d)
  have hw := bucket_width_pos P.d (by omega) j
  obtain ⟨i, hi⟩ := hne
  obtain ⟨hcon, hij⟩ := (Finset.mem_filter.mp hi).2
  have hwidth : 1 / (P.d : ℝ) ≤ bucket_width P.d j := by
    exact (hmin i b y hcon).trans (by simpa only [hij] using hindex i b y hcon)
  have hmul : 1 ≤ (P.d : ℝ) * bucket_width P.d j := by
    have hh := (div_le_iff₀ hp).mp hwidth
    nlinarith only [hh]
  have hmean : bucket_mean P index b y j ≤ 1 / 1000 :=
    (bucket_mean_le_nominal P index hu b y j).trans (hload y)
  have hdiv : bucket_mean P index b y j / bucket_width P.d j ≤ (P.d : ℝ) / 1000 := by
    apply (div_le_iff₀ hw).mpr
    nlinarith only [hmul, hmean]
  have hsqrt : Real.rpow (P.d : ℝ) 0.5 ≤ P.d := by
    have hh := Real.rpow_le_rpow_of_exponent_le (show (1 : ℝ) ≤ P.d by exact_mod_cast (by omega : 1 ≤ P.d))
      (by norm_num : (0.5 : ℝ) ≤ 1)
    have hone : Real.rpow (P.d : ℝ) 1 = P.d := Real.rpow_one _
    have hh' : Real.rpow (P.d : ℝ) 0.5 ≤ Real.rpow (P.d : ℝ) 1 := hh
    exact hh'.trans_eq hone
  apply capacity_size_upper P.d _ hd (bucket_ratio_nonneg P (by omega) index hu b y j)
  unfold bucket_ratio
  have hid : 80 * bucket_mean P index b y j / bucket_width P.d j =
      80 * (bucket_mean P index b y j / bucket_width P.d j) := by ring
  rw [hid]
  nlinarith only [hdiv, hsqrt, hp]

theorem bucket_geometric_sum (d : ℕ) : (∑ j : Fin d, 1 / (2 : ℝ) ^ (j : ℕ)) ≤ 2 := by
  have hrange : (∑ j ∈ Finset.range d, 1 / (2 : ℝ) ^ j) = 2 - 2 / (2 : ℝ) ^ d := by
    induction d with
    | zero => norm_num
    | succ d ih => rw [Finset.sum_range_succ, ih, pow_succ]; ring
  rw [Fin.sum_univ_eq_sum_range (fun j => 1 / (2 : ℝ) ^ j), hrange]
  have hh : 0 ≤ 2 / (2 : ℝ) ^ d := by positivity
  linarith

theorem bucket_load_sum (P : GroupBinProblem I O Star Y) (index : I → O → Y → Fin P.d)
    (a : I → O) (b : O) (y : Y) :
    (∑ j : Fin P.d, ∑ i ∈ dyadic_bucket P index b y j,
      if a i = b then P.contribution i b y else 0) =
      ∑ i, if a i = b then P.contribution i b y else 0 := by
  simp only [dyadic_bucket, Finset.sum_filter]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i _
  by_cases hu : P.contribution i b y = 0
  · simp [hu]
  · simp [hu]

set_option maxHeartbeats 800000 in
theorem dyadic_safe_cover (P : GroupBinProblem I O Star Y) (hd : 2 ≤ P.d)
    (index : I → O → Y → Fin P.d) (columns : O → Finset Y)
    (hdis : ∀ b b', b ≠ b' → Disjoint (columns b) (columns b'))
    (hsupp : ∀ i b y, P.contribution i b y ≠ 0 → y ∈ columns b)
    (hu : ∀ i b y, 0 ≤ P.contribution i b y)
    (hindex : ∀ i b y, P.contribution i b y ≠ 0 →
      P.contribution i b y ≤ bucket_width P.d (index i b y))
    (hload : ∀ y, P.nominalColumnLoad y ≤ 1 / 1000)
    (q : I → FinLaw O) (x : ℝ) (a : I → O)
    (havoid : ∀ e, a ∉ (group_data P q columns (dyadic_bucket P index)
      (fun b y j => ⌊bucket_ratio P index b y j⌋₊) x).bad e) : P.safe a := by
  have hstar : ∀ s, ¬ group_star_bad P s a := by
    intro s
    simpa only [group_data, Finset.mem_filter, Finset.mem_univ, true_and] using havoid (.inl s)
  refine ⟨?_, ?_, ?_⟩
  · intro s i i' hi hi' hne heq
    exact hstar s (Or.inl ⟨i, hi, i', hi', hne, heq⟩)
  · intro s
    exact le_of_not_gt (fun h => hstar s (Or.inr h))
  · intro y
    by_cases hex : ∃ i b, P.contribution i b y ≠ 0
    · obtain ⟨i₀, b, hi₀⟩ := hex
      have hy := hsupp i₀ b y hi₀
      have hcol : P.columnLoad a y = ∑ i, if a i = b then P.contribution i b y else 0 := by
        apply Finset.sum_congr rfl
        intro i _
        by_cases ha : a i = b
        · simp [ha]
        · have hz : P.contribution i (a i) y = 0 := by
            by_contra hn
            exact Finset.disjoint_left.mp (hdis b (a i) (Ne.symm ha)) hy (hsupp i (a i) y hn)
          simp [ha, hz]
      have hBucket : ∀ j : Fin P.d, (∑ i ∈ dyadic_bucket P index b y j,
          if a i = b then P.contribution i b y else 0) ≤
          bucket_width P.d j * bucket_ratio P index b y j := by
        intro j
        let w := bucket_width P.d j
        let r := bucket_ratio P index b y j
        have hw : 0 < w := bucket_width_pos P.d (by omega) j
        have hr : 0 ≤ r := bucket_ratio_nonneg P (by omega) index hu b y j
        have hh := capacity_bucket_load_bound (dyadic_bucket P index b y j) a b
          (fun i => P.contribution i b y) w (w * r) hw (mul_nonneg hw.le hr)
          (by
            intro i hi
            obtain ⟨hcon, hij⟩ := (Finset.mem_filter.mp hi).2
            simpa only [hij] using hindex i b y hcon)
          (by
            intro S hS hcard hbad
            have hratio : w * r / w = r := by field_simp [hw.ne'] <;> ring
            rw [hratio] at hcard
            let c : CapacityEvent P.d columns (dyadic_bucket P index)
                (fun b y j => ⌊bucket_ratio P index b y j⌋₊) :=
              ⟨b, ⟨y, hy⟩, j, S, Finset.mem_powersetCard.mpr ⟨hS, hcard⟩⟩
            apply havoid (.inr c)
            change a ∈ Finset.univ.filter (capacity_bad S b)
            exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, hbad⟩)
        exact hh
      have hmu : (∑ j : Fin P.d, bucket_mean P index b y j) ≤ P.nominalColumnLoad y := by
        rw [bucket_mean_sum, nominal_column_sum]
        exact Finset.sum_le_sum fun i _ => Finset.single_le_sum
          (fun b _ => mul_nonneg ((P.target i).nonneg b) (hu i b y)) (Finset.mem_univ b)
      have hIdentity : ∀ j : Fin P.d, bucket_width P.d j * bucket_ratio P index b y j =
          80 * bucket_mean P index b y j + (1 / 100 : ℝ) / (2 : ℝ) ^ (j : ℕ) := by
        intro j
        have hw := bucket_width_pos P.d (by omega) j
        have hp : (0 : ℝ) < P.d := by exact_mod_cast (by omega : 0 < P.d)
        have hprod : Real.rpow (P.d : ℝ) (-0.5) * Real.rpow (P.d : ℝ) 0.5 = 1 := by
          convert (Real.rpow_add hp (-0.5) 0.5).symm using 1 <;> norm_num
        unfold bucket_ratio
        rw [mul_add]
        have hfirst : bucket_width P.d j * (80 * bucket_mean P index b y j / bucket_width P.d j) =
            80 * bucket_mean P index b y j := by field_simp [hw.ne'] <;> ring
        rw [hfirst]
        unfold bucket_width
        have hsecond : Real.rpow (P.d : ℝ) (-0.5) / (2 : ℝ) ^ (j : ℕ) *
            ((1 / 100 : ℝ) * Real.rpow (P.d : ℝ) 0.5) = (1 / 100 : ℝ) / (2 : ℝ) ^ (j : ℕ) := by
          calc
            _ = (1 / 100 : ℝ) * (Real.rpow (P.d : ℝ) (-0.5) * Real.rpow (P.d : ℝ) 0.5) /
                (2 : ℝ) ^ (j : ℕ) := by ring
            _ = _ := by rw [hprod]; ring
        rw [hsecond]
      rw [hcol, ← bucket_load_sum P index a b y]
      calc
        _ ≤ ∑ j : Fin P.d, bucket_width P.d j * bucket_ratio P index b y j :=
          Finset.sum_le_sum fun j _ => hBucket j
        _ = 80 * (∑ j : Fin P.d, bucket_mean P index b y j) +
            (1 / 100 : ℝ) * (∑ j : Fin P.d, 1 / (2 : ℝ) ^ (j : ℕ)) := by
          simp_rw [hIdentity]
          rw [Finset.sum_add_distrib, Finset.mul_sum, Finset.mul_sum]
          congr 1
          apply Finset.sum_congr rfl
          intro j _
          ring
        _ ≤ 1 / 5 := by nlinarith only [hmu, hload y, bucket_geometric_sum P.d]
    · have hz : ∀ i b, P.contribution i b y = 0 := by
        intro i b
        by_contra hn
        exact hex ⟨i, b, hn⟩
      simp [GroupBinProblem.columnLoad, hz]

set_option maxHeartbeats 1000000 in
theorem dyadic_group_certificates
    (P : GroupBinProblem I O Star Y) (hd : (10 ^ 100 : ℕ) ≤ P.d)
    (hε : 0 < P.ε) (h : ℕ)
    (hroom : 16 * (P.d : ℝ) ^ 2 * (h + 1 : ℝ) ^ 2 * Real.rpow P.ε (1 / 16 : ℝ) ≤
      Real.rpow (P.d : ℝ) (-20))
    (columns : O → Finset Y) (hcol : ∀ b, (columns b).card ≤ P.d)
    (hdis : ∀ b b', b ≠ b' → Disjoint (columns b) (columns b'))
    (hsupp : ∀ i b y, P.contribution i b y ≠ 0 → y ∈ columns b)
    (hu : ∀ i b y, 0 ≤ P.contribution i b y)
    (hcap : ∀ i b y, P.contribution i b y ≤ Real.rpow (P.d : ℝ) (-0.5))
    (hmin : ∀ i b y, P.contribution i b y ≠ 0 → 1 / (P.d : ℝ) ≤ P.contribution i b y)
    (hload : ∀ y, P.nominalColumnLoad y ≤ 1 / 1000)
    (hlocal : ∀ s, DependsOn (P.failureMass s) (P.participants s : Set I))
    (hsize : ∀ s, (P.participants s).card ≤ P.d)
    (hdegree : ∀ i, ((Finset.univ.filter fun s => i ∈ P.participants s).card : ℝ) ≤ P.d)
    (q : I → FinLaw O) (hq : RelativePerturbation P.target q (Real.rpow (P.d : ℝ) (-0.1)))
    (hstar : ∀ s, (FinLaw.pi q).pr (group_star_bad P s) ≤
      4 * Real.rpow P.ε (1 / 8 : ℝ) + 2 * ((P.participants s).card : ℝ) ^ 2 * Real.rpow (P.d : ℝ) (-40))
    (hstarPin : ∀ s i o, (FinLaw.pi q).pr (fun a => a i = o ∧ group_star_bad P s a) ≤
      (4 * Real.rpow P.ε (1 / 8 : ℝ) + 2 * ((P.participants s).card : ℝ) ^ 2 * Real.rpow (P.d : ℝ) (-40)) * (q i).w o) :
    ∃ A : AvoidanceData (fun a : I → O => a) (fun i : I => i) P.safe,
      A.base = FinLaw.pi q ∧ AvoidanceHypotheses A P.target q (fun _ => True)
        (Real.rpow (P.d : ℝ) (-0.1)) (Real.rpow (P.d : ℝ) (-2))
        (Real.rpow (P.d : ℝ) (-0.05)) := by
  have hd2 : 2 ≤ P.d := by omega
  have hp : (0 : ℝ) < P.d := by exact_mod_cast (by omega : 0 < P.d)
  obtain ⟨index, hindex⟩ := dyadic_index_exists P (by omega) hcap hmin
  let bucket := dyadic_bucket P index
  let t := fun b y j => ⌊bucket_ratio P index b y j⌋₊
  let x := Real.rpow P.ε (1 / 16 : ℝ) + Real.rpow (P.d : ℝ) (-20)
  let G := Real.rpow (P.d : ℝ) (-2) / (16 * (P.d : ℝ) ^ 2)
  have hG : 0 ≤ G := by
    dsimp only [G]
    exact div_nonneg (rpow_nonneg hp.le _) (by positivity)
  have hGbudget : (P.d : ℝ) ^ 2 * G ≤ Real.rpow (P.d : ℝ) (-2) / 16 := by
    dsimp only [G]
    apply le_of_eq
    field_simp [hp.ne']
  have hsmall : ∀ b y j, 4 * (3 / 5 : ℝ) ^ t b y j ≤ G := by
    intro b y j
    have hh := capacity_total_charge_small P.d (t b y j) hd (bucket_ratio_lower P hd index hu b y j)
    dsimp only [G]
    apply (le_div_iff₀ (by positivity : 0 < 16 * (P.d : ℝ) ^ 2)).mpr
    nlinarith only [hh]
  have hq2 : ∀ i b, (q i).w b ≤ 2 * (P.target i).w b := by
    intro i b
    have hρ := (calibration_power_bounds P.d hd).1
    have hρ0 := rpow_nonneg (Nat.cast_nonneg P.d) (-0.1)
    have hc : (1 + Real.rpow (P.d : ℝ) (-0.1)) / (1 - Real.rpow (P.d : ℝ) (-0.1)) ≤ 2 := by
      apply (div_le_iff₀ (by linarith : 0 < 1 - Real.rpow (P.d : ℝ) (-0.1))).mpr
      linarith
    exact ((hq i b).2).trans (mul_le_mul_of_nonneg_right hc ((P.target i).nonneg b))
  have hcharge := group_star_charge_room P.d h P.ε hd2 hε hroom
  have hStarBound : ∀ s, 4 * Real.rpow P.ε (1 / 8 : ℝ) +
      2 * ((P.participants s).card : ℝ) ^ 2 * Real.rpow (P.d : ℝ) (-40) ≤ x / 2 := by
    intro s
    have hc : ((P.participants s).card : ℝ) ≤ P.d := by exact_mod_cast hsize s
    have hs : ((P.participants s).card : ℝ) ^ 2 ≤ (P.d : ℝ) ^ 2 := by
      nlinarith [Nat.cast_nonneg (α := ℝ) (P.participants s).card]
    have hh := mul_le_mul_of_nonneg_right hs (rpow_nonneg hp.le (-40))
    exact le_trans (by nlinarith only [hh]) hcharge.2.2.2
  apply group_certificates P q columns bucket t x G hd2 hG hGbudget
    (group_avoidance_rate_budget P.d hd) (calibration_power_bounds P.d hd).1 hq hlocal
  · intro a _ ha
    exact dyadic_safe_cover P hd2 index columns hdis hsupp hu
      (fun i b y hn => (hindex i b y hn).2) hload q x a ha
  · exact ⟨hcharge.1, hcharge.2.1⟩
  · intro s
    exact (hstar s).trans (hStarBound s)
  · intro s i o
    exact (hstarPin s i o).trans (mul_le_mul_of_nonneg_right (hStarBound s) ((q i).nonneg o))
  · intro i
    rw [Finset.sum_const, nsmul_eq_mul]
    exact (mul_le_mul_of_nonneg_right (hdegree i) hcharge.1).trans hcharge.2.2.1
  · intro e
    cases e with
    | inl s => exact hsize s
    | inr c =>
      obtain ⟨i, hi⟩ := capacity_event_nonempty P.d columns bucket t c
      have hmem := (Finset.mem_powersetCard.mp c.2.2.2.2).1 hi
      change c.2.2.2.1.card ≤ P.d
      rw [(Finset.mem_powersetCard.mp c.2.2.2.2).2]
      exact bucket_ratio_upper P hd2 index hu (fun i b y hn => (hindex i b y hn).2)
        hmin hload c.1 c.2.1.1 c.2.2.1 ⟨i, hmem⟩
  · exact hcol
  · exact bucket_ratio_budget P hd index hu hindex q hq2
  · exact hsmall

end HypercubeRamsey.S16.Lane_sol_s16_group
