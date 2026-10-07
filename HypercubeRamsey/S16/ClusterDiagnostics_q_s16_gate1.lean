import HypercubeRamsey.S16.ProducersDefs

namespace HypercubeRamsey.S16.Lane_q_s16_gate1

open Classical
open scoped BigOperators

private theorem finLaw_ext {α : Type*} [Fintype α] {P Q : FinLaw α}
    (h : ∀ x, P.w x = Q.w x) : P = Q := by
  cases P with
  | mk pw hp hs =>
    cases Q with
    | mk qw hq hsq =>
      have hw : pw = qw := funext h
      subst qw
      rfl

/-- Mapping a product law coordinatewise gives the product of the image laws. -/
private theorem finLaw_map_pi {ι : Type*} [Fintype ι] [DecidableEq ι]
    {α : ι → Type*} {β : ι → Type*}
    [∀ i, Fintype (α i)] [∀ i, DecidableEq (α i)]
    [∀ i, Fintype (β i)] [∀ i, DecidableEq (β i)]
    (P : ∀ i, FinLaw (α i)) (f : ∀ i, α i → β i) :
    FinLaw.map (FinLaw.pi P) (fun x i => f i (x i)) =
      FinLaw.pi (fun i => FinLaw.map (P i) (f i)) := by
  classical
  apply finLaw_ext
  intro y
  simp only [FinLaw.map, FinLaw.pi]
  calc
    (∑ x : (∀ i, α i),
        if (fun i => f i (x i)) = y then ∏ i, (P i).w (x i) else 0) =
        ∑ x : (∀ i, α i), ∏ i, if f i (x i) = y i then (P i).w (x i) else 0 := by
      apply Finset.sum_congr rfl
      intro x hx
      by_cases hall : ∀ i, f i (x i) = y i
      · have hfun : (fun i => f i (x i)) = y := funext hall
        simp [hfun, hall]
      · have hex : ∃ i, f i (x i) ≠ y i := by
          simpa only [not_forall] using hall
        obtain ⟨i, hi⟩ := hex
        have hfun : (fun i => f i (x i)) ≠ y := by
          intro heq
          exact hi (congrFun heq i)
        rw [if_neg hfun]
        symm
        apply Finset.prod_eq_zero (Finset.mem_univ i)
        simp [hi]
    _ = ∏ i, ∑ a : α i, if f i a = y i then (P i).w a else 0 :=
      (Fintype.prod_sum (fun i a => if f i a = y i then (P i).w a else 0)).symm
    _ = ∏ i, (FinLaw.map (P i) (f i)).w (y i) := by
      simp [FinLaw.map]

/-- The conditioned law, represented on its positive support subtype. -/
private noncomputable def condSupportLaw {α : Type*} [Fintype α] [DecidableEq α]
    (P : FinLaw α) (A : Finset α) (hA : 0 < ∑ x ∈ A, P.w x) :
    FinLaw {x : α // x ∈ A ∧ P.w x ≠ 0} := by
  classical
  let Q := FinLaw.cond P A hA
  let p := fun x : α => x ∈ A ∧ P.w x ≠ 0
  refine ⟨fun z => Q.w z.1, ?_, ?_⟩
  · intro z
    exact Q.nonneg z.1
  · have hfilter :
        (∑ z : {x : α // p x}, Q.w z.1) =
          ∑ x ∈ Finset.univ.filter p, Q.w x := by
      simpa [p] using
        (Finset.sum_subtype_eq_sum_filter (s := (Finset.univ : Finset α))
          (p := p) (f := fun x => Q.w x))
    have hsub : Finset.univ.filter p ⊆ A := by
      intro x hx
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hx
      exact hx.1
    have hzero : ∀ x ∈ A, x ∉ Finset.univ.filter p → Q.w x = 0 := by
      intro x hxA hxnot
      have hnot : ¬ p x := by
        intro hp
        apply hxnot
        simp [hp]
      rcases not_and_or.mp hnot with hnotA | hzero
      · exact (hnotA hxA).elim
      · have hPx : P.w x = 0 := not_ne_iff.mp hzero
        simp [Q, FinLaw.cond, hxA, hPx]
    have hQsum : (∑ x ∈ A, Q.w x) = 1 := by
      calc
        (∑ x ∈ A, Q.w x) = (∑ x ∈ A, P.w x) / (∑ x ∈ A, P.w x) := by
          rw [Finset.sum_div]
          apply Finset.sum_congr rfl
          intro x hx
          simp [Q, FinLaw.cond, hx]
        _ = 1 := div_self (ne_of_gt hA)
    calc
      (∑ z : {x : α // p x}, Q.w z.1) = ∑ x ∈ Finset.univ.filter p, Q.w x := hfilter
      _ = ∑ x ∈ A, Q.w x := Finset.sum_subset hsub hzero
      _ = 1 := hQsum

private theorem condSupport_map {α : Type*} [Fintype α] [DecidableEq α]
    (P : FinLaw α) (A : Finset α) (hA : 0 < ∑ x ∈ A, P.w x) :
    FinLaw.map (condSupportLaw P A hA)
        (fun z : {x : α // x ∈ A ∧ P.w x ≠ 0} => z.1) = FinLaw.cond P A hA := by
  classical
  apply finLaw_ext
  intro x
  let p := fun a : α => a ∈ A ∧ P.w a ≠ 0
  change (∑ z : {a : α // p a},
      if z.1 = x then (FinLaw.cond P A hA).w z.1 else 0) =
    (FinLaw.cond P A hA).w x
  by_cases hx : p x
  · rw [Finset.sum_eq_single (⟨x, hx⟩ : {a : α // p a})]
    · simp
    · intro z hz hne
      have hval : z.1 ≠ x := by
        intro heq
        exact hne (Subtype.ext heq)
      simp [hval]
    · simp
  · have hzero : (FinLaw.cond P A hA).w x = 0 := by
      rcases not_and_or.mp hx with hnotA | hweight
      · simp [FinLaw.cond, hnotA]
      · have hz : P.w x = 0 := not_ne_iff.mp hweight
        simp [FinLaw.cond, hz]
    rw [hzero]
    apply Finset.sum_eq_zero
    intro z hz
    have hval : z.1 ≠ x := by
      intro heq
      subst x
      exact hx ⟨z.property.1, z.property.2⟩
    simp [hval]

/-- Product conditioning is the image of the product of positive-support laws. -/
theorem pi_cond_support_map {I : Type*} [Fintype I] [DecidableEq I]
    {V : I → Type*} [∀ i, Fintype (V i)] [∀ i, DecidableEq (V i)]
    (P : ∀ i, FinLaw (V i)) (A : ∀ i, Finset (V i))
    (hA : ∀ i, 0 < ∑ v ∈ A i, (P i).w v) :
    ∃ P' : ∀ i, FinLaw {v : V i // v ∈ A i ∧ (P i).w v ≠ 0},
      FinLaw.pi (fun i => FinLaw.cond (P i) (A i) (hA i)) =
        FinLaw.map (FinLaw.pi P') (fun z i => (z i).1) := by
  classical
  let P' : ∀ i, FinLaw {v : V i // v ∈ A i ∧ (P i).w v ≠ 0} :=
    fun i => condSupportLaw (P i) (A i) (hA i)
  refine ⟨P', ?_⟩
  calc
    FinLaw.pi (fun i => FinLaw.cond (P i) (A i) (hA i)) =
        FinLaw.pi (fun i => FinLaw.map (P' i) (fun z => z.1)) := by
      congr 1
      funext i
      exact (condSupport_map (P i) (A i) (hA i)).symm
    _ = FinLaw.map (FinLaw.pi P') (fun z i => (z i).1) :=
      (finLaw_map_pi P' (fun i z => z.1)).symm

end HypercubeRamsey.S16.Lane_q_s16_gate1
