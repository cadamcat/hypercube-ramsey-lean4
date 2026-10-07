import HypercubeRamsey.S03.Clock.Steps_sol_clock_s7

set_option autoImplicit false

namespace HypercubeRamsey.Lane_sol_clock_s7

open Clock
open scoped BigOperators

/-- Conditional rectangle probabilities are products after the background coordinates are fixed. -/
theorem pi_background_rectangle {ι : Type*} [Fintype ι] [DecidableEq ι]
    {α : ι → Type*} [∀ i, Fintype (α i)]
    (P : ∀ i, FinProb (α i)) (D : Finset ι)
    (A : (∀ i : {i // i ∈ D}, α i.1) → ∀ i : {i // i ∉ D}, α i.1 → Prop) :
    (FinProb.pi P).pr (fun x => ∀ i : {i // i ∉ D}, A (fun j => x j.1) i (x i.1)) =
      (FinProb.pi (fun i : {i // i ∈ D} => P i.1)).expect
        (fun bg => ∏ i : {i // i ∉ D}, (P i.1).pr (A bg i)) := by
  classical
  let E : (∀ i, α i) → Prop := fun x => ∀ i : {i // i ∉ D}, A (fun j => x j.1) i (x i.1)
  let fill := (Equiv.piEquivPiSubtypeProd (fun i => i ∈ D) α).symm
  have hpr : (FinProb.pi P).pr E = (FinProb.pi P).expect (fun x => if E x then 1 else 0) := by
    unfold FinProb.pr FinProb.expect
    apply Finset.sum_congr rfl
    intro x _
    by_cases h : E x <;> simp [h]
  have hE (bg : ∀ i : {i // i ∈ D}, α i.1) (rest : ∀ i : {i // i ∉ D}, α i.1) :
      E (fill (bg, rest)) ↔ ∀ i : {i // i ∉ D}, A bg i (rest i) := by
    have hbg : (fun j : {j // j ∈ D} => fill (bg, rest) j.1) = bg := by
      funext j
      simp [fill, Equiv.piEquivPiSubtypeProd]
    have hrest (i : {i // i ∉ D}) : fill (bg, rest) i.1 = rest i := by
      simp only [fill, Equiv.piEquivPiSubtypeProd_symm_apply, dif_neg i.2]
    simp only [E, hbg, hrest]
  change (FinProb.pi P).pr E = _
  rw [hpr, pi_expect_split_p_clock_r4 P D]
  change (∑ bg, ∑ rest,
      (FinProb.pi (fun i : {i // i ∈ D} => P i.1)).w bg *
        (FinProb.pi (fun i : {i // i ∉ D} => P i.1)).w rest *
        (if E (fill (bg, rest)) then 1 else 0)) = _
  calc
    _ = (FinProb.pi (fun i : {i // i ∈ D} => P i.1)).expect
        (fun bg => (FinProb.pi (fun i : {i // i ∉ D} => P i.1)).pr
          (fun rest => ∀ i : {i // i ∉ D}, A bg i (rest i))) := by
      unfold FinProb.expect FinProb.pr
      apply Finset.sum_congr rfl
      intro bg _
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro rest _
      by_cases h : ∀ i : {i // i ∉ D}, A bg i (rest i) <;> simp [hE, h]
    _ = _ := by
      congr 1
      funext bg
      exact Clock.pi_pr_forall_coordinates _ _

/-- Background coordinates may be included in the rectangle when their constraints are identically true. -/
theorem pi_background_rectangle_full {ι : Type*} [Fintype ι] [DecidableEq ι]
    {α : ι → Type*} [∀ i, Fintype (α i)]
    (P : ∀ i, FinProb (α i)) (D : Finset ι)
    (A : (∀ i : {i // i ∈ D}, α i.1) → ∀ i : ι, α i → Prop)
    (hA : ∀ bg i, i ∈ D → ∀ x, A bg i x) :
    (FinProb.pi P).pr (fun x => ∀ i, A (fun j => x j.1) i (x i)) =
      (FinProb.pi (fun i : {i // i ∈ D} => P i.1)).expect
        (fun bg => ∏ i, (P i).pr (A bg i)) := by
  classical
  have hevent : (fun x : ∀ i, α i => ∀ i, A (fun j => x j.1) i (x i)) =
      (fun x => ∀ i : {i // i ∉ D}, A (fun j => x j.1) i.1 (x i.1)) := by
    funext x
    apply propext
    constructor
    · intro h i
      exact h i.1
    · intro h i
      by_cases hi : i ∈ D
      · exact hA _ i hi (x i)
      · exact h ⟨i, hi⟩
  rw [hevent, pi_background_rectangle P D (fun bg i => A bg i.1)]
  congr 1
  funext bg
  have hprBG (i : {i // i ∈ D}) : (P i.1).pr (A bg i.1) = 1 := by
    have hpred : A bg i.1 = fun _ => True := by
      funext x
      apply propext
      exact ⟨fun _ => trivial, fun _ => hA bg i.1 i.2 x⟩
    rw [hpred]
    simpa [FinProb.pr] using (P i.1).sum_eq_one
  have hsplit := Fintype.prod_subtype_mul_prod_subtype (fun i => i ∈ D)
    (fun i => (P i).pr (A bg i))
  simp_rw [hprBG] at hsplit
  simpa only [Finset.prod_const_one, one_mul] using hsplit

/-- Null-weight fields can be discarded when deriving necessary rectangle constraints. -/
theorem pr_le_of_weighted_implication {Ω : Type*} [Fintype Ω]
    (P : FinProb Ω) (E F : Ω → Prop)
    (hEF : ∀ x, P.w x ≠ 0 → E x → F x) : P.pr E ≤ P.pr F := by
  classical
  unfold FinProb.pr
  apply Finset.sum_le_sum
  intro x _
  by_cases hzero : P.w x = 0
  · simp [hzero]
  · by_cases hE : E x
    · simp [hE, hEF x hzero hE]
    · by_cases hF : F x
      · simpa [hE, hF] using P.nonneg x
      · simp [hE, hF]

private theorem noEarlyArrival_zero {T : ℕ} {α : Type*} (x : MeshClockValue T α) :
    NoEarlyArrival 0 x := by
  cases x <;> simp [NoEarlyArrival]

/-- Prescribed target arrivals retain their full output product under fixed cross-edge survival constraints. -/
theorem joint_target_arrival_and_survival_probability {T : ℕ} {R : Type*}
    [Fintype R] [DecidableEq R] {g : ℕ} {Ω : R → Type*}
    [∀ a, Fintype (Ω a)] [∀ a, DecidableEq (Ω a)]
    (δ : ℝ) (hδ : 0 ≤ δ) (hδ1 : δ ≤ 1)
    (p : ∀ a, FinProb (Ω a)) (lab : ∀ a, Ω a → Fin g)
    (S : Finset R) (o : ∀ a, Ω a) (times : R → Fin T)
    (cutoff : RowLabel R g → ℕ) (hcut : ∀ e, cutoff e ≤ T)
    (hzero : ∀ a ∈ S, cutoff (a, lab a (o a)) = 0) :
    (clockFieldLaw (edgeLaw δ hδ hδ1 p lab)).pr
      (fun ξ => (∀ a ∈ S, ξ (a, lab a (o a)) = .tick (times a) (o a)) ∧
        ∀ e, NoEarlyArrival (cutoff e) (ξ e)) =
      ((∏ a ∈ S, (p a).w (o a)) *
        ∏ a ∈ S, survival δ (labMarg (p a) (lab a) (lab a (o a))) (times a).val * δ) *
        ∏ e : RowLabel R g, survival δ (labMarg (p e.1) (lab e.1) e.2) (cutoff e) := by
  classical
  let F : ClockField T R g Ω → Prop := fun ξ => ∀ e, NoEarlyArrival (cutoff e) (ξ e)
  let D : Finset (RowLabel R g) := Finset.univ.filter fun e => cutoff e ≠ 0
  have hF : FinProb.DependsOn F D := by
    intro ξ ξ' hξ
    apply propext
    constructor
    · intro h e
      by_cases he : cutoff e = 0
      · rw [he]
        exact noEarlyArrival_zero _
      · rw [← hξ e (by simp [D, he])]
        exact h e
    · intro h e
      by_cases he : cutoff e = 0
      · rw [he]
        exact noEarlyArrival_zero _
      · rw [hξ e (by simp [D, he])]
        exact h e
  have hD : Disjoint (S.image fun a => (a, lab a (o a))) D := by
    apply Finset.disjoint_left.mpr
    intro e he hmem
    obtain ⟨a, ha, rfl⟩ := Finset.mem_image.mp he
    simpa [D, hzero a ha] using hmem
  rw [joint_target_arrival_and_disjoint_probability δ hδ hδ1 p lab S o times F D hF hD]
  rw [pi_noEarlyArrival_probability δ hδ hδ1 p lab cutoff hcut]

/-- Conditioning on outside clocks extracts the full target-arrival product from the survival integrand. -/
theorem target_rectangle_background_factorization {T : ℕ} {R : Type*}
    [Fintype R] [DecidableEq R] {g : ℕ} {Ω : R → Type*}
    [∀ a, Fintype (Ω a)] [∀ a, DecidableEq (Ω a)]
    (δ : ℝ) (hδ : 0 ≤ δ) (hδ1 : δ ≤ 1)
    (p : ∀ a, FinProb (Ω a)) (lab : ∀ a, Ω a → Fin g)
    (S : Finset R) (o : ∀ a, Ω a) (times : R → Fin T)
    (D : Finset (RowLabel R g))
    (hD : ∀ a ∈ S, (a, lab a (o a)) ∉ D)
    (cutoff : (∀ e : {e // e ∈ D}, MeshClockValue T (Ω e.1.1)) → RowLabel R g → ℕ)
    (hcut : ∀ bg e, cutoff bg e ≤ T)
    (hzeroTarget : ∀ bg a, a ∈ S → cutoff bg (a, lab a (o a)) = 0)
    (hzeroBG : ∀ bg e, e ∈ D → cutoff bg e = 0) :
    (clockFieldLaw (edgeLaw δ hδ hδ1 p lab)).pr
      (fun ξ => (∀ a ∈ S, ξ (a, lab a (o a)) = .tick (times a) (o a)) ∧
        ∀ e, NoEarlyArrival (cutoff (fun j => ξ j.1) e) (ξ e)) =
      ((∏ a ∈ S, (p a).w (o a)) *
        ∏ a ∈ S, survival δ (labMarg (p a) (lab a) (lab a (o a))) (times a).val * δ) *
        (FinProb.pi (fun e : {e // e ∈ D} => edgeLaw δ hδ hδ1 p lab e.1)).expect
          (fun bg => ∏ e : RowLabel R g,
            survival δ (labMarg (p e.1) (lab e.1) e.2) (cutoff bg e)) := by
  classical
  let A (bg : ∀ e : {e // e ∈ D}, MeshClockValue T (Ω e.1.1))
      (e : RowLabel R g) (x : MeshClockValue T (Ω e.1)) : Prop :=
    ((e.1 ∈ S ∧ e.2 = lab e.1 (o e.1)) → x = .tick (times e.1) (o e.1)) ∧
      NoEarlyArrival (cutoff bg e) x
  have hlogical (ξ : ClockField T R g Ω)
      (bg : ∀ e : {e // e ∈ D}, MeshClockValue T (Ω e.1.1)) :
      (∀ e, A bg e (ξ e)) ↔
        (∀ a ∈ S, ξ (a, lab a (o a)) = .tick (times a) (o a)) ∧
          ∀ e, NoEarlyArrival (cutoff bg e) (ξ e) := by
    constructor
    · intro h
      exact ⟨fun a ha => (h (a, lab a (o a))).1 ⟨ha, rfl⟩, fun e => (h e).2⟩
    · rintro ⟨htarget, htail⟩ e
      refine ⟨?_, htail e⟩
      rintro ⟨ha, hy⟩
      rcases e with ⟨a, y⟩
      change y = lab a (o a) at hy
      subst y
      exact htarget a ha
  have hA : ∀ bg e, e ∈ D → ∀ x, A bg e x := by
    intro bg e he x
    refine ⟨?_, ?_⟩
    · rintro ⟨ha, hy⟩
      rcases e with ⟨a, y⟩
      change y = lab a (o a) at hy
      subst y
      exact False.elim (hD a ha he)
    · rw [hzeroBG bg e he]
      exact noEarlyArrival_zero x
  have hevent :
      (fun ξ : ClockField T R g Ω =>
        (∀ a ∈ S, ξ (a, lab a (o a)) = .tick (times a) (o a)) ∧
          ∀ e, NoEarlyArrival (cutoff (fun j => ξ j.1) e) (ξ e)) =
        (fun ξ => ∀ e, A (fun j => ξ j.1) e (ξ e)) := by
    funext ξ
    exact propext (hlogical ξ (fun j => ξ j.1)).symm
  rw [hevent, clockFieldLaw, pi_background_rectangle_full (edgeLaw δ hδ hδ1 p lab) D A hA]
  have hcoeff (bg : ∀ e : {e // e ∈ D}, MeshClockValue T (Ω e.1.1)) :
      (∏ e, (edgeLaw δ hδ hδ1 p lab e).pr (A bg e)) =
        ((∏ a ∈ S, (p a).w (o a)) *
          ∏ a ∈ S, survival δ (labMarg (p a) (lab a) (lab a (o a))) (times a).val * δ) *
          ∏ e : RowLabel R g, survival δ (labMarg (p e.1) (lab e.1) e.2) (cutoff bg e) := by
    rw [← pi_pr_forall_coordinates (edgeLaw δ hδ hδ1 p lab) (A bg)]
    have hpred : (fun ξ : ClockField T R g Ω => ∀ e, A bg e (ξ e)) =
        (fun ξ => (∀ a ∈ S, ξ (a, lab a (o a)) = .tick (times a) (o a)) ∧
          ∀ e, NoEarlyArrival (cutoff bg e) (ξ e)) := by
      funext ξ
      exact propext (hlogical ξ bg)
    rw [hpred]
    exact joint_target_arrival_and_survival_probability δ hδ hδ1 p lab S o times
      (cutoff bg) (hcut bg) (hzeroTarget bg)
  simp_rw [hcoeff]
  rw [FinProb.expect_smul]

end HypercubeRamsey.Lane_sol_clock_s7
