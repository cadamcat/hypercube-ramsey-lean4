import HypercubeRamsey.S03.ConditionalAvoidance
import HypercubeRamsey.S15.ClusterNodes_sol_s15_transfer

namespace HypercubeRamsey.Lane_sol_s15_c2

open Classical
open scoped BigOperators
set_option backward.isDefEq.respectTransparency false

theorem mass_eq_pr_mem {Ω : Type*} [Fintype Ω] [DecidableEq Ω]
    (P : FinLaw Ω) (S : Finset Ω) : LocalLemma.mass P.w S = P.pr (fun ω => ω ∈ S) := by
  classical
  unfold LocalLemma.mass
  calc
    _ = ∑ ω ∈ Finset.univ.filter (fun ω : Ω => ω ∈ S), P.w ω := by simp
    _ = ∑ ω, if ω ∈ S then P.w ω else 0 := by rw [Finset.sum_filter]
    _ = _ := by
      unfold FinLaw.pr
      apply Finset.sum_congr rfl
      intro ω hω
      by_cases h : ω ∈ S <;> simp [h]

theorem avoid_indicator_depends {R I : Type*} [Fintype R] [DecidableEq R]
    [Fintype I] [DecidableEq I] {Ω : R → Type*} [∀ r, Fintype (Ω r)]
    (bad : I → (∀ r, Ω r) → Prop) (scope : I → Finset R)
    (hbad : ∀ i, FinProb.DependsOn (bad i) (scope i)) (S : Finset I) :
    FinProb.DependsOn (fun ω => if ∀ i ∈ S, ¬ bad i ω then (1 : ℝ) else 0) (S.biUnion scope) := by
  intro ω ω' hω
  have heq : (∀ i ∈ S, ¬ bad i ω) ↔ ∀ i ∈ S, ¬ bad i ω' := by
    apply forall₂_congr
    intro i hi
    rw [hbad i ω ω' (fun r hr => hω r (Finset.mem_biUnion.mpr ⟨i, hi, hr⟩))]
  simp only [heq]

theorem product_bad_avoid_probability {R I : Type*} [Fintype R] [DecidableEq R]
    [Fintype I] [DecidableEq I] {Ω : R → Type*} [∀ r, Fintype (Ω r)]
    (P : ∀ r, FinLaw (Ω r)) (bad : I → (∀ r, Ω r) → Prop) (scope : I → Finset R)
    (hbad : ∀ i, FinProb.DependsOn (bad i) (scope i)) (i : I) (S : Finset I)
    (hdis : Disjoint (scope i) (S.biUnion scope)) :
    (FinLaw.pi P).pr (fun ω => bad i ω ∧ ∀ j ∈ S, ¬ bad j ω) =
      (FinLaw.pi P).pr (bad i) * (FinLaw.pi P).pr (fun ω => ∀ j ∈ S, ¬ bad j ω) := by
  let F := fun ω => if bad i ω then (1 : ℝ) else 0
  let G := fun ω => if ∀ j ∈ S, ¬ bad j ω then (1 : ℝ) else 0
  have hF : FinProb.DependsOn F (scope i) := by
    intro ω ω' hω
    simp only [F, hbad i ω ω' hω]
  have hG : FinProb.DependsOn G (S.biUnion scope) := avoid_indicator_depends bad scope hbad S
  have h := Lane_sol_s15_transfer.E_pi_mul_of_disjoint P F G (scope i) (S.biUnion scope) hF hG hdis
  have hL : (FinLaw.pi P).E (fun ω => F ω * G ω) =
      (FinLaw.pi P).pr (fun ω => bad i ω ∧ ∀ j ∈ S, ¬ bad j ω) := by
    unfold FinLaw.E FinLaw.pr
    apply Finset.sum_congr rfl
    intro ω hω
    dsimp [F, G]
    split_ifs <;> simp_all
  have hFpr : (FinLaw.pi P).E F = (FinLaw.pi P).pr (bad i) := by
    unfold FinLaw.E FinLaw.pr
    apply Finset.sum_congr rfl
    intro ω hω
    dsimp [F]
    split_ifs <;> simp
  have hGpr : (FinLaw.pi P).E G = (FinLaw.pi P).pr (fun ω => ∀ j ∈ S, ¬ bad j ω) := by
    unfold FinLaw.E FinLaw.pr
    apply Finset.sum_congr rfl
    intro ω hω
    dsimp [G]
    split_ifs <;> simp
  rwa [hL, hFpr, hGpr] at h

theorem condition_product_events {R I : Type*} [Fintype R] [DecidableEq R]
    [Fintype I] [DecidableEq I] {Ω : R → Type*} [∀ r, Fintype (Ω r)]
    (P : ∀ r, FinLaw (Ω r)) (bad : I → (∀ r, Ω r) → Prop) (scope : I → Finset R)
    (hbad : ∀ i, FinProb.DependsOn (bad i) (scope i)) (x : I → ℝ)
    (hx0 : ∀ i, 0 ≤ x i) (hx1 : ∀ i, x i < 1)
    (hLLL : ∀ i, (FinLaw.pi P).pr (bad i) ≤ x i *
      ∏ j ∈ Finset.univ.filter (fun j => i ≠ j ∧ ¬ Disjoint (scope i) (scope j)), (1 - x j))
    (budget C : ℝ)
    (hquery : ∀ U : Finset R, (U.card : ℝ) ≤ budget →
      (∏ i ∈ Finset.univ.filter (fun i => ¬ Disjoint U (scope i)), (1 - x i))⁻¹ ≤ C) :
    ∃ L : FinLaw (∀ r, Ω r),
      (∀ ω, L.w ω ≠ 0 → (FinLaw.pi P).w ω ≠ 0) ∧
      (∀ ω, L.w ω ≠ 0 → ∀ i, ¬ bad i ω) ∧
      ∀ F : (∀ r, Ω r) → ℝ, (∀ ω, 0 ≤ F ω) → ∀ U : Finset R,
        FinProb.DependsOn F U → (U.card : ℝ) ≤ budget → L.E F ≤ C * (FinLaw.pi P).E F := by
  classical
  let Q := FinLaw.pi P
  let E := fun i => Finset.univ.filter (bad i)
  let adj := fun i j => i ≠ j ∧ ¬ Disjoint (scope i) (scope j)
  have hp (i : I) (S : Finset I) (hi : i ∉ S) (hFar : ∀ j ∈ S, ¬ adj i j) :
      LocalLemma.mass Q.w (E i ∩ LocalLemma.avoid E S) ≤
        Q.pr (bad i) * LocalLemma.mass Q.w (LocalLemma.avoid E S) := by
    have hdis : Disjoint (scope i) (S.biUnion scope) := by
      apply Finset.disjoint_left.mpr
      intro r hr hrS
      obtain ⟨j, hj, hrj⟩ := Finset.mem_biUnion.mp hrS
      have hij : i ≠ j := by intro heq; subst j; exact hi hj
      exact hFar j hj ⟨hij, fun hd => Finset.disjoint_left.mp hd hr hrj⟩
    have h := product_bad_avoid_probability P bad scope hbad i S hdis
    rw [mass_eq_pr_mem, mass_eq_pr_mem]
    have hleft : (fun ω => ω ∈ E i ∩ LocalLemma.avoid E S) =
        (fun ω => bad i ω ∧ ∀ j ∈ S, ¬ bad j ω) := by
      funext ω
      apply propext
      simp [E, LocalLemma.avoid]
    have hright : (fun ω => ω ∈ LocalLemma.avoid E S) = (fun ω => ∀ j ∈ S, ¬ bad j ω) := by
      funext ω
      apply propext
      simp [E, LocalLemma.avoid]
    rw [hleft, hright]
    exact h.le
  have hsym : ∀ i j, adj i j → adj j i := by
    intro i j h
    exact ⟨h.1.symm, fun hd => h.2 hd.symm⟩
  have hirr : ∀ i, ¬ adj i i := by intro i h; exact h.1 rfl
  have hLL := LocalLemma.conditional_avoidance Q.w Q.nonneg Q.sum_one E adj hsym hirr
    (fun i => Q.pr (bad i)) x hp hx0 hx1 hLLL
  have hpos : 0 < ∑ ω ∈ LocalLemma.avoid E Finset.univ, Q.w ω := hLL.1
  let L := Q.cond (LocalLemma.avoid E Finset.univ) hpos
  refine ⟨L, ?_, ?_, ?_⟩
  · intro ω hω hz
    change Q.w ω = 0 at hz
    exact hω (by simp [L, FinLaw.cond, hz])
  · intro ω hω i hbadω
    have hnot : ω ∉ LocalLemma.avoid E Finset.univ := by
      simp only [LocalLemma.avoid, Finset.mem_filter, Finset.mem_univ, true_and]
      intro h
      exact h i True.intro (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hbadω⟩)
    exact hω (by simp [L, FinLaw.cond, hnot])
  · intro F hF U hdep hcard
    let Touched : Finset I := Finset.univ.filter fun i => ¬ Disjoint U (scope i)
    let Far := Finset.univ \ Touched
    have hST : Disjoint Far Touched := Finset.sdiff_disjoint
    have hUnion : Far ∪ Touched = Finset.univ := by ext i; simp [Far]
    have hdis : Disjoint U (Far.biUnion scope) := by
      apply Finset.disjoint_left.mpr
      intro r hr hrS
      obtain ⟨i, hi, hri⟩ := Finset.mem_biUnion.mp hrS
      have hnot := (Finset.mem_sdiff.mp hi).2
      apply hnot
      exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, fun hd => Finset.disjoint_left.mp hd hr hri⟩
    have hGdep : FinProb.DependsOn (fun ω => if ω ∈ LocalLemma.avoid E Far then (1 : ℝ) else 0)
        (Far.biUnion scope) := by
      have h := avoid_indicator_depends bad scope hbad Far
      simpa only [LocalLemma.avoid, E, Finset.mem_filter, Finset.mem_univ, true_and] using h
    have hfactor := Lane_sol_s15_transfer.E_pi_mul_of_disjoint P F
      (fun ω => if ω ∈ LocalLemma.avoid E Far then (1 : ℝ) else 0) U (Far.biUnion scope) hdep hGdep hdis
    have hnum : (∑ ω ∈ LocalLemma.avoid E Far, Q.w ω * F ω) =
        Q.E F * LocalLemma.mass Q.w (LocalLemma.avoid E Far) := by
      have hN : (∑ ω ∈ LocalLemma.avoid E Far, Q.w ω * F ω) =
          Q.E (fun ω => F ω * (if ω ∈ LocalLemma.avoid E Far then 1 else 0)) := by
        simp [FinLaw.E, mul_ite, Finset.sum_ite_mem, Finset.univ_inter]
      have hM : Q.E (fun ω => if ω ∈ LocalLemma.avoid E Far then (1 : ℝ) else 0) =
          LocalLemma.mass Q.w (LocalLemma.avoid E Far) := by
        simp [FinLaw.E, LocalLemma.mass, mul_ite, Finset.sum_ite_mem, Finset.univ_inter]
      exact hN.trans (hfactor.trans (by rw [hM]))
    have hFarPos : 0 < LocalLemma.mass Q.w (LocalLemma.avoid E Far) := by
      have hsub : LocalLemma.avoid E Finset.univ ⊆ LocalLemma.avoid E Far := by
        intro ω hω
        simp only [LocalLemma.avoid, Finset.mem_filter, Finset.mem_univ, true_and] at hω ⊢
        exact fun i hi => hω i True.intro
      have hmono : LocalLemma.mass Q.w (LocalLemma.avoid E Finset.univ) ≤
          LocalLemma.mass Q.w (LocalLemma.avoid E Far) := by
        unfold LocalLemma.mass
        exact Finset.sum_le_sum_of_subset_of_nonneg hsub (fun ω _ _ => Q.nonneg ω)
      exact lt_of_lt_of_le hLL.1 hmono
    have hFarRatio : (∑ ω ∈ LocalLemma.avoid E Far, Q.w ω * F ω) /
        LocalLemma.mass Q.w (LocalLemma.avoid E Far) = Q.E F := by
      rw [hnum]
      exact mul_div_cancel_right₀ _ hFarPos.ne'
    have hcomp := hLL.2.2.1 Far Touched hST F hF
    rw [hUnion, hFarRatio] at hcomp
    rw [Lane_q_s15_c3.finLaw_cond_E_eq]
    exact hcomp.trans (mul_le_mul_of_nonneg_right (hquery U hcard)
      (Lane_sol_s15_transfer.E_nonneg Q F hF))

end HypercubeRamsey.Lane_sol_s15_c2
