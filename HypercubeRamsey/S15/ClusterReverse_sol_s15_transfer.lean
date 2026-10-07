import HypercubeRamsey.S15.ClusterNodes_sol_s15_transfer

namespace HypercubeRamsey.Lane_sol_s15_transfer

open Classical S15 Filter
open scoped BigOperators

set_option backward.isDefEq.respectTransparency false

theorem E_finset_sum {ι Ω : Type*} [DecidableEq ι] [Fintype Ω]
    (P : FinLaw Ω) (S : Finset ι) (F : ι → Ω → ℝ) :
    P.E (fun ω => ∑ i ∈ S, F i ω) = ∑ i ∈ S, P.E (F i) := by
  unfold FinLaw.E
  simp_rw [Finset.mul_sum]
  exact Finset.sum_comm

theorem E_indicator_union_le {ι Ω : Type*} [DecidableEq ι] [Fintype Ω]
    (P : FinLaw Ω) (S : Finset ι) (A : ι → Ω → Prop) (F : Ω → ℝ)
    (hF : ∀ ω, 0 ≤ F ω) :
    P.E (fun ω => if ∃ i ∈ S, A i ω then F ω else 0) ≤
      ∑ i ∈ S, P.E (fun ω => if A i ω then F ω else 0) := by
  rw [← E_finset_sum]
  apply E_mono
  intro ω
  by_cases h : ∃ i ∈ S, A i ω
  · rw [if_pos h]
    obtain ⟨i, hi, hA⟩ := h
    calc
      F ω = (if A i ω then F ω else 0) := by rw [if_pos hA]
      _ ≤ ∑ j ∈ S, if A j ω then F ω else 0 :=
        Finset.single_le_sum (f := fun j => if A j ω then F ω else 0)
          (fun j hj => by split_ifs; exact hF ω; exact le_rfl) hi
  · rw [if_neg h]
    exact Finset.sum_nonneg fun i hi => by split_ifs; exact hF ω; exact le_rfl

/-- Charge a removed core block by summing its possible current-group witnesses. -/
theorem E_pi_charge_repeat_block
    {ι β : Type*} [Fintype ι] [DecidableEq ι]
    {Ω : ι → Type*} [∀ i, Fintype (Ω i)]
    (P : ∀ i, FinLaw (Ω i)) (value : ∀ i, Ω i → β)
    (C D : Finset ι) (p : ℝ) (F : (∀ i, Ω i) → ℝ)
    (hF : ∀ ω, 0 ≤ F ω)
    (hskip : ∀ i ∈ C, ∀ ω a, F (Function.update ω i a) = F ω)
    (hdis : Disjoint C D)
    (hatom : ∀ i ∈ C, ∀ b, (P i).pr (fun a => value i a = b) ≤ p) :
    (FinLaw.pi P).E (fun ω =>
      if ∃ i ∈ C, ∃ j ∈ D, value i (ω i) = value j (ω j) then F ω else 0) ≤
      ((C.card : ℝ) * D.card * p) * (FinLaw.pi P).E F := by
  classical
  calc
    _ ≤ ∑ i ∈ C, (FinLaw.pi P).E (fun ω =>
        if ∃ j ∈ D, value i (ω i) = value j (ω j) then F ω else 0) :=
      by
        rw [← E_finset_sum]
        apply E_mono
        intro ω
        by_cases h : ∃ i ∈ C, ∃ j ∈ D, value i (ω i) = value j (ω j)
        · rw [if_pos h]
          obtain ⟨i, hi, hA⟩ := h
          have hterm : F ω = (if ∃ j ∈ D, value i (ω i) = value j (ω j) then F ω else 0) := by
            rw [if_pos hA]
          apply le_trans (le_of_eq hterm)
          exact Finset.single_le_sum (f := fun i =>
            if ∃ j ∈ D, value i (ω i) = value j (ω j) then F ω else 0)
            (fun i hi => by split_ifs; exact hF ω; exact le_rfl) hi
        · rw [if_neg h]
          exact Finset.sum_nonneg fun i hi => by split_ifs; exact hF ω; exact le_rfl
    _ ≤ ∑ i ∈ C, ((D.card : ℝ) * p) * (FinLaw.pi P).E F := by
      apply Finset.sum_le_sum
      intro i hi
      let A : (∀ i, Ω i) → Prop := fun ω => ∃ j ∈ D, value i (ω i) = value j (ω j)
      have hcharge : ∀ ω, (P i).pr (fun a => A (Function.update ω i a)) ≤ (D.card : ℝ) * p := by
        intro ω
        dsimp only [A]
        have heq : (fun a : Ω i => ∃ j ∈ D,
            value i ((Function.update ω i a) i) = value j ((Function.update ω i a) j)) =
            (fun a => ∃ j ∈ D, value i a = value j (ω j)) := by
          funext a
          apply propext
          apply exists_congr
          intro j
          by_cases hj : j ∈ D
          · have hne : j ≠ i := by
              intro heq
              subst j
              exact Finset.disjoint_left.mp hdis hi hj
            simp only [hj, true_and, Function.update_self, Function.update_of_ne hne]
          · simp only [hj, false_and]
        rw [heq]
        calc
          _ ≤ ∑ j ∈ D, (P i).pr (fun a => value i a = value j (ω j)) :=
            pr_finset_exists_le_sum _ D _
          _ ≤ ∑ _j ∈ D, p := Finset.sum_le_sum fun j hj => hatom i hi _
          _ = _ := by simp
      have hbound := E_pi_charge_one P i F A ((D.card : ℝ) * p) hF (hskip i hi) hcharge
      have hfun : (fun ω => if ∃ j ∈ D, value i (ω i) = value j (ω j) then F ω else 0) =
          (fun ω => @ite ℝ (A ω) (Classical.propDecidable (A ω)) (F ω) 0) := by
        funext ω
        by_cases h : A ω
        · simp only [if_pos h, show (∃ j ∈ D, value i (ω i) = value j (ω j)) from h,
            ite_true]
        · simp only [if_neg h, show ¬ (∃ j ∈ D, value i (ω i) = value j (ω j)) from h,
            ite_false]
      rw [hfun]
      exact hbound
    _ = _ := by simp [mul_assoc, mul_left_comm, mul_comm]

/-- Reverse integration of disjoint row blocks. Earlier removed blocks remain available as witnesses. -/
theorem E_pi_charge_repeat_blocks_ordered
    {ι β I : Type*} [Fintype ι] [DecidableEq ι] [LinearOrder I]
    {Ω : ι → Type*} [∀ i, Fintype (Ω i)]
    (P : ∀ i, FinLaw (Ω i)) (value : ∀ i, Ω i → β)
    (R : Finset I) (C D : I → Finset ι) (p : I → ℝ)
    (F : (∀ i, Ω i) → ℝ)
    (hF : ∀ ω, 0 ≤ F ω)
    (hskip : ∀ i ∈ R, ∀ g ∈ C i, ∀ ω a, F (Function.update ω g a) = F ω)
    (hdis : ∀ i ∈ R, Disjoint (C i) (D i))
    (hearlier : ∀ i ∈ R, ∀ j ∈ R, i < j → Disjoint (C j) (C i ∪ D i))
    (hp : ∀ i ∈ R, 0 ≤ p i)
    (hatom : ∀ i ∈ R, ∀ g ∈ C i, ∀ b, (P g).pr (fun a => value g a = b) ≤ p i) :
    (FinLaw.pi P).E (fun ω => if ∀ i ∈ R,
      ∃ g ∈ C i, ∃ g' ∈ D i, value g (ω g) = value g' (ω g') then F ω else 0) ≤
      (∏ i ∈ R, (C i).card * (D i).card * p i) * (FinLaw.pi P).E F := by
  classical
  induction R using Finset.induction_on_max with
  | empty => simp
  | insert j R hlt ih =>
    have hj : j ∉ R := fun h => lt_irrefl j (hlt j h)
    let A (i : I) (ω : ∀ g, Ω g) : Prop := ∃ g ∈ C i, ∃ g' ∈ D i, value g (ω g) = value g' (ω g')
    let G : (∀ i, Ω i) → ℝ := fun ω => if ∀ i ∈ R, A i ω then F ω else 0
    have hG ω : 0 ≤ G ω := by dsimp [G]; split_ifs; exact hF ω; exact le_rfl
    have hGskip g (hg : g ∈ C j) ω a : G (Function.update ω g a) = G ω := by
      have hA : (∀ i ∈ R, A i (Function.update ω g a)) ↔ ∀ i ∈ R, A i ω := by
        apply forall₂_congr
        intro i hi
        have hd := hearlier i (Finset.mem_insert_of_mem hi) j
          (Finset.mem_insert_self _ _) (hlt i hi)
        have hunchanged l (hl : l ∈ C i ∪ D i) : (Function.update ω g a) l = ω l := by
          have hne : l ≠ g := by
            intro h
            subst l
            exact Finset.disjoint_left.mp hd hg hl
          exact Function.update_of_ne hne _ _
        dsimp [A]
        apply exists_congr
        intro l
        by_cases hl : l ∈ C i
        · simp only [hl, true_and]
          apply exists_congr
          intro l'
          by_cases hl' : l' ∈ D i
          · simp only [hl', true_and,
              hunchanged l (Finset.mem_union_left _ hl),
              hunchanged l' (Finset.mem_union_right _ hl')]
          · simp only [hl', false_and]
        · simp only [hl, false_and]
      simp only [G, hA, hskip j (Finset.mem_insert_self _ _) g hg ω a]
    have hpoint ω : (if ∀ i ∈ insert j R, A i ω then F ω else 0) =
        if A j ω then G ω else 0 := by
      simp only [Finset.forall_mem_insert, G]
      split_ifs <;> simp_all
    have hpj := hp j (Finset.mem_insert_self _ _)
    calc
      _ = (FinLaw.pi P).E (fun ω => if A j ω then G ω else 0) := by
        apply congrArg (FinLaw.E (FinLaw.pi P))
        funext ω
        exact hpoint ω
      _ ≤ (((C j).card : ℝ) * (D j).card * p j) * (FinLaw.pi P).E G :=
        E_pi_charge_repeat_block P value (C j) (D j) (p j) G hG hGskip
          (hdis j (Finset.mem_insert_self _ _)) (hatom j (Finset.mem_insert_self _ _))
      _ ≤ (((C j).card : ℝ) * (D j).card * p j) *
          ((∏ i ∈ R, (C i).card * (D i).card * p i) * (FinLaw.pi P).E F) := by
        apply mul_le_mul_of_nonneg_left _ (by positivity)
        exact ih (fun i hi => hskip i (Finset.mem_insert_of_mem hi))
          (fun i hi => hdis i (Finset.mem_insert_of_mem hi))
          (fun i hi l hl => hearlier i (Finset.mem_insert_of_mem hi) l (Finset.mem_insert_of_mem hl))
          (fun i hi => hp i (Finset.mem_insert_of_mem hi))
          (fun i hi => hatom i (Finset.mem_insert_of_mem hi))
      _ = _ := by rw [Finset.prod_insert hj]; ring

end HypercubeRamsey.Lane_sol_s15_transfer
