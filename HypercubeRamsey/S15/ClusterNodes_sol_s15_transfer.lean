import HypercubeRamsey.S15.Masks
import HypercubeRamsey.S15.ClusterNodes_q_s15_c3
import HypercubeRamsey.S15.DirectNodes_q_s15_direct
import HypercubeRamsey.Framework.FinProbLemmas

namespace HypercubeRamsey.Lane_sol_s15_transfer

open HypercubeRamsey S15 Classical Filter
open scoped BigOperators

private def toFinProb {Ω : Type*} [Fintype Ω] (P : FinLaw Ω) : FinProb Ω :=
  ⟨P.w, P.nonneg, P.sum_one⟩

theorem E_nonneg {Ω : Type*} [Fintype Ω] (P : FinLaw Ω)
    (F : Ω → ℝ) (hF : ∀ ω, 0 ≤ F ω) : 0 ≤ P.E F :=
  Finset.sum_nonneg fun ω _ => mul_nonneg (P.nonneg ω) (hF ω)

theorem E_mono {Ω : Type*} [Fintype Ω] (P : FinLaw Ω)
    {F G : Ω → ℝ} (h : ∀ ω, F ω ≤ G ω) : P.E F ≤ P.E G :=
  Finset.sum_le_sum fun ω _ => mul_le_mul_of_nonneg_left (h ω) (P.nonneg ω)

theorem E_mul_const {Ω : Type*} [Fintype Ω] (P : FinLaw Ω)
    (F : Ω → ℝ) (c : ℝ) : P.E (fun ω => c * F ω) = c * P.E F := by
  unfold FinLaw.E
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro ω hω
  ring

theorem pr_eq_E_indicator {Ω : Type*} [Fintype Ω] (P : FinLaw Ω) (A : Ω → Prop) :
    P.pr A = P.E (fun ω => if A ω then 1 else 0) := by
  classical
  unfold FinLaw.pr FinLaw.E
  apply Finset.sum_congr rfl
  intro ω hω
  by_cases h : A ω <;> simp [h]

theorem pr_finset_exists_le_sum {ι Ω : Type*} [Fintype Ω] [DecidableEq ι]
    (P : FinLaw Ω) (S : Finset ι) (A : ι → Ω → Prop) :
    P.pr (fun ω => ∃ i ∈ S, A i ω) ≤ ∑ i ∈ S, P.pr (A i) := by
  classical
  unfold FinLaw.pr
  rw [← Finset.sum_comm]
  apply Finset.sum_le_sum
  intro ω hω
  by_cases h : ∃ i ∈ S, A i ω
  · obtain ⟨i, hi, hAi⟩ := h
    simp only [if_pos (show ∃ i ∈ S, A i ω from ⟨i, hi, hAi⟩)]
    calc
      P.w ω = (if A i ω then P.w ω else 0) := by simp [hAi]
      _ ≤ ∑ j ∈ S, if A j ω then P.w ω else 0 :=
        Finset.single_le_sum (f := fun j => if A j ω then P.w ω else 0) (fun j hj => by
          split_ifs
          · exact P.nonneg ω
          · exact le_rfl) hi
  · simp only [if_neg h]
    apply Finset.sum_nonneg
    intro i hi
    split_ifs
    · exact P.nonneg ω
    · exact le_rfl

theorem pr_injective_value_le_cap {Ω B : Type*} [Fintype Ω]
    (P : FinLaw Ω) (f : Ω → B) (hf : Function.Injective f) (c : ℝ)
    (hc : 0 ≤ c) (hcap : ∀ ω, P.w ω ≤ c) (b : B) :
    P.pr (fun ω => f ω = b) ≤ c := by
  classical
  by_cases hb : ∃ ω, f ω = b
  · obtain ⟨ω, hω⟩ := hb
    have heq : (fun z => f z = b) = (fun z => z = ω) := by
      funext z
      apply propext
      rw [← hω]
      exact hf.eq_iff
    rw [heq]
    simpa [FinLaw.pr] using hcap ω
  · have hnone : ∀ ω, f ω ≠ b := by simpa using hb
    simpa [FinLaw.pr, hnone] using hc

theorem E_pi_mul_of_disjoint
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    {Ω : ι → Type*} [∀ i, Fintype (Ω i)]
    (P : ∀ i, FinLaw (Ω i)) (F G : (∀ i, Ω i) → ℝ) (S U : Finset ι)
    (hF : FinProb.DependsOn F S) (hG : FinProb.DependsOn G U)
    (hSU : Disjoint S U) :
    (FinLaw.pi P).E (fun ω => F ω * G ω) =
      (FinLaw.pi P).E F * (FinLaw.pi P).E G := by
  exact FinProb.pi_expect_mul_of_disjoint (fun i => toFinProb (P i)) F G S U hF hG hSU

theorem E_pi_prod_of_disjoint
    {ι I : Type*} [Fintype ι] [DecidableEq ι] [DecidableEq I]
    {Ω : ι → Type*} [∀ i, Fintype (Ω i)]
    (P : ∀ i, FinLaw (Ω i)) (A : Finset I)
    (F : I → (∀ i, Ω i) → ℝ) (S : I → Finset ι)
    (hF : ∀ i ∈ A, FinProb.DependsOn (F i) (S i))
    (hS : ∀ i ∈ A, ∀ j ∈ A, i ≠ j → Disjoint (S i) (S j)) :
    (FinLaw.pi P).E (fun ω => ∏ i ∈ A, F i ω) =
      ∏ i ∈ A, (FinLaw.pi P).E (F i) := by
  induction A using Finset.induction_on with
  | empty => simp [FinLaw.E, (FinLaw.pi P).sum_one]
  | @insert i A hi ih =>
    have hFA : FinProb.DependsOn (fun ω => ∏ j ∈ A, F j ω) (A.biUnion S) := by
      intro ω ω' hω
      apply Finset.prod_congr rfl
      intro j hj
      apply hF j (Finset.mem_insert_of_mem hj) ω ω'
      intro r hr
      exact hω r (Finset.mem_biUnion.mpr ⟨j, hj, hr⟩)
    have hdis : Disjoint (S i) (A.biUnion S) := by
      apply Finset.disjoint_left.mpr
      intro r hr hrA
      obtain ⟨j, hj, hrj⟩ := Finset.mem_biUnion.mp hrA
      exact Finset.disjoint_left.mp
        (hS i (Finset.mem_insert_self _ _) j (Finset.mem_insert_of_mem hj)
          (fun hij => hi (hij ▸ hj))) hr hrj
    simp only [Finset.prod_insert hi]
    rw [E_pi_mul_of_disjoint P (F i) (fun ω => ∏ j ∈ A, F j ω)
      (S i) (A.biUnion S) (hF i (Finset.mem_insert_self _ _)) hFA hdis]
    rw [ih (fun j hj => hF j (Finset.mem_insert_of_mem hj))
      (fun j hj l hl => hS j (Finset.mem_insert_of_mem hj) l (Finset.mem_insert_of_mem hl))]

theorem E_three_stage_prod
    {R B L I : Type*} [Fintype R] [DecidableEq R] [Fintype B] [DecidableEq B]
    [Fintype L] [DecidableEq L] [DecidableEq I]
    {ΩR : R → Type*} [∀ r, Fintype (ΩR r)]
    {ΩB : B → Type*} [∀ b, Fintype (ΩB b)]
    {ΩL : L → Type*} [∀ l, Fintype (ΩL l)]
    (P : ∀ r, FinLaw (ΩR r))
    (Q : (∀ r, ΩR r) → ∀ b, FinLaw (ΩB b))
    (K : (∀ r, ΩR r) → (∀ b, ΩB b) → ∀ l, FinLaw (ΩL l))
    (A : Finset I) (F : I → (∀ r, ΩR r) → (∀ b, ΩB b) → (∀ l, ΩL l) → ℝ)
    (SR : I → Finset R) (SB : I → Finset B) (SL : I → Finset L)
    (hSL : ∀ i ∈ A, ∀ j ∈ A, i ≠ j → Disjoint (SL i) (SL j))
    (hSB : ∀ i ∈ A, ∀ j ∈ A, i ≠ j → Disjoint (SB i) (SB j))
    (hSR : ∀ i ∈ A, ∀ j ∈ A, i ≠ j → Disjoint (SR i) (SR j))
    (hL : ∀ W B, ∀ i ∈ A, FinProb.DependsOn (F i W B) (SL i))
    (hB : ∀ W, ∀ i ∈ A, FinProb.DependsOn
      (fun B => (FinLaw.pi (K W B)).E (F i W B)) (SB i))
    (hR : ∀ i ∈ A, FinProb.DependsOn
      (fun W => (FinLaw.pi (Q W)).E (fun B => (FinLaw.pi (K W B)).E (F i W B))) (SR i)) :
    (FinLaw.pi P).E (fun W => (FinLaw.pi (Q W)).E (fun B =>
      (FinLaw.pi (K W B)).E (fun ys => ∏ i ∈ A, F i W B ys))) =
      ∏ i ∈ A, (FinLaw.pi P).E (fun W => (FinLaw.pi (Q W)).E
        (fun B => (FinLaw.pi (K W B)).E (F i W B))) := by
  calc
    _ = (FinLaw.pi P).E (fun W => (FinLaw.pi (Q W)).E
        (fun B => ∏ i ∈ A, (FinLaw.pi (K W B)).E (F i W B))) := by
      apply congrArg (FinLaw.E (FinLaw.pi P))
      funext W
      apply congrArg (FinLaw.E (FinLaw.pi (Q W)))
      funext B
      exact E_pi_prod_of_disjoint (K W B) A (fun i => F i W B) SL (hL W B) hSL
    _ = (FinLaw.pi P).E (fun W => ∏ i ∈ A, (FinLaw.pi (Q W)).E
        (fun B => (FinLaw.pi (K W B)).E (F i W B))) := by
      apply congrArg (FinLaw.E (FinLaw.pi P))
      funext W
      exact E_pi_prod_of_disjoint (Q W) A
        (fun i B => (FinLaw.pi (K W B)).E (F i W B)) SB (hB W) hSB
    _ = _ := E_pi_prod_of_disjoint P A
      (fun i W => (FinLaw.pi (Q W)).E (fun B => (FinLaw.pi (K W B)).E (F i W B))) SR hR hSR

theorem E_pi_splitAt
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    {Ω : ι → Type*} [∀ i, Fintype (Ω i)]
    (P : ∀ i, FinLaw (Ω i)) (i : ι) (F : (∀ i, Ω i) → ℝ) :
    (FinLaw.pi P).E F =
      (FinLaw.pi (fun j : {j // j ≠ i} => P j)).E (fun b =>
        (P i).E (fun a => F ((Equiv.piSplitAt i Ω).symm (a, b)))) := by
  classical
  let e := Equiv.piSplitAt i Ω
  have hweight (z : Ω i × (∀ j : {j // j ≠ i}, Ω j)) :
      (∏ j, (P j).w (e.symm z j)) =
        (P i).w z.1 * ∏ j : {j // j ≠ i}, (P j).w (z.2 j) := by
    rw [Fintype.prod_eq_mul_prod_subtype_ne _ i]
    congr 1
    · simp [e, Equiv.piSplitAt]
    · apply Finset.prod_congr rfl
      intro j hj
      simp [e, Equiv.piSplitAt, j.2]
  unfold FinLaw.E
  change (∑ ω, (∏ j, (P j).w (ω j)) * F ω) = _
  rw [← e.symm.sum_comp, Fintype.sum_prod_type]
  simp_rw [hweight]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro b hb
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro a ha
  dsimp [FinLaw.pi, e]
  ring

theorem E_pi_coord
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    {Ω : ι → Type*} [∀ i, Fintype (Ω i)]
    (P : ∀ i, FinLaw (Ω i)) (i : ι) (F : Ω i → ℝ) :
    (FinLaw.pi P).E (fun ω => F (ω i)) = (P i).E F := by
  rw [E_pi_splitAt P i]
  have hcoord (a : Ω i) (b : ∀ j : {j // j ≠ i}, Ω j) :
      (Equiv.piSplitAt i Ω).symm (a, b) i = a := by
    simp [Equiv.piSplitAt]
  simp only [hcoord]
  simp [FinLaw.E, ← Finset.sum_mul, FinLaw.sum_one]

theorem nonempty_of_finLaw {Ω : Type*} [Fintype Ω] (P : FinLaw Ω) : Nonempty Ω := by
  classical
  by_contra h
  haveI : IsEmpty Ω := ⟨fun ω => h ⟨ω⟩⟩
  have hsum : (∑ ω, P.w ω) = 0 := by simp
  rw [P.sum_one] at hsum
  norm_num at hsum

theorem E_pi_congr_on
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    {Ω : ι → Type*} [∀ i, Fintype (Ω i)]
    (P Q : ∀ i, FinLaw (Ω i)) (S : Finset ι) (F : (∀ i, Ω i) → ℝ)
    (hF : FinProb.DependsOn F S)
    (hPQ : ∀ i ∈ S, ∀ a, (P i).w a = (Q i).w a) :
    (FinLaw.pi P).E F = (FinLaw.pi Q).E F := by
  classical
  let ω₀ := Classical.choice (nonempty_of_finLaw (FinLaw.pi P))
  let f := fun a : (∀ i : {i // i ∈ S}, Ω i.1) =>
    F ((Equiv.piEquivPiSubtypeProd (fun i => i ∈ S) Ω).symm (a, fun i => ω₀ i.1))
  calc
    _ = (FinLaw.pi (fun i : {i // i ∈ S} => P i.1)).E f :=
      FinProb.pi_expect_depends (fun i => toFinProb (P i)) S F ω₀ hF
    _ = (FinLaw.pi (fun i : {i // i ∈ S} => Q i.1)).E f := by
      unfold FinLaw.E
      apply Finset.sum_congr rfl
      intro a ha
      apply congrArg (fun w : ℝ => w * f a)
      apply Finset.prod_congr rfl
      intro i hi
      exact hPQ i.1 i.2 (a i)
    _ = (FinLaw.pi Q).E F :=
      (FinProb.pi_expect_depends (fun i => toFinProb (Q i)) S F ω₀ hF).symm

/-- Integrate one removed coordinate while all other choices remain fixed. -/
theorem E_pi_charge_one
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    {Ω : ι → Type*} [∀ i, Fintype (Ω i)]
    (P : ∀ i, FinLaw (Ω i)) (i : ι) (F : (∀ i, Ω i) → ℝ)
    (A : (∀ i, Ω i) → Prop) (c : ℝ)
    (hF : ∀ ω, 0 ≤ F ω)
    (hskip : ∀ ω a, F (Function.update ω i a) = F ω)
    (hcharge : ∀ ω, (P i).pr (fun a => A (Function.update ω i a)) ≤ c) :
    (FinLaw.pi P).E (fun ω => if A ω then F ω else 0) ≤ c * (FinLaw.pi P).E F := by
  classical
  let a₀ := Classical.choice (nonempty_of_finLaw (P i))
  let e := Equiv.piSplitAt i Ω
  have hu (a : Ω i) (b : ∀ j : {j // j ≠ i}, Ω j) :
      e.symm (a, b) = Function.update (e.symm (a₀, b)) i a := by
    funext j
    by_cases hji : j = i
    · subst j
      simp [e, Equiv.piSplitAt]
    · simp [e, Equiv.piSplitAt, hji]
  have hsame (a : Ω i) (b : ∀ j : {j // j ≠ i}, Ω j) :
      F (e.symm (a, b)) = F (e.symm (a₀, b)) := by
    rw [hu]
    exact hskip _ _
  rw [E_pi_splitAt P i, E_pi_splitAt P i F, ← E_mul_const]
  apply E_mono
  intro b
  change (P i).E (fun a => if A (e.symm (a, b)) then F (e.symm (a, b)) else 0) ≤
    c * (P i).E (fun a => F (e.symm (a, b)))
  simp_rw [hsame]
  have heq : (P i).E (fun a => if A (e.symm (a, b)) then F (e.symm (a₀, b)) else 0) =
      (P i).pr (fun a => A (e.symm (a, b))) * F (e.symm (a₀, b)) := by
    unfold FinLaw.E FinLaw.pr
    rw [Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro a ha
    by_cases h : A (e.symm (a, b)) <;> simp [h]
  rw [heq]
  have hconst : (P i).E (fun _ => F (e.symm (a₀, b))) = F (e.symm (a₀, b)) := by
    simp [FinLaw.E, ← Finset.sum_mul, FinLaw.sum_one]
  rw [hconst]
  apply mul_le_mul_of_nonneg_right _ (hF _)
  have hPr : (P i).pr (fun a => A (e.symm (a, b))) =
      (P i).pr (fun a => A (Function.update (e.symm (a₀, b)) i a)) := by
    congr 1
    funext a
    exact congrArg A (hu a b)
  rw [hPr]
  exact hcharge _

/-- Later removed choices are charged first, so earlier repeat witnesses may stay fixed. -/
theorem E_pi_charge_ordered
    {ι : Type*} [Fintype ι] [LinearOrder ι]
    {Ω : ι → Type*} [∀ i, Fintype (Ω i)]
    (P : ∀ i, FinLaw (Ω i)) (R : Finset ι) (F : (∀ i, Ω i) → ℝ)
    (A : ι → (∀ i, Ω i) → Prop) (c : ι → ℝ)
    (hF : ∀ ω, 0 ≤ F ω)
    (hskip : ∀ i ∈ R, ∀ ω a, F (Function.update ω i a) = F ω)
    (hearlier : ∀ i ∈ R, ∀ j ∈ R, i < j → ∀ ω a,
      A i (Function.update ω j a) ↔ A i ω)
    (hc : ∀ i ∈ R, 0 ≤ c i)
    (hcharge : ∀ i ∈ R, ∀ ω, (P i).pr (fun a => A i (Function.update ω i a)) ≤ c i) :
    (FinLaw.pi P).E (fun ω => if ∀ i ∈ R, A i ω then F ω else 0) ≤
      (∏ i ∈ R, c i) * (FinLaw.pi P).E F := by
  classical
  induction R using Finset.induction_on_max with
  | empty => simp
  | insert j R hlt ih =>
    have hj : j ∉ R := fun h => lt_irrefl j (hlt j h)
    let G : (∀ i, Ω i) → ℝ := fun ω => if ∀ i ∈ R, A i ω then F ω else 0
    have hG ω : 0 ≤ G ω := by
      dsimp [G]
      split_ifs
      · exact hF ω
      · exact le_rfl
    have hGskip ω a : G (Function.update ω j a) = G ω := by
      have hA : (∀ i ∈ R, A i (Function.update ω j a)) ↔ ∀ i ∈ R, A i ω := by
        apply forall₂_congr
        intro i hi
        exact hearlier i (Finset.mem_insert_of_mem hi) j (Finset.mem_insert_self _ _)
          (hlt i hi) ω a
      simp only [G, hA, hskip j (Finset.mem_insert_self _ _) ω a]
    have hpoint ω : (if ∀ i ∈ insert j R, A i ω then F ω else 0) =
        if A j ω then G ω else 0 := by
      simp only [Finset.forall_mem_insert, G]
      split_ifs <;> simp_all
    calc
      _ = (FinLaw.pi P).E (fun ω => if A j ω then G ω else 0) := by
        congr 1
        funext ω
        exact hpoint ω
      _ ≤ c j * (FinLaw.pi P).E G :=
        E_pi_charge_one P j G (A j) (c j) hG hGskip
          (hcharge j (Finset.mem_insert_self _ _))
      _ ≤ c j * ((∏ i ∈ R, c i) * (FinLaw.pi P).E F) := by
        apply mul_le_mul_of_nonneg_left _ (hc j (Finset.mem_insert_self _ _))
        exact ih (fun i hi => hskip i (Finset.mem_insert_of_mem hi))
          (fun i hi j hj => hearlier i (Finset.mem_insert_of_mem hi) j (Finset.mem_insert_of_mem hj))
          (fun i hi => hc i (Finset.mem_insert_of_mem hi))
          (fun i hi => hcharge i (Finset.mem_insert_of_mem hi))
      _ = (∏ i ∈ insert j R, c i) * (FinLaw.pi P).E F := by
        rw [Finset.prod_insert hj]
        ring

theorem E_pi_bind
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    {α β : ι → Type*} [∀ i, Fintype (α i)] [∀ i, Fintype (β i)]
    (P : ∀ i, FinLaw (α i)) (K : ∀ i, α i → FinLaw (β i))
    (F : (∀ i, α i × β i) → ℝ) :
    (FinLaw.pi (fun i => FinLaw.bind (P i) (K i))).E F =
      (FinLaw.pi P).E (fun a => (FinLaw.pi (fun i => K i (a i))).E
        (fun b => F (fun i => (a i, b i)))) := by
  classical
  let e : ((∀ i, α i) × (∀ i, β i)) ≃ (∀ i, α i × β i) :=
    { toFun := fun ab i => (ab.1 i, ab.2 i)
      invFun := fun z => (fun i => (z i).1, fun i => (z i).2)
      left_inv := by intro ab; rfl
      right_inv := by intro z; funext i; exact Prod.eta (z i) }
  unfold FinLaw.E
  change (∑ z, (∏ i, (P i).w (z i).1 * (K i (z i).1).w (z i).2) * F z) = _
  rw [← e.sum_comp, Fintype.sum_prod_type]
  simp only [e, Equiv.coe_fn_mk]
  simp_rw [Finset.prod_mul_distrib]
  apply Finset.sum_congr rfl
  intro a ha
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro b hb
  dsimp [FinLaw.pi]
  ring

theorem E_pi_sigma
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    {J : ι → Type*} [∀ i, Fintype (J i)] [∀ i, DecidableEq (J i)]
    {Ω : (Σ i, J i) → Type*} [∀ j, Fintype (Ω j)]
    (P : ∀ j, FinLaw (Ω j)) (F : (∀ j, Ω j) → ℝ) :
    (FinLaw.pi P).E F =
      (FinLaw.pi (fun i => FinLaw.pi (fun j => P ⟨i, j⟩))).E
        (fun ω => F (fun j => ω j.1 j.2)) := by
  classical
  let e := Equiv.piCurry (fun i j => Ω ⟨i, j⟩)
  unfold FinLaw.E
  change (∑ ω, (∏ j, (P j).w (ω j)) * F ω) = _
  rw [← e.symm.sum_comp]
  apply Finset.sum_congr rfl
  intro ω hω
  change (∏ j, (P j).w (ω j.1 j.2)) * F (fun j => ω j.1 j.2) = _
  rw [Fintype.prod_sigma]
  rfl

/-- Global independent group bins and labels are the product of the slice reference laws. -/
theorem internal_kernel_eq_bin_label_E
    {κ : CConsts} {T : Stage} {k : ℕ}
    (PT : ProfiledTiling κ T k) (hPT : PT.Valid)
    (hm : PT.tiling.mode = .highSmall ∨ PT.tiling.mode = .highLarge)
    (W : ClusterHistory PT hPT hm) (F : ClusterInternalData PT → ℝ) :
    (clusterInternalKernel PT hPT hm W).E F =
      (clusterIndependentBinKernel PT hPT hm W).E (fun B =>
        (clusterIndependentLabelKernel PT hPT hm W B).E F) := by
  classical
  let Q (s : ClusterSlice PT) : FinLaw (Group PT.tiling s.1 → Bin PT.tiling s.1) :=
    FinLaw.pi fun g =>
      ⟨(clusterSolver PT hPT hm s.1).q g (historyOnSlice W s),
        (clusterSolver PT hPT hm s.1).q_nonneg g (historyOnSlice W s),
        (clusterSolver PT hPT hm s.1).q_sum g (historyOnSlice W s)⟩
  let K (s : ClusterSlice PT) (D : Group PT.tiling s.1 → Bin PT.tiling s.1) :
      FinLaw (IWord PT.tiling s.1 → Fin (T.S.N k)) :=
    FinLaw.pi fun z =>
      ⟨(clusterSolver PT hPT hm s.1).U ((clusterSolver PT hPT hm s.1).groupOf z)
          (historyOnSlice W s) (D ((clusterSolver PT hPT hm s.1).groupOf z)),
        (clusterSolver PT hPT hm s.1).U_nonneg _ _ _,
        (clusterSolver PT hPT hm s.1).U_sum _ _ _⟩
  change (FinLaw.pi (fun s => FinLaw.bind (Q s) (K s))).E F = _
  rw [E_pi_bind]
  have hbins := E_pi_sigma
    (Ω := fun g : ClusterGroupIndex PT => Bin PT.tiling g.1.1)
    (fun g => (⟨(clusterSolver PT hPT hm g.1.1).q g.2 (historyOnSlice W g.1),
      (clusterSolver PT hPT hm g.1.1).q_nonneg _ _,
      (clusterSolver PT hPT hm g.1.1).q_sum _ _⟩ : FinLaw (Bin PT.tiling g.1.1)))
    (fun B => (clusterIndependentLabelKernel PT hPT hm W B).E F)
  have hbins' : (clusterIndependentBinKernel PT hPT hm W).E
      (fun B => (clusterIndependentLabelKernel PT hPT hm W B).E F) =
      (FinLaw.pi Q).E (fun B =>
        (clusterIndependentLabelKernel PT hPT hm W (fun g => B g.1 g.2)).E F) := by
    simp only [FinLaw.E, FinLaw.pi] at hbins
    simp only [FinLaw.E, FinLaw.pi, clusterIndependentBinKernel, Q]
    convert hbins using 1 <;> congr 1
    all_goals first | rfl | exact congrArg (@Fintype.elems _) (Subsingleton.elim _ _)
  apply Eq.trans _ hbins'.symm
  apply congrArg (FinLaw.E (FinLaw.pi Q))
  funext B
  unfold clusterIndependentLabelKernel
  rw [Lane_q_s15_c3.finLaw_map_E]

theorem reference_mean_eq_internal_E {κ : CConsts} {T : Stage} {k : ℕ}
    (PT : ProfiledTiling κ T k) (hPT : PT.Valid)
    (hm : PT.tiling.mode = .highSmall ∨ PT.tiling.mode = .highLarge)
    (i : Fin PT.tiling.m) (x : Fin (T.S.N k)) (M : ClusterMask PT)
    (W : ClusterHistory PT hPT hm) :
    clusterReferenceMean PT hPT hm i x M W =
      (clusterInternalKernel PT hPT hm W).E (clusterKeptProduct PT hPT hm i x M W) :=
  (internal_kernel_eq_bin_label_E PT hPT hm W _).symm

theorem raw_reference_mean_eq {κ : CConsts} {T : Stage} {k : ℕ}
    (PT : ProfiledTiling κ T k) (hPT : PT.Valid)
    (hm : PT.tiling.mode = .highSmall ∨ PT.tiling.mode = .highLarge)
    (i : Fin PT.tiling.m) (x : Fin (T.S.N k)) (M : ClusterMask PT) :
    (clusterHistoryLaw PT hPT hm).E (clusterReferenceMean PT hPT hm i x M) =
      (clusterRawReferenceLaw PT hPT hm).E
        (fun z => clusterKeptProduct PT hPT hm i x M z.1 z.2) := by
  rw [clusterRawReferenceLaw, Lane_q_s15_c3.finLaw_bind_E]
  apply congrArg (FinLaw.E (clusterHistoryLaw PT hPT hm))
  funext W
  exact reference_mean_eq_internal_E PT hPT hm i x M W

noncomputable def sliceRawLaw {κ : CConsts} {T : Stage} {k : ℕ}
    (PT : ProfiledTiling κ T k) (hPT : PT.Valid)
    (hm : PT.tiling.mode = .highSmall ∨ PT.tiling.mode = .highLarge)
    (s : ClusterSlice PT) :
    FinLaw ((∀ r, (clusterSolver PT hPT hm s.1).Val r) × ClusterSliceOutcome PT s.1) :=
  FinLaw.bind ((clusterSolver PT hPT hm s.1).recLaw PT.parameter)
    (clusterSolver PT hPT hm s.1).refLaw

set_option maxHeartbeats 600000 in
theorem raw_reference_E_eq_slices {κ : CConsts} {T : Stage} {k : ℕ}
    (PT : ProfiledTiling κ T k) (hPT : PT.Valid)
    (hm : PT.tiling.mode = .highSmall ∨ PT.tiling.mode = .highLarge)
    (F : ClusterHistory PT hPT hm × ClusterInternalData PT → ℝ) :
    (clusterRawReferenceLaw PT hPT hm).E F =
      (FinLaw.pi (sliceRawLaw PT hPT hm)).E
        (fun z => F (fun r => (z r.1).1 r.2, fun s => (z s).2)) := by
  rw [clusterRawReferenceLaw, Lane_q_s15_c3.finLaw_bind_E]
  change (FinLaw.pi (fun r : ClusterRecordIndex PT hPT hm =>
    (⟨(clusterSolver PT hPT hm r.1.1).lawRec PT.parameter r.2,
      (clusterSolver PT hPT hm r.1.1).lawRec_nonneg PT.parameter r.2,
      (clusterSolver PT hPT hm r.1.1).lawRec_sum PT.parameter r.2⟩ :
        FinLaw (ClusterRecordValue r)))).E _ = _
  have hrecords := E_pi_sigma
    (Ω := fun r : ClusterRecordIndex PT hPT hm =>
      (clusterSolver PT hPT hm r.1.1).Val r.2)
    (fun r => (⟨(clusterSolver PT hPT hm r.1.1).lawRec PT.parameter r.2,
      (clusterSolver PT hPT hm r.1.1).lawRec_nonneg PT.parameter r.2,
      (clusterSolver PT hPT hm r.1.1).lawRec_sum PT.parameter r.2⟩ :
        FinLaw ((clusterSolver PT hPT hm r.1.1).Val r.2)))
    (fun W => (clusterInternalKernel PT hPT hm W).E (fun I => F (W, I)))
  have hrecords' : (clusterHistoryLaw PT hPT hm).E
      (fun W => (clusterInternalKernel PT hPT hm W).E (fun I => F (W, I))) =
      (FinLaw.pi (fun s => (clusterSolver PT hPT hm s.1).recLaw PT.parameter)).E
        (fun W => (clusterInternalKernel PT hPT hm (fun r => W r.1 r.2)).E
          (fun I => F (fun r => W r.1 r.2, I))) := by
    simp only [FinLaw.E, FinLaw.pi] at hrecords
    simp only [FinLaw.E, FinLaw.pi, clusterHistoryLaw, SliceSolver.recLaw, recordLaw]
    convert hrecords using 1 <;> congr 1
    all_goals first | rfl | exact congrArg (@Fintype.elems _) (Subsingleton.elim _ _)
  apply Eq.trans hrecords'
  have h := (E_pi_bind (fun s : ClusterSlice PT => (clusterSolver PT hPT hm s.1).recLaw PT.parameter)
    (fun s => (clusterSolver PT hPT hm s.1).refLaw)
    (fun z => F (fun r => (z r.1).1 r.2, fun s => (z s).2))).symm
  simp only [FinLaw.E, FinLaw.pi, FinLaw.bind] at h
  simp only [FinLaw.E, FinLaw.pi, FinLaw.bind, clusterInternalKernel, sliceRawLaw]
  convert h using 1 <;> congr 1 <;> ext <;> simp
  all_goals exact @Finset.mem_univ _ _ _

theorem raw_row_mean_le {κ : CConsts} {T : Stage} {k : ℕ}
    (PT : ProfiledTiling κ T k) (hPT : PT.Valid)
    (hm : PT.tiling.mode = .highSmall ∨ PT.tiling.mode = .highLarge)
    (a : EvenPosition T k) (x : Fin (T.S.N k)) :
    (clusterRawReferenceLaw PT hPT hm).E (fun z =>
      (PT.tiling.P (patchAt PT hPT a.1)).M * clusterSigma PT hPT hm z.1 z.2 a x) ≤
        rowMeanConstant κ := by
  let s := clusterSliceAt PT hPT a.1
  let S := clusterSolver PT hPT hm s.1
  let v : EvenRole PT.tiling s.1 := clusterCenterRole PT hPT hm a
  let m : ℝ := (PT.tiling.P s.1).M
  have hmpos : 0 < m := by
    dsimp [m]
    exact_mod_cast (show 0 < (PT.tiling.P s.1).M by
      rw [← (PT.tiling.P s.1).cardX]
      exact Finset.card_pos.mpr (hPT.tiling_valid.patch_nonempty s.1).1)
  rw [raw_reference_E_eq_slices]
  change (FinLaw.pi (sliceRawLaw PT hPT hm)).E
    (fun z => m * S.σ v (z s).1 (nbrLabels v.1 (z s).2.2) x) ≤ _
  rw [E_pi_coord (sliceRawLaw PT hPT hm) s
    (fun z => m * S.σ v z.1 (nbrLabels v.1 z.2.2) x)]
  change (FinLaw.bind (S.recLaw PT.parameter) S.refLaw).E
    (fun z => m * S.σ v z.1 (nbrLabels v.1 z.2.2) x) ≤ _
  rw [Lane_q_s15_c3.finLaw_bind_E]
  simp_rw [E_mul_const]
  calc
    _ ≤ m * (rowMeanConstant κ / m) :=
      mul_le_mul_of_nonneg_left (S.σ_mean PT.parameter v x) hmpos.le
    _ = rowMeanConstant κ := mul_div_cancel₀ _ hmpos.ne'

theorem raw_patch_row_mean_le {κ : CConsts} {T : Stage} {k : ℕ}
    (PT : ProfiledTiling κ T k) (hPT : PT.Valid)
    (hm : PT.tiling.mode = .highSmall ∨ PT.tiling.mode = .highLarge)
    (i : Fin PT.tiling.m) (a : EvenPosition T k)
    (ha : a ∈ evenPatchPositions PT.tiling i) (x : Fin (T.S.N k)) :
    (clusterRawReferenceLaw PT hPT hm).E
      (fun z => (PT.tiling.P i).M * clusterSigma PT hPT hm z.1 z.2 a x) ≤ rowMeanConstant κ := by
  have hleaf : a.1 ∈ PT.tiling.leaf i := (Finset.mem_filter.mp ha).2
  have hpatch : patchAt PT hPT a.1 = i := by
    obtain ⟨hchosen, hunique⟩ := Classical.choose_spec (hPT.tiling_valid.prefix_complete a.1)
    exact (hunique i hleaf).symm
  simpa only [hpatch] using raw_row_mean_le PT hPT hm a x

theorem slice_ref_label_E {κ : CConsts} {T : Stage} {k : ℕ}
    {𝒯 : Tiling κ T k} {i : Fin 𝒯.m} {mesh : Mesh 𝒯}
    (S : SliceSolver κ 𝒯 i mesh) (W : ∀ r, S.Val r)
    (z : IWord 𝒯 i) (F : Fin (T.S.N k) → ℝ) :
    (S.refLaw W).E (fun ω => F (ω.2 z)) =
      ∑ D : Bin 𝒯 i, S.q (S.groupOf z) W D *
        ∑ y, S.U (S.groupOf z) W D y * F y := by
  change (FinLaw.bind (FinLaw.pi (fun g =>
    (⟨S.q g W, S.q_nonneg g W, S.q_sum g W⟩ : FinLaw (Bin 𝒯 i))))
    (fun D => FinLaw.pi fun z =>
      (⟨S.U (S.groupOf z) W (D (S.groupOf z)), S.U_nonneg _ _ _, S.U_sum _ _ _⟩ :
        FinLaw (Fin (T.S.N k))))).E _ = _
  rw [Lane_q_s15_c3.finLaw_bind_E]
  simp_rw [E_pi_coord]
  rw [E_pi_coord
    (fun g => (⟨S.q g W, S.q_nonneg g W, S.q_sum g W⟩ : FinLaw (Bin 𝒯 i)))
    (S.groupOf z)
    (fun D => (⟨S.U (S.groupOf z) W D, S.U_nonneg _ _ _, S.U_sum _ _ _⟩ :
      FinLaw (Fin (T.S.N k))).E F)]
  rfl

theorem raw_slice_label_E {κ : CConsts} {T : Stage} {k : ℕ}
    (PT : ProfiledTiling κ T k) (hPT : PT.Valid)
    (hm : PT.tiling.mode = .highSmall ∨ PT.tiling.mode = .highLarge)
    (s : ClusterSlice PT) (z : IWord PT.tiling s.1)
    (F : Fin (T.S.N k) → ℝ) :
    (sliceRawLaw PT hPT hm s).E (fun ω => F (ω.2.2 z)) =
      ∑ y, (PT.π s.1).w y * F y := by
  let S := clusterSolver PT hPT hm s.1
  have hmean y : S.oddMean PT.parameter (S.groupOf z) y = (PT.π s.1).w y := by
    rw [hPT.high_profile hm s.1]
    exact (hPT.raw_profile (highMode_isCluster PT hm) s.1 S
      (Classical.choose_spec (hPT.cluster_solver (highMode_isCluster PT hm) s.1))
      (S.groupOf z) y).symm
  change (FinLaw.bind (S.recLaw PT.parameter) S.refLaw).E _ = _
  rw [Lane_q_s15_c3.finLaw_bind_E]
  simp_rw [slice_ref_label_E]
  unfold FinLaw.E
  simp_rw [Finset.mul_sum]
  rw [Finset.sum_comm]
  simp_rw [Finset.sum_comm (s := (Finset.univ : Finset (∀ r, S.Val r)))
    (t := (Finset.univ : Finset (Fin (T.S.N k))))]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro y hy
  rw [← hmean y]
  change (∑ D, ∑ W, (S.recLaw PT.parameter).w W *
    (S.q (S.groupOf z) W D * (S.U (S.groupOf z) W D y * F y))) =
      (∑ W, (S.recLaw PT.parameter).w W *
        (∑ D, S.q (S.groupOf z) W D * S.U (S.groupOf z) W D y)) * F y
  rw [Finset.sum_comm, Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro W hW
  rw [Finset.mul_sum, Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro D hD
  ring

theorem raw_slice_nominal_hit_E {κ : CConsts} {T : Stage} {k : ℕ}
    (PT : ProfiledTiling κ T k) (hPT : PT.Valid)
    (hm : PT.tiling.mode = .highSmall ∨ PT.tiling.mode = .highLarge)
    (s : ClusterSlice PT) (z : IWord PT.tiling s.1) (x : Fin (T.S.N k))
    (hd : 0 < deg (T.S.E k) PT.tiling.c (PT.π s.1).w x) :
    (sliceRawLaw PT hPT hm s).E (fun ω =>
      hit (T.S.E k) PT.tiling.c x (ω.2.2 z) /
        deg (T.S.E k) PT.tiling.c (PT.π s.1).w x) = 1 := by
  rw [raw_slice_label_E PT hPT hm s z (fun y =>
    hit (T.S.E k) PT.tiling.c x y / deg (T.S.E k) PT.tiling.c (PT.π s.1).w x)]
  calc
    _ = (∑ y, (PT.π s.1).w y * hit (T.S.E k) PT.tiling.c x y) /
        deg (T.S.E k) PT.tiling.c (PT.π s.1).w x := by
      rw [Finset.sum_div]
      apply Finset.sum_congr rfl
      intro y hy
      ring
    _ = 1 := div_self hd.ne'

def internalOfWordLabels {κ : CConsts} {T : Stage} {k : ℕ}
    {PT : ProfiledTiling κ T k} (B : ClusterBinAssignment PT)
    (ys : ClusterConsultation PT → Fin (T.S.N k)) : ClusterInternalData PT :=
  fun s => (fun g => B ⟨s, g⟩, fun z => ys ⟨s, z⟩)

noncomputable def wordGroup {κ : CConsts} {T : Stage} {k : ℕ}
    (PT : ProfiledTiling κ T k) (hPT : PT.Valid)
    (hm : PT.tiling.mode = .highSmall ∨ PT.tiling.mode = .highLarge)
    (c : ClusterConsultation PT) : ClusterGroupIndex PT :=
  ⟨c.1, (clusterSolver PT hPT hm c.1.1).groupOf c.2⟩

noncomputable def wordLabelLaw {κ : CConsts} {T : Stage} {k : ℕ}
    (PT : ProfiledTiling κ T k) (hPT : PT.Valid)
    (hm : PT.tiling.mode = .highSmall ∨ PT.tiling.mode = .highLarge)
    (W : ClusterHistory PT hPT hm) (B : ClusterBinAssignment PT)
    (c : ClusterConsultation PT) : FinLaw (Fin (T.S.N k)) :=
  ⟨(clusterSolver PT hPT hm c.1.1).U ((wordGroup PT hPT hm c).2)
      (historyOnSlice W c.1) (B (wordGroup PT hPT hm c)),
    (clusterSolver PT hPT hm c.1.1).U_nonneg _ _ _,
    (clusterSolver PT hPT hm c.1.1).U_sum _ _ _⟩

theorem independent_label_E_eq_word_E {κ : CConsts} {T : Stage} {k : ℕ}
    (PT : ProfiledTiling κ T k) (hPT : PT.Valid)
    (hm : PT.tiling.mode = .highSmall ∨ PT.tiling.mode = .highLarge)
    (W : ClusterHistory PT hPT hm) (B : ClusterBinAssignment PT)
    (F : ClusterInternalData PT → ℝ) :
    (clusterIndependentLabelKernel PT hPT hm W B).E F =
      (FinLaw.pi (wordLabelLaw PT hPT hm W B)).E
        (fun ys => F (internalOfWordLabels B ys)) := by
  unfold clusterIndependentLabelKernel
  rw [Lane_q_s15_c3.finLaw_map_E]
  exact (E_pi_sigma (wordLabelLaw PT hPT hm W B)
    (fun ys => F (internalOfWordLabels B ys))).symm

noncomputable def rowWordQueries {κ : CConsts} {T : Stage} {k : ℕ}
    (PT : ProfiledTiling κ T k) (hPT : PT.Valid)
    (hm : PT.tiling.mode = .highSmall ∨ PT.tiling.mode = .highLarge)
    (a : EvenPosition T k) : Finset (ClusterConsultation PT) :=
  Finset.univ.image fun j =>
    ⟨clusterSliceAt PT hPT a.1, flipPos (clusterCenterRole PT hPT hm a).1 j⟩

noncomputable def wordAtOdd {κ : CConsts} {T : Stage} {k : ℕ}
    (PT : ProfiledTiling κ T k) (hPT : PT.Valid)
    (hm : PT.tiling.mode = .highSmall ∨ PT.tiling.mode = .highLarge)
    (b : OddPosition T k) : ClusterConsultation PT :=
  ⟨clusterSliceAt PT hPT b.1, solverWordAt PT hPT hm b.1⟩

noncomputable def keptWordQueries {κ : CConsts} {T : Stage} {k : ℕ}
    (PT : ProfiledTiling κ T k) (hPT : PT.Valid)
    (hm : PT.tiling.mode = .highSmall ∨ PT.tiling.mode = .highLarge)
    (M : ClusterMask PT) : Finset (ClusterConsultation PT) :=
  (clusterKeptRows M).biUnion (fun r => rowWordQueries PT hPT hm (M.positions r)) ∪
    (((clusterKeptRows M).biUnion (fun r => clusterBulkNeighbours PT hPT (M.positions r))).image
      (wordAtOdd PT hPT hm)) ∪
    ((clusterAllowedCrossings PT hPT M \ M.crossingBins).image
      (fun q => wordAtOdd PT hPT hm q.2))

theorem kept_product_bins_irrelevant {κ : CConsts} {T : Stage} {k : ℕ}
    (PT : ProfiledTiling κ T k) (hPT : PT.Valid)
    (hm : PT.tiling.mode = .highSmall ∨ PT.tiling.mode = .highLarge)
    (i : Fin PT.tiling.m) (x : Fin (T.S.N k)) (M : ClusterMask PT)
    (W : ClusterHistory PT hPT hm) (B B' : ClusterBinAssignment PT)
    (ys : ClusterConsultation PT → Fin (T.S.N k)) :
    clusterKeptProduct PT hPT hm i x M W (internalOfWordLabels B ys) =
      clusterKeptProduct PT hPT hm i x M W (internalOfWordLabels B' ys) := rfl

theorem kept_product_word_depends {κ : CConsts} {T : Stage} {k : ℕ}
    (PT : ProfiledTiling κ T k) (hPT : PT.Valid)
    (hm : PT.tiling.mode = .highSmall ∨ PT.tiling.mode = .highLarge)
    (i : Fin PT.tiling.m) (x : Fin (T.S.N k)) (M : ClusterMask PT)
    (W : ClusterHistory PT hPT hm) (B : ClusterBinAssignment PT) :
    FinProb.DependsOn
      (fun ys => clusterKeptProduct PT hPT hm i x M W (internalOfWordLabels B ys))
      (keptWordQueries PT hPT hm M) := by
  intro ys ys' hys
  have hlabel (b : OddPosition T k) (hb : wordAtOdd PT hPT hm b ∈ keptWordQueries PT hPT hm M) :
      clusterLabelFromInternal (hPT := hPT) hm (internalOfWordLabels B ys) b =
        clusterLabelFromInternal (hPT := hPT) hm (internalOfWordLabels B ys') b :=
    hys _ hb
  unfold clusterKeptProduct
  apply congrArg₂ (fun a b : ℝ => a * b)
  · apply Finset.prod_congr rfl
    intro r hr
    have hsigma : clusterSigma PT hPT hm W (internalOfWordLabels B ys) (M.positions r) x =
        clusterSigma PT hPT hm W (internalOfWordLabels B ys') (M.positions r) x := by
      let a := M.positions r
      let s := clusterSliceAt PT hPT a.1
      let v : EvenRole PT.tiling s.1 := clusterCenterRole PT hPT hm a
      change (clusterSolver PT hPT hm s.1).σ v (historyOnSlice W s)
        (fun j => ys ⟨s, flipPos v.1 j⟩) x =
          (clusterSolver PT hPT hm s.1).σ v (historyOnSlice W s)
            (fun j => ys' ⟨s, flipPos v.1 j⟩) x
      apply congrArg (fun labels => (clusterSolver PT hPT hm s.1).σ v (historyOnSlice W s) labels x)
      funext j
      apply hys
      apply Finset.mem_union_left
      apply Finset.mem_union_left
      apply Finset.mem_biUnion.mpr
      refine ⟨r, hr, ?_⟩
      exact Finset.mem_image.mpr ⟨j, Finset.mem_univ _, rfl⟩
    rw [hsigma]
    apply congrArg (fun z : ℝ =>
      (PT.tiling.P i).M * clusterSigma PT hPT hm W (internalOfWordLabels B ys') (M.positions r) x * z)
    apply Finset.prod_congr rfl
    intro b hb
    have hq : wordAtOdd PT hPT hm b ∈ keptWordQueries PT hPT hm M := by
      apply Finset.mem_union_left
      apply Finset.mem_union_right
      apply Finset.mem_image.mpr
      refine ⟨b, ?_, rfl⟩
      exact Finset.mem_biUnion.mpr ⟨r, hr, hb⟩
    dsimp only
    rw [hlabel b hq]
  · apply Finset.prod_congr rfl
    intro q hq
    have hword : wordAtOdd PT hPT hm q.2 ∈ keptWordQueries PT hPT hm M :=
      Finset.mem_union_right _ (Finset.mem_image.mpr ⟨q, hq, rfl⟩)
    dsimp only
    rw [hlabel q.2 hword]

theorem kept_label_integral_bin_depends {κ : CConsts} {T : Stage} {k : ℕ}
    (PT : ProfiledTiling κ T k) (hPT : PT.Valid)
    (hm : PT.tiling.mode = .highSmall ∨ PT.tiling.mode = .highLarge)
    (i : Fin PT.tiling.m) (x : Fin (T.S.N k)) (M : ClusterMask PT)
    (W : ClusterHistory PT hPT hm) :
    ClusterBinDependsOn
      (fun B => (clusterIndependentLabelKernel PT hPT hm W B).E
        (clusterKeptProduct PT hPT hm i x M W))
      ((keptWordQueries PT hPT hm M).image (wordGroup PT hPT hm)) := by
  intro B B' hBB
  dsimp only
  rw [independent_label_E_eq_word_E PT hPT hm W B,
    independent_label_E_eq_word_E PT hPT hm W B']
  calc
    _ = (FinLaw.pi (wordLabelLaw PT hPT hm W B')).E
        (fun ys => clusterKeptProduct PT hPT hm i x M W (internalOfWordLabels B ys)) := by
      apply E_pi_congr_on _ _ (keptWordQueries PT hPT hm M) _
        (kept_product_word_depends PT hPT hm i x M W B)
      intro c hc y
      have hg := hBB (wordGroup PT hPT hm c) (Finset.mem_image.mpr ⟨c, hc, rfl⟩)
      dsimp [wordLabelLaw]
      rw [hg]
    _ = _ := rfl

noncomputable def maskBinQueries {κ : CConsts} {T : Stage} {k : ℕ}
    (PT : ProfiledTiling κ T k) (hPT : PT.Valid)
    (hm : PT.tiling.mode = .highSmall ∨ PT.tiling.mode = .highLarge)
    (M : ClusterMask PT) : Finset (ClusterGroupIndex PT) :=
  (Finset.univ.biUnion (fun r => clusterCoreGroups PT hPT hm (M.positions r)) ∪
    (clusterAllowedCrossings PT hPT M).image
      (fun q => clusterGroupIndexAt PT hPT hm q.2)) ∪
    (keptWordQueries PT hPT hm M).image (wordGroup PT hPT hm)

theorem mask_consistent_bin_depends {κ : CConsts} {T : Stage} {k : ℕ}
    (PT : ProfiledTiling κ T k) (hPT : PT.Valid)
    (hm : PT.tiling.mode = .highSmall ∨ PT.tiling.mode = .highLarge)
    (M : ClusterMask PT) {B B' : ClusterBinAssignment PT}
    (hBB : ∀ g ∈ maskBinQueries PT hPT hm M, B g = B' g) :
    ClusterMaskConsistent PT hPT hm M B ↔ ClusterMaskConsistent PT hPT hm M B' := by
  have hcore r g (hg : g ∈ clusterCoreGroups PT hPT hm (M.positions r)) : B g = B' g := by
    apply hBB
    apply Finset.mem_union_left
    apply Finset.mem_union_left
    exact Finset.mem_biUnion.mpr ⟨r, Finset.mem_univ _, hg⟩
  have hcross q (hq : q ∈ clusterAllowedCrossings PT hPT M) :
      B (clusterGroupIndexAt PT hPT hm q.2) = B' (clusterGroupIndexAt PT hPT hm q.2) := by
    apply hBB
    apply Finset.mem_union_left
    apply Finset.mem_union_right
    exact Finset.mem_image.mpr ⟨q, hq, rfl⟩
  have hcrep r : clusterCoreRepeat PT hPT hm M B r ↔ clusterCoreRepeat PT hPT hm M B' r := by
    unfold clusterCoreRepeat
    apply exists_congr
    intro t
    apply and_congr_right
    intro ht
    apply and_congr_right
    intro htG
    apply exists_congr
    intro g
    apply and_congr_right
    intro hg
    apply exists_congr
    intro g'
    apply and_congr_right
    intro hg'
    rw [hcore r g hg, hcore t g' hg']
  have hxrep q (hq : q ∈ clusterAllowedCrossings PT hPT M) :
      clusterCrossingRepeat PT hPT hm M B q ↔ clusterCrossingRepeat PT hPT hm M B' q := by
    unfold clusterCrossingRepeat
    apply exists_congr
    intro p
    apply and_congr_right
    intro hp
    rw [hcross p hp, hcross q hq]
  unfold ClusterMaskConsistent
  split_ifs
  · apply and_congr
    · apply forall_congr'
      intro r
      rw [hcrep r]
    · apply forall_congr'
      intro q
      have hright : (q ∈ clusterAllowedCrossings PT hPT M ∧ clusterCrossingRepeat PT hPT hm M B q) ↔
          (q ∈ clusterAllowedCrossings PT hPT M ∧ clusterCrossingRepeat PT hPT hm M B' q) := by
        apply and_congr_right
        exact hxrep q
      rw [hright]
  · exact Iff.rfl

theorem masked_label_integral_bin_depends {κ : CConsts} {T : Stage} {k : ℕ}
    (PT : ProfiledTiling κ T k) (hPT : PT.Valid)
    (hm : PT.tiling.mode = .highSmall ∨ PT.tiling.mode = .highLarge)
    (i : Fin PT.tiling.m) (x : Fin (T.S.N k)) (M : ClusterMask PT)
    (W : ClusterHistory PT hPT hm) :
    ClusterBinDependsOn
      (fun B => if ClusterMaskConsistent PT hPT hm M B then
        (clusterIndependentLabelKernel PT hPT hm W B).E
          (clusterKeptProduct PT hPT hm i x M W) else 0)
      (maskBinQueries PT hPT hm M) := by
  intro B B' hBB
  dsimp only
  rw [mask_consistent_bin_depends PT hPT hm M hBB]
  split_ifs
  · apply kept_label_integral_bin_depends PT hPT hm i x M W B B'
    intro g hg
    exact hBB g (Finset.mem_union_right _ hg)
  · rfl

private theorem card_biUnion_le_mul {α β : Type*} [DecidableEq α] [DecidableEq β]
    (A : Finset α) (F : α → Finset β) (n : ℕ) (hF : ∀ a ∈ A, (F a).card ≤ n) :
    (A.biUnion F).card ≤ A.card * n := by
  calc
    _ ≤ ∑ a ∈ A, (F a).card := Finset.card_biUnion_le
    _ ≤ ∑ _a ∈ A, n := Finset.sum_le_sum hF
    _ = _ := by simp

theorem core_groups_card_le {κ : CConsts} {T : Stage} {k : ℕ}
    (PT : ProfiledTiling κ T k) (hPT : PT.Valid)
    (hm : PT.tiling.mode = .highSmall ∨ PT.tiling.mode = .highLarge)
    (a : EvenPosition T k) : (clusterCoreGroups PT hPT hm a).card ≤ T.S.n k := by
  calc
    _ ≤ (Finset.univ.filter fun b : OddPosition T k =>
      Adjacent a b ∧ patchAt PT hPT b.1 = patchAt PT hPT a.1).card := Finset.card_image_le
    _ ≤ (Lane_q_s15_direct.star a).card := by
      apply Finset.card_le_card
      intro b hb
      exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, (Finset.mem_filter.mp hb).2.1⟩
    _ ≤ _ := Lane_q_s15_direct.star_card_le a

theorem bulk_neighbours_card_le {κ : CConsts} {T : Stage} {k : ℕ}
    (PT : ProfiledTiling κ T k) (hPT : PT.Valid) (a : EvenPosition T k) :
    (clusterBulkNeighbours PT hPT a).card ≤ T.S.n k := by
  calc
    _ ≤ (Lane_q_s15_direct.star a).card := by
      apply Finset.card_le_card
      intro b hb
      exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, (Finset.mem_filter.mp hb).2.1⟩
    _ ≤ _ := Lane_q_s15_direct.star_card_le a

theorem crossing_neighbours_card_le {κ : CConsts} {T : Stage} {k : ℕ}
    (PT : ProfiledTiling κ T k) (hPT : PT.Valid) (a : EvenPosition T k) :
    (clusterCrossingNeighbours PT hPT a).card ≤ T.S.n k := by
  calc
    _ ≤ (Lane_q_s15_direct.star a).card := by
      apply Finset.card_le_card
      intro b hb
      exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, (Finset.mem_filter.mp hb).2.1⟩
    _ ≤ _ := Lane_q_s15_direct.star_card_le a

theorem allowed_crossings_card_le {κ : CConsts} {T : Stage} {k : ℕ}
    (PT : ProfiledTiling κ T k) (hPT : PT.Valid) (M : ClusterMask PT) :
    (clusterAllowedCrossings PT hPT M).card ≤ (T.S.n k) ^ 2 := by
  let F (r : Fin (T.S.n k)) :=
    (clusterCrossingNeighbours PT hPT (M.positions r)).image (fun b => (r, b))
  have hsub : clusterAllowedCrossings PT hPT M ⊆ Finset.univ.biUnion F := by
    intro q hq
    apply Finset.mem_biUnion.mpr
    refine ⟨q.1, Finset.mem_univ _, ?_⟩
    exact Finset.mem_image.mpr ⟨q.2, (Finset.mem_filter.mp hq).2.2.2, rfl⟩
  calc
    _ ≤ (Finset.univ.biUnion F).card := Finset.card_le_card hsub
    _ ≤ Finset.univ.card * T.S.n k := by
      apply card_biUnion_le_mul
      intro r hr
      exact (Finset.card_image_le).trans (crossing_neighbours_card_le PT hPT (M.positions r))
    _ = _ := by simp [pow_two]

theorem kept_word_queries_card_le {κ : CConsts} {T : Stage} {k : ℕ}
    (PT : ProfiledTiling κ T k) (hPT : PT.Valid)
    (hm : PT.tiling.mode = .highSmall ∨ PT.tiling.mode = .highLarge)
    (M : ClusterMask PT) : (keptWordQueries PT hPT hm M).card ≤ 3 * (T.S.n k) ^ 2 := by
  have hkept : (clusterKeptRows M).card ≤ T.S.n k := by
    simpa using Finset.card_le_card (Finset.subset_univ (clusterKeptRows M))
  have hrow a : (rowWordQueries PT hPT hm a).card ≤ T.S.n k := by
    calc
      _ ≤ Finset.univ.card := Finset.card_image_le
      _ = (PT.tiling.P (patchAt PT hPT a.1)).h := Fintype.card_fin _
      _ ≤ _ := clusterHeight_le PT hPT _
  have hrows : ((clusterKeptRows M).biUnion
      (fun r => rowWordQueries PT hPT hm (M.positions r))).card ≤ (T.S.n k) ^ 2 := by
    calc
      _ ≤ (clusterKeptRows M).card * T.S.n k :=
        card_biUnion_le_mul _ _ _ (fun r hr => hrow (M.positions r))
      _ ≤ T.S.n k * T.S.n k := Nat.mul_le_mul_right _ hkept
      _ = _ := (pow_two _).symm
  have hbulk : (((clusterKeptRows M).biUnion
      (fun r => clusterBulkNeighbours PT hPT (M.positions r))).image
        (wordAtOdd PT hPT hm)).card ≤ (T.S.n k) ^ 2 := by
    calc
      _ ≤ ((clusterKeptRows M).biUnion
          (fun r => clusterBulkNeighbours PT hPT (M.positions r))).card := Finset.card_image_le
      _ ≤ (clusterKeptRows M).card * T.S.n k :=
        card_biUnion_le_mul _ _ _ (fun r hr => bulk_neighbours_card_le PT hPT (M.positions r))
      _ ≤ T.S.n k * T.S.n k := Nat.mul_le_mul_right _ hkept
      _ = _ := (pow_two _).symm
  have hcross : ((clusterAllowedCrossings PT hPT M \ M.crossingBins).image
      (fun q => wordAtOdd PT hPT hm q.2)).card ≤ (T.S.n k) ^ 2 := by
    exact Finset.card_image_le.trans ((Finset.card_le_card Finset.sdiff_subset).trans
      (allowed_crossings_card_le PT hPT M))
  unfold keptWordQueries
  have houter := Finset.card_union_le
    ((clusterKeptRows M).biUnion (fun r => rowWordQueries PT hPT hm (M.positions r)) ∪
      (((clusterKeptRows M).biUnion (fun r => clusterBulkNeighbours PT hPT (M.positions r))).image
        (wordAtOdd PT hPT hm)))
    ((clusterAllowedCrossings PT hPT M \ M.crossingBins).image
      (fun q => wordAtOdd PT hPT hm q.2))
  have hinner := Finset.card_union_le
    ((clusterKeptRows M).biUnion (fun r => rowWordQueries PT hPT hm (M.positions r)))
    (((clusterKeptRows M).biUnion (fun r => clusterBulkNeighbours PT hPT (M.positions r))).image
      (wordAtOdd PT hPT hm))
  omega

theorem mask_bin_queries_card_le {κ : CConsts} {T : Stage} {k : ℕ}
    (PT : ProfiledTiling κ T k) (hPT : PT.Valid)
    (hm : PT.tiling.mode = .highSmall ∨ PT.tiling.mode = .highLarge)
    (M : ClusterMask PT) : (maskBinQueries PT hPT hm M).card ≤ 5 * (T.S.n k) ^ 2 := by
  have hcore : (Finset.univ.biUnion
      (fun r => clusterCoreGroups PT hPT hm (M.positions r))).card ≤ (T.S.n k) ^ 2 := by
    simpa [pow_two] using card_biUnion_le_mul Finset.univ
      (fun r => clusterCoreGroups PT hPT hm (M.positions r)) (T.S.n k)
      (fun r hr => core_groups_card_le PT hPT hm (M.positions r))
  have hcross : ((clusterAllowedCrossings PT hPT M).image
      (fun q => clusterGroupIndexAt PT hPT hm q.2)).card ≤ (T.S.n k) ^ 2 :=
    Finset.card_image_le.trans (allowed_crossings_card_le PT hPT M)
  have hwords : ((keptWordQueries PT hPT hm M).image (wordGroup PT hPT hm)).card ≤
      3 * (T.S.n k) ^ 2 := Finset.card_image_le.trans (kept_word_queries_card_le PT hPT hm M)
  unfold maskBinQueries
  have houter := Finset.card_union_le
    (Finset.univ.biUnion (fun r => clusterCoreGroups PT hPT hm (M.positions r)) ∪
      (clusterAllowedCrossings PT hPT M).image (fun q => clusterGroupIndexAt PT hPT hm q.2))
    ((keptWordQueries PT hPT hm M).image (wordGroup PT hPT hm))
  have hinner := Finset.card_union_le
    (Finset.univ.biUnion (fun r => clusterCoreGroups PT hPT hm (M.positions r)))
    ((clusterAllowedCrossings PT hPT M).image (fun q => clusterGroupIndexAt PT hPT hm q.2))
  omega

theorem mask_bin_queries_budget {κ : CConsts} {T : Stage} {k : ℕ}
    (PT : ProfiledTiling κ T k) (hPT : PT.Valid)
    (hm : PT.tiling.mode = .highSmall ∨ PT.tiling.mode = .highLarge)
    (M : ClusterMask PT) (hn : 5 ≤ T.S.n k) :
    ((maskBinQueries PT hPT hm M).card : ℝ) ≤ (T.S.n k : ℝ) ^ 3 := by
  have hcard : ((maskBinQueries PT hPT hm M).card : ℝ) ≤ 5 * (T.S.n k : ℝ) ^ 2 := by
    exact_mod_cast mask_bin_queries_card_le PT hPT hm M
  have hnR : (5 : ℝ) ≤ T.S.n k := by exact_mod_cast hn
  calc
    _ ≤ 5 * (T.S.n k : ℝ) ^ 2 := hcard
    _ ≤ (T.S.n k : ℝ) * (T.S.n k : ℝ) ^ 2 :=
      mul_le_mul_of_nonneg_right hnR (sq_nonneg _)
    _ = _ := by ring

noncomputable def rowConsultation {κ : CConsts} {T : Stage} {k : ℕ}
    (PT : ProfiledTiling κ T k) (hPT : PT.Valid)
    (hm : PT.tiling.mode = .highSmall ∨ PT.tiling.mode = .highLarge)
    (a : EvenPosition T k) : ClusterConsultation PT :=
  ⟨clusterSliceAt PT hPT a.1, (clusterCenterRole PT hPT hm a).1⟩

def groupConsultation {κ : CConsts} {T : Stage} {k : ℕ}
    {PT : ProfiledTiling κ T k} (g : ClusterGroupIndex PT) : ClusterConsultation PT :=
  ⟨g.1, (groupCenter g.2).1⟩

noncomputable def referenceConsultations {κ : CConsts} {T : Stage} {k : ℕ}
    (PT : ProfiledTiling κ T k) (hPT : PT.Valid)
    (hm : PT.tiling.mode = .highSmall ∨ PT.tiling.mode = .highLarge)
    (M : ClusterMask PT) : Finset (ClusterConsultation PT) :=
  ((clusterKeptRows M).image (fun r => rowConsultation PT hPT hm (M.positions r))) ∪
    (((keptWordQueries PT hPT hm M).image (wordGroup PT hPT hm)).image groupConsultation)

theorem history_agrees_on_consultation {κ : CConsts} {T : Stage} {k : ℕ}
    (PT : ProfiledTiling κ T k) (hPT : PT.Valid)
    (hm : PT.tiling.mode = .highSmall ∨ PT.tiling.mode = .highLarge)
    (U : Finset (ClusterConsultation PT)) (c : ClusterConsultation PT) (hc : c ∈ U)
    (W W' : ClusterHistory PT hPT hm)
    (hWW : ∀ r ∈ clusterConsultationScope PT hPT hm U, W r = W' r)
    (r : (clusterSolver PT hPT hm c.1.1).Rec)
    (hr : (hammingDist ((clusterSolver PT hPT hm c.1.1).loc r) c.2 : ℝ) ≤
      10 * κ.ρ * (PT.tiling.P c.1.1).h) :
    historyOnSlice W c.1 r = historyOnSlice W' c.1 r := by
  apply hWW ⟨c.1, r⟩
  exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, c, hc, rfl, hr⟩

theorem kept_product_history_eq_on_scope {κ : CConsts} {T : Stage} {k : ℕ}
    (PT : ProfiledTiling κ T k) (hPT : PT.Valid)
    (hm : PT.tiling.mode = .highSmall ∨ PT.tiling.mode = .highLarge)
    (i : Fin PT.tiling.m) (x : Fin (T.S.N k)) (M : ClusterMask PT)
    (W W' : ClusterHistory PT hPT hm)
    (hWW : ∀ r ∈ clusterConsultationScope PT hPT hm (referenceConsultations PT hPT hm M),
      W r = W' r) (I : ClusterInternalData PT) :
    clusterKeptProduct PT hPT hm i x M W I = clusterKeptProduct PT hPT hm i x M W' I := by
  unfold clusterKeptProduct
  apply congrArg (fun z : ℝ => z *
    ∏ q ∈ clusterAllowedCrossings PT hPT M \ M.crossingBins,
      (let d := deg (T.S.E k) PT.tiling.c (PT.π (patchAt PT hPT q.2.1)).w x
       if 0 < d then hit (T.S.E k) PT.tiling.c x
         (clusterLabelFromInternal (hPT := hPT) hm I q.2) / d else 0))
  apply Finset.prod_congr rfl
  intro r hr
  have hc : rowConsultation PT hPT hm (M.positions r) ∈ referenceConsultations PT hPT hm M :=
    Finset.mem_union_left _ (Finset.mem_image.mpr ⟨r, hr, rfl⟩)
  have hsig : clusterSigma PT hPT hm W I (M.positions r) x =
      clusterSigma PT hPT hm W' I (M.positions r) x := by
    let s := clusterSliceAt PT hPT (M.positions r).1
    let v : EvenRole PT.tiling s.1 := clusterCenterRole PT hPT hm (M.positions r)
    have h := (clusterSolver PT hPT hm s.1).σ_local v (historyOnSlice W s) (historyOnSlice W' s)
      (nbrLabels v.1 (I s).2)
      (fun q hq => history_agrees_on_consultation PT hPT hm _ _ hc W W' hWW q hq)
    exact congrFun h x
  rw [hsig]

set_option maxHeartbeats 400000 in
theorem reference_mean_history_depends {κ : CConsts} {T : Stage} {k : ℕ}
    (PT : ProfiledTiling κ T k) (hPT : PT.Valid)
    (hm : PT.tiling.mode = .highSmall ∨ PT.tiling.mode = .highLarge)
    (i : Fin PT.tiling.m) (x : Fin (T.S.N k)) (M : ClusterMask PT) :
    ClusterHistoryDependsOn (clusterReferenceMean PT hPT hm i x M)
      (clusterConsultationScope PT hPT hm (referenceConsultations PT hPT hm M)) := by
  intro W W' hWW
  let G := (keptWordQueries PT hPT hm M).image (wordGroup PT hPT hm)
  have hc (g : ClusterGroupIndex PT) (hg : g ∈ G) :
      groupConsultation g ∈ referenceConsultations PT hPT hm M :=
    Finset.mem_union_right _ (Finset.mem_image.mpr ⟨g, hg, rfl⟩)
  have hnear g (hg : g ∈ G) (r : (clusterSolver PT hPT hm g.1.1).Rec)
      (hr : (hammingDist ((clusterSolver PT hPT hm g.1.1).loc r) (groupCenter g.2).1 : ℝ) ≤
        10 * κ.ρ * (PT.tiling.P g.1.1).h) :
      historyOnSlice W g.1 r = historyOnSlice W' g.1 r :=
    history_agrees_on_consultation PT hPT hm _ (groupConsultation g) (hc g hg) W W' hWW r hr
  have hlabel B : (clusterIndependentLabelKernel PT hPT hm W B).E
      (clusterKeptProduct PT hPT hm i x M W) =
      (clusterIndependentLabelKernel PT hPT hm W' B).E
        (clusterKeptProduct PT hPT hm i x M W') := by
    rw [independent_label_E_eq_word_E PT hPT hm W B,
      independent_label_E_eq_word_E PT hPT hm W' B]
    calc
      _ = (FinLaw.pi (wordLabelLaw PT hPT hm W' B)).E
          (fun ys => clusterKeptProduct PT hPT hm i x M W (internalOfWordLabels B ys)) := by
        apply E_pi_congr_on _ _ (keptWordQueries PT hPT hm M) _
          (kept_product_word_depends PT hPT hm i x M W B)
        intro c hc' y
        have hg : wordGroup PT hPT hm c ∈ G := Finset.mem_image.mpr ⟨c, hc', rfl⟩
        dsimp [wordLabelLaw]
        exact congrFun ((clusterSolver PT hPT hm c.1.1).U_local
          ((clusterSolver PT hPT hm c.1.1).groupOf c.2)
          (historyOnSlice W c.1) (historyOnSlice W' c.1) (B (wordGroup PT hPT hm c))
          (fun r hr => hnear (wordGroup PT hPT hm c) hg r hr)) y
      _ = _ := by
        apply congrArg (FinLaw.E (FinLaw.pi (wordLabelLaw PT hPT hm W' B)))
        funext ys
        exact kept_product_history_eq_on_scope PT hPT hm i x M W W' hWW _
  unfold clusterReferenceMean
  have hbins : (clusterIndependentBinKernel PT hPT hm W).E
      (fun B => (clusterIndependentLabelKernel PT hPT hm W B).E (clusterKeptProduct PT hPT hm i x M W)) =
      (clusterIndependentBinKernel PT hPT hm W').E
        (fun B => (clusterIndependentLabelKernel PT hPT hm W B).E (clusterKeptProduct PT hPT hm i x M W)) := by
    let Q (W : ClusterHistory PT hPT hm) (g : ClusterGroupIndex PT) : FinLaw (clusterBinType g) :=
      ⟨(clusterSolver PT hPT hm g.1.1).q g.2 (historyOnSlice W g.1),
        (clusterSolver PT hPT hm g.1.1).q_nonneg _ _, (clusterSolver PT hPT hm g.1.1).q_sum _ _⟩
    have h := E_pi_congr_on (Q W) (Q W') G
      (fun B => (clusterIndependentLabelKernel PT hPT hm W B).E (clusterKeptProduct PT hPT hm i x M W))
      (kept_label_integral_bin_depends PT hPT hm i x M W)
      (fun g hg D => congrFun ((clusterSolver PT hPT hm g.1.1).q_local _ _ _ (hnear g hg)) D)
    simp only [FinLaw.E, FinLaw.pi, Q] at h
    simp only [FinLaw.E, FinLaw.pi, clusterIndependentBinKernel]
    exact h
  rw [hbins]
  apply congrArg (FinLaw.E (clusterIndependentBinKernel PT hPT hm W'))
  funext B
  exact hlabel B

theorem reference_consultations_budget {κ : CConsts} {T : Stage} {k : ℕ}
    (PT : ProfiledTiling κ T k) (hPT : PT.Valid)
    (hm : PT.tiling.mode = .highSmall ∨ PT.tiling.mode = .highLarge)
    (M : ClusterMask PT) (hn : 2 ≤ T.S.n k) :
    ((referenceConsultations PT hPT hm M).card : ℝ) ≤ (T.S.n k : ℝ) ^ 5 := by
  have hkept : (clusterKeptRows M).card ≤ T.S.n k := by
    simpa using Finset.card_le_card (Finset.subset_univ (clusterKeptRows M))
  have hrow : ((clusterKeptRows M).image
      (fun r => rowConsultation PT hPT hm (M.positions r))).card ≤ T.S.n k :=
    Finset.card_image_le.trans hkept
  have hgrp : (((keptWordQueries PT hPT hm M).image (wordGroup PT hPT hm)).image groupConsultation).card ≤
      3 * (T.S.n k) ^ 2 :=
    Finset.card_image_le.trans (Finset.card_image_le.trans (kept_word_queries_card_le PT hPT hm M))
  have hcard := Finset.card_union_le
    ((clusterKeptRows M).image (fun r => rowConsultation PT hPT hm (M.positions r)))
    (((keptWordQueries PT hPT hm M).image (wordGroup PT hPT hm)).image groupConsultation)
  have hcNat : (referenceConsultations PT hPT hm M).card ≤ T.S.n k + 3 * (T.S.n k) ^ 2 := by
    dsimp [referenceConsultations]
    omega
  have hcR : ((referenceConsultations PT hPT hm M).card : ℝ) ≤
      (T.S.n k : ℝ) + 3 * (T.S.n k : ℝ) ^ 2 := by exact_mod_cast hcNat
  have hnR : (2 : ℝ) ≤ T.S.n k := by exact_mod_cast hn
  have hsq : (T.S.n k : ℝ) ≤ (T.S.n k : ℝ) ^ 2 := by nlinarith
  have hcube : (4 : ℝ) ≤ (T.S.n k : ℝ) ^ 3 := by
    have h := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 2) hnR 3
    norm_num at h
    linarith
  calc
    _ ≤ (T.S.n k : ℝ) + 3 * (T.S.n k : ℝ) ^ 2 := hcR
    _ ≤ 4 * (T.S.n k : ℝ) ^ 2 := by linarith
    _ ≤ (T.S.n k : ℝ) ^ 3 * (T.S.n k : ℝ) ^ 2 :=
      mul_le_mul_of_nonneg_right hcube (sq_nonneg _)
    _ = _ := by ring

theorem kept_product_nonneg {κ : CConsts} {T : Stage} {k : ℕ}
    (PT : ProfiledTiling κ T k) (hPT : PT.Valid)
    (hm : PT.tiling.mode = .highSmall ∨ PT.tiling.mode = .highLarge)
    (i : Fin PT.tiling.m) (x : Fin (T.S.N k)) (M : ClusterMask PT)
    (W : ClusterHistory PT hPT hm) (I : ClusterInternalData PT) :
    0 ≤ clusterKeptProduct PT hPT hm i x M W I := by
  have hsigma (a : EvenPosition T k) : 0 ≤ clusterSigma PT hPT hm W I a x :=
    (clusterSolver PT hPT hm (patchAt PT hPT a.1)).σ_nonneg _ _ _ _
  have hhit (y : Fin (T.S.N k)) : 0 ≤ hit (T.S.E k) PT.tiling.c x y := by
    unfold hit
    split_ifs <;> norm_num
  unfold clusterKeptProduct
  apply mul_nonneg
  · apply Finset.prod_nonneg
    intro r hr
    apply mul_nonneg
    · exact mul_nonneg (Nat.cast_nonneg _) (hsigma _)
    · apply Finset.prod_nonneg
      intro b hb
      dsimp only
      split_ifs with hd
      · exact div_nonneg (hhit _) hd.le
      · exact le_rfl
  · apply Finset.prod_nonneg
    intro q hq
    dsimp only
    split_ifs with hd
    · exact div_nonneg (hhit _) hd.le
    · exact le_rfl

theorem reference_mean_nonneg {κ : CConsts} {T : Stage} {k : ℕ}
    (PT : ProfiledTiling κ T k) (hPT : PT.Valid)
    (hm : PT.tiling.mode = .highSmall ∨ PT.tiling.mode = .highLarge)
    (i : Fin PT.tiling.m) (x : Fin (T.S.N k)) (M : ClusterMask PT)
    (W : ClusterHistory PT hPT hm) :
    0 ≤ clusterReferenceMean PT hPT hm i x M W := by
  apply E_nonneg
  intro B
  apply E_nonneg
  exact kept_product_nonneg PT hPT hm i x M W

theorem raw_bin_repeat_bound_large {κ : CConsts} {T : Stage} {k : ℕ}
    (PT : ProfiledTiling κ T k) (hPT : PT.Valid)
    (hm : PT.tiling.mode = .highSmall ∨ PT.tiling.mode = .highLarge)
    (hlarge : PT.tiling.mode = .highLarge)
    (i : Fin PT.tiling.m) (x : Fin (T.S.N k)) (M : ClusterMask PT)
    (W : ClusterHistory PT hPT hm) :
    (clusterIndependentBinKernel PT hPT hm W).E
      (fun B => if ClusterMaskConsistent PT hPT hm M B then
        (clusterIndependentLabelKernel PT hPT hm W B).E
          (clusterKeptProduct PT hPT hm i x M W) else 0) ≤
      clusterCoreRepeatCost PT i ^ M.coreBins.card *
        clusterCrossingFraction T k ^ M.crossingBins.card *
          clusterReferenceMean PT hPT hm i x M W := by
  classical
  have hpred B : ClusterMaskConsistent PT hPT hm M B ↔ M.coreBins = ∅ ∧ M.crossingBins = ∅ := by
    simp [ClusterMaskConsistent, hlarge]
  by_cases hempty : M.coreBins = ∅ ∧ M.crossingBins = ∅
  · have heq : (clusterIndependentBinKernel PT hPT hm W).E
        (fun B => if ClusterMaskConsistent PT hPT hm M B then
          (clusterIndependentLabelKernel PT hPT hm W B).E
            (clusterKeptProduct PT hPT hm i x M W) else 0) =
        clusterReferenceMean PT hPT hm i x M W := by
      apply congrArg (FinLaw.E (clusterIndependentBinKernel PT hPT hm W))
      funext B
      simp [hpred, hempty]
    rw [heq]
    simp [hempty.1, hempty.2]
  · have heq : (clusterIndependentBinKernel PT hPT hm W).E
        (fun B => if ClusterMaskConsistent PT hPT hm M B then
          (clusterIndependentLabelKernel PT hPT hm W B).E
            (clusterKeptProduct PT hPT hm i x M W) else 0) = 0 := by
      simp [FinLaw.E, hpred, hempty]
    rw [heq]
    have hcore : 0 ≤ clusterCoreRepeatCost PT i := by unfold clusterCoreRepeatCost; positivity
    have hcross : 0 ≤ clusterCrossingFraction T k := by unfold clusterCrossingFraction; positivity
    exact mul_nonneg (mul_nonneg (pow_nonneg hcore _) (pow_nonneg hcross _))
      (reference_mean_nonneg PT hPT hm i x M W)

theorem after_label_bin_comparison {κ : CConsts} {T : Stage} {k : ℕ}
    (PT : ProfiledTiling κ T k) (hPT : PT.Valid)
    (hm : PT.tiling.mode = .highSmall ∨ PT.tiling.mode = .highLarge)
    (CS : ClusterSample PT hPT hm) (i : Fin PT.tiling.m) (x : Fin (T.S.N k))
    (M : ClusterMask PT) (hn : 1 ≤ T.S.n k)
    (S : Finset (ClusterGroupIndex PT))
    (hdep : ∀ W, ClusterBinDependsOn
      (fun B => if ClusterMaskConsistent PT hPT hm M B then
        (clusterIndependentLabelKernel PT hPT hm W B).E
          (clusterKeptProduct PT hPT hm i x M W) else 0) S)
    (hS : (S.card : ℝ) ≤ (T.S.n k : ℝ) ^ 3) :
    clusterAfterLabelIntegral CS i x M ≤
      2 * CS.binStage.historyLaw.E (fun W =>
        (clusterIndependentBinKernel PT hPT hm W).E fun B =>
          if ClusterMaskConsistent PT hPT hm M B then
            (clusterIndependentLabelKernel PT hPT hm W B).E
              (clusterKeptProduct PT hPT hm i x M W) else 0) := by
  let F := fun W B => if ClusterMaskConsistent PT hPT hm M B then
    (clusterIndependentLabelKernel PT hPT hm W B).E
      (clusterKeptProduct PT hPT hm i x M W) else 0
  have hF W B : 0 ≤ F W B := by
    dsimp [F]
    split_ifs
    · exact E_nonneg _ _ (kept_product_nonneg PT hPT hm i x M W)
    · exact le_rfl
  have hC : 1 + 1 / (T.S.n k : ℝ) ≤ 2 := by
    have hnR : (1 : ℝ) ≤ T.S.n k := by exact_mod_cast hn
    have h := one_div_le_one_div_of_le (by norm_num : (0 : ℝ) < 1) hnR
    norm_num at h ⊢
    linarith
  change CS.binStage.historyLaw.E (fun W => if clusterHistoryLoad PT hPT hm W then
    (CS.binStage.binLaw W).E (F W) else 0) ≤
      2 * CS.binStage.historyLaw.E (fun W => (clusterIndependentBinKernel PT hPT hm W).E (F W))
  rw [← E_mul_const]
  unfold FinLaw.E
  apply Finset.sum_le_sum
  intro W hW
  by_cases hw : CS.binStage.historyLaw.w W = 0
  · simp [hw]
  · apply mul_le_mul_of_nonneg_left _ (CS.binStage.historyLaw.nonneg W)
    by_cases hload : clusterHistoryLoad PT hPT hm W
    · simp only [if_pos hload]
      calc
        _ ≤ (1 + 1 / (T.S.n k : ℝ)) *
            (clusterIndependentBinKernel PT hPT hm W).E (F W) :=
          CS.binStage.local_upper_comparison W hw hload (F W) (hF W) S (hdep W) hS
        _ ≤ 2 * (clusterIndependentBinKernel PT hPT hm W).E (F W) :=
          mul_le_mul_of_nonneg_right hC (E_nonneg _ _ (hF W))
    · simp only [if_neg hload]
      exact mul_nonneg (by norm_num) (E_nonneg _ _ (hF W))

theorem after_label_le_reference
    {κ : CConsts} {T : Stage} {k : ℕ}
    (PT : ProfiledTiling κ T k) (hPT : PT.Valid)
    (hm : PT.tiling.mode = .highSmall ∨ PT.tiling.mode = .highLarge)
    (CS : ClusterSample PT hPT hm) (i : Fin PT.tiling.m) (x : Fin (T.S.N k))
    (M : ClusterMask PT) (hn : 1 ≤ T.S.n k)
    (S : Finset (ClusterGroupIndex PT))
    (hdep : ∀ W, ClusterBinDependsOn
      (fun B => if ClusterMaskConsistent PT hPT hm M B then
        (clusterIndependentLabelKernel PT hPT hm W B).E
          (clusterKeptProduct PT hPT hm i x M W) else 0) S)
    (hS : (S.card : ℝ) ≤ (T.S.n k : ℝ) ^ 3) :
    clusterAfterLabelIntegral CS i x M ≤
      2 * CS.binStage.historyLaw.E (clusterReferenceMean PT hPT hm i x M) := by
  calc
    _ ≤ 2 * CS.binStage.historyLaw.E (fun W =>
        (clusterIndependentBinKernel PT hPT hm W).E fun B =>
          if ClusterMaskConsistent PT hPT hm M B then
            (clusterIndependentLabelKernel PT hPT hm W B).E
              (clusterKeptProduct PT hPT hm i x M W) else 0) :=
      after_label_bin_comparison PT hPT hm CS i x M hn S hdep hS
    _ ≤ 2 * CS.binStage.historyLaw.E (clusterReferenceMean PT hPT hm i x M) := by
      apply mul_le_mul_of_nonneg_left _ (by norm_num)
      apply E_mono
      intro W
      apply E_mono
      intro B
      split_ifs
      · exact le_rfl
      · exact E_nonneg _ _ (kept_product_nonneg PT hPT hm i x M W)

theorem bin_transfer_of_scope_and_reverse
    {κ : CConsts} {T : Stage} {k : ℕ}
    (PT : ProfiledTiling κ T k) (hPT : PT.Valid)
    (hm : PT.tiling.mode = .highSmall ∨ PT.tiling.mode = .highLarge)
    (CS : ClusterSample PT hPT hm) (i : Fin PT.tiling.m) (x : Fin (T.S.N k))
    (M : ClusterMask PT) (hn : 1 ≤ T.S.n k)
    (S : Finset (ClusterGroupIndex PT))
    (hdep : ∀ W, ClusterBinDependsOn
      (fun B => if ClusterMaskConsistent PT hPT hm M B then
        (clusterIndependentLabelKernel PT hPT hm W B).E
          (clusterKeptProduct PT hPT hm i x M W) else 0) S)
    (hS : (S.card : ℝ) ≤ (T.S.n k : ℝ) ^ 3)
    (hreverse : ∀ W, (clusterIndependentBinKernel PT hPT hm W).E
      (fun B => if ClusterMaskConsistent PT hPT hm M B then
        (clusterIndependentLabelKernel PT hPT hm W B).E
          (clusterKeptProduct PT hPT hm i x M W) else 0) ≤
        clusterCoreRepeatCost PT i ^ M.coreBins.card *
          clusterCrossingFraction T k ^ M.crossingBins.card *
            clusterReferenceMean PT hPT hm i x M W) :
    clusterAfterLabelIntegral CS i x M ≤
      2 * clusterCoreRepeatCost PT i ^ M.coreBins.card *
        clusterCrossingFraction T k ^ M.crossingBins.card *
          CS.binStage.historyLaw.E (clusterReferenceMean PT hPT hm i x M) := by
  calc
    _ ≤ 2 * CS.binStage.historyLaw.E (fun W =>
        (clusterIndependentBinKernel PT hPT hm W).E fun B =>
          if ClusterMaskConsistent PT hPT hm M B then
            (clusterIndependentLabelKernel PT hPT hm W B).E
              (clusterKeptProduct PT hPT hm i x M W) else 0) :=
      after_label_bin_comparison PT hPT hm CS i x M hn S hdep hS
    _ ≤ 2 * CS.binStage.historyLaw.E (fun W =>
        (clusterCoreRepeatCost PT i ^ M.coreBins.card *
          clusterCrossingFraction T k ^ M.crossingBins.card) *
            clusterReferenceMean PT hPT hm i x M W) := by
      apply mul_le_mul_of_nonneg_left _ (by norm_num)
      exact E_mono _ hreverse
    _ = _ := by rw [E_mul_const]; ring

theorem independent_bin_atom_le {κ : CConsts} {T : Stage} {k : ℕ}
    (PT : ProfiledTiling κ T k) (hPT : PT.Valid)
    (hm : PT.tiling.mode = .highSmall ∨ PT.tiling.mode = .highLarge)
    (W : ClusterHistory PT hPT hm) (g : ClusterGroupIndex PT)
    (D : Finset (Fin (T.S.N k))) :
    (clusterIndependentBinKernel PT hPT hm W).pr (fun B => (B g).1 = D) ≤
      4 * Real.exp (2 * (PT.tiling.kScale g.1.1 : ℝ) * PT.tiling.tScale g.1.1) *
        (PT.tiling.P g.1.1).d / (PT.tiling.P g.1.1).M := by
  let Q (g : ClusterGroupIndex PT) : FinLaw (Bin PT.tiling g.1.1) :=
    ⟨(clusterSolver PT hPT hm g.1.1).q g.2 (historyOnSlice W g.1),
      (clusterSolver PT hPT hm g.1.1).q_nonneg _ _,
      (clusterSolver PT hPT hm g.1.1).q_sum _ _⟩
  have hmarg : (clusterIndependentBinKernel PT hPT hm W).pr (fun B => (B g).1 = D) =
      (Q g).pr (fun B => B.1 = D) := by
    rw [pr_eq_E_indicator, pr_eq_E_indicator]
    have h := E_pi_coord Q g (fun B => if B.1 = D then (1 : ℝ) else 0)
    simp only [FinLaw.E, FinLaw.pi, Q] at h
    simp only [FinLaw.E, FinLaw.pi, clusterIndependentBinKernel, Q]
    convert h using 1 <;> congr 1 <;> ext <;> simp
  rw [hmarg]
  apply pr_injective_value_le_cap _ Subtype.val Subtype.val_injective _
  · positivity
  · exact (clusterSolver PT hPT hm g.1.1).q_cap g.2 (historyOnSlice W g.1)

theorem independent_bins_fixed_repeat_le {κ : CConsts} {T : Stage} {k : ℕ}
    (PT : ProfiledTiling κ T k) (hPT : PT.Valid)
    (hm : PT.tiling.mode = .highSmall ∨ PT.tiling.mode = .highLarge)
    (W : ClusterHistory PT hPT hm) (i : Fin PT.tiling.m)
    (C : Finset (ClusterGroupIndex PT)) (hi : ∀ g ∈ C, g.1.1 = i)
    (D : Finset (Finset (Fin (T.S.N k)))) :
    (clusterIndependentBinKernel PT hPT hm W).pr (fun B => ∃ g ∈ C, (B g).1 ∈ D) ≤
      (C.card : ℝ) * D.card *
        (4 * Real.exp (2 * (PT.tiling.kScale i : ℝ) * PT.tiling.tScale i) *
          (PT.tiling.P i).d / (PT.tiling.P i).M) := by
  calc
    _ ≤ ∑ g ∈ C, (clusterIndependentBinKernel PT hPT hm W).pr
        (fun B => (B g).1 ∈ D) := pr_finset_exists_le_sum _ C _
    _ ≤ ∑ g ∈ C, ∑ E ∈ D,
        (4 * Real.exp (2 * (PT.tiling.kScale i : ℝ) * PT.tiling.tScale i) *
          (PT.tiling.P i).d / (PT.tiling.P i).M) := by
      apply Finset.sum_le_sum
      intro g hg
      have heq : (fun B : ClusterBinAssignment PT => (B g).1 ∈ D) =
          (fun B => ∃ E ∈ D, (B g).1 = E) := by
        funext B
        simp
      rw [heq]
      apply le_trans (pr_finset_exists_le_sum _ D _)
      apply Finset.sum_le_sum
      intro E hE
      simpa only [hi g hg] using independent_bin_atom_le PT hPT hm W g E
    _ = _ := by simp [mul_assoc]

theorem history_mean_comparison {κ : CConsts} {T : Stage} {k : ℕ}
    (PT : ProfiledTiling κ T k) (hPT : PT.Valid)
    (hm : PT.tiling.mode = .highSmall ∨ PT.tiling.mode = .highLarge)
    (CS : ClusterSample PT hPT hm) (i : Fin PT.tiling.m) (x : Fin (T.S.N k))
    (M : ClusterMask PT) (hn : 1 ≤ T.S.n k)
    (U : Finset (ClusterConsultation PT))
    (hdep : ClusterHistoryDependsOn (clusterReferenceMean PT hPT hm i x M)
      (clusterConsultationScope PT hPT hm U))
    (hU : (U.card : ℝ) ≤ (T.S.n k : ℝ) ^ 5) :
    CS.binStage.historyLaw.E (clusterReferenceMean PT hPT hm i x M) ≤
      2 * (clusterHistoryLaw PT hPT hm).E (clusterReferenceMean PT hPT hm i x M) := by
  have hraw := E_nonneg (clusterHistoryLaw PT hPT hm)
    (clusterReferenceMean PT hPT hm i x M) (reference_mean_nonneg PT hPT hm i x M)
  have hnR : (1 : ℝ) ≤ T.S.n k := by exact_mod_cast hn
  calc
    _ ≤ (1 + 1 / (T.S.n k : ℝ)) *
        (clusterHistoryLaw PT hPT hm).E (clusterReferenceMean PT hPT hm i x M) :=
      CS.binStage.history_local_upper_comparison _
        (reference_mean_nonneg PT hPT hm i x M) U hdep hU
    _ ≤ 2 * (clusterHistoryLaw PT hPT hm).E (clusterReferenceMean PT hPT hm i x M) := by
      apply mul_le_mul_of_nonneg_right _ hraw
      have h := one_div_le_one_div_of_le (by norm_num : (0 : ℝ) < 1) hnR
      norm_num at h ⊢
      linarith

theorem history_restore_of_scope_and_factorization
    {κ : CConsts} {T : Stage} {k : ℕ}
    (PT : ProfiledTiling κ T k) (hPT : PT.Valid)
    (hm : PT.tiling.mode = .highSmall ∨ PT.tiling.mode = .highLarge)
    (CS : ClusterSample PT hPT hm) (i : Fin PT.tiling.m) (x : Fin (T.S.N k))
    (M : ClusterMask PT) (hn : 1 ≤ T.S.n k)
    (U : Finset (ClusterConsultation PT))
    (hdep : ClusterHistoryDependsOn (clusterReferenceMean PT hPT hm i x M)
      (clusterConsultationScope PT hPT hm U))
    (hU : (U.card : ℝ) ≤ (T.S.n k : ℝ) ^ 5)
    (hpositions : ∀ r, M.positions r ∈ evenPatchPositions PT.tiling i)
    (hfactor : (clusterHistoryLaw PT hPT hm).E (clusterReferenceMean PT hPT hm i x M) =
      ∏ r ∈ clusterKeptRows M, (clusterRawReferenceLaw PT hPT hm).E
        (fun z => (PT.tiling.P i).M * clusterSigma PT hPT hm z.1 z.2 (M.positions r) x)) :
    (clusterHistoryLaw PT hPT hm).E (clusterReferenceMean PT hPT hm i x M) =
      ∏ r ∈ clusterKeptRows M, (clusterRawReferenceLaw PT hPT hm).E
        (fun z => (PT.tiling.P i).M * clusterSigma PT hPT hm z.1 z.2 (M.positions r) x) ∧
    CS.binStage.historyLaw.E (clusterReferenceMean PT hPT hm i x M) ≤
      2 * rowMeanConstant κ ^ (clusterKeptRows M).card := by
  refine ⟨hfactor, ?_⟩
  calc
    _ ≤ 2 * (clusterHistoryLaw PT hPT hm).E (clusterReferenceMean PT hPT hm i x M) :=
      history_mean_comparison PT hPT hm CS i x M hn U hdep hU
    _ = 2 * ∏ r ∈ clusterKeptRows M, (clusterRawReferenceLaw PT hPT hm).E
        (fun z => (PT.tiling.P i).M * clusterSigma PT hPT hm z.1 z.2 (M.positions r) x) := by
      rw [hfactor]
    _ ≤ 2 * ∏ _r ∈ clusterKeptRows M, rowMeanConstant κ := by
      apply mul_le_mul_of_nonneg_left _ (by norm_num)
      apply Finset.prod_le_prod₀
      · intro r hr
        apply E_nonneg
        intro z
        exact mul_nonneg (Nat.cast_nonneg _)
          ((clusterSolver PT hPT hm (patchAt PT hPT (M.positions r).1)).σ_nonneg _ _ _ _)
      · intro r hr
        exact raw_patch_row_mean_le PT hPT hm i (M.positions r) (hpositions r) x
    _ = 2 * rowMeanConstant κ ^ (clusterKeptRows M).card := by simp

theorem core_near_symm {κ : CConsts} {T : Stage} {k : ℕ}
    (PT : ProfiledTiling κ T k) (hPT : PT.Valid) (i : Fin PT.tiling.m)
    (a b : EvenPosition T k) :
    clusterCoreNear PT hPT i a b ↔ clusterCoreNear PT hPT i b a := by
  simp only [clusterCoreNear, hammingDist_comm]

theorem kept_not_core_near {κ : CConsts} {T : Stage} {k : ℕ}
    (PT : ProfiledTiling κ T k) (hPT : PT.Valid) (i : Fin PT.tiling.m)
    (M : ClusterMask PT) (hM : ClusterMaskGeometry PT hPT i M)
    {r t : Fin (T.S.n k)} (hr : r ∈ clusterKeptRows M)
    (ht : t ∈ clusterKeptRows M) (hrt : r ≠ t) :
    ¬ clusterCoreNear PT hPT i (M.positions r) (M.positions t) := by
  have hrG : r ∉ M.geometric := by
    have h := (Finset.mem_sdiff.mp hr).2
    exact fun hg => h (Finset.mem_union_left _ hg)
  have htG : t ∉ M.geometric := by
    have h := (Finset.mem_sdiff.mp ht).2
    exact fun hg => h (Finset.mem_union_left _ hg)
  intro hnear
  rcases lt_or_gt_of_ne hrt with hrt | htr
  · exact htG ((hM.2.1 t).mpr ⟨r, hrt, hnear⟩)
  · exact hrG ((hM.2.1 r).mpr ⟨t, htr,
      (core_near_symm PT hPT i _ _).mp hnear⟩)

end HypercubeRamsey.Lane_sol_s15_transfer
