import HypercubeRamsey.Framework.FinProbLemmas

namespace HypercubeRamsey.Clock

open scoped BigOperators

/-- The probabilities of an event and its complement add to one. -/
theorem finProb_pr_compl {α : Type*} [Fintype α] (P : FinProb α) (A : α → Prop) :
    P.pr A + P.pr (fun x => ¬ A x) = 1 := by
  classical
  letI : DecidablePred A := fun x => Classical.propDecidable (A x)
  letI : DecidablePred (fun x => ¬ A x) := fun x => Classical.propDecidable (¬ A x)
  unfold FinProb.pr
  rw [← Finset.sum_add_distrib]
  convert P.sum_eq_one using 1
  apply Finset.sum_congr rfl
  intro x hx
  by_cases h : A x <;> simp [h]

theorem finProb_pr_nonneg {α : Type*} [Fintype α] (P : FinProb α) (A : α → Prop) :
    0 ≤ P.pr A := by
  classical
  unfold FinProb.pr
  exact Finset.sum_nonneg fun x _ => by
    split_ifs
    · exact P.nonneg x
    · exact le_rfl

theorem finProb_pr_mono {α : Type*} [Fintype α] (P : FinProb α)
    {A B : α → Prop} (hAB : ∀ x, A x → B x) : P.pr A ≤ P.pr B := by
  classical
  unfold FinProb.pr
  apply Finset.sum_le_sum
  intro x hx
  by_cases hA : A x
  · by_cases hB : B x
    · simp [hA, hB]
    · exact False.elim (hB (hAB x hA))
  · by_cases hB : B x
    · simpa [hA, hB] using P.nonneg x
    · simp [hA, hB]

/-- A finite probability law has nonempty support space. -/
theorem finProb_nonempty {α : Type*} [Fintype α] (P : FinProb α) : Nonempty α := by
  classical
  by_contra h
  haveI : IsEmpty α := ⟨fun a => h ⟨a⟩⟩
  have hsum : (∑ a, P.w a) = 0 := by simp
  rw [P.sum_eq_one] at hsum
  norm_num at hsum

/-- A finite union of events has probability at most the sum of their probabilities. -/
theorem finProb_pr_biUnion_le_sum {α κ : Type*} [Fintype α] [DecidableEq α]
    (P : FinProb α) (s : Finset κ) (E : κ → α → Prop) :
    P.pr (fun x => ∃ k ∈ s, E k x) ≤ ∑ k ∈ s, P.pr (E k) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [FinProb.pr]
  | @insert k s hk ih =>
      have hEq : (fun x => ∃ j ∈ insert k s, E j x) =
          (fun x => E k x ∨ ∃ j ∈ s, E j x) := by
        funext x
        simp [hk]
      calc
        P.pr (fun x => ∃ j ∈ insert k s, E j x) =
            P.pr (fun x => E k x ∨ ∃ j ∈ s, E j x) := by rw [hEq]
        _ ≤ P.pr (E k) + P.pr (fun x => ∃ j ∈ s, E j x) := FinProb.pr_union P _ _
        _ ≤ P.pr (E k) + ∑ j ∈ s, P.pr (E j) := add_le_add le_rfl ih
        _ = ∑ j ∈ insert k s, P.pr (E j) := by simp [hk]

/-- A coordinate of a finite product law has its declared one-coordinate marginal. -/
theorem pi_pr_coordinate {ι : Type*} [Fintype ι] [DecidableEq ι]
    {Ω : ι → Type*} [∀ i, Fintype (Ω i)] (P : ∀ i, FinProb (Ω i))
    (i : ι) (o : Ω i) :
    (FinProb.pi P).pr (fun ω => ω i = o) = (P i).w o := by
  classical
  let S : Finset ι := {i}
  let J := {j // j ∈ S}
  letI : Unique J := ⟨⟨i, by simp [S]⟩, fun j => by
    apply Subtype.ext
    exact Finset.mem_singleton.mp j.2⟩
  let j₀ : J := default
  let f : (∀ j : {j // j ∈ S}, Ω j.1) → ℝ := fun x => if x j₀ = o then 1 else 0
  have hm := FinProb.pi_marginal_expect P S f
  have hleft : (FinProb.pi P).expect (fun ω => if ω i = o then 1 else 0) =
      (FinProb.pi P).pr (fun ω => ω i = o) := by
    simp [FinProb.expect, FinProb.pr, FinProb.pi]
  have hmid : (FinProb.pi P).expect (fun ω => if ω i = o then 1 else 0) =
      (FinProb.pi P).expect (fun ω => f (fun j => ω j.1)) := by
    simpa [f, j₀, S, J] using hm
  have hright : (FinProb.pi (fun j : {j // j ∈ S} => P j.1)).expect f = (P i).w o := by
    let e : (∀ j : J, Ω j.1) ≃ Ω i := Equiv.piUnique (fun j : J => Ω j.1)
    change (∑ x : (∀ j : J, Ω j.1),
      (∏ j : J, (P j.1).w (x j)) * f x) = (P i).w o
    rw [← Equiv.sum_comp e.symm]
    simp only [e, Equiv.piUnique_apply, f, j₀, S, J, mul_ite, mul_one, mul_zero]
    simpa using (Finset.sum_ite_eq' Finset.univ o (fun x => (P i).w x))
  calc
    (FinProb.pi P).pr (fun ω => ω i = o) =
        (FinProb.pi P).expect (fun ω => if ω i = o then 1 else 0) := hleft.symm
    _ = (FinProb.pi P).expect (fun ω => f (fun j => ω j.1)) := hmid
    _ = (FinProb.pi (fun j : {j // j ∈ S} => P j.1)).expect f := hm
    _ = (P i).w o := hright

/-- Pinning one coordinate and averaging its conditional failure probability recovers the event probability. -/
theorem pi_pinned_expect {ι : Type*} [Fintype ι] [DecidableEq ι]
    {Ω : ι → Type*} [∀ i, Fintype (Ω i)] (P : ∀ i, FinProb (Ω i))
    (F : (∀ i, Ω i) → Prop) (i : ι) :
    (P i).expect (fun o =>
      (FinProb.pi P).pr (fun ω => F ω ∧ ω i = o) / (P i).w o) =
        (FinProb.pi P).pr F := by
  classical
  let Q := FinProb.pi P
  have hterm : ∀ o : Ω i,
      (P i).w o * (Q.pr (fun ω => F ω ∧ ω i = o) / (P i).w o) =
        Q.pr (fun ω => F ω ∧ ω i = o) := by
    intro o
    have hbound := finProb_pr_mono Q
      (A := fun ω => F ω ∧ ω i = o) (B := fun ω => ω i = o)
      (by intro ω h; exact h.2)
    rw [pi_pr_coordinate] at hbound
    by_cases hz : (P i).w o = 0
    · have hzero : Q.pr (fun ω => F ω ∧ ω i = o) = 0 := by
        apply le_antisymm
        · simpa [hz] using hbound
        · exact finProb_pr_nonneg Q _
      simp [hz, hzero]
    · field_simp [hz]
  have hsum :
      (∑ o : Ω i, Q.pr (fun ω => F ω ∧ ω i = o)) = Q.pr F := by
    unfold FinProb.pr
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro ω hω
    by_cases hF : F ω
    · simp [hF, Q, FinProb.pi]
    · simp [hF, Q]
  calc
    (P i).expect (fun o => Q.pr (fun ω => F ω ∧ ω i = o) / (P i).w o) =
        ∑ o : Ω i, (P i).w o *
          (Q.pr (fun ω => F ω ∧ ω i = o) / (P i).w o) := rfl
    _ = ∑ o : Ω i, Q.pr (fun ω => F ω ∧ ω i = o) := by
      apply Finset.sum_congr rfl
      intro o ho
      exact hterm o
    _ = Q.pr F := hsum

/-- Product probabilities of an event depending on `s` compare using only the rows in `s`. -/
theorem pi_pr_depends_le {ι : Type*} [Fintype ι] [DecidableEq ι]
    {Ω : ι → Type*} [∀ i, Fintype (Ω i)] (P Q : ∀ i, FinProb (Ω i))
    (s : Finset ι) (F : (∀ i, Ω i) → Prop)
    (hF : FinProb.DependsOn F s) (L : ℝ) (hL : 0 ≤ L)
    (hweight : ∀ i ∈ s, ∀ o, (Q i).w o ≤ L * (P i).w o) :
    (FinProb.pi Q).pr F ≤ L ^ s.card * (FinProb.pi P).pr F := by
  classical
  let ω₀ : ∀ i, Ω i := fun i => Classical.choice (finProb_nonempty (P i))
  let e := Equiv.piEquivPiSubtypeProd (fun i => i ∈ s) Ω
  let lift (a : ∀ i : {i // i ∈ s}, Ω i.1) : ∀ i, Ω i :=
    e.symm (a, fun i => ω₀ i.1)
  let indicator : (∀ i, Ω i) → ℝ := fun ω => if F ω then 1 else 0
  let eventOnS (a : ∀ i : {i // i ∈ s}, Ω i.1) : Prop := F (lift a)
  have hdepIndicator : FinProb.DependsOn indicator s := by
    intro ω ω' hagree
    simp only [indicator]
    rw [hF ω ω' hagree]
  have hQ := FinProb.pi_expect_depends Q s indicator ω₀ hdepIndicator
  have hP := FinProb.pi_expect_depends P s indicator ω₀ hdepIndicator
  have hQ' : (FinProb.pi Q).pr F =
      (FinProb.pi (fun i : {i // i ∈ s} => Q i.1)).pr eventOnS := by
    simpa [FinProb.pr, FinProb.expect, indicator, eventOnS, lift, e]
      using hQ
  have hP' : (FinProb.pi P).pr F =
      (FinProb.pi (fun i : {i // i ∈ s} => P i.1)).pr eventOnS := by
    simpa [FinProb.pr, FinProb.expect, indicator, eventOnS, lift, e]
      using hP
  let Qs := FinProb.pi (fun i : {i // i ∈ s} => Q i.1)
  let Ps := FinProb.pi (fun i : {i // i ∈ s} => P i.1)
  have hweightS : ∀ a, Qs.w a ≤ L ^ s.card * Ps.w a := by
    intro a
    change (∏ i : {i // i ∈ s}, (Q i.1).w (a i)) ≤
      L ^ s.card * ∏ i : {i // i ∈ s}, (P i.1).w (a i)
    calc
      (∏ i : {i // i ∈ s}, (Q i.1).w (a i)) ≤
          ∏ i : {i // i ∈ s}, (L * (P i.1).w (a i)) := by
        apply Finset.prod_le_prod₀
        · intro i hi
          exact (Q i.1).nonneg (a i)
        · intro i hi
          exact hweight i.1 i.2 (a i)
      _ = L ^ s.card * ∏ i : {i // i ∈ s}, (P i.1).w (a i) := by
        rw [Finset.prod_mul_distrib]
        have hconst : (∏ i : {i // i ∈ s}, L) = L ^ s.card := by
          calc
            (∏ i : {i // i ∈ s}, L) = ∏ i ∈ s, L := by
              rw [Finset.univ_eq_attach]
              simpa using (Finset.prod_attach s (fun _ => L))
            _ = L ^ s.card := by simp
        rw [hconst]
  have hprobS : Qs.pr eventOnS ≤ L ^ s.card * Ps.pr eventOnS := by
    unfold FinProb.pr
    calc
      (∑ a, if eventOnS a then Qs.w a else 0) ≤
          ∑ a, if eventOnS a then L ^ s.card * Ps.w a else 0 := by
        apply Finset.sum_le_sum
        intro a ha
        by_cases he : eventOnS a
        · simpa [he] using hweightS a
        · simp [he]
      _ = L ^ s.card * Ps.pr eventOnS := by
        rw [FinProb.pr]
        calc
          (∑ a, if eventOnS a then L ^ s.card * Ps.w a else 0) =
              ∑ a, L ^ s.card * (if eventOnS a then Ps.w a else 0) := by
            apply Finset.sum_congr rfl
            intro a ha
            by_cases he : eventOnS a <;> simp [he]
          _ = L ^ s.card * ∑ a, if eventOnS a then Ps.w a else 0 := by
            rw [← Finset.mul_sum]
  calc
    (FinProb.pi Q).pr F = Qs.pr eventOnS := hQ'
    _ ≤ L ^ s.card * Ps.pr eventOnS := hprobS
    _ = L ^ s.card * (FinProb.pi P).pr F := by rw [← hP']

/-- A uniform multiplicative bound for repeatedly renormalizing after removing mass `q`. -/
theorem inv_one_sub_pow_le {m : ℕ} {q : ℝ} (hq0 : 0 ≤ q) (hq : q ≤ 1 / 4)
    (hmq : (m : ℝ) * q ≤ 1 / 4) :
    (1 - q)⁻¹ ^ m ≤ 1 + (4 / 3 : ℝ) * (m : ℝ) * q := by
  have hden : 0 < 1 - q := by linarith
  induction m with
  | zero => simp
  | succ m ih =>
      rw [Nat.cast_succ]
      have hs : ((m : ℝ) + 1) * q ≤ 1 / 4 := by
        simpa [Nat.cast_succ] using hmq
      have hmle : (m : ℝ) * q ≤ 1 / 4 := by
        calc
          (m : ℝ) * q ≤ ((m : ℝ) + 1) * q := by nlinarith [hq0]
          _ ≤ 1 / 4 := hs
      have hstep' : (4 / 3 : ℝ) * ((m : ℝ) + 1) * q ≤ 1 / 3 := by
        nlinarith [hs]
      have hmul := mul_le_mul_of_nonneg_right (ih hmle) (inv_nonneg.mpr hden.le)
      rw [pow_succ]
      calc
        (1 - q)⁻¹ ^ m * (1 - q)⁻¹ ≤
            (1 + (4 / 3 : ℝ) * (m : ℝ) * q) * (1 - q)⁻¹ := hmul
        _ ≤ 1 + (4 / 3 : ℝ) * ((m : ℝ) + 1) * q := by
          rw [← div_eq_mul_inv]
          apply (div_le_iff₀ hden).2
          have hstepq := mul_le_mul_of_nonneg_right hstep' hq0
          nlinarith [hstepq] <;> ring

end HypercubeRamsey.Clock
