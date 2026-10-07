import HypercubeRamsey.Framework.FinProbLemmas

namespace HypercubeRamsey

open scoped BigOperators

theorem FinProb.ext {α : Type*} [Fintype α] {P Q : FinProb α}
    (h : ∀ x, P.w x = Q.w x) : P = Q := by
  cases P with
  | mk pw hp hs =>
    cases Q with
    | mk qw hq hst =>
      have hw : pw = qw := funext h
      subst qw
      rfl

/-- Mapping independent coordinates maps the product law to the product of the coordinate image laws. -/
theorem FinProb.map_pi {ι : Type*} [Fintype ι] [DecidableEq ι]
    {α : ι → Type*} {β : ι → Type*}
    [∀ i, Fintype (α i)] [∀ i, DecidableEq (α i)]
    [∀ i, Fintype (β i)] [∀ i, DecidableEq (β i)]
    (instFun : DecidableEq (∀ i, β i))
    (P : ∀ i, FinProb (α i)) (f : ∀ i, α i → β i) :
    @FinProb.map (∀ i, α i) (∀ i, β i) (inferInstance) (inferInstance) instFun
      (FinProb.pi P) (fun x i => f i (x i)) =
      FinProb.pi (fun i => FinProb.map (P i) (f i)) := by
  classical
  apply FinProb.ext
  intro y
  letI : DecidableEq (∀ i, β i) := instFun
  simp only [FinProb.map, FinProb.pi]
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
    _ = ∏ i, ∑ a : α i, if f i a = y i then (P i).w a else 0 := by
      exact (Fintype.prod_sum (fun i a => if f i a = y i then (P i).w a else 0)).symm
    _ = ∏ i, (FinProb.map (P i) (f i)).w (y i) := by
      simp [FinProb.map]

/-- A product probability of coordinate conditions factors over the coordinates. -/
theorem FinProb.pi_pr_forall {ι : Type*} [Fintype ι] [DecidableEq ι]
    {α : ι → Type*} [∀ i, Fintype (α i)]
    (P : ∀ i, FinProb (α i)) (C : ∀ i, α i → Prop) :
    (FinProb.pi P).pr (fun x => ∀ i, C i (x i)) = ∏ i, (P i).pr (C i) := by
  classical
  let Ev : (∀ i, α i) → Prop := fun x => ∀ i, C i (x i)
  letI : DecidablePred Ev := fun x => Classical.propDecidable _
  have hweight (x : (∀ i, α i)) :
      (if Ev x then ∏ i, (P i).w (x i) else 0) =
        ∏ i, if C i (x i) then (P i).w (x i) else 0 := by
    by_cases hall : Ev x
    · simp [Ev, hall]
    · have hex : ∃ i, ¬ C i (x i) := by
        simpa [Ev, not_forall] using hall
      obtain ⟨i, hi⟩ := hex
      rw [if_neg hall]
      symm
      apply Finset.prod_eq_zero (Finset.mem_univ i)
      simp [hi]
  change (∑ x : (∀ i, α i), if Ev x then ∏ i, (P i).w (x i) else 0) =
    ∏ i, (P i).pr (C i)
  calc
    (∑ x : (∀ i, α i), if Ev x then ∏ i, (P i).w (x i) else 0) =
        ∑ x : (∀ i, α i), ∏ i, if C i (x i) then (P i).w (x i) else 0 := by
      apply Finset.sum_congr rfl
      intro x hx
      exact hweight x
    _ = ∏ i, ∑ a : α i, if C i a then (P i).w a else 0 := by
      exact (Fintype.prod_sum (fun i a => if C i a then (P i).w a else 0)).symm
    _ = ∏ i, (P i).pr (C i) := by simp only [FinProb.pr]

/-- Conditioning a product law on a product rectangle conditions each coordinate separately. -/
theorem FinProb.pi_cond_forall {ι : Type*} [Fintype ι] [DecidableEq ι]
    {α : ι → Type*} [∀ i, Fintype (α i)] [∀ i, DecidableEq (α i)]
    (P : ∀ i, FinProb (α i)) (C : ∀ i, α i → Prop)
    (hcoord : ∀ i, 0 < (P i).pr (C i))
    (hpos : 0 < (FinProb.pi P).pr (fun x => ∀ i, C i (x i))) :
    (FinProb.pi P).cond (fun x => ∀ i, C i (x i)) hpos =
      FinProb.pi (fun i => (P i).cond (C i) (hcoord i)) := by
  classical
  let Ev : (∀ i, α i) → Prop := fun x => ∀ i, C i (x i)
  letI : DecidablePred Ev := fun x => Classical.propDecidable _
  have hfactor : (FinProb.pi P).pr Ev = ∏ i, (P i).pr (C i) := by
    simpa [Ev] using FinProb.pi_pr_forall P C
  apply FinProb.ext
  intro x
  change (if Ev x then ∏ i, (P i).w (x i) else 0) / (FinProb.pi P).pr Ev =
    ∏ i, ((P i).cond (C i) (hcoord i)).w (x i)
  by_cases hall : Ev x
  · have hqprod :
        (∏ i, ((P i).cond (C i) (hcoord i)).w (x i)) =
          (∏ i, (P i).w (x i)) / ∏ i, (P i).pr (C i) := by
      rw [← Finset.prod_div_distrib]
      apply Finset.prod_congr rfl
      intro i hi
      simp [FinProb.cond, hall i]
    simp [hall]
    rw [hfactor]
    exact hqprod.symm
  · have hex : ∃ i, ¬ C i (x i) := by
      simpa [Ev, not_forall] using hall
    obtain ⟨i, hi⟩ := hex
    have hzero : ((P i).cond (C i) (hcoord i)).w (x i) = 0 := by
      simp [FinProb.cond, hi]
    have hprodzero :
        (∏ j : ι, ((P j).cond (C j) (hcoord j)).w (x j)) = 0 :=
      Finset.prod_eq_zero (Finset.mem_univ i) hzero
    simp [hall, hprodzero]

end HypercubeRamsey

namespace HypercubeRamsey

open scoped BigOperators

theorem FinProb.pr_indicator {α : Type*} [Fintype α]
    (P : FinProb α) (A : α → Prop) [DecidablePred A] :
    P.pr A = P.expect (fun x => if A x then 1 else 0) := by
  classical
  unfold FinProb.pr FinProb.expect
  apply Finset.sum_congr rfl
  intro x hx
  by_cases hA : A x <;> simp [hA]

theorem FinProb.map_pr {α β : Type*} [Fintype α] [Fintype β] [DecidableEq β]
    (P : FinProb α) (f : α → β) (A : β → Prop) :
    (FinProb.map P f).pr A = P.pr (fun x => A (f x)) := by
  classical
  calc
    (FinProb.map P f).pr A =
        (FinProb.map P f).expect (fun y => if A y then 1 else 0) :=
      FinProb.pr_indicator _ _
    _ = P.expect (fun x => if A (f x) then 1 else 0) :=
      FinProb.map_expect P f (fun y => if A y then 1 else 0)
    _ = P.pr (fun x => A (f x)) := (FinProb.pr_indicator _ _).symm

theorem FinProb.pr_singleton {α : Type*} [Fintype α] [DecidableEq α]
    (P : FinProb α) (a : α) : P.pr (fun x => x = a) = P.w a := by
  classical
  unfold FinProb.pr
  rw [Fintype.sum_eq_single a]
  · simp
  · intro x hxa
    simp [hxa]

theorem FinProb.bind_pr {α β : Type*} [Fintype α] [Fintype β]
    (P : FinProb α) (K : α → FinProb β) (A : α × β → Prop) :
    (FinProb.bind P K).pr A =
      ∑ a, P.w a * (K a).pr (fun b => A (a, b)) := by
  classical
  unfold FinProb.pr FinProb.bind
  rw [Fintype.sum_prod_type]
  apply Finset.sum_congr rfl
  intro a ha
  calc
    (∑ b, if A (a, b) then P.w a * (K a).w b else 0) =
        ∑ b, P.w a * (if A (a, b) then (K a).w b else 0) := by
      apply Finset.sum_congr rfl
      intro b hb
      by_cases hA : A (a, b) <;> simp [hA]
    _ = P.w a * ∑ b, if A (a, b) then (K a).w b else 0 := by
      rw [Finset.mul_sum]
    _ = P.w a * (K a).pr (fun b => A (a, b)) := rfl

end HypercubeRamsey

namespace HypercubeRamsey

open scoped BigOperators

theorem FinProb.map_bind_condition_delay {α : Type*} [Fintype α] [DecidableEq α]
    (P : FinProb α) (C : α → Prop) (hC : 0 < P.pr C) (d : α → α → α)
    (hstay : ∀ x y, C x → d x y = x)
    (hdelay : ∀ x y, ¬ C x → C y → d x y = y) :
    FinProb.map (FinProb.bind P (fun _ => P.cond C hC)) (fun xy => d xy.1 xy.2) =
      P.cond C hC := by
  classical
  let Q := P.cond C hC
  letI : DecidablePred C := fun x => Classical.propDecidable _
  letI : DecidablePred (fun x => ¬ C x) := fun x => Classical.propDecidable _
  have hqzero (y : α) (hy : ¬ C y) : Q.w y = 0 := by
    simp [Q, FinProb.cond, hy]
  have hqform (y : α) (hy : C y) : Q.w y = P.w y / P.pr C := by
    simp [Q, FinProb.cond, hy]
  have hsplit :
      (∑ x, P.w x) =
        (∑ x, if C x then P.w x else 0) +
          (∑ x, if ¬ C x then P.w x else 0) := by
      rw [← Finset.sum_add_distrib]
      apply Finset.sum_congr rfl
      intro x hx
      by_cases h : C x <;> simp [h]
  have hCsum : (∑ x, if C x then P.w x else 0) = P.pr C := by
    rfl
  have hnotmass : (∑ x, if ¬ C x then P.w x else 0) = 1 - P.pr C := by
    have hprob : 1 = (∑ x, if C x then P.w x else 0) +
        (∑ x, if ¬ C x then P.w x else 0) := by
      rw [← P.sum_eq_one]
      exact hsplit
    rw [hCsum] at hprob
    linarith
  have hinner (x z : α) :
      Q.pr (fun y => d x y = z) =
        if C x then (if x = z then 1 else 0) else Q.w z := by
    letI : DecidablePred (fun y => d x y = z) := fun y => Classical.propDecidable _
    unfold FinProb.pr
    by_cases hx : C x
    · have hterm (y : α) :
          (if d x y = z then Q.w y else 0) = if x = z then Q.w y else 0 := by
        simp [hstay x y hx]
      calc
        (∑ y, if d x y = z then Q.w y else 0) =
            ∑ y, if x = z then Q.w y else 0 := by
          apply Finset.sum_congr rfl
          intro y hy
          exact hterm y
        _ = if x = z then 1 else 0 := by
          by_cases hxz : x = z
          · simp [hx, hxz, Q.sum_eq_one]
          · simp [hx, hxz]
        _ = if C x then (if x = z then 1 else 0) else Q.w z := by simp [hx]
    · by_cases hz : C z
      · have hterm (y : α) :
          (if d x y = z then Q.w y else 0) = if y = z then Q.w z else 0 := by
          by_cases hy : C y
          · by_cases hyz : y = z
            · subst y
              have hd := hdelay x z hx hz
              simp [hd]
            · have hd := hdelay x y hx hy
              simp [hd, hyz]
          · have hqy := hqzero y hy
            by_cases hyz : y = z
            · subst y
              exact False.elim (hy hz)
            · simp [hyz, hqy]
        calc
          (∑ y, if d x y = z then Q.w y else 0) =
              ∑ y, if y = z then Q.w z else 0 := by
            apply Finset.sum_congr rfl
            intro y hy
            exact hterm y
          _ = Q.w z := by simp
          _ = if C x then (if x = z then 1 else 0) else Q.w z := by simp [hx]
      · have hqz := hqzero z hz
        calc
          (∑ y, if d x y = z then Q.w y else 0) = 0 := by
            apply Finset.sum_eq_zero
            intro y hy
            by_cases hyC : C y
            · have hyDelay := hdelay x y hx hyC
              have hyz : y ≠ z := by
                intro heq
                subst y
                exact hz hyC
              simp [hyDelay, hyz]
            · simp [hqzero y hyC]
          _ = if C x then (if x = z then 1 else 0) else Q.w z := by simp [hx, hqz]
  have houter (z : α) :
      (∑ x, P.w x * (if C x then (if x = z then 1 else 0) else Q.w z)) = Q.w z := by
    have honeSum :
        (∑ x, if C x ∧ x = z then P.w x else 0) = if C z then P.w z else 0 := by
      by_cases hz : C z
      · rw [Finset.sum_eq_single z]
        · simp [hz]
        · intro x hx hxz
          simp [hxz]
        · simp
      · simp only [if_neg hz]
        apply Finset.sum_eq_zero
        intro x hx
        by_cases hxz : x = z
        · subst x
          simp [hz]
        · simp [hxz]
    have hterm (x : α) :
        P.w x * (if C x then (if x = z then 1 else 0) else Q.w z) =
          (if C x ∧ x = z then P.w x else 0) +
            (if ¬ C x then Q.w z * P.w x else 0) := by
      by_cases hx : C x
      · by_cases hxz : x = z
        · subst z
          simp [hx]
        · simp [hx, hxz]
      · by_cases hxz : x = z
        · subst z
          simp [hx]
          ring
        · simp [hx, hxz, mul_comm]
    calc
      (∑ x, P.w x * (if C x then (if x = z then 1 else 0) else Q.w z)) =
          (∑ x, if C x ∧ x = z then P.w x else 0) +
            ∑ x, if ¬ C x then Q.w z * P.w x else 0 := by
        rw [← Finset.sum_add_distrib]
        exact Finset.sum_congr rfl (fun x _ => hterm x)
      _ = (if C z then P.w z else 0) + Q.w z * (1 - P.pr C) := by
        rw [honeSum]
        apply congrArg (fun v => (if C z then P.w z else 0) + v)
        calc
          (∑ x, if ¬ C x then Q.w z * P.w x else 0) =
              ∑ x, Q.w z * (if ¬ C x then P.w x else 0) := by
            apply Finset.sum_congr rfl
            intro x hx
            by_cases hxC : C x <;> simp [hxC]
          _ = Q.w z * ∑ x, if ¬ C x then P.w x else 0 := by rw [Finset.mul_sum]
          _ = Q.w z * (1 - P.pr C) := by rw [hnotmass]
      _ = Q.w z := by
        by_cases hz : C z
        · rw [hqform z hz]
          simp only [if_pos hz]
          field_simp [ne_of_gt hC]
          all_goals ring_nf
        · rw [hqzero z hz]
          simp [hz]
  have hweight (z : α) :
      (FinProb.map (FinProb.bind P (fun _ => Q)) (fun xy => d xy.1 xy.2)).w z = Q.w z := by
    calc
      (FinProb.map (FinProb.bind P (fun _ => Q)) (fun xy => d xy.1 xy.2)).w z =
          (FinProb.map (FinProb.bind P (fun _ => Q)) (fun xy => d xy.1 xy.2)).pr (fun y => y = z) :=
            (FinProb.pr_singleton _ z).symm
      _ = (FinProb.bind P (fun _ => Q)).pr (fun xy => d xy.1 xy.2 = z) :=
            FinProb.map_pr _ _ _
      _ = ∑ x, P.w x * Q.pr (fun y => d x y = z) := FinProb.bind_pr _ _ _
      _ = ∑ x, P.w x * (if C x then (if x = z then 1 else 0) else Q.w z) := by
            apply Finset.sum_congr rfl
            intro x hx
            rw [hinner]
      _ = Q.w z := houter z
  apply FinProb.ext
  intro z
  exact hweight z

end HypercubeRamsey

namespace HypercubeRamsey

open scoped BigOperators

theorem FinProb.pr_nonneg {α : Type*} [Fintype α] (P : FinProb α) (A : α → Prop) :
    0 ≤ P.pr A := by
  classical
  unfold FinProb.pr
  exact Finset.sum_nonneg fun x hx => by
    split_ifs
    · exact P.nonneg x
    · exact le_rfl

theorem FinProb.cond_pr {α : Type*} [Fintype α]
    (P : FinProb α) (A B : α → Prop) (hA : 0 < P.pr A) :
    (P.cond A hA).pr B = P.pr (fun x => A x ∧ B x) / P.pr A := by
  classical
  dsimp [FinProb.pr, FinProb.cond]
  rw [Finset.sum_div]
  apply Finset.sum_congr rfl
  intro x hx
  by_cases hA' : A x <;> by_cases hB : B x <;> simp [hA', hB]

end HypercubeRamsey

namespace HypercubeRamsey

open scoped BigOperators

theorem FinProb.map_bind_fst {α β : Type*} [Fintype α] [Fintype β] [DecidableEq α]
    (P : FinProb α) (Q : FinProb β) :
    FinProb.map (FinProb.bind P (fun _ => Q)) Prod.fst = P := by
  classical
  apply FinProb.ext
  intro x
  change (∑ ab : α × β, if ab.1 = x then P.w ab.1 * Q.w ab.2 else 0) = P.w x
  calc
    (∑ ab : α × β, if ab.1 = x then P.w ab.1 * Q.w ab.2 else 0) =
        ∑ a : α, ∑ b : β, if a = x then P.w a * Q.w b else 0 := by
      rw [Fintype.sum_prod_type]
    _ = ∑ a : α, if a = x then P.w a else 0 := by
      apply Finset.sum_congr rfl
      intro a ha
      by_cases hax : a = x
      · subst a
        simp only [if_pos rfl]
        change (∑ b ∈ (Finset.univ : Finset β), P.w x * Q.w b) = P.w x
        rw [← Finset.mul_sum]
        simp [Q.sum_eq_one]
      · simp [hax]
    _ = P.w x := by simp

end HypercubeRamsey
