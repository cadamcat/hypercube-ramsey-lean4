import HypercubeRamsey.S18.Defs

namespace HypercubeRamsey.Lane_sol_s18_n4

open Classical
open scoped BigOperators

private theorem law_pr_map
    {α β : Type*} [Fintype α] [Fintype β] [DecidableEq β]
    (P : FinLaw α) (f : α → β) (A : β → Prop) :
    (FinLaw.map P f).pr A = P.pr (fun x => A (f x)) := by
  classical
  unfold FinLaw.pr FinLaw.map
  have hinner : ∀ y,
      (if A y then ∑ x, if f x = y then P.w x else 0 else 0) =
      ∑ x, if A y then (if f x = y then P.w x else 0) else 0 := by
    intro y
    by_cases h : A y <;> simp [h]
  simp_rw [hinner]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro x hx
  have hpoint : ∀ y,
      (if A y then (if f x = y then P.w x else 0) else 0) =
      (if f x = y then (if A (f x) then P.w x else 0) else 0) := by
    intro y
    by_cases h : f x = y
    · subst y
      simp
    · simp [h]
  simp_rw [hpoint]
  simp

private theorem law_pr_bind
    {α β : Type*} [Fintype α] [Fintype β]
    (P : FinLaw α) (K : α → FinLaw β) (A : α × β → Prop) :
    (FinLaw.bind P K).pr A = ∑ x, P.w x * (K x).pr (fun y => A (x, y)) := by
  simp [FinLaw.pr, FinLaw.bind, Fintype.sum_prod_type, Finset.mul_sum, mul_ite]

private theorem law_pr_le_one
    {Ω : Type*} [Fintype Ω] (P : FinLaw Ω) (A : Ω → Prop) : P.pr A ≤ 1 := by
  rw [← P.sum_one]
  unfold FinLaw.pr
  apply Finset.sum_le_sum
  intro x hx
  by_cases h : A x
  · simp [h]
  · simpa [h] using P.nonneg x

private theorem law_leaf_mass
    {Ω : Type*} [Fintype Ω] [DecidableEq Ω] (P : FinLaw Ω) (leaf : Finset Ω) :
    (∑ x ∈ leaf, P.w x) = P.pr (fun x => x ∈ leaf) := by
  classical
  symm
  calc
    P.pr (fun x => x ∈ leaf) = ∑ x, if x ∈ leaf then P.w x else 0 := by
      unfold FinLaw.pr
      apply Finset.sum_congr rfl
      intro x hx
      by_cases h : x ∈ leaf <;> simp [h]
    _ =
        ∑ x ∈ leaf, if x ∈ leaf then P.w x else 0 :=
      (Finset.sum_subset (Finset.subset_univ leaf) (fun x _ hx => by simp [hx])).symm
    _ = ∑ x ∈ leaf, P.w x := Finset.sum_congr rfl (fun x hx => by simp [hx])

theorem forcingLopsided
    {Ω : Type*} [Fintype Ω] [DecidableEq Ω]
    (P : FinLaw Ω) (leaf : Finset Ω)
    (hpos : 0 < ∑ x ∈ leaf, P.w x) (force : Ω → FinLaw Ω)
    (hpush : FinLaw.map (FinLaw.bind P force) Prod.snd = FinLaw.cond P leaf hpos)
    (B : Ω → Prop)
    (hpreserve : ∀ x y, 0 < (force x).w y → B y → B x) :
    P.pr (fun x => x ∈ leaf ∧ B x) ≤ P.pr (fun x => x ∈ leaf) * P.pr B := by
  classical
  have hforce : (FinLaw.bind P force).pr (fun xy => B xy.2) ≤ P.pr B := by
    rw [law_pr_bind]
    change (∑ x, P.w x * (force x).pr B) ≤ ∑ x, if B x then P.w x else 0
    apply Finset.sum_le_sum
    intro x hx
    by_cases hb : B x
    · simp only [hb, ite_true]
      simpa using mul_le_mul_of_nonneg_left (law_pr_le_one (force x) B) (P.nonneg x)
    · simp only [hb, ite_false]
      have hzero : (force x).pr B = 0 := by
        unfold FinLaw.pr
        apply Finset.sum_eq_zero
        intro y hy
        by_cases hby : B y
        · have hw : (force x).w y = 0 := by
            apply le_antisymm
            · exact le_of_not_gt (fun h => hb (hpreserve x y h hby))
            · exact (force x).nonneg y
          simp [hby, hw]
        · simp [hby]
      rw [hzero, mul_zero]
  have hcond : (FinLaw.cond P leaf hpos).pr B ≤ P.pr B := by
    rw [← hpush, law_pr_map]
    exact hforce
  have hformula : (FinLaw.cond P leaf hpos).pr B =
      P.pr (fun x => x ∈ leaf ∧ B x) / (∑ x ∈ leaf, P.w x) := by
    unfold FinLaw.pr FinLaw.cond
    rw [Finset.sum_div]
    apply Finset.sum_congr rfl
    intro x hx
    by_cases hl : x ∈ leaf <;> by_cases hb : B x <;> simp [hl, hb]
  have hmass : (∑ x ∈ leaf, P.w x) = P.pr (fun x => x ∈ leaf) := by
    exact law_leaf_mass P leaf
  rw [hformula] at hcond
  have h := (div_le_iff₀ hpos).1 hcond
  simpa [hmass, mul_comm] using h

theorem leafNonneighborBoundOfForcing
    {κ : CConsts} {T : Stage} {k : ℕ} {PT : ProfiledTiling κ T k}
    {hPT : PT.Valid} (D : S18.LateData hPT)
    {I : Type*} [Fintype I] (leaves : I → Finset D.encoding.InitInput)
    (adj : I → I → Prop)
    (force : ∀ i, 0 < ∑ x ∈ leaves i, D.encoding.permLaw.w x →
      D.encoding.InitInput → FinLaw D.encoding.InitInput)
    (hpush : ∀ i hi, FinLaw.map (FinLaw.bind D.encoding.permLaw (force i hi)) Prod.snd =
      FinLaw.cond D.encoding.permLaw (leaves i) hi)
    (hpreserve : ∀ i hi x y, 0 < (force i hi x).w y →
      ∀ j, ¬ adj i j → x ∈ leaves j → y ∈ leaves j) :
    ∀ i (S : Finset I), (∀ j ∈ S, ¬ adj i j) →
      D.encoding.permLaw.pr (fun x => x ∈ leaves i ∧ ∀ j ∈ S, x ∉ leaves j) ≤
        D.encoding.permLaw.pr (fun x => x ∈ leaves i) *
          D.encoding.permLaw.pr (fun x => ∀ j ∈ S, x ∉ leaves j) := by
  classical
  intro i S hS
  by_cases hpos : 0 < ∑ x ∈ leaves i, D.encoding.permLaw.w x
  · apply forcingLopsided D.encoding.permLaw (leaves i) hpos (force i hpos)
      (hpush i hpos) (fun x => ∀ j ∈ S, x ∉ leaves j)
    intro x y hxy hy j hj hxj
    exact hy j hj (hpreserve i hpos x y hxy j (hS j hj) hxj)
  · have hnonneg : 0 ≤ ∑ x ∈ leaves i, D.encoding.permLaw.w x :=
      Finset.sum_nonneg (fun x _ => D.encoding.permLaw.nonneg x)
    have hzero : ∑ x ∈ leaves i, D.encoding.permLaw.w x = 0 := by linarith
    have hmass : D.encoding.permLaw.pr (fun x => x ∈ leaves i) = 0 := by
      rw [← law_leaf_mass]
      exact hzero
    rw [hmass, zero_mul]
    have hnum : D.encoding.permLaw.pr (fun x => x ∈ leaves i ∧ ∀ j ∈ S, x ∉ leaves j) = 0 := by
      unfold FinLaw.pr
      apply Finset.sum_eq_zero
      intro x hx
      by_cases hleaf : x ∈ leaves i
      · have hle : D.encoding.permLaw.w x ≤ ∑ y ∈ leaves i, D.encoding.permLaw.w y :=
          Finset.single_le_sum (fun y _ => D.encoding.permLaw.nonneg y) hleaf
        have hw : D.encoding.permLaw.w x = 0 := by
          have hnonneg := D.encoding.permLaw.nonneg x
          rw [hzero] at hle
          linarith
        simp [hw]
      · simp [hleaf]
    rw [hnum]

end HypercubeRamsey.Lane_sol_s18_n4
