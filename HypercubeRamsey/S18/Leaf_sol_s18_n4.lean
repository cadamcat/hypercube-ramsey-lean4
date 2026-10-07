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

/-- A token's incident charge is bounded whenever its incident leaves form an adjacency clique. -/
theorem tokenChargeOfCliques {I A : Type*} [Fintype I] [DecidableEq A]
    (adj : I → I → Prop) (tokens : I → Finset A) (charge : I → ℝ)
    (hcharge : ∀ i, 0 ≤ charge i) (bound : ℝ) (hbound : 0 ≤ bound)
    (hclique : ∀ i j a, a ∈ tokens i → a ∈ tokens j → adj i j)
    (hadj : ∀ i, (∑ j, if adj i j then charge j else 0) ≤ bound) (a : A) :
    (∑ i, if a ∈ tokens i then charge i else 0) ≤ bound := by
  by_cases hex : ∃ i, a ∈ tokens i
  · obtain ⟨i, hi⟩ := hex
    calc
      _ ≤ ∑ j, if adj i j then charge j else 0 := by
        apply Finset.sum_le_sum
        intro j hj
        by_cases ha : a ∈ tokens j
        · simp [ha, hclique i j a hi ha]
        · simp only [ha, ite_false]
          split_ifs <;> simp [hcharge]
      _ ≤ bound := hadj i
  · have hnone : ∀ i, a ∉ tokens i := by simpa using hex
    simpa [hnone] using hbound

/-- A finite test pays at most one token charge for each token it consults. -/
theorem testTouchingCharge {I A : Type*} [Fintype I] [DecidableEq A]
    (tokens : I → Finset A) (charge : I → ℝ) (hcharge : ∀ i, 0 ≤ charge i)
    (test : Finset A) (bound : ℝ)
    (htoken : ∀ a ∈ test, (∑ i, if a ∈ tokens i then charge i else 0) ≤ bound) :
    (∑ i, if ¬ Disjoint (tokens i) test then charge i else 0) ≤ (test.card : ℝ) * bound := by
  have hpoint : ∀ i, (if ¬ Disjoint (tokens i) test then charge i else 0) ≤
      ∑ a ∈ test, if a ∈ tokens i then charge i else 0 := by
    intro i
    by_cases ht : ¬ Disjoint (tokens i) test
    · obtain ⟨a, ha, htest⟩ := Finset.not_disjoint_iff.mp ht
      simp only [ht, ite_true]
      have h := Finset.single_le_sum (f := fun a => if a ∈ tokens i then charge i else 0)
        (fun a _ => by split_ifs <;> simp [hcharge]) htest
      simpa [ha] using h
    · simp only [ht, ite_false]
      exact Finset.sum_nonneg (fun a _ => by split_ifs <;> simp [hcharge])
  calc
    _ ≤ ∑ i, ∑ a ∈ test, if a ∈ tokens i then charge i else 0 :=
      Finset.sum_le_sum (fun i _ => hpoint i)
    _ = ∑ a ∈ test, ∑ i, if a ∈ tokens i then charge i else 0 := Finset.sum_comm
    _ ≤ ∑ a ∈ test, bound := Finset.sum_le_sum htoken
    _ = (test.card : ℝ) * bound := by simp

/-- The actual three kinds of leaf dependency each form a charge clique. -/
theorem leafTestTouchingCharge
    {κ : CConsts} {T : Stage} {k : ℕ} {PT : ProfiledTiling κ T k}
    {hPT : PT.Valid} (D : S18.LateData hPT) (δ : ℝ)
    (L : S18.LeafCoupling D δ)
    (domains : Finset (Sigma fun C : D.geom.Cell => Fin (D.geom.nslot C)))
    (images : Finset (Sigma fun i : Fin PT.tiling.m => Bin PT.tiling i))
    (tapes : Finset D.geom.Cell) :
    (∑ i, if ¬ Disjoint (L.domains i) domains ∨ ¬ Disjoint (L.images i) images ∨
        ¬ Disjoint (L.tapes i) tapes then 2 * D.encoding.permLaw.pr (fun x => x ∈ L.leaf i) else 0) ≤
      ((domains.card + images.card + tapes.card : ℕ) : ℝ) *
        (2 * Real.rpow (T.S.n k : ℝ)
          (20 * (((κ.Ac + 4) * D.encoding.Ts + D.geom.r : ℕ) : ℝ) -
            (κ.P : ℝ) * D.encoding.Ts / 3)) := by
  let q := fun i => 2 * D.encoding.permLaw.pr (fun x => x ∈ L.leaf i)
  let B := 2 * Real.rpow (T.S.n k : ℝ)
    (20 * (((κ.Ac + 4) * D.encoding.Ts + D.geom.r : ℕ) : ℝ) -
      (κ.P : ℝ) * D.encoding.Ts / 3)
  have hq0 : ∀ i, 0 ≤ q i := by
    intro i
    unfold q FinLaw.pr
    apply mul_nonneg (by norm_num)
    exact Finset.sum_nonneg (fun x _ => by split_ifs <;> simp [D.encoding.permLaw.nonneg])
  have hB0 : 0 ≤ B := mul_nonneg (by norm_num) (Real.rpow_nonneg (Nat.cast_nonneg _) _)
  have hdom : (∑ i, if ¬ Disjoint (L.domains i) domains then q i else 0) ≤
      (domains.card : ℝ) * B := by
    apply testTouchingCharge _ _ hq0 domains B
    intro a ha
    apply tokenChargeOfCliques L.adjacent L.domains q hq0 B hB0
    · intro i j a hai haj
      apply (L.adjacent_eq i j).2
      exact Or.inl (Finset.not_disjoint_iff.2 ⟨a, hai, haj⟩)
    · exact L.touching_charge
  have himage : (∑ i, if ¬ Disjoint (L.images i) images then q i else 0) ≤
      (images.card : ℝ) * B := by
    apply testTouchingCharge _ _ hq0 images B
    intro a ha
    apply tokenChargeOfCliques L.adjacent L.images q hq0 B hB0
    · intro i j a hai haj
      apply (L.adjacent_eq i j).2
      exact Or.inr (Or.inl (Finset.not_disjoint_iff.2 ⟨a, hai, haj⟩))
    · exact L.touching_charge
  have htape : (∑ i, if ¬ Disjoint (L.tapes i) tapes then q i else 0) ≤
      (tapes.card : ℝ) * B := by
    apply testTouchingCharge _ _ hq0 tapes B
    intro a ha
    apply tokenChargeOfCliques L.adjacent L.tapes q hq0 B hB0
    · intro i j a hai haj
      apply (L.adjacent_eq i j).2
      exact Or.inr (Or.inr (Finset.not_disjoint_iff.2 ⟨a, hai, haj⟩))
    · exact L.touching_charge
  change (∑ i, if ¬ Disjoint (L.domains i) domains ∨ ¬ Disjoint (L.images i) images ∨
      ¬ Disjoint (L.tapes i) tapes then q i else 0) ≤ _
  calc
    _ ≤ (∑ i, if ¬ Disjoint (L.domains i) domains then q i else 0) +
        (∑ i, if ¬ Disjoint (L.images i) images then q i else 0) +
        (∑ i, if ¬ Disjoint (L.tapes i) tapes then q i else 0) := by
      rw [← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
      apply Finset.sum_le_sum
      intro i hi
      by_cases hd : Disjoint (L.domains i) domains <;>
        by_cases him : Disjoint (L.images i) images <;>
        by_cases ht : Disjoint (L.tapes i) tapes <;> simp [hd, him, ht] <;> linarith [hq0 i]
    _ ≤ (domains.card : ℝ) * B + (images.card : ℝ) * B + (tapes.card : ℝ) * B :=
      add_le_add (add_le_add hdom himage) htape
    _ = _ := by
      change _ = ((domains.card + images.card + tapes.card : ℕ) : ℝ) * B
      push_cast
      ring

private theorem prodOneSubLowerCharge
    {I : Type*} [DecidableEq I] (S : Finset I) (q : I → ℝ)
    (hq0 : ∀ i ∈ S, 0 ≤ q i) (hq1 : ∀ i ∈ S, q i ≤ 1) :
    1 - ∑ i ∈ S, q i ≤ ∏ i ∈ S, (1 - q i) := by
  classical
  induction S using Finset.induction_on with
  | empty => simp
  | @insert i S hi ih =>
      have hi0 := hq0 i (Finset.mem_insert_self i S)
      have hi1 := hq1 i (Finset.mem_insert_self i S)
      have hq0' : ∀ j ∈ S, 0 ≤ q j := fun j hj => hq0 j (Finset.mem_insert_of_mem hj)
      have hq1' : ∀ j ∈ S, q j ≤ 1 := fun j hj => hq1 j (Finset.mem_insert_of_mem hj)
      have hsum0 : 0 ≤ ∑ j ∈ S, q j := Finset.sum_nonneg fun j hj => hq0' j hj
      rw [Finset.sum_insert hi, Finset.prod_insert hi]
      calc
        1 - (q i + ∑ j ∈ S, q j) ≤ (1 - q i) * (1 - ∑ j ∈ S, q j) := by
          nlinarith [mul_nonneg hi0 hsum0]
        _ ≤ (1 - q i) * ∏ j ∈ S, (1 - q j) :=
          mul_le_mul_of_nonneg_left (ih hq0' hq1') (sub_nonneg.mpr hi1)

/-- The sum bound gives the reciprocal avoidance-product cost used in P18.3f. -/
theorem reciprocalAvoidanceProductLe {I : Type*} [DecidableEq I]
    (S : Finset I) (q : I → ℝ) (ε : ℝ) (hε : 0 ≤ ε)
    (hq0 : ∀ i ∈ S, 0 ≤ q i) (hq1 : ∀ i ∈ S, q i < 1)
    (hsum : ∑ i ∈ S, q i ≤ ε / (1 + ε)) :
    (∏ i ∈ S, (1 - q i)⁻¹) ≤ 1 + ε := by
  have hden : 0 < 1 + ε := by linarith
  have hprod : 0 < ∏ i ∈ S, (1 - q i) := Finset.prod_pos (fun i hi => sub_pos.mpr (hq1 i hi))
  have hlower := prodOneSubLowerCharge S q hq0 (fun i hi => (hq1 i hi).le)
  have hrecip : (1 + ε)⁻¹ ≤ ∏ i ∈ S, (1 - q i) := by
    have heq : 1 - ε / (1 + ε) = (1 + ε)⁻¹ := by field_simp [ne_of_gt hden]; ring
    rw [← heq]
    linarith
  rw [Finset.prod_inv_distrib]
  have h1 : 1 ≤ (1 + ε) * ∏ i ∈ S, (1 - q i) := by
    have h := mul_le_mul_of_nonneg_left hrecip hden.le
    simpa only [mul_inv_cancel₀ (ne_of_gt hden)] using h
  have h := mul_le_mul_of_nonneg_right h1 (inv_nonneg.mpr hprod.le)
  simpa only [one_mul, mul_assoc, mul_inv_cancel₀ (ne_of_gt hprod), mul_one] using h

end HypercubeRamsey.Lane_sol_s18_n4
