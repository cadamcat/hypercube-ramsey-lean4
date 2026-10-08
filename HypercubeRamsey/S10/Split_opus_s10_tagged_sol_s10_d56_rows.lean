import HypercubeRamsey.S10.FixedList
import HypercubeRamsey.S10.Split_opus_s10_tagged_sol_s10_d56_independence
import HypercubeRamsey.S10.Split_opus_s10_tagged_sol_s10_d56_enumeration

namespace HypercubeRamsey.Lane_sol_s10_d56

open Classical HypercubeRamsey.S10
open scoped BigOperators

/-- Restrict a positive-mass hit set, with the same default as the experiment. -/
noncomputable def rowRestriction {N : ℕ} (D : Law N) (F : Finset (Fin N)) : Law N :=
  if h : 0 < lawMassOn D F then Law.restrict D F h else D

/-- Absolute and per-block deletion gates of a fixed-list cluster. -/
def listKept {N r k q : ℕ} (E : Fin N → Fin N → Prop) (G : Colour)
    (D : Fin q → Law N) (a : ℝ) (own : Fin r → Prop)
    (W : Fin r → Fin k → Fin N) (j : Fin q) : Prop :=
  Real.exp (-(3 / 2 : ℝ) * k * r) ≤ lawMassOn (D j) (fixedListHitSet E G W) ∧
  ∀ b, (if own b then Real.exp ((-Real.log 2 + (8 / 100 : ℝ) * a) * k)
    else Real.exp (-(6 / 5 : ℝ) * k)) *
      lawMassOn (D j) (fixedListHitSetWithout E G W b) ≤
        lawMassOn (D j) (fixedListHitSet E G W)

noncomputable def listWeight {N r k q : ℕ} (E : Fin N → Fin N → Prop) (G : Colour)
    (ρ : FinProb (Fin q)) (D : Fin q → Law N) (a : ℝ) (own : Fin r → Prop)
    (W : Fin r → Fin k → Fin N) (j : Fin q) : ℝ :=
  if listKept E G D a own W j then
    ρ.w j * (lawMassOn (D j) (fixedListHitSet E G W)) ^ 2 else 0

/-- The fixed-list row, with the tag and mask laws supplied as parameters. -/
noncomputable def fixedRow {N r k q : ℕ} (E : Fin N → Fin N → Prop) (G : Colour)
    (ρ : FinProb (Fin q)) (D : Fin q → Law N) (μs : Fin r → Law N) (a : ℝ)
    (own : Fin r → Prop) (W : Fin r → Fin k → Fin N) (y : Fin N) : ℝ :=
  if fixedListFailure E G ρ D μs a W ∨ ∑ j, listWeight E G ρ D a own W j = 0 then 0
  else ∑ j, listWeight E G ρ D a own W j / (∑ j', listWeight E G ρ D a own W j') *
    (rowRestriction (D j) (fixedListHitSet E G W)).w y

private theorem listWeight_nonneg {N r k q : ℕ} (E : Fin N → Fin N → Prop) (G : Colour)
    (ρ : FinProb (Fin q)) (D : Fin q → Law N) (a : ℝ) (own : Fin r → Prop)
    (W : Fin r → Fin k → Fin N) (j : Fin q) : 0 ≤ listWeight E G ρ D a own W j := by
  unfold listWeight
  split_ifs
  · exact mul_nonneg (ρ.nonneg j) (sq_nonneg _)
  · exact le_rfl

/-- Counterfactual fixed-list rows are nonnegative even at the fallback branches. -/
theorem fixedRow_nonneg {N r k q : ℕ} (E : Fin N → Fin N → Prop) (G : Colour)
    (ρ : FinProb (Fin q)) (D : Fin q → Law N) (μs : Fin r → Law N) (a : ℝ)
    (own : Fin r → Prop) (W : Fin r → Fin k → Fin N) (y : Fin N) :
    0 ≤ fixedRow E G ρ D μs a own W y := by
  unfold fixedRow
  split_ifs
  · exact le_rfl
  · apply Finset.sum_nonneg
    intro j hj
    apply mul_nonneg
    · exact div_nonneg (listWeight_nonneg E G ρ D a own W j)
        (Finset.sum_nonneg fun j' _ => listWeight_nonneg E G ρ D a own W j')
    · exact (rowRestriction (D j) (fixedListHitSet E G W)).nonneg y

/-- Reordering the block names leaves the common hit set unchanged. -/
theorem fixedListHitSet_perm {N r k : ℕ} (E : Fin N → Fin N → Prop) (G : Colour)
    (e : Equiv.Perm (Fin r)) (W : Fin r → Fin k → Fin N) :
    fixedListHitSet E G (fun b => W (e b)) = fixedListHitSet E G W := by
  classical
  ext y
  simp only [fixedListHitSet, Finset.mem_filter, Finset.mem_univ, true_and]
  constructor
  · intro h b i
    simpa using h (e.symm b) i
  · intro h b i
    exact h (e b) i

/-- Deleting a reordered block is the same as deleting its original name. -/
theorem fixedListHitSetWithout_perm {N r k : ℕ} (E : Fin N → Fin N → Prop) (G : Colour)
    (e : Equiv.Perm (Fin r)) (W : Fin r → Fin k → Fin N) (b : Fin r) :
    fixedListHitSetWithout E G (fun b => W (e b)) b = fixedListHitSetWithout E G W (e b) := by
  classical
  ext y
  simp only [fixedListHitSetWithout, Finset.mem_filter, Finset.mem_univ, true_and]
  constructor
  · intro h c hc i
    have hne : e.symm c ≠ b := by
      intro heq
      exact hc (by simpa using congrArg e heq)
    simpa using h (e.symm c) hne i
  · intro h c hc i
    exact h (e c) (fun heq => hc (e.injective heq)) i

/-- The fixed-list failure test is invariant under a permutation of blocks and their laws. -/
theorem fixedListFailure_perm {N r k q : ℕ} (E : Fin N → Fin N → Prop) (G : Colour)
    (ρ : FinProb (Fin q)) (D : Fin q → Law N) (μs : Fin r → Law N) (a : ℝ)
    (e : Equiv.Perm (Fin r)) (W : Fin r → Fin k → Fin N) :
    fixedListFailure E G ρ D (fun b => μs (e b)) a (fun b => W (e b)) ↔
      fixedListFailure E G ρ D μs a W := by
  classical
  unfold fixedListFailure
  simp only [fixedListHitSet_perm, fixedListHitSetWithout_perm]
  constructor
  · rintro (h | ⟨b, hb, hm⟩ | ⟨b, hb, hm⟩)
    · exact Or.inl h
    · exact Or.inr (Or.inl ⟨e b, hb, hm⟩)
    · exact Or.inr (Or.inr ⟨e b, hb, hm⟩)
  · rintro (h | ⟨b, hb, hm⟩ | ⟨b, hb, hm⟩)
    · exact Or.inl h
    · exact Or.inr (Or.inl ⟨e.symm b, by simpa using hb, by simpa using hm⟩)
    · exact Or.inr (Or.inr ⟨e.symm b, by simpa using hb, by simpa using hm⟩)

private theorem listKept_perm {N r k q : ℕ} (E : Fin N → Fin N → Prop) (G : Colour)
    (D : Fin q → Law N) (a : ℝ) (own : Fin r → Prop)
    (e : Equiv.Perm (Fin r)) (W : Fin r → Fin k → Fin N) (j : Fin q) :
    listKept E G D a (fun b => own (e b)) (fun b => W (e b)) j ↔
      listKept E G D a own W j := by
  classical
  unfold listKept
  simp only [fixedListHitSet_perm, fixedListHitSetWithout_perm]
  constructor
  · rintro ⟨habs, h⟩
    exact ⟨habs, fun b => by simpa using h (e.symm b)⟩
  · rintro ⟨habs, h⟩
    exact ⟨habs, fun b => h (e b)⟩

/-- The list row does not depend on the order used to enumerate its named IDs. -/
theorem fixedRow_perm {N r k q : ℕ} (E : Fin N → Fin N → Prop) (G : Colour)
    (ρ : FinProb (Fin q)) (D : Fin q → Law N) (μs : Fin r → Law N) (a : ℝ)
    (own : Fin r → Prop) (e : Equiv.Perm (Fin r)) (W : Fin r → Fin k → Fin N) (y : Fin N) :
    fixedRow E G ρ D (fun b => μs (e b)) a (fun b => own (e b))
      (fun b => W (e b)) y = fixedRow E G ρ D μs a own W y := by
  classical
  unfold fixedRow
  simp only [fixedListFailure_perm, listWeight, listKept_perm, fixedListHitSet_perm]
  rfl


/-- Product tuple averaging respects the same permutation of the prescribed blocks. -/
theorem fixedRow_mean_perm {N r k q : ℕ} (E : Fin N → Fin N → Prop) (G : Colour)
    (ρ : FinProb (Fin q)) (D : Fin q → Law N) (μs : Fin r → Law N) (a : ℝ)
    (own : Fin r → Prop) (e : Equiv.Perm (Fin r)) (y : Fin N) :
    (FinProb.pi (fun b => FinProb.pi (fun _ : Fin k => μs (e b)))).expect
      (fun W => fixedRow E G ρ D (fun b => μs (e b)) a (fun b => own (e b)) W y) =
    (FinProb.pi (fun b => FinProb.pi (fun _ : Fin k => μs b))).expect
      (fun W => fixedRow E G ρ D μs a own W y) := by
  let P : Fin r → FinProb (Fin k → Fin N) := fun b => FinProb.pi (fun _ => μs b)
  have h := pi_equiv_expect e.symm P
    (fun W => fixedRow E G ρ D (fun b => μs (e b)) a (fun b => own (e b)) W y)
  simp only [Equiv.symm_symm, fixedRow_perm] at h
  exact h.symm


/-- Conditional values are independent of the decision procedure for their proposition. -/
theorem ite_classical {α : Sort*} (P : Prop) (d : Decidable P) (t e : α) :
    @ite α P d t e = @ite α P (Classical.propDecidable P) t e := by
  have hd : d = Classical.propDecidable P := Subsingleton.elim _ _
  rw [hd]


/-- Universal conditions on a canonical list enumeration are conditions on its named members. -/
theorem namedList_forall {I : Type*} [DecidableEq I] (L : Finset I) (P : I → Prop) :
    (∀ b : Fin L.card, P (L.equivFin.symm b).1) ↔ ∀ c ∈ L, P c := by
  constructor
  · intro h c hc
    simpa using h (L.equivFin ⟨c, hc⟩)
  · intro h b
    exact h (L.equivFin.symm b).1 (L.equivFin.symm b).2

/-- Canonical block indices enumerate exactly the named common hits. -/
theorem fixedListHitSet_enum {I : Type*} [DecidableEq I] {N k : ℕ}
    (E : Fin N → Fin N → Prop) (G : Colour) (L : Finset I) (W : I → Fin k → Fin N) :
    fixedListHitSet E G (fun b : Fin L.card => W (L.equivFin.symm b).1) =
      Finset.univ.filter (fun y => ∀ c ∈ L, ∀ i, Hits E G (W c i) y) := by
  classical
  ext y
  simp only [fixedListHitSet, Finset.mem_filter, Finset.mem_univ, true_and]
  exact namedList_forall L (fun c => ∀ i, Hits E G (W c i) y)

/-- The canonical deletion set removes exactly the corresponding named ID. -/
theorem fixedListHitSetWithout_enum {I : Type*} [DecidableEq I] {N k : ℕ}
    (E : Fin N → Fin N → Prop) (G : Colour) (L : Finset I) (W : I → Fin k → Fin N)
    (b : Fin L.card) :
    fixedListHitSetWithout E G (fun b : Fin L.card => W (L.equivFin.symm b).1) b =
      Finset.univ.filter (fun y => ∀ c ∈ L, c ≠ (L.equivFin.symm b).1 →
        ∀ i, Hits E G (W c i) y) := by
  classical
  ext y
  simp only [fixedListHitSetWithout, Finset.mem_filter, Finset.mem_univ, true_and]
  have hne (j : Fin L.card) : j ≠ b ↔ (L.equivFin.symm j).1 ≠ (L.equivFin.symm b).1 := by
    constructor
    · intro hj heq
      exact hj (L.equivFin.symm.injective (Subtype.ext heq))
    · intro hj heq
      exact hj (congrArg (fun j => (L.equivFin.symm j).1) heq)
  simp only [hne]
  exact namedList_forall L (fun c => c ≠ (L.equivFin.symm b).1 → ∀ i, Hits E G (W c i) y)

/-- Equivalent finite block presentations have the same fixed-list row. -/
theorem fixedRow_equiv {N r s k q : ℕ} (E : Fin N → Fin N → Prop) (G : Colour)
    (ρ : FinProb (Fin q)) (D : Fin q → Law N) (μs : Fin s → Law N) (a : ℝ)
    (own : Fin s → Prop) (e : Fin r ≃ Fin s) (W : Fin s → Fin k → Fin N) (y : Fin N) :
    fixedRow E G ρ D (fun b => μs (e b)) a (fun b => own (e b)) (fun b => W (e b)) y =
      fixedRow E G ρ D μs a own W y := by
  have hrs : r = s := by simpa using Fintype.card_congr e
  subst s
  exact fixedRow_perm E G ρ D μs a own e W y

/-- Product averaging also permits equivalent presentations with different written block counts. -/
theorem fixedRow_mean_equiv {N r s k q : ℕ} (E : Fin N → Fin N → Prop) (G : Colour)
    (ρ : FinProb (Fin q)) (D : Fin q → Law N) (μs : Fin s → Law N) (a : ℝ)
    (own : Fin s → Prop) (e : Fin r ≃ Fin s) (y : Fin N) :
    (FinProb.pi (fun b => FinProb.pi (fun _ : Fin k => μs (e b)))).expect
      (fun W => fixedRow E G ρ D (fun b => μs (e b)) a (fun b => own (e b)) W y) =
    (FinProb.pi (fun b => FinProb.pi (fun _ : Fin k => μs b))).expect
      (fun W => fixedRow E G ρ D μs a own W y) := by
  have hrs : r = s := by simpa using Fintype.card_congr e
  subst s
  exact fixedRow_mean_perm E G ρ D μs a own e y

end HypercubeRamsey.Lane_sol_s10_d56
