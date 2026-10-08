import HypercubeRamsey.S03.Clock.Steps_sol_clock_s7_absence

set_option autoImplicit false

namespace HypercubeRamsey.Lane_sol_clock_s7

open Clock Classical
open scoped BigOperators

/-- A rate-weighted zero extension sums exactly over the injected cross-edge indices. -/
theorem sum_extended_cutoff {ι κ : Type*} [Fintype ι] [Fintype κ]
    (f : κ → ℝ) (ψ : ι → κ) (hψ : Function.Injective ψ) (cut : ι → ℕ) :
    (∑ e : κ, f e * ((Function.extend ψ cut (fun _ => 0) e : ℕ) : ℝ)) =
      ∑ c : ι, f (ψ c) * (cut c : ℝ) := by
  classical
  let s : Finset κ := Finset.univ.image ψ
  have hnot (e : κ) (he : e ∉ s) : ¬ ∃ c, ψ c = e := by
    rintro ⟨c, hc⟩
    exact he (Finset.mem_image.mpr ⟨c, Finset.mem_univ _, hc⟩)
  have hsum : (∑ e : κ, f e * ((Function.extend ψ cut (fun _ => 0) e : ℕ) : ℝ)) =
      ∑ e ∈ s, f e * ((Function.extend ψ cut (fun _ => 0) e : ℕ) : ℝ) := by
    symm
    apply Finset.sum_subset (Finset.subset_univ s)
    intro e _ he
    rw [Function.extend_apply' cut (fun _ => 0) e (hnot e he)]
    simp
  rw [hsum]
  dsimp [s]
  rw [Finset.sum_image]
  · apply Finset.sum_congr rfl
    intro c _
    rw [hψ.extend_apply cut (fun _ => 0) c]
  · intro c _ d _ hcd
    exact hψ hcd

theorem rate_times_forbidden_count {T : ℕ} (r : ℝ) (H : Fin T → Prop) :
    r * ((Finset.univ.filter H).card : ℝ) = ∑ t : Fin T, if H t then r else 0 := by
  classical
  rw [← Finset.sum_filter]
  simp [mul_comm]

/-- The total cross-survival exponent is a sum of rates at each forbidden mesh tick. -/
theorem targetCrossCutoff_rate_sum {T : ℕ} {R : Type*} [Fintype R] [DecidableEq R]
    {g : ℕ} {Ω : R → Type*} [∀ a, Fintype (Ω a)] [∀ a, DecidableEq (Ω a)]
    (ins : ∀ e : RowLabel R g, Option (MeshClockValue T (Ω e.1)))
    (ξ : ClockField T R g Ω) (S : Finset R) (o : ∀ a, Ω a)
    (lab : ∀ a, Ω a → Fin g) (times : R → Fin T) (r : R → Fin g → ℝ)
    (hInj : Set.InjOn (fun a => lab a (o a)) S) :
    (∑ e : RowLabel R g, r e.1 e.2 * (targetCrossCutoff ins ξ S o lab times e : ℝ)) =
      ∑ c : CrossIndex S (S.image fun a => lab a (o a)), ∑ t : Fin T,
        if crossForbiddenTimes ins ξ S (S.image fun a => lab a (o a)) o lab times c t then
          r (crossEdge S (S.image fun a => lab a (o a)) o lab c).1
            (crossEdge S (S.image fun a => lab a (o a)) o lab c).2
        else 0 := by
  classical
  rw [targetCrossCutoff]
  change (∑ e, (fun e : RowLabel R g => r e.1 e.2) e *
      ((Function.extend (crossEdge S (S.image fun a => lab a (o a)) o lab)
        (crossDynamicCutoff ins ξ S (S.image fun a => lab a (o a)) o lab times) (fun _ => 0) e : ℕ) : ℝ)) = _
  rw [sum_extended_cutoff _ _ (crossEdge_injective _ _ _ _ hInj)]
  apply Finset.sum_congr rfl
  intro c _
  exact rate_times_forbidden_count _ _

section Masses

variable {T : ℕ} {R : Type*} [Fintype R] [DecidableEq R]
  {g : ℕ} {Ω : R → Type*} [∀ a, Fintype (Ω a)] [∀ a, DecidableEq (Ω a)]

noncomputable def rowAvailableMass (r : R → Fin g → ℝ)
    (ins : ∀ e : RowLabel R g, Option (MeshClockValue T (Ω e.1)))
    (ξ : ClockField T R g Ω) (S : Finset R) (L : Finset (Fin g)) (a : R) (h : ℕ) : ℝ :=
  ∑ y, if y ∉ L ∧ ¬ labelUsed (backgroundAt ins ξ S L h) y then r a y else 0

noncomputable def columnAvailableMass (r : R → Fin g → ℝ)
    (ins : ∀ e : RowLabel R g, Option (MeshClockValue T (Ω e.1)))
    (ξ : ClockField T R g Ω) (S : Finset R) (L : Finset (Fin g)) (y : Fin g) (h : ℕ) : ℝ :=
  ∑ a, if a ∉ S ∧ (backgroundAt ins ξ S L h).assignment a = none then r a y else 0

noncomputable def ordinaryRowMass (r : R → Fin g → ℝ)
    (ins : ∀ e : RowLabel R g, Option (MeshClockValue T (Ω e.1)))
    (ξ : ClockField T R g Ω) (S : Finset R) (L : Finset (Fin g)) (a : R) (h : ℕ) : ℝ :=
  ∑ y, if (y ∉ L ∧ ¬ labelUsed (backgroundAt ins ξ S L h) y) ∧ ins (a, y) = none then r a y else 0

noncomputable def ordinaryColumnMass (r : R → Fin g → ℝ)
    (ins : ∀ e : RowLabel R g, Option (MeshClockValue T (Ω e.1)))
    (ξ : ClockField T R g Ω) (S : Finset R) (L : Finset (Fin g)) (y : Fin g) (h : ℕ) : ℝ :=
  ∑ a, if (a ∉ S ∧ (backgroundAt ins ξ S L h).assignment a = none) ∧ ins (a, y) = none then r a y else 0

noncomputable def prescribedRateMass (r : R → Fin g → ℝ)
    (ins : ∀ e : RowLabel R g, Option (MeshClockValue T (Ω e.1))) : ℝ :=
  ∑ e : RowLabel R g, if ins e = none then 0 else r e.1 e.2

noncomputable def prescribedCount
    (ins : ∀ e : RowLabel R g, Option (MeshClockValue T (Ω e.1))) : ℕ :=
  (Finset.univ.filter fun e => ins e ≠ none).card

theorem prescribedRateMass_le (r : R → Fin g → ℝ)
    (ins : ∀ e : RowLabel R g, Option (MeshClockValue T (Ω e.1)))
    (rateCap : ℝ) (hr : ∀ a y, r a y ≤ rateCap) : prescribedRateMass r ins ≤ prescribedCount ins * rateCap := by
  classical
  have hpoint (e : RowLabel R g) :
      (if ins e = none then 0 else r e.1 e.2) = (if ins e ≠ none then r e.1 e.2 else 0) := by
    by_cases he : ins e = none <;> simp [he]
  unfold prescribedRateMass
  simp_rw [hpoint]
  rw [← Finset.sum_filter]
  calc
    _ ≤ ∑ _e ∈ Finset.univ.filter (fun e : RowLabel R g => ins e ≠ none), rateCap := by
      apply Finset.sum_le_sum
      intro e _
      exact hr e.1 e.2
    _ = _ := by simp [prescribedCount]

theorem rowAvailableMass_le_ordinary (r : R → Fin g → ℝ)
    (ins : ∀ e : RowLabel R g, Option (MeshClockValue T (Ω e.1)))
    (ξ : ClockField T R g Ω) (S : Finset R) (L : Finset (Fin g)) (a : R) (h : ℕ)
    (hr : ∀ b y, 0 ≤ r b y) :
    rowAvailableMass r ins ξ S L a h ≤ ordinaryRowMass r ins ξ S L a h + prescribedRateMass r ins := by
  classical
  have hpoint (y : Fin g) :
      (if y ∉ L ∧ ¬ labelUsed (backgroundAt ins ξ S L h) y then r a y else 0) ≤
        (if (y ∉ L ∧ ¬ labelUsed (backgroundAt ins ξ S L h) y) ∧ ins (a, y) = none then r a y else 0) +
          (if ins (a, y) = none then 0 else r a y) := by
    by_cases hf : y ∉ L ∧ ¬ labelUsed (backgroundAt ins ξ S L h) y <;>
      by_cases hi : ins (a, y) = none <;> simp [hf, hi, hr a y]
  have hrowPres : (∑ y : Fin g, if ins (a, y) = none then 0 else r a y) ≤ prescribedRateMass r ins := by
    unfold prescribedRateMass
    rw [Fintype.sum_prod_type]
    apply Finset.single_le_sum _ (Finset.mem_univ a)
    intro b _
    apply Finset.sum_nonneg
    intro y _
    split_ifs
    · exact le_rfl
    · exact hr b y
  calc
    _ ≤ ordinaryRowMass r ins ξ S L a h + ∑ y : Fin g, if ins (a, y) = none then 0 else r a y := by
      simpa only [rowAvailableMass, ordinaryRowMass, Finset.sum_add_distrib] using
        Finset.sum_le_sum (fun y _ => hpoint y)
    _ ≤ _ := add_le_add le_rfl hrowPres

theorem columnAvailableMass_le_ordinary (r : R → Fin g → ℝ)
    (ins : ∀ e : RowLabel R g, Option (MeshClockValue T (Ω e.1)))
    (ξ : ClockField T R g Ω) (S : Finset R) (L : Finset (Fin g)) (y : Fin g) (h : ℕ)
    (hr : ∀ a z, 0 ≤ r a z) :
    columnAvailableMass r ins ξ S L y h ≤ ordinaryColumnMass r ins ξ S L y h + prescribedRateMass r ins := by
  classical
  have hpoint (a : R) :
      (if a ∉ S ∧ (backgroundAt ins ξ S L h).assignment a = none then r a y else 0) ≤
        (if (a ∉ S ∧ (backgroundAt ins ξ S L h).assignment a = none) ∧ ins (a, y) = none then r a y else 0) +
          (if ins (a, y) = none then 0 else r a y) := by
    by_cases hf : a ∉ S ∧ (backgroundAt ins ξ S L h).assignment a = none <;>
      by_cases hi : ins (a, y) = none <;> simp [hf, hi, hr a y]
  have hcolPres : (∑ a : R, if ins (a, y) = none then 0 else r a y) ≤ prescribedRateMass r ins := by
    unfold prescribedRateMass
    rw [Fintype.sum_prod_type]
    apply Finset.sum_le_sum
    intro a _
    apply Finset.single_le_sum _ (Finset.mem_univ y)
    intro z _
    split_ifs
    · exact le_rfl
    · exact hr a z
  calc
    _ ≤ ordinaryColumnMass r ins ξ S L y h + ∑ a : R, if ins (a, y) = none then 0 else r a y := by
      simpa only [columnAvailableMass, ordinaryColumnMass, Finset.sum_add_distrib] using
        Finset.sum_le_sum (fun a _ => hpoint a)
    _ ≤ _ := add_le_add le_rfl hcolPres

end Masses

private theorem sum_outside_finset {α : Type*} [Fintype α] [DecidableEq α] (s : Finset α) (f : α → ℝ) :
    (∑ a : {a // a ∉ s}, f a.1) = ∑ a, if a ∉ s then f a else 0 := by
  classical
  symm
  apply Finset.sum_congr_set {a : α | a ∉ s}
  · intro a ha
    change a ∉ s at ha
    simp [ha]
  · intro a ha
    change ¬ (a ∉ s) at ha
    simp [not_not.mp ha]

/-- The cross-survival exponent is the integrated ordinary row and label mass at each target. -/
theorem targetCrossCutoff_mass_identity {T : ℕ} {R : Type*} [Fintype R] [DecidableEq R]
    {g : ℕ} {Ω : R → Type*} [∀ a, Fintype (Ω a)] [∀ a, DecidableEq (Ω a)]
    (ins : ∀ e : RowLabel R g, Option (MeshClockValue T (Ω e.1)))
    (ξ : ClockField T R g Ω) (S : Finset R) (o : ∀ a, Ω a)
    (lab : ∀ a, Ω a → Fin g) (times : R → Fin T) (r : R → Fin g → ℝ)
    (hInj : Set.InjOn (fun a => lab a (o a)) S) :
    (∑ e : RowLabel R g, r e.1 e.2 * (targetCrossCutoff ins ξ S o lab times e : ℝ)) =
      ∑ a : S, ∑ t : Fin T, if t.val < (times a.1).val then
        ordinaryRowMass r ins ξ S (S.image fun b => lab b (o b)) a.1 (t.val + 1) +
          ordinaryColumnMass r ins ξ S (S.image fun b => lab b (o b)) (lab a.1 (o a.1)) (t.val + 1)
      else 0 := by
  let L := S.image fun b => lab b (o b)
  have hrow (a : S) :
      (∑ y : {y : Fin g // y ∉ L}, ∑ t : Fin T,
        if crossForbiddenTimes ins ξ S L o lab times (.inl (a, y)) t then r a.1 y.1 else 0) =
      ∑ t : Fin T, if t.val < (times a.1).val then
        ordinaryRowMass r ins ξ S L a.1 (t.val + 1) else 0 := by
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro t _
    by_cases ht : t.val < (times a.1).val
    · simp only [crossForbiddenTimes, ht, true_and, if_pos]
      have hs := sum_outside_finset L (fun y =>
        if ins (a.1, y) = none ∧ ¬ labelUsed (backgroundAt ins ξ S L (t.val + 1)) y then r a.1 y else 0)
      rw [hs]
      unfold ordinaryRowMass
      apply Finset.sum_congr rfl
      intro y _
      by_cases hy : y ∉ L <;>
        by_cases hi : ins (a.1, y) = none <;>
          by_cases hf : ¬ labelUsed (backgroundAt ins ξ S L (t.val + 1)) y <;> simp [hy, hi, hf]
    · simp [crossForbiddenTimes, ht]
  have hcol (a : S) :
      (∑ b : {b : R // b ∉ S}, ∑ t : Fin T,
        if crossForbiddenTimes ins ξ S L o lab times (.inr (a, b)) t then
          r b.1 (lab a.1 (o a.1)) else 0) =
      ∑ t : Fin T, if t.val < (times a.1).val then
        ordinaryColumnMass r ins ξ S L (lab a.1 (o a.1)) (t.val + 1) else 0 := by
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro t _
    by_cases ht : t.val < (times a.1).val
    · simp only [crossForbiddenTimes, ht, true_and, if_pos]
      have hs := sum_outside_finset S (fun b =>
        if ins (b, lab a.1 (o a.1)) = none ∧ (backgroundAt ins ξ S L (t.val + 1)).assignment b = none then
          r b (lab a.1 (o a.1)) else 0)
      rw [hs]
      unfold ordinaryColumnMass
      apply Finset.sum_congr rfl
      intro b _
      by_cases hb : b ∉ S <;>
        by_cases hi : ins (b, lab a.1 (o a.1)) = none <;>
          by_cases hf : (backgroundAt ins ξ S L (t.val + 1)).assignment b = none <;> simp [hb, hi, hf]
    · simp [crossForbiddenTimes, ht]
  rw [targetCrossCutoff_rate_sum ins ξ S o lab times r hInj,
    Fintype.sum_sum_type, Fintype.sum_prod_type, Fintype.sum_prod_type]
  dsimp only [crossEdge]
  calc
    _ = (∑ a : S, ∑ t : Fin T, if t.val < (times a.1).val then
          ordinaryRowMass r ins ξ S L a.1 (t.val + 1) else 0) +
        (∑ a : S, ∑ t : Fin T, if t.val < (times a.1).val then
          ordinaryColumnMass r ins ξ S L (lab a.1 (o a.1)) (t.val + 1) else 0) := by
      apply congrArg₂ (· + ·)
      · apply Finset.sum_congr rfl
        intro a _
        exact hrow a
      · apply Finset.sum_congr rfl
        intro a _
        exact hcol a
    _ = _ := by
      rw [← Finset.sum_add_distrib]
      apply Finset.sum_congr rfl
      intro a _
      rw [← Finset.sum_add_distrib]
      apply Finset.sum_congr rfl
      intro t _
      by_cases ht : t.val < (times a.1).val <;> simp [ht, L]

end HypercubeRamsey.Lane_sol_clock_s7
