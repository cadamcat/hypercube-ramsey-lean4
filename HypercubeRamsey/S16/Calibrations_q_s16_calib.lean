import HypercubeRamsey.PartC.Core

/-! Shared finite-weight facts used by the q-s16-calib proofs. -/

namespace HypercubeRamsey.S16.Lane_q_s16_calib

open Classical
open scoped BigOperators

variable {I O X J : Type*}

noncomputable def eventWeightSum [Fintype X] (event : X → Prop) (w : X → ℝ) : ℝ :=
  (Finset.univ.filter event).sum w

noncomputable def feasibleWeights [Fintype (I → O)]
    (safe : (I → O) → Prop) (event : J → (I → O) → Prop) (bound : J → ℝ) :
    Set ((I → O) → ℝ) :=
  {w | (∀ a, 0 ≤ w a) ∧ (∑ a, w a = 1) ∧
    (∀ a : {a : I → O // ¬ safe a}, w a.1 = 0) ∧
    (∀ j, eventWeightSum (event j) w ≤ bound j)}

noncomputable def weightMarginalImage [Fintype (I → O)]
    (G : Set ((I → O) → ℝ)) : Set ((I × O) → ℝ) :=
  {v | ∃ w ∈ G, ∀ i o,
    v (i, o) = eventWeightSum (fun a : I → O => a i = o) w}

theorem finLaw_map_pr {α β : Type*} [Fintype α] [Fintype β] [DecidableEq β]
    (Q : FinLaw α) (f : α → β) (A : β → Prop) :
    (FinLaw.map Q f).pr A = Q.pr (fun x => A (f x)) := by
  classical
  unfold FinLaw.pr FinLaw.map
  have hterm (b : β) :
      (if A b then ∑ a, if f a = b then Q.w a else 0 else 0) =
        ∑ a, if A b ∧ f a = b then Q.w a else 0 := by
    by_cases hA : A b <;> simp [hA]
  calc
    (∑ b, if A b then ∑ a, if f a = b then Q.w a else 0 else 0) =
        ∑ a, ∑ b, if A b ∧ f a = b then Q.w a else 0 := by
          simp_rw [hterm]
          rw [Finset.sum_comm]
    _ = ∑ a, if A (f a) then Q.w a else 0 := by
          apply Finset.sum_congr rfl
          intro a ha
          rw [Finset.sum_eq_single (f a)]
          · simp
          · intro b hb hne
            have hneq : ¬ f a = b := fun h => hne h.symm
            simp [hneq]
          · simp
    _ = Q.pr (fun x => A (f x)) := rfl

theorem finLaw_pr_eq_weight {α : Type*} [Fintype α] [DecidableEq α]
    (Q : FinLaw α) (x : α) : Q.pr (fun y => y = x) = Q.w x := by
  classical
  unfold FinLaw.pr
  rw [Finset.sum_eq_single x]
  · simp
  · intro y hy hne
    simp [hne]
  · simp

theorem finLaw_map_support {α β : Type*} [Fintype α] [Fintype β] [DecidableEq β]
    (Q : FinLaw α) (f : α → β) (y : β)
    (hy : (FinLaw.map Q f).w y ≠ 0) :
    ∃ x, f x = y ∧ Q.w x ≠ 0 := by
  classical
  by_contra h
  push_neg at h
  have hz : ∀ x, (if f x = y then Q.w x else 0) = 0 := by
    intro x
    by_cases hxy : f x = y
    · simp [hxy, h x hxy]
    · simp [hxy]
  apply hy
  simp [FinLaw.map, hz]

theorem finLaw_map_weight_supported {α β : Type*} [Fintype α] [Fintype β]
    [DecidableEq β] (Q : FinLaw α) (S : α → Prop)
    (e : {x // S x} → β) (f : α → β)
    (hf : ∀ x hx, f x = e ⟨x, hx⟩)
    (hsupport : ∀ x, Q.w x ≠ 0 → S x)
    (hinj : Function.Injective e) :
    ∀ y : {x // S x}, (FinLaw.map Q f).w (e y) = Q.w y.1 := by
  classical
  intro y
  unfold FinLaw.map
  change (∑ x, if f x = e y then Q.w x else 0) = Q.w y.1
  rw [Finset.sum_eq_single y.1]
  · simp [hf y.1 y.2]
  · intro x hx hne
    by_cases hs : S x
    · by_cases hxy : f x = e y
      · have heq : e ⟨x, hs⟩ = e y := by simpa [hf x hs] using hxy
        have hxval : x = y.1 := congrArg Subtype.val (hinj heq)
        exact (hne hxval).elim
      · simp [hxy]
    · have hwzero : Q.w x = 0 := by
        by_contra hw
        exact hs (hsupport x hw)
      simp [hwzero]
  · simp

theorem finLaw_pi_support {ι : Type*} [Fintype ι] [DecidableEq ι]
    {Ω : ι → Type*} [∀ i, Fintype (Ω i)]
    (P : ∀ i, FinLaw (Ω i)) (ω : ∀ i, Ω i)
    (hω : (FinLaw.pi P).w ω ≠ 0) : ∀ i, (P i).w (ω i) ≠ 0 := by
  intro i hi
  apply hω
  change (∏ j, (P j).w (ω j)) = 0
  exact Finset.prod_eq_zero (Finset.mem_univ i) hi

theorem finLaw_pi_pr_forall {ι : Type*} [Fintype ι] [DecidableEq ι]
    {Ω : ι → Type*} [∀ i, Fintype (Ω i)]
    (P : ∀ i, FinLaw (Ω i)) (C : ∀ i, Ω i → Prop) :
    (FinLaw.pi P).pr (fun x => ∀ i, C i (x i)) = ∏ i, (P i).pr (C i) := by
  classical
  let Ev : (∀ i, Ω i) → Prop := fun x => ∀ i, C i (x i)
  letI : DecidablePred Ev := fun x => Classical.propDecidable _
  have hweight (x : ∀ i, Ω i) :
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
  simp only [FinLaw.pr, FinLaw.pi]
  change (∑ x : (∀ i, Ω i), if Ev x then ∏ i, (P i).w (x i) else 0) =
    ∏ i, ∑ y : Ω i, if C i y then (P i).w y else 0
  calc
    (∑ x : (∀ i, Ω i), if Ev x then ∏ i, (P i).w (x i) else 0) =
        ∑ x : (∀ i, Ω i), ∏ i, if C i (x i) then (P i).w (x i) else 0 := by
          apply Finset.sum_congr rfl
          intro x hx
          exact hweight x
    _ = ∏ i, ∑ y : Ω i, if C i y then (P i).w y else 0 := by
          exact (Fintype.prod_sum (fun i y => if C i y then (P i).w y else 0)).symm
    _ = ∏ i, (P i).pr (C i) := by
          simp [FinLaw.pr]

theorem finLaw_pi_pr_coordinate {ι : Type*} [Fintype ι] [DecidableEq ι]
    {Ω : ι → Type*} [∀ i, Fintype (Ω i)]
    (P : ∀ i, FinLaw (Ω i)) (i : ι) (A : Ω i → Prop) :
    (FinLaw.pi P).pr (fun x => A (x i)) = (P i).pr A := by
  classical
  let C : ∀ j, Ω j → Prop := fun j z => if h : j = i then A (h ▸ z) else True
  have hEvent :
      (fun x : ∀ j, Ω j => ∀ j, C j (x j)) = (fun x => A (x i)) := by
    funext x
    apply propext
    constructor
    · intro h
      simpa [C] using h i
    · intro h j
      by_cases hj : j = i
      · subst j
        simpa [C] using h
      · simp [C, hj]
  rw [← hEvent, finLaw_pi_pr_forall]
  rw [Finset.prod_eq_single i]
  · simpa [C]
  · intro j hj hji
    have htrue : (P j).pr (fun _ => True) = 1 := by
      simp [FinLaw.pr, (P j).sum_one]
    simpa [C, hji] using htrue
  · simp

private theorem eventWeightSum_mix [Fintype X] (event : X → Prop)
    (w₁ w₂ : X → ℝ) (a b : ℝ) :
    eventWeightSum event (a • w₁ + b • w₂) =
      a * eventWeightSum event w₁ + b * eventWeightSum event w₂ := by
  classical
  unfold eventWeightSum
  simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
  rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum]

theorem feasibleWeights_weightMarginalImage_compact_convex
    [Fintype I] [DecidableEq I] [Fintype O] [Fintype (I → O)]
    (safe : (I → O) → Prop) (event : J → (I → O) → Prop) (bound : J → ℝ) :
    IsCompact (weightMarginalImage (feasibleWeights safe event bound)) ∧
      Convex ℝ (weightMarginalImage (feasibleWeights safe event bound)) := by
  classical
  let X := I → O
  let W := X → ℝ
  let Nonneg : Set W := Set.iInter fun x : X => {w : W | 0 ≤ w x}
  let Total : Set W := {w | ∑ x, w x = 1}
  let BadIndex := {x : X // ¬ safe x}
  let Supported : Set W := Set.iInter fun x : BadIndex => {w | w x.1 = 0}
  let Upper : Set W := Set.iInter fun j : J => {w : W | eventWeightSum (event j) w ≤ bound j}
  let Good : Set W := Nonneg ∩ (Total ∩ (Supported ∩ Upper))
  have hnonnegClosed : IsClosed Nonneg := by
    exact isClosed_iInter fun x : X => isClosed_Ici.preimage (continuous_apply x)
  have htotalClosed : IsClosed Total := by
    exact isClosed_eq (by fun_prop) continuous_const
  have hsupportedClosed : IsClosed Supported := by
    exact isClosed_iInter fun x : BadIndex =>
      isClosed_eq (continuous_apply x.1) continuous_const
  have hupperClosed : IsClosed Upper := by
    exact isClosed_iInter fun j : J => isClosed_le (by
      unfold eventWeightSum
      exact continuous_finsetSum _ (fun x hx => continuous_apply x)) continuous_const
  have hgoodClosed : IsClosed Good := by
    exact hnonnegClosed.inter (htotalClosed.inter (hsupportedClosed.inter hupperClosed))
  let box : Set W := Set.pi Set.univ (fun _ : X => Set.Icc (0 : ℝ) 1)
  have hboxCompact : IsCompact box := isCompact_univ_pi fun _ : X => isCompact_Icc
  have hgoodSubsetBox : Good ⊆ box := by
    intro w hw x hx
    have hnon : ∀ x : X, 0 ≤ w x := Set.mem_iInter.mp hw.1
    have hsum : ∑ x : X, w x = 1 := hw.2.1
    have hupper : w x ≤ 1 := by
      calc
        w x ≤ ∑ a : X, w a :=
          Finset.single_le_sum (fun a _ => hnon a) (Finset.mem_univ x)
        _ = 1 := hsum
    exact ⟨hnon x, hupper⟩
  have hgoodCompact : IsCompact Good :=
    hboxCompact.of_isClosed_subset hgoodClosed hgoodSubsetBox
  have hgoodConvex : Convex ℝ Good := by
    intro w₁ hw₁ w₂ hw₂ a b ha hb hab
    change (w₁ ∈ Nonneg ∧ w₁ ∈ Total ∧ w₁ ∈ Supported ∧ w₁ ∈ Upper) at hw₁
    change (w₂ ∈ Nonneg ∧ w₂ ∈ Total ∧ w₂ ∈ Supported ∧ w₂ ∈ Upper) at hw₂
    change (a • w₁ + b • w₂ ∈ Nonneg ∧ a • w₁ + b • w₂ ∈ Total ∧
      a • w₁ + b • w₂ ∈ Supported ∧ a • w₁ + b • w₂ ∈ Upper)
    refine ⟨?_, ⟨?_, ⟨?_, ?_⟩⟩⟩
    · change (a • w₁ + b • w₂) ∈ Set.iInter
        (fun x : X => {w : W | 0 ≤ w x})
      rw [Set.mem_iInter]
      simp only [Set.mem_setOf_eq]
      intro x
      change 0 ≤ a * w₁ x + b * w₂ x
      have h₁ : 0 ≤ w₁ x := by simpa using Set.mem_iInter.mp hw₁.1 x
      have h₂ : 0 ≤ w₂ x := by simpa using Set.mem_iInter.mp hw₂.1 x
      exact add_nonneg
        (mul_nonneg ha h₁) (mul_nonneg hb h₂)
    · change (∑ x : X, (a • w₁ + b • w₂) x) = 1
      calc
        ∑ x : X, (a • w₁ + b • w₂) x =
            ∑ x : X, (a * w₁ x + b * w₂ x) := by
          apply Finset.sum_congr rfl
          intro x hx
          rfl
        _ = (∑ x : X, a * w₁ x) + (∑ x : X, b * w₂ x) := Finset.sum_add_distrib
        _ = a * (∑ x : X, w₁ x) + b * (∑ x : X, w₂ x) := by
          rw [← Finset.mul_sum, ← Finset.mul_sum]
        _ = 1 := by rw [hw₁.2.1, hw₂.2.1]; nlinarith [hab]
    · change (a • w₁ + b • w₂) ∈ Set.iInter
        (fun x : BadIndex => {w : W | w x.1 = 0})
      rw [Set.mem_iInter]
      simp only [Set.mem_setOf_eq]
      intro x
      have h₁ : w₁ x.1 = 0 := by simpa using Set.mem_iInter.mp hw₁.2.2.1 x
      have h₂ : w₂ x.1 = 0 := by simpa using Set.mem_iInter.mp hw₂.2.2.1 x
      change a * w₁ x.1 + b * w₂ x.1 = 0
      rw [h₁, h₂]
      ring
    · change (a • w₁ + b • w₂) ∈ Set.iInter
        (fun j : J => {w : W | eventWeightSum (event j) w ≤ bound j})
      rw [Set.mem_iInter]
      simp only [Set.mem_setOf_eq]
      intro j
      have h₁ : eventWeightSum (event j) w₁ ≤ bound j := by
        simpa using Set.mem_iInter.mp hw₁.2.2.2 j
      have h₂ : eventWeightSum (event j) w₂ ≤ bound j := by
        simpa using Set.mem_iInter.mp hw₂.2.2.2 j
      rw [eventWeightSum_mix]
      calc
        a * eventWeightSum (event j) w₁ + b * eventWeightSum (event j) w₂ ≤
            a * bound j + b * bound j :=
          add_le_add (mul_le_mul_of_nonneg_left h₁ ha)
            (mul_le_mul_of_nonneg_left h₂ hb)
        _ = bound j := by rw [← add_mul, hab, one_mul]
  let marginal : W → (I × O → ℝ) := fun w io =>
    eventWeightSum (fun x : X => x io.1 = io.2) w
  have hmarginalContinuous : Continuous marginal := by
    apply continuous_pi
    intro io
    dsimp [marginal, eventWeightSum]
    exact continuous_finsetSum _ (fun x hx => continuous_apply x)
  have himage : weightMarginalImage (feasibleWeights safe event bound) =
      marginal '' Good := by
    ext v
    constructor
    · rintro ⟨w, hw, hv⟩
      refine ⟨w, ?_, ?_⟩
      · have hn : w ∈ Nonneg := by
          apply Set.mem_iInter.mpr
          intro x
          exact hw.1 x
        have hs : w ∈ Supported := by
          apply Set.mem_iInter.mpr
          intro x
          exact hw.2.2.1 x
        have hu : w ∈ Upper := by
          apply Set.mem_iInter.mpr
          intro j
          exact hw.2.2.2 j
        exact ⟨hn, hw.2.1, hs, hu⟩
      · funext io
        exact (hv io.1 io.2).symm
    · rintro ⟨w, hw, hv⟩
      refine ⟨w, ?_, ?_⟩
      · have hn : ∀ x : X, 0 ≤ w x := by
          intro x
          have h := Set.mem_iInter.mp hw.1 x
          change 0 ≤ w x at h
          exact h
        have hs : ∀ x : BadIndex, w x.1 = 0 := by
          intro x
          have h := Set.mem_iInter.mp hw.2.2.1 x
          change w x.1 = 0 at h
          exact h
        have hu : ∀ j : J, eventWeightSum (event j) w ≤ bound j := by
          intro j
          have h := Set.mem_iInter.mp hw.2.2.2 j
          change eventWeightSum (event j) w ≤ bound j at h
          exact h
        exact ⟨hn, hw.2.1, hs, hu⟩
      · intro i o
        exact (congrFun hv (i, o)).symm
  have hcompactImage : IsCompact (marginal '' Good) :=
    hgoodCompact.image hmarginalContinuous
  constructor
  · rw [himage]
    exact hcompactImage
  · rw [himage]
    intro v hv w hw a b ha hb hab
    rcases hv with ⟨w₁, hw₁, rfl⟩
    rcases hw with ⟨w₂, hw₂, rfl⟩
    refine ⟨a • w₁ + b • w₂, hgoodConvex hw₁ hw₂ ha hb hab, ?_⟩
    funext io
    simpa [marginal] using
      eventWeightSum_mix (fun x : X => x io.1 = io.2) w₁ w₂ a b

end HypercubeRamsey.S16.Lane_q_s16_calib
