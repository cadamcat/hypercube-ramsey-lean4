import Mathlib

/-!
# Lemma 3.4: conditional avoidance comparison

The lopsided asymmetric local lemma with conditional comparisons, on a finite probability space given by
weights, and the independent-variables case of its hypothesis. Source: `sections/03-…tex`, Lemma 3.4 and the
paragraph after it.
-/

namespace HypercubeRamsey.LocalLemma

variable {Ω : Type*} [Fintype Ω] [DecidableEq Ω] {I : Type*} [Fintype I] [DecidableEq I]

open scoped BigOperators

/-- The mass of an event. -/
def mass (w : Ω → ℝ) (A : Finset Ω) : ℝ := ∑ ω ∈ A, w ω

/-- The avoidance event `A_S`: no event indexed by `S` occurs. -/
def avoid (E : I → Finset Ω) (S : Finset I) : Finset Ω :=
  Finset.univ.filter (fun ω => ∀ j ∈ S, ω ∉ E j)

private theorem mass_nonneg (w : Ω → ℝ) (hw : ∀ ω, 0 ≤ w ω) (A : Finset Ω) :
    0 ≤ mass w A := by
  exact Finset.sum_nonneg fun ω _ => hw ω

private theorem mass_mono (w : Ω → ℝ) (hw : ∀ ω, 0 ≤ w ω) {A B : Finset Ω}
    (hAB : A ⊆ B) : mass w A ≤ mass w B := by
  exact Finset.sum_le_sum_of_subset_of_nonneg hAB fun ω _ _ => hw ω

private theorem mass_split (w : Ω → ℝ) (A B : Finset Ω) :
    mass w (A \ B) + mass w (A ∩ B) = mass w A := by
  unfold mass
  exact (add_comm _ _).trans (Finset.sum_inter_add_sum_sdiff A B w)

private theorem avoid_insert (E : I → Finset Ω) (i : I) (S : Finset I) :
    avoid E (insert i S) = avoid E S \ E i := by
  classical
  ext ω
  simp [avoid, and_comm]

private theorem avoid_antitone (E : I → Finset Ω) {S T : Finset I}
    (hST : S ⊆ T) : avoid E T ⊆ avoid E S := by
  intro ω hω
  have hT : ∀ j ∈ T, ω ∉ E j := by simpa [avoid] using hω
  have hS : ∀ j ∈ S, ω ∉ E j := fun j hj => hT j (hST hj)
  simpa [avoid] using hS

private theorem mem_avoid_iff (E : I → Finset Ω) (S : Finset I) (ω : Ω) :
    ω ∈ avoid E S ↔ ∀ j ∈ S, ω ∉ E j := by
  simp [avoid]

private theorem avoid_mass_lower (w : Ω → ℝ) (hw : ∀ ω, 0 ≤ w ω)
    (E : I → Finset Ω) (x : I → ℝ) (i : I) (S : Finset I)
    (hbound : mass w (E i ∩ avoid E S) ≤ x i * mass w (avoid E S)) :
    (1 - x i) * mass w (avoid E S) ≤ mass w (avoid E (insert i S)) := by
  rw [avoid_insert]
  have hsplit := mass_split w (avoid E S) (E i)
  rw [Finset.inter_comm] at hsplit
  have hbound' := hbound
  nlinarith

private theorem prod_antitone_of_unitInterval {S T : Finset I} {f : I → ℝ}
    (hST : S ⊆ T) (h0 : ∀ i ∈ T, 0 ≤ f i) (h1 : ∀ i ∈ T, f i ≤ 1) :
    (∏ i ∈ T, f i) ≤ ∏ i ∈ S, f i := by
  rw [← Finset.prod_sdiff hST]
  exact mul_le_of_le_one_left
    (Finset.prod_nonneg fun i hi => h0 i (hST hi))
    (Finset.prod_le_one₀
      (fun i hi => h0 i (Finset.mem_sdiff.mp hi).1)
      (fun i hi => h1 i (Finset.mem_sdiff.mp hi).1))

private theorem avoid_union_lower (w : Ω → ℝ) (hw : ∀ ω, 0 ≤ w ω)
    (E : I → Finset Ω) (x : I → ℝ) (target S U : Finset I)
    (hx1 : ∀ i, x i < 1)
    (hST : S ⊆ target) (hUT : U ⊆ target) (hSU : Disjoint S U)
    (hcond : ∀ R, R ⊂ target → ∀ i, i ∉ R →
      mass w (E i ∩ avoid E R) ≤ x i * mass w (avoid E R)) :
    mass w (avoid E S) * (∏ i ∈ U, (1 - x i)) ≤
      mass w (avoid E (S ∪ U)) := by
  classical
  revert hUT hSU
  induction U using Finset.induction_on with
  | empty => intro _ _; simp
  | @insert i U hiU ih =>
      intro hUT hSU
      have hiT : i ∈ target := hUT (Finset.mem_insert_self i U)
      have hUT' : U ⊆ target := fun j hj => hUT (Finset.mem_insert_of_mem hj)
      have hiS : i ∉ S := by
        intro hiS
        exact Finset.disjoint_left.mp hSU hiS (Finset.mem_insert_self i U)
      have hSU' : Disjoint S U := Finset.disjoint_left.mpr fun j hjS hjU =>
        Finset.disjoint_left.mp hSU hjS (Finset.mem_insert_of_mem hjU)
      have hiR : i ∉ S ∪ U := by simp [hiS, hiU]
      have hRT : S ∪ U ⊆ target := Finset.union_subset hST hUT'
      have hRproper : S ∪ U ⊂ target := by
        refine Finset.ssubset_iff_subset_ne.mpr ⟨hRT, ?_⟩
        intro heq
        exact hiR (heq.symm ▸ hiT)
      have hbound := hcond (S ∪ U) hRproper i hiR
      have hstep := avoid_mass_lower w hw E x i (S ∪ U) hbound
      have hstep' : (1 - x i) * mass w (avoid E (S ∪ U)) ≤
          mass w (avoid E (S ∪ insert i U)) := by
        rw [Finset.union_insert]
        exact hstep
      rw [Finset.prod_insert hiU]
      calc
        mass w (avoid E S) * ((1 - x i) * ∏ j ∈ U, (1 - x j)) =
            (1 - x i) * (mass w (avoid E S) * ∏ j ∈ U, (1 - x j)) := by ring
        _ ≤ (1 - x i) * mass w (avoid E (S ∪ U)) :=
          mul_le_mul_of_nonneg_left (ih hUT' hSU') (sub_nonneg.mpr (le_of_lt (hx1 i)))
        _ ≤ mass w (avoid E (S ∪ insert i U)) := hstep'

private theorem conditional_avoidance_core
    (w : Ω → ℝ) (hw : ∀ ω, 0 ≤ w ω) (hw1 : ∑ ω, w ω = 1)
    (E : I → Finset Ω) (adj : I → I → Prop) [DecidableRel adj]
    (hsymm : ∀ i j, adj i j → adj j i) (hirr : ∀ i, ¬ adj i i)
    (p x : I → ℝ)
    (hp : ∀ i (S : Finset I), i ∉ S → (∀ j ∈ S, ¬ adj i j) →
      mass w (E i ∩ avoid E S) ≤ p i * mass w (avoid E S))
    (hx0 : ∀ i, 0 ≤ x i) (hx1 : ∀ i, x i < 1)
    (hpx : ∀ i, p i ≤ x i * ∏ j ∈ Finset.univ.filter (adj i), (1 - x j)) :
    ∀ S : Finset I, (0 < mass w (avoid E S)) ∧
      (∀ i, i ∉ S → mass w (E i ∩ avoid E S) ≤ x i * mass w (avoid E S)) := by
  classical
  intro S
  refine Finset.strongInductionOn S ?_
  intro S ih
  have hpositive : 0 < mass w (avoid E S) := by
    by_cases hS : S = ∅
    · subst S
      simpa [mass, avoid, hw1] using (show (0 : ℝ) < 1 by norm_num)
    · obtain ⟨j, hj⟩ := Finset.nonempty_iff_ne_empty.mpr hS
      have hrec := ih (S.erase j) (Finset.erase_ssubset hj)
      have hjnot : j ∉ S.erase j := Finset.notMem_erase j S
      have hbound := hrec.2 j hjnot
      have hstep := avoid_mass_lower w hw E x j (S.erase j) hbound
      have hstrict : 0 < (1 - x j) * mass w (avoid E (S.erase j)) :=
        mul_pos (sub_pos.mpr (hx1 j)) hrec.1
      rw [← Finset.insert_erase hj]
      exact lt_of_lt_of_le hstrict hstep
  refine ⟨hpositive, ?_⟩
  intro i hiS
  let N := S.filter (adj i)
  let R := S.filter (fun j => ¬ adj i j)
  have hRS : R ⊆ S := Finset.filter_subset _ _
  have hNS : N ⊆ S := Finset.filter_subset _ _
  have hRN : Disjoint R N := by
    apply Finset.disjoint_left.mpr
    intro j hjR hjN
    exact (Finset.mem_filter.mp hjR).2 ((Finset.mem_filter.mp hjN).2)
  have hunion : R ∪ N = S := by
    ext j
    by_cases hj : adj i j <;> simp [R, N, hj]
  have hiR : i ∉ R := fun h => hiS (hRS h)
  have hRnon : ∀ j ∈ R, ¬ adj i j := by
    intro j hj
    exact (Finset.mem_filter.mp hj).2
  have hNneigh : N ⊆ Finset.univ.filter (adj i) := by
    intro j hj
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ j, (Finset.mem_filter.mp hj).2⟩
  have hprod : (∏ j ∈ Finset.univ.filter (adj i), (1 - x j)) ≤
      ∏ j ∈ N, (1 - x j) :=
    prod_antitone_of_unitInterval hNneigh
      (fun j _ => le_of_lt (sub_pos.mpr (hx1 j)))
      (fun j _ => sub_le_self 1 (hx0 j))
  have hpN : p i ≤ x i * ∏ j ∈ N, (1 - x j) :=
    (hpx i).trans (mul_le_mul_of_nonneg_left hprod (hx0 i))
  have hlow : mass w (avoid E R) * (∏ j ∈ N, (1 - x j)) ≤
      mass w (avoid E S) := by
    have h := avoid_union_lower w hw E x S R N hx1 hRS hNS hRN
      (fun A hAS j hjA => (ih A hAS).2 j hjA)
    simpa [hunion] using h
  have hnum : mass w (E i ∩ avoid E S) ≤ p i * mass w (avoid E R) := by
    calc
      mass w (E i ∩ avoid E S) ≤ mass w (E i ∩ avoid E R) :=
        mass_mono w hw (Finset.inter_subset_inter_left (avoid_antitone E hRS))
      _ ≤ p i * mass w (avoid E R) := hp i R hiR hRnon
  calc
    mass w (E i ∩ avoid E S) ≤ p i * mass w (avoid E R) := hnum
    _ ≤ (x i * ∏ j ∈ N, (1 - x j)) * mass w (avoid E R) :=
      mul_le_mul_of_nonneg_right hpN (mass_nonneg w hw _)
    _ = x i * (mass w (avoid E R) * ∏ j ∈ N, (1 - x j)) := by ring
        _ ≤ x i * mass w (avoid E S) :=
          mul_le_mul_of_nonneg_left hlow (hx0 i)

private theorem weighted_mass_mono (w W : Ω → ℝ) (hw : ∀ ω, 0 ≤ w ω)
    (hW : ∀ ω, 0 ≤ W ω) {A B : Finset Ω} (hAB : A ⊆ B) :
    (∑ ω ∈ A, w ω * W ω) ≤ ∑ ω ∈ B, w ω * W ω := by
  exact Finset.sum_le_sum_of_subset_of_nonneg hAB fun ω _ _ => mul_nonneg (hw ω) (hW ω)

private def outside {V : Type*} [Fintype V] [DecidableEq V] (U : Finset V) : Finset V :=
  Finset.univ.filter (fun v => v ∉ U)

private def splitAssignments {V : Type*} [Fintype V] [DecidableEq V]
    (α : V → Type*) (U : Finset V) :
    (∀ v, α v) ≃ ((∀ v : U, α v) × ∀ v : (outside U), α v) where
  toFun ω := (fun v => ω v, fun v => ω v)
  invFun p v := if hv : v ∈ U then p.1 ⟨v, hv⟩ else
    p.2 ⟨v, by simp [outside, hv]⟩
  left_inv := by
    intro ω
    funext v
    by_cases hv : v ∈ U <;> simp [hv]
  right_inv := by
    rintro ⟨f, g⟩
    apply Prod.ext
    · funext v
      simp [v.property]
    · funext v
      have hv : (v : V) ∉ U := by simpa [outside] using v.property
      simp [hv]

private theorem splitAssignments_left {V : Type*} [Fintype V] [DecidableEq V] (α : V → Type*)
    (U : Finset V) (a : ∀ v : U, α v) (b : ∀ v : (outside U), α v) (v : U) :
    (splitAssignments α U).symm (a, b) v = a v := by
  have h := congrArg Prod.fst ((splitAssignments α U).apply_symm_apply (a, b))
  exact congrFun h v

private theorem splitAssignments_right {V : Type*} [Fintype V] [DecidableEq V] (α : V → Type*)
    (U : Finset V) (a : ∀ v : U, α v) (b : ∀ v : (outside U), α v)
    (v : outside U) :
    (splitAssignments α U).symm (a, b) v = b v := by
  have h := congrArg Prod.snd ((splitAssignments α U).apply_symm_apply (a, b))
  exact congrFun h v

private theorem prod_finset_eq_prod_subtype {V : Type*} [Fintype V] [DecidableEq V]
    {α : V → Type*} [∀ v, Fintype (α v)] [∀ v, DecidableEq (α v)]
    (q : ∀ v, α v → ℝ) (U : Finset V) (a : ∀ v : U, α v) (ω : ∀ v, α v)
    (hω : ∀ v (hv : v ∈ U), ω v = a ⟨v, hv⟩) :
    (∏ v ∈ U, q v (ω v)) = ∏ v : U, q v (a v) := by
  classical
  let f : V → ℝ := fun v => if hv : v ∈ U then q v (a ⟨v, hv⟩) else 1
  calc
    (∏ v ∈ U, q v (ω v)) = ∏ v ∈ U, f v := by
      apply Finset.prod_congr rfl
      intro v hv
      rw [hω v hv]
      simp [f, hv]
    _ = ∏ v : U, f v := (Finset.prod_coe_sort U f).symm
    _ = ∏ v : U, q v (a v) := by
      apply Finset.prod_congr rfl
      intro v hv
      simp [f]

private theorem splitAssignments_weight {V : Type*} [Fintype V] [DecidableEq V]
    {α : V → Type*} [∀ v, Fintype (α v)] [∀ v, DecidableEq (α v)]
    (q : ∀ v, α v → ℝ) (U : Finset V)
    (a : ∀ v : U, α v) (b : ∀ v : (outside U), α v) :
    (∏ v, q v ((splitAssignments α U).symm (a, b) v)) =
      (∏ v : U, q v (a v)) * (∏ v : (outside U), q v (b v)) := by
  classical
  let C := outside U
  have hdis : Disjoint U C := by
    apply Finset.disjoint_left.mpr
    intro v hvU hvC
    exact (Finset.mem_filter.mp hvC).2 hvU
  have hUnion : U ∪ C = Finset.univ := by
    ext v
    by_cases hv : v ∈ U <;> simp [C, outside, hv]
  calc
    (∏ v, q v ((splitAssignments α U).symm (a, b) v)) =
        ∏ v ∈ (Finset.univ : Finset V), q v ((splitAssignments α U).symm (a, b) v) := by simp
    _ = ∏ v ∈ U ∪ C, q v ((splitAssignments α U).symm (a, b) v) := by rw [← hUnion]
    _ = (∏ v ∈ U, q v ((splitAssignments α U).symm (a, b) v)) *
          (∏ v ∈ C, q v ((splitAssignments α U).symm (a, b) v)) := Finset.prod_union hdis
    _ = (∏ v : U, q v (a v)) * (∏ v : C, q v (b v)) := by
      congr 1
      · apply prod_finset_eq_prod_subtype q U a _
        intro v hv
        exact splitAssignments_left α U a b ⟨v, hv⟩
      · apply prod_finset_eq_prod_subtype q C b _
        intro v hv
        exact splitAssignments_right α U a b ⟨v, hv⟩

private theorem mass_eq_sum_ite (w : Ω → ℝ) (A : Finset Ω) :
    mass w A = ∑ ω, if ω ∈ A then w ω else 0 := by
  classical
  exact (Finset.sum_ite_mem_eq A w).symm

private theorem sum_splitAssignments {V : Type*} [Fintype V] [DecidableEq V]
    {α : V → Type*} [∀ v, Fintype (α v)] [∀ v, DecidableEq (α v)]
    (U : Finset V) (f : (∀ v, α v) → ℝ) :
    (∑ ω, f ω) = ∑ z : ((∀ v : U, α v) × (∀ v : (outside U), α v)),
      f ((splitAssignments α U).symm z) := by
  classical
  exact (Equiv.sum_comp (splitAssignments α U).symm f).symm

private theorem pair_sum_factor {A B : Type*} [Fintype A] [Fintype B]
    (f : A → ℝ) (g : B → ℝ) (P : A → Prop) (Q : B → Prop)
    [DecidablePred P] [DecidablePred Q] :
    (∑ z : A × B, if P z.1 ∧ Q z.2 then f z.1 * g z.2 else 0) =
      (∑ a, if P a then f a else 0) * (∑ b, if Q b then g b else 0) := by
  classical
  calc
    (∑ z : A × B, if P z.1 ∧ Q z.2 then f z.1 * g z.2 else 0) =
        ∑ z : A × B, (if P z.1 then f z.1 else 0) * (if Q z.2 then g z.2 else 0) := by
      apply Finset.sum_congr rfl
      intro z hz
      by_cases hp : P z.1 <;> by_cases hq : Q z.2 <;> simp [hp, hq]
    _ = (∑ a, if P a then f a else 0) * (∑ b, if Q b then g b else 0) := by
      rw [Fintype.sum_prod_type]
      exact (Fintype.sum_mul_sum
        (fun a : A => if P a then f a else 0)
        (fun b : B => if Q b then g b else 0)).symm

private theorem sum_subtype_prod_weights {V : Type*} [Fintype V] [DecidableEq V]
    {α : V → Type*} [∀ v, Fintype (α v)] [∀ v, DecidableEq (α v)]
    (q : ∀ v, α v → ℝ) (hq1 : ∀ v, ∑ a, q v a = 1) (U : Finset V) :
    (∑ a : (∀ v : U, α v), ∏ v : U, q v (a v)) = 1 := by
  classical
  simp only [← Fintype.prod_sum, hq1, Finset.prod_const_one]

/-- Lemma 3.4. `adj` is the symmetric, irreflexive neighbour relation; the hypothesis `hp` is the lopsided
condition in multiplicative form (so it holds trivially when the conditioning event has mass zero). -/
theorem conditional_avoidance
    (w : Ω → ℝ) (hw : ∀ ω, 0 ≤ w ω) (hw1 : ∑ ω, w ω = 1)
    (E : I → Finset Ω) (adj : I → I → Prop) [DecidableRel adj]
    (hsymm : ∀ i j, adj i j → adj j i) (hirr : ∀ i, ¬ adj i i)
    (p x : I → ℝ)
    (hp : ∀ i (S : Finset I), i ∉ S → (∀ j ∈ S, ¬ adj i j) →
      mass w (E i ∩ avoid E S) ≤ p i * mass w (avoid E S))
    (hx0 : ∀ i, 0 ≤ x i) (hx1 : ∀ i, x i < 1)
    (hpx : ∀ i, p i ≤ x i * ∏ j ∈ Finset.univ.filter (adj i), (1 - x j)) :
    (0 < mass w (avoid E Finset.univ)) ∧
    (∀ i (S : Finset I), i ∉ S → mass w (E i ∩ avoid E S) ≤ x i * mass w (avoid E S)) ∧
    (∀ S T : Finset I, Disjoint S T → ∀ W : Ω → ℝ, (∀ ω, 0 ≤ W ω) →
      (∑ ω ∈ avoid E (S ∪ T), w ω * W ω) / mass w (avoid E (S ∪ T)) ≤
        (∏ j ∈ T, (1 - x j))⁻¹ * ((∑ ω ∈ avoid E S, w ω * W ω) / mass w (avoid E S))) ∧
    (∀ (F : Finset Ω) (pF : ℝ) (adjF : I → Prop) [DecidablePred adjF],
      (∀ S : Finset I, (∀ j ∈ S, ¬ adjF j) → mass w (F ∩ avoid E S) ≤ pF * mass w (avoid E S)) →
      ∀ S : Finset I, mass w (F ∩ avoid E S) / mass w (avoid E S) ≤
        pF * ∏ j ∈ S.filter adjF, (1 - x j)⁻¹) := by
  classical
  have hmain := conditional_avoidance_core w hw hw1 E adj hsymm hirr p x hp hx0 hx1 hpx
  refine ⟨(hmain Finset.univ).1, ?_, ?_, ?_⟩
  · intro i S hiS
    exact (hmain S).2 i hiS
  · intro S T hST W hW
    let a := mass w (avoid E (S ∪ T))
    let b := mass w (avoid E S)
    let u := ∑ ω ∈ avoid E (S ∪ T), w ω * W ω
    let v := ∑ ω ∈ avoid E S, w ω * W ω
    let P := ∏ j ∈ T, (1 - x j)
    have ha : 0 < a := by simpa [a] using (hmain (S ∪ T)).1
    have hb : 0 < b := by simpa [b] using (hmain S).1
    have hP : 0 < P := by
      apply Finset.prod_pos
      intro j hj
      exact sub_pos.mpr (hx1 j)
    have hlow : b * P ≤ a := by
      have h := avoid_union_lower w hw E x (S ∪ T) S T hx1
        (by intro j hj; exact Finset.mem_union_left T hj)
        (by intro j hj; exact Finset.mem_union_right S hj) hST
        (fun R _ j hjR => (hmain R).2 j hjR)
      simpa [a, b, P] using h
    have hu : 0 ≤ u := by
      dsimp [u]
      exact Finset.sum_nonneg fun ω _ => mul_nonneg (hw ω) (hW ω)
    have hv : 0 ≤ v := by
      dsimp [v]
      exact Finset.sum_nonneg fun ω _ => mul_nonneg (hw ω) (hW ω)
    have huv : u ≤ v := by
      dsimp [u, v]
      exact weighted_mass_mono w W hw hW
        (avoid_antitone E (by intro j hj; exact Finset.mem_union_left T hj))
    have hden : 0 < b * P := mul_pos hb hP
    have hfrac : v / (b * P) = P⁻¹ * (v / b) := by
      field_simp [ne_of_gt hb, ne_of_gt hP]
      <;> ring
    calc
      (∑ ω ∈ avoid E (S ∪ T), w ω * W ω) / mass w (avoid E (S ∪ T)) = u / a := rfl
      _ ≤ u / (b * P) := div_le_div_of_nonneg_left hu hden hlow
      _ ≤ v / (b * P) := div_le_div₀ hv huv hden le_rfl
      _ = P⁻¹ * (v / b) := hfrac
  · intro F pF adjF _inst hF S
    let N := S.filter adjF
    let R := S.filter (fun j => ¬ adjF j)
    let dN := mass w (avoid E N)
    let dR := mass w (avoid E R)
    let dS := mass w (avoid E S)
    let nS := mass w (F ∩ avoid E S)
    let P := ∏ j ∈ N, (1 - x j)
    have hRS : R ⊆ S := Finset.filter_subset _ _
    have hNS : N ⊆ S := Finset.filter_subset _ _
    have hRN : Disjoint R N := by
      apply Finset.disjoint_left.mpr
      intro j hjR hjN
      exact (Finset.mem_filter.mp hjR).2 ((Finset.mem_filter.mp hjN).2)
    have hunion : R ∪ N = S := by
      ext j
      by_cases hj : adjF j <;> simp [R, N, hj]
    have hRnon : ∀ j ∈ R, ¬ adjF j := by
      intro j hj
      exact (Finset.mem_filter.mp hj).2
    have hpF0 : 0 ≤ pF := by
      have hbase := hF ∅ (by intro j hj; simp at hj)
      have hmassEmpty : mass w (avoid E ∅) = 1 := by
        simpa [mass, avoid, hw1]
      have hnum0 := mass_nonneg w hw (F ∩ avoid E ∅)
      rw [hmassEmpty, mul_one] at hbase
      exact hnum0.trans hbase
    have hdR : 0 < dR := by simpa [dR] using (hmain R).1
    have hdS : 0 < dS := by simpa [dS] using (hmain S).1
    have hP : 0 < P := by
      apply Finset.prod_pos
      intro j hj
      exact sub_pos.mpr (hx1 j)
    have hlow : dR * P ≤ dS := by
      have h := avoid_union_lower w hw E x S R N hx1 hRS hNS hRN
        (fun A _ j hjA => (hmain A).2 j hjA)
      rw [hunion] at h
      simpa [dR, dS, P, mul_comm] using h
    have hN0 : 0 ≤ nS := mass_nonneg w hw _
    have hnum : nS ≤ pF * dR := by
      calc
        mass w (F ∩ avoid E S) ≤ mass w (F ∩ avoid E R) :=
          mass_mono w hw (Finset.inter_subset_inter_left (avoid_antitone E hRS))
        _ ≤ pF * mass w (avoid E R) := hF R hRnon
    have hden : 0 < P * dR := mul_pos hP hdR
    have hlow' : P * dR ≤ dS := by simpa [mul_comm] using hlow
    have hpFdR : 0 ≤ pF * dR := mul_nonneg hpF0 (le_of_lt hdR)
    have hcancel : (pF * dR) / (P * dR) = pF * P⁻¹ := by
      field_simp [ne_of_gt hP, ne_of_gt hdR]
      <;> ring
    calc
      mass w (F ∩ avoid E S) / mass w (avoid E S) = nS / dS := rfl
      _ ≤ nS / (P * dR) := div_le_div_of_nonneg_left hN0 hden hlow'
      _ ≤ (pF * dR) / (P * dR) := div_le_div₀ hpFdR hnum hden le_rfl
      _ = pF * P⁻¹ := hcancel
      _ = pF * ∏ j ∈ S.filter adjF, (1 - x j)⁻¹ := by
        have hprodInv : P⁻¹ = ∏ j ∈ S.filter adjF, (1 - x j)⁻¹ := by
          dsimp [P, N]
          rw [← Finset.prod_inv_distrib]
        exact congrArg (fun y : ℝ => pF * y) hprodInv

/-- Independent underlying variables: an event and an avoidance event with disjoint variable scopes are
independent under the product weights, so `hp` holds with `p i = mass w (E i)` when events are joined exactly
when their scopes overlap. -/
theorem mass_inter_avoid_of_disjoint_scopes {V : Type*} [Fintype V] [DecidableEq V]
    {α : V → Type*} [∀ v, Fintype (α v)] [∀ v, DecidableEq (α v)]
    (q : ∀ v, α v → ℝ) (hq0 : ∀ v a, 0 ≤ q v a) (hq1 : ∀ v, ∑ a, q v a = 1)
    (E : I → Finset (∀ v, α v)) (scope : I → Finset V)
    (hscope : ∀ i (ω ω' : ∀ v, α v), (∀ v ∈ scope i, ω v = ω' v) → (ω ∈ E i ↔ ω' ∈ E i))
    (i : I) (S : Finset I) (hS : ∀ j ∈ S, Disjoint (scope i) (scope j)) :
    mass (fun ω => ∏ v, q v (ω v)) (E i ∩ avoid E S) =
      mass (fun ω => ∏ v, q v (ω v)) (E i) * mass (fun ω => ∏ v, q v (ω v)) (avoid E S) := by
  classical
  let U := scope i
  let w : (∀ v, α v) → ℝ := fun ω => ∏ v, q v (ω v)
  let wa : (∀ v : U, α v) → ℝ := fun a => ∏ v : U, q v (a v)
  let wb : (∀ v : outside U, α v) → ℝ := fun b => ∏ v : outside U, q v (b v)
  let EA : (∀ v : U, α v) → Prop := fun a =>
    ∀ b : (∀ v : outside U, α v), (splitAssignments α U).symm (a, b) ∈ E i
  let EB : (∀ v : outside U, α v) → Prop := fun b =>
    ∀ a : (∀ v : U, α v), (splitAssignments α U).symm (a, b) ∈ avoid E S
  let ra := ∑ a, if EA a then wa a else 0
  let rb := ∑ b, if EB b then wb b else 0
  have hEi (a : ∀ v : U, α v) (b : ∀ v : outside U, α v) :
      (splitAssignments α U).symm (a, b) ∈ E i ↔ EA a := by
    constructor
    · intro h b'
      apply (hscope i _ _ ?_).mp h
      intro v hv
      have hvU : v ∈ U := by simpa [U] using hv
      exact (splitAssignments_left α U a b ⟨v, hvU⟩).trans
        (splitAssignments_left α U a b' ⟨v, hvU⟩).symm
    · intro h
      exact h b
  have hAvoid (a : ∀ v : U, α v) (b : ∀ v : outside U, α v) :
      (splitAssignments α U).symm (a, b) ∈ avoid E S ↔ EB b := by
    constructor
    · intro h a'
      apply (mem_avoid_iff E S ((splitAssignments α U).symm (a', b))).2
      intro j hj
      have hnot := (mem_avoid_iff E S _).1 h j hj
      have hscopeEq :
          (splitAssignments α U).symm (a, b) ∈ E j ↔
            (splitAssignments α U).symm (a', b) ∈ E j := by
        apply hscope j
        intro v hvj
        have hvU : v ∉ U := by
          intro hvU
          exact Finset.disjoint_left.mp (by simpa [U] using hS j hj) hvU hvj
        have hvC : v ∈ outside U := by
          simp [outside, hvU]
        exact (splitAssignments_right α U a b ⟨v, hvC⟩).trans
          (splitAssignments_right α U a' b ⟨v, hvC⟩).symm
      intro hmem
      exact hnot (hscopeEq.mpr hmem)
    · intro h
      exact h a
  have hweight (a : ∀ v : U, α v) (b : ∀ v : outside U, α v) :
      w ((splitAssignments α U).symm (a, b)) = wa a * wb b := by
    simpa [w, wa, wb] using splitAssignments_weight q U a b
  have htotalA : (∑ a : (∀ v : U, α v), wa a) = 1 := by
    simpa [wa] using sum_subtype_prod_weights q hq1 U
  have htotalB : (∑ b : (∀ v : outside U, α v), wb b) = 1 := by
    simpa [wb] using sum_subtype_prod_weights q hq1 (outside U)
  have hmassE : mass w (E i) = ra := by
    calc
      mass w (E i) = ∑ ω, if ω ∈ E i then w ω else 0 := mass_eq_sum_ite w _
      _ = ∑ z : (∀ v : U, α v) × (∀ v : outside U, α v),
            if (splitAssignments α U).symm z ∈ E i then
              w ((splitAssignments α U).symm z) else 0 :=
          sum_splitAssignments (α := α) U _
      _ = ∑ z : (∀ v : U, α v) × (∀ v : outside U, α v),
            if EA z.1 ∧ True then wa z.1 * wb z.2 else 0 := by
          apply Finset.sum_congr rfl
          intro z hz
          rcases z with ⟨a, b⟩
          simp only [hEi a b, hweight a b, and_true]
      _ = ra * (∑ b : (∀ v : outside U, α v), wb b) := by
          simpa [ra] using (pair_sum_factor wa wb EA (fun _ => True))
      _ = ra := by rw [htotalB]; ring
  have hmassAvoid : mass w (avoid E S) = rb := by
    calc
      mass w (avoid E S) = ∑ ω, if ω ∈ avoid E S then w ω else 0 := mass_eq_sum_ite w _
      _ = ∑ z : (∀ v : U, α v) × (∀ v : outside U, α v),
            if (splitAssignments α U).symm z ∈ avoid E S then
              w ((splitAssignments α U).symm z) else 0 :=
          sum_splitAssignments (α := α) U _
      _ = ∑ z : (∀ v : U, α v) × (∀ v : outside U, α v),
            if True ∧ EB z.2 then wa z.1 * wb z.2 else 0 := by
          apply Finset.sum_congr rfl
          intro z hz
          rcases z with ⟨a, b⟩
          simp only [hAvoid a b, hweight a b, true_and]
      _ = (∑ a : (∀ v : U, α v), wa a) * rb := by
          simpa [rb] using (pair_sum_factor wa wb (fun _ => True) EB)
      _ = rb := by rw [htotalA]; ring
  have hmassBoth : mass w (E i ∩ avoid E S) = ra * rb := by
    calc
      mass w (E i ∩ avoid E S) =
          ∑ ω, if ω ∈ E i ∩ avoid E S then w ω else 0 := mass_eq_sum_ite w _
      _ = ∑ z : (∀ v : U, α v) × (∀ v : outside U, α v),
            if (splitAssignments α U).symm z ∈ E i ∩ avoid E S then
              w ((splitAssignments α U).symm z) else 0 :=
          sum_splitAssignments (α := α) U _
      _ = ∑ z : (∀ v : U, α v) × (∀ v : outside U, α v),
            if EA z.1 ∧ EB z.2 then wa z.1 * wb z.2 else 0 := by
          apply Finset.sum_congr rfl
          intro z hz
          rcases z with ⟨a, b⟩
          simp only [Finset.mem_inter, hEi a b, hAvoid a b, hweight a b]
      _ = ra * rb := by simpa [ra, rb] using (pair_sum_factor wa wb EA EB)
  rw [hmassBoth, hmassE, hmassAvoid]

/-- The product weights form a probability. -/
theorem sum_prod_weights {V : Type*} [Fintype V] [DecidableEq V]
    {α : V → Type*} [∀ v, Fintype (α v)] [∀ v, DecidableEq (α v)]
    (q : ∀ v, α v → ℝ) (hq1 : ∀ v, ∑ a, q v a = 1) :
    ∑ ω : (∀ v, α v), ∏ v, q v (ω v) = 1 := by
  classical
  simp only [← Fintype.prod_sum, hq1, Finset.prod_const_one]

end HypercubeRamsey.LocalLemma
