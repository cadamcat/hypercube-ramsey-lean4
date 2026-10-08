import HypercubeRamsey.S05.Even_load_scopes_sol_s05_even
import HypercubeRamsey.Tools.ScatteredUnion

/-!
# Lane opus-s05-even: generic sub-lemmas for L5.1o

The even-load node `L5_1o` (05:1209–1282) is assembled in `Even.lean` from the sub-lemmas stated there
(they read the even-row definitions of that file) and from the generic clock comparison below.
-/

namespace HypercubeRamsey.Setup5.Lane_opus_s05_even

open Classical
open scoped BigOperators

noncomputable section

/-- SUB-LEMMA D1 (05:1266–1270, clock comparison on finitely many outputs): if a law on assignments has
cylinder probabilities on `S` at most `(1 + ε)` times a product law, then it integrates every nonnegative
function of the `S`-coordinates to at most `(1 + ε)` times the product-law mean. Group assignments by their
restriction to `S`; the product law of a cylinder is `∏_{b ∈ S} P_b(o_b)` since the other factors sum to one. -/
theorem clock_expect_le {B A : Type*} [Fintype B] [DecidableEq B] [Fintype A] [DecidableEq A]
    (Q : FinProb (B → A)) (P : B → FinProb A) (S : Finset B) (ε : ℝ) (hε : 0 ≤ ε)
    (hcyl : ∀ o : B → A, Q.pr (fun O => ∀ b ∈ S, O b = o b) ≤ (1 + ε) * ∏ b ∈ S, (P b).w (o b))
    (F : (B → A) → ℝ) (hF : ∀ O, 0 ≤ F O) (hS : FinProb.DependsOn F S) :
    Q.expect F ≤ (1 + ε) * (FinProb.pi P).expect F := by
  classical
  let C := {b : B // b ∈ S} → A
  let D := {b : B // b ∉ S} → A
  let e := Equiv.piEquivPiSubtypeProd (fun b : B => b ∈ S) (fun _ => A)
  have hnonempty : Nonempty (B → A) := by
    by_contra h
    haveI : IsEmpty (B → A) := ⟨fun o => h ⟨o⟩⟩
    have hzero : (∑ o, Q.w o) = 0 := by simp
    rw [Q.sum_eq_one] at hzero
    norm_num at hzero
  let o₀ : B → A := Classical.choice hnonempty
  let b₀ : D := fun b => o₀ b.1
  let f : C → ℝ := fun a => F (e.symm (a, b₀))
  let q : C → ℝ := fun a => ∑ b : D, Q.w (e.symm (a, b))
  let p : C → ℝ := fun a => ∏ i : {b : B // b ∈ S}, (P i.1).w (a i)
  let Pcomp : FinProb D := FinProb.pi fun b : {b : B // b ∉ S} => P b.1
  have hFsame (a : C) (b : D) : F (e.symm (a, b)) = f a := by
    apply hS
    intro i hi
    simp [f, e, Equiv.piEquivPiSubtypeProd_symm_apply, hi]
  have hQ : Q.expect F = ∑ a : C, q a * f a := by
    unfold FinProb.expect
    rw [← Equiv.sum_comp e.symm (fun o => Q.w o * F o), Fintype.sum_prod_type]
    calc
      (∑ a : C, ∑ b : D, Q.w (e.symm (a, b)) * F (e.symm (a, b))) =
          ∑ a : C, (∑ b : D, Q.w (e.symm (a, b))) * f a := by
        apply Finset.sum_congr rfl
        intro a _
        simp_rw [hFsame]
        change (∑ b ∈ (Finset.univ : Finset D), Q.w (e.symm (a, b)) * f a) =
          (∑ b ∈ (Finset.univ : Finset D), Q.w (e.symm (a, b))) * f a
        exact (Finset.sum_mul Finset.univ (fun b => Q.w (e.symm (a, b))) (f a)).symm
      _ = ∑ a : C, q a * f a := by rfl
  have hweight (a : C) (b : D) :
      (FinProb.pi P).w (e.symm (a, b)) = p a * Pcomp.w b := by
    let g : B → ℝ := fun i => (P i).w ((e.symm (a, b)) i)
    have hsprod : (∏ i : {i : B // i ∈ S}, g i.1) =
        ∏ i ∈ Finset.univ with i ∈ S, g i := by
      rw [Finset.univ_eq_attach]
      simpa [g] using Finset.prod_attach S g
    let t : Finset B := Finset.univ.filter (fun i => i ∉ S)
    let ecomp : {i : B // i ∉ S} ≃ {i : B // i ∈ t} := {
      toFun := fun i => ⟨i.1, by simp [t, i.2]⟩
      invFun := fun i => ⟨i.1, (Finset.mem_filter.mp i.2).2⟩
      left_inv := by intro i; apply Subtype.ext; rfl
      right_inv := by intro i; apply Subtype.ext; rfl
    }
    have hnot : (∏ i : {i : B // i ∉ S}, g i.1) =
        ∏ i ∈ Finset.univ with i ∉ S, g i := by
      calc
        (∏ i : {i : B // i ∉ S}, g i.1) = ∏ i : {i : B // i ∈ t}, g i.1 :=
          Fintype.prod_equiv ecomp _ _ (by intro i; rfl)
        _ = ∏ i ∈ t.attach, g i.1 := by rw [Finset.univ_eq_attach]
        _ = ∏ i ∈ t, g i := Finset.prod_attach t g
        _ = ∏ i ∈ Finset.univ with i ∉ S, g i := by simp [t]
    calc
      (FinProb.pi P).w (e.symm (a, b)) = ∏ i : B, g i := by rfl
      _ = (∏ i ∈ Finset.univ with i ∈ S, g i) *
          (∏ i ∈ Finset.univ with i ∉ S, g i) :=
        (Finset.prod_filter_mul_prod_filter_not Finset.univ (fun i : B => i ∈ S) g).symm
      _ = (∏ i : {i : B // i ∈ S}, g i.1) *
          (∏ i : {i : B // i ∉ S}, g i.1) := by rw [← hsprod, ← hnot]
      _ = p a * Pcomp.w b := by
        dsimp [p, Pcomp, FinProb.pi]
        congr 1
        · apply Fintype.prod_congr
          intro i
          simp [g, e, i.2]
        · apply Fintype.prod_congr
          intro i
          simp [g, e, i.2]
  have hP : (FinProb.pi P).expect F = ∑ a : C, p a * f a := by
    unfold FinProb.expect
    rw [← Equiv.sum_comp e.symm (fun o => (FinProb.pi P).w o * F o), Fintype.sum_prod_type]
    apply Finset.sum_congr rfl
    intro a _
    calc
      (∑ b : D, (FinProb.pi P).w (e.symm (a, b)) * F (e.symm (a, b))) =
          ∑ b : D, Pcomp.w b * (p a * f a) := by
        apply Finset.sum_congr rfl
        intro b _
        rw [hweight, hFsame]
        ring
      _ = p a * f a := by
        change (∑ b ∈ (Finset.univ : Finset D), Pcomp.w b * (p a * f a)) = p a * f a
        rw [← Finset.sum_mul]
        simp only [Pcomp.sum_eq_one, one_mul]
  let cyl (a : C) : (B → A) → Prop :=
    fun O => ∀ b ∈ S, O b = (e.symm (a, b₀)) b
  have hpr (a : C) : Q.pr (cyl a) = q a := by
    unfold FinProb.pr
    letI : DecidablePred (cyl a) := fun O => Classical.propDecidable (cyl a O)
    change (∑ O, if cyl a O then Q.w O else 0) = q a
    rw [← Equiv.sum_comp e.symm
      (fun o => if cyl a o then Q.w o else 0),
      Fintype.sum_prod_type]
    have hevent (a' : C) (b : D) :
        (∀ i ∈ S, (e.symm (a', b)) i = (e.symm (a, b₀)) i) ↔ a' = a := by
      constructor
      · intro h
        funext j
        have hj := h j.1 j.2
        simpa [e, Equiv.piEquivPiSubtypeProd_symm_apply, j.2] using hj
      · intro h i hi
        have hj := congrFun h ⟨i, hi⟩
        simpa [e, Equiv.piEquivPiSubtypeProd_symm_apply, hi] using hj
    calc
      (∑ a' : C, ∑ b : D,
          if ∀ i ∈ S, (e.symm (a', b)) i = (e.symm (a, b₀)) i
          then Q.w (e.symm (a', b)) else 0) =
          ∑ a' : C, if a' = a then q a else 0 := by
        apply Finset.sum_congr rfl
        intro a' _
        simp_rw [hevent]
        by_cases h : a' = a <;> simp [h, q]
      _ = q a := by
        simpa only [eq_comm] using
          (Fintype.sum_ite_eq' a (fun _ : C => q a)).symm
  have hprod (a : C) :
      (∏ b ∈ S, (P b).w ((e.symm (a, b₀)) b)) = p a := by
    let g : B → ℝ := fun b => (P b).w ((e.symm (a, b₀)) b)
    have hattach : (∏ i : {b : B // b ∈ S}, g i.1) = ∏ b ∈ S, g b := by
      rw [Finset.univ_eq_attach]
      simpa using Finset.prod_attach S g
    calc
      (∏ b ∈ S, (P b).w ((e.symm (a, b₀)) b)) = ∏ i : {b : B // b ∈ S}, g i.1 := hattach.symm
      _ = p a := by
        apply Finset.prod_congr rfl
        intro i _
        simp [g, p, e, Equiv.piEquivPiSubtypeProd_symm_apply]
  have hbound (a : C) : q a ≤ (1 + ε) * p a := by
    have hh := hcyl (e.symm (a, b₀))
    change Q.pr (cyl a) ≤ _ at hh
    rw [hpr, hprod] at hh
    exact hh
  calc
    Q.expect F = ∑ a : C, q a * f a := hQ
    _ ≤ ∑ a : C, ((1 + ε) * p a) * f a := by
      apply Finset.sum_le_sum
      intro a _
      exact mul_le_mul_of_nonneg_right (hbound a) (hF _)
    _ = (1 + ε) * (FinProb.pi P).expect F := by
      rw [hP]
      simp_rw [mul_assoc]
      rw [← Finset.mul_sum]

end

end HypercubeRamsey.Setup5.Lane_opus_s05_even
