import HypercubeRamsey.S15.Defs
import HypercubeRamsey.Framework.FinProbLemmas
import HypercubeRamsey.S03.ConditionalAvoidance
import HypercubeRamsey.S05.Clock_q_s05_even

namespace HypercubeRamsey.Lane_q_s15_c1

open HypercubeRamsey HypercubeRamsey.S15
open Classical
open scoped BigOperators

private def finLawToProb {Ω : Type*} [Fintype Ω] (P : HypercubeRamsey.FinLaw Ω) :
    HypercubeRamsey.FinProb Ω where
  w := P.w
  nonneg := P.nonneg
  sum_eq_one := P.sum_one

private theorem finLaw_ext {Ω : Type*} [Fintype Ω]
    {P Q : HypercubeRamsey.FinLaw Ω} (h : P.w = Q.w) : P = Q := by
  cases P with
  | mk pw pnon psum =>
    cases Q with
    | mk qw qnon qsum =>
      cases h
      have hnon : pnon = qnon := Subsingleton.elim _ _
      have hsum : psum = qsum := Subsingleton.elim _ _
      cases hnon
      cases hsum
      rfl

/-- Expanding a finite-law bind is iterated expectation. -/
private theorem finLaw_bind_E {α β : Type*} [Fintype α] [Fintype β]
    (P : HypercubeRamsey.FinLaw α) (K : α → HypercubeRamsey.FinLaw β)
    (f : α → β → ℝ) :
    (HypercubeRamsey.FinLaw.bind P K).E (fun ab => f ab.1 ab.2) =
      ∑ a, P.w a * (K a).E (f a) := by
  let P' : HypercubeRamsey.FinProb α := finLawToProb P
  let K' : α → HypercubeRamsey.FinProb β := fun a => finLawToProb (K a)
  change (HypercubeRamsey.FinProb.bind P' K').expect (fun ab => f ab.1 ab.2) =
    ∑ a, P'.w a * (K' a).expect (f a)
  exact HypercubeRamsey.FinProb.bind_expect P' K' f

private theorem finLaw_map_equiv_weight {α β : Type*} [Fintype α] [Fintype β]
    [DecidableEq β] (e : α ≃ β) (P : HypercubeRamsey.FinLaw α) (b : β) :
    (HypercubeRamsey.FinLaw.map P e).w b = P.w (e.symm b) := by
  classical
  have heq : ∀ a, (e a = b) ↔ a = e.symm b := by
    intro a
    constructor
    · intro h
      have h' := congrArg e.symm h
      simpa using h'
    · rintro rfl
      exact e.apply_symm_apply b
  simp [HypercubeRamsey.FinLaw.map, heq]

private theorem finLaw_map_equiv_pr {α β : Type*} [Fintype α] [Fintype β]
    [DecidableEq β] (e : α ≃ β) (P : HypercubeRamsey.FinLaw α)
    (A : β → Prop) :
    (HypercubeRamsey.FinLaw.map P e).pr A = P.pr (fun a => A (e a)) := by
  classical
  unfold HypercubeRamsey.FinLaw.pr
  calc
    (∑ b, if A b then (HypercubeRamsey.FinLaw.map P e).w b else 0) =
        ∑ b, if A b then P.w (e.symm b) else 0 := by
          apply Finset.sum_congr rfl
          intro b hb
          rw [finLaw_map_equiv_weight]
    _ = ∑ a, if A (e a) then P.w a else 0 := by
          rw [← Equiv.sum_comp e (fun b => if A b then P.w (e.symm b) else 0)]
          apply Finset.sum_congr rfl
          intro a ha
          simp

private theorem finLaw_map_equiv_E {α β : Type*} [Fintype α] [Fintype β]
    [DecidableEq β] (e : α ≃ β) (P : HypercubeRamsey.FinLaw α)
    (f : β → ℝ) :
    (HypercubeRamsey.FinLaw.map P e).E f = P.E (fun a => f (e a)) := by
  classical
  unfold HypercubeRamsey.FinLaw.E
  calc
    (∑ b, (HypercubeRamsey.FinLaw.map P e).w b * f b) =
        ∑ b, P.w (e.symm b) * f b := by
          apply Finset.sum_congr rfl
          intro b hb
          rw [finLaw_map_equiv_weight]
    _ = ∑ a, P.w a * f (e a) := by
          rw [← Equiv.sum_comp e (fun b => P.w (e.symm b) * f b)]
          apply Finset.sum_congr rfl
          intro a ha
          simp

private theorem finLaw_pi_unique_map {ι : Type*} [Fintype ι] [DecidableEq ι]
    [Unique ι] {Ω : ι → Type*} [∀ i, Fintype (Ω i)]
    (P : ∀ i, HypercubeRamsey.FinLaw (Ω i)) :
    HypercubeRamsey.FinLaw.map (HypercubeRamsey.FinLaw.pi P)
      (Equiv.piUnique Ω) = P default := by
  classical
  apply finLaw_ext
  funext x
  rw [finLaw_map_equiv_weight]
  simp [HypercubeRamsey.FinLaw.pi, Equiv.piUnique, Fintype.prod_unique]

/-- A function of selected coordinates has the same expectation under the restricted product law. -/
theorem pi_marginal_E {ι : Type*} [Fintype ι] [DecidableEq ι]
    {Ω : ι → Type*} [∀ i, Fintype (Ω i)]
    (P : ∀ i, HypercubeRamsey.FinLaw (Ω i)) (s : Finset ι)
    (g : (∀ i : {i // i ∈ s}, Ω i.1) → ℝ) :
    (HypercubeRamsey.FinLaw.pi P).E (fun ω => g (fun i => ω i.1)) =
      (HypercubeRamsey.FinLaw.pi (fun i : {i // i ∈ s} => P i.1)).E g := by
  let Q : ∀ i, HypercubeRamsey.FinProb (Ω i) := fun i => finLawToProb (P i)
  change (HypercubeRamsey.FinProb.pi Q).expect (fun ω => g (fun i => ω i.1)) =
    (HypercubeRamsey.FinProb.pi (fun i : {i // i ∈ s} => Q i.1)).expect g
  exact HypercubeRamsey.FinProb.pi_marginal_expect Q s g

/-- A product expectation of a selected-coordinate function can use any fixed outside extension. -/
theorem pi_E_depends {ι : Type*} [Fintype ι] [DecidableEq ι]
    {Ω : ι → Type*} [∀ i, Fintype (Ω i)]
    (P : ∀ i, HypercubeRamsey.FinLaw (Ω i)) (s : Finset ι)
    (f : (∀ i, Ω i) → ℝ) (ω₀ : ∀ i, Ω i)
    (hf : ∀ ω ω', (∀ i ∈ s, ω i = ω' i) → f ω = f ω') :
    (HypercubeRamsey.FinLaw.pi P).E f =
      (HypercubeRamsey.FinLaw.pi (fun i : {i // i ∈ s} => P i.1)).E
        (fun a => f ((Equiv.piEquivPiSubtypeProd (fun i => i ∈ s) Ω).symm
          (a, fun i => ω₀ i.1))) := by
  let Q : ∀ i, HypercubeRamsey.FinProb (Ω i) := fun i => finLawToProb (P i)
  change (HypercubeRamsey.FinProb.pi Q).expect f =
    (HypercubeRamsey.FinProb.pi (fun i : {i // i ∈ s} => Q i.1)).expect
      (fun a => f ((Equiv.piEquivPiSubtypeProd (fun i => i ∈ s) Ω).symm
        (a, fun i => ω₀ i.1)))
  exact HypercubeRamsey.FinProb.pi_expect_depends Q s f ω₀ hf

/-- The internal reference experiment's selected label marginal only reads the laws of the groups
that supply those selected word coordinates. -/
theorem internalRefLaw_E_eq_of_local_labels
    {Gp Bn Wd : Type*} [Fintype Gp] [DecidableEq Gp] [Fintype Bn]
    [Fintype Wd] [DecidableEq Wd] {N : ℕ}
    (q q' : Gp → Bn → ℝ)
    (hq0 : ∀ g D, 0 ≤ q g D) (hq1 : ∀ g, ∑ D, q g D = 1)
    (hq'0 : ∀ g D, 0 ≤ q' g D) (hq'1 : ∀ g, ∑ D, q' g D = 1)
    (U U' : Gp → Bn → Fin N → ℝ)
    (hU0 : ∀ g D z, 0 ≤ U g D z) (hU1 : ∀ g D, ∑ z, U g D z = 1)
    (hU'0 : ∀ g D z, 0 ≤ U' g D z) (hU'1 : ∀ g D, ∑ z, U' g D z = 1)
    (grp : Wd → Gp) (G : Finset Gp) (Z : Finset Wd)
    (hgrp : ∀ z ∈ Z, grp z ∈ G)
    (D₀ : Gp → Bn) (Y₀ : Wd → Fin N)
    (F : (Gp → Bn) × (Wd → Fin N) → ℝ)
    (hF : ∀ D D' Y Y', (∀ z ∈ Z, Y z = Y' z) → F (D, Y) = F (D', Y'))
    (hq : ∀ g ∈ G, ∀ D, q g D = q' g D)
    (hU : ∀ z ∈ Z, ∀ D y, U (grp z) D y = U' (grp z) D y) :
    (HypercubeRamsey.internalRefLaw q hq0 hq1 U hU0 hU1 grp).E F =
      (HypercubeRamsey.internalRefLaw q' hq'0 hq'1 U' hU'0 hU'1 grp).E F := by
  classical
  let Q : ∀ g, FinLaw Bn := fun g => ⟨q g, hq0 g, hq1 g⟩
  let Q' : ∀ g, FinLaw Bn := fun g => ⟨q' g, hq'0 g, hq'1 g⟩
  let extendG : (∀ g : {g // g ∈ G}, Bn) → (Gp → Bn) := fun d =>
    (Equiv.piEquivPiSubtypeProd (fun g => g ∈ G) (fun _ : Gp => Bn)).symm
      (d, fun g => D₀ g.1)
  let extendZ : (∀ z : {z // z ∈ Z}, Fin N) → (Wd → Fin N) := fun y =>
    (Equiv.piEquivPiSubtypeProd (fun z => z ∈ Z) (fun _ : Wd => Fin N)).symm
      (y, fun z => Y₀ z.1)
  let labelLaw (V : Gp → Bn → Fin N → ℝ)
      (v0 : ∀ g D z, 0 ≤ V g D z)
      (v1 : ∀ g D, ∑ z, V g D z = 1) (D : Gp → Bn) : FinLaw (Wd → Fin N) :=
    FinLaw.pi fun z => ⟨V (grp z) (D (grp z)),
      fun y => v0 (grp z) (D (grp z)) y, v1 (grp z) (D (grp z))⟩
  let localLabelLaw (V : Gp → Bn → Fin N → ℝ)
      (v0 : ∀ g D z, 0 ≤ V g D z)
      (v1 : ∀ g D, ∑ z, V g D z = 1) (D : Gp → Bn) :
      FinLaw (∀ z : {z // z ∈ Z}, Fin N) :=
    FinLaw.pi fun z => ⟨V (grp z.1) (D (grp z.1)),
      fun y => v0 (grp z.1) (D (grp z.1)) y, v1 (grp z.1) (D (grp z.1))⟩
  let localExpectation (V : Gp → Bn → Fin N → ℝ)
      (v0 : ∀ g D z, 0 ≤ V g D z)
      (v1 : ∀ g D, ∑ z, V g D z = 1) (D : Gp → Bn) : ℝ :=
    (localLabelLaw V v0 v1 D).E (fun y => F (D, extendZ y))
  have hlocalDep (V : Gp → Bn → Fin N → ℝ)
      (v0 : ∀ g D z, 0 ≤ V g D z)
      (v1 : ∀ g D, ∑ z, V g D z = 1) :
      ∀ D D', (∀ g ∈ G, D g = D' g) → localExpectation V v0 v1 D =
        localExpectation V v0 v1 D' := by
    intro D D' hDD
    have hLaw : localLabelLaw V v0 v1 D = localLabelLaw V v0 v1 D' := by
      apply finLaw_ext
      funext y
      simp only [localLabelLaw, FinLaw.pi]
      apply Finset.prod_congr rfl
      intro z hz
      have hbin := hDD (grp z.1) (hgrp z.1 z.2)
      simp [hbin]
    unfold localExpectation
    rw [hLaw]
    unfold FinLaw.E
    apply Finset.sum_congr rfl
    intro y hy
    have hvalue := hF D D' (extendZ y) (extendZ y) (by intro z hz; rfl)
    simpa [hvalue]
  have hproject (V : Gp → Bn → Fin N → ℝ)
      (v0 : ∀ g D z, 0 ≤ V g D z)
      (v1 : ∀ g D, ∑ z, V g D z = 1) (D : Gp → Bn) :
      (labelLaw V v0 v1 D).E (fun Y => F (D, Y)) = localExpectation V v0 v1 D := by
    unfold localExpectation localLabelLaw
    exact pi_E_depends (fun z =>
      ⟨V (grp z) (D (grp z)), fun y => v0 (grp z) (D (grp z)) y,
        v1 (grp z) (D (grp z))⟩) Z (fun Y => F (D, Y)) Y₀
        (by
          intro Y Y' hYY'
          exact hF D D Y Y' hYY')
  have hiterated :
      (HypercubeRamsey.internalRefLaw q hq0 hq1 U hU0 hU1 grp).E F =
        (FinLaw.pi Q).E (localExpectation U hU0 hU1) := by
    calc
      (HypercubeRamsey.internalRefLaw q hq0 hq1 U hU0 hU1 grp).E F =
          ∑ D, (FinLaw.pi Q).w D *
            (labelLaw U hU0 hU1 D).E (fun Y => F (D, Y)) :=
        finLaw_bind_E (FinLaw.pi Q) (labelLaw U hU0 hU1)
          (fun D Y => F (D, Y))
      _ = (FinLaw.pi Q).E (localExpectation U hU0 hU1) := by
        change (∑ D, (FinLaw.pi Q).w D *
            (labelLaw U hU0 hU1 D).E (fun Y => F (D, Y))) =
          ∑ D, (FinLaw.pi Q).w D * localExpectation U hU0 hU1 D
        apply Finset.sum_congr rfl
        intro D hD
        rw [hproject U hU0 hU1 D]
  have hiterated' :
      (HypercubeRamsey.internalRefLaw q' hq'0 hq'1 U' hU'0 hU'1 grp).E F =
        (FinLaw.pi Q').E (localExpectation U' hU'0 hU'1) := by
    calc
      (HypercubeRamsey.internalRefLaw q' hq'0 hq'1 U' hU'0 hU'1 grp).E F =
          ∑ D, (FinLaw.pi Q').w D *
            (labelLaw U' hU'0 hU'1 D).E (fun Y => F (D, Y)) :=
        finLaw_bind_E (FinLaw.pi Q') (labelLaw U' hU'0 hU'1)
          (fun D Y => F (D, Y))
      _ = (FinLaw.pi Q').E (localExpectation U' hU'0 hU'1) := by
        change (∑ D, (FinLaw.pi Q').w D *
            (labelLaw U' hU'0 hU'1 D).E (fun Y => F (D, Y))) =
          ∑ D, (FinLaw.pi Q').w D * localExpectation U' hU'0 hU'1 D
        apply Finset.sum_congr rfl
        intro D hD
        rw [hproject U' hU'0 hU'1 D]
  let QG : FinLaw (∀ g : {g // g ∈ G}, Bn) := FinLaw.pi fun g => Q g.1
  let QG' : FinLaw (∀ g : {g // g ∈ G}, Bn) := FinLaw.pi fun g => Q' g.1
  have hQG : QG = QG' := by
    apply finLaw_ext
    funext d
    simp only [QG, QG', FinLaw.pi]
    apply Finset.prod_congr rfl
    intro g hg
    exact hq g.1 g.2 (d g)
  have houter (V : Gp → Bn → Fin N → ℝ)
      (v0 : ∀ g D z, 0 ≤ V g D z)
      (v1 : ∀ g D, ∑ z, V g D z = 1) (QV : ∀ g, FinLaw Bn) :
      (FinLaw.pi QV).E (localExpectation V v0 v1) =
        (FinLaw.pi (fun g : {g // g ∈ G} => QV g.1)).E
          (fun d => localExpectation V v0 v1 (extendG d)) := by
    exact pi_E_depends QV G (localExpectation V v0 v1) D₀ (hlocalDep V v0 v1)
  have hlocalLaw (d : ∀ g : {g // g ∈ G}, Bn) :
      localLabelLaw U hU0 hU1 (extendG d) =
        localLabelLaw U' hU'0 hU'1 (extendG d) := by
    apply finLaw_ext
    funext y
    simp only [localLabelLaw, FinLaw.pi]
    apply Finset.prod_congr rfl
    intro z hz
    exact hU z.1 z.2 (extendG d (grp z.1)) (y z)
  have hlocalExpect (d : ∀ g : {g // g ∈ G}, Bn) :
      localExpectation U hU0 hU1 (extendG d) =
        localExpectation U' hU'0 hU'1 (extendG d) := by
    exact congrArg (fun P : FinLaw (∀ z : {z // z ∈ Z}, Fin N) =>
      P.E (fun y => F (extendG d, extendZ y))) (hlocalLaw d)
  calc
    (HypercubeRamsey.internalRefLaw q hq0 hq1 U hU0 hU1 grp).E F =
        (FinLaw.pi Q).E (localExpectation U hU0 hU1) := hiterated
    _ = QG.E (fun d => localExpectation U hU0 hU1 (extendG d)) :=
          houter U hU0 hU1 Q
    _ = QG'.E (fun d => localExpectation U' hU'0 hU'1 (extendG d)) := by
          rw [hQG]
          simp only [FinLaw.E]
          apply Finset.sum_congr rfl
          intro d hd
          change QG'.w d * localExpectation U hU0 hU1 (extendG d) =
            QG'.w d * localExpectation U' hU'0 hU'1 (extendG d)
          exact congrArg (fun z : ℝ => QG'.w d * z) (hlocalExpect d)
    _ = (FinLaw.pi Q').E (localExpectation U' hU'0 hU'1) :=
          (houter U' hU'0 hU'1 Q').symm
    _ = (HypercubeRamsey.internalRefLaw q' hq'0 hq'1 U' hU'0 hU'1 grp).E F :=
          hiterated'.symm

/-- The same projection identity for event probabilities. -/
theorem pi_marginal_pr {ι : Type*} [Fintype ι] [DecidableEq ι]
    {Ω : ι → Type*} [∀ i, Fintype (Ω i)]
    (P : ∀ i, HypercubeRamsey.FinLaw (Ω i)) (s : Finset ι)
    (q : (∀ i : {i // i ∈ s}, Ω i.1) → Prop) :
    (HypercubeRamsey.FinLaw.pi P).pr (fun ω => q (fun i => ω i.1)) =
      (HypercubeRamsey.FinLaw.pi (fun i : {i // i ∈ s} => P i.1)).pr q := by
  classical
  calc
    (HypercubeRamsey.FinLaw.pi P).pr (fun ω => q (fun i => ω i.1)) =
        (HypercubeRamsey.FinLaw.pi P).E (fun ω => if q (fun i => ω i.1) then 1 else 0) := by
          simp [HypercubeRamsey.FinLaw.pr, HypercubeRamsey.FinLaw.E]
    _ = (HypercubeRamsey.FinLaw.pi (fun i : {i // i ∈ s} => P i.1)).E
          (fun a => if q a then 1 else 0) :=
          pi_marginal_E P s (fun a => if q a then 1 else 0)
    _ = (HypercubeRamsey.FinLaw.pi (fun i : {i // i ∈ s} => P i.1)).pr q := by
          simp [HypercubeRamsey.FinLaw.pr, HypercubeRamsey.FinLaw.E]

/-- A product event depending on one coordinate has its marginal probability. -/
theorem pi_pr_coordinate {ι : Type*} [Fintype ι] [DecidableEq ι]
    {Ω : ι → Type*} [∀ i, Fintype (Ω i)]
    (P : ∀ i, HypercubeRamsey.FinLaw (Ω i)) (i₀ : ι) (A : Ω i₀ → Prop) :
    (HypercubeRamsey.FinLaw.pi P).pr (fun ω => A (ω i₀)) = (P i₀).pr A := by
  classical
  let s : Finset ι := {i₀}
  let I := {i : ι // i ∈ s}
  let iI : I := ⟨i₀, by simp [s]⟩
  letI : Unique I :=
    { default := iI
      uniq := by
        intro i
        apply Subtype.ext
        exact Finset.mem_singleton.mp (by simpa [s] using i.property) }
  let Psub : ∀ i : I, HypercubeRamsey.FinLaw (Ω i.1) := fun i => P i.1
  have hMarginal := pi_marginal_pr P s (fun a => A (a default))
  have hMap := finLaw_pi_unique_map Psub
  have hdefault : (default : I).1 = i₀ := by
    simp [I, iI, s]
  calc
    (HypercubeRamsey.FinLaw.pi P).pr (fun ω => A (ω i₀)) =
        (HypercubeRamsey.FinLaw.pi Psub).pr (fun a => A (a default)) := by
          simpa [s, I] using hMarginal
    _ = (HypercubeRamsey.FinLaw.map (HypercubeRamsey.FinLaw.pi Psub)
          (Equiv.piUnique (fun i : I => Ω i.1))).pr A := by
          rw [finLaw_map_equiv_pr]
          simp [Psub, Equiv.piUnique]
    _ = (Psub default).pr A := by
          exact congrArg (fun Q : HypercubeRamsey.FinLaw (Ω (default : I).1) => Q.pr A) hMap
    _ = (P i₀).pr A := by
          change (P ((default : I).1)).pr A = (P i₀).pr A
          cases hdefault
          rfl

/-- The expectation of a one-coordinate function is its coordinate marginal expectation. -/
theorem pi_E_coordinate {ι : Type*} [Fintype ι] [DecidableEq ι]
    {Ω : ι → Type*} [∀ i, Fintype (Ω i)]
    (P : ∀ i, HypercubeRamsey.FinLaw (Ω i)) (i₀ : ι) (f : Ω i₀ → ℝ) :
    (HypercubeRamsey.FinLaw.pi P).E (fun ω => f (ω i₀)) = (P i₀).E f := by
  classical
  let s : Finset ι := {i₀}
  let I := {i : ι // i ∈ s}
  let iI : I := ⟨i₀, by simp [s]⟩
  letI : Unique I :=
    { default := iI
      uniq := by
        intro i
        apply Subtype.ext
        exact Finset.mem_singleton.mp (by simpa [s] using i.property) }
  let Psub : ∀ i : I, HypercubeRamsey.FinLaw (Ω i.1) := fun i => P i.1
  have hMarginal := pi_marginal_E P s (fun a => f (a default))
  have hMap := finLaw_pi_unique_map Psub
  have hdefault : (default : I).1 = i₀ := by simp [I, iI, s]
  calc
    (HypercubeRamsey.FinLaw.pi P).E (fun ω => f (ω i₀)) =
        (HypercubeRamsey.FinLaw.pi Psub).E (fun a => f (a default)) := by
          simpa [s, I] using hMarginal
    _ = (HypercubeRamsey.FinLaw.map (HypercubeRamsey.FinLaw.pi Psub)
          (Equiv.piUnique (fun i : I => Ω i.1))).E f := by
          rw [finLaw_map_equiv_E]
          simp [Equiv.piUnique]
    _ = (Psub default).E f :=
          congrArg (fun Q : HypercubeRamsey.FinLaw (Ω (default : I).1) => Q.E f) hMap
    _ = (P i₀).E f := by
          change (P ((default : I).1)).E f = (P i₀).E f
          cases hdefault
          rfl

/-- Expectations of disjoint-coordinate functions factor under a product finite law. -/
theorem pi_E_mul_of_disjoint {ι : Type*} [Fintype ι] [DecidableEq ι]
    {Ω : ι → Type*} [∀ i, Fintype (Ω i)]
    (P : ∀ i, HypercubeRamsey.FinLaw (Ω i))
    (f g : (∀ i, Ω i) → ℝ) (s t : Finset ι)
    (hf : HypercubeRamsey.FinProb.DependsOn f s)
    (hg : HypercubeRamsey.FinProb.DependsOn g t) (hst : Disjoint s t) :
    (HypercubeRamsey.FinLaw.pi P).E (fun ω => f ω * g ω) =
      (HypercubeRamsey.FinLaw.pi P).E f * (HypercubeRamsey.FinLaw.pi P).E g := by
  let Q : ∀ i, HypercubeRamsey.FinProb (Ω i) := fun i => finLawToProb (P i)
  change (HypercubeRamsey.FinProb.pi Q).expect (fun ω => f ω * g ω) =
    (HypercubeRamsey.FinProb.pi Q).expect f * (HypercubeRamsey.FinProb.pi Q).expect g
  exact HypercubeRamsey.FinProb.pi_expect_mul_of_disjoint Q f g s t hf hg hst

/-- A product event that reads only selected coordinates can be evaluated on a fixed extension. -/
theorem pi_pr_depends {ι : Type*} [Fintype ι] [DecidableEq ι]
    {Ω : ι → Type*} [∀ i, Fintype (Ω i)]
    (P : ∀ i, HypercubeRamsey.FinLaw (Ω i)) (s : Finset ι)
    (F : (∀ i, Ω i) → Prop) (ω₀ : ∀ i, Ω i)
    (hF : ∀ ω ω', (∀ i ∈ s, ω i = ω' i) → (F ω ↔ F ω')) :
    (HypercubeRamsey.FinLaw.pi P).pr F =
      (HypercubeRamsey.FinLaw.pi (fun i : {i // i ∈ s} => P i.1)).pr
        (fun a => F ((Equiv.piEquivPiSubtypeProd (fun i => i ∈ s) Ω).symm
          (a, fun i => ω₀ i.1))) := by
  classical
  let Q : ∀ i, HypercubeRamsey.FinProb (Ω i) := fun i => finLawToProb (P i)
  let f : (∀ i, Ω i) → ℝ := fun ω => if F ω then 1 else 0
  have hf : HypercubeRamsey.FinProb.DependsOn f s := by
    intro ω ω' hω
    dsimp [f]
    have h := hF ω ω' hω
    by_cases hωF : F ω
    · have hω'F : F ω' := h.mp hωF
      simp [hωF, hω'F]
    · have hω'F : ¬ F ω' := fun hω'F => hωF (h.mpr hω'F)
      simp [hωF, hω'F]
  change (HypercubeRamsey.FinProb.pi Q).pr F =
    (HypercubeRamsey.FinProb.pi (fun i : {i // i ∈ s} => Q i.1)).pr
      (fun a => F ((Equiv.piEquivPiSubtypeProd (fun i => i ∈ s) Ω).symm
        (a, fun i => ω₀ i.1)))
  calc
    (HypercubeRamsey.FinProb.pi Q).pr F = (HypercubeRamsey.FinProb.pi Q).expect f := by
      simp [HypercubeRamsey.FinProb.pr, HypercubeRamsey.FinProb.expect, f]
    _ = (HypercubeRamsey.FinProb.pi (fun i : {i // i ∈ s} => Q i.1)).expect
          (fun a => f ((Equiv.piEquivPiSubtypeProd (fun i => i ∈ s) Ω).symm
            (a, fun i => ω₀ i.1))) :=
          HypercubeRamsey.FinProb.pi_expect_depends Q s f ω₀ hf
    _ = (HypercubeRamsey.FinProb.pi (fun i : {i // i ∈ s} => Q i.1)).pr
          (fun a => F ((Equiv.piEquivPiSubtypeProd (fun i => i ∈ s) Ω).symm
            (a, fun i => ω₀ i.1))) := by
          simp [HypercubeRamsey.FinProb.pr, HypercubeRamsey.FinProb.expect, f]

/-- Events on disjoint sets of coordinates are independent under a product finite law. -/
theorem pi_pr_and_of_disjoint {ι : Type*} [Fintype ι] [DecidableEq ι]
    {Ω : ι → Type*} [∀ i, Fintype (Ω i)]
    (P : ∀ i, HypercubeRamsey.FinLaw (Ω i))
    (F G : (∀ i, Ω i) → Prop) (s t : Finset ι)
    (hF : ∀ ω ω', (∀ i ∈ s, ω i = ω' i) → (F ω ↔ F ω'))
    (hG : ∀ ω ω', (∀ i ∈ t, ω i = ω' i) → (G ω ↔ G ω')) (hst : Disjoint s t) :
    (HypercubeRamsey.FinLaw.pi P).pr (fun ω => F ω ∧ G ω) =
      (HypercubeRamsey.FinLaw.pi P).pr F * (HypercubeRamsey.FinLaw.pi P).pr G := by
  classical
  let f : (∀ i, Ω i) → ℝ := fun ω => if F ω then 1 else 0
  let g : (∀ i, Ω i) → ℝ := fun ω => if G ω then 1 else 0
  have hf : HypercubeRamsey.FinProb.DependsOn f s := by
    intro ω ω' hω
    dsimp [f]
    have h := hF ω ω' hω
    by_cases hωF : F ω
    · have hω'F : F ω' := h.mp hωF
      simp [hωF, hω'F]
    · have hω'F : ¬ F ω' := fun hω'F => hωF (h.mpr hω'F)
      simp [hωF, hω'F]
  have hg : HypercubeRamsey.FinProb.DependsOn g t := by
    intro ω ω' hω
    dsimp [g]
    have h := hG ω ω' hω
    by_cases hωG : G ω
    · have hω'G : G ω' := h.mp hωG
      simp [hωG, hω'G]
    · have hω'G : ¬ G ω' := fun hω'G => hωG (h.mpr hω'G)
      simp [hωG, hω'G]
  have hfg : (fun ω => if F ω ∧ G ω then 1 else 0) = fun ω => f ω * g ω := by
    funext ω
    by_cases h₁ : F ω <;> by_cases h₂ : G ω <;> simp [f, g, h₁, h₂]
  calc
    (HypercubeRamsey.FinLaw.pi P).pr (fun ω => F ω ∧ G ω) =
        (HypercubeRamsey.FinLaw.pi P).E (fun ω => if F ω ∧ G ω then 1 else 0) := by
          classical
          simp only [HypercubeRamsey.FinLaw.pr, HypercubeRamsey.FinLaw.E]
          apply Finset.sum_congr rfl
          intro ω hω
          by_cases h : F ω ∧ G ω <;> simp [h]
    _ = (HypercubeRamsey.FinLaw.pi P).E (fun ω => f ω * g ω) := by rw [hfg]
    _ = (HypercubeRamsey.FinLaw.pi P).E f * (HypercubeRamsey.FinLaw.pi P).E g :=
          pi_E_mul_of_disjoint P f g s t hf hg hst
    _ = (HypercubeRamsey.FinLaw.pi P).pr F * (HypercubeRamsey.FinLaw.pi P).pr G := by
          simp [f, g, HypercubeRamsey.FinLaw.pr, HypercubeRamsey.FinLaw.E]

/-- The raw product law restricted to a finite set of primitive records. -/
noncomputable def clusterHistoryScopeLaw {κ : CConsts} {T : Stage} {k : ℕ}
    (PT : ProfiledTiling κ T k) (hPT : PT.Valid)
    (hm : PT.tiling.mode = .highSmall ∨ PT.tiling.mode = .highLarge)
    (S : Finset (ClusterRecordIndex PT hPT hm)) :
    FinLaw (∀ r : {r // r ∈ S}, ClusterRecordValue r.1) := by
  classical
  exact FinLaw.pi fun r =>
    let Sl := clusterSolver PT hPT hm r.1.1.1
    ⟨Sl.lawRec PT.parameter r.1.2,
      Sl.lawRec_nonneg PT.parameter r.1.2,
      Sl.lawRec_sum PT.parameter r.1.2⟩

/-- All primitive records belonging to a single patch. -/
noncomputable def clusterPatchRecordScope {κ : CConsts} {T : Stage} {k : ℕ}
    (PT : ProfiledTiling κ T k) (hPT : PT.Valid)
    (hm : PT.tiling.mode = .highSmall ∨ PT.tiling.mode = .highLarge)
    (i : Fin PT.tiling.m) : Finset (ClusterRecordIndex PT hPT hm) :=
  Finset.univ.filter fun r => r.1.1 = i

/-- The local query site whose solver marginal supplies one odd cube position. -/
noncomputable def clusterMarginalConsultation {κ : CConsts} {T : Stage} {k : ℕ}
    (PT : ProfiledTiling κ T k) (hPT : PT.Valid)
    (hm : PT.tiling.mode = .highSmall ∨ PT.tiling.mode = .highLarge)
    (b : OddPosition T k) : ClusterConsultation PT := by
  let s := clusterSliceAt PT hPT b.1
  let S := clusterSolver PT hPT hm s.1
  let g := S.groupOf (solverWordAt PT hPT hm b.1)
  exact ⟨s, (groupCenter g).1⟩

/-- A solver's odd marginal is fixed by the records in its consultation domain. -/
theorem clusterMarginal_eq_of_consultation_scope {κ : CConsts} {T : Stage} {k : ℕ}
    (PT : ProfiledTiling κ T k) (hPT : PT.Valid)
    (hm : PT.tiling.mode = .highSmall ∨ PT.tiling.mode = .highLarge)
    (W W' : ClusterHistory PT hPT hm) (b : OddPosition T k)
    (hWW' : ∀ r ∈ clusterConsultationScope PT hPT hm
      {clusterMarginalConsultation PT hPT hm b}, W r = W' r)
    (y : Fin (T.S.N k)) :
    clusterMarginal PT hPT hm W b y = clusterMarginal PT hPT hm W' b y := by
  classical
  let s := clusterSliceAt PT hPT b.1
  let S := clusterSolver PT hPT hm s.1
  let g := S.groupOf (solverWordAt PT hPT hm b.1)
  let c := clusterMarginalConsultation PT hPT hm b
  have hlocal : ∀ r, (_root_.hammingDist (S.loc r) (groupCenter g).1 : ℝ) ≤
      10 * κ.ρ * (PT.tiling.P s.1).h →
      historyOnSlice W s r = historyOnSlice W' s r := by
    intro r hr
    let ri : ClusterRecordIndex PT hPT hm := ⟨s, r⟩
    have hmem : ri ∈ clusterConsultationScope PT hPT hm {c} := by
      simp only [clusterConsultationScope, Finset.mem_filter, Finset.mem_univ, true_and]
      refine ⟨c, by simp [c], rfl, ?_⟩
      simpa [c, clusterMarginalConsultation, s, S, g] using hr
    exact hWW' ri hmem
  have hq (D : Bin PT.tiling s.1) :
      S.q g (historyOnSlice W s) D = S.q g (historyOnSlice W' s) D :=
    congrFun (S.q_local g (historyOnSlice W s) (historyOnSlice W' s) hlocal) D
  have hU (D : Bin PT.tiling s.1) (z : Fin (T.S.N k)) :
      S.U g (historyOnSlice W s) D z = S.U g (historyOnSlice W' s) D z :=
    congrFun (S.U_local g (historyOnSlice W s) (historyOnSlice W' s) D hlocal) z
  simp only [clusterMarginal]
  rw [SliceSolver.oddMarginal]
  apply Finset.sum_congr rfl
  intro D hD
  rw [hq D, hU D y]

/-- A selected group's bin and label rules are fixed by its center consultation. -/
theorem clusterSliceGroupLaws_eq_of_consultation_scope {κ : CConsts} {T : Stage} {k : ℕ}
    (PT : ProfiledTiling κ T k) (hPT : PT.Valid)
    (hm : PT.tiling.mode = .highSmall ∨ PT.tiling.mode = .highLarge)
    (s : ClusterSlice PT) (g : Group PT.tiling s.1)
    (W W' : ClusterHistory PT hPT hm)
    (hWW' : ∀ r ∈ clusterConsultationScope PT hPT hm
      {⟨s, (groupCenter g).1⟩}, W r = W' r) :
    let S := clusterSolver PT hPT hm s.1
    (S.q g (historyOnSlice W s) = S.q g (historyOnSlice W' s)) ∧
      (∀ D, S.U g (historyOnSlice W s) D = S.U g (historyOnSlice W' s) D) := by
  classical
  let S := clusterSolver PT hPT hm s.1
  have hlocal : ∀ r, (_root_.hammingDist (S.loc r) (groupCenter g).1 : ℝ) ≤
      10 * κ.ρ * (PT.tiling.P s.1).h →
      historyOnSlice W s r = historyOnSlice W' s r := by
    intro r hr
    let ri : ClusterRecordIndex PT hPT hm := ⟨s, r⟩
    have hmem : ri ∈ clusterConsultationScope PT hPT hm
        {⟨s, (groupCenter g).1⟩} := by
      simp only [clusterConsultationScope, Finset.mem_filter, Finset.mem_univ, true_and]
      refine ⟨⟨s, (groupCenter g).1⟩, by simp, rfl, ?_⟩
      exact hr
    exact hWW' ri hmem
  refine ⟨S.q_local g (historyOnSlice W s) (historyOnSlice W' s) hlocal, ?_⟩
  intro D
  exact S.U_local g (historyOnSlice W s) (historyOnSlice W' s) D hlocal

/-- Consultation scopes grow monotonically with their finite set of query sites. -/
theorem clusterConsultationScope_mono {κ : CConsts} {T : Stage} {k : ℕ}
    (PT : ProfiledTiling κ T k) (hPT : PT.Valid)
    (hm : PT.tiling.mode = .highSmall ∨ PT.tiling.mode = .highLarge)
    (U V : Finset (ClusterConsultation PT)) (hUV : U ⊆ V) :
    clusterConsultationScope PT hPT hm U ⊆ clusterConsultationScope PT hPT hm V := by
  intro r hr
  rcases Finset.mem_filter.mp hr with ⟨hrU, c, hc, e, hdist⟩
  exact Finset.mem_filter.mpr ⟨hrU, c, hUV hc, e, hdist⟩

/-- The local query sites supplying the center's bulk odd marginals. -/
noncomputable def clusterBulkMarginalConsultations {κ : CConsts} {T : Stage} {k : ℕ}
    (PT : ProfiledTiling κ T k) (hPT : PT.Valid)
    (hm : PT.tiling.mode = .highSmall ∨ PT.tiling.mode = .highLarge)
    (a : EvenPosition T k) : Finset (ClusterConsultation PT) :=
  (clusterBulkNeighbours PT hPT a).image (clusterMarginalConsultation PT hPT hm)

/-- The consultation site for the center's even row and local test. -/
noncomputable def clusterCenterConsultation {κ : CConsts} {T : Stage} {k : ℕ}
    (PT : ProfiledTiling κ T k) (hPT : PT.Valid)
    (hm : PT.tiling.mode = .highSmall ∨ PT.tiling.mode = .highLarge)
    (a : EvenPosition T k) : ClusterConsultation PT :=
  ⟨clusterSliceAt PT hPT a.1, (clusterCenterRole PT hPT hm a).1⟩

/-- The center's internal star words, whose labels are used by its slice row. -/
noncomputable def clusterCenterStarWords {κ : CConsts} {T : Stage} {k : ℕ}
    (PT : ProfiledTiling κ T k) (hPT : PT.Valid)
    (hm : PT.tiling.mode = .highSmall ∨ PT.tiling.mode = .highLarge)
    (a : EvenPosition T k) : Finset (IWord PT.tiling (patchAt PT hPT a.1)) :=
  Finset.univ.image fun l : Fin (PT.tiling.P (patchAt PT hPT a.1)).h =>
    flipPos (clusterCenterRole PT hPT hm a).1 l

/-- The even row read by a center depends on its internal reference outcome at that slice. -/
noncomputable def clusterSigmaAtCenter {κ : CConsts} {T : Stage} {k : ℕ}
    (PT : ProfiledTiling κ T k) (hPT : PT.Valid)
    (hm : PT.tiling.mode = .highSmall ∨ PT.tiling.mode = .highLarge)
    (W : ClusterHistory PT hPT hm) (a : EvenPosition T k)
    (Y : ClusterSliceOutcome PT (clusterSliceAt PT hPT a.1).1)
    (x : Fin (T.S.N k)) : ℝ := by
  let s := clusterSliceAt PT hPT a.1
  let S := clusterSolver PT hPT hm s.1
  let v := clusterCenterRole PT hPT hm a
  exact S.σ v (historyOnSlice W s) (nbrLabels v.1 Y.2) x

/-- The groups that supply the labels in the center's internal star. -/
noncomputable def clusterCenterStarGroups {κ : CConsts} {T : Stage} {k : ℕ}
    (PT : ProfiledTiling κ T k) (hPT : PT.Valid)
    (hm : PT.tiling.mode = .highSmall ∨ PT.tiling.mode = .highLarge)
    (a : EvenPosition T k) : Finset (Group PT.tiling (patchAt PT hPT a.1)) :=
  (clusterCenterStarWords PT hPT hm a).image
    (clusterSolver PT hPT hm (patchAt PT hPT a.1)).groupOf

/-- The consultations controlling labels read from the center's internal star. -/
noncomputable def clusterCenterStarConsultations {κ : CConsts} {T : Stage} {k : ℕ}
    (PT : ProfiledTiling κ T k) (hPT : PT.Valid)
    (hm : PT.tiling.mode = .highSmall ∨ PT.tiling.mode = .highLarge)
    (a : EvenPosition T k) : Finset (ClusterConsultation PT) := by
  let s := clusterSliceAt PT hPT a.1
  let S := clusterSolver PT hPT hm s.1
  exact (clusterCenterStarWords PT hPT hm a).image fun z =>
    ⟨s, (groupCenter (S.groupOf z)).1⟩

/-- All consultation sites used by the three alarms at one even row. -/
noncomputable def clusterRowConsultations {κ : CConsts} {T : Stage} {k : ℕ}
    (PT : ProfiledTiling κ T k) (hPT : PT.Valid)
    (hm : PT.tiling.mode = .highSmall ∨ PT.tiling.mode = .highLarge)
    (a : EvenPosition T k) : Finset (ClusterConsultation PT) :=
  insert (clusterCenterConsultation PT hPT hm a)
    (clusterBulkMarginalConsultations PT hPT hm a ∪
      clusterCenterStarConsultations PT hPT hm a)

/-- Restricting Boolean words to an injectively selected coordinate set cannot increase distance. -/
private theorem hammingDist_restrict_le {m n : ℕ} (f : Fin m → Fin n)
    (hf : Function.Injective f) (u v : OAI.HypercubeRamsey.CubeVertex n) :
    _root_.hammingDist (fun j => u (f j)) (fun j => v (f j)) ≤
      _root_.hammingDist u v := by
  classical
  let A := Finset.univ.filter fun j : Fin m => u (f j) ≠ v (f j)
  let B := Finset.univ.filter fun j : Fin n => u j ≠ v j
  have hsub : A.image f ⊆ B := by
    intro j hj
    rcases Finset.mem_image.mp hj with ⟨j', hj', rfl⟩
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, (Finset.mem_filter.mp hj').2⟩
  have himage : A.card = (A.image f).card :=
    (Finset.card_image_of_injective A hf).symm
  change A.card ≤ B.card
  exact himage ▸ Finset.card_le_card hsub

/-- One coordinate flip has Hamming distance one. -/
private theorem hammingDist_flipPos_one {n : ℕ}
    (v : OAI.HypercubeRamsey.CubeVertex n) (j : Fin n) :
    _root_.hammingDist v (flipPos v j) = 1 := by
  have h := HypercubeRamsey.cubeFlip_adj v j
  change _root_.hammingDist v (HypercubeRamsey.cubeFlip v j) = 1 at h
  simpa [flipPos, HypercubeRamsey.cubeFlip] using h

private def clusterOutsideCoord {n h : ℕ} (j : Fin (n - h)) : Fin n :=
  ⟨j.val, lt_of_lt_of_le j.isLt (Nat.sub_le n h)⟩

private def clusterInternalCoord {n h : ℕ} (hh : h ≤ n) (j : Fin h) : Fin n :=
  ⟨n - h + j.val, by omega⟩

private theorem clusterOutsideCoord_injective {n h : ℕ} :
  Function.Injective (@clusterOutsideCoord n h) := by
  intro j j' hj
  have hval := congrArg (fun x : Fin n => x.val) hj
  change j.val = j'.val at hval
  exact Fin.ext hval

private theorem clusterInternalCoord_injective {n h : ℕ} (hh : h ≤ n) :
    Function.Injective (clusterInternalCoord hh) := by
  intro j j' hj
  have hval := congrArg Fin.val hj
  exact Fin.ext (Nat.add_left_cancel hval)

private theorem outsideWord_hammingDist_le {κ : CConsts} {T : Stage} {k : ℕ}
    (PT : ProfiledTiling κ T k) (hPT : PT.Valid) (i : Fin PT.tiling.m)
    (v w : Position T k) :
    _root_.hammingDist (outsideWord PT hPT i v) (outsideWord PT hPT i w) ≤
      _root_.hammingDist v w := by
  change _root_.hammingDist (fun j : Fin (T.S.n k - (PT.tiling.P i).h) =>
      v (clusterOutsideCoord j)) (fun j => w (clusterOutsideCoord j)) ≤ _
  exact hammingDist_restrict_le clusterOutsideCoord clusterOutsideCoord_injective v w

private theorem internalWord_hammingDist_le {κ : CConsts} {T : Stage} {k : ℕ}
    (PT : ProfiledTiling κ T k) (hPT : PT.Valid) (i : Fin PT.tiling.m)
    (v w : Position T k) :
    _root_.hammingDist (internalWord PT hPT i v) (internalWord PT hPT i w) ≤
      _root_.hammingDist v w := by
  let hh := clusterHeight_le PT hPT i
  change _root_.hammingDist (fun j : Fin (PT.tiling.P i).h =>
      v (clusterInternalCoord hh j)) (fun j => w (clusterInternalCoord hh j)) ≤ _
  exact hammingDist_restrict_le (clusterInternalCoord hh)
    (clusterInternalCoord_injective hh) v w

private theorem clusterSolverWordAt_dist_le_one {κ : CConsts} {T : Stage} {k : ℕ}
    (PT : ProfiledTiling κ T k) (hPT : PT.Valid)
    (hm : PT.tiling.mode = .highSmall ∨ PT.tiling.mode = .highLarge)
    (v : Position T k) :
    _root_.hammingDist (clusterWordAt PT hPT v) (solverWordAt PT hPT hm v) ≤ 1 := by
  classical
  unfold solverWordAt
  dsimp
  split_ifs with h
  · simp
  · exact Nat.le_of_eq (hammingDist_flipPos_one _ _)

private theorem clusterSolverWordAt_dist_le_one_symm {κ : CConsts} {T : Stage} {k : ℕ}
    (PT : ProfiledTiling κ T k) (hPT : PT.Valid)
    (hm : PT.tiling.mode = .highSmall ∨ PT.tiling.mode = .highLarge)
    (v : Position T k) :
    _root_.hammingDist (solverWordAt PT hPT hm v) (clusterWordAt PT hPT v) ≤ 1 := by
  rw [_root_.hammingDist_comm]
  exact clusterSolverWordAt_dist_le_one PT hPT hm v

private theorem clusterSolverWordAt_role_iff {κ : CConsts} {T : Stage} {k : ℕ}
    (PT : ProfiledTiling κ T k) (hPT : PT.Valid)
    (hm : PT.tiling.mode = .highSmall ∨ PT.tiling.mode = .highLarge)
    (v : Position T k) :
    HypercubeRamsey.IsEvenRole (solverWordAt PT hPT hm v) ↔
      HypercubeRamsey.IsEvenRole v := by
  classical
  unfold solverWordAt
  dsimp
  split_ifs with h
  · exact h
  · have hflip := HypercubeRamsey.S15.evenRole_flipPos (clusterWordAt PT hPT v)
      ⟨0, clusterHeight_pos PT hPT hm (patchAt PT hPT v)⟩
    by_cases hz : HypercubeRamsey.IsEvenRole (clusterWordAt PT hPT v) <;>
      by_cases hv : HypercubeRamsey.IsEvenRole v <;> simp_all

private theorem clusterGroupCenter_dist_le_one_of_fiber {κ : CConsts} {T : Stage} {k : ℕ}
    (PT : ProfiledTiling κ T k) (i : Fin PT.tiling.m)
    (g : Group PT.tiling i) (z : IWord PT.tiling i)
    (hz : z ∈ groupFiber g) :
    _root_.hammingDist (groupCenter g).1 z ≤ 1 := by
  rcases Finset.mem_image.mp hz with ⟨j, -, rfl⟩
  exact Nat.le_of_eq (hammingDist_flipPos_one _ _)

private theorem clusterAdjacent_hammingDist_eq_one {T : Stage} {k : ℕ}
    (a : EvenPosition T k) (b : OddPosition T k) (hab : Adjacent a b) :
    _root_.hammingDist a.1 b.1 = 1 := by
  simpa [Adjacent, OAI.HypercubeRamsey.cube] using hab

private theorem clusterMarginalQuery_word_dist_le_three {κ : CConsts} {T : Stage} {k : ℕ}
    (PT : ProfiledTiling κ T k) (hPT : PT.Valid)
    (hm : PT.tiling.mode = .highSmall ∨ PT.tiling.mode = .highLarge)
    (a : EvenPosition T k) (b : OddPosition T k)
    (hab : Adjacent a b) :
    _root_.hammingDist (internalWord PT hPT (patchAt PT hPT b.1) a.1)
      (clusterMarginalConsultation PT hPT hm b).2 ≤ 3 := by
  classical
  let i := patchAt PT hPT b.1
  let s := clusterSliceAt PT hPT b.1
  let S := clusterSolver PT hPT hm s.1
  let z := solverWordAt PT hPT hm b.1
  let g := S.groupOf z
  have hz : ¬ HypercubeRamsey.IsEvenRole z := by
    intro hz
    exact b.2 ((clusterSolverWordAt_role_iff PT hPT hm b.1).mp hz)
  have hgroup := S.groupOf_spec z hz
  have hcenter := clusterGroupCenter_dist_le_one_of_fiber PT i g z hgroup
  have hadj := clusterAdjacent_hammingDist_eq_one a b hab
  have hraw : _root_.hammingDist (internalWord PT hPT i a.1)
      (internalWord PT hPT i b.1) ≤ 1 := by
    exact (internalWord_hammingDist_le PT hPT i a.1 b.1).trans (by omega)
  have hsolver : _root_.hammingDist (internalWord PT hPT i a.1)
      (solverWordAt PT hPT hm b.1) ≤ 2 := by
    have ht := _root_.hammingDist_triangle
      (internalWord PT hPT i a.1) (clusterWordAt PT hPT b.1)
      (solverWordAt PT hPT hm b.1)
    have hraw' : clusterWordAt PT hPT b.1 = internalWord PT hPT i b.1 := by
      simp [clusterWordAt, i, clusterSliceAt]
    have hleft : _root_.hammingDist (internalWord PT hPT i a.1)
        (clusterWordAt PT hPT b.1) ≤ 1 := by simpa [hraw'] using hraw
    have hright := clusterSolverWordAt_dist_le_one PT hPT hm b.1
    omega
  have hcenter' : _root_.hammingDist (solverWordAt PT hPT hm b.1) (groupCenter g).1 ≤ 1 := by
    calc
      _ = _ := _root_.hammingDist_comm _ _
      _ ≤ 1 := hcenter
  have hfin : _root_.hammingDist (internalWord PT hPT i a.1) (groupCenter g).1 ≤ 3 := by
    calc
      _ ≤ _root_.hammingDist (internalWord PT hPT i a.1) (solverWordAt PT hPT hm b.1) +
          _root_.hammingDist (solverWordAt PT hPT hm b.1) (groupCenter g).1 :=
        _root_.hammingDist_triangle _ _ _
      _ ≤ 2 + 1 := Nat.add_le_add hsolver hcenter'
      _ ≤ 3 := by omega
  simpa [clusterMarginalConsultation, clusterSliceAt, s, S, z, g, i] using hfin

private theorem clusterStarQuery_word_dist_le_two {κ : CConsts} {T : Stage} {k : ℕ}
    (PT : ProfiledTiling κ T k) (hPT : PT.Valid)
    (hm : PT.tiling.mode = .highSmall ∨ PT.tiling.mode = .highLarge)
    (a : EvenPosition T k) (l : Fin (PT.tiling.P (patchAt PT hPT a.1)).h) :
    _root_.hammingDist (clusterCenterRole PT hPT hm a).1
      (groupCenter ((clusterSolver PT hPT hm (patchAt PT hPT a.1)).groupOf
        (flipPos (clusterCenterRole PT hPT hm a).1 l))).1 ≤ 2 := by
  classical
  let i := patchAt PT hPT a.1
  let S := clusterSolver PT hPT hm i
  let v := clusterCenterRole PT hPT hm a
  let z := flipPos v.1 l
  let g := S.groupOf z
  have hz : ¬ HypercubeRamsey.IsEvenRole z := by
    intro hz
    have hflip := HypercubeRamsey.S15.evenRole_flipPos v.1 l
    exact (hflip.mp hz) v.2
  have hgroup := S.groupOf_spec z hz
  have hcenter := clusterGroupCenter_dist_le_one_of_fiber PT i g z hgroup
  have hflip : _root_.hammingDist v.1 z = 1 := hammingDist_flipPos_one _ _
  change _root_.hammingDist v.1 (groupCenter g).1 ≤ 2
  have hcenter' : _root_.hammingDist z (groupCenter g).1 ≤ 1 := by
    rw [_root_.hammingDist_comm]
    exact hcenter
  calc
    _ ≤ _root_.hammingDist v.1 z + _root_.hammingDist z (groupCenter g).1 :=
      _root_.hammingDist_triangle _ _ _
    _ ≤ 1 + 1 := Nat.add_le_add (Nat.le_of_eq hflip) hcenter'
    _ ≤ 2 := by omega

/-- Every row consultation belongs to the row's own patch. -/
theorem clusterRowConsultation_patchAt_eq {κ : CConsts} {T : Stage} {k : ℕ}
    (PT : ProfiledTiling κ T k) (hPT : PT.Valid)
    (hm : PT.tiling.mode = .highSmall ∨ PT.tiling.mode = .highLarge)
    (a : EvenPosition T k) (c : ClusterConsultation PT)
    (hc : c ∈ clusterRowConsultations PT hPT hm a) :
    c.1.1 = patchAt PT hPT a.1 := by
  rcases Finset.mem_insert.mp hc with hcenter | hc
  · subst c
    simp [clusterCenterConsultation, clusterSliceAt]
  · rcases Finset.mem_union.mp hc with hbulk | hstar
    · rcases Finset.mem_image.mp hbulk with ⟨b, hb, rfl⟩
      have hpatch : patchAt PT hPT b.1 = patchAt PT hPT a.1 :=
        (Finset.mem_filter.mp hb).2.2.1
      simpa [clusterMarginalConsultation, clusterSliceAt] using hpatch
    · rcases Finset.mem_image.mp hstar with ⟨z, hz, rfl⟩
      simp [clusterCenterStarConsultations, clusterSliceAt]

/-- A record in a row consultation scope lies in that row's patch. -/
theorem clusterRowConsultationScope_patchAt_eq {κ : CConsts} {T : Stage} {k : ℕ}
    (PT : ProfiledTiling κ T k) (hPT : PT.Valid)
    (hm : PT.tiling.mode = .highSmall ∨ PT.tiling.mode = .highLarge)
    (a : EvenPosition T k) (r : ClusterRecordIndex PT hPT hm)
    (hr : r ∈ clusterConsultationScope PT hPT hm
      (clusterRowConsultations PT hPT hm a)) :
    r.1.1 = patchAt PT hPT a.1 := by
  rcases Finset.mem_filter.mp hr with ⟨_, c, hc, e, _⟩
  have he := congrArg (fun s : ClusterSlice PT => s.1) e
  calc
    r.1.1 = c.1.1 := he.symm
    _ = patchAt PT hPT a.1 := clusterRowConsultation_patchAt_eq PT hPT hm a c hc

/-- Distinct patches have disjoint row consultation scopes. -/
theorem clusterRowConsultationScopes_disjoint_of_patch_ne {κ : CConsts} {T : Stage} {k : ℕ}
    (PT : ProfiledTiling κ T k) (hPT : PT.Valid)
    (hm : PT.tiling.mode = .highSmall ∨ PT.tiling.mode = .highLarge)
    (a a' : EvenPosition T k)
    (hne : patchAt PT hPT a.1 ≠ patchAt PT hPT a'.1) :
    Disjoint
      (clusterConsultationScope PT hPT hm (clusterRowConsultations PT hPT hm a))
      (clusterConsultationScope PT hPT hm (clusterRowConsultations PT hPT hm a')) := by
  apply Finset.disjoint_left.mpr
  intro r hr hr'
  have hpatch := clusterRowConsultationScope_patchAt_eq PT hPT hm a r hr
  have hpatch' := clusterRowConsultationScope_patchAt_eq PT hPT hm a' r hr'
  exact hne (hpatch.symm.trans hpatch')

/-- The center's row values agree when its own consultation records agree. -/
theorem clusterSigmaAtCenter_eq_of_row_scope {κ : CConsts} {T : Stage} {k : ℕ}
    (PT : ProfiledTiling κ T k) (hPT : PT.Valid)
    (hm : PT.tiling.mode = .highSmall ∨ PT.tiling.mode = .highLarge)
    (W W' : ClusterHistory PT hPT hm) (a : EvenPosition T k)
    (Y : ClusterSliceOutcome PT (clusterSliceAt PT hPT a.1).1)
    (hWW' : ∀ r ∈ clusterConsultationScope PT hPT hm
      (clusterRowConsultations PT hPT hm a), W r = W' r)
    (x : Fin (T.S.N k)) :
    clusterSigmaAtCenter PT hPT hm W a Y x =
      clusterSigmaAtCenter PT hPT hm W' a Y x := by
  classical
  let s := clusterSliceAt PT hPT a.1
  let S := clusterSolver PT hPT hm s.1
  let v := clusterCenterRole PT hPT hm a
  let c := clusterCenterConsultation PT hPT hm a
  have hc : c ∈ clusterRowConsultations PT hPT hm a := by
    simp [c, clusterRowConsultations, clusterCenterConsultation]
  have hsubset : clusterConsultationScope PT hPT hm {c} ⊆
      clusterConsultationScope PT hPT hm (clusterRowConsultations PT hPT hm a) :=
    clusterConsultationScope_mono PT hPT hm _ _ (by
      intro c' hc'
      have hc'Eq := Finset.mem_singleton.mp hc'
      rw [hc'Eq]
      exact hc)
  have hlocal : ∀ r, (_root_.hammingDist (S.loc r) v.1 : ℝ) ≤
      10 * κ.ρ * (PT.tiling.P s.1).h →
      historyOnSlice W s r = historyOnSlice W' s r := by
    intro r hr
    let ri : ClusterRecordIndex PT hPT hm := ⟨s, r⟩
    have hmem : ri ∈ clusterConsultationScope PT hPT hm {c} := by
      simp only [clusterConsultationScope, Finset.mem_filter, Finset.mem_univ, true_and]
      refine ⟨c, by simp [c], rfl, ?_⟩
      simpa [c, clusterCenterConsultation, s, v, ri] using hr
    exact hWW' ri (hsubset hmem)
  have hσfun := S.σ_local v (historyOnSlice W s) (historyOnSlice W' s)
    (nbrLabels v.1 Y.2) hlocal
  change S.σ v (historyOnSlice W s) (nbrLabels v.1 Y.2) x =
    S.σ v (historyOnSlice W' s) (nbrLabels v.1 Y.2) x
  exact congrFun hσfun x

/-- The bulk query set contains at most one consultation for each cube neighbor. -/
theorem clusterBulkMarginalConsultations_card_le {κ : CConsts} {T : Stage} {k : ℕ}
    (PT : ProfiledTiling κ T k) (hPT : PT.Valid)
    (hm : PT.tiling.mode = .highSmall ∨ PT.tiling.mode = .highLarge)
    (a : EvenPosition T k) :
    (clusterBulkMarginalConsultations PT hPT hm a).card ≤ T.S.n k := by
  classical
  let S := clusterBulkNeighbours PT hPT a
  let N := Finset.univ.filter fun y : OAI.HypercubeRamsey.CubeVertex (T.S.n k) =>
    (OAI.HypercubeRamsey.cube _).Adj a.1 y
  have hcardImg : S.card = (S.image (fun b => b.1)).card := by
    exact (Finset.card_image_of_injective S Subtype.val_injective).symm
  have hsub : S.image (fun b => b.1) ⊆ N := by
    intro y hy
    rcases Finset.mem_image.mp hy with ⟨b, hb, rfl⟩
    have hadj := (Finset.mem_filter.mp hb).2.1
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, hadj⟩
  have hS : S.card ≤ T.S.n k := by
    calc
      S.card = (S.image (fun b => b.1)).card := hcardImg
      _ ≤ N.card := Finset.card_le_card hsub
      _ ≤ T.S.n k := HypercubeRamsey.cube_adj_neighbors_card_le _ _
  calc
    (clusterBulkMarginalConsultations PT hPT hm a).card ≤ S.card := by
      simpa [clusterBulkMarginalConsultations, S] using
        (Finset.card_image_le :
          ((clusterBulkNeighbours PT hPT a).image
            (clusterMarginalConsultation PT hPT hm)).card ≤
              (clusterBulkNeighbours PT hPT a).card)
    _ ≤ T.S.n k := hS

/-- The row consultation budget is polynomial in the cube dimension. -/
theorem clusterRowConsultations_card_le {κ : CConsts} {T : Stage} {k : ℕ}
    (PT : ProfiledTiling κ T k) (hPT : PT.Valid)
    (hm : PT.tiling.mode = .highSmall ∨ PT.tiling.mode = .highLarge)
    (a : EvenPosition T k) (hn : 2 ≤ T.S.n k) :
    (clusterRowConsultations PT hPT hm a).card ≤ (T.S.n k) ^ 5 := by
  classical
  let i := patchAt PT hPT a.1
  let B := clusterBulkMarginalConsultations PT hPT hm a
  let C := clusterCenterStarConsultations PT hPT hm a
  have hBulk := clusterBulkMarginalConsultations_card_le PT hPT hm a
  have hStarWords : (clusterCenterStarWords PT hPT hm a).card ≤ (PT.tiling.P i).h := by
    calc
      (clusterCenterStarWords PT hPT hm a).card ≤
          (Finset.univ : Finset (Fin (PT.tiling.P i).h)).card := by
            simp only [clusterCenterStarWords, i]
            exact Finset.card_image_le
      _ = (PT.tiling.P i).h := by simp
  have hStar : C.card ≤ (PT.tiling.P i).h := by
    calc
      C.card ≤ (clusterCenterStarWords PT hPT hm a).card := by
        dsimp [C, clusterCenterStarConsultations]
        exact Finset.card_image_le
      _ ≤ (PT.tiling.P i).h := hStarWords
  have hHeight : (PT.tiling.P i).h ≤ T.S.n k := by
    exact clusterHeight_le PT hPT i
  have hLinear : (clusterRowConsultations PT hPT hm a).card ≤
      1 + 2 * T.S.n k := by
    have hRow : (clusterRowConsultations PT hPT hm a).card ≤ 1 + B.card + C.card := by
      change (insert (clusterCenterConsultation PT hPT hm a) (B ∪ C)).card ≤
        1 + B.card + C.card
      calc
        _ ≤ (B ∪ C).card + 1 := Finset.card_insert_le _ _
        _ ≤ B.card + C.card + 1 := Nat.add_le_add_right (Finset.card_union_le B C) 1
        _ = 1 + B.card + C.card := by omega
    calc
      (clusterRowConsultations PT hPT hm a).card ≤ 1 + B.card + C.card := hRow
      _ ≤ 1 + T.S.n k + (PT.tiling.P i).h :=
        by
          have hsum := Nat.add_le_add hBulk hStar
          calc
            1 + B.card + C.card = 1 + (B.card + C.card) := by omega
            _ ≤ 1 + (T.S.n k + (PT.tiling.P i).h) := by
              simpa [B] using Nat.add_le_add_left hsum 1
            _ = 1 + T.S.n k + (PT.tiling.P i).h := by omega
      _ ≤ 1 + T.S.n k + T.S.n k := Nat.add_le_add_left hHeight (1 + T.S.n k)
      _ = 1 + 2 * T.S.n k := by omega
  have hnR : (2 : ℝ) ≤ (T.S.n k : ℝ) := by exact_mod_cast hn
  have hsq : (4 : ℝ) ≤ (T.S.n k : ℝ) ^ 2 := by nlinarith [sq_nonneg ((T.S.n k : ℝ) - 2)]
  have hfour : (4 : ℝ) ≤ (T.S.n k : ℝ) ^ 4 := by
    have hmul := mul_le_mul hsq hsq (by norm_num) (by positivity)
    nlinarith [hmul]
  have hfive : 4 * (T.S.n k : ℝ) ≤ (T.S.n k : ℝ) ^ 5 := by
    calc
      4 * (T.S.n k : ℝ) ≤ (T.S.n k : ℝ) ^ 4 * T.S.n k :=
        mul_le_mul_of_nonneg_right hfour (by positivity)
      _ = (T.S.n k : ℝ) ^ 5 := by ring
  have hlin : 1 + 2 * (T.S.n k : ℝ) ≤ 4 * (T.S.n k : ℝ) := by nlinarith [hnR]
  have hLinearR :
      ((clusterRowConsultations PT hPT hm a).card : ℝ) ≤
        1 + 2 * (T.S.n k : ℝ) := by exact_mod_cast hLinear
  have hfinal :
      ((clusterRowConsultations PT hPT hm a).card : ℝ) ≤ (T.S.n k : ℝ) ^ 5 :=
    hLinearR.trans (hlin.trans hfive)
  exact_mod_cast hfinal

/-- A row consultation query stays near the row in its patch's outside/internal coordinates. -/
theorem clusterRowConsultation_geometry {κ : CConsts} {T : Stage} {k : ℕ}
    (PT : ProfiledTiling κ T k) (hPT : PT.Valid)
    (hm : PT.tiling.mode = .highSmall ∨ PT.tiling.mode = .highLarge)
    (a : EvenPosition T k) (c : ClusterConsultation PT)
    (hc : c ∈ clusterRowConsultations PT hPT hm a) :
    _root_.hammingDist (outsideWord PT hPT c.1.1 a.1) c.1.2 ≤ 1 ∧
      _root_.hammingDist (internalWord PT hPT c.1.1 a.1) c.2 ≤ 4 := by
  classical
  rcases Finset.mem_insert.mp hc with hcenter | hc
  · subst c
    constructor
    · change _root_.hammingDist (outsideWord PT hPT (patchAt PT hPT a.1) a.1)
        (outsideWord PT hPT (patchAt PT hPT a.1) a.1) ≤ 1
      rw [_root_.hammingDist_self]
      omega
    · have hcenter : _root_.hammingDist (internalWord PT hPT
          (patchAt PT hPT a.1) a.1) (clusterCenterRole PT hPT hm a).1 ≤ 1 := by
        simpa [clusterWordAt, clusterCenterRole] using
          clusterSolverWordAt_dist_le_one PT hPT hm a.1
      exact hcenter.trans (by omega)
  · rcases Finset.mem_union.mp hc with hbulk | hstar
    · rcases Finset.mem_image.mp hbulk with ⟨b, hb, rfl⟩
      have hadj : Adjacent a b := (Finset.mem_filter.mp hb).2.1
      have houter := outsideWord_hammingDist_le PT hPT (patchAt PT hPT b.1) a.1 b.1
      have houter' : _root_.hammingDist
          (outsideWord PT hPT (patchAt PT hPT b.1) a.1)
          (outsideWord PT hPT (patchAt PT hPT b.1) b.1) ≤ 1 := by
        have hdist := clusterAdjacent_hammingDist_eq_one a b hadj
        have hle : _root_.hammingDist a.1 b.1 ≤ 1 := by omega
        exact houter.trans hle
      have houter'' : _root_.hammingDist
          (outsideWord PT hPT (clusterMarginalConsultation PT hPT hm b).1.1 a.1)
          (clusterMarginalConsultation PT hPT hm b).1.2 ≤ 1 := by
        change _root_.hammingDist
          (outsideWord PT hPT (patchAt PT hPT b.1) a.1)
          (outsideWord PT hPT (patchAt PT hPT b.1) b.1) ≤ 1
        exact houter'
      have hinner : _root_.hammingDist
          (internalWord PT hPT (clusterMarginalConsultation PT hPT hm b).1.1 a.1)
          (clusterMarginalConsultation PT hPT hm b).2 ≤ 4 := by
        change _root_.hammingDist
          (internalWord PT hPT (patchAt PT hPT b.1) a.1)
          (groupCenter ((clusterSolver PT hPT hm (patchAt PT hPT b.1)).groupOf
            (solverWordAt PT hPT hm b.1))).1 ≤ 4
        have h := clusterMarginalQuery_word_dist_le_three PT hPT hm a b hadj
        exact h.trans (by omega)
      exact ⟨houter'', hinner⟩
    · rcases Finset.mem_image.mp hstar with ⟨z, hz, rfl⟩
      rcases Finset.mem_image.mp hz with ⟨l, -, rfl⟩
      let i := patchAt PT hPT a.1
      have houter : _root_.hammingDist
          (outsideWord PT hPT i a.1) (outsideWord PT hPT i a.1) ≤ 1 := by
        rw [_root_.hammingDist_self]
        omega
      have hcenterRaw : _root_.hammingDist
          (internalWord PT hPT i a.1) (clusterCenterRole PT hPT hm a).1 ≤ 1 := by
        simpa [i, clusterWordAt, clusterCenterRole] using
          clusterSolverWordAt_dist_le_one PT hPT hm a.1
      have hstar' := clusterStarQuery_word_dist_le_two PT hPT hm a l
      have hinner : _root_.hammingDist (internalWord PT hPT i a.1)
          (groupCenter ((clusterSolver PT hPT hm i).groupOf
            (flipPos (clusterCenterRole PT hPT hm a).1 l))).1 ≤ 3 := by
        calc
          _ ≤ _root_.hammingDist (internalWord PT hPT i a.1)
              (clusterCenterRole PT hPT hm a).1 +
              _root_.hammingDist (clusterCenterRole PT hPT hm a).1
                (groupCenter ((clusterSolver PT hPT hm i).groupOf
                  (flipPos (clusterCenterRole PT hPT hm a).1 l))).1 :=
            _root_.hammingDist_triangle _ _ _
          _ ≤ 1 + 2 := Nat.add_le_add hcenterRaw hstar'
          _ ≤ 3 := by omega
      constructor
      · change _root_.hammingDist (outsideWord PT hPT i a.1)
          (outsideWord PT hPT i a.1) ≤ 1
        exact houter
      · change _root_.hammingDist (internalWord PT hPT i a.1)
          (groupCenter ((clusterSolver PT hPT hm i).groupOf
            (flipPos (clusterCenterRole PT hPT hm a).1 l))).1 ≤ 4
        exact hinner.trans (by omega)

private theorem clusterConsultation_words_dist_of_shared_record {κ : CConsts} {T : Stage} {k : ℕ}
    (PT : ProfiledTiling κ T k) (hPT : PT.Valid)
    (hm : PT.tiling.mode = .highSmall ∨ PT.tiling.mode = .highLarge)
    (r : ClusterRecordIndex PT hPT hm) (c c' : ClusterConsultation PT)
    (e : c.1 = r.1) (e' : c'.1 = r.1)
    (hc : (_root_.hammingDist
      ((clusterSolver PT hPT hm r.1.1).loc r.2) (e ▸ c.2) : ℝ) ≤
        10 * κ.ρ * (PT.tiling.P r.1.1).h)
    (hc' : (_root_.hammingDist
      ((clusterSolver PT hPT hm r.1.1).loc r.2) (e' ▸ c'.2) : ℝ) ≤
        10 * κ.ρ * (PT.tiling.P r.1.1).h) :
    (_root_.hammingDist (e ▸ c.2) (e' ▸ c'.2) : ℝ) ≤
      20 * κ.ρ * (PT.tiling.P r.1.1).h := by
  classical
  rcases c with ⟨s, z⟩
  rcases c' with ⟨s', z'⟩
  rcases r with ⟨rs, rr⟩
  change s = rs at e
  change s' = rs at e'
  cases e
  cases e'
  let S := clusterSolver PT hPT hm s.1
  have htri := _root_.hammingDist_triangle z (S.loc rr) z'
  have htriR : (_root_.hammingDist z z' : ℝ) ≤
      (_root_.hammingDist z (S.loc rr) : ℝ) +
        (_root_.hammingDist (S.loc rr) z' : ℝ) := by exact_mod_cast htri
  have hc1 : (_root_.hammingDist z (S.loc rr) : ℝ) ≤
      10 * κ.ρ * (PT.tiling.P s.1).h := by
    have hsymm : _root_.hammingDist z (S.loc rr) =
        _root_.hammingDist (S.loc rr) z := _root_.hammingDist_comm _ _
    rw [hsymm]
    simpa [S] using hc
  have hc2 : (_root_.hammingDist (S.loc rr) z' : ℝ) ≤
      10 * κ.ρ * (PT.tiling.P s.1).h := by simpa [S] using hc'
  change (_root_.hammingDist z z' : ℝ) ≤ 20 * κ.ρ * (PT.tiling.P s.1).h
  calc
    _ ≤ (_root_.hammingDist z (S.loc rr) : ℝ) +
        (_root_.hammingDist (S.loc rr) z' : ℝ) := htriR
    _ ≤ 10 * κ.ρ * (PT.tiling.P s.1).h + 10 * κ.ρ * (PT.tiling.P s.1).h :=
      add_le_add hc1 hc2
    _ = 20 * κ.ρ * (PT.tiling.P s.1).h := by ring

/-- A shared consultation record puts the two row centers in one nearby patch region. -/
theorem clusterRowConsultationScopes_intersection_geometry {κ : CConsts} {T : Stage} {k : ℕ}
    (PT : ProfiledTiling κ T k) (hPT : PT.Valid)
    (hm : PT.tiling.mode = .highSmall ∨ PT.tiling.mode = .highLarge)
    (a a' : EvenPosition T k) (r : ClusterRecordIndex PT hPT hm)
    (hr : r ∈ clusterConsultationScope PT hPT hm (clusterRowConsultations PT hPT hm a))
    (hr' : r ∈ clusterConsultationScope PT hPT hm (clusterRowConsultations PT hPT hm a')) :
    ∃ i : Fin PT.tiling.m, patchAt PT hPT a.1 = i ∧ patchAt PT hPT a'.1 = i ∧
      _root_.hammingDist (outsideWord PT hPT i a.1) (outsideWord PT hPT i a'.1) ≤ 2 ∧
      (_root_.hammingDist (internalWord PT hPT i a.1) (internalWord PT hPT i a'.1) : ℝ) ≤
        20 * κ.ρ * (PT.tiling.P i).h + 8 := by
  classical
  rcases Finset.mem_filter.mp hr with ⟨_, c, hc, e, hloc⟩
  rcases Finset.mem_filter.mp hr' with ⟨_, c', hc', e', hloc'⟩
  have hquery := clusterConsultation_words_dist_of_shared_record
    PT hPT hm r c c' e e' hloc hloc'
  rcases c with ⟨s, z⟩
  rcases c' with ⟨s', z'⟩
  rcases r with ⟨rs, rr⟩
  change s = rs at e
  change s' = rs at e'
  cases e
  cases e'
  let i := s.1
  have hpatchA : s.1 = patchAt PT hPT a.1 :=
    clusterRowConsultation_patchAt_eq PT hPT hm a ⟨s, z⟩ hc
  have hpatchB : s.1 = patchAt PT hPT a'.1 :=
    clusterRowConsultation_patchAt_eq PT hPT hm a' ⟨s, z'⟩ hc'
  have hgeomA := clusterRowConsultation_geometry PT hPT hm a ⟨s, z⟩ hc
  have hgeomB := clusterRowConsultation_geometry PT hPT hm a' ⟨s, z'⟩ hc'
  have haOuter : _root_.hammingDist (outsideWord PT hPT i a.1) s.2 ≤ 1 := by
    simpa [i] using hgeomA.1
  have hbOuter : _root_.hammingDist (outsideWord PT hPT i a'.1) s.2 ≤ 1 := by
    simpa [i] using hgeomB.1
  have houter : _root_.hammingDist (outsideWord PT hPT i a.1)
      (outsideWord PT hPT i a'.1) ≤ 2 := by
    have hbOuter' : _root_.hammingDist s.2 (outsideWord PT hPT i a'.1) ≤ 1 := by
      calc
        _ = _ := _root_.hammingDist_comm _ _
        _ ≤ 1 := hbOuter
    calc
      _ ≤ _root_.hammingDist (outsideWord PT hPT i a.1) s.2 +
          _root_.hammingDist s.2 (outsideWord PT hPT i a'.1) :=
        _root_.hammingDist_triangle _ _ _
      _ ≤ 1 + 1 := Nat.add_le_add haOuter hbOuter'
      _ ≤ 2 := by omega
  have haInner : _root_.hammingDist (internalWord PT hPT i a.1) z ≤ 4 := by
    simpa [i] using hgeomA.2
  have hbInner : _root_.hammingDist (internalWord PT hPT i a'.1) z' ≤ 4 := by
    simpa [i] using hgeomB.2
  have hqueryR : (_root_.hammingDist z z' : ℝ) ≤ 20 * κ.ρ * (PT.tiling.P i).h := by
    simpa [i] using hquery
  have hinnerNat : _root_.hammingDist (internalWord PT hPT i a.1)
      (internalWord PT hPT i a'.1) ≤
        _root_.hammingDist (internalWord PT hPT i a.1) z +
          _root_.hammingDist z z' + _root_.hammingDist z' (internalWord PT hPT i a'.1) := by
    have ht₁ := _root_.hammingDist_triangle
      (internalWord PT hPT i a.1) z (internalWord PT hPT i a'.1)
    have ht₂ := _root_.hammingDist_triangle z z' (internalWord PT hPT i a'.1)
    calc
      _ ≤ _root_.hammingDist (internalWord PT hPT i a.1) z +
          _root_.hammingDist z (internalWord PT hPT i a'.1) := ht₁
      _ ≤ _root_.hammingDist (internalWord PT hPT i a.1) z +
          (_root_.hammingDist z z' + _root_.hammingDist z' (internalWord PT hPT i a'.1)) :=
        Nat.add_le_add_left ht₂ _
      _ = _ := by omega
  have hbInner' : _root_.hammingDist z' (internalWord PT hPT i a'.1) ≤ 4 := by
    calc
      _ = _ := _root_.hammingDist_comm _ _
      _ ≤ 4 := hbInner
  have haInnerR : (_root_.hammingDist (internalWord PT hPT i a.1) z : ℝ) ≤ 4 := by
    exact_mod_cast haInner
  have hbInnerR : (_root_.hammingDist z' (internalWord PT hPT i a'.1) : ℝ) ≤ 4 := by
    exact_mod_cast hbInner'
  have hinnerR : (_root_.hammingDist
      (internalWord PT hPT i a.1) (internalWord PT hPT i a'.1) : ℝ) ≤
        20 * κ.ρ * (PT.tiling.P i).h + 8 := by
    calc
      _ ≤ (_root_.hammingDist (internalWord PT hPT i a.1) z : ℝ) +
          (_root_.hammingDist z z' : ℝ) +
          (_root_.hammingDist z' (internalWord PT hPT i a'.1) : ℝ) := by
        exact_mod_cast hinnerNat
      _ ≤ 4 + 20 * κ.ρ * (PT.tiling.P i).h + 4 := by
        nlinarith [haInnerR, hqueryR, hbInnerR]
      _ = 20 * κ.ρ * (PT.tiling.P i).h + 8 := by ring
  exact ⟨i, hpatchA.symm, hpatchB.symm, houter, hinnerR⟩

/-- A row whose scope meets one consultation site has its projected center near that site. -/
theorem clusterConsultation_rowScope_intersection_geometry {κ : CConsts} {T : Stage} {k : ℕ}
    (PT : ProfiledTiling κ T k) (hPT : PT.Valid)
    (hm : PT.tiling.mode = .highSmall ∨ PT.tiling.mode = .highLarge)
    (a : EvenPosition T k) (c : ClusterConsultation PT)
    (r : ClusterRecordIndex PT hPT hm)
    (hc : r ∈ clusterConsultationScope PT hPT hm {c})
    (ha : r ∈ clusterConsultationScope PT hPT hm
      (clusterRowConsultations PT hPT hm a)) :
    c.1.1 = patchAt PT hPT a.1 ∧
      _root_.hammingDist (outsideWord PT hPT c.1.1 a.1) c.1.2 ≤ 1 ∧
      (_root_.hammingDist (internalWord PT hPT c.1.1 a.1) c.2 : ℝ) ≤
        20 * κ.ρ * (PT.tiling.P c.1.1).h + 4 := by
  classical
  rcases Finset.mem_filter.mp hc with ⟨_, d, hd, e, hloc⟩
  have hdEq : d = c := Finset.mem_singleton.mp hd
  subst d
  rcases Finset.mem_filter.mp ha with ⟨_, c', hc', e', hloc'⟩
  have hquery := clusterConsultation_words_dist_of_shared_record
    PT hPT hm r c c' e e' hloc hloc'
  rcases c with ⟨s, z⟩
  rcases c' with ⟨s', z'⟩
  rcases r with ⟨rs, rr⟩
  change s = rs at e
  change s' = rs at e'
  cases e
  cases e'
  have hpatch : s.1 = patchAt PT hPT a.1 :=
    clusterRowConsultation_patchAt_eq PT hPT hm a ⟨s, z'⟩ hc'
  have hgeom := clusterRowConsultation_geometry PT hPT hm a ⟨s, z'⟩ hc'
  have hqueryR : (_root_.hammingDist z z' : ℝ) ≤ 20 * κ.ρ * (PT.tiling.P s.1).h := by
    simpa using hquery
  have hquerySymm : (_root_.hammingDist z' z : ℝ) ≤ 20 * κ.ρ * (PT.tiling.P s.1).h := by
    calc
      _ = (_root_.hammingDist z z' : ℝ) := by
        congr 1
        exact _root_.hammingDist_comm _ _
      _ ≤ 20 * κ.ρ * (PT.tiling.P s.1).h := hqueryR
  have hcenter : _root_.hammingDist (internalWord PT hPT s.1 a.1) z' ≤ 4 :=
    hgeom.2
  have hcenterR : (_root_.hammingDist (internalWord PT hPT s.1 a.1) z' : ℝ) ≤ 4 := by
    exact_mod_cast hcenter
  have hinnerNat : _root_.hammingDist (internalWord PT hPT s.1 a.1) z ≤
      _root_.hammingDist (internalWord PT hPT s.1 a.1) z' + _root_.hammingDist z' z :=
    _root_.hammingDist_triangle _ _ _
  have hinner : (_root_.hammingDist (internalWord PT hPT s.1 a.1) z : ℝ) ≤
      20 * κ.ρ * (PT.tiling.P s.1).h + 4 := by
    calc
      _ ≤ (_root_.hammingDist (internalWord PT hPT s.1 a.1) z' : ℝ) +
          (_root_.hammingDist z' z : ℝ) := by exact_mod_cast hinnerNat
      _ ≤ 4 + 20 * κ.ρ * (PT.tiling.P s.1).h := add_le_add hcenterR hquerySymm
      _ = 20 * κ.ρ * (PT.tiling.P s.1).h + 4 := by ring
  refine ⟨?_, hgeom.1, hinner⟩
  exact hpatch

private def clusterJoin {n h : ℕ} (hh : h ≤ n)
    (outside : OAI.HypercubeRamsey.CubeVertex (n - h))
    (inside : OAI.HypercubeRamsey.CubeVertex h) : OAI.HypercubeRamsey.CubeVertex n :=
  fun j => if hj : j.val < n - h then outside ⟨j.val, hj⟩ else
    inside ⟨j.val - (n - h), by have := j.isLt; omega⟩

private theorem clusterJoin_outside_internal {κ : CConsts} {T : Stage} {k : ℕ}
    (PT : ProfiledTiling κ T k) (hPT : PT.Valid) (i : Fin PT.tiling.m)
    (v : Position T k) :
    clusterJoin (clusterHeight_le PT hPT i)
      (outsideWord PT hPT i v) (internalWord PT hPT i v) = v := by
  classical
  funext j
  by_cases hj : j.val < T.S.n k - (PT.tiling.P i).h
  · simp [clusterJoin, hj, outsideWord]
  · simp only [clusterJoin, dif_neg hj, internalWord, Fin.val_mk]
    have hidx :
        (⟨T.S.n k - (PT.tiling.P i).h +
          (j.val - (T.S.n k - (PT.tiling.P i).h)), by
            have hh := clusterHeight_le PT hPT i
            have hj' := j.isLt
            omega⟩ : Fin (T.S.n k)) = j := by
      apply Fin.ext
      simp only [Fin.val_mk]
      have hh := clusterHeight_le PT hPT i
      have hj' := j.isLt
      omega
    simpa using congrArg v hidx

private theorem clusterPositionCoordinates_injective {κ : CConsts} {T : Stage} {k : ℕ}
    (PT : ProfiledTiling κ T k) (hPT : PT.Valid) (i : Fin PT.tiling.m) :
    Function.Injective (fun a : EvenPosition T k =>
      (outsideWord PT hPT i a.1, internalWord PT hPT i a.1)) := by
  intro a b hab
  apply Subtype.ext
  have houtside := congrArg Prod.fst hab
  have hinside := congrArg Prod.snd hab
  change outsideWord PT hPT i a.1 = outsideWord PT hPT i b.1 at houtside
  change internalWord PT hPT i a.1 = internalWord PT hPT i b.1 at hinside
  calc
    a.1 = clusterJoin (clusterHeight_le PT hPT i)
        (outsideWord PT hPT i a.1) (internalWord PT hPT i a.1) :=
      (clusterJoin_outside_internal PT hPT i a.1).symm
    _ = clusterJoin (clusterHeight_le PT hPT i)
        (outsideWord PT hPT i b.1) (internalWord PT hPT i b.1) := by rw [houtside, hinside]
    _ = b.1 := clusterJoin_outside_internal PT hPT i b.1

private theorem clusterLocalHammingDist_eq {n : ℕ}
    (u v : OAI.HypercubeRamsey.CubeVertex n) :
    HypercubeRamsey.hammingDist u v = _root_.hammingDist u v := rfl

private theorem clusterHammingBall_two_card_le {n : ℕ}
    (v : OAI.HypercubeRamsey.CubeVertex n) :
    (HypercubeRamsey.hammingBall v 2).card ≤ (n + 1) ^ 2 := by
  classical
  let support : OAI.HypercubeRamsey.CubeVertex n → Finset (Fin n) := fun u =>
    Finset.univ.filter (fun j => u j ≠ v j)
  let B := HypercubeRamsey.hammingBall v 2
  let Q := (Finset.univ : Finset (Finset (Fin n))).filter (fun s => s.card ≤ 2)
  let P0 := (Finset.univ : Finset (Fin n)).powersetCard 0
  let P1 := (Finset.univ : Finset (Fin n)).powersetCard 1
  let P2 := (Finset.univ : Finset (Fin n)).powersetCard 2
  have hsupportDist (u : OAI.HypercubeRamsey.CubeVertex n) :
      (support u).card = _root_.hammingDist v u := by
    simp [support, _root_.hammingDist, ne_comm]
  have hinj : Set.InjOn support (B : Set (OAI.HypercubeRamsey.CubeVertex n)) := by
    intro x hx y hy hxy
    funext j
    have hiff : x j ≠ v j ↔ y j ≠ v j := by
      have h := congrArg (fun s : Finset (Fin n) => j ∈ s) hxy
      simpa [support] using h
    cases hv : v j <;> cases hxj : x j <;> cases hyj : y j <;> simp_all
  have hsupport_subset : B.image support ⊆ Q := by
    intro s hs
    rcases Finset.mem_image.mp hs with ⟨u, hu, rfl⟩
    apply Finset.mem_filter.mpr
    refine ⟨Finset.mem_univ _, ?_⟩
    have hball : u ∈ HypercubeRamsey.hammingBall v 2 := by simpa [B] using hu
    rw [hsupportDist]
    exact (Finset.mem_filter.mp hball).2
  have hball : B.card ≤ Q.card := by
    calc
      B.card = (B.image support).card := (Finset.card_image_of_injOn hinj).symm
      _ ≤ Q.card := Finset.card_le_card hsupport_subset
  have hQsubset : Q ⊆ P0 ∪ (P1 ∪ P2) := by
    intro s hs
    have hsCard : s.card ≤ 2 := (Finset.mem_filter.mp hs).2
    have hsU : s ⊆ (Finset.univ : Finset (Fin n)) := Finset.subset_univ _
    have hc : s.card = 0 ∨ s.card = 1 ∨ s.card = 2 := by omega
    rcases hc with h0 | h1 | h2
    · have h0empty : s = ∅ := Finset.card_eq_zero.mp h0
      simp [P0, P1, P2, h0empty]
    · simp [P0, P1, P2, Finset.mem_powersetCard, hsU, h1]
    · simp [P0, P1, P2, Finset.mem_powersetCard, hsU, h2]
  have hP : (P0 ∪ (P1 ∪ P2)).card ≤ 1 + n + Nat.choose n 2 := by
    calc
      (P0 ∪ (P1 ∪ P2)).card ≤ P0.card + (P1 ∪ P2).card := Finset.card_union_le _ _
      _ ≤ P0.card + (P1.card + P2.card) := Nat.add_le_add_left (Finset.card_union_le _ _) _
      _ = 1 + n + Nat.choose n 2 := by
        simp [P0, P1, P2, Finset.card_powersetCard]
        omega
  have hchoose : Nat.choose n 2 ≤ n ^ 2 := Nat.choose_le_pow n 2
  have htotal : 1 + n + Nat.choose n 2 ≤ (n + 1) ^ 2 := by nlinarith
  exact hball.trans ((Finset.card_le_card hQsubset).trans (hP.trans htotal))

theorem clusterConsultation_touchingRows_count_le_ball_product {κ : CConsts} {T : Stage} {k : ℕ}
    (PT : ProfiledTiling κ T k) (hPT : PT.Valid)
    (hm : PT.tiling.mode = .highSmall ∨ PT.tiling.mode = .highLarge)
    (c : ClusterConsultation PT)
    (hRadius : 8 ≤ 10 * κ.ρ * (PT.tiling.P c.1.1).h) :
    (Finset.univ.filter fun a : EvenPosition T k =>
      ∃ r : ClusterRecordIndex PT hPT hm,
        r ∈ clusterConsultationScope PT hPT hm {c} ∧
        r ∈ clusterConsultationScope PT hPT hm (clusterRowConsultations PT hPT hm a)).card ≤
      (HypercubeRamsey.hammingBall c.1.2.1 2).card *
        (HypercubeRamsey.hammingBall (c.2)
          ⌊30 * κ.ρ * ((PT.tiling.P c.1.1).h : ℝ)⌋₊).card := by
  classical
  let i := c.1.1
  let h := (PT.tiling.P i).h
  let rball := ⌊30 * κ.ρ * (h : ℝ)⌋₊
  let rows := Finset.univ.filter fun a : EvenPosition T k =>
    ∃ r : ClusterRecordIndex PT hPT hm,
      r ∈ clusterConsultationScope PT hPT hm {c} ∧
      r ∈ clusterConsultationScope PT hPT hm (clusterRowConsultations PT hPT hm a)
  let outerBall := HypercubeRamsey.hammingBall c.1.2.1 2
  let innerBall := HypercubeRamsey.hammingBall c.2 rball
  let coords : EvenPosition T k → OAI.HypercubeRamsey.CubeVertex (T.S.n k - h) ×
      OAI.HypercubeRamsey.CubeVertex h := fun a =>
        (outsideWord PT hPT i a.1, internalWord PT hPT i a.1)
  have hsubset : rows.image coords ⊆ outerBall.product innerBall := by
    intro p hp
    rcases Finset.mem_image.mp hp with ⟨a, ha, rfl⟩
    rcases Finset.mem_filter.mp ha with ⟨_, ⟨r, hr, hr'⟩⟩
    obtain ⟨hpatch, houter, hinner⟩ :=
      clusterConsultation_rowScope_intersection_geometry PT hPT hm a c r hr hr'
    have hinnerReal : (_root_.hammingDist (internalWord PT hPT i a.1) c.2 : ℝ) ≤
        30 * κ.ρ * (h : ℝ) := by nlinarith [hinner, hRadius]
    have hinnerNat : _root_.hammingDist (c.2) (internalWord PT hPT i a.1) ≤ rball := by
      have hcast : (_root_.hammingDist (c.2) (internalWord PT hPT i a.1) : ℝ) ≤
          30 * κ.ρ * (h : ℝ) := by
        calc
          _ = (_root_.hammingDist (internalWord PT hPT i a.1) c.2 : ℝ) := by
            congr 1
            exact _root_.hammingDist_comm _ _
          _ ≤ 30 * κ.ρ * (h : ℝ) := hinnerReal
      rw [show rball = ⌊30 * κ.ρ * (h : ℝ)⌋₊ from rfl]
      exact Nat.le_floor hcast
    have houter' : _root_.hammingDist c.1.2.1
        (outsideWord PT hPT i a.1) ≤ 1 := by
      calc
        _ = _ := _root_.hammingDist_comm _ _
        _ ≤ 1 := by simpa [i] using houter
    have houterMem : outsideWord PT hPT i a.1 ∈ outerBall := by
      change outsideWord PT hPT i a.1 ∈ HypercubeRamsey.hammingBall c.1.2.1 2
      simp only [HypercubeRamsey.hammingBall, Finset.mem_filter, Finset.mem_univ, true_and]
      rw [clusterLocalHammingDist_eq]
      omega
    have hinnerMem : internalWord PT hPT i a.1 ∈ innerBall := by
      change internalWord PT hPT i a.1 ∈ HypercubeRamsey.hammingBall c.2 rball
      simp only [HypercubeRamsey.hammingBall, Finset.mem_filter, Finset.mem_univ, true_and]
      rw [clusterLocalHammingDist_eq]
      exact hinnerNat
    exact Finset.mem_product.mpr ⟨houterMem, hinnerMem⟩
  have hinj : Function.Injective coords := clusterPositionCoordinates_injective PT hPT i
  calc
    rows.card = (rows.image coords).card :=
      (Finset.card_image_of_injective rows hinj).symm
    _ ≤ (outerBall.product innerBall).card := Finset.card_le_card hsubset
    _ = outerBall.card * innerBall.card := Finset.card_product _ _

theorem clusterConsultations_touchingRows_count_le_sum {κ : CConsts} {T : Stage} {k : ℕ}
    (PT : ProfiledTiling κ T k) (hPT : PT.Valid)
    (hm : PT.tiling.mode = .highSmall ∨ PT.tiling.mode = .highLarge)
    (U : Finset (ClusterConsultation PT))
    (hRadius : ∀ c ∈ U, 8 ≤ 10 * κ.ρ * (PT.tiling.P c.1.1).h) :
    (Finset.univ.filter fun a : EvenPosition T k =>
      ∃ r : ClusterRecordIndex PT hPT hm,
        r ∈ clusterConsultationScope PT hPT hm U ∧
        r ∈ clusterConsultationScope PT hPT hm (clusterRowConsultations PT hPT hm a)).card ≤
      ∑ c ∈ U,
        (HypercubeRamsey.hammingBall (c.1.2.1) 2).card *
          (HypercubeRamsey.hammingBall c.2
            ⌊30 * κ.ρ * ((PT.tiling.P c.1.1).h : ℝ)⌋₊).card := by
  classical
  let rowsTouching (c : ClusterConsultation PT) :=
    Finset.univ.filter fun a : EvenPosition T k =>
      ∃ r : ClusterRecordIndex PT hPT hm,
        r ∈ clusterConsultationScope PT hPT hm {c} ∧
        r ∈ clusterConsultationScope PT hPT hm (clusterRowConsultations PT hPT hm a)
  let touched := Finset.univ.filter fun a : EvenPosition T k =>
    ∃ r : ClusterRecordIndex PT hPT hm,
      r ∈ clusterConsultationScope PT hPT hm U ∧
      r ∈ clusterConsultationScope PT hPT hm (clusterRowConsultations PT hPT hm a)
  have hsubset : touched ⊆ U.biUnion rowsTouching := by
    intro a ha
    rcases Finset.mem_filter.mp ha with ⟨_, ⟨r, hrU, hrA⟩⟩
    rcases Finset.mem_filter.mp hrU with ⟨_, c, hcU, e, hloc⟩
    have hsingle : r ∈ clusterConsultationScope PT hPT hm {c} := by
      simp only [clusterConsultationScope, Finset.mem_filter, Finset.mem_univ, true_and]
      exact ⟨c, Finset.mem_singleton_self _, e, hloc⟩
    apply Finset.mem_biUnion.mpr
    exact ⟨c, hcU, Finset.mem_filter.mpr ⟨Finset.mem_univ _, r, hsingle, hrA⟩⟩
  have hcards : ∀ c ∈ U,
      (rowsTouching c).card ≤
        (HypercubeRamsey.hammingBall (c.1.2.1) 2).card *
          (HypercubeRamsey.hammingBall c.2
            ⌊30 * κ.ρ * ((PT.tiling.P c.1.1).h : ℝ)⌋₊).card := by
    intro c hc
    exact clusterConsultation_touchingRows_count_le_ball_product PT hPT hm c (hRadius c hc)
  calc
    touched.card ≤ (U.biUnion rowsTouching).card := Finset.card_le_card hsubset
    _ ≤ ∑ c ∈ U, (rowsTouching c).card := Finset.card_biUnion_le
    _ ≤ ∑ c ∈ U,
          (HypercubeRamsey.hammingBall (c.1.2.1) 2).card *
            (HypercubeRamsey.hammingBall c.2
              ⌊30 * κ.ρ * ((PT.tiling.P c.1.1).h : ℝ)⌋₊).card := by
        apply Finset.sum_le_sum
        intro c hc
        exact hcards c hc
    _ = _ := rfl 

theorem clusterRowScopes_overlap_count_le_ball_product {κ : CConsts} {T : Stage} {k : ℕ}
    (PT : ProfiledTiling κ T k) (hPT : PT.Valid)
    (hm : PT.tiling.mode = .highSmall ∨ PT.tiling.mode = .highLarge)
    (a : EvenPosition T k) (rball : ℕ)
    (hRadius : 8 ≤ 10 * κ.ρ * (PT.tiling.P (patchAt PT hPT a.1)).h)
    (hradius : rball = ⌊30 * κ.ρ * (PT.tiling.P (patchAt PT hPT a.1)).h⌋₊) :
    (Finset.univ.filter fun a' : EvenPosition T k =>
      ∃ r : ClusterRecordIndex PT hPT hm,
        r ∈ clusterConsultationScope PT hPT hm (clusterRowConsultations PT hPT hm a) ∧
        r ∈ clusterConsultationScope PT hPT hm (clusterRowConsultations PT hPT hm a')).card ≤
      (HypercubeRamsey.hammingBall
        (outsideWord PT hPT (patchAt PT hPT a.1) a.1) 2).card *
      (HypercubeRamsey.hammingBall
        (internalWord PT hPT (patchAt PT hPT a.1) a.1) rball).card := by
  classical
  let i := patchAt PT hPT a.1
  let rows := Finset.univ.filter fun a' : EvenPosition T k =>
    ∃ r : ClusterRecordIndex PT hPT hm,
      r ∈ clusterConsultationScope PT hPT hm (clusterRowConsultations PT hPT hm a) ∧
      r ∈ clusterConsultationScope PT hPT hm (clusterRowConsultations PT hPT hm a')
  let outerBall := HypercubeRamsey.hammingBall (outsideWord PT hPT i a.1) 2
  let innerBall := HypercubeRamsey.hammingBall (internalWord PT hPT i a.1) rball
  let coords : EvenPosition T k → OAI.HypercubeRamsey.CubeVertex (T.S.n k - (PT.tiling.P i).h) ×
      OAI.HypercubeRamsey.CubeVertex (PT.tiling.P i).h := fun a' =>
        (outsideWord PT hPT i a'.1, internalWord PT hPT i a'.1)
  have hsubset : rows.image coords ⊆ outerBall.product innerBall := by
    intro p hp
    rcases Finset.mem_image.mp hp with ⟨a', ha', rfl⟩
    rcases Finset.mem_filter.mp ha' with ⟨_, ⟨r, hr, hr'⟩⟩
    obtain ⟨j, hja, hja', hout, hinner⟩ :=
      clusterRowConsultationScopes_intersection_geometry PT hPT hm a a' r hr hr'
    cases hja
    have hinnerReal : (_root_.hammingDist
        (internalWord PT hPT i a.1) (internalWord PT hPT i a'.1) : ℝ) ≤
          30 * κ.ρ * (PT.tiling.P i).h := by nlinarith [hinner, hRadius]
    have hinnerNat : _root_.hammingDist
        (internalWord PT hPT i a.1) (internalWord PT hPT i a'.1) ≤ rball := by
      rw [hradius]
      exact Nat.le_floor hinnerReal
    have houterMem : outsideWord PT hPT i a'.1 ∈ outerBall := by
      change outsideWord PT hPT i a'.1 ∈
        HypercubeRamsey.hammingBall (outsideWord PT hPT i a.1) 2
      simp only [HypercubeRamsey.hammingBall, Finset.mem_filter, Finset.mem_univ, true_and]
      change HypercubeRamsey.hammingDist
        (outsideWord PT hPT i a.1) (outsideWord PT hPT i a'.1) ≤ 2
      rw [clusterLocalHammingDist_eq]
      exact hout
    have hinnerMem : internalWord PT hPT i a'.1 ∈ innerBall := by
      change internalWord PT hPT i a'.1 ∈
        HypercubeRamsey.hammingBall (internalWord PT hPT i a.1) rball
      simp only [HypercubeRamsey.hammingBall, Finset.mem_filter, Finset.mem_univ, true_and]
      change HypercubeRamsey.hammingDist
        (internalWord PT hPT i a.1) (internalWord PT hPT i a'.1) ≤ rball
      rw [clusterLocalHammingDist_eq]
      exact hinnerNat
    exact Finset.mem_product.mpr ⟨houterMem, hinnerMem⟩
  have hinj : Function.Injective coords := clusterPositionCoordinates_injective PT hPT i
  calc
    rows.card = (rows.image coords).card :=
      (Finset.card_image_of_injective rows hinj).symm
    _ ≤ (outerBall.product innerBall).card := Finset.card_le_card hsubset
    _ = outerBall.card * innerBall.card := Finset.card_product _ _

private theorem clusterInnerHammingBall_volume_bound (κ : CConsts) (hκ : κ.Admissible)
    (h : ℕ) (hh : 0 < h) (v : OAI.HypercubeRamsey.CubeVertex h) :
    (HypercubeRamsey.hammingBall v ⌊30 * κ.ρ * (h : ℝ)⌋₊).card ≤
      Real.exp ((κ.a / 10 ^ 9) * h) := by
  classical
  rcases hκ.ρ_rng with ⟨hρ, hρlt, hEntropy⟩
  let r := ⌊30 * κ.ρ * (h : ℝ)⌋₊
  have hfloor : (r : ℝ) ≤ 30 * κ.ρ * h := by
    simpa [r] using Nat.floor_le (show 0 ≤ 30 * κ.ρ * (h : ℝ) by positivity)
  have hratio : (r : ℝ) / h ≤ 30 * κ.ρ := by
    apply (div_le_iff₀ (by exact_mod_cast hh)).2
    nlinarith [hfloor]
  have h30 : 30 * κ.ρ < (2 : ℝ)⁻¹ := by nlinarith [hρlt]
  have h1000 : 1000 * κ.ρ < (2 : ℝ)⁻¹ := by nlinarith [hρlt]
  have hr : r ≤ h / 2 := by
    have htwo : (2 * r : ℝ) ≤ h := by
      nlinarith [hfloor, hρlt, show (0 : ℝ) < (h : ℝ) by exact_mod_cast hh]
    have htwoNat : 2 * r ≤ h := by exact_mod_cast htwo
    omega
  have hvolume := HypercubeRamsey.hammingBall_volume_bound (by omega) hr v
  have hrange : (r : ℝ) / h ∈ Set.Icc 0 (2 : ℝ)⁻¹ := by
    refine ⟨?_, ?_⟩
    · positivity
    · exact hratio.trans h30.le
  have hbigRange : 1000 * κ.ρ ∈ Set.Icc 0 (2 : ℝ)⁻¹ := by
    exact ⟨by positivity, h1000.le⟩
  have hmono : Real.binEntropy ((r : ℝ) / h) ≤ Real.binEntropy (1000 * κ.ρ) :=
    Real.binEntropy_strictMonoOn.monotoneOn hrange hbigRange (by nlinarith [hratio])
  have harg0 : 0 < 1000 * κ.ρ := by positivity
  have harg1 : 1000 * κ.ρ < 1 := by nlinarith [hρlt]
  have hcustom : HypercubeRamsey.binEntropy (1000 * κ.ρ) = Real.binEntropy (1000 * κ.ρ) := by
    simp only [HypercubeRamsey.binEntropy, if_neg harg0.ne', if_neg (ne_of_lt harg1)]
    unfold Real.binEntropy
    rw [Real.log_inv, Real.log_inv]
    ring
  have hEntReal : Real.binEntropy (1000 * κ.ρ) < κ.a / 10 ^ 9 := by
    rw [← hcustom]
    exact hEntropy
  calc
    (HypercubeRamsey.hammingBall v r).card ≤
        Real.exp (Real.binEntropy ((r : ℝ) / h) * h) := hvolume
    _ ≤ Real.exp ((κ.a / 10 ^ 9) * h) := by
      apply Real.exp_le_exp.mpr
      have hprod := mul_le_mul_of_nonneg_right (hmono.trans hEntReal.le)
        (show (0 : ℝ) ≤ h by positivity)
      nlinarith [hprod]

private theorem clusterHeight_gt_log5 {κ : CConsts} {T : Stage} {k : ℕ}
    (PT : ProfiledTiling κ T k) (hPT : PT.Valid)
    (hm : PT.tiling.mode = .highSmall ∨ PT.tiling.mode = .highLarge)
    (hκ : κ.Admissible) (i : Fin PT.tiling.m)
    (hlog : 1 < Real.log (T.S.n k)) :
    Real.rpow (Real.log (T.S.n k)) ((5 : ℕ) : ℝ) < (PT.tiling.P i).h := by
  have hcluster : PT.tiling.mode = .lowCluster ∨ PT.tiling.mode = .highSmall ∨
      PT.tiling.mode = .highLarge := by
    rcases hm with hs | hl
    · exact Or.inr (Or.inl hs)
    · exact Or.inr (Or.inr hl)
  rcases hPT.tiling_valid.cluster_data hcluster i with
    ⟨_, _, _, _, _, _, _, hqle, _, _, hsmallReg, hlargeReg⟩
  have hMlo : 100 < (κ.Mlo : ℝ) := by
    have hratio : 0 < 100 * κ.aC / κ.aB := by
      exact div_pos (mul_pos (by norm_num) hκ.aC_rng.1) hκ.aB_rng.1
    have hCb : 100 < κ.Cb := by linarith [hκ.Cb_big]
    linarith [hκ.Mlo_big]
  have hMhi : 5 < (κ.Mhi : ℝ) := by
    have hBound := hκ.Mhi_big.1
    have hterm : 0 < 10 / κ.cq := div_pos (by norm_num) hκ.cq_rng.1
    linarith
  have hMhiPos : 0 < (κ.Mhi : ℝ) := by linarith
  have hresult : Real.rpow (Real.log (T.S.n k)) ((5 : ℕ) : ℝ) < (PT.tiling.P i).h := by
    rcases hm with hsmall | hlarge
    · have hReg := hsmallReg.mp hsmall
      have hqLower : Real.rpow (Real.log (T.S.n k)) κ.cq < (PT.tiling.P i).q := hReg.1
      have hqle' : Real.rpow ((PT.tiling.P i).q : ℝ) κ.Mhi ≤ (PT.tiling.P i).h := by
        simpa [hsmall] using hqle
      have hExp : 5 < κ.cq * (κ.Mhi : ℝ) := hκ.Mhi_big.2
      have hpowBase : Real.rpow (Real.log (T.S.n k)) ((5 : ℕ) : ℝ) <
          Real.rpow (Real.log (T.S.n k)) (κ.cq * (κ.Mhi : ℝ)) :=
        Real.rpow_lt_rpow_of_exponent_lt hlog hExp
      have hmul : Real.rpow (Real.log (T.S.n k)) (κ.cq * (κ.Mhi : ℝ)) =
          Real.rpow (Real.rpow (Real.log (T.S.n k)) κ.cq) (κ.Mhi : ℝ) :=
        Real.rpow_mul (by positivity) κ.cq (κ.Mhi : ℝ)
      have hqPow : Real.rpow (Real.rpow (Real.log (T.S.n k)) κ.cq) (κ.Mhi : ℝ) <
          Real.rpow ((PT.tiling.P i).q : ℝ) κ.Mhi :=
        Real.rpow_lt_rpow
          (le_of_lt (Real.rpow_pos_of_pos (by linarith [hlog]) κ.cq)) hqLower hMhiPos
      calc
        Real.rpow (Real.log (T.S.n k)) ((5 : ℕ) : ℝ) <
            Real.rpow (Real.log (T.S.n k)) (κ.cq * (κ.Mhi : ℝ)) := hpowBase
        _ = Real.rpow (Real.rpow (Real.log (T.S.n k)) κ.cq) (κ.Mhi : ℝ) := hmul
        _ < Real.rpow ((PT.tiling.P i).q : ℝ) κ.Mhi := hqPow
        _ ≤ (PT.tiling.P i).h := hqle'
    · have hReg := hlargeReg.mp hlarge
      have hqLower : Real.log (T.S.n k) ^ 2 < (PT.tiling.P i).q := hReg
      have hqle' : Real.rpow ((PT.tiling.P i).q : ℝ) κ.Mhi ≤ (PT.tiling.P i).h := by
        simpa [hlarge] using hqle
      have hqgt : Real.log (T.S.n k) < (PT.tiling.P i).q := by
        nlinarith [hlog, hqLower]
      have hLpow : Real.rpow (Real.log (T.S.n k)) ((5 : ℕ) : ℝ) <
          Real.rpow ((PT.tiling.P i).q : ℝ) ((5 : ℕ) : ℝ) :=
        Real.rpow_lt_rpow (by positivity) hqgt (by norm_num)
      have hqPow : Real.rpow ((PT.tiling.P i).q : ℝ) 5 ≤
          Real.rpow ((PT.tiling.P i).q : ℝ) κ.Mhi :=
        Real.rpow_le_rpow_of_exponent_le (by linarith [hqgt]) (by linarith [hMhi])
      calc
        Real.rpow (Real.log (T.S.n k)) ((5 : ℕ) : ℝ) <
            Real.rpow ((PT.tiling.P i).q : ℝ) 5 := by simpa using hLpow
        _ ≤ Real.rpow ((PT.tiling.P i).q : ℝ) κ.Mhi := hqPow
        _ ≤ (PT.tiling.P i).h := hqle'
  exact hresult

private theorem clusterA_lt_one (κ : CConsts) (hκ : κ.Admissible) : κ.a < 1 := by
  have hfactor : Real.rpow 2 (-(10 * (κ.u : ℝ) + 100)) ≤ 1 := by
    apply Real.rpow_le_one_of_one_le_of_nonpos (by norm_num)
    have hu : (0 : ℝ) ≤ (κ.u : ℝ) := by positivity
    nlinarith
  have hxi : κ.ξ < κ.α := by
    calc
      κ.ξ < κ.α * Real.rpow 2 (-(10 * (κ.u : ℝ) + 100)) := hκ.ξ_rng.2
      _ ≤ κ.α * 1 := mul_le_mul_of_nonneg_left hfactor hκ.α_rng.1.le
      _ = κ.α := by ring
  have hxiLt : κ.ξ < 1 := lt_trans hxi (by linarith [hκ.α_rng.2])
  have hxiSq : κ.ξ ^ 2 < 1 := by nlinarith [hκ.ξ_rng.1, hxiLt]
  have hpow : (1 : ℝ) ≤ (4 : ℝ) ^ (κ.u + 3) := by
    exact_mod_cast (Nat.one_le_pow (κ.u + 3) 4 (by decide))
  have hden : (1 : ℝ) ≤ 3 * 4 ^ (κ.u + 3) := by nlinarith [hpow]
  have htheta : κ.θ < 1 := by
    have hdiv : κ.ξ ^ 2 / (3 * 4 ^ (κ.u + 3)) ≤ κ.ξ ^ 2 :=
      div_le_self (sq_nonneg κ.ξ) hden
    exact lt_of_lt_of_le hκ.θ_rng.2 (hdiv.trans hxiSq.le)
  rw [hκ.a_eq]
  linarith

private theorem clusterSum_union_le_of_nonneg {α : Type*} [Fintype α] [DecidableEq α]
    (A B : Finset α) (f : α → ℝ) (hf : ∀ x, 0 ≤ f x) :
    (∑ x ∈ A ∪ B, f x) ≤ (∑ x ∈ A, f x) + ∑ x ∈ B, f x := by
  classical
  have hdisj : Disjoint (A \ B) B := by
    apply Finset.disjoint_left.mpr
    intro x hx hxB
    exact (Finset.mem_sdiff.mp hx).2 hxB
  have hunion : A ∪ B = (A \ B) ∪ B := by
    ext x
    simp
  have hsumUnion : (∑ x ∈ A ∪ B, f x) =
      (∑ x ∈ A \ B, f x) + ∑ x ∈ B, f x := by
    rw [hunion, Finset.sum_union hdisj]
  have hsumA := Finset.sum_inter_add_sum_sdiff A B f
  have hnonneg : 0 ≤ ∑ x ∈ A ∩ B, f x :=
    Finset.sum_nonneg fun x hx => hf x
  rw [hsumUnion]
  nlinarith [hsumA]

private theorem clusterSum_biUnion_le_sum_sum {α β : Type*} [Fintype α]
    [DecidableEq α] [DecidableEq β] (s : Finset β) (t : β → Finset α)
    (f : α → ℝ) (hf : ∀ x, 0 ≤ f x) :
    (∑ x ∈ s.biUnion t, f x) ≤ ∑ b ∈ s, ∑ x ∈ t b, f x := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | @insert b s hb ih =>
      rw [Finset.biUnion_insert]
      calc
        (∑ x ∈ t b ∪ s.biUnion t, f x) ≤
            (∑ x ∈ t b, f x) + ∑ x ∈ s.biUnion t, f x :=
          clusterSum_union_le_of_nonneg (t b) (s.biUnion t) f hf
        _ ≤ (∑ x ∈ t b, f x) + ∑ c ∈ s, ∑ x ∈ t c, f x :=
          add_le_add (le_rfl) ih
        _ = ∑ c ∈ insert b s, ∑ x ∈ t c, f x := by
          rw [Finset.sum_insert hb]

private theorem clusterExp_pow_nat (x : ℝ) (n : ℕ) :
    Real.exp x ^ n = Real.exp ((n : ℝ) * x) := by
  induction n with
  | zero => simp
  | succ n ih =>
      rw [pow_succ, ih, ← Real.exp_add]
      congr 1
      push_cast
      ring

theorem clusterBadProbability_pr_le_half_charge {Ω : Type*} [Fintype Ω]
    (P : Ω → Prop) (L : FinLaw Ω) (n g h c14 : ℝ)
    (hg : 0 ≤ g) (hn : Real.rpow n 0.2 ≥ 30 * g)
    (hh : Real.rpow h (1 + c14) ≥ 30 * g)
    (hlarge : 6 ≤ Real.exp (10 * g))
    (hraw : L.pr P ≤ Real.exp (-Real.rpow n 0.2) + Real.exp (-200 * g) +
        Real.exp (-Real.rpow h (1 + c14))) :
    L.pr P ≤
      Real.exp (-20 * g) / 2 := by
  have hz : 0 ≤ Real.exp (-30 * g) := (Real.exp_pos _).le
  have h1 : Real.exp (-Real.rpow n 0.2) ≤ Real.exp (-30 * g) := by
    apply Real.exp_le_exp.mpr
    nlinarith [hn]
  have h2 : Real.exp (-200 * g) ≤ Real.exp (-30 * g) := by
    apply Real.exp_le_exp.mpr
    nlinarith [hg]
  have h3 : Real.exp (-Real.rpow h (1 + c14)) ≤ Real.exp (-30 * g) := by
    apply Real.exp_le_exp.mpr
    nlinarith [hh]
  have hsum : Real.exp (-Real.rpow n 0.2) + Real.exp (-200 * g) +
      Real.exp (-Real.rpow h (1 + c14)) ≤ 3 * Real.exp (-30 * g) := by
    nlinarith [h1, h2, h3]
  have hratio : 6 * Real.exp (-30 * g) ≤ Real.exp (-20 * g) := by
    calc
      6 * Real.exp (-30 * g) ≤ Real.exp (10 * g) * Real.exp (-30 * g) :=
        mul_le_mul_of_nonneg_right hlarge hz
      _ = Real.exp (-20 * g) := by rw [← Real.exp_add]; congr 1 <;> ring
  calc
    L.pr P ≤ Real.exp (-Real.rpow n 0.2) + Real.exp (-200 * g) +
        Real.exp (-Real.rpow h (1 + c14)) := hraw
    _ ≤ 3 * Real.exp (-30 * g) := hsum
    _ ≤ Real.exp (-20 * g) / 2 := by nlinarith [hratio]

private theorem clusterConsultation_ball_charge_bound (κ : CConsts) (hκ : κ.Admissible)
    (n h : ℕ) (L : ℝ) (hn : 2 ≤ n) (hL : L = Real.log (n : ℝ))
    (hThreshold : 10 ^ 7 / κ.a ≤ L)
    (hHeight : Real.rpow L ((5 : ℕ) : ℝ) < h) (hh : h ≤ n)
    (outside : OAI.HypercubeRamsey.CubeVertex (n - h))
    (inside : OAI.HypercubeRamsey.CubeVertex h) :
    ((HypercubeRamsey.hammingBall outside 2).card : ℝ) *
      ((HypercubeRamsey.hammingBall inside
        ⌊30 * κ.ρ * (h : ℝ)⌋₊).card : ℝ) *
        Real.exp (-20 * (κ.a * (h : ℝ) / 10 ^ 6)) ≤ Real.exp (-6 * L) / 2 := by
  classical
  have ha0 : 0 < κ.a := by rw [hκ.a_eq]; exact div_pos hκ.θ_rng.1 (by norm_num)
  have ha1 : κ.a ≤ 1 := (clusterA_lt_one κ hκ).le
  have hC : 10 ^ 7 / κ.a ≤ L := hThreshold
  have hCpos : 0 < 10 ^ 7 / κ.a := div_pos (by norm_num) ha0
  have hC1 : 1 ≤ 10 ^ 7 / κ.a := by
    apply (le_div_iff₀ ha0).2
    nlinarith [ha1]
  have hL1 : 1 ≤ L := hC1.trans hC
  have hAC : κ.a * (10 ^ 7 / κ.a) = 10 ^ 7 := by
    field_simp [ne_of_gt ha0]
  have hLpow4 : L ≤ L ^ 4 := by
    have hLsq : L ≤ L ^ 2 := by
      have hmul := mul_nonneg (sub_nonneg.mpr hL1) (le_trans (by norm_num) hL1)
      nlinarith [hmul]
    have hL2 : (1 : ℝ) ≤ L ^ 2 := by nlinarith [hL1]
    calc
      L ≤ L ^ 2 := hLsq
      _ = L ^ 2 * 1 := by ring
      _ ≤ L ^ 2 * L ^ 2 := mul_le_mul_of_nonneg_left hL2 (sq_nonneg L)
      _ = L ^ 4 := by ring
  have hAL4 : 10 ^ 7 ≤ κ.a * L ^ 4 := by
    calc
      10 ^ 7 = κ.a * (10 ^ 7 / κ.a) := hAC.symm
      _ ≤ κ.a * L := mul_le_mul_of_nonneg_left hC ha0.le
      _ ≤ κ.a * L ^ 4 := mul_le_mul_of_nonneg_left hLpow4 ha0.le
  have hcoeff : 40 ≤ κ.a * L ^ 4 / 60000 := by nlinarith [hAL4]
  have hslack0 : 20 * (L + 1) ≤ κ.a * L ^ 5 / 60000 := by
    have hcoeffL := mul_le_mul_of_nonneg_right hcoeff (le_trans (by norm_num) hL1)
    nlinarith [hcoeffL]
  have hHeightNat : L ^ 5 < (h : ℝ) := by
    have h' := hHeight
    rw [Real.rpow_eq_pow] at h'
    rw [Real.rpow_natCast] at h'
    exact h'
  have hheightPos : 0 < (h : ℝ) := lt_trans (Real.rpow_pos_of_pos (by linarith [hL1]) 5) hHeight
  have hslack : 20 * (L + 1) ≤ κ.a * (h : ℝ) / 60000 := by
    have hmul := mul_le_mul_of_nonneg_left (le_of_lt hHeightNat) ha0.le
    have hdiv := div_le_div_of_nonneg_right hmul (by norm_num : (0 : ℝ) ≤ 60000)
    exact hslack0.trans hdiv
  have hlog2 : Real.log 2 ≤ 1 := by
    apply (Real.log_le_iff_le_exp (by norm_num)).2
    have he := Real.add_one_le_exp 1
    nlinarith
  have hplusNat : n + 1 ≤ 2 * n := by omega
  have hplus : ((n + 1 : ℕ) : ℝ) ≤ 2 * (n : ℝ) := by exact_mod_cast hplusNat
  have hlogPlus : Real.log ((n + 1 : ℕ) : ℝ) ≤ L + 1 := by
    calc
      Real.log ((n + 1 : ℕ) : ℝ) ≤ Real.log (2 * (n : ℝ)) :=
        Real.log_le_log (by positivity) hplus
      _ = Real.log 2 + Real.log (n : ℝ) := Real.log_mul (by norm_num) (by positivity)
      _ ≤ L + 1 := by rw [hL]; linarith [hlog2]
  have hnplusExp : ((n + 1 : ℕ) : ℝ) ≤ Real.exp (L + 1) := by
    calc
      ((n + 1 : ℕ) : ℝ) = Real.exp (Real.log ((n + 1 : ℕ) : ℝ)) :=
        (Real.exp_log (by positivity)).symm
      _ ≤ Real.exp (L + 1) := Real.exp_le_exp.mpr hlogPlus
  have houterNat := clusterHammingBall_two_card_le outside
  have hdim : ((n - h + 1 : ℕ) : ℝ) ≤ ((n + 1 : ℕ) : ℝ) := by
    exact_mod_cast (Nat.add_le_add_right (Nat.sub_le n h) 1)
  have houter : ((HypercubeRamsey.hammingBall outside 2).card : ℝ) ≤
      Real.exp (2 * (L + 1)) := by
    have houter' : ((HypercubeRamsey.hammingBall outside 2).card : ℝ) ≤
        ((n - h + 1 : ℕ) : ℝ) ^ 2 := by exact_mod_cast houterNat
    calc
      _ ≤ ((n + 1 : ℕ) : ℝ) ^ 2 := by nlinarith [houter', hdim]
      _ = ((n + 1 : ℕ) : ℝ) * ((n + 1 : ℕ) : ℝ) := by ring
      _ ≤ Real.exp (L + 1) * Real.exp (L + 1) :=
        mul_le_mul hnplusExp hnplusExp (by positivity) (by positivity)
      _ = Real.exp (2 * (L + 1)) := by rw [← Real.exp_add]; congr 1 <;> ring
  have hinner := clusterInnerHammingBall_volume_bound κ hκ h
    (by exact_mod_cast (lt_trans (Real.rpow_pos_of_pos (by linarith [hL1]) 5) hHeight)) inside
  have hinnerR : ((HypercubeRamsey.hammingBall inside
      ⌊30 * κ.ρ * (h : ℝ)⌋₊).card : ℝ) ≤
        Real.exp ((κ.a / 10 ^ 9) * (h : ℝ)) := hinner
  have hprod : ((HypercubeRamsey.hammingBall outside 2).card : ℝ) *
      ((HypercubeRamsey.hammingBall inside
        ⌊30 * κ.ρ * (h : ℝ)⌋₊).card : ℝ) ≤
        Real.exp (2 * (L + 1) + (κ.a / 10 ^ 9) * (h : ℝ)) := by
    calc
      _ ≤ Real.exp (2 * (L + 1)) * Real.exp ((κ.a / 10 ^ 9) * (h : ℝ)) :=
        mul_le_mul houter hinnerR (by positivity) (by positivity)
    _ = Real.exp (2 * (L + 1) + (κ.a / 10 ^ 9) * (h : ℝ)) := by
        rw [← Real.exp_add]
  have hcoef : (1 : ℝ) / 50000 - 1 / 10 ^ 9 ≥ 1 / 60000 := by norm_num
  have hgap : (κ.a * (h : ℝ)) / 60000 ≤
      20 * (κ.a * (h : ℝ) / 10 ^ 6) - (κ.a / 10 ^ 9) * (h : ℝ) := by
    have hmul := mul_le_mul_of_nonneg_left hcoef (mul_nonneg ha0.le (by positivity : (0 : ℝ) ≤ (h : ℝ)))
    nlinarith [hmul]
  have hexp : 2 * (L + 1) + (κ.a / 10 ^ 9) * (h : ℝ) -
      20 * (κ.a * (h : ℝ) / 10 ^ 6) ≤ -18 * (L + 1) := by
    nlinarith [hslack, hgap]
  calc
    _ ≤ Real.exp (2 * (L + 1) + (κ.a / 10 ^ 9) * (h : ℝ)) *
        Real.exp (-20 * (κ.a * (h : ℝ) / 10 ^ 6)) :=
      mul_le_mul_of_nonneg_right hprod (Real.exp_pos _).le
    _ = Real.exp (2 * (L + 1) + (κ.a / 10 ^ 9) * (h : ℝ) -
        20 * (κ.a * (h : ℝ) / 10 ^ 6)) := by rw [← Real.exp_add]; congr 1 <;> ring
    _ ≤ Real.exp (-6 * L - 1) := Real.exp_le_exp.mpr (by nlinarith [hexp, hL1])
    _ = Real.exp (-6 * L) * Real.exp (-1) := by
      have hsum : -6 * L - 1 = (-6 * L) + (-1) := by ring
      rw [hsum, Real.exp_add]
    _ ≤ Real.exp (-6 * L) / 2 := by
      have he : 2 ≤ Real.exp 1 := by nlinarith [Real.add_one_le_exp 1]
      have hInv : Real.exp (-1) ≤ 1 / 2 := by
        rw [Real.exp_neg]
        have hInv' : (Real.exp 1)⁻¹ ≤ (2 : ℝ)⁻¹ :=
          (inv_le_inv₀ (Real.exp_pos 1) (by norm_num : (0 : ℝ) < 2)).2 he
        simpa using hInv'
      calc
        Real.exp (-6 * L) * Real.exp (-1) ≤ Real.exp (-6 * L) * (1 / 2) :=
          mul_le_mul_of_nonneg_left hInv (Real.exp_pos _).le
        _ = Real.exp (-6 * L) / 2 := by ring

theorem clusterConsultation_radius_eventually (κ : CConsts) (hκ : κ.Admissible) (T : Stage) :
    ∀ᶠ k in Filter.atTop, ∀ PT : ProfiledTiling κ T k, ∀ hPT : PT.Valid,
      ∀ hm : PT.tiling.mode = .highSmall ∨ PT.tiling.mode = .highLarge,
      ∀ a : EvenPosition T k,
        8 ≤ 10 * κ.ρ * (PT.tiling.P (patchAt PT hPT a.1)).h := by
  have hnReal : Filter.Tendsto (fun k => (T.S.n k : ℝ)) Filter.atTop Filter.atTop :=
    tendsto_natCast_atTop_atTop.comp T.S.n_tendsto
  have hlog : Filter.Tendsto (fun k => Real.log (T.S.n k : ℝ)) Filter.atTop Filter.atTop :=
    Real.tendsto_log_atTop.comp hnReal
  let B : ℝ := max 2 (8 / (10 * κ.ρ) + 1)
  have hev : ∀ᶠ k in Filter.atTop, B ≤ Real.log (T.S.n k : ℝ) :=
    hlog.eventually_ge_atTop B
  filter_upwards [hev] with k hk
  intro PT hPT hm a
  let i := patchAt PT hPT a.1
  let L := Real.log (T.S.n k : ℝ)
  have hlogN : 1 < L := by dsimp [L, B] at hk ⊢; linarith [le_max_left 2 (8 / (10 * κ.ρ) + 1)]
  have hlarge : 8 / (10 * κ.ρ) ≤ L := by
    have hB : 8 / (10 * κ.ρ) + 1 ≤ B := le_max_right 2 _
    dsimp [L]
    linarith [hk, hB]
  have hheight := clusterHeight_gt_log5 PT hPT hm hκ i hlogN
  have hL1 : (1 : ℝ) ≤ L := le_of_lt hlogN
  have hLpow : L ≤ Real.rpow L 5 := by
    calc
      L = Real.rpow L 1 := (Real.rpow_one L).symm
      _ ≤ Real.rpow L 5 := Real.rpow_le_rpow_of_exponent_le hL1 (by norm_num)
  have hh : (8 / (10 * κ.ρ)) < (PT.tiling.P i).h :=
    lt_of_le_of_lt hlarge (lt_of_le_of_lt hLpow hheight)
  have hmul : (8 : ℝ) < 10 * κ.ρ * (PT.tiling.P i).h := by
    calc
      (8 : ℝ) < (PT.tiling.P i).h * (10 * κ.ρ) :=
        (div_lt_iff₀ (mul_pos (by norm_num) hκ.ρ_rng.1)).mp hh
      _ = 10 * κ.ρ * (PT.tiling.P i).h := by ring
  exact le_of_lt (by simpa [i] using hmul)

/-- Every patch has a sufficiently large consultation radius at all large stages. -/
theorem clusterPatch_radius_eventually (κ : CConsts) (hκ : κ.Admissible) (T : Stage) :
    ∀ᶠ k in Filter.atTop, ∀ PT : ProfiledTiling κ T k, ∀ hPT : PT.Valid,
      ∀ hm : PT.tiling.mode = .highSmall ∨ PT.tiling.mode = .highLarge,
      ∀ i : Fin PT.tiling.m, 8 ≤ 10 * κ.ρ * (PT.tiling.P i).h := by
  have hnReal : Filter.Tendsto (fun k => (T.S.n k : ℝ)) Filter.atTop Filter.atTop :=
    tendsto_natCast_atTop_atTop.comp T.S.n_tendsto
  have hlog : Filter.Tendsto (fun k => Real.log (T.S.n k : ℝ)) Filter.atTop Filter.atTop :=
    Real.tendsto_log_atTop.comp hnReal
  let B : ℝ := max 2 (8 / (10 * κ.ρ) + 1)
  have hev : ∀ᶠ k in Filter.atTop, B ≤ Real.log (T.S.n k : ℝ) :=
    hlog.eventually_ge_atTop B
  filter_upwards [hev] with k hk
  intro PT hPT hm i
  let L := Real.log (T.S.n k : ℝ)
  have hlogN : 1 < L := by dsimp [L, B] at hk ⊢; linarith [le_max_left 2 (8 / (10 * κ.ρ) + 1)]
  have hlarge : 8 / (10 * κ.ρ) ≤ L := by
    have hB : 8 / (10 * κ.ρ) + 1 ≤ B := le_max_right 2 _
    dsimp [L]
    linarith [hk, hB]
  have hheight := clusterHeight_gt_log5 PT hPT hm hκ i hlogN
  have hL1 : (1 : ℝ) ≤ L := le_of_lt hlogN
  have hLpow : L ≤ Real.rpow L 5 := by
    calc
      L = Real.rpow L 1 := (Real.rpow_one L).symm
      _ ≤ Real.rpow L 5 := Real.rpow_le_rpow_of_exponent_le hL1 (by norm_num)
  have hh : (8 / (10 * κ.ρ)) < (PT.tiling.P i).h :=
    lt_of_le_of_lt hlarge (lt_of_le_of_lt hLpow hheight)
  have hmul : (8 : ℝ) < 10 * κ.ρ * (PT.tiling.P i).h := by
    calc
      (8 : ℝ) < (PT.tiling.P i).h * (10 * κ.ρ) :=
        (div_lt_iff₀ (mul_pos (by norm_num) hκ.ρ_rng.1)).mp hh
      _ = 10 * κ.ρ * (PT.tiling.P i).h := by ring
  exact le_of_lt (by simpa using hmul)

theorem clusterRowScopes_overlap_degree_bound {κ : CConsts} {T : Stage} {k : ℕ}
    (PT : ProfiledTiling κ T k) (hPT : PT.Valid)
    (hm : PT.tiling.mode = .highSmall ∨ PT.tiling.mode = .highLarge)
    (hκ : κ.Admissible) (a : EvenPosition T k)
    (hRadius : 8 ≤ 10 * κ.ρ * (PT.tiling.P (patchAt PT hPT a.1)).h) :
    (Finset.univ.filter fun a' : EvenPosition T k =>
      ∃ r : ClusterRecordIndex PT hPT hm,
        r ∈ clusterConsultationScope PT hPT hm (clusterRowConsultations PT hPT hm a) ∧
        r ∈ clusterConsultationScope PT hPT hm (clusterRowConsultations PT hPT hm a')).card ≤
      ((T.S.n k : ℝ) + 1) ^ 2 *
        Real.exp ((κ.a / 10 ^ 9) * ((PT.tiling.P (patchAt PT hPT a.1)).h : ℝ)) := by
  classical
  let i := patchAt PT hPT a.1
  let h := (PT.tiling.P i).h
  let rball := ⌊30 * κ.ρ * (h : ℝ)⌋₊
  let outerBall := HypercubeRamsey.hammingBall (outsideWord PT hPT i a.1) 2
  let innerBall := HypercubeRamsey.hammingBall (internalWord PT hPT i a.1) rball
  have hcount := clusterRowScopes_overlap_count_le_ball_product PT hPT hm a rball hRadius rfl
  have houterNat := clusterHammingBall_two_card_le (outsideWord PT hPT i a.1)
  have hdimNat : (T.S.n k - h + 1) ≤ T.S.n k + 1 := by omega
  have houter : (outerBall.card : ℝ) ≤ ((T.S.n k : ℝ) + 1) ^ 2 := by
    have houter' : (outerBall.card : ℝ) ≤ ((T.S.n k - h + 1 : ℕ) : ℝ) ^ 2 := by
      exact_mod_cast houterNat
    have hdim : ((T.S.n k - h + 1 : ℕ) : ℝ) ≤ (T.S.n k : ℝ) + 1 := by
      exact_mod_cast hdimNat
    nlinarith [houter', hdim, sq_nonneg ((T.S.n k : ℝ) + 1)]
  have hinnerNat := clusterInnerHammingBall_volume_bound κ hκ h
    (clusterHeight_pos PT hPT hm i) (internalWord PT hPT i a.1)
  have hinner : (innerBall.card : ℝ) ≤
      Real.exp ((κ.a / 10 ^ 9) * (h : ℝ)) := by
    simpa [innerBall, rball, h] using hinnerNat
  have hcountR : ((Finset.univ.filter fun a' : EvenPosition T k =>
      ∃ r : ClusterRecordIndex PT hPT hm,
        r ∈ clusterConsultationScope PT hPT hm (clusterRowConsultations PT hPT hm a) ∧
        r ∈ clusterConsultationScope PT hPT hm (clusterRowConsultations PT hPT hm a')).card : ℝ) ≤
      (outerBall.card : ℝ) * (innerBall.card : ℝ) := by
    exact_mod_cast hcount
  have hprod := mul_le_mul houter hinner (by positivity) (by positivity)
  simpa [i, h] using hcountR.trans hprod

theorem clusterHighRow_charge_facts {κ : CConsts} {T : Stage} {k : ℕ}
    (PT : ProfiledTiling κ T k) (hPT : PT.Valid)
    (hm : PT.tiling.mode = .highSmall ∨ PT.tiling.mode = .highLarge)
    (hκ : κ.Admissible) (a : EvenPosition T k) (hn : 2 ≤ T.S.n k)
    (L : ℝ) (hL : L = Real.log (T.S.n k : ℝ))
    (hThreshold : 10 ^ 7 / κ.a ≤ L)
    (hRadius : 8 ≤ 10 * κ.ρ * (PT.tiling.P (patchAt PT hPT a.1)).h) :
    1 ≤ PT.tiling.gain (patchAt PT hPT a.1) ∧
      Real.rpow (T.S.n k : ℝ) 0.2 ≥
        30 * PT.tiling.gain (patchAt PT hPT a.1) ∧
      Real.rpow ((PT.tiling.P (patchAt PT hPT a.1)).h : ℝ) (1 + κ.c14) ≥
        30 * PT.tiling.gain (patchAt PT hPT a.1) ∧
      6 ≤ Real.exp (10 * PT.tiling.gain (patchAt PT hPT a.1)) ∧
      ((Finset.univ.filter fun a' : EvenPosition T k =>
        ∃ r : ClusterRecordIndex PT hPT hm,
          r ∈ clusterConsultationScope PT hPT hm
            (clusterRowConsultations PT hPT hm a) ∧
          r ∈ clusterConsultationScope PT hPT hm
            (clusterRowConsultations PT hPT hm a')).card : ℝ) *
        Real.exp (-20 * PT.tiling.gain (patchAt PT hPT a.1)) ≤ 1 / 2 := by
  classical
  let i := patchAt PT hPT a.1
  let h := (PT.tiling.P i).h
  let g := PT.tiling.gain i
  have ha0 : 0 < κ.a := by rw [hκ.a_eq]; exact div_pos hκ.θ_rng.1 (by norm_num)
  have ha1 : κ.a ≤ 1 := (clusterA_lt_one κ hκ).le
  have hlog : 1 < L := by
    have hC : (1 : ℝ) < 10 ^ 7 / κ.a :=
      (lt_div_iff₀ ha0).2 (by nlinarith [ha1])
    exact lt_of_lt_of_le hC hThreshold
  have hlog' : 1 < Real.log (T.S.n k) := by simpa [hL] using hlog
  have hheight := clusterHeight_gt_log5 PT hPT hm hκ i hlog'
  have hheightL : Real.rpow L ((5 : ℕ) : ℝ) < (h : ℝ) := by
    simpa [hL, i, h] using hheight
  have hLpow : L ≤ Real.rpow L 5 := by
    have hL1 : 1 ≤ L := le_of_lt hlog
    calc
      L = Real.rpow L 1 := (Real.rpow_one L).symm
      _ ≤ Real.rpow L 5 := Real.rpow_le_rpow_of_exponent_le hL1 (by norm_num)
  have hhLower : L < (h : ℝ) := lt_of_le_of_lt hLpow hheightL
  have hthresholdProd : 10 ^ 7 ≤ κ.a * L := by
    have hmul := mul_le_mul_of_nonneg_left hThreshold ha0.le
    have hEq : κ.a * (10 ^ 7 / κ.a) = 10 ^ 7 := by field_simp [ha0.ne']
    nlinarith [hmul, hEq]
  have hgain : g = κ.a * (h : ℝ) / 10 ^ 6 := by
    rcases hm with hs | hl
    · simp [g, Tiling.gain, i, h, hs]
    · simp [g, Tiling.gain, i, h, hl]
  have hg : 1 ≤ g := by
    rw [hgain]
    have hlargeGain : 10 ^ 7 < κ.a * (h : ℝ) :=
      lt_of_le_of_lt hthresholdProd (mul_lt_mul_of_pos_left hhLower ha0)
    apply (le_div_iff₀ (by norm_num : (0 : ℝ) < 10 ^ 6)).2
    nlinarith [hlargeGain]
  have hupper : (h : ℝ) < (T.S.n k : ℝ) ^ κ.ι := by
    rcases hPT.tiling_valid.allocation_bounds i with ⟨hmax, _⟩
    have hle : h ≤ max h (PT.tiling.P i).ℓ := Nat.le_max_left _ _
    have hleR : (h : ℝ) ≤ (max h (PT.tiling.P i).ℓ : ℝ) := by exact_mod_cast hle
    exact hleR.trans_lt hmax
  have hι : κ.ι < 0.2 := by
    have hmin : min κ.xs (min κ.η0 0.01) ≤ 0.01 :=
      (min_le_right _ _).trans (min_le_right _ _)
    have hι' : κ.ι < (0.01 : ℝ) / 1000 :=
      lt_of_lt_of_le hκ.ι_rng.2 (div_le_div_of_nonneg_right hmin (by norm_num))
    nlinarith
  have hnOne : (1 : ℝ) ≤ (T.S.n k : ℝ) := by exact_mod_cast (by omega : 1 ≤ T.S.n k)
  have hnPow : (T.S.n k : ℝ) ^ κ.ι ≤ (T.S.n k : ℝ) ^ (0.2 : ℝ) :=
    Real.rpow_le_rpow_of_exponent_le hnOne hι.le
  have hnAlarm : Real.rpow (T.S.n k : ℝ) 0.2 ≥ 30 * g := by
    have hhpow : (h : ℝ) ≤ (T.S.n k : ℝ) ^ (0.2 : ℝ) :=
      le_of_lt hupper |>.trans hnPow
    have hgh : g ≤ (h : ℝ) / 10 ^ 6 := by
      rw [hgain]
      apply div_le_div_of_nonneg_right
      · have hhnonneg : (0 : ℝ) ≤ (h : ℝ) := by positivity
        simpa using mul_le_mul_of_nonneg_right ha1 hhnonneg
      · positivity
    have h30g : 30 * g ≤ (h : ℝ) := by nlinarith [hgh]
    exact h30g.trans hhpow
  have hHeightOne : (1 : ℝ) ≤ (h : ℝ) := by
    have hpos := clusterHeight_pos PT hPT hm i
    exact_mod_cast (Nat.one_le_iff_ne_zero.mpr (Nat.ne_of_gt hpos))
  have hhAlarm : Real.rpow (h : ℝ) (1 + κ.c14) ≥ 30 * g := by
    have hpowa : (h : ℝ) ≤ Real.rpow (h : ℝ) (1 + κ.c14) := by
      calc
        (h : ℝ) = Real.rpow (h : ℝ) 1 := (Real.rpow_one _).symm
        _ ≤ Real.rpow (h : ℝ) (1 + κ.c14) :=
          Real.rpow_le_rpow_of_exponent_le hHeightOne (by linarith [hκ.c14_pos])
    have hgh : g ≤ (h : ℝ) / 10 ^ 6 := by
      rw [hgain]
      apply div_le_div_of_nonneg_right
      · have hhnonneg : (0 : ℝ) ≤ (h : ℝ) := by positivity
        simpa using mul_le_mul_of_nonneg_right ha1 hhnonneg
      · positivity
    have h30g : 30 * g ≤ (h : ℝ) := by nlinarith [hgh]
    exact h30g.trans hpowa
  have hlarge : 6 ≤ Real.exp (10 * g) := by
    have he := Real.add_one_le_exp (10 * g)
    nlinarith [hg, he]
  let rowOverlap := Finset.univ.filter fun a' : EvenPosition T k =>
    ∃ r : ClusterRecordIndex PT hPT hm,
      r ∈ clusterConsultationScope PT hPT hm (clusterRowConsultations PT hPT hm a) ∧
      r ∈ clusterConsultationScope PT hPT hm (clusterRowConsultations PT hPT hm a')
  have hcount := clusterRowScopes_overlap_count_le_ball_product PT hPT hm a
    (⌊30 * κ.ρ * (h : ℝ)⌋₊) hRadius rfl
  have hcountR : (rowOverlap.card : ℝ) ≤
      ((HypercubeRamsey.hammingBall (outsideWord PT hPT i a.1) 2).card : ℝ) *
        ((HypercubeRamsey.hammingBall (internalWord PT hPT i a.1)
          ⌊30 * κ.ρ * (h : ℝ)⌋₊).card : ℝ) := by
    exact_mod_cast hcount
  have hBall := clusterConsultation_ball_charge_bound κ hκ (T.S.n k) h L hn hL
    hThreshold hheightL (clusterHeight_le PT hPT i)
    (outsideWord PT hPT i a.1) (internalWord PT hPT i a.1)
  have hcountCharge : (rowOverlap.card : ℝ) * Real.exp (-20 * g) ≤ 1 / 2 := by
    calc
      _ ≤ ((HypercubeRamsey.hammingBall (outsideWord PT hPT i a.1) 2).card : ℝ) *
          ((HypercubeRamsey.hammingBall (internalWord PT hPT i a.1)
            ⌊30 * κ.ρ * (h : ℝ)⌋₊).card : ℝ) * Real.exp (-20 * g) :=
        mul_le_mul_of_nonneg_right hcountR (Real.exp_pos _).le
      _ = ((HypercubeRamsey.hammingBall (outsideWord PT hPT i a.1) 2).card : ℝ) *
          ((HypercubeRamsey.hammingBall (internalWord PT hPT i a.1)
            ⌊30 * κ.ρ * (h : ℝ)⌋₊).card : ℝ) *
            Real.exp (-20 * (κ.a * (h : ℝ) / 10 ^ 6)) := by rw [hgain]
      _ ≤ Real.exp (-6 * L) / 2 := hBall
      _ ≤ 1 / 2 := by
        have hExp : Real.exp (-6 * L) ≤ 1 :=
          Real.exp_le_one_iff.mpr (by linarith [hlog])
        exact div_le_div_of_nonneg_right hExp (by norm_num)
  exact ⟨hg, hnAlarm, hhAlarm, hlarge, hcountCharge⟩

/-- The first alarm is fixed by the consultation neighborhoods of its bulk marginals. -/
theorem clusterAlarm1_indicator_depends_on_bulk_consultations {κ : CConsts} {T : Stage} {k : ℕ}
    (PT : ProfiledTiling κ T k) (hPT : PT.Valid)
    (hm : PT.tiling.mode = .highSmall ∨ PT.tiling.mode = .highLarge)
    (a : EvenPosition T k) :
    ClusterHistoryDependsOn
      (fun W => if clusterAlarm1 PT hPT hm W a then 1 else 0)
      (clusterConsultationScope PT hPT hm
        (clusterBulkMarginalConsultations PT hPT hm a)) := by
  classical
  intro W W' hWW'
  have hmarginal (b : OddPosition T k) (hb : b ∈ clusterBulkNeighbours PT hPT a)
      (y : Fin (T.S.N k)) :
      clusterMarginal PT hPT hm W b y = clusterMarginal PT hPT hm W' b y := by
    have hquery : clusterMarginalConsultation PT hPT hm b ∈
        clusterBulkMarginalConsultations PT hPT hm a := by
      exact Finset.mem_image.mpr ⟨b, hb, rfl⟩
    have hsingleton :
        clusterConsultationScope PT hPT hm {clusterMarginalConsultation PT hPT hm b} ⊆
          clusterConsultationScope PT hPT hm
            (clusterBulkMarginalConsultations PT hPT hm a) :=
      clusterConsultationScope_mono PT hPT hm _ _ (by
        intro c hc
        have hc' := Finset.mem_singleton.mp hc
        rw [hc']
        exact hquery)
    exact clusterMarginal_eq_of_consultation_scope PT hPT hm W W' b
      (fun r hr => hWW' r (hsingleton hr)) y
  have hdegree (b : OddPosition T k) (hb : b ∈ clusterBulkNeighbours PT hPT a)
      (x : Fin (T.S.N k)) :
      clusterDegree PT hPT hm W b x = clusterDegree PT hPT hm W' b x := by
    have hmarginalFun : clusterMarginal PT hPT hm W b = clusterMarginal PT hPT hm W' b := by
      funext y
      exact hmarginal b hb y
    simp [clusterDegree, hmarginalFun]
  have hJ0 (x : Fin (T.S.N k)) :
      clusterJ0 PT hPT hm W a x ↔ clusterJ0 PT hPT hm W' a x := by
    unfold clusterJ0
    constructor
    · rintro ⟨hx, hgate, hpos, hlo, hhi⟩
      refine ⟨hx, ?_, hpos, ?_, ?_⟩
      · intro b hb
        simpa [hdegree b hb x] using hgate b hb
      · have hprod :
          (∏ b ∈ clusterBulkNeighbours PT hPT a, clusterDegree PT hPT hm W b x) =
            ∏ b ∈ clusterBulkNeighbours PT hPT a, clusterDegree PT hPT hm W' b x := by
          apply Finset.prod_congr rfl
          intro b hb
          exact hdegree b hb x
        simpa [hprod] using hlo
      · have hprod :
          (∏ b ∈ clusterBulkNeighbours PT hPT a, clusterDegree PT hPT hm W b x) =
            ∏ b ∈ clusterBulkNeighbours PT hPT a, clusterDegree PT hPT hm W' b x := by
          apply Finset.prod_congr rfl
          intro b hb
          exact hdegree b hb x
        simpa [hprod] using hhi
    · rintro ⟨hx, hgate, hpos, hlo, hhi⟩
      refine ⟨hx, ?_, hpos, ?_, ?_⟩
      · intro b hb
        simpa [hdegree b hb x] using hgate b hb
      · have hprod :
          (∏ b ∈ clusterBulkNeighbours PT hPT a, clusterDegree PT hPT hm W' b x) =
            ∏ b ∈ clusterBulkNeighbours PT hPT a, clusterDegree PT hPT hm W b x := by
          apply Finset.prod_congr rfl
          intro b hb
          exact (hdegree b hb x).symm
        simpa [hprod] using hlo
      · have hprod :
          (∏ b ∈ clusterBulkNeighbours PT hPT a, clusterDegree PT hPT hm W' b x) =
            ∏ b ∈ clusterBulkNeighbours PT hPT a, clusterDegree PT hPT hm W b x := by
          apply Finset.prod_congr rfl
          intro b hb
          exact (hdegree b hb x).symm
        simpa [hprod] using hhi
  have hbad : clusterAlarm1 PT hPT hm W a ↔ clusterAlarm1 PT hPT hm W' a := by
    unfold clusterAlarm1
    have hsum :
        (∑ x, if clusterJ0 PT hPT hm W a x then 0 else
          (Law.unifCore (PT.tiling.P (patchAt PT hPT a.1)).X
            (hPT.tiling_valid.patch_nonempty (patchAt PT hPT a.1)).1).w x) =
        ∑ x, if clusterJ0 PT hPT hm W' a x then 0 else
          (Law.unifCore (PT.tiling.P (patchAt PT hPT a.1)).X
            (hPT.tiling_valid.patch_nonempty (patchAt PT hPT a.1)).1).w x := by
      apply Finset.sum_congr rfl
      intro x hx
      simp only [hJ0 x]
    rw [hsum]
  change (if clusterAlarm1 PT hPT hm W a then 1 else 0) =
    (if clusterAlarm1 PT hPT hm W' a then 1 else 0)
  rw [hbad]

/-- Agreement on a patch's primitive records fixes the history on every slice in that patch. -/
theorem clusterHistoryOnSlice_eq_of_patch_scope {κ : CConsts} {T : Stage} {k : ℕ}
    (PT : ProfiledTiling κ T k) (hPT : PT.Valid)
    (hm : PT.tiling.mode = .highSmall ∨ PT.tiling.mode = .highLarge)
    (W W' : ClusterHistory PT hPT hm) (i : Fin PT.tiling.m)
    (hWW' : ∀ r ∈ clusterPatchRecordScope PT hPT hm i, W r = W' r)
    (s : ClusterSlice PT) (hs : s.1 = i) : historyOnSlice W s = historyOnSlice W' s := by
  funext r
  have hr : (⟨s, r⟩ : ClusterRecordIndex PT hPT hm) ∈
      clusterPatchRecordScope PT hPT hm i := by
    simp [clusterPatchRecordScope, hs]
  exact hWW' ⟨s, r⟩ hr

/-- Expectations of functions of one slice depend only on its product-law marginal. -/
theorem clusterInternalKernel_E_at_slice {κ : CConsts} {T : Stage} {k : ℕ}
    (PT : ProfiledTiling κ T k) (hPT : PT.Valid)
    (hm : PT.tiling.mode = .highSmall ∨ PT.tiling.mode = .highLarge)
    (W : ClusterHistory PT hPT hm) (s : ClusterSlice PT)
    (f : ClusterSliceOutcome PT s.1 → ℝ) :
    (clusterInternalKernel PT hPT hm W).E (fun I => f (I s)) =
      ((clusterSolver PT hPT hm s.1).refLaw (historyOnSlice W s)).E f := by
  change (FinLaw.pi (fun s' : ClusterSlice PT =>
      (clusterSolver PT hPT hm s'.1).refLaw (historyOnSlice W s'))).E
      (fun I => f (I s)) = _
  exact pi_E_coordinate
    (fun s' : ClusterSlice PT =>
      (clusterSolver PT hPT hm s'.1).refLaw (historyOnSlice W s')) s f

/-- The integrand of the large-interaction statistic as a function of its center slice outcome. -/
noncomputable def clusterInteractionIntegrandAtCenter {κ : CConsts} {T : Stage} {k : ℕ}
    (PT : ProfiledTiling κ T k) (hPT : PT.Valid)
    (hm : PT.tiling.mode = .highSmall ∨ PT.tiling.mode = .highLarge)
    (W : ClusterHistory PT hPT hm) (a : EvenPosition T k)
    (Y : ClusterSliceOutcome PT (clusterSliceAt PT hPT a.1).1) : ℝ :=
  ∑ xs : Fin κ.u → Fin (T.S.N k),
    (∏ j, clusterSigmaAtCenter PT hPT hm W a Y (xs j)) *
      (if (∀ j, clusterJ0 PT hPT hm W a (xs j)) ∧
          ∃ b ∈ clusterBulkNeighbours PT hPT a, ∃ J : Finset (Fin κ.u),
            2 ≤ J.card ∧ 2 * κ.ξ < |clusterInteraction PT hPT hm W b J xs| then
        clusterInteractionEnvelope PT hPT hm W a xs else 0)

/-- The raw interaction statistic is the center-slice expectation of its local integrand. -/
theorem clusterInteractionCost_eq_centerExpectation {κ : CConsts} {T : Stage} {k : ℕ}
    (PT : ProfiledTiling κ T k) (hPT : PT.Valid)
    (hm : PT.tiling.mode = .highSmall ∨ PT.tiling.mode = .highLarge)
    (W : ClusterHistory PT hPT hm) (a : EvenPosition T k) :
    clusterInteractionCost PT hPT hm W a =
      ((clusterSolver PT hPT hm (clusterSliceAt PT hPT a.1).1).refLaw
        (historyOnSlice W (clusterSliceAt PT hPT a.1))).E
        (clusterInteractionIntegrandAtCenter PT hPT hm W a) := by
  let s := clusterSliceAt PT hPT a.1
  have hpoint (I : ClusterInternalData PT) :
      (∑ xs : Fin κ.u → Fin (T.S.N k),
        (∏ j, clusterSigma PT hPT hm W I a (xs j)) *
          (if (∀ j, clusterJ0 PT hPT hm W a (xs j)) ∧
              ∃ b ∈ clusterBulkNeighbours PT hPT a, ∃ J : Finset (Fin κ.u),
                2 ≤ J.card ∧ 2 * κ.ξ < |clusterInteraction PT hPT hm W b J xs| then
            clusterInteractionEnvelope PT hPT hm W a xs else 0)) =
        clusterInteractionIntegrandAtCenter PT hPT hm W a (I s) := by
    simp [clusterInteractionIntegrandAtCenter, clusterSigmaAtCenter, clusterSigma, s]
  unfold clusterInteractionCost
  rw [FinLaw.E]
  calc
    (∑ I, (clusterInternalKernel PT hPT hm W).w I *
      (∑ xs : Fin κ.u → Fin (T.S.N k),
        (∏ j, clusterSigma PT hPT hm W I a (xs j)) *
          (if (∀ j, clusterJ0 PT hPT hm W a (xs j)) ∧
              ∃ b ∈ clusterBulkNeighbours PT hPT a, ∃ J : Finset (Fin κ.u),
                2 ≤ J.card ∧ 2 * κ.ξ < |clusterInteraction PT hPT hm W b J xs| then
            clusterInteractionEnvelope PT hPT hm W a xs else 0))) =
      (clusterInternalKernel PT hPT hm W).E
        (fun I => clusterInteractionIntegrandAtCenter PT hPT hm W a (I s)) := by
          rw [FinLaw.E]
          apply Finset.sum_congr rfl
          intro I hI
          rw [hpoint]
    _ = ((clusterSolver PT hPT hm s.1).refLaw (historyOnSlice W s)).E
        (clusterInteractionIntegrandAtCenter PT hPT hm W a) := by
          exact clusterInternalKernel_E_at_slice PT hPT hm W s
            (clusterInteractionIntegrandAtCenter PT hPT hm W a)

/-- A union of three events has probability at most the sum of their probabilities. -/
theorem finLaw_pr_or3_le_add {Ω : Type*} [Fintype Ω]
    (P : FinLaw Ω) (A B C : Ω → Prop) :
    P.pr (fun ω => A ω ∨ B ω ∨ C ω) ≤ P.pr A + P.pr B + P.pr C := by
  classical
  let P' : FinProb Ω := finLawToProb P
  change P'.pr (fun ω => A ω ∨ B ω ∨ C ω) ≤ P'.pr A + P'.pr B + P'.pr C
  calc
    P'.pr (fun ω => A ω ∨ B ω ∨ C ω) ≤
        P'.pr A + P'.pr (fun ω => B ω ∨ C ω) :=
      FinProb.pr_union P' A (fun ω => B ω ∨ C ω)
    _ ≤ P'.pr A + P'.pr B + P'.pr C := by
      have h := FinProb.pr_union P' B C
      linarith

/-- The product of the complements of small charges is at least one minus their sum. -/
theorem clusterProd_one_sub_lower {I : Type*} [Fintype I] [DecidableEq I]
    (s : Finset I) (x : I → ℝ)
    (hx0 : ∀ i ∈ s, 0 ≤ x i) (hx1 : ∀ i ∈ s, x i ≤ 1) :
    1 - ∑ i ∈ s, x i ≤ ∏ i ∈ s, (1 - x i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | @insert i s hi ih =>
      have ih' : 1 - ∑ j ∈ s, x j ≤ ∏ j ∈ s, (1 - x j) := by
        apply ih
        · intro j hj
          exact hx0 j (Finset.mem_insert_of_mem hj)
        · intro j hj
          exact hx1 j (Finset.mem_insert_of_mem hj)
      have hxi0 : 0 ≤ x i := hx0 i (Finset.mem_insert_self _ _)
      have hxi1 : x i ≤ 1 := hx1 i (Finset.mem_insert_self _ _)
      have hsum0 : 0 ≤ ∑ j ∈ s, x j := Finset.sum_nonneg fun j hj => hx0 j
        (Finset.mem_insert_of_mem hj)
      rw [Finset.sum_insert hi, Finset.prod_insert hi]
      calc
        1 - (x i + ∑ j ∈ s, x j) ≤ (1 - x i) * (1 - ∑ j ∈ s, x j) := by
          nlinarith [mul_nonneg hxi0 hsum0]
        _ ≤ (1 - x i) * ∏ j ∈ s, (1 - x j) :=
          mul_le_mul_of_nonneg_left ih' (sub_nonneg.mpr hxi1)
        _ = (1 - x i) * ∏ j ∈ s, (1 - x j) := rfl

/-- Raw high-cluster history events inherit the product projection on a record scope. -/
theorem clusterHistory_pr_depends {κ : CConsts} {T : Stage} {k : ℕ}
    (PT : ProfiledTiling κ T k) (hPT : PT.Valid)
    (hm : PT.tiling.mode = .highSmall ∨ PT.tiling.mode = .highLarge)
    (F : ClusterHistory PT hPT hm → Prop)
    (S : Finset (ClusterRecordIndex PT hPT hm)) (W₀ : ClusterHistory PT hPT hm)
    (hF : ∀ W W', (∀ r ∈ S, W r = W' r) → (F W ↔ F W')) :
    (clusterHistoryLaw PT hPT hm).pr F =
      (clusterHistoryScopeLaw PT hPT hm S).pr
        (fun a => F ((Equiv.piEquivPiSubtypeProd
          (fun r : ClusterRecordIndex PT hPT hm => r ∈ S)
          (fun r => ClusterRecordValue r)).symm
            (a, fun r => W₀ r.1))) := by
  let P : ∀ r : ClusterRecordIndex PT hPT hm, FinLaw (ClusterRecordValue r) := fun r =>
    let Sl := clusterSolver PT hPT hm r.1.1
    ⟨Sl.lawRec PT.parameter r.2,
      Sl.lawRec_nonneg PT.parameter r.2,
      Sl.lawRec_sum PT.parameter r.2⟩
  simpa [clusterHistoryLaw, clusterHistoryScopeLaw, P] using pi_pr_depends P S F W₀ hF

/-- Raw high-cluster history expectations factor over disjoint record scopes. -/
theorem clusterHistory_E_mul_of_disjoint {κ : CConsts} {T : Stage} {k : ℕ}
    (PT : ProfiledTiling κ T k) (hPT : PT.Valid)
    (hm : PT.tiling.mode = .highSmall ∨ PT.tiling.mode = .highLarge)
    (F G : ClusterHistory PT hPT hm → ℝ)
    (S R : Finset (ClusterRecordIndex PT hPT hm))
    (hF : ∀ W W', (∀ r ∈ S, W r = W' r) → F W = F W')
    (hG : ∀ W W', (∀ r ∈ R, W r = W' r) → G W = G W')
    (hSR : Disjoint S R) :
    (clusterHistoryLaw PT hPT hm).E (fun W => F W * G W) =
      (clusterHistoryLaw PT hPT hm).E F * (clusterHistoryLaw PT hPT hm).E G := by
  let P : ∀ r : ClusterRecordIndex PT hPT hm, FinLaw (ClusterRecordValue r) := fun r =>
    let Sl := clusterSolver PT hPT hm r.1.1
    ⟨Sl.lawRec PT.parameter r.2,
      Sl.lawRec_nonneg PT.parameter r.2,
      Sl.lawRec_sum PT.parameter r.2⟩
  simpa [clusterHistoryLaw, P] using pi_E_mul_of_disjoint P F G S R hF hG hSR

/-- Raw high-cluster history events on disjoint record scopes are independent. -/
theorem clusterHistory_pr_and_of_disjoint {κ : CConsts} {T : Stage} {k : ℕ}
    (PT : ProfiledTiling κ T k) (hPT : PT.Valid)
    (hm : PT.tiling.mode = .highSmall ∨ PT.tiling.mode = .highLarge)
    (F G : ClusterHistory PT hPT hm → Prop)
    (S R : Finset (ClusterRecordIndex PT hPT hm))
    (hF : ∀ W W', (∀ r ∈ S, W r = W' r) → (F W ↔ F W'))
    (hG : ∀ W W', (∀ r ∈ R, W r = W' r) → (G W ↔ G W'))
    (hSR : Disjoint S R) :
    (clusterHistoryLaw PT hPT hm).pr (fun W => F W ∧ G W) =
      (clusterHistoryLaw PT hPT hm).pr F * (clusterHistoryLaw PT hPT hm).pr G := by
  let P : ∀ r : ClusterRecordIndex PT hPT hm, FinLaw (ClusterRecordValue r) := fun r =>
    let Sl := clusterSolver PT hPT hm r.1.1
    ⟨Sl.lawRec PT.parameter r.2,
      Sl.lawRec_nonneg PT.parameter r.2,
      Sl.lawRec_sum PT.parameter r.2⟩
  simpa [clusterHistoryLaw, P] using pi_pr_and_of_disjoint P F G S R hF hG hSR

abbrev ClusterSlicedHistory {κ : CConsts} {T : Stage} {k : ℕ}
    (PT : ProfiledTiling κ T k) (hPT : PT.Valid)
    (hm : PT.tiling.mode = .highSmall ∨ PT.tiling.mode = .highLarge) :=
  ∀ s : ClusterSlice PT, ∀ r : (clusterSolver PT hPT hm s.1).Rec,
    (clusterSolver PT hPT hm s.1).Val r

noncomputable def clusterHistoryCurryEquiv {κ : CConsts} {T : Stage} {k : ℕ}
    (PT : ProfiledTiling κ T k) (hPT : PT.Valid)
    (hm : PT.tiling.mode = .highSmall ∨ PT.tiling.mode = .highLarge) :
    ClusterHistory PT hPT hm ≃ ClusterSlicedHistory PT hPT hm where
  toFun W s r := W ⟨s, r⟩
  invFun W r := W r.1 r.2
  left_inv W := by
    funext r
    cases r
    rfl
  right_inv W := by
    funext s r
    rfl

@[simp] theorem clusterHistoryCurryEquiv_symm_apply {κ : CConsts} {T : Stage} {k : ℕ}
    (PT : ProfiledTiling κ T k) (hPT : PT.Valid)
    (hm : PT.tiling.mode = .highSmall ∨ PT.tiling.mode = .highLarge)
    (W : ClusterSlicedHistory PT hPT hm) (s : ClusterSlice PT)
    (r : (clusterSolver PT hPT hm s.1).Rec) :
    (clusterHistoryCurryEquiv PT hPT hm).symm W ⟨s, r⟩ = W s r := rfl

noncomputable def clusterSlicedHistoryLaw {κ : CConsts} {T : Stage} {k : ℕ}
    (PT : ProfiledTiling κ T k) (hPT : PT.Valid)
    (hm : PT.tiling.mode = .highSmall ∨ PT.tiling.mode = .highLarge) :
    FinLaw (ClusterSlicedHistory PT hPT hm) := by
  classical
  exact FinLaw.pi fun s => (clusterSolver PT hPT hm s.1).recLaw PT.parameter

/-- The primitive history product regroups into independent slice record laws. -/
theorem clusterHistoryLaw_map_curry {κ : CConsts} {T : Stage} {k : ℕ}
    (PT : ProfiledTiling κ T k) (hPT : PT.Valid)
    (hm : PT.tiling.mode = .highSmall ∨ PT.tiling.mode = .highLarge) :
    FinLaw.map (clusterHistoryLaw PT hPT hm) (clusterHistoryCurryEquiv PT hPT hm) =
      clusterSlicedHistoryLaw PT hPT hm := by
  classical
  apply finLaw_ext
  funext W
  rw [finLaw_map_equiv_weight]
  simp [clusterHistoryLaw, clusterSlicedHistoryLaw,
    FinLaw.pi, SliceSolver.recLaw, recordLaw, Fintype.prod_sigma]

/-- A fixed third-alarm failure has the corresponding slice solver's raw probability. -/
theorem clusterAlarm3_pr_le_slice_bad {κ : CConsts} {T : Stage} {k : ℕ}
    (PT : ProfiledTiling κ T k) (hPT : PT.Valid)
    (hm : PT.tiling.mode = .highSmall ∨ PT.tiling.mode = .highLarge)
    (a : EvenPosition T k) :
    (clusterHistoryLaw PT hPT hm).pr (fun W => clusterAlarm3 PT hPT hm W a) ≤
      Real.exp (-Real.rpow ((PT.tiling.P (patchAt PT hPT a.1)).h : ℝ)
        (1 + κ.c14)) := by
  classical
  let s := clusterSliceAt PT hPT a.1
  let S := clusterSolver PT hPT hm s.1
  let v := clusterCenterRole PT hPT hm a
  let E := clusterHistoryCurryEquiv PT hPT hm
  let F : ClusterSlicedHistory PT hPT hm → Prop := fun X =>
    clusterAlarm3 PT hPT hm (E.symm X) a
  have hTransfer : (clusterHistoryLaw PT hPT hm).pr
        (fun W => clusterAlarm3 PT hPT hm W a) =
      (clusterSlicedHistoryLaw PT hPT hm).pr F := by
    calc
      (clusterHistoryLaw PT hPT hm).pr (fun W => clusterAlarm3 PT hPT hm W a) =
          (FinLaw.map (clusterHistoryLaw PT hPT hm) E).pr F := by
            symm
            simpa [F, E] using finLaw_map_equiv_pr E (clusterHistoryLaw PT hPT hm) F
      _ = (clusterSlicedHistoryLaw PT hPT hm).pr F := by
            rw [clusterHistoryLaw_map_curry]
  have hPred : F = (fun X => ¬ S.Hgood v (X s)) := by
    funext X
    apply propext
    have hSlice : historyOnSlice (E.symm X) s = X s := by
      funext r
      change (E.symm X) ⟨s, r⟩ = X s r
      simpa [E] using clusterHistoryCurryEquiv_symm_apply PT hPT hm X s r
    change (¬ S.Hgood v (historyOnSlice (E.symm X) s)) ↔
      (¬ S.Hgood v (X s))
    rw [hSlice]
  rw [hTransfer, hPred]
  have hMarginal : (clusterSlicedHistoryLaw PT hPT hm).pr
        (fun X => ¬ S.Hgood v (X s)) =
      (S.recLaw PT.parameter).pr (fun W => ¬ S.Hgood v W) := by
    simpa [clusterSlicedHistoryLaw, S] using
      pi_pr_coordinate (fun s' => (clusterSolver PT hPT hm s'.1).recLaw PT.parameter)
        s (fun W => ¬ S.Hgood v W)
  have hSub : ∀ W : ∀ r, S.Val r, ¬ S.Hgood v W → ∃ v', ¬ S.Hgood v' W := by
    intro W hbad
    exact ⟨v, hbad⟩
  have hPr : (S.recLaw PT.parameter).pr (fun W => ¬ S.Hgood v W) ≤
      (S.recLaw PT.parameter).pr (fun W => ∃ v', ¬ S.Hgood v' W) := by
    unfold FinLaw.pr
    apply Finset.sum_le_sum
    intro W _
    by_cases hb : ¬ S.Hgood v W
    · have hany := hSub W hb
      simp [hb, hany]
    · by_cases hany : ∃ v', ¬ S.Hgood v' W
      · simp [hb, hany]
        exact (S.recLaw PT.parameter).nonneg W
      · simp [hb, hany]
  have hBad := S.Hgood_bad PT.parameter
  have hFinal :
      (S.recLaw PT.parameter).pr (fun W => ∃ v', ¬ S.Hgood v' W) ≤
        Real.exp (-Real.rpow ((PT.tiling.P s.1).h : ℝ) (1 + κ.c14)) := hBad
  have hCalc :
      (clusterSlicedHistoryLaw PT hPT hm).pr (fun X => ¬ S.Hgood v (X s)) ≤
        Real.exp (-Real.rpow ((PT.tiling.P s.1).h : ℝ) (1 + κ.c14)) := by
    calc
      (clusterSlicedHistoryLaw PT hPT hm).pr (fun X => ¬ S.Hgood v (X s)) =
          (S.recLaw PT.parameter).pr (fun W => ¬ S.Hgood v W) := hMarginal
      _ ≤ (S.recLaw PT.parameter).pr (fun W => ∃ v', ¬ S.Hgood v' W) := hPr
      _ ≤ Real.exp (-Real.rpow ((PT.tiling.P s.1).h : ℝ) (1 + κ.c14)) := hFinal
  simpa [s, clusterSliceAt] using hCalc

/-- The third cluster alarm reads only the center's consultation neighborhood. -/
theorem clusterAlarm3_indicator_depends {κ : CConsts} {T : Stage} {k : ℕ}
    (PT : ProfiledTiling κ T k) (hPT : PT.Valid)
    (hm : PT.tiling.mode = .highSmall ∨ PT.tiling.mode = .highLarge)
    (a : EvenPosition T k) :
    ClusterHistoryDependsOn
      (fun W => if clusterAlarm3 PT hPT hm W a then 1 else 0)
      (clusterConsultationScope PT hPT hm
        {⟨clusterSliceAt PT hPT a.1,
          (clusterCenterRole PT hPT hm a).1⟩}) := by
  classical
  let s := clusterSliceAt PT hPT a.1
  let v := clusterCenterRole PT hPT hm a
  let c : ClusterConsultation PT := ⟨s, v.1⟩
  intro W W' hWW
  have hlocal : ∀ r, (_root_.hammingDist
      ((clusterSolver PT hPT hm s.1).loc r) v.1 : ℝ) ≤
        10 * κ.ρ * (PT.tiling.P s.1).h →
      historyOnSlice W s r = historyOnSlice W' s r := by
    intro r hr
    let ri : ClusterRecordIndex PT hPT hm := ⟨s, r⟩
    have hmem : ri ∈ clusterConsultationScope PT hPT hm {c} := by
      simp only [clusterConsultationScope, Finset.mem_filter, Finset.mem_univ, true_and]
      refine ⟨c, by simp [c], rfl, ?_⟩
      simpa [c, s, v, ri] using hr
    exact hWW ri hmem
  have hgood := (clusterSolver PT hPT hm s.1).Hgood_local v
    (historyOnSlice W s) (historyOnSlice W' s) hlocal
  have hgood' : (clusterSolver PT hPT hm (patchAt PT hPT a.1)).Hgood v
      (historyOnSlice W s) ↔
      (clusterSolver PT hPT hm (patchAt PT hPT a.1)).Hgood v
        (historyOnSlice W' s) := by
    simpa [s, clusterSliceAt] using hgood
  have hbad : clusterAlarm3 PT hPT hm W a ↔ clusterAlarm3 PT hPT hm W' a := by
    simpa [clusterAlarm3] using not_congr hgood'
  change (if clusterAlarm3 PT hPT hm W a then 1 else 0) =
    (if clusterAlarm3 PT hPT hm W' a then 1 else 0)
  rw [hbad]

/-- One patch's record scope fixes every odd marginal read from that patch. -/
theorem clusterMarginal_eq_of_patch_scope {κ : CConsts} {T : Stage} {k : ℕ}
    (PT : ProfiledTiling κ T k) (hPT : PT.Valid)
    (hm : PT.tiling.mode = .highSmall ∨ PT.tiling.mode = .highLarge)
    (W W' : ClusterHistory PT hPT hm) (i : Fin PT.tiling.m)
    (hWW' : ∀ r ∈ clusterPatchRecordScope PT hPT hm i, W r = W' r)
    (b : OddPosition T k) (hb : patchAt PT hPT b.1 = i)
    (y : Fin (T.S.N k)) :
    clusterMarginal PT hPT hm W b y = clusterMarginal PT hPT hm W' b y := by
  have hs : (clusterSliceAt PT hPT b.1).1 = i := by
    simpa [clusterSliceAt] using hb
  have hslice := clusterHistoryOnSlice_eq_of_patch_scope PT hPT hm W W' i hWW'
    (clusterSliceAt PT hPT b.1) hs
  simp only [clusterMarginal]
  rw [hslice]

/-- Degrees read from odd marginals are fixed by the patch record scope. -/
theorem clusterDegree_eq_of_patch_scope {κ : CConsts} {T : Stage} {k : ℕ}
    (PT : ProfiledTiling κ T k) (hPT : PT.Valid)
    (hm : PT.tiling.mode = .highSmall ∨ PT.tiling.mode = .highLarge)
    (W W' : ClusterHistory PT hPT hm) (i : Fin PT.tiling.m)
    (hWW' : ∀ r ∈ clusterPatchRecordScope PT hPT hm i, W r = W' r)
    (b : OddPosition T k) (hb : patchAt PT hPT b.1 = i)
    (x : Fin (T.S.N k)) :
    clusterDegree PT hPT hm W b x = clusterDegree PT hPT hm W' b x := by
  have hmarg : clusterMarginal PT hPT hm W b = clusterMarginal PT hPT hm W' b := by
    funext y
    exact clusterMarginal_eq_of_patch_scope PT hPT hm W W' i hWW' b hb y
  simp only [clusterDegree, hmarg]

/-- The first cluster alarm reads only records in the row's patch. -/
theorem clusterAlarm1_indicator_depends_on_patch {κ : CConsts} {T : Stage} {k : ℕ}
    (PT : ProfiledTiling κ T k) (hPT : PT.Valid)
    (hm : PT.tiling.mode = .highSmall ∨ PT.tiling.mode = .highLarge)
    (a : EvenPosition T k) :
    ClusterHistoryDependsOn
      (fun W => if clusterAlarm1 PT hPT hm W a then 1 else 0)
      (clusterPatchRecordScope PT hPT hm (patchAt PT hPT a.1)) := by
  classical
  let i := patchAt PT hPT a.1
  intro W W' hWW'
  have hdeg (b : OddPosition T k) (x : Fin (T.S.N k))
      (hb : patchAt PT hPT b.1 = i) :
      clusterDegree PT hPT hm W b x = clusterDegree PT hPT hm W' b x :=
    clusterDegree_eq_of_patch_scope PT hPT hm W W' i hWW' b hb x
  have hJ0 (x : Fin (T.S.N k)) :
      clusterJ0 PT hPT hm W a x ↔ clusterJ0 PT hPT hm W' a x := by
    unfold clusterJ0
    constructor
    · rintro ⟨hx, hgate, hpos, hlo, hhi⟩
      refine ⟨hx, ?_, hpos, ?_, ?_⟩
      · intro b hb
        have hb' := (Finset.mem_filter.mp hb).2.2.1
        simpa [hdeg b x hb'] using hgate b hb
      · have hprod :
          (∏ b ∈ clusterBulkNeighbours PT hPT a, clusterDegree PT hPT hm W b x) =
            ∏ b ∈ clusterBulkNeighbours PT hPT a, clusterDegree PT hPT hm W' b x := by
          apply Finset.prod_congr rfl
          intro b hb
          exact hdeg b x ((Finset.mem_filter.mp hb).2.2.1)
        simpa [hprod] using hlo
      · have hprod :
          (∏ b ∈ clusterBulkNeighbours PT hPT a, clusterDegree PT hPT hm W b x) =
            ∏ b ∈ clusterBulkNeighbours PT hPT a, clusterDegree PT hPT hm W' b x := by
          apply Finset.prod_congr rfl
          intro b hb
          exact hdeg b x ((Finset.mem_filter.mp hb).2.2.1)
        simpa [hprod] using hhi
    · rintro ⟨hx, hgate, hpos, hlo, hhi⟩
      refine ⟨hx, ?_, hpos, ?_, ?_⟩
      · intro b hb
        have hb' := (Finset.mem_filter.mp hb).2.2.1
        simpa [hdeg b x hb'] using hgate b hb
      · have hprod :
          (∏ b ∈ clusterBulkNeighbours PT hPT a, clusterDegree PT hPT hm W' b x) =
            ∏ b ∈ clusterBulkNeighbours PT hPT a, clusterDegree PT hPT hm W b x := by
          apply Finset.prod_congr rfl
          intro b hb
          exact (hdeg b x ((Finset.mem_filter.mp hb).2.2.1)).symm
        simpa [hprod] using hlo
      · have hprod :
          (∏ b ∈ clusterBulkNeighbours PT hPT a, clusterDegree PT hPT hm W' b x) =
            ∏ b ∈ clusterBulkNeighbours PT hPT a, clusterDegree PT hPT hm W b x := by
          apply Finset.prod_congr rfl
          intro b hb
          exact (hdeg b x ((Finset.mem_filter.mp hb).2.2.1)).symm
        simpa [hprod] using hhi
  have hbad : clusterAlarm1 PT hPT hm W a ↔ clusterAlarm1 PT hPT hm W' a := by
    unfold clusterAlarm1
    have hsum :
        (∑ x, if clusterJ0 PT hPT hm W a x then 0 else
          (Law.unifCore (PT.tiling.P i).X
            (hPT.tiling_valid.patch_nonempty i).1).w x) =
        ∑ x, if clusterJ0 PT hPT hm W' a x then 0 else
          (Law.unifCore (PT.tiling.P i).X
            (hPT.tiling_valid.patch_nonempty i).1).w x := by
      apply Finset.sum_congr rfl
      intro x hx
      simp only [hJ0 x]
    rw [hsum]
  change (if clusterAlarm1 PT hPT hm W a then 1 else 0) =
    (if clusterAlarm1 PT hPT hm W' a then 1 else 0)
  rw [hbad]

/-- The interaction-cost integrand is determined by the center slice and its patch history. -/
theorem clusterInteractionCost_eq_of_patch_scope {κ : CConsts} {T : Stage} {k : ℕ}
    (PT : ProfiledTiling κ T k) (hPT : PT.Valid)
    (hm : PT.tiling.mode = .highSmall ∨ PT.tiling.mode = .highLarge)
    (W W' : ClusterHistory PT hPT hm) (a : EvenPosition T k)
    (hWW' : ∀ r ∈ clusterPatchRecordScope PT hPT hm (patchAt PT hPT a.1),
      W r = W' r) :
    clusterInteractionCost PT hPT hm W a = clusterInteractionCost PT hPT hm W' a := by
  classical
  let i := patchAt PT hPT a.1
  let s := clusterSliceAt PT hPT a.1
  have hslice : historyOnSlice W s = historyOnSlice W' s := by
    apply clusterHistoryOnSlice_eq_of_patch_scope PT hPT hm W W' i
      (by simpa [i] using hWW') s
    rfl
  have hmarginal (b : OddPosition T k) (hb : b ∈ clusterBulkNeighbours PT hPT a)
      (y : Fin (T.S.N k)) :
      clusterMarginal PT hPT hm W b y = clusterMarginal PT hPT hm W' b y := by
    have hbPatch : patchAt PT hPT b.1 = i :=
      (Finset.mem_filter.mp hb).2.2.1
    exact clusterMarginal_eq_of_patch_scope PT hPT hm W W' i
      (by simpa [i] using hWW') b hbPatch y
  have hdegree (b : OddPosition T k) (hb : b ∈ clusterBulkNeighbours PT hPT a)
      (x : Fin (T.S.N k)) :
      clusterDegree PT hPT hm W b x = clusterDegree PT hPT hm W' b x := by
    have hbPatch : patchAt PT hPT b.1 = i :=
      (Finset.mem_filter.mp hb).2.2.1
    exact clusterDegree_eq_of_patch_scope PT hPT hm W W' i
      (by simpa [i] using hWW') b hbPatch x
  have hJ0 (x : Fin (T.S.N k)) :
      clusterJ0 PT hPT hm W a x ↔ clusterJ0 PT hPT hm W' a x := by
    unfold clusterJ0
    constructor
    · rintro ⟨hx, hgate, hpos, hlo, hhi⟩
      refine ⟨hx, ?_, hpos, ?_, ?_⟩
      · intro b hb
        simpa [hdegree b hb x] using hgate b hb
      · have hprod :
          (∏ b ∈ clusterBulkNeighbours PT hPT a, clusterDegree PT hPT hm W b x) =
            ∏ b ∈ clusterBulkNeighbours PT hPT a, clusterDegree PT hPT hm W' b x := by
          apply Finset.prod_congr rfl
          intro b hb
          exact hdegree b hb x
        simpa [hprod] using hlo
      · have hprod :
          (∏ b ∈ clusterBulkNeighbours PT hPT a, clusterDegree PT hPT hm W b x) =
            ∏ b ∈ clusterBulkNeighbours PT hPT a, clusterDegree PT hPT hm W' b x := by
          apply Finset.prod_congr rfl
          intro b hb
          exact hdegree b hb x
        simpa [hprod] using hhi
    · rintro ⟨hx, hgate, hpos, hlo, hhi⟩
      refine ⟨hx, ?_, hpos, ?_, ?_⟩
      · intro b hb
        simpa [hdegree b hb x] using hgate b hb
      · have hprod :
          (∏ b ∈ clusterBulkNeighbours PT hPT a, clusterDegree PT hPT hm W' b x) =
            ∏ b ∈ clusterBulkNeighbours PT hPT a, clusterDegree PT hPT hm W b x := by
          apply Finset.prod_congr rfl
          intro b hb
          exact (hdegree b hb x).symm
        simpa [hprod] using hlo
      · have hprod :
          (∏ b ∈ clusterBulkNeighbours PT hPT a, clusterDegree PT hPT hm W' b x) =
            ∏ b ∈ clusterBulkNeighbours PT hPT a, clusterDegree PT hPT hm W b x := by
          apply Finset.prod_congr rfl
          intro b hb
          exact (hdegree b hb x).symm
        simpa [hprod] using hhi
  have hinteraction (b : OddPosition T k) (hb : b ∈ clusterBulkNeighbours PT hPT a)
      (J : Finset (Fin κ.u)) (xs : Fin κ.u → Fin (T.S.N k)) :
      clusterInteraction PT hPT hm W b J xs = clusterInteraction PT hPT hm W' b J xs := by
    unfold clusterInteraction
    apply Finset.sum_congr rfl
    intro y hy
    rw [hmarginal b hb y]
    congr 1
    apply Finset.prod_congr rfl
    intro j hj
    simp only [hdegree b hb (xs j)]
  have henvelope (xs : Fin κ.u → Fin (T.S.N k)) :
      clusterInteractionEnvelope PT hPT hm W a xs =
        clusterInteractionEnvelope PT hPT hm W' a xs := by
    unfold clusterInteractionEnvelope
    apply Finset.sum_congr rfl
    intro J hJ
    apply Finset.prod_congr rfl
    intro b hb
    apply Finset.sum_congr rfl
    intro y hy
    rw [hmarginal b hb y]
  have hsigma (Y : ClusterSliceOutcome PT s.1) (x : Fin (T.S.N k)) :
      clusterSigmaAtCenter PT hPT hm W a Y x =
        clusterSigmaAtCenter PT hPT hm W' a Y x := by
    simp only [clusterSigmaAtCenter]
    rw [hslice]
  have hintegrand (Y : ClusterSliceOutcome PT s.1) :
      clusterInteractionIntegrandAtCenter PT hPT hm W a Y =
        clusterInteractionIntegrandAtCenter PT hPT hm W' a Y := by
    unfold clusterInteractionIntegrandAtCenter
    apply Finset.sum_congr rfl
    intro xs hxs
    have hprod :
        (∏ j, clusterSigmaAtCenter PT hPT hm W a Y (xs j)) =
          ∏ j, clusterSigmaAtCenter PT hPT hm W' a Y (xs j) := by
      apply Finset.prod_congr rfl
      intro j hj
      exact hsigma Y (xs j)
    have htest :
        ((∀ j, clusterJ0 PT hPT hm W a (xs j)) ∧
          ∃ b ∈ clusterBulkNeighbours PT hPT a, ∃ J : Finset (Fin κ.u),
            2 ≤ J.card ∧ 2 * κ.ξ < |clusterInteraction PT hPT hm W b J xs|) ↔
        ((∀ j, clusterJ0 PT hPT hm W' a (xs j)) ∧
          ∃ b ∈ clusterBulkNeighbours PT hPT a, ∃ J : Finset (Fin κ.u),
            2 ≤ J.card ∧ 2 * κ.ξ < |clusterInteraction PT hPT hm W' b J xs|) := by
      constructor
      · rintro ⟨hJ, ⟨b, hb, J, hJcard, hlarge⟩⟩
        refine ⟨?_, ⟨b, hb, J, hJcard, ?_⟩⟩
        · intro j
          exact (hJ0 (xs j)).mp (hJ j)
        · rw [← hinteraction b hb J xs]
          exact hlarge
      · rintro ⟨hJ, ⟨b, hb, J, hJcard, hlarge⟩⟩
        refine ⟨?_, ⟨b, hb, J, hJcard, ?_⟩⟩
        · intro j
          exact (hJ0 (xs j)).mpr (hJ j)
        · rw [hinteraction b hb J xs]
          exact hlarge
    rw [hprod, if_congr htest rfl rfl, henvelope xs]
  calc
    clusterInteractionCost PT hPT hm W a =
        ((clusterSolver PT hPT hm s.1).refLaw (historyOnSlice W s)).E
          (clusterInteractionIntegrandAtCenter PT hPT hm W a) := by
            simpa [s] using clusterInteractionCost_eq_centerExpectation PT hPT hm W a
    _ = ((clusterSolver PT hPT hm s.1).refLaw (historyOnSlice W' s)).E
          (clusterInteractionIntegrandAtCenter PT hPT hm W' a) := by
            rw [hslice]
            unfold FinLaw.E
            apply Finset.sum_congr rfl
            intro Y hY
            exact congrArg (fun z : ℝ => ((clusterSolver PT hPT hm s.1).refLaw
              (historyOnSlice W' s)).w Y * z) (hintegrand Y)
    _ = clusterInteractionCost PT hPT hm W' a := by
            symm
            simpa [s] using clusterInteractionCost_eq_centerExpectation PT hPT hm W' a

/-- The large-interaction statistic reads only the row consultation scope. -/
theorem clusterInteractionCost_eq_of_row_scope {κ : CConsts} {T : Stage} {k : ℕ}
    (PT : ProfiledTiling κ T k) (hPT : PT.Valid)
    (hm : PT.tiling.mode = .highSmall ∨ PT.tiling.mode = .highLarge)
    (W W' : ClusterHistory PT hPT hm) (a : EvenPosition T k)
    (hWW' : ∀ r ∈ clusterConsultationScope PT hPT hm
      (clusterRowConsultations PT hPT hm a), W r = W' r) :
    clusterInteractionCost PT hPT hm W a = clusterInteractionCost PT hPT hm W' a := by
  classical
  let s := clusterSliceAt PT hPT a.1
  let S := clusterSolver PT hPT hm s.1
  let i := patchAt PT hPT a.1
  have hmarginal (b : OddPosition T k) (hb : b ∈ clusterBulkNeighbours PT hPT a)
      (y : Fin (T.S.N k)) :
      clusterMarginal PT hPT hm W b y = clusterMarginal PT hPT hm W' b y := by
    have hquery : clusterMarginalConsultation PT hPT hm b ∈
        clusterBulkMarginalConsultations PT hPT hm a :=
      Finset.mem_image.mpr ⟨b, hb, rfl⟩
    have hrow : clusterMarginalConsultation PT hPT hm b ∈ clusterRowConsultations PT hPT hm a := by
      simp only [clusterRowConsultations, Finset.mem_insert, Finset.mem_union]
      exact Or.inr (Or.inl hquery)
    have hsubset :
        clusterConsultationScope PT hPT hm {clusterMarginalConsultation PT hPT hm b} ⊆
          clusterConsultationScope PT hPT hm (clusterRowConsultations PT hPT hm a) :=
      clusterConsultationScope_mono PT hPT hm _ _ (by
        intro c hc
        have hcEq := Finset.mem_singleton.mp hc
        rw [hcEq]
        exact hrow)
    exact clusterMarginal_eq_of_consultation_scope PT hPT hm W W' b
      (fun r hr => hWW' r (hsubset hr)) y
  have hdegree (b : OddPosition T k) (hb : b ∈ clusterBulkNeighbours PT hPT a)
      (x : Fin (T.S.N k)) :
      clusterDegree PT hPT hm W b x = clusterDegree PT hPT hm W' b x := by
    have hmarginalFun : clusterMarginal PT hPT hm W b = clusterMarginal PT hPT hm W' b := by
      funext y
      exact hmarginal b hb y
    simp [clusterDegree, hmarginalFun]
  have hJ0 (x : Fin (T.S.N k)) :
      clusterJ0 PT hPT hm W a x ↔ clusterJ0 PT hPT hm W' a x := by
    unfold clusterJ0
    constructor
    · rintro ⟨hx, hgate, hpos, hlo, hhi⟩
      refine ⟨hx, ?_, hpos, ?_, ?_⟩
      · intro b hb
        simpa [hdegree b hb x] using hgate b hb
      · have hprod :
          (∏ b ∈ clusterBulkNeighbours PT hPT a, clusterDegree PT hPT hm W b x) =
            ∏ b ∈ clusterBulkNeighbours PT hPT a, clusterDegree PT hPT hm W' b x := by
          apply Finset.prod_congr rfl
          intro b hb
          exact hdegree b hb x
        simpa [hprod] using hlo
      · have hprod :
          (∏ b ∈ clusterBulkNeighbours PT hPT a, clusterDegree PT hPT hm W b x) =
            ∏ b ∈ clusterBulkNeighbours PT hPT a, clusterDegree PT hPT hm W' b x := by
          apply Finset.prod_congr rfl
          intro b hb
          exact hdegree b hb x
        simpa [hprod] using hhi
    · rintro ⟨hx, hgate, hpos, hlo, hhi⟩
      refine ⟨hx, ?_, hpos, ?_, ?_⟩
      · intro b hb
        simpa [hdegree b hb x] using hgate b hb
      · have hprod :
          (∏ b ∈ clusterBulkNeighbours PT hPT a, clusterDegree PT hPT hm W' b x) =
            ∏ b ∈ clusterBulkNeighbours PT hPT a, clusterDegree PT hPT hm W b x := by
          apply Finset.prod_congr rfl
          intro b hb
          exact (hdegree b hb x).symm
        simpa [hprod] using hlo
      · have hprod :
          (∏ b ∈ clusterBulkNeighbours PT hPT a, clusterDegree PT hPT hm W' b x) =
            ∏ b ∈ clusterBulkNeighbours PT hPT a, clusterDegree PT hPT hm W b x := by
          apply Finset.prod_congr rfl
          intro b hb
          exact (hdegree b hb x).symm
        simpa [hprod] using hhi
  have hinteraction (b : OddPosition T k) (hb : b ∈ clusterBulkNeighbours PT hPT a)
      (J : Finset (Fin κ.u)) (xs : Fin κ.u → Fin (T.S.N k)) :
      clusterInteraction PT hPT hm W b J xs = clusterInteraction PT hPT hm W' b J xs := by
    unfold clusterInteraction
    apply Finset.sum_congr rfl
    intro y hy
    rw [hmarginal b hb y]
    congr 1
    apply Finset.prod_congr rfl
    intro j hj
    simp only [hdegree b hb (xs j)]
  have henvelope (xs : Fin κ.u → Fin (T.S.N k)) :
      clusterInteractionEnvelope PT hPT hm W a xs =
        clusterInteractionEnvelope PT hPT hm W' a xs := by
    unfold clusterInteractionEnvelope
    apply Finset.sum_congr rfl
    intro J hJ
    apply Finset.prod_congr rfl
    intro b hb
    apply Finset.sum_congr rfl
    intro y hy
    rw [hmarginal b hb y]
  have htest (xs : Fin κ.u → Fin (T.S.N k)) :
      ((∀ j, clusterJ0 PT hPT hm W a (xs j)) ∧
        ∃ b ∈ clusterBulkNeighbours PT hPT a, ∃ J : Finset (Fin κ.u),
          2 ≤ J.card ∧ 2 * κ.ξ < |clusterInteraction PT hPT hm W b J xs|) ↔
      ((∀ j, clusterJ0 PT hPT hm W' a (xs j)) ∧
        ∃ b ∈ clusterBulkNeighbours PT hPT a, ∃ J : Finset (Fin κ.u),
          2 ≤ J.card ∧ 2 * κ.ξ < |clusterInteraction PT hPT hm W' b J xs|) := by
    constructor
    · rintro ⟨hJ, ⟨b, hb, J, hJcard, hlarge⟩⟩
      refine ⟨?_, ⟨b, hb, J, hJcard, ?_⟩⟩
      · intro j
        exact (hJ0 (xs j)).mp (hJ j)
      · rw [← hinteraction b hb J xs]
        exact hlarge
    · rintro ⟨hJ, ⟨b, hb, J, hJcard, hlarge⟩⟩
      refine ⟨?_, ⟨b, hb, J, hJcard, ?_⟩⟩
      · intro j
        exact (hJ0 (xs j)).mpr (hJ j)
      · rw [hinteraction b hb J xs]
        exact hlarge
  have hintegrand (Y : ClusterSliceOutcome PT s.1) :
      clusterInteractionIntegrandAtCenter PT hPT hm W a Y =
        clusterInteractionIntegrandAtCenter PT hPT hm W' a Y := by
    unfold clusterInteractionIntegrandAtCenter
    apply Finset.sum_congr rfl
    intro xs hxs
    have hprod :
        (∏ j, clusterSigmaAtCenter PT hPT hm W a Y (xs j)) =
          ∏ j, clusterSigmaAtCenter PT hPT hm W' a Y (xs j) := by
      apply Finset.prod_congr rfl
      intro j hj
      exact clusterSigmaAtCenter_eq_of_row_scope PT hPT hm W W' a Y hWW' (xs j)
    rw [hprod, if_congr (htest xs) rfl rfl, henvelope xs]
  let Z := clusterCenterStarWords PT hPT hm a
  let G := clusterCenterStarGroups PT hPT hm a
  have hgrp (z : IWord PT.tiling s.1) (hz : z ∈ Z) :
      S.groupOf z ∈ G := by
    exact Finset.mem_image.mpr ⟨z, hz, rfl⟩
  have hGroupLaw (z : IWord PT.tiling s.1) (hz : z ∈ Z) :
      (S.q (S.groupOf z) (historyOnSlice W s) =
        S.q (S.groupOf z) (historyOnSlice W' s)) ∧
      ∀ D, S.U (S.groupOf z) (historyOnSlice W s) D =
        S.U (S.groupOf z) (historyOnSlice W' s) D := by
    let c : ClusterConsultation PT := ⟨s, (groupCenter (S.groupOf z)).1⟩
    have hcStar : c ∈ clusterCenterStarConsultations PT hPT hm a := by
      exact Finset.mem_image.mpr ⟨z, hz, rfl⟩
    have hcRow : c ∈ clusterRowConsultations PT hPT hm a := by
      simp only [clusterRowConsultations, Finset.mem_insert, Finset.mem_union]
      exact Or.inr (Or.inr hcStar)
    have hsubset : clusterConsultationScope PT hPT hm {c} ⊆
        clusterConsultationScope PT hPT hm (clusterRowConsultations PT hPT hm a) :=
      clusterConsultationScope_mono PT hPT hm _ _ (by
        intro c' hc'
        have hc'Eq := Finset.mem_singleton.mp hc'
        rw [hc'Eq]
        exact hcRow)
    exact clusterSliceGroupLaws_eq_of_consultation_scope PT hPT hm s (S.groupOf z) W W'
      (fun r hr => hWW' r (hsubset hr))
  have hqLocal : ∀ g ∈ G, ∀ D,
      S.q g (historyOnSlice W s) D = S.q g (historyOnSlice W' s) D := by
    intro g hg D
    rcases Finset.mem_image.mp hg with ⟨z, hz, hzg⟩
    rw [← hzg]
    exact congrFun (hGroupLaw z hz).1 D
  have hULocal : ∀ z ∈ Z, ∀ D y,
      S.U (S.groupOf z) (historyOnSlice W s) D y =
        S.U (S.groupOf z) (historyOnSlice W' s) D y := by
    intro z hz D y
    exact congrFun ((hGroupLaw z hz).2 D) y
  have hBins : Nonempty (Bin PT.tiling s.1) := by
    by_contra hn
    haveI : IsEmpty (Bin PT.tiling s.1) := not_nonempty_iff.mp hn
    have hsum := S.q_sum (S.groupOf (solverWordAt PT hPT hm a.1)) (historyOnSlice W s)
    simp at hsum
  have hN : 0 < T.S.N k := T.S.N_pos k
  let D₀ : Group PT.tiling s.1 → Bin PT.tiling s.1 := fun _ => Classical.choice hBins
  let Y₀ : IWord PT.tiling s.1 → Fin (T.S.N k) := fun _ => ⟨0, hN⟩
  let F : (Group PT.tiling s.1 → Bin PT.tiling s.1) ×
      (IWord PT.tiling s.1 → Fin (T.S.N k)) → ℝ := fun x =>
    clusterInteractionIntegrandAtCenter PT hPT hm W' a x
  have hF : ∀ D D' Y Y', (∀ z ∈ Z, Y z = Y' z) → F (D, Y) = F (D', Y') := by
    intro D D' Y Y' hY
    change clusterInteractionIntegrandAtCenter PT hPT hm W' a (D, Y) =
      clusterInteractionIntegrandAtCenter PT hPT hm W' a (D', Y')
    unfold clusterInteractionIntegrandAtCenter
    apply Finset.sum_congr rfl
    intro xs hxs
    have hlabels : nbrLabels (clusterCenterRole PT hPT hm a).1 Y =
        nbrLabels (clusterCenterRole PT hPT hm a).1 Y' := by
      funext l
      apply hY
      exact Finset.mem_image.mpr ⟨l, Finset.mem_univ _, rfl⟩
    have hprod :
        (∏ j, clusterSigmaAtCenter PT hPT hm W' a (D, Y) (xs j)) =
          ∏ j, clusterSigmaAtCenter PT hPT hm W' a (D', Y') (xs j) := by
      apply Finset.prod_congr rfl
      intro j hj
      simp only [clusterSigmaAtCenter, clusterSliceAt]
      rw [hlabels]
    rw [hprod]
  have hKernel :
      (S.refLaw (historyOnSlice W s)).E
        (clusterInteractionIntegrandAtCenter PT hPT hm W' a) =
      (S.refLaw (historyOnSlice W' s)).E
        (clusterInteractionIntegrandAtCenter PT hPT hm W' a) := by
    simpa [SliceSolver.refLaw, S, Z, G, F] using
      (internalRefLaw_E_eq_of_local_labels
        (fun g D => S.q g (historyOnSlice W s) D)
        (fun g D => S.q g (historyOnSlice W' s) D)
        (fun g D => S.q_nonneg g (historyOnSlice W s) D)
        (fun g => S.q_sum g (historyOnSlice W s))
        (fun g D => S.q_nonneg g (historyOnSlice W' s) D)
        (fun g => S.q_sum g (historyOnSlice W' s))
        (fun g D y => S.U g (historyOnSlice W s) D y)
        (fun g D y => S.U g (historyOnSlice W' s) D y)
        (fun g D y => S.U_nonneg g (historyOnSlice W s) D y)
        (fun g D => S.U_sum g (historyOnSlice W s) D)
        (fun g D y => S.U_nonneg g (historyOnSlice W' s) D y)
        (fun g D => S.U_sum g (historyOnSlice W' s) D)
        S.groupOf G Z hgrp D₀ Y₀ F hF hqLocal hULocal)
  calc
    clusterInteractionCost PT hPT hm W a =
        (S.refLaw (historyOnSlice W s)).E
          (clusterInteractionIntegrandAtCenter PT hPT hm W a) := by
            simpa [s, S] using clusterInteractionCost_eq_centerExpectation PT hPT hm W a
    _ = (S.refLaw (historyOnSlice W s)).E
          (clusterInteractionIntegrandAtCenter PT hPT hm W' a) := by
            unfold FinLaw.E
            apply Finset.sum_congr rfl
            intro Y hY
            exact congrArg (fun z : ℝ => (S.refLaw (historyOnSlice W s)).w Y * z)
              (hintegrand Y)
    _ = (S.refLaw (historyOnSlice W' s)).E
          (clusterInteractionIntegrandAtCenter PT hPT hm W' a) := hKernel
    _ = clusterInteractionCost PT hPT hm W' a := by
            symm
            simpa [s, S] using clusterInteractionCost_eq_centerExpectation PT hPT hm W' a

/-- The second cluster alarm reads only records in the row's patch. -/
theorem clusterAlarm2_indicator_depends_on_patch {κ : CConsts} {T : Stage} {k : ℕ}
    (PT : ProfiledTiling κ T k) (hPT : PT.Valid)
    (hm : PT.tiling.mode = .highSmall ∨ PT.tiling.mode = .highLarge)
    (a : EvenPosition T k) :
    ClusterHistoryDependsOn
      (fun W => if clusterAlarm2 PT hPT hm W a then 1 else 0)
      (clusterPatchRecordScope PT hPT hm (patchAt PT hPT a.1)) := by
  intro W W' hWW'
  have hcost := clusterInteractionCost_eq_of_patch_scope PT hPT hm W W' a hWW'
  change (if clusterInteractionCost PT hPT hm W a >
      Real.exp (-100 * PT.tiling.gain (patchAt PT hPT a.1)) then 1 else 0) =
    (if clusterInteractionCost PT hPT hm W' a >
      Real.exp (-100 * PT.tiling.gain (patchAt PT hPT a.1)) then 1 else 0)
  rw [hcost]

/-- The second alarm is fixed by the row's center, bulk, and internal-star consultations. -/
theorem clusterAlarm2_indicator_depends_on_row_consultations {κ : CConsts} {T : Stage} {k : ℕ}
    (PT : ProfiledTiling κ T k) (hPT : PT.Valid)
    (hm : PT.tiling.mode = .highSmall ∨ PT.tiling.mode = .highLarge)
    (a : EvenPosition T k) :
    ClusterHistoryDependsOn
      (fun W => if clusterAlarm2 PT hPT hm W a then 1 else 0)
      (clusterConsultationScope PT hPT hm (clusterRowConsultations PT hPT hm a)) := by
  intro W W' hWW'
  have hcost := clusterInteractionCost_eq_of_row_scope PT hPT hm W W' a hWW'
  change (if clusterInteractionCost PT hPT hm W a >
      Real.exp (-100 * PT.tiling.gain (patchAt PT hPT a.1)) then 1 else 0) =
    (if clusterInteractionCost PT hPT hm W' a >
      Real.exp (-100 * PT.tiling.gain (patchAt PT hPT a.1)) then 1 else 0)
  rw [hcost]

/-- A row fails one of its three raw history alarms. -/
def clusterRowAlarm {κ : CConsts} {T : Stage} {k : ℕ}
    (PT : ProfiledTiling κ T k) (hPT : PT.Valid)
    (hm : PT.tiling.mode = .highSmall ∨ PT.tiling.mode = .highLarge)
    (W : ClusterHistory PT hPT hm) (a : EvenPosition T k) : Prop :=
  clusterAlarm1 PT hPT hm W a ∨ clusterAlarm2 PT hPT hm W a ∨ clusterAlarm3 PT hPT hm W a

/-- Exponential charge assigned to a row alarm at its patch's gain scale. -/
noncomputable def clusterRowAlarmCharge {κ : CConsts} {T : Stage} {k : ℕ}
    (PT : ProfiledTiling κ T k) (hPT : PT.Valid)
    (hm : PT.tiling.mode = .highSmall ∨ PT.tiling.mode = .highLarge)
    (a : EvenPosition T k) : ℝ :=
  Real.exp (-20 * PT.tiling.gain (patchAt PT hPT a.1))

theorem clusterRowAlarmCharge_eq_of_patch_eq {κ : CConsts} {T : Stage} {k : ℕ}
    (PT : ProfiledTiling κ T k) (hPT : PT.Valid)
    (hm : PT.tiling.mode = .highSmall ∨ PT.tiling.mode = .highLarge)
    (a a' : EvenPosition T k) (hpatch : patchAt PT hPT a.1 = patchAt PT hPT a'.1) :
    clusterRowAlarmCharge PT hPT hm a = clusterRowAlarmCharge PT hPT hm a' := by
  classical
  unfold clusterRowAlarmCharge
  rw [hpatch]

theorem clusterConsultation_touching_charge_bound {κ : CConsts} {T : Stage} {k : ℕ}
    (PT : ProfiledTiling κ T k) (hPT : PT.Valid)
    (hm : PT.tiling.mode = .highSmall ∨ PT.tiling.mode = .highLarge)
    (hκ : κ.Admissible) (c : ClusterConsultation PT)
    (hn : 2 ≤ T.S.n k)
    (hRadius : 8 ≤ 10 * κ.ρ * (PT.tiling.P c.1.1).h)
    (hThreshold : 10 ^ 7 / κ.a ≤ Real.log (T.S.n k)) :
    (((Finset.univ.filter fun a : EvenPosition T k =>
      ∃ r : ClusterRecordIndex PT hPT hm,
        r ∈ clusterConsultationScope PT hPT hm {c} ∧
        r ∈ clusterConsultationScope PT hPT hm (clusterRowConsultations PT hPT hm a)).card : ℝ) *
      Real.exp (-20 * (κ.a * ((PT.tiling.P c.1.1).h : ℝ) / 10 ^ 6))) ≤
      Real.exp (-6 * Real.log (T.S.n k)) / 2 := by
  classical
  let i := c.1.1
  let h := (PT.tiling.P i).h
  let L := Real.log (T.S.n k : ℝ)
  have ha0 : 0 < κ.a := by rw [hκ.a_eq]; exact div_pos hκ.θ_rng.1 (by norm_num)
  have ha1 : κ.a ≤ 1 := (clusterA_lt_one κ hκ).le
  have hlog : 1 < L := by
    have hC : (1 : ℝ) < 10 ^ 7 / κ.a :=
      (lt_div_iff₀ ha0).2 (by nlinarith [ha1])
    simpa [L] using lt_of_lt_of_le hC hThreshold
  have hHeight := clusterHeight_gt_log5 PT hPT hm hκ i hlog
  have hHeight' : Real.rpow L ((5 : ℕ) : ℝ) < h := by simpa [L] using hHeight
  have hhh : h ≤ T.S.n k := clusterHeight_le PT hPT i
  have hBall := clusterConsultation_ball_charge_bound κ hκ (T.S.n k) h L hn rfl
    hThreshold hHeight' hhh c.1.2.1 c.2
  let rows := Finset.univ.filter fun a : EvenPosition T k =>
    ∃ r : ClusterRecordIndex PT hPT hm,
      r ∈ clusterConsultationScope PT hPT hm {c} ∧
      r ∈ clusterConsultationScope PT hPT hm (clusterRowConsultations PT hPT hm a)
  have hcount := clusterConsultation_touchingRows_count_le_ball_product PT hPT hm c
    hRadius
  have hcountR : (rows.card : ℝ) ≤
      ((HypercubeRamsey.hammingBall c.1.2.1 2).card : ℝ) *
        ((HypercubeRamsey.hammingBall c.2
          ⌊30 * κ.ρ * (h : ℝ)⌋₊).card : ℝ) := by
    exact_mod_cast hcount
  calc
    (rows.card : ℝ) * Real.exp (-20 * (κ.a * (h : ℝ) / 10 ^ 6)) ≤
        ((HypercubeRamsey.hammingBall c.1.2.1 2).card : ℝ) *
          ((HypercubeRamsey.hammingBall c.2
            ⌊30 * κ.ρ * (h : ℝ)⌋₊).card : ℝ) *
            Real.exp (-20 * (κ.a * (h : ℝ) / 10 ^ 6)) :=
      mul_le_mul_of_nonneg_right hcountR (Real.exp_pos _).le
    _ ≤ Real.exp (-6 * L) / 2 := hBall

theorem clusterRowAlarmTouching_charge_sum_bound {κ : CConsts} {T : Stage} {k : ℕ}
    (PT : ProfiledTiling κ T k) (hPT : PT.Valid)
    (hm : PT.tiling.mode = .highSmall ∨ PT.tiling.mode = .highLarge)
    (hκ : κ.Admissible) (U : Finset (ClusterConsultation PT))
    (hn : 2 ≤ T.S.n k) (L : ℝ) (hL : L = Real.log (T.S.n k : ℝ))
    (hThreshold : 10 ^ 7 / κ.a ≤ L)
    (hRadius : ∀ c ∈ U, 8 ≤ 10 * κ.ρ * (PT.tiling.P c.1.1).h)
    (hUcard : (U.card : ℝ) ≤ (T.S.n k : ℝ) ^ 5) :
    (∑ a ∈ Finset.univ.filter (fun a : EvenPosition T k =>
        ∃ r : ClusterRecordIndex PT hPT hm,
          r ∈ clusterConsultationScope PT hPT hm U ∧
          r ∈ clusterConsultationScope PT hPT hm (clusterRowConsultations PT hPT hm a)),
      clusterRowAlarmCharge PT hPT hm a) ≤ Real.exp (-L) / 2 := by
  classical
  let rowsAt (c : ClusterConsultation PT) := Finset.univ.filter fun a : EvenPosition T k =>
    ∃ r : ClusterRecordIndex PT hPT hm,
      r ∈ clusterConsultationScope PT hPT hm {c} ∧
      r ∈ clusterConsultationScope PT hPT hm (clusterRowConsultations PT hPT hm a)
  let touched := Finset.univ.filter fun a : EvenPosition T k =>
    ∃ r : ClusterRecordIndex PT hPT hm,
      r ∈ clusterConsultationScope PT hPT hm U ∧
      r ∈ clusterConsultationScope PT hPT hm (clusterRowConsultations PT hPT hm a)
  have hsubset : touched ⊆ U.biUnion rowsAt := by
    intro a ha
    rcases Finset.mem_filter.mp ha with ⟨_, ⟨r, hrU, hrA⟩⟩
    rcases Finset.mem_filter.mp hrU with ⟨_, c, hcU, e, hdist⟩
    have hsingle : r ∈ clusterConsultationScope PT hPT hm {c} := by
      simp only [clusterConsultationScope, Finset.mem_filter, Finset.mem_univ, true_and]
      exact ⟨c, Finset.mem_singleton_self c, e, hdist⟩
    exact Finset.mem_biUnion.mpr
      ⟨c, hcU, Finset.mem_filter.mpr ⟨Finset.mem_univ _, r, hsingle, hrA⟩⟩
  have hchargeNonneg : ∀ a, 0 ≤ clusterRowAlarmCharge PT hPT hm a := by
    intro a
    unfold clusterRowAlarmCharge
    exact (Real.exp_pos _).le
  have hsumSubset :
      (∑ a ∈ touched, clusterRowAlarmCharge PT hPT hm a) ≤
        ∑ a ∈ U.biUnion rowsAt, clusterRowAlarmCharge PT hPT hm a :=
    Finset.sum_le_sum_of_subset_of_nonneg hsubset (fun a ha hmem => hchargeNonneg a)
  have hsumBiUnion := clusterSum_biUnion_le_sum_sum U rowsAt
      (clusterRowAlarmCharge PT hPT hm) hchargeNonneg
  have hsiteSum : ∀ c ∈ U,
      (∑ a ∈ rowsAt c, clusterRowAlarmCharge PT hPT hm a) ≤ Real.exp (-6 * L) / 2 := by
    intro c hc
    have hsingleCharge := clusterConsultation_touching_charge_bound PT hPT hm hκ c hn
      (hRadius c hc) (by simpa [hL] using hThreshold)
    have hchargeEq (a : EvenPosition T k) (ha : a ∈ rowsAt c) :
        clusterRowAlarmCharge PT hPT hm a = Real.exp (-20 *
          (κ.a * ((PT.tiling.P c.1.1).h : ℝ) / 10 ^ 6)) := by
      rcases Finset.mem_filter.mp ha with ⟨_, ⟨r, hrc, hra⟩⟩
      obtain ⟨hpatch, _, _⟩ :=
        clusterConsultation_rowScope_intersection_geometry PT hPT hm a c r hrc hra
      unfold clusterRowAlarmCharge
      have hgain : PT.tiling.gain (patchAt PT hPT a.1) =
          κ.a * (PT.tiling.P c.1.1).h / 10 ^ 6 := by
        rcases hm with hs | hl
        · simp [Tiling.gain, hpatch, hs]
        · simp [Tiling.gain, hpatch, hl]
      rw [hgain]
    have hsumEq : (∑ a ∈ rowsAt c, clusterRowAlarmCharge PT hPT hm a) =
        (rowsAt c).card * Real.exp (-20 *
          (κ.a * ((PT.tiling.P c.1.1).h : ℝ) / 10 ^ 6)) := by
      calc
        _ = ∑ a ∈ rowsAt c, Real.exp (-20 *
            (κ.a * ((PT.tiling.P c.1.1).h : ℝ) / 10 ^ 6)) := by
          apply Finset.sum_congr rfl
          intro a ha
          rw [hchargeEq a ha]
        _ = _ := by simp [Finset.sum_const, nsmul_eq_mul]
    rw [hsumEq]
    simpa [hL, rowsAt] using hsingleCharge
  have hsumSites : (∑ c ∈ U, ∑ a ∈ rowsAt c, clusterRowAlarmCharge PT hPT hm a) ≤
      ∑ c ∈ U, Real.exp (-6 * L) / 2 := by
    apply Finset.sum_le_sum
    intro c hc
    simpa [rowsAt] using hsiteSum c hc
  have hsumConst : (∑ c ∈ U, Real.exp (-6 * L) / 2) =
      (U.card : ℝ) * (Real.exp (-6 * L) / 2) := by
    simp [Finset.sum_const, nsmul_eq_mul]
  have hUreal : (U.card : ℝ) ≤ (T.S.n k : ℝ) ^ 5 := hUcard
  have hnExp : (T.S.n k : ℝ) = Real.exp L := by
    rw [hL]
    exact (Real.exp_log (by exact_mod_cast (show 0 < T.S.n k by omega))).symm
  calc
    _ = ∑ a ∈ touched, clusterRowAlarmCharge PT hPT hm a := rfl
    _ ≤ ∑ a ∈ U.biUnion rowsAt, clusterRowAlarmCharge PT hPT hm a := hsumSubset
    _ ≤ ∑ c ∈ U, ∑ a ∈ rowsAt c, clusterRowAlarmCharge PT hPT hm a := hsumBiUnion
    _ ≤ ∑ c ∈ U, Real.exp (-6 * L) / 2 := hsumSites
    _ = (U.card : ℝ) * (Real.exp (-6 * L) / 2) := hsumConst
    _ ≤ (T.S.n k : ℝ) ^ 5 * (Real.exp (-6 * L) / 2) :=
      mul_le_mul_of_nonneg_right hUreal (by positivity)
    _ = Real.exp (-L) / 2 := by
      rw [hnExp, clusterExp_pow_nat]
      calc
        Real.exp (5 * L) * (Real.exp (-6 * L) / 2) =
            (Real.exp (5 * L) * Real.exp (-6 * L)) / 2 := by ring
        _ = Real.exp (-L) / 2 := by
          congr 1
          rw [← Real.exp_add]
          congr 1 <;> ring

/-- Product weight of the primitive record coordinates, before conditioning on row alarms. -/
noncomputable def clusterHistoryProductWeight {κ : CConsts} {T : Stage} {k : ℕ}
    (PT : ProfiledTiling κ T k) (hPT : PT.Valid)
    (hm : PT.tiling.mode = .highSmall ∨ PT.tiling.mode = .highLarge)
    (W : ClusterHistory PT hPT hm) : ℝ :=
  ∏ r : ClusterRecordIndex PT hPT hm,
    (clusterSolver PT hPT hm r.1.1).lawRec PT.parameter r.2 (W r)

/-- Finset of histories where a particular row alarm occurs. -/
noncomputable def clusterRowAlarmEventSet {κ : CConsts} {T : Stage} {k : ℕ}
    (PT : ProfiledTiling κ T k) (hPT : PT.Valid)
    (hm : PT.tiling.mode = .highSmall ∨ PT.tiling.mode = .highLarge)
    (a : EvenPosition T k) : Finset (ClusterHistory PT hPT hm) :=
  Finset.univ.filter fun W => clusterRowAlarm PT hPT hm W a

/-- Primitive coordinates consulted by one row alarm. -/
noncomputable def clusterRowAlarmVariables {κ : CConsts} {T : Stage} {k : ℕ}
    (PT : ProfiledTiling κ T k) (hPT : PT.Valid)
    (hm : PT.tiling.mode = .highSmall ∨ PT.tiling.mode = .highLarge)
    (a : EvenPosition T k) : Finset (ClusterRecordIndex PT hPT hm) :=
  clusterConsultationScope PT hPT hm (clusterRowConsultations PT hPT hm a)

/-- Two distinct row alarms are adjacent when their primitive consultation scopes overlap. -/
def clusterRowAlarmAdjacent {κ : CConsts} {T : Stage} {k : ℕ}
    (PT : ProfiledTiling κ T k) (hPT : PT.Valid)
    (hm : PT.tiling.mode = .highSmall ∨ PT.tiling.mode = .highLarge)
    (a a' : EvenPosition T k) : Prop :=
  a ≠ a' ∧ ¬ Disjoint (clusterRowAlarmVariables PT hPT hm a)
    (clusterRowAlarmVariables PT hPT hm a')

/-- The raw history product law has the coordinate product weights used by the local lemma. -/
theorem clusterHistoryLaw_weight_eq_product {κ : CConsts} {T : Stage} {k : ℕ}
    (PT : ProfiledTiling κ T k) (hPT : PT.Valid)
    (hm : PT.tiling.mode = .highSmall ∨ PT.tiling.mode = .highLarge)
    (W : ClusterHistory PT hPT hm) :
    (clusterHistoryLaw PT hPT hm).w W = clusterHistoryProductWeight PT hPT hm W := rfl

theorem clusterHistoryProductWeight_nonneg {κ : CConsts} {T : Stage} {k : ℕ}
    (PT : ProfiledTiling κ T k) (hPT : PT.Valid)
    (hm : PT.tiling.mode = .highSmall ∨ PT.tiling.mode = .highLarge)
    (W : ClusterHistory PT hPT hm) : 0 ≤ clusterHistoryProductWeight PT hPT hm W := by
  rw [← clusterHistoryLaw_weight_eq_product PT hPT hm W]
  exact (clusterHistoryLaw PT hPT hm).nonneg W

theorem clusterHistoryProductWeight_sum_one {κ : CConsts} {T : Stage} {k : ℕ}
    (PT : ProfiledTiling κ T k) (hPT : PT.Valid)
    (hm : PT.tiling.mode = .highSmall ∨ PT.tiling.mode = .highLarge) :
    ∑ W : ClusterHistory PT hPT hm, clusterHistoryProductWeight PT hPT hm W = 1 := by
  calc
    _ = ∑ W : ClusterHistory PT hPT hm, (clusterHistoryLaw PT hPT hm).w W := by
      apply Finset.sum_congr rfl
      intro W hW
      rw [clusterHistoryLaw_weight_eq_product]
    _ = 1 := (clusterHistoryLaw PT hPT hm).sum_one

theorem clusterHistoryProductWeight_mass_eq_pr {κ : CConsts} {T : Stage} {k : ℕ}
    (PT : ProfiledTiling κ T k) (hPT : PT.Valid)
    (hm : PT.tiling.mode = .highSmall ∨ PT.tiling.mode = .highLarge)
    (A : Finset (ClusterHistory PT hPT hm)) :
    LocalLemma.mass (clusterHistoryProductWeight PT hPT hm) A =
      (clusterHistoryLaw PT hPT hm).pr (fun W => W ∈ A) := by
  classical
  unfold LocalLemma.mass
  calc
    _ = ∑ W ∈ A, (clusterHistoryLaw PT hPT hm).w W := by
      apply Finset.sum_congr rfl
      intro W hW
      rw [clusterHistoryLaw_weight_eq_product]
    _ = ∑ W ∈ Finset.univ.filter (fun W : ClusterHistory PT hPT hm => W ∈ A),
        (clusterHistoryLaw PT hPT hm).w W := by simp
    _ = ∑ W, if W ∈ A then (clusterHistoryLaw PT hPT hm).w W else 0 := by
      rw [Finset.sum_filter]
    _ = (clusterHistoryLaw PT hPT hm).pr (fun W => W ∈ A) := by
      unfold FinLaw.pr
      apply Finset.sum_congr rfl
      intro W hW
      by_cases h : W ∈ A <;> simp [h]

/-- The union of the three alarms at one row reads only its row consultation scope. -/
theorem clusterRowAlarm_indicator_depends_on_consultations {κ : CConsts} {T : Stage} {k : ℕ}
    (PT : ProfiledTiling κ T k) (hPT : PT.Valid)
    (hm : PT.tiling.mode = .highSmall ∨ PT.tiling.mode = .highLarge)
    (a : EvenPosition T k) :
    ClusterHistoryDependsOn
      (fun W => if clusterRowAlarm PT hPT hm W a then 1 else 0)
      (clusterConsultationScope PT hPT hm (clusterRowConsultations PT hPT hm a)) := by
  classical
  let c := clusterCenterConsultation PT hPT hm a
  have hBulkSubset : clusterBulkMarginalConsultations PT hPT hm a ⊆
      clusterRowConsultations PT hPT hm a := by
    intro d hd
    simp only [clusterRowConsultations, Finset.mem_insert, Finset.mem_union]
    exact Or.inr (Or.inl hd)
  have hCenter : c ∈ clusterRowConsultations PT hPT hm a := by
    simp [c, clusterRowConsultations, clusterCenterConsultation]
  have hCenterSubset :
      clusterConsultationScope PT hPT hm {c} ⊆
        clusterConsultationScope PT hPT hm (clusterRowConsultations PT hPT hm a) :=
    clusterConsultationScope_mono PT hPT hm _ _ (by
      intro d hd
      have hdEq := Finset.mem_singleton.mp hd
      rw [hdEq]
      exact hCenter)
  intro W W' hWW'
  have h1 : (if clusterAlarm1 PT hPT hm W a then (1 : ℝ) else 0) =
      (if clusterAlarm1 PT hPT hm W' a then (1 : ℝ) else 0) := by
    simpa using clusterAlarm1_indicator_depends_on_bulk_consultations PT hPT hm a W W'
      (fun r hr => hWW' r (clusterConsultationScope_mono PT hPT hm _ _ hBulkSubset hr))
  have h2 : (if clusterAlarm2 PT hPT hm W a then (1 : ℝ) else 0) =
      (if clusterAlarm2 PT hPT hm W' a then (1 : ℝ) else 0) := by
    simpa using clusterAlarm2_indicator_depends_on_row_consultations PT hPT hm a W W' hWW'
  have h3 : (if clusterAlarm3 PT hPT hm W a then (1 : ℝ) else 0) =
      (if clusterAlarm3 PT hPT hm W' a then (1 : ℝ) else 0) := by
    simpa using clusterAlarm3_indicator_depends PT hPT hm a W W'
      (fun r hr => hWW' r (hCenterSubset hr))
  have hAlarm1 : clusterAlarm1 PT hPT hm W a ↔ clusterAlarm1 PT hPT hm W' a := by
    constructor
    · intro hp
      by_contra hn
      simp [hp, hn] at h1
    · intro hp
      by_contra hn
      simp [hn, hp] at h1
  have hAlarm2 : clusterAlarm2 PT hPT hm W a ↔ clusterAlarm2 PT hPT hm W' a := by
    constructor
    · intro hp
      by_contra hn
      simp [hp, hn] at h2
    · intro hp
      by_contra hn
      simp [hn, hp] at h2
  have hAlarm3 : clusterAlarm3 PT hPT hm W a ↔ clusterAlarm3 PT hPT hm W' a := by
    constructor
    · intro hp
      by_contra hn
      simp [hp, hn] at h3
    · intro hp
      by_contra hn
      simp [hn, hp] at h3
  have hbad : clusterRowAlarm PT hPT hm W a ↔ clusterRowAlarm PT hPT hm W' a := by
    simp [clusterRowAlarm, hAlarm1, hAlarm2, hAlarm3]
  change (if clusterRowAlarm PT hPT hm W a then (1 : ℝ) else 0) =
    (if clusterRowAlarm PT hPT hm W' a then (1 : ℝ) else 0)
  exact if_congr hbad rfl rfl

/-- The row alarm predicate itself depends only on its consultation scope. -/
theorem clusterRowAlarm_depends_on_consultations {κ : CConsts} {T : Stage} {k : ℕ}
    (PT : ProfiledTiling κ T k) (hPT : PT.Valid)
    (hm : PT.tiling.mode = .highSmall ∨ PT.tiling.mode = .highLarge)
    (a : EvenPosition T k) :
    ∀ W W', (∀ r ∈ clusterConsultationScope PT hPT hm
      (clusterRowConsultations PT hPT hm a), W r = W' r) →
        (clusterRowAlarm PT hPT hm W a ↔ clusterRowAlarm PT hPT hm W' a) := by
  intro W W' hWW'
  have hInd := clusterRowAlarm_indicator_depends_on_consultations PT hPT hm a W W' hWW'
  constructor
  · intro h
    by_contra h'
    simp [h, h'] at hInd
  · intro h
    by_contra h'
    simp [h, h'] at hInd

/-- A bad row and avoidance of non-neighbor rows factor under the primitive product law. -/
theorem clusterRowAlarm_mass_inter_avoid_of_nonadjacent {κ : CConsts} {T : Stage} {k : ℕ}
    (PT : ProfiledTiling κ T k) (hPT : PT.Valid)
    (hm : PT.tiling.mode = .highSmall ∨ PT.tiling.mode = .highLarge)
    (a : EvenPosition T k) (S : Finset (EvenPosition T k))
    (haS : a ∉ S)
    (hnon : ∀ a' ∈ S, ¬ clusterRowAlarmAdjacent PT hPT hm a a') :
    LocalLemma.mass (clusterHistoryProductWeight PT hPT hm)
        (clusterRowAlarmEventSet PT hPT hm a ∩
          LocalLemma.avoid (clusterRowAlarmEventSet PT hPT hm) S) =
      LocalLemma.mass (clusterHistoryProductWeight PT hPT hm)
          (clusterRowAlarmEventSet PT hPT hm a) *
        LocalLemma.mass (clusterHistoryProductWeight PT hPT hm)
          (LocalLemma.avoid (clusterRowAlarmEventSet PT hPT hm) S) := by
  classical
  let Rec := ClusterRecordIndex PT hPT hm
  let Val : Rec → Type := ClusterRecordValue
  let q : ∀ r : Rec, Val r → ℝ := fun r v =>
    (clusterSolver PT hPT hm r.1.1).lawRec PT.parameter r.2 v
  let E : EvenPosition T k → Finset (∀ r : Rec, Val r) :=
    clusterRowAlarmEventSet PT hPT hm
  let scope : EvenPosition T k → Finset Rec := clusterRowAlarmVariables PT hPT hm
  have hq0 : ∀ r v, 0 ≤ q r v := by
    intro r v
    exact (clusterSolver PT hPT hm r.1.1).lawRec_nonneg PT.parameter r.2 v
  have hq1 : ∀ r, ∑ v, q r v = 1 := by
    intro r
    exact (clusterSolver PT hPT hm r.1.1).lawRec_sum PT.parameter r.2
  have hscope : ∀ a' (W W' : ∀ r : Rec, Val r),
      (∀ r ∈ scope a', W r = W' r) → (W ∈ E a' ↔ W' ∈ E a') := by
    intro a' W W' hWW'
    have hbad := clusterRowAlarm_depends_on_consultations PT hPT hm a' W W'
      (by simpa [scope, clusterRowAlarmVariables] using hWW')
    simpa [E, clusterRowAlarmEventSet] using hbad
  have hdisj : ∀ a' ∈ S, Disjoint (scope a) (scope a') := by
    intro a' ha'
    have hnot : ¬ clusterRowAlarmAdjacent PT hPT hm a a' := hnon a' ha'
    have hne : a ≠ a' := by
      intro haa'
      subst a'
      exact haS ha'
    by_contra hdisj
    exact hnot ⟨hne, hdisj⟩
  have hfactor := LocalLemma.mass_inter_avoid_of_disjoint_scopes
    q hq0 hq1 E scope hscope a S hdisj
  change LocalLemma.mass (fun W : ∀ r : Rec, Val r => ∏ r, q r (W r))
      (E a ∩ LocalLemma.avoid E S) =
    LocalLemma.mass (fun W : ∀ r : Rec, Val r => ∏ r, q r (W r)) (E a) *
      LocalLemma.mass (fun W : ∀ r : Rec, Val r => ∏ r, q r (W r))
        (LocalLemma.avoid E S)
  exact hfactor

/-- Raw alarm probability bounds extend to conditioning on any set of non-neighbor alarms. -/
theorem clusterRowAlarm_LLL_independent_bound_of_raw {κ : CConsts} {T : Stage} {k : ℕ}
    (PT : ProfiledTiling κ T k) (hPT : PT.Valid)
    (hm : PT.tiling.mode = .highSmall ∨ PT.tiling.mode = .highLarge)
    (p : EvenPosition T k → ℝ)
    (hp : ∀ a, (clusterHistoryLaw PT hPT hm).pr (clusterRowAlarm PT hPT hm · a) ≤ p a) :
    ∀ a (S : Finset (EvenPosition T k)), a ∉ S →
      (∀ a' ∈ S, ¬ clusterRowAlarmAdjacent PT hPT hm a a') →
      LocalLemma.mass (clusterHistoryProductWeight PT hPT hm)
          (clusterRowAlarmEventSet PT hPT hm a ∩
            LocalLemma.avoid (clusterRowAlarmEventSet PT hPT hm) S) ≤
        p a * LocalLemma.mass (clusterHistoryProductWeight PT hPT hm)
          (LocalLemma.avoid (clusterRowAlarmEventSet PT hPT hm) S) := by
  intro a S haS hnon
  have hfactor := clusterRowAlarm_mass_inter_avoid_of_nonadjacent
    PT hPT hm a S haS hnon
  have hraw : LocalLemma.mass (clusterHistoryProductWeight PT hPT hm)
      (clusterRowAlarmEventSet PT hPT hm a) =
        (clusterHistoryLaw PT hPT hm).pr (clusterRowAlarm PT hPT hm · a) := by
    simpa [clusterRowAlarmEventSet] using
      clusterHistoryProductWeight_mass_eq_pr PT hPT hm
        (clusterRowAlarmEventSet PT hPT hm a)
  have havoid : 0 ≤ LocalLemma.mass (clusterHistoryProductWeight PT hPT hm)
      (LocalLemma.avoid (clusterRowAlarmEventSet PT hPT hm) S) := by
    unfold LocalLemma.mass
    exact Finset.sum_nonneg fun W hW => clusterHistoryProductWeight_nonneg PT hPT hm W
  rw [hfactor, hraw]
  exact mul_le_mul_of_nonneg_right (hp a) havoid

/-- Row alarm events in distinct patches are independent under the raw history product law. -/
theorem clusterRowAlarm_independent_of_disjoint_patches {κ : CConsts} {T : Stage} {k : ℕ}
    (PT : ProfiledTiling κ T k) (hPT : PT.Valid)
    (hm : PT.tiling.mode = .highSmall ∨ PT.tiling.mode = .highLarge)
    (a a' : EvenPosition T k)
    (hpatch : patchAt PT hPT a.1 ≠ patchAt PT hPT a'.1) :
    (clusterHistoryLaw PT hPT hm).pr
      (fun W => clusterRowAlarm PT hPT hm W a ∧ clusterRowAlarm PT hPT hm W a') =
      (clusterHistoryLaw PT hPT hm).pr (clusterRowAlarm PT hPT hm · a) *
        (clusterHistoryLaw PT hPT hm).pr (clusterRowAlarm PT hPT hm · a') := by
  exact clusterHistory_pr_and_of_disjoint PT hPT hm
    (clusterRowAlarm PT hPT hm · a) (clusterRowAlarm PT hPT hm · a')
    (clusterConsultationScope PT hPT hm (clusterRowConsultations PT hPT hm a))
    (clusterConsultationScope PT hPT hm (clusterRowConsultations PT hPT hm a'))
    (clusterRowAlarm_depends_on_consultations PT hPT hm a)
    (clusterRowAlarm_depends_on_consultations PT hPT hm a')
    (clusterRowConsultationScopes_disjoint_of_patch_ne PT hPT hm a a' hpatch)

/-- The large-interaction cost is nonnegative, so its alarm admits Markov's bound. -/
theorem clusterInteractionCost_nonneg {κ : CConsts} {T : Stage} {k : ℕ}
    {PT : ProfiledTiling κ T k} {hPT : PT.Valid}
    {hm : PT.tiling.mode = .highSmall ∨ PT.tiling.mode = .highLarge}
    (W : ClusterHistory PT hPT hm) (a : EvenPosition T k) :
    0 ≤ clusterInteractionCost PT hPT hm W a := by
  classical
  have hMarginal (b : OddPosition T k) (y : Fin (T.S.N k)) :
      0 ≤ clusterMarginal PT hPT hm W b y := by
    let s := clusterSliceAt PT hPT b.1
    let S := clusterSolver PT hPT hm s.1
    let g := S.groupOf (solverWordAt PT hPT hm b.1)
    change 0 ≤ S.oddMarginal g (historyOnSlice W s) y
    rw [SliceSolver.oddMarginal]
    exact Finset.sum_nonneg fun D _ =>
      mul_nonneg (S.q_nonneg g (historyOnSlice W s) D)
        (S.U_nonneg g (historyOnSlice W s) D y)
  have hNominal (x y : Fin (T.S.N k)) :
      0 ≤ clusterNominalRatio PT hPT a x y := by
    have hhit : 0 ≤ hit (T.S.E k) PT.tiling.c x y := by
      unfold hit
      split_ifs <;> norm_num
    dsimp [clusterNominalRatio]
    split_ifs with hd
    · exact div_nonneg hhit hd.le
    · exact le_rfl
  have hEnvelope (xs : Fin κ.u → Fin (T.S.N k)) :
      0 ≤ clusterInteractionEnvelope PT hPT hm W a xs := by
    unfold clusterInteractionEnvelope
    apply Finset.sum_nonneg
    intro J _
    apply Finset.prod_nonneg
    intro b _
    apply Finset.sum_nonneg
    intro y _
    apply mul_nonneg
    · exact hMarginal b y
    · apply Finset.prod_nonneg
      intro j _
      exact hNominal (xs j) y
  have hSigma (I : ClusterInternalData PT) (j : Fin κ.u)
      (xs : Fin κ.u → Fin (T.S.N k)) :
      0 ≤ clusterSigma PT hPT hm W I a (xs j) := by
    let s := clusterSliceAt PT hPT a.1
    let S := clusterSolver PT hPT hm s.1
    let v := clusterCenterRole PT hPT hm a
    change 0 ≤ S.σ v (historyOnSlice W s) (nbrLabels v.1 (I s).2) (xs j)
    exact S.σ_nonneg v (historyOnSlice W s) (nbrLabels v.1 (I s).2) (xs j)
  unfold clusterInteractionCost
  rw [FinLaw.E]
  apply Finset.sum_nonneg
  intro I _
  apply mul_nonneg
  · exact (clusterInternalKernel PT hPT hm W).nonneg I
  · apply Finset.sum_nonneg
    intro xs _
    apply mul_nonneg
    · apply Finset.prod_nonneg
      intro j _
      exact hSigma I j xs
    · split_ifs
      · exact hEnvelope xs
      · exact le_rfl

/-- Finite Markov inequality for an upper-tail event. -/
theorem finLaw_pr_gt_le_E_div {Ω : Type*} [Fintype Ω]
    (P : FinLaw Ω) (f : Ω → ℝ) (hf : ∀ ω, 0 ≤ f ω)
    (t : ℝ) (ht : 0 < t) :
    P.pr (fun ω => t < f ω) ≤ P.E f / t := by
  classical
  have hscaled : t * P.pr (fun ω => t < f ω) ≤ P.E f := by
    unfold FinLaw.pr FinLaw.E
    rw [Finset.mul_sum]
    apply Finset.sum_le_sum
    intro ω hω
    by_cases h : t < f ω
    · simp [h]
      nlinarith [mul_le_mul_of_nonneg_left (le_of_lt h) (P.nonneg ω)]
    · simp [h]
      exact mul_nonneg (P.nonneg ω) (hf ω)
  apply (le_div_iff₀ ht).2
  calc
    P.pr (fun ω => t < f ω) * t = t * P.pr (fun ω => t < f ω) := by ring
    _ ≤ P.E f := hscaled

/-- The second cluster alarm is bounded by the raw interaction mean via Markov. -/
theorem clusterAlarm2_pr_le_mean_div {κ : CConsts} {T : Stage} {k : ℕ}
    {PT : ProfiledTiling κ T k} (hPT : PT.Valid)
    (hm : PT.tiling.mode = .highSmall ∨ PT.tiling.mode = .highLarge)
    (a : EvenPosition T k) :
    (clusterHistoryLaw PT hPT hm).pr (fun W => clusterAlarm2 PT hPT hm W a) ≤
      (clusterHistoryLaw PT hPT hm).E (fun W => clusterInteractionCost PT hPT hm W a) /
        Real.exp (-100 * PT.tiling.gain (patchAt PT hPT a.1)) := by
  apply finLaw_pr_gt_le_E_div (P := clusterHistoryLaw PT hPT hm)
    (f := fun W => clusterInteractionCost PT hPT hm W a)
    (t := Real.exp (-100 * PT.tiling.gain (patchAt PT hPT a.1)))
  · intro W
    exact clusterInteractionCost_nonneg W a
  · positivity

/-- The prescribed interaction mean yields the alarm-two failure probability. -/
theorem clusterAlarm2_pr_le_exp {κ : CConsts} {T : Stage} {k : ℕ}
    {PT : ProfiledTiling κ T k} (hPT : PT.Valid)
    (hm : PT.tiling.mode = .highSmall ∨ PT.tiling.mode = .highLarge)
    (a : EvenPosition T k)
    (hmean : (clusterHistoryLaw PT hPT hm).E
      (fun W => clusterInteractionCost PT hPT hm W a) ≤
        Real.exp (-300 * PT.tiling.gain (patchAt PT hPT a.1))) :
    (clusterHistoryLaw PT hPT hm).pr (fun W => clusterAlarm2 PT hPT hm W a) ≤
      Real.exp (-200 * PT.tiling.gain (patchAt PT hPT a.1)) := by
  let g := PT.tiling.gain (patchAt PT hPT a.1)
  calc
    (clusterHistoryLaw PT hPT hm).pr (fun W => clusterAlarm2 PT hPT hm W a) ≤
      (clusterHistoryLaw PT hPT hm).E
          (fun W => clusterInteractionCost PT hPT hm W a) / Real.exp (-100 * g) :=
      clusterAlarm2_pr_le_mean_div hPT hm a
    _ ≤ Real.exp (-300 * g) / Real.exp (-100 * g) :=
      div_le_div_of_nonneg_right hmean (le_of_lt (Real.exp_pos _))
    _ = Real.exp (-200 * g) := by
      rw [← Real.exp_sub]
      congr 1
      ring

/-- A consultation-local expectation factors from avoidance of alarms whose scopes are disjoint from it. -/
theorem clusterHistory_E_mul_avoid_disjoint_scope {κ : CConsts} {T : Stage} {k : ℕ}
    (PT : ProfiledTiling κ T k) (hPT : PT.Valid)
    (hm : PT.tiling.mode = .highSmall ∨ PT.tiling.mode = .highLarge)
    (F : ClusterHistory PT hPT hm → ℝ)
    (U : Finset (ClusterConsultation PT)) (S : Finset (EvenPosition T k))
    (hF : ClusterHistoryDependsOn F (clusterConsultationScope PT hPT hm U))
    (hdisj : Disjoint (clusterConsultationScope PT hPT hm U)
      (S.biUnion (clusterRowAlarmVariables PT hPT hm))) :
    (clusterHistoryLaw PT hPT hm).E (fun W => F W *
      (if W ∈ LocalLemma.avoid (clusterRowAlarmEventSet PT hPT hm) S then 1 else 0)) =
      (clusterHistoryLaw PT hPT hm).E F *
        (clusterHistoryLaw PT hPT hm).pr
          (fun W => W ∈ LocalLemma.avoid (clusterRowAlarmEventSet PT hPT hm) S) := by
  classical
  let E := clusterRowAlarmEventSet PT hPT hm
  let G : ClusterHistory PT hPT hm → ℝ := fun W =>
    if W ∈ LocalLemma.avoid E S then 1 else 0
  have havoid (W : ClusterHistory PT hPT hm) :
      W ∈ LocalLemma.avoid E S ↔ ∀ a ∈ S, ¬ clusterRowAlarm PT hPT hm W a := by
    simp [LocalLemma.avoid, E, clusterRowAlarmEventSet]
  have hG : ∀ W W',
      (∀ r ∈ S.biUnion (clusterRowAlarmVariables PT hPT hm), W r = W' r) →
      G W = G W' := by
    intro W W' hWW'
    have hsame : W ∈ LocalLemma.avoid E S ↔ W' ∈ LocalLemma.avoid E S := by
      rw [havoid, havoid]
      constructor
      · intro h a ha hbad
        have hrow := clusterRowAlarm_depends_on_consultations PT hPT hm a W W'
          (by
            intro r hr
            exact hWW' r (Finset.mem_biUnion.mpr ⟨a, ha, hr⟩))
        exact h a ha (hrow.mpr hbad)
      · intro h a ha hbad
        have hrow := clusterRowAlarm_depends_on_consultations PT hPT hm a W W'
          (by
            intro r hr
            exact hWW' r (Finset.mem_biUnion.mpr ⟨a, ha, hr⟩))
        exact h a ha (hrow.mp hbad)
    simp [G, hsame]
  have hfactor := clusterHistory_E_mul_of_disjoint PT hPT hm F G
    (clusterConsultationScope PT hPT hm U)
    (S.biUnion (clusterRowAlarmVariables PT hPT hm)) hF hG hdisj
  have hGpr : (clusterHistoryLaw PT hPT hm).E G =
      (clusterHistoryLaw PT hPT hm).pr
        (fun W => W ∈ LocalLemma.avoid E S) := by
    simp [G, FinLaw.E, FinLaw.pr, LocalLemma.avoid, Finset.sum_filter]
  simpa [G, E, hGpr] using hfactor

/-- Weighted mass of a consultation-local function under non-touching avoidance factors. -/
theorem clusterHistory_sum_mul_avoid_disjoint_scope {κ : CConsts} {T : Stage} {k : ℕ}
    (PT : ProfiledTiling κ T k) (hPT : PT.Valid)
    (hm : PT.tiling.mode = .highSmall ∨ PT.tiling.mode = .highLarge)
    (F : ClusterHistory PT hPT hm → ℝ)
    (U : Finset (ClusterConsultation PT)) (S : Finset (EvenPosition T k))
    (hF : ClusterHistoryDependsOn F (clusterConsultationScope PT hPT hm U))
    (hdisj : Disjoint (clusterConsultationScope PT hPT hm U)
      (S.biUnion (clusterRowAlarmVariables PT hPT hm))) :
    (∑ W ∈ LocalLemma.avoid (clusterRowAlarmEventSet PT hPT hm) S,
      clusterHistoryProductWeight PT hPT hm W * F W) =
      (clusterHistoryLaw PT hPT hm).E F *
        LocalLemma.mass (clusterHistoryProductWeight PT hPT hm)
          (LocalLemma.avoid (clusterRowAlarmEventSet PT hPT hm) S) := by
  classical
  let E := clusterRowAlarmEventSet PT hPT hm
  have hfactor := clusterHistory_E_mul_avoid_disjoint_scope PT hPT hm F U S hF hdisj
  have hnum :
      (∑ W ∈ LocalLemma.avoid E S, clusterHistoryProductWeight PT hPT hm W * F W) =
        (clusterHistoryLaw PT hPT hm).E
          (fun W => F W * (if W ∈ LocalLemma.avoid E S then 1 else 0)) := by
    simp [FinLaw.E, LocalLemma.avoid, Finset.sum_filter, mul_comm,
      clusterHistoryLaw_weight_eq_product]
  have hden : (clusterHistoryLaw PT hPT hm).pr
      (fun W => W ∈ LocalLemma.avoid E S) =
        LocalLemma.mass (clusterHistoryProductWeight PT hPT hm)
          (LocalLemma.avoid E S) :=
    (clusterHistoryProductWeight_mass_eq_pr PT hPT hm
      (LocalLemma.avoid E S)).symm
  calc
    _ = (clusterHistoryLaw PT hPT hm).E
        (fun W => F W * (if W ∈ LocalLemma.avoid E S then 1 else 0)) := hnum
    _ = (clusterHistoryLaw PT hPT hm).E F *
        (clusterHistoryLaw PT hPT hm).pr (fun W => W ∈ LocalLemma.avoid E S) := hfactor
    _ = _ := by rw [hden]

end HypercubeRamsey.Lane_q_s15_c1
