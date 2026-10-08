import HypercubeRamsey.S16.ProducersDefs
import HypercubeRamsey.S16.ClusterDiagnostics_q_s16_gate1
import HypercubeRamsey.S16.ClusterDiagnostics_q_s16_conc
import HypercubeRamsey.S16.ClusterDiagnostics_q_s16_scope
import HypercubeRamsey.S16.ClusterDiagnostics_q_s16_gate2

/-! Cluster diagnostics proof nodes from the S16 pool diagnosis. -/

namespace HypercubeRamsey.S16.ClusterDiagnostics

open Classical
open scoped BigOperators
open Lane_sol_fix2_s16

/-- Fill the coordinates outside a finite scope from a fixed base point. -/
noncomputable def fillScope {J Bin : Type*} (I : Finset J) (base : J → Bin) (a : I → Bin) : J → Bin :=
  fun g => if h : g ∈ I then a ⟨g, h⟩ else base g

/-- Slot-expanded empirical integral of `f` over the scope `I`, with weights
`B * P j`; the coordinates outside `I` are frozen at `base`. -/
noncomputable def scopedEmpirical {J Slot Bin : Type*} [DecidableEq J]
    [Fintype Slot] [DecidableEq Slot] [Nonempty Slot] [Fintype Bin]
    (I : Finset J) (P : J → FinLaw Bin) (base : J → Bin) (f : (J → Bin) → ℝ)
    (pool : Slot → Bin) : ℝ :=
  Lane_sol_s16_prod1.empirical_statistic
    (Lane_sol_s16_prod1.empirical_weighted_kernel (fun j : I => P j.1) (Fintype.card Bin)
      (fun a => f (fillScope I base a))) pool

/-- C1. One-slot sensitivity (from `empirical_statistic_one_slot`).
TeX 16:235–249; estimated proof: 40 lines. -/
theorem scopedEmpirical_one_slot {J Slot Bin : Type*} [DecidableEq J]
    [Fintype Slot] [DecidableEq Slot] [Nonempty Slot] [Fintype Bin] [Nonempty Bin]
    (I : Finset J) (P : J → FinLaw Bin) (base : J → Bin) (f : (J → Bin) → ℝ)
    (hf : ∀ a, 0 ≤ f a ∧ f a ≤ 1) (A : ℝ) (hA : 1 ≤ A)
    (hcap : ∀ j b, (P j).w b ≤ A / Fintype.card Bin)
    (s : Slot) (x y : Slot → Bin) (hxy : ∀ t, t ≠ s → x t = y t) :
    |scopedEmpirical I P base f x - scopedEmpirical I P base f y| ≤
      (I.card : ℝ) * A ^ I.card / Fintype.card Slot := by
  classical
  let P' : I → FinLaw Bin := fun j => P j.1
  let f' : (I → Bin) → ℝ := fun a => f (fillScope I base a)
  let F : (I → Bin) → ℝ :=
    Lane_sol_s16_prod1.empirical_weighted_kernel P' (Fintype.card Bin) f'
  have hB : (0 : ℝ) < Fintype.card Bin := by positivity
  have hA0 : 0 ≤ A := le_trans (by norm_num) hA
  have hF : ∀ a, 0 ≤ F a ∧ F a ≤ A ^ Fintype.card I := by
    simpa only [F, P', f'] using
      (Lane_sol_s16_prod1.empirical_weighted_kernel_range
        P' (Fintype.card Bin) A hB hA0
        (by intro j b; exact hcap j.1 b)
        f' (by intro a; exact hf (fillScope I base a)))
  simpa [scopedEmpirical, F, P', f'] using
    (Lane_sol_s16_prod1.empirical_statistic_one_slot
      F (A ^ Fintype.card I) (pow_nonneg hA0 _) hF s x y hxy)

/-- C2. Mean under iid uniform slots (from `empirical_statistic_mean`,
`empirical_weighted_kernel_range` and `empirical_weighted_kernel_integral`).
TeX 16:235–249; estimated proof: 50 lines. -/
theorem scopedEmpirical_mean {J Slot Bin : Type*} [DecidableEq J]
    [Fintype Slot] [DecidableEq Slot] [Nonempty Slot] [Fintype Bin] [DecidableEq Bin]
    [Nonempty Bin]
    (I : Finset J) (P : J → FinLaw Bin) (base : J → Bin) (f : (J → Bin) → ℝ)
    (hf : ∀ a, 0 ≤ f a ∧ f a ≤ 1) (A : ℝ) (hA : 1 ≤ A)
    (hcap : ∀ j b, (P j).w b ≤ A / Fintype.card Bin) :
    (FinLaw.pi (fun _ : Slot => FinLaw.uniform (Finset.univ : Finset Bin) Finset.univ_nonempty)).E
        (scopedEmpirical I P base f) ≤
      (FinLaw.pi (fun j : I => P j.1)).E (fun a => f (fillScope I base a)) +
        A ^ I.card * ((I.card : ℝ) ^ 2 / Fintype.card Slot) := by
  classical
  let P' : I → FinLaw Bin := fun j => P j.1
  let f' : (I → Bin) → ℝ := fun a => f (fillScope I base a)
  let F : (I → Bin) → ℝ :=
    Lane_sol_s16_prod1.empirical_weighted_kernel P' (Fintype.card Bin) f'
  have hB : (0 : ℝ) < Fintype.card Bin := by positivity
  have hA0 : 0 ≤ A := le_trans (by norm_num) hA
  have hF : ∀ a, 0 ≤ F a ∧ F a ≤ A ^ Fintype.card I := by
    simpa only [F, P', f'] using
      (Lane_sol_s16_prod1.empirical_weighted_kernel_range
        P' (Fintype.card Bin) A hB hA0
        (by intro j b; exact hcap j.1 b)
        f' (by intro a; exact hf (fillScope I base a)))
  have hmean := Lane_sol_s16_prod1.empirical_statistic_mean
    (Index := I) (Slot := Slot) (Bin := Bin)
    F (FinLaw.uniform (Finset.univ : Finset Bin) Finset.univ_nonempty)
    (A ^ Fintype.card I) (pow_nonneg hA0 _) hF
  change
    (FinLaw.pi (fun _ : Slot =>
      FinLaw.uniform (Finset.univ : Finset Bin) Finset.univ_nonempty)).E
        (Lane_sol_s16_prod1.empirical_statistic F) ≤
      (FinLaw.pi P').E f' +
        A ^ I.card * ((I.card : ℝ) ^ 2 / Fintype.card Slot)
  calc
    _ ≤ (FinLaw.pi (fun _ : I =>
          FinLaw.uniform (Finset.univ : Finset Bin) Finset.univ_nonempty)).E F +
          A ^ Fintype.card I * ((Fintype.card I : ℝ) ^ 2 / Fintype.card Slot) := by
      exact hmean
    _ = (FinLaw.pi P').E f' +
          A ^ I.card * ((I.card : ℝ) ^ 2 / Fintype.card Slot) := by
      rw [Lane_sol_s16_prod1.empirical_weighted_kernel_integral P' f']
      simp only [Fintype.card_coe]

/-- C3. The pool-restricted integral is bounded by the slot expansion, on
every pool (repeated images only enlarge the right side).
TeX 16:235–249; estimated proof: 150 lines. -/
theorem scopedEmpirical_restricted {J Slot Bin : Type*} [DecidableEq J]
    [Fintype Slot] [DecidableEq Slot] [Nonempty Slot] [Fintype Bin] [DecidableEq Bin]
    (I : Finset J) (Q P : J → FinLaw Bin) (base : J → Bin) (f : (J → Bin) → ℝ)
    (hf : ∀ a, 0 ≤ f a) (pool : Slot → Bin)
    (hmass : ∀ j ∈ I, 0 < ∑ b ∈ Finset.univ.image pool, (Q j).w b)
    (hP : ∀ j ∈ I, ∀ b, (P j).w b =
      (if b ∈ Finset.univ.image pool then (Q j).w b else 0) /
        ∑ b' ∈ Finset.univ.image pool, (Q j).w b') :
    (FinLaw.pi (fun j : I => P j.1)).E (fun a => f (fillScope I base a)) *
        ∏ j ∈ I, ((Fintype.card Bin : ℝ) / Fintype.card Slot *
          ∑ b ∈ Finset.univ.image pool, (Q j).w b) ≤
      scopedEmpirical I Q base f pool := by
  classical
  letI : Nonempty Bin := ⟨pool (Classical.choice (inferInstance : Nonempty Slot))⟩
  let B : ℝ := Fintype.card Bin
  let L : ℝ := Fintype.card Slot
  let QI : I → FinLaw Bin := fun j => Q j.1
  let F : (I → Bin) → ℝ := fun a => f (fillScope I base a)
  let mass : J → ℝ := fun j => ∑ b ∈ Finset.univ.image pool, (Q j).w b
  let imageWeight : (I → Bin) → ℝ := fun a =>
    ∏ i : I, if a i ∈ Finset.univ.image pool then (Q i.1).w (a i) else 0
  let imageSum : ℝ := ∑ a : I → Bin, F a * imageWeight a
  have hB : 0 < B := by
    dsimp [B]
    exact_mod_cast (Fintype.card_pos : 0 < Fintype.card Bin)
  have hL : 0 < L := by
    dsimp [L]
    exact_mod_cast (Fintype.card_pos : 0 < Fintype.card Slot)
  have hprod_attach :
      (∏ j ∈ I, (B / L * mass j)) = ∏ i : I, (B / L * mass i.1) := by
    simpa using (Finset.prod_attach I (fun j => B / L * mass j)).symm
  have hweight (a : I → Bin) :
      (∏ i : I, (P i.1).w (a i)) * ∏ i : I, (B / L * mass i.1) =
        (B / L) ^ Fintype.card I * imageWeight a := by
    calc
      _ = ∏ i : I, ((P i.1).w (a i) * (B / L * mass i.1)) := by
        rw [← Finset.prod_mul_distrib]
      _ = ∏ i : I,
            ((if a i ∈ Finset.univ.image pool then (Q i.1).w (a i) else 0) /
                mass i.1 * (B / L * mass i.1)) := by
        apply Finset.prod_congr rfl
        intro i _
        rw [hP i.1 i.2 (a i)]
      _ = ∏ i : I,
            ((B / L) * (if a i ∈ Finset.univ.image pool then
              (Q i.1).w (a i) else 0)) := by
        apply Finset.prod_congr rfl
        intro i _
        have hm : mass i.1 ≠ 0 := ne_of_gt (by
          simpa [mass] using hmass i.1 i.2)
        field_simp [hm]
      _ = (B / L) ^ Fintype.card I * imageWeight a := by
        rw [Finset.prod_mul_distrib]
        change (∏ _i : I, B / L) * imageWeight a =
          (B / L) ^ Fintype.card I * imageWeight a
        have hconst : (∏ _i : I, B / L) = (B / L) ^ Fintype.card I := by
          simp only [Finset.prod_const, Finset.card_univ]
        rw [hconst]
  have hscaled :
      (FinLaw.pi (fun j : I => P j.1)).E F *
          (∏ j ∈ I, (B / L * mass j)) =
        (B / L) ^ Fintype.card I * imageSum := by
    calc
      _ = ∑ a : I → Bin,
            ((∏ i : I, (P i.1).w (a i)) * F a) *
              (∏ i : I, (B / L * mass i.1)) := by
        rw [hprod_attach]
        change (∑ a : I → Bin, (∏ i : I, (P i.1).w (a i)) * F a) *
            (∏ i : I, (B / L * mass i.1)) = _
        rw [Finset.sum_mul]
      _ = ∑ a : I → Bin, (B / L) ^ Fintype.card I * (F a * imageWeight a) := by
        apply Finset.sum_congr rfl
        intro a _
        calc
          _ = ((∏ i : I, (P i.1).w (a i)) *
              ∏ i : I, (B / L * mass i.1)) * F a := by ring
          _ = ((B / L) ^ Fintype.card I * imageWeight a) * F a := by
            rw [hweight a]
          _ = (B / L) ^ Fintype.card I * (F a * imageWeight a) := by ring
      _ = (B / L) ^ Fintype.card I * imageSum := by
        rw [Finset.mul_sum]
  have himage : imageSum ≤
      ((Fintype.card Slot : ℝ) / B) ^ Fintype.card I *
        scopedEmpirical I Q base f pool := by
    have hh := Lane_q_s16_scope.image_product_le_empirical QI B hB F
      (fun a => hf (fillScope I base a)) pool
    simpa [imageSum, imageWeight, scopedEmpirical, QI, B, F] using hh
  have hcancel : (B / L) ^ Fintype.card I *
      ((Fintype.card Slot : ℝ) / B) ^ Fintype.card I = 1 := by
    rw [← mul_pow]
    have hratio : (B / L) * ((Fintype.card Slot : ℝ) / B) = 1 := by
      dsimp [B, L]
      field_simp [ne_of_gt hB, ne_of_gt hL]
    rw [hratio, one_pow]
  calc
    _ = (B / L) ^ Fintype.card I * imageSum := hscaled
    _ ≤ (B / L) ^ Fintype.card I *
        (((Fintype.card Slot : ℝ) / B) ^ Fintype.card I *
          scopedEmpirical I Q base f pool) :=
      mul_le_mul_of_nonneg_left himage (pow_nonneg (div_nonneg hB.le hL.le) _)
    _ = scopedEmpirical I Q base f pool := by
      rw [← mul_assoc, hcancel, one_mul]

/-- C4a. Marginalisation of a scope-local integrand.
TeX 16:235–245; estimated proof: 40 lines. -/
theorem pi_E_scope {J Bin : Type*} [Fintype J] [DecidableEq J] [Fintype Bin] [Nonempty Bin]
    (R : J → FinLaw Bin) (I : Finset J) (base : J → Bin) (f : (J → Bin) → ℝ)
    (hf : ∀ x y, (∀ g ∈ I, x g = y g) → f x = f y) :
    (FinLaw.pi R).E f = (FinLaw.pi (fun j : I => R j.1)).E (fun a => f (fillScope I base a)) := by
  classical
  let ι : {j : J // j ∈ I} → J := Subtype.val
  have hi : Function.Injective ι := fun a b h => Subtype.ext h
  have h := Lane_sol_s16_prod1.pi_injective_coordinate_E R ι hi
    (fun a => f (fillScope I base a))
  calc
    (FinLaw.pi R).E f =
        (FinLaw.pi R).E
          (fun x => f (fillScope I base (fun j : {j : J // j ∈ I} => x j.1))) := by
      unfold FinLaw.E
      apply Finset.sum_congr rfl
      intro x _
      congr 1
      apply hf
      intro g hg
      simp [fillScope, hg]
    _ = (FinLaw.pi (fun j : {j : J // j ∈ I} => R j.1)).E
          (fun a => f (fillScope I base a)) := h

/-- C4b. The same with one coordinate of the scope pinned.
TeX 16:228–245; estimated proof: 40 lines. -/
theorem pi_E_scope_pin {J Bin : Type*} [Fintype J] [DecidableEq J] [Fintype Bin]
    [DecidableEq Bin] [Nonempty Bin]
    (R : J → FinLaw Bin) (I : Finset J) (g : J) (hg : g ∈ I) (b : Bin)
    (base : J → Bin) (hbase : base g = b) (f : (J → Bin) → ℝ)
    (hf : ∀ x y, (∀ g ∈ I, x g = y g) → f x = f y) :
    (FinLaw.pi (Lane_sol_s16_prod1.coordinatePin R g b)).E f =
      (FinLaw.pi (fun j : (I.erase g) => R j.1)).E
        (fun a => f (fillScope (I.erase g) base a)) := by
  classical
  letI : Nonempty Bin := ⟨b⟩
  let f' : (J → Bin) → ℝ := fun x => f (Function.update x g b)
  have hf' : ∀ x y, (∀ j ∈ I.erase g, x j = y j) → f' x = f' y := by
    intro x y hxy
    dsimp [f']
    apply hf
    intro j hj
    by_cases hgj : j = g
    · subst j
      simp [Function.update]
    · have hj' : j ∈ I.erase g := Finset.mem_erase.mpr ⟨hgj, hj⟩
      simp [Function.update, hgj, hxy j hj']
  have hpin : (FinLaw.pi (Lane_sol_s16_prod1.coordinatePin R g b)).E f =
      (FinLaw.pi (Lane_sol_s16_prod1.coordinatePin R g b)).E f' := by
    unfold FinLaw.E
    apply Finset.sum_congr rfl
    intro x _
    by_cases hx : x g = b
    · have hu : Function.update x g b = x := by
        funext j
        by_cases hj : j = g <;> simp [Function.update, hj, hx]
      simp [f', hu]
    · have hw : (FinLaw.pi (Lane_sol_s16_prod1.coordinatePin R g b)).w x = 0 := by
        change (∏ j, (Lane_sol_s16_prod1.coordinatePin R g b j).w (x j)) = 0
        rw [← Finset.mul_prod_erase _ _ (Finset.mem_univ g)]
        simp [Lane_sol_s16_prod1.coordinatePin, FinLaw.dirac, hx]
      simp [f', hw]
  have hscope := pi_E_scope (Lane_sol_s16_prod1.coordinatePin R g b) (I.erase g)
    base f' hf'
  have hQ : (fun j : {j : J // j ∈ I.erase g} =>
      Lane_sol_s16_prod1.coordinatePin R g b j.1) =
      (fun j : {j : J // j ∈ I.erase g} => R j.1) := by
    funext j
    have hne : j.1 ≠ g := (Finset.mem_erase.mp j.2).1
    simp [Lane_sol_s16_prod1.coordinatePin, hne]
  rw [hQ] at hscope
  have hpoint (a : {j : J // j ∈ I.erase g} → Bin) :
      f' (fillScope (I.erase g) base a) = f (fillScope (I.erase g) base a) := by
    dsimp [f']
    have hgbase : fillScope (I.erase g) base a g = b := by
      simp [fillScope, hbase]
    have hu : Function.update (fillScope (I.erase g) base a) g b =
        fillScope (I.erase g) base a := by
      funext j
      by_cases hj : j = g <;> simp [Function.update, hj, hgbase]
    rw [hu]
  calc
    (FinLaw.pi (Lane_sol_s16_prod1.coordinatePin R g b)).E f =
        (FinLaw.pi (Lane_sol_s16_prod1.coordinatePin R g b)).E f' := hpin
    _ = (FinLaw.pi (fun j : {j : J // j ∈ I.erase g} => R j.1)).E
          (fun a => f (fillScope (I.erase g) base a)) := by
      calc
        _ = (FinLaw.pi (fun j : {j : J // j ∈ I.erase g} => R j.1)).E
              (fun a => f' (fillScope (I.erase g) base a)) := hscope
        _ = _ := by
          unfold FinLaw.E
          apply Finset.sum_congr rfl
          intro a _
          change (FinLaw.pi (fun j : {j : J // j ∈ I.erase g} => R j.1)).w a *
              f' (fillScope (I.erase g) base a) =
            (FinLaw.pi (fun j : {j : J // j ∈ I.erase g} => R j.1)).w a *
              f (fillScope (I.erase g) base a)
          rw [hpoint a]

/-- C4c. A pin outside the scope is invisible.
TeX 16:228–245; estimated proof: 40 lines. -/
theorem pi_E_pin_outside {J Bin : Type*} [Fintype J] [DecidableEq J] [Fintype Bin]
    [DecidableEq Bin] [Nonempty Bin]
    (R : J → FinLaw Bin) (I : Finset J) (g : J) (hg : g ∉ I) (b : Bin)
    (f : (J → Bin) → ℝ) (hf : ∀ x y, (∀ g ∈ I, x g = y g) → f x = f y) :
    (FinLaw.pi (Lane_sol_s16_prod1.coordinatePin R g b)).E f = (FinLaw.pi R).E f := by
  classical
  apply Lane_sol_s16_prod1.pi_E_local (Lane_sol_s16_prod1.coordinatePin R g b) R I f hf
  intro j hj
  have hne : j ≠ g := fun h => hg (h ▸ hj)
  simp [Lane_sol_s16_prod1.coordinatePin, hne]

/-- C4d. Injective reindexing commutes with a coordinate pin.
TeX 16:239–245; estimated proof: 40 lines. -/
theorem pi_coordinatePin_comp {I J O : Type*} [Fintype I] [DecidableEq I]
    [Fintype J] [DecidableEq J] [Fintype O] [DecidableEq O]
    (P : I → FinLaw O) (ι : J → I) (hι : Function.Injective ι) (j : J) (o : O)
    (F : (J → O) → ℝ) :
    (FinLaw.pi (Lane_sol_s16_prod1.coordinatePin P (ι j) o)).E (fun a => F (fun j' => a (ι j'))) =
      (FinLaw.pi (Lane_sol_s16_prod1.coordinatePin (fun j' => P (ι j')) j o)).E F := by
  classical
  have h := Lane_sol_s16_prod1.pi_injective_coordinate_E
    (Lane_sol_s16_prod1.coordinatePin P (ι j) o) ι hι F
  have hQ : (fun j' => Lane_sol_s16_prod1.coordinatePin P (ι j) o (ι j')) =
      Lane_sol_s16_prod1.coordinatePin (fun j' => P (ι j')) j o := by
    funext j'
    by_cases hj' : j' = j
    · subst j'
      simp [Lane_sol_s16_prod1.coordinatePin]
    · have hne : ι j' ≠ ι j := fun h => hj' (hι h)
      simp [Lane_sol_s16_prod1.coordinatePin, hj', hne]
  simpa only [hQ] using h

/-- C4e. `GroupBinProblem.pinnedFailure` as a pinned product integral.
TeX 16:228–245; estimated proof: 40 lines. -/
theorem pinned_ratio_eq {I O : Type*} [Fintype I] [DecidableEq I] [Fintype O] [DecidableEq O]
    (P : I → FinLaw O) (i : I) (o : O) (f : (I → O) → ℝ) :
    (FinLaw.pi P).E (fun a => if a i = o then f a else 0) /
        (FinLaw.pi P).pr (fun a => a i = o) =
      if (P i).w o = 0 then 0 else (FinLaw.pi (Lane_sol_s16_prod1.coordinatePin P i o)).E f := by
  have hnum : (FinLaw.pi P).E (fun a => if a i = o then f a else 0) =
      (P i).w o * (FinLaw.pi (Lane_sol_s16_prod1.coordinatePin P i o)).E f := by
    let dO : DecidableEq O := inferInstance
    have hconvert : (fun a => if a i = o then f a else 0) =
        (fun a => @ite ℝ (a i = o) (Classical.propDecidable (a i = o)) (f a) 0) := by
      funext a
      change @ite ℝ (a i = o) (dO (a i) o) (f a) 0 =
        @ite ℝ (a i = o) (Classical.propDecidable (a i = o)) (f a) 0
      have hdec : dO (a i) o = Classical.propDecidable (a i = o) :=
        Subsingleton.elim _ _
      rw [hdec]
    calc
      _ = (FinLaw.pi P).E
            (fun a => @ite ℝ (a i = o) (Classical.propDecidable (a i = o)) (f a) 0) :=
          congrArg (fun F => (FinLaw.pi P).E F) hconvert
      _ = _ := Lane_sol_s16_prod1.coordinate_pin_E P i o f
  have hden := Lane_sol_s16_prod1.pi_coordinate_pr P i o
  calc
    _ = ((P i).w o * (FinLaw.pi (Lane_sol_s16_prod1.coordinatePin P i o)).E f) /
        (FinLaw.pi P).pr (fun a => a i = o) :=
      congrArg (fun n : ℝ => n / (FinLaw.pi P).pr (fun a => a i = o)) hnum
    _ = ((P i).w o * (FinLaw.pi (Lane_sol_s16_prod1.coordinatePin P i o)).E f) /
        (P i).w o :=
      congrArg (fun d : ℝ => ((P i).w o *
        (FinLaw.pi (Lane_sol_s16_prod1.coordinatePin P i o)).E f) / d) hden
    _ = if (P i).w o = 0 then 0 else
        (FinLaw.pi (Lane_sol_s16_prod1.coordinatePin P i o)).E f := by
      by_cases hzero : (P i).w o = 0
      · simp [hzero]
      · simp [hzero]

/-- C5. A slot pin moves an expectation by at most the one-slot sensitivity.
TeX 16:247–257; estimated proof: 80 lines. -/
theorem pinLaw_E_close {Slot Bin Hist Check : Type*}
    [Fintype Slot] [DecidableEq Slot] [Fintype Bin] [DecidableEq Bin]
    [Fintype Hist] [Fintype Check] {n : ℕ} {c0 : ℝ}
    (D : CellPoolDiagnostics Slot Bin Hist Check n c0) (Φ : (Slot → Bin) → ℝ)
    (s : Slot) (b : Bin) (δ : ℝ)
    (hΦ : ∀ x y, (∀ t, t ≠ s → x t = y t) → |Φ x - Φ y| ≤ δ) :
    |(D.pinLaw s b).E Φ - D.poolLaw.E Φ| ≤ δ := by
  classical
  letI : Nonempty Bin := D.bins_nonempty
  let Ppin : Slot → FinLaw Bin := fun t =>
    if t = s then FinLaw.dirac b else D.iidSlotLaw t
  let Ψ : (Slot → Bin) → ℝ := fun x => Φ (Function.update x s b)
  have hreplace : (FinLaw.pi Ppin).E Φ = (FinLaw.pi Ppin).E Ψ := by
    unfold FinLaw.E
    apply Finset.sum_congr rfl
    intro x hx
    change (∏ t, (Ppin t).w (x t)) * Φ x =
      (∏ t, (Ppin t).w (x t)) * Φ (Function.update x s b)
    have hprod : (∏ t, (Ppin t).w (x t)) =
        (Ppin s).w (x s) * ∏ t ∈ Finset.univ.erase s, (Ppin t).w (x t) := by
      rw [← Finset.mul_prod_erase _ _ (Finset.mem_univ s)]
    rw [hprod]
    by_cases hxs : x s = b
    · have hupdate : Function.update x s b = x := by
        funext t
        by_cases ht : t = s <;> simp [ht, hxs]
      simp [hupdate]
    · have hzero : (Ppin s).w (x s) = 0 := by
        simp [Ppin, hxs, FinLaw.dirac]
      simp [hzero]
  have hlocal : ∀ x y, (∀ t, t ∈ Finset.univ.erase s → x t = y t) → Ψ x = Ψ y := by
    intro x y hxy
    change Φ (Function.update x s b) = Φ (Function.update y s b)
    congr 1
    funext t
    by_cases hts : t = s
    · subst t
      simp
    · have ht : t ∈ Finset.univ.erase s :=
        Finset.mem_erase.mpr ⟨hts, Finset.mem_univ t⟩
      have h := hxy t ht
      simp [Function.update, hts, h]
  have hsame : ∀ t, t ∈ Finset.univ.erase s → Ppin t = D.iidSlotLaw t := by
    intro t ht
    have hts : t ≠ s := (Finset.mem_erase.mp ht).1
    simp [Ppin, hts]
  have hpin : (FinLaw.pi Ppin).E Ψ = (FinLaw.pi D.iidSlotLaw).E Ψ :=
    Lane_sol_s16_prod1.pi_E_local Ppin D.iidSlotLaw (Finset.univ.erase s) Ψ hlocal hsame
  have hdiff : (FinLaw.pi D.iidSlotLaw).E Ψ - (FinLaw.pi D.iidSlotLaw).E Φ =
      (FinLaw.pi D.iidSlotLaw).E (fun x => Ψ x - Φ x) := by
    unfold FinLaw.E
    rw [← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro x hx
    ring
  change |(FinLaw.pi Ppin).E Φ - (FinLaw.pi D.iidSlotLaw).E Φ| ≤ δ
  rw [hreplace, hpin, hdiff]
  have hδ : 0 ≤ δ := by
    let x : Slot → Bin := fun _ => Classical.choice D.bins_nonempty
    have h := hΦ x x (by intro t ht; rfl)
    simpa using h
  have hpoint : ∀ x, |Ψ x - Φ x| ≤ δ := by
    intro x
    exact hΦ (Function.update x s b) x (by
      intro t ht
      simp [Function.update, ht])
  unfold FinLaw.E
  calc
    |∑ x, (FinLaw.pi D.iidSlotLaw).w x * (Ψ x - Φ x)| ≤
        ∑ x, |(FinLaw.pi D.iidSlotLaw).w x * (Ψ x - Φ x)| :=
      Finset.abs_sum_le_sum_abs _ _
    _ = ∑ x, (FinLaw.pi D.iidSlotLaw).w x * |Ψ x - Φ x| := by
      apply Finset.sum_congr rfl
      intro x hx
      rw [abs_mul, abs_of_nonneg ((FinLaw.pi D.iidSlotLaw).nonneg x)]
    _ ≤ ∑ x, (FinLaw.pi D.iidSlotLaw).w x * δ :=
      Finset.sum_le_sum fun x hx =>
        mul_le_mul_of_nonneg_left (hpoint x) ((FinLaw.pi D.iidSlotLaw).nonneg x)
    _ = δ := by rw [← Finset.sum_mul, (FinLaw.pi D.iidSlotLaw).sum_one, one_mul]

/-- C6. Per-check facts assemble the concentration record (mixed families).
TeX 16:247–257; estimated proof: 80 lines. -/
theorem pool_concentration_of_checks {Slot Bin Hist Check : Type*}
    [Fintype Slot] [DecidableEq Slot] [Fintype Bin] [DecidableEq Bin]
    [Fintype Hist] [Fintype Check] {n : ℕ} {c0 : ℝ}
    (D : CellPoolDiagnostics Slot Bin Hist Check n c0)
    (hn : 2 ≤ n) (hc0 : 0 < c0) (hslots : 0 < Fintype.card Slot)
    (heps : 0 < D.ε ∧ D.ε ≤ 1) (htol : ∀ c, 0 < D.tolerance c)
    (sens : Check → ℝ) (hsens : ∀ c, 0 < sens c)
    (hone : ∀ c s x y, (∀ t, t ≠ s → x t = y t) →
      |D.normalizer x c - D.normalizer y c| ≤ sens c)
    (hmean : ∀ c, |D.poolLaw.E (D.normalizer · c) - D.center c| + sens c ≤ D.tolerance c / 2)
    (hvar : ∀ c, (n : ℝ) ^ c0 + Real.log (8 * max 1 (Fintype.card Check : ℝ)) ≤
      2 * (D.tolerance c / 2) ^ 2 / ((Fintype.card Slot : ℝ) * sens c ^ 2))
    (hcollision : (Fintype.card Slot : ℝ) ^ 2 / Fintype.card Bin ≤
      Real.exp (-(n : ℝ) ^ c0) / 4) :
    Nonempty (PoolConcentrationHypotheses D) := by
  classical
  have hslotsReal : 0 < (Fintype.card Slot : ℝ) := by exact_mod_cast hslots
  refine ⟨{
    n_large := hn
    exponent_pos := hc0
    slots_pos := hslots
    epsilon_pos := heps
    tolerance_pos := htol
    sensitivity := fun c _ => sens c
    sensitivity_nonneg := fun c _ => (hsens c).le
    mean_close := ?_
    pinned_mean_close := ?_
    one_slot_change := ?_
    variance_budget := ?_
    collision_budget := hcollision }⟩
  · intro c
    have h := hmean c
    have hs : 0 ≤ sens c := (hsens c).le
    linarith
  · intro s b c
    have hpin := pinLaw_E_close D (D.normalizer · c) s b (sens c) (hone c s)
    have h := hmean c
    have hsum : sens c + |D.poolLaw.E (D.normalizer · c) - D.center c| ≤
        D.tolerance c / 2 := by linarith
    calc
      |(D.pinLaw s b).E (D.normalizer · c) - D.center c| ≤
          |(D.pinLaw s b).E (D.normalizer · c) - D.poolLaw.E (D.normalizer · c)| +
            |D.poolLaw.E (D.normalizer · c) - D.center c| :=
        abs_sub_le _ _ _
      _ ≤ D.tolerance c / 2 := by
        exact (add_le_add hpin (le_refl _)).trans hsum
  · exact hone
  · intro c
    have hsum : (∑ s : Slot, (fun _ : Slot => sens c) s ^ 2) =
        (Fintype.card Slot : ℝ) * sens c ^ 2 := by simp
    rw [hsum]
    exact Or.inr ⟨mul_pos hslotsReal (sq_pos_of_pos (hsens c)), hvar c⟩

/-- C7. Numerical room for star/pin checks: sensitivity, variance budget, cover.
TeX 16:247–257; estimated proof: 150 lines. -/
theorem cluster_star_budget_room : ∃ n₀ : ℕ, ∀ (n h : ℕ) (L ε Checks : ℝ),
    n₀ ≤ n → 2 ≤ n → h ≤ n → (n : ℝ) ^ (199 : ℕ) ≤ L →
    Real.rpow (n : ℝ) (-1) ≤ ε → ε ≤ 1 / 10 ^ 6 →
    Checks ≤ Real.exp (3 * (n : ℝ) ^ (1.01 : ℝ)) →
    ((h : ℝ) + 1) * n / L ≤ Real.rpow ε (1 / 4 : ℝ) / 8 / 2 ∧
    Real.rpow (n : ℝ) (1 / 2 : ℝ) + Real.log (8 * max 1 Checks) ≤
      2 * (Real.rpow ε (1 / 4 : ℝ) / 8 / 2) ^ 2 / (L * (((h : ℝ) + 1) * n / L) ^ 2) ∧
    2 * Real.sqrt ε + (n : ℝ) * (h : ℝ) ^ 2 / L + Real.rpow ε (1 / 4 : ℝ) / 8 ≤
      (1 - Real.rpow (n : ℝ) (-4)) ^ h * Real.rpow ε (1 / 4 : ℝ) := by
  refine ⟨2, ?_⟩
  intro n h L ε Checks hn hn2 hh hL hεlower hepsSmall hchecks
  let x : ℝ := n
  let τ : ℝ := Real.rpow ε (1 / 4 : ℝ)
  let σ : ℝ := ((h : ℝ) + 1) * x / L
  have hx2 : (2 : ℝ) ≤ x := by dsimp [x]; exact_mod_cast hn2
  have hx : 0 < x := by linarith
  have hx1 : 1 ≤ x := by linarith
  have hLp : 0 < L := lt_of_lt_of_le (pow_pos hx _) hL
  have hhCast : (h : ℝ) ≤ x := by dsimp [x]; exact_mod_cast hh
  have hPlus : (h : ℝ) + 1 ≤ 2 * x := by linarith
  have hρ1 : Real.rpow x (-1) = 1 / x := by
    rw [Real.rpow_eq_pow, Real.rpow_neg, Real.rpow_one, one_div] <;> exact hx.le
  have hρ4 : Real.rpow x (-4) = 1 / x ^ (4 : ℕ) := by
    rw [Real.rpow_eq_pow, Real.rpow_neg,
      show (4 : ℝ) = ((4 : ℕ) : ℝ) by norm_num,
      Real.rpow_natCast, one_div] <;> exact hx.le
  have hεpos : 0 < ε := lt_of_lt_of_le (Real.rpow_pos_of_pos hx _) hεlower
  have hεle1 : ε ≤ 1 := by linarith
  have hεlower' : 1 / x ≤ ε := by
    calc
      1 / x = Real.rpow x (-1) := hρ1.symm
      _ ≤ ε := hεlower
  have hετ : ε ≤ τ := by
    calc
      ε = Real.rpow ε 1 := (Real.rpow_one _).symm
      _ ≤ Real.rpow ε (1 / 4 : ℝ) :=
        Real.rpow_le_rpow_of_exponent_ge hεpos hεle1
          (by norm_num : (1 / 4 : ℝ) ≤ 1)
      _ = τ := rfl
  have hτpos : 0 < τ := Real.rpow_pos_of_pos hεpos _
  have hτlower : 1 / x ≤ τ := hεlower'.trans hετ
  have hpow101 : Real.rpow x (1.01 : ℝ) ≤ x ^ (2 : ℕ) := by
    simpa only [Real.rpow_eq_pow, Real.rpow_two] using
      Real.rpow_le_rpow_of_exponent_le hx1 (by norm_num : (1.01 : ℝ) ≤ 2)
  have hmax : max 1 Checks ≤ Real.exp (3 * Real.rpow x (1.01 : ℝ)) := by
    refine max_le ?_ hchecks
    exact Real.one_le_exp_iff.mpr
      (mul_nonneg (by norm_num) (Real.rpow_nonneg hx.le _))
  have hlog8 : Real.log 8 ≤ 8 := by
    have hhlog := Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 8)
    linarith
  have hlog : Real.log (8 * max 1 Checks) ≤ 8 + 3 * x ^ (2 : ℕ) := by
    calc
      _ ≤ Real.log (8 * Real.exp (3 * Real.rpow x (1.01 : ℝ))) :=
        Real.log_le_log (by positivity)
          (mul_le_mul_of_nonneg_left hmax (by norm_num))
      _ = Real.log 8 + 3 * Real.rpow x (1.01 : ℝ) := by
        rw [Real.log_mul (by norm_num : (8 : ℝ) ≠ 0)
          (Real.exp_pos _).ne', Real.log_exp]
      _ ≤ 8 + 3 * x ^ (2 : ℕ) := by nlinarith [hlog8, hpow101]
  have hroot : Real.rpow x (1 / 2 : ℝ) ≤ x := by
    simpa only [Real.rpow_eq_pow, Real.rpow_one] using
      Real.rpow_le_rpow_of_exponent_le hx1 (by norm_num : (1 / 2 : ℝ) ≤ 1)
  have hx196 : (32 : ℝ) ≤ x ^ (196 : ℕ) := by
    calc
      32 = (2 : ℝ) ^ (5 : ℕ) := by norm_num
      _ ≤ x ^ (5 : ℕ) := pow_le_pow_left₀ (by norm_num) hx2 _
      _ ≤ x ^ (196 : ℕ) := pow_le_pow_right₀ hx1 (by norm_num)
  have hx195 : (4 : ℝ) ≤ x ^ (195 : ℕ) := by
    calc
      4 = (2 : ℝ) ^ (2 : ℕ) := by norm_num
      _ ≤ x ^ (2 : ℕ) := pow_le_pow_left₀ (by norm_num) hx2 _
      _ ≤ x ^ (195 : ℕ) := pow_le_pow_right₀ hx1 (by norm_num)
  have hσbound : σ ≤ 2 / x ^ (197 : ℕ) := by
    calc
      σ = ((h : ℝ) + 1) * x / L := by rfl
      _ ≤ 2 * x ^ (2 : ℕ) / L := by
        apply div_le_div_of_nonneg_right _ hLp.le
        have hh := mul_le_mul_of_nonneg_right hPlus hx.le
        nlinarith [hh]
      _ ≤ 2 * x ^ (2 : ℕ) / x ^ (199 : ℕ) := by
        apply (div_le_div_iff₀ hLp (pow_pos hx _)).mpr
        exact mul_le_mul_of_nonneg_left hL (by positivity)
      _ = 2 / x ^ (197 : ℕ) := by field_simp [hx.ne']
  have hx197 : x ^ (197 : ℕ) = x ^ (196 : ℕ) * x := by
    rw [show (197 : ℕ) = 196 + 1 by norm_num, pow_succ]
  have h32x : 32 * x ≤ x ^ (197 : ℕ) := by
    rw [hx197]
    exact mul_le_mul_of_nonneg_right hx196 hx.le
  have hσsmall : σ ≤ 1 / (16 * x) := by
    calc
      σ ≤ 2 / x ^ (197 : ℕ) := hσbound
      _ ≤ 1 / (16 * x) := by
        apply (div_le_div_iff₀ (pow_pos hx _) (mul_pos (by norm_num) hx)).mpr
        nlinarith [h32x]
  refine ⟨?_, ?_, ?_⟩
  · calc
      σ ≤ 1 / (16 * x) := hσsmall
      _ = (1 / x) / 16 := by ring
      _ ≤ τ / 16 := div_le_div_of_nonneg_right hτlower (by norm_num)
      _ = τ / 8 / 2 := by ring
  · have hτsq₀ : (Real.rpow ε (1 / 4 : ℝ)) ^ 2 = Real.rpow ε (1 / 2 : ℝ) := by
      simp only [Real.rpow_eq_pow]
      rw [← Real.rpow_natCast, ← Real.rpow_mul hεpos.le]
      norm_num
    have hτsq : τ ^ 2 = Real.sqrt ε := by
      calc
        τ ^ 2 = Real.rpow ε (1 / 2 : ℝ) := by simpa [τ] using hτsq₀
        _ = Real.sqrt ε := (Real.sqrt_eq_rpow _).symm
    have hεsqrt : ε ≤ Real.sqrt ε := by
      have hεsq : ε ^ 2 ≤ ε := by
        calc
          ε ^ 2 = ε * ε := by rw [pow_two]
          _ ≤ ε * 1 := mul_le_mul_of_nonneg_left hεle1 hεpos.le
          _ = ε := by ring
      exact (Real.le_sqrt hεpos.le hεpos.le).mpr hεsq
    have hτsqLower : 1 / x ≤ τ ^ 2 := by rw [hτsq]; exact hεlower'.trans hεsqrt
    have hPlusSq : ((h : ℝ) + 1) ^ 2 ≤ 4 * x ^ (2 : ℕ) := by
      have hpow := pow_le_pow_left₀ (by positivity : 0 ≤ (h : ℝ) + 1) hPlus 2
      calc
        ((h : ℝ) + 1) ^ 2 ≤ (2 * x) ^ 2 := hpow
        _ = 4 * x ^ (2 : ℕ) := by ring
    have hden : 0 < 128 * ((h : ℝ) + 1) ^ 2 * x ^ (2 : ℕ) := by positivity
    have hdenUpper : 128 * ((h : ℝ) + 1) ^ 2 * x ^ (2 : ℕ) ≤
        512 * x ^ (4 : ℕ) := by
      have hh := mul_le_mul_of_nonneg_right hPlusSq (pow_nonneg hx.le (2 : ℕ))
      have hh' := mul_le_mul_of_nonneg_left hh (by norm_num : (0 : ℝ) ≤ 128)
      calc
        _ = 128 * (((h : ℝ) + 1) ^ 2 * x ^ (2 : ℕ)) := by ring
        _ ≤ 128 * ((4 * x ^ (2 : ℕ)) * x ^ (2 : ℕ)) := hh'
        _ = 512 * x ^ (4 : ℕ) := by ring
    have hx192 : (4096 : ℝ) ≤ x ^ (192 : ℕ) := by
      calc
        4096 = (2 : ℝ) ^ (12 : ℕ) := by norm_num
        _ ≤ x ^ (12 : ℕ) := pow_le_pow_left₀ (by norm_num) hx2 _
        _ ≤ x ^ (192 : ℕ) := pow_le_pow_right₀ hx1 (by norm_num)
    have hx194 : x ^ (194 : ℕ) = x ^ (192 : ℕ) * x ^ (2 : ℕ) := by
      rw [← pow_add]
    have hx198 : x ^ (198 : ℕ) = x ^ (194 : ℕ) * x ^ (4 : ℕ) := by
      rw [← pow_add]
    have hnumLower : x ^ (198 : ℕ) ≤ τ ^ 2 * L := by
      calc
        x ^ (198 : ℕ) = (1 / x) * x ^ (199 : ℕ) := by field_simp [hx.ne']
        _ ≤ τ ^ 2 * L := mul_le_mul hτsqLower hL (by positivity) (by positivity)
    have hbig : 8 * x ^ (2 : ℕ) ≤ x ^ (194 : ℕ) / 512 := by
      apply (le_div_iff₀ (by norm_num : (0 : ℝ) < 512)).mpr
      have hh := mul_le_mul_of_nonneg_right hx192 (pow_nonneg hx.le (2 : ℕ))
      calc
        8 * x ^ (2 : ℕ) * 512 = 4096 * x ^ (2 : ℕ) := by ring
        _ ≤ x ^ (192 : ℕ) * x ^ (2 : ℕ) := by nlinarith [hh]
        _ = x ^ (194 : ℕ) := by rw [hx194]
    have hbudgetRaw : x ^ (194 : ℕ) / 512 ≤ τ ^ 2 * L /
        (128 * ((h : ℝ) + 1) ^ 2 * x ^ (2 : ℕ)) := by
      apply (div_le_div_iff₀ (by norm_num : (0 : ℝ) < 512) hden).mpr
      calc
        x ^ (194 : ℕ) * (128 * ((h : ℝ) + 1) ^ 2 * x ^ (2 : ℕ)) ≤
            x ^ (194 : ℕ) * (512 * x ^ (4 : ℕ)) :=
          mul_le_mul_of_nonneg_left hdenUpper (by positivity)
        _ = 512 * x ^ (198 : ℕ) := by rw [hx198]; ring
        _ ≤ 512 * (τ ^ 2 * L) := mul_le_mul_of_nonneg_left hnumLower (by norm_num)
        _ = (τ ^ 2 * L) * 512 := by ring
    have hbudget : 8 * x ^ (2 : ℕ) ≤ τ ^ 2 * L /
        (128 * ((h : ℝ) + 1) ^ 2 * x ^ (2 : ℕ)) := hbig.trans hbudgetRaw
    have hvarEq : 2 * (τ / 8 / 2) ^ 2 / (L * σ ^ 2) =
        τ ^ 2 * L / (128 * ((h : ℝ) + 1) ^ 2 * x ^ (2 : ℕ)) := by
      dsimp [σ]
      field_simp [hLp.ne', hx.ne'] <;> ring
    have hleft : Real.rpow x (1 / 2 : ℝ) + Real.log (8 * max 1 Checks) ≤
        8 * x ^ (2 : ℕ) := by
      calc
        _ ≤ x + (8 + 3 * x ^ (2 : ℕ)) := add_le_add hroot hlog
        _ = x + 8 + 3 * x ^ (2 : ℕ) := by ring
        _ ≤ 6 * x ^ (2 : ℕ) := by
          have hxle : x ≤ x ^ (2 : ℕ) := by
            calc
              x = x * 1 := by ring
              _ ≤ x * x := mul_le_mul_of_nonneg_left hx1 hx.le
              _ = x ^ (2 : ℕ) := by ring
          have hxSq4 : 4 ≤ x ^ (2 : ℕ) := by
            calc
              4 = (2 : ℝ) ^ (2 : ℕ) := by norm_num
              _ ≤ x ^ (2 : ℕ) := pow_le_pow_left₀ (by norm_num) hx2 _
          have h8 : 8 ≤ 2 * x ^ (2 : ℕ) := by
            calc
              8 = 2 * 4 := by norm_num
              _ ≤ 2 * x ^ (2 : ℕ) := mul_le_mul_of_nonneg_left hxSq4 (by norm_num)
          calc
            x + 8 + 3 * x ^ (2 : ℕ) ≤
                x ^ (2 : ℕ) + 2 * x ^ (2 : ℕ) + 3 * x ^ (2 : ℕ) :=
              add_le_add (add_le_add hxle h8) le_rfl
            _ = 6 * x ^ (2 : ℕ) := by ring
        _ ≤ 8 * x ^ (2 : ℕ) :=
          mul_le_mul_of_nonneg_right (by norm_num : (6 : ℝ) ≤ 8) (pow_nonneg hx.le (2 : ℕ))
    have hbudgetGoal : Real.rpow x (1 / 2 : ℝ) + Real.log (8 * max 1 Checks) ≤
        2 * (τ / 8 / 2) ^ 2 / (L * σ ^ 2) := by
      rw [hvarEq]
      exact hleft.trans hbudget
    exact hbudgetGoal
  · have hτcap : τ ≤ 1 / 10 := by
      have hεquarter : ε ≤ ((1 : ℝ) / 10) ^ (4 : ℕ) := by
        exact le_trans hepsSmall (by norm_num)
      calc
        τ = Real.rpow ε (1 / 4 : ℝ) := rfl
        _ ≤ Real.rpow (((1 : ℝ) / 10) ^ (4 : ℕ)) (1 / 4 : ℝ) :=
          Real.rpow_le_rpow hεpos.le hεquarter (by norm_num)
        _ = 1 / 10 := by
          have hmul : Real.rpow (Real.rpow (1 / 10 : ℝ) 4) (1 / 4 : ℝ) =
              Real.rpow (1 / 10 : ℝ) (4 * (1 / 4 : ℝ)) :=
            (Real.rpow_mul (by norm_num : (0 : ℝ) ≤ (1 / 10)) 4 (1 / 4 : ℝ)).symm
          rw [show ((1 : ℝ) / 10) ^ (4 : ℕ) = Real.rpow (1 / 10 : ℝ) 4 by
            exact (Real.rpow_natCast _ _).symm, hmul]
          norm_num
    have hτsq : τ ^ 2 = Real.sqrt ε := by
      have hs : (Real.rpow ε (1 / 4 : ℝ)) ^ 2 = Real.rpow ε (1 / 2 : ℝ) := by
        simp only [Real.rpow_eq_pow]
        rw [← Real.rpow_natCast, ← Real.rpow_mul hεpos.le]
        norm_num
      calc
        τ ^ 2 = Real.rpow ε (1 / 2 : ℝ) := by simpa [τ] using hs
        _ = Real.sqrt ε := (Real.sqrt_eq_rpow _).symm
    have hrootSmall : 2 * Real.sqrt ε ≤ τ / 5 := by
      rw [← hτsq]
      have hh := mul_le_mul_of_nonneg_left hτcap (by positivity : 0 ≤ 2 * τ)
      nlinarith [hτpos]
    have hLerr : 4 * x ^ (4 : ℕ) ≤ L := by
      calc
        4 * x ^ (4 : ℕ) ≤ x ^ (195 : ℕ) * x ^ (4 : ℕ) :=
          mul_le_mul_of_nonneg_right hx195 (pow_nonneg hx.le _)
        _ = x ^ (199 : ℕ) := by rw [← pow_add]
        _ ≤ L := hL
    have hhSq : (h : ℝ) ^ 2 ≤ x ^ (2 : ℕ) := by
      have hh' := mul_le_mul hhCast hhCast (by positivity) (by positivity)
      simpa only [pow_two] using hh'
    have herr : x * (h : ℝ) ^ 2 / L ≤ τ / 4 := by
      have hbase : x * (h : ℝ) ^ 2 / L ≤ 1 / (4 * x) := by
        calc
          _ ≤ x ^ (3 : ℕ) / L := by
            apply div_le_div_of_nonneg_right _ hLp.le
            have hh' := mul_le_mul_of_nonneg_left hhSq hx.le
            calc
              x * (h : ℝ) ^ 2 ≤ x * x ^ (2 : ℕ) := hh'
              _ = x ^ (3 : ℕ) := by ring
        _ ≤ 1 / (4 * x) := by
            apply (div_le_div_iff₀ hLp (mul_pos (by norm_num) hx)).mpr
            have hxpow : x ^ (3 : ℕ) * (4 * x) = 4 * x ^ (4 : ℕ) := by ring
            rw [hxpow]
            simpa only [one_mul] using hLerr
      calc
        x * (h : ℝ) ^ 2 / L ≤ 1 / (4 * x) := hbase
        _ = (1 / x) / 4 := by ring
        _ ≤ τ / 4 := div_le_div_of_nonneg_right hτlower (by norm_num)
    have hfactor : (7 / 8 : ℝ) ≤ (1 - Real.rpow x (-4)) ^ h := by
      let t : ℝ := 1 / x ^ (4 : ℕ)
      have ht0 : 0 ≤ t := by dsimp [t]; positivity
      have ht1 : t ≤ 1 := by
        dsimp [t]
        apply (div_le_iff₀ (pow_pos hx _)).mpr
        simpa only [one_mul] using (one_le_pow₀ hx1 : (1 : ℝ) ≤ x ^ (4 : ℕ))
      have hbern : ∀ m : ℕ, 0 ≤ t → t ≤ 1 →
          1 - (m : ℝ) * t ≤ (1 - t) ^ m := by
        intro m
        induction m with
        | zero => intro _ _; simp
        | succ m ih =>
            intro ht0 ht1
            have hpow : (1 - t) ^ m ≤ 1 :=
              pow_le_one₀ (sub_nonneg.mpr ht1) (sub_le_self 1 ht0)
            have hprod : t * (1 - t) ^ m ≤ t := by
              simpa only [mul_one] using mul_le_mul_of_nonneg_left hpow ht0
            calc
              1 - ((m + 1 : ℕ) : ℝ) * t = (1 - (m : ℝ) * t) - t := by push_cast; ring
              _ ≤ (1 - t) ^ m - t := sub_le_sub_right (ih ht0 ht1) _
              _ ≤ (1 - t) ^ m - t * (1 - t) ^ m :=
                sub_le_sub_left hprod ((1 - t) ^ m)
              _ = (1 - t) ^ (m + 1) := by rw [pow_succ]; ring
      have hx3 : (8 : ℝ) ≤ x ^ (3 : ℕ) := by
        calc
          8 = (2 : ℝ) ^ (3 : ℕ) := by norm_num
          _ ≤ x ^ (3 : ℕ) := pow_le_pow_left₀ (by norm_num) hx2 _
      have hrecip3 : 1 / x ^ (3 : ℕ) ≤ 1 / 8 := by
        apply (div_le_div_iff₀ (pow_pos hx _) (by norm_num)).mpr
        simpa using hx3
      have hxt : x * t = 1 / x ^ (3 : ℕ) := by
        dsimp [t]
        field_simp [hx.ne']
      have hhT : (h : ℝ) * t ≤ x * t := mul_le_mul_of_nonneg_right hhCast ht0
      have hber : 1 - (h : ℝ) * t ≤ (1 - t) ^ h := hbern h ht0 ht1
      calc
        (7 / 8 : ℝ) ≤ 1 - 1 / x ^ (3 : ℕ) := by linarith
        _ = 1 - x * t := by rw [hxt]
        _ ≤ 1 - (h : ℝ) * t := sub_le_sub_left hhT _
        _ ≤ (1 - t) ^ h := hber
        _ = (1 - Real.rpow x (-4)) ^ h := by
          dsimp [t]
          have hb : 1 - 1 / x ^ (4 : ℕ) = 1 - Real.rpow x (-4) := by rw [hρ4]
          exact congrArg (fun y : ℝ => y ^ h) hb
    have hrootQuarter : 2 * Real.sqrt ε ≤ τ / 4 := by
      have hfrac : τ / 5 ≤ τ / 4 := by
        apply (div_le_div_iff₀ (by norm_num) (by norm_num)).mpr
        exact mul_le_mul_of_nonneg_left (by norm_num : (4 : ℝ) ≤ 5) hτpos.le
      exact hrootSmall.trans hfrac
    have hfracEighth : τ / 8 ≤ τ / 4 := by
      apply (div_le_div_iff₀ (by norm_num) (by norm_num)).mpr
      exact mul_le_mul_of_nonneg_left (by norm_num : (4 : ℝ) ≤ 8) hτpos.le
    have hcoverL : 2 * Real.sqrt ε + x * (h : ℝ) ^ 2 / L + τ / 8 ≤
        (7 / 8 : ℝ) * τ := by
      calc
        2 * Real.sqrt ε + x * (h : ℝ) ^ 2 / L + τ / 8 ≤ τ / 4 + τ / 4 + τ / 4 :=
          add_le_add (add_le_add hrootQuarter herr) hfracEighth
        _ = (3 / 4 : ℝ) * τ := by ring
        _ ≤ (7 / 8 : ℝ) * τ :=
          mul_le_mul_of_nonneg_right (by norm_num) hτpos.le
    have hcoverR : (7 / 8 : ℝ) * τ ≤
        (1 - Real.rpow x (-4)) ^ h * τ :=
      mul_le_mul_of_nonneg_right hfactor hτpos.le
    have hcover := hcoverL.trans hcoverR
    exact hcover

/-- C8. `cluster_normalizer_budget_room` with the total check count.
TeX 16:206–219,247–257; estimated proof: 100 lines. -/
theorem cluster_normalizer_budget_room3 : ∃ n₀ : ℕ, ∀ (n : ℕ) (L B Checks : ℝ),
    n₀ ≤ n → 2 ≤ n → 0 < B → (n : ℝ) ^ (199 : ℕ) ≤ L →
    L ^ 2 / B ≤ Real.exp (-Real.rpow (n : ℝ) (1 / 2 : ℝ)) / 4 →
    Checks ≤ Real.exp (3 * (n : ℝ) ^ (1.01 : ℝ)) →
    ((n : ℝ) * L ^ 2 / B + ((n : ℝ) + 1) / L ≤ Real.rpow (n : ℝ) (-4) / 2) ∧
    (Real.rpow (n : ℝ) (1 / 2 : ℝ) + Real.log (8 * max 1 Checks) ≤
      L * Real.rpow (n : ℝ) (-4) ^ 2 / (8 * (n : ℝ) ^ (2 : ℕ))) := by
  obtain ⟨n₀, hroom⟩ := Lane_sol_s16_prod1.logarithmic_room
    (1 / 2) 1 0 5 (by norm_num) (by norm_num) (by norm_num)
  refine ⟨n₀, ?_⟩
  intro n L B Checks hn hn2 hB hL hcollision hchecks
  let x : ℝ := n
  have hx2 : (2 : ℝ) ≤ x := by dsimp [x]; exact_mod_cast hn2
  have hx : 0 < x := by linarith
  have hx1 : 1 ≤ x := by linarith
  have hLp : 0 < L := lt_of_lt_of_le (pow_pos hx _) hL
  have hρ : Real.rpow x (-4) = 1 / x ^ (4 : ℕ) := by
    rw [Real.rpow_eq_pow, Real.rpow_neg,
      show (4 : ℝ) = ((4 : ℕ) : ℝ) by norm_num,
      Real.rpow_natCast, one_div] <;> exact hx.le
  have hsmall : Real.exp (-Real.rpow x (1 / 2 : ℝ)) ≤ 1 / x ^ (5 : ℕ) := by
    have hr := hroom n hn
    simp only [one_mul, zero_add] at hr
    have he := Real.exp_le_exp.mpr (neg_le_neg hr)
    have he5 : Real.exp (5 * Real.log x) = x ^ (5 : ℕ) := by
      simpa only [Nat.cast_ofNat, Real.exp_log hx] using Real.exp_nat_mul (Real.log x) 5
    change Real.exp (-Real.rpow x (1 / 2 : ℝ)) ≤ Real.exp (-(5 * Real.log x)) at he
    rw [Real.exp_neg (5 * Real.log x), he5] at he
    simpa only [one_div] using he
  have h194 : (8 : ℝ) ≤ x ^ (194 : ℕ) := by
    calc
      8 = (2 : ℝ) ^ (3 : ℕ) := by norm_num
      _ ≤ x ^ (3 : ℕ) := pow_le_pow_left₀ (by norm_num) hx2 _
      _ ≤ x ^ (194 : ℕ) := pow_le_pow_right₀ hx1 (by norm_num)
  have h187 : (2048 : ℝ) ≤ x ^ (187 : ℕ) := by
    calc
      2048 = (2 : ℝ) ^ (11 : ℕ) := by norm_num
      _ ≤ x ^ (11 : ℕ) := pow_le_pow_left₀ (by norm_num) hx2 _
      _ ≤ x ^ (187 : ℕ) := pow_le_pow_right₀ hx1 (by norm_num)
  have hpinL : 8 * x ^ (5 : ℕ) ≤ L := by
    calc
      _ ≤ x ^ (194 : ℕ) * x ^ (5 : ℕ) :=
        mul_le_mul_of_nonneg_right h194 (pow_nonneg hx.le _)
      _ = x ^ (199 : ℕ) := by rw [← pow_add]
      _ ≤ L := hL
  have hvarL : 2048 * x ^ (12 : ℕ) ≤ L := by
    calc
      _ ≤ x ^ (187 : ℕ) * x ^ (12 : ℕ) :=
        mul_le_mul_of_nonneg_right h187 (pow_nonneg hx.le _)
      _ = x ^ (199 : ℕ) := by rw [← pow_add]
      _ ≤ L := hL
  refine ⟨?_, ?_⟩
  · have hpin : (x + 1) / L ≤ Real.rpow x (-4) / 4 := by
      calc
        _ ≤ (2 * x) / L := div_le_div_of_nonneg_right (by linarith) hLp.le
        _ ≤ (2 * x) / (8 * x ^ (5 : ℕ)) :=
          div_le_div_of_nonneg_left (by positivity) (by positivity) hpinL
        _ = _ := by rw [hρ]; field_simp <;> ring
    have hcoll : x * L ^ 2 / B ≤ Real.rpow x (-4) / 4 := by
      calc
        _ = x * (L ^ 2 / B) := by ring
        _ ≤ x * (Real.exp (-Real.rpow x (1 / 2 : ℝ)) / 4) :=
          mul_le_mul_of_nonneg_left hcollision hx.le
        _ ≤ x * ((1 / x ^ (5 : ℕ)) / 4) :=
          mul_le_mul_of_nonneg_left (div_le_div_of_nonneg_right hsmall (by norm_num)) hx.le
        _ = _ := by rw [hρ]; field_simp <;> ring
    dsimp only [x] at *
    linarith only [hpin, hcoll]
  · have hpow101 : Real.rpow x (1.01 : ℝ) ≤ x ^ (2 : ℕ) := by
      simpa only [Real.rpow_eq_pow, Real.rpow_two] using
        Real.rpow_le_rpow_of_exponent_le hx1 (by norm_num : (1.01 : ℝ) ≤ 2)
    have hmax : max 1 Checks ≤ Real.exp (3 * Real.rpow x (1.01 : ℝ)) := by
      refine max_le ?_ hchecks
      exact Real.one_le_exp_iff.mpr
        (mul_nonneg (by norm_num) (Real.rpow_nonneg hx.le _))
    have hlog8 : Real.log 8 ≤ 8 := by
      have hh := Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 8)
      linarith
    have hlog : Real.log (8 * max 1 Checks) ≤ 8 + 3 * x ^ (2 : ℕ) := by
      calc
        _ ≤ Real.log (8 * Real.exp (3 * Real.rpow x (1.01 : ℝ))) :=
          Real.log_le_log (by positivity)
            (mul_le_mul_of_nonneg_left hmax (by norm_num))
        _ = Real.log 8 + 3 * Real.rpow x (1.01 : ℝ) := by
          rw [Real.log_mul (by norm_num : (8 : ℝ) ≠ 0)
            (Real.exp_pos _).ne', Real.log_exp]
        _ ≤ 8 + 3 * x ^ (2 : ℕ) := by nlinarith [hlog8, hpow101]
    have hroot : Real.rpow x (1 / 2 : ℝ) ≤ x := by
      simpa only [Real.rpow_eq_pow, Real.rpow_one] using
        Real.rpow_le_rpow_of_exponent_le hx1 (by norm_num : (1 / 2 : ℝ) ≤ 1)
    have hpoly : 256 * x ^ (2 : ℕ) ≤ L * Real.rpow x (-4) ^ 2 /
        (8 * x ^ (2 : ℕ)) := by
      calc
        _ = (2048 * x ^ (12 : ℕ)) * Real.rpow x (-4) ^ 2 /
            (8 * x ^ (2 : ℕ)) := by rw [hρ]; field_simp <;> ring
        _ ≤ _ := div_le_div_of_nonneg_right
          (mul_le_mul_of_nonneg_right hvarL (sq_nonneg _)) (by positivity)
    have hsmallLog : Real.rpow x (1 / 2 : ℝ) + Real.log (8 * max 1 Checks) ≤
        256 * x ^ (2 : ℕ) := by
      nlinarith [hroot, hlog, sq_nonneg (x - 2)]
    exact hsmallLog.trans hpoly

/-! ## Lane B: star/pin physics (Producers.lean, private in the real file). -/

/-- B1 (= run 7's `cluster_failure_dictionary7`).
TeX 16:228–245; estimated proof: 250 lines. -/
theorem cluster_failure_dictionary {κ : CConsts} {T : Stage} {k : ℕ}
    {PT : ProfiledTiling κ T k} {G : LowGeom PT} (R : CellRawData G)
    (Perm : CellPermissions R) (K : CellRestrictedKernels R Perm)
    (hc : PT.tiling.mode.isCluster) (C : G.Cell) (W : R.Hist C)
    (S : SliceSolver κ PT.tiling (G.cellPatch C) PT.mesh) (Z : ∀ r, S.Val r)
    (groups : (R.Slice C × HypercubeRamsey.Group PT.tiling (G.cellPatch C)) ≃ R.Group C)
    (s : R.Slice C) (w : EvenRole PT.tiling (G.cellPatch C))
    (hGroup : ∀ z (hz : ¬ IsEvenRole (R.cellWords C (s, z)).1),
      R.groupOf C ⟨(R.cellWords C (s, z)).1, (R.cellWords C (s, z)).2, hz⟩ =
        groups (s, S.groupOf z))
    (hU : ∀ g D y, (R.U C W (groups (s, g)) D).w y = S.U g Z D y)
    (hPrior : ∀ ys fallback,
      R.rawPrior C W ys (R.cellWords C (s, w.1)).1 =
        S.σ w Z (nbrLabels w.1 (R.wordLabel C ys s fallback)))
    (a : R.Group C → Bin PT.tiling (G.cellPatch C)) :
    K.failure C W
      ⟨(R.cellWords C (s, w.1)).1, (R.cellWords C (s, w.1)).2,
        (R.word_parity hc C s w.1).mpr w.2⟩ a =
      Lane_sol_s16_prod1.solver_star_bin_failure S Z w (fun g => a (groups (s, g))) := by
  classical
  have finLaw_ext (P Q : FinLaw (Fin (T.S.N k)))
      (hw : ∀ x, P.w x = Q.w x) : P = Q := by
    cases P
    cases Q
    congr 1
    exact funext hw
  have flip_neighbors_injective : Function.Injective (flipPos w.1) := by
    intro j l h
    by_contra hjl
    have he := congrFun h j
    simp [flipPos, hjl] at he
  let fallback : Fin (T.S.N k) := ⟨0, T.S.N_pos k⟩
  have hodd : ∀ j : Fin (PT.tiling.P (G.cellPatch C)).h,
      ¬ IsEvenRole (R.cellWords C (s, flipPos w.1 j)).1 := by
    intro j
    rw [R.word_parity hc, Lane_sol_s16_prod1.flip_parity]
    exact not_not.mpr w.2
  let neighbor : Fin (PT.tiling.P (G.cellPatch C)).h → OddCellRole G C := fun j =>
    ⟨(R.cellWords C (s, flipPos w.1 j)).1,
      (R.cellWords C (s, flipPos w.1 j)).2, hodd j⟩
  have hi : Function.Injective neighbor := by
    intro j l heq
    have hw : R.cellWords C (s, flipPos w.1 j) = R.cellWords C (s, flipPos w.1 l) :=
      Subtype.ext (congrArg (fun r : OddCellRole G C => r.1) heq)
    exact flip_neighbors_injective (congrArg Prod.snd ((R.cellWords C).injective hw))
  have hlabels (ys : OddCellRole G C → Fin (T.S.N k)) :
      nbrLabels w.1 (R.wordLabel C ys s fallback) = fun j => ys (neighbor j) := by
    funext j
    simp only [nbrLabels, CellRawData.wordLabel, dif_pos (hodd j), neighbor]
  have hprior (ys : OddCellRole G C → Fin (T.S.N k)) :
      R.rawPrior C W ys (R.cellWords C (s, w.1)).1 =
        S.σ w Z (fun j => ys (neighbor j)) := by
    rw [hPrior ys fallback, hlabels]
  let P := fun r : OddCellRole G C => R.U C W (R.groupOf C r) (a (R.groupOf C r))
  let Q := fun z : IWord PT.tiling (G.cellPatch C) =>
    (⟨S.U (S.groupOf z) Z (a (groups (s, S.groupOf z))),
      S.U_nonneg (S.groupOf z) Z (a (groups (s, S.groupOf z))),
      S.U_sum (S.groupOf z) Z (a (groups (s, S.groupOf z)))⟩ :
        FinLaw (Fin (T.S.N k)))
  have hrows : (fun j => P (neighbor j)) = (fun j => Q (flipPos w.1 j)) := by
    funext j
    dsimp only [P, neighbor]
    rw [hGroup (flipPos w.1 j) (hodd j)]
    calc
      _ = (⟨S.U (S.groupOf (flipPos w.1 j)) Z
          (a (groups (s, S.groupOf (flipPos w.1 j)))),
        S.U_nonneg (S.groupOf (flipPos w.1 j)) Z
          (a (groups (s, S.groupOf (flipPos w.1 j)))),
        S.U_sum (S.groupOf (flipPos w.1 j)) Z
          (a (groups (s, S.groupOf (flipPos w.1 j))))⟩ :
            FinLaw (Fin (T.S.N k))) := by
          apply finLaw_ext
          intro y
          exact hU _ _ y
      _ = Q (flipPos w.1 j) := rfl
  change (if PT.tiling.mode.isCluster then
    (FinLaw.pi P).pr
      (fun ys => R.rawPrior C W ys (R.cellWords C (s, w.1)).1 = 0) else 0) = _
  rw [if_pos hc]
  simp_rw [hprior]
  rw [Lane_sol_s16_prod1.pr_eq_indicator_E]
  let F : InternalLabels PT.tiling (G.cellPatch C) → ℝ :=
    fun zs => @ite ℝ (S.σ w Z zs = 0) (Classical.propDecidable _) 1 0
  have hleft := Lane_sol_s16_prod1.pi_injective_coordinate_E P neighbor hi F
  have hright := Lane_sol_s16_prod1.pi_injective_coordinate_E Q (flipPos w.1)
    flip_neighbors_injective F
  rw [hrows] at hleft
  unfold Lane_sol_s16_prod1.solver_star_bin_failure
  rw [Lane_sol_s16_prod1.pr_eq_indicator_E]
  change (FinLaw.pi P).E (fun ys => F (fun j => ys (neighbor j))) =
    (FinLaw.pi Q).E (fun ys => F (fun j => ys (flipPos w.1 j)))
  exact hleft.trans hright.symm

/-- B2. Sharp domination of the restricted rows by the raw solver rows:
pretrim loss `h^2 sqrt eps` and permission loss `exp(-cperm n/2)`, with the
cost over at most `h` groups at most 2 (run 7: `permission_retained_sharp7`,
`normalization_product_room7`, `low_cluster_pretrim_power_small7`,
`cluster_permission_cost_room7`).
TeX 16:228–233; estimated proof: 150 lines. -/
theorem cluster_qbar_domination {κ : CConsts} (hκ : κ.Admissible) :
    ∃ n₀ : ℕ, ∀ {T : Stage} {k : ℕ} {PT : ProfiledTiling κ T k} {K16 : ℝ}
      (Q : LowModeQuantFacts hκ (PT := PT) K16) {G : LowGeom PT}
      (R : CellRawData G) (Perm : CellPermissions R) (K : CellRestrictedKernels R Perm),
      PT.tiling.mode = .lowCluster → n₀ ≤ T.S.n k → ∀ C : G.Cell,
      ∃ c : ℝ, 1 ≤ c ∧ c ^ (PT.tiling.P (G.cellPatch C)).h ≤ 2 ∧
        ∀ (S : SliceSolver κ PT.tiling (G.cellPatch C) PT.mesh)
          (records : ∀ s, R.Value C s ≃ (∀ r, S.Val r))
          (groups : (R.Slice C × HypercubeRamsey.Group PT.tiling (G.cellPatch C)) ≃ R.Group C),
          (∀ s V, V ∈ R.slicePass C s ↔ S.AllGood (records s V)) →
          (∀ W s g D, (R.qraw C W (groups (s, g))).w D = S.q g (records s (W s)) D) →
          (∀ W s g, R.pretrim C W (groups (s, g)) = S.pretrimBins (records s (W s)) g) →
          ∀ W, (R.history C).w W ≠ 0 → PermissionLossHypotheses (Perm.table C) (R.qin C W) →
          ∀ s g D, (K.qbar C W (groups (s, g))).w D ≤ c * S.q g (records s (W s)) D := by
  classical
  obtain ⟨n₁, hpermRoom⟩ := Lane_sol_s16_prod1.cluster_permission_cost_room hκ
  refine ⟨n₁, ?_⟩
  intro T k PT K16 Q G R Perm K hmode hn C
  let n := T.S.n k
  let h := (PT.tiling.P (G.cellPatch C)).h
  let ε := sliceEps κ h
  let u := Real.exp (-κ.cperm * (n : ℝ) / 2)
  let v := (h : ℝ) ^ 2 * Real.sqrt ε
  have hnlarge : 2 ≤ n := Q.n_large
  have hheight : h ≤ n := by
    simpa only [Fintype.card_fin] using
      Fintype.card_le_of_injective (R.axis C) (R.axis_injective C)
  have huNonneg : 0 ≤ u := le_of_lt (Real.exp_pos _)
  have hrate : 0 < κ.cperm * (n : ℝ) / 2 := by
    have hnpos : (0 : ℝ) < n := by exact_mod_cast lt_of_lt_of_le (by norm_num : (0 : ℕ) < 2) hnlarge
    exact div_pos (mul_pos hκ.cperm_rng.1 hnpos) (by norm_num)
  have huLt : u < 1 := by
    exact Real.exp_lt_one_iff.mpr (by nlinarith [hrate])
  have hvNonneg : 0 ≤ v := by
    dsimp [v]
    positivity
  have hsmall2 : v ≤ 1 / 1000 := by
    have hs := Lane_sol_s16_prod1.low_cluster_pretrim_power_small
      hκ Q hmode (G.cellPatch C) 2 (by norm_num)
    norm_num [Real.rpow_neg, Real.rpow_natCast] at hs
    simpa [v, h, ε] using hs
  have hsmall3 : (h : ℝ) ^ 3 * Real.sqrt ε ≤ 1 / 1000 := by
    have hs := Lane_sol_s16_prod1.low_cluster_pretrim_power_small
      hκ Q hmode (G.cellPatch C) 3 (by norm_num)
    norm_num [Real.rpow_neg, Real.rpow_natCast] at hs
    simpa [h, ε] using hs
  have hvLt : v < 1 := by linarith
  have hhu : (h : ℝ) * u ≤ 1 / 4 := by
    exact hpermRoom n h hn hnlarge hheight
  have hsmallSum : (h : ℝ) * (u + v) ≤ 1 / 2 := by
    have hhv : (h : ℝ) * v = (h : ℝ) ^ 3 * Real.sqrt ε := by
      dsimp [v]
      ring
    rw [mul_add, hhv]
    linarith
  have hnorm := Lane_sol_s16_prod1.normalization_product_room h h u v
    huNonneg hvNonneg huLt hvLt le_rfl hsmallSum
  let c : ℝ := ((1 - u) * (1 - v))⁻¹
  have hc : 1 ≤ c := by simpa [c] using hnorm.1
  have hcpow : c ^ h ≤ 2 := by simpa [c] using hnorm.2
  have huPos : 0 < 1 - u := sub_pos.mpr huLt
  have hvPos : 0 < 1 - v := sub_pos.mpr hvLt
  refine ⟨c, hc, hcpow, ?_⟩
  intro S records groups hPass hqraw hpretrim W hW hPerm s g D
  have hSlices : ∀ t, W t ∈ R.slicePass C t ∧ (R.sliceLaw C t).w (W t) ≠ 0 := by
    intro t
    exact Lane_sol_s16_prod1.cond_support _ _ _ _
      (Lane_sol_s16_prod1.pi_support _ W hW t)
  have hGood : S.AllGood (records s (W s)) :=
    (hPass s (W s)).mp (hSlices s).1
  let rawMass : ℝ :=
    ∑ D' ∈ S.pretrimBins (records s (W s)) g, S.q g (records s (W s)) D'
  have hsolverMass := Lane_sol_s16_prod1.solver_pretrim_mass
    S (records s (W s)) hGood g (Real.exp_pos _)
  have hpreMass : 1 - v ≤ rawMass := by
    simpa [rawMass, v, h, ε] using hsolverMass
  have hrawMass :
      (∑ D' ∈ R.pretrim C W (groups (s, g)),
        (R.qraw C W (groups (s, g))).w D') = rawMass := by
    rw [hpretrim]
    apply Finset.sum_congr rfl
    intro D' hD'
    exact hqraw W s g D'
  have hqinFormula : (R.qin C W (groups (s, g))).w D =
      (if D ∈ S.pretrimBins (records s (W s)) g then
        S.q g (records s (W s)) D else 0) / rawMass := by
    rw [R.qin_eq C W (groups (s, g)) D hSlices, ← hrawMass, hpretrim, hqraw]
  have hqinBound : (R.qin C W (groups (s, g))).w D ≤
      S.q g (records s (W s)) D / (1 - v) := by
    rw [hqinFormula]
    by_cases hD : D ∈ S.pretrimBins (records s (W s)) g
    · rw [if_pos hD]
      exact div_le_div_of_nonneg_left (S.q_nonneg g (records s (W s)) D)
        (sub_pos.mpr hvLt) hpreMass
    · simp [hD]
      exact div_nonneg (S.q_nonneg g (records s (W s)) D) (sub_nonneg.mpr hvLt.le)
  have hpermSharp := Lane_sol_s16_prod1.permission_retained_sharp
    (Perm.table C) (R.qin C W) hPerm (groups (s, g))
  have hpermMass : 1 - u ≤
      ∑ D' ∈ (Perm.table C).permitted (groups (s, g)),
        (R.qin C W (groups (s, g))).w D' := by
    simpa [u, n, Perm.rate_eq C, Perm.n_eq C] using hpermSharp
  have hpermPos : 0 <
      ∑ D' ∈ (Perm.table C).permitted (groups (s, g)),
        (R.qin C W (groups (s, g))).w D' :=
    lt_of_lt_of_le huPos hpermMass
  rw [K.qbar_eq C W (groups (s, g)) D hW]
  by_cases hD : D ∈ (Perm.table C).permitted (groups (s, g))
  · rw [if_pos hD]
    calc
      _ ≤ (S.q g (records s (W s)) D / (1 - v)) /
          (∑ D' ∈ (Perm.table C).permitted (groups (s, g)),
            (R.qin C W (groups (s, g))).w D') :=
        div_le_div_of_nonneg_right hqinBound hpermPos.le
      _ ≤ (S.q g (records s (W s)) D / (1 - v)) / (1 - u) :=
        div_le_div_of_nonneg_left
          (div_nonneg (S.q_nonneg g (records s (W s)) D) hvPos.le)
          huPos hpermMass
      _ = c * S.q g (records s (W s)) D := by
        dsimp [c, u, v]
        field_simp [ne_of_gt huPos, ne_of_gt hvPos]
        <;> ring
  · simp [hD]
    exact mul_nonneg (le_trans (by norm_num) hc)
      (S.q_nonneg g (records s (W s)) D)

/-- B3. Star and pinned-star integrals against the restricted (unpooled)
rows: `solver_star_trimmed_mean` / `solver_star_trimmed_pin_mean` with B2.
TeX 16:228–249; estimated proof: 100 lines. -/
theorem cluster_star_qbar_means {κ : CConsts} (hκ : κ.Admissible) :
    ∃ n₀ : ℕ, ∀ {T : Stage} {k : ℕ} {PT : ProfiledTiling κ T k} {K16 : ℝ}
      (Q : LowModeQuantFacts hκ (PT := PT) K16) {G : LowGeom PT}
      (R : CellRawData G) (Perm : CellPermissions R) (K : CellRestrictedKernels R Perm),
      PT.tiling.mode = .lowCluster → n₀ ≤ T.S.n k → ∀ (C : G.Cell)
      (S : SliceSolver κ PT.tiling (G.cellPatch C) PT.mesh)
      (records : ∀ s, R.Value C s ≃ (∀ r, S.Val r))
      (groups : (R.Slice C × HypercubeRamsey.Group PT.tiling (G.cellPatch C)) ≃ R.Group C),
      (∀ s V, V ∈ R.slicePass C s ↔ S.AllGood (records s V)) →
      (∀ W s g D, (R.qraw C W (groups (s, g))).w D = S.q g (records s (W s)) D) →
      (∀ W s g, R.pretrim C W (groups (s, g)) = S.pretrimBins (records s (W s)) g) →
      ∀ W, (R.history C).w W ≠ 0 → PermissionLossHypotheses (Perm.table C) (R.qin C W) →
      ∀ s (w : EvenRole PT.tiling (G.cellPatch C)),
        (FinLaw.pi fun g => K.qbar C W (groups (s, g))).E
            (Lane_sol_s16_prod1.solver_star_bin_failure S (records s (W s)) w) ≤
          2 * sliceEps κ (PT.tiling.P (G.cellPatch C)).h ∧
        ∀ g D, g ∈ Lane_sol_s16_prod1.solver_star_group_scope S w →
          D ∈ S.pretrimBins (records s (W s)) g →
          (FinLaw.pi (Lane_sol_s16_prod1.coordinatePin
              (fun g => K.qbar C W (groups (s, g))) g D)).E
              (Lane_sol_s16_prod1.solver_star_bin_failure S (records s (W s)) w) ≤
            2 * Real.sqrt (sliceEps κ (PT.tiling.P (G.cellPatch C)).h) := by
  classical
  obtain ⟨n₀, hdom⟩ := cluster_qbar_domination hκ
  refine ⟨n₀, ?_⟩
  intro T k PT K16 Q G R Perm K hmode hn C S records groups hPass hqraw hpretrim
    W hW hPerm s w
  obtain ⟨c, hc, hcpow, hrows⟩ := hdom Q R Perm K hmode hn C
  have hrows := hrows S records groups hPass hqraw hpretrim W hW hPerm
  have hSlices : ∀ t, W t ∈ R.slicePass C t ∧ (R.sliceLaw C t).w (W t) ≠ 0 := by
    intro t
    exact Lane_sol_s16_prod1.cond_support _ _ _ _
      (Lane_sol_s16_prod1.pi_support _ W hW t)
  have hGood : S.AllGood (records s (W s)) :=
    (hPass s (W s)).mp (hSlices s).1
  let P : HypercubeRamsey.Group PT.tiling (G.cellPatch C) →
      FinLaw (Bin PT.tiling (G.cellPatch C)) :=
    fun g => K.qbar C W (groups (s, g))
  have hP : ∀ g ∈ Lane_sol_s16_prod1.solver_star_group_scope S w, ∀ D,
      (P g).w D ≤ c * S.q g (records s (W s)) D := by
    intro g _ D
    exact hrows s g D
  have hc0 : 0 ≤ c := le_trans (by norm_num) hc
  have hcount := Lane_sol_s16_prod1.solver_star_group_scope_count S w
  have hpow : c ^ (Lane_sol_s16_prod1.solver_star_group_scope S w).card ≤ 2 := by
    exact (pow_le_pow_right₀ hc hcount).trans hcpow
  have hmean := Lane_sol_s16_prod1.solver_star_trimmed_mean
    S (records s (W s)) w (hGood w) P c hc0 hP
  have hεnonneg : 0 ≤ sliceEps κ (PT.tiling.P (G.cellPatch C)).h := by
    unfold sliceEps
    exact (Real.exp_pos _).le
  constructor
  · exact hmean.trans (mul_le_mul_of_nonneg_right hpow hεnonneg)
  · intro g D hg hD
    have hvg : SliceSolver.Incident w g := by
      obtain ⟨j, _, heq⟩ := Finset.mem_image.mp hg
      rw [← heq]
      refine ⟨j, S.groupOf_spec _ ?_⟩
      rw [Lane_sol_s16_prod1.flip_parity]
      exact not_not.mpr w.2
    have hpin := Lane_sol_s16_prod1.solver_star_trimmed_pin_mean
      S (records s (W s)) w P c hc hP g D hD hvg
    exact hpin.trans (mul_le_mul_of_nonneg_right hpow (Real.sqrt_nonneg _))

/-! ## Lane D: the cluster load gate, under the repair. -/

/-- D1. Generic: a product of conditioned laws is the image of a product of
laws on the positive passing values.
TeX 16:259–278; estimated proof: 120 lines. -/
theorem pi_cond_support_map {I : Type*} [Fintype I] [DecidableEq I]
    {V : I → Type*} [∀ i, Fintype (V i)] [∀ i, DecidableEq (V i)]
    (P : ∀ i, FinLaw (V i)) (A : ∀ i, Finset (V i))
    (hA : ∀ i, 0 < ∑ v ∈ A i, (P i).w v) :
    ∃ P' : ∀ i, FinLaw {v : V i // v ∈ A i ∧ (P i).w v ≠ 0},
      FinLaw.pi (fun i => FinLaw.cond (P i) (A i) (hA i)) =
        FinLaw.map (FinLaw.pi P') (fun z i => (z i).1) := by
  exact Lane_q_s16_gate1.pi_cond_support_map P A hA

/-- D2. The load summand of one odd role depends on its own slice value.
TeX 16:259–278; estimated proof: 150 lines. -/
theorem cluster_role_term_local {κ : CConsts} {T : Stage} {k : ℕ}
    {PT : ProfiledTiling κ T k} {G : LowGeom PT} (R : CellRawData G)
    (Perm : CellPermissions R) (K : CellRestrictedKernels R Perm)
    (hFallback : ∀ C pool W g, (∑ D ∈ Finset.univ.image pool, (K.qbar C W g).w D) = 0 →
      K.qtilde C pool W g = K.qbar C W g)
    (hR : R.SourceValid) (hc : PT.tiling.mode.isCluster) (C : G.Cell) (pool : CellPool G C)
    (W W' : R.Hist C) (hW : (R.history C).w W ≠ 0) (hW' : (R.history C).w W' ≠ 0)
    (r : OddCellRole G C)
    (heq : W ((R.cellWords C).symm ⟨r.1, r.2.1⟩).1 = W' ((R.cellWords C).symm ⟨r.1, r.2.1⟩).1)
    (y : Fin (T.S.N k)) :
    ∑ b, (K.qtilde C pool W (R.groupOf C r)).w b * (R.U C W (R.groupOf C r) b).w y =
      ∑ b, (K.qtilde C pool W' (R.groupOf C r)).w b * (R.U C W' (R.groupOf C r) b).w y := by
  exact Lane_q_s16_gate1.cluster_role_term_local R Perm K hFallback hR hc C pool W W'
    hW hW' r heq y

/-- D3. Per-role cap at pools whose normalizers pass (typical pools).
TeX 16:274–276; estimated proof: 150 lines. -/
theorem cluster_role_term_cap {κ : CConsts} (hκ : κ.Admissible)
    {T : Stage} {k : ℕ} {PT : ProfiledTiling κ T k} {K16 : ℝ}
    (Q : LowModeQuantFacts hκ (PT := PT) K16) (H : LowGeometryCertificate hκ Q)
    (R : CellRawData H.geom) (Perm : CellPermissions R) (K : CellRestrictedKernels R Perm)
    (hR : R.SourceValid) (hc : PT.tiling.mode.isCluster)
    (hPerm : ∀ C W, (R.history C).w W ≠ 0 → PermissionLossHypotheses (Perm.table C) (R.qin C W))
    (C : H.geom.Cell) (pool : CellPool H.geom C) (W : R.Hist C) (hW : (R.history C).w W ≠ 0)
    (hn4 : Real.rpow (T.S.n k : ℝ) (-4) ≤ 1 / 2)
    (hmass : ∀ g, (1 - Real.rpow (T.S.n k : ℝ) (-4)) *
      ((H.geom.nslot C : ℝ) / Fintype.card (Bin PT.tiling (H.geom.cellPatch C))) ≤
        ∑ b ∈ Finset.univ.image pool, (K.qbar C W g).w b)
    (r : OddCellRole H.geom C) (y : Fin (T.S.N k)) :
    ∑ b, (K.qtilde C pool W (R.groupOf C r)).w b * (R.U C W (R.groupOf C r) b).w y ≤
      64 * Real.exp (2 * (sliceK κ (PT.tiling.P (H.geom.cellPatch C)).h : ℝ) *
        sliceT κ (PT.tiling.P (H.geom.cellPatch C)).h) / (H.geom.nslot C : ℝ) := by
  exact Lane_q_s16_gate1.cluster_role_term_cap hκ Q H R Perm K hR hc hPerm C pool W hW hn4
    hmass r y

set_option maxHeartbeats 800000 in
/-- D4. Per-role history mean at typical pools, through `low_profile` and
`law_cap` (T16:268-273): `4 (B/L) * 11/M`.
TeX 16:268–273; estimated proof: 350 lines. -/
theorem cluster_role_term_mean {κ : CConsts} (hκ : κ.Admissible)
    {T : Stage} {k : ℕ} {PT : ProfiledTiling κ T k} {K16 : ℝ}
    (Q : LowModeQuantFacts hκ (PT := PT) K16) (H : LowGeometryCertificate hκ Q)
    (R : CellRawData H.geom) (Perm : CellPermissions R) (K : CellRestrictedKernels R Perm)
    (hR : R.SourceValid) (hc : PT.tiling.mode.isCluster)
    (hPerm : ∀ C W, (R.history C).w W ≠ 0 → PermissionLossHypotheses (Perm.table C) (R.qin C W))
    (C : H.geom.Cell) (pool : CellPool H.geom C)
    (hn4 : Real.rpow (T.S.n k : ℝ) (-4) ≤ 1 / 2)
    (hmass : ∀ W, (R.history C).w W ≠ 0 → ∀ g, (1 - Real.rpow (T.S.n k : ℝ) (-4)) *
      ((H.geom.nslot C : ℝ) / Fintype.card (Bin PT.tiling (H.geom.cellPatch C))) ≤
        ∑ b ∈ Finset.univ.image pool, (K.qbar C W g).w b)
    (r : OddCellRole H.geom C) (y : Fin (T.S.N k)) :
    (R.history C).E (fun W =>
      ∑ b, (K.qtilde C pool W (R.groupOf C r)).w b * (R.U C W (R.groupOf C r) b).w y) ≤
      44 / ((H.geom.nslot C : ℝ) * (PT.tiling.P (H.geom.cellPatch C)).d) := by
  classical
  let i := H.geom.cellPatch C
  let patch := PT.tiling.P i
  let B : ℝ := Fintype.card (Bin PT.tiling i)
  let L : ℝ := H.geom.nslot C
  have hMnat : 0 < patch.M := by
    rw [← patch.cardY]
    exact_mod_cast Finset.card_pos.mpr
      (Q.profiled_valid.tiling_valid.patch_nonempty i).2
  have hMpos : 0 < (patch.M : ℝ) := by exact_mod_cast hMnat
  have hbinSum := patch.bins.sum_card_parts
  have hparts : (∑ b ∈ patch.bins.parts, b.card) = patch.bins.parts.card * patch.d := by
    calc
      _ = ∑ b ∈ patch.bins.parts, patch.d := by
        apply Finset.sum_congr rfl
        intro b hb
        exact Q.profiled_valid.tiling_valid.bins_card i b hb
      _ = _ := by simp
  rw [hparts, patch.cardY] at hbinSum
  have hbinNat : Fintype.card (Bin PT.tiling i) * patch.d = patch.M := by
    change Fintype.card {b // b ∈ patch.bins.parts} * patch.d = patch.M
    rw [Fintype.card_of_subtype patch.bins.parts (fun _ => Iff.rfl)]
    exact hbinSum
  have hBnat : 0 < Fintype.card (Bin PT.tiling i) := by
    by_contra h
    have hz : Fintype.card (Bin PT.tiling i) = 0 := Nat.eq_zero_of_not_pos h
    rw [hz, zero_mul] at hbinNat
    omega
  have hdNat : 0 < patch.d := by
    by_contra h
    have hz : patch.d = 0 := Nat.eq_zero_of_not_pos h
    rw [hz, Nat.mul_zero] at hbinNat
    omega
  have hBpos : 0 < B := by
    dsimp [B]
    exact_mod_cast hBnat
  have hdpos : 0 < (patch.d : ℝ) := by exact_mod_cast hdNat
  have hθ : 0 < κ.θstar := hκ.bucket.2.2.2.2
  have hKcell : 0 < κ.Kcell :=
    lt_of_lt_of_le (div_pos (by norm_num) hθ) hκ.Kcell_big
  have hnpos : 0 < (T.S.n k : ℝ) := by
    exact_mod_cast lt_of_lt_of_le (by norm_num : (0 : ℕ) < 2) Q.n_large
  have hLnat : 0 < H.geom.nslot C := by
    change 0 < H.data.cells.nslot C
    rw [H.cell_partition.slot_count C]
    apply Nat.ceil_pos.mpr
    exact div_pos (mul_pos hKcell (Real.rpow_pos_of_pos hnpos _)) hdpos
  have hLpos : 0 < L := by
    dsimp [L]
    exact_mod_cast hLnat
  have hbinReal : B * (patch.d : ℝ) = patch.M := by
    dsimp [B]
    exact_mod_cast hbinNat
  rcases hR with ⟨hMode, _hUniform, hSource⟩ | ⟨hNotCluster, _hSource⟩
  · obtain ⟨S, hS, records, groups, hLaw, hPass, hGroup, hQ, hTrim, hU, _hPrior⟩ := hSource C
    let words := R.cellWords C
    let sz := words.symm ⟨r.1, r.2.1⟩
    let s : R.Slice C := sz.1
    let z := sz.2
    have hback : words sz = ⟨r.1, r.2.1⟩ := words.apply_symm_apply _
    have hval : (words (s, z)).1 = r.1 := by
      simpa [s, z] using congrArg Subtype.val hback
    have hodd : ¬ IsEvenRole (words (s, z)).1 := by
      rw [hval]
      exact r.2.2
    have hrole : (⟨(words (s, z)).1, (words (s, z)).2, hodd⟩ : OddCellRole H.geom C) = r := by
      apply Subtype.ext
      exact hval
    have hgroup : R.groupOf C r = groups (s, S.groupOf z) := by
      have hh := hGroup s z hodd
      rw [hrole] at hh
      exact hh
    let g := S.groupOf z
    let P : FinLaw (∀ t, S.Val t) := S.recLaw PT.parameter
    let good := Finset.univ.filter S.AllGood
    have hgood : 0 < P.pr S.AllGood :=
      Lane_sol_s16_prod1.solver_good_pos Q.profiled_valid hMode S hS
    let condLaw : ∀ t : R.Slice C, FinLaw (R.Value C t) := fun t =>
      FinLaw.cond (R.sliceLaw C t) (R.slicePass C t) (R.slice_pos C t)
    have hSupported : ∀ W : R.Hist C, (R.history C).w W ≠ 0 →
        ∀ t, W t ∈ R.slicePass C t ∧ (R.sliceLaw C t).w (W t) ≠ 0 := by
      intro W hW t
      have hw : (condLaw t).w (W t) ≠ 0 := by
        exact Lane_sol_s16_prod1.pi_support condLaw W
          (by simpa [CellRawData.history, condLaw] using hW) t
      exact Lane_sol_s16_prod1.cond_support _ _ _ (W t) hw
    have hqin (W : R.Hist C) (hW : (R.history C).w W ≠ 0) (b : Bin PT.tiling i) :
        (R.qin C W (groups (s, g))).w b = S.qin (records s (W s)) g b := by
      rw [R.qin_eq C W (groups (s, g)) b (hSupported W hW)]
      simp_rw [hTrim W s g, hQ W s g]
      by_cases hb : b ∈ S.pretrimBins (records s (W s)) g
      · simp [SliceSolver.qin, hb]
      · simp [SliceSolver.qin, hb]
    let fRole : R.Hist C → ℝ := fun W =>
      ∑ b, (K.qtilde C pool W (R.groupOf C r)).w b *
        (R.U C W (R.groupOf C r) b).w y
    let fQin : R.Hist C → ℝ := fun W =>
      ∑ b, (R.qin C W (R.groupOf C r)).w b *
        (R.U C W (R.groupOf C r) b).w y
    let fSlice : R.Value C s → ℝ := fun w =>
      ∑ b, S.qin (records s w) g b * S.U g (records s w) b y
    have hqinTerm (W : R.Hist C) (hW : (R.history C).w W ≠ 0) :
        fQin W = fSlice (W s) := by
      dsimp [fQin, fSlice]
      rw [hgroup]
      apply Finset.sum_congr rfl
      intro b _
      rw [hqin W hW b, hU W s g b y]
    have hnormalizer (W : R.Hist C) (hW : (R.history C).w W ≠ 0) :
        L / (2 * B) ≤
          ∑ b ∈ Finset.univ.image pool, (K.qbar C W (groups (s, g))).w b := by
      have hm := hmass W hW (groups (s, g))
      have hfactor : (1 / 2 : ℝ) ≤ 1 - Real.rpow (T.S.n k : ℝ) (-4) := by
        linarith [hn4]
      have hLB : 0 ≤ L / B := div_nonneg hLpos.le hBpos.le
      calc
        L / (2 * B) = (1 / 2 : ℝ) * (L / B) := by ring
        _ ≤ (1 - Real.rpow (T.S.n k : ℝ) (-4)) * (L / B) :=
          mul_le_mul_of_nonneg_right hfactor hLB
        _ ≤ _ := hm
    have hqbar (W : R.Hist C) (hW : (R.history C).w W ≠ 0)
        (b : Bin PT.tiling i) :
        (K.qbar C W (groups (s, g))).w b ≤
          2 * (R.qin C W (groups (s, g))).w b := by
      have hret := Lane_sol_s16_prod1.permission_retained_half
        (Perm.table C) (R.qin C W) (hPerm C W hW) (groups (s, g))
      have hden : 0 < ∑ b' ∈ (Perm.table C).permitted (groups (s, g)),
          (R.qin C W (groups (s, g))).w b' := by linarith
      rw [K.qbar_eq C W (groups (s, g)) b hW]
      by_cases hb : b ∈ (Perm.table C).permitted (groups (s, g))
      · rw [if_pos hb]
        calc
          _ ≤ (R.qin C W (groups (s, g))).w b / (1 / 2 : ℝ) :=
            div_le_div_of_nonneg_left ((R.qin C W (groups (s, g))).nonneg b)
              (by norm_num) hret
          _ = 2 * (R.qin C W (groups (s, g))).w b := by ring
      · simpa [hb] using (R.qin C W (groups (s, g))).nonneg b
    have hqtilde (W : R.Hist C) (hW : (R.history C).w W ≠ 0)
        (b : Bin PT.tiling i) :
        (K.qtilde C pool W (groups (s, g))).w b ≤
          (2 * B / L) * (K.qbar C W (groups (s, g))).w b := by
      have hZ := hnormalizer W hW
      have hZpos : 0 < ∑ b' ∈ Finset.univ.image pool,
          (K.qbar C W (groups (s, g))).w b' := by
        exact lt_of_lt_of_le (div_pos hLpos (by positivity)) hZ
      rw [K.qtilde_eq C pool W (groups (s, g)) b hW (ne_of_gt hZpos)]
      by_cases hb : b ∈ Finset.univ.image pool
      · rw [if_pos hb]
        calc
          _ ≤ (K.qbar C W (groups (s, g))).w b / (L / (2 * B)) :=
            div_le_div_of_nonneg_left
              ((K.qbar C W (groups (s, g))).nonneg b) (by positivity) hZ
          _ = (2 * B / L) * (K.qbar C W (groups (s, g))).w b := by
            field_simp [ne_of_gt hLpos] <;> ring
      · simp only [if_neg hb, zero_div]
        exact mul_nonneg (div_nonneg (mul_nonneg (by norm_num) hBpos.le) hLpos.le)
          ((K.qbar C W (groups (s, g))).nonneg b)
    have hpoint (W : R.Hist C) (hW : (R.history C).w W ≠ 0) :
        fRole W ≤ (4 * B / L) * fQin W := by
      dsimp [fRole, fQin]
      rw [hgroup]
      have hsum :
          (∑ b, (K.qbar C W (groups (s, g))).w b *
            (R.U C W (groups (s, g)) b).w y) ≤
          2 * ∑ b, (R.qin C W (groups (s, g))).w b *
            (R.U C W (groups (s, g)) b).w y := by
        calc
          _ ≤ ∑ b, 2 * ((R.qin C W (groups (s, g))).w b *
              (R.U C W (groups (s, g)) b).w y) := by
            apply Finset.sum_le_sum
            intro b _
            calc
              _ ≤ (2 * (R.qin C W (groups (s, g))).w b) *
                  (R.U C W (groups (s, g)) b).w y :=
                mul_le_mul_of_nonneg_right (hqbar W hW b)
                  ((R.U C W (groups (s, g)) b).nonneg y)
              _ = _ := by ring
          _ = _ := by rw [← Finset.mul_sum]
      calc
        _ ≤ (2 * B / L) *
            ∑ b, (K.qbar C W (groups (s, g))).w b *
              (R.U C W (groups (s, g)) b).w y := by
          calc
            _ ≤ ∑ b, ((2 * B / L) * (K.qbar C W (groups (s, g))).w b) *
                (R.U C W (groups (s, g)) b).w y := by
              apply Finset.sum_le_sum
              intro b _
              exact mul_le_mul_of_nonneg_right (hqtilde W hW b)
                ((R.U C W (groups (s, g)) b).nonneg y)
            _ = _ := by
              rw [Finset.mul_sum]
              apply Finset.sum_congr rfl
              intro b _
              ring
        _ ≤ (2 * B / L) *
            (2 * ∑ b, (R.qin C W (groups (s, g))).w b *
              (R.U C W (groups (s, g)) b).w y) :=
          mul_le_mul_of_nonneg_left hsum (by positivity)
        _ = (4 * B / L) *
            ∑ b, (R.qin C W (groups (s, g))).w b *
              (R.U C W (groups (s, g)) b).w y := by ring
    have hEbound : (R.history C).E fRole ≤ (4 * B / L) * (R.history C).E fQin := by
      unfold FinLaw.E
      calc
        _ ≤ ∑ W, (R.history C).w W * ((4 * B / L) * fQin W) := by
          apply Finset.sum_le_sum
          intro W _
          by_cases hW : (R.history C).w W = 0
          · simp [hW]
          · exact mul_le_mul_of_nonneg_left (hpoint W hW) ((R.history C).nonneg W)
        _ = _ := by
          calc
            _ = ∑ W, (4 * B / L) * ((R.history C).w W * fQin W) := by
              apply Finset.sum_congr rfl
              intro W _
              ring
            _ = _ := by rw [Finset.mul_sum]
    have hmeanQin : (R.history C).E fQin = (PT.π i).w y := by
      let law : ∀ t : R.Slice C, FinLaw (R.Value C t) := condLaw
      have hreplace : (FinLaw.pi law).E fQin =
          (FinLaw.pi law).E (fun W => fSlice (W s)) := by
        unfold FinLaw.E
        apply Finset.sum_congr rfl
        intro W _
        by_cases hW : (FinLaw.pi law).w W = 0
        · simp [hW]
        · have hW' : (R.history C).w W ≠ 0 := by
            simpa [CellRawData.history, law, condLaw] using hW
          rw [hqinTerm W hW']
      have hcoord : (FinLaw.pi law).E (fun W => fSlice (W s)) =
          (law s).E fSlice := by
        let S : Finset (R.Slice C) := {s}
        let st : {t : R.Slice C // t ∈ S} := ⟨s, by simp [S]⟩
        letI inst : Unique {t : R.Slice C // t ∈ S} := {
          default := st
          uniq := by
            intro t
            apply Subtype.ext
            exact Finset.mem_singleton.mp (by simpa [S] using t.2) }
        let Qfw : ∀ t : R.Slice C, FinProb (R.Value C t) := fun t =>
          HypercubeRamsey.S16.finLawToFramework (law t)
        have hm := FinProb.pi_marginal_expect Qfw S (fun a => fSlice (a default))
        let e : (∀ t : {t : R.Slice C // t ∈ S}, R.Value C t.1) ≃ R.Value C s :=
          Equiv.piUnique (fun t : {t : R.Slice C // t ∈ S} => R.Value C t.1)
        have hprod (a : ∀ t : {t : R.Slice C // t ∈ S}, R.Value C t.1) :
            (∏ t, (Qfw t.1).w (a t)) = (Qfw s).w (a default) := by
          rw [Fintype.prod_unique]
          simp [Qfw, inst, st, S]
        have hsingle :
            (FinProb.pi (fun t : {t : R.Slice C // t ∈ S} => Qfw t.1)).expect
                (fun a => fSlice (a default)) = (Qfw s).expect fSlice := by
          calc
            _ = ∑ a, (Qfw s).w (e a) * fSlice (e a) := by
              unfold FinProb.expect
              apply Finset.sum_congr rfl
              intro a _
              change (∏ t, (Qfw t.1).w (a t)) * fSlice (a default) = _
              rw [hprod a]
              change (Qfw s).w (e a) * fSlice (e a) = _
              have he : e a = a default := rfl
              rw [he]
            _ = ∑ w, (Qfw s).w w * fSlice w :=
              Equiv.sum_comp e (fun w => (Qfw s).w w * fSlice w)
            _ = _ := rfl
        rw [hsingle] at hm
        simpa [FinProb.expect, FinProb.pi, FinLaw.E, FinLaw.pi, Qfw, inst, st, S,
          HypercubeRamsey.S16.finLawToFramework] using hm
      have hweight (w : R.Value C s) : (R.sliceLaw C s).w w = P.w (records s w) := by
        rw [hLaw s]
        change (FinLaw.map (S.recLaw PT.parameter) (records s).symm).w w =
          (S.recLaw PT.parameter).w (records s w)
        simp [FinLaw.map, Equiv.symm_apply_eq, P]
      have hgoodDen : (∑ W ∈ good, P.w W) = P.pr S.AllGood := by
        simpa [good, FinLaw.pr] using (Finset.sum_ite_mem_eq good P.w).symm
      have hgoodMass : 0 < ∑ W ∈ good, P.w W := by
        rw [hgoodDen]
        exact hgood
      have hden : ∑ w ∈ R.slicePass C s, (R.sliceLaw C s).w w = P.pr S.AllGood := by
        calc
          _ = ∑ w ∈ R.slicePass C s, P.w (records s w) := by
            apply Finset.sum_congr rfl
            intro w _
            exact hweight w
          _ = ∑ w, if w ∈ R.slicePass C s then P.w (records s w) else 0 := by
            simp [Finset.sum_ite_mem, Finset.univ_inter]
          _ = ∑ W, if (records s).symm W ∈ R.slicePass C s then P.w W else 0 := by
            simpa [Equiv.apply_symm_apply] using
              (Equiv.sum_comp (records s) (fun W =>
                if (records s).symm W ∈ R.slicePass C s then P.w W else 0))
          _ = P.pr S.AllGood := by
            calc
              _ = ∑ W, if S.AllGood W then P.w W else 0 := by
                apply Finset.sum_congr rfl
                intro W _
                have hp : (records s).symm W ∈ R.slicePass C s ↔ S.AllGood W := by
                  simpa using hPass s ((records s).symm W)
                by_cases hg : S.AllGood W
                · simp [hp.mpr hg, hg]
                · have hn : (records s).symm W ∉ R.slicePass C s := by
                    intro h
                    exact hg (hp.mp h)
                  simp [hn, hg]
              _ = ∑ W ∈ good, P.w W := by
                simpa [good] using (Finset.sum_ite_mem_eq good P.w)
              _ = _ := hgoodDen
      have hcondE : (law s).E fSlice =
          (FinLaw.cond P good hgoodMass).E (fun W => fSlice ((records s).symm W)) := by
        have hcondWeight (w : R.Value C s) : (law s).w w =
            (FinLaw.cond P good hgoodMass).w (records s w) := by
          simp only [law, condLaw, FinLaw.cond]
          rw [hweight w, hden, hgoodDen]
          have hp := hPass s w
          simp only [good, Finset.mem_filter, Finset.mem_univ, true_and]
          by_cases hg : S.AllGood (records s w)
          · simp [hp.mpr hg, hg]
          · have hn : w ∉ R.slicePass C s := fun hw => hg (hp.mp hw)
            simp [hn, hg]
        calc
          _ = ∑ w, (FinLaw.cond P good hgoodMass).w (records s w) * fSlice w := by
            unfold FinLaw.E
            apply Finset.sum_congr rfl
            intro w _
            rw [hcondWeight w]
          _ = _ := by
            unfold FinLaw.E
            simpa [Equiv.apply_symm_apply] using
              (Equiv.sum_comp (records s) (fun W =>
                (FinLaw.cond P good hgoodMass).w W * fSlice ((records s).symm W)))
      have hlow : (FinLaw.cond P good hgoodMass).E
          (fun W => fSlice ((records s).symm W)) = S.lowOut PT.parameter g y := by
        have hnum :
            (∑ W, (if S.AllGood W then P.w W else 0) *
              fSlice ((records s).symm W)) =
            ∑ W, P.w W * (if S.AllGood W then
              ∑ b, S.qin W g b * S.U g W b y else 0) := by
          apply Finset.sum_congr rfl
          intro W _
          by_cases hg : S.AllGood W
          · simp [hg, fSlice, Equiv.apply_symm_apply]
          · simp [hg]
        have hnumS :
            (∑ W, (if S.AllGood W then (S.recLaw PT.parameter).w W else 0) *
              fSlice ((records s).symm W)) =
            ∑ W, (S.recLaw PT.parameter).w W * (if S.AllGood W then
              ∑ b, S.qin W g b * S.U g W b y else 0) := by
          simpa [P] using hnum
        have hgoodDenS : (∑ W ∈ good, (S.recLaw PT.parameter).w W) =
            (S.recLaw PT.parameter).pr S.AllGood := by
          simpa [P] using hgoodDen
        dsimp only [FinLaw.E, FinLaw.cond, SliceSolver.lowOut, P]
        simp only [good, Finset.mem_filter, Finset.mem_univ, true_and]
        calc
          _ = ∑ W, ((if S.AllGood W then (S.recLaw PT.parameter).w W else 0) *
              fSlice ((records s).symm W)) /
              (∑ W' ∈ good, (S.recLaw PT.parameter).w W') := by
            apply Finset.sum_congr rfl
            intro W _
            simp only [good, Finset.mem_filter, Finset.mem_univ, true_and]
            ring
          _ = (∑ W, (if S.AllGood W then (S.recLaw PT.parameter).w W else 0) *
              fSlice ((records s).symm W)) /
              (∑ W' ∈ good, (S.recLaw PT.parameter).w W') := by
            rw [← Finset.sum_div]
          _ = _ := by rw [hgoodDenS, hnumS]
      change (FinLaw.pi law).E fQin = (PT.π i).w y
      calc
        _ = (law s).E fSlice := hreplace.trans hcoord
        _ = S.lowOut PT.parameter g y := hcondE.trans hlow
        _ = (PT.π i).w y := (Q.profiled_valid.low_profile hMode i S hS g y).symm
    have hcap := Q.profiled_valid.law_cap i y
    calc
      _ ≤ (4 * B / L) * (R.history C).E fQin := hEbound
      _ = (4 * B / L) * (PT.π i).w y := by rw [hmeanQin]
      _ ≤ (4 * B / L) * (11 / (patch.M : ℝ)) :=
        mul_le_mul_of_nonneg_left hcap (by positivity)
      _ = 44 / (L * (patch.d : ℝ)) := by
        rw [← hbinReal]
        field_simp [ne_of_gt hLpos, ne_of_gt hBpos, ne_of_gt hdpos]
        ring
  · exact False.elim (hNotCluster hc)

/-- D5. Numerical room of the gate variance budget. Here `words = 2^h`,
`A = exp(2kT)` and `slices * words` is the cell size.
TeX 16:274–278; estimated proof: 120 lines. -/
theorem cluster_gate_budget_room {κ : CConsts} (hκ : κ.Admissible) :
    ∃ n₀ : ℕ, ∀ (n : ℕ) (L slices words A N : ℝ),
      n₀ ≤ n → 2 ≤ n → (n : ℝ) ^ (199 : ℕ) ≤ L → 0 ≤ slices → 1 ≤ words → words ≤ n →
      slices * words ≤ (n : ℝ) ^ (200 : ℕ) → 1 ≤ A → A ≤ n → 1 ≤ N → N ≤ n * 2 ^ n →
      (Real.rpow (n : ℝ) (1 / 2 : ℝ) + Real.log (max 1 N)) *
          (slices * (words * (64 * A / L)) ^ 2) ≤ 2 * (κ.θstar / 2) ^ 2 := by
  have hθ : 0 < κ.θstar := hκ.bucket.2.2.2.2
  let n₀ : ℕ := ⌈24576 / κ.θstar ^ 2⌉₊
  refine ⟨n₀, ?_⟩
  intro n L slices words A N hn₀ hn2 hL hslices hwords hwordsN hcell hA hAN hN hNbound
  let x : ℝ := n
  have hx2 : 2 ≤ x := by dsimp [x]; exact_mod_cast hn2
  have hx : 0 < x := by linarith
  have hx1 : 1 ≤ x := by linarith
  have hLp : 0 < L := lt_of_lt_of_le (pow_pos hx _) hL
  have hceil : 24576 / κ.θstar ^ 2 ≤ (n₀ : ℝ) := by
    change 24576 / κ.θstar ^ 2 ≤ (⌈24576 / κ.θstar ^ 2⌉₊ : ℝ)
    exact Nat.le_ceil _
  have hn₀' : (n₀ : ℝ) ≤ x := by
    dsimp [x]
    exact_mod_cast hn₀
  have hxpow : x ≤ x ^ (194 : ℕ) := by
    have hh := pow_le_pow_right₀ hx1 (by norm_num : 1 ≤ (194 : ℕ))
    simpa using hh
  have hthreshold : 24576 / κ.θstar ^ 2 ≤ x ^ (194 : ℕ) :=
    le_trans (le_trans hceil hn₀') hxpow
  have hbudget : 12288 / x ^ (194 : ℕ) ≤ κ.θstar ^ 2 / 2 := by
    apply (div_le_iff₀ (pow_pos hx 194)).2
    have hprod : 12288 ≤ (κ.θstar ^ 2 / 2) * x ^ (194 : ℕ) := by
      calc
        12288 = (κ.θstar ^ 2 / 2) * (24576 / κ.θstar ^ 2) := by
          field_simp [ne_of_gt hθ]
          norm_num
        _ ≤ (κ.θstar ^ 2 / 2) * x ^ (194 : ℕ) :=
          mul_le_mul_of_nonneg_left hthreshold (by positivity)
    nlinarith
  have hlogx : Real.log x ≤ x := by
    exact (Real.log_le_sub_one_of_pos hx).trans (by linarith)
  have hlog2 : Real.log (2 : ℝ) ≤ 1 := by
    exact (Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 2)).trans (by norm_num)
  have hmax : max 1 N ≤ x * 2 ^ n := by
    apply max_le
    · have hxreal : (1 : ℝ) ≤ x := hx1
      have hpow : (1 : ℝ) ≤ 2 ^ n := one_le_pow₀ (by norm_num : (1 : ℝ) ≤ 2)
      nlinarith
    · simpa [x] using hNbound
  have hlog : Real.log (max 1 N) ≤ 2 * x := by
    calc
      Real.log (max 1 N) ≤ Real.log (x * 2 ^ n) :=
        Real.log_le_log (by positivity) hmax
      _ = Real.log x + (n : ℝ) * Real.log 2 := by
        rw [Real.log_mul hx.ne' (by positivity), Real.log_pow]
      _ ≤ x + x := by
        have hnreal : (n : ℝ) = x := by rfl
        rw [hnreal]
        calc
          Real.log x + x * Real.log 2 ≤ x + x * 1 :=
            add_le_add hlogx (mul_le_mul_of_nonneg_left hlog2 hx.le)
          _ = x + x := by ring
      _ = 2 * x := by ring
  have hrpow : Real.rpow x (1 / 2 : ℝ) ≤ x := by
    simpa only [Real.rpow_eq_pow, Real.rpow_one] using
      Real.rpow_le_rpow_of_exponent_le hx1 (by norm_num : (1 / 2 : ℝ) ≤ 1)
  have hstat : Real.rpow x (1 / 2 : ℝ) + Real.log (max 1 N) ≤ 3 * x := by
    linarith
  have hratio : 0 ≤ 64 * A / L ∧ 64 * A / L ≤ 64 / x ^ (198 : ℕ) := by
    constructor
    · positivity
    · calc
        64 * A / L ≤ 64 * x / L :=
          div_le_div_of_nonneg_right (by nlinarith) hLp.le
        _ ≤ 64 * x / x ^ (199 : ℕ) :=
          div_le_div_of_nonneg_left (by positivity) (pow_pos hx 199) hL
        _ = 64 / x ^ (198 : ℕ) := by
          rw [show (199 : ℕ) = 198 + 1 by norm_num, pow_succ]
          field_simp [ne_of_gt hx] <;> ring
  have hratioSq : (64 * A / L) ^ 2 ≤ (64 / x ^ (198 : ℕ)) ^ 2 := by
    have hgap : 0 ≤ 64 / x ^ (198 : ℕ) - 64 * A / L := sub_nonneg.mpr hratio.2
    have hplus : 0 ≤ 64 * A / L + 64 / x ^ (198 : ℕ) := by positivity
    nlinarith [mul_nonneg hgap hplus]
  have hsw : slices * words ≤ x ^ (200 : ℕ) := by
    simpa [x] using hcell
  have hcoeff : slices * words ^ 2 ≤ x ^ (201 : ℕ) := by
    calc
      slices * words ^ 2 = (slices * words) * words := by ring
      _ ≤ x ^ (200 : ℕ) * x :=
        mul_le_mul hsw hwordsN (by positivity) (by positivity)
      _ = x ^ (201 : ℕ) := by rw [← pow_succ]
  have hwidth : slices * (words * (64 * A / L)) ^ 2 ≤ 4096 / x ^ (195 : ℕ) := by
    calc
      slices * (words * (64 * A / L)) ^ 2 =
          (slices * words ^ 2) * (64 * A / L) ^ 2 := by ring
      _ ≤ x ^ (201 : ℕ) * (64 / x ^ (198 : ℕ)) ^ 2 :=
        mul_le_mul hcoeff hratioSq (by positivity) (by positivity)
      _ = 4096 / x ^ (195 : ℕ) := by
        field_simp [ne_of_gt hx]
        ring
  have hstatNonneg : 0 ≤ Real.rpow x (1 / 2 : ℝ) + Real.log (max 1 N) := by
    exact add_nonneg (Real.rpow_nonneg hx.le _) (Real.log_nonneg (le_max_left 1 N))
  calc
    _ ≤ (3 * x) * (4096 / x ^ (195 : ℕ)) :=
      mul_le_mul hstat hwidth (by positivity) (by positivity)
    _ = 12288 / x ^ (194 : ℕ) := by
      field_simp [ne_of_gt hx]
      ring
    _ ≤ κ.θstar ^ 2 / 2 := hbudget
    _ = 2 * (κ.θstar / 2) ^ 2 := by ring

set_option maxHeartbeats 1600000 in
/-- D6. The cluster gate (assembled from D1-D5 plus Link/checks_cover).
TeX 16:259–278; estimated proof: 250 lines. -/
theorem cluster_load_gate {κ : CConsts} (hκ : κ.Admissible) :
    ∃ n₀ : ℕ, ∀ {T : Stage} {k : ℕ} {PT : ProfiledTiling κ T k} {K16 : ℝ}
      (Q : LowModeQuantFacts hκ (PT := PT) K16) (H : LowGeometryCertificate hκ Q)
      (R : CellRawData H.geom) (Perm : CellPermissions R) (K : CellRestrictedKernels R Perm),
      (∀ C pool W g, (∑ D ∈ Finset.univ.image pool, (K.qbar C W g).w D) = 0 →
        K.qtilde C pool W g = K.qbar C W g) →
      R.SourceValid → PT.tiling.mode.isCluster → n₀ ≤ T.S.n k →
      (∀ C W, (R.history C).w W ≠ 0 → PermissionLossHypotheses (Perm.table C) (R.qin C W)) →
      ∀ (C : H.geom.Cell) {Check : Type} [Fintype Check]
        (D : CellPoolDiagnostics (Fin (H.geom.nslot C)) (Bin PT.tiling (H.geom.cellPatch C))
          (R.Hist C) Check (T.S.n k) (1 / 2)),
        CellDiagnosticLink K C D → Nonempty (LoadGateHypotheses D) := by
  classical
  obtain ⟨nAmp, hAmp⟩ := Lane_sol_s16_prod1.cluster_slice_amplitude_room hκ
  obtain ⟨nBudget, hBudget⟩ := cluster_gate_budget_room hκ
  let cutoff := max nBudget (max nAmp ⌈Real.exp 1⌉₊)
  refine ⟨cutoff, ?_⟩
  intro T k PT K16 Q H R Perm K hFallback hR hc hn hPerm C Check instCheck D Link
  letI : DecidableEq (R.Hist C) := fun a b => Fintype.decidablePiFintype a b
  letI := instCheck
  have hnBudget : nBudget ≤ T.S.n k := by
    dsimp [cutoff] at hn
    omega
  have hnAmp : nAmp ≤ T.S.n k := by
    dsimp [cutoff] at hn
    omega
  have hnExp : ⌈Real.exp 1⌉₊ ≤ T.S.n k := by
    dsimp [cutoff] at hn
    omega
  have hMode : PT.tiling.mode = .lowCluster := by
    have hlow := Q.mode_low
    cases hm : PT.tiling.mode <;> simp_all [Mode.isCluster, Mode.isLow]
  let i := H.geom.cellPatch C
  let patch := PT.tiling.P i
  let n : ℝ := T.S.n k
  let L : ℝ := H.geom.nslot C
  let B : ℝ := Fintype.card (Bin PT.tiling i)
  let d : ℝ := patch.d
  let A : ℝ := Real.exp (2 * (sliceK κ patch.h : ℝ) * sliceT κ patch.h)
  let words : ℝ := Fintype.card (IWord PT.tiling i)
  let slices : ℝ := Fintype.card (R.Slice C)
  letI : Nonempty (Bin PT.tiling i) := D.bins_nonempty
  have hnpos : 0 < n := by
    dsimp [n]
    exact_mod_cast lt_of_lt_of_le (by norm_num : (0 : ℕ) < 2) Q.n_large
  have hBpos : 0 < B := by
    dsimp [B]
    exact_mod_cast Fintype.card_pos
  have hMnat : 0 < patch.M := by
    rw [← patch.cardY]
    exact_mod_cast Finset.card_pos.mpr
      (Q.profiled_valid.tiling_valid.patch_nonempty i).2
  have hbinSum := patch.bins.sum_card_parts
  have hparts : (∑ b ∈ patch.bins.parts, b.card) = patch.bins.parts.card * patch.d := by
    calc
      _ = ∑ b ∈ patch.bins.parts, patch.d := by
        apply Finset.sum_congr rfl
        intro b hb
        exact Q.profiled_valid.tiling_valid.bins_card i b hb
      _ = _ := by simp
  rw [hparts, patch.cardY] at hbinSum
  have hbinNat : Fintype.card (Bin PT.tiling i) * patch.d = patch.M := by
    change Fintype.card {b // b ∈ patch.bins.parts} * patch.d = patch.M
    rw [Fintype.card_of_subtype patch.bins.parts (fun _ => Iff.rfl)]
    exact hbinSum
  have hBnat : 0 < Fintype.card (Bin PT.tiling i) := by
    by_contra h
    have hz : Fintype.card (Bin PT.tiling i) = 0 := Nat.eq_zero_of_not_pos h
    rw [hz, zero_mul] at hbinNat
    omega
  have hdNat : 0 < patch.d := by
    by_contra h
    have hz : patch.d = 0 := Nat.eq_zero_of_not_pos h
    rw [hz, Nat.mul_zero] at hbinNat
    omega
  have hLnat : 0 < H.geom.nslot C := by
    change 0 < H.data.cells.nslot C
    rw [H.cell_partition.slot_count C]
    apply Nat.ceil_pos.mpr
    exact div_pos (mul_pos (lt_of_lt_of_le
      (div_pos (by norm_num) hκ.bucket.2.2.2.2) hκ.Kcell_big)
      (Real.rpow_pos_of_pos hnpos _)) (by exact_mod_cast hdNat)
  have hLpos : 0 < L := by
    dsimp [L]
    exact_mod_cast hLnat
  have hBpos' : 0 < (Fintype.card (Bin PT.tiling i) : ℝ) := by
    dsimp [B] at hBpos
    exact hBpos
  have hdpos : 0 < d := by
    dsimp [d]
    exact_mod_cast hdNat
  have hθ : 0 < κ.θstar := hκ.bucket.2.2.2.2
  have htheta : κ.θstar ≤ 1 := by
    have hb := hκ.bucket
    rw [hκ.clock.2.1] at hb
    have hKp : (40 : ℝ) ≤ κ.Kp := by exact_mod_cast hb.1
    nlinarith [mul_le_mul_of_nonneg_right hKp hκ.bucket.2.2.2.2.le]
  have hK : 0 < κ.Kcell := lt_of_lt_of_le
    (div_pos (by norm_num) hθ) hκ.Kcell_big
  have hK1 : 1 ≤ κ.Kcell := by
    have hh := (div_le_iff₀ hθ).mp hκ.Kcell_big
    nlinarith [mul_nonneg hK.le (sub_nonneg.mpr htheta)]
  have hslotReal : κ.Kcell * n ^ (200 : ℕ) / d ≤ L := by
    have heq := H.cell_partition.slot_count C
    change H.geom.nslot C =
      ⌈κ.Kcell * Real.rpow (T.S.n k : ℝ) κ.Ac / patch.d⌉₊ at heq
    rw [hκ.Ac_eq] at heq
    simp only [Real.rpow_eq_pow, Real.rpow_natCast] at heq
    dsimp [n, L, d]
    rw [heq]
    exact Nat.le_ceil _
  have hslotProduct : κ.Kcell * n ^ (200 : ℕ) ≤ L * d :=
    (div_le_iff₀ hdpos).mp hslotReal
  have hlog : 1 ≤ Real.log n := by
    have he : Real.exp 1 ≤ n := by
      dsimp [n]
      exact (Nat.le_ceil _).trans (by exact_mod_cast hnExp)
    have hh := Real.log_le_log (Real.exp_pos 1) he
    simpa only [Real.log_exp] using hh
  have hsqrt : Real.sqrt (Real.log n) ≤ Real.log n := by
    nlinarith [Real.sq_sqrt (by linarith : 0 ≤ Real.log n),
      sq_nonneg (Real.sqrt (Real.log n) - 1)]
  have hdle : d ≤ n := by
    calc
      d ≤ Real.exp (Real.sqrt (Real.log n)) := by
        dsimp [d, n]
        exact Q.bin_count_bound i
      _ ≤ Real.exp (Real.log n) := Real.exp_le_exp.mpr hsqrt
      _ = n := by rw [Real.exp_log hnpos]
  have hLlower : n ^ (199 : ℕ) ≤ L := by
    have hmul : n ^ (199 : ℕ) * n ≤ L * n := by
      calc
        n ^ (199 : ℕ) * n = n ^ (200 : ℕ) := by rw [← pow_succ]
        _ ≤ κ.Kcell * n ^ (200 : ℕ) :=
          by simpa only [one_mul] using
            (mul_le_mul_of_nonneg_right hK1 (pow_nonneg hnpos.le _))
        _ ≤ L * d := hslotProduct
        _ ≤ L * n := mul_le_mul_of_nonneg_left hdle hLpos.le
    exact le_of_mul_le_mul_right hmul hnpos
  have hAmpCell := hAmp (T.S.n k) patch.h hnAmp Q.n_large (Q.height_bound i)
  have hheight : 1 ≤ patch.h := by
    have hdy := (Q.profiled_valid.tiling_valid.cluster_data (Or.inl hMode) i).2.2.2.2.2.2.1
    have hp : 0 < patch.h := by rw [hdy]; positivity
    omega
  have hAone : 1 ≤ A := by
    dsimp [A]
    exact Real.one_le_exp_iff.mpr (by positivity)
  have hAmpBase : (16 * A) ^ patch.h ≤ n := by
    change (16 * Real.exp (2 * (sliceK κ patch.h : ℝ) * sliceT κ patch.h)) ^ patch.h ≤
      (T.S.n k : ℝ)
    exact hAmpCell.1
  have hAN : A ≤ n := by
    have hpow : A ≤ A ^ patch.h :=
      le_self_pow₀ hAone (Nat.one_le_iff_ne_zero.mp hheight)
    have hstep : A ^ patch.h ≤ (16 * A) ^ patch.h :=
      pow_le_pow_left₀ (by linarith [hAone]) (by nlinarith [hAone]) _
    exact hpow.trans (hstep.trans hAmpBase)
  have hwordsEq : words = (2 : ℝ) ^ patch.h := by
    dsimp [words]
    have hh : Fintype.card (IWord PT.tiling i) = 2 ^ patch.h := by
      simpa [patch, IWord, CubePos]
    exact_mod_cast hh
  have hwords1 : 1 ≤ words := by
    rw [hwordsEq]
    exact one_le_pow₀ (by norm_num : (1 : ℝ) ≤ 2)
  have hwordsN : words ≤ n := by
    rw [hwordsEq]
    have htwo : (2 : ℝ) ≤ 16 * A := by nlinarith [hAone]
    exact (pow_le_pow_left₀ (by norm_num) htwo _).trans hAmpBase
  have hRoles : (Fintype.card (OddCellRole H.geom C) : ℝ) ≤ n ^ (200 : ℕ) := by
    let positions : Finset (Pos T k) := Finset.univ.filter fun v => H.geom.cellOf v = C
    let f : OddCellRole H.geom C → {v // v ∈ positions} :=
      fun r => ⟨r.1, by simpa only [positions, Finset.mem_filter, Finset.mem_univ, true_and] using r.2.1⟩
    have hf : Function.Injective f := by
      intro r r' hh
      apply Subtype.ext
      have hv := congrArg Subtype.val hh
      change r.1 = r'.1 at hv
      exact hv
    have hcard := Fintype.card_le_of_injective f hf
    have hsize := H.cell_partition.cell_size C
    change positions.card ≤ ⌊Real.rpow (T.S.n k : ℝ) κ.Ac⌋₊ at hsize
    have hncard : Fintype.card (OddCellRole H.geom C) ≤
        ⌊Real.rpow (T.S.n k : ℝ) κ.Ac⌋₊ := by
      exact hcard.trans (by simpa only [Fintype.card_coe] using hsize)
    have hr : (Fintype.card (OddCellRole H.geom C) : ℝ) ≤
        Real.rpow (T.S.n k : ℝ) κ.Ac := by
      exact (show (Fintype.card (OddCellRole H.geom C) : ℝ) ≤
          (⌊Real.rpow (T.S.n k : ℝ) κ.Ac⌋₊ : ℝ) by exact_mod_cast hncard).trans
        (Nat.floor_le (Real.rpow_nonneg (Nat.cast_nonneg _) _))
    simpa only [n, hκ.Ac_eq, Real.rpow_eq_pow, Real.rpow_natCast] using hr
  have hCountCell : slices * words ≤ n ^ (200 : ℕ) := by
    let positions : Finset (Pos T k) := Finset.univ.filter fun v => H.geom.cellOf v = C
    have heq := Fintype.card_congr (R.cellWords C)
    rw [Fintype.card_prod] at heq
    have hsub : Fintype.card {v : Pos T k // H.geom.cellOf v = C} = positions.card :=
      Fintype.card_subtype (fun v : Pos T k => H.geom.cellOf v = C)
    rw [hsub] at heq
    have hcellEq : slices * words = (positions.card : ℝ) := by
      dsimp [slices, words]
      exact_mod_cast heq
    have hsize := H.cell_partition.cell_size C
    change positions.card ≤ ⌊Real.rpow (T.S.n k : ℝ) κ.Ac⌋₊ at hsize
    have hpos : (positions.card : ℝ) ≤ n ^ (200 : ℕ) := by
      calc
        _ ≤ (⌊Real.rpow (T.S.n k : ℝ) κ.Ac⌋₊ : ℝ) := by exact_mod_cast hsize
        _ ≤ Real.rpow (T.S.n k : ℝ) κ.Ac :=
          Nat.floor_le (Real.rpow_nonneg (Nat.cast_nonneg _) _)
        _ = n ^ (200 : ℕ) := by
          simp [n, hκ.Ac_eq, Real.rpow_eq_pow, Real.rpow_natCast]
    rw [hcellEq]
    exact hpos
  have hNpos : 1 ≤ (T.S.N k : ℝ) := by
    exact_mod_cast (Nat.succ_le_of_lt (T.S.N_pos k))
  have hNbound : (T.S.N k : ℝ) ≤ n * 2 ^ (T.S.n k) := by
    change (T.S.N k : ℝ) ≤ (T.S.n k : ℝ) * (2 : ℝ) ^ (T.S.n k)
    exact_mod_cast T.S.N_le k
  let Slice := R.Slice C
  let Value := fun s : Slice =>
    {z : R.Value C s // z ∈ R.slicePass C s ∧ (R.sliceLaw C s).w z ≠ 0}
  let P' : ∀ s : Slice, FinLaw (Value s) :=
    Classical.choose (Lane_q_s16_gate2.pi_cond_support_map (R.sliceLaw C) (R.slicePass C)
      (fun s => R.slice_pos C s))
  have hpush : R.history C = FinLaw.map (FinLaw.pi P') (fun z s => (z s).1) := by
    simpa [CellRawData.history, P', Value] using
      (Classical.choose_spec (Lane_q_s16_gate2.pi_cond_support_map (R.sliceLaw C) (R.slicePass C)
        (fun s => R.slice_pos C s)))
  let encode : (∀ s : Slice, Value s) → R.Hist C := fun z s => (z s).1
  let dPi : DecidableEq (R.Hist C) := fun a b => Fintype.decidablePiFintype a b
  let dClassical : DecidableEq (R.Hist C) := Classical.decEq _
  have hMapDecEq :
      @FinLaw.map (∀ s : Slice, Value s) (R.Hist C) _ _ dPi (FinLaw.pi P') encode =
        @FinLaw.map (∀ s : Slice, Value s) (R.Hist C) _ _ dClassical (FinLaw.pi P') encode := by
    have hdec : dPi = dClassical := Subsingleton.elim _ _
    rw [hdec]
  have hpushPi : R.history C =
      @FinLaw.map (∀ s : Slice, Value s) (R.Hist C) _ _ dPi (FinLaw.pi P') encode := by
    simpa [encode] using hpush
  have hpush' : R.history C =
      @FinLaw.map (∀ s : Slice, Value s) (R.Hist C) _ _ dClassical (FinLaw.pi P') encode :=
    hpushPi.trans hMapDecEq
  letI : DecidableEq (R.Hist C) := dClassical
  have hSupport (W : R.Hist C) (hW : (R.history C).w W ≠ 0) :
      ∀ s, W s ∈ R.slicePass C s ∧ (R.sliceLaw C s).w (W s) ≠ 0 := by
    intro s
    exact Lane_sol_s16_prod1.cond_support _ _ _ _
      (Lane_sol_s16_prod1.pi_support _ W hW s)
  have hSupportOf (W : R.Hist C)
      (hs : ∀ s, W s ∈ R.slicePass C s ∧ (R.sliceLaw C s).w (W s) ≠ 0) :
      (R.history C).w W ≠ 0 := by
    apply Finset.prod_ne_zero_iff.mpr
    intro s _
    simp only [CellRawData.history, FinLaw.pi, FinLaw.cond, if_pos (hs s).1]
    exact div_ne_zero (hs s).2 (R.slice_pos C s).ne'
  have hSomeHistory : ∃ W : R.Hist C, (R.history C).w W ≠ 0 := by
    by_contra h
    have hz : ∀ W : R.Hist C, (R.history C).w W = 0 := by simpa using h
    have hone := (R.history C).sum_one
    simp only [hz, Finset.sum_const_zero] at hone
    norm_num at hone
  obtain ⟨W0, hW0⟩ := hSomeHistory
  let extend := fun (s : Slice) (z : Value s) => Function.update W0 s z.1
  have hExtend (s : Slice) (z : Value s) : (R.history C).w (extend s z) ≠ 0 := by
    apply hSupportOf
    intro t
    by_cases ht : t = s
    · subst t
      simpa [extend] using z.2
    · simpa [extend, Function.update_of_ne ht] using (hSupport W0 hW0 t)
  have hEncodeSupport (z : ∀ s : Slice, Value s) : (R.history C).w (encode z) ≠ 0 := by
    apply hSupportOf
    intro s
    exact (z s).2
  let roleSlice := fun r : OddCellRole H.geom C =>
    ((R.cellWords C).symm ⟨r.1, r.2.1⟩).1
  let term := fun (pool : CellPool H.geom C) (W : R.Hist C)
      (r : OddCellRole H.geom C) (y : Fin (T.S.N k)) =>
    ∑ b, (K.qtilde C pool W (R.groupOf C r)).w b * (R.U C W (R.groupOf C r) b).w y
  let physicalLoad := fun (pool : CellPool H.geom C) (W : R.Hist C)
      (y : Fin (T.S.N k)) => ∑ r : OddCellRole H.geom C, term pool W r y
  let contribution := fun (pool : CellPool H.geom C) (s : Slice) (z : Value s)
      (y : D.LoadColumn) =>
    ∑ r ∈ Finset.univ.filter (fun r : OddCellRole H.geom C => roleSlice r = s),
      term pool (extend s z) r (Link.Column y)
  let range := fun (_ : Slice) => words * (64 * A / L)
  have hTermNonneg (pool : CellPool H.geom C) (W : R.Hist C)
      (r : OddCellRole H.geom C) (y : Fin (T.S.N k)) : 0 ≤ term pool W r y := by
    unfold term
    apply Finset.sum_nonneg
    intro b _
    exact mul_nonneg ((K.qtilde C pool W (R.groupOf C r)).nonneg b)
      ((R.U C W (R.groupOf C r) b).nonneg y)
  have hMass (pool : CellPool H.geom C) (hp : D.typical pool)
      (W : R.Hist C) (hW : (R.history C).w W ≠ 0) (g : R.Group C) :
      (1 - Real.rpow n (-4 : ℝ)) * (L / B) ≤
        ∑ b ∈ Finset.univ.image pool, (K.qbar C W g).w b := by
    have hnorm := (D.checks_cover pool hp.2).1 (Link.groupProbe g) W
    rw [Link.normalizer_eq pool W g hW] at hnorm
    have hratio : |(∑ b ∈ Finset.univ.image pool, (K.qbar C W g).w b) / (L / B) - 1| ≤
        Real.rpow n (-4 : ℝ) := by
      simpa [L, B, n] using hnorm
    have hlow : 1 - Real.rpow n (-4 : ℝ) ≤
        (∑ b ∈ Finset.univ.image pool, (K.qbar C W g).w b) / (L / B) := by
      linarith [(abs_le.mp hratio).1]
    exact (le_div_iff₀ (div_pos hLpos hBpos')).mp hlow
  have hn4 : Real.rpow n (-4 : ℝ) ≤ 1 / 2 := by
    have heq : Real.rpow n (-4 : ℝ) = (n ^ (4 : ℕ))⁻¹ := by
      norm_num [Real.rpow_neg, Real.rpow_natCast]
    rw [heq]
    have h16 : (16 : ℝ) ≤ n ^ (4 : ℕ) := by
      have hn2 : (2 : ℝ) ≤ n := by
        dsimp [n]
        exact_mod_cast Q.n_large
      have hp := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 2) hn2 (4 : ℕ)
      norm_num at hp ⊢
      exact hp
    have hpowpos : 0 < n ^ (4 : ℕ) := pow_pos hnpos _
    have hInv : (n ^ (4 : ℕ))⁻¹ ≤ (1 : ℝ) / 16 := by
      rw [inv_eq_one_div]
      apply (div_le_div_iff₀ hpowpos (by norm_num : (0 : ℝ) < 16)).2
      nlinarith
    linarith
  have hloadReindex (pool : CellPool H.geom C) (z : ∀ s : Slice, Value s)
      (y : D.LoadColumn) :
      D.loadValue pool (encode z) y = ∑ s, contribution pool s (z s) y := by
    have hLocal : ∀ r : OddCellRole H.geom C,
        term pool (encode z) r (Link.Column y) =
          term pool (extend (roleSlice r) (z (roleSlice r))) r (Link.Column y) := by
      intro r
      apply Lane_q_s16_gate2.cluster_role_term_local R Perm K hFallback hR hc C pool
        (encode z) (extend (roleSlice r) (z (roleSlice r)))
        (hEncodeSupport z) (hExtend (roleSlice r) (z (roleSlice r))) r ?_ (Link.Column y)
      change encode z (roleSlice r) =
        extend (roleSlice r) (z (roleSlice r)) (roleSlice r)
      simp [encode, extend]
    calc
      _ = ∑ r : OddCellRole H.geom C, term pool (encode z) r (Link.Column y) := by
        rw [Link.load_eq pool (encode z) y]
      _ = ∑ r : OddCellRole H.geom C,
          term pool (extend (roleSlice r) (z (roleSlice r))) r (Link.Column y) := by
        apply Finset.sum_congr rfl
        intro r _
        exact hLocal r
      _ = ∑ s : Slice, contribution pool s (z s) y := by
        change (∑ r : OddCellRole H.geom C,
            term pool (extend (roleSlice r) (z (roleSlice r))) r (Link.Column y)) = _
        simp only [contribution, Finset.sum_filter]
        symm
        rw [Finset.sum_comm]
        apply Finset.sum_congr rfl
        intro r _
        calc
          _ = ∑ x : Slice, if x = roleSlice r then
                term pool (extend x (z x)) r (Link.Column y) else 0 := by
            apply Finset.sum_congr rfl
            intro x _
            by_cases hx : roleSlice r = x
            · simp [hx]
            · have hx' : x ≠ roleSlice r := fun h => hx h.symm
              simp [hx, hx']
          _ = if roleSlice r ∈ (Finset.univ : Finset Slice) then
              term pool (extend (roleSlice r) (z (roleSlice r))) r (Link.Column y) else 0 :=
            Finset.sum_ite_eq' Finset.univ (roleSlice r)
              (fun x => term pool (extend x (z x)) r (Link.Column y))
          _ = _ := by simp
  have hloadDirect (pool : CellPool H.geom C) (z : ∀ s : Slice, Value s)
      (y : D.LoadColumn) :
      D.loadValue pool (encode z) y = physicalLoad pool (encode z) (Link.Column y) := by
    rw [Link.load_eq pool (encode z) y]

  have hMapEHist (g : R.Hist C → ℝ) :
      (FinLaw.map (FinLaw.pi P') encode).E g =
        (FinLaw.pi P').E (fun z => g (encode z)) :=
    HypercubeRamsey.Lane_q_s16_comp1.finlaw_map_E (FinLaw.pi P') encode g
  have hMeanEq (pool : CellPool H.geom C) (y : D.LoadColumn) :
      (D.historyLaw pool).E (fun W => D.loadValue pool W y) =
        (R.history C).E (fun W => physicalLoad pool W (Link.Column y)) := by
    calc
      _ = (FinLaw.map (FinLaw.pi P') encode).E (fun W => D.loadValue pool W y) := by
        rw [Link.history_eq pool, hpush']
      _ = (FinLaw.pi P').E (fun z => D.loadValue pool (encode z) y) := hMapEHist _
      _ = (FinLaw.pi P').E (fun z => physicalLoad pool (encode z) (Link.Column y)) := by
        congr 1
        funext z
        exact hloadDirect pool z y
      _ = (FinLaw.map (FinLaw.pi P') encode).E
          (fun W => physicalLoad pool W (Link.Column y)) := by
        symm
        exact hMapEHist _
      _ = _ := by rw [← hpush']
  have hEsum (pool : CellPool H.geom C) (y : Fin (T.S.N k)) :
      (R.history C).E (fun W => physicalLoad pool W y) =
        ∑ r : OddCellRole H.geom C, (R.history C).E (fun W => term pool W r y) := by
    unfold physicalLoad
    unfold FinLaw.E
    simp_rw [Finset.mul_sum]
    rw [Finset.sum_comm]
  have hMeanNum :
      (Fintype.card (OddCellRole H.geom C) : ℝ) * (44 / (L * d)) ≤ 44 / κ.Kcell := by
    have hrolesK : (Fintype.card (OddCellRole H.geom C) : ℝ) * κ.Kcell ≤ L * d := by
      calc
        _ ≤ n ^ (200 : ℕ) * κ.Kcell :=
          mul_le_mul_of_nonneg_right hRoles hK.le
        _ = κ.Kcell * n ^ (200 : ℕ) := by ring
        _ ≤ L * d := hslotProduct
    rw [show (Fintype.card (OddCellRole H.geom C) : ℝ) * (44 / (L * d)) =
        (44 * Fintype.card (OddCellRole H.geom C)) / (L * d) by ring]
    apply (div_le_div_iff₀ (mul_pos hLpos hdpos) hK).2
    nlinarith [hrolesK]
  have hMeanK : 44 / κ.Kcell ≤ κ.θstar / 2 := by
    calc
      44 / κ.Kcell ≤ 44 / (100 / κ.θstar) :=
        div_le_div_of_nonneg_left (by norm_num) (div_pos (by norm_num) hθ) hκ.Kcell_big
      _ = 44 * κ.θstar / 100 := by field_simp [ne_of_gt hθ]
      _ ≤ κ.θstar / 2 := by nlinarith
  have hMeanPhysical (pool : CellPool H.geom C) (hp : D.typical pool)
      (y : Fin (T.S.N k)) :
      (R.history C).E (fun W => physicalLoad pool W y) ≤ κ.θstar / 2 := by
    rw [hEsum]
    calc
      _ ≤ ∑ r : OddCellRole H.geom C, 44 / (L * d) := by
        apply Finset.sum_le_sum
        intro r _
        simpa [term, L, d] using
          (cluster_role_term_mean hκ Q H R Perm K hR hc hPerm C pool hn4
            (fun W hW g => hMass pool hp W hW g) r y)
      _ = (Fintype.card (OddCellRole H.geom C) : ℝ) * (44 / (L * d)) := by simp
      _ ≤ 44 / κ.Kcell := hMeanNum
      _ ≤ κ.θstar / 2 := hMeanK
  have hRoleAtCard (s : Slice) :
      (Finset.univ.filter (fun r : OddCellRole H.geom C => roleSlice r = s)).card ≤
        Fintype.card (IWord PT.tiling i) := by
    let F := Finset.univ.filter (fun r : OddCellRole H.geom C => roleSlice r = s)
    let RoleAt := {r : OddCellRole H.geom C // r ∈ F}
    let f : RoleAt → IWord PT.tiling i := fun rr =>
      ((R.cellWords C).symm ⟨rr.1.1, rr.1.2.1⟩).2
    have hf : Function.Injective f := by
      intro a b hab
      apply Subtype.ext
      apply Subtype.ext
      have hsa : roleSlice a.1 = s := (Finset.mem_filter.mp a.2).2
      have hsb : roleSlice b.1 = s := (Finset.mem_filter.mp b.2).2
      have hpair :
          ((R.cellWords C).symm ⟨a.1.1, a.1.2.1⟩) =
            ((R.cellWords C).symm ⟨b.1.1, b.1.2.1⟩) := by
        exact Prod.ext (hsa.trans hsb.symm) hab
      have hpos := (R.cellWords C).symm.injective hpair
      exact congrArg (fun v : {v : Pos T k // H.geom.cellOf v = C} => v.1) hpos
    have hcard := Fintype.card_le_of_injective f hf
    calc
      F.card = Fintype.card RoleAt := by
        symm
        exact Fintype.card_of_subtype F (fun _ => Iff.rfl)
      _ ≤ Fintype.card (IWord PT.tiling i) := hcard
  have hContributionRange (pool : CellPool H.geom C) (hp : D.typical pool)
      (s : Slice) (z : Value s) (y : D.LoadColumn) :
      0 ≤ contribution pool s z y ∧ contribution pool s z y ≤ range s := by
    have hcap : ∀ r : OddCellRole H.geom C,
        term pool (extend s z) r (Link.Column y) ≤ 64 * A / L := by
      intro r
      have hh := Lane_q_s16_gate2.cluster_role_term_cap hκ Q H R Perm K hR hc hPerm C pool
        (extend s z) (hExtend s z) hn4 (fun g => hMass pool hp (extend s z) (hExtend s z) g)
        r (Link.Column y)
      simpa [term, A, L] using hh
    constructor
    · unfold contribution
      apply Finset.sum_nonneg
      intro r hr
      exact hTermNonneg pool (extend s z) r (Link.Column y)
    · unfold contribution range
      have hsum := Finset.sum_le_sum (s := Finset.univ.filter
        (fun r : OddCellRole H.geom C => roleSlice r = s))
        (fun r _ => hcap r)
      calc
        _ ≤ ∑ _r ∈ Finset.univ.filter
            (fun r : OddCellRole H.geom C => roleSlice r = s), 64 * A / L := hsum
        _ = ((Finset.univ.filter
            (fun r : OddCellRole H.geom C => roleSlice r = s)).card : ℝ) * (64 * A / L) := by simp
        _ ≤ words * (64 * A / L) := by
          have hcard : ((Finset.univ.filter
              (fun r : OddCellRole H.geom C => roleSlice r = s)).card : ℝ) ≤ words := by
            dsimp [words]
            exact_mod_cast hRoleAtCard s
          exact mul_le_mul_of_nonneg_right hcard (by positivity)
  have hVarianceBudget :
      (Real.rpow n (1 / 2 : ℝ) + Real.log (max 1 (Fintype.card D.LoadColumn : ℝ))) *
        (∑ s : Slice, range s ^ 2) ≤ 2 * (D.loadThreshold / 2) ^ 2 := by
    have hsumRange : (∑ s : Slice, range s ^ 2) =
        slices * (words * (64 * A / L)) ^ 2 := by
      simp only [range, Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
      simp only [slices, Slice]
    have hcardColumn : Fintype.card D.LoadColumn = T.S.N k := by
      simpa only [Fintype.card_fin] using Fintype.card_congr Link.Column
    have hbudget := hBudget (T.S.n k) L slices words A (T.S.N k)
      hnBudget Q.n_large hLlower (by positivity) hwords1 hwordsN hCountCell
      hAone hAN hNpos hNbound
    rw [hsumRange, Link.threshold_eq, hcardColumn]
    simpa [n] using hbudget
  refine ⟨{
    n_large := Q.n_large
    exponent_pos := by norm_num
    Slice := Slice
    sliceFin := inferInstance
    sliceDec := inferInstance
    Value := Value
    valueFin := fun _ => inferInstance
    sliceLaw := fun _ s => P' s
    encode := encode
    history_eq := ?_
    contribution := contribution
    range := range
    range_nonneg := by intro s; positivity
    contribution_range := ?_
    load_eq := ?_
    threshold_pos := by rw [Link.threshold_eq]; exact hθ
    mean_small := ?_
    variance_budget := ?_ }⟩
  · intro pool
    rw [Link.history_eq pool]
    exact hpush'
  · intro pool hp s z y
    exact hContributionRange pool hp s z y
  · intro pool z y
    exact hloadReindex pool z y
  · intro pool hp y
    rw [Link.threshold_eq]
    calc
      _ = (R.history C).E (fun W => physicalLoad pool W (Link.Column y)) := hMeanEq pool y
      _ ≤ κ.θstar / 2 := hMeanPhysical pool hp (Link.Column y)
  · by_cases hz : (∑ s : Slice, range s ^ 2) = 0
    · exact Or.inl hz
    · have hnonneg : 0 ≤ ∑ s : Slice, range s ^ 2 :=
        Finset.sum_nonneg fun s _ => sq_nonneg (range s)
      have hpos : 0 < ∑ s : Slice, range s ^ 2 := lt_of_le_of_ne hnonneg (Ne.symm hz)
      refine Or.inr ⟨hpos, ?_⟩
      apply (le_div_iff₀ hpos).2
      simpa [Link.threshold_eq] using hVarianceBudget

/-! ## Assembly. -/

/-- Star checks (`none`) and pinned-star checks (`some (g, b)`), indexed by a
positive passing slice value, never by a whole-cell history. -/
abbrev ClusterStarCheck {κ : CConsts} {T : Stage} {k : ℕ} {PT : ProfiledTiling κ T k}
    {G : LowGeom PT} (R : CellRawData G) (C : G.Cell) :=
  (s : R.Slice C) × ({z : R.Value C s // z ∈ R.slicePass C s ∧ (R.sliceLaw C s).w z ≠ 0} ×
    EvenRole PT.tiling (G.cellPatch C) ×
    Option (HypercubeRamsey.Group PT.tiling (G.cellPatch C) × Bin PT.tiling (G.cellPatch C)))

/-- E1. Total check count (normalizer rows from `cluster_normalizer_setup`,
`hrowCount`, plus star/pin checks): cell size, `low_support`, `2^h <= n`
from the amplitude room, and `#bins <= N <= n 2^n`.
TeX 16:249–257; estimated proof: 100 lines. -/
theorem cluster_check_count {κ : CConsts} (hκ : κ.Admissible) :
    ∃ n₀ : ℕ, ∀ {T : Stage} {k : ℕ} {PT : ProfiledTiling κ T k} {K16 : ℝ}
      (Q : LowModeQuantFacts hκ (PT := PT) K16) (H : LowGeometryCertificate hκ Q)
      (R : CellRawData H.geom), R.SourceValid → PT.tiling.mode.isCluster → n₀ ≤ T.S.n k →
      ∀ (C : H.geom.Cell) (NormalizerCheck : Type) [Fintype NormalizerCheck],
        (Fintype.card NormalizerCheck : ℝ) ≤
          (T.S.n k : ℝ) ^ (200 : ℕ) * Real.exp ((T.S.n k : ℝ) ^ (1.01 : ℝ)) →
        (Fintype.card (NormalizerCheck ⊕ ClusterStarCheck R C) : ℝ) ≤
          Real.exp (3 * (T.S.n k : ℝ) ^ (1.01 : ℝ)) := by
  exact Lane_q_s16_conc.total_check_count hκ


end HypercubeRamsey.S16.ClusterDiagnostics
