import HypercubeRamsey.S16.Calibrations
import Mathlib.Probability.Moments.SubGaussian
import Mathlib.Probability.ProbabilityMassFunction.Integrals

/-! Lane-local weighted bounded-differences facts for Section 16. -/

namespace HypercubeRamsey.Lane_q_s16_comp1

open Classical
open scoped BigOperators
open Finset MeasureTheory ProbabilityTheory

noncomputable def finiteExpectation {Ω : Type*} [Fintype Ω]
    (w : Ω → ℝ) (f : Ω → ℝ) : ℝ := ∑ x, w x * f x

noncomputable def finiteProbability {Ω : Type*} [Fintype Ω]
    (w : Ω → ℝ) (E : Ω → Prop) : ℝ := by
  classical exact ∑ x, if E x then w x else 0

theorem finiteProbability_mono {Ω : Type*} [Fintype Ω]
    (w : Ω → ℝ) (hw : ∀ x, 0 ≤ w x) {E F : Ω → Prop}
    (hEF : ∀ x, E x → F x) :
    finiteProbability w E ≤ finiteProbability w F := by
  classical
  unfold finiteProbability
  apply Finset.sum_le_sum
  intro x _
  by_cases hE : E x
  · simp [hE, hEF x hE]
  · by_cases hF : F x <;> simp [hE, hF, hw x]

noncomputable def siteProductMass {I A : Type*} [Fintype I]
    (p : I → A → ℝ) (x : I → A) : ℝ := ∏ i, p i (x i)


theorem siteProductMass_cons {A : Type*} {n : ℕ} (p : Fin (n + 1) → A → ℝ)
    (a : A) (x : Fin n → A) :
    siteProductMass p (Fin.cons a x) =
      p 0 a * siteProductMass (fun i : Fin n => p (Fin.succ i)) x := by
  simp [siteProductMass, Fin.prod_univ_succ]

noncomputable def finiteMassLaw {A : Type*} [Fintype A]
    (p : A → ℝ) (hp : ∀ a, 0 ≤ p a) (hone : ∑ a, p a = 1) : PMF A :=
  PMF.ofFintype (fun a => ENNReal.ofReal (p a)) (by
    rw [← ENNReal.ofReal_sum_of_nonneg (fun a _ => hp a), hone]
    simp)

theorem finiteMassLaw_integral {A : Type*} [Fintype A]
    [MeasurableSpace A] [MeasurableSingletonClass A]
    (p : A → ℝ) (hp : ∀ a, 0 ≤ p a) (hone : ∑ a, p a = 1) (f : A → ℝ) :
    ∫ a, f a ∂(finiteMassLaw p hp hone).toMeasure = finiteExpectation p f := by
  rw [PMF.integral_eq_sum]
  simp only [finiteMassLaw, PMF.ofFintype_apply, ENNReal.toReal_ofReal (hp _),
    smul_eq_mul, finiteExpectation]

theorem finite_hoeffding {A : Type*} [Fintype A]
    (p : A → ℝ) (hp : ∀ a, 0 ≤ p a) (hone : ∑ a, p a = 1)
    (f : A → ℝ) {a b : ℝ} (hf : ∀ x, f x ∈ Set.Icc a b) (t : ℝ) :
    finiteExpectation p (fun x => Real.exp (t * (f x - finiteExpectation p f))) ≤
      Real.exp ((b - a) ^ 2 * t ^ 2 / 8) := by
  let _ : MeasurableSpace A := ⊤
  let μ : Measure A := (finiteMassLaw p hp hone).toMeasure
  have hsub := hasSubgaussianMGF_of_mem_Icc (μ := μ)
    (measurable_of_countable f).aemeasurable (ae_of_all μ hf)
  have hm := hsub.mgf_le t
  rw [mgf, finiteMassLaw_integral] at hm
  rw [finiteMassLaw_integral] at hm
  convert hm using 1
  congr 1
  simp only [NNReal.coe_pow, NNReal.coe_div, coe_nnnorm, NNReal.coe_ofNat, Real.norm_eq_abs,
    div_pow, sq_abs]
  ring

theorem finite_hoeffding_diameter {A : Type*} [Fintype A]
    (p : A → ℝ) (hp : ∀ a, 0 ≤ p a) (hone : ∑ a, p a = 1)
    (f : A → ℝ) {c : ℝ} (hf : ∀ x y, |f x - f y| ≤ c) (t : ℝ) :
    finiteExpectation p (fun x => Real.exp (t * (f x - finiteExpectation p f))) ≤
      Real.exp (c ^ 2 * t ^ 2 / 8) := by
  classical
  have hA : Nonempty A := by
    by_contra h
    have : IsEmpty A := not_nonempty_iff.mp h
    simp at hone
  obtain ⟨a, _, ha⟩ := (univ : Finset A).exists_min_image f univ_nonempty
  have hbound (x : A) : f x ∈ Set.Icc (f a) (f a + c) :=
    ⟨ha x (mem_univ _), by have := (abs_le.mp (hf x a)).2; linarith⟩
  simpa only [add_sub_cancel_left] using finite_hoeffding p hp hone f hbound t

theorem finiteExpectation_sub_le {A : Type*} [Fintype A]
    (p : A → ℝ) (hp : ∀ a, 0 ≤ p a) (hone : ∑ a, p a = 1)
    (f g : A → ℝ) {c : ℝ} (hfg : ∀ a, |f a - g a| ≤ c) :
    |finiteExpectation p f - finiteExpectation p g| ≤ c := by
  calc
    _ = |∑ a, p a * (f a - g a)| := by
      simp only [finiteExpectation, mul_sub, Finset.sum_sub_distrib]
    _ ≤ ∑ a, p a * |f a - g a| := by
      simpa only [abs_mul, abs_of_nonneg (hp _)] using
        (abs_sum_le_sum_abs (fun a => p a * (f a - g a)) univ)
    _ ≤ ∑ a, p a * c := Finset.sum_le_sum fun a _ =>
      mul_le_mul_of_nonneg_left (hfg a) (hp a)
    _ = c := by rw [← Finset.sum_mul, hone, one_mul]

theorem finite_product_expectation_cons {A : Type*} [Fintype A] {n : ℕ}
    (p : Fin (n + 1) → A → ℝ) (f : (Fin (n + 1) → A) → ℝ) :
    finiteExpectation (siteProductMass p) f =
      finiteExpectation (siteProductMass (fun i : Fin n => p (Fin.succ i)))
        (fun x => finiteExpectation (p 0) (fun a => f (Fin.cons a x))) := by
  classical
  unfold finiteExpectation
  rw [← (Fin.consEquiv (fun _ : Fin (n + 1) => A)).sum_comp]
  simp only [Fintype.sum_prod_type]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro x _
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro a _
  change siteProductMass p (Fin.cons a x) * f (Fin.cons a x) = _
  rw [siteProductMass_cons]
  ring

theorem finite_chernoff_bound {Ω : Type*} [Fintype Ω]
    (w : Ω → ℝ) (hw : ∀ x, 0 ≤ w x) (f : Ω → ℝ) (a : ℝ)
    {t : ℝ} (ht : 0 ≤ t) :
    finiteProbability w (fun x => a < f x) ≤
      Real.exp (-t * a) * finiteExpectation w (fun x => Real.exp (t * f x)) := by
  classical
  calc
    _ ≤ ∑ x, w x * (Real.exp (-t * a) * Real.exp (t * f x)) := by
      apply Finset.sum_le_sum
      intro x _
      by_cases hx : a < f x
      · simp only [hx, ite_true]
        have he : 1 ≤ Real.exp (-t * a) * Real.exp (t * f x) := by
          rw [← Real.exp_add, Real.one_le_exp_iff]
          have := mul_nonneg ht (sub_nonneg.mpr hx.le)
          nlinarith
        simpa only [mul_one] using mul_le_mul_of_nonneg_left he (hw x)
      · simp only [hx, ite_false]
        exact mul_nonneg (hw x) (mul_nonneg (Real.exp_pos _).le (Real.exp_pos _).le)
    _ = _ := by
      simp only [finiteExpectation, mul_sum]
      apply Finset.sum_congr rfl
      intro x _
      ring

noncomputable def dependentProductMass {I : Type*} [Fintype I]
    {A : I → Type*} [∀ i, Fintype (A i)]
    (p : ∀ i, A i → ℝ) (x : ∀ i, A i) : ℝ := ∏ i, p i (x i)

theorem dependentProductMass_cons {n : ℕ} {A : Fin (n + 1) → Type*}
    [∀ i, Fintype (A i)]
    (p : ∀ i, A i → ℝ) (a : A 0) (x : ∀ i : Fin n, A (Fin.succ i)) :
    dependentProductMass p (Fin.cons a x) =
      p 0 a * dependentProductMass (fun i : Fin n => p (Fin.succ i)) x := by
  simp [dependentProductMass, Fin.prod_univ_succ]

theorem dependentProductExpectation_cons {n : ℕ} {A : Fin (n + 1) → Type*}
    [∀ i, Fintype (A i)]
    (p : ∀ i, A i → ℝ) (f : (∀ i, A i) → ℝ) :
    finiteExpectation (dependentProductMass p) f =
      finiteExpectation (dependentProductMass (fun i : Fin n => p (Fin.succ i)))
        (fun x => finiteExpectation (p 0) (fun a => f (Fin.cons a x))) := by
  classical
  unfold finiteExpectation
  rw [← (Fin.consEquiv A).sum_comp]
  simp only [Fintype.sum_prod_type]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro x _
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro a _
  change dependentProductMass p (Fin.cons a x) * f (Fin.cons a x) = _
  rw [dependentProductMass_cons]
  ring

theorem weighted_product_mgf_dep_fin {n : ℕ} {A : Fin n → Type*}
    [∀ i, Fintype (A i)]
    (p : ∀ i, A i → ℝ) (hp : ∀ i a, 0 ≤ p i a)
    (hone : ∀ i, ∑ a, p i a = 1) (f : (∀ i, A i) → ℝ)
    (c : Fin n → ℝ)
    (hc : ∀ i x y, (∀ j, j ≠ i → x j = y j) → |f x - f y| ≤ c i)
    (t : ℝ) :
    finiteExpectation (dependentProductMass p)
      (fun x => Real.exp (t * (f x - finiteExpectation (dependentProductMass p) f))) ≤
        Real.exp ((∑ i, c i ^ 2) * t ^ 2 / 8) := by
  classical
  induction n with
  | zero => simp [finiteExpectation, dependentProductMass]
  | succ n ih =>
      let q : ∀ i : Fin n, A (Fin.succ i) → ℝ := fun i => p (Fin.succ i)
      let g : (∀ i : Fin n, A (Fin.succ i)) → ℝ := fun x =>
        finiteExpectation (p 0) (fun a => f (Fin.cons a x))
      have hmean : finiteExpectation (dependentProductMass p) f =
          finiteExpectation (dependentProductMass q) g :=
        dependentProductExpectation_cons p f
      have hg : ∀ i : Fin n, ∀ (x y : ∀ j : Fin n, A (Fin.succ j)),
          (∀ j, j ≠ i → x j = y j) → |g x - g y| ≤ c (Fin.succ i) := by
        intro i x y hxy
        apply finiteExpectation_sub_le (p 0) (hp 0) (hone 0)
        intro a
        apply hc (Fin.succ i) (Fin.cons a x) (Fin.cons a y)
        intro j hj
        cases j using Fin.cases with
        | zero => simp
        | succ j =>
            simp only [Fin.cons_succ]
            apply hxy j
            intro hji
            exact hj (congrArg Fin.succ hji)
      have hcond (x : ∀ i : Fin n, A (Fin.succ i)) :
          finiteExpectation (p 0)
            (fun a => Real.exp (t * (f (Fin.cons a x) - g x))) ≤
          Real.exp ((c 0) ^ 2 * t ^ 2 / 8) := by
        apply finite_hoeffding_diameter (p 0) (hp 0) (hone 0)
        intro a b
        apply hc 0 (Fin.cons a x) (Fin.cons b x)
        intro j hj
        cases j using Fin.cases with
        | zero => exact (False.elim (hj rfl))
        | succ j => rfl
      have hstep (x : ∀ i : Fin n, A (Fin.succ i)) :
          finiteExpectation (p 0)
            (fun a => Real.exp (t *
              (f (Fin.cons a x) - finiteExpectation (dependentProductMass q) g))) ≤
          Real.exp (t * (g x - finiteExpectation (dependentProductMass q) g)) *
            Real.exp ((c 0) ^ 2 * t ^ 2 / 8) := by
        calc
          _ = Real.exp (t * (g x - finiteExpectation (dependentProductMass q) g)) *
                finiteExpectation (p 0)
                  (fun a => Real.exp (t * (f (Fin.cons a x) - g x))) := by
            change (∑ a, p 0 a *
                Real.exp (t * (f (Fin.cons a x) - finiteExpectation (dependentProductMass q) g))) = _
            let k := Real.exp (t * (g x - finiteExpectation (dependentProductMass q) g))
            calc
              _ = ∑ a, p 0 a * (k * Real.exp (t * (f (Fin.cons a x) - g x))) := by
                apply Finset.sum_congr rfl
                intro a _
                dsimp [k]
                rw [show t * (f (Fin.cons a x) - finiteExpectation (dependentProductMass q) g) =
                  t * (g x - finiteExpectation (dependentProductMass q) g) +
                    t * (f (Fin.cons a x) - g x) by ring, Real.exp_add]
              _ = k * ∑ a, p 0 a * Real.exp (t * (f (Fin.cons a x) - g x)) := by
                rw [Finset.mul_sum]
                apply Finset.sum_congr rfl
                intro a _
                ring
          _ ≤ _ := mul_le_mul_of_nonneg_left (hcond x) (Real.exp_pos _).le
      rw [hmean, dependentProductExpectation_cons]
      calc
        _ ≤ finiteExpectation (dependentProductMass q)
            (fun x => Real.exp (t * (g x - finiteExpectation (dependentProductMass q) g)) *
              Real.exp ((c 0) ^ 2 * t ^ 2 / 8)) := by
          exact Finset.sum_le_sum fun x _ =>
            mul_le_mul_of_nonneg_left (hstep x)
              (Finset.prod_nonneg fun i _ => hp (Fin.succ i) (x i))
        _ = finiteExpectation (dependentProductMass q)
              (fun x => Real.exp (t * (g x - finiteExpectation (dependentProductMass q) g))) *
                Real.exp ((c 0) ^ 2 * t ^ 2 / 8) := by
          simp only [finiteExpectation, ← mul_assoc, Finset.sum_mul]
        _ ≤ Real.exp ((∑ i : Fin n, c (Fin.succ i) ^ 2) * t ^ 2 / 8) *
              Real.exp ((c 0) ^ 2 * t ^ 2 / 8) :=
          mul_le_mul_of_nonneg_right
            (ih q (fun i a => hp (Fin.succ i) a) (fun i => hone (Fin.succ i)) g
              (fun i => c (Fin.succ i)) (fun i x y hxy => hg i x y hxy))
            (Real.exp_pos _).le
        _ = Real.exp ((∑ i : Fin (n + 1), c i ^ 2) * t ^ 2 / 8) := by
          rw [← Real.exp_add]
          congr 1
          simp only [Fin.sum_univ_succ]
          ring

theorem weighted_product_tail_dep_fin {n : ℕ} {A : Fin n → Type*}
    [∀ i, Fintype (A i)]
    (p : ∀ i, A i → ℝ) (hp : ∀ i a, 0 ≤ p i a)
    (hone : ∀ i, ∑ a, p i a = 1) (f : (∀ i, A i) → ℝ)
    (c : Fin n → ℝ)
    (hc : ∀ i x y, (∀ j, j ≠ i → x j = y j) → |f x - f y| ≤ c i)
    {a : ℝ} (ha : 0 < a) (hvar : 0 < ∑ i, c i ^ 2) :
    finiteProbability (dependentProductMass p)
      (fun x => a < f x - finiteExpectation (dependentProductMass p) f) ≤
        Real.exp (-2 * a ^ 2 / (∑ i, c i ^ 2)) := by
  classical
  let S := ∑ i, c i ^ 2
  let t := 4 * a / S
  have ht : 0 ≤ t := (div_pos (by positivity) hvar).le
  have hw (x : ∀ i, A i) : 0 ≤ dependentProductMass p x :=
    Finset.prod_nonneg fun i _ => hp i (x i)
  calc
    _ ≤ Real.exp (-t * a) * finiteExpectation (dependentProductMass p)
        (fun x => Real.exp (t * (f x - finiteExpectation (dependentProductMass p) f))) :=
      finite_chernoff_bound _ hw _ _ ht
    _ ≤ Real.exp (-t * a) * Real.exp (S * t ^ 2 / 8) :=
      mul_le_mul_of_nonneg_left (weighted_product_mgf_dep_fin p hp hone f c hc t)
        (Real.exp_pos _).le
    _ = Real.exp (-2 * a ^ 2 / S) := by
      rw [← Real.exp_add]
      congr 1
      dsimp [t, S]
      field_simp [ne_of_gt hvar]
      ring

theorem weighted_product_tail_dep {I : Type*} [Fintype I] [DecidableEq I]
    {A : I → Type*} [∀ i, Fintype (A i)]
    (p : ∀ i, A i → ℝ) (hp : ∀ i a, 0 ≤ p i a)
    (hone : ∀ i, ∑ a, p i a = 1) (f : (∀ i, A i) → ℝ)
    (c : I → ℝ)
    (hc : ∀ i x y, (∀ j, j ≠ i → x j = y j) → |f x - f y| ≤ c i)
    {a : ℝ} (ha : 0 < a) (hvar : 0 < ∑ i, c i ^ 2) :
    finiteProbability (fun x : ∀ i, A i => ∏ i, p i (x i))
      (fun x => a < f x - finiteExpectation (fun x : ∀ i, A i => ∏ i, p i (x i)) f) ≤
        Real.exp (-2 * a ^ 2 / (∑ i, c i ^ 2)) := by
  classical
  let n := Fintype.card I
  let e : Fin n ≃ I := (Fintype.equivFin I).symm
  let A' := fun i : Fin n => A (e i)
  let E : (∀ i : Fin n, A' i) ≃ (∀ i : I, A i) := Equiv.piCongrLeft A e
  letI : ∀ i : Fin n, Fintype (A' i) := fun i => by
    dsimp [A']
    infer_instance
  let p' : ∀ i : Fin n, A' i → ℝ := fun i z => p (e i) z
  let f' : (∀ i : Fin n, A' i) → ℝ := fun x => f (E x)
  let c' : Fin n → ℝ := fun i => c (e i)
  let mass : (∀ i : I, A i) → ℝ := fun x => ∏ i, p i (x i)
  have hE_apply (x : ∀ i : Fin n, A' i) (s : I) :
      E x s = (e.apply_symm_apply s) ▸ x (e.symm s) := by
    exact Equiv.piCongrLeft_apply A e x s
  have hE_at (x : ∀ i : Fin n, A' i) (i : Fin n) : E x (e i) = x i := by
    have h := congrFun (E.left_inv x) i
    change ((Equiv.piCongrLeft A e).symm ((Equiv.piCongrLeft A e) x)) i = x i at h
    simpa only [Equiv.piCongrLeft_symm_apply] using h
  have hmass (x : ∀ i : Fin n, A' i) : dependentProductMass p' x = mass (E x) := by
    change (∏ i : Fin n, p (e i) (x i)) =
      ∏ s : I, p s (E x s)
    apply Fintype.prod_equiv e
    intro i
    rw [hE_at]
  have hlocal : ∀ i x y, (∀ j, j ≠ i → x j = y j) → |f' x - f' y| ≤ c' i := by
    intro i x y hxy
    apply hc (e i) (E x) (E y)
    intro s hs
    have hne : e.symm s ≠ i := by
      intro heq
      apply hs
      calc
        s = e (e.symm s) := by simp
        _ = e i := congrArg e heq
    have hxy' := hxy (e.symm s) hne
    change (Equiv.piCongrLeft A e) x s = (Equiv.piCongrLeft A e) y s
    rw [Equiv.piCongrLeft_apply, Equiv.piCongrLeft_apply]
    congr 1
  have hsumc : (∑ i : Fin n, c' i ^ 2) = ∑ i : I, c i ^ 2 := by
    apply Fintype.sum_equiv e
    intro i
    rfl
  have hvar' : 0 < ∑ i : Fin n, c' i ^ 2 := by rw [hsumc]; exact hvar
  have hp' : ∀ i z, 0 ≤ p' i z := fun i z => hp (e i) z
  have hone' : ∀ i, ∑ z, p' i z = 1 := fun i => hone (e i)
  have hmean : finiteExpectation mass f =
      finiteExpectation (dependentProductMass p') f' := by
    unfold finiteExpectation
    apply Fintype.sum_equiv E.symm
    intro x
    rw [hmass (E.symm x)]
    simp [mass, f', E, A']
  have hprob : finiteProbability mass
        (fun x => a < f x - finiteExpectation mass f) =
      finiteProbability (dependentProductMass p')
        (fun x => a < f' x - finiteExpectation (dependentProductMass p') f') := by
    unfold finiteProbability
    apply Fintype.sum_equiv E.symm
    intro x
    rw [hmass (E.symm x), hmean]
    simp [mass, f', E, A']
  rw [hprob, ← hsumc]
  exact weighted_product_tail_dep_fin p' hp' hone' f' c' hlocal ha hvar'


theorem weighted_product_mgf_fin {A : Type*} [Fintype A] [DecidableEq A]
    {n : ℕ} (p : Fin n → A → ℝ) (hp : ∀ i a, 0 ≤ p i a)
    (hone : ∀ i, ∑ a, p i a = 1) (f : (Fin n → A) → ℝ)
    (c : Fin n → ℝ)
    (hc : ∀ i x y, (∀ j, j ≠ i → x j = y j) → |f x - f y| ≤ c i)
    (t : ℝ) :
    finiteExpectation (siteProductMass p)
      (fun x => Real.exp (t * (f x - finiteExpectation (siteProductMass p) f)) ) ≤
        Real.exp ((∑ i, c i ^ 2) * t ^ 2 / 8) := by
  classical
  induction n with
  | zero => simp [finiteExpectation, siteProductMass]
  | succ n ih =>
      let q : Fin n → A → ℝ := fun i => p (Fin.succ i)
      let g : (Fin n → A) → ℝ := fun x =>
        finiteExpectation (p 0) (fun a => f (Fin.cons a x))
      have hmean : finiteExpectation (siteProductMass p) f =
          finiteExpectation (siteProductMass q) g :=
        finite_product_expectation_cons p f
      have hg : ∀ i (x y : Fin n → A),
          (∀ j, j ≠ i → x j = y j) → |g x - g y| ≤ c (Fin.succ i) := by
        intro i x y hxy
        apply finiteExpectation_sub_le (p 0) (hp 0) (hone 0)
        intro a
        apply hc (Fin.succ i) (Fin.cons a x) (Fin.cons a y)
        intro j hj
        cases j using Fin.cases with
        | zero => simp
        | succ j =>
            simp only [Fin.cons_succ]
            apply hxy j
            intro hji
            exact hj (congrArg Fin.succ hji)
      have hcond (x : Fin n → A) :
          finiteExpectation (p 0)
            (fun a => Real.exp (t * (f (Fin.cons a x) - g x))) ≤
          Real.exp ((c 0) ^ 2 * t ^ 2 / 8) := by
        apply finite_hoeffding_diameter (p 0) (hp 0) (hone 0)
        intro a b
        apply hc 0 (Fin.cons a x) (Fin.cons b x)
        intro j hj
        cases j using Fin.cases with
        | zero => exact (False.elim (hj rfl))
        | succ j => rfl
      have hstep (x : Fin n → A) :
          finiteExpectation (p 0)
            (fun a => Real.exp (t *
              (f (Fin.cons a x) - finiteExpectation (siteProductMass q) g))) ≤
          Real.exp (t * (g x - finiteExpectation (siteProductMass q) g)) *
            Real.exp ((c 0) ^ 2 * t ^ 2 / 8) := by
        calc
          _ = Real.exp (t * (g x - finiteExpectation (siteProductMass q) g)) *
                finiteExpectation (p 0)
                  (fun a => Real.exp (t * (f (Fin.cons a x) - g x))) := by
            change (∑ a, p 0 a *
                Real.exp (t * (f (Fin.cons a x) - finiteExpectation (siteProductMass q) g))) = _
            calc
              _ = ∑ a, p 0 a *
                    (Real.exp (t * (g x - finiteExpectation (siteProductMass q) g)) *
                      Real.exp (t * (f (Fin.cons a x) - g x))) := by
                apply Finset.sum_congr rfl
                intro a _
                rw [show t * (f (Fin.cons a x) - finiteExpectation (siteProductMass q) g) =
                  t * (g x - finiteExpectation (siteProductMass q) g) +
                    t * (f (Fin.cons a x) - g x) by ring, Real.exp_add]
              _ = Real.exp (t * (g x - finiteExpectation (siteProductMass q) g)) *
                    ∑ a, p 0 a * Real.exp (t * (f (Fin.cons a x) - g x)) := by
                rw [Finset.mul_sum]
                apply Finset.sum_congr rfl
                intro a _
                ring
          _ ≤ _ := mul_le_mul_of_nonneg_left (hcond x) (Real.exp_pos _).le
      rw [hmean, finite_product_expectation_cons]
      calc
        _ ≤ finiteExpectation (siteProductMass q)
            (fun x => Real.exp (t * (g x - finiteExpectation (siteProductMass q) g)) *
              Real.exp ((c 0) ^ 2 * t ^ 2 / 8)) := by
          exact sum_le_sum fun x _ =>
            mul_le_mul_of_nonneg_left (hstep x)
              (prod_nonneg fun i _ => hp (Fin.succ i) (x i))
        _ = finiteExpectation (siteProductMass q)
              (fun x => Real.exp (t * (g x - finiteExpectation (siteProductMass q) g))) *
                Real.exp ((c 0) ^ 2 * t ^ 2 / 8) := by
          simp only [finiteExpectation, ← mul_assoc, Finset.sum_mul]
        _ ≤ Real.exp ((∑ i : Fin n, c (Fin.succ i) ^ 2) * t ^ 2 / 8) *
              Real.exp ((c 0) ^ 2 * t ^ 2 / 8) := by
          exact mul_le_mul_of_nonneg_right
            (ih q (fun i a => hp (Fin.succ i) a) (fun i => hone (Fin.succ i)) g
              (fun i => c (Fin.succ i)) (fun i x y hxy => hg i x y hxy))
            (Real.exp_pos _).le
        _ = Real.exp ((∑ i : Fin (n + 1), c i ^ 2) * t ^ 2 / 8) := by
          rw [← Real.exp_add]
          congr 1
          simp only [Fin.sum_univ_succ]
          ring

theorem weighted_product_tail_fin {A : Type*} [Fintype A] [DecidableEq A]
    {n : ℕ} (p : Fin n → A → ℝ) (hp : ∀ i a, 0 ≤ p i a)
    (hone : ∀ i, ∑ a, p i a = 1) (f : (Fin n → A) → ℝ)
    (c : Fin n → ℝ)
    (hc : ∀ i x y, (∀ j, j ≠ i → x j = y j) → |f x - f y| ≤ c i)
    {a : ℝ} (ha : 0 < a) (hvar : 0 < ∑ i, c i ^ 2) :
    finiteProbability (siteProductMass p)
      (fun x => a < f x - finiteExpectation (siteProductMass p) f) ≤
        Real.exp (-2 * a ^ 2 / (∑ i, c i ^ 2)) := by
  classical
  let S := ∑ i, c i ^ 2
  let t := 4 * a / S
  have ht : 0 ≤ t := (div_pos (by positivity) hvar).le
  have hw (x : Fin n → A) : 0 ≤ siteProductMass p x :=
    prod_nonneg fun i _ => hp i (x i)
  calc
    _ ≤ Real.exp (-t * a) * finiteExpectation (siteProductMass p)
        (fun x => Real.exp (t * (f x - finiteExpectation (siteProductMass p) f))) :=
      finite_chernoff_bound _ hw _ _ ht
    _ ≤ Real.exp (-t * a) * Real.exp (S * t ^ 2 / 8) :=
      mul_le_mul_of_nonneg_left (weighted_product_mgf_fin p hp hone f c hc t)
        (Real.exp_pos _).le
    _ = Real.exp (-2 * a ^ 2 / S) := by
      rw [← Real.exp_add]
      congr 1
      dsimp [t, S]
      field_simp [ne_of_gt hvar]
      ring

theorem weighted_product_tail {I A : Type*} [Fintype I] [DecidableEq I]
    [Fintype A] [DecidableEq A]
    (p : I → A → ℝ) (hp : ∀ i a, 0 ≤ p i a)
    (hone : ∀ i, ∑ a, p i a = 1) (f : (I → A) → ℝ)
    (c : I → ℝ)
    (hc : ∀ i x y, (∀ j, j ≠ i → x j = y j) → |f x - f y| ≤ c i)
    {a : ℝ} (ha : 0 < a) (hvar : 0 < ∑ i, c i ^ 2) :
    finiteProbability (fun x : I → A => ∏ i, p i (x i))
      (fun x => a < f x - finiteExpectation (fun x : I → A => ∏ i, p i (x i)) f) ≤
        Real.exp (-2 * a ^ 2 / (∑ i, c i ^ 2)) := by
  classical
  let n := Fintype.card I
  let e : Fin n ≃ I := (Fintype.equivFin I).symm
  let E : (Fin n → A) ≃ (I → A) :=
    { toFun := fun (x : Fin n → A) => fun (i : I) => x (e.symm i)
      invFun := fun (x : I → A) => fun (i : Fin n) => x (e i)
      left_inv := by intro x; funext i; simp
      right_inv := by intro x; funext i; simp }
  let p' : Fin n → A → ℝ := fun i a => p (e i) a
  let f' : (Fin n → A) → ℝ := fun x => f (E x)
  let c' : Fin n → ℝ := fun i => c (e i)
  let mass : (I → A) → ℝ := fun x => ∏ i, p i (x i)
  have hmass (x : Fin n → A) : siteProductMass p' x = mass (E x) := by
    change (∏ i : Fin n, p (e i) (x i)) = ∏ s : I, p s (x (e.symm s))
    exact Fintype.prod_equiv e _ _ (fun _ => by simp)
  have hlocal : ∀ i x y, (∀ j, j ≠ i → x j = y j) → |f' x - f' y| ≤ c' i := by
    intro i x y hxy
    apply hc (e i) (E x) (E y)
    intro s hs
    apply hxy (e.symm s)
    intro heq
    apply hs
    calc
      s = e (e.symm s) := by simp
      _ = e i := congrArg e heq
  have hsumc : (∑ i : Fin n, c' i ^ 2) = ∑ i : I, c i ^ 2 := by
    apply Fintype.sum_equiv e
    intro i
    rfl
  have hvar' : 0 < ∑ i : Fin n, c' i ^ 2 := by rw [hsumc]; exact hvar
  have hp' : ∀ i a, 0 ≤ p' i a := fun i a => hp (e i) a
  have hone' : ∀ i, ∑ a, p' i a = 1 := fun i => hone (e i)
  have hmean : finiteExpectation mass f =
      finiteExpectation (siteProductMass p') f' := by
    unfold finiteExpectation
    apply Fintype.sum_equiv E.symm
    intro x
    rw [hmass (E.symm x)]
    simp [mass, f', E]
  have hprob : finiteProbability mass
        (fun x => a < f x - finiteExpectation mass f) =
      finiteProbability (siteProductMass p')
        (fun x => a < f' x - finiteExpectation (siteProductMass p') f') := by
    unfold finiteProbability
    apply Fintype.sum_equiv E.symm
    intro x
    rw [hmass (E.symm x), hmean]
    simp [mass, f', E]
  rw [hprob, ← hsumc]
  exact weighted_product_tail_fin p' hp' hone' f' c' hlocal ha hvar'

theorem weighted_product_abs_tail {I A : Type*} [Fintype I] [DecidableEq I]
    [Fintype A] [DecidableEq A]
    (p : I → A → ℝ) (hp : ∀ i a, 0 ≤ p i a)
    (hone : ∀ i, ∑ a, p i a = 1) (f : (I → A) → ℝ)
    (c : I → ℝ)
    (hc : ∀ i x y, (∀ j, j ≠ i → x j = y j) → |f x - f y| ≤ c i)
    {a : ℝ} (ha : 0 < a) (hvar : 0 < ∑ i, c i ^ 2) :
    finiteProbability (fun x : I → A => ∏ i, p i (x i))
      (fun x => a < |f x - finiteExpectation (fun x : I → A => ∏ i, p i (x i)) f|) ≤
        2 * Real.exp (-2 * a ^ 2 / (∑ i, c i ^ 2)) := by
  classical
  let mass : (I → A) → ℝ := fun x => ∏ i, p i (x i)
  have hw (x : I → A) : 0 ≤ mass x := prod_nonneg fun i _ => hp i (x i)
  have hupper := weighted_product_tail p hp hone f c hc ha hvar
  have hcneg : ∀ i x y, (∀ j, j ≠ i → x j = y j) → |(-f x) - (-f y)| ≤ c i := by
    intro i x y hxy
    have heq : (-f x) - (-f y) = -(f x - f y) := by ring
    rw [heq, abs_neg]
    exact hc i x y hxy
  have hlower := weighted_product_tail p hp hone (fun x => -f x) c hcneg ha hvar
  have hneg : finiteExpectation mass (fun x => -f x) = -finiteExpectation mass f := by
    unfold finiteExpectation
    rw [← Finset.sum_neg_distrib]
    apply Finset.sum_congr rfl
    intro x _
    ring
  have hlowerevent :
      (fun x : I → A => a < (-f x) - finiteExpectation mass (fun x => -f x)) =
        fun x => a < -(f x - finiteExpectation mass f) := by
    funext x
    rw [hneg]
    ring_nf
  unfold finiteProbability
  calc
    _ ≤ ∑ x,
        ((if a < f x - finiteExpectation mass f then mass x else 0) +
          (if a < -(f x - finiteExpectation mass f) then mass x else 0)) := by
      apply Finset.sum_le_sum
      intro x _
      by_cases hx : a < |f x - finiteExpectation mass f|
      · rcases (lt_abs.mp hx) with hpos | hneg
        · have hnoLower : ¬ a < -(f x - finiteExpectation mass f) := by linarith [hpos, ha]
          have hnoLower' : ¬ a < finiteExpectation (fun x : I → A => ∏ i, p i (x i)) f - f x := by
            simpa [mass] using hnoLower
          simp [hx, hpos, hnoLower', mass]
        · have hnoUpper : ¬ a < f x - finiteExpectation mass f := by linarith [hneg, ha]
          have hnoUpper' : ¬ a < f x - finiteExpectation (fun x : I → A => ∏ i, p i (x i)) f := by
            simpa [mass] using hnoUpper
          have hyesLower' : a < finiteExpectation (fun x : I → A => ∏ i, p i (x i)) f - f x := by
            simpa [mass] using hneg
          simp [hx, hnoUpper', hyesLower', mass]
      · have hnoUpper : ¬ a < f x - finiteExpectation mass f := by
          intro h
          exact hx ((lt_abs.mpr (Or.inl h)))
        have hnoLower : ¬ a < -(f x - finiteExpectation mass f) := by
          intro h
          exact hx ((lt_abs.mpr (Or.inr h)))
        have hnoUpper' : ¬ a < f x - finiteExpectation (fun x : I → A => ∏ i, p i (x i)) f := by
          simpa [mass] using hnoUpper
        have hnoLower' : ¬ a < finiteExpectation (fun x : I → A => ∏ i, p i (x i)) f - f x := by
          simpa [mass] using hnoLower
        simp [hx, hnoUpper', hnoLower', mass]
    _ = finiteProbability mass (fun x => a < f x - finiteExpectation mass f) +
          finiteProbability mass (fun x => a < -(f x - finiteExpectation mass f)) := by
      simp only [finiteProbability]
      rw [Finset.sum_add_distrib]
    _ ≤ Real.exp (-2 * a ^ 2 / (∑ i, c i ^ 2)) +
          Real.exp (-2 * a ^ 2 / (∑ i, c i ^ 2)) := by
      have hupper' : finiteProbability mass
          (fun x => a < f x - finiteExpectation mass f) ≤
            Real.exp (-2 * a ^ 2 / (∑ i, c i ^ 2)) := by
        simpa [mass] using hupper
      have hlower' : finiteProbability mass
          (fun x => a < -(f x - finiteExpectation mass f)) ≤
            Real.exp (-2 * a ^ 2 / (∑ i, c i ^ 2)) := by
        simpa [mass, hlowerevent] using hlower
      exact add_le_add hupper' hlower'
    _ = _ := by ring

theorem pi_pair_collision {I A : Type*} [Fintype I] [DecidableEq I]
    [Fintype A] [DecidableEq A]
    (P : I → FinLaw A) (i j : I) (hij : i ≠ j) :
    (FinLaw.pi P).pr (fun x => x i = x j) =
      ∑ a, (P i).w a * (P j).w a := by
  classical
  unfold FinLaw.pr FinLaw.pi
  simp only [FinLaw.w]
  change (∑ x : I → A, if x i = x j then ∏ t : I, (P t).w (x t) else 0) = _
  have hterm (x : I → A) :
      (if x i = x j then ∏ t : I, (P t).w (x t) else 0) =
        ∑ a : A, if x i = a ∧ x j = a then ∏ t : I, (P t).w (x t) else 0 := by
    by_cases h : x i = x j
    · rw [if_pos h]
      simp [h, Finset.sum_ite_eq]
    · rw [if_neg h]
      symm
      apply Finset.sum_eq_zero
      intro a _
      by_cases hia : x i = a
      · by_cases hja : x j = a
        · exact False.elim (h (hia.trans hja.symm))
        · simp [hia, hja]
      · simp [hia]
  calc
    (∑ x : I → A, if x i = x j then ∏ t : I, (P t).w (x t) else 0) =
        ∑ x : I → A, ∑ a : A, if x i = a ∧ x j = a then ∏ t : I, (P t).w (x t) else 0 := by
      apply Finset.sum_congr rfl
      intro x _
      exact hterm x
    _ = ∑ a : A, ∑ x : I → A, if x i = a ∧ x j = a then ∏ t : I, (P t).w (x t) else 0 := by
      exact Finset.sum_comm
    _ = ∑ a, (P i).w a * (P j).w a := by
      apply Finset.sum_congr rfl
      intro a _
      let allowed : I → Finset A := fun t =>
        if t = i ∨ t = j then {a} else Finset.univ
      let mass : (I → A) → ℝ := fun x => ∏ t, (P t).w (x t)
      have hmem (x : I → A) :
          (x i = a ∧ x j = a) ↔ x ∈ Fintype.piFinset allowed := by
        constructor
        · rintro ⟨hi, hj⟩
          apply Fintype.mem_piFinset.mpr
          intro t
          by_cases hti : t = i
          · subst t
            simp [allowed, hi]
          · by_cases htj : t = j
            · subst t
              simp [allowed, hij, hj]
            · simp [allowed, hti, htj]
        · intro hx
          have hx := Fintype.mem_piFinset.mp hx
          constructor
          · have h := hx i
            simpa [allowed] using h
          · have h := hx j
            simpa [allowed, hij] using h
      have hfiber :
          (∑ x, if x i = a ∧ x j = a then mass x else 0) =
            ∑ x ∈ Fintype.piFinset allowed, mass x := by
        calc
          _ = ∑ x, if x ∈ Fintype.piFinset allowed then mass x else 0 := by
            apply Finset.sum_congr rfl
            intro x _
            simp [hmem x]
          _ = ∑ x ∈ Fintype.piFinset allowed, mass x := by
            rw [← Finset.sum_filter]
            have hfilter :
                Finset.univ.filter (fun x : I → A =>
                  x ∈ Fintype.piFinset allowed) = Fintype.piFinset allowed := by
              ext x
              simp
            rw [hfilter]
      rw [hfiber, ← Finset.prod_univ_sum]
      have hfactor (t : I) :
          (∑ x ∈ allowed t, (P t).w x) =
            if t = i then (P i).w a else if t = j then (P j).w a else 1 := by
        by_cases hti : t = i
        · subst t
          simp [allowed]
        · by_cases htj : t = j
          · subst t
            simp [allowed, hti, hij.symm]
          · simp [allowed, hti, htj, (P t).sum_one]
      have hprod :
          (∏ t, ∑ x ∈ allowed t, (P t).w x) =
            (P i).w a * (P j).w a := by
        calc
          _ = ∏ t, (if t = i then (P i).w a else if t = j then (P j).w a else 1) := by
            apply Finset.prod_congr rfl
            intro t _
            exact hfactor t
          _ = _ := by
            have hsplit (t : I) :
                (if t = i then (P i).w a else if t = j then (P j).w a else 1) =
                  (if t = i then (P i).w a else 1) *
                    (if t = j then (P j).w a else 1) := by
              by_cases hti : t = i
              · subst t
                simp [hij]
              · by_cases htj : t = j
                · subst t
                  simp [hti, hij.symm]
                · simp [hti, htj]
            calc
              _ = ∏ t, (if t = i then (P i).w a else 1) *
                    (if t = j then (P j).w a else 1) := by
                apply Finset.prod_congr rfl
                intro t _
                exact hsplit t
              _ = (∏ t, if t = i then (P i).w a else 1) *
                    (∏ t, if t = j then (P j).w a else 1) := Finset.prod_mul_distrib
              _ = _ := by simp [Fintype.prod_ite_eq']
      exact hprod

theorem pi_pair_collision_uniform {I A : Type*} [Fintype I] [DecidableEq I]
    [Fintype A] [DecidableEq A] (P : I → FinLaw A)
    (hcard : 0 < (Fintype.card A : ℝ))
    (huniform : ∀ i a, (P i).w a = 1 / (Fintype.card A : ℝ))
    (i j : I) (hij : i ≠ j) :
    (FinLaw.pi P).pr (fun x => x i = x j) = 1 / (Fintype.card A : ℝ) := by
  rw [pi_pair_collision P i j hij]
  calc
    _ = ∑ a, (1 / (Fintype.card A : ℝ)) * (1 / (Fintype.card A : ℝ)) := by
      apply Finset.sum_congr rfl
      intro a _
      rw [huniform i a, huniform j a]
    _ = (Fintype.card A : ℝ) * ((1 / (Fintype.card A : ℝ)) ^ 2) := by
      calc
        _ = ∑ _a : A, (1 : ℝ) *
              ((1 / (Fintype.card A : ℝ)) * (1 / (Fintype.card A : ℝ))) := by
          apply Finset.sum_congr rfl
          intro a _
          ring
        _ = (∑ _a : A, (1 : ℝ)) *
              ((1 / (Fintype.card A : ℝ)) * (1 / (Fintype.card A : ℝ))) := by
          rw [← Finset.sum_mul]
        _ = _ := by simp [pow_two]
    _ = _ := by
      field_simp [ne_of_gt hcard]
      <;> ring

theorem finlaw_union_le {Ω J : Type*} [Fintype Ω] [Fintype J]
    (P : FinLaw Ω) (E : J → Ω → Prop) :
    P.pr (fun x => ∃ j, E j x) ≤ ∑ j, P.pr (E j) := by
  classical
  unfold FinLaw.pr
  rw [Finset.sum_comm]
  apply Finset.sum_le_sum
  intro x _
  by_cases hx : ∃ j, E j x
  · obtain ⟨j, hj⟩ := hx
    have hx' : (fun z : Ω => ∃ j, E j z) x := ⟨j, hj⟩
    rw [if_pos hx']
    calc
      P.w x = (if E j x then P.w x else 0) := (if_pos hj).symm
      _ ≤ ∑ j, if E j x then P.w x else 0 :=
        Finset.single_le_sum (f := fun j => if E j x then P.w x else 0)
          (fun j _ => by by_cases h : E j x <;> simp [h, P.nonneg x]) (Finset.mem_univ j)
  · calc
      _ = 0 := if_neg (by simpa using hx)
      _ ≤ ∑ j, if E j x then P.w x else 0 := Finset.sum_nonneg fun j _ => by
        by_cases h : E j x <;> simp [h, P.nonneg x]

theorem finlaw_map_pr {Ω Ψ : Type*} [Fintype Ω] [Fintype Ψ] [DecidableEq Ψ]
    (P : FinLaw Ω) (f : Ω → Ψ) (A : Ψ → Prop) :
    (FinLaw.map P f).pr A = P.pr (fun x => A (f x)) := by
  classical
  unfold FinLaw.pr FinLaw.map
  change (∑ y, if A y then ∑ x, if f x = y then P.w x else 0 else 0) = _
  calc
    _ = ∑ y, ∑ x, if A y ∧ f x = y then P.w x else 0 := by
      apply Finset.sum_congr rfl
      intro y _
      by_cases hA : A y
      · simp only [hA, if_true]
        apply Finset.sum_congr rfl
        intro x _
        by_cases hEq : f x = y <;> simp [hEq]
      · simp only [hA, if_false]
        symm
        apply Finset.sum_eq_zero
        intro x _
        simp [hA]
    _ = ∑ x, ∑ y, if A y ∧ f x = y then P.w x else 0 := Finset.sum_comm
    _ = ∑ x, if A (f x) then P.w x else 0 := by
      apply Finset.sum_congr rfl
      intro x _
      calc
        _ = ∑ y, if f x = y then (if A y then P.w x else 0) else 0 := by
          apply Finset.sum_congr rfl
          intro y _
          by_cases hA : A y <;> by_cases hEq : f x = y <;> simp [hA, hEq]
        _ = if A (f x) then P.w x else 0 := by simp [Finset.sum_ite_eq]

theorem finlaw_map_E {Ω Ψ : Type*} [Fintype Ω] [Fintype Ψ] [DecidableEq Ψ]
    (P : FinLaw Ω) (f : Ω → Ψ) (g : Ψ → ℝ) :
    (FinLaw.map P f).E g = P.E (fun x => g (f x)) := by
  classical
  unfold FinLaw.E FinLaw.map
  change (∑ y, (∑ x, if f x = y then P.w x else 0) * g y) = _
  calc
    _ = ∑ y, ∑ x, if f x = y then P.w x * g y else 0 := by
      apply Finset.sum_congr rfl
      intro y _
      rw [Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro x _
      by_cases hEq : f x = y <;> simp [hEq]
    _ = ∑ x, ∑ y, if f x = y then P.w x * g y else 0 := Finset.sum_comm
    _ = ∑ x, P.w x * g (f x) := by
      apply Finset.sum_congr rfl
      intro x _
      simp [Finset.sum_ite_eq]

theorem finlaw_bind_pr {Ω Ψ : Type*} [Fintype Ω] [Fintype Ψ]
    (P : FinLaw Ω) (K : Ω → FinLaw Ψ) (E : Ω → Ψ → Prop) :
    (FinLaw.bind P K).pr (fun xy => E xy.1 xy.2) =
      ∑ x, P.w x * (K x).pr (E x) := by
  classical
  unfold FinLaw.pr FinLaw.bind
  rw [Fintype.sum_prod_type]
  apply Finset.sum_congr rfl
  intro x _
  calc
    _ = ∑ y, P.w x * (if E x y then (K x).w y else 0) := by
      apply Finset.sum_congr rfl
      intro y _
      by_cases h : E x y <;> simp [h]
    _ = P.w x * ∑ y, if E x y then (K x).w y else 0 := by
      rw [Finset.mul_sum]

theorem zero_weight_change_constant {I A : Type*} [Fintype I] [DecidableEq I]
    (f : (I → A) → ℝ) (c : I → ℝ)
    (hchange : ∀ i x y, (∀ j, j ≠ i → x j = y j) → |f x - f y| ≤ c i)
    (hzero : ∑ i, c i ^ 2 = 0) : ∀ x y, f x = f y := by
  classical
  let path (x y : I → A) (S : Finset I) : I → A := fun i => if i ∈ S then y i else x i
  intro x y
  have hpath (S : Finset I) : f (path x y S) = f x := by
    induction S using Finset.induction_on with
    | empty => simp [path]
    | @insert i S hnot ih =>
        have hci : c i = 0 := by
          have hs := Finset.single_le_sum (f := fun j => c j ^ 2)
            (fun j _ => sq_nonneg (c j)) (Finset.mem_univ i)
          rw [hzero] at hs
          nlinarith [sq_nonneg (c i)]
        have hAgree : ∀ j, j ≠ i → path x y (insert i S) j = path x y S j := by
          intro j hji
          simp [path, Finset.mem_insert, hji]
        have hbound := hchange i (path x y (insert i S)) (path x y S) hAgree
        have heq : f (path x y (insert i S)) = f (path x y S) := by
          rw [hci] at hbound
          have habs := abs_eq_zero.mp
            (le_antisymm hbound (abs_nonneg (f (path x y (insert i S)) - f (path x y S))))
          linarith
        exact heq.trans ih
  have h := hpath (Finset.univ : Finset I)
  simpa [path] using h.symm

theorem uniform_pr_equiv {Ω Ψ : Type*} [Fintype Ω] [DecidableEq Ω]
    [Fintype Ψ] [DecidableEq Ψ]
    (S : Finset Ω) (hS : S.Nonempty) (T : Finset Ψ) (hT : T.Nonempty)
    (e : Ω ≃ Ψ) (he : ∀ x, x ∈ S ↔ e x ∈ T) (hcard : S.card = T.card)
    (A : Ψ → Prop) :
    (FinLaw.uniform S hS).pr (fun x => A (e x)) =
      (FinLaw.uniform T hT).pr A := by
  classical
  unfold FinLaw.pr FinLaw.uniform
  let g : Ψ → ℝ := fun y => if A y then if y ∈ T then 1 / (T.card : ℝ) else 0 else 0
  calc
    _ = ∑ x, g (e x) := by
      apply Finset.sum_congr rfl
      intro x _
      by_cases hA : A (e x) <;> simp [g, he x, hcard]
    _ = ∑ x, g x := Equiv.sum_comp e g

theorem finlaw_pr_fiber_sum {Ω A : Type*} [Fintype Ω] [Fintype A]
    (P : FinLaw Ω) (f : Ω → A) (E : Ω → Prop) :
    ∑ a, P.pr (fun x => E x ∧ f x = a) = P.pr E := by
  classical
  unfold FinLaw.pr
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro x _
  by_cases hx : E x
  · simp [hx, Finset.sum_ite_eq']
  · simp [hx]

theorem finlaw_pr_congr {Ω : Type*} [Fintype Ω] [DecidableEq Ω]
    (P : FinLaw Ω) {E F : Ω → Prop} (hEF : ∀ x, E x ↔ F x) :
    P.pr E = P.pr F := by
  classical
  unfold FinLaw.pr
  apply Finset.sum_congr rfl
  intro x _
  by_cases hE : E x
  · have hF : F x := (hEF x).mp hE
    simp [hE, hF]
  · have hF : ¬ F x := fun h => hE ((hEF x).mpr h)
    simp [hE, hF]

theorem finlaw_ext {Ω : Type*} [Fintype Ω] {P Q : FinLaw Ω}
    (h : ∀ x, P.w x = Q.w x) : P = Q := by
  cases P with
  | mk wP hwP hsumP =>
    cases Q with
    | mk wQ hwQ hsumQ =>
      have hw : wP = wQ := funext h
      cases hw
      have hn : hwP = hwQ := Subsingleton.elim _ _
      cases hn
      have hs : hsumP = hsumQ := Subsingleton.elim _ _
      cases hs
      rfl

theorem finlaw_eq_of_const_weights {Ω : Type*} [Fintype Ω] [DecidableEq Ω]
    (P Q : FinLaw Ω) (cP cQ : ℝ) (hΩ : Nonempty Ω)
    (hP : ∀ x, P.w x = cP) (hQ : ∀ x, Q.w x = cQ) : P = Q := by
  have hcard : (Fintype.card Ω : ℝ) ≠ 0 := by
    exact_mod_cast (Fintype.card_pos_iff.mpr hΩ).ne'
  have hsumP : (Fintype.card Ω : ℝ) * cP = 1 := by
    calc
      _ = ∑ x, P.w x := by simp [hP]
      _ = 1 := P.sum_one
  have hsumQ : (Fintype.card Ω : ℝ) * cQ = 1 := by
    calc
      _ = ∑ x, Q.w x := by simp [hQ]
      _ = 1 := Q.sum_one
  have hc : cP = cQ := mul_left_cancel₀ hcard (hsumP.trans hsumQ.symm)
  apply finlaw_ext
  intro x
  rw [hP x, hQ x, hc]

theorem finlaw_eq_of_const_on_set {Ω : Type*} [Fintype Ω] [DecidableEq Ω]
    (P Q : FinLaw Ω) (S : Finset Ω) (hS : S.Nonempty) (cP cQ : ℝ)
    (hPzero : ∀ x, x ∉ S → P.w x = 0) (hQzero : ∀ x, x ∉ S → Q.w x = 0)
    (hPconst : ∀ x ∈ S, P.w x = cP) (hQconst : ∀ x ∈ S, Q.w x = cQ) : P = Q := by
  have hcard : (S.card : ℝ) ≠ 0 := by
    exact_mod_cast (Finset.card_pos.mpr hS).ne'
  have hsum_eq (R : FinLaw Ω) (hzero : ∀ x, x ∉ S → R.w x = 0) :
      (∑ x, R.w x) = ∑ x ∈ S, R.w x := by
    calc
      _ = ∑ x, if x ∈ S then R.w x else 0 := by
        apply Finset.sum_congr rfl
        intro x _
        by_cases hx : x ∈ S
        · simp [hx]
        · simp [hx, hzero x hx]
      _ = _ := by rw [← Finset.sum_filter]; simp
  have hsumP : (S.card : ℝ) * cP = 1 := by
    calc
      _ = ∑ x ∈ S, cP := by simp
      _ = ∑ x ∈ S, P.w x := by
        apply Finset.sum_congr rfl
        intro x hx
        rw [hPconst x hx]
      _ = ∑ x, P.w x := (hsum_eq P hPzero).symm
      _ = 1 := P.sum_one
  have hsumQ : (S.card : ℝ) * cQ = 1 := by
    calc
      _ = ∑ x ∈ S, cQ := by simp
      _ = ∑ x ∈ S, Q.w x := by
        apply Finset.sum_congr rfl
        intro x hx
        rw [hQconst x hx]
      _ = ∑ x, Q.w x := (hsum_eq Q hQzero).symm
      _ = 1 := Q.sum_one
  have hc : cP = cQ := mul_left_cancel₀ hcard (hsumP.trans hsumQ.symm)
  apply finlaw_ext
  intro x
  by_cases hx : x ∈ S
  · rw [hPconst x hx, hQconst x hx, hc]
  · rw [hPzero x hx, hQzero x hx]

theorem finlaw_pr_filter_intersection {Ω : Type*} [Fintype Ω] [DecidableEq Ω]
    (P : FinLaw Ω) (S : Finset Ω) (E : Ω → Prop) :
    (∑ x ∈ S, if E x then P.w x else 0) =
      P.pr (fun x => x ∈ S ∧ E x) := by
  classical
  have hfilter : S.filter E = Finset.univ.filter (fun x => x ∈ S ∧ E x) := by
    ext x
    simp [and_comm]
  unfold FinLaw.pr
  calc
    _ = ∑ x ∈ S.filter E, P.w x := by rw [← Finset.sum_filter]
    _ = ∑ x ∈ Finset.univ.filter (fun x => x ∈ S ∧ E x), P.w x := by rw [hfilter]
    _ = ∑ x, if x ∈ S ∧ E x then P.w x else 0 := by rw [Finset.sum_filter]
    _ = P.pr (fun x => x ∈ S ∧ E x) := by
      unfold FinLaw.pr
      apply Finset.sum_congr rfl
      intro x _
      by_cases hS : x ∈ S <;> by_cases hE : E x <;> simp [hS, hE]

theorem finlaw_pr_filter {Ω : Type*} [Fintype Ω] [DecidableEq Ω]
    (P : FinLaw Ω) (S : Finset Ω) :
    (∑ x ∈ S, P.w x) = P.pr (fun x => x ∈ S) := by
  simpa using finlaw_pr_filter_intersection P S (fun _ => True)

theorem finlaw_cond_pr_ratio {Ω : Type*} [Fintype Ω] [DecidableEq Ω]
    (P : FinLaw Ω) (S : Finset Ω) (hS : 0 < ∑ x ∈ S, P.w x) (E : Ω → Prop) :
    (FinLaw.cond P S hS).pr E =
      (∑ x ∈ S, if E x then P.w x else 0) / (∑ x ∈ S, P.w x) := by
  classical
  calc
    _ = ∑ x, (if x ∈ S then (if E x then P.w x else 0) else 0) /
          (∑ x ∈ S, P.w x) := by
      unfold FinLaw.pr FinLaw.cond
      apply Finset.sum_congr rfl
      intro x _
      by_cases hE : E x <;> by_cases hmem : x ∈ S <;> simp [hE, hmem]
    _ = (∑ x, if x ∈ S then (if E x then P.w x else 0) else 0) /
          (∑ x ∈ S, P.w x) := by
      rw [← Finset.sum_div]
    _ = _ := by
      rw [← Finset.sum_filter]
      simp

theorem finlaw_cond_pr_ratio_event {Ω : Type*} [Fintype Ω] [DecidableEq Ω]
    (P : FinLaw Ω) (S : Finset Ω) (hS : 0 < ∑ x ∈ S, P.w x) (E : Ω → Prop) :
    (FinLaw.cond P S hS).pr E =
      P.pr (fun x => x ∈ S ∧ E x) / P.pr (fun x => x ∈ S) := by
  calc
    _ = (∑ x ∈ S, if E x then P.w x else 0) / (∑ x ∈ S, P.w x) :=
      finlaw_cond_pr_ratio P S hS E
    _ = _ := by
      rw [finlaw_pr_filter_intersection, finlaw_pr_filter]

theorem uniform_prod_eq_bind {A B : Type*} [Fintype A] [DecidableEq A]
    [Fintype B] [DecidableEq B] (ha : Nonempty A) (hb : Nonempty B) :
    (FinLaw.uniform (Finset.univ : Finset (A × B))
        ⟨(Classical.choice ha, Classical.choice hb), Finset.mem_univ _⟩) =
      FinLaw.bind (FinLaw.uniform (Finset.univ : Finset A)
          ⟨Classical.choice ha, Finset.mem_univ _⟩)
        (fun _ => FinLaw.uniform (Finset.univ : Finset B)
          ⟨Classical.choice hb, Finset.mem_univ _⟩) := by
  have hp : Nonempty (A × B) := Nonempty.map (fun a : A => (a, Classical.choice hb)) ha
  apply finlaw_eq_of_const_weights _ _
    (1 / (Fintype.card (A × B) : ℝ))
    ((1 / (Fintype.card A : ℝ)) * (1 / (Fintype.card B : ℝ))) hp
  · intro x
    simp [FinLaw.uniform]
  · intro x
    simp [FinLaw.bind, FinLaw.uniform]

theorem finlaw_bind_cond_pr_right {A B : Type*} [Fintype A] [DecidableEq A]
    [Fintype B] [DecidableEq B] (P : FinLaw A) (Q : FinLaw B)
    (Bfun : B → Prop) (Afun : A → Prop)
    (h : 0 < ∑ z ∈ Finset.univ.filter (fun z : A × B => Bfun z.2),
      (FinLaw.bind P (fun _ => Q)).w z) :
    (FinLaw.cond (FinLaw.bind P (fun _ => Q))
      (Finset.univ.filter (fun z : A × B => Bfun z.2)) h).pr
        (fun z => Afun z.1) = P.pr Afun := by
  classical
  have hden : (∑ z ∈ Finset.univ.filter (fun z : A × B => Bfun z.2),
        (FinLaw.bind P (fun _ => Q)).w z) = Q.pr Bfun := by
    calc
      _ = (FinLaw.bind P (fun _ => Q)).pr (fun z => Bfun z.2) := by
        unfold FinLaw.pr
        rw [Finset.sum_filter]
      _ = ∑ a, P.w a * Q.pr Bfun :=
        finlaw_bind_pr P (fun _ => Q) (fun _ b => Bfun b)
      _ = Q.pr Bfun := by
        rw [← Finset.sum_mul, P.sum_one, one_mul]
  have hnum : (∑ z ∈ Finset.univ.filter (fun z : A × B => Bfun z.2),
        if Afun z.1 then (FinLaw.bind P (fun _ => Q)).w z else 0) =
      P.pr Afun * Q.pr Bfun := by
    calc
      _ = (FinLaw.bind P (fun _ => Q)).pr (fun z => Bfun z.2 ∧ Afun z.1) := by
        unfold FinLaw.pr
        rw [Finset.sum_filter]
        apply Finset.sum_congr rfl
        intro z _
        by_cases hB : Bfun z.2 <;> by_cases hA : Afun z.1 <;> simp [hB, hA]
      _ = ∑ a, P.w a * (Q.pr fun b => Bfun b ∧ Afun a) :=
        finlaw_bind_pr P (fun _ => Q) (fun a b => Bfun b ∧ Afun a)
      _ = ∑ a, (if Afun a then P.w a else 0) * Q.pr Bfun := by
        apply Finset.sum_congr rfl
        intro a _
        by_cases hA : Afun a <;> simp [hA, FinLaw.pr, mul_comm]
      _ = (∑ a, if Afun a then P.w a else 0) * Q.pr Bfun := by
        rw [← Finset.sum_mul]
      _ = P.pr Afun * Q.pr Bfun := rfl
  have hratio := finlaw_cond_pr_ratio (FinLaw.bind P (fun _ => Q))
    (Finset.univ.filter (fun z : A × B => Bfun z.2)) h (fun z => Afun z.1)
  rw [hnum, hden] at hratio
  rw [hratio]
  have hQ : 0 < Q.pr Bfun := by rw [← hden]; exact h
  field_simp [ne_of_gt hQ]

theorem finlaw_bind_pr_first {A B : Type*} [Fintype A] [DecidableEq A]
    [Fintype B] [DecidableEq B] (P : FinLaw A) (Q : FinLaw B) (E : A → Prop) :
    (FinLaw.bind P (fun _ => Q)).pr (fun z => E z.1) = P.pr E := by
  have hQtrue : Q.pr (fun _ => True) = 1 := by
    simpa [FinLaw.pr] using Q.sum_one
  have hQpr (a : A) : Q.pr (fun _ => E a) = if E a then 1 else 0 := by
    by_cases hE : E a
    · simp [hE, hQtrue]
    · simp [hE, FinLaw.pr]
  calc
    _ = ∑ a, P.w a * Q.pr (fun _ => E a) := by
      simpa using finlaw_bind_pr P (fun _ => Q) (fun a _ => E a)
    _ = ∑ a, if E a then P.w a else 0 := by
      apply Finset.sum_congr rfl
      intro a _
      rw [hQpr a]
      by_cases hE : E a <;> simp [hE]
    _ = P.pr E := rfl

theorem finlaw_bind_cond_pr_left {A B : Type*} [Fintype A] [DecidableEq A]
    [Fintype B] [DecidableEq B] (P : FinLaw A) (Q : FinLaw B)
    (Bfun : A → Prop) (Afun : A → Prop)
    (h : 0 < ∑ z ∈ Finset.univ.filter (fun z : A × B => Bfun z.1),
      (FinLaw.bind P (fun _ => Q)).w z) :
    (FinLaw.cond (FinLaw.bind P (fun _ => Q))
      (Finset.univ.filter (fun z : A × B => Bfun z.1)) h).pr
        (fun z => Afun z.1) =
      (FinLaw.cond P (Finset.univ.filter Bfun)
        (by
          have hmass :
              (∑ z ∈ Finset.univ.filter (fun z : A × B => Bfun z.1),
                (FinLaw.bind P (fun _ => Q)).w z) =
                ∑ a ∈ Finset.univ.filter Bfun, P.w a := by
            calc
              _ = (FinLaw.bind P (fun _ => Q)).pr (fun z => Bfun z.1) := by
                unfold FinLaw.pr
                rw [Finset.sum_filter]
              _ = P.pr Bfun := finlaw_bind_pr_first P Q Bfun
              _ = ∑ a ∈ Finset.univ.filter Bfun, P.w a := by
                unfold FinLaw.pr
                rw [Finset.sum_filter]
          exact lt_of_lt_of_eq h hmass)
        ).pr Afun := by
  classical
  let S := Finset.univ.filter (fun z : A × B => Bfun z.1)
  let T := Finset.univ.filter Bfun
  have hmass : (∑ z ∈ S, (FinLaw.bind P (fun _ => Q)).w z) =
      ∑ a ∈ T, P.w a := by
    calc
      _ = (FinLaw.bind P (fun _ => Q)).pr (fun z => Bfun z.1) := by
        unfold S FinLaw.pr
        rw [Finset.sum_filter]
      _ = P.pr Bfun := finlaw_bind_pr_first P Q Bfun
      _ = ∑ a ∈ T, P.w a := by
        unfold T FinLaw.pr
        rw [Finset.sum_filter]
  have hlocal : 0 < ∑ a ∈ T, P.w a := lt_of_lt_of_eq h hmass
  have hnum : (∑ z ∈ S, if Afun z.1 then (FinLaw.bind P (fun _ => Q)).w z else 0) =
      P.pr (fun a => Bfun a ∧ Afun a) := by
    calc
      _ = (FinLaw.bind P (fun _ => Q)).pr (fun z => Bfun z.1 ∧ Afun z.1) := by
        unfold S FinLaw.pr
        rw [Finset.sum_filter]
        apply Finset.sum_congr rfl
        intro z _
        by_cases hB : Bfun z.1 <;> by_cases hA : Afun z.1 <;> simp [hB, hA]
      _ = P.pr (fun a => Bfun a ∧ Afun a) :=
        finlaw_bind_pr_first P Q (fun a => Bfun a ∧ Afun a)
  have hnumLocal : (∑ a ∈ T, if Afun a then P.w a else 0) =
      P.pr (fun a => Bfun a ∧ Afun a) := by
    unfold T FinLaw.pr
    rw [Finset.sum_filter]
    apply Finset.sum_congr rfl
    intro a _
    by_cases hB : Bfun a <;> by_cases hA : Afun a <;> simp [hB, hA]
  have hratioGlobal := finlaw_cond_pr_ratio (FinLaw.bind P (fun _ => Q)) S h
    (fun z => Afun z.1)
  have hratioLocal := finlaw_cond_pr_ratio P T hlocal Afun
  rw [hnum, hmass] at hratioGlobal
  rw [hnumLocal] at hratioLocal
  exact hratioGlobal.trans hratioLocal.symm

theorem uniform_prod_pr_fst {A B : Type*} [Fintype A] [DecidableEq A]
    [Fintype B] [DecidableEq B] (ha : Nonempty A) (hb : Nonempty B) (E : A → Prop) :
    (FinLaw.uniform (Finset.univ : Finset (A × B))
      ⟨(Classical.choice ha, Classical.choice hb), Finset.mem_univ _⟩).pr
      (fun z => E z.1) =
    (FinLaw.uniform (Finset.univ : Finset A)
      ⟨Classical.choice ha, Finset.mem_univ _⟩).pr E := by
  rw [uniform_prod_eq_bind ha hb]
  rw [finlaw_bind_pr (FinLaw.uniform (Finset.univ : Finset A)
    ⟨Classical.choice ha, Finset.mem_univ _⟩)
    (fun _ => FinLaw.uniform (Finset.univ : Finset B)
      ⟨Classical.choice hb, Finset.mem_univ _⟩) (fun a _ => E a)]
  let Q : FinLaw B := FinLaw.uniform (Finset.univ : Finset B)
    ⟨Classical.choice hb, Finset.mem_univ _⟩
  have hQtrue : Q.pr (fun _ => True) = 1 := by
    simpa [Q, FinLaw.pr] using Q.sum_one
  have hQpr (a : A) : Q.pr (fun _ => E a) = if E a then 1 else 0 := by
    by_cases hE : E a
    · simp [hE, hQtrue]
    · simp [hE, FinLaw.pr]
  calc
    _ = ∑ a, if E a then
          (FinLaw.uniform (Finset.univ : Finset A)
            ⟨Classical.choice ha, Finset.mem_univ _⟩).w a else 0 := by
      apply Finset.sum_congr rfl
      intro a _
      rw [hQpr a]
      by_cases hE : E a <;> simp [hE]
    _ = (FinLaw.uniform (Finset.univ : Finset A)
          ⟨Classical.choice ha, Finset.mem_univ _⟩).pr E := rfl

end HypercubeRamsey.Lane_q_s16_comp1
