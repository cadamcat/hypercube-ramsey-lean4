import HypercubeRamsey.S03.Injection.Comparison
import HypercubeRamsey.S03.Injection.Nodes_q_inj_nodes

/-!
Lemma 3.9 assemblies and calibration. Concrete sequential/forcing processes and the
Steps 2–3 estimates are in `Sampler` and `Comparison`. The final export and the price
witness have no local placeholder; analytic nodes remain assigned proof obligations.
-/

namespace HypercubeRamsey

open Filter
open scoped BigOperators

/-- Label mass of a full-output law, in the form used by the side-data transfer. -/
noncomputable def injectionLabelMass {Ω : Type*} [Fintype Ω] {d : ℕ}
    (p : FinProb Ω) (lab : Ω → Fin d) (y : Fin d) : ℝ :=
  ∑ o, if lab o = y then p.w o else 0

/-- A label law is supported on injective assignments. -/
def LabelInjectionSupported {R : Type*} [Fintype R] [DecidableEq R] {d : ℕ}
    (Q : FinProb (R → Fin d)) : Prop :=
  ∀ x, Q.w x ≠ 0 → Function.Injective x

/-- The near-product upper bounds for prescribed labels. -/
def LabelNearProductBound {R : Type*} [Fintype R] [DecidableEq R] (d : ℕ)
    (q : R → Fin d → ℝ) (Q : FinProb (R → Fin d)) : Prop :=
  ∀ (S : Finset R) (y : R → Fin d), (S.card : ℝ) ≤ (d : ℝ) ^ (0.025 : ℝ) →
    Q.pr (fun x => ∀ i ∈ S, x i = y i) ≤
      Real.exp ((d : ℝ) ^ (-(0.04 : ℝ)) * S.card) * ∏ i ∈ S, q i (y i)

/-- The price of a label law and a comparison price of the target marginals. -/
noncomputable def injectionLabelPrice {R : Type*} [Fintype R] [DecidableEq R] {d : ℕ}
    (Q : FinProb (R → Fin d)) (c : R → Fin d → ℝ) : ℝ :=
  ∑ i, ∑ y, c i y * Q.pr (fun x => x i = y)

noncomputable def injectionTargetPrice {R : Type*} [Fintype R] [DecidableEq R] {d : ℕ}
    (q : R → Fin d → ℝ) (c : R → Fin d → ℝ) : ℝ :=
  ∑ i, ∑ y, c i y * q i y

/-- The vector of one-coordinate marginals of a label law. -/
noncomputable def LabelMarginalVector {R : Type*} [Fintype R] [DecidableEq R] {d : ℕ}
    (Q : FinProb (R → Fin d)) : (R × Fin d) → ℝ :=
  fun iy => Q.pr (fun x => x iy.1 = iy.2)

/-- The feasible marginal vectors of injective label laws satisfying the near-product bounds. -/
def LabelMarginalImage {R : Type*} [Fintype R] [DecidableEq R] (d : ℕ)
    (q : R → Fin d → ℝ) : Set ((R × Fin d) → ℝ) :=
  {v | ∃ Q : FinProb (R → Fin d), LabelInjectionSupported Q ∧
    LabelNearProductBound d q Q ∧ ∀ i y, v (i, y) = LabelMarginalVector Q (i, y)}

/-- Step 1 (03:627–647), with the relaxed atom cap needed after price perturbation.
Only dummy rows have the `10/d` cap. The actual order is part of the witness. -/
theorem balanced_completion_good_order :
    ∀ᶠ d : ℕ in Filter.atTop, ∀ {R : Type} [Fintype R] [DecidableEq R]
      (q : R → Fin d → ℝ),
      (∀ i y, 0 ≤ q i y) → (∀ i, ∑ y, q i y = 1) →
      (∀ i y, q i y ≤ 2 * (d : ℝ) ^ (-(0.95 : ℝ))) →
      (∀ y, ∑ i, q i y ≤ 1 / 2) →
      ∃ t : ℕ, t = Nat.ceil ((2 / 3 : ℝ) * d) ∧ Fintype.card R ≤ t ∧
        ∃ qbar : (R ⊕ Fin (t - Fintype.card R)) → Fin d → ℝ,
          ∃ e : Fin t ≃ (R ⊕ Fin (t - Fintype.card R)),
            (∀ i y, qbar (Sum.inl i) y = q i y) ∧
            (∀ j y, qbar (Sum.inr j) y =
              ((t : ℝ) / d - ∑ i, q i y) / (t - Fintype.card R : ℕ)) ∧
            (∀ j y, qbar (Sum.inr j) y ≤ 10 / d) ∧
            (∀ y, ∑ j, qbar j y = (t : ℝ) / d) ∧
            Injection.OrderedInput d t (fun k y => qbar (e k) y) := by
  classical
  have hsqrtT : Tendsto (fun n : ℕ => Real.sqrt (n : ℝ)) atTop atTop := by
    have h := (tendsto_rpow_atTop (by norm_num : (0 : ℝ) < 1 / 2)).comp
      tendsto_natCast_atTop_atTop
    simpa only [Function.comp_def, Real.sqrt_eq_rpow] using h
  have hpolyExp : Tendsto
      (fun n : ℕ => (Real.sqrt (n : ℝ)) ^ 4 *
        Real.exp (-(1 / 2 : ℝ) * Real.sqrt (n : ℝ))) atTop (nhds 0) := by
    have h := (tendsto_rpow_mul_exp_neg_mul_atTop_nhds_zero
      (4 : ℝ) (1 / 2 : ℝ) (by norm_num)).comp hsqrtT
    have hfun : (fun n : ℕ => (Real.sqrt (n : ℝ)) ^ (4 : ℝ) *
        Real.exp (-(1 / 2 : ℝ) * Real.sqrt (n : ℝ))) =
        (fun n : ℕ => (Real.sqrt (n : ℝ)) ^ 4 *
          Real.exp (-(1 / 2 : ℝ) * Real.sqrt (n : ℝ))) := by
      funext n
      congr 1
      exact Real.rpow_natCast _ _
    rw [← hfun]
    simpa only [Function.comp_def] using h
  have hsmallT : ∀ᶠ n : ℕ in atTop, 2 * (Real.sqrt (n : ℝ)) ^ 4 *
      Real.exp (-(1 / 2 : ℝ) * Real.sqrt (n : ℝ)) < 1 := by
    have h := hpolyExp.const_mul 2
    simpa [mul_assoc] using
      h.eventually (Iio_mem_nhds (by norm_num : 2 * (0 : ℝ) < 1))
  filter_upwards [Filter.eventually_ge_atTop 100, hsmallT] with d hd hsmall
  intro R hR hdec q hq0 hqsum hqcap hqload
  have hdR : (100 : ℝ) ≤ (d : ℝ) := by exact_mod_cast hd
  have hdpos : (0 : ℝ) < (d : ℝ) := by linarith
  have hbase : (1 : ℝ) ≤ (d : ℝ) := by linarith
  have hloadTotal : (∑ y : Fin d, ∑ i : R, q i y) = (Fintype.card R : ℝ) := by
    rw [Finset.sum_comm]
    calc
      (∑ i : R, ∑ y : Fin d, q i y) = ∑ i : R, (1 : ℝ) := by
        apply Finset.sum_congr rfl
        intro i hi
        exact hqsum i
      _ = (Fintype.card R : ℝ) := by simp
  have hrowsR : (Fintype.card R : ℝ) ≤ (d : ℝ) / 2 := by
    calc
      (Fintype.card R : ℝ) = ∑ y : Fin d, ∑ i : R, q i y := hloadTotal.symm
      _ ≤ ∑ y : Fin d, (1 / 2 : ℝ) :=
        Finset.sum_le_sum fun y hy => hqload y
      _ = (d : ℝ) / 2 := by
        rw [Finset.sum_const]
        simp [Fintype.card_fin, nsmul_eq_mul]
        ring
  let t : ℕ := Nat.ceil ((2 / 3 : ℝ) * (d : ℝ))
  let m : ℕ := t - Fintype.card R
  have htlo : (2 / 3 : ℝ) * (d : ℝ) ≤ (t : ℝ) := by
    dsimp [t]
    exact Nat.le_ceil _
  have htup : (t : ℝ) ≤ (2 / 3 : ℝ) * (d : ℝ) + 1 := by
    dsimp [t]
    have hnat := Nat.ceil_le_floor_add_one ((2 / 3 : ℝ) * (d : ℝ))
    have hnatR : (Nat.ceil ((2 / 3 : ℝ) * (d : ℝ)) : ℝ) ≤
        (Nat.floor ((2 / 3 : ℝ) * (d : ℝ)) : ℝ) + 1 := by exact_mod_cast hnat
    have hfloor : (Nat.floor ((2 / 3 : ℝ) * (d : ℝ)) : ℝ) ≤
        (2 / 3 : ℝ) * (d : ℝ) := Nat.floor_le (by positivity)
    exact hnatR.trans (by nlinarith [hfloor])
  have htHorizon : (t : ℝ) ≤ 3 * (d : ℝ) / 4 := by
    nlinarith [htup, hdR]
  have hrowsReal : (Fintype.card R : ℝ) ≤ (t : ℝ) := by
    nlinarith [hrowsR, htlo]
  have hrows : Fintype.card R ≤ t := by exact_mod_cast hrowsReal
  have hmcast : (m : ℝ) = (t : ℝ) - (Fintype.card R : ℝ) := by
    rw [Nat.cast_sub hrows]
  have hmLower : (d : ℝ) / 6 ≤ (m : ℝ) := by
    rw [hmcast]
    nlinarith [htlo, hrowsR]
  have hmpos : (0 : ℝ) < (m : ℝ) := by
    have : (0 : ℝ) < (d : ℝ) / 6 := by positivity
    exact lt_of_lt_of_le this hmLower
  let load : Fin d → ℝ := fun y => ∑ i : R, q i y
  let qbar : (R ⊕ Fin m) → Fin d → ℝ := fun j y =>
    match j with
    | Sum.inl i => q i y
    | Sum.inr _ => ((t : ℝ) / d - load y) / (m : ℝ)
  have htdivLo : (2 / 3 : ℝ) ≤ (t : ℝ) / d :=
    (le_div_iff₀ hdpos).2 htlo
  have htdivHi : (t : ℝ) / d ≤ 1 := by
    apply (div_le_iff₀ hdpos).2
    nlinarith [htup, hdR]
  have hloadNonneg (y : Fin d) : 0 ≤ load y := by
    dsimp [load]
    exact Finset.sum_nonneg fun i hi => hq0 i y
  have hnumLo (y : Fin d) : 1 / 6 ≤ (t : ℝ) / d - load y := by
    linarith [htdivLo, hqload y]
  have hnumHi (y : Fin d) : (t : ℝ) / d - load y ≤ 1 := by
    linarith [htdivHi, hloadNonneg y]
  have hnumNonneg (y : Fin d) : 0 ≤ (t : ℝ) / d - load y := by
    linarith [hnumLo y]
  have hloadConst : ∑ y : Fin d, (t : ℝ) / d = (t : ℝ) := by
    calc
      ∑ y : Fin d, (t : ℝ) / d = (d : ℝ) * ((t : ℝ) / d) := by simp
      _ = (t : ℝ) := by field_simp [ne_of_gt hdpos]
  have hdummyRow (j : Fin m) : ∑ y : Fin d, qbar (Sum.inr j) y = 1 := by
    calc
      ∑ y : Fin d, qbar (Sum.inr j) y =
          ((∑ y : Fin d, (t : ℝ) / d) - ∑ y : Fin d, load y) / (m : ℝ) := by
            simp only [qbar]
            rw [← Finset.sum_div, Finset.sum_sub_distrib]
      _ = ((t : ℝ) - (Fintype.card R : ℝ)) / (m : ℝ) := by
            rw [hloadConst, hloadTotal]
      _ = 1 := by rw [← hmcast]; exact div_self (ne_of_gt hmpos)
  have hqbarNonneg : ∀ j y, 0 ≤ qbar j y := by
    intro j y
    cases j with
    | inl i => exact hq0 i y
    | inr j =>
        dsimp [qbar]
        exact div_nonneg (hnumNonneg y) (le_of_lt hmpos)
  have hqbarRow : ∀ j, ∑ y : Fin d, qbar j y = 1 := by
    intro j
    cases j with
    | inl i => simpa [qbar] using hqsum i
    | inr j => exact hdummyRow j
  have hrealCol (y : Fin d) : ∑ i : R, qbar (Sum.inl i) y = load y := by
    simp [qbar, load]
  have hdummyCol (y : Fin d) :
      ∑ j : Fin m, qbar (Sum.inr j) y =
        (m : ℝ) * (((t : ℝ) / d - load y) / (m : ℝ)) := by
    simp [qbar, Finset.sum_const, Finset.card_fin]
  have hqbarCol (y : Fin d) : ∑ j : R ⊕ Fin m, qbar j y = (t : ℝ) / d := by
    rw [Fintype.sum_sum_type, hrealCol y, hdummyCol y]
    have hmne : (m : ℝ) ≠ 0 := ne_of_gt hmpos
    field_simp [hmne]
    ring
  have hden : (1 : ℝ) ≤ (10 / d) * (m : ℝ) := by
    have hm10 := mul_le_mul_of_nonneg_left hmLower (by positivity : 0 ≤ (10 : ℝ) / d)
    have heq : (10 : ℝ) / d * ((d : ℝ) / 6) = 5 / 3 := by
      field_simp [ne_of_gt hdpos]
      ring
    linarith
  have hdummyCap : ∀ j : Fin m, ∀ y : Fin d, qbar (Sum.inr j) y ≤ 10 / d := by
    intro j y
    apply (div_le_iff₀ hmpos).2
    exact (hnumHi y).trans hden
  have hpow : (d : ℝ) ^ (-1 : ℝ) ≤ (d : ℝ) ^ (-(0.95 : ℝ)) :=
    Real.rpow_le_rpow_of_exponent_le hbase (by norm_num)
  have hInvPow : (1 : ℝ) / d ≤ (d : ℝ) ^ (-(0.95 : ℝ)) := by
    simpa [Real.rpow_neg_eq_inv_rpow, Real.rpow_one] using hpow
  have hqbarAtom : ∀ j y, qbar j y ≤ 10 * (d : ℝ) ^ (-(0.95 : ℝ)) := by
    intro j y
    cases j with
    | inl i =>
        have hp := Real.rpow_nonneg (by positivity : (0 : ℝ) ≤ (d : ℝ)) (-(0.95 : ℝ))
        dsimp [qbar]
        nlinarith [hqcap i y]
    | inr j =>
        calc
          qbar (Sum.inr j) y ≤ 10 / d := hdummyCap j y
          _ ≤ 10 * (d : ℝ) ^ (-(0.95 : ℝ)) := by
            simpa [div_eq_mul_inv] using
              mul_le_mul_of_nonneg_left hInvPow (by norm_num : (0 : ℝ) ≤ 10)
  have hcardEq : Fintype.card (R ⊕ Fin m) = t := by
    simp [m, Nat.add_sub_of_le hrows]
  have hcardEq' : Fintype.card (R ⊕ Fin m) = Fintype.card (Fin t) := by
    simpa using hcardEq
  let e : Fin t ≃ (R ⊕ Fin m) := (Fintype.equivOfCardEq hcardEq').symm
  have htposR : (0 : ℝ) < (t : ℝ) := by nlinarith [htlo, hdR]
  have htpos : 0 < t := by exact_mod_cast htposR
  have hweakPow : (d : ℝ) ^ (-(0.95 : ℝ)) ≤ (d : ℝ) ^ (-(9 / 10 : ℝ)) :=
    Real.rpow_le_rpow_of_exponent_le hbase (by norm_num)
  have hqbarWeak : ∀ j y, qbar j y ≤ 10 * (d : ℝ) ^ (-(9 / 10 : ℝ)) := by
    intro j y
    calc
      qbar j y ≤ 10 * (d : ℝ) ^ (-(0.95 : ℝ)) := hqbarAtom j y
      _ ≤ 10 * (d : ℝ) ^ (-(9 / 10 : ℝ)) :=
        mul_le_mul_of_nonneg_left hweakPow (by norm_num)
  have horderCol (y : Fin d) :
      (∑ k : Fin t, qbar (e k) y) = (t : ℝ) / d := by
    calc
      (∑ k : Fin t, qbar (e k) y) = ∑ j : R ⊕ Fin m, qbar j y :=
        Equiv.sum_comp e (fun j : R ⊕ Fin m => qbar j y)
      _ = (t : ℝ) / d := hqbarCol y
  obtain ⟨σ, hprefix⟩ := Lane_q_inj_nodes.prefix_order_exists hd htHorizon htpos
    (fun k y => qbar (e k) y)
    (by intro k y; exact hqbarNonneg (e k) y)
    (by intro k y; exact hqbarWeak (e k) y)
    horderCol hsmall
  let e' : Fin t ≃ (R ⊕ Fin m) := σ.trans e
  have hordered : Injection.OrderedInput d t (fun k y => qbar (e' k) y) := by
    refine ⟨hd, htHorizon, ?_, ?_, ?_, ?_⟩
    · intro k y
      exact hqbarNonneg (e' k) y
    · intro k
      exact hqbarRow (e' k)
    · intro k y
      exact hqbarAtom (e' k) y
    · intro b y
      simpa [e'] using hprefix b y
  refine ⟨t, rfl, hrows, qbar, e', ?_, ?_, hdummyCap, hqbarCol, hordered⟩
  · intro i y
    rfl
  · intro j y
    rfl

/-- Step 2 now refers to the concrete process and tracking event, not to an
arbitrary law with additive singleton error. This is an assembly node. -/
theorem tracking_label_sampler :
    ∀ᶠ d : ℕ in Filter.atTop, ∀ t (q : Fin t → Fin d → ℝ)
      (h : Injection.OrderedInput d t q),
      1 - Injection.failureBound d ≤
        (Injection.sequentialLaw q h.nonneg h.row_sum).pr (Injection.Good q) := by
  obtain ⟨K, hK, hrec⟩ := Injection.tracking_drift_recurrence
  filter_upwards [Injection.sequential_martingale_concentration,
    Injection.tracking_bootstrap K hK] with d hc hb
  intro t q h
  exact Injection.tracking_probability_transfer q h (hc t q h)
    (hb t q h (hrec d t q h))

/-- Steps 2–3 assembled: the law is specifically the sequential law conditioned
on its successful tracking event. -/
theorem ordered_conditioned_sampler_estimates :
    ∀ᶠ d : ℕ in Filter.atTop, ∀ t (q : Fin t → Fin d → ℝ)
      (h : Injection.OrderedInput d t q),
      ∃ hG : 0 < (Injection.sequentialLaw q h.nonneg h.row_sum).pr (Injection.Good q),
        LabelInjectionSupported (Injection.conditionedLaw q h hG) ∧
        (∀ (S : Finset (Fin t)) (y : Fin t → Fin d), (S.card : ℝ) ≤ (d : ℝ) ^ (0.025 : ℝ) →
          (Injection.conditionedLaw q h hG).pr (fun x => ∀ i ∈ S, x i = y i) ≤
            Real.exp (Injection.relativeError d * S.card) * ∏ i ∈ S, q i (y i)) ∧
        (∀ i y, |(Injection.conditionedLaw q h hG).pr (fun x => x i = y) - q i y| ≤
          Injection.relativeError d * q i y) := by
  obtain ⟨K, hK, hrec⟩ := Injection.tracking_drift_recurrence
  obtain ⟨K₁, hK₁, hlin⟩ := Injection.linear_likelihood_cancellation
  obtain ⟨K₂, hK₂, hquad⟩ := Injection.quadratic_likelihood_remainder
  filter_upwards [tracking_label_sampler, Injection.forcing_likelihood_identity,
    hquad, Injection.likelihood_log_transfer K₁ K₂ hK₁ hK₂,
    Injection.singleton_forcing_drift_stability, Injection.forced_martingale_concentration,
    Injection.singleton_forcing_tracking_transfer K hK,
    Injection.conditioned_comparison_transfer] with d ht hi hq hl hs hm hf hc
  intro t q h
  apply hc t q h (ht t q h) (hi t q h)
  · intro S y hpos hsize x hgood htarget
    have hquadratic := hq t q h S y hpos hsize x hgood htarget
    exact hl t q h S y hpos hsize x hgood htarget
      (hlin d t q h S y hpos x hgood htarget) hquadratic.1 hquadratic.2
  · intro i y hpos
    exact hf t q h (hrec d t q h) i y hpos
      (hs t q h i y hpos) (hm t q h i y hpos)

/-- Restrict the ordered completed law back to the real rows. Empty real row
sets are allowed; no singleton estimate is converted into an absolute error. -/
theorem restrict_ordered_sampler {R : Type} [Fintype R] [DecidableEq R]
    {d t : ℕ} (q : R → Fin d → ℝ) (p : Fin t → Fin d → ℝ)
    (e : R ↪ Fin t) (he : ∀ i y, p (e i) y = q i y)
    (Q : FinProb (Fin t → Fin d)) (hinj : LabelInjectionSupported Q)
    (hjoint : ∀ (S : Finset (Fin t)) (y : Fin t → Fin d), (S.card : ℝ) ≤ (d : ℝ) ^ (0.025 : ℝ) →
      Q.pr (fun x => ∀ i ∈ S, x i = y i) ≤
        Real.exp (Injection.relativeError d * S.card) * ∏ i ∈ S, p i (y i))
    (hmarg : ∀ i y, |Q.pr (fun x => x i = y) - p i y| ≤ Injection.relativeError d * p i y) :
    ∃ P : FinProb (R → Fin d), LabelInjectionSupported P ∧
      (∀ (S : Finset R) (y : R → Fin d), (S.card : ℝ) ≤ (d : ℝ) ^ (0.025 : ℝ) →
        P.pr (fun x => ∀ i ∈ S, x i = y i) ≤
          Real.exp (Injection.relativeError d * S.card) * ∏ i ∈ S, q i (y i)) ∧
      (∀ i y, |P.pr (fun x => x i = y) - q i y| ≤ Injection.relativeError d * q i y) := by
  classical
  let f : (Fin t → Fin d) → (R → Fin d) := fun x i => x (e i)
  let P : FinProb (R → Fin d) := FinProb.map Q f
  have hmapPr (A : (R → Fin d) → Prop) :
      P.pr A = Q.pr (fun x => A (f x)) := by
    classical
    have hprIndicator (P₀ : FinProb (R → Fin d)) (A₀ : (R → Fin d) → Prop) :
        P₀.pr A₀ = P₀.expect (fun z => if A₀ z then 1 else 0) := by
      unfold FinProb.pr FinProb.expect
      apply Finset.sum_congr rfl
      intro z hz
      by_cases hA : A₀ z <;> simp [hA]
    have hmapExpect (g : (R → Fin d) → ℝ) : P.expect g = Q.expect (fun x => g (f x)) := by
      classical
      unfold P FinProb.expect FinProb.map
      calc
        _ = ∑ z, ∑ x, (if f x = z then Q.w x else 0) * g z := by
          apply Finset.sum_congr rfl
          intro z hz
          rw [Finset.sum_mul]
        _ = ∑ x, ∑ z, (if f x = z then Q.w x else 0) * g z := Finset.sum_comm
        _ = ∑ x, Q.w x * g (f x) := by
          apply Finset.sum_congr rfl
          intro x hx
          rw [Finset.sum_eq_single (f x)]
          · simp
          · intro z hz hzf
            simp [Ne.symm hzf]
          · simp
    calc
      P.pr A = P.expect (fun z => if A z then 1 else 0) := hprIndicator P A
      _ = Q.expect (fun x => if A (f x) then 1 else 0) := hmapExpect _
      _ = Q.pr (fun x => A (f x)) := (by
        unfold FinProb.pr FinProb.expect
        apply Finset.sum_congr rfl
        intro x hx
        by_cases hA : A (f x) <;> simp [hA])
  have hsource : ∀ z, P.w z ≠ 0 → ∃ x, f x = z ∧ Q.w x ≠ 0 := by
    intro z hz
    by_contra hn
    push_neg at hn
    apply hz
    change (∑ x, if f x = z then Q.w x else 0) = 0
    apply Finset.sum_eq_zero
    intro x hx
    by_cases hfx : f x = z
    · simp [hfx, hn x hfx]
    · simp [hfx]
  refine ⟨P, ?_, ?_, ?_⟩
  · intro z hz
    obtain ⟨x, hxeq, hxw⟩ := hsource z hz
    have hxinj := hinj x hxw
    intro i j hij
    have hxeq' : ∀ k, x (e k) = z k := by
      intro k
      exact congrFun (by simpa [f] using hxeq) k
    apply e.injective
    exact hxinj (hxeq' i |>.trans (hij.trans (hxeq' j).symm))
  · intro S y hsize
    let T : Finset (Fin t) := S.image e
    by_cases hS : S.Nonempty
    · letI : Inhabited (Fin d) := ⟨y hS.choose⟩
      let witness (k : Fin t) (hk : k ∈ T) : R := Classical.choose (Finset.mem_image.mp hk)
      have witness_mem (k : Fin t) (hk : k ∈ T) : witness k hk ∈ S :=
        (Classical.choose_spec (Finset.mem_image.mp hk)).1
      have witness_eq (k : Fin t) (hk : k ∈ T) : e (witness k hk) = k :=
        (Classical.choose_spec (Finset.mem_image.mp hk)).2
      let y' : Fin t → Fin d := fun k => if hk : k ∈ T then y (witness k hk) else default
      have hpre (x : Fin t → Fin d) :
          (∀ i ∈ S, x (e i) = y i) ↔ ∀ k ∈ T, x k = y' k := by
        constructor
        · intro hx k hk
          have h := hx (witness k hk) (witness_mem k hk)
          simpa [y', hk, witness_eq k hk] using h
        · intro hx i hi
          have hk : e i ∈ T := Finset.mem_image.mpr ⟨i, hi, rfl⟩
          have h := hx (e i) hk
          have heq : witness (e i) hk = i := e.injective (by simpa [witness_eq (e i) hk])
          simpa [y', hk, heq] using h
      have hcard : T.card = S.card := by
        dsimp [T]
        apply Finset.card_image_iff.mpr
        intro i hi j hj hij
        exact e.injective hij
      have hprod : (∏ k ∈ T, p k (y' k)) = ∏ i ∈ S, q i (y i) := by
        rw [show T = S.image e by rfl, Finset.prod_image]
        · apply Finset.prod_congr rfl
          intro i hi
          have hk : e i ∈ T := Finset.mem_image.mpr ⟨i, hi, rfl⟩
          have hwi : witness (e i) hk = i := e.injective (witness_eq (e i) hk)
          have hyval : y' (e i) = y i := by simp [y', hk, hwi]
          rw [hyval, he i (y i)]
        · intro i hi j hj hij
          exact e.injective hij
      have hprob : Q.pr (fun x => ∀ i ∈ S, x (e i) = y i) =
          Q.pr (fun x => ∀ k ∈ T, x k = y' k) := by
        have hpred : (fun x : Fin t → Fin d => ∀ i ∈ S, x (e i) = y i) =
            (fun x => ∀ k ∈ T, x k = y' k) := by
          funext x
          exact propext (hpre x)
        rw [hpred]
      calc
        P.pr (fun x => ∀ i ∈ S, x i = y i) =
            Q.pr (fun x => ∀ i ∈ S, (f x) i = y i) := hmapPr _
        _ = Q.pr (fun x => ∀ i ∈ S, x (e i) = y i) := by rfl
        _ = Q.pr (fun x => ∀ k ∈ T, x k = y' k) := hprob
        _ ≤ Real.exp (Injection.relativeError d * T.card) * ∏ k ∈ T, p k (y' k) :=
          hjoint T y' (by rw [hcard]; exact hsize)
        _ = Real.exp (Injection.relativeError d * S.card) * ∏ i ∈ S, q i (y i) := by
          rw [hcard, hprod]
    · have hempty : S = ∅ := Finset.not_nonempty_iff_eq_empty.mp hS
      have hfull : P.pr (fun _ => True) = 1 := by
        unfold FinProb.pr
        simpa using P.sum_eq_one
      simpa [hempty] using hfull.le
  · intro i y
    have h := hmarg (e i) y
    have hprob : P.pr (fun x => x i = y) = Q.pr (fun x => x (e i) = y) := by
      rw [hmapPr]
    rw [hprob, ← he i y]
    exact h

/-- Centered prices and the paper's explicit normalized sign perturbation (03:739–741). -/
noncomputable def injectionPriceMean {R : Type*} [Fintype R] {d : ℕ}
    (q c : R → Fin d → ℝ) (i : R) : ℝ := ∑ y, q i y * c i y

noncomputable def injectionPriceDelta (d : ℕ) : ℝ := (d : ℝ) ^ (-(0.05 : ℝ))

noncomputable def injectionPriceSign (z : ℝ) : ℝ := if 0 < z then 1 else if z < 0 then -1 else 0

noncomputable def injectionPriceTilt {R : Type*} [Fintype R] {d : ℕ}
    (q c : R → Fin d → ℝ) (i : R) (y : Fin d) : ℝ :=
  q i y * (1 + injectionPriceDelta d * injectionPriceSign (c i y - injectionPriceMean q c i))

noncomputable def injectionPricePerturbation {R : Type*} [Fintype R] {d : ℕ}
    (q c : R → Fin d → ℝ) (i : R) (y : Fin d) : ℝ :=
  injectionPriceTilt q c i y / ∑ z, injectionPriceTilt q c i z

/-- TeX 03:742–752: normalization, relaxed hypotheses, support and centered gain.
Pointwise control against the original q will pay for the final joint bound. -/
theorem price_perturbation_estimates :
    ∀ᶠ d : ℕ in Filter.atTop, ∀ {R : Type} [Fintype R] [DecidableEq R]
      (q : R → Fin d → ℝ),
      (∀ i y, 0 ≤ q i y) → (∀ i, ∑ y, q i y = 1) →
      (∀ i y, q i y ≤ (d : ℝ) ^ (-(0.95 : ℝ))) →
      (∀ y, ∑ i, q i y ≤ 0.4) → ∀ c : R → Fin d → ℝ,
      (∀ i y, 0 ≤ injectionPricePerturbation q c i y) ∧
      (∀ i, ∑ y, injectionPricePerturbation q c i y = 1) ∧
      (∀ i y, injectionPricePerturbation q c i y ≤ 2 * (d : ℝ) ^ (-(0.95 : ℝ))) ∧
      (∀ y, ∑ i, injectionPricePerturbation q c i y ≤ 1 / 2) ∧
      (∀ i y, injectionPricePerturbation q c i y ≤ Real.exp (3 * injectionPriceDelta d) * q i y) ∧
      (∀ i, injectionPriceDelta d / 2 * (∑ y, q i y * |c i y - injectionPriceMean q c i|) ≤
        ∑ y, injectionPricePerturbation q c i y * (c i y - injectionPriceMean q c i)) := by
  classical
  have hdeltaT : Tendsto (fun n : ℕ => injectionPriceDelta n) atTop (nhds 0) := by
    change Tendsto ((fun x : ℝ => x ^ (-(0.05 : ℝ))) ∘ Nat.cast) atTop (nhds 0)
    exact (tendsto_rpow_neg_atTop (by norm_num : 0 < (0.05 : ℝ))).comp
      tendsto_natCast_atTop_atTop
  have hdeltaSmall : ∀ᶠ n : ℕ in atTop, injectionPriceDelta n < 1 / 6 :=
    hdeltaT.eventually (Iio_mem_nhds (by norm_num))
  have hexpT : Tendsto (fun n : ℕ => Real.exp (3 * injectionPriceDelta n)) atTop (nhds 1) := by
    have hmul : Tendsto (fun n : ℕ => 3 * injectionPriceDelta n) atTop (nhds 0) := by
      simpa using hdeltaT.const_mul 3
    exact Real.tendsto_exp_nhds_zero_nhds_one.comp hmul
  have hexpSmall : ∀ᶠ n : ℕ in atTop,
      Real.exp (3 * injectionPriceDelta n) < 5 / 4 :=
    hexpT.eventually (Iio_mem_nhds (by norm_num))
  filter_upwards [hdeltaSmall, hexpSmall] with d hδ hE
  intro R instR instDecR q hnq hsq hcap hload c
  let δ : ℝ := injectionPriceDelta d
  let Z : R → ℝ := fun i => ∑ y, injectionPriceTilt q c i y
  have hδnonneg : 0 ≤ δ := by
    dsimp [δ, injectionPriceDelta]
    exact Real.rpow_nonneg (by positivity) _
  have hsignLo (a : ℝ) : -1 ≤ injectionPriceSign a := by
    unfold injectionPriceSign
    split_ifs <;> norm_num
  have hsignHi (a : ℝ) : injectionPriceSign a ≤ 1 := by
    unfold injectionPriceSign
    split_ifs <;> norm_num
  have hmultLo (a : ℝ) : 1 - δ ≤ 1 + δ * injectionPriceSign a := by
    have := mul_le_mul_of_nonneg_left (hsignLo a) hδnonneg
    linarith
  have hmultHi (a : ℝ) : 1 + δ * injectionPriceSign a ≤ 1 + δ := by
    have := mul_le_mul_of_nonneg_left (hsignHi a) hδnonneg
    linarith
  have hZbounds (i : R) : 1 - δ ≤ Z i ∧ Z i ≤ 1 + δ := by
    constructor
    · dsimp [Z, injectionPriceTilt]
      calc
        (∑ y, q i y * (1 + δ * injectionPriceSign
            (c i y - injectionPriceMean q c i))) ≥
          ∑ y, q i y * (1 - δ) := by
            apply Finset.sum_le_sum
            intro y hy
            exact mul_le_mul_of_nonneg_left (hmultLo _) (hnq i y)
        _ = (∑ y, q i y) * (1 - δ) := by rw [Finset.sum_mul]
        _ = 1 - δ := by rw [hsq i]; ring
    · dsimp [Z, injectionPriceTilt]
      calc
        (∑ y, q i y * (1 + δ * injectionPriceSign
            (c i y - injectionPriceMean q c i))) ≤
          ∑ y, q i y * (1 + δ) := by
            apply Finset.sum_le_sum
            intro y hy
            exact mul_le_mul_of_nonneg_left (hmultHi _) (hnq i y)
        _ = (∑ y, q i y) * (1 + δ) := by rw [Finset.sum_mul]
        _ = 1 + δ := by rw [hsq i]; ring
  have hZpos (i : R) : 0 < Z i := by
    have : 0 < 1 - δ := by dsimp [δ]; linarith
    exact lt_of_lt_of_le this (hZbounds i).1
  have hratio : (1 + δ) / (1 - δ) ≤ Real.exp (3 * δ) := by
    have hlin : (1 + δ) / (1 - δ) ≤ 1 + 3 * δ := by
      apply (div_le_iff₀ (by dsimp [δ]; linarith)).2
      have hδsq : δ * δ ≤ δ / 6 := by
        calc
          δ * δ ≤ δ * (1 / 6 : ℝ) := mul_le_mul_of_nonneg_left hδ.le hδnonneg
          _ = δ / 6 := by ring
      nlinarith [hδsq, hδnonneg]
    have hexp : 1 + 3 * δ ≤ Real.exp (3 * δ) := by
      have h := Real.add_one_le_exp (3 * δ)
      linarith
    exact hlin.trans hexp
  have hratio' : 1 + δ ≤ Real.exp (3 * δ) * (1 - δ) :=
    (div_le_iff₀ (by dsimp [δ]; linarith)).mp hratio
  have hpdom (i : R) (y : Fin d) :
      injectionPricePerturbation q c i y ≤ Real.exp (3 * δ) * q i y := by
    have hnum : injectionPriceTilt q c i y ≤
        Real.exp (3 * δ) * (q i y * Z i) := by
      dsimp [injectionPriceTilt]
      calc
        q i y * (1 + δ * injectionPriceSign
            (c i y - injectionPriceMean q c i)) ≤ q i y * (1 + δ) :=
          mul_le_mul_of_nonneg_left (hmultHi _) (hnq i y)
        _ ≤ q i y * (Real.exp (3 * δ) * (1 - δ)) :=
          mul_le_mul_of_nonneg_left hratio' (hnq i y)
        _ ≤ q i y * (Real.exp (3 * δ) * Z i) := by
          apply mul_le_mul_of_nonneg_left
          · exact mul_le_mul_of_nonneg_left (hZbounds i).1 (Real.exp_nonneg _)
          · exact hnq i y
        _ = Real.exp (3 * δ) * (q i y * Z i) := by ring
    apply (div_le_iff₀ (hZpos i)).2
    simpa [δ, Z, injectionPricePerturbation, mul_assoc] using hnum
  have hpertNonneg (i : R) (y : Fin d) : 0 ≤ injectionPricePerturbation q c i y := by
    have hnum : 0 ≤ injectionPriceTilt q c i y := by
      dsimp [injectionPriceTilt]
      exact mul_nonneg (hnq i y) (by linarith [hmultLo (c i y - injectionPriceMean q c i)])
    exact div_nonneg hnum (le_of_lt (hZpos i))
  have hrowSum (i : R) : ∑ y, injectionPricePerturbation q c i y = 1 := by
    unfold injectionPricePerturbation
    rw [← Finset.sum_div]
    have hz : 0 < ∑ z, injectionPriceTilt q c i z := by simpa [Z] using hZpos i
    exact div_self (ne_of_gt hz)
  have hatom (i : R) (y : Fin d) :
      injectionPricePerturbation q c i y ≤ 2 * (d : ℝ) ^ (-(0.95 : ℝ)) := by
    calc
      injectionPricePerturbation q c i y ≤ Real.exp (3 * δ) * q i y := hpdom i y
      _ ≤ 2 * q i y := by
        have hE2 : Real.exp (3 * δ) ≤ 2 := by dsimp [δ]; linarith
        exact mul_le_mul_of_nonneg_right hE2 (hnq i y)
      _ ≤ 2 * (d : ℝ) ^ (-(0.95 : ℝ)) := by
        exact mul_le_mul_of_nonneg_left (hcap i y) (by norm_num)
  have hcol (y : Fin d) : ∑ i, injectionPricePerturbation q c i y ≤ 1 / 2 := by
    calc
      (∑ i, injectionPricePerturbation q c i y) ≤ ∑ i, Real.exp (3 * δ) * q i y :=
        Finset.sum_le_sum fun i hi => hpdom i y
      _ = Real.exp (3 * δ) * ∑ i, q i y := by rw [Finset.mul_sum]
      _ ≤ Real.exp (3 * δ) * (0.4 : ℝ) :=
        mul_le_mul_of_nonneg_left (hload y) (Real.exp_nonneg _)
      _ ≤ 1 / 2 := by
        have hE' : Real.exp (3 * δ) ≤ 5 / 4 := by simpa [δ] using hE.le
        calc
          Real.exp (3 * δ) * (0.4 : ℝ) ≤ (5 / 4) * (0.4 : ℝ) :=
            mul_le_mul_of_nonneg_right hE' (by norm_num)
          _ = 1 / 2 := by norm_num
  have hmean0 (i : R) :
      ∑ y, q i y * (c i y - injectionPriceMean q c i) = 0 := by
    calc
      ∑ y, q i y * (c i y - injectionPriceMean q c i) =
          ∑ y, (q i y * c i y - injectionPriceMean q c i * q i y) := by
            apply Finset.sum_congr rfl
            intro y hy
            ring
      _ = (∑ y, q i y * c i y) - injectionPriceMean q c i * ∑ y, q i y := by
            rw [Finset.sum_sub_distrib, ← Finset.mul_sum]
      _ = 0 := by simp [injectionPriceMean, hsq i]
  have hsignMul (a : ℝ) : injectionPriceSign a * a = |a| := by
    by_cases ha : 0 < a
    · simp [injectionPriceSign, ha, abs_of_pos ha]
    · by_cases ha' : a < 0
      · simp [injectionPriceSign, ha, ha', abs_of_neg ha']
      · have hz : a = 0 := le_antisymm
            (show a ≤ 0 from le_of_not_gt ha)
            (show 0 ≤ a from le_of_not_gt ha')
        simp [injectionPriceSign, ha, ha', hz]
  have hgainEq (i : R) :
      ∑ y, injectionPricePerturbation q c i y *
          (c i y - injectionPriceMean q c i) =
        injectionPriceDelta d / Z i *
          (∑ y, q i y * |c i y - injectionPriceMean q c i|) := by
    have hnum :
        ∑ y, injectionPriceTilt q c i y *
            (c i y - injectionPriceMean q c i) =
          injectionPriceDelta d *
            (∑ y, q i y * |c i y - injectionPriceMean q c i|) := by
      calc
        _ = ∑ y, (q i y * (c i y - injectionPriceMean q c i) +
              injectionPriceDelta d * (q i y * |c i y - injectionPriceMean q c i|)) := by
          apply Finset.sum_congr rfl
          intro y hy
          dsimp [injectionPriceTilt]
          calc
            q i y * (1 + injectionPriceDelta d *
                injectionPriceSign (c i y - injectionPriceMean q c i)) *
                (c i y - injectionPriceMean q c i) =
              q i y * (c i y - injectionPriceMean q c i) +
                injectionPriceDelta d * (q i y *
                  (injectionPriceSign (c i y - injectionPriceMean q c i) *
                    (c i y - injectionPriceMean q c i))) := by ring
            _ = q i y * (c i y - injectionPriceMean q c i) +
                injectionPriceDelta d * (q i y *
                  |c i y - injectionPriceMean q c i|) := by
                    rw [hsignMul]
        _ = (∑ y, q i y * (c i y - injectionPriceMean q c i)) +
              injectionPriceDelta d * (∑ y, q i y *
                |c i y - injectionPriceMean q c i|) := by
          rw [Finset.sum_add_distrib, ← Finset.mul_sum]
        _ = injectionPriceDelta d *
              (∑ y, q i y * |c i y - injectionPriceMean q c i|) := by
          rw [hmean0 i]
          ring
    calc
      ∑ y, injectionPricePerturbation q c i y *
          (c i y - injectionPriceMean q c i) =
          (∑ y, injectionPriceTilt q c i y *
            (c i y - injectionPriceMean q c i)) / Z i := by
              unfold injectionPricePerturbation
              calc
                _ = ∑ y, (injectionPriceTilt q c i y *
                    (c i y - injectionPriceMean q c i)) /
                    (∑ z, injectionPriceTilt q c i z) := by
                      apply Finset.sum_congr rfl
                      intro y hy
                      field_simp [ne_of_gt (by simpa [Z] using hZpos i)]
                _ = (∑ y, injectionPriceTilt q c i y *
                    (c i y - injectionPriceMean q c i)) / Z i := by
                      rw [Finset.sum_div]
      _ = injectionPriceDelta d / Z i *
          (∑ y, q i y * |c i y - injectionPriceMean q c i|) := by rw [hnum]; ring
  have hgain (i : R) :
      injectionPriceDelta d / 2 * (∑ y, q i y * |c i y - injectionPriceMean q c i|) ≤
        ∑ y, injectionPricePerturbation q c i y *
          (c i y - injectionPriceMean q c i) := by
    let L := ∑ y, q i y * |c i y - injectionPriceMean q c i|
    have hL : 0 ≤ L := by
      dsimp [L]
      exact Finset.sum_nonneg fun y hy => mul_nonneg (hnq i y) (abs_nonneg _)
    have hdelta0 : 0 ≤ injectionPriceDelta d := by
      unfold injectionPriceDelta
      exact Real.rpow_nonneg (by positivity) _
    have hcoeff : 0 ≤ injectionPriceDelta d / 2 * L :=
      mul_nonneg (div_nonneg hdelta0 (by norm_num)) hL
    have hZ2 : Z i ≤ 2 := by
      have : δ ≤ 1 := by dsimp [δ]; linarith
      linarith [(hZbounds i).2]
    rw [hgainEq i]
    change injectionPriceDelta d / 2 * L ≤ injectionPriceDelta d / Z i * L
    have hdivmul : injectionPriceDelta d / Z i * L =
        (injectionPriceDelta d * L) / Z i := by rw [div_mul_eq_mul_div]
    rw [hdivmul]
    apply (le_div_iff₀ (hZpos i)).2
    calc
      (injectionPriceDelta d / 2 * L) * Z i ≤
          (injectionPriceDelta d / 2 * L) * 2 :=
        mul_le_mul_of_nonneg_left hZ2 hcoeff
      _ = injectionPriceDelta d * L := by ring
  exact ⟨hpertNonneg, hrowSum, hatom, hcol, hpdom, hgain⟩

/-- TeX 03:753–755: relative singleton error, measured against the perturbed
row, is dominated by its gain. Constant prices have zero centered error. -/
theorem price_gain_dominates_relative_error :
    ∀ᶠ d : ℕ in Filter.atTop, ∀ {R : Type} [Fintype R] [DecidableEq R]
      (q c : R → Fin d → ℝ), (∀ i y, 0 ≤ q i y) → (∀ i, ∑ y, q i y = 1) →
      (∀ i, ∑ y, injectionPricePerturbation q c i y = 1) →
      (∀ i y, injectionPricePerturbation q c i y ≤ Real.exp (3 * injectionPriceDelta d) * q i y) →
      (∀ i, injectionPriceDelta d / 2 * (∑ y, q i y * |c i y - injectionPriceMean q c i|) ≤
        ∑ y, injectionPricePerturbation q c i y * (c i y - injectionPriceMean q c i)) →
      ∀ Q : FinProb (R → Fin d),
        (∀ i y, |Q.pr (fun x => x i = y) - injectionPricePerturbation q c i y| ≤
          Injection.relativeError d * injectionPricePerturbation q c i y) →
        injectionTargetPrice q c ≤ injectionLabelPrice Q c := by
  classical
  have hpowerT : Tendsto (fun n : ℕ => (n : ℝ) ^ (-(0.04 : ℝ))) atTop (nhds 0) := by
    change Tendsto ((fun x : ℝ => x ^ (-(0.04 : ℝ))) ∘ Nat.cast) atTop (nhds 0)
    exact (tendsto_rpow_neg_atTop (by norm_num : 0 < (0.04 : ℝ))).comp
      tendsto_natCast_atTop_atTop
  have hpower : ∀ᶠ n : ℕ in atTop, (n : ℝ) ^ (-(0.04 : ℝ)) < 1 / 4 :=
    hpowerT.eventually (Iio_mem_nhds (by norm_num))
  have hdeltaT : Tendsto (fun n : ℕ => injectionPriceDelta n) atTop (nhds 0) := by
    change Tendsto ((fun x : ℝ => x ^ (-(0.05 : ℝ))) ∘ Nat.cast) atTop (nhds 0)
    exact (tendsto_rpow_neg_atTop (by norm_num : 0 < (0.05 : ℝ))).comp
      tendsto_natCast_atTop_atTop
  have hexpT : Tendsto (fun n : ℕ => Real.exp (3 * injectionPriceDelta n)) atTop (nhds 1) := by
    have hmul : Tendsto (fun n : ℕ => 3 * injectionPriceDelta n) atTop (nhds 0) := by
      simpa using hdeltaT.const_mul 3
    exact Real.tendsto_exp_nhds_zero_nhds_one.comp hmul
  have hexp : ∀ᶠ n : ℕ in atTop, Real.exp (3 * injectionPriceDelta n) < 2 :=
    hexpT.eventually (Iio_mem_nhds (by norm_num))
  have hcoef : ∀ᶠ n : ℕ in atTop,
      Injection.relativeError n * Real.exp (3 * injectionPriceDelta n) ≤
        injectionPriceDelta n / 2 := by
    filter_upwards [hpower, hexp, Filter.eventually_gt_atTop 0] with n hp he hn
    have hnR : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn
    have hsplit : (n : ℝ) ^ (-(0.09 : ℝ)) =
        injectionPriceDelta n * (n : ℝ) ^ (-(0.04 : ℝ)) := by
      rw [injectionPriceDelta, ← Real.rpow_add hnR]
      norm_num
    have hdelta : 0 ≤ injectionPriceDelta n := by
      rw [injectionPriceDelta]
      exact Real.rpow_nonneg (by positivity) _
    have hrel : Injection.relativeError n ≤ injectionPriceDelta n / 4 := by
      rw [Injection.relativeError, hsplit]
      nlinarith [mul_le_mul_of_nonneg_left hp.le hdelta]
    calc
      Injection.relativeError n * Real.exp (3 * injectionPriceDelta n) ≤
          (injectionPriceDelta n / 4) * Real.exp (3 * injectionPriceDelta n) :=
        mul_le_mul_of_nonneg_right hrel (Real.exp_nonneg _)
      _ ≤ (injectionPriceDelta n / 4) * 2 :=
        mul_le_mul_of_nonneg_left he.le (by positivity)
      _ = injectionPriceDelta n / 2 := by ring
  filter_upwards [hcoef] with d hcoef
  intro R instR instDecR q c hnq hsq hpsum hdom hgain Q hrelQ
  have hMargSum (i : R) : ∑ y, Q.pr (fun x => x i = y) = 1 := by
    calc
      (∑ y, Q.pr (fun x => x i = y)) = ∑ x, Q.w x := by
        simp only [FinProb.pr]
        rw [Finset.sum_comm]
        apply Finset.sum_congr rfl
        intro x hx
        rw [Finset.sum_eq_single (x i)]
        · simp
        · intro y hy hne
          simp [Ne.symm hne]
        · simp
      _ = 1 := Q.sum_eq_one
  let μ : R → ℝ := fun i => injectionPriceMean q c i
  let z : R → Fin d → ℝ := fun i y => c i y - μ i
  have hcenter (i : R) (m : Fin d → ℝ) (hm : ∑ y, m y = 1) :
      ∑ y, c i y * m y = (∑ y, z i y * m y) + μ i := by
    calc
      ∑ y, c i y * m y = ∑ y, (z i y * m y + μ i * m y) := by
        apply Finset.sum_congr rfl
        intro y hy
        simp [z]
        ring
      _ = (∑ y, z i y * m y) + μ i * ∑ y, m y := by
        rw [Finset.sum_add_distrib, ← Finset.mul_sum]
      _ = (∑ y, z i y * m y) + μ i := by rw [hm, mul_one]
  have hqcenter (i : R) : ∑ y, q i y * z i y = 0 := by
    calc
      ∑ y, q i y * z i y = ∑ y, (q i y * c i y - μ i * q i y) := by
        apply Finset.sum_congr rfl
        intro y hy
        simp [z]
        ring
      _ = (∑ y, q i y * c i y) - μ i * ∑ y, q i y := by
        rw [Finset.sum_sub_distrib, ← Finset.mul_sum]
      _ = 0 := by simp [μ, injectionPriceMean, hsq i]
  have hsignMul (a : ℝ) : injectionPriceSign a * a = |a| := by
    by_cases ha : 0 < a
    · simp [injectionPriceSign, ha, abs_of_pos ha]
    · by_cases ha' : a < 0
      · simp [injectionPriceSign, ha, ha', abs_of_neg ha']
      · have hz : a = 0 := le_antisymm
            (show a ≤ 0 from le_of_not_gt ha)
            (show 0 ≤ a from le_of_not_gt ha')
        simp [injectionPriceSign, ha, ha', hz]
  have hrow (i : R) :
      (∑ y, c i y * q i y) ≤ ∑ y, c i y * Q.pr (fun x => x i = y) := by
    let L : ℝ := ∑ y, q i y * |z i y|
    have hL : 0 ≤ L := by
      dsimp [L]
      exact Finset.sum_nonneg fun y hy => mul_nonneg (hnq i y) (abs_nonneg _)
    have herror : |(∑ y, c i y * Q.pr (fun x => x i = y)) -
          (∑ y, c i y * injectionPricePerturbation q c i y)| ≤
          Injection.relativeError d * Real.exp (3 * injectionPriceDelta d) * L := by
      have hcentered :
          (∑ y, c i y * Q.pr (fun x => x i = y)) -
            (∑ y, c i y * injectionPricePerturbation q c i y) =
          ∑ y, z i y * (Q.pr (fun x => x i = y) - injectionPricePerturbation q c i y) := by
        rw [hcenter i _ (hMargSum i), hcenter i _ (hpsum i)]
        calc
          (∑ y, z i y * Q.pr (fun x => x i = y) + μ i) -
              (∑ y, z i y * injectionPricePerturbation q c i y + μ i) =
            (∑ y, z i y * Q.pr (fun x => x i = y)) -
              (∑ y, z i y * injectionPricePerturbation q c i y) := by ring
          _ = ∑ y, z i y * (Q.pr (fun x => x i = y) - injectionPricePerturbation q c i y) := by
            rw [← Finset.sum_sub_distrib]
            apply Finset.sum_congr rfl
            intro y hy
            ring
      rw [hcentered]
      calc
        |∑ y, z i y * (Q.pr (fun x => x i = y) - injectionPricePerturbation q c i y)| ≤
            ∑ y, |z i y * (Q.pr (fun x => x i = y) - injectionPricePerturbation q c i y)| :=
          Finset.abs_sum_le_sum_abs _ _
        _ ≤ ∑ y, Injection.relativeError d * Real.exp (3 * injectionPriceDelta d) *
              (q i y * |z i y|) := by
          apply Finset.sum_le_sum
          intro y hy
          have hr := hrelQ i y
          have hd := hdom i y
          have hrelNonneg : 0 ≤ Injection.relativeError d := by
            unfold Injection.relativeError
            exact Real.rpow_nonneg (by positivity) _
          have hscaled : Injection.relativeError d * injectionPricePerturbation q c i y ≤
              Injection.relativeError d * (Real.exp (3 * injectionPriceDelta d) * q i y) :=
            mul_le_mul_of_nonneg_left hd hrelNonneg
          calc
            |z i y * (Q.pr (fun x => x i = y) - injectionPricePerturbation q c i y)| =
                |z i y| * |Q.pr (fun x => x i = y) - injectionPricePerturbation q c i y| := by
                  rw [abs_mul]
            _ ≤ |z i y| * (Injection.relativeError d * injectionPricePerturbation q c i y) :=
              mul_le_mul_of_nonneg_left hr (abs_nonneg _)
            _ ≤ |z i y| * (Injection.relativeError d *
                  (Real.exp (3 * injectionPriceDelta d) * q i y)) :=
              mul_le_mul_of_nonneg_left hscaled (abs_nonneg _)
            _ = Injection.relativeError d * Real.exp (3 * injectionPriceDelta d) *
                  (q i y * |z i y|) := by ring
        _ = Injection.relativeError d * Real.exp (3 * injectionPriceDelta d) * L := by
          dsimp [L]
          rw [← Finset.mul_sum]
    have herrorLo :
        -(injectionPriceDelta d / 2 * L) ≤
          (∑ y, c i y * Q.pr (fun x => x i = y)) -
            (∑ y, c i y * injectionPricePerturbation q c i y) := by
      have hleft := (abs_le.mp herror).1
      have hscale := mul_le_mul_of_nonneg_right hcoef hL
      linarith
    have hpertGain :
        (∑ y, c i y * injectionPricePerturbation q c i y) -
          (∑ y, c i y * q i y) ≥ injectionPriceDelta d / 2 * L := by
      have hcenterP := hcenter i (fun y => injectionPricePerturbation q c i y) (hpsum i)
      have hcenterQ := hcenter i (q i) (hsq i)
      have hqcz : ∑ y, z i y * q i y = 0 := by
        convert hqcenter i using 1 <;> apply Finset.sum_congr rfl <;> intro y hy <;> ring
      have hpriceDiff :
          (∑ y, c i y * injectionPricePerturbation q c i y) -
            (∑ y, c i y * q i y) =
          ∑ y, injectionPricePerturbation q c i y * z i y := by
        calc
          _ = ∑ y, z i y * injectionPricePerturbation q c i y := by
            rw [hcenterP, hcenterQ, hqcz]
            ring
          _ = ∑ y, injectionPricePerturbation q c i y * z i y := by
            apply Finset.sum_congr rfl
            intro y hy
            ring
      have hgc : injectionPriceDelta d / 2 * L ≤
          ∑ y, injectionPricePerturbation q c i y * z i y := by
        simpa [L, z, μ] using hgain i
      rw [hpriceDiff]
      exact hgc
    have hrowle :
        ∑ y, c i y * q i y ≤ ∑ y, c i y * Q.pr (fun x => x i = y) := by
      linarith [herrorLo, hpertGain]
    exact hrowle
  change (∑ i, ∑ y, c i y * q i y) ≤
    ∑ i, ∑ y, c i y * Q.pr (fun x => x i = y)
  apply Finset.sum_le_sum
  intro i hi
  exact hrow i

/-- TeX 03:756–758: absorb perturbation and comparison slack into d^(-.04).
The empty query has bound 1; zero atoms remain zero under pointwise domination. -/
theorem perturbed_joint_bound_transfer :
    ∀ᶠ d : ℕ in Filter.atTop, ∀ {R : Type} [Fintype R] [DecidableEq R]
      (q p : R → Fin d → ℝ), (∀ i y, 0 ≤ q i y) → (∀ i y, 0 ≤ p i y) →
      (∀ i y, p i y ≤ Real.exp (3 * injectionPriceDelta d) * q i y) →
      ∀ Q : FinProb (R → Fin d),
      (∀ (S : Finset R) (y : R → Fin d), (S.card : ℝ) ≤ (d : ℝ) ^ (0.025 : ℝ) →
        Q.pr (fun x => ∀ i ∈ S, x i = y i) ≤
          Real.exp (Injection.relativeError d * S.card) * ∏ i ∈ S, p i (y i)) →
      LabelNearProductBound d q Q := by
  classical
  have hpow01 : Tendsto (fun n : ℕ => (n : ℝ) ^ (-(0.01 : ℝ))) atTop (nhds 0) :=
    by
      change Tendsto ((fun x : ℝ => x ^ (-(0.01 : ℝ))) ∘ Nat.cast) atTop (nhds 0)
      exact (tendsto_rpow_neg_atTop (by norm_num : 0 < (0.01 : ℝ))).comp
        tendsto_natCast_atTop_atTop
  have hpow05 : Tendsto (fun n : ℕ => (n : ℝ) ^ (-(0.05 : ℝ))) atTop (nhds 0) :=
    by
      change Tendsto ((fun x : ℝ => x ^ (-(0.05 : ℝ))) ∘ Nat.cast) atTop (nhds 0)
      exact (tendsto_rpow_neg_atTop (by norm_num : 0 < (0.05 : ℝ))).comp
        tendsto_natCast_atTop_atTop
  have hsmall01 : ∀ᶠ n : ℕ in atTop, (n : ℝ) ^ (-(0.01 : ℝ)) < 1 / 12 :=
    hpow01.eventually (Iio_mem_nhds (by norm_num))
  have hsmall05 : ∀ᶠ n : ℕ in atTop, (n : ℝ) ^ (-(0.05 : ℝ)) < 1 / 2 :=
    hpow05.eventually (Iio_mem_nhds (by norm_num))
  have hcoef : ∀ᶠ n : ℕ in atTop,
      Injection.relativeError n + 3 * injectionPriceDelta n ≤ (n : ℝ) ^ (-(0.04 : ℝ)) := by
    filter_upwards [hsmall01, hsmall05, Filter.eventually_gt_atTop 0] with n h01 h05 hn
    have hnR : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn
    have hratio1 : injectionPriceDelta n = (n : ℝ) ^ (-(0.04 : ℝ)) *
        (n : ℝ) ^ (-(0.01 : ℝ)) := by
      rw [injectionPriceDelta, ← Real.rpow_add hnR]
      norm_num
    have hratio2 : Injection.relativeError n = (n : ℝ) ^ (-(0.04 : ℝ)) *
        (n : ℝ) ^ (-(0.05 : ℝ)) := by
      rw [Injection.relativeError, ← Real.rpow_add hnR]
      norm_num
    rw [hratio1, hratio2]
    have hr : 0 ≤ (n : ℝ) ^ (-(0.04 : ℝ)) := Real.rpow_nonneg (by positivity) _
    nlinarith [mul_le_mul_of_nonneg_left h01.le hr,
      mul_le_mul_of_nonneg_left h05.le hr]
  filter_upwards [hcoef] with d hcoef
  intro R instR instDecR q p hnq hnp hpdom Q hjoint S y hsize
  let ε := Injection.relativeError d
  let δ := injectionPriceDelta d
  let r := (d : ℝ) ^ (-(0.04 : ℝ))
  have hprod : (∏ i ∈ S, p i (y i)) ≤
      (∏ i ∈ S, Real.exp (3 * δ) * q i (y i)) := by
    apply Finset.prod_le_prod₀
    · intro i hi
      exact hnp i (y i)
    · intro i hi
      exact hpdom i (y i)
  have hprod' : (∏ i ∈ S, Real.exp (3 * δ) * q i (y i)) =
      Real.exp (3 * δ * S.card) * ∏ i ∈ S, q i (y i) := by
    calc
      (∏ i ∈ S, Real.exp (3 * δ) * q i (y i)) =
          Real.exp ((S.card : ℝ) * (3 * δ)) * ∏ i ∈ S, q i (y i) := by
            rw [Finset.prod_mul_distrib, Finset.prod_const, ← Real.exp_nat_mul]
      _ = Real.exp (3 * δ * S.card) * ∏ i ∈ S, q i (y i) := by
            congr 2
            ring
  have hexp : Real.exp (ε * S.card) * (∏ i ∈ S, p i (y i)) ≤
      Real.exp (r * S.card) * ∏ i ∈ S, q i (y i) := by
    have hqprod : 0 ≤ ∏ i ∈ S, q i (y i) :=
      Finset.prod_nonneg fun i hi => hnq i (y i)
    calc
      Real.exp (ε * S.card) * (∏ i ∈ S, p i (y i)) ≤
          Real.exp (ε * S.card) * (∏ i ∈ S, Real.exp (3 * δ) * q i (y i)) :=
        mul_le_mul_of_nonneg_left hprod (Real.exp_nonneg _)
      _ = Real.exp ((ε + 3 * δ) * S.card) * ∏ i ∈ S, q i (y i) := by
        rw [hprod']
        calc
          Real.exp (ε * S.card) *
              (Real.exp (3 * δ * S.card) * ∏ i ∈ S, q i (y i)) =
            (Real.exp (ε * S.card) * Real.exp (3 * δ * S.card)) *
              ∏ i ∈ S, q i (y i) := by ring
          _ = Real.exp (ε * S.card + 3 * δ * S.card) *
              ∏ i ∈ S, q i (y i) := by rw [← Real.exp_add]
          _ = Real.exp ((ε + 3 * δ) * S.card) * ∏ i ∈ S, q i (y i) := by
              congr 2
              dsimp [ε, δ]
              ring
      _ ≤ Real.exp (r * S.card) * ∏ i ∈ S, q i (y i) := by
        apply mul_le_mul_of_nonneg_right _ hqprod
        apply Real.exp_le_exp.mpr
        dsimp [r, ε, δ]
        exact mul_le_mul_of_nonneg_right (hcoef) (by positivity)
  exact (hjoint S y hsize).trans hexp

/-- Price-directed witness, now an assembly of Steps 1–4. Its type is unchanged. -/
theorem price_directed_label_sampler :
    ∃ d₀ : ℕ, 1 ≤ d₀ ∧ ∀ d ≥ d₀, ∀ {R : Type} [Fintype R] [DecidableEq R]
      (q : R → Fin d → ℝ),
      (∀ i y, 0 ≤ q i y) →
      (∀ i, ∑ y, q i y = 1) →
      (∀ i y, q i y ≤ (d : ℝ) ^ (-(0.95 : ℝ))) →
      (∀ y, ∑ i, q i y ≤ 0.4) →
      ∀ c : R → Fin d → ℝ, ∃ Q : FinProb (R → Fin d),
        LabelInjectionSupported Q ∧ LabelNearProductBound d q Q ∧
        injectionTargetPrice q c ≤ injectionLabelPrice Q c := by
  have hAll : ∀ᶠ d : ℕ in Filter.atTop, ∀ {R : Type} [Fintype R] [DecidableEq R]
      (q : R → Fin d → ℝ),
      (∀ i y, 0 ≤ q i y) → (∀ i, ∑ y, q i y = 1) →
      (∀ i y, q i y ≤ (d : ℝ) ^ (-(0.95 : ℝ))) → (∀ y, ∑ i, q i y ≤ 0.4) →
      ∀ c : R → Fin d → ℝ, ∃ Q : FinProb (R → Fin d),
        LabelInjectionSupported Q ∧ LabelNearProductBound d q Q ∧
        injectionTargetPrice q c ≤ injectionLabelPrice Q c := by
    filter_upwards [balanced_completion_good_order, ordered_conditioned_sampler_estimates,
      price_perturbation_estimates, price_gain_dominates_relative_error,
      perturbed_joint_bound_transfer] with d hcomplete hsample hpert hgain hjoint
    intro R instR instDecR q hn hs ha hl c
    obtain ⟨hpn, hps, hpa, hpl, hpdom, hpgain⟩ := hpert q hn hs ha hl c
    obtain ⟨t, ht, hrows, qbar, e, hreal, hdummy, hdummycap, hcol, hordered⟩ :=
      hcomplete (injectionPricePerturbation q c) hpn hps hpa hpl
    obtain ⟨hG, hinj, hnear, hmarg⟩ := hsample t (fun k y => qbar (e k) y) hordered
    let emb : R ↪ Fin t := {
      toFun := fun i => e.symm (Sum.inl i)
      inj' := fun i j hij => Sum.inl_injective (e.symm.injective hij) }
    have hemb : ∀ i y, qbar (e (emb i)) y = injectionPricePerturbation q c i y := by
      intro i y
      change qbar (e (e.symm (Sum.inl i))) y = injectionPricePerturbation q c i y
      rw [e.apply_symm_apply]
      exact hreal i y
    obtain ⟨Q, hQinj, hQjoint, hQmarg⟩ := restrict_ordered_sampler
      (injectionPricePerturbation q c) (fun k y => qbar (e k) y) emb hemb
      (Injection.conditionedLaw _ hordered hG) hinj hnear hmarg
    exact ⟨Q, hQinj, hjoint q (injectionPricePerturbation q c) hn hpn hpdom Q hQjoint,
      hgain q c hn hs hps hpdom hpgain Q hQmarg⟩
  obtain ⟨d₀, hd₀⟩ := Filter.eventually_atTop.1 hAll
  refine ⟨max 1 d₀, Nat.le_max_left _ _, ?_⟩
  intro d hd
  exact hd₀ d (le_trans (Nat.le_max_right _ _) hd)

/-- L3.9d (03:736–768): abstract calibration by separation. If a compact convex set of
finite-dimensional marginal vectors has a member at least as good as the target in every linear
price, it contains the target. This form is independent of the sampler and is reusable in Section 16. -/
theorem calibration_by_separation {K : Type*} [Fintype K]
    (C : Set (K → ℝ)) (p : K → ℝ)
    (hcompact : IsCompact C) (hconvex : Convex ℝ C)
    (hprice : ∀ c : K → ℝ, ∃ q ∈ C, ∑ k, c k * p k ≤ ∑ k, c k * q k) :
    p ∈ C := by
  classical
  have hclosed : IsClosed C := hcompact.isClosed
  let half : StrongDual ℝ (K → ℝ) → Set (K → ℝ) :=
    fun f => {x | ∃ q ∈ C, f x ≤ f q}
  have hpinter : p ∈ Set.iInter half := by
    simp only [Set.mem_iInter]
    intro f
    let c : K → ℝ := fun k => f (Pi.single k (1 : ℝ))
    obtain ⟨q, hqC, hq⟩ := hprice c
    refine ⟨q, hqC, ?_⟩
    have hrepr (x : K → ℝ) : f x = ∑ k, c k * x k := by
      have hx : x = ∑ k, x k • Pi.single k (1 : ℝ) := pi_eq_sum_univ' x
      calc
        f x = f (∑ k, x k • Pi.single k (1 : ℝ)) := congrArg f hx
        _ = ∑ k, x k * f (Pi.single k (1 : ℝ)) := by simp only [map_sum, map_smul, smul_eq_mul]
        _ = ∑ k, c k * x k := by simp [c, mul_comm]
    calc
      f p = ∑ k, c k * p k := hrepr p
      _ ≤ ∑ k, c k * q k := hq
      _ = f q := (hrepr q).symm
  exact (iInter_halfSpaces_eq hconvex hclosed).symm ▸ hpinter

/-- The feasible marginal image is compact and convex: all constraints on the assignment law
are linear inequalities in a finite probability simplex. -/
theorem label_marginal_image_compact_convex {R : Type*} [Fintype R] [DecidableEq R]
    (d : ℕ) (q : R → Fin d → ℝ) :
    IsCompact (LabelMarginalImage d q) ∧ Convex ℝ (LabelMarginalImage d q) := by
  classical
  let X := R → Fin d
  let W := X → ℝ
  let NearIndex := {S : Finset R // (S.card : ℝ) ≤ (d : ℝ) ^ (0.025 : ℝ)} × X
  let eventFilter : (X → Prop) → Finset X := fun A =>
    @Finset.filter X A (fun x => Classical.propDecidable (A x)) Finset.univ
  let probW : NearIndex → W → ℝ := fun z w =>
    (eventFilter (fun x : X => ∀ i ∈ z.1.1, x i = z.2 i)).sum w
  let bound : NearIndex → ℝ := fun z =>
    Real.exp ((d : ℝ) ^ (-(0.04 : ℝ)) * z.1.1.card) * ∏ i ∈ z.1.1, q i (z.2 i)
  let Nonneg : Set W := Set.iInter fun x : X => {w | 0 ≤ w x}
  let Total : Set W := {w | ∑ x : X, w x = 1}
  let BadIndex := {x : X // ¬ Function.Injective x}
  let Supported : Set W := Set.iInter fun x : BadIndex => {w | w x.1 = 0}
  let Near : Set W := Set.iInter fun z : NearIndex => {w | probW z w ≤ bound z}
  let Good : Set W := Nonneg ∩ (Total ∩ (Supported ∩ Near))
  let box : Set W := Set.pi Set.univ (fun _ : X => Set.Icc (0 : ℝ) 1)
  let marg : W → (R × Fin d → ℝ) := fun w iy =>
    (eventFilter (fun x : X => x iy.1 = iy.2)).sum w
  have hnonnegClosed : IsClosed Nonneg := by
    exact isClosed_iInter fun x => isClosed_Ici.preimage (continuous_apply x)
  have htotalClosed : IsClosed Total := by
    exact isClosed_eq (by fun_prop) continuous_const
  have hsupportedClosed : IsClosed Supported := by
    exact isClosed_iInter fun x => isClosed_eq (continuous_apply x.1) continuous_const
  have hnearClosed : IsClosed Near := by
    change IsClosed (Set.iInter fun z : NearIndex => {w : W | probW z w ≤ bound z})
    exact isClosed_iInter fun z => isClosed_le (by
      dsimp [probW]
      exact continuous_finsetSum _ (fun x hx => continuous_apply x)) continuous_const
  have hgoodClosed : IsClosed Good := by
    exact hnonnegClosed.inter (htotalClosed.inter (hsupportedClosed.inter hnearClosed))
  have hboxCompact : IsCompact box := by
    exact isCompact_univ_pi fun _ : X => isCompact_Icc
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
  have hgoodCompact : IsCompact Good := hboxCompact.of_isClosed_subset hgoodClosed hgoodSubsetBox
  have hmargContinuous : Continuous marg := by
    apply continuous_pi
    intro iy
    dsimp [marg]
    exact continuous_finsetSum _ (fun x hx => continuous_apply x)
  have hprSum (Q : FinProb X) (A : X → Prop) :
      Q.pr A = (eventFilter A).sum Q.w := by
    simp [FinProb.pr, eventFilter, Finset.sum_filter]
  have himage : LabelMarginalImage d q = marg '' Good := by
    ext v
    constructor
    · rintro ⟨Q, hQinj, hQnear, hv⟩
      have hQnon : Q.w ∈ Nonneg := by
        simp only [Nonneg, Set.mem_iInter]
        exact Q.nonneg
      have hQtotal : Q.w ∈ Total := Q.sum_eq_one
      have hQsupported : Q.w ∈ Supported := by
        simp only [Supported, Set.mem_iInter]
        intro x
        change Q.w x.1 = 0
        by_contra hne
        exact x.2 (hQinj x.1 hne)
      have hQNear : Q.w ∈ Near := by
        simp only [Near, Set.mem_iInter]
        intro z
        change probW z Q.w ≤ bound z
        have hpr : probW z Q.w = Q.pr (fun x => ∀ i ∈ z.1.1, x i = z.2 i) := by
          dsimp [probW]
          rw [hprSum]
        rw [hpr]
        simpa [bound] using hQnear z.1.1 z.2 z.1.2
      refine ⟨Q.w, ⟨hQnon, hQtotal, hQsupported, hQNear⟩, ?_⟩
      ext iy
      calc
        marg Q.w iy = Q.pr (fun x => x iy.1 = iy.2) := by
          dsimp [marg]
          rw [hprSum]
        _ = LabelMarginalVector Q iy := rfl
        _ = v iy := (hv iy.1 iy.2).symm
    · rintro ⟨w, hw, hv⟩
      let Q : FinProb X := ⟨w, fun x => Set.mem_iInter.mp hw.1 x, hw.2.1⟩
      have hQw : Q.w = w := by rfl
      refine ⟨Q, ?_, ?_, ?_⟩
      · intro x hx
        by_contra hnot
        have hzero : w x = 0 := Set.mem_iInter.mp hw.2.2.1 ⟨x, hnot⟩
        exact hx (by simpa [Q] using hzero)
      · intro S y hcard
        have h := Set.mem_iInter.mp hw.2.2.2 ⟨⟨S, hcard⟩, y⟩
        have hpr : probW ⟨⟨S, hcard⟩, y⟩ w = Q.pr (fun x => ∀ i ∈ S, x i = y i) := by
          dsimp [probW]
          rw [hprSum]
        change probW ⟨⟨S, hcard⟩, y⟩ w ≤ bound ⟨⟨S, hcard⟩, y⟩ at h
        rw [hpr] at h
        simpa [bound] using h
      · intro i y
        calc
          v (i, y) = marg w (i, y) := (congrFun hv (i, y)).symm
          _ = Q.pr (fun x => x i = y) := by
            dsimp [marg]
            rw [hprSum]
          _ = LabelMarginalVector Q (i, y) := rfl
  have hcompactImage : IsCompact (marg '' Good) := hgoodCompact.image hmargContinuous
  constructor
  · simpa [himage] using hcompactImage
  · intro v hv w hw a b ha hb hab
    rcases hv with ⟨Q₁, hQ₁inj, hQ₁near, hv⟩
    rcases hw with ⟨Q₂, hQ₂inj, hQ₂near, hw⟩
    let Q : FinProb X := {
      w := fun x => a * Q₁.w x + b * Q₂.w x
      nonneg := fun x => add_nonneg (mul_nonneg ha (Q₁.nonneg x)) (mul_nonneg hb (Q₂.nonneg x))
      sum_eq_one := by
        calc
          ∑ x : X, (a * Q₁.w x + b * Q₂.w x) =
              a * (∑ x : X, Q₁.w x) + b * (∑ x : X, Q₂.w x) := by
            simp [Finset.sum_add_distrib, Finset.mul_sum]
          _ = a + b := by rw [Q₁.sum_eq_one, Q₂.sum_eq_one]; ring
          _ = 1 := hab
    }
    have hpr_mix (A : X → Prop) : Q.pr A = a * Q₁.pr A + b * Q₂.pr A := by
      calc
        Q.pr A = ∑ x : X, (if A x then a * Q₁.w x + b * Q₂.w x else 0) := by rfl
        _ = ∑ x : X, ((if A x then a * Q₁.w x else 0) +
              (if A x then b * Q₂.w x else 0)) := by
          apply Finset.sum_congr rfl
          intro x hx
          by_cases h : A x <;> simp [h]
        _ = a * Q₁.pr A + b * Q₂.pr A := by
          rw [Finset.sum_add_distrib]
          simp [FinProb.pr, Finset.mul_sum]
          rfl
    refine ⟨Q, ?_, ?_, ?_⟩
    · intro x hx
      by_cases h₁ : Q₁.w x = 0
      · have h₂ : Q₂.w x ≠ 0 := by
          intro h₂
          apply hx
          simp [Q, h₁, h₂]
        exact hQ₂inj x h₂
      · exact hQ₁inj x h₁
    · intro S y hcard
      have hp₁ := hQ₁near S y hcard
      have hp₂ := hQ₂near S y hcard
      rw [hpr_mix]
      calc
        a * Q₁.pr (fun x => ∀ i ∈ S, x i = y i) + b * Q₂.pr (fun x => ∀ i ∈ S, x i = y i)
            ≤ a * (bound ⟨⟨S, hcard⟩, y⟩) + b * (bound ⟨⟨S, hcard⟩, y⟩) :=
          add_le_add (mul_le_mul_of_nonneg_left hp₁ ha) (mul_le_mul_of_nonneg_left hp₂ hb)
        _ = bound ⟨⟨S, hcard⟩, y⟩ := by rw [← add_mul, hab, one_mul]
    · intro i y
      have hv' := hv i y
      have hw' := hw i y
      change a * v (i, y) + b * w (i, y) = LabelMarginalVector Q (i, y)
      simpa [hv', hw', LabelMarginalVector] using (hpr_mix (fun x : X => x i = y)).symm

/-- L3.9d, finite-label specialization: calibrate the price witnesses to the exact row-label
marginals while retaining injective support and every queried-label upper bound. -/
theorem calibrate_label_marginals {R : Type*} [Fintype R] [DecidableEq R]
    (d : ℕ) (q : R → Fin d → ℝ)
    (hprice : ∀ c : R → Fin d → ℝ, ∃ Q : FinProb (R → Fin d),
      LabelInjectionSupported Q ∧ LabelNearProductBound d q Q ∧
      injectionTargetPrice q c ≤ injectionLabelPrice Q c) :
    ∃ Q : FinProb (R → Fin d), LabelInjectionSupported Q ∧
      LabelNearProductBound d q Q ∧
      ∀ i y, Q.pr (fun x => x i = y) = q i y := by
  let C := LabelMarginalImage d q
  let pvec : (R × Fin d) → ℝ := fun iy => q iy.1 iy.2
  obtain ⟨hcompact, hconvex⟩ := label_marginal_image_compact_convex d q
  have hprice' : ∀ c : (R × Fin d) → ℝ,
      ∃ v ∈ C, ∑ k, c k * pvec k ≤ ∑ k, c k * v k := by
    intro c
    let c' : R → Fin d → ℝ := fun i y => c (i, y)
    obtain ⟨Q, hQinj, hQjoint, hQprice⟩ := hprice c'
    refine ⟨LabelMarginalVector Q, ?_, ?_⟩
    · exact ⟨Q, hQinj, hQjoint, fun _ _ => rfl⟩
    · have htarget : injectionTargetPrice q c' = ∑ k, c k * pvec k := by
        simp [injectionTargetPrice, pvec, c', Fintype.sum_prod_type]
      have hlaw : injectionLabelPrice Q c' = ∑ k, c k * LabelMarginalVector Q k := by
        simp [injectionLabelPrice, LabelMarginalVector, c', Fintype.sum_prod_type]
      rw [← htarget, ← hlaw]
      exact hQprice
  have hpvec : pvec ∈ C := calibration_by_separation C pvec hcompact hconvex hprice'
  rcases hpvec with ⟨Q, hQinj, hQjoint, hQmarg⟩
  refine ⟨Q, hQinj, hQjoint, ?_⟩
  intro i y
  have h := hQmarg i y
  simpa [pvec, LabelMarginalVector] using h.symm

/-- L3.9e (03:618–625): draw full outputs from their conditional laws after the labels have
been sampled. Exact label marginals and the label joint bound transfer to exact full-output
marginals and the corresponding near-product bound. -/
theorem lift_side_data {R : Type*} [Fintype R] [DecidableEq R]
    {Ω : R → Type} [∀ i, Fintype (Ω i)] [∀ i, DecidableEq (Ω i)]
    (d : ℕ) (lab : ∀ i, Ω i → Fin d) (p : ∀ i, FinProb (Ω i))
    (q : R → Fin d → ℝ) (Q : FinProb (R → Fin d))
    (hq : ∀ i y, q i y = injectionLabelMass (p i) (lab i) y)
    (hQinj : LabelInjectionSupported Q)
    (hQmarg : ∀ i y, Q.pr (fun x => x i = y) = q i y)
    (hQjoint : LabelNearProductBound d q Q) :
    ∃ J : FinProb (∀ i, Ω i),
      (∀ ω, J.w ω ≠ 0 → Function.Injective (fun i => lab i (ω i))) ∧
      (∀ i o, J.pr (fun ω => ω i = o) = (p i).w o) ∧
      (∀ (S : Finset R) (o : ∀ i, Ω i), (S.card : ℝ) ≤ (d : ℝ) ^ (0.025 : ℝ) →
        J.pr (fun ω => ∀ i ∈ S, ω i = o i) ≤
          Real.exp ((d : ℝ) ^ (-(0.04 : ℝ)) * S.card) * ∏ i ∈ S, (p i).w (o i)) := by
  classical
  let eventFilter : ((R → Fin d) → Prop) → Finset (R → Fin d) := fun A =>
    @Finset.filter (R → Fin d) A (fun x => Classical.propDecidable (A x)) Finset.univ
  have hprQ (A : (R → Fin d) → Prop) :
      Q.pr A = (eventFilter A).sum Q.w := by
    simp [FinProb.pr, eventFilter, Finset.sum_filter]
  have hfilterClassicalQ (A : (R → Fin d) → Prop) [DecidablePred A] :
      Finset.univ.filter A = eventFilter A := by
    unfold eventFilter
    symm
    exact Finset.filter_congr_decidable Finset.univ A
      (fun x => Classical.propDecidable (A x))
  have hsumFilterQ (A : (R → Fin d) → Prop) (f : (R → Fin d) → ℝ) [DecidablePred A] :
      (∑ x, if A x then f x else 0) = (eventFilter A).sum f := by
    calc
      (∑ x, if A x then f x else 0) = (Finset.univ.filter A).sum f := by
        rw [← Finset.sum_filter]
      _ = (eventFilter A).sum f := by
        exact congrArg (fun s : Finset (R → Fin d) => s.sum f) (hfilterClassicalQ A)
  have hQcoordLe (x : R → Fin d) (i : R) :
      Q.w x ≤ Q.pr (fun z => z i = x i) := by
    calc
      Q.w x ≤ (eventFilter (fun z => z i = x i)).sum Q.w :=
        Finset.single_le_sum (fun z _ => Q.nonneg z) (by simp [eventFilter])
      _ = Q.pr (fun z => z i = x i) := (hprQ _).symm
  have hQpositive (x : R → Fin d) (hx : Q.w x ≠ 0) (i : R) : 0 < q i (x i) := by
    have hpos : 0 < Q.w x := lt_of_le_of_ne (Q.nonneg x) (Ne.symm hx)
    have hle : Q.w x ≤ q i (x i) := by
      rw [← hQmarg i (x i)]
      exact hQcoordLe x i
    exact lt_of_lt_of_le hpos hle
  have hqnonneg (i : R) (y : Fin d) : 0 ≤ q i y := by
    rw [hq i y]
    unfold injectionLabelMass
    exact Finset.sum_nonneg fun o _ => by
      split_ifs
      · exact (p i).nonneg o
      · exact le_rfl
  have hzeroLabel (i : R) (y : Fin d) (o : Ω i)
      (hqzero : q i y = 0) (hlabel : lab i o = y) : (p i).w o = 0 := by
    have hle : (p i).w o ≤ injectionLabelMass (p i) (lab i) y := by
      unfold injectionLabelMass
      let f : Ω i → ℝ := fun o' => if lab i o' = y then (p i).w o' else 0
      calc
        (p i).w o = f o := by simp [f, hlabel]
        _ ≤ ∑ o', f o' :=
          Finset.single_le_sum (f := f) (fun o' _ => by
            dsimp [f]
            by_cases h : lab i o' = y
            · simpa [h] using (p i).nonneg o'
            · simp [h])
            (Finset.mem_univ o)
    rw [← hq i y, hqzero] at hle
    exact le_antisymm hle ((p i).nonneg o)
  let condLaw : ∀ i, Fin d → FinProb (Ω i) := fun i y =>
    if hy : 0 < q i y then
      { w := fun o => if lab i o = y then (p i).w o / q i y else 0
        nonneg := by
          intro o
          by_cases ho : lab i o = y
          · simp only [if_pos ho]
            exact div_nonneg ((p i).nonneg o) hy.le
          · simp [ho]
        sum_eq_one := by
          have hmass : ∑ o : Ω i, (if lab i o = y then (p i).w o else 0) = q i y := by
            simpa [injectionLabelMass] using (hq i y).symm
          calc
            ∑ o : Ω i, (if lab i o = y then (p i).w o / q i y else 0) =
                ∑ o : Ω i, (if lab i o = y then (p i).w o else 0) / q i y := by
              apply Finset.sum_congr rfl
              intro o ho
              by_cases h : lab i o = y <;> simp [h]
            _ = (∑ o : Ω i, if lab i o = y then (p i).w o else 0) / q i y := by
              simpa using (Finset.sum_div Finset.univ
                (fun o => if lab i o = y then (p i).w o else 0) (q i y)).symm
            _ = 1 := by rw [hmass, div_self hy.ne'] }
    else p i
  have hcondWeight (i : R) (y : Fin d) (o : Ω i) (hy : 0 < q i y) :
      (condLaw i y).w o = if lab i o = y then (p i).w o / q i y else 0 := by
    simp [condLaw, hy]
  have hcondScaled (i : R) (y : Fin d) (o : Ω i) (hy : lab i o = y) :
      q i y * (condLaw i y).w o = (p i).w o := by
    by_cases hpos : 0 < q i y
    · rw [hcondWeight i y o hpos, if_pos hy]
      field_simp [ne_of_gt hpos]
    · have hzero : q i y = 0 := le_antisymm (le_of_not_gt hpos) (hqnonneg i y)
      have hpzero := hzeroLabel i y o hzero hy
      simp [condLaw, hpos, hzero, hy, hpzero]
  let kernel : (R → Fin d) → FinProb (∀ i, Ω i) :=
    fun x => FinProb.pi (fun i => condLaw i (x i))
  have hpiEvent (K : ∀ i, FinProb (Ω i)) (S : Finset R) (o : ∀ i, Ω i) :
      (FinProb.pi K).pr (fun ω => ∀ i ∈ S, ω i = o i) =
        ∏ i ∈ S, (K i).w (o i) := by
    let event : (∀ i, Ω i) → Prop := fun ω => ∀ i ∈ S, ω i = o i
    let outFilter : Finset (∀ i, Ω i) :=
      @Finset.filter (∀ i, Ω i) event (fun ω => Classical.propDecidable (event ω)) Finset.univ
    have hfilterEq : Finset.univ.filter event = outFilter := by
      unfold outFilter
      symm
      exact Finset.filter_congr_decidable Finset.univ event
        (fun ω => Classical.propDecidable (event ω))
    have hsumFilterOut (g : (∀ i, Ω i) → ℝ) :
        (∑ ω, if event ω then g ω else 0) = outFilter.sum g := by
      calc
        (∑ ω, if event ω then g ω else 0) = (Finset.univ.filter event).sum g := by
          rw [← Finset.sum_filter]
        _ = outFilter.sum g := by rw [hfilterEq]
    let f : ∀ i, Ω i → ℝ := fun i z =>
      if i ∈ S then if z = o i then (K i).w z else 0 else (K i).w z
    have hpiPr : (FinProb.pi K).pr event = outFilter.sum (fun ω => ∏ i, (K i).w (ω i)) := by
      simp [FinProb.pr, FinProb.pi, outFilter, Finset.sum_filter]
    have hpoint (ω : ∀ i, Ω i) :
        (if event ω then ∏ i, (K i).w (ω i) else 0) =
          ∏ i, f i (ω i) := by
      by_cases hall : event ω
      · simp only [if_pos hall]
        apply Finset.prod_congr rfl
        intro i hi
        by_cases his : i ∈ S
        · simp [f, his, hall i his]
        · simp [f, his]
      · have hall' : ¬ ∀ i ∈ S, ω i = o i := by simpa [event] using hall
        push_neg at hall'
        rcases hall' with ⟨i, hi, hne⟩
        have hnot : ¬ event ω := hall
        have hz : f i (ω i) = 0 := by simp [f, hi, hne]
        simp only [if_neg hnot]
        exact (Finset.prod_eq_zero (Finset.mem_univ i) hz).symm
    calc
      (FinProb.pi K).pr (fun ω => ∀ i ∈ S, ω i = o i) =
          outFilter.sum (fun ω => ∏ i, (K i).w (ω i)) := hpiPr
      _ = ∑ ω : (∀ i, Ω i), ∏ i, f i (ω i) := by
        rw [(hsumFilterOut (fun ω => ∏ i, (K i).w (ω i))).symm]
        apply Finset.sum_congr rfl
        intro ω hω
        exact hpoint ω
      _ = ∏ i, ∑ z, f i z := by rw [← Fintype.prod_sum]
      _ = ∏ i, (if i ∈ S then (K i).w (o i) else 1) := by
        apply Finset.prod_congr rfl
        intro i hi
        by_cases his : i ∈ S
        · simp [f, his]
        · simp [f, his, (K i).sum_eq_one]
      _ = ∏ i ∈ S, (K i).w (o i) := by
        rw [← Finset.prod_filter]
        simp
  have hΩne (i : R) : Nonempty (Ω i) := by
    have hcard : 0 < Fintype.card (Ω i) := by
      by_contra hn
      have hz : Fintype.card (Ω i) = 0 := Nat.eq_zero_of_not_pos hn
      letI : IsEmpty (Ω i) := Fintype.card_eq_zero_iff.mp hz
      have hsum : ∑ o : Ω i, (p i).w o = 0 := by simp
      rw [(p i).sum_eq_one] at hsum
      norm_num at hsum
    exact Fintype.card_pos_iff.mp hcard
  let defaultOutput : ∀ i, Ω i := fun i => Classical.choice (hΩne i)
  have hpiCoord (K : ∀ i, FinProb (Ω i)) (i : R) (o : Ω i) :
      (FinProb.pi K).pr (fun ω => ω i = o) = (K i).w o := by
    let o' : ∀ j, Ω j := fun j => if h : j = i then h.symm ▸ o else defaultOutput j
    have h := hpiEvent K {i} o'
    simpa [o'] using h
  let J : FinProb (∀ i, Ω i) := {
    w := fun ω => ∑ x : R → Fin d, Q.w x * (kernel x).w ω
    nonneg := fun ω => Finset.sum_nonneg fun x _ => mul_nonneg (Q.nonneg x) ((kernel x).nonneg ω)
    sum_eq_one := by
      calc
        ∑ ω, ∑ x : R → Fin d, Q.w x * (kernel x).w ω =
            ∑ x : R → Fin d, ∑ ω, Q.w x * (kernel x).w ω := Finset.sum_comm
        _ = ∑ x : R → Fin d, Q.w x := by
          apply Finset.sum_congr rfl
          intro x hx
          rw [← Finset.mul_sum, (kernel x).sum_eq_one, mul_one]
        _ = 1 := Q.sum_eq_one
  }
  have hJpr (A : (∀ i, Ω i) → Prop) :
      J.pr A = ∑ x : R → Fin d, Q.w x * (kernel x).pr A := by
    unfold FinProb.pr
    change (∑ ω, if A ω then ∑ x : R → Fin d, Q.w x * (kernel x).w ω else 0) = _
    calc
      (∑ ω, if A ω then ∑ x : R → Fin d, Q.w x * (kernel x).w ω else 0) =
          ∑ ω, ∑ x : R → Fin d, if A ω then Q.w x * (kernel x).w ω else 0 := by
        apply Finset.sum_congr rfl
        intro ω hω
        by_cases hA : A ω <;> simp [hA]
      _ = ∑ x : R → Fin d, ∑ ω, if A ω then Q.w x * (kernel x).w ω else 0 := Finset.sum_comm
      _ = ∑ x : R → Fin d, Q.w x * (kernel x).pr A := by
        apply Finset.sum_congr rfl
        intro x hx
        calc
          (∑ ω, if A ω then Q.w x * (kernel x).w ω else 0) =
              ∑ ω, Q.w x * (if A ω then (kernel x).w ω else 0) := by
            apply Finset.sum_congr rfl
            intro ω hω
            by_cases hA : A ω <;> simp [hA]
          _ = Q.w x * ∑ ω, if A ω then (kernel x).w ω else 0 := by rw [← Finset.mul_sum]
          _ = Q.w x * (kernel x).pr A := rfl
  refine ⟨J, ?_, ?_, ?_⟩
  · intro ω hω
    have hterm : ∃ x : R → Fin d, Q.w x * (kernel x).w ω ≠ 0 := by
      by_contra h
      push_neg at h
      apply hω
      simp [J, h]
    obtain ⟨x, hxterm⟩ := hterm
    have hxQ : Q.w x ≠ 0 := by
      intro hzero
      apply hxterm
      simp [hzero]
    have hxkernel : (kernel x).w ω ≠ 0 := by
      intro hzero
      apply hxterm
      simp [hzero]
    have hcoord (i : R) : lab i (ω i) = x i := by
      by_contra hneq
      have hz : (condLaw i (x i)).w (ω i) = 0 := by
        rw [hcondWeight i (x i) (ω i) (hQpositive x hxQ i)]
        simp [hneq]
      have hzprod : (kernel x).w ω = 0 := by
        unfold kernel FinProb.pi
        exact Finset.prod_eq_zero (Finset.mem_univ i) hz
      exact hxkernel hzprod
    have hinj := hQinj x hxQ
    intro i j hij
    have hi := hcoord i
    have hj := hcoord j
    change lab i (ω i) = lab j (ω j) at hij
    rw [hi, hj] at hij
    exact hinj hij
  · intro i o
    have hfiber (g : Fin d → ℝ) :
        ∑ x : R → Fin d, Q.w x * g (x i) =
          ∑ y : Fin d, Q.pr (fun x => x i = y) * g y := by
      classical
      have hsingle (x : R → Fin d) :
          (∑ y : Fin d, if x i = y then Q.w x * g y else 0) = Q.w x * g (x i) := by
        first | simp [Finset.sum_ite_eq', eq_comm] | rfl
      symm
      calc
        ∑ y : Fin d, Q.pr (fun x => x i = y) * g y =
            ∑ y : Fin d, ∑ x : R → Fin d, if x i = y then Q.w x * g y else 0 := by
          apply Finset.sum_congr rfl
          intro y hy
          rw [hprQ]
          calc
            (eventFilter (fun x => x i = y)).sum Q.w * g y =
                (eventFilter (fun x => x i = y)).sum (fun x => Q.w x * g y) := by
              rw [Finset.sum_mul]
            _ = ∑ x : R → Fin d, if x i = y then Q.w x * g y else 0 :=
              (hsumFilterQ (fun x : R → Fin d => x i = y)
                (fun x => Q.w x * g y)).symm
        _ = ∑ x : R → Fin d, ∑ y : Fin d, if x i = y then Q.w x * g y else 0 :=
          Finset.sum_comm
        _ = ∑ x : R → Fin d, Q.w x * g (x i) := by
          apply Finset.sum_congr rfl
          intro x hx
          exact hsingle x
    have hcollapsed : ∑ y : Fin d, q i y * (condLaw i y).w o = (p i).w o := by
      calc
        ∑ y : Fin d, q i y * (condLaw i y).w o =
            ∑ y : Fin d, (if lab i o = y then (p i).w o else 0) := by
          apply Finset.sum_congr rfl
          intro y hy
          by_cases hlabel : lab i o = y
          · rw [if_pos hlabel]
            exact hcondScaled i y o hlabel
          · rw [if_neg hlabel]
            by_cases hpos : 0 < q i y
            · rw [hcondWeight i y o hpos]
              simp [hlabel]
            · have hzero : q i y = 0 := le_antisymm (le_of_not_gt hpos) (hqnonneg i y)
              simp [condLaw, hpos, hzero]
        _ = (p i).w o := by simp [Finset.sum_ite_eq', eq_comm]
    calc
      J.pr (fun ω => ω i = o) =
          ∑ x : R → Fin d, Q.w x * (kernel x).pr (fun ω => ω i = o) := hJpr _
      _ = ∑ x : R → Fin d, Q.w x * (condLaw i (x i)).w o := by
        apply Finset.sum_congr rfl
        intro x hx
        exact congrArg (fun z => Q.w x * z) (hpiCoord (fun j => condLaw j (x j)) i o)
      _ = ∑ y : Fin d, Q.pr (fun x => x i = y) * (condLaw i y).w o :=
        hfiber (fun y => (condLaw i y).w o)
      _ = ∑ y : Fin d, q i y * (condLaw i y).w o := by
        apply Finset.sum_congr rfl
        intro y hy
        rw [hQmarg i y]
      _ = (p i).w o := hcollapsed
  · intro S o hsize
    let y : R → Fin d := fun i => lab i (o i)
    by_cases hzerorow : ∃ i ∈ S, q i (y i) = 0
    · obtain ⟨i, hiS, hi0⟩ := hzerorow
      have hpo : (p i).w (o i) = 0 := hzeroLabel i (y i) (o i) hi0 rfl
      have hJzero : J.pr (fun ω => ∀ i ∈ S, ω i = o i) = 0 := by
        rw [hJpr]
        apply Finset.sum_eq_zero
        intro x hx
        by_cases hxQ : Q.w x = 0
        · simp [hxQ]
        · have hqpos : 0 < q i (x i) := hQpositive x hxQ i
          have hneq : lab i (o i) ≠ x i := by
            intro heq
            have hzero : q i (x i) = 0 := by simpa [y, heq] using hi0
            exact hqpos.ne' hzero
          have hfactor : (condLaw i (x i)).w (o i) = 0 := by
            rw [hcondWeight i (x i) (o i) hqpos]
            simp [y, hneq]
          have hkernelzero : (kernel x).pr (fun ω => ∀ i ∈ S, ω i = o i) = 0 := by
            rw [hpiEvent (fun j => condLaw j (x j)) S o]
            exact Finset.prod_eq_zero hiS hfactor
          simp [hkernelzero]
      rw [hJzero]
      exact mul_nonneg (Real.exp_nonneg _) <| Finset.prod_nonneg fun i hi => (p i).nonneg (o i)
    · have hqposS : ∀ i ∈ S, 0 < q i (y i) := by
        intro i hi
        have hn : 0 ≤ q i (y i) := hqnonneg i (y i)
        have hne : q i (y i) ≠ 0 := by
          intro he
          exact hzerorow ⟨i, hi, he⟩
        exact lt_of_le_of_ne hn (Ne.symm hne)
      have hfactor (x : R → Fin d) (hx : Q.w x ≠ 0) :
          ∏ i ∈ S, (condLaw i (x i)).w (o i) =
            if ∀ i ∈ S, x i = y i then ∏ i ∈ S, (p i).w (o i) / q i (y i) else 0 := by
        by_cases hall : ∀ i ∈ S, x i = y i
        · simp only [if_pos hall]
          apply Finset.prod_congr rfl
          intro i hi
          rw [hall i hi, hcondWeight i (y i) (o i) (hqposS i hi)]
          simp [y]
        · have hnot : ¬ ∀ i ∈ S, x i = y i := hall
          push_neg at hall
          rcases hall with ⟨i, hi, hneq⟩
          have hqpos : 0 < q i (x i) := hQpositive x hx i
          have hz : (condLaw i (x i)).w (o i) = 0 := by
            have hlabel : lab i (o i) ≠ x i := by simpa [y, eq_comm] using hneq
            rw [hcondWeight i (x i) (o i) hqpos]
            simp [hlabel]
          simp only [if_neg hnot]
          exact Finset.prod_eq_zero (s := S)
            (f := fun j => (condLaw j (x j)).w (o j)) hi hz
      have hratio : ∏ i ∈ S, (p i).w (o i) / q i (y i) ≥ 0 :=
        Finset.prod_nonneg fun i hi => div_nonneg ((p i).nonneg _) (hqnonneg i _)
      have hJformula : J.pr (fun ω => ∀ i ∈ S, ω i = o i) =
          (∏ i ∈ S, (p i).w (o i) / q i (y i)) * Q.pr (fun x => ∀ i ∈ S, x i = y i) := by
        calc
          J.pr (fun ω => ∀ i ∈ S, ω i = o i) =
              ∑ x : R → Fin d, Q.w x * (kernel x).pr (fun ω => ∀ i ∈ S, ω i = o i) :=
            hJpr _
          _ = ∑ x : R → Fin d, Q.w x * ∏ i ∈ S, (condLaw i (x i)).w (o i) := by
            apply Finset.sum_congr rfl
            intro x hx
            rw [hpiEvent (fun j => condLaw j (x j)) S o]
          _ = ∑ x, Q.w x *
                (if ∀ i ∈ S, x i = y i then (∏ i ∈ S, (p i).w (o i) / q i (y i)) else 0) := by
            apply Finset.sum_congr rfl
            intro x hx
            by_cases hxQ : Q.w x = 0
            · simp [hxQ]
            · rw [hfactor x hxQ]
          _ = (∏ i ∈ S, (p i).w (o i) / q i (y i)) *
                Q.pr (fun x => ∀ i ∈ S, x i = y i) := by
            calc
              ∑ x, Q.w x * (if ∀ i ∈ S, x i = y i then (∏ i ∈ S, (p i).w (o i) / q i (y i)) else 0) =
                  ∑ x, (if ∀ i ∈ S, x i = y i then Q.w x * (∏ i ∈ S, (p i).w (o i) / q i (y i)) else 0) := by
                apply Finset.sum_congr rfl
                intro x hx
                by_cases h : ∀ i ∈ S, x i = y i <;> simp [h]
              _ = (∏ i ∈ S, (p i).w (o i) / q i (y i)) *
                    Q.pr (fun x => ∀ i ∈ S, x i = y i) := by
                calc
                  ∑ x, (if ∀ i ∈ S, x i = y i then
                    Q.w x * (∏ i ∈ S, (p i).w (o i) / q i (y i)) else 0) =
                      (eventFilter (fun x => ∀ i ∈ S, x i = y i)).sum
                        (fun x => Q.w x * (∏ i ∈ S, (p i).w (o i) / q i (y i))) :=
                    hsumFilterQ
                      (fun x : R → Fin d => ∀ i ∈ S, x i = y i)
                      (fun x : R → Fin d => Q.w x * ∏ i ∈ S, (p i).w (o i) / q i (y i))
                  _ = (eventFilter (fun x => ∀ i ∈ S, x i = y i)).sum Q.w *
                        (∏ i ∈ S, (p i).w (o i) / q i (y i)) :=
                    (Finset.sum_mul _ Q.w (∏ i ∈ S, (p i).w (o i) / q i (y i))).symm
                  _ = (∏ i ∈ S, (p i).w (o i) / q i (y i)) *
                        (eventFilter (fun x => ∀ i ∈ S, x i = y i)).sum Q.w := by ring
                  _ = (∏ i ∈ S, (p i).w (o i) / q i (y i)) *
                        Q.pr (fun x => ∀ i ∈ S, x i = y i) := by rw [← hprQ]
      have hprice := hQjoint S y hsize
      calc
        J.pr (fun ω => ∀ i ∈ S, ω i = o i) =
            (∏ i ∈ S, (p i).w (o i) / q i (y i)) * Q.pr (fun x => ∀ i ∈ S, x i = y i) := hJformula
        _ ≤ (∏ i ∈ S, (p i).w (o i) / q i (y i)) *
                (Real.exp ((d : ℝ) ^ (-(0.04 : ℝ)) * S.card) * ∏ i ∈ S, q i (y i)) :=
          mul_le_mul_of_nonneg_left hprice hratio
        _ = Real.exp ((d : ℝ) ^ (-(0.04 : ℝ)) * S.card) * ∏ i ∈ S, (p i).w (o i) := by
          rw [Finset.prod_div_distrib]
          have hcancel : ∀ i ∈ S, q i (y i) ≠ 0 := fun i hi => (hqposS i hi).ne'
          have hprodq : (∏ i ∈ S, q i (y i)) ≠ 0 := by
            apply Finset.prod_ne_zero_iff.mpr
            intro i hi
            exact hcancel i hi
          field_simp [hprodq]

end HypercubeRamsey
