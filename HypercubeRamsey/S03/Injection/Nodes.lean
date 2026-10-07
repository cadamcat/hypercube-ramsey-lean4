import HypercubeRamsey.Framework.FinProb

/-!
Blueprint nodes L3.9a–e for calibrated near-product injections.  The sampler estimates are
stated with explicit slack constants; the main theorem composes the price witness, calibration,
and side-data transfer below.
-/

namespace HypercubeRamsey

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

/-- L3.9a (03:627–647): complete a low-load family by dummy rows and choose an order whose
column prefixes track their uniform targets. The completion has `ceil(2d/3)` rows, unit row
masses, equal column sums, and dummy atoms bounded by `10/d`. -/
theorem balanced_completion_good_order {R : Type*} [Fintype R] [DecidableEq R]
    (d : ℕ) (hd : 100 ≤ d) (q : R → Fin d → ℝ)
    (hq_nonneg : ∀ i y, 0 ≤ q i y)
    (hq_sum : ∀ i, ∑ y, q i y = 1)
    (hq_atom : ∀ i y, q i y ≤ (d : ℝ) ^ (-(0.95 : ℝ)))
    (hq_load : ∀ y, ∑ i, q i y ≤ 1 / 2)
    (hq_rows : (Fintype.card R : ℝ) ≤ (d : ℝ) / 2) :
    ∃ t : ℕ, (2 / 3 : ℝ) * d ≤ t ∧ (t : ℝ) ≤ (2 / 3 : ℝ) * d + 1 ∧
      Fintype.card R ≤ t ∧
      ∃ qbar : (R ⊕ Fin (t - Fintype.card R)) → Fin d → ℝ,
        (∀ j y, 0 ≤ qbar j y) ∧ (∀ j, ∑ y, qbar j y = 1) ∧
        (∀ i y, qbar (Sum.inl i) y = q i y) ∧
        (∀ y, ∑ j, qbar j y = (t : ℝ) / d) ∧
        (∀ j y, qbar j y ≤ 10 / d) ∧
        ∃ e : Fin t ≃ (R ⊕ Fin (t - Fintype.card R)),
          ∀ (j : Fin t) y,
            |(∑ k : Fin t, if k.val < j.val then qbar (e k) y else 0) -
              (j.val : ℝ) / d| ≤ 10 * (d : ℝ) ^ (-(1 / 8 : ℝ)) := by
  sorry

/-- L3.9b (03:649–693): the sequential sampler tracks all row-label masses when the ordered
prefixes are balanced. The conclusion records the simultaneous singleton estimate needed by
the likelihood comparison in L3.9c. -/
theorem tracking_label_sampler (d t : ℕ) (hd : 100 ≤ d)
    (ht : t ≤ d)
    (q : Fin t → Fin d → ℝ)
    (hq_nonneg : ∀ i y, 0 ≤ q i y)
    (hq_sum : ∀ i, ∑ y, q i y = 1)
    (hq_atom : ∀ i y, q i y ≤ 10 * (d : ℝ) ^ (-(0.95 : ℝ)))
    (hq_load : ∀ y, ∑ i, q i y = (t : ℝ) / d)
    (hprefix : ∀ (j : Fin t) y,
      |(∑ k : Fin t, if k.val < j.val then q k y else 0) -
        (j.val : ℝ) / d| ≤ 10 * (d : ℝ) ^ (-(1 / 8 : ℝ))) :
    ∃ Q : FinProb (Fin t → Fin d), LabelInjectionSupported Q ∧
      ∀ i y, |Q.pr (fun x => x i = y) - q i y| ≤ (d : ℝ) ^ (-(1 / 10 : ℝ)) := by
  classical
  letI : NeZero d := ⟨by omega⟩
  have hdR : (100 : ℝ) ≤ (d : ℝ) := by exact_mod_cast hd
  have hbase : 1 ≤ (d : ℝ) := by linarith
  have hsqrt : (10 : ℝ) ≤ Real.sqrt (d : ℝ) := by
    rw [Real.le_sqrt (by norm_num) (by positivity)]
    nlinarith
  have hhalf : (10 : ℝ) ≤ (d : ℝ) ^ (1 / (2 : ℝ)) := by
    simpa [Real.sqrt_eq_rpow] using hsqrt
  have hexp : (d : ℝ) ^ (1 / (2 : ℝ)) ≤ (d : ℝ) ^ (0.85 : ℝ) :=
    Real.rpow_le_rpow_of_exponent_le hbase (by norm_num)
  have hpow : (10 : ℝ) ≤ (d : ℝ) ^ (0.85 : ℝ) := hhalf.trans hexp
  have hneg : 10 * (d : ℝ) ^ (-(0.85 : ℝ)) ≤ 1 := by
    have hdiv : 10 / (d : ℝ) ^ (0.85 : ℝ) ≤ 1 := by
      rw [div_le_iff₀ (by positivity)]
      simpa using hpow
    simpa [Real.rpow_neg, div_eq_mul_inv] using hdiv
  have hsplit : (d : ℝ) ^ (-(0.95 : ℝ)) =
      (d : ℝ) ^ (-(0.1 : ℝ)) * (d : ℝ) ^ (-(0.85 : ℝ)) := by
    rw [← Real.rpow_add (by positivity)]
    norm_num
  have hatom_small : 10 * (d : ℝ) ^ (-(0.95 : ℝ)) ≤
      (d : ℝ) ^ (-(1 / 10 : ℝ)) := by
    rw [hsplit]
    calc
      10 * ((d : ℝ) ^ (-(0.1 : ℝ)) * (d : ℝ) ^ (-(0.85 : ℝ)))
          = (d : ℝ) ^ (-(0.1 : ℝ)) * (10 * (d : ℝ) ^ (-(0.85 : ℝ))) := by ring
      _ ≤ (d : ℝ) ^ (-(0.1 : ℝ)) * 1 :=
        mul_le_mul_of_nonneg_left hneg (Real.rpow_nonneg (by positivity) _)
      _ = (d : ℝ) ^ (-(1 / 10 : ℝ)) := by norm_num
  have huniform_small : (1 / (d : ℝ)) ≤ (d : ℝ) ^ (-(1 / 10 : ℝ)) := by
    have hexp' : (d : ℝ) ^ (-(1 : ℝ)) ≤ (d : ℝ) ^ (-(1 / 10 : ℝ)) :=
      Real.rpow_le_rpow_of_exponent_le hbase (by norm_num)
    simpa [Real.rpow_neg_eq_inv_rpow, Real.rpow_one] using hexp'
  let shift : Fin d → (Fin t → Fin d) := fun k i => i.castLE ht + k
  let Q : FinProb (Fin t → Fin d) := {
    w := fun x => ∑ k : Fin d, if shift k = x then (d : ℝ)⁻¹ else 0
    nonneg := by
      intro x
      apply Finset.sum_nonneg
      intro k hk
      split_ifs <;> positivity
    sum_eq_one := by
      calc
        ∑ x : Fin t → Fin d, (∑ k : Fin d, if shift k = x then (d : ℝ)⁻¹ else 0)
            = ∑ k : Fin d, ∑ x : Fin t → Fin d, if shift k = x then (d : ℝ)⁻¹ else 0 := by
                rw [Finset.sum_comm]
        _ = ∑ k : Fin d, (d : ℝ)⁻¹ := by
              simp [Finset.sum_ite_eq, Finset.mem_univ]
        _ = 1 := by
              simp [Fintype.card_fin, Nat.cast_ne_zero.mpr (by omega : d ≠ 0)]
  }
  refine ⟨Q, ?_, ?_⟩
  · intro x hx
    have hex : ∃ k : Fin d, shift k = x := by
      by_contra h
      push Not at h
      have hz : Q.w x = 0 := by simp [Q, h]
      exact hx hz
    obtain ⟨k, hk⟩ := hex
    rw [← hk]
    intro a b hab
    apply Fin.castLE_injective ht
    exact add_right_cancel hab
  · intro i y
    have hprob : Q.pr (fun x => x i = y) = (1 / (d : ℝ)) := by
      simp only [FinProb.pr, Q]
      calc
        (∑ x : Fin t → Fin d,
          if x i = y then ∑ k : Fin d, if shift k = x then (d : ℝ)⁻¹ else 0 else 0)
            = ∑ x : Fin t → Fin d, ∑ k : Fin d,
                if x i = y then (if shift k = x then (d : ℝ)⁻¹ else 0) else 0 := by
                  apply Finset.sum_congr rfl
                  intro x hx
                  by_cases hxy : x i = y <;> simp [hxy]
        _ = ∑ k : Fin d, ∑ x : Fin t → Fin d,
              if x i = y then (if shift k = x then (d : ℝ)⁻¹ else 0) else 0 := by
                rw [Finset.sum_comm]
        _ = ∑ k : Fin d, if (shift k) i = y then (d : ℝ)⁻¹ else 0 := by
              apply Finset.sum_congr rfl
              intro k hk
              calc
                (∑ x : Fin t → Fin d,
                  if x i = y then (if shift k = x then (d : ℝ)⁻¹ else 0) else 0)
                    = ∑ x : Fin t → Fin d,
                      if shift k = x then (if x i = y then (d : ℝ)⁻¹ else 0) else 0 := by
                        apply Finset.sum_congr rfl
                        intro x hx
                        by_cases hxy : x i = y <;> by_cases hxk : shift k = x <;>
                          simp [hxy, hxk]
                _ = if (shift k) i = y then (d : ℝ)⁻¹ else 0 := by
                      simp [Finset.sum_ite_eq, Finset.mem_univ]
        _ = (1 / (d : ℝ)) := by
              let k₀ : Fin d := y - i.castLE ht
              have hsol (k : Fin d) : i.castLE ht + k = y ↔ k = k₀ := by
                constructor
                · intro heq
                  calc
                    k = (i.castLE ht + k) - i.castLE ht := by abel
                    _ = y - i.castLE ht := by rw [heq]
                · intro heq
                  rw [heq]
                  simp [k₀]
              calc
                (∑ k : Fin d, if (shift k) i = y then (d : ℝ)⁻¹ else 0)
                    = ∑ k : Fin d, if k = k₀ then (d : ℝ)⁻¹ else 0 := by
                        apply Finset.sum_congr rfl
                        intro k hk
                        simp only [shift, hsol k]
                _ = (d : ℝ)⁻¹ := by simp
                _ = 1 / (d : ℝ) := by ring
    rw [hprob]
    have htarget : q i y ≤ (d : ℝ) ^ (-(1 / 10 : ℝ)) :=
      (hq_atom i y).trans hatom_small
    have hunif_nonneg : 0 ≤ (1 / (d : ℝ)) := by positivity
    rw [abs_le]
    constructor <;> nlinarith [hq_nonneg i y, hunif_nonneg, huniform_small, htarget]

/-- L3.9c (03:695–734): price-directed perturbations of the rows give injective label laws
whose joint probabilities have the required near-product upper bound and whose price is at
least the target price. This is the sampler estimate consumed by exact calibration. -/
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
  sorry

/-- L3.9d (03:736–768): abstract calibration by separation. If a compact convex set of
finite-dimensional marginal vectors has a member at least as good as the target in every linear
price, it contains the target. This form is independent of the sampler and is reusable in Section 16. -/
theorem calibration_by_separation {K : Type*} [Fintype K]
    (C : Set (K → ℝ)) (p : K → ℝ)
    (hcompact : IsCompact C) (hconvex : Convex ℝ C)
    (hprice : ∀ c : K → ℝ, ∃ q ∈ C, ∑ k, c k * p k ≤ ∑ k, c k * q k) :
    p ∈ C := by
  sorry

/-- The feasible marginal image is compact and convex: all constraints on the assignment law
are linear inequalities in a finite probability simplex. -/
theorem label_marginal_image_compact_convex {R : Type*} [Fintype R] [DecidableEq R]
    (d : ℕ) (q : R → Fin d → ℝ) :
    IsCompact (LabelMarginalImage d q) ∧ Convex ℝ (LabelMarginalImage d q) := by
  sorry

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
  sorry

end HypercubeRamsey
