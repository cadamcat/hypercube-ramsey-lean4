import HypercubeRamsey.S03.Injection.Comparison

/-!
Lemma 3.9 assemblies and calibration. Concrete sequential/forcing processes and the
Steps 2–3 estimates are in `Sampler` and `Comparison`. The final export and the price
witness have no local placeholder; analytic nodes remain assigned proof obligations.
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
  sorry

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
  sorry

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
  sorry

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
  sorry

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
  sorry

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
