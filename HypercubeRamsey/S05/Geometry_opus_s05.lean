import HypercubeRamsey.S05.Defs

/-!
# Lane opus-s05-geo: sub-lemmas for the S05 geometry/parameter targets

* `common_point_of_price`: the separation step of L5.1g (05:574–581), from Sion's minimax theorem.
  Price feasibility over a compact convex set of laws, with continuous convex costs, gives one law
  meeting every cost at once.
* `excessCost`, `excessSum`: the scalar log-excess cost `r ↦ r · log⁺(r / a)` of `highDeletionCost5`,
  rewritten on `r ≥ 0` as a continuous function that is convex on `[0, ∞)`.
-/

set_option linter.deprecated false

namespace HypercubeRamsey.Lane_opus_s05_geo

open scoped BigOperators

/-- L5.1g separation step (05:574–581): if every price vector on the references admits a point of the
compact convex set `K` whose price-weighted cost is nonpositive, then one point of `K` has every cost
nonpositive.  Proof: Sion's minimax theorem for `(x, p) ↦ ∑ p_c f_c(x)` on `K × Δ(Ref)`. -/
theorem common_point_of_price {E Ref : Type*} [TopologicalSpace E] [AddCommGroup E] [Module ℝ E]
    [IsTopologicalAddGroup E] [ContinuousSMul ℝ E] [Fintype Ref] [Nonempty Ref]
    {K : Set E} (hne : K.Nonempty) (hcv : Convex ℝ K) (hK : IsCompact K)
    (f : Ref → E → ℝ) (hcont : ∀ c, ContinuousOn (f c) K) (hconv : ∀ c, ConvexOn ℝ K (f c))
    (hprice : ∀ p : Ref → ℝ, (∀ c, 0 ≤ p c) → ∑ c, p c = 1 →
      ∃ x ∈ K, ∑ c, p c * f c x ≤ 0) :
    ∃ x ∈ K, ∀ c, f c x ≤ 0 := by
  classical
  let Y : Set (Ref → ℝ) := stdSimplex ℝ Ref
  let g : E → (Ref → ℝ) → ℝ := fun x p => ∑ c, p c * f c x
  have neY : Y.Nonempty := ⟨Pi.single (Classical.arbitrary Ref) 1, single_mem_stdSimplex ℝ _⟩
  have kY : IsCompact Y :=
    IsCompact.of_isClosed_subset isCompact_Icc (isClosed_stdSimplex ℝ Ref)
      (stdSimplex_subset_Icc ℝ)
  have cY : Convex ℝ Y := convex_stdSimplex ℝ Ref
  have hfy : ∀ p ∈ Y, LowerSemicontinuousOn (fun x => g x p) K := by
    intro p _
    apply ContinuousOn.lowerSemicontinuousOn
    exact continuousOn_finset_sum _ (fun c _ => continuousOn_const.mul (hcont c))
  have hfy' : ∀ p ∈ Y, QuasiconvexOn ℝ K (fun x => g x p) := by
    intro p hp
    apply ConvexOn.quasiconvexOn
    have key : ∀ S : Finset Ref, ConvexOn ℝ K (fun x => ∑ c ∈ S, p c * f c x) := by
      intro S
      induction S using Finset.induction_on with
      | empty => simpa using (convexOn_const (0 : ℝ) hcv)
      | insert c S hc ih =>
        simp only [Finset.sum_insert hc]
        exact (ConvexOn.smul (hp.1 c) (hconv c)).add ih
    exact key Finset.univ
  have hfx : ∀ x ∈ K, UpperSemicontinuousOn (fun p => g x p) Y := by
    intro x _
    apply ContinuousOn.upperSemicontinuousOn
    exact (continuous_finset_sum _
      (fun c _ => (continuous_apply c).mul continuous_const)).continuousOn
  have hfx' : ∀ x ∈ K, QuasiconcaveOn ℝ Y (fun p => g x p) := by
    intro x _
    apply ConcaveOn.quasiconcaveOn
    refine ⟨cY, fun p _ q _ a b _ _ _ => le_of_eq ?_⟩
    simp only [g, Pi.add_apply, Pi.smul_apply, smul_eq_mul, add_mul, Finset.sum_add_distrib,
      Finset.mul_sum, mul_assoc]
  obtain ⟨a, ha, b, hb, hsad⟩ :=
    Sion.exists_isSaddlePointOn (f := g) hne hcv hK hfy hfy' cY neY kY hfx hfx'
  refine ⟨a, ha, fun c => ?_⟩
  obtain ⟨x, hx, hxb⟩ := hprice b hb.1 hb.2
  have h1 := hsad x hx (Pi.single c 1) (single_mem_stdSimplex ℝ c)
  have hga : g a (Pi.single c 1) = f c a := by
    simp [g, Pi.single_apply]
  have hgx : g x b ≤ 0 := hxb
  linarith

/-- The scalar log-excess cost on `r ≥ 0`: `0` at a null reference weight, otherwise
`max 0 (r log r - r log a)`. -/
noncomputable def excessCost (a r : ℝ) : ℝ :=
  if a = 0 then 0 else max 0 (r * Real.log r - r * Real.log a)

/-- On `r ≥ 0`, the deletion-cost summand `r · max 0 (log (r / a))` equals `excessCost a r`. -/
theorem excessCost_eq {a r : ℝ} (hr : 0 ≤ r) :
    r * max 0 (Real.log (r / a)) = excessCost a r := by
  unfold excessCost
  split_ifs with ha
  · simp [ha]
  · rcases hr.eq_or_lt with h | h
    · subst h
      simp
    · rw [Real.log_div h.ne' ha, mul_max_of_nonneg _ _ hr, mul_zero, mul_sub]

theorem excessCost_continuous (a : ℝ) : Continuous (excessCost a) := by
  unfold excessCost
  by_cases ha : a = 0
  · simp only [ha, if_true]
    exact continuous_const
  · simp only [ha, if_false]
    exact continuous_const.max
      (Real.continuous_mul_log.sub (continuous_id.mul continuous_const))

theorem excessCost_convexOn (a : ℝ) : ConvexOn ℝ (Set.Ici 0) (excessCost a) := by
  by_cases ha : a = 0
  · have h : excessCost a = fun _ => (0 : ℝ) := by
      funext r
      simp [excessCost, ha]
    rw [h]
    exact convexOn_const 0 (convex_Ici 0)
  · have hlin : ConcaveOn ℝ (Set.Ici (0 : ℝ)) (fun r => r * Real.log a) := by
      refine ⟨convex_Ici 0, fun x _ y _ p q _ _ _ => le_of_eq ?_⟩
      simp only [smul_eq_mul]
      ring
    have h1 : ConvexOn ℝ (Set.Ici (0 : ℝ)) (fun r => r * Real.log r - r * Real.log a) :=
      Real.convexOn_mul_log.sub hlin
    have h2 := (convexOn_const (0 : ℝ) (convex_Ici (0 : ℝ))).sup h1
    have h : excessCost a = (fun _ => (0 : ℝ)) ⊔ (fun r => r * Real.log r - r * Real.log a) := by
      funext r
      simp [excessCost, ha]
    rw [h]
    exact h2

/-- The total log-excess cost of a weight vector against reference weights `a`. -/
noncomputable def excessSum {ι : Type*} [Fintype ι] (a w : ι → ℝ) : ℝ :=
  ∑ i, excessCost (a i) (w i)

theorem excessSum_continuous {ι : Type*} [Fintype ι] (a : ι → ℝ) : Continuous (excessSum a) :=
  continuous_finset_sum _ (fun i _ => (excessCost_continuous (a i)).comp (continuous_apply i))

theorem convex_nonnegOrthant {ι : Type*} : Convex ℝ {w : ι → ℝ | ∀ i, 0 ≤ w i} := by
  intro x hx y hy a b ha hb _ i
  simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
  exact add_nonneg (mul_nonneg ha (hx i)) (mul_nonneg hb (hy i))

theorem excessSum_convexOn {ι : Type*} [Fintype ι] (a : ι → ℝ) :
    ConvexOn ℝ {w : ι → ℝ | ∀ i, 0 ≤ w i} (excessSum a) := by
  classical
  have hcv := convex_nonnegOrthant (ι := ι)
  have key : ∀ S : Finset ι, ConvexOn ℝ {w : ι → ℝ | ∀ i, 0 ≤ w i}
      (fun w => ∑ i ∈ S, excessCost (a i) (w i)) := by
    intro S
    induction S using Finset.induction_on with
    | empty => simpa using (convexOn_const (0 : ℝ) hcv)
    | insert i S hi ih =>
      simp only [Finset.sum_insert hi]
      have hi' : ConvexOn ℝ {w : ι → ℝ | ∀ i, 0 ≤ w i} (fun w => excessCost (a i) (w i)) :=
        ((excessCost_convexOn (a i)).comp_linearMap
          (LinearMap.proj (R := ℝ) (φ := fun _ : ι => ℝ) i)).subset
          (fun w hw => by simpa using hw i) hcv
      exact hi'.add ih
  exact key Finset.univ

end HypercubeRamsey.Lane_opus_s05_geo
