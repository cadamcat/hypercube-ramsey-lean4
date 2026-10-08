import HypercubeRamsey.Framework.OneShot
import HypercubeRamsey.Framework.FinProbLemmas
import HypercubeRamsey.S03.ScatteredMoments
import HypercubeRamsey.S03.ClockSampling
import HypercubeRamsey.Tools.Concentration

/-!
# Section 10 clock transfer

Finite versions of the integration and success-event arguments at
`10-full-dimensional-cluster-patches.tex:283–294`.
-/

namespace HypercubeRamsey.Lane_sol_s10_1k

open Classical OAI.HypercubeRamsey
open scoped BigOperators

private theorem outcome_nonempty {Ω : Type*} [Fintype Ω] (P : FinProb Ω) :
    Nonempty Ω := by
  by_contra h
  have : IsEmpty Ω := ⟨fun ω => h ⟨ω⟩⟩
  have hs := P.sum_eq_one
  simp at hs

/-- Section 10 uses the clock sampler with no forbidden predicates and with
queries of at most `n²` odd labels (TeX 10:281–284). -/
theorem clock_injective_labels (C_g : ℝ) :
    ∃ A : ℝ, ∃ n₀ : ℕ, ∃ ε : ℕ → ℝ,
      Filter.Tendsto ε Filter.atTop (nhds 0) ∧
      ∀ n ≥ n₀, ∀ N : ℕ, Real.log N ≤ C_g * n →
        ∀ {R : Type} [Fintype R] [DecidableEq R] (p : R → FinProb (Fin N)),
          (∀ y, ∑ a, (p a).w y ≤ 1e-8) →
          (∀ a y, (p a).w y ≤ (n : ℝ) ^ (-A)) →
          ∃ J : FinProb (R → Fin N),
            (∀ ω, J.w ω ≠ 0 → Function.Injective ω) ∧
            (∀ (S : Finset R) (o : R → Fin N),
              (S.card : ℝ) ≤ (n : ℝ) ^ (2 : ℝ) →
                J.pr (fun ω => ∀ a ∈ S, ω a = o a) ≤
                  (1 + ε n) * ∏ a ∈ S, (p a).w (o a)) := by
  obtain ⟨A, P, n₀, ε, hε, hclock⟩ := clock_sampling 2 C_g (by norm_num)
  refine ⟨A, n₀, ε, hε, ?_⟩
  intro n hn N hN R _ _ p hcolumn hatom
  let bad : Fin 0 → (R → Fin N) → Prop := fun k => Fin.elim0 k
  let scope : Fin 0 → Finset R := fun k => Fin.elim0 k
  have hlabel (a : R) (y : Fin N) : labMarg (p a) id y = (p a).w y := by
    classical
    simp [labMarg]
  obtain ⟨J, hsupport, hquery⟩ := hclock n hn N hN
    (R := R) (K := Fin 0) (Ω := fun _ => Fin N) (fun _ => id) p bad scope
    (by simpa only [hlabel] using hcolumn)
    (by simpa only [hlabel] using hatom)
    (fun k => Fin.elim0 k) (fun k => Fin.elim0 k)
    (by intro a; simp)
    (fun k => Fin.elim0 k)
  exact ⟨J, fun ω hω => (hsupport ω hω).1, hquery⟩

/-- Cylinder domination implies expectation domination for every nonnegative
function of the queried outputs. No conditioning on a global success event is
introduced here. -/
theorem query_expect_le {R : Type*} [Fintype R] [DecidableEq R]
    {Ω : R → Type*} [∀ a, Fintype (Ω a)]
    (p : ∀ a, FinProb (Ω a)) (J : FinProb (∀ a, Ω a))
    (S : Finset R) (C : ℝ) (f : (∀ a, Ω a) → ℝ)
    (hf : ∀ ω, 0 ≤ f ω) (hdep : FinProb.DependsOn f S)
    (hquery : ∀ o : ∀ a, Ω a,
      J.pr (fun ω => ∀ a ∈ S, ω a = o a) ≤ C * ∏ a ∈ S, (p a).w (o a)) :
    J.expect f ≤ C * (FinProb.pi p).expect f := by
  classical
  let Rₛ := {a : R // a ∈ S}
  let restrict : (∀ a, Ω a) → (∀ a : Rₛ, Ω a.1) := fun ω a => ω a.1
  let ω₀ : ∀ a, Ω a := Classical.choice (outcome_nonempty (FinProb.pi p))
  let extend : (∀ a : Rₛ, Ω a.1) → (∀ a, Ω a) :=
    fun z a => if h : a ∈ S then z ⟨a, h⟩ else ω₀ a
  let g : (∀ a : Rₛ, Ω a.1) → ℝ := fun z => f (extend z)
  have hfg (ω : ∀ a, Ω a) : f ω = g (restrict ω) := by
    apply hdep
    intro a ha
    simp [restrict, extend, ha]
  have hiff (z : ∀ a : Rₛ, Ω a.1) (ω : ∀ a, Ω a) :
      restrict ω = z ↔ ∀ a ∈ S, ω a = extend z a := by
    constructor
    · intro hz a ha
      have h := congrFun hz ⟨a, ha⟩
      simpa [restrict, extend, ha] using h
    · intro hz
      funext a
      simpa [restrict, extend, a.2] using hz a.1 a.2
  let Jₛ := FinProb.map J restrict
  let pₛ := FinProb.pi (fun a : Rₛ => p a.1)
  have hatom (z : ∀ a : Rₛ, Ω a.1) : Jₛ.w z ≤ C * pₛ.w z := by
    have hweight : Jₛ.w z = J.pr (fun ω => ∀ a ∈ S, ω a = extend z a) := by
      simp only [Jₛ, FinProb.map, FinProb.pr]
      apply Finset.sum_congr rfl
      intro ω _
      split_ifs with h h' h''
      · rfl
      · exact (h' ((hiff z ω).mp h)).elim
      · exact (h ((hiff z ω).mpr h'')).elim
      · rfl
    rw [hweight]
    have hprod : (∏ a ∈ S, (p a).w (extend z a)) = pₛ.w z := by
      change (∏ a ∈ S, (p a).w (extend z a)) = ∏ a : Rₛ, (p a.1).w (z a)
      rw [← Finset.prod_attach S]
      change (∏ a ∈ S.attach, (p a.1).w (extend z a.1)) = _
      simp [extend, Rₛ, Finset.univ_eq_attach]
    simpa only [hprod] using hquery (extend z)
  have hJ : J.expect f = Jₛ.expect g := by
    rw [FinProb.map_expect]
    unfold FinProb.expect
    simp_rw [hfg]
  have hp : (FinProb.pi p).expect f = pₛ.expect g := by
    calc
      (FinProb.pi p).expect f =
          (FinProb.pi p).expect (fun ω => g (restrict ω)) := by
        unfold FinProb.expect
        simp_rw [hfg]
      _ = pₛ.expect g := FinProb.pi_marginal_expect p S g
  rw [hJ, hp]
  unfold FinProb.expect
  rw [Finset.mul_sum]
  apply Finset.sum_le_sum
  intro z _
  calc
    Jₛ.w z * g z ≤ (C * pₛ.w z) * g z :=
      mul_le_mul_of_nonneg_right (hatom z) (hf (extend z))
    _ = C * (pₛ.w z * g z) := by ring

/-- Keep the global history indicator during the clock comparison, then
drop it before averaging the independent reference rows. -/
theorem gated_query_expect_le {H R : Type*} [Fintype H]
    [Fintype R] [DecidableEq R] {Ω : R → Type*} [∀ a, Fintype (Ω a)]
    (P : FinProb H) (p : H → ∀ a, FinProb (Ω a))
    (J : H → FinProb (∀ a, Ω a)) (good : H → Prop)
    (S : Finset R) (C : ℝ) (hC : 0 ≤ C)
    (f : H → (∀ a, Ω a) → ℝ)
    (hf : ∀ h ω, 0 ≤ f h ω)
    (hdep : ∀ h, FinProb.DependsOn (f h) S)
    (hquery : ∀ h, good h → ∀ o : ∀ a, Ω a,
      (J h).pr (fun ω => ∀ a ∈ S, ω a = o a) ≤
        C * ∏ a ∈ S, (p h a).w (o a)) :
    (∑ h, P.w h * (if good h then (J h).expect (f h) else 0)) ≤
      C * ∑ h, P.w h * (FinProb.pi (p h)).expect (f h) := by
  classical
  rw [Finset.mul_sum]
  apply Finset.sum_le_sum
  intro h _
  have hlocal : (if good h then (J h).expect (f h) else 0) ≤
      C * (FinProb.pi (p h)).expect (f h) := by
    by_cases hh : good h
    · rw [ite_eq_left hh]
      exact query_expect_le (p h) (J h) S C (f h) (hf h) (hdep h) (hquery h hh)
    · rw [ite_eq_right hh]
      apply mul_nonneg hC
      exact Finset.sum_nonneg fun ω _ =>
        mul_nonneg ((FinProb.pi (p h)).nonneg ω) (hf h ω)
  calc
    P.w h * (if good h then (J h).expect (f h) else 0) ≤
        P.w h * (C * (FinProb.pi (p h)).expect (f h)) :=
      mul_le_mul_of_nonneg_left hlocal (P.nonneg h)
    _ = C * (P.w h * (FinProb.pi (p h)).expect (f h)) := by ring

/-- The preceding comparison with the cluster draw still inside the history.
The right side integrates the product reference law over the original cluster
kernel, after removing the nonlocal history and cluster-column restrictions. -/
theorem cluster_query_expect_le {H D R : Type*} [Fintype H] [Fintype D]
    [Fintype R] [DecidableEq R] {Ω : R → Type*} [∀ a, Fintype (Ω a)]
    (P : FinProb H) (K : H → FinProb D)
    (p : H → D → ∀ a, FinProb (Ω a))
    (J : H → D → FinProb (∀ a, Ω a)) (good : H → D → Prop)
    (S : Finset R) (C : ℝ) (hC : 0 ≤ C)
    (f : H → (∀ a, Ω a) → ℝ)
    (hf : ∀ h ω, 0 ≤ f h ω)
    (hdep : ∀ h, FinProb.DependsOn (f h) S)
    (hquery : ∀ h d, good h d → ∀ o : ∀ a, Ω a,
      (J h d).pr (fun ω => ∀ a ∈ S, ω a = o a) ≤
        C * ∏ a ∈ S, (p h d a).w (o a)) :
    (∑ h, P.w h * ∑ d, (K h).w d *
      (if good h d then (J h d).expect (f h) else 0)) ≤
      C * ∑ h, P.w h * ∑ d, (K h).w d *
        (FinProb.pi (p h d)).expect (f h) := by
  have h := gated_query_expect_le (FinProb.bind P K)
    (fun hd => p hd.1 hd.2) (fun hd => J hd.1 hd.2)
    (fun hd => good hd.1 hd.2) S C hC (fun hd => f hd.1)
    (fun hd => hf hd.1) (fun hd => hdep hd.1)
    (fun hd => hquery hd.1 hd.2)
  simpa only [FinProb.bind, Fintype.sum_prod_type, Finset.mul_sum, mul_assoc] using h

/-- Concentration of independent group contributions at a fixed column
(TeX 10:277–281). The exponent depends on the maximum group contribution,
rather than the number of groups. -/
theorem independent_group_column_tail {I : Type*} [Fintype I] [DecidableEq I]
    {Ω : I → Type*} [∀ i, Fintype (Ω i)]
    (P : ∀ i, FinProb (Ω i)) (X : ∀ i, Ω i → ℝ)
    (L m θ : ℝ) (hL : 0 < L)
    (hX : ∀ i ω, 0 ≤ X i ω ∧ X i ω ≤ L)
    (hmean : ∑ i, (P i).expect (X i) ≤ m) :
    (FinProb.pi P).pr (fun ω => θ ≤ ∑ i, X i (ω i)) ≤
      Real.exp (((Real.exp 1 - 1) * m - θ) / L) := by
  let Y : ∀ i, Ω i → ℝ := fun i ω => X i ω / L
  have hY (i : I) (ω : Ω i) : 0 ≤ Y i ω ∧ Y i ω ≤ 1 := by
    refine ⟨div_nonneg (hX i ω).1 hL.le, ?_⟩
    exact (div_le_one hL).mpr (hX i ω).2
  have hsumY (ω : ∀ i, Ω i) : (∑ i, Y i (ω i)) = (∑ i, X i (ω i)) / L :=
    (Finset.sum_div Finset.univ (fun i => X i (ω i)) L).symm
  have hevent : (fun ω : ∀ i, Ω i => θ ≤ ∑ i, X i (ω i)) =
      (fun ω : ∀ i, Ω i => θ / L ≤ ∑ i, Y i (ω i)) := by
    funext ω
    rw [hsumY]
    exact propext (div_le_div_iff_of_pos_right hL).symm
  have hEY (i : I) : (P i).expect (Y i) = (P i).expect (X i) / L := by
    unfold FinProb.expect
    change (∑ ω, (P i).w ω * (X i ω / L)) = (∑ ω, (P i).w ω * X i ω) / L
    rw [Finset.sum_div]
    apply Finset.sum_congr rfl
    intro ω _
    ring
  have hμ : (∑ i, (P i).expect (Y i)) = (∑ i, (P i).expect (X i)) / L := by
    simp_rw [hEY]
    exact (Finset.sum_div _ _ _).symm
  have he : 0 ≤ Real.exp 1 - 1 := by
    have h := Real.one_le_exp_iff.mpr (by norm_num : (0 : ℝ) ≤ 1)
    linarith
  rw [hevent]
  calc
    (FinProb.pi P).pr (fun ω => θ / L ≤ ∑ i, Y i (ω i)) ≤
        Real.exp (-1 * (θ / L)) *
          (FinProb.pi P).expect (fun ω => Real.exp (1 * ∑ i, Y i (ω i))) :=
      FinProb.pr_exp_markov (FinProb.pi P) (fun ω => ∑ i, Y i (ω i))
        1 (θ / L) (by norm_num)
    _ ≤ Real.exp (-1 * (θ / L)) *
        Real.exp ((Real.exp 1 - 1) * ∑ i, (P i).expect (Y i)) :=
      mul_le_mul_of_nonneg_left
        (FinProb.expect_exp_sum_le_of_mem_Icc P Y hY 1) (Real.exp_nonneg _)
    _ = Real.exp (((Real.exp 1 - 1) * (∑ i, (P i).expect (X i)) - θ) / L) := by
      rw [← Real.exp_add, hμ]
      congr 1
      ring
    _ ≤ Real.exp (((Real.exp 1 - 1) * m - θ) / L) := by
      apply Real.exp_le_exp.mpr
      apply div_le_div_of_nonneg_right _ hL.le
      exact sub_le_sub_right (mul_le_mul_of_nonneg_left hmean he) θ

/-- A small column mean converts the preceding estimate to the exponentially
small tail used before clock sampling. -/
theorem independent_group_column_tail_small_mean {I : Type*}
    [Fintype I] [DecidableEq I] {Ω : I → Type*} [∀ i, Fintype (Ω i)]
    (P : ∀ i, FinProb (Ω i)) (X : ∀ i, Ω i → ℝ)
    (L m θ : ℝ) (hL : 0 < L)
    (hX : ∀ i ω, 0 ≤ X i ω ∧ X i ω ≤ L)
    (hmean : ∑ i, (P i).expect (X i) ≤ m)
    (hsmall : (Real.exp 1 - 1) * m ≤ θ / 2) :
    (FinProb.pi P).pr (fun ω => θ ≤ ∑ i, X i (ω i)) ≤
      Real.exp (-θ / (2 * L)) := by
  apply (independent_group_column_tail P X L m θ hL hX hmean).trans
  apply Real.exp_le_exp.mpr
  calc
    ((Real.exp 1 - 1) * m - θ) / L ≤ (θ / 2 - θ) / L :=
      div_le_div_of_nonneg_right (sub_le_sub_right hsmall θ) hL.le
    _ = -θ / (2 * L) := by ring

/-- An `n`th moment bound on retained outcomes gives a tail bound without
renormalizing the retained law. -/
theorem retained_moment_tail {Ω : Type*} [Fintype Ω]
    (P : FinProb Ω) (good : Finset Ω) (Z : Ω → ℝ)
    (hZ : ∀ ω, 0 ≤ Z ω) (t M : ℝ) (ht : 0 < t) (n : ℕ)
    (hmoment : ∑ ω ∈ good, P.w ω * Z ω ^ n ≤ M) :
    P.pr (fun ω => ω ∈ good ∧ t < Z ω) ≤ M / t ^ n := by
  classical
  have hpoint : t ^ n * P.pr (fun ω => ω ∈ good ∧ t < Z ω) ≤ M := by
    calc
      t ^ n * P.pr (fun ω => ω ∈ good ∧ t < Z ω) =
          ∑ ω ∈ good, (if t < Z ω then P.w ω * t ^ n else 0) := by
        simp only [FinProb.pr, Finset.mul_sum, mul_ite, mul_zero, ite_and]
        rw [← Finset.sum_filter (s := Finset.univ) (p := fun ω => ω ∈ good)]
        simp [mul_comm]
      _ ≤ ∑ ω ∈ good, P.w ω * Z ω ^ n := by
        apply Finset.sum_le_sum
        intro ω _
        by_cases hω : t < Z ω
        · rw [ite_eq_left hω]
          exact mul_le_mul_of_nonneg_left (pow_le_pow_left₀ ht.le hω.le n) (P.nonneg ω)
        · rw [ite_eq_right hω]
          exact mul_nonneg (P.nonneg ω) (pow_nonneg (hZ ω) n)
      _ ≤ M := hmoment
  exact (le_div_iff₀ (pow_pos ht n)).mpr (by simpa [mul_comm] using hpoint)

/-- Scattered moments applied to the unconditioned law with its retained
success set. This is the column estimate in TeX 10:288–292. -/
theorem scattered_retained_tail {Ω U : Type*} [Fintype Ω]
    [Fintype U] [DecidableEq U] [Nonempty U]
    (P : FinProb Ω) (good : Finset Ω) (Z : U → Ω → ℝ)
    (hZ : ∀ v ω, 0 ≤ Z v ω) (L : ℝ) (hL : 0 ≤ L)
    (hcap : ∀ v ω, ω ∈ good → Z v ω ≤ L)
    (near : U → Finset U) (hself : ∀ v, v ∈ near v)
    (f : ℝ) (hnear : ∀ v, ((near v).card : ℝ) ≤ f * Fintype.card U)
    (n : ℕ) (K : ℝ) (hK : 1 ≤ K) (d : U → ℝ) (hd : ∀ v, 0 ≤ d v)
    (hjoint : ∀ m, m ≤ n → ∀ s : Fin m → U,
      (∀ i j : Fin m, j < i → s i ∉ near (s j)) →
        ∑ ω ∈ good, P.w ω * ∏ i, Z (s i) ω ≤ K ^ m * ∏ i, d (s i))
    (t : ℝ) (ht : 0 < t) :
    P.pr (fun ω => ω ∈ good ∧ t <
      (Fintype.card U : ℝ)⁻¹ * ∑ v, Z v ω) ≤
      (K ^ n * ((Fintype.card U : ℝ)⁻¹ * ∑ v, d v + n * f * L) ^ n) / t ^ n := by
  exact retained_moment_tail P good
    (fun ω => (Fintype.card U : ℝ)⁻¹ * ∑ v, Z v ω)
    (fun ω => mul_nonneg (by positivity) (Finset.sum_nonneg fun v _ => hZ v ω))
    t _ ht n
    (scattered_moments P.w P.nonneg good Z hZ L hL hcap near hself f hnear
      n K hK d hd hjoint)

private theorem pr_exists_le_sum {Ω I : Type*} [Fintype Ω] [Fintype I]
    (P : FinProb Ω) (bad : I → Ω → Prop) :
    P.pr (fun ω => ∃ i, bad i ω) ≤ ∑ i, P.pr (bad i) := by
  classical
  unfold FinProb.pr
  rw [Finset.sum_comm]
  apply Finset.sum_le_sum
  intro ω _
  by_cases hω : ∃ i, bad i ω
  · rw [ite_eq_left hω]
    obtain ⟨i, hi⟩ := hω
    calc
      P.w ω = (if bad i ω then P.w ω else 0) := by rw [ite_eq_left hi]
      _ ≤ ∑ j, if bad j ω then P.w ω else 0 :=
        Finset.single_le_sum (f := fun j => if bad j ω then P.w ω else 0)
          (fun j _ => by split_ifs <;> simp [P.nonneg ω])
          (Finset.mem_univ i)
  · rw [ite_eq_right hω]
    exact Finset.sum_nonneg fun i _ => by split_ifs <;> simp [P.nonneg ω]

private theorem pr_mono {Ω : Type*} [Fintype Ω] (P : FinProb Ω)
    {A B : Ω → Prop} (h : ∀ ω, A ω → B ω) : P.pr A ≤ P.pr B := by
  classical
  unfold FinProb.pr
  apply Finset.sum_le_sum
  intro ω _
  by_cases hA : A ω
  · simp [hA, h ω hA]
  · simp [hA]
    split_ifs <;> simp [P.nonneg ω]

private theorem pr_compl {Ω : Type*} [Fintype Ω] (P : FinProb Ω) (A : Ω → Prop) :
    P.pr A + P.pr (fun ω => ¬ A ω) = 1 := by
  classical
  rw [FinProb.pr, FinProb.pr, ← Finset.sum_add_distrib]
  calc
    _ = ∑ ω, P.w ω := by
      apply Finset.sum_congr rfl
      intro ω _
      by_cases hω : A ω <;> simp [hω]
    _ = 1 := P.sum_eq_one

/-- Intersect the entering successes with all predictive tests and all column
tests. Their failure bounds remain under the original law. -/
theorem simultaneous_success {Ω A X : Type*}
    [Fintype Ω] [Fintype A] [Fintype X]
    (P : FinProb Ω) (good : Ω → Prop)
    (rowGood : A → Ω → Prop) (columnGood : X → Ω → Prop)
    (ε₀ ε₁ ε₂ : ℝ)
    (henter : P.pr (fun ω => ¬ good ω) ≤ ε₀)
    (hrow : ∀ a, P.pr (fun ω => good ω ∧ ¬ rowGood a ω) ≤ ε₁)
    (hcolumn : ∀ x, P.pr (fun ω => good ω ∧ ¬ columnGood x ω) ≤ ε₂)
    (hbudget : ε₀ + Fintype.card A * ε₁ + Fintype.card X * ε₂ < 1) :
    ∃ ω, P.w ω ≠ 0 ∧ good ω ∧ (∀ a, rowGood a ω) ∧ ∀ x, columnGood x ω := by
  classical
  let success := fun ω => good ω ∧ (∀ a, rowGood a ω) ∧ ∀ x, columnGood x ω
  let badRow := fun ω => ∃ a, good ω ∧ ¬ rowGood a ω
  let badColumn := fun ω => ∃ x, good ω ∧ ¬ columnGood x ω
  have hbad : P.pr (fun ω => ¬ success ω) ≤
      ε₀ + Fintype.card A * ε₁ + Fintype.card X * ε₂ := by
    have hsub : ∀ ω, ¬ success ω → ¬ good ω ∨ badRow ω ∨ badColumn ω := by
      intro ω hω
      by_cases hg : good ω
      · right
        by_cases hr : ∀ a, rowGood a ω
        · right
          have hc : ¬ ∀ x, columnGood x ω := fun hc => hω ⟨hg, hr, hc⟩
          obtain ⟨x, hx⟩ := not_forall.mp hc
          exact ⟨x, hg, hx⟩
        · left
          obtain ⟨a, ha⟩ := not_forall.mp hr
          exact ⟨a, hg, ha⟩
      · exact Or.inl hg
    have hr : P.pr badRow ≤ Fintype.card A * ε₁ := by
      calc
        P.pr badRow ≤ ∑ a, P.pr (fun ω => good ω ∧ ¬ rowGood a ω) :=
          pr_exists_le_sum P _
        _ ≤ ∑ _a : A, ε₁ := Finset.sum_le_sum fun a _ => hrow a
        _ = Fintype.card A * ε₁ := by simp
    have hc : P.pr badColumn ≤ Fintype.card X * ε₂ := by
      calc
        P.pr badColumn ≤ ∑ x, P.pr (fun ω => good ω ∧ ¬ columnGood x ω) :=
          pr_exists_le_sum P _
        _ ≤ ∑ _x : X, ε₂ := Finset.sum_le_sum fun x _ => hcolumn x
        _ = Fintype.card X * ε₂ := by simp
    calc
      P.pr (fun ω => ¬ success ω) ≤
          P.pr (fun ω => ¬ good ω ∨ badRow ω ∨ badColumn ω) := pr_mono P hsub
      _ ≤ P.pr (fun ω => ¬ good ω) + (P.pr badRow + P.pr badColumn) :=
        (FinProb.pr_union P _ _).trans
          (add_le_add le_rfl (FinProb.pr_union P badRow badColumn))
      _ ≤ ε₀ + (Fintype.card A * ε₁ + Fintype.card X * ε₂) :=
        add_le_add henter (add_le_add hr hc)
      _ = _ := by ring
  have hpos : 0 < P.pr success := by
    have hc := pr_compl P success
    linarith
  have hex : ∃ ω, P.w ω ≠ 0 ∧ success ω := by
    by_contra h
    have hz : P.pr success = 0 := by
      unfold FinProb.pr
      apply Finset.sum_eq_zero
      intro ω _
      by_cases hs : success ω
      · rw [ite_eq_left hs]
        by_contra hn
        exact h ⟨ω, hn, hs⟩
      · rw [ite_eq_right hs]
    linarith
  obtain ⟨ω, hω, hs⟩ := hex
  exact ⟨ω, hω, hs⟩

/-- The outputs and quantitative estimates needed after the prehistory and
cluster construction. `column_moment` is measured under the original law,
retaining `good`; it does not assert a passing column load. -/
structure RowExperiment (n N : ℕ) (E : Fin N → Fin N → Prop) (G : Colour) where
  Outcome : Type
  [fin : Fintype Outcome]
  law : FinProb Outcome
  good : Finset Outcome
  predictive : {v : CubeVertex n // IsEvenRole v} → Outcome → Prop
  odd : Outcome → {v : CubeVertex n // ¬ IsEvenRole v} → Fin N
  row : Outcome → {v : CubeVertex n // IsEvenRole v} → Fin N → ℝ
  odd_injective : ∀ ω, law.w ω ≠ 0 → ω ∈ good → Function.Injective (odd ω)
  row_nonnegative : ∀ ω a x, 0 ≤ row ω a x
  row_sum : ∀ ω a, ω ∈ good → predictive a ω → ∑ x, row ω a x = 1
  common_neighbor : ∀ ω a, ω ∈ good → predictive a ω →
    ∀ x, row ω a x ≠ 0 → ∀ b : {v : CubeVertex n // ¬ IsEvenRole v},
      (cube n).Adj a.1 b.1 → Hits E G x (odd ω b)
  ε_enter : ℝ
  ε_predictive : ℝ
  moment : ℝ
  entering_failure : law.pr (fun ω => ω ∉ good) ≤ ε_enter
  predictive_failure : ∀ a, law.pr (fun ω => ω ∈ good ∧ ¬ predictive a ω) ≤ ε_predictive
  column_moment : ∀ x, ∑ ω ∈ good, law.w ω * (∑ a, row ω a x) ^ n ≤ moment
  failure_budget : ε_enter +
    Fintype.card {v : CubeVertex n // IsEvenRole v} * ε_predictive + N * moment < 1

attribute [instance] RowExperiment.fin

/-- The final realization in TeX 10:294. Predictive row normalization and
support, clock injectivity, and the moment column test hold at one common
positive-weight outcome. -/
theorem RowExperiment.realization {n N : ℕ} {E : Fin N → Fin N → Prop} {G : Colour}
    (D : RowExperiment n N E G) :
    ∃ ω, D.law.w ω ≠ 0 ∧
      Function.Injective (D.odd ω) ∧
      (∀ a x, 0 ≤ D.row ω a x) ∧
      (∀ a, ∑ x, D.row ω a x = 1) ∧
      (∀ a x, D.row ω a x ≠ 0 → ∀ b : {v : CubeVertex n // ¬ IsEvenRole v},
        (cube n).Adj a.1 b.1 → Hits E G x (D.odd ω b)) ∧
      ∀ x, ∑ a, D.row ω a x ≤ 1 := by
  have hcolumn (x : Fin N) :
      D.law.pr (fun ω => ω ∈ D.good ∧ ¬ (∑ a, D.row ω a x ≤ 1)) ≤ D.moment := by
    have h := retained_moment_tail D.law D.good (fun ω => ∑ a, D.row ω a x)
      (fun ω => Finset.sum_nonneg fun a _ => D.row_nonnegative ω a x)
      1 D.moment (by norm_num) n (D.column_moment x)
    simpa only [not_le, one_pow, div_one] using h
  obtain ⟨ω, hω, hg, hp, hc⟩ := simultaneous_success D.law
    (fun ω => ω ∈ D.good) D.predictive (fun x ω => ∑ a, D.row ω a x ≤ 1)
    D.ε_enter D.ε_predictive D.moment D.entering_failure D.predictive_failure
    hcolumn (by simpa using D.failure_budget)
  exact ⟨ω, hω, D.odd_injective ω hω hg, D.row_nonnegative ω,
    fun a => D.row_sum ω a hg (hp a),
    fun a => D.common_neighbor ω a hg (hp a), hc⟩

end HypercubeRamsey.Lane_sol_s10_1k
