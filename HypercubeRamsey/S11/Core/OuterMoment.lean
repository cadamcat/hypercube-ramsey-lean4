import HypercubeRamsey.S11.Core.Local
import HypercubeRamsey.S11.Needs

/-! L11.3's finite interaction variables, moment estimates, and tail assembly. -/

namespace HypercubeRamsey.S11.Core

open HypercubeRamsey
open Classical
open scoped BigOperators

/-- No large correlation clique occurs in the retained label set. -/
def NoCorrelationClique {n N : ℕ} (E : Fin N → Fin N → Prop) (G : Colour)
    (π : Law N) (S : Finset (Fin N)) (δ : ℝ) : Prop :=
  ∀ C : Finset (Fin N), C ⊆ S →
    C.card = Nat.ceil (Real.exp ((n : ℝ) ^ (1 / 100 : ℝ))) →
    ∃ x ∈ C, ∃ y ∈ C, x ≠ y ∧ signedCorrelation E G π x y ≤ 8 * (n : ℝ) ^ (-δ)

/-- All one-shot hypotheses for L11.3, including support, cap, degree and discrepancy conditions. -/
structure OuterSetup {n N : ℕ} (E : Fin N → Fin N → Prop) (X Y : Finset (Fin N))
    (δ x₀ K : ℝ) where
  G : Colour
  π : Law N
  σ : Law N
  S : Finset (Fin N)
  hδ : 0 < δ
  hδ' : δ < 1 / 20000
  hx₀ : 0 < x₀
  hx₀' : x₀ < 1
  hK : 0 < K
  hHost : 2 ^ n ≤ N
  π_supported : π.SupportedIn Y
  π_cap : Law.CapLE π K
  σ_supported : σ.SupportedIn S
  S_subset : S ⊆ X
  σ_cap : Law.CapLE σ (Real.exp ((Real.log 2 - sliceSurplus n / 2) * innerDimension n))
  degree_good : ∀ (x : Fin N), x ∈ S →
    |signedMean (N := N) E G π x| ≤ 4 * signedBiasScale n
  no_clique : NoCorrelationClique (n := n) E G π S δ
  discrepancy : DiscOne E X Y
    ((n : ℝ) ^ (1 - δ / 16)) ((n : ℝ) ^ x₀) (signedBiasScale n)

/-- Product probability of an outer word under the independent law `π`. -/
noncomputable def outerTupleWeight {N d : ℕ} (π : Law N) (Y : Fin d → Fin N) : ℝ :=
  ∏ j, π.w (Y j)

/-- The exact failure probability in L11.3. -/
noncomputable def outerFailureMass {n N : ℕ} {E : Fin N → Fin N → Prop}
    {X Y : Finset (Fin N)} {δ x₀ K : ℝ} (O : OuterSetup (n := n) E X Y δ x₀ K) : ℝ := by
  classical
  exact ∑ Z : Fin (outerDimension n) → Fin N,
    outerTupleWeight O.π Z * (if outerMass E O.G O.π O.σ Z < 1 / 2 then 1 else 0)

/-- Product weight of a tuple of first-side labels drawn from `σ`. -/
noncomputable def sigmaTupleWeight {N u : ℕ} (σ : Law N) (x : Fin u → Fin N) : ℝ :=
  ∏ j, σ.w (x j)

/-- Maximum absolute interaction of size at least two in an `u`-tuple. -/
noncomputable def interactionEnvelope {N u : ℕ} (E : Fin N → Fin N → Prop) (G : Colour)
    (π : Law N) (x : Fin u → Fin N) : ℝ := by
  classical
  exact (Finset.univ : Finset (Finset (Fin u))).sup' ⟨∅, Finset.mem_univ _⟩ fun J =>
    if 2 ≤ J.card then |interaction E G π J x| else 0

/-- The alternating interaction expansion `Φ_u` from L11.3f. -/
noncomputable def centeredExpansion {n N u : ℕ} {E : Fin N → Fin N → Prop}
    {X Y : Finset (Fin N)} {δ x₀ K : ℝ} (O : OuterSetup (n := n) E X Y δ x₀ K)
    (x : Fin u → Fin N) : ℝ :=
  ∑ I : Finset (Fin u), (-1 : ℝ) ^ (u - I.card) *
    (∑ y, O.π.w y * ∏ j ∈ I, (1 + likelihoodFactor E O.G O.π (x j) y)) ^
      outerDimension n

/-- The `u`th absolute centered moment of the outer mass. -/
noncomputable def outerMoment {n N u : ℕ} {E : Fin N → Fin N → Prop}
    {X Y : Finset (Fin N)} {δ x₀ K : ℝ} (O : OuterSetup (n := n) E X Y δ x₀ K) : ℝ := by
  classical
  exact ∑ Z : Fin (outerDimension n) → Fin N,
    outerTupleWeight O.π Z * |outerMass E O.G O.π O.σ Z - 1| ^ u

/-- The contribution from tuples whose interactions are at most `n^(-1-.03)`. -/
noncomputable def smallInteractionContribution {n N u : ℕ}
    {E : Fin N → Fin N → Prop} {X Y : Finset (Fin N)} {δ x₀ K : ℝ}
    (O : OuterSetup (n := n) E X Y δ x₀ K) : ℝ := by
  classical
  exact ∑ x : Fin u → Fin N,
    sigmaTupleWeight O.σ x *
      (if interactionEnvelope E O.G O.π x ≤ (n : ℝ) ^ (-1 - (3 : ℝ) / 100)
       then |centeredExpansion O x| else 0)

/-- The contribution from tuples with larger interactions. -/
noncomputable def largeInteractionContribution {n N u : ℕ}
    {E : Fin N → Fin N → Prop} {X Y : Finset (Fin N)} {δ x₀ K : ℝ}
    (O : OuterSetup (n := n) E X Y δ x₀ K) : ℝ := by
  classical
  exact ∑ x : Fin u → Fin N,
    sigmaTupleWeight O.σ x *
      (if (n : ℝ) ^ (-1 - (3 : ℝ) / 100) < interactionEnvelope E O.G O.π x
       then |centeredExpansion O x| else 0)

/-- L11.3c–f output, including the alternating-sum identity and the small-interaction estimate. -/
structure SmallMomentData {n N : ℕ} {E : Fin N → Fin N → Prop} {X Y : Finset (Fin N)}
    {δ x₀ K P : ℝ} (O : OuterSetup (n := n) E X Y δ x₀ K) where
  u : ℕ
  u_even : Even u
  u_pos : 0 < u
  good_bound : smallInteractionContribution (u := u) O ≤
    (2 : ℝ) ^ (-(u + 1 : ℤ)) * (n : ℝ) ^ (-P)
  expansion_bound : outerMoment (u := u) O ≤
    smallInteractionContribution (u := u) O + largeInteractionContribution (u := u) O

/-- The uniform one-free-label interaction estimate. -/
def OneFreeEstimate {n N : ℕ} {E : Fin N → Fin N → Prop} {X Y : Finset (Fin N)}
    {δ x₀ K : ℝ} (O : OuterSetup (n := n) E X Y δ x₀ K) : Prop :=
  ∀ (u : ℕ) (J : Finset (Fin u)) (j : Fin u) (hj : j ∈ J)
    (base : Fin u → Fin N),
    (∑ x, O.σ.w x *
      (if (8 : ℝ) ^ u * signedBiasScale n <
          |interaction E O.G O.π J (Function.update base j x)| then 1 else 0)) ≤
      2 * Real.exp (-((n : ℝ) ^ (1 - δ / 16) / 2))

/-- The uniform two-free-label interaction estimate. -/
def TwoFreeEstimate {n N : ℕ} {E : Fin N → Fin N → Prop} {X Y : Finset (Fin N)}
    {δ x₀ K : ℝ} (O : OuterSetup (n := n) E X Y δ x₀ K) : Prop :=
  ∀ (u : ℕ) (J : Finset (Fin u)) (j j' : Fin u) (hjj : j ≠ j')
    (hj : j ∈ J) (hj' : j' ∈ J) (base : Fin u → Fin N),
    (∑ x, ∑ z, O.σ.w x * O.σ.w z *
      (if (n : ℝ) ^ (-1 - (3 : ℝ) / 100) <
          |interaction E O.G O.π J (Function.update (Function.update base j x) j' z)|
       then 1 else 0)) ≤ Real.exp (-((n : ℝ) ^ (2 / 5 : ℝ)))

/-- Uniform mean interaction estimate for all interaction sets of cardinality at least two. -/
def MeanInteractionEstimate {n N : ℕ} {E : Fin N → Fin N → Prop}
    {X Y : Finset (Fin N)} {δ x₀ K : ℝ} (O : OuterSetup (n := n) E X Y δ x₀ K) : Prop :=
  ∀ (u : ℕ) (J : Finset (Fin u)), 2 ≤ J.card →
    (∑ x : Fin u → Fin N, sigmaTupleWeight O.σ x *
      |interaction E O.G O.π J x|) ≤ (n : ℝ) ^ (-(2 / 5 : ℝ) * J.card)

/-- Uniform Ramsey count for labels extending an interaction above the `n^(-δ/4)` cutoff. -/
def LargeExtensionEstimate {n N : ℕ} {E : Fin N → Fin N → Prop}
    {X Y : Finset (Fin N)} {δ x₀ K : ℝ} (O : OuterSetup (n := n) E X Y δ x₀ K) : Prop :=
  ∀ (u : ℕ) (J : Finset (Fin u)) (j : Fin u) (hj : j ∈ J)
    (base : Fin u → Fin N),
    ((Finset.univ.filter fun x : Fin N =>
      x ∈ O.S ∧ (n : ℝ) ^ (-δ / 4) <
        |interaction E O.G O.π J (Function.update base j x)|).card : ℝ) ≤
      Real.exp ((n : ℝ) ^ (3 / 100 : ℝ))

/-- The shared X-RamseyBinom contract from `Needs.lean`. -/
def RamseyBinomialContract (N : ℕ) : Prop :=
  ∀ (G : SimpleGraph (Fin N)) (s t : ℕ)
    (hs : 0 < s) (ht : 0 < t)
    (hcard : Nat.choose (s + t - 2) (s - 1) ≤ Fintype.card (Fin N)),
    (∃ S : Finset (Fin N), S.card = s ∧
        ∀ ⦃x y : Fin N⦄, x ∈ S → y ∈ S → x ≠ y → G.Adj x y) ∨
      (∃ S : Finset (Fin N), S.card = t ∧
        ∀ ⦃x y : Fin N⦄, x ∈ S → y ∈ S → x ≠ y → ¬ G.Adj x y)

/-- Uniform exponential-weight estimate below the `n^(-δ/4)` cutoff. -/
def ModerateWeightEstimate {n N : ℕ} {E : Fin N → Fin N → Prop}
    {X Y : Finset (Fin N)} {δ x₀ K : ℝ} (O : OuterSetup (n := n) E X Y δ x₀ K) : Prop :=
  ∀ (u : ℕ),
    (∑ x : Fin u → Fin N, sigmaTupleWeight O.σ x *
      (if interactionEnvelope E O.G O.π x ≤ (n : ℝ) ^ (-δ / 4)
       then Real.exp ((2 : ℝ) ^ u * n * interactionEnvelope E O.G O.π x) else 0)) ≤
      (8 : ℝ) ^ u

/-- L11.3a: one-free-label signed interactions have an exponentially small exceptional set. -/
theorem one_free_interaction {n N : ℕ} {E : Fin N → Fin N → Prop}
    {X Y : Finset (Fin N)} {δ x₀ K : ℝ} (O : OuterSetup (n := n) E X Y δ x₀ K) :
    OneFreeEstimate O := by
  sorry

/-- L11.3b: two-free-label interactions exceed `n^(-1-.03)` with probability at most `e^{-n^.4}`. -/
theorem two_free_interaction {n N : ℕ} {E : Fin N → Fin N → Prop}
    {X Y : Finset (Fin N)} {δ x₀ K : ℝ} (O : OuterSetup (n := n) E X Y δ x₀ K) :
    TwoFreeEstimate O := by
  sorry

/-- L11.3c: mean interaction sizes decay as `n^(-.4 |J|)`. -/
theorem mean_interaction {n N : ℕ} {E : Fin N → Fin N → Prop}
    {X Y : Finset (Fin N)} {δ x₀ K : ℝ} (O : OuterSetup (n := n) E X Y δ x₀ K) :
    MeanInteractionEstimate O := by
  sorry

/-- L11.3d: only `exp(n^.03)` labels extend fixed data to a large interaction. -/
theorem count_large_extensions {n N : ℕ} {E : Fin N → Fin N → Prop}
    {X Y : Finset (Fin N)} {δ x₀ K : ℝ} (hRamsey : RamseyBinomialContract N)
    (O : OuterSetup (n := n) E X Y δ x₀ K) :
    LargeExtensionEstimate O := by
  sorry

/-- L11.3e: exponential weights are controlled below the `n^(-δ/4)` interaction cutoff. -/
theorem moderate_interaction_weights {n N : ℕ} {E : Fin N → Fin N → Prop}
    {X Y : Finset (Fin N)} {δ x₀ K : ℝ} (O : OuterSetup (n := n) E X Y δ x₀ K) :
    ModerateWeightEstimate O := by
  sorry

/-- L11.3f: the centered expansion controls the contribution from small interactions. -/
theorem centered_interaction_expansion {n N : ℕ} {E : Fin N → Fin N → Prop}
    {X Y : Finset (Fin N)} {δ x₀ K P : ℝ} (O : OuterSetup (n := n) E X Y δ x₀ K)
    (hOne : OneFreeEstimate O) (hTwo : TwoFreeEstimate O)
    (hMean : MeanInteractionEstimate O) (hModerate : ModerateWeightEstimate O) :
    ∃ D : SmallMomentData (P := P) O, True := by
  sorry

/-- L11.3g: Ramsey extension counting removes the large-interaction tuples. -/
theorem remove_large_interactions {n N : ℕ} {E : Fin N → Fin N → Prop}
    {X Y : Finset (Fin N)} {δ x₀ K P : ℝ} (O : OuterSetup (n := n) E X Y δ x₀ K)
    (hCount : LargeExtensionEstimate O) (hModerate : ModerateWeightEstimate O)
    (hSmall : SmallMomentData (P := P) O) :
    largeInteractionContribution (u := hSmall.u) O ≤
      (2 : ℝ) ^ (-(hSmall.u + 1 : ℤ)) * (n : ℝ) ^ (-P) := by
  sorry

/-- Markov's inequality from the even-moment certificate, proved directly on the finite sample space. -/
theorem outer_tail_from_even_moment {n N : ℕ} {E : Fin N → Fin N → Prop}
    {X Y : Finset (Fin N)} {δ x₀ K P : ℝ} (O : OuterSetup (n := n) E X Y δ x₀ K)
    (h : ∃ u : ℕ, Even u ∧ 0 < u ∧
      outerMoment (u := u) O ≤ (2 : ℝ) ^ (-(u : ℤ)) * (n : ℝ) ^ (-P)) :
    outerFailureMass O ≤ (n : ℝ) ^ (-P) := by
  classical
  obtain ⟨u, huEven, huPos, hMoment⟩ := h
  have hcancel : (2 : ℝ) ^ u * (2 : ℝ) ^ (-(u : ℤ)) = 1 := by
    rw [← zpow_natCast]
    rw [mul_comm]
    exact zpow_neg_mul_zpow_self (u : ℤ) (by norm_num)
  have hpoint (Z : Fin (outerDimension n) → Fin N) :
      outerTupleWeight O.π Z *
          (if outerMass E O.G O.π O.σ Z < 1 / 2 then 1 else 0) ≤
        (2 : ℝ) ^ u * outerTupleWeight O.π Z *
          |outerMass E O.G O.π O.σ Z - 1| ^ u := by
    have hw : 0 ≤ outerTupleWeight O.π Z := by
      unfold outerTupleWeight
      exact Finset.prod_nonneg fun j _ => O.π.nonneg (Z j)
    by_cases hZ : outerMass E O.G O.π O.σ Z < 1 / 2
    · rw [if_pos hZ]
      have hneg : outerMass E O.G O.π O.σ Z - 1 < 0 := by
        calc
          outerMass E O.G O.π O.σ Z - 1 < 1 / 2 - 1 := sub_lt_sub_right hZ 1
          _ < 0 := by norm_num
      have hlarge : (1 / 2 : ℝ) ≤ |outerMass E O.G O.π O.σ Z - 1| := by
        rw [abs_of_neg hneg]
        have hstrong : outerMass E O.G O.π O.σ Z - 1 < -(1 / 2 : ℝ) := by
          calc
            outerMass E O.G O.π O.σ Z - 1 < 1 / 2 - 1 := sub_lt_sub_right hZ 1
            _ = -(1 / 2 : ℝ) := by norm_num
        linarith
      have hpow := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 1 / 2) hlarge u
      have hone : 1 ≤ (2 : ℝ) ^ u * |outerMass E O.G O.π O.σ Z - 1| ^ u := by
        calc
          1 = (2 : ℝ) ^ u * (1 / 2 : ℝ) ^ u := by
            rw [← mul_pow]
            norm_num
          _ ≤ (2 : ℝ) ^ u * |outerMass E O.G O.π O.σ Z - 1| ^ u :=
            mul_le_mul_of_nonneg_left hpow (by positivity)
      calc
        outerTupleWeight O.π Z * 1 ≤ outerTupleWeight O.π Z *
            ((2 : ℝ) ^ u * |outerMass E O.G O.π O.σ Z - 1| ^ u) :=
          mul_le_mul_of_nonneg_left hone hw
        _ = (2 : ℝ) ^ u * outerTupleWeight O.π Z *
            |outerMass E O.G O.π O.σ Z - 1| ^ u := by ring
    · rw [if_neg hZ]
      simp
      positivity
  unfold outerFailureMass
  calc
    (∑ Z : Fin (outerDimension n) → Fin N,
        outerTupleWeight O.π Z *
          (if outerMass E O.G O.π O.σ Z < 1 / 2 then 1 else 0)) ≤
      ∑ Z : Fin (outerDimension n) → Fin N,
        (2 : ℝ) ^ u * outerTupleWeight O.π Z *
          |outerMass E O.G O.π O.σ Z - 1| ^ u :=
      Finset.sum_le_sum fun Z _ => hpoint Z
    _ = (2 : ℝ) ^ u * outerMoment (u := u) O := by
      unfold outerMoment
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro Z _
      ring
    _ ≤ (2 : ℝ) ^ u * ((2 : ℝ) ^ (-(u : ℤ)) * (n : ℝ) ^ (-P)) :=
      mul_le_mul_of_nonneg_left hMoment (by positivity)
    _ = ((2 : ℝ) ^ u * (2 : ℝ) ^ (-(u : ℤ))) * (n : ℝ) ^ (-P) := by ring
    _ = (n : ℝ) ^ (-P) := by rw [hcancel]; ring

/-- L11.3: assemble L11.3a–g and apply the finite even-moment bound. -/
theorem outer_mass_tail {n N : ℕ} {E : Fin N → Fin N → Prop}
    {X Y : Finset (Fin N)} {δ x₀ K P : ℝ} (O : OuterSetup (n := n) E X Y δ x₀ K) :
  outerFailureMass O ≤ (n : ℝ) ^ (-P) := by
  have hOne := one_free_interaction O
  have hTwo := two_free_interaction O
  have hMean := mean_interaction O
  have hRamsey : RamseyBinomialContract N := by
    intro G s t hs ht hcard
    exact HypercubeRamsey.S11.graph_ramsey_binomial_bound G s t hs ht hcard
  have hCount := count_large_extensions hRamsey O
  have hModerate := moderate_interaction_weights O
  obtain ⟨hSmall, -⟩ : ∃ D : SmallMomentData (P := P) O, True :=
    centered_interaction_expansion (P := P) O hOne hTwo hMean hModerate
  have hLarge := remove_large_interactions (P := P) O hCount hModerate hSmall
  have hMoment : ∃ u : ℕ, Even u ∧ 0 < u ∧
      outerMoment (u := u) O ≤ (2 : ℝ) ^ (-(u : ℤ)) * (n : ℝ) ^ (-P) := by
    refine ⟨hSmall.u, hSmall.u_even, hSmall.u_pos, ?_⟩
    calc
      outerMoment (u := hSmall.u) O ≤
          smallInteractionContribution (u := hSmall.u) O +
            largeInteractionContribution (u := hSmall.u) O :=
        hSmall.expansion_bound
      _ ≤ (2 : ℝ) ^ (-(hSmall.u + 1 : ℤ)) * (n : ℝ) ^ (-P) +
          (2 : ℝ) ^ (-(hSmall.u + 1 : ℤ)) * (n : ℝ) ^ (-P) :=
        add_le_add hSmall.good_bound hLarge
      _ = (2 : ℝ) ^ (-(hSmall.u : ℤ)) * (n : ℝ) ^ (-P) := by
        rw [← two_mul]
        rw [show -(hSmall.u + 1 : ℤ) = (-(hSmall.u : ℤ)) + (-1) by omega]
        rw [zpow_add₀ (by norm_num : (2 : ℝ) ≠ 0)]
        simp
        ring
  exact outer_tail_from_even_moment O hMoment

end HypercubeRamsey.S11.Core
