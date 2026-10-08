import HypercubeRamsey.Framework.FinProbLemmas
import HypercubeRamsey.S03.Mixtures
import HypercubeRamsey.S03.ScatteredMoments
import HypercubeRamsey.Tools.CubeGeometry

/-!
# Lane q-s10-c helpers for the Section 10 tagged-to-typical step
-/

namespace HypercubeRamsey.Lane_q_s10_c

open scoped BigOperators

/-- Under a product law, a finite product of functions with pairwise disjoint
coordinate scopes has expectation equal to the product of their expectations.
This is the finite-family form of `FinProb.pi_expect_mul_of_disjoint`. -/
theorem pi_expect_prod_pairwise_disjoint {ι ξ : Type*} [Fintype ι] [DecidableEq ι]
    [Fintype ξ] [DecidableEq ξ] {Ω : ι → Type*} [∀ i, Fintype (Ω i)]
    (P : ∀ i, FinProb (Ω i)) (s : Finset ξ)
    (f : ξ → (∀ i, Ω i) → ℝ) (scope : ξ → Finset ι)
    (hf : ∀ j, FinProb.DependsOn (f j) (scope j))
    (hdisj : ∀ j ∈ s, ∀ k ∈ s, j ≠ k → Disjoint (scope j) (scope k)) :
    (FinProb.pi P).expect (fun ω => ∏ j ∈ s, f j ω) =
      ∏ j ∈ s, (FinProb.pi P).expect (f j) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [FinProb.expect, (FinProb.pi P).sum_eq_one]
  | @insert j s hj ih =>
      let otherScope := s.biUnion scope
      have hOther : FinProb.DependsOn (fun ω => ∏ k ∈ s, f k ω) otherScope := by
        intro ω ω' hagree
        apply Finset.prod_congr rfl
        intro k hk
        apply hf k
        intro i hi
        exact hagree i (Finset.mem_biUnion.mpr ⟨k, hk, hi⟩)
      have hSeparate : Disjoint (scope j) otherScope := by
        rw [Finset.disjoint_left]
        intro i hi hrest
        rcases Finset.mem_biUnion.mp hrest with ⟨k, hk, hik⟩
        have hjk : j ≠ k := by
          intro heq
          subst k
          exact hj hk
        exact (Finset.disjoint_left.mp
          (hdisj j (Finset.mem_insert_self j s) k (Finset.mem_insert_of_mem hk) hjk)) hi hik
      have hdisjS : ∀ k ∈ s, ∀ l ∈ s, k ≠ l → Disjoint (scope k) (scope l) := by
        intro k hk l hl hkl
        exact hdisj k (Finset.mem_insert_of_mem hk) l (Finset.mem_insert_of_mem hl) hkl
      calc
        (FinProb.pi P).expect (fun ω => ∏ k ∈ insert j s, f k ω) =
            (FinProb.pi P).expect (fun ω => f j ω * ∏ k ∈ s, f k ω) := by
          congr 1
          funext ω
          rw [Finset.prod_insert hj]
        _ = (FinProb.pi P).expect (f j) *
              (FinProb.pi P).expect (fun ω => ∏ k ∈ s, f k ω) :=
          FinProb.pi_expect_mul_of_disjoint P (f j) (fun ω => ∏ k ∈ s, f k ω)
            (scope j) otherScope (hf j) hOther hSeparate
        _ = ∏ k ∈ insert j s, (FinProb.pi P).expect (f k) := by
          rw [ih hdisjS]
          rw [Finset.prod_insert hj]

private theorem expect_sum_finset {Ω U : Type*} [Fintype Ω]
    (P : FinProb Ω) (s : Finset U) (f : U → Ω → ℝ) :
    P.expect (fun ω => ∑ u ∈ s, f u ω) = ∑ u ∈ s, P.expect (f u) := by
  classical
  simp only [FinProb.expect]
  calc
    (∑ ω, P.w ω * ∑ u ∈ s, f u ω) =
        ∑ ω, ∑ u ∈ s, P.w ω * f u ω := by
      apply Finset.sum_congr rfl
      intro ω hω
      rw [Finset.mul_sum]
    _ = ∑ u ∈ s, ∑ ω, P.w ω * f u ω := by
      rw [Finset.sum_comm]
    _ = ∑ u ∈ s, P.expect (f u) := rfl

/-- The response condition in Lemma 3.3 yields a product profile whose average
expected role value is at most the common per-slice bound. The payoff for a
slice is its share of the sum over roles assigned to that slice. -/
theorem simultaneous_profiles_role_average
    {J A U X : Type*} [Fintype J] [DecidableEq J] [Nonempty J]
    [Fintype A] [DecidableEq A] [Nonempty A] [Fintype U] [Nonempty U] [Fintype X]
    (roleSlice : U → J) (Z : X → U → (J → A) → ℝ)
    (scale bound : ℝ) (hscale : scale = (Fintype.card J : ℝ) / Fintype.card U)
    (hresp : ∀ j (q : J → A → ℝ), (∀ i a, 0 ≤ q i a) → (∀ i, ∑ a, q i a = 1) →
      ∃ qj : A → ℝ, (∀ a, 0 ≤ qj a) ∧ ∑ a, qj a = 1 ∧
        ∀ x, ∑ σ : J → A, (∏ i, Function.update q j qj i (σ i)) *
          (scale * ∑ u ∈ Finset.univ.filter (fun u : U => roleSlice u = j),
            Z x u σ) ≤ bound) :
    ∃ q : J → A → ℝ, ∃ hq0 : ∀ j a, 0 ≤ q j a,
      ∃ hq1 : ∀ j, ∑ a, q j a = 1,
      ∀ x, (Fintype.card U : ℝ)⁻¹ * ∑ u,
        (FinProb.pi (fun j => ⟨q j, hq0 j, hq1 j⟩ : J → FinProb A)).expect (Z x u) ≤ bound := by
  classical
  let m : J → ℕ := fun _ => Fintype.card X
  let e : X ≃ Fin (Fintype.card X) := Fintype.equivFin X
  let payoff : ∀ j, (J → A) → Fin (m j) → ℝ := fun j σ r =>
    scale * ∑ u ∈ Finset.univ.filter (fun u : U => roleSlice u = j), Z (e.symm r) u σ
  have hresp' : ∀ j (q : J → A → ℝ), (∀ i a, 0 ≤ q i a) →
      (∀ i, ∑ a, q i a = 1) →
      ∃ qj : A → ℝ, (∀ a, 0 ≤ qj a) ∧ ∑ a, qj a = 1 ∧
        ∀ r, ∑ σ : J → A, (∏ i, Function.update q j qj i (σ i)) * payoff j σ r ≤ bound := by
    intro j q hq0 hq1
    obtain ⟨qj, hqj0, hqj1, hqout⟩ := hresp j q hq0 hq1
    refine ⟨qj, hqj0, hqj1, ?_⟩
    intro r
    simpa [payoff, m] using hqout (e.symm r)
  obtain ⟨q, hq0, hq1, hprofile⟩ :=
    HypercubeRamsey.simultaneous_profiles payoff (fun _ _ => bound) hresp'
  let P : J → FinProb A := fun j => ⟨q j, hq0 j, hq1 j⟩
  let Q : FinProb (J → A) := FinProb.pi P
  have hprofileExpect (j : J) (x : X) :
      Q.expect (fun σ => scale *
        ∑ u ∈ Finset.univ.filter (fun u : U => roleSlice u = j), Z x u σ) ≤ bound := by
    have h := hprofile j (e x)
    simpa [Q, P, payoff, m, FinProb.expect, FinProb.pi] using h
  have hdouble (x : X) :
      (∑ j, ∑ u ∈ Finset.univ.filter (fun u : U => roleSlice u = j),
          Q.expect (Z x u)) = ∑ u, Q.expect (Z x u) := by
    calc
      _ = ∑ j, ∑ u, if roleSlice u = j then Q.expect (Z x u) else 0 := by
        apply Finset.sum_congr rfl
        intro j hj
        rw [Finset.sum_filter]
      _ = ∑ u, ∑ j, if roleSlice u = j then Q.expect (Z x u) else 0 := by
        rw [Finset.sum_comm]
      _ = _ := by
        apply Finset.sum_congr rfl
        intro u hu
        simp
  have htotal (x : X) :
      scale * ∑ u, Q.expect (Z x u) ≤ (Fintype.card J : ℝ) * bound := by
    calc
      scale * ∑ u, Q.expect (Z x u) =
          ∑ j, scale * ∑ u ∈ Finset.univ.filter (fun u : U => roleSlice u = j),
            Q.expect (Z x u) := by
              rw [← hdouble x, Finset.mul_sum]
      _ ≤ ∑ j, bound := Finset.sum_le_sum fun j hj => by
            have h := hprofileExpect j x
            rw [FinProb.expect_smul, expect_sum_finset] at h
            exact h
      _ = (Fintype.card J : ℝ) * bound := by simp
  have hcardJ : 0 < (Fintype.card J : ℝ) := Nat.cast_pos.mpr Fintype.card_pos
  have hcardU : 0 < (Fintype.card U : ℝ) := Nat.cast_pos.mpr Fintype.card_pos
  refine ⟨q, hq0, hq1, ?_⟩
  intro x
  have htotal' : (Fintype.card J : ℝ) / Fintype.card U *
      ∑ u, Q.expect (Z x u) ≤ (Fintype.card J : ℝ) * bound := by
    simpa [hscale] using htotal x
  have hratio : (Fintype.card J : ℝ) / Fintype.card U *
      ∑ u, Q.expect (Z x u) = (Fintype.card J : ℝ) *
        ((Fintype.card U : ℝ)⁻¹ * ∑ u, Q.expect (Z x u)) := by
    rw [div_eq_mul_inv]
    ring
  have hmul : (Fintype.card J : ℝ) *
      ((Fintype.card U : ℝ)⁻¹ * ∑ u, Q.expect (Z x u)) ≤
        (Fintype.card J : ℝ) * bound := by
    rw [← hratio]
    exact htotal'
  have hfinal := le_of_mul_le_mul_left hmul hcardJ
  simpa [Q, P] using hfinal

/-- Convert slice profile bounds into a bound on the average expected role
value, for a fixed profile shared by any number of label families. -/
theorem role_average_of_profiles
    {J A U X : Type*} [Fintype J] [DecidableEq J] [Nonempty J]
    [Fintype A] [DecidableEq A] [Nonempty A] [Fintype U] [Nonempty U] [Fintype X]
    (roleSlice : U → J) (Z : X → U → (J → A) → ℝ)
    (scale bound : ℝ) (hscale : scale = (Fintype.card J : ℝ) / Fintype.card U)
    (q : J → A → ℝ) (hq0 : ∀ j a, 0 ≤ q j a) (hq1 : ∀ j, ∑ a, q j a = 1)
    (hprofile : ∀ j x,
      (FinProb.pi (fun j => ⟨q j, hq0 j, hq1 j⟩ : J → FinProb A)).expect
        (fun σ => scale * ∑ u ∈ Finset.univ.filter (fun u : U => roleSlice u = j),
          Z x u σ) ≤ bound) :
    ∀ x, (Fintype.card U : ℝ)⁻¹ * ∑ u,
      (FinProb.pi (fun j => ⟨q j, hq0 j, hq1 j⟩ : J → FinProb A)).expect (Z x u) ≤ bound := by
  classical
  let P : J → FinProb A := fun j => ⟨q j, hq0 j, hq1 j⟩
  let Q : FinProb (J → A) := FinProb.pi P
  have hdouble (x : X) :
      (∑ j, ∑ u ∈ Finset.univ.filter (fun u : U => roleSlice u = j),
          Q.expect (Z x u)) = ∑ u, Q.expect (Z x u) := by
    calc
      _ = ∑ j, ∑ u, if roleSlice u = j then Q.expect (Z x u) else 0 := by
        apply Finset.sum_congr rfl
        intro j hj
        rw [Finset.sum_filter]
      _ = ∑ u, ∑ j, if roleSlice u = j then Q.expect (Z x u) else 0 := by
        rw [Finset.sum_comm]
      _ = _ := by
        apply Finset.sum_congr rfl
        intro u hu
        simp
  have htotal (x : X) :
      scale * ∑ u, Q.expect (Z x u) ≤ (Fintype.card J : ℝ) * bound := by
    calc
      scale * ∑ u, Q.expect (Z x u) =
          ∑ j, scale * ∑ u ∈ Finset.univ.filter (fun u : U => roleSlice u = j),
            Q.expect (Z x u) := by
              rw [← hdouble x, Finset.mul_sum]
      _ ≤ ∑ j, bound := Finset.sum_le_sum fun j hj => by
            have h := hprofile j x
            simpa [Q, P, FinProb.expect_smul, expect_sum_finset] using h
      _ = (Fintype.card J : ℝ) * bound := by simp
  have hcardJ : 0 < (Fintype.card J : ℝ) := Nat.cast_pos.mpr Fintype.card_pos
  have hcardU : 0 < (Fintype.card U : ℝ) := Nat.cast_pos.mpr Fintype.card_pos
  intro x
  have htotal' : (Fintype.card J : ℝ) / Fintype.card U *
      ∑ u, Q.expect (Z x u) ≤ (Fintype.card J : ℝ) * bound := by
    simpa [hscale] using htotal x
  have hratio : (Fintype.card J : ℝ) / Fintype.card U *
      ∑ u, Q.expect (Z x u) = (Fintype.card J : ℝ) *
        ((Fintype.card U : ℝ)⁻¹ * ∑ u, Q.expect (Z x u)) := by
    rw [div_eq_mul_inv]
    ring
  have hmul : (Fintype.card J : ℝ) *
      ((Fintype.card U : ℝ)⁻¹ * ∑ u, Q.expect (Z x u)) ≤
        (Fintype.card J : ℝ) * bound := by
    rw [← hratio]
    exact htotal'
  have hfinal := le_of_mul_le_mul_left hmul hcardJ
  simpa [Q, P] using hfinal

private theorem pr_mono_finprob {Ω : Type*} [Fintype Ω] (P : FinProb Ω)
    {A B : Ω → Prop} (hAB : ∀ ω, A ω → B ω) : P.pr A ≤ P.pr B := by
  classical
  unfold FinProb.pr
  apply Finset.sum_le_sum
  intro ω hω
  by_cases hA : A ω
  · have hB := hAB ω hA
    simp [hA, hB]
  · by_cases hB : B ω
    · simp [hA, hB, P.nonneg ω]
    · simp [hA, hB]

/-- A finite union has probability at most the sum of its member probabilities. -/
theorem pr_exists_finset_le_sum {Ω ι : Type*} [Fintype Ω]
    (P : FinProb Ω) (s : Finset ι) (A : ι → Ω → Prop) :
    P.pr (fun ω => ∃ i ∈ s, A i ω) ≤ ∑ i ∈ s, P.pr (A i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [FinProb.pr]
  | @insert i s his ih =>
      have hevent : (fun ω => ∃ j ∈ insert i s, A j ω) =
          (fun ω => A i ω ∨ ∃ j ∈ s, A j ω) := by
        funext ω
        simp [Finset.mem_insert]
      rw [hevent]
      calc
        P.pr (fun ω => A i ω ∨ ∃ j ∈ s, A j ω) ≤
            P.pr (A i) + P.pr (fun ω => ∃ j ∈ s, A j ω) := FinProb.pr_union P _ _
        _ ≤ P.pr (A i) + ∑ j ∈ s, P.pr (A j) := by nlinarith [ih]
        _ = ∑ j ∈ insert i s, P.pr (A j) := by rw [Finset.sum_insert his]

/-- Scattered moments for functions local to tag neighborhoods give the
single-label tail bound used after simultaneous profiles. -/
theorem pi_scattered_average_tail
    {I U X : Type*} [Fintype I] [DecidableEq I] [Fintype U] [DecidableEq U]
    [Nonempty U] [Fintype X] {Ω : I → Type*} [∀ i, Fintype (Ω i)]
    (P : ∀ i, FinProb (Ω i)) (scope : U → Finset I) (near : U → Finset U)
    (hscope : ∀ u v, v ∉ near u → Disjoint (scope u) (scope v))
    (hself : ∀ u, u ∈ near u) (f L bound threshold : ℝ)
    (hnear : ∀ u, ((near u).card : ℝ) ≤ f * Fintype.card U)
    (hf : 0 ≤ f) (hL : 0 ≤ L) (hthreshold : 0 < threshold)
    (Z : X → U → (∀ i, Ω i) → ℝ)
    (hlocal : ∀ x u, FinProb.DependsOn (Z x u) (scope u))
    (hZ0 : ∀ x u ω, 0 ≤ Z x u ω) (hZL : ∀ x u ω, Z x u ω ≤ L)
    (haverage : ∀ x, (Fintype.card U : ℝ)⁻¹ * ∑ u,
      (FinProb.pi P).expect (Z x u) ≤ bound)
    (n : ℕ) :
    ∀ x, (FinProb.pi P).pr (fun ω => threshold ≤
      (Fintype.card U : ℝ)⁻¹ * ∑ u, Z x u ω) ≤
        ((bound + n * f * L) / threshold) ^ n := by
  classical
  let Q : FinProb (∀ i, Ω i) := FinProb.pi P
  let d : X → U → ℝ := fun x u => Q.expect (Z x u)
  let avg (x : X) (ω : ∀ i, Ω i) : ℝ :=
    (Fintype.card U : ℝ)⁻¹ * ∑ u, Z x u ω
  have hcardU : 0 < (Fintype.card U : ℝ) := Nat.cast_pos.mpr Fintype.card_pos
  have hdisjoint (x : X) (m : ℕ) (hm : m ≤ n) (s : Fin m → U)
      (hsep : ∀ i j : Fin m, j < i → s i ∉ near (s j)) :
      ∀ i ∈ (Finset.univ : Finset (Fin m)), ∀ j ∈ Finset.univ, i ≠ j →
        Disjoint (scope (s i)) (scope (s j)) := by
    intro i hi j hj hij
    rcases lt_or_gt_of_ne hij with hlt | hgt
    · have hnot := hsep j i hlt
      exact hscope (s i) (s j) hnot
    · have hnot := hsep i j hgt
      exact (hscope (s j) (s i) hnot).symm
  have hjoint (x : X) : ∀ (m : ℕ), m ≤ n → ∀ s : Fin m → U,
      (∀ i j : Fin m, j < i → s i ∉ near (s j)) →
        ∑ ω ∈ Finset.univ, Q.w ω * ∏ i, Z x (s i) ω ≤
          1 ^ m * ∏ i, d x (s i) := by
    intro m hm s hsep
    have hfactor : Q.expect (fun ω => ∏ i : Fin m, Z x (s i) ω) =
        ∏ i : Fin m, Q.expect (Z x (s i)) := by
      simpa [Q] using pi_expect_prod_pairwise_disjoint P Finset.univ
        (fun i ω => Z x (s i) ω) (fun i => scope (s i))
        (fun i => hlocal x (s i)) (hdisjoint x m hm s hsep)
    have hsum : (∑ ω ∈ Finset.univ, Q.w ω * ∏ i, Z x (s i) ω) =
        Q.expect (fun ω => ∏ i : Fin m, Z x (s i) ω) := by
      simp [FinProb.expect]
    calc
      _ = ∏ i : Fin m, Q.expect (Z x (s i)) := by
        rw [hsum, hfactor]
      _ ≤ 1 ^ m * ∏ i : Fin m, d x (s i) := by
        simp [d]
  have hd0 : ∀ x u, 0 ≤ d x u := by
    intro x u
    unfold d FinProb.expect
    apply Finset.sum_nonneg
    intro ω hω
    exact mul_nonneg (Q.nonneg ω) (hZ0 x u ω)
  intro x
  have hsc := HypercubeRamsey.scattered_moments Q.w Q.nonneg Finset.univ
    (fun u ω => Z x u ω) (fun u ω => hZ0 x u ω) L hL
    (fun u ω hω => hZL x u ω) near hself f hnear n 1 (by norm_num)
    (fun u => d x u) (hd0 x) (hjoint x)
  let dAvg : ℝ := (Fintype.card U : ℝ)⁻¹ * ∑ u, d x u
  let base : ℝ := bound + n * f * L
  have hdAvg0 : 0 ≤ dAvg := by
    dsimp [dAvg]
    apply mul_nonneg (inv_nonneg.mpr hcardU.le)
    exact Finset.sum_nonneg fun u hu => hd0 x u
  have herror0 : 0 ≤ (n : ℝ) * f * L := by positivity
  have hbase0 : 0 ≤ dAvg + (n : ℝ) * f * L := add_nonneg hdAvg0 herror0
  have hbaseBound : dAvg + (n : ℝ) * f * L ≤ base := by
    dsimp [base, dAvg, d]
    linarith [haverage x]
  have hmoment : Q.expect (fun ω => avg x ω ^ n) ≤ base ^ n := by
    have hsc' : Q.expect (fun ω => avg x ω ^ n) ≤
        (dAvg + (n : ℝ) * f * L) ^ n := by
      simpa [Q, avg, dAvg, d, FinProb.expect, one_pow] using hsc
    exact hsc'.trans (pow_le_pow_left₀ hbase0 hbaseBound n)
  have havg0 : ∀ ω, 0 ≤ avg x ω := by
    intro ω
    dsimp [avg]
    apply mul_nonneg (inv_nonneg.mpr hcardU.le)
    exact Finset.sum_nonneg fun u hu => hZ0 x u ω
  have hmarkov := FinProb.markov Q (fun ω => avg x ω ^ n) (threshold ^ n)
    (fun ω => pow_nonneg (havg0 ω) n) (pow_pos hthreshold n)
  have hbadSubset : ∀ ω, threshold ≤ avg x ω → threshold ^ n ≤ avg x ω ^ n := by
    intro ω hω
    exact pow_le_pow_left₀ (le_of_lt hthreshold) hω n
  have hbad := pr_mono_finprob Q hbadSubset
  calc
    Q.pr (fun ω => threshold ≤ avg x ω) ≤
        Q.pr (fun ω => threshold ^ n ≤ avg x ω ^ n) := hbad
    _ ≤ Q.expect (fun ω => avg x ω ^ n) / threshold ^ n := hmarkov
    _ ≤ base ^ n / threshold ^ n :=
      div_le_div_of_nonneg_right hmoment (pow_pos hthreshold n).le
    _ = (base / threshold) ^ n := by rw [div_pow]

end HypercubeRamsey.Lane_q_s10_c
