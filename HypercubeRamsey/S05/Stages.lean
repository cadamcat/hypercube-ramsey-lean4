import HypercubeRamsey.S05.Defs
import HypercubeRamsey.S05.Geometry_opus_s05

/-!
# L5.1g and L5.1i: the common high-row law and the prior-heavy bound

L5.1g is the separation step of the high rows (05:574–592); L5.1i bounds the number of prior-heavy entries of a
dominated tuple (05:785–806).  Both are used by the row construction of `Centres.lean`.
-/

set_option linter.deprecated false

namespace HypercubeRamsey

open Classical
open scoped BigOperators

/-- Positive log deletion cost for one high-row output relative to a smoothed deletion reference. -/
noncomputable def highDeletionCost5 {N s : ℕ} {Ref : Type*}
    (R : FinProb (Fin s × Fin N)) (Q : Ref → Fin s → Law N)
    (c : Ref) (h : Fin s) (y : Fin N) : ℝ :=
  max 0 (Real.log (R.w (h, y) / ((Q c h).w y / (s : ℝ))))

/-- Finite high-row data at a fixed observation history.

`capped_feasible` is the paper's density-good law (05:479–481, 05:557–573, 05:591–593): on a path passing the
tests, `ν` restricted to `G_D` and normalized lies in the compact convex set `𝔉`, whose members have the atom
cap and the true support.  It supplies the cap when there are no deletion references (`r_ref = 0`,
05:479–481), where `price_feasible` is vacuous. -/
structure HighRowModel5 (Data Ref : Type*) [Fintype Data] [Fintype Ref]
    (s N : ℕ) where
  raw : FinProb Data
  good : Data → Prop
  errorExponent : ℝ
  failure_bound : raw.pr (fun d => ¬ good d) ≤ Real.exp (-errorExponent * s)
  source : Data → Fin s → Law N
  deleted : Data → Ref → Fin s → Law N
  length : Ref → ℕ
  capExponent : ℝ
  costBound : ℝ
  capped_feasible : ∀ d, good d →
    ∃ R : FinProb (Fin s × Fin N),
      (∀ h y, R.w (h, y) ≤ 2 * Real.exp capExponent / ((s : ℝ) * N)) ∧
      (∀ h y, R.w (h, y) ≠ 0 → (source d h).w y ≠ 0)
  price_feasible : ∀ d, good d →
    ∀ price : Ref → ℝ, (∀ c, 0 ≤ price c) → (∑ c, price c = 1) →
      ∃ R : FinProb (Fin s × Fin N),
        (∀ h y, R.w (h, y) ≤ 2 * Real.exp capExponent / ((s : ℝ) * N)) ∧
        (∀ h y, R.w (h, y) ≠ 0 → (source d h).w y ≠ 0) ∧
        ∑ c, price c * (∑ h, ∑ y,
          R.w (h, y) * highDeletionCost5 R (deleted d) c h y) ≤
            ∑ c, price c * (costBound * length c)

/-- L5.1g (05:574–581): price feasibility over the compact high-row laws yields one law meeting every deletion
cost at once, with the atom cap and support on labels of positive reconstructed likelihood.  The proof is the
separation step: the capped, supported laws form a nonempty (`capped_feasible`) compact convex set and each
cost `∑ R log⁺(R/q)` is convex and continuous in `R`; with no references the cost clause is vacuous. -/
theorem L5_1g_common_high_law {Data Ref : Type*} [Fintype Data] [Fintype Ref]
    {s N : ℕ} (M : HighRowModel5 Data Ref s N) :
    M.raw.pr (fun d => ¬ M.good d) ≤ Real.exp (-M.errorExponent * s) ∧
    ∀ d, M.good d → ∃ R : FinProb (Fin s × Fin N),
      (∀ h y, R.w (h, y) ≤ 2 * Real.exp M.capExponent / ((s : ℝ) * N)) ∧
      (∀ h y, R.w (h, y) ≠ 0 → (M.source d h).w y ≠ 0) ∧
      (∀ c, ∑ h, ∑ y,
        R.w (h, y) * highDeletionCost5 R (M.deleted d) c h y ≤
          M.costBound * M.length c) := by
  refine ⟨M.failure_bound, ?_⟩
  intro d hd
  classical
  by_cases hRef : Nonempty Ref
  · by_cases hSub : Subsingleton Ref
    · let c₀ : Ref := Classical.choice hRef
      letI : Unique Ref := ⟨⟨c₀⟩, fun c => hSub.elim c c₀⟩
      let price : Ref → ℝ := fun _ => 1
      have hprice_nonneg : ∀ c, 0 ≤ price c := fun _ => by simp [price]
      have hprice_sum : ∑ c : Ref, price c = 1 := by simp [price]
      obtain ⟨R, hcap, hsupp, hcost⟩ := M.price_feasible d hd price hprice_nonneg hprice_sum
      refine ⟨R, hcap, hsupp, ?_⟩
      intro c
      have hc : c = default := hSub.elim _ _
      rw [hc]
      simpa [price] using hcost
    · -- Multiple references: the separation step (Sion's minimax theorem, 05:574–581).
      haveI : Nonempty Ref := hRef
      let cap : ℝ := 2 * Real.exp M.capExponent / ((s : ℝ) * N)
      let src : Fin s × Fin N → ℝ := fun i => (M.source d i.1).w i.2
      let K : Set (Fin s × Fin N → ℝ) := stdSimplex ℝ (Fin s × Fin N) ∩
        {w | ∀ i, w i ≤ cap ∧ (src i = 0 → w i = 0)}
      let a : Ref → Fin s × Fin N → ℝ := fun c i => (M.deleted d c i.1).w i.2 / (s : ℝ)
      let f : Ref → (Fin s × Fin N → ℝ) → ℝ := fun c w =>
        Lane_opus_s05_geo.excessSum (a c) w - M.costBound * M.length c
      have hcostEq : ∀ (R : FinProb (Fin s × Fin N)) (c : Ref),
          ∑ h, ∑ y, R.w (h, y) * highDeletionCost5 R (M.deleted d) c h y =
            Lane_opus_s05_geo.excessSum (a c) R.w := by
        intro R c
        unfold Lane_opus_s05_geo.excessSum
        rw [Fintype.sum_prod_type]
        refine Finset.sum_congr rfl fun h _ => Finset.sum_congr rfl fun y _ => ?_
        exact Lane_opus_s05_geo.excessCost_eq (R.nonneg (h, y))
      have hmemK : ∀ R : FinProb (Fin s × Fin N),
          (∀ h y, R.w (h, y) ≤ cap) → (∀ h y, R.w (h, y) ≠ 0 → (M.source d h).w y ≠ 0) →
            R.w ∈ K := by
        intro R hcap hsupp
        refine ⟨⟨R.nonneg, R.sum_eq_one⟩, fun i => ⟨hcap i.1 i.2, fun hi => ?_⟩⟩
        by_contra hne
        exact hsupp i.1 i.2 hne hi
      have hKsub : K ⊆ {w | ∀ i, 0 ≤ w i} := fun w hw => hw.1.1
      have hK : IsCompact K := by
        apply IsCompact.inter_right
        · exact IsCompact.of_isClosed_subset isCompact_Icc (isClosed_stdSimplex ℝ _)
            (stdSimplex_subset_Icc ℝ)
        · have hset : {w : Fin s × Fin N → ℝ | ∀ i, w i ≤ cap ∧ (src i = 0 → w i = 0)} =
              ⋂ i, ({w : Fin s × Fin N → ℝ | w i ≤ cap} ∩
                {w : Fin s × Fin N → ℝ | src i = 0 → w i = 0}) := by
            ext w
            simp [Set.mem_iInter]
          rw [hset]
          refine isClosed_iInter fun i =>
            (isClosed_le (continuous_apply i) continuous_const).inter ?_
          by_cases hi : src i = 0
          · simpa [hi] using isClosed_eq (continuous_apply i) continuous_const
          · simp [hi]
      have hcv : Convex ℝ K := by
        refine (convex_stdSimplex ℝ _).inter ?_
        intro x hx y hy p q hp hq hpq i
        refine ⟨?_, fun hi => ?_⟩
        · simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
          have hxi := (hx i).1
          have hyi := (hy i).1
          calc p * x i + q * y i ≤ p * cap + q * cap := by
                exact add_le_add (mul_le_mul_of_nonneg_left hxi hp)
                  (mul_le_mul_of_nonneg_left hyi hq)
            _ = cap := by rw [← add_mul, hpq, one_mul]
        · simp [(hx i).2 hi, (hy i).2 hi]
      obtain ⟨R0, hcap0, hsupp0⟩ := M.capped_feasible d hd
      have hne : K.Nonempty := ⟨R0.w, hmemK R0 hcap0 hsupp0⟩
      have hcont : ∀ c, ContinuousOn (f c) K := fun c =>
        ((Lane_opus_s05_geo.excessSum_continuous (a c)).sub continuous_const).continuousOn
      have hconv : ∀ c, ConvexOn ℝ K (f c) := fun c =>
        ((Lane_opus_s05_geo.excessSum_convexOn (a c)).subset hKsub hcv).sub
          (concaveOn_const _ hcv)
      have hprice : ∀ p : Ref → ℝ, (∀ c, 0 ≤ p c) → ∑ c, p c = 1 →
          ∃ x ∈ K, ∑ c, p c * f c x ≤ 0 := by
        intro p hp0 hp1
        obtain ⟨R, hcap, hsupp, hcost⟩ := M.price_feasible d hd p hp0 hp1
        refine ⟨R.w, hmemK R hcap hsupp, ?_⟩
        simp only [hcostEq] at hcost
        simp only [f, mul_sub, Finset.sum_sub_distrib]
        linarith
      obtain ⟨w, hwK, hw⟩ :=
        Lane_opus_s05_geo.common_point_of_price hne hcv hK f hcont hconv hprice
      let R : FinProb (Fin s × Fin N) := ⟨w, hwK.1.1, hwK.1.2⟩
      refine ⟨R, fun h y => (hwK.2 (h, y)).1,
        fun h y hRy hsrc => hRy ((hwK.2 (h, y)).2 hsrc), ?_⟩
      intro c
      rw [hcostEq R c]
      have hc := hw c
      simp only [f] at hc
      change Lane_opus_s05_geo.excessSum (a c) w ≤ M.costBound * M.length c
      linarith
  · haveI : IsEmpty Ref := ⟨fun c => hRef ⟨c⟩⟩
    obtain ⟨R, hcap, hsupp⟩ := M.capped_feasible d hd
    refine ⟨R, hcap, hsupp, ?_⟩
    intro c
    exact isEmptyElim c

/-- L5.1i: a tuple whose coordinate law is dominated by `M` times a product reference has few entries in a
small label set. -/
theorem L5_1i_prior_heavy {N k : ℕ} (P Q : FinProb (Fin k → Fin N))
    (M q υ : ℝ) (hM : 0 ≤ M) (hq : 0 ≤ q) (hυ : 0 ≤ υ)
    (hdom : P.DensityLE5 Q M)
    (hQ : ∀ S : Finset (Fin k),
      Q.pr (fun z => ∀ i ∈ S, (z i).val < (q * N)) ≤ q ^ S.card) :
    P.pr (fun z =>
      υ * k < (Finset.univ.filter (fun i => (z i).val < q * N)).card) ≤
        2 ^ k * M * q ^ (υ * k) := by
  classical
  let low : (Fin k → Fin N) → Finset (Fin k) := fun z =>
    Finset.univ.filter (fun i => (z i).val < q * N)
  let big : Finset (Finset (Fin k)) :=
    Finset.univ.filter (fun S => υ * k < (S.card : ℝ))
  let bad : (Fin k → Fin N) → Prop := fun z => υ * k < (low z).card
  let allLow : Finset (Fin k) → (Fin k → Fin N) → Prop :=
    fun S z => ∀ i ∈ S, (z i).val < q * N
  let lowWeight : Finset (Fin k) → (Fin k → Fin N) → ℝ := fun S z =>
    @ite ℝ (allLow S z) (Classical.propDecidable (allLow S z)) (Q.w z) 0
  have hdom_pr (A : (Fin k → Fin N) → Prop) :
      P.pr A ≤ M * Q.pr A := by
    unfold FinProb.pr
    calc
      (∑ z, if A z then P.w z else 0) ≤
          ∑ z, if A z then M * Q.w z else 0 := by
        apply Finset.sum_le_sum
        intro z hz
        by_cases hAz : A z
        · simp only [if_pos hAz]
          exact hdom z
        · simp [hAz]
      _ = M * (∑ z, if A z then Q.w z else 0) := by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro z hz
        by_cases hAz : A z <;> simp [hAz] <;> ring
      _ = M * Q.pr A := by rfl
  have hQ_union : Q.pr bad ≤ ∑ S ∈ big, Q.pr (allLow S) := by
    unfold FinProb.pr
    calc
      (∑ z, if bad z then Q.w z else 0) ≤
          ∑ z, ∑ S ∈ big, lowWeight S z := by
        apply Finset.sum_le_sum
        intro z hz
        by_cases hzbad : bad z
        · have hmem : low z ∈ big := by
            simp only [big, Finset.mem_filter, Finset.mem_univ, true_and]
            exact hzbad
          have hall : allLow (low z) z := by
            intro i hi
            exact (Finset.mem_filter.mp hi).2
          have hnonneg (S : Finset (Fin k)) (hS : S ∈ big) :
              0 ≤ lowWeight S z := by
            dsimp [lowWeight]
            split_ifs
            · exact Q.nonneg z
            · exact le_rfl
          have hsingle := Finset.single_le_sum hnonneg hmem
          simpa [hzbad, lowWeight, hall] using hsingle
        · simp only [if_neg hzbad]
          exact Finset.sum_nonneg fun S hS => by
            dsimp [lowWeight]
            split_ifs
            · exact Q.nonneg z
            · exact le_rfl
      _ = ∑ S ∈ big, Q.pr (allLow S) := by
        rw [Finset.sum_comm]
        apply Finset.sum_congr rfl
        intro S hS
        rfl
  have hbig_card : (big.card : ℝ) ≤ (2 : ℝ) ^ k := by
    have hcard : big.card ≤ Fintype.card (Finset (Fin k)) := Finset.card_le_univ big
    have hpow : Fintype.card (Finset (Fin k)) = 2 ^ k := by simp
    exact_mod_cast hcard.trans_eq hpow
  have hQ_bound : Q.pr bad ≤ (2 : ℝ) ^ k * q ^ (υ * k) := by
    by_cases hq1 : q ≤ 1
    · have hsum : (∑ S ∈ big, Q.pr (allLow S)) ≤
          ∑ S ∈ big, q ^ S.card := by
        apply Finset.sum_le_sum
        intro S hS
        exact hQ S
      have hsum' : (∑ S ∈ big, q ^ S.card) ≤
          ∑ S ∈ big, q ^ (υ * k) := by
        apply Finset.sum_le_sum
        intro S hS
        have hexp : υ * k ≤ (S.card : ℝ) :=
          le_of_lt (Finset.mem_filter.mp hS).2
        have hp : q ^ S.card ≤ q ^ (υ * k) := by
          rw [← Real.rpow_natCast q S.card]
          exact Real.rpow_le_rpow_of_exponent_ge' hq hq1
            (mul_nonneg hυ (Nat.cast_nonneg k)) hexp
        exact hp
      have hconst : (∑ S ∈ big, q ^ (υ * k)) =
          (big.card : ℝ) * q ^ (υ * k) := by simp [Finset.sum_const, nsmul_eq_mul]
      have hcard_mul : (big.card : ℝ) * q ^ (υ * k) ≤
          (2 : ℝ) ^ k * q ^ (υ * k) :=
        mul_le_mul_of_nonneg_right hbig_card (Real.rpow_nonneg hq (υ * k))
      calc
        Q.pr bad ≤ ∑ S ∈ big, Q.pr (allLow S) := hQ_union
        _ ≤ ∑ S ∈ big, q ^ S.card := hsum
        _ ≤ ∑ S ∈ big, q ^ (υ * k) := hsum'
        _ = (big.card : ℝ) * q ^ (υ * k) := hconst
        _ ≤ (2 : ℝ) ^ k * q ^ (υ * k) := hcard_mul
    · have hqone : 1 ≤ q := le_of_not_ge hq1
      have hQbad : Q.pr bad ≤ 1 := by
        unfold FinProb.pr
        calc
          (∑ z, if bad z then Q.w z else 0) ≤ ∑ z, Q.w z := by
            apply Finset.sum_le_sum
            intro z hz
            by_cases hbz : bad z
            · simp [hbz]
            · simp [hbz, Q.nonneg z]
          _ = 1 := Q.sum_eq_one
      have htwo : 1 ≤ (2 : ℝ) ^ k := by
        exact one_le_pow₀ (by norm_num : (1 : ℝ) ≤ 2)
      have hqpow : 1 ≤ q ^ (υ * k) :=
        Real.one_le_rpow hqone (mul_nonneg hυ (Nat.cast_nonneg k))
      have hprod : 1 ≤ (2 : ℝ) ^ k * q ^ (υ * k) := by
        calc
          1 = 1 * 1 := by ring
          _ ≤ (2 : ℝ) ^ k * q ^ (υ * k) :=
            mul_le_mul htwo hqpow (by norm_num) (by norm_num)
      exact hQbad.trans hprod
  calc
    P.pr bad ≤ M * Q.pr bad := hdom_pr bad
    _ ≤ M * ((2 : ℝ) ^ k * q ^ (υ * k)) :=
      mul_le_mul_of_nonneg_left hQ_bound hM
    _ = (2 : ℝ) ^ k * M * q ^ (υ * k) := by ring

end HypercubeRamsey
