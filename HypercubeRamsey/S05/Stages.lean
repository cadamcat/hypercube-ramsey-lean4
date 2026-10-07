import HypercubeRamsey.S05.Defs

/-!
# L5.1g and L5.1i: the common high-row law and the prior-heavy bound

L5.1g is the separation step of the high rows (05:574–592); L5.1i bounds the number of prior-heavy entries of a
dominated tuple (05:785–806).  Both are used by the row construction of `Centres.lean`.
-/

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
    · -- Multiple references require the finite separation argument.
      sorry
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
