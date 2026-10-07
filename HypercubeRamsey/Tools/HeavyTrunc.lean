import HypercubeRamsey.Framework.FinProb

/-!
# Heavy-coordinate truncation

F-HeavyTrunc bounds the size and average-coordinate mass of labels with unusually large marginal, using a
pointwise cap on the joint law of a finite tuple.
-/

namespace HypercubeRamsey

open scoped BigOperators

private theorem ite_decidable_irrel {α : Sort*} (p : Prop)
    (d₁ d₂ : Decidable p) (a b : α) : @ite α p d₁ a b = @ite α p d₂ a b := by
  cases d₁ <;> cases d₂ <;> simp_all

/-- Average of the `k` coordinate marginals of a tuple law. -/
noncomputable def averageCoordinateMarginal {N k : ℕ} (P : FinProb (Fin k → Fin N))
    (x : Fin N) : ℝ :=
  (k : ℝ)⁻¹ * ∑ i, P.pr (fun ω => ω i = x)

/-- Coordinates whose normalized average marginal exceeds `exp(B)`. -/
noncomputable def heavyCoordinateSet {N k : ℕ} (P : FinProb (Fin k → Fin N)) (B : ℝ) :
    Finset (Fin N) :=
  Finset.univ.filter (fun x => Real.exp B < (N : ℝ) * averageCoordinateMarginal P x)

/-- F-HeavyTrunc: if `N^k P(ω) ≤ exp(A)` pointwise, then the heavy set is small and its average marginal
mass is controlled by `q/k + 2^k exp(A-Bq)` for every `q ≤ k`. -/
theorem heavyTruncation {N k : ℕ} (hN : 0 < N) (hk : 0 < k)
    (P : FinProb (Fin k → Fin N)) (A B : ℝ)
    (hcap : ∀ ω, (N : ℝ) ^ k * P.w ω ≤ Real.exp A) :
    let H := heavyCoordinateSet P B
    ((H.card : ℝ) ≤ (N : ℝ) * Real.exp (-B)) ∧
      (∀ q : ℕ, q ≤ k →
        ∑ x ∈ H, averageCoordinateMarginal P x ≤
          (q : ℝ) / k + (2 : ℝ) ^ k * Real.exp A * Real.exp (-B * q)) := by
  classical
  let H : Finset (Fin N) := heavyCoordinateSet P B
  have hcoordRow (i : Fin k) (ω : Fin k → Fin N) :
      (∑ x : Fin N, @ite ℝ ((fun ω' => ω' i = x) ω)
        (Classical.propDecidable ((fun ω' => ω' i = x) ω)) (P.w ω) 0) = P.w ω := by
    have hconvert :
        (∑ x : Fin N, @ite ℝ ((fun ω' => ω' i = x) ω)
          (Classical.propDecidable ((fun ω' => ω' i = x) ω)) (P.w ω) 0) =
          ∑ x : Fin N, @ite ℝ (ω i = x) (inferInstance : Decidable (ω i = x)) (P.w ω) 0 := by
      apply Finset.sum_congr rfl
      intro x hx
      exact ite_decidable_irrel (ω i = x) (Classical.propDecidable _)
        (inferInstance : Decidable (ω i = x)) _ _
    have hsum :
        (∑ x : Fin N, if ω i = x then P.w ω else 0) =
          (if ω i = ω i then P.w ω else 0) := by
      apply Finset.sum_eq_single (ω i)
      · intro x hx hne
        by_cases heq : ω i = x
        · exact False.elim (hne heq.symm)
        · simp [heq]
      · intro hnot
        exact False.elim (hnot (Finset.mem_univ _))
    rw [hconvert, hsum]
    simp
  have hcoord (i : Fin k) : ∑ x : Fin N, P.pr (fun ω => ω i = x) = 1 := by
    have hsumEq :
        (∑ x : Fin N, P.pr (fun ω => ω i = x)) = ∑ ω, P.w ω := by
      unfold FinProb.pr
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro ω hω
      exact hcoordRow i ω
    calc
      ∑ x : Fin N, P.pr (fun ω => ω i = x) = ∑ ω, P.w ω := hsumEq
      _ = 1 := P.sum_eq_one
  have htotal : ∑ x : Fin N, averageCoordinateMarginal P x = 1 := by
    unfold averageCoordinateMarginal
    rw [← Finset.mul_sum, Finset.sum_comm]
    calc
      (k : ℝ)⁻¹ * ∑ i : Fin k, ∑ x : Fin N, P.pr (fun ω => ω i = x) =
          (k : ℝ)⁻¹ * ∑ i : Fin k, 1 := by
            congr 1
            apply Finset.sum_congr rfl
            intro i hi
            exact hcoord i
      _ = 1 := by simp [hk.ne']
  have havgNonneg (x : Fin N) : 0 ≤ averageCoordinateMarginal P x := by
    unfold averageCoordinateMarginal
    apply mul_nonneg (inv_nonneg.mpr (Nat.cast_nonneg k))
    apply Finset.sum_nonneg
    intro i hi
    unfold FinProb.pr
    apply Finset.sum_nonneg
    intro ω hω
    split_ifs
    · exact P.nonneg ω
    · exact le_rfl
  have hHmass : ∑ x ∈ H, averageCoordinateMarginal P x ≤ 1 := by
    calc
      ∑ x ∈ H, averageCoordinateMarginal P x ≤ ∑ x, averageCoordinateMarginal P x := by
        apply Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ H)
        intro x hx hxnot
        exact havgNonneg x
      _ = 1 := htotal
  have hHpoint (x : Fin N) (hx : x ∈ H) :
      Real.exp B < (N : ℝ) * averageCoordinateMarginal P x := by
    exact (Finset.mem_filter.mp hx).2
  have hHsizeExp : (H.card : ℝ) * Real.exp B ≤ (N : ℝ) := by
    calc
      (H.card : ℝ) * Real.exp B = ∑ x ∈ H, Real.exp B := by simp
      _ ≤ ∑ x ∈ H, (N : ℝ) * averageCoordinateMarginal P x := by
        apply Finset.sum_le_sum
        intro x hx
        exact le_of_lt (hHpoint x hx)
      _ = (N : ℝ) * ∑ x ∈ H, averageCoordinateMarginal P x := by
        rw [Finset.mul_sum]
      _ ≤ (N : ℝ) := by
        calc
          (N : ℝ) * ∑ x ∈ H, averageCoordinateMarginal P x ≤ (N : ℝ) * 1 :=
            mul_le_mul_of_nonneg_left hHmass (Nat.cast_nonneg N)
          _ = (N : ℝ) := by ring
  have hHsize : (H.card : ℝ) ≤ (N : ℝ) * Real.exp (-B) := by
    have hexp : 0 < Real.exp B := Real.exp_pos B
    have hdiv : (H.card : ℝ) ≤ (N : ℝ) / Real.exp B :=
      (le_div_iff₀ hexp).2 hHsizeExp
    calc
      (H.card : ℝ) ≤ (N : ℝ) / Real.exp B := hdiv
      _ = (N : ℝ) * Real.exp (-B) := by rw [Real.exp_neg]; ring
  have hNpow : 0 < (N : ℝ) ^ k := pow_pos (Nat.cast_pos.mpr hN) k
  have hcardTuple : (Fintype.card (Fin k → Fin N) : ℝ) = (N : ℝ) ^ k := by
    simp
  have hcapSum : (N : ℝ) ^ k ≤ (Fintype.card (Fin k → Fin N) : ℝ) * Real.exp A := by
    calc
      (N : ℝ) ^ k = (N : ℝ) ^ k * ∑ ω, P.w ω := by simp [P.sum_eq_one]
      _ = ∑ ω, (N : ℝ) ^ k * P.w ω := by rw [Finset.mul_sum]
      _ ≤ ∑ ω, Real.exp A := by
        apply Finset.sum_le_sum
        intro ω hω
        exact hcap ω
      _ = (Fintype.card (Fin k → Fin N) : ℝ) * Real.exp A := by simp
  have hAone : 1 ≤ Real.exp A := by
    have hmul : (N : ℝ) ^ k * 1 ≤ (N : ℝ) ^ k * Real.exp A := by
      simpa [hcardTuple] using hcapSum
    exact (mul_le_mul_iff_of_pos_left hNpow).mp hmul
  let hits : (Fin k → Fin N) → ℕ := fun ω =>
    (Finset.univ.filter (fun i : Fin k => ω i ∈ H)).card
  have hmassH :
      ∑ x ∈ H, averageCoordinateMarginal P x =
        (k : ℝ)⁻¹ * ∑ ω, P.w ω * (hits ω : ℝ) := by
    have hcoordH (i : Fin k) :
        ∑ x ∈ H, P.pr (fun ω => ω i = x) =
          ∑ ω, if ω i ∈ H then P.w ω else 0 := by
      have hrow (ω : Fin k → Fin N) :
          (∑ x ∈ H, @ite ℝ (ω i = x) (Classical.propDecidable (ω i = x))
            (P.w ω) 0) = (if ω i ∈ H then P.w ω else 0) := by
        have hconvert :
            (∑ x ∈ H, @ite ℝ (ω i = x) (Classical.propDecidable (ω i = x))
              (P.w ω) 0) =
              ∑ x ∈ H, @ite ℝ (ω i = x) (inferInstance : Decidable (ω i = x))
                (P.w ω) 0 := by
          apply Finset.sum_congr rfl
          intro x hx
          exact ite_decidable_irrel (ω i = x) (Classical.propDecidable _)
            (inferInstance : Decidable (ω i = x)) _ _
        rw [hconvert]
        by_cases hx : ω i ∈ H
        · have hsum :
              (∑ x ∈ H, (if ω i = x then P.w ω else 0)) =
                (if ω i = ω i then P.w ω else 0) := by
            apply Finset.sum_eq_single (ω i)
            · intro x hx' hne
              by_cases heq : ω i = x
              · exact False.elim (hne heq.symm)
              · simp [heq]
            · intro hnot
              exact False.elim (hnot hx)
          rw [hsum]
          simp [hx]
        · have hsum :
              (∑ x ∈ H, (if ω i = x then P.w ω else 0)) = 0 := by
            apply Finset.sum_eq_zero
            intro x hx'
            by_cases heq : ω i = x
            · exact False.elim (hx (heq ▸ hx'))
            · simp [heq]
          rw [hsum]
          simp [hx]
      calc
        ∑ x ∈ H, P.pr (fun ω => ω i = x) =
            ∑ ω, ∑ x ∈ H,
              @ite ℝ (ω i = x) (Classical.propDecidable (ω i = x)) (P.w ω) 0 := by
                unfold FinProb.pr
                rw [Finset.sum_comm]
        _ = ∑ ω, if ω i ∈ H then P.w ω else 0 := by
              apply Finset.sum_congr rfl
              intro ω hω
              exact hrow ω
    have hcount (ω : Fin k → Fin N) :
        ∑ i : Fin k, (if ω i ∈ H then P.w ω else 0) = P.w ω * (hits ω : ℝ) := by
      rw [← Finset.sum_filter]
      simp [hits, Finset.sum_const, nsmul_eq_mul, mul_comm]
    unfold averageCoordinateMarginal
    rw [← Finset.mul_sum, Finset.sum_comm]
    congr 1
    calc
      ∑ i : Fin k, ∑ x ∈ H, P.pr (fun ω => ω i = x) =
          ∑ i : Fin k, ∑ ω, if ω i ∈ H then P.w ω else 0 := by
            apply Finset.sum_congr rfl
            intro i hi
            exact hcoordH i
      _ = ∑ ω, ∑ i : Fin k, (if ω i ∈ H then P.w ω else 0) := Finset.sum_comm
      _ = ∑ ω, P.w ω * (hits ω : ℝ) := by
            apply Finset.sum_congr rfl
            intro ω hω
            exact hcount ω
  have hmassH_nonneg : 0 ≤ ∑ x ∈ H, averageCoordinateMarginal P x :=
    Finset.sum_nonneg fun x hx => havgNonneg x
  have hpointHit (q : ℕ) (ω : Fin k → Fin N) :
      (hits ω : ℝ) / k ≤ (q : ℝ) / k + (if q < hits ω then 1 else 0) := by
    by_cases hq : q < hits ω
    · have hle : hits ω ≤ k := by
        dsimp [hits]
        calc
          (Finset.univ.filter (fun i : Fin k => ω i ∈ H)).card ≤ Finset.univ.card :=
            Finset.card_le_card (Finset.filter_subset _ _)
          _ = k := by simp
      have hkR : 0 < (k : ℝ) := Nat.cast_pos.mpr hk
      have hqdiv : ((q : ℝ) / k) * k = q := by field_simp [ne_of_gt hkR]
      rw [div_le_iff₀ hkR]
      simp [hq]
      have hleR : (hits ω : ℝ) ≤ k := by exact_mod_cast hle
      nlinarith [hleR, (Nat.cast_nonneg q : (q : ℝ) ≥ 0), hqdiv]
    · have hle : hits ω ≤ q := Nat.le_of_not_gt hq
      have hleR : (hits ω : ℝ) ≤ (q : ℝ) := by exact_mod_cast hle
      have hkR : 0 < (k : ℝ) := Nat.cast_pos.mpr hk
      calc
        (hits ω : ℝ) / k ≤ (q : ℝ) / k := div_le_div_of_nonneg_right hleR hkR.le
        _ = (q : ℝ) / k + (if q < hits ω then 1 else 0) := by simp [hq]
  have htailProb (q : ℕ) (hq : q ≤ k) :
      (∑ ω, if q < hits ω then P.w ω else 0) ≤
        (2 : ℝ) ^ k * Real.exp A * Real.exp (-B * q) := by
    let Js : Finset (Finset (Fin k)) :=
      Finset.univ.filter (fun J => J.card = q)
    have hJbound (J : Finset (Fin k)) (hJ : J.card = q) :
        (∑ ω ∈ Finset.univ.filter (fun ω : Fin k → Fin N =>
          ∀ i ∈ J, ω i ∈ H), P.w ω) ≤ Real.exp A * Real.exp (-B * q) := by
      let T : Fin k → Finset (Fin N) := fun i => if i ∈ J then H else Finset.univ
      let E : Finset (Fin k → Fin N) := Finset.univ.filter (fun ω => ∀ i ∈ J, ω i ∈ H)
      have hEsub : E ⊆ Fintype.piFinset T := by
        intro ω hω
        rw [Fintype.mem_piFinset]
        intro i
        by_cases hi : i ∈ J
        · simp [T, hi, (Finset.mem_filter.mp hω).2 i hi]
        · simp [T, hi]
      have hEcardNat : E.card ≤ (Fintype.piFinset T).card := Finset.card_le_card hEsub
      have hTcard : (Fintype.piFinset T).card = H.card ^ q * N ^ (k - q) := by
        rw [Fintype.card_piFinset]
        have hcompl : (Finset.univ.filter (fun i : Fin k => i ∉ J)).card = k - q := by
          have hset : Finset.univ.filter (fun i : Fin k => i ∉ J) = Finset.univ \ J := by
            ext i
            simp
          rw [hset, Finset.card_sdiff_of_subset (Finset.subset_univ J), hJ]
          simp
        have hprod :
            (∏ i : Fin k, if i ∈ J then H.card else N) = H.card ^ q * N ^ (k - q) := by
          calc
            (∏ i : Fin k, if i ∈ J then H.card else N) =
                ∏ i ∈ (Finset.univ : Finset (Fin k)), if i ∈ J then H.card else N := by simp
            _ = (∏ i ∈ Finset.univ with i ∈ J, if i ∈ J then H.card else N) *
                  ∏ i ∈ Finset.univ with i ∉ J, if i ∈ J then H.card else N := by
                    rw [← Finset.prod_filter_mul_prod_filter_not Finset.univ
                      (fun i : Fin k => i ∈ J)
                      (fun i : Fin k => if i ∈ J then H.card else N)]
            _ = H.card ^ q * N ^ (k - q) := by
                  have hleft :
                      (∏ i ∈ J, if i ∈ J then H.card else N) = H.card ^ q := by
                    calc
                      _ = ∏ i ∈ J, H.card := by
                        apply Finset.prod_congr rfl
                        intro i hi
                        simp [hi]
                      _ = H.card ^ q := by simp [hJ]
                  have hright :
                      (∏ i ∈ Finset.univ.filter (fun i : Fin k => i ∉ J),
                        if i ∈ J then H.card else N) = N ^ (k - q) := by
                    calc
                      _ = ∏ i ∈ Finset.univ.filter (fun i : Fin k => i ∉ J), N := by
                        apply Finset.prod_congr rfl
                        intro i hi
                        simp [(Finset.mem_filter.mp hi).2]
                      _ = N ^ (k - q) := by
                        rw [Finset.prod_const, hcompl]
                  have hleft' :
                      (∏ i ∈ Finset.univ with i ∈ J, if i ∈ J then H.card else N) =
                        H.card ^ q := by simpa using hleft
                  have hright' :
                      (∏ i ∈ Finset.univ with i ∉ J, if i ∈ J then H.card else N) =
                        N ^ (k - q) := hright
                  rw [hleft', hright']
        calc
          (∏ i : Fin k, (T i).card) = ∏ i : Fin k, if i ∈ J then H.card else N := by
            apply Finset.prod_congr rfl
            intro i hi
            by_cases hmem : i ∈ J <;> simp [T, hmem]
          _ = H.card ^ q * N ^ (k - q) := hprod
      have hEcard : (E.card : ℝ) ≤ (H.card : ℝ) ^ q * (N : ℝ) ^ (k - q) := by
        exact_mod_cast (hTcard ▸ hEcardNat)
      have hweight (ω : Fin k → Fin N) : P.w ω ≤ Real.exp A / (N : ℝ) ^ k := by
        apply (le_div_iff₀ hNpow).2
        simpa [mul_comm] using hcap ω
      have hcountWeight :
          (∑ ω ∈ E, P.w ω) ≤ (E.card : ℝ) * (Real.exp A / (N : ℝ) ^ k) := by
        calc
          ∑ ω ∈ E, P.w ω ≤ ∑ _ω ∈ E, Real.exp A / (N : ℝ) ^ k := by
            apply Finset.sum_le_sum
            intro ω hω
            exact hweight ω
          _ = (E.card : ℝ) * (Real.exp A / (N : ℝ) ^ k) := by simp
      have hpowBound :
          (H.card : ℝ) ^ q * (N : ℝ) ^ (k - q) ≤
            (N : ℝ) ^ k * Real.exp (-B * q) := by
        have hpowH : (H.card : ℝ) ^ q ≤ ((N : ℝ) * Real.exp (-B)) ^ q :=
          pow_le_pow_left₀ (Nat.cast_nonneg H.card) hHsize q
        calc
          (H.card : ℝ) ^ q * (N : ℝ) ^ (k - q) ≤
              ((N : ℝ) * Real.exp (-B)) ^ q * (N : ℝ) ^ (k - q) :=
                mul_le_mul_of_nonneg_right hpowH (by positivity)
          _ = (N : ℝ) ^ k * Real.exp (-B * q) := by
                rw [mul_pow]
                have hNpow' : (N : ℝ) ^ q * (N : ℝ) ^ (k - q) = (N : ℝ) ^ k := by
                  rw [← pow_add, Nat.add_sub_of_le hq]
                have hexppow : Real.exp (-B) ^ q = Real.exp (-B * q) := by
                  rw [← Real.exp_nat_mul]
                  congr 1
                  push_cast
                  ring
                calc
                  (N : ℝ) ^ q * Real.exp (-B) ^ q * (N : ℝ) ^ (k - q) =
                      ((N : ℝ) ^ q * (N : ℝ) ^ (k - q)) * Real.exp (-B) ^ q := by ring
                  _ = (N : ℝ) ^ k * Real.exp (-B) ^ q := by rw [hNpow']
                  _ = (N : ℝ) ^ k * Real.exp (-B * q) := by rw [hexppow]
      have hexpden : 0 < (N : ℝ) ^ k := hNpow
      calc
        ∑ ω ∈ E, P.w ω ≤ (E.card : ℝ) * (Real.exp A / (N : ℝ) ^ k) := hcountWeight
        _ ≤ ((H.card : ℝ) ^ q * (N : ℝ) ^ (k - q)) *
              (Real.exp A / (N : ℝ) ^ k) :=
                mul_le_mul_of_nonneg_right hEcard (div_nonneg (Real.exp_nonneg A) hexpden.le)
        _ ≤ ((N : ℝ) ^ k * Real.exp (-B * q)) *
              (Real.exp A / (N : ℝ) ^ k) :=
                mul_le_mul_of_nonneg_right hpowBound (div_nonneg (Real.exp_nonneg A) hexpden.le)
        _ = Real.exp A * Real.exp (-B * q) := by
              field_simp [ne_of_gt hexpden]
              <;> ring
    have htailUnion :
        (∑ ω, if q < hits ω then P.w ω else 0) ≤
          (∑ J ∈ Js, ∑ ω, if (∀ i ∈ J, ω i ∈ H) then P.w ω else 0) := by
      calc
        (∑ ω, if q < hits ω then P.w ω else 0) ≤
            (∑ ω, ∑ J ∈ Js, if (∀ i ∈ J, ω i ∈ H) then P.w ω else 0) := by
              apply Finset.sum_le_sum
              intro ω hω
              by_cases htail : q < hits ω
              · let hitSet : Finset (Fin k) := Finset.univ.filter (fun i => ω i ∈ H)
                have hqle : q ≤ hitSet.card := by
                  simpa [hitSet, hits] using Nat.le_of_lt htail
                obtain ⟨J, hJsubset, hJcard⟩ := Finset.exists_subset_card_eq hqle
                have hJmem : J ∈ Js := by simp [Js, hJcard]
                have hJhit : ∀ i ∈ J, ω i ∈ H := by
                  intro i hi
                  exact (Finset.mem_filter.mp (hJsubset hi)).2
                have hsum : P.w ω ≤
                    (∑ J' ∈ Js, if (∀ i ∈ J', ω i ∈ H) then P.w ω else 0) := by
                  let term : Finset (Fin k) → ℝ := fun J' =>
                    if (∀ i ∈ J', ω i ∈ H) then P.w ω else 0
                  have hsubset : ({J} : Finset (Finset (Fin k))) ⊆ Js := by
                    intro J' hJ'
                    have : J' = J := Finset.mem_singleton.mp hJ'
                    simpa [this] using hJmem
                  have hsubsetSum :
                      (∑ J' ∈ ({J} : Finset (Finset (Fin k))), term J') ≤
                        ∑ J' ∈ Js, term J' := by
                    apply Finset.sum_le_sum_of_subset_of_nonneg hsubset
                    intro J' hJ' hJnot
                    dsimp [term]
                    by_cases hcond : ∀ i ∈ J', ω i ∈ H
                    · rw [if_pos hcond]
                      exact P.nonneg ω
                    · rw [if_neg hcond]
                  have hsingle : term J ≤ ∑ J' ∈ Js, term J' := by
                    calc
                      term J = ∑ J' ∈ ({J} : Finset (Finset (Fin k))), term J' := by simp
                      _ ≤ ∑ J' ∈ Js, term J' := hsubsetSum
                  have htermJ : term J = P.w ω := by
                    dsimp [term]
                    exact if_pos hJhit
                  calc
                    P.w ω = term J := htermJ.symm
                    _ ≤ ∑ J' ∈ Js,
                        if (∀ i ∈ J', ω i ∈ H) then P.w ω else 0 := by simpa [term] using hsingle
                simpa [htail] using hsum
              · simp [htail]
                apply Finset.sum_nonneg
                intro J hJ
                split_ifs
                · exact P.nonneg ω
                · exact le_rfl
        _ = (∑ J ∈ Js, ∑ ω, if (∀ i ∈ J, ω i ∈ H) then P.w ω else 0) := by
              rw [Finset.sum_comm]
    calc
      (∑ ω, if q < hits ω then P.w ω else 0) ≤
          (∑ J ∈ Js, ∑ ω, if (∀ i ∈ J, ω i ∈ H) then P.w ω else 0) := htailUnion
      _ ≤ ∑ _J ∈ Js, Real.exp A * Real.exp (-B * q) := by
            apply Finset.sum_le_sum
            intro J hJ
            have hJcard : J.card = q := (Finset.mem_filter.mp hJ).2
            have hprob := hJbound J hJcard
            have hsumIte :
                (∑ ω ∈ Finset.univ.filter (fun ω : Fin k → Fin N => ∀ i ∈ J, ω i ∈ H),
                    P.w ω) =
                  ∑ ω, if (∀ i ∈ J, ω i ∈ H) then P.w ω else 0 := by
                    simpa using (Finset.sum_ite_mem_eq
                      (Finset.univ.filter (fun ω : Fin k → Fin N => ∀ i ∈ J, ω i ∈ H))
                      P.w).symm
            rw [← hsumIte]
            exact hprob
      _ = (Js.card : ℝ) * (Real.exp A * Real.exp (-B * q)) := by simp
      _ ≤ (2 : ℝ) ^ k * Real.exp A * Real.exp (-B * q) := by
            have hJs : Js.card ≤ (Finset.univ : Finset (Finset (Fin k))).card :=
              Finset.card_le_card (Finset.filter_subset _ _)
            have hcardPowerset :
                (Finset.univ : Finset (Finset (Fin k))).card = 2 ^ k := by simp
            have hfactor : 0 ≤ Real.exp A * Real.exp (-B * q) := by positivity
            have hJsR : (Js.card : ℝ) ≤ (2 : ℝ) ^ k := by
              exact_mod_cast (hcardPowerset ▸ hJs)
            calc
              (Js.card : ℝ) * (Real.exp A * Real.exp (-B * q)) ≤
                  (2 : ℝ) ^ k * (Real.exp A * Real.exp (-B * q)) :=
                    mul_le_mul_of_nonneg_right hJsR hfactor
              _ = (2 : ℝ) ^ k * Real.exp A * Real.exp (-B * q) := by ring
  refine ⟨?_, ?_⟩
  · simpa [H] using hHsize
  · intro q hq
    rw [hmassH]
    have hkR : 0 < (k : ℝ) := Nat.cast_pos.mpr hk
    calc
      (k : ℝ)⁻¹ * ∑ ω, P.w ω * (hits ω : ℝ) ≤
          (q : ℝ) / k + ∑ ω, if q < hits ω then P.w ω else 0 := by
            have hpω (ω : Fin k → Fin N) :
                P.w ω * ((hits ω : ℝ) / k) ≤
                  P.w ω * ((q : ℝ) / k + (if q < hits ω then 1 else 0)) :=
                    mul_le_mul_of_nonneg_left (hpointHit q ω) (P.nonneg ω)
            have hsum :
                (∑ ω, P.w ω * ((hits ω : ℝ) / k)) ≤
                  ∑ ω, P.w ω * ((q : ℝ) / k + (if q < hits ω then 1 else 0)) := by
              apply Finset.sum_le_sum
              intro ω hω
              exact hpω ω
            have hleft :
                ∑ ω, P.w ω * ((hits ω : ℝ) / k) =
                  (k : ℝ)⁻¹ * ∑ ω, P.w ω * (hits ω : ℝ) := by
                    calc
                      ∑ ω, P.w ω * ((hits ω : ℝ) / k) =
                          ∑ ω, (k : ℝ)⁻¹ * (P.w ω * (hits ω : ℝ)) := by
                            apply Finset.sum_congr rfl
                            intro ω hω
                            field_simp [ne_of_gt hkR] <;> ring
                      _ = (k : ℝ)⁻¹ * ∑ ω, P.w ω * (hits ω : ℝ) := by
                            rw [Finset.mul_sum]
            have hright :
                ∑ ω, P.w ω * ((q : ℝ) / k + (if q < hits ω then 1 else 0)) =
                  (q : ℝ) / k + ∑ ω, if q < hits ω then P.w ω else 0 := by
                    calc
                      _ = ∑ ω, (P.w ω * ((q : ℝ) / k) +
                          P.w ω * (if q < hits ω then 1 else 0)) := by
                            apply Finset.sum_congr rfl
                            intro ω hω
                            ring
                      _ = (∑ ω, P.w ω) * ((q : ℝ) / k) +
                            ∑ ω, if q < hits ω then P.w ω else 0 := by
                              rw [Finset.sum_add_distrib, Finset.sum_mul]
                              simp
                      _ = (q : ℝ) / k + ∑ ω, if q < hits ω then P.w ω else 0 := by
                              simp [P.sum_eq_one]
            calc
              (k : ℝ)⁻¹ * ∑ ω, P.w ω * (hits ω : ℝ) =
                  ∑ ω, P.w ω * ((hits ω : ℝ) / k) := hleft.symm
              _ ≤ ∑ ω, P.w ω *
                    ((q : ℝ) / k + (if q < hits ω then 1 else 0)) := hsum
              _ = (q : ℝ) / k + ∑ ω, if q < hits ω then P.w ω else 0 := hright
      _ ≤ (q : ℝ) / k + (2 : ℝ) ^ k * Real.exp A * Real.exp (-B * q) :=
            by nlinarith [htailProb q hq]

end HypercubeRamsey
