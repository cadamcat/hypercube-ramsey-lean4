import HypercubeRamsey.S04.Defs

namespace HypercubeRamsey

open scoped BigOperators
open Filter

private abbrev WeightPair (N : ℕ) := (Fin N → ℝ) × (Fin N → ℝ)

open Classical in
private noncomputable def rawDensity {N : ℕ} (E : Fin N → Fin N → Prop)
    (G : Colour) (w : WeightPair N) : ℝ :=
  ∑ x, ∑ y, w.1 x * w.2 y * (if Hits E G x y then 1 else 0)

private def plateauFeasible {N : ℕ} (A B : Finset (Fin N)) (sX sY : ℝ) :
    Set (WeightPair N) :=
  {w | w.1 ∈ stdSimplex ℝ (Fin N) ∧ w.2 ∈ stdSimplex ℝ (Fin N) ∧
    (∀ x, x ∉ A → w.1 x = 0) ∧ (∀ y, y ∉ B → w.2 y = 0) ∧
    (∀ x, w.1 x ≤ Real.exp sX / N) ∧ (∀ y, w.2 y ≤ Real.exp sY / N)}

private theorem plateauFeasible_compact {N : ℕ} (A B : Finset (Fin N)) (sX sY : ℝ) :
    IsCompact (plateauFeasible A B sX sY) := by
  classical
  let S : Set (WeightPair N) := stdSimplex ℝ (Fin N) ×ˢ stdSimplex ℝ (Fin N)
  let SX : Set (WeightPair N) := {w | ∀ x, x ∉ A → w.1 x = 0}
  let SY : Set (WeightPair N) := {w | ∀ y, y ∉ B → w.2 y = 0}
  let CX : Set (WeightPair N) := {w | ∀ x, w.1 x ≤ Real.exp sX / N}
  let CY : Set (WeightPair N) := {w | ∀ y, w.2 y ≤ Real.exp sY / N}
  have hSclosed : IsClosed S := by
    have hEq : S =
        (fun w : WeightPair N => w.1) ⁻¹' stdSimplex ℝ (Fin N) ∩
          (fun w : WeightPair N => w.2) ⁻¹' stdSimplex ℝ (Fin N) := by
      ext w
      simp [S]
    rw [hEq]
    exact ((isClosed_stdSimplex ℝ (Fin N)).preimage (by fun_prop)).inter
      ((isClosed_stdSimplex ℝ (Fin N)).preimage (by fun_prop))
  have hSXclosed : IsClosed SX := by
    rw [show SX = ⋂ x : Fin N, {w : WeightPair N | x ∉ A → w.1 x = 0} by
      ext w
      simp [SX]]
    apply isClosed_iInter
    intro x
    by_cases hx : x ∈ A
    · simp [hx]
    · simpa [hx] using (isClosed_eq (by fun_prop) continuous_const)
  have hSYclosed : IsClosed SY := by
    rw [show SY = ⋂ y : Fin N, {w : WeightPair N | y ∉ B → w.2 y = 0} by
      ext w
      simp [SY]]
    apply isClosed_iInter
    intro y
    by_cases hy : y ∈ B
    · simp [hy]
    · simpa [hy] using (isClosed_eq (by fun_prop) continuous_const)
  have hCXclosed : IsClosed CX := by
    rw [show CX = ⋂ x : Fin N, {w : WeightPair N | w.1 x ≤ Real.exp sX / N} by
      ext w
      simp [CX]]
    apply isClosed_iInter
    intro x
    exact isClosed_le (by fun_prop) continuous_const
  have hCYclosed : IsClosed CY := by
    rw [show CY = ⋂ y : Fin N, {w : WeightPair N | w.2 y ≤ Real.exp sY / N} by
      ext w
      simp [CY]]
    apply isClosed_iInter
    intro y
    exact isClosed_le (by fun_prop) continuous_const
  have hEq : plateauFeasible A B sX sY = S ∩ (SX ∩ (SY ∩ (CX ∩ CY))) := by
    ext w
    simp [plateauFeasible, S, SX, SY, CX, CY] <;> tauto
  rw [hEq]
  apply IsCompact.of_isClosed_subset
    ((isCompact_stdSimplex ℝ (Fin N)).prod (isCompact_stdSimplex ℝ (Fin N)))
  · exact hSclosed.inter (hSXclosed.inter (hSYclosed.inter (hCXclosed.inter hCYclosed)))
  · intro w hw
    exact hw.1

private theorem continuous_rawDensity {N : ℕ} (E : Fin N → Fin N → Prop) (G : Colour) :
    Continuous (rawDensity E G) := by
  classical
  unfold rawDensity
  apply continuous_finset_sum
  intro x hx
  apply continuous_finset_sum
  intro y hy
  by_cases h : Hits E G x y
  · simp [h]
    fun_prop
  · simp [h]
    fun_prop

private theorem rawDensity_nonneg_le_one {N : ℕ} (E : Fin N → Fin N → Prop)
    (G : Colour) (μ ν : Law N) : 0 ≤ dens E G μ ν ∧ dens E G μ ν ≤ 1 := by
  classical
  constructor
  · unfold dens
    apply Finset.sum_nonneg
    intro x hx
    apply Finset.sum_nonneg
    intro y hy
    by_cases h : Hits E G x y
    · simp [h]
      exact mul_nonneg (μ.nonneg x) (ν.nonneg y)
    · simp [h]
  · unfold dens
    calc
      (∑ x, ∑ y, μ.w x * ν.w y * (if Hits E G x y then 1 else 0)) ≤
          ∑ x, ∑ y, μ.w x * ν.w y := by
        apply Finset.sum_le_sum
        intro x hx
        apply Finset.sum_le_sum
        intro y hy
        by_cases h : Hits E G x y
        · simp [h]
        · simp [h]
          exact mul_nonneg (μ.nonneg x) (ν.nonneg y)
      _ = (∑ x, μ.w x) * ∑ y, ν.w y := by
        rw [Finset.sum_mul_sum]
      _ = 1 := by rw [μ.sum_eq_one, ν.sum_eq_one]; norm_num

private theorem exists_rawDensity_max {N : ℕ} (E : Fin N → Fin N → Prop)
    (A B : Finset (Fin N)) (sX sY : ℝ)
    (hne : (plateauFeasible A B sX sY).Nonempty) :
    ∃ G : Colour, ∃ w ∈ plateauFeasible A B sX sY,
      ∀ G' : Colour, ∀ w' ∈ plateauFeasible A B sX sY,
        rawDensity E G' w' ≤ rawDensity E G w := by
  classical
  have hcompact := plateauFeasible_compact A B sX sY
  obtain ⟨wT, hwT, hmaxT⟩ :=
    hcompact.exists_isMaxOn hne (continuous_rawDensity E true).continuousOn
  obtain ⟨wF, hwF, hmaxF⟩ :=
    hcompact.exists_isMaxOn hne (continuous_rawDensity E false).continuousOn
  rcases le_total (rawDensity E false wF) (rawDensity E true wT) with h | h
  · refine ⟨true, wT, hwT, ?_⟩
    intro G' w' hw'
    cases G'
    · exact (hmaxF hw').trans h
    · exact hmaxT hw'
  · refine ⟨false, wF, hwF, ?_⟩
    intro G' w' hw'
    cases G'
    · exact hmaxF hw'
    · exact (hmaxT hw').trans h



open Classical in
private noncomputable def colDegree {N : ℕ} (E : Fin N → Fin N → Prop)
    (G : Colour) (μ : Law N) (y : Fin N) : ℝ :=
  ∑ x, μ.w x * (if Hits E G x y then 1 else 0)

private theorem dens_eq_sum_colDegree {N : ℕ} (E : Fin N → Fin N → Prop)
    (G : Colour) (μ ν : Law N) :
    dens E G μ ν = ∑ y, ν.w y * colDegree E G μ y := by
  classical
  unfold dens colDegree
  calc
    (∑ x, ∑ y, μ.w x * ν.w y * (if Hits E G x y then 1 else 0)) =
        ∑ y, ∑ x, μ.w x * ν.w y * (if Hits E G x y then 1 else 0) := by
      rw [Finset.sum_comm]
    _ = ∑ y, ν.w y * ∑ x, μ.w x * (if Hits E G x y then 1 else 0) := by
      apply Finset.sum_congr rfl
      intro y hy
      calc
        (∑ x, μ.w x * ν.w y * (if Hits E G x y then 1 else 0)) =
            ∑ x, ν.w y * (μ.w x * (if Hits E G x y then 1 else 0)) := by
          apply Finset.sum_congr rfl
          intro x hx
          ring
        _ = ν.w y * ∑ x, μ.w x * (if Hits E G x y then 1 else 0) := by
          rw [Finset.mul_sum]

private theorem sum_mul_indicator {N : ℕ} (S : Finset (Fin N))
    (f : Fin N → ℝ) (c : ℝ) :
    (∑ y, f y * (if y ∈ S then c else 0)) = (∑ y ∈ S, f y) * c := by
  classical
  have hfilter : Finset.univ.filter (fun y : Fin N => y ∈ S) = S := by
    ext y
    simp
  calc
    (∑ y, f y * (if y ∈ S then c else 0)) =
        ∑ y, if y ∈ S then f y * c else 0 := by
      apply Finset.sum_congr rfl
      intro y hy
      by_cases h : y ∈ S <;> simp [h]
    _ = ∑ y ∈ Finset.univ.filter (fun y : Fin N => y ∈ S), f y * c := by
      rw [Finset.sum_filter]
    _ = ∑ y ∈ S, f y * c := by rw [hfilter]
    _ = (∑ y ∈ S, f y) * c := by rw [Finset.sum_mul]

private noncomputable def conditionedLaw {N : ℕ} (ν : Law N)
    (H : Finset (Fin N)) (hH : 0 < ∑ y ∈ H, ν.w y) : Law N where
  w y := if y ∈ H then ν.w y / ∑ z ∈ H, ν.w z else 0
  nonneg y := by
    by_cases hy : y ∈ H
    · simp [hy]
      exact div_nonneg (ν.nonneg y) (le_of_lt hH)
    · simp [hy]
  sum_eq_one := by
    have hsum : (∑ y, if y ∈ H then ν.w y / (∑ z ∈ H, ν.w z) else 0) =
        (∑ y ∈ H, ν.w y) * (∑ z ∈ H, ν.w z)⁻¹ := by
      calc
        (∑ y, if y ∈ H then ν.w y / (∑ z ∈ H, ν.w z) else 0) =
            ∑ y, ν.w y * (if y ∈ H then (∑ z ∈ H, ν.w z)⁻¹ else 0) := by
          apply Finset.sum_congr rfl
          intro y hy
          by_cases h : y ∈ H <;> simp [h, div_eq_mul_inv]
        _ = (∑ y ∈ H, ν.w y) * (∑ z ∈ H, ν.w z)⁻¹ :=
          sum_mul_indicator H ν.w _
    rw [hsum]
    exact mul_inv_cancel₀ (ne_of_gt hH)

private theorem dens_complement_sum {N : ℕ} (E : Fin N → Fin N → Prop)
    (μ ν : Law N) : dens E true μ ν + dens E false μ ν = 1 := by
  classical
  unfold dens
  have hcolor (x y : Fin N) :
      (if Hits E true x y then (1 : ℝ) else 0) +
        (if Hits E false x y then (1 : ℝ) else 0) = 1 := by
    by_cases h : E x y <;> simp [Hits, h]
  calc
    (∑ x, ∑ y, μ.w x * ν.w y * (if Hits E true x y then 1 else 0)) +
        (∑ x, ∑ y, μ.w x * ν.w y * (if Hits E false x y then 1 else 0)) =
        ∑ x, ((∑ y, μ.w x * ν.w y * (if Hits E true x y then 1 else 0)) +
          ∑ y, μ.w x * ν.w y * (if Hits E false x y then 1 else 0)) := by
      rw [← Finset.sum_add_distrib]
    _ = ∑ x, ∑ y, μ.w x * ν.w y *
        ((if Hits E true x y then 1 else 0) + (if Hits E false x y then 1 else 0)) := by
      apply Finset.sum_congr rfl
      intro x hx
      rw [← Finset.sum_add_distrib]
      apply Finset.sum_congr rfl
      intro y hy
      ring
    _ = ∑ x, ∑ y, μ.w x * ν.w y := by
      apply Finset.sum_congr rfl
      intro x hx
      apply Finset.sum_congr rfl
      intro y hy
      rw [hcolor]
      ring
    _ = (∑ x, μ.w x) * ∑ y, ν.w y := by rw [Finset.sum_mul_sum]
    _ = 1 := by rw [μ.sum_eq_one, ν.sum_eq_one]; norm_num

private noncomputable def rawLaw {N : ℕ} (w : Fin N → ℝ)
    (hw : w ∈ stdSimplex ℝ (Fin N)) : Law N :=
  ⟨w, hw.1, hw.2⟩

private theorem rawDensity_eq_dens {N : ℕ} (E : Fin N → Fin N → Prop) (G : Colour)
    (w : WeightPair N) (hw : w.1 ∈ stdSimplex ℝ (Fin N))
    (hv : w.2 ∈ stdSimplex ℝ (Fin N)) :
    rawDensity E G w = dens E G (rawLaw w.1 hw) (rawLaw w.2 hv) := rfl

private theorem rawDensity_bounds_of_feasible {N : ℕ} (E : Fin N → Fin N → Prop)
    (A B : Finset (Fin N)) (sX sY : ℝ) (w : WeightPair N)
    (hw : w ∈ plateauFeasible A B sX sY) :
    0 ≤ rawDensity E true w ∧ rawDensity E true w ≤ 1 ∧
    0 ≤ rawDensity E false w ∧ rawDensity E false w ≤ 1 := by
  rcases hw with ⟨hμ, hν, -, -, -, -⟩
  have ht := rawDensity_nonneg_le_one E true (rawLaw w.1 hμ) (rawLaw w.2 hν)
  have hf := rawDensity_nonneg_le_one E false (rawLaw w.1 hμ) (rawLaw w.2 hν)
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [rawDensity_eq_dens]
    exact ht.1
  · rw [rawDensity_eq_dens]
    exact ht.2
  · rw [rawDensity_eq_dens]
    exact hf.1
  · rw [rawDensity_eq_dens]
    exact hf.2

private structure PlateauMax {N : ℕ} (E : Fin N → Fin N → Prop)
    (A B : Finset (Fin N)) (sX sY : ℝ) where
  G : Colour
  w : WeightPair N
  feasible : w ∈ plateauFeasible A B sX sY
  maximal : ∀ G' : Colour, ∀ w' ∈ plateauFeasible A B sX sY,
    rawDensity E G' w' ≤ rawDensity E G w

private theorem existsPlateauMax {N : ℕ} (E : Fin N → Fin N → Prop)
    (A B : Finset (Fin N)) (sX sY : ℝ)
    (hne : (plateauFeasible A B sX sY).Nonempty) :
    Nonempty (PlateauMax E A B sX sY) := by
  obtain ⟨G, w, hw, hmax⟩ := exists_rawDensity_max E A B sX sY hne
  exact ⟨⟨G, w, hw, hmax⟩⟩


private lemma omega4_pos (β γ : ℝ) (hβ : 0 < β) (hγ : γ < 1) :
    0 < omega4 β γ := by
  unfold omega4
  apply div_pos
  · exact lt_min hβ (by linarith)
  · positivity

private lemma omega4_le_beta_div (β γ : ℝ) :
    omega4 β γ ≤ β / 1000 := by
  unfold omega4
  exact div_le_div_of_nonneg_right (min_le_left _ _) (by norm_num)

private lemma omega4_le_gamma_div (β γ : ℝ) (hβγ : β ≤ γ) :
    omega4 β γ ≤ γ / 1000 := by
  exact (omega4_le_beta_div β γ).trans (by gcongr)

private lemma eventually_nat_rpow_gt_four {a : ℝ} (ha : 0 < a) :
    ∀ᶠ n : ℕ in atTop, 4 < (n : ℝ) ^ a := by
  have h := (tendsto_rpow_atTop ha).comp tendsto_natCast_atTop_atTop
  filter_upwards [h.eventually (Filter.eventually_gt_atTop 4)] with n hn
  exact hn

private theorem neg_rpow_lt_quarter {n : ℕ} (hn : 1 ≤ n) (r : ℝ)
    (hpow : 4 < (n : ℝ) ^ r) : (n : ℝ) ^ (-r) < 1 / 4 := by
  have hnR : 0 < (n : ℝ) := by exact_mod_cast (by omega : 0 < n)
  rw [Real.rpow_neg hnR.le]
  simpa [one_div] using one_div_lt_one_div_of_lt (by norm_num) hpow

private theorem rpow_mul_eq {x : ℝ} (hx : 0 < x) (r s : ℝ) :
    x ^ r * x ^ s = x ^ (r + s) := (Real.rpow_add hx r s).symm

private theorem exists_plateau_threshold (β γ : ℝ) (hβ : 0 < β)
    (hβγ : β ≤ γ) (hγ : γ < 1) :
    ∃ n₀ : ℕ, ∀ n ≥ n₀,
      2 ≤ n ∧
      4 < (n : ℝ) ^ (omega4 β γ / 2) ∧
      4 < (n : ℝ) ^ (omega4 β γ / 6) ∧
      4 < (n : ℝ) ^ (2 * omega4 β γ / 15) ∧
      4 < (n : ℝ) ^ (3 * omega4 β γ / 10) := by
  have hω := omega4_pos β γ hβ hγ
  have hω2 : 0 < omega4 β γ / 2 := div_pos hω (by norm_num)
  have hω6 : 0 < omega4 β γ / 6 := div_pos hω (by norm_num)
  have hω15 : 0 < 2 * omega4 β γ / 15 := div_pos (mul_pos (by norm_num) hω) (by norm_num)
  have hω10 : 0 < 3 * omega4 β γ / 10 := div_pos (mul_pos (by norm_num) hω) (by norm_num)
  have e1 : ∀ᶠ n : ℕ in atTop, 4 < (n : ℝ) ^ (omega4 β γ / 2) :=
    eventually_nat_rpow_gt_four hω2
  have e2 : ∀ᶠ n : ℕ in atTop, 4 < (n : ℝ) ^ (omega4 β γ / 6) :=
    eventually_nat_rpow_gt_four hω6
  have e3 : ∀ᶠ n : ℕ in atTop, 4 < (n : ℝ) ^ (2 * omega4 β γ / 15) :=
    eventually_nat_rpow_gt_four hω15
  have e4 : ∀ᶠ n : ℕ in atTop, 4 < (n : ℝ) ^ (3 * omega4 β γ / 10) :=
    eventually_nat_rpow_gt_four hω10
  have hevent := (Filter.eventually_ge_atTop 2).and (e1.and (e2.and (e3.and e4)))
  obtain ⟨n₀, hn₀⟩ := Filter.eventually_atTop.1 hevent
  refine ⟨n₀, ?_⟩
  intro n hn
  have h := hn₀ n hn
  exact ⟨h.1, h.2.1, h.2.2.1, h.2.2.2.1, h.2.2.2.2⟩

private noncomputable def plateauSteps (n : ℕ) (ω : ℝ) : ℕ :=
  Nat.floor ((n : ℝ) ^ (ω / 2)) / 2

private theorem plateauSteps_le_half {n : ℕ} {ω : ℝ} :
    (plateauSteps n ω : ℝ) ≤ (n : ℝ) ^ (ω / 2) / 2 := by
  let x := (n : ℝ) ^ (ω / 2)
  let m := Nat.floor x
  let J := m / 2
  have hfloor : (m : ℝ) ≤ x := Nat.floor_le (by positivity)
  have hdiv : 2 * J ≤ m := by dsimp [J]; omega
  have hdiv' : (2 : ℝ) * (J : ℝ) ≤ (m : ℝ) := by exact_mod_cast hdiv
  dsimp [plateauSteps, m, J, x]
  nlinarith

private theorem plateauSteps_mul_small_gt_one {n : ℕ} {ω : ℝ}
    (hn : 2 ≤ n) (hω : 0 < ω)
    (hω6 : 4 < (n : ℝ) ^ (ω / 6))
    (hω2 : 4 ≤ (n : ℝ) ^ (ω / 2)) :
    1 < (plateauSteps n ω : ℝ) * (n : ℝ) ^ (-ω / 3) := by
  have hnR : 0 < (n : ℝ) := by exact_mod_cast (by omega : 0 < n)
  let x := (n : ℝ) ^ (ω / 2)
  let b := (n : ℝ) ^ (-ω / 3)
  let m := Nat.floor x
  let J := m / 2
  have hm : m < 2 * J + 2 := by dsimp [m, J]; omega
  have hm' : m + 1 ≤ 2 * J + 2 := Nat.succ_le_of_lt hm
  have hm'' : (m : ℝ) + 1 ≤ 2 * (J : ℝ) + 2 := by exact_mod_cast hm'
  have hxlt : x < 2 * (J : ℝ) + 2 := (Nat.lt_floor_add_one x).trans_le hm''
  have hJlow : x / 4 < (J : ℝ) := by nlinarith [hxlt, hω2]
  have hbpos : 0 < b := by dsimp [b]; positivity
  have hprod : x * b = (n : ℝ) ^ (ω / 6) := by
    dsimp [x, b]
    rw [← Real.rpow_add hnR]
    congr 1
    ring
  have hJb : (x / 4) * b < (J : ℝ) * b :=
    mul_lt_mul_of_pos_right hJlow hbpos
  have hJeq : (J : ℝ) = (plateauSteps n ω : ℝ) := by rfl
  rw [← hJeq]
  dsimp [b] at hJb ⊢
  nlinarith [hJb, hprod, hω6]

private theorem exists_small_adjacent_gap {J : ℕ} {δ : ℝ} (v : ℕ → ℝ)
    (hJ : 1 < (J : ℝ) * δ) (hmono : ∀ j, v j ≤ 1)
    (hv0 : 0 ≤ v 0) : ∃ j < J, v (j + 1) - v j < δ := by
  by_contra hnone
  have hinc : ∀ j < J, δ ≤ v (j + 1) - v j := by
    intro j hj
    apply le_of_not_gt
    intro hlt
    exact hnone ⟨j, hj, hlt⟩
  have hsum : ∀ m ≤ J, (m : ℝ) * δ ≤ v m - v 0 := by
    intro m
    induction m with
    | zero => intro hm; simp
    | succ m ih =>
      intro hm
      have hmJ : m < J := by omega
      have hprev := ih (by omega)
      have hnext := hinc m hmJ
      calc
        (↑(m + 1) : ℝ) * δ = (m : ℝ) * δ + δ := by simp; ring
        _ ≤ (v m - v 0) + (v (m + 1) - v m) := add_le_add hprev hnext
        _ = v (m + 1) - v 0 := by ring
  have hJsum := hsum J le_rfl
  have hvJ := hmono J
  nlinarith


private noncomputable def plateauBudgetX (n : ℕ) (β ω : ℝ) (j : ℕ) : ℝ :=
  (n : ℝ) ^ β + (j : ℝ) * (n : ℝ) ^ (β - ω / 2)

private noncomputable def plateauBudgetY (n : ℕ) (γ ω : ℝ) (j : ℕ) : ℝ :=
  (n : ℝ) ^ γ + (j : ℝ) * (n : ℝ) ^ (γ - ω / 2)

set_option maxHeartbeats 1000000 in
private theorem plateau_selected (β γ : ℝ) (hβ : 0 < β) (hβγ : β ≤ γ)
    (hγ : γ < 1) {n N : ℕ} (hn2 : 2 ≤ n)
    (hω6 : 4 < (n : ℝ) ^ (omega4 β γ / 6))
    (hω2 : 4 ≤ (n : ℝ) ^ (omega4 β γ / 2)) (hN : 0 < N)
    (E : Fin N → Fin N → Prop) (A B : Finset (Fin N))
    (q : Law N × Law N)
    (hBias : PBias (pw β) (pw γ) (h4 β γ) n N E q.1 q.2)
    (hμA : q.1.SupportedIn A) (hνB : q.2.SupportedIn B) :
    ∃ j, j < plateauSteps n (omega4 β γ) ∧
      ∃ G : Colour, ∃ μ ν : Law N, ∃ p : ℝ,
        μ.SupportedIn A ∧ ν.SupportedIn B ∧
        μ.WidthLE (plateauBudgetX n β (omega4 β γ) j) ∧
        ν.WidthLE (plateauBudgetY n γ (omega4 β γ) j) ∧
        plateauBudgetX n β (omega4 β γ) j ≤ 3 / 2 * (n : ℝ) ^ β ∧
        plateauBudgetY n γ (omega4 β γ) j ≤ 3 / 2 * (n : ℝ) ^ γ ∧
        1 / 2 + (n : ℝ) ^ (-h4 β γ) ≤ p ∧ dens E G μ ν = p ∧
        (∀ μ' ν' : Law N,
          μ'.SupportedIn A → ν'.SupportedIn B →
          μ'.WidthLE (plateauBudgetX n β (omega4 β γ) j +
            (n : ℝ) ^ (β - omega4 β γ / 2) / 2) →
          ν'.WidthLE (plateauBudgetY n γ (omega4 β γ) j +
            (n : ℝ) ^ (γ - omega4 β γ / 2) / 2) →
          dens E G μ' ν' ≤ p + (n : ℝ) ^ (-omega4 β γ / 3)) := by
  classical
  have hω : 0 < omega4 β γ := omega4_pos β γ hβ hγ
  have hωβ := omega4_le_beta_div β γ
  have hωγ := omega4_le_gamma_div β γ hβγ
  have hβmargin : 0 < β - omega4 β γ / 2 := by nlinarith
  have hγmargin : 0 < γ - omega4 β γ / 2 := by nlinarith
  have hγlarge : omega4 β γ / 2 ≤ γ - omega4 β γ / 2 := by nlinarith
  have hnR : 0 < (n : ℝ) := by exact_mod_cast (by omega : 0 < n)
  have hNR : 0 < (N : ℝ) := by exact_mod_cast hN
  rcases hBias with ⟨hμWidth, hνWidth, hBiasAbs⟩
  let ω := omega4 β γ
  let dX := (n : ℝ) ^ (β - ω / 2)
  let dY := (n : ℝ) ^ (γ - ω / 2)
  have hdX : 0 < dX := by dsimp [dX]; exact Real.rpow_pos_of_pos hnR _
  have hdY : 0 < dY := by dsimp [dY]; exact Real.rpow_pos_of_pos hnR _
  have hXgrow (j : ℕ) : (n : ℝ) ^ β ≤ plateauBudgetX n β ω j := by
    dsimp [plateauBudgetX]
    exact le_add_of_nonneg_right
      (mul_nonneg (Nat.cast_nonneg j) (Real.rpow_pos_of_pos hnR _).le)
  have hYgrow (j : ℕ) : (n : ℝ) ^ γ ≤ plateauBudgetY n γ ω j := by
    dsimp [plateauBudgetY]
    exact le_add_of_nonneg_right
      (mul_nonneg (Nat.cast_nonneg j) (Real.rpow_pos_of_pos hnR _).le)
  have hfeas (j : ℕ) :
      (q.1.w, q.2.w) ∈ plateauFeasible A B
        (plateauBudgetX n β ω j) (plateauBudgetY n γ ω j) := by
    refine ⟨⟨q.1.nonneg, q.1.sum_eq_one⟩, ⟨q.2.nonneg, q.2.sum_eq_one⟩,
      hμA, hνB, ?_, ?_⟩
    · intro x
      calc
        q.1.w x ≤ Real.exp ((n : ℝ) ^ β) / N := hμWidth x
        _ ≤ Real.exp (plateauBudgetX n β ω j) / N :=
          div_le_div_of_nonneg_right
            (Real.exp_le_exp.mpr (hXgrow j)) hNR.le
    · intro y
      calc
        q.2.w y ≤ Real.exp ((n : ℝ) ^ γ) / N := hνWidth y
        _ ≤ Real.exp (plateauBudgetY n γ ω j) / N :=
          div_le_div_of_nonneg_right
            (Real.exp_le_exp.mpr (hYgrow j)) hNR.le
  let M : (j : ℕ) → PlateauMax E A B
      (plateauBudgetX n β ω j) (plateauBudgetY n γ ω j) :=
    fun j => Classical.choice
      (existsPlateauMax E A B (plateauBudgetX n β ω j) (plateauBudgetY n γ ω j)
        ⟨(q.1.w, q.2.w), hfeas j⟩)
  let v : ℕ → ℝ := fun j => rawDensity E (M j).G (M j).w
  have hvbound (j : ℕ) : v j ≤ 1 := by
    have hb := rawDensity_bounds_of_feasible E A B
      (plateauBudgetX n β ω j) (plateauBudgetY n γ ω j) (M j).w (M j).feasible
    cases hG : (M j).G with
    | false => simpa [v, hG] using hb.2.2.2
    | true => simpa [v, hG] using hb.2.1
  have hv0nonneg : 0 ≤ v 0 := by
    have hb := rawDensity_bounds_of_feasible E A B
      (plateauBudgetX n β ω 0) (plateauBudgetY n γ ω 0) (M 0).w (M 0).feasible
    cases hG : (M 0).G with
    | false => simpa [v, hG] using hb.2.2.1
    | true => simpa [v, hG] using hb.1
  have hsxmono (j : ℕ) :
      plateauBudgetX n β ω j ≤ plateauBudgetX n β ω (j + 1) := by
    dsimp [plateauBudgetX]
    rw [Nat.cast_add, Nat.cast_one]
    nlinarith [Real.rpow_pos_of_pos hnR (β - ω / 2)]
  have hsymono (j : ℕ) :
      plateauBudgetY n γ ω j ≤ plateauBudgetY n γ ω (j + 1) := by
    dsimp [plateauBudgetY]
    rw [Nat.cast_add, Nat.cast_one]
    nlinarith [Real.rpow_pos_of_pos hnR (γ - ω / 2)]
  have hfeasMono (j : ℕ) {w : WeightPair N}
      (hw : w ∈ plateauFeasible A B
        (plateauBudgetX n β ω j) (plateauBudgetY n γ ω j)) :
      w ∈ plateauFeasible A B
        (plateauBudgetX n β ω (j + 1)) (plateauBudgetY n γ ω (j + 1)) := by
    rcases hw with ⟨hμsimp, hνsimp, hμsupp, hνsupp, hX, hY⟩
    refine ⟨hμsimp, hνsimp, hμsupp, hνsupp, ?_, ?_⟩
    · intro x
      exact (hX x).trans (div_le_div_of_nonneg_right
        (Real.exp_le_exp.mpr (hsxmono j)) hNR.le)
    · intro y
      exact (hY y).trans (div_le_div_of_nonneg_right
        (Real.exp_le_exp.mpr (hsymono j)) hNR.le)
  have hvmono (j : ℕ) : v j ≤ v (j + 1) := by
    exact (M (j + 1)).maximal (M j).G (M j).w (hfeasMono j (M j).feasible)
  have hv0le_all : ∀ k, v 0 ≤ v k := by
    intro k
    induction k with
    | zero => exact le_rfl
    | succ k ih => exact ih.trans (hvmono k)
  let J := plateauSteps n ω
  have hJδ : 1 < (J : ℝ) * (n : ℝ) ^ (-ω / 3) := by
    simpa [J, ω] using plateauSteps_mul_small_gt_one hn2 hω hω6 hω2
  obtain ⟨j, hjJ, hgap⟩ := exists_small_adjacent_gap v hJδ hvbound hv0nonneg
  let G := (M j).G
  let μ := rawLaw (M j).w.1 ((M j).feasible).1
  let ν := rawLaw (M j).w.2 ((M j).feasible).2.1
  let p := v j
  have hμsupp : μ.SupportedIn A := by
    intro x hx
    simpa [μ, rawLaw] using ((M j).feasible).2.2.1 x hx
  have hνsupp : ν.SupportedIn B := by
    intro y hy
    simpa [ν, rawLaw] using ((M j).feasible).2.2.2.1 y hy
  have hμw : μ.WidthLE (plateauBudgetX n β ω j) := by
    intro x
    change (M j).w.1 x ≤ Real.exp (plateauBudgetX n β ω j) / N
    exact ((M j).feasible).2.2.2.2.1 x
  have hνw : ν.WidthLE (plateauBudgetY n γ ω j) := by
    intro y
    change (M j).w.2 y ≤ Real.exp (plateauBudgetY n γ ω j) / N
    exact ((M j).feasible).2.2.2.2.2 y
  have hpEq : dens E G μ ν = p := by
    dsimp [G, p, v, μ, ν]
    exact (rawDensity_eq_dens E (M j).G (M j).w
      ((M j).feasible).1 ((M j).feasible).2.1).symm
  have hrawTrueEq :
      rawDensity E true (q.1.w, q.2.w) = dens E true q.1 q.2 := by
    exact rawDensity_eq_dens E true (q.1.w, q.2.w)
      ⟨q.1.nonneg, q.1.sum_eq_one⟩ ⟨q.2.nonneg, q.2.sum_eq_one⟩
  have hrawFalseEq :
      rawDensity E false (q.1.w, q.2.w) = dens E false q.1 q.2 := by
    exact rawDensity_eq_dens E false (q.1.w, q.2.w)
      ⟨q.1.nonneg, q.1.sum_eq_one⟩ ⟨q.2.nonneg, q.2.sum_eq_one⟩
  have hdomTrue : dens E true q.1 q.2 ≤ v 0 := by
    rw [← hrawTrueEq]
    exact (M 0).maximal true (q.1.w, q.2.w) (hfeas 0)
  have hdomFalse : dens E false q.1 q.2 ≤ v 0 := by
    rw [← hrawFalseEq]
    exact (M 0).maximal false (q.1.w, q.2.w) (hfeas 0)
  have hcomp := dens_complement_sum E q.1 q.2
  have hp0 : 1 / 2 + (n : ℝ) ^ (-h4 β γ) ≤ v 0 := by
    by_cases hq : 1 / 2 ≤ dens E true q.1 q.2
    · have habs : |dens E true q.1 q.2 - 1 / 2| =
          dens E true q.1 q.2 - 1 / 2 :=
        abs_of_nonneg (by linarith)
      have hsur := hBiasAbs
      rw [habs] at hsur
      have htrue : 1 / 2 + (n : ℝ) ^ (-h4 β γ) ≤ dens E true q.1 q.2 := by
        linarith
      exact htrue.trans hdomTrue
    · have hqneg : dens E true q.1 q.2 < 1 / 2 := lt_of_not_ge hq
      have habs : |dens E true q.1 q.2 - 1 / 2| =
          1 / 2 - dens E true q.1 q.2 :=
        calc
          |dens E true q.1 q.2 - 1 / 2| =
              -(dens E true q.1 q.2 - 1 / 2) :=
            abs_of_neg (sub_neg.mpr hqneg)
          _ = 1 / 2 - dens E true q.1 q.2 := by ring
      have hsur := hBiasAbs
      rw [habs] at hsur
      have hfalse : 1 / 2 + (n : ℝ) ^ (-h4 β γ) ≤ dens E false q.1 q.2 := by
        linarith [hcomp]
      exact hfalse.trans hdomFalse
  have hv0le : v 0 ≤ v j := hv0le_all j
  have hpLower : 1 / 2 + (n : ℝ) ^ (-h4 β γ) ≤ p := by
    dsimp [p]
    exact hp0.trans hv0le
  have hx : (n : ℝ) ^ (ω / 2) = (n : ℝ) ^ (omega4 β γ / 2) := by rfl
  have hJhalf : (J : ℝ) ≤ (n : ℝ) ^ (ω / 2) / 2 := by
    exact plateauSteps_le_half
  have hjJreal : (j : ℝ) ≤ (J : ℝ) := by
    exact_mod_cast (Nat.le_of_lt hjJ)
  have hjhalf : (j : ℝ) ≤ (n : ℝ) ^ (ω / 2) / 2 := hjJreal.trans hJhalf
  have hmulX : (n : ℝ) ^ (ω / 2) * dX = (n : ℝ) ^ β := by
    calc
      (n : ℝ) ^ (ω / 2) * dX =
          (n : ℝ) ^ (ω / 2) * (n : ℝ) ^ (β - ω / 2) := by rfl
      _ = (n : ℝ) ^ ((ω / 2) + (β - ω / 2)) := by
        exact (Real.rpow_add hnR (ω / 2) (β - ω / 2)).symm
      _ = (n : ℝ) ^ β := by rw [show (ω / 2) + (β - ω / 2) = β by ring]
  have hmulY : (n : ℝ) ^ (ω / 2) * dY = (n : ℝ) ^ γ := by
    calc
      (n : ℝ) ^ (ω / 2) * dY =
          (n : ℝ) ^ (ω / 2) * (n : ℝ) ^ (γ - ω / 2) := by rfl
      _ = (n : ℝ) ^ ((ω / 2) + (γ - ω / 2)) := by
        exact (Real.rpow_add hnR (ω / 2) (γ - ω / 2)).symm
      _ = (n : ℝ) ^ γ := by rw [show (ω / 2) + (γ - ω / 2) = γ by ring]
  have hXadd : (j : ℝ) * dX ≤ (n : ℝ) ^ β / 2 := by
    calc
      (j : ℝ) * dX ≤ ((n : ℝ) ^ (ω / 2) / 2) * dX :=
        mul_le_mul_of_nonneg_right hjhalf hdX.le
      _ = (n : ℝ) ^ β / 2 := by rw [← hmulX]; ring
  have hYadd : (j : ℝ) * dY ≤ (n : ℝ) ^ γ / 2 := by
    calc
      (j : ℝ) * dY ≤ ((n : ℝ) ^ (ω / 2) / 2) * dY :=
        mul_le_mul_of_nonneg_right hjhalf hdY.le
      _ = (n : ℝ) ^ γ / 2 := by rw [← hmulY]; ring
  have hsxupper : plateauBudgetX n β ω j ≤ 3 / 2 * (n : ℝ) ^ β := by
    dsimp [plateauBudgetX]
    nlinarith [hXadd]
  have hsyupper : plateauBudgetY n γ ω j ≤ 3 / 2 * (n : ℝ) ^ γ := by
    dsimp [plateauBudgetY]
    nlinarith [hYadd]
  let b := (n : ℝ) ^ (-ω / 3)
  have hgap' : v (j + 1) ≤ p + b := by
    dsimp [p, b]
    linarith
  refine ⟨j, hjJ, G, μ, ν, p, hμsupp, hνsupp, ?_, ?_, hsxupper, hsyupper,
    hpLower, hpEq, ?_⟩
  · simpa [ω] using hμw
  · simpa [ω] using hνw
  · intro μ' ν' hμ'A hν'B hμ'W hν'W
    let w' : WeightPair N := (μ'.w, ν'.w)
    have hstepX : plateauBudgetX n β ω j +
        (n : ℝ) ^ (β - ω / 2) / 2 ≤
          plateauBudgetX n β ω (j + 1) := by
      simp only [plateauBudgetX, Nat.cast_add, Nat.cast_one]
      have hstep : 0 ≤ (n : ℝ) ^ (β - ω / 2) :=
        (Real.rpow_pos_of_pos hnR _).le
      nlinarith
    have hstepY : plateauBudgetY n γ ω j +
        (n : ℝ) ^ (γ - ω / 2) / 2 ≤
          plateauBudgetY n γ ω (j + 1) := by
      simp only [plateauBudgetY, Nat.cast_add, Nat.cast_one]
      have hstep : 0 ≤ (n : ℝ) ^ (γ - ω / 2) :=
        (Real.rpow_pos_of_pos hnR _).le
      nlinarith
    have hnext : w' ∈ plateauFeasible A B
        (plateauBudgetX n β ω (j + 1)) (plateauBudgetY n γ ω (j + 1)) := by
      refine ⟨⟨μ'.nonneg, μ'.sum_eq_one⟩, ⟨ν'.nonneg, ν'.sum_eq_one⟩,
        hμ'A, hν'B, ?_, ?_⟩
      · intro x
        exact (hμ'W x).trans (div_le_div_of_nonneg_right
          (Real.exp_le_exp.mpr hstepX) hNR.le)
      · intro y
        exact (hν'W y).trans (div_le_div_of_nonneg_right
          (Real.exp_le_exp.mpr hstepY) hNR.le)
    have hmax : rawDensity E G w' ≤ v (j + 1) := by
      dsimp [v]
      exact (M (j + 1)).maximal G w' hnext
    calc
      dens E G μ' ν' = rawDensity E G w' := by
        symm
        exact rawDensity_eq_dens E G w'
          ⟨μ'.nonneg, μ'.sum_eq_one⟩ ⟨ν'.nonneg, ν'.sum_eq_one⟩
      _ ≤ v (j + 1) := hmax
      _ ≤ p + b := hgap'


private noncomputable def massOn {N : ℕ} (ν : Law N) (S : Finset (Fin N)) : ℝ :=
  ∑ y ∈ S, ν.w y

private theorem sum_if_mem_div_eq {N : ℕ} (H : Finset (Fin N))
    (f : Fin N → ℝ) (m : ℝ) :
    (∑ y, if y ∈ H then f y / m else 0) = (∑ y ∈ H, f y) / m := by
  classical
  have hfilter : Finset.univ.filter (fun y : Fin N => y ∈ H) = H := by
    ext y
    simp
  rw [← Finset.sum_filter, hfilter, Finset.sum_div]

private theorem colDegree_eq_diracDensity {N : ℕ} (E : Fin N → Fin N → Prop)
    (G : Colour) (μ : Law N) (y : Fin N) :
    colDegree E G μ y = dens E G μ (Law.dirac y) := by
  classical
  unfold colDegree dens Law.dirac
  calc
    (∑ x, μ.w x * (if Hits E G x y then 1 else 0)) =
        ∑ x, ∑ z, μ.w x * (if z = y then 1 else 0) *
          (if Hits E G x z then 1 else 0) := by
      apply Finset.sum_congr rfl
      intro x hx
      symm
      calc
        (∑ z, μ.w x * (if z = y then 1 else 0) *
            (if Hits E G x z then 1 else 0)) =
          ∑ z, if z = y then μ.w x * (if Hits E G x z then 1 else 0) else 0 := by
            apply Finset.sum_congr rfl
            intro z hz
            by_cases h : z = y <;> simp [h] <;> ring
        _ = μ.w x * (if Hits E G x y then 1 else 0) := by
            simp [Finset.sum_ite_eq']

private theorem conditioned_density_eq {N : ℕ} (E : Fin N → Fin N → Prop)
    (G : Colour) (μ ν : Law N) (H : Finset (Fin N))
    (hH : 0 < massOn ν H) :
    dens E G μ (conditionedLaw ν H hH) =
      (∑ y ∈ H, ν.w y * dens E G μ (Law.dirac y)) / massOn ν H := by
  classical
  rw [dens_eq_sum_colDegree]
  calc
    (∑ y, (conditionedLaw ν H hH).w y * colDegree E G μ y) =
        ∑ y, if y ∈ H then (ν.w y * dens E G μ (Law.dirac y)) /
          massOn ν H else 0 := by
      apply Finset.sum_congr rfl
      intro y hy
      by_cases hyH : y ∈ H
      · simp [conditionedLaw, massOn, hyH, colDegree_eq_diracDensity]
        ring
      · simp [conditionedLaw, massOn, hyH]
    _ = (∑ y ∈ H, ν.w y * dens E G μ (Law.dirac y)) / massOn ν H :=
      sum_if_mem_div_eq H (fun y => ν.w y * dens E G μ (Law.dirac y)) (massOn ν H)

private theorem conditioned_average_gt {N : ℕ} (E : Fin N → Fin N → Prop)
    (G : Colour) (μ ν : Law N) (H : Finset (Fin N)) (r : ℝ)
    (hH : 0 < massOn ν H)
    (hdegree : ∀ y ∈ H, r < dens E G μ (Law.dirac y)) :
    r < dens E G μ (conditionedLaw ν H hH) := by
  classical
  have hexists : ∃ y ∈ H, 0 < ν.w y := by
    by_contra hno
    have hzero : ∀ y ∈ H, ν.w y = 0 := by
      intro y hy
      have hnot : ¬ 0 < ν.w y := by
        intro hypos
        exact hno ⟨y, hy, hypos⟩
      exact le_antisymm (le_of_not_gt hnot) (ν.nonneg y)
    have hmzero : massOn ν H = 0 := by
      unfold massOn
      apply Finset.sum_eq_zero
      intro y hy
      exact hzero y hy
    linarith
  obtain ⟨y₀, hy₀, hypos⟩ := hexists
  have hsumlt :
      (∑ y ∈ H, ν.w y) * r <
        ∑ y ∈ H, ν.w y * dens E G μ (Law.dirac y) := by
    rw [Finset.sum_mul]
    apply Finset.sum_lt_sum
    · intro y hy
      exact mul_le_mul_of_nonneg_left (le_of_lt (hdegree y hy)) (ν.nonneg y)
    · exact ⟨y₀, hy₀, mul_lt_mul_of_pos_left (hdegree y₀ hy₀) hypos⟩
  have hratio :
      r < (∑ y ∈ H, ν.w y * dens E G μ (Law.dirac y)) / massOn ν H :=
    (lt_div_iff₀ hH).2 (by simpa [massOn, mul_comm] using hsumlt)
  rw [conditioned_density_eq E G μ ν H hH]
  exact hratio


private theorem low_columns_mass_lt_half {N : ℕ} (E : Fin N → Fin N → Prop)
    (G : Colour) (μ ν : Law N) (p a b c : ℝ)
    (ha : 0 < a) (hb : 0 < b) (hp : 0 ≤ p) (hbc : b + c < a / 2)
    (hmean : dens E G μ ν = p)
    (hH : massOn ν (Finset.univ.filter
      fun y => p + b < dens E G μ (Law.dirac y)) ≤ c) :
    massOn ν (Finset.univ.filter fun y => dens E G μ (Law.dirac y) < p - a) < 1 / 2 := by
  classical
  let L := Finset.univ.filter fun y => dens E G μ (Law.dirac y) < p - a
  let H := Finset.univ.filter fun y => p + b < dens E G μ (Law.dirac y)
  let t := massOn ν L
  let u := massOn ν H
  have hdegree_le (y : Fin N) : dens E G μ (Law.dirac y) ≤ 1 :=
    (rawDensity_nonneg_le_one E G μ (Law.dirac y)).2
  have hdegree_mean : (∑ y, ν.w y * dens E G μ (Law.dirac y)) = p := by
    calc
      (∑ y, ν.w y * dens E G μ (Law.dirac y)) =
          ∑ y, ν.w y * colDegree E G μ y := by
        apply Finset.sum_congr rfl
        intro y hy
        rw [colDegree_eq_diracDensity]
      _ = dens E G μ ν := (dens_eq_sum_colDegree E G μ ν).symm
      _ = p := hmean
  have hpoint (y : Fin N) :
      dens E G μ (Law.dirac y) ≤
        p + b - (if y ∈ L then a else 0) + (if y ∈ H then 1 else 0) := by
    by_cases hyL : y ∈ L
    · have hlow := (Finset.mem_filter.mp hyL).2
      have hyH : y ∉ H := by
        intro hy
        have hhigh : p + b < dens E G μ (Law.dirac y) :=
          (Finset.mem_filter.mp hy).2
        linarith
      simp [hyL, hyH]
      linarith
    · by_cases hyH : y ∈ H
      · have hhigh := (Finset.mem_filter.mp hyH).2
        simp [hyL, hyH]
        linarith [hdegree_le y]
      · have hnotHigh : ¬ p + b < dens E G μ (Law.dirac y) := by
          intro hgt
          exact hyH (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hgt⟩)
        simp [hyL, hyH]
        exact le_of_not_gt hnotHigh
  have hsumUpper :
      (∑ y, ν.w y * dens E G μ (Law.dirac y)) ≤
        (∑ y, ν.w y) * (p + b) - t * a + u := by
    have hterm (y : Fin N) :
        ν.w y * (p + b - (if y ∈ L then a else 0) +
          (if y ∈ H then 1 else 0)) =
          ν.w y * (p + b) -
            ν.w y * (if y ∈ L then a else 0) +
            ν.w y * (if y ∈ H then 1 else 0) := by ring
    calc
      (∑ y, ν.w y * dens E G μ (Law.dirac y)) ≤
          ∑ y, ν.w y *
            (p + b - (if y ∈ L then a else 0) + (if y ∈ H then 1 else 0)) := by
        apply Finset.sum_le_sum
        intro y hy
        exact mul_le_mul_of_nonneg_left (hpoint y) (ν.nonneg y)
      _ = (∑ y, ν.w y * (p + b)) -
            (∑ y, ν.w y * (if y ∈ L then a else 0)) +
            (∑ y, ν.w y * (if y ∈ H then 1 else 0)) := by
        calc
          _ = ∑ y, (ν.w y * (p + b) -
                ν.w y * (if y ∈ L then a else 0) +
                ν.w y * (if y ∈ H then 1 else 0)) := by
              apply Finset.sum_congr rfl
              intro y hy
              exact hterm y
          _ = _ := by rw [Finset.sum_add_distrib, Finset.sum_sub_distrib]
      _ = (∑ y, ν.w y) * (p + b) - t * a + u := by
        have hc : (∑ y, ν.w y * (p + b)) = (∑ y, ν.w y) * (p + b) := by
          rw [← Finset.sum_mul]
        have hl : (∑ y, ν.w y * (if y ∈ L then a else 0)) = t * a := by
          dsimp [t, massOn, L]
          exact sum_mul_indicator _ _ _
        have hh : (∑ y, ν.w y * (if y ∈ H then (1 : ℝ) else 0)) = u := by
          dsimp [u, massOn]
          simpa using (sum_mul_indicator H ν.w (1 : ℝ))
        rw [hc, hl, hh]
  have hmeanUpper : p ≤ p + b - t * a + u := by
    calc
      p = ∑ y, ν.w y * dens E G μ (Law.dirac y) := hdegree_mean.symm
      _ ≤ (∑ y, ν.w y) * (p + b) - t * a + u := hsumUpper
      _ = p + b - t * a + u := by rw [ν.sum_eq_one]; ring
  by_contra hnot
  have ht : 1 / 2 ≤ t := le_of_not_gt hnot
  have hta' : (1 / 2) * a ≤ t * a := mul_le_mul_of_nonneg_right ht ha.le
  have hta : a / 2 ≤ t * a := by linarith
  have hu : u ≤ c := by simpa [u] using hH
  nlinarith


private theorem trim_low_columns {N : ℕ} (hNR : 0 < (N : ℝ))
    (E : Fin N → Fin N → Prop)
    (G : Colour) (A B : Finset (Fin N)) (μ ν : Law N)
    (p sY a b c : ℝ)
    (hmean : dens E G μ ν = p) (hνsupp : ν.SupportedIn B)
    (hνwidth : ν.WidthLE sY)
    (ha : 0 < a) (hb : 0 < b) (hp : 0 ≤ p)
    (hbc : b + c < a / 2)
    (hH : massOn ν (Finset.univ.filter
      fun y => p + b < dens E G μ (Law.dirac y)) ≤ c) :
    ∃ ν' : Law N, ν'.SupportedIn B ∧ ν'.WidthLE (sY + 1) ∧
      ∀ y, ν'.w y ≠ 0 → p - a ≤ dens E G μ (Law.dirac y) := by
  classical
  let lowCond := fun y : Fin N => dens E G μ (Law.dirac y) < p - a
  let L := Finset.univ.filter lowCond
  let R := Finset.univ.filter fun y => ¬ lowCond y
  have ht : massOn ν L < 1 / 2 :=
    low_columns_mass_lt_half E G μ ν p a b c ha hb hp hbc hmean hH
  have hsplit : massOn ν L + massOn ν R = 1 := by
    dsimp [massOn, L, R]
    rw [Finset.sum_filter_add_sum_filter_not (s := Finset.univ)
      (p := lowCond) (f := ν.w)]
    exact ν.sum_eq_one
  have hmassR : 1 / 2 < massOn ν R := by linarith
  have hmassRpos : 0 < massOn ν R := by linarith
  let ν' := conditionedLaw ν R hmassRpos
  have hInv : 1 / (massOn ν R) ≤ 2 := by
    calc
      1 / massOn ν R ≤ 1 / (1 / 2) :=
        one_div_le_one_div_of_le (by norm_num) (le_of_lt hmassR)
      _ = 2 := by norm_num
  have h2exp : 2 ≤ Real.exp 1 := by
    have h := Real.add_one_le_exp (1 : ℝ)
    nlinarith
  have hν'supp : ν'.SupportedIn B := by
    intro y hy
    by_cases hyR : y ∈ R
    · have hzero := hνsupp y hy
      simp [ν', conditionedLaw, hyR, hzero]
    · simp [ν', conditionedLaw, hyR]
  have hν'width : ν'.WidthLE (sY + 1) := by
    intro y
    by_cases hyR : y ∈ R
    · have hcap := hνwidth y
      have hcapPos : 0 ≤ Real.exp sY / N := div_nonneg (Real.exp_pos _).le hNR.le
      calc
        ν'.w y = ν.w y / massOn ν R := by simp [ν', conditionedLaw, hyR, massOn]
        _ ≤ (Real.exp sY / N) / massOn ν R :=
          div_le_div_of_nonneg_right hcap hmassRpos.le
        _ = (Real.exp sY / N) * (1 / massOn ν R) := by ring
        _ ≤ (Real.exp sY / N) * 2 :=
          mul_le_mul_of_nonneg_left hInv hcapPos
        _ ≤ (Real.exp sY / N) * Real.exp 1 :=
          mul_le_mul_of_nonneg_left h2exp hcapPos
        _ = Real.exp (sY + 1) / N := by rw [Real.exp_add]; ring
    · have hzero : ν'.w y = 0 := by simp [ν', conditionedLaw, hyR]
      rw [hzero]
      positivity
  have hν'local : ∀ y, ν'.w y ≠ 0 → p - a ≤ dens E G μ (Law.dirac y) := by
    intro y hy
    have hyR : y ∈ R := by
      by_contra hnot
      simp [ν', conditionedLaw, hnot] at hy
    have hyNotLow : ¬ dens E G μ (Law.dirac y) < p - a :=
      (Finset.mem_filter.mp hyR).2
    exact le_of_not_gt hyNotLow
  exact ⟨ν', hν'supp, hν'width, hν'local⟩


set_option maxHeartbeats 1000000 in
theorem l41a_proof (β γ : ℝ) (hβ : 0 < β) (hβγ : β ≤ γ) (hγ : γ < 1) :
    ∃ n₀ : ℕ, ∀ n ≥ n₀, ∀ N (E : Fin N → Fin N → Prop)
      (A B : Finset (Fin N)) (q : Law N × Law N),
      PBias (pw β) (pw γ) (h4 β γ) n N E q.1 q.2 →
      q.1.SupportedIn A → q.2.SupportedIn B →
      ∃ G : Colour, ∃ μ ν : Law N,
        PrepLaw β γ G n N E μ ν ∧ μ.SupportedIn A ∧ ν.SupportedIn B := by
  obtain ⟨n₀, hn₀⟩ := exists_plateau_threshold β γ hβ hβγ hγ
  refine ⟨n₀, ?_⟩
  intro n hn N E A B q hBias hμA hνB
  rcases hn₀ n hn with ⟨hn2, hω2, hω6, hω15, hω10⟩
  have hNpos : 0 < N := by
    by_contra h
    have hNzero : N = 0 := Nat.eq_zero_of_not_pos h
    subst N
    have hsum := q.1.sum_eq_one
    norm_num at hsum
  have hnR : 0 < (n : ℝ) := by exact_mod_cast (by omega : 0 < n)
  have hNR : 0 < (N : ℝ) := by exact_mod_cast hNpos
  have hω : 0 < omega4 β γ := omega4_pos β γ hβ hγ
  have hωγ := omega4_le_gamma_div β γ hβγ
  have hγlarge : omega4 β γ / 2 ≤ γ - omega4 β γ / 2 := by nlinarith
  obtain ⟨j, hjJ, G, μ, ν₀, p, hμsupport, hν₀support, hμwidth, hν₀width,
    hsxupper, hsyupper, hplower, hmean, hupper⟩ :=
      plateau_selected β γ hβ hβγ hγ hn2 hω6 (le_of_lt hω2) hNpos E A B q
        hBias hμA hνB
  let ω := omega4 β γ
  let sx := plateauBudgetX n β ω j
  let sy := plateauBudgetY n γ ω j
  let a := (n : ℝ) ^ (-(ω / 5))
  let b := (n : ℝ) ^ (-(ω / 3))
  let c := (n : ℝ) ^ (-(ω / 2))
  have haEq : a = (n : ℝ) ^ (-omega4 β γ / 5) := by
    dsimp [a, ω]
    congr 1
    ring
  have hbEq : b = (n : ℝ) ^ (-omega4 β γ / 3) := by
    dsimp [b, ω]
    congr 1
    ring
  have ha : 0 < a := by dsimp [a]; exact Real.rpow_pos_of_pos hnR _
  have hb : 0 < b := by dsimp [b]; exact Real.rpow_pos_of_pos hnR _
  have hc : 0 < c := by dsimp [c]; exact Real.rpow_pos_of_pos hnR _
  have hratioB : (n : ℝ) ^ (-(2 * ω / 15)) < 1 / 4 :=
    neg_rpow_lt_quarter (by exact_mod_cast (by omega : 1 ≤ n)) (2 * ω / 15) hω15
  have hratioC : (n : ℝ) ^ (-(3 * ω / 10)) < 1 / 4 :=
    neg_rpow_lt_quarter (by exact_mod_cast (by omega : 1 ≤ n)) (3 * ω / 10) hω10
  have hba : b = a * (n : ℝ) ^ (-(2 * ω / 15)) := by
    dsimp [a, b]
    calc
      (n : ℝ) ^ (-(ω / 3)) =
          (n : ℝ) ^ ((-(ω / 5)) + (-(2 * ω / 15))) := by
            rw [show (-(ω / 5)) + (-(2 * ω / 15)) = -(ω / 3) by ring]
      _ = (n : ℝ) ^ (-(ω / 5)) * (n : ℝ) ^ (-(2 * ω / 15)) :=
        Real.rpow_add hnR _ _
  have hca : c = a * (n : ℝ) ^ (-(3 * ω / 10)) := by
    dsimp [a, c]
    calc
      (n : ℝ) ^ (-(ω / 2)) =
          (n : ℝ) ^ ((-(ω / 5)) + (-(3 * ω / 10))) := by
            rw [show (-(ω / 5)) + (-(3 * ω / 10)) = -(ω / 2) by ring]
      _ = (n : ℝ) ^ (-(ω / 5)) * (n : ℝ) ^ (-(3 * ω / 10)) :=
        Real.rpow_add hnR _ _
  have hba' : b < a / 4 := by
    calc
      b = a * (n : ℝ) ^ (-(2 * ω / 15)) := hba
      _ < a * (1 / 4) := mul_lt_mul_of_pos_left hratioB ha
      _ = a / 4 := by ring
  have hca' : c < a / 4 := by
    calc
      c = a * (n : ℝ) ^ (-(3 * ω / 10)) := hca
      _ < a * (1 / 4) := mul_lt_mul_of_pos_left hratioC ha
      _ = a / 4 := by ring
  have hbc : b + c < a / 2 := by linarith
  have hpnonneg : 0 ≤ p := by
    have hpowpos : 0 < (n : ℝ) ^ (-h4 β γ) := Real.rpow_pos_of_pos hnR _
    linarith [hplower]
  let H : Finset (Fin N) :=
    Finset.univ.filter fun y => p + b < dens E G μ (Law.dirac y)
  have hHbound : massOn ν₀ H ≤ c := by
    by_contra hnot
    have hmassgt : c < massOn ν₀ H := lt_of_not_ge hnot
    have hmasspos : 0 < massOn ν₀ H := lt_trans hc hmassgt
    let νH := conditionedLaw ν₀ H hmasspos
    have hdegree : ∀ y ∈ H, p + b < dens E G μ (Law.dirac y) := by
      intro y hy
      exact (Finset.mem_filter.mp hy).2
    have hcond : p + b < dens E G μ νH :=
      conditioned_average_gt E G μ ν₀ H (p + b) hmasspos hdegree
    have hinv : 1 / massOn ν₀ H ≤ (n : ℝ) ^ (ω / 2) := by
      calc
        1 / massOn ν₀ H ≤ 1 / c :=
          one_div_le_one_div_of_le hc (le_of_lt hmassgt)
        _ = (n : ℝ) ^ (ω / 2) := by
          dsimp [c]
          rw [Real.rpow_neg hnR.le]
          simp
    have huNonneg : 0 ≤ (n : ℝ) ^ (γ - ω / 2) :=
      (Real.rpow_pos_of_pos hnR _).le
    have hpow : (n : ℝ) ^ (ω / 2) ≤ (n : ℝ) ^ (γ - ω / 2) :=
      Real.rpow_le_rpow_of_exponent_le (by exact_mod_cast (by omega : 1 ≤ n)) hγlarge
    have hquarter : 1 + ((n : ℝ) ^ (γ - ω / 2)) / 4 ≤
        Real.exp (((n : ℝ) ^ (γ - ω / 2)) / 4) := by
      have h := Real.add_one_le_exp (((n : ℝ) ^ (γ - ω / 2)) / 4)
      nlinarith
    have hquarterNonneg : 0 ≤ 1 + ((n : ℝ) ^ (γ - ω / 2)) / 4 := by positivity
    have hsq : (1 + ((n : ℝ) ^ (γ - ω / 2)) / 4) ^ 2 ≤
        Real.exp (((n : ℝ) ^ (γ - ω / 2)) / 2) := by
      calc
        (1 + ((n : ℝ) ^ (γ - ω / 2)) / 4) ^ 2 ≤
            (Real.exp (((n : ℝ) ^ (γ - ω / 2)) / 4)) ^ 2 :=
          by
            simpa [pow_two] using
              (mul_le_mul hquarter hquarter hquarterNonneg (Real.exp_pos _).le)
        _ = Real.exp (((n : ℝ) ^ (γ - ω / 2)) / 2) := by
          rw [show ((n : ℝ) ^ (γ - ω / 2)) / 2 =
            ((n : ℝ) ^ (γ - ω / 2)) / 4 + ((n : ℝ) ^ (γ - ω / 2)) / 4 by ring,
            Real.exp_add]
          ring
    have hquad : (n : ℝ) ^ (γ - ω / 2) ≤
        (1 + ((n : ℝ) ^ (γ - ω / 2)) / 4) ^ 2 := by
      nlinarith [sq_nonneg ((n : ℝ) ^ (γ - ω / 2) - 4)]
    have hexp : (n : ℝ) ^ (ω / 2) ≤
        Real.exp (((n : ℝ) ^ (γ - ω / 2)) / 2) :=
      hpow.trans (hquad.trans hsq)
    have hνHwidth : νH.WidthLE (sy + (n : ℝ) ^ (γ - ω / 2) / 2) := by
      intro y
      by_cases hyH : y ∈ H
      · have hcap := hν₀width y
        have hcapPos : 0 ≤ Real.exp sy / N := div_nonneg (Real.exp_pos _).le hNR.le
        calc
          νH.w y = ν₀.w y / massOn ν₀ H := by simp [νH, conditionedLaw, hyH, massOn]
          _ ≤ (Real.exp sy / N) / massOn ν₀ H :=
            div_le_div_of_nonneg_right hcap hmasspos.le
          _ = (Real.exp sy / N) * (1 / massOn ν₀ H) := by ring
          _ ≤ (Real.exp sy / N) * (n : ℝ) ^ (ω / 2) :=
            mul_le_mul_of_nonneg_left hinv hcapPos
          _ ≤ (Real.exp sy / N) * Real.exp (((n : ℝ) ^ (γ - ω / 2)) / 2) :=
            mul_le_mul_of_nonneg_left hexp hcapPos
          _ = Real.exp (sy + (n : ℝ) ^ (γ - ω / 2) / 2) / N := by
            rw [Real.exp_add]
            ring
      · have hz : νH.w y = 0 := by simp [νH, conditionedLaw, hyH]
        rw [hz]
        positivity
    have hνHsupport : νH.SupportedIn B := by
      intro y hy
      by_cases hyH : y ∈ H
      · have hz := hν₀support y hy
        simp [νH, conditionedLaw, hyH, hz]
      · simp [νH, conditionedLaw, hyH]
    have hμupper : μ.WidthLE (sx + (n : ℝ) ^ (β - ω / 2) / 2) := by
      intro x
      have hbudget : sx ≤ sx + (n : ℝ) ^ (β - ω / 2) / 2 :=
        le_add_of_nonneg_right
          (div_nonneg (Real.rpow_pos_of_pos hnR _).le (by norm_num))
      exact (hμwidth x).trans (div_le_div_of_nonneg_right
        (Real.exp_le_exp.mpr hbudget) hNR.le)
    have hplateau := hupper μ νH hμsupport hνHsupport hμupper hνHwidth
    have hplateau' : dens E G μ νH ≤ p + b := by
      simpa [hbEq] using hplateau
    exact (not_lt_of_ge hplateau') hcond
  obtain ⟨ν, hνsupport, hνwidth, hνlocal⟩ :=
    trim_low_columns hNR E G A B μ ν₀ p sy a b c hmean hν₀support hν₀width
      ha hb hpnonneg hbc hHbound
  refine ⟨G, μ, ν, ?_⟩
  refine ⟨?_, hμsupport, hνsupport⟩
  refine ⟨sx, sy, p, ?_⟩
  have hsxLower : (n : ℝ) ^ β ≤ sx := by
    dsimp [sx, plateauBudgetX]
    exact le_add_of_nonneg_right
      (mul_nonneg (Nat.cast_nonneg j) (Real.rpow_pos_of_pos hnR _).le)
  have hsyLower : (n : ℝ) ^ γ ≤ sy := by
    dsimp [sy, plateauBudgetY]
    exact le_add_of_nonneg_right
      (mul_nonneg (Nat.cast_nonneg j) (Real.rpow_pos_of_pos hnR _).le)
  refine ⟨hsxLower, ?_, hsyLower, ?_, hμwidth, hνwidth, hplower, ?_, ?_⟩
  · simpa [sx, ω] using hsxupper
  · simpa [sy, ω] using hsyupper
  · intro y hy
    have h := hνlocal y hy
    rw [haEq] at h
    exact h
  · intro μ' ν' hμkeep hνkeep hμ'width hν'width
    have hμ'A : μ'.SupportedIn A := by
      intro x hx
      apply hμkeep x
      exact hμsupport x hx
    have hν'B : ν'.SupportedIn B := by
      intro y hy
      apply hνkeep y
      exact hνsupport y hy
    exact hupper μ' ν' hμ'A hν'B hμ'width hν'width

end HypercubeRamsey
