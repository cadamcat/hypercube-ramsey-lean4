import HypercubeRamsey.S12.RowTrimming
import HypercubeRamsey.Framework.LawLemmas
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics

/-!
Lane-local imports for Section 13 cleaning proofs.
-/

namespace HypercubeRamsey.S13.Lane_q_s13_clean

open HypercubeRamsey
open Classical
open HypercubeRamsey.S12.Exceptional_q_s12_exc
open scoped BigOperators

/-- The exponential host scale eventually pays for a twelfth power and a quarter exponent. -/
theorem exp_quarter_dominates_pow12 (T : Stage) :
    ∀ᶠ k in Filter.atTop,
      (T.S.n k : ℝ) ^ 12 ≤ Real.exp ((T.S.n k : ℝ) / 4) := by
  have hnCast : Filter.Tendsto (fun k : ℕ => (T.S.n k : ℝ)) Filter.atTop Filter.atTop :=
    tendsto_natCast_atTop_atTop.comp T.S.n_tendsto
  have hscaled := hnCast.atTop_div_const (by norm_num : (0 : ℝ) < 4)
  have hratio := (tendsto_exp_div_rpow_atTop (12 : ℝ)).comp hscaled
  have hnPosEvent : ∀ᶠ k in Filter.atTop, 1 ≤ T.S.n k :=
    T.S.n_tendsto.eventually_ge_atTop 1
  filter_upwards [hratio.eventually (Filter.eventually_ge_atTop ((4 : ℝ) ^ 12)),
    hnPosEvent] with k hk hkN
  have hnR : 0 < (T.S.n k : ℝ) := by exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one hkN)
  have hden : 0 < Real.rpow ((T.S.n k : ℝ) / 4) (12 : ℝ) :=
    Real.rpow_pos_of_pos (div_pos hnR (by norm_num)) _
  change (4 : ℝ) ^ 12 ≤
    Real.exp ((T.S.n k : ℝ) / 4) /
      Real.rpow ((T.S.n k : ℝ) / 4) (12 : ℝ) at hk
  have hmul := (le_div_iff₀ hden).mp hk
  have hpow : (4 : ℝ) ^ 12 * Real.rpow ((T.S.n k : ℝ) / 4) (12 : ℝ) =
      (T.S.n k : ℝ) ^ 12 := by
    have hnat : Real.rpow ((T.S.n k : ℝ) / 4) (12 : ℝ) =
        ((T.S.n k : ℝ) / 4) ^ 12 := Real.rpow_natCast _ 12
    rw [hnat, div_pow]
    field_simp
  rw [hpow] at hmul
  exact hmul

def IsDisjointPack {α : Type*} [DecidableEq α]
    (P : Finset (Finset α)) : Prop :=
  ∀ A ∈ P, ∀ B ∈ P, A ≠ B → Disjoint A B

/-- Enumerate a finset by its cardinality. -/
noncomputable def finsetEnum {α : Type*} [DecidableEq α] (s : Finset α) :
    Fin s.card ≃ {x // x ∈ s} := s.equivFin.symm

/-- A maximal family of disjoint equal-size cliques leaves no clique in the complement. -/
theorem maximal_disjoint_clique_pack {α : Type*} [DecidableEq α]
    (X : Finset α) (m : ℕ) (hm : 0 < m) (R : α → α → Prop) :
    ∃ P : Finset (Finset α),
      P ⊆ X.powerset.filter (fun K => K.card = m ∧
        ∀ x ∈ K, ∀ y ∈ K, x ≠ y → R x y) ∧
      IsDisjointPack P ∧
      ∀ K ∈ X.powerset.filter (fun K => K.card = m ∧
        ∀ x ∈ K, ∀ y ∈ K, x ≠ y → R x y),
        ¬ K ⊆ X \ P.biUnion id := by
  classical
  let candidate : Finset α → Prop := fun K => K.card = m ∧
    ∀ x ∈ K, ∀ y ∈ K, x ≠ y → R x y
  letI : DecidablePred candidate := Classical.decPred _
  let Family : Finset (Finset α) := X.powerset.filter candidate
  letI : DecidablePred (fun P : Finset (Finset α) => IsDisjointPack P) := Classical.decPred _
  let Packs : Finset (Finset (Finset α)) :=
    Family.powerset.filter (fun P : Finset (Finset α) => IsDisjointPack P)
  have hPacks : Packs.Nonempty := by
    refine ⟨∅, ?_⟩
    change ∅ ∈ Family.powerset.filter (fun P : Finset (Finset α) => IsDisjointPack P)
    apply Finset.mem_filter.mpr
    constructor
    · simp
    · simp [IsDisjointPack]
  obtain ⟨P, hPmem, hPmax⟩ :=
    Finset.exists_max_image Packs (fun P => (P.biUnion id).card) hPacks
  have hPFamily : P ⊆ Family := Finset.mem_powerset.mp (Finset.mem_filter.mp hPmem).1
  have hPdisjoint : IsDisjointPack P := (Finset.mem_filter.mp hPmem).2
  refine ⟨P, ?_, hPdisjoint, ?_⟩
  · simpa [Family, candidate] using hPFamily
  · intro K hK hKsub
    have hKFamily : K ∈ Family := by simpa [Family, candidate] using hK
    have hKprops := (Finset.mem_filter.mp hKFamily).2
    have hKne : K.Nonempty := by
      apply Finset.card_pos.mp
      rw [hKprops.1]
      exact Nat.pos_of_ne_zero (by omega)
    have hKnotP : K ∉ P := by
      intro hKP
      obtain ⟨x, hx⟩ := hKne
      have hxUnion : x ∈ P.biUnion id := Finset.mem_biUnion.mpr ⟨K, hKP, hx⟩
      exact (Finset.mem_sdiff.mp (hKsub hx)).2 hxUnion
    have hKdisj : ∀ A ∈ P, Disjoint K A := by
      intro A hA
      apply Finset.disjoint_left.mpr
      intro x hxK hxA
      have hxUnion : x ∈ P.biUnion id := Finset.mem_biUnion.mpr ⟨A, hA, hxA⟩
      exact (Finset.mem_sdiff.mp (hKsub hxK)).2 hxUnion
    let P' := insert K P
    have hP'sub : P' ⊆ Family := by
      intro A hA
      rcases Finset.mem_insert.mp hA with rfl | hAP
      · exact hKFamily
      · exact hPFamily hAP
    have hP'disjoint : IsDisjointPack P' := by
      intro A hA B hB hne
      rcases Finset.mem_insert.mp hA with rfl | hAP
      · rcases Finset.mem_insert.mp hB with rfl | hBP
        · exact (hne rfl).elim
        · exact hKdisj B hBP
      · rcases Finset.mem_insert.mp hB with rfl | hBP
        · exact (hKdisj A hAP).symm
        · exact hPdisjoint A hAP B hBP hne
    have hP'mem : P' ∈ Packs := by
      apply Finset.mem_filter.mpr
      exact ⟨Finset.mem_powerset.mpr hP'sub, hP'disjoint⟩
    have hKunionDisj : Disjoint K (P.biUnion id) := by
      apply Finset.disjoint_left.mpr
      intro x hxK hxUnion
      rcases Finset.mem_biUnion.mp hxUnion with ⟨A, hA, hxA⟩
      exact (Finset.mem_sdiff.mp (hKsub hxK)).2 (Finset.mem_biUnion.mpr ⟨A, hA, hxA⟩)
    have hUnion : P'.biUnion id = K ∪ P.biUnion id := by
      simp [P']
    have hCardUnion : (P'.biUnion id).card = K.card + (P.biUnion id).card := by
      rw [hUnion, Finset.card_union_of_disjoint hKunionDisj]
    have hMax := hPmax P' hP'mem
    have hCardle : (P'.biUnion id).card ≤ (P.biUnion id).card := hMax
    rw [hCardUnion] at hCardle
    omega

/-- The admissible parameter choice makes the sampler's fixed logarithmic slack large. -/
theorem sampler_log_budget (κ : CConsts) (hκ : CConsts.Admissible κ) :
    200 ≤ Real.log (320000 / κ.a) := by
  have hP : 21000 ≤ κ.P := by
    have hp := hκ.P_big.2
    rw [hκ.Ac_eq] at hp
    norm_num at hp
    exact hp
  have hPpos : 0 < κ.P := by omega
  have hR : 1 ≤ κ.R := by
    rw [hκ.R_eq]
    have hp : 0 < κ.P ^ 2 := Nat.pow_pos hPpos
    omega
  have hL : 500 ≤ κ.L := by
    rw [hκ.L_eq]
    calc
      500 = 500 * 1 := by norm_num
      _ ≤ 500 * κ.R := Nat.mul_le_mul_left 500 hR
  have hLcast : (500 : ℝ) ≤ κ.L := by exact_mod_cast hL
  have hu : 10 ≤ (κ.u : ℝ) := by
    have hu' : 10 * (κ.L : ℝ) ^ 2 < (κ.u : ℝ) := by
      exact_mod_cast hκ.u_rng.2
    have hLsq : (500 : ℝ) ^ 2 ≤ (κ.L : ℝ) ^ 2 := by
      nlinarith [sq_nonneg ((κ.L : ℝ) - 500)]
    nlinarith [hu', hLsq]
  have hexpLe : -(10 * (κ.u : ℝ) + 100) ≤ -200 := by nlinarith [hu]
  have hpowLe : Real.rpow 2 (-(10 * (κ.u : ℝ) + 100)) ≤
      Real.rpow 2 (-200 : ℝ) :=
    Real.rpow_le_rpow_of_exponent_le (by norm_num) hexpLe
  have hpowPos : 0 < Real.rpow 2 (-200 : ℝ) :=
    Real.rpow_pos_of_pos (by norm_num) _
  have hξsmall : κ.ξ < Real.rpow 2 (-200 : ℝ) := by
    have hAlpha : κ.α ≤ 1 := by linarith [hκ.α_rng.2]
    calc
      κ.ξ < κ.α * Real.rpow 2 (-(10 * (κ.u : ℝ) + 100)) := hκ.ξ_rng.2
      _ ≤ 1 * Real.rpow 2 (-200 : ℝ) := by
        exact mul_le_mul hAlpha hpowLe
          (Real.rpow_nonneg (by norm_num) _) (by linarith [hκ.α_rng.1])
      _ = Real.rpow 2 (-200 : ℝ) := by ring
  have hξPos : 0 < κ.ξ := hκ.ξ_rng.1
  have hξsq : κ.ξ ^ 2 < (Real.rpow 2 (-200 : ℝ)) ^ 2 := by
    have hmul := mul_pos (sub_pos.mpr hξsmall) (add_pos hξPos hpowPos)
    nlinarith [hmul]
  have hpowSq : (Real.rpow 2 (-200 : ℝ)) ^ 2 = Real.rpow 2 (-400 : ℝ) := by
    calc
      (Real.rpow 2 (-200 : ℝ)) ^ 2 =
          Real.rpow (Real.rpow 2 (-200 : ℝ)) (2 : ℝ) := by
            rw [← Real.rpow_natCast]
            norm_num
      _ = Real.rpow 2 ((-200 : ℝ) * 2) :=
        (Real.rpow_mul (x := (2 : ℝ)) (by norm_num) (-200) 2).symm
      _ = Real.rpow 2 (-400 : ℝ) := by congr 1 <;> norm_num
  have hθsmall : κ.θ < Real.rpow 2 (-400 : ℝ) := by
    have h4pow : (1 : ℝ) ≤ (4 : ℝ) ^ (κ.u + 3) :=
      one_le_pow₀ (by norm_num)
    have hden : 1 ≤ 3 * (4 : ℝ) ^ (κ.u + 3) := by nlinarith [h4pow]
    have hfrac : κ.ξ ^ 2 / (3 * (4 : ℝ) ^ (κ.u + 3)) ≤ κ.ξ ^ 2 :=
      div_le_self (sq_nonneg κ.ξ) hden
    have hxiBound : κ.ξ ^ 2 ≤ Real.rpow 2 (-400 : ℝ) := by
      rw [← hpowSq]
      exact hξsq.le
    exact lt_of_lt_of_le hκ.θ_rng.2 (le_trans hfrac hxiBound)
  have haPos : 0 < κ.a := by rw [hκ.a_eq]; exact div_pos hκ.θ_rng.1 (by norm_num)
  have haSmall : κ.a < Real.rpow 2 (-400 : ℝ) := by
    rw [hκ.a_eq]
    have hθdiv : κ.θ / 100 < κ.θ := by nlinarith [hκ.θ_rng.1]
    exact lt_trans hθdiv hθsmall
  have hrecip : (Real.rpow 2 (-400 : ℝ))⁻¹ < κ.a⁻¹ :=
    by simpa [one_div] using one_div_lt_one_div_of_lt haPos haSmall
  have hpowInv : (Real.rpow 2 (-400 : ℝ))⁻¹ = Real.rpow 2 (400 : ℝ) := by
    have hneg : Real.rpow 2 (-400 : ℝ) =
        (Real.rpow 2 (400 : ℝ))⁻¹ :=
      Real.rpow_neg (x := (2 : ℝ)) (by norm_num) (400 : ℝ)
    calc
      (Real.rpow 2 (-400 : ℝ))⁻¹ = ((Real.rpow 2 (400 : ℝ))⁻¹)⁻¹ := by rw [hneg]
      _ = Real.rpow 2 (400 : ℝ) := by simp
  have hratio : Real.rpow 2 (400 : ℝ) ≤ 320000 / κ.a := by
    have hInv : Real.rpow 2 (400 : ℝ) < κ.a⁻¹ := by simpa [hpowInv] using hrecip
    calc
      Real.rpow 2 (400 : ℝ) ≤ κ.a⁻¹ := hInv.le
      _ ≤ 320000 * κ.a⁻¹ :=
        by
          simpa using mul_le_mul_of_nonneg_right (by norm_num : (1 : ℝ) ≤ 320000)
            (inv_nonneg.mpr haPos.le)
      _ = 320000 / κ.a := by rw [div_eq_mul_inv]
  have hlog : Real.log (Real.rpow 2 (400 : ℝ)) ≤ Real.log (320000 / κ.a) :=
    Real.log_le_log (Real.rpow_pos_of_pos (by norm_num) _) hratio
  have hlogRpow : Real.log (Real.rpow 2 (400 : ℝ)) =
      400 * Real.log 2 := Real.log_rpow (by norm_num : (0 : ℝ) < 2) (400 : ℝ)
  have hlog2 : (1 / 2 : ℝ) ≤ Real.log 2 := by
    have h := Real.one_sub_inv_le_log_of_pos (by norm_num : (0 : ℝ) < 2)
    norm_num at h ⊢
    exact h
  rw [hlogRpow] at hlog
  nlinarith [hlog, hlog2]

private theorem hit_abs_le_one {N : ℕ} (E : Fin N → Fin N → Prop)
    (c : Colour) (x y : Fin N) : |hit E c x y| ≤ 1 := by
  unfold hit
  split_ifs <;> norm_num

private theorem fv_abs_eq_one {N : ℕ} (E : Fin N → Fin N → Prop)
    (c : Colour) (x y : Fin N) : |fv E c x y| = 1 := by
  unfold fv hit
  split_ifs <;> norm_num

theorem corr_color_eq {N : ℕ} (E : Fin N → Fin N → Prop)
    (c : Colour) (w : Fin N → ℝ) (x z : Fin N) :
    corr E c w x z = corr E true w x z := by
  by_cases hc : c = true
  · subst c
    rfl
  · have hc' : c = false := by cases c <;> simp_all
    subst c
    simp only [corr]
    apply Finset.sum_congr rfl
    intro y hy
    by_cases hxy : E x y <;> by_cases hzy : E z y <;>
      simp [fv, hit, Hits, hxy, hzy] <;> ring

/-- Degree changes by at most the entrywise `l1` change in the law. -/
theorem deg_l1 {N : ℕ} (E : Fin N → Fin N → Prop) (c : Colour)
    (μ ν : Law N) (x : Fin N) {ε : ℝ}
    (hε : (∑ y, |μ.w y - ν.w y|) ≤ ε) :
    |deg E c μ.w x - deg E c ν.w x| ≤ ε := by
  have hEq : deg E c μ.w x - deg E c ν.w x =
      ∑ y, (μ.w y - ν.w y) * hit E c x y := by
    simp only [deg]
    rw [← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro y hy
    ring
  calc
    |deg E c μ.w x - deg E c ν.w x| =
        |∑ y, (μ.w y - ν.w y) * hit E c x y| := by rw [hEq]
    _ ≤ ∑ y, |(μ.w y - ν.w y) * hit E c x y| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ y, |μ.w y - ν.w y| := by
      apply Finset.sum_le_sum
      intro y hy
      rw [abs_mul]
      exact mul_le_of_le_one_right (abs_nonneg _) (hit_abs_le_one E c x y)
    _ ≤ ε := hε

/-- Pair correlation changes by at most the entrywise `l1` change in the law. -/
theorem corr_l1 {N : ℕ} (E : Fin N → Fin N → Prop) (c : Colour)
    (μ ν : Law N) (x z : Fin N) {ε : ℝ}
    (hε : (∑ y, |μ.w y - ν.w y|) ≤ ε) :
    |corr E c μ.w x z - corr E c ν.w x z| ≤ ε := by
  have hEq : corr E c μ.w x z - corr E c ν.w x z =
      ∑ y, (μ.w y - ν.w y) * (fv E c x y * fv E c z y) := by
    simp only [corr]
    rw [← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro y hy
    ring
  have hprod (y : Fin N) : |fv E c x y * fv E c z y| = 1 := by
    rw [abs_mul, fv_abs_eq_one, fv_abs_eq_one]
    norm_num
  calc
    |corr E c μ.w x z - corr E c ν.w x z| =
        |∑ y, (μ.w y - ν.w y) * (fv E c x y * fv E c z y)| := by rw [hEq]
    _ ≤ ∑ y, |(μ.w y - ν.w y) * (fv E c x y * fv E c z y)| :=
      Finset.abs_sum_le_sum_abs _ _
    _ = ∑ y, |μ.w y - ν.w y| := by
      apply Finset.sum_congr rfl
      intro y hy
      rw [abs_mul, hprod]
      ring
    _ ≤ ε := hε

/-- Degree into a uniform core law is the ordinary average over its support. -/
theorem deg_unifCore {N : ℕ} (E : Fin N → Fin N → Prop) (c : Colour)
    (A : Finset (Fin N)) (hA : A.Nonempty) (x : Fin N) :
    deg E c (Law.unifCore A hA).w x =
      (∑ y ∈ A, hit E c x y) / A.card := by
  classical
  have hcard : (A.card : ℝ) ≠ 0 := by
    exact_mod_cast (Finset.card_pos.mpr hA).ne'
  calc
    deg E c (Law.unifCore A hA).w x =
        ∑ y ∈ A, (A.card : ℝ)⁻¹ * hit E c x y := by
      simp [deg, Law.unifCore]
    _ = (A.card : ℝ)⁻¹ * ∑ y ∈ A, hit E c x y := by
      rw [Finset.mul_sum]
    _ = (∑ y ∈ A, hit E c x y) / A.card := by
      rw [div_eq_mul_inv]
      ring

/-- Degrees against a law lie in the unit interval. -/
theorem deg_bounds {N : ℕ} (E : Fin N → Fin N → Prop) (c : Colour)
    (μ : Law N) (x : Fin N) : 0 ≤ deg E c μ.w x ∧ deg E c μ.w x ≤ 1 := by
  have hhit (y : Fin N) : 0 ≤ hit E c x y ∧ hit E c x y ≤ 1 := by
    unfold hit
    split_ifs <;> norm_num
  constructor
  · unfold deg
    apply Finset.sum_nonneg
    intro y hy
    exact mul_nonneg (μ.nonneg y) (hhit y).1
  · unfold deg
    calc
      (∑ y, μ.w y * hit E c x y) ≤ ∑ y, μ.w y * 1 := by
        apply Finset.sum_le_sum
        intro y hy
        exact mul_le_mul_of_nonneg_left (hhit y).2 (μ.nonneg y)
      _ = 1 := by simp [μ.sum_eq_one]

/-- A host of size at most `n 2^n` fits the sampler's finite test-count budget. -/
theorem host_test_count {n N : ℕ} (hn : 1 ≤ n) (hN : N ≤ n * 2 ^ n) :
    N ≤ Nat.ceil (Real.exp (2 * (n : ℝ))) * n ^ 4 := by
  have h2exp : (2 : ℝ) ≤ Real.exp 2 := by
    have h := Real.add_one_le_exp (2 : ℝ)
    nlinarith
  have hpow : (2 : ℝ) ^ n ≤ (Real.exp 2) ^ n := by
    gcongr
  have hexp : (2 : ℝ) ^ n ≤ Real.exp (2 * (n : ℝ)) := by
    calc
      (2 : ℝ) ^ n ≤ (Real.exp 2) ^ n := hpow
      _ = Real.exp ((n : ℝ) * 2) := (Real.exp_nat_mul 2 n).symm
      _ = Real.exp (2 * (n : ℝ)) := by congr 1 <;> ring
  have hceil : 2 ^ n ≤ Nat.ceil (Real.exp (2 * (n : ℝ))) := by
    exact_mod_cast le_trans hexp (Nat.le_ceil _)
  have hn3 : 1 ≤ n ^ 3 := by
    rw [← Nat.sub_add_cancel hn]
    exact Nat.one_le_pow' 3 (n - 1)
  have hn4 : n ≤ n ^ 4 := by
    calc
      n = n * 1 := by simp
      _ ≤ n * n ^ 3 := Nat.mul_le_mul_left _ hn3
      _ = n ^ 4 := by ring
  calc
    N ≤ n * 2 ^ n := hN
    _ ≤ n ^ 4 * 2 ^ n := Nat.mul_le_mul_right _ hn4
    _ ≤ n ^ 4 * Nat.ceil (Real.exp (2 * (n : ℝ))) :=
      Nat.mul_le_mul_left _ hceil
    _ = Nat.ceil (Real.exp (2 * (n : ℝ))) * n ^ 4 := Nat.mul_comm _ _

/-- The full `N²` family of pair-correlation tests fits the uniform sampler's cap. -/
theorem host_pair_test_count {n N : ℕ} (hn : 1 ≤ n) (hN : N ≤ n * 2 ^ n) :
    N ^ 2 ≤ Nat.ceil (Real.exp (2 * (n : ℝ))) * n ^ 4 := by
  have hExp1 : (2 : ℝ) ≤ Real.exp 1 := by
    have h := Real.add_one_le_exp (1 : ℝ)
    nlinarith [h]
  have hExp2 : Real.exp 1 ^ 2 = Real.exp 2 := by
    calc
      Real.exp 1 ^ 2 = Real.exp ((2 : ℝ) * 1) := (Real.exp_nat_mul 1 2).symm
      _ = Real.exp 2 := by norm_num
  have hExp2Lower : (4 : ℝ) ≤ Real.exp 2 := by
    rw [← hExp2]
    nlinarith [hExp1]
  have hpow : (4 : ℝ) ^ n ≤ (Real.exp 2) ^ n := by gcongr
  have hexp : (4 : ℝ) ^ n ≤ Real.exp (2 * (n : ℝ)) := by
    calc
      (4 : ℝ) ^ n ≤ (Real.exp 2) ^ n := hpow
      _ = Real.exp ((n : ℝ) * 2) := (Real.exp_nat_mul 2 n).symm
      _ = Real.exp (2 * (n : ℝ)) := by congr 1 <;> ring
  have hceil : 4 ^ n ≤ Nat.ceil (Real.exp (2 * (n : ℝ))) := by
    exact_mod_cast le_trans hexp (Nat.le_ceil _)
  have hNreal : (N : ℝ) ≤ (n : ℝ) * (2 : ℝ) ^ n := by exact_mod_cast hN
  have hN2real : (N : ℝ) ^ 2 ≤ (n : ℝ) ^ 2 * (4 : ℝ) ^ n := by
    have hsq := mul_self_le_mul_self (Nat.cast_nonneg N) hNreal
    have hpowSq : ((2 : ℝ) ^ n) ^ 2 = (4 : ℝ) ^ n := by
      calc
        ((2 : ℝ) ^ n) ^ 2 = (2 : ℝ) ^ n * (2 : ℝ) ^ n := by rw [pow_two]
        _ = ((2 : ℝ) * 2) ^ n := (mul_pow 2 2 n).symm
        _ = (4 : ℝ) ^ n := by norm_num
    have hsq' : (N : ℝ) ^ 2 ≤ ((n : ℝ) * (2 : ℝ) ^ n) ^ 2 := by
      simpa [pow_two] using hsq
    have hExpand : ((n : ℝ) * (2 : ℝ) ^ n) ^ 2 =
        (n : ℝ) ^ 2 * (4 : ℝ) ^ n := by
      rw [mul_pow, hpowSq]
    exact hsq'.trans_eq hExpand
  have hN2 : N ^ 2 ≤ n ^ 2 * 4 ^ n := by exact_mod_cast hN2real
  have hn2le : n ^ 2 ≤ n ^ 4 := by
    have hpowOne : 1 ≤ n ^ 2 := by
      exact one_le_pow₀ (by omega)
    calc
      n ^ 2 = n ^ 2 * 1 := by simp
      _ ≤ n ^ 2 * n ^ 2 := Nat.mul_le_mul_left _ hpowOne
      _ = n ^ 4 := by ring
  calc
    N ^ 2 ≤ n ^ 2 * 4 ^ n := hN2
    _ ≤ n ^ 4 * 4 ^ n := Nat.mul_le_mul_right _ hn2le
    _ ≤ n ^ 4 * Nat.ceil (Real.exp (2 * (n : ℝ))) :=
      Nat.mul_le_mul_left _ hceil
    _ = Nat.ceil (Real.exp (2 * (n : ℝ))) * n ^ 4 := Nat.mul_comm _ _

/-- A uniform core law has the logarithmic width of its support. -/
theorem unifCore_width {N : ℕ} (A : Finset (Fin N)) (hA : A.Nonempty) :
    (Law.unifCore A hA).WidthLE (Real.log ((N : ℝ) / A.card)) := by
  have hN : 0 < (N : ℝ) := by
    obtain ⟨x, hx⟩ := hA
    exact_mod_cast Nat.lt_of_le_of_lt (Nat.zero_le x.val) x.isLt
  have hcard : 0 < (A.card : ℝ) := by exact_mod_cast Finset.card_pos.mpr hA
  intro x
  by_cases hx : x ∈ A
  · have hweight : (Law.unifCore A hA).w x = (A.card : ℝ)⁻¹ := by
      simp [Law.unifCore, hx]
    rw [hweight, Real.exp_log (div_pos hN hcard)]
    field_simp [ne_of_gt hN, ne_of_gt hcard]
    norm_num
  · have hweight : (Law.unifCore A hA).w x = 0 := by
      simp [Law.unifCore, hx]
    rw [hweight]
    positivity

/-- A uniform core expectation is the average over its support. -/
theorem unifCore_expect {N : ℕ} (A : Finset (Fin N)) (hA : A.Nonempty)
    (f : Fin N → ℝ) :
    (Law.unifCore A hA).expect f = (∑ x ∈ A, f x) / A.card := by
  classical
  have hcard : (A.card : ℝ) ≠ 0 := by
    exact_mod_cast (Finset.card_pos.mpr hA).ne'
  calc
    (Law.unifCore A hA).expect f =
        ∑ x, (if x ∈ A then (A.card : ℝ)⁻¹ else 0) * f x := rfl
    _ = ∑ x, if x ∈ A then (A.card : ℝ)⁻¹ * f x else 0 := by
      apply Finset.sum_congr rfl
      intro x hx
      by_cases h : x ∈ A <;> simp [h]
    _ = ∑ x ∈ A, (A.card : ℝ)⁻¹ * f x := by
      rw [← Finset.sum_filter]
      simp
    _ = (A.card : ℝ)⁻¹ * ∑ x ∈ A, f x := by
      rw [Finset.mul_sum]
    _ = (∑ x ∈ A, f x) / A.card := by
      rw [div_eq_mul_inv]
      ring

/-- Correlation is twice the expectation of its `[0,1]` shifted pair test, minus one. -/
theorem corr_expect_shift {N : ℕ} (E : Fin N → Fin N → Prop) (μ : Law N)
    (y z : Fin N) :
    corr E true μ.w y z =
      2 * μ.expect (fun x => (fv E true x y * fv E true x z + 1) / 2) - 1 := by
  classical
  let f : Fin N → ℝ := fun x => (fv E true x y * fv E true x z + 1) / 2
  have hsum :
      2 * (∑ x, μ.w x * f x) =
        (∑ x, μ.w x * (fv E true x y * fv E true x z)) + 1 := by
    calc
      2 * (∑ x, μ.w x * f x) =
          ∑ x, 2 * (μ.w x * f x) := by rw [Finset.mul_sum]
      _ = ∑ x, (μ.w x * (fv E true x y * fv E true x z) + μ.w x) := by
        apply Finset.sum_congr rfl
        intro x hx
        dsimp [f]
        ring
      _ = (∑ x, μ.w x * (fv E true x y * fv E true x z)) + ∑ x, μ.w x := by
        rw [Finset.sum_add_distrib]
      _ = (∑ x, μ.w x * (fv E true x y * fv E true x z)) + 1 := by
        rw [μ.sum_eq_one]
  rw [corr, FinProb.expect]
  linarith [hsum]

/-- The internal slice counts fit below any admissible integer height. -/
theorem slice_bounds_by_height (κ : CConsts) (hκ : CConsts.Admissible κ)
    (h : ℕ) (hh : 1 ≤ h) : sliceK κ h ≤ h ∧ sliceT κ h ≤ h := by
  have hMhi : 1 ≤ κ.Mhi := by
    have hterm : 0 < (10 : ℝ) / κ.cq := div_pos (by norm_num) hκ.cq_rng.1
    have hpos : (0 : ℝ) < κ.Mhi := by
      have := hκ.Mhi_big.1
      have hMlo : (0 : ℝ) ≤ κ.Mlo := Nat.cast_nonneg _
      nlinarith
    exact Nat.one_le_iff_ne_zero.mpr (by
      intro hzero
      simp [hzero] at hpos)
  have hωM : 0 ≤ κ.ω * κ.Mhi :=
    mul_nonneg hκ.ω_rng.1.le (Nat.cast_nonneg _)
  have hωsmall : 3 * κ.ω ≤ 1 := by
    have hω5 : 5 * κ.ω ≤ 5 * κ.ω * κ.Mhi := by
      have hfactor : (1 : ℝ) ≤ κ.Mhi := by exact_mod_cast hMhi
      have hCoeff : (0 : ℝ) ≤ 5 * κ.ω :=
        mul_nonneg (by norm_num : (0 : ℝ) ≤ (5 : ℝ)) hκ.ω_rng.1.le
      calc
        5 * κ.ω = 5 * κ.ω * 1 := by ring
        _ ≤ 5 * κ.ω * κ.Mhi :=
          mul_le_mul_of_nonneg_left hfactor hCoeff
    have hA : κ.aC < (1 / 10 ^ 6 : ℝ) := by
      have hmin : min κ.η0 1 ≤ 1 := min_le_right _ _
      have hbound := hκ.aC_rng.2
      have hbound' : min κ.η0 1 / 10 ^ 6 ≤ 1 / 10 ^ 6 :=
        div_le_div_of_nonneg_right hmin (by norm_num)
      exact lt_of_lt_of_le hbound hbound'
    have hω : 5 * κ.ω < 1 / 100000000 := by
      exact lt_of_le_of_lt hω5 (lt_of_lt_of_le hκ.ω_rng.2 (by nlinarith [hA]))
    nlinarith
  have hωle : κ.ω ≤ 1 := by nlinarith [hωsmall]
  have hhR : (1 : ℝ) ≤ h := by exact_mod_cast hh
  constructor
  · unfold sliceK
    apply Nat.ceil_le.mpr
    calc
      Real.rpow (h : ℝ) (3 * κ.ω) ≤ Real.rpow (h : ℝ) 1 :=
        Real.rpow_le_rpow_of_exponent_le hhR hωsmall
      _ = h := Real.rpow_one _
  · unfold sliceT
    apply Nat.ceil_le.mpr
    calc
      Real.rpow (h : ℝ) κ.ω ≤ Real.rpow (h : ℝ) 1 :=
        Real.rpow_le_rpow_of_exponent_le hhR hωle
      _ = h := Real.rpow_one _

/-- Direct clique scales dominate the powered mass loss once the extracted scale is large. -/
theorem direct_clique_power_gap {g M1 Q aB aC : ℝ}
    (hM1 : 4 ≤ M1) (hM1G : M1 ≤ g) (haB : 0 < aB) (haBOne : aB ≤ 1)
    (hGap : aB < aC / 1000) (hg : 0 < g)
    (hMassPower : 200 ≤ Real.rpow g aB)
    (hQ : g / (2 * Real.sqrt M1) ≤ Q) :
    2 * Real.rpow g aB ≤ Real.rpow Q aC := by
  have hM1pos : 0 < M1 := by linarith
  have hSMpos : 0 < Real.sqrt M1 := Real.sqrt_pos.2 hM1pos
  have hSGpos : 0 < Real.sqrt g := Real.sqrt_pos.2 hg
  have hSMle : Real.sqrt M1 ≤ Real.sqrt g := Real.sqrt_le_sqrt hM1G
  have hSGsq : (Real.sqrt g) ^ 2 = g := Real.sq_sqrt hg.le
  have hQlower : Real.sqrt g / 2 ≤ Q := by
    have htemp : Real.sqrt g / 2 ≤ g / (2 * Real.sqrt M1) := by
      apply (div_le_div_iff₀ (by norm_num : (0 : ℝ) < 2)
        (mul_pos (by norm_num) hSMpos)).2
      have hmul := mul_le_mul_of_nonneg_left hSMle
        (mul_nonneg (by norm_num : (0 : ℝ) ≤ 2) (Real.sqrt_nonneg g))
      nlinarith [hmul, hSGsq]
    exact htemp.trans hQ
  have hg16 : 16 ≤ g := by
    by_contra hnot
    have hg' : g < 16 := lt_of_not_ge hnot
    have hpowg : Real.rpow g aB ≤ Real.rpow 16 aB :=
      Real.rpow_le_rpow hg.le hg'.le haB.le
    have hpow16 : Real.rpow (16 : ℝ) aB ≤ 16 := by
      calc
        Real.rpow 16 aB ≤ Real.rpow 16 1 :=
          Real.rpow_le_rpow_of_exponent_le (by norm_num) haBOne
        _ = 16 := Real.rpow_one _
    linarith
  have hroot4 : 4 ≤ Real.sqrt g := Real.le_sqrt_of_sq_le (by nlinarith [hg16])
  have hroot2 : 2 ≤ Real.sqrt (Real.sqrt g) :=
    Real.le_sqrt_of_sq_le (by nlinarith [hroot4])
  have hSGroot : Real.sqrt g = Real.rpow g (1 / 2 : ℝ) := Real.sqrt_eq_rpow _
  have hNestedRoot : Real.sqrt (Real.sqrt g) = Real.rpow g (1 / 4 : ℝ) := by
    calc
      Real.sqrt (Real.sqrt g) = Real.rpow (Real.sqrt g) (1 / 2 : ℝ) :=
        Real.sqrt_eq_rpow _
      _ = Real.rpow (Real.rpow g (1 / 2 : ℝ)) (1 / 2 : ℝ) := by
        rw [hSGroot]
      _ = Real.rpow g ((1 / 2 : ℝ) * (1 / 2 : ℝ)) :=
        (Real.rpow_mul hg.le _ _).symm
      _ = Real.rpow g (1 / 4 : ℝ) := by congr 1 <;> norm_num
  have hrootToQ : Real.sqrt (Real.sqrt g) ≤ Q := by
    have hsq := Real.sq_sqrt (Real.sqrt_nonneg g)
    have hprod := mul_nonneg (Real.sqrt_nonneg (Real.sqrt g))
      (sub_nonneg.mpr (by linarith [hroot2]))
    have hle : Real.sqrt (Real.sqrt g) ≤ Real.sqrt g / 2 := by nlinarith [hprod, hsq]
    exact hle.trans hQlower
  have hQpow : Real.rpow (Real.sqrt (Real.sqrt g)) aC ≤ Real.rpow Q aC :=
    Real.rpow_le_rpow (Real.sqrt_nonneg _) hrootToQ (le_of_lt (by linarith : 0 < aC))
  have hNestedPow : Real.rpow (Real.sqrt (Real.sqrt g)) aC =
      Real.rpow g (aC / 4) := by
    rw [hNestedRoot]
    have hmul := Real.rpow_mul hg.le (1 / 4 : ℝ) aC
    have hexp : (1 / 4 : ℝ) * aC = aC / 4 := by ring
    rw [hexp] at hmul
    exact hmul.symm
  have hExponent : 2 * aB ≤ aC / 4 := by nlinarith [hGap, haB]
  have hpowMono : Real.rpow g (2 * aB) ≤ Real.rpow g (aC / 4) :=
    Real.rpow_le_rpow_of_exponent_le (by linarith [hg]) hExponent
  have hpowSquare : Real.rpow g (2 * aB) = (Real.rpow g aB) ^ 2 := by
    have hmul := Real.rpow_add hg aB aB
    have hexp : aB + aB = 2 * aB := by ring
    simpa [pow_two, hexp] using hmul
  have hSquareLarge : 2 * Real.rpow g aB ≤ Real.rpow g (2 * aB) := by
    rw [hpowSquare]
    nlinarith [hMassPower]
  calc
    2 * Real.rpow g aB ≤ Real.rpow g (2 * aB) := hSquareLarge
    _ ≤ Real.rpow g (aC / 4) := hpowMono
    _ = Real.rpow (Real.sqrt (Real.sqrt g)) aC := hNestedPow.symm
    _ ≤ Real.rpow Q aC := hQpow

/-- Cluster slice sizes are controlled by the patch scale's small power. -/
theorem slice_product_cluster_bound (κ : CConsts) (hκ : CConsts.Admissible κ)
    (q h : ℕ) (hq : 1 ≤ q) (hh : 1 ≤ h)
    (hUpper : (h : ℝ) < 2 * Real.rpow (q : ℝ) κ.Mhi) :
    (sliceK κ h : ℝ) * sliceT κ h ≤
      8 * Real.rpow (q : ℝ) (4 * κ.ω * κ.Mhi) := by
  have hqR : (1 : ℝ) ≤ q := by exact_mod_cast hq
  have hhR : (1 : ℝ) ≤ h := by exact_mod_cast hh
  have hKupper : (sliceK κ h : ℝ) < Real.rpow (h : ℝ) (3 * κ.ω) + 1 := by
    unfold sliceK
    exact Nat.ceil_lt_add_one (Real.rpow_nonneg (Nat.cast_nonneg _) _)
  have hTupper : (sliceT κ h : ℝ) < Real.rpow (h : ℝ) κ.ω + 1 := by
    unfold sliceT
    exact Nat.ceil_lt_add_one (Real.rpow_nonneg (Nat.cast_nonneg _) _)
  have hktBound : (sliceK κ h : ℝ) * sliceT κ h ≤
      4 * Real.rpow (h : ℝ) (4 * κ.ω) := by
    have hω : 0 < κ.ω := hκ.ω_rng.1
    have hpow1 : 1 ≤ Real.rpow (h : ℝ) κ.ω := Real.one_le_rpow hhR hω.le
    have hA : Real.rpow (h : ℝ) κ.ω ≤ Real.rpow (h : ℝ) (3 * κ.ω) := by
      apply Real.rpow_le_rpow_of_exponent_le hhR
      linarith [hω.le]
    have hprod : (Real.rpow (h : ℝ) (3 * κ.ω) + 1) *
        (Real.rpow (h : ℝ) κ.ω + 1) ≤ 4 * Real.rpow (h : ℝ) (4 * κ.ω) := by
      have hpow4 : Real.rpow (h : ℝ) (3 * κ.ω) * Real.rpow (h : ℝ) κ.ω =
          Real.rpow (h : ℝ) (4 * κ.ω) := by
        calc
          Real.rpow (h : ℝ) (3 * κ.ω) * Real.rpow (h : ℝ) κ.ω =
              Real.rpow (h : ℝ) (3 * κ.ω + κ.ω) := by
            exact (Real.rpow_add (by exact_mod_cast (Nat.lt_of_lt_of_le Nat.zero_lt_one hh))
              (3 * κ.ω) κ.ω).symm
          _ = Real.rpow (h : ℝ) (4 * κ.ω) := by congr 1 <;> ring
      have hK : Real.rpow (h : ℝ) (3 * κ.ω) ≤ Real.rpow (h : ℝ) (4 * κ.ω) := by
        apply Real.rpow_le_rpow_of_exponent_le hhR
        linarith [hω.le]
      have hT : Real.rpow (h : ℝ) κ.ω ≤ Real.rpow (h : ℝ) (4 * κ.ω) := by
        apply Real.rpow_le_rpow_of_exponent_le hhR
        linarith [hω.le]
      have hOne : (1 : ℝ) ≤ Real.rpow (h : ℝ) (4 * κ.ω) := by
        apply Real.one_le_rpow hhR
        positivity
      calc
        (Real.rpow (h : ℝ) (3 * κ.ω) + 1) *
            (Real.rpow (h : ℝ) κ.ω + 1) =
          Real.rpow (h : ℝ) (3 * κ.ω) * Real.rpow (h : ℝ) κ.ω +
            Real.rpow (h : ℝ) (3 * κ.ω) + Real.rpow (h : ℝ) κ.ω + 1 := by ring
        _ ≤ Real.rpow (h : ℝ) (4 * κ.ω) + Real.rpow (h : ℝ) (4 * κ.ω) +
            Real.rpow (h : ℝ) (4 * κ.ω) + Real.rpow (h : ℝ) (4 * κ.ω) := by
          rw [hpow4]
          exact add_le_add (add_le_add (add_le_add le_rfl hK) hT) hOne
        _ = 4 * Real.rpow (h : ℝ) (4 * κ.ω) := by ring
    have hmul := mul_le_mul hKupper.le hTupper.le (Nat.cast_nonneg _) 
      (add_nonneg (Real.rpow_nonneg (Nat.cast_nonneg _) _) (by norm_num))
    calc
      (sliceK κ h : ℝ) * sliceT κ h ≤
          (Real.rpow (h : ℝ) (3 * κ.ω) + 1) * (Real.rpow (h : ℝ) κ.ω + 1) := hmul
      _ ≤ 4 * Real.rpow (h : ℝ) (4 * κ.ω) := hprod
  have homegaSmall : 4 * κ.ω * κ.Mhi < κ.aC / 100 := by
    have hωM := hκ.ω_rng.2
    have hωMpos : 0 ≤ κ.ω * κ.Mhi :=
      mul_nonneg hκ.ω_rng.1.le (Nat.cast_nonneg _)
    have hfour : 4 * κ.ω * κ.Mhi ≤ 5 * κ.ω * κ.Mhi := by nlinarith only [hωMpos]
    exact lt_of_le_of_lt hfour hωM
  have hHpow : Real.rpow (h : ℝ) (4 * κ.ω) ≤
      Real.rpow (2 * Real.rpow (q : ℝ) κ.Mhi) (4 * κ.ω) := by
    have hBaseNonneg : 0 ≤ 2 * Real.rpow (q : ℝ) κ.Mhi :=
      mul_nonneg (by norm_num) (Real.rpow_nonneg (Nat.cast_nonneg _) _)
    have hexpNonneg : 0 ≤ 4 * κ.ω := mul_nonneg (by norm_num) hκ.ω_rng.1.le
    exact Real.rpow_le_rpow (Nat.cast_nonneg _) hUpper.le hexpNonneg
  have hHpow' : Real.rpow (2 * Real.rpow (q : ℝ) κ.Mhi) (4 * κ.ω) ≤
      2 * Real.rpow (q : ℝ) (4 * κ.ω * κ.Mhi) := by
    have htwo : Real.rpow 2 (4 * κ.ω) ≤ 2 := by
      have hMhi : (1 : ℝ) ≤ κ.Mhi := by
        have h := hκ.Mhi_big.1
        have hterm : 0 < (10 : ℝ) / κ.cq := div_pos (by norm_num) hκ.cq_rng.1
        have hpos : 0 < (κ.Mhi : ℝ) := by linarith [h]
        have hposNat : 0 < κ.Mhi := by exact_mod_cast hpos
        exact_mod_cast (Nat.one_le_iff_ne_zero.mpr hposNat.ne')
      have hCoeff : (0 : ℝ) ≤ 5 * κ.ω := mul_nonneg (by norm_num) hκ.ω_rng.1.le
      have hωMlo : 5 * κ.ω ≤ 5 * κ.ω * κ.Mhi := by
        calc 5 * κ.ω = 5 * κ.ω * 1 := by ring
             _ ≤ 5 * κ.ω * κ.Mhi := mul_le_mul_of_nonneg_left hMhi hCoeff
      have hAClt : κ.aC < 1 := by
        have hmin : min κ.η0 (1 : ℝ) ≤ 1 := min_le_right _ _
        have hsmall : min κ.η0 1 / (10 ^ 6 : ℝ) ≤ 1 / (10 ^ 6 : ℝ) :=
          div_le_div_of_nonneg_right hmin (by norm_num)
        have hsmall' : (1 / (10 ^ 6 : ℝ)) < 1 := by norm_num
        exact lt_trans hκ.aC_rng.2 (lt_of_le_of_lt hsmall hsmall')
      have hsmall : κ.aC / 100 < (1 / 100 : ℝ) := by nlinarith [hAClt]
      have hωineq : 5 * κ.ω < (1 / 100 : ℝ) :=
        lt_of_le_of_lt hωMlo (lt_trans hκ.ω_rng.2 hsmall)
      have hωsmall : κ.ω < (1 / 500 : ℝ) := by nlinarith [hωineq]
      have hExp : 4 * κ.ω ≤ 1 := by nlinarith [hωsmall]
      calc
        Real.rpow 2 (4 * κ.ω) ≤ Real.rpow 2 1 :=
          Real.rpow_le_rpow_of_exponent_le (by norm_num) hExp
        _ = 2 := Real.rpow_one 2
    have hqpowNonneg : 0 ≤ Real.rpow (q : ℝ) κ.Mhi :=
      Real.rpow_nonneg (Nat.cast_nonneg _) _
    have hNested : Real.rpow (Real.rpow (q : ℝ) κ.Mhi) (4 * κ.ω) =
        Real.rpow (q : ℝ) (4 * κ.ω * κ.Mhi) := by
      have hmul := Real.rpow_mul (x := (q : ℝ)) (Nat.cast_nonneg _) κ.Mhi (4 * κ.ω)
      have hexpEq : (κ.Mhi : ℝ) * (4 * κ.ω) = 4 * κ.ω * κ.Mhi := by ring
      rw [hexpEq] at hmul
      exact hmul.symm
    calc
      Real.rpow (2 * Real.rpow (q : ℝ) κ.Mhi) (4 * κ.ω) =
          Real.rpow 2 (4 * κ.ω) * Real.rpow (Real.rpow (q : ℝ) κ.Mhi) (4 * κ.ω) :=
        Real.mul_rpow (by norm_num) hqpowNonneg
      _ = Real.rpow 2 (4 * κ.ω) * Real.rpow (q : ℝ) (4 * κ.ω * κ.Mhi) := by rw [hNested]
      _ ≤ 2 * Real.rpow (q : ℝ) (4 * κ.ω * κ.Mhi) :=
        mul_le_mul_of_nonneg_right htwo (Real.rpow_nonneg (Nat.cast_nonneg _) _)
  calc
    (sliceK κ h : ℝ) * sliceT κ h ≤ 4 * Real.rpow (h : ℝ) (4 * κ.ω) := hktBound
    _ ≤ 4 * Real.rpow (2 * Real.rpow (q : ℝ) κ.Mhi) (4 * κ.ω) :=
      mul_le_mul_of_nonneg_left hHpow (by norm_num)
    _ ≤ 4 * (2 * Real.rpow (q : ℝ) (4 * κ.ω * κ.Mhi)) :=
      mul_le_mul_of_nonneg_left hHpow' (by norm_num)
    _ = 8 * Real.rpow (q : ℝ) (4 * κ.ω * κ.Mhi) := by ring

/-- Fixed eventual margins used by other-patch degree and row-tail cleaning. -/
theorem eventual_otherpatch_numeric (κ : CConsts) (hκ : CConsts.Admissible κ) (T : Stage) :
    ∀ᶠ k in Filter.atTop,
      (Real.exp (-((T.S.n k : ℝ) ^ (0.3 : ℝ))) ≤ κ.a / 8) ∧
      (Real.log (400 : ℝ) ≤ (T.S.n k : ℝ) ^ (κ.xs / 4)) ∧
      ((T.S.n k : ℝ) ^ (κ.xs / 4) ≤ κ.α * T.S.n k / 2) ∧
      (Real.log (400 : ℝ) + (T.S.n k : ℝ) ^ κ.ι ≤
        (T.S.n k : ℝ) ^ (0.1 : ℝ)) ∧
      ((T.S.n k : ℝ) ^ (κ.xs / 4) ≤ Real.sqrt (T.S.n k : ℝ)) ∧
      ((T.S.n k : ℝ) ^ (0.1 : ℝ) ≤ Real.sqrt (T.S.n k : ℝ)) ∧
      (Real.sqrt (T.S.n k : ℝ) ≤ κ.α * T.S.n k / 8) ∧
      (2 * Real.exp (-κ.α * T.S.n k / 4) ≤ κ.a / 8) ∧
      (12 * (T.S.n k : ℝ) ^ (2 * κ.ι) ≤ (T.S.n k : ℝ) ^ (κ.xs / 4)) ∧
      (Real.log (400 : ℝ) ≤ (T.S.n k : ℝ) ^ κ.ι) := by
  have hnCast : Filter.Tendsto (fun k : ℕ => (T.S.n k : ℝ)) Filter.atTop Filter.atTop :=
    tendsto_natCast_atTop_atTop.comp T.S.n_tendsto
  have hxsPos : 0 < κ.xs := hκ.xs_rng.1
  have hαPos : 0 < κ.α := hκ.α_rng.1
  have haPos : 0 < κ.a := by rw [hκ.a_eq]; exact div_pos hκ.θ_rng.1 (by norm_num)
  have hpXs4 : 0 < κ.xs / 4 := by positivity
  have hp03 : 0 < (0.3 : ℝ) := by norm_num
  have hp005 : 0 < (0.05 : ℝ) := by norm_num
  have hp01 : 0 < (0.1 : ℝ) := by norm_num
  have hιPos : 0 < κ.ι := hκ.ι_rng.1
  have hdeltaXs4 : 0 < 1 - κ.xs / 4 := by
    have hxs : κ.xs / 4 < 1 := by linarith [hκ.xs_rng.2]
    linarith
  have hGapXs : 0 < κ.xs / 4 - 2 * κ.ι := by
    have hιxs : κ.ι < κ.xs / 1000 := by
      have hmin : min κ.xs (min κ.η0 (0.01 : ℝ)) ≤ κ.xs := min_le_left _ _
      exact lt_of_lt_of_le hκ.ι_rng.2 (div_le_div_of_nonneg_right hmin (by norm_num))
    nlinarith [hιxs, hxsPos]
  have hPowXs4 : ∀ᶠ k in Filter.atTop,
      Real.log (400 : ℝ) ≤ (T.S.n k : ℝ) ^ (κ.xs / 4) := by
    have ht := (tendsto_rpow_atTop hpXs4).comp hnCast
    exact ht.eventually (Filter.eventually_ge_atTop (Real.log (400 : ℝ)))
  have hPow03 : ∀ᶠ k in Filter.atTop,
      Real.log (8 / κ.a) ≤ (T.S.n k : ℝ) ^ (0.3 : ℝ) := by
    have ht := (tendsto_rpow_atTop hp03).comp hnCast
    exact ht.eventually (Filter.eventually_ge_atTop (Real.log (8 / κ.a)))
  have hPow005 : ∀ᶠ k in Filter.atTop, 100 ≤ (T.S.n k : ℝ) ^ (0.05 : ℝ) := by
    have ht := (tendsto_rpow_atTop hp005).comp hnCast
    exact ht.eventually (Filter.eventually_ge_atTop 100)
  have hPowDelta : ∀ᶠ k in Filter.atTop,
      2 / κ.α ≤ (T.S.n k : ℝ) ^ (1 - κ.xs / 4) := by
    have ht := (tendsto_rpow_atTop hdeltaXs4).comp hnCast
    exact ht.eventually (Filter.eventually_ge_atTop (2 / κ.α))
  have hRootLower : ∀ᶠ k in Filter.atTop,
      8 / κ.α ≤ (T.S.n k : ℝ) ^ (1 / 2 : ℝ) := by
    have ht := (tendsto_rpow_atTop (by norm_num : (0 : ℝ) < 1 / 2)).comp hnCast
    exact ht.eventually (Filter.eventually_ge_atTop (8 / κ.α))
  have hPowGap : ∀ᶠ k in Filter.atTop,
      12 ≤ (T.S.n k : ℝ) ^ (κ.xs / 4 - 2 * κ.ι) := by
    have ht := (tendsto_rpow_atTop hGapXs).comp hnCast
    exact ht.eventually (Filter.eventually_ge_atTop 12)
  have hPowIota : ∀ᶠ k in Filter.atTop,
      Real.log (400 : ℝ) ≤ (T.S.n k : ℝ) ^ κ.ι := by
    have ht := (tendsto_rpow_atTop hιPos).comp hnCast
    exact ht.eventually (Filter.eventually_ge_atTop (Real.log (400 : ℝ)))
  have hLinear : ∀ᶠ k in Filter.atTop,
      Real.log (16 / κ.a) ≤ κ.α * T.S.n k / 4 := by
    have ht := hnCast.atTop_mul_const (div_pos hαPos (by norm_num : (0 : ℝ) < 4))
    have hevent := ht.eventually (Filter.eventually_ge_atTop (Real.log (16 / κ.a)))
    filter_upwards [hevent] with k hk
    have hEq : (T.S.n k : ℝ) * (κ.α / 4) = κ.α * T.S.n k / 4 := by ring
    rw [← hEq]
    exact hk
  have hIotaSmall : κ.ι ≤ (0.05 : ℝ) := by
    have hxs : min κ.xs (min κ.η0 (0.01 : ℝ)) ≤ (0.01 : ℝ) :=
      le_trans (min_le_right _ _) (min_le_right _ _)
    have hι : κ.ι < min κ.xs (min κ.η0 (0.01 : ℝ)) / 1000 := hκ.ι_rng.2
    nlinarith [hι, hxs]
  filter_upwards [hPowXs4, hPow03, hPow005, hPowDelta, hRootLower, hLinear, hPowGap, hPowIota,
    (T.S.n_tendsto.eventually (Filter.eventually_ge_atTop 1))]
    with k hxs4 h03 h005 hδ hroot hlin hgap hiota hk
  have hnR : (1 : ℝ) ≤ T.S.n k := by exact_mod_cast hk
  have hnPosR : (0 : ℝ) < T.S.n k := by linarith [hnR]
  have hxs4Half : (T.S.n k : ℝ) ^ (κ.xs / 4) ≤
      (T.S.n k : ℝ) ^ (1 / 2 : ℝ) :=
    Real.rpow_le_rpow_of_exponent_le hnR (by nlinarith [hκ.xs_rng.2])
  have h01Half : (T.S.n k : ℝ) ^ (0.1 : ℝ) ≤
      (T.S.n k : ℝ) ^ (1 / 2 : ℝ) :=
    Real.rpow_le_rpow_of_exponent_le hnR (by norm_num)
  have hSqrtEq : Real.sqrt (T.S.n k : ℝ) =
      (T.S.n k : ℝ) ^ (1 / 2 : ℝ) := Real.sqrt_eq_rpow (T.S.n k : ℝ)
  have hSqrtAlpha : Real.sqrt (T.S.n k : ℝ) ≤ κ.α * T.S.n k / 8 := by
    have hpow : (T.S.n k : ℝ) ^ (1 / 2 : ℝ) *
        (T.S.n k : ℝ) ^ (1 / 2 : ℝ) = (T.S.n k : ℝ) := by
      have hadd := Real.rpow_add hnPosR (1 / 2 : ℝ) (1 / 2 : ℝ)
      have hexp : (1 / 2 : ℝ) + (1 / 2 : ℝ) = 1 := by norm_num
      rw [hexp, Real.rpow_one] at hadd
      simpa [pow_two] using hadd.symm
    have hroot' : 8 ≤ κ.α * (T.S.n k : ℝ) ^ (1 / 2 : ℝ) := by
      simpa [mul_comm] using (div_le_iff₀ hαPos).mp hroot
    have hcoef : 1 ≤ κ.α * (T.S.n k : ℝ) ^ (1 / 2 : ℝ) / 8 := by
      apply (le_div_iff₀ (by norm_num : (0 : ℝ) < 8)).2
      nlinarith [hroot']
    have hmul := mul_le_mul_of_nonneg_right hcoef
      (Real.rpow_nonneg (le_trans (by norm_num) hnR) (1 / 2 : ℝ))
    calc
      Real.sqrt (T.S.n k : ℝ) = (T.S.n k : ℝ) ^ (1 / 2 : ℝ) := hSqrtEq
      _ = 1 * (T.S.n k : ℝ) ^ (1 / 2 : ℝ) := by ring
      _ ≤ (κ.α * (T.S.n k : ℝ) ^ (1 / 2 : ℝ) / 8) *
          (T.S.n k : ℝ) ^ (1 / 2 : ℝ) := hmul
      _ = κ.α * ((T.S.n k : ℝ) ^ (1 / 2 : ℝ) *
          (T.S.n k : ℝ) ^ (1 / 2 : ℝ)) / 8 := by ring
      _ = κ.α * T.S.n k / 8 := by rw [hpow]
  have hXs4Lin : (T.S.n k : ℝ) ^ (κ.xs / 4) ≤ κ.α * T.S.n k / 2 := by
    have hpow : (T.S.n k : ℝ) ^ (1 - κ.xs / 4) *
        (T.S.n k : ℝ) ^ (κ.xs / 4) = T.S.n k := by
      have hadd := Real.rpow_add hnPosR (1 - κ.xs / 4) (κ.xs / 4)
      have hexp' : (1 - κ.xs / 4) + κ.xs / 4 = 1 := by ring
      rw [hexp'] at hadd
      rw [Real.rpow_one] at hadd
      exact hadd.symm
    have hdelta' : 2 ≤ κ.α * (T.S.n k : ℝ) ^ (1 - κ.xs / 4) :=
      by simpa [mul_comm] using (div_le_iff₀ hαPos).mp hδ
    have hcoef : 1 ≤ κ.α * (T.S.n k : ℝ) ^ (1 - κ.xs / 4) / 2 := by
      apply (le_div_iff₀ (by norm_num : (0 : ℝ) < 2)).2
      nlinarith [hdelta']
    have hmul := mul_le_mul_of_nonneg_right hcoef
      (Real.rpow_nonneg (le_trans (by norm_num) hnR) (κ.xs / 4))
    calc
      (T.S.n k : ℝ) ^ (κ.xs / 4) =
          1 * (T.S.n k : ℝ) ^ (κ.xs / 4) := by ring
      _ ≤ (κ.α * (T.S.n k : ℝ) ^ (1 - κ.xs / 4) / 2) *
          (T.S.n k : ℝ) ^ (κ.xs / 4) := hmul
      _ = κ.α * ((T.S.n k : ℝ) ^ (1 - κ.xs / 4) *
          (T.S.n k : ℝ) ^ (κ.xs / 4)) / 2 := by ring
      _ = κ.α * T.S.n k / 2 := by rw [hpow]
  have hIotaPow : (T.S.n k : ℝ) ^ κ.ι ≤
      (T.S.n k : ℝ) ^ (0.05 : ℝ) :=
    Real.rpow_le_rpow_of_exponent_le hnR hIotaSmall
  have hCountSmall : Real.log (400 : ℝ) + (T.S.n k : ℝ) ^ κ.ι ≤
      (T.S.n k : ℝ) ^ (0.1 : ℝ) := by
    let v := (T.S.n k : ℝ) ^ (0.05 : ℝ)
    have hv : 100 ≤ v := h005
    have hsq : v ^ 2 = (T.S.n k : ℝ) ^ (0.1 : ℝ) := by
      dsimp [v]
      have hadd := Real.rpow_add hnPosR (0.05 : ℝ) (0.05 : ℝ)
      have hexp : (0.05 : ℝ) + (0.05 : ℝ) = 0.1 := by norm_num
      rw [hexp] at hadd
      simpa [pow_two] using hadd.symm
    have hlog400le : Real.log (400 : ℝ) ≤ 399 := by
      have hlog := Real.log_le_sub_one_of_pos (x := (400 : ℝ))
        (by norm_num : (0 : ℝ) < 400)
      norm_num at hlog ⊢
      exact hlog
    have hmargin : Real.log (400 : ℝ) + v ≤ 100 * v := by
      nlinarith [hv, hlog400le]
    have hprod := mul_nonneg (by positivity : (0 : ℝ) ≤ v)
      (sub_nonneg.mpr (by linarith [hv]))
    have hsquare : 100 * v ≤ v ^ 2 := by nlinarith [hprod]
    have hbase : Real.log (400 : ℝ) + v ≤ v ^ 2 := le_trans hmargin hsquare
    calc
      Real.log (400 : ℝ) + (T.S.n k : ℝ) ^ κ.ι ≤ Real.log (400 : ℝ) + v :=
        add_le_add le_rfl hIotaPow
      _ ≤ (T.S.n k : ℝ) ^ (0.1 : ℝ) := by rw [← hsq]; exact hbase
  have hExpSmall : Real.exp (-((T.S.n k : ℝ) ^ (0.3 : ℝ))) ≤ κ.a / 8 := by
    have hlog : Real.log (κ.a / 8) = -Real.log (8 / κ.a) := by
      rw [show κ.a / 8 = (8 / κ.a)⁻¹ by field_simp, Real.log_inv]
    calc
      Real.exp (-((T.S.n k : ℝ) ^ (0.3 : ℝ))) ≤ Real.exp (Real.log (κ.a / 8)) :=
        Real.exp_le_exp.mpr (by rw [hlog]; linarith [h03])
      _ = κ.a / 8 := Real.exp_log (div_pos haPos (by norm_num))
  have hExpOutlier : 2 * Real.exp (-κ.α * T.S.n k / 4) ≤ κ.a / 8 := by
    have hlog : Real.log (κ.a / 16) = -Real.log (16 / κ.a) := by
      rw [show κ.a / 16 = (16 / κ.a)⁻¹ by field_simp, Real.log_inv]
    have hExp : Real.exp (-κ.α * T.S.n k / 4) ≤ κ.a / 16 := by
      calc
        Real.exp (-κ.α * T.S.n k / 4) ≤ Real.exp (Real.log (κ.a / 16)) :=
          Real.exp_le_exp.mpr (by rw [hlog]; linarith [hlin])
        _ = κ.a / 16 := Real.exp_log (div_pos haPos (by norm_num))
    calc
      2 * Real.exp (-κ.α * T.S.n k / 4) ≤ 2 * (κ.a / 16) :=
        mul_le_mul_of_nonneg_left hExp (by norm_num)
      _ = κ.a / 8 := by ring
  have hGapPow : 12 * (T.S.n k : ℝ) ^ (2 * κ.ι) ≤
      (T.S.n k : ℝ) ^ (κ.xs / 4) := by
    have hnNonneg : (0 : ℝ) ≤ (T.S.n k : ℝ) := Nat.cast_nonneg _
    have hmul : 12 * (T.S.n k : ℝ) ^ (2 * κ.ι) ≤
        (T.S.n k : ℝ) ^ (κ.xs / 4 - 2 * κ.ι) * (T.S.n k : ℝ) ^ (2 * κ.ι) :=
      mul_le_mul_of_nonneg_right hgap
        (Real.rpow_nonneg hnNonneg (2 * κ.ι))
    have hpow : (T.S.n k : ℝ) ^ (2 * κ.ι) *
        (T.S.n k : ℝ) ^ (κ.xs / 4 - 2 * κ.ι) =
          (T.S.n k : ℝ) ^ (κ.xs / 4) := by
      rw [← Real.rpow_add hnPosR]
      congr 1 <;> ring
    calc
      12 * (T.S.n k : ℝ) ^ (2 * κ.ι) ≤
          ((T.S.n k : ℝ) ^ (κ.xs / 4 - 2 * κ.ι)) *
            (T.S.n k : ℝ) ^ (2 * κ.ι) := by simpa [mul_comm] using hmul
      _ = (T.S.n k : ℝ) ^ (κ.xs / 4) := by rw [mul_comm, hpow]
  exact ⟨hExpSmall, hxs4, hXs4Lin, hCountSmall, hxs4Half.trans_eq hSqrtEq.symm,
    h01Half.trans_eq hSqrtEq.symm, hSqrtAlpha, hExpOutlier, hGapPow, hiota⟩

/-- Round a real scale upward to a dyadic integer with a factor-two loss. -/
theorem exists_dyadic_ceiling {x : ℝ} (hx : 1 ≤ x) :
    ∃ b : ℕ, IsDyadic b ∧ x ≤ b ∧ b < 2 * x := by
  have hxpos : 0 < x := lt_of_lt_of_le zero_lt_one hx
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hy : 0 ≤ Real.log x / Real.log 2 :=
    div_nonneg (Real.log_nonneg hx) hlog2.le
  let j : ℕ := Nat.ceil (Real.log x / Real.log 2)
  have hceil : Real.log x / Real.log 2 ≤ (j : ℝ) := by
    exact Nat.le_ceil _
  have hceil' : (j : ℝ) < Real.log x / Real.log 2 + 1 := by
    exact Nat.ceil_lt_add_one hy
  have hExpPow : Real.exp ((j : ℝ) * Real.log 2) = (2 : ℝ) ^ j := by
    rw [Real.exp_nat_mul, Real.exp_log (by norm_num : (0 : ℝ) < 2)]
  have hlogLo : Real.log x ≤ (j : ℝ) * Real.log 2 := by
    rw [div_le_iff₀ hlog2] at hceil
    exact hceil
  have hlogHi : (j : ℝ) * Real.log 2 < Real.log x + Real.log 2 := by
    calc
      (j : ℝ) * Real.log 2 <
          (Real.log x / Real.log 2 + 1) * Real.log 2 :=
        mul_lt_mul_of_pos_right hceil' hlog2
      _ = Real.log x + Real.log 2 := by
        field_simp [ne_of_gt hlog2]
  have hlow : x ≤ (2 : ℝ) ^ j := by
    calc
      x = Real.exp (Real.log x) := (Real.exp_log hxpos).symm
      _ ≤ Real.exp ((j : ℝ) * Real.log 2) :=
        Real.exp_le_exp.mpr hlogLo
      _ = (2 : ℝ) ^ j := hExpPow
  have hhigh : (2 : ℝ) ^ j < 2 * x := by
    calc
      (2 : ℝ) ^ j = Real.exp ((j : ℝ) * Real.log 2) := hExpPow.symm
      _ < Real.exp (Real.log x + Real.log 2) :=
        Real.exp_lt_exp.mpr hlogHi
      _ = 2 * x := by
        rw [Real.exp_add, Real.exp_log hxpos, Real.exp_log (by norm_num : (0 : ℝ) < 2)]
        ring
  refine ⟨2 ^ j, ⟨j, rfl⟩, ?_, ?_⟩
  · exact_mod_cast hlow
  · exact_mod_cast hhigh

/-- A large set of rows whose degree is high yields a bias rectangle. -/
theorem biasWitness_of_highRows (κ : CConsts) (T : Stage) (k : ℕ) (b : ℕ)
    (c : Colour) (RX RY U V : Finset (Fin (T.S.N k)))
    (hUn : U.Nonempty) (hVn : V.Nonempty)
    (hUR : U ⊆ RX) (hVR : V ⊆ RY)
    (hUcard : (T.S.N k : ℝ) * Real.exp (-((b : ℝ) ^ κ.aB)) ≤ U.card)
    (hVcard : (T.S.N k : ℝ) * Real.exp (-((b : ℝ) ^ κ.aB)) ≤ V.card)
    (π : Law (T.S.N k))
    (hApprox : ∀ x, |(∑ y ∈ V, hit (T.S.E k) c x y) / V.card -
      deg (T.S.E k) c π.w x| ≤ (T.S.n k : ℝ) ^ (-2 : ℝ))
    (hRows : ∀ x ∈ U, 2 * (b : ℝ) / T.S.n k <
      deg (T.S.E k) c π.w x - 1 / 2)
    (hn : 0 < T.S.n k)
    (hError : (T.S.n k : ℝ) ^ (-2 : ℝ) ≤ (b : ℝ) / T.S.n k) :
    BiasWitness κ T k RX RY b := by
  let μ := Law.unifCore U hUn
  let ν := Law.unifCore V hVn
  have hVdeg (x : Fin (T.S.N k)) (hx : x ∈ U) :
      (1 / 2 : ℝ) + (b : ℝ) / T.S.n k < deg (T.S.E k) c ν.w x := by
    rw [show ν = Law.unifCore V hVn by rfl]
    rw [deg_unifCore]
    have htest := (abs_le.mp (hApprox x)).1
    have hdeg : (1 / 2 : ℝ) + 2 * (b : ℝ) / T.S.n k <
        deg (T.S.E k) c π.w x := by
      have := hRows x hx
      linarith
    have hAvgLower : deg (T.S.E k) c π.w x -
        (T.S.n k : ℝ) ^ (-2 : ℝ) ≤
          (∑ y ∈ V, hit (T.S.E k) c x y) / V.card := by
      linarith [htest]
    let t : ℝ := (b : ℝ) / T.S.n k
    let e : ℝ := (T.S.n k : ℝ) ^ (-2 : ℝ)
    have hError' : e ≤ t := by simpa [e, t] using hError
    have hdeg' : (1 / 2 : ℝ) + 2 * t < deg (T.S.E k) c π.w x := by
      dsimp [t]
      convert hdeg using 1 <;> ring
    have hMargin : (1 / 2 : ℝ) + (b : ℝ) / T.S.n k <
        deg (T.S.E k) c π.w x - (T.S.n k : ℝ) ^ (-2 : ℝ) := by
      have hMargin' : (1 / 2 : ℝ) + t < deg (T.S.E k) c π.w x - e := by
        linarith [hdeg', hError']
      simpa [e, t] using hMargin'
    exact lt_of_lt_of_le hMargin hAvgLower
  have hDens : dens (T.S.E k) c μ ν =
      (∑ x ∈ U, deg (T.S.E k) c ν.w x) / U.card := by
    rw [dens_eq_rowDegree_sum]
    dsimp [μ]
    calc
      (∑ x, (Law.unifCore U hUn).w x * deg (T.S.E k) c ν.w x) =
          ∑ x, if x ∈ U then (U.card : ℝ)⁻¹ *
            deg (T.S.E k) c ν.w x else 0 := by
        apply Finset.sum_congr rfl
        intro x hx
        by_cases hxU : x ∈ U <;> simp [Law.unifCore, hxU]
      _ = ∑ x ∈ U, (U.card : ℝ)⁻¹ * deg (T.S.E k) c ν.w x := by
        rw [Finset.sum_ite_mem, Finset.univ_inter]
      _ = (U.card : ℝ)⁻¹ * ∑ x ∈ U, deg (T.S.E k) c ν.w x := by
        rw [Finset.mul_sum]
      _ = (∑ x ∈ U, deg (T.S.E k) c ν.w x) / U.card := by
        rw [div_eq_mul_inv]
        ring
  have hsum : (U.card : ℝ) * ((1 / 2 : ℝ) + (b : ℝ) / T.S.n k) <
      ∑ x ∈ U, deg (T.S.E k) c ν.w x := by
    calc
      (U.card : ℝ) * ((1 / 2 : ℝ) + (b : ℝ) / T.S.n k) =
          ∑ x ∈ U, ((1 / 2 : ℝ) + (b : ℝ) / T.S.n k) := by
        rw [Finset.sum_const, nsmul_eq_mul]
      _ < ∑ x ∈ U, deg (T.S.E k) c ν.w x := by
        apply Finset.sum_lt_sum
        · intro x hx
          exact le_of_lt (hVdeg x hx)
        · obtain ⟨x, hx⟩ := hUn
          exact ⟨x, hx, hVdeg x hx⟩
  have hUpos : 0 < (U.card : ℝ) := by
    exact_mod_cast Finset.card_pos.mpr hUn
  have hDensHigh : (1 / 2 : ℝ) + (b : ℝ) / T.S.n k < dens (T.S.E k) c μ ν := by
    rw [hDens]
    have hsum' : ((1 / 2 : ℝ) + (b : ℝ) / T.S.n k) * (U.card : ℝ) <
        ∑ x ∈ U, deg (T.S.E k) c ν.w x := by simpa [mul_comm] using hsum
    exact (lt_div_iff₀ hUpos).2 hsum'
  have hnR : (0 : ℝ) < T.S.n k := by exact_mod_cast hn
  have hbn : 0 ≤ (b : ℝ) / T.S.n k :=
    div_nonneg (Nat.cast_nonneg _) hnR.le
  have hTrue : (b : ℝ) / T.S.n k ≤ |dens (T.S.E k) true μ ν - 1 / 2| := by
    cases c with
    | true =>
        have hnonneg : 0 ≤ dens (T.S.E k) true μ ν - 1 / 2 := by
          linarith [hDensHigh]
        rw [abs_of_nonneg hnonneg]
        linarith [hDensHigh]
    | false =>
        have hsumdens := dens_add_dens_not (T.S.E k) μ ν
        have hlt : dens (T.S.E k) true μ ν <
            (1 / 2 : ℝ) - (b : ℝ) / T.S.n k := by
          linarith [hDensHigh]
        have hnonpos : dens (T.S.E k) true μ ν - 1 / 2 ≤ 0 := by
          linarith [hlt, hbn]
        rw [abs_of_nonpos hnonpos]
        linarith
  exact ⟨U, V, hUn, hVn, hUR, hVR, hUcard, hVcard, hTrue⟩

/-- A large set of rows whose degree is low yields a bias rectangle. -/
theorem biasWitness_of_lowRows (κ : CConsts) (T : Stage) (k : ℕ) (b : ℕ)
    (c : Colour) (RX RY U V : Finset (Fin (T.S.N k)))
    (hUn : U.Nonempty) (hVn : V.Nonempty)
    (hUR : U ⊆ RX) (hVR : V ⊆ RY)
    (hUcard : (T.S.N k : ℝ) * Real.exp (-((b : ℝ) ^ κ.aB)) ≤ U.card)
    (hVcard : (T.S.N k : ℝ) * Real.exp (-((b : ℝ) ^ κ.aB)) ≤ V.card)
    (π : Law (T.S.N k))
    (hApprox : ∀ x, |(∑ y ∈ V, hit (T.S.E k) c x y) / V.card -
      deg (T.S.E k) c π.w x| ≤ (T.S.n k : ℝ) ^ (-2 : ℝ))
    (hRows : ∀ x ∈ U, 2 * (b : ℝ) / T.S.n k <
      1 / 2 - deg (T.S.E k) c π.w x)
    (hn : 0 < T.S.n k)
    (hError : (T.S.n k : ℝ) ^ (-2 : ℝ) ≤ (b : ℝ) / T.S.n k) :
    BiasWitness κ T k RX RY b := by
  let μ := Law.unifCore U hUn
  let ν := Law.unifCore V hVn
  have hVdeg (x : Fin (T.S.N k)) (hx : x ∈ U) :
      deg (T.S.E k) c ν.w x <
        (1 / 2 : ℝ) - (b : ℝ) / T.S.n k := by
    rw [show ν = Law.unifCore V hVn by rfl]
    rw [deg_unifCore]
    have htest := (abs_le.mp (hApprox x)).2
    have hdeg : deg (T.S.E k) c π.w x <
        (1 / 2 : ℝ) - 2 * (b : ℝ) / T.S.n k := by
      have := hRows x hx
      linarith
    have hAvgUpper : (∑ y ∈ V, hit (T.S.E k) c x y) / V.card ≤
        deg (T.S.E k) c π.w x + (T.S.n k : ℝ) ^ (-2 : ℝ) := by
      linarith [htest]
    let t : ℝ := (b : ℝ) / T.S.n k
    let e : ℝ := (T.S.n k : ℝ) ^ (-2 : ℝ)
    have hError' : e ≤ t := by simpa [e, t] using hError
    have hdeg' : deg (T.S.E k) c π.w x <
        (1 / 2 : ℝ) - 2 * t := by
      dsimp [t]
      convert hdeg using 1 <;> ring
    have hMargin : deg (T.S.E k) c π.w x +
        (T.S.n k : ℝ) ^ (-2 : ℝ) <
          (1 / 2 : ℝ) - (b : ℝ) / T.S.n k := by
      have hMargin' : deg (T.S.E k) c π.w x + e < (1 / 2 : ℝ) - t := by
        linarith [hdeg', hError']
      simpa [e, t] using hMargin'
    exact lt_of_le_of_lt hAvgUpper hMargin
  have hDens : dens (T.S.E k) c μ ν =
      (∑ x ∈ U, deg (T.S.E k) c ν.w x) / U.card := by
    rw [dens_eq_rowDegree_sum]
    dsimp [μ]
    calc
      (∑ x, (Law.unifCore U hUn).w x * deg (T.S.E k) c ν.w x) =
          ∑ x, if x ∈ U then (U.card : ℝ)⁻¹ *
            deg (T.S.E k) c ν.w x else 0 := by
        apply Finset.sum_congr rfl
        intro x hx
        by_cases hxU : x ∈ U <;> simp [Law.unifCore, hxU]
      _ = ∑ x ∈ U, (U.card : ℝ)⁻¹ * deg (T.S.E k) c ν.w x := by
        rw [Finset.sum_ite_mem, Finset.univ_inter]
      _ = (U.card : ℝ)⁻¹ * ∑ x ∈ U, deg (T.S.E k) c ν.w x := by
        rw [Finset.mul_sum]
      _ = (∑ x ∈ U, deg (T.S.E k) c ν.w x) / U.card := by
        rw [div_eq_mul_inv]
        ring
  have hsum : ∑ x ∈ U, deg (T.S.E k) c ν.w x <
      (U.card : ℝ) * ((1 / 2 : ℝ) - (b : ℝ) / T.S.n k) := by
    calc
      ∑ x ∈ U, deg (T.S.E k) c ν.w x <
          ∑ x ∈ U, ((1 / 2 : ℝ) - (b : ℝ) / T.S.n k) := by
        apply Finset.sum_lt_sum
        · intro x hx
          exact le_of_lt (hVdeg x hx)
        · obtain ⟨x, hx⟩ := hUn
          exact ⟨x, hx, hVdeg x hx⟩
      _ = (U.card : ℝ) * ((1 / 2 : ℝ) - (b : ℝ) / T.S.n k) := by
        rw [Finset.sum_const, nsmul_eq_mul]
  have hUpos : 0 < (U.card : ℝ) := by
    exact_mod_cast Finset.card_pos.mpr hUn
  have hDensLow : dens (T.S.E k) c μ ν <
      (1 / 2 : ℝ) - (b : ℝ) / T.S.n k := by
    rw [hDens]
    have hsum' : ∑ x ∈ U, deg (T.S.E k) c ν.w x <
        ((1 / 2 : ℝ) - (b : ℝ) / T.S.n k) * (U.card : ℝ) := by
      simpa [mul_comm] using hsum
    exact (div_lt_iff₀ hUpos).2 hsum'
  have hnR : (0 : ℝ) < T.S.n k := by exact_mod_cast hn
  have hbn : 0 ≤ (b : ℝ) / T.S.n k :=
    div_nonneg (Nat.cast_nonneg _) hnR.le
  have hTrue : (b : ℝ) / T.S.n k ≤ |dens (T.S.E k) true μ ν - 1 / 2| := by
    cases c with
    | true =>
        have hnonpos : dens (T.S.E k) true μ ν - 1 / 2 ≤ 0 := by
          linarith [hDensLow, hbn]
        rw [abs_of_nonpos hnonpos]
        linarith
    | false =>
        have hsumdens := dens_add_dens_not (T.S.E k) μ ν
        have hlt : (1 / 2 : ℝ) + (b : ℝ) / T.S.n k <
            dens (T.S.E k) true μ ν := by
          linarith [hDensLow]
        have hnonneg : 0 ≤ dens (T.S.E k) true μ ν - 1 / 2 := by
          linarith [hlt, hbn]
        rw [abs_of_nonneg hnonneg]
        linarith
  exact ⟨U, V, hUn, hVn, hUR, hVR, hUcard, hVcard, hTrue⟩

end HypercubeRamsey.S13.Lane_q_s13_clean
