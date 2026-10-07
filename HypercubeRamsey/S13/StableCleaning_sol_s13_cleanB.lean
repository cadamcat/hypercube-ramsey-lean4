import HypercubeRamsey.S13.StableCleaning_q_s13_clean
import HypercubeRamsey.PartC.Cleaning

namespace HypercubeRamsey.S13.Lane_sol_s13_cleanB

open Filter Classical
open scoped BigOperators

theorem admissible_a_small (κ : CConsts) (hκ : κ.Admissible) : 0 < κ.a ∧ κ.a < 1 / 100 := by
  have hpow : Real.rpow 2 (-(10 * (κ.u : ℝ) + 100)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by linarith [show (0 : ℝ) ≤ κ.u from Nat.cast_nonneg _])
  have hxi : κ.ξ < 1 := by
    have ht := mul_le_mul_of_nonneg_left hpow hκ.α_rng.1.le
    linarith [hκ.ξ_rng.2, hκ.α_rng.2]
  have hden : (3 : ℝ) ≤ 3 * (4 : ℝ) ^ (κ.u + 3) := by
    have hp : (1 : ℝ) ≤ (4 : ℝ) ^ (κ.u + 3) := one_le_pow₀ (by norm_num)
    linarith
  have htheta : κ.θ < 1 := by
    have hd := div_le_div_of_nonneg_left (sq_nonneg κ.ξ) (by norm_num : (0 : ℝ) < 3) hden
    have hx : κ.ξ ^ 2 < 1 := by nlinarith [hκ.ξ_rng.1]
    linarith [hκ.θ_rng.2, hd]
  rw [hκ.a_eq]
  constructor
  · exact div_pos hκ.θ_rng.1 (by norm_num)
  · linarith

/-- Expose a maximal pack through membership propositions, independent of predicate deciders. -/
theorem clique_pack {α : Type*} [DecidableEq α] (X : Finset α) (m : ℕ)
    (hm : 0 < m) (R : α → α → Prop) :
    ∃ P : Finset (Finset α),
      (∀ A ∈ P, A ⊆ X ∧ A.card = m ∧ ∀ x ∈ A, ∀ z ∈ A, x ≠ z → R x z) ∧
      Lane_q_s13_clean.IsDisjointPack P ∧
      ∀ K, K ⊆ X → K.card = m → (∀ x ∈ K, ∀ z ∈ K, x ≠ z → R x z) →
        ¬ K ⊆ X \ P.biUnion id := by
  classical
  obtain ⟨P, hP, hD, hM⟩ := Lane_q_s13_clean.maximal_disjoint_clique_pack X m hm R
  refine ⟨P, ?_, hD, ?_⟩
  · intro A hA
    have ht := Finset.mem_filter.mp (hP hA)
    exact ⟨Finset.mem_powerset.mp ht.1, ht.2⟩
  · intro K hK hcard hp
    apply hM K
    rw [Finset.filter_congr_decidable]
    rw [Finset.mem_filter, Finset.mem_powerset]
    exact ⟨hK, hcard, hp⟩

private theorem log400_le : Real.log (400 : ℝ) ≤ 10 := by
  have h := Real.add_one_le_exp (1 : ℝ)
  have he : 2 ≤ Real.exp (1 : ℝ) := by linarith
  have hp : (2 : ℝ) ^ 10 ≤ Real.exp (1 : ℝ) ^ 10 := pow_le_pow_left₀ (by norm_num) he 10
  rw [← Real.exp_nat_mul] at hp
  norm_num at hp
  exact (Real.log_le_iff_le_exp (by norm_num)).2 (by linarith)

private theorem cap_gap {q aC e L cap : ℝ} (hq : 1 ≤ q)
    (he : 0 ≤ e) (heSmall : e < aC / 100) (hL : 200 ≤ L)
    (hCap' : cap ≤ 80 * Real.rpow q e) :
    Real.rpow q aC + 2 * Real.rpow (2 * q) e + L ≥
      Real.log (400 : ℝ) + cap + 2 := by
  let qPow := Real.rpow q aC
  let qE := Real.rpow q e
  let qDouble := Real.rpow (2 * q) e
  have hqPowNonneg : 0 ≤ qPow := Real.rpow_nonneg (by linarith) _
  have hqDoubleNonneg : 0 ≤ qDouble := Real.rpow_nonneg (by linarith) _
  have hQDouble : qE ≤ qDouble :=
    Real.rpow_le_rpow (by linarith) (by linarith) he
  have hLog400 := log400_le
  have hBaseGap : qPow + 2 * qDouble +
      L ≥
        Real.log (400 : ℝ) + cap + 2 := by
    by_cases hBig : 78 * qE ≤ qPow
    · have hlarge : 80 * qE ≤ qPow + 2 * qDouble := by
        nlinarith [hBig, hQDouble]
      nlinarith [hlarge, hL, hLog400, hCap']
    · have hSmall : qPow < 78 * qE := lt_of_not_ge hBig
      have hqPos : 0 < q := by linarith
      have hqLogNonneg : 0 ≤ Real.log q := Real.log_nonneg hq
      have hqPowPos : 0 < qPow := by dsimp [qPow]; positivity
      have hqEPos : 0 < qE := by dsimp [qE]; positivity
      have hLogLeft : Real.log qPow < Real.log (78 * qE) :=
        Real.log_lt_log hqPowPos (by nlinarith [hSmall])
      have hLogLeft' : aC * Real.log q <
          Real.log (78 : ℝ) + e * Real.log q := by
        have hLhs : Real.log qPow = aC * Real.log q := by
          dsimp [qPow]
          exact Real.log_rpow hqPos aC
        have hRhs : Real.log (78 * qE) =
            Real.log (78 : ℝ) + e * Real.log q := by
          rw [Real.log_mul (by norm_num) (ne_of_gt hqEPos)]
          dsimp [qE]
          rw [Real.log_rpow hqPos]
        rw [hLhs, hRhs] at hLogLeft
        exact hLogLeft
      have hDeltaPos : 0 < aC - e := by nlinarith [heSmall]
      have hDeltaLog : (aC - e) * Real.log q < Real.log 78 := by
        nlinarith [hLogLeft']
      have heDelta : e ≤ (aC - e) / 99 := by
        nlinarith [heSmall]
      have heLog : e * Real.log q < Real.log 78 / 99 := by
        have hmul := mul_le_mul_of_nonneg_right heDelta hqLogNonneg
        nlinarith [hmul, hDeltaLog]
      have hLog78 : Real.log (78 : ℝ) < 99 * Real.log 2 := by
        have hpow : (78 : ℝ) < (2 : ℝ) ^ 99 := by norm_num
        have h := Real.log_lt_log (by norm_num) hpow
        rw [Real.log_pow] at h
        exact h
      have heLog2 : e * Real.log q < Real.log 2 := by
        nlinarith [heLog, hLog78]
      have hLogQE : Real.log qE < Real.log 2 := by
        dsimp [qE]
        rw [Real.log_rpow hqPos]
        exact heLog2
      have hqElt2 : qE < 2 := by
        by_contra hnot
        have hle : 2 ≤ qE := le_of_not_gt hnot
        have hmono := Real.log_le_log (by norm_num : (0 : ℝ) < 2) hle
        linarith [hLogQE]
      have hcap160 : cap ≤ 160 := by
        calc
          cap ≤ 80 * qE := hCap'
          _ ≤ 80 * 2 := mul_le_mul_of_nonneg_left hqElt2.le (by norm_num)
          _ = 160 := by norm_num
      nlinarith [hL, hLog400, hcap160, hqPowNonneg, hqDoubleNonneg]
  exact hBaseGap


private theorem mass_log {N M A : ℝ} (hN : 0 < N) (hM : 0 < M)
    (hm : N / 400 * Real.exp (-A) ≤ M) :
    Real.log (N / M) ≤ A + Real.log 400 := by
  have hNM : N / M ≤ 400 * Real.exp A := by
    apply (div_le_iff₀ hM).mpr
    have ht := mul_le_mul_of_nonneg_right hm (Real.exp_nonneg A)
    rw [mul_assoc, ← Real.exp_add] at ht
    simp at ht
    nlinarith [ht]
  calc
    Real.log (N / M) ≤ Real.log (400 * Real.exp A) :=
      Real.log_le_log (div_pos hN hM) hNM
    _ = A + Real.log 400 := by rw [Real.log_mul (by norm_num) (Real.exp_ne_zero _), Real.log_exp]; ring

private theorem loss_budget {N M A B a : ℝ} (hN : 0 ≤ N) (hM : 0 < M) (ha : 0 < a)
    (hm : N / 400 * Real.exp (-A) ≤ M)
    (hgap : A + Real.log (320000 / a) ≤ B) :
    N * Real.exp (-B) < a / 4 * M := by
  have hx : Real.exp (-B) ≤ Real.exp (-A) * (a / 320000) := by
    calc
      Real.exp (-B) ≤ Real.exp (-A - Real.log (320000 / a)) :=
        Real.exp_le_exp.mpr (by linarith)
      _ = Real.exp (-A) * (a / 320000) := by
        rw [sub_eq_add_neg, Real.exp_add, Real.exp_neg (Real.log (320000 / a)), Real.exp_log (by positivity)]
        field_simp
  have ht := mul_le_mul_of_nonneg_left hx hN
  have hm' := mul_le_mul_of_nonneg_right hm (by positivity : 0 ≤ a / 800)
  have hle : N * Real.exp (-B) ≤ a / 800 * M := by nlinarith [ht, hm']
  have hlt : a / 800 * M < a / 4 * M := mul_lt_mul_of_pos_right (by linarith) hM
  exact hle.trans_lt hlt

/-- Every mode pays for a uniform law at the larger clique budget and a small deletion. -/
theorem clique_budget (κ : CConsts) (hκ : κ.Admissible) (T : Stage) (k : ℕ)
    (𝒯 : Tiling κ T k) (h𝒯 : Tiling.Valid 𝒯)
    (i : Fin 𝒯.m) (π : Fin 𝒯.m → Law (T.S.N k)) (hInput : InputOK 𝒯 h𝒯 π) :
    IsDyadic (𝒯.Q i) ∧ (𝒯.P i).q < 𝒯.Q i ∧
    (π i).WidthLE (Real.rpow (𝒯.Q i : ℝ) κ.aC - 2) ∧
    (T.S.N k : ℝ) * Real.exp (-Real.rpow (𝒯.Q i : ℝ) κ.aC) <
      κ.a / 4 * (𝒯.P i).M := by
  have ha : 0 < κ.a := by rw [hκ.a_eq]; exact div_pos hκ.θ_rng.1 (by norm_num)
  have hN : 0 < (T.S.N k : ℝ) := by exact_mod_cast T.S.N_pos k
  have hM : 0 < ((𝒯.P i).M : ℝ) := by
    have ht := Finset.card_pos.mpr (h𝒯.patch_nonempty i).1
    rw [(𝒯.P i).cardX] at ht
    exact_mod_cast ht
  have hAC : κ.aC < 1 := by
    have ht := hκ.aC_rng.2
    have hm := min_le_right κ.η0 (1 : ℝ)
    linarith
  have hAB : κ.aB ≤ 1 := by linarith [hκ.aB_rng.2.1]
  have hLog := Lane_q_s13_clean.sampler_log_budget κ hκ
  have hLogEq : 800 / (κ.a * (1 / 400 : ℝ)) = 320000 / κ.a := by field_simp [ne_of_gt ha]; ring
  have hq : (1 : ℝ) ≤ (𝒯.P i).q := by
    have dy : IsDyadic (qScale κ T k (𝒯.P i).resX (𝒯.P i).resY) := ⟨_, rfl⟩
    rw [← (h𝒯.measured_scales i).2] at dy
    obtain ⟨j, hj⟩ := dy
    rw [hj]
    exact_mod_cast Nat.one_le_pow' j 1
  have uniform (hc : ¬ 𝒯.mode.isCluster) :
      π i = Law.unifCore (𝒯.P i).Y (h𝒯.patch_nonempty i).2 := by
    simpa [hc] using (hInput i).2
  have uniform_width (hc : ¬ 𝒯.mode.isCluster) :
      (π i).WidthLE (Real.log ((T.S.N k : ℝ) / (𝒯.P i).M)) := by
    rw [uniform hc]
    simpa [(𝒯.P i).cardY] using
      Lane_q_s13_clean.unifCore_width (𝒯.P i).Y (h𝒯.patch_nonempty i).2
  have widen {W B : ℝ} (hw : (π i).WidthLE W) (hg : W + 2 ≤ B) :
      (π i).WidthLE (B - 2) := by
    intro y
    exact (hw y).trans (div_le_div_of_nonneg_right
      (Real.exp_le_exp.mpr (by linarith)) hN.le)
  have direct (hm : 𝒯.mode = .lowDirect ∨ 𝒯.mode = .highDirect) :
      IsDyadic (𝒯.Q i) ∧ (𝒯.P i).q < 𝒯.Q i ∧
      (π i).WidthLE (Real.rpow (𝒯.Q i : ℝ) κ.aC - 2) ∧
      (T.S.N k : ℝ) * Real.exp (-Real.rpow (𝒯.Q i : ℝ) κ.aC) <
        κ.a / 4 * (𝒯.P i).M := by
    rcases h𝒯.direct_data hm i with ⟨hmax, hgq, hmass, _⟩
    rcases (h𝒯.clique_scales i).2 hm with ⟨hdy, hQlo, hQhi, hqQ⟩
    have hM1 : 0 < (κ.M1 : ℝ) := by linarith [hκ.M1_big.1]
    have hqg : ((𝒯.P i).q : ℝ) ≤ (𝒯.P i).g := by
      have hp := mul_le_mul_of_nonneg_right (by linarith [hκ.M1_big.1] : (1 : ℝ) ≤ κ.M1)
        (Nat.cast_nonneg (𝒯.P i).q)
      linarith [hgq, hp]
    have hscale : κ.M1 * κ.Q0 ≤ (𝒯.P i).g := by
      have hmx : κ.M1 * κ.Q0 ≤ max ((𝒯.P i).g : ℝ) ((𝒯.P i).q : ℝ) := by exact_mod_cast hmax
      rwa [max_eq_left hqg] at hmx
    have hbase : κ.Q0 ≤ ((𝒯.P i).g : ℝ) / κ.M1 := (le_div_iff₀ hM1).mpr (by simpa [mul_comm] using hscale)
    have hcond := (hκ.Q0_large _ hbase).1
    rw [show (κ.M1 : ℝ) * ((𝒯.P i).g / κ.M1) = (𝒯.P i).g by field_simp [ne_of_gt hM1], hLogEq] at hcond
    have htwo : Real.rpow 2 κ.aB ≤ 2 := by
      calc
        Real.rpow 2 κ.aB ≤ Real.rpow 2 1 := Real.rpow_le_rpow_of_exponent_le (by norm_num) hAB
        _ = 2 := Real.rpow_one 2
    have hpow : Real.log (320000 / κ.a) ≤ Real.rpow ((𝒯.P i).g : ℝ) κ.aB := by
      have hp := mul_le_mul_of_nonneg_right (by linarith [htwo] : Real.rpow 2 κ.aB - 1 ≤ 1)
        (Real.rpow_nonneg (Nat.cast_nonneg (𝒯.P i).g) κ.aB)
      exact hcond.trans (by simpa only [one_mul, Real.rpow_eq_pow] using hp)
    have hg : 0 < ((𝒯.P i).g : ℝ) := by linarith [hq, hqg]
    have hgM1 : (κ.M1 : ℝ) ≤ (𝒯.P i).g := by
      have hp := mul_le_mul_of_nonneg_left hq hM1.le
      linarith [hgq, hp]
    have hgap := Lane_q_s13_clean.direct_clique_power_gap
      (by exact_mod_cast hκ.M1_big.1) hgM1 hκ.aB_rng.1 hAB
      hκ.aB_rng.2.1 hg (hLog.trans hpow) hQlo.le
    have hmasslog := mass_log (A := Real.rpow ((𝒯.P i).g : ℝ) κ.aB) hN hM (by simpa [div_eq_mul_inv, mul_comm, mul_left_comm, mul_assoc, Real.rpow_eq_pow] using hmass)
    have hnc : ¬ 𝒯.mode.isCluster := by rcases hm with hm | hm <;> simp [hm, Mode.isCluster]
    simp only [Real.rpow_eq_pow] at hmasslog hgap hpow
    refine ⟨hdy, hqQ, widen (uniform_width hnc) ?_, ?_⟩
    · simp only [Real.rpow_eq_pow]
      linarith [hmasslog, log400_le, hLog.trans hpow, hgap]
    · exact loss_budget (A := Real.rpow ((𝒯.P i).g : ℝ) κ.aB)
        (B := Real.rpow (𝒯.Q i : ℝ) κ.aC) hN.le hM ha
        (by simpa [div_eq_mul_inv, mul_comm, mul_left_comm, mul_assoc, Real.rpow_eq_pow] using hmass)
        (by simp only [Real.rpow_eq_pow]; linarith [hgap, hpow])
  have cluster (hm : 𝒯.mode = .lowCluster ∨ 𝒯.mode = .highSmall ∨ 𝒯.mode = .highLarge) :
      IsDyadic (𝒯.Q i) ∧ (𝒯.P i).q < 𝒯.Q i ∧
      (π i).WidthLE (Real.rpow (𝒯.Q i : ℝ) κ.aC - 2) ∧
      (T.S.N k : ℝ) * Real.exp (-Real.rpow (𝒯.Q i : ℝ) κ.aC) <
        κ.a / 4 * (𝒯.P i).M := by
    rcases h𝒯.cluster_data hm i with ⟨hmax, hgq, hmass, _, _, _, _, hhlo, hhhi, _⟩
    rcases (h𝒯.clique_scales i).1 hm with ⟨hdy, hQlo, hQhi, _⟩
    have hM1 : 0 < (κ.M1 : ℝ) := by linarith [hκ.M1_big.1]
    have hqQ0 : κ.Q0 ≤ (𝒯.P i).q := by
      have hmx : κ.M1 * κ.Q0 ≤ max ((𝒯.P i).g : ℝ) ((𝒯.P i).q : ℝ) := by exact_mod_cast hmax
      have hqM := mul_le_mul_of_nonneg_left hq hM1.le
      have hqm : ((𝒯.P i).q : ℝ) ≤ κ.M1 * (𝒯.P i).q := by
        have hp := mul_le_mul_of_nonneg_right (by linarith [hκ.M1_big.1] : (1 : ℝ) ≤ κ.M1)
          (Nat.cast_nonneg (𝒯.P i).q)
        simpa using hp
      have hm := hmx.trans (max_le hgq hqm)
      exact (mul_le_mul_iff_right₀ hM1).mp hm
    have hcond := hκ.Q0_large _ hqQ0
    have hqq : 1 < ((𝒯.P i).q : ℝ) := by
      have hg := hcond.2.2.2.1
      by_contra hh
      have hqe : ((𝒯.P i).q : ℝ) = 1 := le_antisymm (le_of_not_gt hh) hq
      rw [hqe] at hg
      norm_num at hg
      linarith [hκ.M1_big.1]
    have hqQ : (𝒯.P i).q < 𝒯.Q i := by
      have hqr : ((𝒯.P i).q : ℝ) < ((𝒯.P i).q : ℝ) ^ 2 := by nlinarith
      have hQc : ((𝒯.P i).q : ℝ) ^ 2 ≤ (𝒯.Q i : ℝ) := by exact_mod_cast hQlo
      exact_mod_cast hqr.trans_le hQc
    have hMloHi : (κ.Mlo : ℝ) ≤ κ.Mhi := by
      have hp : 0 ≤ 10 / κ.cq := div_nonneg (by norm_num) hκ.cq_rng.1.le
      linarith [hκ.Mhi_big.1]
    have hhe : (𝒯.P i).h ≥ (1 : ℝ) := by
      have hex : 0 ≤ (if 𝒯.mode = .lowCluster then (κ.Mlo : ℝ) else κ.Mhi) := by positivity
      exact (Real.one_le_rpow hq hex).trans hhlo
    have hhexp : (if 𝒯.mode = .lowCluster then (κ.Mlo : ℝ) else κ.Mhi) ≤ κ.Mhi := by
      by_cases hl : 𝒯.mode = .lowCluster
      · simpa only [if_pos hl] using hMloHi
      · simp only [if_neg hl, le_refl]
    have hh : ((𝒯.P i).h : ℝ) < 2 * Real.rpow ((𝒯.P i).q : ℝ) κ.Mhi := by
      have ht : ((𝒯.P i).h : ℝ) < 2 * Real.rpow ((𝒯.P i).q : ℝ)
          (if 𝒯.mode = .lowCluster then (κ.Mlo : ℝ) else κ.Mhi) := by simpa only [Nat.cast_ite] using hhhi
      exact ht.trans_le (mul_le_mul_of_nonneg_left
        (Real.rpow_le_rpow_of_exponent_le hq hhexp) (by norm_num))
    have hkt := Lane_q_s13_clean.slice_product_cluster_bound κ hκ (𝒯.P i).q (𝒯.P i).h
      (by exact_mod_cast hq) (by exact_mod_cast hhe) hh
    let cap : ℝ := 10 * (𝒯.kScale i : ℝ) * 𝒯.tScale i
    let W : ℝ := Real.log ((T.S.N k : ℝ) / (𝒯.P i).M) + cap
    have hw : (π i).WidthLE W := by
      intro y
      have hc : 𝒯.mode.isCluster := by rcases hm with hm | hm | hm <;> simp [hm, Mode.isCluster]
      have ht := (hInput i).2
      rw [if_pos hc] at ht
      have hty : (π i).w y ≤ Real.exp cap / (𝒯.P i).M :=
        (le_div_iff₀ hM).mpr (by simpa [cap, mul_comm] using ht y)
      have heq : Real.exp W / (T.S.N k : ℝ) = Real.exp cap / (𝒯.P i).M := by
        dsimp [W]
        rw [Real.exp_add, Real.exp_log (div_pos hN hM)]
        field_simp [ne_of_gt hN, ne_of_gt hM] <;> ring
      rwa [heq]
    let e : ℝ := 4 * κ.ω * κ.Mhi
    have he : 0 ≤ e := mul_nonneg (mul_nonneg (by norm_num) hκ.ω_rng.1.le) (Nat.cast_nonneg _)
    have hes : e < κ.aC / 100 := by
      have hp : 0 ≤ κ.ω * κ.Mhi := mul_nonneg hκ.ω_rng.1.le (Nat.cast_nonneg _)
      dsimp [e]
      nlinarith [hκ.ω_rng.2]
    have hcap : cap ≤ 80 * Real.rpow ((𝒯.P i).q : ℝ) e := by
      dsimp [cap, e, Tiling.kScale, Tiling.tScale]
      simp only [Real.rpow_eq_pow] at hkt ⊢
      nlinarith only [hkt]
    have hcg := cap_gap hq he hes hLog hcap
    have hmasslog := mass_log (A := Real.rpow ((𝒯.P i).q : ℝ) κ.aC) hN hM (by simpa [div_eq_mul_inv, mul_comm, mul_left_comm, mul_assoc, Real.rpow_eq_pow] using hmass)
    have hbudget : Real.rpow ((𝒯.P i).q : ℝ) (2 * κ.aC) ≤ Real.rpow (𝒯.Q i : ℝ) κ.aC := by
      calc
        Real.rpow ((𝒯.P i).q : ℝ) (2 * κ.aC) = Real.rpow (((𝒯.P i).q : ℝ) ^ 2) κ.aC := by
          have ht : Real.rpow ((𝒯.P i).q : ℝ) (2 : ℝ) = ((𝒯.P i).q : ℝ) ^ 2 :=
            Real.rpow_natCast _ 2
          calc
            Real.rpow ((𝒯.P i).q : ℝ) (2 * κ.aC) =
                Real.rpow (Real.rpow ((𝒯.P i).q : ℝ) (2 : ℝ)) κ.aC :=
              Real.rpow_mul (Nat.cast_nonneg _) _ _
            _ = Real.rpow (((𝒯.P i).q : ℝ) ^ 2) κ.aC := by rw [ht]
        _ ≤ Real.rpow (𝒯.Q i : ℝ) κ.aC :=
          Real.rpow_le_rpow (sq_nonneg _) (by exact_mod_cast hQlo) hκ.aC_rng.1.le
    have hgap := hcond.2.2.2.2.2.1
    rw [hLogEq] at hgap
    simp only [Real.rpow_eq_pow] at hcg hmasslog hbudget hgap
    refine ⟨hdy, hqQ, widen hw ?_, ?_⟩
    · dsimp [W]
      dsimp [e] at hcg
      linarith [hcg, hgap, hmasslog, hbudget]
    · apply loss_budget (A := Real.rpow ((𝒯.P i).q : ℝ) κ.aC)
        (B := Real.rpow (𝒯.Q i : ℝ) κ.aC) hN.le hM ha
        (by simpa [div_eq_mul_inv, mul_comm, mul_left_comm, mul_assoc, Real.rpow_eq_pow] using hmass)
      have hp : 0 ≤ Real.rpow ((𝒯.P i).q : ℝ) κ.aC := Real.rpow_nonneg (Nat.cast_nonneg _) _
      have he : 0 ≤ Real.rpow (2 * ((𝒯.P i).q : ℝ)) (4 * κ.ω * κ.Mhi) :=
        Real.rpow_nonneg (mul_nonneg (by norm_num) (Nat.cast_nonneg _)) _
      simp only [Real.rpow_eq_pow] at hp he ⊢
      linarith [hgap, hbudget]
  cases hm : 𝒯.mode with
  | lowDirect => exact direct (Or.inl hm)
  | highDirect => exact direct (Or.inr hm)
  | lowCluster => exact cluster (Or.inl hm)
  | highSmall => exact cluster (Or.inr (Or.inl hm))
  | highLarge => exact cluster (Or.inr (Or.inr hm))
  | bounded =>
    have hbm := h𝒯.bounded_data hm
    rcases hbm.2 i with ⟨_, _, _, hmass, hQ⟩
    have hnc : ¬ 𝒯.mode.isCluster := by simp [hm, Mode.isCluster]
    have hqQ : (𝒯.P i).q < 𝒯.Q i := by
      have hmax := h𝒯.bounded_scale_cutoff hm i
      have ht : ((𝒯.P i).q : ℝ) < κ.M1 * κ.Q0 := by
        have hmaxR : max ((𝒯.P i).g : ℝ) ((𝒯.P i).q : ℝ) < κ.M1 * κ.Q0 := by exact_mod_cast hmax
        exact (le_max_right _ _).trans_lt hmaxR
      rw [hQ]
      exact_mod_cast ht.trans hκ.bounded.2.1
    have hB : Real.log (4000 / κ.a) ≤ Real.rpow (κ.Qbd : ℝ) κ.aC := by
      have ht := hκ.bounded.2.2.1
      have hl := Real.log_le_log (Real.exp_pos _) ht
      rw [Real.log_exp, Real.log_div (ne_of_gt ha) (by norm_num)] at hl
      rw [Real.log_div (by norm_num) (ne_of_gt ha)]
      linarith
    have hBlarge : 120 ≤ Real.rpow (κ.Qbd : ℝ) κ.aC := by
      have hl80 : Real.log (80 : ℝ) ≤ 80 := by
        have ht := Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 80)
        linarith
      have hleq : Real.log (320000 / κ.a) = Real.log 80 + Real.log (4000 / κ.a) := by
        rw [← Real.log_mul (by norm_num) (by positivity)]
        congr 1
        ring
      rw [hleq] at hLog
      linarith [hB, hl80]
    refine ⟨?_, hqQ, widen (uniform_width hnc) ?_, ?_⟩
    · rw [hQ]; exact hκ.bounded.1
    · have hl : Real.log ((T.S.N k : ℝ) / (𝒯.P i).M) ≤ Real.log 400 := by
        simpa using mass_log (A := 0) hN hM
          (by simpa [div_eq_mul_inv, mul_comm] using hmass)
      rw [hQ]
      linarith [hl, log400_le, hBlarge]
    · rw [hQ]
      have ht := mul_le_mul_of_nonneg_left hκ.bounded.2.2.1 hN.le
      have hm' := mul_le_mul_of_nonneg_left (by simpa [div_eq_mul_inv, mul_comm] using hmass)
        (by positivity : 0 ≤ κ.a / 10)
      have hle : (T.S.N k : ℝ) * Real.exp (-Real.rpow (κ.Qbd : ℝ) κ.aC) ≤ κ.a / 10 * (𝒯.P i).M := by
        nlinarith [ht, hm']
      exact hle.trans_lt (mul_lt_mul_of_pos_right (by linarith) hM)


/-- Eventual sampler size, test count, and stability margins; cliques larger than the host are trivial. -/
theorem sampler_numeric (κ : CConsts) (hκ : κ.Admissible) (T : Stage) :
    ∀ᶠ k in atTop,
      1 ≤ T.S.n k ∧
      2 * (T.S.n k : ℝ) ^ (-2 : ℝ) ≤ κ.θ ∧
      (T.S.n k : ℝ) ^ (-3 : ℝ) ≤ κ.θ ∧
      (T.S.N k) ^ 2 ≤ Nat.ceil (Real.exp (2 * (T.S.n k : ℝ))) * (T.S.n k) ^ 4 ∧
      ∀ Q : ℕ, Real.exp (Q : ℝ) ≤ T.S.N k →
        Q ≤ T.S.N k + 1 ∧
        Real.rpow (Q : ℝ) κ.aC ≤ (T.S.n k : ℝ) ^ (1 / 2 : ℝ) ∧
        (T.S.n k : ℝ) ^ 12 ≤ (T.S.N k : ℝ) *
          Real.exp (-(Real.rpow (Q : ℝ) κ.aC + (Real.rpow (Q : ℝ) κ.aC - 2)) / 2) := by
  have hn : Tendsto (fun k => (T.S.n k : ℝ)) atTop atTop :=
    tendsto_natCast_atTop_atTop.comp T.S.n_tendsto
  have hAC : κ.aC < 1 / 2 := by
    have ht := hκ.aC_rng.2
    have hm := min_le_right κ.η0 (1 : ℝ)
    linarith
  have hpow := (tendsto_rpow_atTop (by linarith : 0 < 1 / 2 - κ.aC)).comp hn
  have hsmall2 := (tendsto_rpow_neg_atTop (by norm_num : (0 : ℝ) < 2)).comp hn
  have hsmall3 := (tendsto_rpow_neg_atTop (by norm_num : (0 : ℝ) < 3)).comp hn
  filter_upwards [T.S.eventually_large 1 16,
    hpow.eventually (eventually_ge_atTop 2),
    hsmall2.eventually (Iio_mem_nhds (by linarith [hκ.θ_rng.1] : (0 : ℝ) < κ.θ / 2)),
    hsmall3.eventually (Iio_mem_nhds hκ.θ_rng.1),
    Lane_q_s13_clean.exp_quarter_dominates_pow12 T] with k hhost hpow hsmall2 hsmall3 hpoly
  rcases hhost with ⟨hn16, hhost⟩
  dsimp only [Function.comp_def] at hpow hsmall2 hsmall3
  have hn1 : 1 ≤ T.S.n k := by omega
  have hnR : (1 : ℝ) ≤ T.S.n k := by exact_mod_cast hn1
  have hnPos : (0 : ℝ) < T.S.n k := by linarith
  refine ⟨hn1, by linarith, hsmall3.le,
    Lane_q_s13_clean.host_pair_test_count hn1 hhost.2, ?_⟩
  intro Q hQ
  have hQr : Q ≤ T.S.N k + 1 := by
    have hq : Q ≤ T.S.N k := by exact_mod_cast (show (Q : ℝ) ≤ T.S.N k by linarith [Real.add_one_le_exp (Q : ℝ), hQ])
    omega
  have hlog2 : Real.log 2 ≤ 1 := by
    have ht := Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 2)
    norm_num at ht
    exact ht
  have h2 : (2 : ℝ) ^ (T.S.n k) ≤ Real.exp (T.S.n k : ℝ) := by
    calc
      (2 : ℝ) ^ T.S.n k = Real.exp (Real.log 2) ^ T.S.n k := by rw [Real.exp_log (by norm_num)]
      _ = Real.exp ((T.S.n k : ℝ) * Real.log 2) := (Real.exp_nat_mul _ _).symm
      _ ≤ Real.exp (T.S.n k : ℝ) := Real.exp_le_exp.mpr (by nlinarith)
  have hNexp : (T.S.N k : ℝ) ≤ Real.exp (2 * (T.S.n k : ℝ)) := by
    have hu : (T.S.N k : ℝ) ≤ (T.S.n k : ℝ) * (2 : ℝ) ^ T.S.n k := by exact_mod_cast hhost.2
    have hne : (T.S.n k : ℝ) ≤ Real.exp (T.S.n k : ℝ) := by linarith [Real.add_one_le_exp (T.S.n k : ℝ)]
    calc
      (T.S.N k : ℝ) ≤ (T.S.n k : ℝ) * (2 : ℝ) ^ T.S.n k := hu
      _ ≤ Real.exp (T.S.n k : ℝ) * Real.exp (T.S.n k : ℝ) :=
        mul_le_mul hne h2 (by positivity) (by positivity)
      _ = Real.exp (2 * (T.S.n k : ℝ)) := by rw [← Real.exp_add]; congr 1; ring
  have hQ2n : (Q : ℝ) ≤ 2 * (T.S.n k : ℝ) := Real.exp_le_exp.mp (hQ.trans hNexp)
  have hB : Real.rpow (Q : ℝ) κ.aC ≤ (T.S.n k : ℝ) ^ (1 / 2 : ℝ) := by
    have h2p : Real.rpow 2 κ.aC ≤ 2 := by
      calc Real.rpow 2 κ.aC ≤ Real.rpow 2 1 := Real.rpow_le_rpow_of_exponent_le (by norm_num) (by linarith)
           _ = 2 := Real.rpow_one _
    have ht : Real.rpow (T.S.n k : ℝ) κ.aC * 2 ≤
        Real.rpow (T.S.n k : ℝ) κ.aC * Real.rpow (T.S.n k : ℝ) (1 / 2 - κ.aC) :=
      mul_le_mul_of_nonneg_left hpow (Real.rpow_nonneg (Nat.cast_nonneg (T.S.n k)) κ.aC)
    have hr : Real.rpow (T.S.n k : ℝ) κ.aC * Real.rpow (T.S.n k : ℝ) (1 / 2 - κ.aC) =
        Real.rpow (T.S.n k : ℝ) (1 / 2 : ℝ) := by
      have hs : κ.aC + (1 / 2 - κ.aC) = (1 / 2 : ℝ) := by ring
      simpa only [Real.rpow_eq_pow, hs] using
        (Real.rpow_add hnPos κ.aC (1 / 2 - κ.aC)).symm
    calc
      Real.rpow (Q : ℝ) κ.aC ≤ Real.rpow (2 * (T.S.n k : ℝ)) κ.aC :=
        Real.rpow_le_rpow (Nat.cast_nonneg _) hQ2n hκ.aC_rng.1.le
      _ = Real.rpow 2 κ.aC * Real.rpow (T.S.n k : ℝ) κ.aC := Real.mul_rpow (by norm_num) (Nat.cast_nonneg _)
      _ ≤ 2 * Real.rpow (T.S.n k : ℝ) κ.aC :=
        mul_le_mul_of_nonneg_right h2p (Real.rpow_nonneg (Nat.cast_nonneg (T.S.n k)) κ.aC)
      _ ≤ (T.S.n k : ℝ) ^ (1 / 2 : ℝ) := by
        rw [hr] at ht
        simpa only [Real.rpow_eq_pow, mul_comm] using ht
  have hroot : Real.sqrt (T.S.n k : ℝ) ≤ (T.S.n k : ℝ) / 4 := by
    apply Real.sqrt_le_iff.mpr
    have hn16R : (16 : ℝ) ≤ T.S.n k := by exact_mod_cast hn16
    constructor
    · positivity
    · nlinarith [mul_nonneg (Nat.cast_nonneg (T.S.n k)) (sub_nonneg.mpr hn16R)]
  have hlog2lo : (1 / 2 : ℝ) ≤ Real.log 2 := by
    have ht := Real.one_sub_inv_le_log_of_pos (by norm_num : (0 : ℝ) < 2)
    norm_num at ht
    exact ht
  have hNlo : Real.exp ((T.S.n k : ℝ) / 2) ≤ T.S.N k := by
    calc
      Real.exp ((T.S.n k : ℝ) / 2) ≤ Real.exp ((T.S.n k : ℝ) * Real.log 2) :=
        Real.exp_le_exp.mpr (by nlinarith)
      _ = (2 : ℝ) ^ T.S.n k := by rw [Real.exp_nat_mul, Real.exp_log (by norm_num)]
      _ ≤ T.S.N k := by simpa [LargeHost] using hhost.1
  refine ⟨hQr, hB, ?_⟩
  have hbr : Real.rpow (Q : ℝ) κ.aC ≤ Real.sqrt (T.S.n k : ℝ) := by simpa [Real.sqrt_eq_rpow] using hB
  calc
    (T.S.n k : ℝ) ^ 12 ≤ Real.exp ((T.S.n k : ℝ) / 4) := hpoly
    _ ≤ Real.exp ((T.S.n k : ℝ) / 2) *
        Real.exp (-(Real.rpow (Q : ℝ) κ.aC + (Real.rpow (Q : ℝ) κ.aC - 2)) / 2) := by
      rw [← Real.exp_add]
      apply Real.exp_le_exp.mpr
      linarith [hbr, hroot]
    _ ≤ (T.S.N k : ℝ) * Real.exp (-(Real.rpow (Q : ℝ) κ.aC + (Real.rpow (Q : ℝ) κ.aC - 2)) / 2) :=
      mul_le_mul_of_nonneg_right hNlo (by positivity)

end HypercubeRamsey.S13.Lane_sol_s13_cleanB
