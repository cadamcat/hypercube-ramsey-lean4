import HypercubeRamsey.S10.ClusterExclusion_p_s10_1k
import HypercubeRamsey.Tools.CubeGeometry
import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import Mathlib.Data.Nat.Choose.Bounds

namespace HypercubeRamsey.Lane_q_s10_d10

open OAI.HypercubeRamsey Filter

theorem ceil_power_bounds {x p : ℝ} (hx : 1 ≤ x) (hp : 0 ≤ p) :
    x ^ p ≤ (⌈x ^ p⌉₊ : ℝ) ∧ (⌈x ^ p⌉₊ : ℝ) ≤ 2 * x ^ p := by
  have hpow : 1 ≤ x ^ p := Real.one_le_rpow hx hp
  exact ⟨Nat.le_ceil _, (Nat.ceil_lt_add_one (by positivity : 0 ≤ x ^ p)).le.trans
    (by linarith)⟩

private theorem firstScale_le (M R target : ℕ) (hex : ∃ i : ℕ, target ≤ M ^ i * R) :
    M ^ Nat.find hex * R ≤ max R (M * target) := by
  cases hi : Nat.find hex with
  | zero => simp [hi]
  | succ i =>
    have hbefore : M ^ i * R < target := by
      apply Nat.lt_of_not_ge
      apply Nat.find_min hex
      rw [hi]
      exact Nat.lt_succ_self i
    calc
      M ^ (i + 1) * R = M * (M ^ i * R) := by rw [pow_succ]; ring
      _ ≤ M * target := Nat.mul_le_mul_left _ hbefore.le
      _ ≤ max R (M * target) := le_max_right _ _

/-- The top height scale is at most four times its target exponent eventually. -/
theorem topScale_power_bound (σ ζ : ℝ) (hσ : 0 < σ) (hζ : ζ < 1) :
    ∀ᶠ n : ℕ in atTop,
      (topScale n σ ζ : ℝ) ≤ 4 * (n : ℝ) ^ (1 - ζ + σ) := by
  have hp : 0 < 1 - ζ + σ := by linarith
  have hlog := (isLittleO_log_rpow_rpow_atTop 2 hp).bound (by norm_num : (0 : ℝ) < 1)
  have hncast : Tendsto (fun n : ℕ => (n : ℝ)) atTop atTop := tendsto_natCast_atTop_atTop
  filter_upwards [hncast.eventually hlog, hncast.eventually (eventually_ge_atTop (1 : ℝ)),
    hncast.eventually ((tendsto_rpow_atTop hσ).eventually_ge_atTop (2 : ℝ))]
    with n hlog hn hM
  have hn0 : 0 < (n : ℝ) := by linarith
  simp only [Real.norm_eq_abs, Real.rpow_two, one_mul] at hlog
  rw [abs_of_nonneg (sq_nonneg (Real.log (n : ℝ))),
    abs_of_nonneg (Real.rpow_nonneg hn0.le _)] at hlog
  have hR : ((max 1 ⌈Real.log (n : ℝ) ^ 2⌉₊ : ℕ) : ℝ) ≤
      2 * (n : ℝ) ^ (1 - ζ + σ) := by
    rw [Nat.cast_max]
    apply max_le
    · have := Real.one_le_rpow hn hp.le
      norm_num
      linarith
    · have := Nat.ceil_lt_add_one (sq_nonneg (Real.log (n : ℝ)))
      have := Real.one_le_rpow hn hp.le
      linarith
  have hM' : ((max 2 ⌈(n : ℝ) ^ σ⌉₊ : ℕ) : ℝ) ≤ 2 * (n : ℝ) ^ σ := by
    rw [Nat.cast_max]
    apply max_le
    · norm_num
      linarith
    · exact (ceil_power_bounds hn hσ.le).2
  have htarget := (ceil_power_bounds hn (by linarith : 0 ≤ 1 - ζ)).2
  have hbound : topScale n σ ζ ≤
      max (max 1 ⌈Real.log (n : ℝ) ^ 2⌉₊)
        ((max 2 ⌈(n : ℝ) ^ σ⌉₊) * ⌈(n : ℝ) ^ (1 - ζ)⌉₊) := by
    unfold topScale
    exact firstScale_le _ _ _ _
  have hboundR := (Nat.cast_le (α := ℝ)).mpr hbound
  rw [Nat.cast_max, Nat.cast_mul] at hboundR
  apply hboundR.trans
  apply max_le
  · nlinarith [Real.rpow_nonneg hn0.le (1 - ζ + σ)]
  · calc
      _ ≤ (2 * (n : ℝ) ^ σ) * (2 * (n : ℝ) ^ (1 - ζ)) :=
        mul_le_mul hM' htarget (by positivity) (by positivity)
      _ = 4 * (n : ℝ) ^ (1 - ζ + σ) := by
        rw [show (2 * (n : ℝ) ^ σ) * (2 * (n : ℝ) ^ (1 - ζ)) =
          4 * ((n : ℝ) ^ σ * (n : ℝ) ^ (1 - ζ)) by ring, ← Real.rpow_add hn0]
        congr 2
        ring

/-- Any fixed polynomial power is dominated by an exponential in a positive power. -/
theorem power_exp_decay {a b c : ℝ} (ha : 0 < a) (hc : 0 < c) :
    Tendsto (fun n : ℕ => (n : ℝ) ^ b * Real.exp (-c * (n : ℝ) ^ a))
      atTop (nhds 0) := by
  have hpow : Tendsto (fun n : ℕ => (n : ℝ) ^ a) atTop atTop :=
    (_root_.tendsto_rpow_atTop ha).comp tendsto_natCast_atTop_atTop
  have hscaled : Tendsto
      (fun n : ℕ => ((n : ℝ) ^ a) ^ (b / a) *
        Real.exp (-c * (n : ℝ) ^ a)) atTop (nhds 0) :=
    (tendsto_rpow_mul_exp_neg_mul_atTop_nhds_zero (b / a) c hc).comp hpow
  have heq :
      (fun n : ℕ => (n : ℝ) ^ b * Real.exp (-c * (n : ℝ) ^ a)) =ᶠ[atTop]
        (fun n : ℕ => ((n : ℝ) ^ a) ^ (b / a) *
          Real.exp (-c * (n : ℝ) ^ a)) := by
    filter_upwards [Filter.eventually_atTop.mpr ⟨1, fun _ hn => hn⟩] with n hn
    have hnpos : 0 < (n : ℝ) := by exact_mod_cast (by omega : 0 < n)
    have hexp : a * (b / a) = b := by field_simp [ne_of_gt ha]
    rw [show (n : ℝ) ^ b = ((n : ℝ) ^ a) ^ (b / a) by
      rw [← Real.rpow_mul hnpos.le]
      rw [hexp]]
  exact hscaled.congr' heq.symm

/-- A strictly smaller power is eventually smaller than any fixed multiple of `n`. -/
theorem power_le_linear_eventually {a c : ℝ} (ha : a < 1) (hc : 0 < c) :
    ∀ᶠ n : ℕ in atTop, c * (n : ℝ) ^ a ≤ n := by
  have hpow : Tendsto (fun n : ℕ => (n : ℝ) ^ (1 - a)) atTop atTop :=
    (_root_.tendsto_rpow_atTop (sub_pos.mpr ha)).comp tendsto_natCast_atTop_atTop
  filter_upwards [hpow.eventually_ge_atTop c,
    Filter.eventually_atTop.mpr ⟨1, fun _ hn => hn⟩] with n hgap hn
  have hnpos : 0 < (n : ℝ) := by exact_mod_cast (by omega : 0 < n)
  calc
    c * (n : ℝ) ^ a ≤ (n : ℝ) ^ (1 - a) * (n : ℝ) ^ a :=
      mul_le_mul_of_nonneg_right hgap (Real.rpow_nonneg (by positivity) _)
    _ = n := by
      rw [← Real.rpow_add hnpos]
      rw [show 1 - a + a = 1 by ring, Real.rpow_one]

/-- A fixed lower power eventually dominates a smaller power by any constant. -/
theorem power_le_power_eventually {a b c : ℝ} (hab : a < b) (hc : 0 < c) :
    ∀ᶠ n : ℕ in atTop, c * (n : ℝ) ^ a ≤ (n : ℝ) ^ b := by
  have hpow : Tendsto (fun n : ℕ => (n : ℝ) ^ (b - a)) atTop atTop :=
    (_root_.tendsto_rpow_atTop (sub_pos.mpr hab)).comp tendsto_natCast_atTop_atTop
  filter_upwards [hpow.eventually_ge_atTop c,
    Filter.eventually_atTop.mpr ⟨1, fun _ hn => hn⟩] with n hgap hn
  have hnpos : 0 < (n : ℝ) := by exact_mod_cast (by omega : 0 < n)
  calc
    c * (n : ℝ) ^ a ≤ (n : ℝ) ^ (b - a) * (n : ℝ) ^ a :=
      mul_le_mul_of_nonneg_right hgap (Real.rpow_nonneg (by positivity) _)
    _ = (n : ℝ) ^ b := by
      rw [← Real.rpow_add hnpos]
      congr 1
      ring

/-- A fixed multiple of `n` is eventually below any power strictly above one. -/
theorem linear_le_power_eventually {a c : ℝ} (ha : 1 < a) (hc : 0 < c) :
    ∀ᶠ n : ℕ in atTop, c * n ≤ (n : ℝ) ^ a := by
  have hpow : Tendsto (fun n : ℕ => (n : ℝ) ^ (a - 1)) atTop atTop :=
    (_root_.tendsto_rpow_atTop (sub_pos.mpr ha)).comp tendsto_natCast_atTop_atTop
  filter_upwards [hpow.eventually_ge_atTop c,
    Filter.eventually_atTop.mpr ⟨1, fun _ hn => hn⟩] with n hgap hn
  have hnpos : 0 < (n : ℝ) := by exact_mod_cast (by omega : 0 < n)
  calc
    c * n ≤ (n : ℝ) ^ (a - 1) * n := mul_le_mul_of_nonneg_right hgap (by positivity)
    _ = (n : ℝ) ^ (a - 1) * (n : ℝ) ^ (1 : ℝ) := by rw [Real.rpow_one]
    _ = (n : ℝ) ^ a := by
      rw [← Real.rpow_add hnpos]
      congr 1
      ring

/-- The logarithm of `n` is eventually below any positive power of `n`. -/
theorem log_nat_le_rpow_eventually {a : ℝ} (ha : 0 < a) :
    ∀ᶠ n : ℕ in atTop, Real.log (n : ℝ) ≤ (n : ℝ) ^ a := by
  let b : ℝ := a / 2
  have hb : 0 < b := by dsimp [b]; linarith
  have hconst : ∀ᶠ n : ℕ in atTop, 1 / b ≤ (n : ℝ) ^ b := by
    have htend : Tendsto (fun n : ℕ => (n : ℝ) ^ b) atTop atTop :=
      (_root_.tendsto_rpow_atTop hb).comp tendsto_natCast_atTop_atTop
    exact htend.eventually_ge_atTop (1 / b)
  filter_upwards [hconst, Filter.eventually_atTop.mpr ⟨1, fun _ hn => hn⟩] with n hlarge hn
  have hnpos : 0 < (n : ℝ) := by exact_mod_cast (by omega : 0 < n)
  have hlog := Real.log_natCast_le_rpow_div n hb
  calc
    Real.log (n : ℝ) ≤ (n : ℝ) ^ b / b := hlog
    _ = (1 / b) * (n : ℝ) ^ b := by ring
    _ ≤ ((n : ℝ) ^ b) * ((n : ℝ) ^ b) :=
      mul_le_mul_of_nonneg_right hlarge (Real.rpow_nonneg hnpos.le _)
    _ = (n : ℝ) ^ a := by
      rw [← Real.rpow_add hnpos]
      congr 1
      dsimp [b]
      ring

/-- A Hamming ball is encoded by the set of changed coordinates, padded to length `R`. -/
theorem hammingBall_card_le_pow {d R : ℕ} (v : CubeVertex d) :
    (Finset.univ.filter fun u : CubeVertex d => hammingDist v u ≤ R).card ≤ (d + 1) ^ R := by
  classical
  let B : Finset (CubeVertex d) := Finset.univ.filter fun u => hammingDist v u ≤ R
  let diff : CubeVertex d → Finset (Fin d) := fun u =>
    Finset.univ.filter fun i => v i ≠ u i
  have hdiff (u : CubeVertex d) : (diff u).card = hammingDist v u := by
    simp [diff, hammingDist, ne_comm]
  have hdiffCard (u : {u : CubeVertex d // u ∈ B}) : (diff u.1).card ≤ R := by
    have hu : hammingDist v u.1 ≤ R := (Finset.mem_filter.mp u.2).2
    rw [hdiff]
    exact hu
  let code (u : {u : CubeVertex d // u ∈ B}) : Fin R → Option (Fin d) := fun j =>
    if hj : j.val < (diff u.1).card then
      some ((diff u.1).equivFin.symm ⟨j.val, hj⟩).1 else none
  have hcodeMem (u : {u : CubeVertex d // u ∈ B}) (i : Fin d) :
      i ∈ diff u.1 ↔ ∃ j : Fin R, code u j = some i := by
    constructor
    · intro hi
      let k := (diff u.1).equivFin ⟨i, hi⟩
      have hkR : k.val < R := lt_of_lt_of_le k.isLt (hdiffCard u)
      let j : Fin R := ⟨k.val, hkR⟩
      refine ⟨j, ?_⟩
      have hj : j.val < (diff u.1).card := by simpa [j] using k.isLt
      have hfin : (⟨j.val, hj⟩ : Fin (diff u.1).card) = k := Fin.ext rfl
      have hval := congrArg Subtype.val (congrArg (diff u.1).equivFin.symm hfin)
      have hval' : ((diff u.1).equivFin.symm ⟨j.val, hj⟩).1 = i := by
        simpa [k] using hval
      simp [code, hj, hval']
    · rintro ⟨j, hj⟩
      by_cases hsmall : j.val < (diff u.1).card
      · have hval : ((diff u.1).equivFin.symm ⟨j.val, hsmall⟩).1 = i := by
          have hsome : some ((diff u.1).equivFin.symm ⟨j.val, hsmall⟩).1 = some i := by
            simpa [code, hsmall] using hj
          exact Option.some.inj hsome
        have hmem : ((diff u.1).equivFin.symm ⟨j.val, hsmall⟩).1 ∈ diff u.1 :=
          ((diff u.1).equivFin.symm ⟨j.val, hsmall⟩).2
        simpa [hval] using hmem
      · simp [code, hsmall] at hj

  have hinj : Function.Injective code := by
    intro x y hxy
    apply Subtype.ext
    funext i
    have hdiffEq : (i ∈ diff x.1) ↔ (i ∈ diff y.1) := by
      rw [hcodeMem x i, hcodeMem y i]
      constructor
      · rintro ⟨j, hj⟩
        exact ⟨j, by simpa [hxy] using hj⟩
      · rintro ⟨j, hj⟩
        exact ⟨j, by simpa [hxy] using hj⟩
    have hdiffBit : v i ≠ x.1 i ↔ v i ≠ y.1 i := by
      simpa [diff] using hdiffEq
    cases hv : v i <;> cases hx : x.1 i <;> cases hy : y.1 i <;>
      simp_all
  have hcardB : B.card = Fintype.card {u : CubeVertex d // u ∈ B} := by
    simpa using (Fintype.card_coe B).symm
  calc
    (Finset.univ.filter fun u : CubeVertex d => hammingDist v u ≤ R).card = B.card := rfl
    _ = Fintype.card {u : CubeVertex d // u ∈ B} := hcardB
    _ ≤ Fintype.card (Fin R → Option (Fin d)) := Fintype.card_le_of_injective code hinj
    _ = (d + 1) ^ R := by simp

/-- The number of binary chunks used by the projection is logarithmic. -/
theorem bitIndices_length_le_log (d : ℕ) :
    d.bitIndices.length ≤ Nat.log 2 d + 1 := by
  classical
  by_cases hd : d = 0
  · simp [hd]
  have hsubset : d.bitIndices.toFinset ⊆ Finset.range (Nat.log 2 d + 1) := by
    intro i hi
    have himem : i ∈ d.bitIndices := List.mem_toFinset.mp hi
    have hpow : 2 ^ i ≤ d := Nat.two_pow_le_of_mem_bitIndices himem
    have hiBound : i ≤ Nat.log 2 d :=
      (Nat.le_log_iff_pow_le (by decide : 1 < 2) hd).2 hpow
    exact Finset.mem_range.mpr (Nat.lt_succ_of_le hiBound)
  calc
    d.bitIndices.length = d.bitIndices.toFinset.card := by
      rw [List.toFinset_card_of_nodup Nat.bitIndices_nodup]
    _ ≤ (Finset.range (Nat.log 2 d + 1)).card := Finset.card_le_card hsubset
    _ = Nat.log 2 d + 1 := by simp

/-- The logarithmic chunk count is absorbed by any positive power eventually. -/
theorem natLog_add_one_le_rpow_eventually (δ : ℝ) (hδ : 0 < δ) :
    ∀ᶠ n : ℕ in atTop, (Nat.log 2 n : ℝ) + 1 ≤ (n : ℝ) ^ (2 * δ) := by
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  let C : ℝ := 1 / (δ * Real.log 2) + 1
  have hC : 0 < C := by positivity
  have hnPow : Tendsto (fun n : ℕ => (n : ℝ) ^ δ) atTop atTop :=
    (_root_.tendsto_rpow_atTop hδ).comp tendsto_natCast_atTop_atTop
  filter_upwards [eventually_atTop.mpr ⟨2, fun _ hn => hn⟩,
    hnPow.eventually_ge_atTop C] with n hn hlarge
  have hn0 : 0 < (n : ℝ) := by exact_mod_cast (by omega : 0 < n)
  have hlog : Real.log (n : ℝ) ≤ (n : ℝ) ^ δ / δ := Real.log_natCast_le_rpow_div n hδ
  have hlogb : (Nat.log 2 n : ℝ) ≤ Real.log (n : ℝ) / Real.log 2 := by
    calc
      (Nat.log 2 n : ℝ) ≤ Real.logb 2 n := Real.natLog_le_logb n 2
      _ = Real.log (n : ℝ) / Real.log 2 := by rfl
  have hlogbound : (Nat.log 2 n : ℝ) + 1 ≤ C * (n : ℝ) ^ δ := by
    have hpow1 : 1 ≤ (n : ℝ) ^ δ := Real.one_le_rpow (by exact_mod_cast (by omega : 1 ≤ n)) hδ.le
    have hlogn' : Real.log (n : ℝ) / Real.log 2 ≤
        ((n : ℝ) ^ δ / δ) / Real.log 2 :=
      div_le_div_of_nonneg_right hlog (by positivity)
    have hcoef : ((n : ℝ) ^ δ / δ) / Real.log 2 =
        (1 / (δ * Real.log 2)) * (n : ℝ) ^ δ := by
      field_simp [ne_of_gt hδ, ne_of_gt hlog2]
      <;> ring
    calc
      (Nat.log 2 n : ℝ) + 1 ≤
          ((n : ℝ) ^ δ / δ) / Real.log 2 + 1 := by linarith [hlogb, hlogn']
      _ = (1 / (δ * Real.log 2)) * (n : ℝ) ^ δ + 1 := by rw [hcoef]
      _ ≤ C * (n : ℝ) ^ δ := by
        dsimp [C]
        nlinarith [hpow1]
  have hlarge' : C ≤ (n : ℝ) ^ δ := hlarge
  have hmul : C * (n : ℝ) ^ δ ≤ ((n : ℝ) ^ δ) ^ 2 := by
    have hdiff : 0 ≤ (n : ℝ) ^ δ - C := sub_nonneg.mpr hlarge'
    have hpow : 0 ≤ (n : ℝ) ^ δ := Real.rpow_nonneg hn0.le δ
    have hprod := mul_nonneg hdiff hpow
    nlinarith
  have hpow : ((n : ℝ) ^ δ) ^ 2 = (n : ℝ) ^ (2 * δ) := by
    calc
      ((n : ℝ) ^ δ) ^ 2 = ((n : ℝ) ^ δ) ^ (2 : ℝ) :=
        (Real.rpow_natCast ((n : ℝ) ^ δ) 2).symm
      _ = (n : ℝ) ^ (δ * 2) := (Real.rpow_mul hn0.le δ 2).symm
      _ = (n : ℝ) ^ (2 * δ) := by congr 1; ring
  calc
    (Nat.log 2 n : ℝ) + 1 ≤ C * (n : ℝ) ^ δ := hlogbound
    _ ≤ ((n : ℝ) ^ δ) ^ 2 := hmul
    _ = (n : ℝ) ^ (2 * δ) := hpow

end HypercubeRamsey.Lane_q_s10_d10
