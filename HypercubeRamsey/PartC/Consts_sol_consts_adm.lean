import HypercubeRamsey.PartC.Core
import HypercubeRamsey.Framework.LawLemmas
import HypercubeRamsey.S03.ClockSampling
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import Mathlib.Analysis.SpecialFunctions.Log.NegMulLog
import Mathlib.Algebra.Order.Floor.Semifield

namespace HypercubeRamsey.Lane_sol_consts_adm

open Filter
open scoped Topology

theorem deep_mono {T : Stage} {x α ε x' α' : ℝ} (h : DeepDisc T x α ε)
    (hx : x' ≤ x) (hα : α' ≤ α) : DeepDisc T x' α' ε := by
  have hn : ∀ᶠ k in atTop, (1 : ℝ) ≤ T.S.n k :=
    ((tendsto_natCast_atTop_atTop : Tendsto (fun n : ℕ => (n : ℝ)) atTop atTop).comp
      T.S.n_tendsto).eventually (eventually_ge_atTop 1)
  filter_upwards [h, hn] with k hk hn c μ ν hμ hν hw
  apply hk c μ ν hμ hν
  have hS := Real.rpow_le_rpow_of_exponent_le hn hx
  have hL := mul_le_mul_of_nonneg_right hα (Nat.cast_nonneg (T.S.n k))
  rcases hw with hw | hw
  · exact Or.inl ⟨hw.1.mono hL, hw.2.mono hS⟩
  · exact Or.inr ⟨hw.1.mono hS, hw.2.mono hL⟩

theorem eventually_power_bound (s t A B : ℝ) (hst : s < t) (hB : 0 < B) :
    ∀ᶠ x : ℝ in atTop, A * x ^ s ≤ B * x ^ t := by
  have hlim : Tendsto (fun x : ℝ => A * x ^ (s - t)) atTop (𝓝 0) := by
    simpa [neg_sub] using (tendsto_rpow_neg_atTop (sub_pos.mpr hst)).const_mul A
  filter_upwards [hlim.eventually (gt_mem_nhds hB), eventually_gt_atTop (0 : ℝ)]
    with x hx hx0
  have hp : 0 < x ^ t := Real.rpow_pos_of_pos hx0 _
  have he : x ^ (s - t) * x ^ t = x ^ s := by
    rw [← Real.rpow_add hx0]
    congr 1
    ring
  have hm := (mul_le_mul_of_nonneg_right hx.le hp.le)
  simpa only [mul_assoc, he] using hm

theorem eventually_power_sum (s₁ s₂ t A₁ A₂ C B : ℝ)
    (h₁ : s₁ < t) (h₂ : s₂ < t) (ht : 0 < t) (hB : 0 < B) :
    ∀ᶠ x : ℝ in atTop, A₁ * x ^ s₁ + A₂ * x ^ s₂ + C ≤ B * x ^ t := by
  filter_upwards [eventually_power_bound s₁ t A₁ (B / 3) h₁ (by positivity),
    eventually_power_bound s₂ t A₂ (B / 3) h₂ (by positivity),
    eventually_power_bound 0 t C (B / 3) ht (by positivity)] with x h₁ h₂ h₃
  simp only [Real.rpow_zero, mul_one] at h₃
  linarith

theorem eventually_exp_bound (s A b : ℝ) (hb : 0 < b) :
    ∀ᶠ x : ℝ in atTop, A * x ^ s ≤ Real.exp (b * x) := by
  have hlim : Tendsto (fun x : ℝ => A * (x ^ s * Real.exp (-b * x))) atTop (𝓝 0) := by
    simpa using (tendsto_rpow_mul_exp_neg_mul_atTop_nhds_zero s b hb).const_mul A
  filter_upwards [hlim.eventually (gt_mem_nhds (show (0 : ℝ) < 1 by norm_num))]
    with x hx
  have hm := mul_le_mul_of_nonneg_right hx.le (Real.exp_pos (b * x)).le
  simpa [mul_assoc, ← Real.exp_add] using hm

theorem tendsto_power_exp_power (s t b : ℝ) (ht : 0 < t) (hb : 0 < b) :
    Tendsto (fun x : ℝ => x ^ s * Real.exp (-b * x ^ t)) atTop (𝓝 0) := by
  have h := (tendsto_rpow_mul_exp_neg_mul_atTop_nhds_zero (s / t) b hb).comp
    (tendsto_rpow_atTop ht)
  refine h.congr' ?_
  filter_upwards [eventually_ge_atTop (0 : ℝ)] with x hx
  dsimp
  rw [← Real.rpow_mul hx, mul_div_cancel₀ _ ht.ne']

theorem entropy_small (a : ℝ) (ha : 0 < a) :
    ∃ ρ : ℝ, 0 < ρ ∧ ρ < 1 / 4000 ∧
      -(1000 * ρ) * Real.log (1000 * ρ) -
        (1 - 1000 * ρ) * Real.log (1 - 1000 * ρ) < a / 10 ^ 9 := by
  have hc : Continuous (fun r : ℝ =>
      -(1000 * r) * Real.log (1000 * r) -
        (1 - 1000 * r) * Real.log (1 - 1000 * r)) := by
    have h1 : Continuous (fun r : ℝ => (1000 * r) * Real.log (1000 * r)) :=
      Real.continuous_mul_log.comp (continuous_const.mul continuous_id)
    have h2 : Continuous (fun r : ℝ => (1 - 1000 * r) * Real.log (1 - 1000 * r)) :=
      Real.continuous_mul_log.comp (continuous_const.sub (continuous_const.mul continuous_id))
    convert h1.neg.sub h2 using 1
    ext r
    simp only [Pi.sub_apply, Pi.neg_apply]
    ring
  have hlim : Tendsto (fun r : ℝ =>
      -(1000 * r) * Real.log (1000 * r) -
        (1 - 1000 * r) * Real.log (1 - 1000 * r)) (𝓝[>] 0) (𝓝 0) := by
    simpa using (hc.tendsto 0).mono_left nhdsWithin_le_nhds
  have he := hlim.eventually (gt_mem_nhds (show (0 : ℝ) < a / 10 ^ 9 by positivity))
  have hr : ∀ᶠ r : ℝ in 𝓝[>] 0, r < 1 / 4000 :=
    (eventually_lt_nhds (show (0 : ℝ) < 1 / 4000 by norm_num)).filter_mono
      nhdsWithin_le_nhds
  have hpos : ∀ᶠ r : ℝ in 𝓝[>] 0, 0 < r := self_mem_nhdsWithin
  obtain ⟨r, hpos, hsmall, hentropy⟩ := (hpos.and (hr.and he)).exists
  exact ⟨r, hpos, hsmall, hentropy⟩

theorem exp_decay_le (a x k : ℝ) (ha : 0 ≤ a) (hx : 0 ≤ x) (hk : 1 ≤ k) :
    Real.exp (-a * k * x) ≤ Real.exp (-a * x) := by
  apply Real.exp_le_exp.mpr
  have h := mul_le_mul_of_nonneg_right hk (mul_nonneg ha hx)
  nlinarith

theorem sqrt_exp_eq (x : ℝ) : Real.sqrt (Real.exp x) = Real.exp (x / 2) := by
  rw [Real.sqrt_eq_rpow, ← Real.exp_mul]
  congr 1
  ring

theorem height_bounds (a ω : ℝ) (ha : 0 < a) (hω : 0 < ω) :
    ∀ᶠ h : ℝ in atTop,
      let K : ℝ := ⌈h ^ (3 * ω)⌉₊
      let T : ℝ := ⌈h ^ ω⌉₊
      1 ≤ h ∧
      T * Real.log h ≤ (1 / 1000 : ℝ) * a ^ 2 * K / 10 ∧
      0.02 * a * h - Real.log (200 / a) ≥ 0.0005 * a * h ∧
      (2 : ℝ) ^ ⌈h ^ (3 * ω)⌉₊ * Real.exp (-0.013 * a * K * h) ≤ 1 / 2 ∧
      Real.exp ((a / 10 ^ 9) * h) * (h + 1) * Real.exp (-0.01 * a * K * h) ≤
        Real.exp (-0.009 * a * K * h) ∧
      h ^ 6 * Real.sqrt (Real.exp (-0.001 * a * K * h)) ≤ Real.rpow 10 (-3) ∧
      Real.exp (-(h ^ (2 : ℝ))) +
        2 * h ^ 2 * Real.sqrt (Real.exp (-0.001 * a * K * h)) ≤ Real.rpow 10 (-5) := by
  have hlog : ∀ᶠ h : ℝ in atTop, Real.log h ≤ (a ^ 2 / 20000) * h ^ (2 * ω) := by
    have he := (isLittleO_log_rpow_atTop (show 0 < 2 * ω by positivity)).bound
      (show 0 < a ^ 2 / 20000 by positivity)
    filter_upwards [he, eventually_ge_atTop (1 : ℝ)] with h he hh
    simpa [Real.norm_of_nonneg (Real.log_nonneg hh),
      Real.norm_of_nonneg (Real.rpow_nonneg (by linarith : 0 ≤ h) _)] using he
  have hlin := eventually_power_bound 0 1 (Real.log (200 / a)) (0.0195 * a)
    (by norm_num) (by positivity)
  have hlog2 := eventually_power_bound 0 1 (Real.log 2) (0.003 * a)
    (by norm_num) (by positivity)
  have hehalf : ∀ᶠ h : ℝ in atTop, Real.exp (-0.01 * a * h) ≤ 1 / 2 := by
    have he := Real.tendsto_exp_atBot.comp
      (tendsto_id.const_mul_atTop_of_neg (show -0.01 * a < 0 by nlinarith [ha]))
    exact (he.eventually (gt_mem_nhds (show (0 : ℝ) < 1 / 2 by norm_num))).mono
      fun _ h => h.le
  have hplus : ∀ᶠ h : ℝ in atTop, h + 1 ≤ Real.exp (0.0005 * a * h) := by
    filter_upwards [eventually_exp_bound 1 2 (0.0005 * a) (by positivity),
      eventually_ge_atTop (1 : ℝ)] with h he hh
    simp only [Real.rpow_one] at he
    linarith
  have hdec6 := (tendsto_rpow_mul_exp_neg_mul_atTop_nhds_zero 6 (0.0005 * a)
    (by positivity)).eventually
      (gt_mem_nhds (show (0 : ℝ) < Real.rpow 10 (-3) from Real.rpow_pos_of_pos (by norm_num) _))
  have hdec2lim : Tendsto (fun h : ℝ => 2 * (h ^ (2 : ℝ) * Real.exp (-(0.0005 * a) * h))) atTop (𝓝 0) := by
    simpa using (tendsto_rpow_mul_exp_neg_mul_atTop_nhds_zero 2 (0.0005 * a)
      (by positivity)).const_mul 2
  have hdec2 := hdec2lim.eventually
    (gt_mem_nhds (show (0 : ℝ) < Real.rpow 10 (-5) / 2 from
      div_pos (Real.rpow_pos_of_pos (by norm_num) _) (by norm_num)))
  have hexp2 := (tendsto_power_exp_power 0 2 1 (by norm_num) (by norm_num)).eventually
    (gt_mem_nhds (show (0 : ℝ) < Real.rpow 10 (-5) / 2 from
      div_pos (Real.rpow_pos_of_pos (by norm_num) _) (by norm_num)))
  filter_upwards [hlog, hlin, hlog2, hehalf, hplus, hdec6, hdec2, hexp2,
    eventually_ge_atTop (1 : ℝ)] with h hlog hlin hlog2 hehalf hplus hdec6 hdec2 hexp2 hh
  dsimp only
  let K : ℝ := ⌈h ^ (3 * ω)⌉₊
  let T : ℝ := ⌈h ^ ω⌉₊
  have hK : h ^ (3 * ω) ≤ K := Nat.le_ceil _
  have hK1 : 1 ≤ K := (Real.one_le_rpow hh (by positivity)).trans hK
  have hT : T ≤ 2 * h ^ ω := Nat.ceil_le_two_mul
    ((show (2 : ℝ)⁻¹ ≤ 1 by norm_num).trans (Real.one_le_rpow hh hω.le))
  have hsqrt : Real.sqrt (Real.exp (-0.001 * a * K * h)) ≤
      Real.exp (-0.0005 * a * h) := by
    rw [sqrt_exp_eq]
    have he : (-0.001 * a * K * h) / 2 = -0.0005 * a * K * h := by ring
    rw [he]
    simpa only [neg_mul] using exp_decay_le (0.0005 * a) h K (by positivity) (by linarith : 0 ≤ h) hK1
  refine ⟨hh, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · calc
      T * Real.log h ≤ (2 * h ^ ω) * ((a ^ 2 / 20000) * h ^ (2 * ω)) :=
        mul_le_mul hT hlog (Real.log_nonneg hh) (by positivity)
      _ = (a ^ 2 / 10000) * h ^ (3 * ω) := by
        rw [show 3 * ω = ω + 2 * ω by ring, Real.rpow_add (by linarith : 0 < h)]
        ring
      _ ≤ (1 / 1000 : ℝ) * a ^ 2 * K / 10 := by nlinarith [mul_le_mul_of_nonneg_left hK (sq_nonneg a)]
  · simp only [Real.rpow_zero, Real.rpow_one, mul_one] at hlin
    linarith
  · simp only [Real.rpow_zero, Real.rpow_one, mul_one] at hlog2
    have he : (2 : ℝ) ^ ⌈h ^ (3 * ω)⌉₊ = Real.exp (K * Real.log 2) := by
      rw [Real.exp_nat_mul, Real.exp_log (by norm_num : (0 : ℝ) < 2)]
    rw [he, ← Real.exp_add]
    calc
      Real.exp (K * Real.log 2 + -0.013 * a * K * h) ≤ Real.exp (-0.01 * a * K * h) := by
        apply Real.exp_le_exp.mpr
        nlinarith [mul_le_mul_of_nonneg_left hlog2 (show 0 ≤ K by positivity)]
      _ ≤ Real.exp (-0.01 * a * h) := by
        simpa only [neg_mul] using exp_decay_le (0.01 * a) h K (by positivity) (by linarith : 0 ≤ h) hK1
      _ ≤ 1 / 2 := hehalf
  · calc
      Real.exp ((a / 10 ^ 9) * h) * (h + 1) * Real.exp (-0.01 * a * K * h) ≤
          Real.exp ((a / 10 ^ 9) * h) * Real.exp (0.0005 * a * h) *
            Real.exp (-0.01 * a * K * h) := by gcongr
      _ = Real.exp ((a / 10 ^ 9) * h + 0.0005 * a * h - 0.01 * a * K * h) := by
        rw [← Real.exp_add, ← Real.exp_add]
        congr 1
        ring
      _ ≤ Real.exp (-0.009 * a * K * h) := by
        apply Real.exp_le_exp.mpr
        nlinarith [mul_le_mul_of_nonneg_right hK1 (mul_nonneg ha.le (by linarith : 0 ≤ h))]
  · have he : h ^ 6 * Real.exp (-0.0005 * a * h) ≤ Real.rpow 10 (-3) := by
      simpa only [Real.rpow_ofNat, neg_mul, mul_assoc] using hdec6.le
    exact (mul_le_mul_of_nonneg_left hsqrt (by positivity)).trans he
  · have he : 2 * h ^ 2 * Real.exp (-0.0005 * a * h) ≤ Real.rpow 10 (-5) / 2 := by
      simpa only [Real.rpow_ofNat, neg_mul, mul_assoc] using hdec2.le
    have he2 : Real.exp (-(h ^ (2 : ℝ))) ≤ Real.rpow 10 (-5) / 2 := by
      simpa only [Real.rpow_zero, one_mul, neg_mul] using hexp2.le
    have he3 := (mul_le_mul_of_nonneg_left hsqrt (show 0 ≤ 2 * h ^ 2 by positivity)).trans he
    linarith

theorem bin_bounds (Mhi : ℝ) (d0 : ℕ) :
    ∀ᶠ q : ℝ in atTop,
      let d := ⌊Real.exp (q / 2)⌋₊
      d0 ≤ d ∧
      (d : ℝ) ^ (-0.05 : ℝ) + (d : ℝ) ^ (-0.01 : ℝ) ≤ Real.rpow 10 (-3) ∧
      2 * q ^ Mhi ≤ (d : ℝ) ^ (0.01 : ℝ) ∧
      (d : ℝ) * Real.exp (-((d : ℝ) ^ (0.4 : ℝ))) ≤
        ((d : ℝ) ^ (-10 : ℝ)) / 2 := by
  have hq : Tendsto (fun q : ℝ => q / 2) atTop atTop := by
    simpa [div_eq_mul_inv] using tendsto_id.atTop_mul_const (show (0 : ℝ) < 2⁻¹ by norm_num)
  have hdNat := tendsto_nat_floor_atTop.comp (Real.tendsto_exp_atTop.comp hq)
  have hd : Tendsto (fun q : ℝ => (⌊Real.exp (q / 2)⌋₊ : ℝ)) atTop atTop :=
    tendsto_natCast_atTop_atTop.comp hdNat
  have hneg := ((tendsto_rpow_neg_atTop (by norm_num : (0 : ℝ) < 0.05)).add
    (tendsto_rpow_neg_atTop (by norm_num : (0 : ℝ) < 0.01))).comp hd
  have htail := (tendsto_power_exp_power 11 0.4 1 (by norm_num) (by norm_num)).comp hd
  have hlower : ∀ᶠ q : ℝ in atTop,
      Real.exp (q / 4) ≤ (⌊Real.exp (q / 2)⌋₊ : ℝ) := by
    have hq4 : Tendsto (fun q : ℝ => q / 4) atTop atTop := by
      simpa [div_eq_mul_inv] using tendsto_id.atTop_mul_const (show (0 : ℝ) < 4⁻¹ by norm_num)
    filter_upwards [(Real.tendsto_exp_atTop.comp hq4).eventually (eventually_ge_atTop (2 : ℝ))]
      with q he
    have hf := Nat.sub_one_lt_floor (Real.exp (q / 2))
    have hexp : Real.exp (q / 2) = Real.exp (q / 4) ^ 2 := by
      rw [← Real.exp_nat_mul]
      congr 1
      norm_num
      ring
    dsimp only [Function.comp_def] at he
    nlinarith [hexp]
  filter_upwards [hdNat.eventually (eventually_ge_atTop d0),
    hneg.eventually (gt_mem_nhds (show (0 : ℝ) + 0 < Real.rpow 10 (-3) by simpa using (Real.rpow_pos_of_pos (by norm_num : (0 : ℝ) < 10) (-3)))),
    htail.eventually (gt_mem_nhds (show (0 : ℝ) < 1 / 2 by norm_num)),
    hlower, eventually_exp_bound Mhi 2 (1 / 400) (by norm_num),
    hd.eventually (eventually_gt_atTop (0 : ℝ))] with q hd0 hneg htail hlower hpoly hdpos
  dsimp only
  let d : ℝ := ⌊Real.exp (q / 2)⌋₊
  refine ⟨hd0, hneg.le, ?_, ?_⟩
  · calc
      2 * q ^ Mhi ≤ Real.exp ((1 / 400) * q) := hpoly
      _ = (Real.exp (q / 4)) ^ (0.01 : ℝ) := by
        rw [← Real.exp_mul]
        congr 1
        ring
      _ ≤ d ^ (0.01 : ℝ) := Real.rpow_le_rpow (Real.exp_pos _).le hlower (by norm_num)
  · have ht : d ^ (11 : ℝ) * Real.exp (-(d ^ (0.4 : ℝ))) ≤ 1 / 2 := by
      simpa [Function.comp_def, d] using htail.le
    calc
      d * Real.exp (-(d ^ (0.4 : ℝ))) =
          (d ^ (11 : ℝ) * Real.exp (-(d ^ (0.4 : ℝ)))) * d ^ (-10 : ℝ) := by
        rw [mul_right_comm, ← Real.rpow_add hdpos]
        norm_num [d]
      _ ≤ (1 / 2 : ℝ) * d ^ (-10 : ℝ) :=
        mul_le_mul_of_nonneg_right ht (Real.rpow_nonneg (by positivity) _)
      _ = d ^ (-10 : ℝ) / 2 := by ring

theorem large_bounds (a aC aB M1 Cb Mlo Mhi ω C u : ℝ)
    (ha : 0 < a) (hu : 0 < u) (hM1 : 0 < M1)
    (haC : 0 < aC) (haB : 0 < aB) (haB1 : aB < 1)
    (hCb : 1 < Cb) (hloC : aC < Mlo) (hlo2 : 2 < Mlo) (hloB : Cb < Mlo)
    (hcbC : aC < Cb * aB) (hcbω : 4 * ω * Mhi < Cb * aB)
    (hcω : 4 * ω * Mhi < 2 * aC) :
    ∀ᶠ q : ℝ in atTop,
      (Real.rpow 2 aB - 1) * Real.rpow (M1 * q) aB ≥ Real.log (800 / (a * (1 / 400 : ℝ))) ∧
      (Real.rpow q aC + 10 ≤ (a / 10 ^ 6) * Real.rpow q Mlo / (1000 * u)) ∧
      (Real.rpow (M1 * q) aB + 10 ≤ M1 * q / (10 ^ 6 * u)) ∧
      (M1 * q < Real.rpow q Cb) ∧
      (Real.rpow q (Cb * aB) ≥ 2 * Real.rpow q aC +
        2 * Real.rpow (2 * q) (4 * ω * Mhi) + Real.log (800 / (a * (1 / 400 : ℝ)))) ∧
      (Real.rpow q (2 * aC) ≥ 2 * Real.rpow q aC +
        2 * Real.rpow (2 * q) (4 * ω * Mhi) + Real.log (800 / (a * (1 / 400 : ℝ)))) ∧
      (4 * C * q ^ 2 ≤ (a / 10 ^ 6) * Real.rpow q Mlo) ∧
      (40 * Real.rpow q Cb ≤ (a / 10 ^ 6) * Real.rpow q Mlo / (100 * u)) := by
  let Z := Real.log (800 / (a * (1 / 400 : ℝ)))
  have hcoeff : 0 < (Real.rpow 2 aB - 1) * M1 ^ aB :=
    mul_pos (sub_pos.mpr (Real.one_lt_rpow (by norm_num) haB))
      (Real.rpow_pos_of_pos hM1 _)
  have he1 := eventually_power_bound 0 aB Z
    ((Real.rpow 2 aB - 1) * M1 ^ aB) haB hcoeff
  have he2 := eventually_power_sum aC 0 Mlo 1 0 10
    ((a / 10 ^ 6) / (1000 * u)) hloC (by linarith) (by linarith) (by positivity)
  have he3 := eventually_power_sum aB 0 1 (M1 ^ aB) 0 10
    (M1 / (10 ^ 6 * u)) haB1 (by norm_num) (by norm_num) (by positivity)
  have he4 := eventually_power_bound 1 Cb M1 (1 / 2) hCb (by norm_num)
  have he5 := eventually_power_sum aC (4 * ω * Mhi) (Cb * aB) 2
    (2 * (2 : ℝ) ^ (4 * ω * Mhi)) Z 1 hcbC hcbω (by positivity) (by norm_num)
  have he6 := eventually_power_sum aC (4 * ω * Mhi) (2 * aC) 2
    (2 * (2 : ℝ) ^ (4 * ω * Mhi)) Z 1 (by linarith) hcω (by positivity) (by norm_num)
  have he7 := eventually_power_bound 2 Mlo (4 * C) (a / 10 ^ 6) hlo2 (by positivity)
  have he8 := eventually_power_bound Cb Mlo 40 ((a / 10 ^ 6) / (100 * u)) hloB (by positivity)
  filter_upwards [he1, he2, he3, he4, he5, he6, he7, he8, eventually_gt_atTop (0 : ℝ)]
    with q he1 he2 he3 he4 he5 he6 he7 he8 hq
  simp only [Real.rpow_eq_pow, Real.mul_rpow hM1.le hq.le,
    Real.mul_rpow (by norm_num : (0 : ℝ) ≤ 2) hq.le]
  simp only [Real.rpow_zero, Real.rpow_one, mul_one, one_mul, zero_mul, add_zero,
    Real.rpow_natCast, Real.rpow_ofNat] at *
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simpa [Z, mul_assoc] using he1
  · simpa [div_eq_mul_inv, mul_assoc, mul_left_comm, mul_comm] using he2
  · simpa [div_eq_mul_inv, mul_assoc, mul_left_comm, mul_comm] using he3
  · have hp := Real.rpow_pos_of_pos hq Cb
    linarith
  · simpa only [Z, mul_assoc] using he5
  · simpa only [Z, mul_assoc] using he6
  · exact he7
  · simpa [div_eq_mul_inv, mul_assoc, mul_left_comm, mul_comm] using he8

end HypercubeRamsey.Lane_sol_consts_adm
