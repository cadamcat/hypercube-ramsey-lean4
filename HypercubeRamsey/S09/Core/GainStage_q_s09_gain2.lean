import HypercubeRamsey.S09.Core.Experiment
import HypercubeRamsey.Tools.SignedTest
import HypercubeRamsey.Tools.Concentration
import HypercubeRamsey.Tools.Finner

/-!
Lane-local analytic and finite-probability helpers for q-s09-gain2.
-/

namespace HypercubeRamsey.Lane_q_s09_gain2

open Classical Filter
open scoped BigOperators Topology

theorem tendsto_nat_rpow_exp_neg_rpow {s u c : ℝ} (hu : 0 < u) (hc : 0 < c) :
    Tendsto (fun n : ℕ => (n : ℝ) ^ s * Real.exp (-c * (n : ℝ) ^ u)) atTop (𝓝 0) := by
  have hn : Tendsto (fun n : ℕ => (n : ℝ) ^ u) atTop atTop :=
    (tendsto_rpow_atTop hu).comp tendsto_natCast_atTop_atTop
  have hbase :=
    (tendsto_rpow_mul_exp_neg_mul_atTop_nhds_zero (s / u) c hc).comp hn
  apply Tendsto.congr' ?_ hbase
  filter_upwards [eventually_gt_atTop (0 : ℕ)] with n hn0
  have hnR : 0 < (n : ℝ) := by exact_mod_cast hn0
  have hpow : (n : ℝ) ^ s = ((n : ℝ) ^ u) ^ (s / u) := by
    rw [← Real.rpow_mul hnR.le]
    congr 1
    field_simp [ne_of_gt hu]
  change ((n : ℝ) ^ u) ^ (s / u) * Real.exp (-c * (n : ℝ) ^ u) =
    (n : ℝ) ^ s * Real.exp (-c * (n : ℝ) ^ u)
  rw [← hpow]

theorem pr_or_le {Ω : Type*} [Fintype Ω] (Q : FinProb Ω) (A B : Ω → Prop) :
    Q.pr (fun ω => A ω ∨ B ω) ≤ Q.pr A + Q.pr B :=
  FinProb.pr_union_le Q A B

theorem pr_or3_le {Ω : Type*} [Fintype Ω] (Q : FinProb Ω)
    (A B C : Ω → Prop) :
    Q.pr (fun ω => A ω ∨ B ω ∨ C ω) ≤ Q.pr A + Q.pr B + Q.pr C := by
  calc
    Q.pr (fun ω => A ω ∨ B ω ∨ C ω) ≤
        Q.pr (fun ω => A ω ∨ B ω) + Q.pr C := by
          have h := pr_or_le Q (fun ω => A ω ∨ B ω) C
          simpa [or_assoc] using h
    _ ≤ Q.pr A + Q.pr B + Q.pr C := by
      linarith [pr_or_le Q A B]

private theorem power_ratio (n : ℕ) (hn : 1 ≤ n) (a b d : ℝ) :
    (n : ℝ) ^ a * ((n : ℝ) ^ (-b)) ^ 2 / ((n : ℝ) ^ (-d) / 2) =
      2 * (n : ℝ) ^ (a + d - 2 * b) := by
  have hx : 0 < (n : ℝ) := by exact_mod_cast hn
  have hsq : ((n : ℝ) ^ (-b)) ^ 2 = (n : ℝ) ^ (-2 * b) := by
    rw [← Real.rpow_mul_natCast hx.le (-b) 2]
    congr 1
    ring
  have hden : (n : ℝ) ^ (-d) = ((n : ℝ) ^ d)⁻¹ := Real.rpow_neg hx.le d
  calc
    (n : ℝ) ^ a * ((n : ℝ) ^ (-b)) ^ 2 / ((n : ℝ) ^ (-d) / 2) =
        2 * (n : ℝ) ^ a * (n : ℝ) ^ (-2 * b) * (n : ℝ) ^ d := by
          rw [hsq, hden]
          have hpow : (n : ℝ) ^ d ≠ 0 := (Real.rpow_pos_of_pos hx d).ne'
          field_simp [hpow]
          <;> ring
    _ = 2 * ((n : ℝ) ^ a * (n : ℝ) ^ (-2 * b) * (n : ℝ) ^ d) := by ring
    _ = 2 * ((n : ℝ) ^ (a + (-2 * b)) * (n : ℝ) ^ d) := by
          rw [← Real.rpow_add hx a (-2 * b)]
    _ = 2 * (n : ℝ) ^ (a + (-2 * b) + d) := by
          rw [← Real.rpow_add hx (a + (-2 * b)) d]
    _ = 2 * (n : ℝ) ^ (a + d - 2 * b) := by congr 2 <;> ring

theorem eventual_mean_error_bound (P : Params9) (hP : P.Valid)
    (C₁ C₂ c₁ c₂ : ℝ) (hc₁ : 0 < c₁) (hc₂ : 0 < c₂) :
    ∃ n₀ : ℕ, ∀ n ≥ n₀,
      (C₁ + C₂) * (n : ℝ) ^ (P.χ : ℝ) * P.bStar n ^ 2 +
        P.tail c₁ n + P.tail c₂ n + 3 * P.aStar n * (n : ℝ) ^ (-(P.χ : ℝ)) ≤
          P.aStar n / 100 := by
  rcases hP with ⟨⟨hxS, _, _⟩, ⟨hminus, hminusPlus, hplus⟩, _, _,
    ⟨hchi, hchiBound⟩, hgap, _⟩
  have hu : 0 < P.u := by
    dsimp [Params9.u]
    positivity
  have hmin : min P.xS (min P.hMinus (1 - P.hPlus)) ≤ P.hMinus :=
    (min_le_right _ _).trans (min_le_left _ _)
  have hchiBoundR : (P.χ : ℝ) <
      ((min P.xS (min P.hMinus (1 - P.hPlus)) : ℚ) : ℝ) / 100 := by
    exact_mod_cast hchiBound
  have hminR : ((min P.xS (min P.hMinus (1 - P.hPlus)) : ℚ) : ℝ) ≤
      (P.hMinus : ℝ) := by exact_mod_cast hmin
  have hchiMinus : (P.χ : ℝ) < (P.hMinus : ℝ) / 100 := by linarith
  have hmargin : (P.χ : ℝ) + (P.hPlus : ℝ) - 2 * (P.hMinus : ℝ) < 0 := by
    have hg : (P.hPlus : ℝ) - (P.hMinus : ℝ) < (P.χ : ℝ) / 10 := by
      exact_mod_cast hgap
    have hχm : 0 < (P.hMinus : ℝ) := by exact_mod_cast hminus
    have hχbound' : (P.χ : ℝ) < (P.hMinus : ℝ) / 100 := hchiMinus
    linarith
  have hchiR : 0 < (P.χ : ℝ) := by exact_mod_cast hchi
  let α : ℝ := (P.χ : ℝ) + (P.hPlus : ℝ) - 2 * (P.hMinus : ℝ)
  have hα : α < 0 := by dsimp [α]; exact hmargin
  have hpseq : Tendsto (fun n : ℕ => 2 * (C₁ + C₂) * (n : ℝ) ^ α) atTop (𝓝 0) := by
    simpa [mul_assoc, neg_neg] using
      (Tendsto.const_mul (2 * (C₁ + C₂))
        ((tendsto_rpow_neg_atTop (neg_pos.mpr hα)).comp tendsto_natCast_atTop_atTop))
  have ht₁ : Tendsto (fun n : ℕ => 2 * (n : ℝ) ^ (P.hPlus : ℝ) *
      Real.exp (-c₁ * (n : ℝ) ^ P.u)) atTop (𝓝 0) := by
    simpa [mul_assoc] using
      (Tendsto.const_mul 2
        (tendsto_nat_rpow_exp_neg_rpow (s := P.hPlus) (u := P.u) (c := c₁) hu hc₁))
  have ht₂ : Tendsto (fun n : ℕ => 2 * (n : ℝ) ^ (P.hPlus : ℝ) *
      Real.exp (-c₂ * (n : ℝ) ^ P.u)) atTop (𝓝 0) := by
    simpa [mul_assoc] using
      (Tendsto.const_mul 2
        (tendsto_nat_rpow_exp_neg_rpow (s := P.hPlus) (u := P.u) (c := c₂) hu hc₂))
  have hχseq : Tendsto (fun n : ℕ => 3 * (n : ℝ) ^ (-(P.χ : ℝ))) atTop (𝓝 0) := by
    simpa [Function.comp_def, mul_assoc] using
      (Tendsto.const_mul 3
        ((tendsto_rpow_neg_atTop hchiR).comp tendsto_natCast_atTop_atTop))
  have hsmall₁ : ∀ᶠ n : ℕ in atTop, 2 * (C₁ + C₂) * (n : ℝ) ^ α < 1 / 400 :=
    hpseq.eventually (Iio_mem_nhds (by norm_num))
  have hsmall₂ : ∀ᶠ n : ℕ in atTop,
      2 * (n : ℝ) ^ (P.hPlus : ℝ) * Real.exp (-c₁ * (n : ℝ) ^ P.u) < 1 / 400 :=
    ht₁.eventually (Iio_mem_nhds (by norm_num))
  have hsmall₃ : ∀ᶠ n : ℕ in atTop,
      2 * (n : ℝ) ^ (P.hPlus : ℝ) * Real.exp (-c₂ * (n : ℝ) ^ P.u) < 1 / 400 :=
    ht₂.eventually (Iio_mem_nhds (by norm_num))
  have hsmall₄ : ∀ᶠ n : ℕ in atTop, 3 * (n : ℝ) ^ (-(P.χ : ℝ)) < 1 / 400 :=
    hχseq.eventually (Iio_mem_nhds (by norm_num))
  obtain ⟨n₁, hn₁⟩ := eventually_atTop.1 hsmall₁
  obtain ⟨n₂, hn₂⟩ := eventually_atTop.1 hsmall₂
  obtain ⟨n₃, hn₃⟩ := eventually_atTop.1 hsmall₃
  obtain ⟨n₄, hn₄⟩ := eventually_atTop.1 hsmall₄
  refine ⟨max (max (max n₁ n₂) (max n₃ n₄)) 1, ?_⟩
  intro n hn
  have hn₁' : n₁ ≤ n := by omega
  have hn₂' : n₂ ≤ n := by omega
  have hn₃' : n₃ ≤ n := by omega
  have hn₄' : n₄ ≤ n := by omega
  have hn0 : 1 ≤ n := le_trans (le_max_right _ _) hn
  have hnR : 0 < (n : ℝ) := by exact_mod_cast hn0
  have ha : 0 < P.aStar n := by
    dsimp [Params9.aStar]
    positivity
  have hratio₁ :
      (C₁ + C₂) * (n : ℝ) ^ (P.χ : ℝ) * P.bStar n ^ 2 / P.aStar n =
        2 * (C₁ + C₂) * (n : ℝ) ^ α := by
    dsimp [α, Params9.aStar, Params9.bStar]
    calc
      (C₁ + C₂) * (n : ℝ) ^ (P.χ : ℝ) * ((n : ℝ) ^ (-(P.hMinus : ℝ))) ^ 2 /
          ((n : ℝ) ^ (-(P.hPlus : ℝ)) / 2) =
          (C₁ + C₂) * ((n : ℝ) ^ (P.χ : ℝ) *
            ((n : ℝ) ^ (-(P.hMinus : ℝ))) ^ 2 /
              ((n : ℝ) ^ (-(P.hPlus : ℝ)) / 2)) := by ring
      _ = (C₁ + C₂) * (2 * (n : ℝ) ^
            ((P.χ : ℝ) + (P.hPlus : ℝ) - 2 * (P.hMinus : ℝ))) := by
          rw [power_ratio n hn0 (P.χ : ℝ) (P.hMinus : ℝ) (P.hPlus : ℝ)]
      _ = 2 * (C₁ + C₂) * (n : ℝ) ^ α := by
          dsimp [α]
          ring
  have hratio₂ : P.tail c₁ n / P.aStar n =
      2 * (n : ℝ) ^ (P.hPlus : ℝ) * Real.exp (-c₁ * (n : ℝ) ^ P.u) := by
    dsimp [Params9.tail, Params9.aStar]
    rw [Real.rpow_neg hnR.le]
    have hp : (n : ℝ) ^ (P.hPlus : ℝ) ≠ 0 :=
      (Real.rpow_pos_of_pos hnR _).ne'
    field_simp [hp]
    <;> ring
  have hratio₃ : P.tail c₂ n / P.aStar n =
      2 * (n : ℝ) ^ (P.hPlus : ℝ) * Real.exp (-c₂ * (n : ℝ) ^ P.u) := by
    dsimp [Params9.tail, Params9.aStar]
    rw [Real.rpow_neg hnR.le]
    have hp : (n : ℝ) ^ (P.hPlus : ℝ) ≠ 0 :=
      (Real.rpow_pos_of_pos hnR _).ne'
    field_simp [hp]
    <;> ring
  have hratio₄ :
      3 * P.aStar n * (n : ℝ) ^ (-(P.χ : ℝ)) / P.aStar n =
        3 * (n : ℝ) ^ (-(P.χ : ℝ)) := by
    field_simp [ha.ne']
  have h₁ :
      (C₁ + C₂) * (n : ℝ) ^ (P.χ : ℝ) * P.bStar n ^ 2 / P.aStar n ≤ 1 / 400 := by
    rw [hratio₁]
    exact (hn₁ n hn₁').le
  have h₂ : P.tail c₁ n / P.aStar n ≤ 1 / 400 := by
    rw [hratio₂]
    exact (hn₂ n hn₂').le
  have h₃ : P.tail c₂ n / P.aStar n ≤ 1 / 400 := by
    rw [hratio₃]
    exact (hn₃ n hn₃').le
  have h₄ :
      3 * P.aStar n * (n : ℝ) ^ (-(P.χ : ℝ)) / P.aStar n ≤ 1 / 400 := by
    rw [hratio₄]
    exact (hn₄ n hn₄').le
  have hsum :
      (C₁ + C₂) * (n : ℝ) ^ (P.χ : ℝ) * P.bStar n ^ 2 +
        P.tail c₁ n + P.tail c₂ n + 3 * P.aStar n * (n : ℝ) ^ (-(P.χ : ℝ)) =
        P.aStar n * ((C₁ + C₂) * (n : ℝ) ^ (P.χ : ℝ) * P.bStar n ^ 2 / P.aStar n +
          P.tail c₁ n / P.aStar n + P.tail c₂ n / P.aStar n +
          3 * P.aStar n * (n : ℝ) ^ (-(P.χ : ℝ)) / P.aStar n) := by
    field_simp [ha.ne']
    <;> ring
  rw [hsum]
  have hratio :
      (C₁ + C₂) * (n : ℝ) ^ (P.χ : ℝ) * P.bStar n ^ 2 / P.aStar n +
          P.tail c₁ n / P.aStar n + P.tail c₂ n / P.aStar n +
          3 * P.aStar n * (n : ℝ) ^ (-(P.χ : ℝ)) / P.aStar n ≤ 1 / 100 := by
    linarith
  calc
    P.aStar n * ((C₁ + C₂) * (n : ℝ) ^ (P.χ : ℝ) * P.bStar n ^ 2 / P.aStar n +
        P.tail c₁ n / P.aStar n + P.tail c₂ n / P.aStar n +
        3 * P.aStar n * (n : ℝ) ^ (-(P.χ : ℝ)) / P.aStar n) ≤
      P.aStar n * (1 / 100) := mul_le_mul_of_nonneg_left hratio ha.le
    _ = P.aStar n / 100 := by ring

theorem eventual_tail_sum3 {u c₁ c₂ c₃ : ℝ} (hu : 0 < u)
    (hc₁ : 0 < c₁) (hc₂ : 0 < c₂) (hc₃ : 0 < c₃) :
    ∃ n₀ : ℕ, ∀ n ≥ n₀,
      Real.exp (-c₁ * (n : ℝ) ^ u) + Real.exp (-c₂ * (n : ℝ) ^ u) +
          Real.exp (-c₃ * (n : ℝ) ^ u) ≤
        Real.exp (-((min c₁ (min c₂ c₃) / 2) * (n : ℝ) ^ u)) := by
  let C : ℝ := min c₁ (min c₂ c₃)
  have hC : 0 < C := by dsimp [C]; exact lt_min hc₁ (lt_min hc₂ hc₃)
  have hC₁ : C ≤ c₁ := by dsimp [C]; exact min_le_left _ _
  have hC₂ : C ≤ c₂ := by dsimp [C]; exact (min_le_right _ _).trans (min_le_left _ _)
  have hC₃ : C ≤ c₃ := by dsimp [C]; exact (min_le_right _ _).trans (min_le_right _ _)
  have hu0 : Tendsto (fun n : ℕ => Real.exp (-(C / 2) * (n : ℝ) ^ u)) atTop (𝓝 0) := by
    simpa using (tendsto_nat_rpow_exp_neg_rpow (s := 0) (u := u) (c := C / 2) hu (by linarith))
  have hsmall : ∀ᶠ n : ℕ in atTop,
      Real.exp (-(C / 2) * (n : ℝ) ^ u) < 1 / 3 :=
    hu0.eventually (Iio_mem_nhds (by norm_num))
  obtain ⟨n₀, hn₀⟩ := eventually_atTop.1 hsmall
  refine ⟨n₀, ?_⟩
  intro n hn
  have hx : 0 ≤ (n : ℝ) ^ u := Real.rpow_nonneg (by positivity) _
  have h₁ : Real.exp (-c₁ * (n : ℝ) ^ u) ≤ Real.exp (-C * (n : ℝ) ^ u) := by
    apply Real.exp_le_exp.mpr
    nlinarith [mul_nonneg (sub_nonneg.mpr hC₁) hx]
  have h₂ : Real.exp (-c₂ * (n : ℝ) ^ u) ≤ Real.exp (-C * (n : ℝ) ^ u) := by
    apply Real.exp_le_exp.mpr
    nlinarith [mul_nonneg (sub_nonneg.mpr hC₂) hx]
  have h₃ : Real.exp (-c₃ * (n : ℝ) ^ u) ≤ Real.exp (-C * (n : ℝ) ^ u) := by
    apply Real.exp_le_exp.mpr
    nlinarith [mul_nonneg (sub_nonneg.mpr hC₃) hx]
  let q : ℝ := Real.exp (-(C / 2) * (n : ℝ) ^ u)
  have hq : q < 1 / 3 := hn₀ n hn
  have hq0 : 0 ≤ q := by dsimp [q]; positivity
  have hexp : Real.exp (-C * (n : ℝ) ^ u) = q * q := by
    dsimp [q]
    rw [← Real.exp_add]
    congr 1
    ring
  have hmul : 3 * q * q ≤ q := by nlinarith [mul_le_mul_of_nonneg_right hq.le hq0]
  calc
    Real.exp (-c₁ * (n : ℝ) ^ u) + Real.exp (-c₂ * (n : ℝ) ^ u) +
        Real.exp (-c₃ * (n : ℝ) ^ u) ≤ 3 * Real.exp (-C * (n : ℝ) ^ u) := by
          linarith
    _ = 3 * q * q := by rw [hexp]; ring
    _ ≤ q := hmul
    _ = Real.exp (-((C / 2) * (n : ℝ) ^ u)) := by
      dsimp [q]
      congr 1
      ring

end HypercubeRamsey.Lane_q_s09_gain2
