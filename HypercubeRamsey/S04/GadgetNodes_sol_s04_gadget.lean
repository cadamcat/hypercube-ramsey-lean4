import HypercubeRamsey.S04.CoreLemmas
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import Mathlib.Data.Nat.Log

namespace HypercubeRamsey.Lane_sol_s04_gadget

open Filter

private theorem gadget_search_exponent_le {β γ : ℝ} (n : ℕ) (hn : 2 ≤ n)
    (hω : 0 < HypercubeRamsey.omega4 β γ) :
    (Nat.log2 (HypercubeRamsey.S04.gadgetPower β γ n) : ℝ) ≤
      (2 * HypercubeRamsey.omega4 β γ / Real.log 2) * Real.log (n : ℝ) + 2 := by
  let ω := HypercubeRamsey.omega4 β γ
  let x : ℝ := (n : ℝ) ^ (2 * ω)
  let q : ℕ := ⌈Real.log x / Real.log 2⌉₊
  have hnreal : 1 ≤ (n : ℝ) := by exact_mod_cast (show 1 ≤ n by omega)
  have hnpos : 0 < (n : ℝ) := by positivity
  have hxone : 1 ≤ x := Real.one_le_rpow hnreal (by positivity)
  have hlog2 : 0 < Real.log (2 : ℝ) := Real.log_pos (by norm_num)
  have hratio : 0 ≤ Real.log x / Real.log 2 :=
    div_nonneg (Real.log_nonneg hxone) hlog2.le
  have hq : (q : ℝ) < Real.log x / Real.log 2 + 1 := Nat.ceil_lt_add_one hratio
  have hmax : ((max 1 q : ℕ) : ℝ) ≤ (q : ℝ) + 1 := by
    exact_mod_cast (show max 1 q ≤ q + 1 by omega)
  have he : Nat.log2 (HypercubeRamsey.S04.gadgetPower β γ n) = max 1 q := by
    unfold HypercubeRamsey.S04.gadgetPower
    rw [Nat.log2_eq_log_two, Nat.log_pow (by norm_num)]
  rw [he]
  have hlogx : Real.log x = (2 * ω) * Real.log (n : ℝ) :=
    Real.log_rpow hnpos _
  rw [hlogx] at hq
  dsimp [ω] at hq
  calc
    ((max 1 q : ℕ) : ℝ) ≤ (q : ℝ) + 1 := hmax
    _ ≤ (2 * HypercubeRamsey.omega4 β γ * Real.log (n : ℝ)) / Real.log 2 + 2 :=
      by linarith
    _ = (2 * HypercubeRamsey.omega4 β γ / Real.log 2) * Real.log (n : ℝ) + 2 :=
      by ring

theorem key_neighbor_numeric_bound {β γ : ℝ}
    (hβ : 0 < β) (hβγ : β ≤ γ) (hγ : γ < 1) :
    ∃ n₀ : ℕ, ∀ n ≥ n₀,
      ((1 + HypercubeRamsey.S04.gadgetNum β γ n *
        (Nat.log2 (HypercubeRamsey.S04.gadgetPower β γ n) * 2) : ℕ) : ℝ) ≤
      (n : ℝ) ^ (γ - 9 / 10 * HypercubeRamsey.omega4 β γ) := by
  let ω := HypercubeRamsey.omega4 β γ
  let d := ω / 10
  let A := 4 * ω / Real.log 2
  have hω : 0 < ω := HypercubeRamsey.S04.omega4_pos hβ hγ
  have hd : 0 < d := by dsimp [d]; positivity
  have hA : 0 < A := by
    dsimp [A]
    exact div_pos (by positivity) (Real.log_pos (by norm_num))
  have hωγ : ω < γ := by
    dsimp [ω, HypercubeRamsey.omega4]
    have hm := min_le_left β (1 - γ)
    have hb : β / 1000 < β := by nlinarith
    linarith
  have hlog := (isLittleO_log_rpow_atTop hd).comp_tendsto
    (tendsto_natCast_atTop_atTop : Tendsto (fun n : ℕ => (n : ℝ)) atTop atTop)
  have hlogbound := hlog.bound (show 0 < 1 / (2 * A) by positivity)
  have hpow : Tendsto (fun n : ℕ => (n : ℝ) ^ d) atTop atTop :=
    (_root_.tendsto_rpow_atTop hd).comp tendsto_natCast_atTop_atTop
  have hevent : ∀ᶠ n : ℕ in atTop,
      ((1 + HypercubeRamsey.S04.gadgetNum β γ n *
        (Nat.log2 (HypercubeRamsey.S04.gadgetPower β γ n) * 2) : ℕ) : ℝ) ≤
      (n : ℝ) ^ (γ - 9 / 10 * ω) := by
    filter_upwards [hlogbound, hpow.eventually_ge_atTop 10, eventually_ge_atTop 2]
      with n hlogn hlarge hn
    have hnreal : 1 ≤ (n : ℝ) := by exact_mod_cast (show 1 ≤ n by omega)
    have hnpos : 0 < (n : ℝ) := by positivity
    have hlognonneg : 0 ≤ Real.log (n : ℝ) := Real.log_nonneg hnreal
    have hpowpos : 0 < (n : ℝ) ^ d := Real.rpow_pos_of_pos hnpos _
    have hlogn' : Real.log (n : ℝ) ≤ 1 / (2 * A) * (n : ℝ) ^ d := by
      simpa only [Function.comp_apply, Real.norm_eq_abs, abs_of_nonneg hlognonneg,
        abs_of_nonneg hpowpos.le] using hlogn
    have hlogsmall : A * Real.log (n : ℝ) ≤ (n : ℝ) ^ d / 2 := by
      have h := mul_le_mul_of_nonneg_left hlogn' hA.le
      calc
        A * Real.log (n : ℝ) ≤ A * (1 / (2 * A) * (n : ℝ) ^ d) := h
        _ = (n : ℝ) ^ d / 2 := by field_simp
    let e := Nat.log2 (HypercubeRamsey.S04.gadgetPower β γ n)
    have hexp : (e : ℝ) ≤ (2 * ω / Real.log 2) * Real.log (n : ℝ) + 2 :=
      gadget_search_exponent_le n hn hω
    have hexp' : (e : ℝ) * 2 ≤ A * Real.log (n : ℝ) + 4 := by
      calc
        (e : ℝ) * 2 ≤ ((2 * ω / Real.log 2) * Real.log (n : ℝ) + 2) * 2 :=
          mul_le_mul_of_nonneg_right hexp (by norm_num)
        _ = A * Real.log (n : ℝ) + 4 := by dsimp [A]; ring
    have hfactor : 1 + (e : ℝ) * 2 ≤ (n : ℝ) ^ d := by
      linarith only [hexp', hlogsmall, hlarge]
    let G := HypercubeRamsey.S04.gadgetNum β γ n
    have hG : (G : ℝ) ≤ (n : ℝ) ^ (γ - ω) :=
      Nat.floor_le (Real.rpow_nonneg hnpos.le _)
    have hbase : 1 ≤ (n : ℝ) ^ (γ - ω) :=
      Real.one_le_rpow hnreal (by linarith)
    calc
      ((1 + G * (e * 2) : ℕ) : ℝ) = 1 + (G : ℝ) * ((e : ℝ) * 2) := by
        push_cast
        rfl
      _ ≤ (n : ℝ) ^ (γ - ω) * (1 + (e : ℝ) * 2) := by
        have h := mul_le_mul_of_nonneg_right hG
          (show 0 ≤ (e : ℝ) * 2 by positivity)
        nlinarith
      _ ≤ (n : ℝ) ^ (γ - ω) * (n : ℝ) ^ d :=
        mul_le_mul_of_nonneg_left hfactor (Real.rpow_nonneg hnpos.le _)
      _ = (n : ℝ) ^ (γ - 9 / 10 * ω) := by
        rw [← Real.rpow_add hnpos]
        congr 1
        dsimp [d]
        ring
  exact Filter.eventually_atTop.1 hevent

end HypercubeRamsey.Lane_sol_s04_gadget
