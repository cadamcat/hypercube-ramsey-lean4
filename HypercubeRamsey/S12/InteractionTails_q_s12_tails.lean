import HypercubeRamsey.S12.Exceptional
import HypercubeRamsey.Framework.FinProbLemmas

set_option maxHeartbeats 1000000

namespace HypercubeRamsey.Lane_q_s12_tails

open HypercubeRamsey.S12
open Filter
open Classical
open scoped BigOperators

private theorem tendsto_stage_n_real (T : Stage) :
    Tendsto (fun k => (T.S.n k : ℝ)) atTop atTop :=
  tendsto_natCast_atTop_atTop.comp T.S.n_tendsto

theorem eventually_rpow_le_mul (T : Stage) {p q c : ℝ}
    (hpq : p < q) (hc : 0 < c) :
    ∀ᶠ k in atTop, (T.S.n k : ℝ) ^ p ≤ c * (T.S.n k : ℝ) ^ q := by
  have hlim : Tendsto (fun k => (T.S.n k : ℝ) ^ (-(q - p))) atTop (nhds 0) :=
    (tendsto_rpow_neg_atTop (sub_pos.mpr hpq)).comp (tendsto_stage_n_real T)
  have hsmall : ∀ᶠ k in atTop, (T.S.n k : ℝ) ^ (-(q - p)) < c :=
    hlim.eventually (gt_mem_nhds hc)
  have hn : ∀ᶠ k in atTop, 1 ≤ (T.S.n k : ℝ) := by
    exact (tendsto_stage_n_real T).eventually (eventually_ge_atTop (1 : ℝ))
  filter_upwards [hsmall, hn] with k hk hnk
  have hnpos : 0 < (T.S.n k : ℝ) := by linarith
  have hratio : (T.S.n k : ℝ) ^ p / (T.S.n k : ℝ) ^ q =
      (T.S.n k : ℝ) ^ (-(q - p)) := by
    rw [← Real.rpow_sub hnpos p q]
    congr 1
    ring
  rw [← hratio] at hk
  have hqpos : 0 < (T.S.n k : ℝ) ^ q := Real.rpow_pos_of_pos hnpos q
  exact le_of_lt ((div_lt_iff₀ hqpos).mp hk)

theorem eventually_rpow_ge (T : Stage) {q C : ℝ}
    (hq : 0 < q) : ∀ᶠ k in atTop, C ≤ (T.S.n k : ℝ) ^ q := by
  exact ((tendsto_rpow_atTop hq).comp (tendsto_stage_n_real T)).eventually
    (eventually_ge_atTop C)

theorem eventually_exp_linear_ge (T : Stage) {a C : ℝ}
    (ha : 0 < a) : ∀ᶠ k in atTop, C ≤ Real.exp (a * (T.S.n k : ℝ)) := by
  have hlinear : Tendsto (fun k => a * (T.S.n k : ℝ)) atTop atTop :=
    (tendsto_stage_n_real T).const_mul_atTop ha
  exact (Real.tendsto_exp_atTop.comp hlinear).eventually (eventually_ge_atTop C)

private theorem fv_abs_bound {N : ℕ} (E : Fin N → Fin N → Prop)
    (c : Colour) (x y : Fin N) : |fv E c x y| ≤ 1 := by
  classical
  by_cases hh : Hits E c x y <;> simp [fv, hit, hh] <;> norm_num

private theorem eventually_small_exp_vs_bstar (T : Stage) (κ : CConsts)
    (hx : 0 < κ.xs) :
    ∀ᶠ k in atTop,
      2 * Real.exp ((T.S.n k : ℝ) ^ (κ.xs / 4) -
        (T.S.n k : ℝ) ^ κ.xs) ≤ bstar T k ^ 2 := by
  have hp := eventually_rpow_le_mul T (p := κ.xs / 4) (q := κ.xs)
    (c := 1 / 4) (by linarith) (by norm_num : (0 : ℝ) < 1 / 4)
  have hlarge : ∀ᶠ k in atTop, 1 ≤ (T.S.n k : ℝ) :=
    tendsto_stage_n_real T |>.eventually (eventually_ge_atTop (1 : ℝ))
  have hlim : Tendsto
      (fun k => (T.S.n k : ℝ) ^ (1.92 : ℝ) *
        Real.exp (-(3 / 4 : ℝ) * (T.S.n k : ℝ) ^ κ.xs)) atTop (nhds 0) := by
    have hX : Tendsto (fun k => (T.S.n k : ℝ) ^ κ.xs) atTop atTop :=
      (tendsto_rpow_atTop hx).comp (tendsto_stage_n_real T)
    have hlimX : Tendsto
        (fun x : ℝ => x ^ ((1.92 : ℝ) / κ.xs) * Real.exp (-(3 / 4 : ℝ) * x))
        atTop (nhds 0) :=
      tendsto_rpow_mul_exp_neg_mul_atTop_nhds_zero
        ((1.92 : ℝ) / κ.xs) (3 / 4) (by norm_num)
    have hc := hlimX.comp hX
    have hpow (k : ℕ) :
        ((T.S.n k : ℝ) ^ κ.xs) ^ ((1.92 : ℝ) / κ.xs) =
          (T.S.n k : ℝ) ^ (1.92 : ℝ) := by
      rw [← Real.rpow_mul (by positivity : 0 ≤ (T.S.n k : ℝ))]
      congr 1
      field_simp [ne_of_gt hx]
    have heq : (fun k =>
        ((fun x : ℝ => x ^ ((1.92 : ℝ) / κ.xs) *
          Real.exp (-(3 / 4 : ℝ) * x)) ((T.S.n k : ℝ) ^ κ.xs))) =ᶠ[atTop]
        (fun k => (T.S.n k : ℝ) ^ (1.92 : ℝ) *
          Real.exp (-(3 / 4 : ℝ) * (T.S.n k : ℝ) ^ κ.xs)) := by
      filter_upwards [] with k
      simp only [Function.comp_apply, hpow k]
    exact hc.congr' heq
  have hsmall := hlim.eventually (gt_mem_nhds (by norm_num : (0 : ℝ) < 1 / 4))
  filter_upwards [hp, hlarge, hsmall] with k hpow hnk hsmall
  have hnpos : 0 < (T.S.n k : ℝ) := by positivity
  have hfourth : (T.S.n k : ℝ) ^ (κ.xs / 4) ≤
      (T.S.n k : ℝ) ^ κ.xs / 4 := by
    convert hpow using 1 <;> ring
  have hexp : (T.S.n k : ℝ) ^ (1.92 : ℝ) *
      Real.exp (-(3 / 4 : ℝ) * (T.S.n k : ℝ) ^ κ.xs) ≤ 1 / 2 := by
    exact (le_of_lt hsmall).trans (by norm_num)
  have hbstarSq : bstar T k ^ 2 = (T.S.n k : ℝ) ^ (-(1.92 : ℝ)) := by
    change ((T.S.n k : ℝ) ^ (-1 + (0.04 : ℝ))) ^ 2 = _
    rw [show (-1 + (0.04 : ℝ)) = -(0.96 : ℝ) by norm_num]
    rw [← Real.rpow_natCast ((T.S.n k : ℝ) ^ (-(0.96 : ℝ))) 2,
      ← Real.rpow_mul (by positivity : 0 ≤ (T.S.n k : ℝ))]
    congr 1
    norm_num
  rw [hbstarSq]
  have hpowpos : 0 < (T.S.n k : ℝ) ^ (1.92 : ℝ) := Real.rpow_pos_of_pos hnpos _
  have hexpneg : Real.exp ((T.S.n k : ℝ) ^ (κ.xs / 4) -
      (T.S.n k : ℝ) ^ κ.xs) ≤
      Real.exp (-(3 / 4 : ℝ) * (T.S.n k : ℝ) ^ κ.xs) := by
    apply Real.exp_le_exp.mpr
    nlinarith [hfourth]
  have hmul := mul_le_mul_of_nonneg_left hexpneg (by norm_num : (0 : ℝ) ≤ 2)
  have hdiv : 2 * Real.exp (-(3 / 4 : ℝ) * (T.S.n k : ℝ) ^ κ.xs) ≤
      (1 / 2) / (T.S.n k : ℝ) ^ (1.92 : ℝ) := by
    apply (le_div_iff₀ hpowpos).2
    nlinarith [hexp]
  calc
    2 * Real.exp ((T.S.n k : ℝ) ^ (κ.xs / 4) - (T.S.n k : ℝ) ^ κ.xs) ≤
        2 * Real.exp (-(3 / 4 : ℝ) * (T.S.n k : ℝ) ^ κ.xs) := hmul
    _ ≤ (1 / 2) / (T.S.n k : ℝ) ^ (1.92 : ℝ) := hdiv
    _ ≤ (T.S.n k : ℝ) ^ (-(1.92 : ℝ)) := by
      rw [Real.rpow_neg (by positivity : 0 ≤ (T.S.n k : ℝ))]
      apply (div_le_iff₀ hpowpos).2
      field_simp
      norm_num

private theorem fv_mean_l2_at_k (T : Stage) (κ : CConsts) (k : ℕ)
    (hn : 1 ≤ (T.S.n k : ℝ))
    (hD : TwoBudgetDisc T k ((T.S.n k : ℝ) ^ κ.xs)
      (κ.α * T.S.n k) (bstar T k))
    (hSmallExp : 2 * Real.exp ((T.S.n k : ℝ) ^ (κ.xs / 4) -
      (T.S.n k : ℝ) ^ κ.xs) ≤ bstar T k ^ 2)
    (c : Colour) {σ ν : Law (T.S.N k)}
    (hσ : σ.SupportedIn (T.X k))
    (hσw : σ.WidthLE (κ.α * T.S.n k))
    (hν : ν.SupportedIn (T.Y k))
    (hνw : ν.WidthLE ((T.S.n k : ℝ) ^ (κ.xs / 4))) :
    ∑ y, ν.w y * (∑ x, σ.w x * fv (T.S.E k) c x y) ^ 2 ≤
      5 * bstar T k ^ 2 := by
  classical
  let D (y : Fin (T.S.N k)) : ℝ := ∑ x, σ.w x * hit (T.S.E k) c x y
  let m (y : Fin (T.S.N k)) : ℝ := ∑ x, σ.w x * fv (T.S.E k) c x y
  let Bad : Finset (Fin (T.S.N k)) := Finset.univ.filter (fun y =>
    bstar T k < |D y - 1 / 2|)
  have hbstar : 0 < bstar T k := by
    exact Real.rpow_pos_of_pos (lt_of_lt_of_le (by norm_num) hn) _
  have hbad := exceptional_second hD c (Or.inr ⟨le_rfl, le_rfl⟩)
    σ hσ hσw ν hν hνw
  have hbad' : ∑ y ∈ Bad, ν.w y ≤ bstar T k ^ 2 := by
    have h := hbad
    simpa [Bad, D] using (h.trans hSmallExp)
  have hm (y : Fin (T.S.N k)) : m y = 2 * (D y - 1 / 2) := by
    dsimp [m, D]
    calc
      ∑ x, σ.w x * fv (T.S.E k) c x y =
          ∑ x, (2 * (σ.w x * hit (T.S.E k) c x y) - σ.w x) := by
        apply Finset.sum_congr rfl
        intro x hx
        simp only [fv]
        ring
      _ = 2 * (∑ x, σ.w x * hit (T.S.E k) c x y) - ∑ x, σ.w x := by
        rw [Finset.sum_sub_distrib, ← Finset.mul_sum]
      _ = 2 * ((∑ x, σ.w x * hit (T.S.E k) c x y) - 1 / 2) := by
        rw [σ.sum_eq_one]
        ring
  have hmall (y : Fin (T.S.N k)) : |m y| ≤ 1 := by
    have hbound : ∑ x, |σ.w x * fv (T.S.E k) c x y| ≤ 1 := by
      calc
        ∑ x, |σ.w x * fv (T.S.E k) c x y| =
            ∑ x, σ.w x * |fv (T.S.E k) c x y| := by
          apply Finset.sum_congr rfl
          intro x hx
          rw [abs_mul, abs_of_nonneg (σ.nonneg x)]
        _ ≤ ∑ x, σ.w x * 1 := by
          apply Finset.sum_le_sum
          intro x hx
          exact mul_le_mul_of_nonneg_left (fv_abs_bound _ _ _ _)
            (σ.nonneg x)
        _ = 1 := by simp [σ.sum_eq_one]
    have habs : |m y| ≤ ∑ x, |σ.w x * fv (T.S.E k) c x y| := by
      simpa [m] using Finset.abs_sum_le_sum_abs
        (fun x => σ.w x * fv (T.S.E k) c x y) Finset.univ
    exact habs.trans hbound
  have hpoint (y : Fin (T.S.N k)) :
      m y ^ 2 ≤ 4 * bstar T k ^ 2 + if y ∈ Bad then 1 else 0 := by
    by_cases hy : y ∈ Bad
    · have hsq : m y ^ 2 ≤ 1 := by
        have hmabs := hmall y
        rw [← sq_abs (m y)]
        nlinarith [abs_nonneg (m y)]
      have hle : 1 ≤ 4 * bstar T k ^ 2 + 1 := by
        nlinarith [sq_nonneg (bstar T k)]
      simpa [hy] using hsq.trans hle
    · have hgood : |D y - 1 / 2| ≤ bstar T k := by
        exact le_of_not_gt (by simpa [Bad, D] using hy)
      have hmsmall : |m y| ≤ 2 * bstar T k := by
        rw [hm]
        rw [abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 2)]
        nlinarith
      have hnonneg : 0 ≤ 2 * bstar T k := by positivity
      have hmsmall' : |m y| ≤ |2 * bstar T k| := by
        rwa [abs_of_nonneg hnonneg]
      have hsq : m y ^ 2 ≤ (2 * bstar T k) ^ 2 := (sq_le_sq).2 hmsmall'
      have hsq' : m y ^ 2 ≤ 4 * bstar T k ^ 2 := by nlinarith [hsq]
      simpa [hy] using hsq'
  calc
    ∑ y, ν.w y * m y ^ 2 ≤
        ∑ y, ν.w y * (4 * bstar T k ^ 2 + if y ∈ Bad then 1 else 0) := by
      apply Finset.sum_le_sum
      intro y hy
      exact mul_le_mul_of_nonneg_left (hpoint y) (ν.nonneg y)
    _ = 4 * bstar T k ^ 2 + ∑ y ∈ Bad, ν.w y := by
      simp_rw [mul_add]
      rw [Finset.sum_add_distrib]
      have hconst : ∑ y, ν.w y * (4 * bstar T k ^ 2) =
          4 * bstar T k ^ 2 := by
        rw [← Finset.sum_mul, ν.sum_eq_one]
        ring
      have hind : ∑ y, ν.w y * (if y ∈ Bad then 1 else 0) =
          ∑ y ∈ Bad, ν.w y := by
        simp_rw [mul_ite, mul_zero, mul_one]
        rw [Finset.sum_ite_mem_eq]
      rw [hconst, hind]
    _ ≤ 5 * bstar T k ^ 2 := by linarith [hbad']

private theorem fv_conditional_l2_at_k (T : Stage) (κ : CConsts) (k : ℕ)
    (hn : 1 ≤ (T.S.n k : ℝ))
    (hD : TwoBudgetDisc T k ((T.S.n k : ℝ) ^ κ.xs)
      (κ.α * T.S.n k) (bstar T k))
    (hSmallExp : 2 * Real.exp ((T.S.n k : ℝ) ^ (κ.xs / 4) -
      (T.S.n k : ℝ) ^ κ.xs) ≤ bstar T k ^ 2)
    (c : Colour) {τ ν : Law (T.S.N k)}
    (hτsupp : τ.SupportedIn (T.X k))
    (hτw : τ.WidthLE ((T.S.n k : ℝ) ^ (κ.xs / 4)))
    (hνsupp : ν.SupportedIn (T.Y k))
    (hνw : ν.WidthLE ((T.S.n k : ℝ) ^ (κ.xs / 4)))
    (A : Finset (Fin (T.S.N k)))
    (hA : 0 < ∑ x ∈ A, τ.w x)
    (hCost : (T.S.n k : ℝ) ^ (κ.xs / 4) -
      Real.log (∑ x ∈ A, τ.w x) ≤ κ.α * T.S.n k) :
    ∑ y, ν.w y *
      (∑ x, (τ.restrict A hA).w x * fv (T.S.E k) c x y) ^ 2 ≤
        (3 * bstar T k) ^ 2 := by
  have hSupp : (τ.restrict A hA).SupportedIn (T.X k) := by
    intro x hx
    by_cases hxA : x ∈ A
    · simp [Law.restrict, hxA, hτsupp x hx]
    · simp [Law.restrict, hxA]
  have hWidth0 := Law.cond_widthLE τ A hA hτw
  have hWidth : (τ.restrict A hA).WidthLE (κ.α * T.S.n k) := by
    have hCost' : (T.S.n k : ℝ) ^ (κ.xs / 4) +
        Real.log (1 / (∑ x ∈ A, τ.w x)) ≤ κ.α * T.S.n k := by
      simpa [Real.log_inv] using hCost
    intro x
    have hExp : Real.exp ((T.S.n k : ℝ) ^ (κ.xs / 4) +
        Real.log (1 / ∑ x ∈ A, τ.w x)) ≤ Real.exp (κ.α * T.S.n k) :=
      Real.exp_le_exp.mpr hCost'
    exact le_trans (hWidth0 x)
      (div_le_div_of_nonneg_right hExp (by positivity))
  have h := fv_mean_l2_at_k T κ k hn hD hSmallExp c hSupp hWidth hνsupp hνw
  nlinarith [h, sq_nonneg (bstar T k)]

private theorem eventually_conditioning_cost (T : Stage) (κ : CConsts)
    (hκ : κ.Admissible) :
    ∀ᶠ k in atTop, ∀ (τ : Law (T.S.N k)) (A : Finset (Fin (T.S.N k))),
      (Real.exp (-((T.S.n k : ℝ) ^ (0.4 : ℝ))) / 8) ^
          (Nat.ceil ((T.S.n k : ℝ) ^ (0.25 : ℝ)) + 1) / 2 ≤
        ∑ x ∈ A, τ.w x →
      (T.S.n k : ℝ) ^ (κ.xs / 4) - Real.log (∑ x ∈ A, τ.w x) ≤
        κ.α * T.S.n k := by
  have hlog8 := eventually_rpow_ge T (q := (0.4 : ℝ))
    (C := Real.log 8) (by norm_num)
  have hlog2 := eventually_rpow_ge T (q := (0.65 : ℝ))
    (C := Real.log 2) (by norm_num)
  have hlin := eventually_rpow_le_mul T (p := (0.65 : ℝ)) (q := 1)
    (c := κ.α / 9) (by norm_num) (by
      have ha := hκ.α_rng.1
      positivity)
  have hn : ∀ᶠ k in atTop, 1 ≤ (T.S.n k : ℝ) :=
    tendsto_stage_n_real T |>.eventually (eventually_ge_atTop (1 : ℝ))
  filter_upwards [hlog8, hlog2, hlin, hn] with k hlog8 hlog2 hlin hn
  intro τ A hmass
  let n : ℝ := T.S.n k
  let q : ℝ := Real.exp (-(n ^ (0.4 : ℝ))) / 8
  let t : ℕ := Nat.ceil (n ^ (0.25 : ℝ))
  let lower : ℝ := q ^ (t + 1) / 2
  have hnpos : 0 < n := lt_of_lt_of_le (by norm_num) hn
  have hlogq : Real.log q = -(n ^ (0.4 : ℝ)) - Real.log 8 := by
    dsimp [q]
    rw [Real.log_div (ne_of_gt (Real.exp_pos _)) (by norm_num), Real.log_exp]
  have hlowerpos : 0 < lower := by
    dsimp [lower, q]
    positivity
  have hloglower : -Real.log lower =
      ((t + 1 : ℕ) : ℝ) * (n ^ (0.4 : ℝ) + Real.log 8) + Real.log 2 := by
    dsimp [lower]
    rw [Real.log_div (ne_of_gt (pow_pos (div_pos (Real.exp_pos _) (by norm_num)) _))
      (by norm_num), Real.log_pow]
    rw [hlogq]
    ring
  have hnQuarter : 1 ≤ n ^ (0.25 : ℝ) := by
    calc
      1 = n ^ (0 : ℝ) := by simp
      _ ≤ n ^ (0.25 : ℝ) := Real.rpow_le_rpow_of_exponent_le hn (by norm_num)
  have htUpper : ((t + 1 : ℕ) : ℝ) ≤ 3 * n ^ (0.25 : ℝ) := by
    have hceil : (t : ℝ) < n ^ (0.25 : ℝ) + 1 := by
      dsimp [t]
      exact Nat.ceil_lt_add_one (by positivity)
    have hceil' : (t : ℝ) + 1 < n ^ (0.25 : ℝ) + 2 := by linarith
    have hlin' : n ^ (0.25 : ℝ) + 2 ≤ 3 * n ^ (0.25 : ℝ) := by
      linarith [hnQuarter]
    simpa [Nat.cast_add] using hceil'.le.trans hlin'
  have hpowmul : n ^ (0.25 : ℝ) * n ^ (0.4 : ℝ) = n ^ (0.65 : ℝ) := by
    rw [← Real.rpow_add (by positivity : 0 < n)]
    congr 1
    norm_num
  have hloglowerBound : -Real.log lower ≤ 7 * n ^ (0.65 : ℝ) := by
    rw [hloglower]
    have hlog8' : Real.log 8 ≤ n ^ (0.4 : ℝ) := by simpa [n] using hlog8
    have hlog2' : Real.log 2 ≤ n ^ (0.65 : ℝ) := by simpa [n] using hlog2
    have hfactor : n ^ (0.4 : ℝ) + Real.log 8 ≤ 2 * n ^ (0.4 : ℝ) := by
      linarith [hlog8']
    have hmul : ((t + 1 : ℕ) : ℝ) * (n ^ (0.4 : ℝ) + Real.log 8) ≤
        (3 * n ^ (0.25 : ℝ)) * (2 * n ^ (0.4 : ℝ)) :=
      mul_le_mul htUpper hfactor (by positivity) (by positivity)
    calc
      ((t + 1 : ℕ) : ℝ) * (n ^ (0.4 : ℝ) + Real.log 8) + Real.log 2 ≤
          (3 * n ^ (0.25 : ℝ)) * (2 * n ^ (0.4 : ℝ)) + n ^ (0.65 : ℝ) := by
        exact add_le_add hmul hlog2'
      _ = 7 * n ^ (0.65 : ℝ) := by
        calc
          (3 * n ^ (0.25 : ℝ)) * (2 * n ^ (0.4 : ℝ)) + n ^ (0.65 : ℝ) =
              6 * (n ^ (0.25 : ℝ) * n ^ (0.4 : ℝ)) + n ^ (0.65 : ℝ) := by ring
          _ = 7 * n ^ (0.65 : ℝ) := by rw [hpowmul]; ring
  have hlogmass : -Real.log (∑ x ∈ A, τ.w x) ≤ 7 * n ^ (0.65 : ℝ) := by
    have hmpos : 0 < ∑ x ∈ A, τ.w x := lt_of_lt_of_le hlowerpos hmass
    have hlog := Real.log_le_log hlowerpos hmass
    linarith
  have hxsSmall : n ^ (κ.xs / 4) ≤ n ^ (0.65 : ℝ) := by
    exact Real.rpow_le_rpow_of_exponent_le (by linarith : 1 ≤ n)
      (by nlinarith [hκ.xs_rng.2])
  have hlin' : 9 * n ^ (0.65 : ℝ) ≤ κ.α * n := by
    have hmul := mul_le_mul_of_nonneg_left hlin (by norm_num : 0 ≤ (9 : ℝ))
    calc
      9 * n ^ (0.65 : ℝ) ≤ 9 * (κ.α / 9 * n) := by simpa [n] using hmul
      _ = κ.α * n := by ring
  calc
    n ^ (κ.xs / 4) - Real.log (∑ x ∈ A, τ.w x) ≤
        n ^ (0.65 : ℝ) + 7 * n ^ (0.65 : ℝ) := by linarith [hxsSmall, hlogmass]
    _ = 8 * n ^ (0.65 : ℝ) := by ring
    _ ≤ 9 * n ^ (0.65 : ℝ) := by
      exact mul_le_mul_of_nonneg_right (by norm_num : (8 : ℝ) ≤ 9)
        (Real.rpow_nonneg (by positivity) _)
    _ ≤ κ.α * n := hlin'

theorem acoef_abs_le_three_of_degree {N : ℕ} (E : Fin N → Fin N → Prop)
    (c : Colour) (π : Fin N → ℝ) (x y : Fin N)
    (hD : (1 / 3 : ℝ) ≤ deg E c π x) :
    |acoef E c π x y| ≤ 3 := by
  classical
  have hDpos : 0 < deg E c π x := by linarith
  by_cases hh : Hits E c x y
  · have hdiv : 1 / deg E c π x ≤ 3 := by
      apply (div_le_iff₀ hDpos).2
      nlinarith
    rw [acoef, hit, if_pos hh]
    rw [abs_le]
    constructor <;> linarith [div_nonneg (show (0 : ℝ) ≤ 1 by norm_num) hDpos.le]
  · rw [acoef, hit, if_neg hh]
    norm_num

private theorem acoef_fv_close_of_gate {N : ℕ} (E : Fin N → Fin N → Prop)
    (c : Colour) (π : Fin N → ℝ) (C0 b : ℝ) (x y : Fin N)
    (hgate : |deg E c π x - 1 / 2| ≤ C0 * b)
    (hscale : C0 * b ≤ 1 / 6) :
    |acoef E c π x y - fv E c x y| ≤ 6 * C0 * b := by
  let D (x : Fin N) := deg E c π x
  have hcb : 0 ≤ C0 * b := le_trans (abs_nonneg _) hgate
  have hgate' := abs_le.mp hgate
  have hDlo : (1 / 3 : ℝ) ≤ D x := by
    dsimp [D]
    nlinarith [hgate'.1, hgate'.2]
  have hDpos : 0 < D x := lt_of_lt_of_le (by norm_num) hDlo
  have hhit : 0 ≤ hit E c x y ∧ hit E c x y ≤ 1 := by
    unfold hit
    split_ifs <;> norm_num
  have hdev : |1 - 2 * D x| ≤ 2 * C0 * b := by
    have heq : 1 - 2 * D x = -(2 * (D x - 1 / 2)) := by ring
    rw [heq, abs_neg, abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 2)]
    nlinarith [hgate'.1, hgate'.2]
  have hformula : acoef E c π x y - fv E c x y =
      hit E c x y * (1 - 2 * D x) / D x := by
    rw [acoef, fv]
    dsimp [D]
    have hcancel : deg E c π x * (deg E c π x)⁻¹ = 1 :=
      mul_inv_cancel₀ (ne_of_gt hDpos)
    have hcancelExpr : hit E c x y * deg E c π x *
        (deg E c π x)⁻¹ * 2 = hit E c x y * 2 := by
      calc
        hit E c x y * deg E c π x * (deg E c π x)⁻¹ * 2 =
            hit E c x y * 2 *
              (deg E c π x * (deg E c π x)⁻¹) := by ring
        _ = hit E c x y * 2 := by rw [hcancel]; ring
    rw [div_eq_mul_inv, div_eq_mul_inv]
    ring_nf
    rw [hcancelExpr]
  have hhitabs : |hit E c x y| ≤ 1 := by
    rw [abs_of_nonneg hhit.1]
    exact hhit.2
  have htop : |hit E c x y| * |1 - 2 * D x| ≤ 2 * C0 * b := by
    calc
      |hit E c x y| * |1 - 2 * D x| ≤ 1 * (2 * C0 * b) :=
        mul_le_mul hhitabs hdev (abs_nonneg _) (by nlinarith [hcb])
      _ = 2 * C0 * b := by ring
  have hDinv : 1 / D x ≤ 3 := by
    apply (div_le_iff₀ hDpos).2
    nlinarith [hDlo]
  calc
    |acoef E c π x y - fv E c x y| =
        |hit E c x y| * |1 - 2 * D x| / D x := by
      rw [hformula, abs_div, abs_mul, abs_of_pos hDpos]
    _ ≤ (2 * C0 * b) / D x :=
      div_le_div_of_nonneg_right htop hDpos.le
    _ = (2 * C0 * b) * (1 / D x) := by ring
    _ ≤ (2 * C0 * b) * 3 :=
      mul_le_mul_of_nonneg_left hDinv (by nlinarith [hcb])
    _ = 6 * C0 * b := by ring

theorem fv_abs_le_one {N : ℕ} (E : Fin N → Fin N → Prop)
    (c : Colour) (x y : Fin N) : |fv E c x y| ≤ 1 := by
  classical
  by_cases hh : Hits E c x y <;> simp [fv, hit, hh] <;> norm_num

theorem one_le_three_pow (u : ℕ) : (1 : ℝ) ≤ 3 ^ u := by
  induction u with
  | zero => norm_num
  | succ u ih =>
      rw [pow_succ]
      nlinarith

private theorem iid_prod_factorization {N u : ℕ} (τ : Law N)
    (J : Finset (Fin u)) (g : Fin N → ℝ) :
    ∑ xs : Fin u → Fin N, prodW τ.w xs * ∏ i ∈ J, g (xs i) =
      (∑ x, τ.w x * g x) ^ J.card := by
  classical
  let f : Fin u → Fin N → ℝ := fun i x => τ.w x * if i ∈ J then g x else 1
  calc
    ∑ xs : Fin u → Fin N, prodW τ.w xs * ∏ i ∈ J, g (xs i) =
        ∑ xs : Fin u → Fin N, ∏ i, f i (xs i) := by
      apply Finset.sum_congr rfl
      intro xs hxs
      dsimp [f, prodW]
      simp_rw [Finset.prod_mul_distrib, Finset.prod_ite_mem_eq]
    _ = ∏ i, ∑ x, f i x := by rw [← Fintype.prod_sum]
    _ = ∏ i : Fin u, if i ∈ J then (∑ x, τ.w x * g x) else 1 := by
      apply Finset.prod_congr rfl
      intro i hi
      by_cases hmem : i ∈ J <;> simp [f, hmem, τ.sum_eq_one]
    _ = (∑ x, τ.w x * g x) ^ J.card := by
      simp [Finset.prod_ite]

private theorem pi_coord_expect {N t : ℕ} (τ : Law N) (i : Fin t)
    (g : Fin N → ℝ) :
    (FinProb.pi (fun _ : Fin t => τ)).expect (fun xs => g (xs i)) = τ.expect g := by
  classical
  change (∑ xs : Fin t → Fin N, prodW τ.w xs * g (xs i)) = ∑ x, τ.w x * g x
  have h := iid_prod_factorization τ ({i} : Finset (Fin t)) g
  simpa [Finset.prod_singleton] using h

private theorem fintype_mul_sum {α : Type*} [Fintype α] (a : ℝ) (f : α → ℝ) :
    a * (∑ x, f x) = ∑ x, a * f x := by
  simpa using Finset.mul_sum Finset.univ f a

private theorem fintype_sum_mul {α : Type*} [Fintype α] (f : α → ℝ) (a : ℝ) :
    (∑ x, f x) * a = ∑ x, f x * a := by
  simpa using Finset.sum_mul Finset.univ f a

private theorem iid_vector_sum_second_moment {N M t : ℕ}
    (τ : Law N) (ν : Law M) (g : Fin N → Fin M → ℝ)
    (B ε : ℝ) (hB : ∀ x y, |g x y| ≤ B)
    (hMean : ∑ y, ν.w y * (∑ x, τ.w x * g x y) ^ 2 ≤ ε ^ 2) :
    (FinProb.pi (fun _ : Fin t => τ)).expect (fun xs =>
      ∑ y, ν.w y * (∑ i, g (xs i) y) ^ 2) ≤
        (t : ℝ) * B ^ 2 + (t : ℝ) ^ 2 * ε ^ 2 := by
  classical
  let P : FinProb (Fin t → Fin N) := FinProb.pi (fun _ : Fin t => τ)
  let μ (y : Fin M) : ℝ := ∑ x, τ.w x * g x y
  let v (y : Fin M) : ℝ := ∑ x, τ.w x * g x y ^ 2
  have hMarg (i : Fin t) (y : Fin M) :
      P.expect (fun xs => g (xs i) y) = μ y := by
    simpa [P, μ, FinProb.expect] using pi_coord_expect τ i (fun x => g x y)
  have hCross (i j : Fin t) (y : Fin M) :
      P.expect (fun xs => g (xs i) y * g (xs j) y) =
        if i = j then v y else μ y ^ 2 := by
    by_cases hij : i = j
    · subst j
      have h := iid_prod_factorization τ ({i} : Finset (Fin t)) (fun x => g x y ^ 2)
      have hsum : ∑ xs : Fin t → Fin N,
          prodW τ.w xs * (g (xs i) y * g (xs i) y) = v y := by
        simpa [v, Finset.prod_singleton, pow_two] using h
      simpa [P, FinProb.expect, FinProb.pi, prodW] using hsum
    · let J : Finset (Fin t) := insert i {j}
      have hprod (xs : Fin t → Fin N) :
          ∏ r ∈ J, g (xs r) y = g (xs i) y * g (xs j) y := by
        simp [J, hij]
      have h := iid_prod_factorization τ J (fun x => g x y)
      have hsum : ∑ xs : Fin t → Fin N,
          prodW τ.w xs * (g (xs i) y * g (xs j) y) = μ y ^ 2 := by
        calc
          ∑ xs, prodW τ.w xs * (g (xs i) y * g (xs j) y) =
              ∑ xs, prodW τ.w xs * ∏ r ∈ J, g (xs r) y := by
            apply Finset.sum_congr rfl
            intro xs hxs
            rw [hprod]
          _ = (∑ x, τ.w x * g x y) ^ J.card := iid_prod_factorization τ J (fun x => g x y)
          _ = μ y ^ 2 := by simp [J, μ, hij]
      simpa [P, FinProb.expect, FinProb.pi, prodW, hij] using hsum
  have hdiag (y : Fin M) : v y ≤ B ^ 2 := by
    dsimp [v]
    calc
      ∑ x, τ.w x * g x y ^ 2 ≤ ∑ x, τ.w x * B ^ 2 := by
        apply Finset.sum_le_sum
        intro x hx
        have hgy := hB x y
        have hBnonneg : 0 ≤ B := le_trans (abs_nonneg (g x y)) hgy
        have hAbs : |g x y| ≤ |B| := by simpa [abs_of_nonneg hBnonneg] using hgy
        have hsq : g x y ^ 2 ≤ B ^ 2 := (sq_le_sq).2 hAbs
        exact mul_le_mul_of_nonneg_left hsq (τ.nonneg x)
      _ = B ^ 2 := by rw [← Finset.sum_mul, τ.sum_eq_one]; ring
  have hY (y : Fin M) :
      P.expect (fun xs => (∑ i, g (xs i) y) ^ 2) ≤
        (t : ℝ) * B ^ 2 + (t : ℝ) ^ 2 * μ y ^ 2 := by
    have hexpand (xs : Fin t → Fin N) :
        (∑ i, g (xs i) y) ^ 2 = ∑ i, ∑ j, g (xs i) y * g (xs j) y := by
      rw [pow_two, Fintype.sum_mul_sum]
    have hExact : P.expect (fun xs => (∑ i, g (xs i) y) ^ 2) =
        ∑ i, ∑ j, P.expect (fun xs => g (xs i) y * g (xs j) y) := by
      unfold FinProb.expect
      calc
        ∑ xs, P.w xs * (∑ i, g (xs i) y) ^ 2 =
            ∑ xs, ∑ i, ∑ j, P.w xs * (g (xs i) y * g (xs j) y) := by
          apply Finset.sum_congr rfl
          intro xs hxs
          rw [hexpand]
          calc
            P.w xs * (∑ i, ∑ j, g (xs i) y * g (xs j) y) =
                ∑ i, P.w xs * (∑ j, g (xs i) y * g (xs j) y) :=
              fintype_mul_sum (P.w xs) (fun i => ∑ j, g (xs i) y * g (xs j) y)
            _ = ∑ i, ∑ j, P.w xs * (g (xs i) y * g (xs j) y) := by
              apply Finset.sum_congr rfl
              intro i hi
              exact fintype_mul_sum (P.w xs) (fun j => g (xs i) y * g (xs j) y)
        _ = ∑ i, ∑ j, ∑ xs, P.w xs * (g (xs i) y * g (xs j) y) := by
          rw [Finset.sum_comm]
          congr 1
          ext i
          rw [Finset.sum_comm]
        _ = ∑ i, ∑ j, P.expect (fun xs => g (xs i) y * g (xs j) y) := by
          simp only [FinProb.expect]
    have hrow (i : Fin t) :
      (∑ j, (if i = j then v y else μ y ^ 2)) ≤ B ^ 2 + (t : ℝ) * μ y ^ 2 := by
      have hdiagFin : ∑ j : Fin t, (if i = j then B ^ 2 else 0) = B ^ 2 := by simp
      have hconst : ∑ j : Fin t, μ y ^ 2 = (t : ℝ) * μ y ^ 2 := by simp
      have hsum : ∑ j : Fin t, (if i = j then v y else μ y ^ 2) ≤
          ∑ j : Fin t, (if i = j then B ^ 2 else 0) + ∑ j : Fin t, μ y ^ 2 := by
        rw [← Finset.sum_add_distrib]
        apply Finset.sum_le_sum
        intro j hj
        by_cases hij : i = j
        · simp [hij]
          nlinarith [hdiag y, sq_nonneg (μ y)]
        · simp [hij]
      simpa [hdiagFin, hconst] using hsum
    have hsumI : ∑ i : Fin t, (B ^ 2 + (t : ℝ) * μ y ^ 2) =
        (t : ℝ) * B ^ 2 + (t : ℝ) ^ 2 * μ y ^ 2 := by
      simp [Finset.sum_add_distrib, Finset.sum_const, nsmul_eq_mul]
      ring
    calc
      P.expect (fun xs => (∑ i, g (xs i) y) ^ 2) =
          ∑ i, ∑ j, P.expect (fun xs => g (xs i) y * g (xs j) y) := hExact
      _ ≤ ∑ i : Fin t, (B ^ 2 + (t : ℝ) * μ y ^ 2) := by
        apply Finset.sum_le_sum
        intro i hi
        calc
          ∑ j, P.expect (fun xs => g (xs i) y * g (xs j) y) ≤
              ∑ j, if i = j then v y else μ y ^ 2 := by
            change (∑ j ∈ Finset.univ,
                P.expect (fun xs => g (xs i) y * g (xs j) y)) ≤
              ∑ j ∈ Finset.univ, if i = j then v y else μ y ^ 2
            apply Finset.sum_le_sum
            intro j hj
            rw [hCross i j y]
          _ ≤ B ^ 2 + (t : ℝ) * μ y ^ 2 := hrow i
      _ = (t : ℝ) * B ^ 2 + (t : ℝ) ^ 2 * μ y ^ 2 := hsumI
  have hFubini :
      P.expect (fun xs => ∑ y, ν.w y * (∑ i, g (xs i) y) ^ 2) =
        ∑ y, ν.w y * P.expect (fun xs => (∑ i, g (xs i) y) ^ 2) := by
    unfold FinProb.expect
    calc
      ∑ xs, P.w xs * (∑ y, ν.w y * (∑ i, g (xs i) y) ^ 2) =
          ∑ xs, ∑ y, ν.w y * (P.w xs * (∑ i, g (xs i) y) ^ 2) := by
        apply Finset.sum_congr rfl
        intro xs hx
        calc
          P.w xs * (∑ y, ν.w y * (∑ i, g (xs i) y) ^ 2) =
              ∑ y, P.w xs * (ν.w y * (∑ i, g (xs i) y) ^ 2) :=
            fintype_mul_sum (P.w xs) (fun y => ν.w y * (∑ i, g (xs i) y) ^ 2)
          _ = ∑ y, ν.w y * (P.w xs * (∑ i, g (xs i) y) ^ 2) := by
            apply Finset.sum_congr rfl
            intro y hy
            ring
      _ = ∑ y, ∑ xs, ν.w y * (P.w xs * (∑ i, g (xs i) y) ^ 2) := by
        rw [Finset.sum_comm]
      _ = ∑ y, ν.w y * P.expect (fun xs => (∑ i, g (xs i) y) ^ 2) := by
        apply Finset.sum_congr rfl
        intro y hy
        exact (fintype_mul_sum (ν.w y)
          (fun xs => P.w xs * (∑ i, g (xs i) y) ^ 2)).symm
  calc
    P.expect (fun xs => ∑ y, ν.w y * (∑ i, g (xs i) y) ^ 2) =
        ∑ y, ν.w y * P.expect (fun xs => (∑ i, g (xs i) y) ^ 2) := hFubini
    _ ≤ ∑ y, ν.w y * ((t : ℝ) * B ^ 2 + (t : ℝ) ^ 2 * μ y ^ 2) := by
      apply Finset.sum_le_sum
      intro y hy
      exact mul_le_mul_of_nonneg_left (hY y) (ν.nonneg y)
    _ ≤ (t : ℝ) * B ^ 2 + (t : ℝ) ^ 2 * ε ^ 2 := by
      have hFirst : ∑ y, ν.w y * ((t : ℝ) * B ^ 2) = (t : ℝ) * B ^ 2 := by
        rw [← fintype_sum_mul, ν.sum_eq_one]
        ring
      have hVar : ∑ y, ν.w y * μ y ^ 2 ≤ ε ^ 2 := by simpa [μ] using hMean
      have hSecond : ∑ y, ν.w y * ((t : ℝ) ^ 2 * μ y ^ 2) ≤
          (t : ℝ) ^ 2 * ε ^ 2 := by
        calc
          ∑ y, ν.w y * ((t : ℝ) ^ 2 * μ y ^ 2) =
              (t : ℝ) ^ 2 * ∑ y, ν.w y * μ y ^ 2 := by
            calc
              ∑ y, ν.w y * ((t : ℝ) ^ 2 * μ y ^ 2) =
                  ∑ y, (t : ℝ) ^ 2 * (ν.w y * μ y ^ 2) := by
                apply Finset.sum_congr rfl
                intro y hy
                ring
              _ = (t : ℝ) ^ 2 * ∑ y, ν.w y * μ y ^ 2 := (fintype_mul_sum _ _).symm
          _ ≤ (t : ℝ) ^ 2 * ε ^ 2 :=
            mul_le_mul_of_nonneg_left hVar (sq_nonneg _)
      calc
        ∑ y, ν.w y * ((t : ℝ) * B ^ 2 + (t : ℝ) ^ 2 * μ y ^ 2) =
            (∑ y, ν.w y * ((t : ℝ) * B ^ 2)) +
              ∑ y, ν.w y * ((t : ℝ) ^ 2 * μ y ^ 2) := by
          simp_rw [mul_add]
          rw [Finset.sum_add_distrib]
        _ ≤ (t : ℝ) * B ^ 2 + (t : ℝ) ^ 2 * ε ^ 2 :=
          add_le_add (le_of_eq hFirst) hSecond

private theorem iid_vector_good_mass {N M t : ℕ}
    (τ : Law N) (ν : Law M) (g : Fin N → Fin M → ℝ)
    (B ε : ℝ) (hB : ∀ x y, |g x y| ≤ B)
    (hMean : ∑ y, ν.w y * (∑ x, τ.w x * g x y) ^ 2 ≤ ε ^ 2)
    (ht : 0 < t) (hBpos : 0 < B) (hteps : (t : ℝ) * ε ^ 2 ≤ B ^ 2) :
    ∑ xs ∈ Finset.univ.filter (fun xs =>
      ∑ y, ν.w y * (∑ i, g (xs i) y) ^ 2 ≤ 4 * (t : ℝ) * B ^ 2),
      (FinProb.pi (fun _ : Fin t => τ)).w xs ≥ 1 / 2 := by
  classical
  let P : FinProb (Fin t → Fin N) := FinProb.pi (fun _ : Fin t => τ)
  let normSq : (Fin t → Fin N) → ℝ := fun xs =>
    ∑ y, ν.w y * (∑ i, g (xs i) y) ^ 2
  let Good : (Fin t → Fin N) → Prop := fun xs =>
    normSq xs ≤ 4 * (t : ℝ) * B ^ 2
  let Bad : (Fin t → Fin N) → Prop := fun xs => ¬ (Good xs)
  letI : DecidablePred Good := fun xs => Classical.propDecidable (Good xs)
  letI : DecidablePred Bad := fun xs => Classical.propDecidable (Bad xs)
  let GoodSet : Finset (Fin t → Fin N) := Finset.univ.filter Good
  let BadSet : Finset (Fin t → Fin N) := Finset.univ.filter Bad
  have hnorm_nonneg (xs : Fin t → Fin N) : 0 ≤ normSq xs := by
    unfold normSq
    exact Finset.sum_nonneg fun y hy => mul_nonneg (ν.nonneg y) (sq_nonneg _)
  have hMoment := iid_vector_sum_second_moment (t := t) τ ν g B ε hB hMean
  have hMomentBound : P.expect normSq ≤ 2 * (t : ℝ) * B ^ 2 := by
    have hraw : P.expect normSq ≤ (t : ℝ) * B ^ 2 + (t : ℝ) ^ 2 * ε ^ 2 := by
      simpa [P, normSq] using hMoment
    calc
      P.expect normSq ≤ (t : ℝ) * B ^ 2 + (t : ℝ) ^ 2 * ε ^ 2 := hraw
      _ ≤ (t : ℝ) * B ^ 2 + (t : ℝ) * B ^ 2 := by
        have ht0 : 0 ≤ (t : ℝ) := Nat.cast_nonneg _
        have h := mul_le_mul_of_nonneg_left hteps ht0
        nlinarith
      _ = 2 * (t : ℝ) * B ^ 2 := by ring
  have hthreshold : 0 < 4 * (t : ℝ) * B ^ 2 := by positivity
  have hMarkov := FinProb.markov P normSq (4 * (t : ℝ) * B ^ 2)
    hnorm_nonneg hthreshold
  have hbad : P.pr (fun xs => 4 * (t : ℝ) * B ^ 2 ≤ normSq xs) ≤ 1 / 2 := by
    calc
      P.pr (fun xs => 4 * (t : ℝ) * B ^ 2 ≤ normSq xs) ≤
          P.expect normSq / (4 * (t : ℝ) * B ^ 2) := hMarkov
      _ ≤ (2 * (t : ℝ) * B ^ 2) / (4 * (t : ℝ) * B ^ 2) :=
        div_le_div_of_nonneg_right hMomentBound (by positivity)
      _ = 1 / 2 := by
        field_simp [ne_of_gt (by exact_mod_cast ht), ne_of_gt hBpos]
        norm_num
  have hGoodPr : P.pr Good = ∑ xs ∈ GoodSet, P.w xs := by
    unfold FinProb.pr
    rw [← Finset.sum_filter]
  have hBadPr : P.pr Bad = ∑ xs ∈ BadSet, P.w xs := by
    unfold FinProb.pr
    rw [← Finset.sum_filter]
  have hDisj : Disjoint GoodSet BadSet := by
    apply Finset.disjoint_left.mpr
    intro xs hgood hbad
    have hg : Good xs := (Finset.mem_filter.mp hgood).2
    have hb : Bad xs := (Finset.mem_filter.mp hbad).2
    exact hb hg
  have hUnion : GoodSet ∪ BadSet = Finset.univ := by
    ext xs
    by_cases h : Good xs <;> simp [GoodSet, BadSet, Bad, h]
  have hcompl : P.pr Good + P.pr Bad = 1 := by
    rw [hGoodPr, hBadPr, ← Finset.sum_union hDisj, hUnion, P.sum_eq_one]
  let MarkovSet := Finset.univ.filter (fun xs =>
    4 * (t : ℝ) * B ^ 2 ≤ normSq xs)
  have hMarkovPr : P.pr (fun xs => 4 * (t : ℝ) * B ^ 2 ≤ normSq xs) =
      ∑ xs ∈ MarkovSet, P.w xs := by
    unfold FinProb.pr
    rw [← Finset.sum_filter]
  have hsubset : BadSet ⊆ MarkovSet := by
    intro xs hxs
    have hb : Bad xs := (Finset.mem_filter.mp hxs).2
    change ¬ (normSq xs ≤ 4 * (t : ℝ) * B ^ 2) at hb
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, (not_le.mp hb).le⟩
  have hnotMass : P.pr Bad ≤ 1 / 2 := by
    calc
      P.pr Bad = ∑ xs ∈ BadSet, P.w xs := hBadPr
      _ ≤ ∑ xs ∈ MarkovSet, P.w xs :=
        Finset.sum_le_sum_of_subset_of_nonneg hsubset
          (fun xs hxs _ => P.nonneg xs)
      _ = P.pr (fun xs => 4 * (t : ℝ) * B ^ 2 ≤ normSq xs) := hMarkovPr.symm
      _ ≤ 1 / 2 := hbad
  have hgoodMass : 1 / 2 ≤ P.pr Good := by
    rw [← sub_nonneg, ← hcompl]
    linarith
  rw [hGoodPr] at hgoodMass
  simpa [GoodSet, Good, normSq] using hgoodMass

private noncomputable def productLaw {α β : Type*} [Fintype α] [Fintype β]
    (P : FinProb α) (Q : FinProb β) : FinProb (α × β) where
  w p := P.w p.1 * Q.w p.2
  nonneg p := mul_nonneg (P.nonneg _) (Q.nonneg _)
  sum_eq_one := by
    rw [Fintype.sum_prod_type]
    simp_rw [← Finset.mul_sum, Q.sum_eq_one]
    simpa using P.sum_eq_one

private theorem productLaw_pr_fst {α β : Type*} [Fintype α] [Fintype β]
    (P : FinProb α) (Q : FinProb β) (R : α → β → Prop) :
    (productLaw P Q).pr (fun p => R p.1 p.2) =
      ∑ a, P.w a * ∑ b, if R a b then Q.w b else 0 := by
  classical
  unfold FinProb.pr productLaw
  rw [Fintype.sum_prod_type]
  apply Finset.sum_congr rfl
  intro a ha
  calc
    ∑ b, (if R a b then P.w a * Q.w b else 0) =
        ∑ b, P.w a * (if R a b then Q.w b else 0) := by
          apply Finset.sum_congr rfl
          intro b hb
          by_cases hR : R a b <;> simp [hR]
    _ = P.w a * ∑ b, if R a b then Q.w b else 0 := by
      rw [← Finset.mul_sum]

private theorem productLaw_pr_snd {α β : Type*} [Fintype α] [Fintype β]
    (P : FinProb α) (Q : FinProb β) (R : α → β → Prop) :
    (productLaw P Q).pr (fun p => R p.1 p.2) =
      ∑ b, Q.w b * ∑ a, if R a b then P.w a else 0 := by
  classical
  unfold FinProb.pr productLaw
  rw [Fintype.sum_prod_type, Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro b hb
  calc
    ∑ a, (if R a b then P.w a * Q.w b else 0) =
        ∑ a, Q.w b * (if R a b then P.w a else 0) := by
          apply Finset.sum_congr rfl
          intro a ha
          by_cases hR : R a b <;> simp [hR] <;> ring
    _ = Q.w b * ∑ a, if R a b then P.w a else 0 := by
      rw [← Finset.mul_sum]

private theorem law_mass_subset {N : ℕ} (τ : Law N)
    (A B : Finset (Fin N)) (hAB : A ⊆ B) :
    (∑ x ∈ A, τ.w x) ≤ ∑ x ∈ B, τ.w x :=
  Finset.sum_le_sum_of_subset_of_nonneg hAB (fun x _ _ => τ.nonneg x)

private theorem signed_pair_tail_impossible {N : ℕ}
    (τ ν : Law N) (g : Fin N → Fin N → ℝ)
    (δ p eps B : ℝ) (t : ℕ)
    (Active : Fin N → Prop)
    (hzero : ∀ x, ¬ Active x → ∀ y, g x y = 0)
    (hδ : 0 < δ) (hp : 0 < p) (hp1 : p ≤ 1)
    (hB : 0 < B) (hBbound : ∀ x y, |g x y| ≤ B)
    (heps : 0 ≤ eps) (hsample : (t : ℝ) * eps ^ 2 ≤ B ^ 2)
    (ht : 0 < t)
    (hcontr : (t : ℝ) * δ > 2 * eps * B * Real.sqrt (t : ℝ))
    (hKsym : ∀ x z,
      (∑ y, ν.w y * g x y * g z y) =
        (∑ y, ν.w y * g z y * g x y))
    (hMean : ∀ (A : Finset (Fin N)) (hA : 0 < ∑ x ∈ A, τ.w x),
      (p / 4) ^ (t + 1) / 2 ≤ ∑ x ∈ A, τ.w x →
      (∀ x ∈ A, Active x) →
      ∑ y, ν.w y *
        (∑ x, (τ.restrict A hA).w x * g x y) ^ 2 ≤ eps ^ 2)
    (s : ℝ) (hs : s = 1 ∨ s = -1)
    (hRelMass : p / 2 <
      ∑ x, ∑ z, (if δ < s * (∑ y, ν.w y * g x y * g z y)
        then τ.w x * τ.w z else 0)) : False := by
  classical
  let r : ℝ := p / 4
  let lower : ℝ := r ^ (t + 1) / 2
  let K (x z : Fin N) : ℝ := ∑ y, ν.w y * g x y * g z y
  let rel (x z : Fin N) : Prop := δ < s * K x z
  let rowSet (x : Fin N) : Finset (Fin N) := Finset.univ.filter (rel x)
  let rowMass (x : Fin N) : ℝ := ∑ z ∈ rowSet x, τ.w z
  let A : Finset (Fin N) := Finset.univ.filter (fun x => r ≤ rowMass x)
  have hr : 0 < r := by dsimp [r]; positivity
  have hr1 : r ≤ 1 := by dsimp [r]; linarith
  have hlowerR : lower ≤ r := by
    have hpow : r ^ t ≤ 1 := pow_le_one₀ hr.le hr1
    dsimp [lower, r]
    have hpow' : (p / 4) ^ t ≤ 1 := by simpa [r] using hpow
    have hpnonneg : 0 ≤ p / 4 := by positivity
    have htplus : (p / 4) ^ (t + 1) = (p / 4) ^ t * (p / 4) := by
      rw [pow_succ]
    rw [htplus]
    nlinarith
  have hrowle (x : Fin N) : rowMass x ≤ 1 := by
    dsimp [rowMass, rowSet]
    calc
      ∑ z ∈ Finset.univ.filter (rel x), τ.w z ≤ ∑ z, τ.w z := by
        apply law_mass_subset τ _ Finset.univ
        exact Finset.filter_subset _ _
      _ = 1 := τ.sum_eq_one
  have hpairEq :
      (∑ x, ∑ z, (if (rel x z) then τ.w x * τ.w z else 0)) =
        ∑ x, τ.w x * rowMass x := by
    have hterm (x z : Fin N) :
        (if rel x z then τ.w x * τ.w z else 0) =
          τ.w x * (if rel x z then τ.w z else 0) := by
      by_cases hR : rel x z <;> simp [hR]
    have hrow (x : Fin N) :
        (∑ z, if rel x z then τ.w z else 0) = rowMass x := by
      dsimp [rowMass, rowSet]
      rw [← Finset.sum_filter]
    apply Finset.sum_congr rfl
    intro x hx
    calc
      ∑ z, (if (rel x z) then τ.w x * τ.w z else 0) =
          ∑ z, τ.w x * (if rel x z then τ.w z else 0) := by
        apply Finset.sum_congr rfl
        intro z hz
        exact hterm x z
      _ = τ.w x * ∑ z, (if rel x z then τ.w z else 0) := by
        rw [← Finset.mul_sum]
      _ = τ.w x * rowMass x := congrArg (fun v : ℝ => τ.w x * v) (hrow x)
  have htotal : p / 2 < ∑ x, τ.w x * rowMass x := by
    calc
      p / 2 < ∑ x, ∑ z, (if rel x z then τ.w x * τ.w z else 0) := by
        simpa [rel, K] using hRelMass
      _ = ∑ x, τ.w x * rowMass x := hpairEq
  have hpoint : ∀ x, τ.w x * rowMass x ≤
      (if x ∈ A then τ.w x else 0) + r * τ.w x := by
    intro x
    by_cases hx : x ∈ A
    · have hτ := τ.nonneg x
      have hmul := mul_le_mul_of_nonneg_left (hrowle x) hτ
      have hadd : τ.w x ≤ τ.w x + r * τ.w x :=
        le_add_of_nonneg_right (mul_nonneg (by positivity) hτ)
      have hmul' : τ.w x * rowMass x ≤ τ.w x := by simpa using hmul
      simpa [hx] using hmul'.trans hadd
    · have hrow : rowMass x < r := by
        have hnot : ¬ r ≤ rowMass x := by
          intro hh
          exact hx (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hh⟩)
        exact lt_of_not_ge hnot
      have hmul := mul_le_mul_of_nonneg_left hrow.le (τ.nonneg x)
      calc
        τ.w x * rowMass x ≤ τ.w x * r := hmul
        _ = r * τ.w x := by ring
        _ = 0 + r * τ.w x := by ring
        _ = (if x ∈ A then τ.w x else 0) + r * τ.w x := by simp [hx]
  have hAmass : r < ∑ x ∈ A, τ.w x := by
    have hsum := Finset.sum_le_sum (s := Finset.univ) (fun x hx => hpoint x)
    have hrewrite :
        ∑ x, ((if x ∈ A then τ.w x else 0) + r * τ.w x) =
          (∑ x ∈ A, τ.w x) + r := by
      rw [Finset.sum_add_distrib, Finset.sum_ite_mem_eq,
        ← Finset.mul_sum, τ.sum_eq_one]
      ring
    rw [hrewrite] at hsum
    have ht' : p / 2 = 2 * r := by dsimp [r]; ring
    rw [ht'] at htotal
    linarith
  have hApos : 0 < ∑ x ∈ A, τ.w x := lt_trans hr hAmass
  have hrowSum (x : Fin N) (hx : x ∈ A) : r ≤ rowMass x :=
    (Finset.mem_filter.mp hx).2
  have hAactive (x : Fin N) (hx : x ∈ A) : Active x := by
    by_contra hnot
    have hKzero (z : Fin N) : K x z = 0 := by
      dsimp [K]
      apply Finset.sum_eq_zero
      intro y hy
      rw [hzero x hnot y]
      ring
    have hrelfalse (z : Fin N) : ¬ rel x z := by
      dsimp [rel]
      rw [hKzero z]
      exact not_lt_of_ge (by nlinarith [hδ])
    have hempty : rowSet x = ∅ := by
      ext z
      simp [rowSet, hrelfalse z]
    have hrowzero : rowMass x = 0 := by simp [rowMass, hempty]
    have hle := hrowSum x hx
    rw [hrowzero] at hle
    exact (not_le_of_gt hr) hle
  let Pτ : FinProb (Fin t → Fin N) := FinProb.pi (fun _ : Fin t => τ)
  let Good (zs : Fin t → Fin N) : Prop :=
    ∑ y, ν.w y * (∑ i, g (zs i) y) ^ 2 ≤ 4 * (t : ℝ) * B ^ 2
  let GoodSet : Finset (Fin t → Fin N) := Finset.univ.filter Good
  have htupleMass (x : Fin N) (hx : x ∈ A) :
      ∑ zs ∈ Finset.univ.filter (fun zs => Good zs ∧ ∀ i, rel x (zs i)),
        Pτ.w zs ≥ r ^ t / 2 := by
    let E := rowSet x
    let q := rowMass x
    have hq : 0 < q := lt_of_lt_of_le hr (hrowSum x hx)
    let ρ : Law N := τ.restrict E hq
    have hEactive : ∀ z ∈ E, Active z := by
      intro z hz
      have hrelxz : rel x z := (Finset.mem_filter.mp hz).2
      by_contra hnot
      have hKzero : K x z = 0 := by
        dsimp [K]
        apply Finset.sum_eq_zero
        intro y hy
        rw [hzero z hnot y]
        ring
      have hcontra : δ < s * 0 := by simpa [rel, hKzero] using hrelxz
      linarith [hδ]
    have hρmean := hMean E hq (le_trans hlowerR (hrowSum x hx)) hEactive
    have hρgood := iid_vector_good_mass ρ ν g B eps hBbound hρmean ht hB hsample
    have hρgood' :
        ∑ zs ∈ Finset.univ.filter Good,
          (FinProb.pi (fun _ : Fin t => ρ)).w zs ≥ 1 / 2 := by
      simpa [Good] using hρgood
    have hρoutside (zs : Fin t → Fin N)
        (hnot : ¬ ∀ i, rel x (zs i)) : prodW ρ.w zs = 0 := by
      push_neg at hnot
      obtain ⟨i, hi⟩ := hnot
      dsimp [prodW]
      apply Finset.prod_eq_zero (Finset.mem_univ i)
      simp [ρ, Law.restrict, E, q, rowMass, rowSet, hi]
    have hgoodInside :
        ∑ zs ∈ GoodSet.filter (fun zs => ∀ i, rel x (zs i)), prodW ρ.w zs ≥ 1 / 2 := by
      have heq :
          ∑ zs ∈ GoodSet.filter (fun zs => ∀ i, rel x (zs i)), prodW ρ.w zs =
            ∑ zs ∈ GoodSet, prodW ρ.w zs := by
        rw [Finset.sum_filter]
        apply Finset.sum_congr rfl
        intro zs hzs
        by_cases hall : ∀ i, rel x (zs i)
        · simp [hall]
        · simp [hall, hρoutside zs hall]
      rw [heq]
      simpa [GoodSet, FinProb.pi, prodW] using hρgood'
    have hcoord (z : Fin N) (hz : z ∈ E) : τ.w z = q * ρ.w z := by
      have hqdef : (∑ y ∈ E, τ.w y) = q := by rfl
      have hrho : ρ.w z = τ.w z / q := by
        simp only [ρ, Law.restrict, if_pos hz]
        rw [hqdef]
      rw [hrho]
      field_simp [ne_of_gt hq]
    have hprod (zs : Fin t → Fin N) (hall : ∀ i, rel x (zs i)) :
        prodW τ.w zs = q ^ t * prodW ρ.w zs := by
      have hzE (i : Fin t) : zs i ∈ E := by
        exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, hall i⟩
      dsimp [prodW]
      calc
        ∏ i, τ.w (zs i) = ∏ i, q * ρ.w (zs i) := by
          apply Finset.prod_congr rfl
          intro i hi
          exact hcoord (zs i) (hzE i)
        _ = (∏ i : Fin t, q) * ∏ i, ρ.w (zs i) := by
          rw [Finset.prod_mul_distrib]
        _ = q ^ t * ∏ i, ρ.w (zs i) := by simp
    have htransfer :
        ∑ zs ∈ GoodSet.filter (fun zs => ∀ i, rel x (zs i)), prodW τ.w zs =
          q ^ t * ∑ zs ∈ GoodSet.filter (fun zs => ∀ i, rel x (zs i)),
            prodW ρ.w zs := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro zs hzs
      exact hprod zs (Finset.mem_filter.mp hzs).2
    have hqpow : r ^ t ≤ q ^ t := pow_le_pow_left₀ hr.le (hrowSum x hx) t
    calc
      ∑ zs ∈ Finset.univ.filter (fun zs => Good zs ∧ ∀ i, rel x (zs i)),
          Pτ.w zs =
        ∑ zs ∈ GoodSet.filter (fun zs => ∀ i, rel x (zs i)), prodW τ.w zs := by
          simp [Pτ, FinProb.pi, GoodSet, prodW, Finset.filter_filter, and_comm]
      _ = q ^ t * ∑ zs ∈ GoodSet.filter (fun zs => ∀ i, rel x (zs i)),
            prodW ρ.w zs := htransfer
      _ ≥ q ^ t * (1 / 2) := by
        exact mul_le_mul_of_nonneg_left hgoodInside (pow_nonneg hq.le t)
      _ ≥ r ^ t / 2 := by nlinarith [hqpow]
  let eventRel (zs : Fin t → Fin N) (x : Fin N) : Prop :=
    x ∈ A ∧ Good zs ∧ ∀ i, rel x (zs i)
  let eventInd (zs : Fin t → Fin N) (x : Fin N) : ℝ :=
    if eventRel zs x then 1 else 0
  let tupleMass (zs : Fin t → Fin N) : ℝ :=
    ∑ x, τ.w x * eventInd zs x
  have hpoint' : ∀ x ∈ A,
      r ^ t / 2 ≤ ∑ zs, Pτ.w zs * eventInd zs x := by
    intro x hxA
    have h := htupleMass x hxA
    rw [Finset.sum_filter] at h
    simpa [eventInd, eventRel, hxA, Good, mul_ite, mul_zero, mul_one,
      and_assoc, and_left_comm, and_comm] using h
  have hExpectedMass : lower <
      ∑ x, τ.w x * (∑ zs, Pτ.w zs * eventInd zs x) := by
    calc
      lower = r * (r ^ t / 2) := by
        dsimp [lower]
        rw [pow_succ]
        ring
      _ < (∑ x ∈ A, τ.w x) * (r ^ t / 2) := by
        exact mul_lt_mul_of_pos_right hAmass (by positivity)
      _ ≤ ∑ x ∈ A, τ.w x * (r ^ t / 2) := by
        rw [Finset.sum_mul]
      _ ≤ ∑ x ∈ A, τ.w x *
          (∑ zs, Pτ.w zs * eventInd zs x) := by
        apply Finset.sum_le_sum
        intro x hx
        exact mul_le_mul_of_nonneg_left (hpoint' x hx) (τ.nonneg x)
      _ ≤ ∑ x, τ.w x * (∑ zs, Pτ.w zs * eventInd zs x) := by
        apply Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ A)
        intro x hx hnot
        exact mul_nonneg (τ.nonneg x)
          (Finset.sum_nonneg fun zs hzs =>
            mul_nonneg (Pτ.nonneg zs) (by dsimp [eventInd]; split_ifs <;> norm_num))
  have hJointMass : lower < ∑ zs, Pτ.w zs * tupleMass zs := by
    calc
      lower < ∑ x, τ.w x * (∑ zs, Pτ.w zs * eventInd zs x) := hExpectedMass
      _ = ∑ zs, Pτ.w zs * tupleMass zs := by
        calc
          ∑ x, τ.w x * (∑ zs, Pτ.w zs * eventInd zs x) =
              ∑ x, ∑ zs, τ.w x * (Pτ.w zs * eventInd zs x) := by
            apply Finset.sum_congr rfl
            intro x hx
            rw [Finset.mul_sum]
          _ = ∑ zs, ∑ x, τ.w x * (Pτ.w zs * eventInd zs x) := by
            rw [Finset.sum_comm]
          _ = ∑ zs, Pτ.w zs * tupleMass zs := by
            apply Finset.sum_congr rfl
            intro zs hzs
            calc
              ∑ x, τ.w x * (Pτ.w zs * eventInd zs x) =
                  Pτ.w zs * ∑ x, τ.w x * eventInd zs x := by
                calc
                  ∑ x, τ.w x * (Pτ.w zs * eventInd zs x) =
                      ∑ x, Pτ.w zs * (τ.w x * eventInd zs x) := by
                    apply Finset.sum_congr rfl
                    intro x hx
                    ring
                  _ = Pτ.w zs * ∑ x, τ.w x * eventInd zs x := by
                    rw [← Finset.mul_sum]
              _ = Pτ.w zs * tupleMass zs := by rfl
  have hselect : ∃ zs, lower ≤ tupleMass zs := by
    by_contra hnone
    push_neg at hnone
    have hlt (zs : Fin t → Fin N) : tupleMass zs < lower := by
      exact hnone zs
    have hsum : ∑ zs, Pτ.w zs * tupleMass zs ≤ lower := by
      calc
        ∑ zs, Pτ.w zs * tupleMass zs ≤ ∑ zs, Pτ.w zs * lower := by
          apply Finset.sum_le_sum
          intro zs hzs
          exact mul_le_mul_of_nonneg_left (hlt zs).le (Pτ.nonneg zs)
        _ = lower := by rw [← Finset.sum_mul, Pτ.sum_eq_one]; ring
    exact (not_lt_of_ge hsum) hJointMass
  obtain ⟨zs, hzsMass⟩ := hselect
  let A₀ : Finset (Fin N) := Finset.univ.filter (fun x => eventRel zs x)
  have hA₀mass : lower ≤ ∑ x ∈ A₀, τ.w x := by
    simpa [A₀, tupleMass, eventInd, Finset.sum_filter,
      mul_ite, mul_zero, mul_one] using hzsMass
  have hA₀pos : 0 < ∑ x ∈ A₀, τ.w x := lt_of_lt_of_le (by
    dsimp [lower]
    positivity) hA₀mass
  have hA₀active : ∀ x ∈ A₀, Active x := by
    intro x hx
    exact hAactive x ((Finset.mem_filter.mp hx).2.1)
  have hMeanA₀ := hMean A₀ hA₀pos hA₀mass hA₀active
  have hA₀nonempty : A₀.Nonempty := by
    apply Finset.card_pos.mp
    by_contra hcard
    have hcard0 : A₀.card = 0 := Nat.eq_zero_of_not_pos hcard
    have hempty : A₀ = ∅ := Finset.card_eq_zero.mp hcard0
    have hmass0 : ∑ x ∈ A₀, τ.w x = 0 := by simp [hempty]
    have hlowerpos : 0 < lower := by dsimp [lower, r]; positivity
    rw [hmass0] at hA₀mass
    linarith
  obtain ⟨x₀, hx₀⟩ := hA₀nonempty
  have hGoodZs : Good zs := ((Finset.mem_filter.mp hx₀).2).2.1
  have hprojLower : (t : ℝ) * δ ≤
      s * (∑ y, ν.w y *
        (∑ x, (τ.restrict A₀ hA₀pos).w x * g x y) * (∑ i, g (zs i) y)) := by
    have hpointproj (x : Fin N) (hx : x ∈ A₀) :
        (t : ℝ) * δ ≤ s *
          (∑ y, ν.w y * g x y * (∑ i, g (zs i) y)) := by
      have hevent : eventRel zs x := (Finset.mem_filter.mp hx).2
      have hrel (i : Fin t) : δ < s * K x (zs i) := hevent.2.2 i
      have hsum : (t : ℝ) * δ < s * ∑ i, K x (zs i) := by
        have htn : (Finset.univ : Finset (Fin t)).Nonempty :=
          ⟨⟨0, ht⟩, Finset.mem_univ _⟩
        have hsum' : (∑ i : Fin t, δ) < ∑ i, s * K x (zs i) :=
          Finset.sum_lt_sum_of_nonempty htn (fun i hi => hrel i)
        calc
          (t : ℝ) * δ = ∑ i : Fin t, δ := by simp
          _ < ∑ i, s * K x (zs i) := hsum'
          _ = s * ∑ i, K x (zs i) := by rw [← Finset.mul_sum]
      have hrepr : ∑ i, K x (zs i) =
          ∑ y, ν.w y * g x y * (∑ i, g (zs i) y) := by
        simp_rw [K]
        rw [Finset.sum_comm]
        apply Finset.sum_congr rfl
        intro y hy
        rw [Finset.mul_sum]
      rw [hrepr] at hsum
      exact le_of_lt hsum
    have haverage' : (t : ℝ) * δ ≤
        s * (∑ y, ν.w y *
          (∑ x, (τ.restrict A₀ hA₀pos).w x * g x y) * (∑ i, g (zs i) y)) := by
      let μ : Law N := τ.restrict A₀ hA₀pos
      have hpointall (x : Fin N) :
          (t : ℝ) * δ * μ.w x ≤ μ.w x *
            (s * ∑ y, ν.w y * g x y * (∑ i, g (zs i) y)) := by
        by_cases hx : x ∈ A₀
        · have hp := hpointproj x hx
          calc
            (t : ℝ) * δ * μ.w x = μ.w x * ((t : ℝ) * δ) := by ring
            _ ≤ μ.w x *
                (s * ∑ y, ν.w y * g x y * (∑ i, g (zs i) y)) :=
              mul_le_mul_of_nonneg_left hp (μ.nonneg x)
        · have hnotEvent : ¬ eventRel zs x := by
            intro he
            exact hx (Finset.mem_filter.mpr ⟨Finset.mem_univ _, he⟩)
          have hzero : μ.w x = 0 := by
            simp [μ, Law.restrict, A₀, hnotEvent]
          simp [hzero]
      have hsum := Finset.sum_le_sum (s := Finset.univ) (fun x hx => hpointall x)
      have hleft : ∑ x, (t : ℝ) * δ * μ.w x = (t : ℝ) * δ := by
        rw [← Finset.mul_sum, μ.sum_eq_one]
        ring
      have hfactor (y : Fin N) :
          (∑ x, μ.w x * (ν.w y * g x y * (∑ i, g (zs i) y))) =
            ν.w y * (∑ x, μ.w x * g x y) * (∑ i, g (zs i) y) := by
        calc
          ∑ x, μ.w x * (ν.w y * g x y * (∑ i, g (zs i) y)) =
              ∑ x, ν.w y * (μ.w x * g x y * (∑ i, g (zs i) y)) := by
            apply Finset.sum_congr rfl
            intro x hx
            ring
          _ = ν.w y * ∑ x, μ.w x * g x y * (∑ i, g (zs i) y) := by
            rw [← Finset.mul_sum]
          _ = ν.w y * ((∑ x, μ.w x * g x y) * (∑ i, g (zs i) y)) := by
            apply congrArg (fun v : ℝ => ν.w y * v)
            rw [Finset.sum_mul]
          _ = ν.w y * (∑ x, μ.w x * g x y) * (∑ i, g (zs i) y) := by ring
      have hright : ∑ x, μ.w x *
          (∑ y, ν.w y * g x y * (∑ i, g (zs i) y)) =
          ∑ y, ν.w y * (∑ x, μ.w x * g x y) * (∑ i, g (zs i) y) := by
        calc
          ∑ x, μ.w x * (∑ y, ν.w y * g x y * (∑ i, g (zs i) y)) =
              ∑ x, ∑ y, μ.w x * (ν.w y * g x y * (∑ i, g (zs i) y)) := by
            apply Finset.sum_congr rfl
            intro x hx
            rw [Finset.mul_sum]
          _ = ∑ y, ∑ x, μ.w x *
              (ν.w y * g x y * (∑ i, g (zs i) y)) := by
            rw [Finset.sum_comm]
          _ = ∑ y, ν.w y * (∑ x, μ.w x * g x y) *
              (∑ i, g (zs i) y) := by
            apply Finset.sum_congr rfl
            intro y hy
            exact hfactor y
      have hscaleSum : ∑ x, μ.w x *
          (s * ∑ y, ν.w y * g x y * (∑ i, g (zs i) y)) =
          s * ∑ x, μ.w x *
            (∑ y, ν.w y * g x y * (∑ i, g (zs i) y)) := by
        calc
          ∑ x, μ.w x * (s *
              ∑ y, ν.w y * g x y * (∑ i, g (zs i) y)) =
              ∑ x, s * (μ.w x *
                ∑ y, ν.w y * g x y * (∑ i, g (zs i) y)) := by
            apply Finset.sum_congr rfl
            intro x hx
            ring
          _ = s * ∑ x, μ.w x *
              ∑ y, ν.w y * g x y * (∑ i, g (zs i) y) := by
            rw [← Finset.mul_sum]
      calc
        (t : ℝ) * δ = ∑ x, (t : ℝ) * δ * μ.w x := hleft.symm
        _ ≤ ∑ x, μ.w x *
            (s * ∑ y, ν.w y * g x y * (∑ i, g (zs i) y)) := hsum
        _ = s * ∑ x, μ.w x *
            (∑ y, ν.w y * g x y * (∑ i, g (zs i) y)) := hscaleSum
        _ = s * (∑ y, ν.w y * (∑ x, μ.w x * g x y) *
            (∑ i, g (zs i) y)) := by rw [hright]
    exact haverage'
  let μ : Law N := τ.restrict A₀ hA₀pos
  let m (y : Fin N) : ℝ := ∑ x, μ.w x * g x y
  let S (y : Fin N) : ℝ := ∑ i, g (zs i) y
  have hInner :
      ∑ y, ν.w y * m y * S y =
        ∑ y, ν.w y * (∑ x, μ.w x * g x y) * (∑ i, g (zs i) y) := by
    simp [m, S]
  have hMeanBound : ∑ y, ν.w y * m y ^ 2 ≤ eps ^ 2 := by
    simpa [μ, m] using hMeanA₀
  have hSBound : ∑ y, ν.w y * S y ^ 2 ≤ 4 * (t : ℝ) * B ^ 2 := by
    simpa [S, Good] using hGoodZs
  have hCS : (∑ y, ν.w y * m y * S y) ^ 2 ≤
      (∑ y, ν.w y * m y ^ 2) * (∑ y, ν.w y * S y ^ 2) := by
    let f (y : Fin N) := Real.sqrt (ν.w y) * m y
    let q (y : Fin N) := Real.sqrt (ν.w y) * S y
    have h := Finset.sum_mul_sq_le_sq_mul_sq Finset.univ f q
    have hleft : ∑ y, f y * q y = ∑ y, ν.w y * m y * S y := by
      apply Finset.sum_congr rfl
      intro y hy
      dsimp [f, q]
      calc
        Real.sqrt (ν.w y) * m y * (Real.sqrt (ν.w y) * S y) =
            (Real.sqrt (ν.w y)) ^ 2 * m y * S y := by ring
        _ = ν.w y * m y * S y := by rw [Real.sq_sqrt (ν.nonneg y)]
    have hf : ∑ y, f y ^ 2 = ∑ y, ν.w y * m y ^ 2 := by
      apply Finset.sum_congr rfl
      intro y hy
      dsimp [f]
      rw [mul_pow, Real.sq_sqrt (ν.nonneg y)]
    have hq : ∑ y, q y ^ 2 = ∑ y, ν.w y * S y ^ 2 := by
      apply Finset.sum_congr rfl
      intro y hy
      dsimp [q]
      rw [mul_pow, Real.sq_sqrt (ν.nonneg y)]
    rw [hleft, hf, hq] at h
    exact h
  have hsquare : (∑ y, ν.w y * m y * S y) ^ 2 ≤
      (2 * eps * B * Real.sqrt (t : ℝ)) ^ 2 := by
    calc
      (∑ y, ν.w y * m y * S y) ^ 2 ≤ eps ^ 2 * (4 * (t : ℝ) * B ^ 2) :=
        hCS.trans (mul_le_mul hMeanBound hSBound
          (Finset.sum_nonneg fun y hy => mul_nonneg (ν.nonneg y) (sq_nonneg (S y)))
          (by positivity))
      _ = (2 * eps * B * Real.sqrt (t : ℝ)) ^ 2 := by
        have hsqrtSq : (Real.sqrt (t : ℝ)) ^ 2 = (t : ℝ) :=
          Real.sq_sqrt (Nat.cast_nonneg t)
        calc
          eps ^ 2 * (4 * (t : ℝ) * B ^ 2) =
              eps ^ 2 * (4 * (Real.sqrt (t : ℝ)) ^ 2 * B ^ 2) := by rw [hsqrtSq]
          _ = (2 * eps * B * Real.sqrt (t : ℝ)) ^ 2 := by ring
  have hbound : |∑ y, ν.w y * m y * S y| ≤
      2 * eps * B * Real.sqrt (t : ℝ) := by
    have hnonneg : 0 ≤ 2 * eps * B * Real.sqrt (t : ℝ) := by positivity
    have habsSq : |∑ y, ν.w y * m y * S y| ^ 2 =
        (∑ y, ν.w y * m y * S y) ^ 2 := sq_abs _
    nlinarith [hsquare, habsSq, sq_nonneg
      (|∑ y, ν.w y * m y * S y| - 2 * eps * B * Real.sqrt (t : ℝ))]
  have hsignAbs : s * (∑ y, ν.w y * m y * S y) ≤
      |∑ y, ν.w y * m y * S y| := by
    rcases hs with hs | hs
    · simpa [hs] using (le_abs_self (∑ y, ν.w y * m y * S y))
    · simpa [hs, abs_neg] using
        (le_abs_self (-(∑ y, ν.w y * m y * S y)))
  have hfinal : (t : ℝ) * δ ≤ |∑ y, ν.w y * m y * S y| := by
    exact hprojLower.trans (by simpa [hInner] using hsignAbs)
  have hupper : (t : ℝ) * δ ≤ 2 * eps * B * Real.sqrt (t : ℝ) :=
    hfinal.trans hbound
  exact (not_le_of_gt hcontr) hupper

theorem pair_tail_from_mean {N : ℕ}
    (τ ν : Law N) (g : Fin N → Fin N → ℝ)
    (δ p eps B : ℝ) (t : ℕ)
    (Active : Fin N → Prop)
    (hzero : ∀ x, ¬ Active x → ∀ y, g x y = 0)
    (hδ : 0 < δ) (hp : 0 < p) (hp1 : p ≤ 1)
    (hB : 0 < B) (hBbound : ∀ x y, |g x y| ≤ B)
    (heps : 0 ≤ eps) (hsample : (t : ℝ) * eps ^ 2 ≤ B ^ 2)
    (ht : 0 < t)
    (hcontr : (t : ℝ) * δ > 2 * eps * B * Real.sqrt (t : ℝ))
    (hKsym : ∀ x z,
      (∑ y, ν.w y * g x y * g z y) =
        (∑ y, ν.w y * g z y * g x y))
    (hMean : ∀ (A : Finset (Fin N)) (hA : 0 < ∑ x ∈ A, τ.w x),
      (p / 4) ^ (t + 1) / 2 ≤ ∑ x ∈ A, τ.w x →
      (∀ x ∈ A, Active x) →
      ∑ y, ν.w y *
        (∑ x, (τ.restrict A hA).w x * g x y) ^ 2 ≤ eps ^ 2) :
    ∑ x, ∑ z, (if δ < |∑ y, ν.w y * g x y * g z y|
      then τ.w x * τ.w z else 0) ≤ p := by
  classical
  let K (x z : Fin N) : ℝ := ∑ y, ν.w y * g x y * g z y
  let Pmass : ℝ := ∑ x, ∑ z,
    (if δ < K x z then τ.w x * τ.w z else 0)
  let Nmass : ℝ := ∑ x, ∑ z,
    (if δ < -K x z then τ.w x * τ.w z else 0)
  have hsplitTerm (x z : Fin N) :
      (if δ < |K x z| then τ.w x * τ.w z else 0) =
        (if δ < K x z then τ.w x * τ.w z else 0) +
        (if δ < -K x z then τ.w x * τ.w z else 0) := by
    by_cases hk : 0 ≤ K x z
    · rw [abs_of_nonneg hk]
      by_cases hh : δ < K x z
      · have hneg : ¬ δ < -K x z := by linarith
        simp [hh, hneg]
      · have hpos : ¬ δ < |K x z| := by simpa [abs_of_nonneg hk] using hh
        simp [hh, hpos]
        have hneg : ¬ δ < -K x z := by linarith
        simp [hneg]
    · have hk' : K x z < 0 := lt_of_not_ge hk
      rw [abs_of_neg hk']
      by_cases hh : δ < -K x z
      · have hpos : ¬ δ < K x z := by linarith
        simp [hh, hpos]
      · have hneg : ¬ δ < |K x z| := by simpa [abs_of_neg hk'] using hh
        simp [hh, hneg]
        have hpos : ¬ δ < K x z := by linarith
        simp [hpos]
  have hsplit :
      (∑ x, ∑ z, (if δ < |K x z| then τ.w x * τ.w z else 0)) =
        Pmass + Nmass := by
    simp_rw [hsplitTerm, Finset.sum_add_distrib]
    rfl
  by_contra hnot
  have hbad : p < ∑ x, ∑ z,
      (if δ < |K x z| then τ.w x * τ.w z else 0) := by
    exact lt_of_not_ge (by simpa [K] using hnot)
  rw [hsplit] at hbad
  have hplus : p / 2 < Pmass ∨ p / 2 < Nmass := by
    by_contra hh
    push_neg at hh
    linarith
  rcases hplus with hplus | hminus
  · exact False.elim (signed_pair_tail_impossible τ ν g δ p eps B t Active hzero
      hδ hp hp1 hB hBbound heps hsample ht hcontr hKsym hMean 1 (Or.inl rfl) (by
        simpa [Pmass, K] using hplus))
  · exact False.elim (signed_pair_tail_impossible τ ν g δ p eps B t Active hzero
      hδ hp hp1 hB hBbound heps hsample ht hcontr hKsym hMean (-1) (Or.inr rfl) (by
        simpa [Nmass, K] using hminus))

private theorem corr_tail_two_at_k {N : ℕ} (n xs α : ℝ) (hn : 1 ≤ n)
    (τ ν : Law N) (E : Fin N → Fin N → Prop) (c : Colour)
    (hCost : ∀ (A : Finset (Fin N)) (hA : 0 < ∑ x ∈ A, τ.w x),
      (Real.exp (-n ^ (0.4 : ℝ)) / 4) ^
        (Nat.ceil (n ^ (0.25 : ℝ)) + 1) / 2 ≤ ∑ x ∈ A, τ.w x →
      n ^ (xs / 4) - Real.log (∑ x ∈ A, τ.w x) ≤ α * n)
    (hMeanData : ∀ (A : Finset (Fin N))
      (hA : 0 < ∑ x ∈ A, τ.w x),
      n ^ (xs / 4) - Real.log (∑ x ∈ A, τ.w x) ≤ α * n →
      ∑ y, ν.w y *
        (∑ x, (τ.restrict A hA).w x * fv E c x y) ^ 2 ≤
          (3 * n ^ (-0.96 : ℝ)) ^ 2)
    (ht : 0 < Nat.ceil (n ^ (0.25 : ℝ)))
    (hsample : (Nat.ceil (n ^ (0.25 : ℝ)) : ℝ) *
      (3 * n ^ (-0.96 : ℝ)) ^ 2 ≤ 1)
    (hcontr : (Nat.ceil (n ^ (0.25 : ℝ)) : ℝ) * n ^ (-1.03 : ℝ) >
      6 * n ^ (-0.96 : ℝ) * Real.sqrt (Nat.ceil (n ^ (0.25 : ℝ)) : ℝ))
    (hE : ∀ x y, |fv E c x y| ≤ 1) :
    ∑ x, ∑ z,
      (if n ^ (-1.03 : ℝ) < |corr E c ν.w x z|
        then τ.w x * τ.w z else 0) ≤ Real.exp (-n ^ (0.4 : ℝ)) := by
  let p := Real.exp (-n ^ (0.4 : ℝ))
  let δ := n ^ (-1.03 : ℝ)
  let t := Nat.ceil (n ^ (0.25 : ℝ))
  let eps := 3 * n ^ (-0.96 : ℝ)
  have hp : 0 < p := by dsimp [p]; positivity
  have hp1 : p ≤ 1 := by
    dsimp [p]
    apply Real.exp_le_one_iff.mpr
    exact neg_nonpos.mpr (Real.rpow_nonneg (by linarith) _)
  have hδ : 0 < δ := by dsimp [δ]; exact Real.rpow_pos_of_pos (by linarith) _
  have heps : 0 ≤ eps := by dsimp [eps]; positivity
  have hKsym (x z : Fin N) :
      (∑ y, ν.w y * fv (N := N) E c x y * fv (N := N) E c z y) =
        (∑ y, ν.w y * fv (N := N) E c z y * fv (N := N) E c x y) := by
    apply Finset.sum_congr rfl
    intro y hy
    ring
  have hMean : ∀ (A : Finset (Fin N)) (hA : 0 < ∑ x ∈ A, τ.w x),
      (p / 4) ^ (t + 1) / 2 ≤ ∑ x ∈ A, τ.w x →
      (∀ x ∈ A, True) →
      ∑ y, ν.w y *
        (∑ x, (τ.restrict A hA).w x * fv E c x y) ^ 2 ≤ eps ^ 2 := by
    intro A hA hm hactive
    have hcost := hCost A hA (by simpa [p, t] using hm)
    have h := hMeanData A hA hcost
    simpa [eps] using h
  have htail := pair_tail_from_mean τ ν (fv E c) δ p eps 1 t
    (fun _ => True) (by intro x hx y; exact (hx trivial).elim) hδ hp hp1
    (by norm_num) hE heps (by simpa [t, eps] using hsample) ht
    (by convert hcontr using 1 <;> ring) hKsym hMean
  change (∑ x, ∑ z,
    (if n ^ (-1.03 : ℝ) <
      |∑ y, ν.w y * fv E c x y * fv E c z y|
     then τ.w x * τ.w z else 0)) ≤ Real.exp (-n ^ (0.4 : ℝ))
  simpa [δ, p] using htail

private theorem inter_second_moment_identity {N u : ℕ}
    (E : Fin N → Fin N → Prop) (c : Colour) (τ : Law N)
    (π : Fin N → ℝ) (J : Finset (Fin u)) :
    ∑ xs : Fin u → Fin N, prodW τ.w xs *
      (inter E c π J xs) ^ 2 =
    ∑ y, ∑ y', π y * π y' *
      (∑ x, τ.w x * acoef E c π x y * acoef E c π x y') ^ J.card := by
  classical
  have hpoint (xs : Fin u → Fin N) :
      (inter E c π J xs) ^ 2 =
        ∑ y, ∑ y', π y * π y' *
          ∏ i ∈ J, (acoef E c π (xs i) y * acoef E c π (xs i) y') := by
    unfold inter
    rw [pow_two, Fintype.sum_mul_sum]
    apply Finset.sum_congr rfl
    intro y hy
    apply Finset.sum_congr rfl
    intro y' hy'
    rw [Finset.prod_mul_distrib]
    ring
  calc
    ∑ xs : Fin u → Fin N, prodW τ.w xs *
        (inter E c π J xs) ^ 2 =
      ∑ xs : Fin u → Fin N, ∑ y, ∑ y',
        π y * π y' * (prodW τ.w xs *
          ∏ i ∈ J, (acoef E c π (xs i) y * acoef E c π (xs i) y')) := by
      apply Finset.sum_congr rfl
      intro xs hxs
      rw [hpoint]
      simp_rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro y hy
      apply Finset.sum_congr rfl
      intro y' hy'
      ring
    _ = ∑ y, ∑ y', ∑ xs : Fin u → Fin N,
        π y * π y' * (prodW τ.w xs *
          ∏ i ∈ J, (acoef E c π (xs i) y * acoef E c π (xs i) y')) := by
      rw [Finset.sum_comm]
      congr 1
      ext y
      rw [Finset.sum_comm]
    _ = ∑ y, ∑ y', π y * π y' *
        (∑ xs : Fin u → Fin N, prodW τ.w xs *
          ∏ i ∈ J, (acoef E c π (xs i) y * acoef E c π (xs i) y')) := by
      apply Finset.sum_congr rfl
      intro y hy
      apply Finset.sum_congr rfl
      intro y' hy'
      rw [← Finset.mul_sum]
    _ = ∑ y, ∑ y', π y * π y' *
        (∑ x, τ.w x * acoef E c π x y * acoef E c π x y') ^ J.card := by
      apply Finset.sum_congr rfl
      intro y hy
      apply Finset.sum_congr rfl
      intro y' hy'
      simpa [mul_assoc] using congrArg (fun r : ℝ => π y * π y' * r)
        (iid_prod_factorization τ J
          (fun x => acoef E c π x y * acoef E c π x y'))

theorem inter_tail_one_at_k (κ : CConsts) (hκ : κ.Admissible) (T : Stage)
    (k : ℕ) (hD : TwoBudgetDisc T k ((T.S.n k : ℝ) ^ κ.xs)
      (κ.α * T.S.n k) (bstar T k)) (hn : 1 ≤ (T.S.n k : ℝ))
    (hgap : (T.S.n k : ℝ) ^ (κ.xs / 4) ≤ (T.S.n k : ℝ) ^ κ.xs / 2)
    (hwidth : (T.S.n k : ℝ) ^ (κ.xs / 4) ≤ κ.α * T.S.n k / 3)
    (hexp : 4 ≤ Real.exp (κ.α * T.S.n k / 3))
    (hlarge : 6 ≤ (T.S.n k : ℝ) ^ κ.xs)
    (c : Colour) (u : ℕ) (C0 : ℝ) (hC0 : 1 ≤ C0)
    (hgateScale : C0 * bstar T k ≤ 1 / 6) :
    ∀ (S : InterSetting T k (κ.xs / 4)) (l : Fin S.d)
      (J : Finset (Fin u)) (i₀ : Fin u),
      i₀ ∈ J → 2 ≤ J.card →
      ∀ xs : Fin u → Fin (T.S.N k),
        (∀ i ∈ J, i ≠ i₀ →
          DegGate (T.S.E k) c (S.π l).w C0 (bstar T k) (xs i)) →
        ∑ z ∈ Finset.univ.filter (fun z =>
          DegGate (T.S.E k) c (S.π l).w C0 (bstar T k) z ∧
          100 * 3 ^ u * C0 * bstar T k <
            |inter (T.S.E k) c (S.π l).w J (Function.update xs i₀ z)|),
          S.τ.w z ≤ Real.exp (-(κ.α * T.S.n k / 3)) := by
  classical
  intro S l J i₀ hi₀ hJ xs hothers
  let π := (S.π l).w
  let D := deg (T.S.E k) c π
  let P : ℝ := 3 ^ u
  let H : Fin (T.S.N k) → ℝ := fun y =>
    ∏ i ∈ J.erase i₀, acoef (T.S.E k) c π (xs i) y
  have hnpos : 0 < (T.S.n k : ℝ) := by linarith
  have hbstar : 0 < bstar T k := by
    exact Real.rpow_pos_of_pos hnpos _
  have hDlo (z : Fin (T.S.N k))
      (hz : DegGate (T.S.E k) c π C0 (bstar T k) z) :
      (1 / 3 : ℝ) ≤ D z := by
    change |D z - 1 / 2| ≤ C0 * bstar T k at hz
    rw [abs_le] at hz
    dsimp [D]
    nlinarith
  have hfactor (i : Fin u) (hi : i ∈ J.erase i₀) (y : Fin (T.S.N k)) :
      |acoef (T.S.E k) c π (xs i) y| ≤ 3 := by
    have hmem := Finset.mem_erase.mp hi
    have hgi := hothers i hmem.2 hmem.1
    exact acoef_abs_le_three_of_degree (T.S.E k) c π (xs i) y (hDlo (xs i) hgi)
  have hcard : (J.erase i₀).card ≤ u := by
    exact (Finset.card_le_card (Finset.erase_subset _ _)).trans
      (by simpa using (Finset.card_le_univ J))
  have hHbound (y : Fin (T.S.N k)) : |H y| ≤ P := by
    dsimp [H, P]
    rw [Finset.abs_prod]
    calc
      (∏ i ∈ J.erase i₀, |acoef (T.S.E k) c π (xs i) y|) ≤
          (3 : ℝ) ^ (J.erase i₀).card := by
        calc
          (∏ i ∈ J.erase i₀, |acoef (T.S.E k) c π (xs i) y|) ≤
              ∏ i ∈ J.erase i₀, (3 : ℝ) :=
            Finset.prod_le_prod₀
              (by intro i hi; exact abs_nonneg _)
              (by intro i hi; exact hfactor i hi y)
          _ = (3 : ℝ) ^ (J.erase i₀).card := by simp
      _ ≤ (3 : ℝ) ^ u := pow_le_pow_right₀ (by norm_num) hcard
  have hPpos : 0 < P := by dsimp [P]; positivity
  let f : Fin (T.S.N k) → ℝ := fun y => H y / P
  have hf : ∀ y, |f y| ≤ 1 := by
    intro y
    dsimp [f]
    rw [abs_div, abs_of_pos hPpos]
    exact (div_le_iff₀ hPpos).2 (by simpa using hHbound y)
  have hpiSignedWidth : (S.π l).WidthLE
      ((T.S.n k : ℝ) ^ κ.xs / 2 + Real.log 3 - Real.log 3) := by
    have hwidthEq : (T.S.n k : ℝ) ^ κ.xs / 2 + Real.log 3 - Real.log 3 =
        (T.S.n k : ℝ) ^ κ.xs / 2 := by ring
    rw [hwidthEq]
    intro y
    calc
      (S.π l).w y ≤ Real.exp ((T.S.n k : ℝ) ^ (κ.xs / 4)) / T.S.N k :=
        S.π_width l y
      _ ≤ Real.exp ((T.S.n k : ℝ) ^ κ.xs / 2) / T.S.N k :=
        div_le_div_of_nonneg_right (Real.exp_le_exp.mpr hgap) (by positivity)
  have hDz (z : Fin (T.S.N k)) (hz :
      DegGate (T.S.E k) c π C0 (bstar T k) z) : 0 < D z := by
    exact lt_of_lt_of_le (by norm_num : (0 : ℝ) < 1 / 3) (hDlo z hz)
  have hproduct (z : Fin (T.S.N k)) (y : Fin (T.S.N k)) :
      (∏ i ∈ J, acoef (T.S.E k) c π (Function.update xs i₀ z i) y) =
        H y * acoef (T.S.E k) c π z y := by
    rw [← Finset.prod_erase_mul J
      (fun i => acoef (T.S.E k) c π (Function.update xs i₀ z i) y) hi₀]
    congr 1
    · apply Finset.prod_congr rfl
      intro i hi
      rw [Function.update_of_ne (Finset.mem_erase.mp hi).1]
    · simp
  let raw : Fin (T.S.N k) → ℝ := fun z =>
    ∑ y, π y * H y * (hit (T.S.E k) c z y - D z)
  have hinter (z : Fin (T.S.N k)) (hz :
      DegGate (T.S.E k) c π C0 (bstar T k) z) :
      inter (T.S.E k) c π J (Function.update xs i₀ z) = raw z / D z := by
    change (∑ y, π y * ∏ i ∈ J,
      acoef (T.S.E k) c π (Function.update xs i₀ z i) y) = raw z / D z
    conv_rhs => rw [div_eq_mul_inv]
    dsimp [raw]
    rw [Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro y hy
    rw [hproduct]
    have hcoef : acoef (T.S.E k) c π z y =
        (hit (T.S.E k) c z y - D z) / D z := by
      rw [acoef]
      dsimp [D]
      rw [div_eq_mul_inv, div_eq_mul_inv]
      have hcancel :
          deg (T.S.E k) c π z * (deg (T.S.E k) c π z)⁻¹ = 1 :=
        mul_inv_cancel₀ (ne_of_gt (hDz z hz))
      ring_nf
      rw [hcancel]
      ring
    rw [hcoef]
    ring
  let signed : Fin (T.S.N k) → ℝ := fun z =>
    ∑ y, π y * f y * (hit (T.S.E k) c z y - D z)
  have hsigned (z : Fin (T.S.N k)) : signed z = raw z / P := by
    dsimp [signed, raw, f]
    conv_rhs => rw [div_eq_mul_inv]
    rw [Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro y hy
    ring
  have hsigned_inter (z : Fin (T.S.N k)) (hz :
      DegGate (T.S.E k) c π C0 (bstar T k) z) :
      signed z = D z * inter (T.S.E k) c π J (Function.update xs i₀ z) / P := by
    rw [hsigned, hinter z hz]
    field_simp [ne_of_gt (hDz z hz)]
  let badSigned : Finset (Fin (T.S.N k)) := Finset.univ.filter (fun z =>
    6 * bstar T k < |∑ y, π y * f y *
      (hit (T.S.E k) c z y - D z)|)
  have hbad :
      ∑ z ∈ Finset.univ.filter (fun z =>
        DegGate (T.S.E k) c π C0 (bstar T k) z ∧
        100 * P * C0 * bstar T k <
          |inter (T.S.E k) c π J (Function.update xs i₀ z)|),
        S.τ.w z ≤ ∑ z ∈ badSigned, S.τ.w z := by
    apply Finset.sum_le_sum_of_subset_of_nonneg
    · intro z hz
      rcases (Finset.mem_filter.mp hz).2 with ⟨hgz, hlarge⟩
      have hrel := hsigned_inter z hgz
      have hsig : 6 * bstar T k < |signed z| := by
        rw [hrel, abs_div, abs_mul, abs_of_pos (hDz z hgz), abs_of_pos hPpos]
        have hbC : bstar T k ≤ C0 * bstar T k := by
          calc
            bstar T k = 1 * bstar T k := by ring
            _ ≤ C0 * bstar T k := mul_le_mul_of_nonneg_right hC0 hbstar.le
        have hPmul : P * bstar T k ≤ P * C0 * bstar T k := by
          calc
            P * bstar T k ≤ P * (C0 * bstar T k) :=
              mul_le_mul_of_nonneg_left hbC (le_of_lt hPpos)
            _ = P * C0 * bstar T k := by ring
        have hlow : 6 * bstar T k * P ≤
            D z * (100 * P * C0 * bstar T k) := by
          have hfactorNonneg : 0 ≤ 100 * P * C0 * bstar T k := by
            have hC0nonneg : 0 ≤ C0 := le_trans (by norm_num) hC0
            exact mul_nonneg
              (mul_nonneg (mul_nonneg (by norm_num) hPpos.le) hC0nonneg) hbstar.le
          have hDstep := mul_le_mul_of_nonneg_right (hDlo z hgz) hfactorNonneg
          have hstep₁ : (100 / 3 : ℝ) * (P * C0 * bstar T k) ≤
              D z * (100 * P * C0 * bstar T k) := by
            nlinarith [hDstep]
          have hPfactorNonneg : 0 ≤ P * C0 * bstar T k := by positivity
          have hstep₂ : 6 * bstar T k * P ≤
              (100 / 3 : ℝ) * (P * C0 * bstar T k) := by
            calc
              6 * bstar T k * P ≤ 6 * (P * C0 * bstar T k) := by nlinarith [hPmul]
              _ ≤ (100 / 3 : ℝ) * (P * C0 * bstar T k) :=
                mul_le_mul_of_nonneg_right (by norm_num) hPfactorNonneg
          exact hstep₂.trans hstep₁
        have hlarge' : D z * (100 * P * C0 * bstar T k) <
            D z * |inter (T.S.E k) c π J (Function.update xs i₀ z)| :=
          mul_lt_mul_of_pos_left hlarge (hDz z hgz)
        have hmul : 6 * bstar T k * P <
            D z * |inter (T.S.E k) c π J (Function.update xs i₀ z)| :=
          hlow.trans_lt hlarge'
        exact (lt_div_iff₀ hPpos).2 (by simpa [mul_comm, mul_left_comm, mul_assoc] using hmul)
      simpa [signed, badSigned] using hsig
    · intro z hz _
      exact S.τ.nonneg z
  have hmass := exceptional_signed hD c
    (w₁ := (T.S.n k : ℝ) ^ κ.xs / 2 + Real.log 3)
    (W₂ := κ.α * T.S.n k) (w := (T.S.n k : ℝ) ^ (κ.xs / 4))
    (Or.inl ⟨by
      have hlog3 : Real.log 3 ≤ 2 := by
        have hh := Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 3)
        linarith
      linarith, le_rfl⟩)
    (S.π l) (S.π_supp l) hpiSignedWidth
    S.τ S.τ_supp (S.τ_width) f hf
  have hfinal : 4 * Real.exp ((T.S.n k : ℝ) ^ (κ.xs / 4) - κ.α * T.S.n k) ≤
      Real.exp (-(κ.α * T.S.n k / 3)) := by
    have hwidth' : (T.S.n k : ℝ) ^ (κ.xs / 4) - κ.α * T.S.n k ≤
        -2 * (κ.α * T.S.n k / 3) := by linarith
    have hmono := Real.exp_le_exp.mpr hwidth'
    calc
      4 * Real.exp ((T.S.n k : ℝ) ^ (κ.xs / 4) - κ.α * T.S.n k) ≤
          4 * Real.exp (-2 * (κ.α * T.S.n k / 3)) :=
        mul_le_mul_of_nonneg_left hmono (by norm_num)
      _ ≤ Real.exp (-(κ.α * T.S.n k / 3)) := by
        have hexpEq : Real.exp (κ.α * T.S.n k / 3) *
            Real.exp (-2 * (κ.α * T.S.n k / 3)) =
            Real.exp (-(κ.α * T.S.n k / 3)) := by
          rw [← Real.exp_add]
          congr 1
          ring
        calc
          4 * Real.exp (-2 * (κ.α * T.S.n k / 3)) ≤
              Real.exp (κ.α * T.S.n k / 3) *
                Real.exp (-2 * (κ.α * T.S.n k / 3)) :=
            mul_le_mul_of_nonneg_right
              (by linarith : (4 : ℝ) ≤ Real.exp (κ.α * T.S.n k / 3))
              (Real.exp_pos _).le
          _ = Real.exp (-(κ.α * T.S.n k / 3)) := hexpEq
  calc
    ∑ z ∈ Finset.univ.filter (fun z =>
      DegGate (T.S.E k) c π C0 (bstar T k) z ∧
      100 * P * C0 * bstar T k <
        |inter (T.S.E k) c π J (Function.update xs i₀ z)|), S.τ.w z ≤
        ∑ z ∈ badSigned, S.τ.w z := hbad
    _ ≤ 4 * Real.exp ((T.S.n k : ℝ) ^ (κ.xs / 4) - κ.α * T.S.n k) := by
      simpa [badSigned] using hmass
    _ ≤ Real.exp (-(κ.α * T.S.n k / 3)) := hfinal

theorem prove_inter_tail_one (κ : CConsts) (hκ : κ.Admissible) (T : Stage)
    (hDeep : DeepDisc T κ.xs κ.α 0.04) (c : Colour) (u : ℕ)
    (C0 : ℝ) (hC0 : 1 ≤ C0) :
    ∀ᶠ k in atTop,
      ∀ (S : InterSetting T k (κ.xs / 4)) (l : Fin S.d)
        (J : Finset (Fin u)) (i₀ : Fin u),
        i₀ ∈ J → 2 ≤ J.card →
        ∀ xs : Fin u → Fin (T.S.N k),
          (∀ i ∈ J, i ≠ i₀ →
            DegGate (T.S.E k) c (S.π l).w C0 (bstar T k) (xs i)) →
          ∑ z ∈ Finset.univ.filter (fun z =>
            DegGate (T.S.E k) c (S.π l).w C0 (bstar T k) z ∧
            100 * 3 ^ u * C0 * bstar T k <
              |inter (T.S.E k) c (S.π l).w J (Function.update xs i₀ z)|),
            S.τ.w z ≤ Real.exp (-(κ.α * T.S.n k / 3)) := by
  have hx : 0 < κ.xs := hκ.xs_rng.1
  have hα : 0 < κ.α := hκ.α_rng.1
  have hp : κ.xs / 4 < κ.xs := by linarith
  have hgap := eventually_rpow_le_mul T hp (by norm_num : (0 : ℝ) < 1 / 2)
  have hlarge := eventually_rpow_ge T (q := κ.xs) (C := 6) hx
  have hpLinear : κ.xs / 4 < 1 := by nlinarith [hκ.xs_rng.2]
  have hwidth := eventually_rpow_le_mul T hpLinear (by positivity : 0 < κ.α / 3)
  have hexp := eventually_exp_linear_ge T (a := κ.α / 3) (C := 4) (by positivity)
  have hn : ∀ᶠ k in atTop, 1 ≤ (T.S.n k : ℝ) := by
    exact (tendsto_natCast_atTop_atTop.comp T.S.n_tendsto).eventually
      (eventually_ge_atTop (1 : ℝ))
  have hscale : ∀ᶠ k in atTop, C0 * bstar T k ≤ 1 / 6 := by
    have hpNeg : (-1 + (0.04 : ℝ)) < 0 := by norm_num
    have hs := eventually_rpow_le_mul T (p := -1 + (0.04 : ℝ))
      (q := 0) (c := 1 / (6 * C0)) hpNeg (by positivity)
    filter_upwards [hs, hn] with k hs hk
    have hnpos : 0 < (T.S.n k : ℝ) := by linarith
    have hmul := mul_le_mul_of_nonneg_left hs (by linarith : 0 ≤ C0)
    have hpow : (T.S.n k : ℝ) ^ (-1 + (0.04 : ℝ)) = bstar T k := rfl
    rw [Real.rpow_zero, hpow] at hmul
    have hmul' : C0 * bstar T k ≤ C0 * (1 / (6 * C0)) := by
      simpa [hpow] using hmul
    calc
      C0 * bstar T k ≤ C0 * (1 / (6 * C0)) := hmul'
      _ = 1 / 6 := by field_simp [ne_of_gt (by linarith : 0 < C0)]
  filter_upwards [hDeep, hgap, hlarge, hwidth, hexp, hn, hscale]
    with k hD hgap hlarge hwidth hexp hn hscale
  have hgap' : (T.S.n k : ℝ) ^ (κ.xs / 4) ≤
      (T.S.n k : ℝ) ^ κ.xs / 2 := by
    convert hgap using 1 <;> ring
  have hwidth' : (T.S.n k : ℝ) ^ (κ.xs / 4) ≤
      κ.α * T.S.n k / 3 := by
    rw [Real.rpow_one] at hwidth
    convert hwidth using 1 <;> ring
  have hexp' : 4 ≤ Real.exp (κ.α * T.S.n k / 3) := by
    convert hexp using 1 <;> ring
  exact inter_tail_one_at_k κ hκ T k hD hn hgap' hwidth' hexp' hlarge
    c u C0 hC0 hscale

theorem corr_tail_one_at_k (κ : CConsts) (hκ : κ.Admissible) (T : Stage)
    (k : ℕ) (hD : TwoBudgetDisc T k ((T.S.n k : ℝ) ^ κ.xs)
      (κ.α * T.S.n k) (bstar T k)) (hn : 1 ≤ (T.S.n k : ℝ))
    (hgap : (T.S.n k : ℝ) ^ (κ.xs / 4) ≤ (T.S.n k : ℝ) ^ κ.xs / 2)
    (hwidth : (T.S.n k : ℝ) ^ (κ.xs / 4) ≤ κ.α * T.S.n k / 3)
    (hexp : 6 ≤ Real.exp (κ.α * T.S.n k / 3))
    (hlarge : 6 ≤ (T.S.n k : ℝ) ^ κ.xs)
    (c : Colour) (u : ℕ) (C0 : ℝ) (hC0 : 1 ≤ C0) :
    ∀ (S : InterSetting T k (κ.xs / 4)) (l : Fin S.d)
      (x : Fin (T.S.N k)),
      ∑ z ∈ Finset.univ.filter (fun z =>
        100 * 3 ^ u * C0 * bstar T k <
          |corr (T.S.E k) c (S.π l).w x z|),
        S.τ.w z ≤ Real.exp (-(κ.α * T.S.n k / 3)) := by
  classical
  intro S l x
  let π := (S.π l).w
  let D := deg (T.S.E k) c π
  let P : ℝ := 3 ^ u
  let m : ℝ := ∑ y, π y * fv (T.S.E k) c x y
  let sig : Fin (T.S.N k) → ℝ := fun z =>
    ∑ y, π y * fv (T.S.E k) c x y *
      (hit (T.S.E k) c z y - D z)
  let SA : Finset (Fin (T.S.N k)) := Finset.univ.filter (fun z =>
    6 * bstar T k < |sig z|)
  let SB : Finset (Fin (T.S.N k)) := Finset.univ.filter (fun z =>
    bstar T k < |D z - 1 / 2|)
  let SC : Finset (Fin (T.S.N k)) := Finset.univ.filter (fun z =>
    100 * P * C0 * bstar T k <
      |corr (T.S.E k) c π x z|)
  have hnpos : 0 < (T.S.n k : ℝ) := by linarith
  have hbstar : 0 < bstar T k := Real.rpow_pos_of_pos hnpos _
  have hPpos : 0 < P := by dsimp [P]; positivity
  have hPge : 1 ≤ P := by
    dsimp [P]
    exact one_le_three_pow u
  have hpc : 1 ≤ P * C0 := by
    calc
      1 ≤ P := hPge
      _ ≤ P * C0 := by
        simpa using mul_le_mul_of_nonneg_left hC0 (le_of_lt hPpos)
  have hcoeff : 14 ≤ 100 * P * C0 := by nlinarith
  have hlog3 : 0 ≤ Real.log 3 ∧ Real.log 3 ≤ 2 := by
    constructor
    · exact Real.log_nonneg (by norm_num)
    · have hh := Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 3)
      linarith
  let w₁ := (T.S.n k : ℝ) ^ κ.xs / 2 + Real.log 3
  have hpair : (w₁ ≤ (T.S.n k : ℝ) ^ κ.xs ∧
      κ.α * T.S.n k ≤ κ.α * T.S.n k) ∨
      (w₁ ≤ κ.α * T.S.n k ∧ κ.α * T.S.n k ≤ (T.S.n k : ℝ) ^ κ.xs) := by
    apply Or.inl
    constructor
    · change (T.S.n k : ℝ) ^ κ.xs / 2 + Real.log 3 ≤ (T.S.n k : ℝ) ^ κ.xs
      linarith [hlarge, hlog3.2]
    · rfl
  have hπwSmall : (S.π l).WidthLE ((T.S.n k : ℝ) ^ κ.xs / 2) := by
    intro y
    calc
      π y ≤ Real.exp ((T.S.n k : ℝ) ^ (κ.xs / 4)) / T.S.N k := S.π_width l y
      _ ≤ Real.exp ((T.S.n k : ℝ) ^ κ.xs / 2) / T.S.N k :=
        div_le_div_of_nonneg_right (Real.exp_le_exp.mpr hgap) (by positivity)
  have hπw : (S.π l).WidthLE w₁ := by
    intro y
    calc
      (S.π l).w y ≤ Real.exp ((T.S.n k : ℝ) ^ κ.xs / 2) / T.S.N k := hπwSmall y
      _ ≤ Real.exp w₁ / T.S.N k :=
        div_le_div_of_nonneg_right
          (Real.exp_le_exp.mpr (by dsimp [w₁]; linarith [hlog3.1])) (by positivity)
  have hπSignedWidth : (S.π l).WidthLE (w₁ - Real.log 3) := by
    have heq : w₁ - Real.log 3 = (T.S.n k : ℝ) ^ κ.xs / 2 := by
      dsimp [w₁]
      ring
    rw [heq]
    exact hπwSmall
  have hf : ∀ y, |fv (T.S.E k) c x y| ≤ 1 :=
    fun y => fv_abs_le_one (T.S.E k) c x y
  have hdecomp (z : Fin (T.S.N k)) :
      corr (T.S.E k) c π x z = 2 * sig z + m * (2 * D z - 1) := by
    have hcorr : corr (T.S.E k) c π x z =
        2 * (∑ y, π y * fv (T.S.E k) c x y * hit (T.S.E k) c z y) - m := by
      calc
        corr (T.S.E k) c π x z =
            ∑ y, (2 * (π y * fv (T.S.E k) c x y * hit (T.S.E k) c z y) -
              π y * fv (T.S.E k) c x y) := by
          unfold corr
          apply Finset.sum_congr rfl
          intro y hy
          simp only [fv]
          ring
        _ = (∑ y, 2 * (π y * fv (T.S.E k) c x y * hit (T.S.E k) c z y)) -
            ∑ y, π y * fv (T.S.E k) c x y := by
          rw [Finset.sum_sub_distrib]
        _ = 2 * (∑ y, π y * fv (T.S.E k) c x y * hit (T.S.E k) c z y) - m := by
          rw [← Finset.mul_sum]
    have hsig : sig z =
        (∑ y, π y * fv (T.S.E k) c x y * hit (T.S.E k) c z y) - D z * m := by
      dsimp [sig, m]
      calc
        ∑ y, π y * fv (T.S.E k) c x y *
            (hit (T.S.E k) c z y - D z) =
            ∑ y, (π y * fv (T.S.E k) c x y * hit (T.S.E k) c z y -
              (π y * fv (T.S.E k) c x y) * D z) := by
          apply Finset.sum_congr rfl
          intro y hy
          ring
        _ = (∑ y, π y * fv (T.S.E k) c x y * hit (T.S.E k) c z y) -
            (∑ y, π y * fv (T.S.E k) c x y) * D z := by
          rw [Finset.sum_sub_distrib, ← Finset.sum_mul]
        _ = (∑ y, π y * fv (T.S.E k) c x y * hit (T.S.E k) c z y) - D z * m := by
          dsimp [m]
          ring
    rw [hcorr, hsig]
    ring
  have hm : |m| ≤ 1 := by
    calc
      |∑ y, π y * fv (T.S.E k) c x y| ≤
          ∑ y, |π y * fv (T.S.E k) c x y| := by
            simpa using Finset.abs_sum_le_sum_abs
              (fun y => π y * fv (T.S.E k) c x y) Finset.univ
      _ ≤ ∑ y, π y := by
        apply Finset.sum_le_sum
        intro y hy
        rw [abs_mul, abs_of_nonneg ((S.π l).nonneg y)]
        exact mul_le_of_le_one_right ((S.π l).nonneg y) (hf y)
      _ = 1 := (S.π l).sum_eq_one
  have hsubset : SC ⊆ SA ∪ SB := by
    intro z hz
    rcases Finset.mem_filter.mp hz with ⟨-, hlarge⟩
    by_contra hnot
    have hnotA : z ∉ SA := by
      intro hzA
      exact hnot (Finset.mem_union.mpr (Or.inl hzA))
    have hnotB : z ∉ SB := by
      intro hzB
      exact hnot (Finset.mem_union.mpr (Or.inr hzB))
    have hsig : |sig z| ≤ 6 * bstar T k := by
      exact le_of_not_gt (by simpa [SA] using hnotA)
    have hdeg : |D z - 1 / 2| ≤ bstar T k := by
      exact le_of_not_gt (by simpa [SB] using hnotB)
    have htwice : |2 * D z - 1| ≤ 2 * bstar T k := by
      calc
        |2 * D z - 1| = |2 * (D z - 1 / 2)| := by congr 1 <;> ring
        _ = 2 * |D z - 1 / 2| := by rw [abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 2)]
        _ ≤ 2 * bstar T k := mul_le_mul_of_nonneg_left hdeg (by norm_num)
    have hcorr : |corr (T.S.E k) c π x z| ≤ 14 * bstar T k := by
      rw [hdecomp]
      calc
        |2 * sig z + m * (2 * D z - 1)| ≤
            |2 * sig z| + |m * (2 * D z - 1)| := abs_add_le _ _
        _ = 2 * |sig z| + |m| * |2 * D z - 1| := by
          rw [abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 2), abs_mul]
        _ ≤ 2 * (6 * bstar T k) + 1 * (2 * bstar T k) := by
          exact add_le_add
            (mul_le_mul_of_nonneg_left hsig (by norm_num))
            (mul_le_mul hm htwice (by positivity) (by positivity))
        _ = 14 * bstar T k := by ring
    have hcoeff' : 14 * bstar T k ≤ 100 * P * C0 * bstar T k := by
      calc
        14 * bstar T k ≤ (100 * P * C0) * bstar T k :=
          mul_le_mul_of_nonneg_right hcoeff hbstar.le
        _ = 100 * P * C0 * bstar T k := by ring
    have : 100 * P * C0 * bstar T k < 14 * bstar T k := by
      exact hlarge.trans_le hcorr
    exact (not_lt_of_ge hcoeff') this
  have hUnionBound :
      (∑ z ∈ SA ∪ SB, S.τ.w z) ≤
        (∑ z ∈ SA, S.τ.w z) + (∑ z ∈ SB, S.τ.w z) := by
    have hdecompSet : SA ∪ SB = (SA \ SB) ∪ SB := by
      ext z
      simp
    have hdisj : Disjoint (SA \ SB) SB := Finset.sdiff_disjoint
    rw [hdecompSet, Finset.sum_union hdisj]
    have hsdiff : (∑ z ∈ SA \ SB, S.τ.w z) ≤ ∑ z ∈ SA, S.τ.w z := by
      have hsubset' : SA \ SB ⊆ SA := Finset.sdiff_subset
      exact Finset.sum_le_sum_of_subset_of_nonneg hsubset'
        (fun z hz _ => S.τ.nonneg z)
    nlinarith
  have hA := exceptional_signed hD c hpair
    (S.π l) (S.π_supp l) hπSignedWidth
    S.τ S.τ_supp S.τ_width
    (fun y => fv (T.S.E k) c x y) hf
  have hB := exceptional_first hD c hpair
    (S.π l) (S.π_supp l) hπw S.τ S.τ_supp S.τ_width
  have hmass :
      ∑ z ∈ SC, S.τ.w z ≤
        6 * Real.exp ((T.S.n k : ℝ) ^ (κ.xs / 4) - κ.α * T.S.n k) := by
    have hc := Finset.sum_le_sum_of_subset_of_nonneg hsubset
      (fun z hz _ => S.τ.nonneg z)
    have hu := hUnionBound
    have ha : ∑ z ∈ SA, S.τ.w z ≤
        4 * Real.exp ((T.S.n k : ℝ) ^ (κ.xs / 4) - κ.α * T.S.n k) := by
      simpa [SA, sig, D, m] using hA
    have hb : ∑ z ∈ SB, S.τ.w z ≤
        2 * Real.exp ((T.S.n k : ℝ) ^ (κ.xs / 4) - κ.α * T.S.n k) := by
      simpa [SB, D] using hB
    linarith
  have hfinal :
      6 * Real.exp ((T.S.n k : ℝ) ^ (κ.xs / 4) - κ.α * T.S.n k) ≤
        Real.exp (-(κ.α * T.S.n k / 3)) := by
    have hwidth' : (T.S.n k : ℝ) ^ (κ.xs / 4) - κ.α * T.S.n k ≤
        -2 * (κ.α * T.S.n k / 3) := by linarith
    calc
      6 * Real.exp ((T.S.n k : ℝ) ^ (κ.xs / 4) - κ.α * T.S.n k) ≤
          6 * Real.exp (-2 * (κ.α * T.S.n k / 3)) :=
        mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr hwidth') (by norm_num)
      _ ≤ Real.exp (-(κ.α * T.S.n k / 3)) := by
        have hexpEq : Real.exp (κ.α * T.S.n k / 3) *
            Real.exp (-2 * (κ.α * T.S.n k / 3)) =
            Real.exp (-(κ.α * T.S.n k / 3)) := by
          rw [← Real.exp_add]
          congr 1
          ring
        calc
          6 * Real.exp (-2 * (κ.α * T.S.n k / 3)) ≤
              Real.exp (κ.α * T.S.n k / 3) *
                Real.exp (-2 * (κ.α * T.S.n k / 3)) :=
            mul_le_mul_of_nonneg_right
              (by linarith : (6 : ℝ) ≤ Real.exp (κ.α * T.S.n k / 3))
              (Real.exp_pos _).le
          _ = Real.exp (-(κ.α * T.S.n k / 3)) := hexpEq
  exact hmass.trans hfinal

theorem prove_corr_tail_one (κ : CConsts) (hκ : κ.Admissible) (T : Stage)
    (hDeep : DeepDisc T κ.xs κ.α 0.04) (c : Colour) (u : ℕ)
    (C0 : ℝ) (hC0 : 1 ≤ C0) :
    ∀ᶠ k in atTop,
      ∀ (S : InterSetting T k (κ.xs / 4)) (l : Fin S.d)
        (x : Fin (T.S.N k)),
        ∑ z ∈ Finset.univ.filter (fun z =>
          100 * 3 ^ u * C0 * bstar T k <
            |corr (T.S.E k) c (S.π l).w x z|),
          S.τ.w z ≤ Real.exp (-(κ.α * T.S.n k / 3)) := by
  have hx : 0 < κ.xs := hκ.xs_rng.1
  have hα : 0 < κ.α := hκ.α_rng.1
  have hp : κ.xs / 4 < κ.xs := by linarith
  have hgap := eventually_rpow_le_mul T hp (by norm_num : (0 : ℝ) < 1 / 2)
  have hlarge := eventually_rpow_ge T (q := κ.xs) (C := 6) hx
  have hpLinear : κ.xs / 4 < 1 := by nlinarith [hκ.xs_rng.2]
  have hwidth := eventually_rpow_le_mul T hpLinear (by positivity : 0 < κ.α / 3)
  have hexp := eventually_exp_linear_ge T (a := κ.α / 3) (C := 6)
    (by positivity : 0 < κ.α / 3)
  have hn : ∀ᶠ k in atTop, 1 ≤ (T.S.n k : ℝ) := by
    exact tendsto_stage_n_real T |>.eventually (eventually_ge_atTop (1 : ℝ))
  filter_upwards [hDeep, hgap, hlarge, hwidth, hexp, hn]
    with k hD hgap hlarge hwidth hexp hn
  have hgap' : (T.S.n k : ℝ) ^ (κ.xs / 4) ≤
      (T.S.n k : ℝ) ^ κ.xs / 2 := by
    convert hgap using 1 <;> ring
  have hwidth' : (T.S.n k : ℝ) ^ (κ.xs / 4) ≤
      κ.α * T.S.n k / 3 := by
    rw [Real.rpow_one] at hwidth
    convert hwidth using 1 <;> ring
  have hexp' : 6 ≤ Real.exp (κ.α * T.S.n k / 3) := by
    convert hexp using 1 <;> ring
  exact corr_tail_one_at_k κ hκ T k hD hn hgap' hwidth' hexp' hlarge
    c u C0 hC0

private theorem inter_kernel_bound_at_k (κ : CConsts) (hκ : κ.Admissible)
    (T : Stage) (k : ℕ)
    (hD : TwoBudgetDisc T k ((T.S.n k : ℝ) ^ κ.xs)
      (κ.α * T.S.n k) (bstar T k))
    (hn : 1 ≤ (T.S.n k : ℝ))
    (hgap : (T.S.n k : ℝ) ^ (κ.xs / 4) ≤ (T.S.n k : ℝ) ^ κ.xs / 2)
    (hexp : 6 ≤ Real.exp (κ.α * T.S.n k / 3))
    (hlarge : 6 ≤ (T.S.n k : ℝ) ^ κ.xs)
    (c : Colour) (C0 : ℝ) (hC0 : 1 ≤ C0)
    (hgateScale : C0 * bstar T k ≤ 1 / 6) :
    ∀ (S : InterSetting T k (κ.xs / 4)) (l : Fin S.d),
      S.DegOK c C0 →
      ∀ y : Fin (T.S.N k),
        ((∑ y' ∈ Finset.univ.filter (fun y' =>
          6 * bstar T k < |∑ x, S.τ.w x *
              (if 0 < S.τ.w x then
                acoef (T.S.E k) c (S.π l).w x y /
                  (9 * deg (T.S.E k) c (S.π l).w x) else 0) *
              (hit (T.S.E k) c x y' -
                ∑ z, S.τ.w z * hit (T.S.E k) c z y')| ∨
          bstar T k < |(∑ x, S.τ.w x * hit (T.S.E k) c x y') - 1 / 2|),
          (S.π l).w y') ≤
            6 * Real.exp ((T.S.n k : ℝ) ^ (κ.xs / 4) - κ.α * T.S.n k)) ∧
        (∀ y',
          ¬ (6 * bstar T k < |∑ x, S.τ.w x *
                (if 0 < S.τ.w x then
                  acoef (T.S.E k) c (S.π l).w x y /
                    (9 * deg (T.S.E k) c (S.π l).w x) else 0) *
                (hit (T.S.E k) c x y' -
                  ∑ z, S.τ.w z * hit (T.S.E k) c z y')| ∨
              bstar T k < |(∑ x, S.τ.w x * hit (T.S.E k) c x y') - 1 / 2|) →
          |∑ x, S.τ.w x * acoef (T.S.E k) c (S.π l).w x y *
              acoef (T.S.E k) c (S.π l).w x y'| ≤
            100 * (C0 + 1) * bstar T k) ∧
        (∀ y',
          |∑ x, S.τ.w x * acoef (T.S.E k) c (S.π l).w x y *
              acoef (T.S.E k) c (S.π l).w x y'| ≤ 9) := by
  classical
  intro S l hDegOK y
  let π := (S.π l).w
  let D := deg (T.S.E k) c π
  let barD : Fin (T.S.N k) → ℝ := fun y' =>
    ∑ x, S.τ.w x * hit (T.S.E k) c x y'
  let A : Fin (T.S.N k) → Fin (T.S.N k) → ℝ := fun x y =>
    acoef (T.S.E k) c π x y
  let q : Fin (T.S.N k) → ℝ := fun y' =>
    ∑ x, S.τ.w x * A x y * A x y'
  let f : Fin (T.S.N k) → ℝ := fun x =>
    if 0 < S.τ.w x then A x y / (9 * D x) else 0
  let badSigned : Finset (Fin (T.S.N k)) := Finset.univ.filter (fun y' =>
    6 * bstar T k < |∑ x, S.τ.w x * f x *
      (hit (T.S.E k) c x y' - barD y')|)
  let badDeg : Finset (Fin (T.S.N k)) := Finset.univ.filter (fun y' =>
    bstar T k < |barD y' - 1 / 2|)
  have hnpos : 0 < (T.S.n k : ℝ) := by linarith
  have hbstar : 0 < bstar T k := Real.rpow_pos_of_pos hnpos _
  have hlog3 : 0 ≤ Real.log 3 ∧ Real.log 3 ≤ 2 := by
    constructor
    · exact Real.log_nonneg (by norm_num)
    · have hh := Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 3)
      linarith
  let w₁ := (T.S.n k : ℝ) ^ κ.xs / 2 + Real.log 3
  have hpair : (w₁ ≤ (T.S.n k : ℝ) ^ κ.xs ∧
      κ.α * T.S.n k ≤ κ.α * T.S.n k) ∨
      (w₁ ≤ κ.α * T.S.n k ∧ κ.α * T.S.n k ≤ (T.S.n k : ℝ) ^ κ.xs) := by
    apply Or.inl
    constructor
    · change (T.S.n k : ℝ) ^ κ.xs / 2 + Real.log 3 ≤ (T.S.n k : ℝ) ^ κ.xs
      linarith [hlarge, hlog3.2]
    · rfl
  have hpiwSmall : (S.π l).WidthLE ((T.S.n k : ℝ) ^ κ.xs / 2) := by
    intro x
    calc
      π x ≤ Real.exp ((T.S.n k : ℝ) ^ (κ.xs / 4)) / T.S.N k := S.π_width l x
      _ ≤ Real.exp ((T.S.n k : ℝ) ^ κ.xs / 2) / T.S.N k :=
        div_le_div_of_nonneg_right (Real.exp_le_exp.mpr hgap) (by positivity)
  have hτwSmall : S.τ.WidthLE ((T.S.n k : ℝ) ^ κ.xs / 2) := by
    intro x
    calc
      S.τ.w x ≤ Real.exp ((T.S.n k : ℝ) ^ (κ.xs / 4)) / T.S.N k := S.τ_width x
      _ ≤ Real.exp ((T.S.n k : ℝ) ^ κ.xs / 2) / T.S.N k :=
        div_le_div_of_nonneg_right (Real.exp_le_exp.mpr hgap) (by positivity)
  have hτwSigned : S.τ.WidthLE (w₁ - Real.log 3) := by
    have heq : w₁ - Real.log 3 = (T.S.n k : ℝ) ^ κ.xs / 2 := by
      dsimp [w₁]
      ring
    rw [heq]
    exact hτwSmall
  have hτw : S.τ.WidthLE w₁ := by
    intro x
    calc
      S.τ.w x ≤ Real.exp ((T.S.n k : ℝ) ^ κ.xs / 2) / T.S.N k := hτwSmall x
      _ ≤ Real.exp w₁ / T.S.N k :=
        div_le_div_of_nonneg_right
          (Real.exp_le_exp.mpr (by dsimp [w₁]; linarith [hlog3.1])) (by positivity)
  have hf (x : Fin (T.S.N k)) : |f x| ≤ 1 := by
    by_cases hx : 0 < S.τ.w x
    · have hgate := hDegOK l x hx
      have hlo : (1 / 3 : ℝ) ≤ D x := by
        change |D x - 1 / 2| ≤ C0 * bstar T k at hgate
        rw [abs_le] at hgate
        nlinarith [hgateScale]
      have hA := acoef_abs_le_three_of_degree (T.S.E k) c π x y hlo
      have hden : 0 < 9 * D x := by nlinarith
      dsimp [f]
      rw [if_pos hx, abs_div, abs_of_pos hden]
      apply (div_le_iff₀ hden).2
      nlinarith
    · have hzero : S.τ.w x = 0 := by
        apply le_antisymm
        · exact le_of_not_gt hx
        · exact S.τ.nonneg x
      simp [f, hx, hzero]
  have hbarGood (y' : Fin (T.S.N k)) (hy' : y' ∉ badDeg) :
      |barD y' - 1 / 2| ≤ bstar T k := by
    exact le_of_not_gt (by simpa [badDeg] using hy')
  have hsigned := exceptional_signed_second hD c hpair
    S.τ S.τ_supp hτwSigned (S.π l) (S.π_supp l) (S.π_width l)
    f hf
  have hdegree := exceptional_second hD c hpair
    S.τ S.τ_supp hτw (S.π l) (S.π_supp l) (S.π_width l)
  have hbadMass :
      ∑ y' ∈ badSigned ∪ badDeg, π y' ≤
        6 * Real.exp ((T.S.n k : ℝ) ^ (κ.xs / 4) - κ.α * T.S.n k) := by
    have hsumSigned : ∑ y' ∈ badSigned, π y' ≤
        4 * Real.exp ((T.S.n k : ℝ) ^ (κ.xs / 4) - κ.α * T.S.n k) := by
      simpa [badSigned, barD, f] using hsigned
    have hsumDegree : ∑ y' ∈ badDeg, π y' ≤
        2 * Real.exp ((T.S.n k : ℝ) ^ (κ.xs / 4) - κ.α * T.S.n k) := by
      simpa [badDeg, barD] using hdegree
    have hUnion :
        (∑ y' ∈ badSigned ∪ badDeg, π y') ≤
          (∑ y' ∈ badSigned, π y') + (∑ y' ∈ badDeg, π y') := by
      have heq : badSigned ∪ badDeg = (badSigned \ badDeg) ∪ badDeg := by
        ext y'
        simp
      rw [heq, Finset.sum_union Finset.sdiff_disjoint]
      have hsdiff : (∑ y' ∈ badSigned \ badDeg, π y') ≤
          ∑ y' ∈ badSigned, π y' :=
        Finset.sum_le_sum_of_subset_of_nonneg Finset.sdiff_subset
          (fun y' hy' _ => (S.π l).nonneg y')
      nlinarith
    linarith
  have hDlo (x : Fin (T.S.N k)) (hx : 0 < S.τ.w x) :
      (1 / 3 : ℝ) ≤ D x := by
    have hgate := hDegOK l x hx
    change |D x - 1 / 2| ≤ C0 * bstar T k at hgate
    rw [abs_le] at hgate
    nlinarith [hgateScale]
  have hAabs (x : Fin (T.S.N k)) (hx : 0 < S.τ.w x)
      (y0 : Fin (T.S.N k)) : |A x y0| ≤ 3 := by
    exact acoef_abs_le_three_of_degree (T.S.E k) c π x y0 (hDlo x hx)
  have hRfactor (y' : Fin (T.S.N k)) :
      9 * (∑ x, S.τ.w x * f x * (hit (T.S.E k) c x y' - barD y')) =
        ∑ x, S.τ.w x * (A x y / D x) *
          (hit (T.S.E k) c x y' - barD y') := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro x hx
    by_cases hxτ : 0 < S.τ.w x
    · have hDx : 0 < D x := lt_of_lt_of_le (by norm_num) (hDlo x hxτ)
      simp [f, hxτ]
      field_simp [ne_of_gt hDx] <;> ring
    · have hzero : S.τ.w x = 0 := by
        apply le_antisymm
        · exact le_of_not_gt hxτ
        · exact S.τ.nonneg x
      simp [f, hxτ, hzero]
  have hqRepr (y' : Fin (T.S.N k)) :
      q y' = ∑ x, S.τ.w x * (A x y / D x * hit (T.S.E k) c x y' - A x y) := by
    dsimp [q, A]
    apply Finset.sum_congr rfl
    intro x hx
    by_cases hxτ : 0 < S.τ.w x
    · have hDx : 0 < D x := lt_of_lt_of_le (by norm_num) (hDlo x hxτ)
      simp only [acoef]
      dsimp [D]
      field_simp [ne_of_gt hDx] <;> ring
    · have hzero : S.τ.w x = 0 := by
        apply le_antisymm
        · exact le_of_not_gt hxτ
        · exact S.τ.nonneg x
      simp [hzero]
  have hqRemainder (y' : Fin (T.S.N k)) :
      q y' = 9 * (∑ x, S.τ.w x * f x *
          (hit (T.S.E k) c x y' - barD y')) +
        ∑ x, S.τ.w x * A x y * (barD y' / D x - 1) := by
    rw [hqRepr]
    calc
      ∑ x, S.τ.w x * (A x y / D x * hit (T.S.E k) c x y' - A x y) =
          ∑ x, (9 * (S.τ.w x * f x *
              (hit (T.S.E k) c x y' - barD y')) +
            S.τ.w x * A x y * (barD y' / D x - 1)) := by
        apply Finset.sum_congr rfl
        intro x hx
        by_cases hxτ : 0 < S.τ.w x
        · have hDx : 0 < D x := lt_of_lt_of_le (by norm_num) (hDlo x hxτ)
          simp [f, hxτ]
          field_simp [ne_of_gt hDx] <;> ring
        · have hzero : S.τ.w x = 0 := by
            apply le_antisymm
            · exact le_of_not_gt hxτ
            · exact S.τ.nonneg x
          simp [f, hxτ, hzero]
      _ = 9 * (∑ x, S.τ.w x * f x *
            (hit (T.S.E k) c x y' - barD y')) +
          ∑ x, S.τ.w x * A x y * (barD y' / D x - 1) := by
        rw [Finset.sum_add_distrib, ← Finset.mul_sum]
  have hgood (y' : Fin (T.S.N k))
      (hnot : y' ∉ badSigned ∪ badDeg) : |q y'| ≤ 100 * (C0 + 1) * bstar T k := by
    have hnotS : y' ∉ badSigned := fun hmem =>
      hnot (Finset.mem_union.mpr (Or.inl hmem))
    have hnotD : y' ∉ badDeg := fun hmem =>
      hnot (Finset.mem_union.mpr (Or.inr hmem))
    have hR : |∑ x, S.τ.w x * f x *
        (hit (T.S.E k) c x y' - barD y')| ≤ 6 * bstar T k :=
      le_of_not_gt (by simpa [badSigned, barD, f] using hnotS)
    have hbar := hbarGood y' hnotD
    have hremPoint (x : Fin (T.S.N k)) :
        |S.τ.w x * A x y * (barD y' / D x - 1)| ≤
          S.τ.w x * (9 * (C0 + 1) * bstar T k) := by
      by_cases hxτ : 0 < S.τ.w x
      · have hDxPos : 0 < D x := lt_of_lt_of_le (by norm_num) (hDlo x hxτ)
        have hDxInv : 1 / D x ≤ 3 := by
          apply (div_le_iff₀ hDxPos).2
          nlinarith [hDlo x hxτ]
        have hdiff : |barD y' - D x| ≤ (C0 + 1) * bstar T k := by
          have hgate := hDegOK l x hxτ
          change |D x - 1 / 2| ≤ C0 * bstar T k at hgate
          calc
            |barD y' - D x| ≤ |barD y' - 1 / 2| + |D x - 1 / 2| := by
              have heq : barD y' - D x =
                  (barD y' - 1 / 2) - (D x - 1 / 2) := by ring
              rw [heq]
              exact abs_sub _ _
            _ ≤ bstar T k + C0 * bstar T k := add_le_add hbar hgate
            _ = (C0 + 1) * bstar T k := by ring
        have hratio : barD y' / D x - 1 = (barD y' - D x) / D x := by
          field_simp [ne_of_gt hDxPos] <;> ring
        have hratioBound : |barD y' / D x - 1| ≤
            3 * (C0 + 1) * bstar T k := by
          rw [hratio, abs_div, abs_of_pos hDxPos]
          calc
            |barD y' - D x| / D x = |barD y' - D x| * (1 / D x) := by ring
            _ ≤ |barD y' - D x| * 3 :=
              mul_le_mul_of_nonneg_left hDxInv (abs_nonneg _)
            _ ≤ ((C0 + 1) * bstar T k) * 3 :=
              mul_le_mul_of_nonneg_right hdiff (by norm_num)
            _ = 3 * (C0 + 1) * bstar T k := by ring
        have hA := hAabs x hxτ y
        rw [abs_mul, abs_mul, abs_of_nonneg (S.τ.nonneg x)]
        calc
          S.τ.w x * |A x y| * |barD y' / D x - 1| =
              S.τ.w x * (|A x y| * |barD y' / D x - 1|) := by ring
          _ ≤ S.τ.w x * (3 * (3 * (C0 + 1) * bstar T k)) :=
            mul_le_mul_of_nonneg_left
              (mul_le_mul hA hratioBound (by positivity) (by positivity))
              (S.τ.nonneg x)
          _ = S.τ.w x * (9 * (C0 + 1) * bstar T k) := by ring
      · have hzero : S.τ.w x = 0 := by
          apply le_antisymm
          · exact le_of_not_gt hxτ
          · exact S.τ.nonneg x
        simp [hzero]
    have hrem : |∑ x, S.τ.w x * A x y * (barD y' / D x - 1)| ≤
        9 * (C0 + 1) * bstar T k := by
      calc
        |∑ x, S.τ.w x * A x y * (barD y' / D x - 1)| ≤
            ∑ x, |S.τ.w x * A x y * (barD y' / D x - 1)| := by
              simpa using Finset.abs_sum_le_sum_abs
                (fun x => S.τ.w x * A x y * (barD y' / D x - 1)) Finset.univ
        _ ≤ ∑ x, S.τ.w x * (9 * (C0 + 1) * bstar T k) :=
              Finset.sum_le_sum fun x hx => hremPoint x
        _ = 9 * (C0 + 1) * bstar T k := by
              rw [← Finset.sum_mul]
              simp [S.τ.sum_eq_one]
    rw [hqRemainder y']
    have hR' : |9 * (∑ x, S.τ.w x * f x *
        (hit (T.S.E k) c x y' - barD y'))| ≤ 54 * bstar T k := by
      rw [abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 9)]
      calc
        9 * |∑ x, S.τ.w x * f x *
            (hit (T.S.E k) c x y' - barD y')| ≤ 9 * (6 * bstar T k) :=
          mul_le_mul_of_nonneg_left hR (by norm_num)
        _ = 54 * bstar T k := by ring
    calc
      |9 * (∑ x, S.τ.w x * f x *
          (hit (T.S.E k) c x y' - barD y') ) +
          ∑ x, S.τ.w x * A x y * (barD y' / D x - 1)| ≤
          54 * bstar T k + 9 * (C0 + 1) * bstar T k :=
        (abs_add_le _ _).trans (add_le_add hR' hrem)
      _ ≤ 100 * (C0 + 1) * bstar T k := by nlinarith [hbstar]
  have hglobal (y' : Fin (T.S.N k)) : |q y'| ≤ 9 := by
    calc
      |∑ x, S.τ.w x * A x y * A x y'| ≤
          ∑ x, |S.τ.w x * A x y * A x y'| := by
            simpa using Finset.abs_sum_le_sum_abs
              (fun x => S.τ.w x * A x y * A x y') Finset.univ
      _ ≤ ∑ x, S.τ.w x * 9 := by
          apply Finset.sum_le_sum
          intro x hx
          by_cases hxτ : 0 < S.τ.w x
          · rw [abs_mul, abs_mul, abs_of_nonneg (S.τ.nonneg x)]
            have h₁ := hAabs x hxτ y
            have h₂ := hAabs x hxτ y'
            calc
              S.τ.w x * |A x y| * |A x y'| =
                  S.τ.w x * (|A x y| * |A x y'|) := by ring
              _ ≤ S.τ.w x * (3 * 3) :=
                mul_le_mul_of_nonneg_left (mul_le_mul h₁ h₂ (by positivity) (by positivity))
                  (S.τ.nonneg x)
              _ = S.τ.w x * 9 := by norm_num
          · have hz : S.τ.w x = 0 := by
              apply le_antisymm
              · exact le_of_not_gt hxτ
              · exact S.τ.nonneg x
            simp [hz]
      _ = 9 := by rw [← Finset.sum_mul]; simp [S.τ.sum_eq_one]
  have hbadSet : badSigned ∪ badDeg = Finset.univ.filter (fun y' =>
      6 * bstar T k < |∑ x, S.τ.w x * f x *
        (hit (T.S.E k) c x y' - barD y')| ∨
      bstar T k < |barD y' - 1 / 2|) := by
    ext y'
    simp [badSigned, badDeg]
  refine ⟨?_, ?_, hglobal⟩
  · have h := hbadMass
    rw [hbadSet] at h
    simpa [barD, f] using h
  · intro y' hy'
    have hnot : y' ∉ badSigned ∪ badDeg := by
      intro hmem
      rcases Finset.mem_union.mp hmem with hs | hd
      · apply hy'
        left
        simpa [badSigned, barD, f] using hs
      · apply hy'
        right
        simpa [badDeg, barD] using hd
    exact hgood y' hnot

private theorem inter_mean_at_k (κ : CConsts) (hκ : κ.Admissible)
    (T : Stage) (k : ℕ)
    (hD : TwoBudgetDisc T k ((T.S.n k : ℝ) ^ κ.xs)
      (κ.α * T.S.n k) (bstar T k))
    (hn : 1 ≤ (T.S.n k : ℝ))
    (hgap : (T.S.n k : ℝ) ^ (κ.xs / 4) ≤ (T.S.n k : ℝ) ^ κ.xs / 2)
    (hwidth : (T.S.n k : ℝ) ^ (κ.xs / 4) ≤ κ.α * T.S.n k / 3)
    (hexp : 6 ≤ Real.exp (κ.α * T.S.n k / 3))
    (hlarge : 6 ≤ (T.S.n k : ℝ) ^ κ.xs)
    (c : Colour) (u : ℕ) (C0 : ℝ) (hC0 : 1 ≤ C0)
    (hgateScale : C0 * bstar T k ≤ 1 / 6)
    (hK : 100 * (C0 + 1) * bstar T k ≤ (T.S.n k : ℝ) ^ (-(0.9 : ℝ)))
    (hhalf : (T.S.n k : ℝ) ^ (-(0.2 : ℝ)) ≤ 1 / 2)
    (hpoly : 6 * 9 ^ u * (T.S.n k : ℝ) ^ (0.8 * (u : ℝ)) *
      Real.exp (-(2 * κ.α * T.S.n k / 3)) ≤ 1 / 2) :
    ∀ (S : InterSetting T k (κ.xs / 4)) (l : Fin S.d),
      S.DegOK c C0 →
      ∀ J : Finset (Fin u), 2 ≤ J.card → J.card ≤ u →
        ∑ xs : Fin u → Fin (T.S.N k),
          prodW S.τ.w xs * |inter (T.S.E k) c (S.π l).w J xs| ≤
            (T.S.n k : ℝ) ^ (-0.4 * (J.card : ℝ)) := by
  classical
  intro S l hDegOK J hJ hJu
  let π := (S.π l).w
  let q (y y' : Fin (T.S.N k)) : ℝ :=
    ∑ x, S.τ.w x * acoef (T.S.E k) c π x y * acoef (T.S.E k) c π x y'
  let bad (y : Fin (T.S.N k)) : Finset (Fin (T.S.N k)) := Finset.univ.filter (fun y' =>
    6 * bstar T k < |∑ x, S.τ.w x *
      (if 0 < S.τ.w x then
        acoef (T.S.E k) c π x y / (9 * deg (T.S.E k) c π x) else 0) *
      (hit (T.S.E k) c x y' - ∑ z, S.τ.w z * hit (T.S.E k) c z y')| ∨
    bstar T k < |(∑ x, S.τ.w x * hit (T.S.E k) c x y') - 1 / 2|)
  let K : ℝ := 100 * (C0 + 1) * bstar T k
  let B : ℝ := 6 * Real.exp ((T.S.n k : ℝ) ^ (κ.xs / 4) - κ.α * T.S.n k)
  let m : ℕ := J.card
  have hnpos : 0 < (T.S.n k : ℝ) := by linarith
  have hC0pos : 0 < C0 := lt_of_lt_of_le zero_lt_one hC0
  have hbstar : 0 < bstar T k := Real.rpow_pos_of_pos hnpos _
  have hKpos : 0 < K := by dsimp [K]; positivity
  have hKern := inter_kernel_bound_at_k κ hκ T k hD hn hgap hexp hlarge
    c C0 hC0 hgateScale S l hDegOK
  have hbad (y : Fin (T.S.N k)) :
      ∑ y' ∈ bad y, π y' ≤ B := by
    simpa [bad, B, π] using (hKern y).1
  have hgood (y y' : Fin (T.S.N k)) (hny : y' ∉ bad y) :
      |q y y'| ≤ K := by
    have hnot : ¬ (6 * bstar T k <
        |∑ x, S.τ.w x *
          (if 0 < S.τ.w x then
            acoef (T.S.E k) c π x y / (9 * deg (T.S.E k) c π x) else 0) *
          (hit (T.S.E k) c x y' - ∑ z, S.τ.w z * hit (T.S.E k) c z y')| ∨
        bstar T k < |(∑ x, S.τ.w x * hit (T.S.E k) c x y') - 1 / 2|) := by
      simpa [bad, π] using hny
    simpa [q, K, π] using (hKern y).2.1 y' hnot
  have hglobal (y y' : Fin (T.S.N k)) : |q y y'| ≤ 9 := by
    simpa [q, π] using (hKern y).2.2 y'
  have hqpow (y y' : Fin (T.S.N k)) :
      q y y' ^ m ≤ K ^ m + if y' ∈ bad y then 9 ^ m else 0 := by
    by_cases hy : y' ∈ bad y
    · have hqabs := hglobal y y'
      have hqle : q y y' ^ m ≤ (9 : ℝ) ^ m := by
        calc
          q y y' ^ m ≤ |q y y' ^ m| := le_abs_self _
          _ = |q y y'| ^ m := by rw [abs_pow]
          _ ≤ (9 : ℝ) ^ m := pow_le_pow_left₀ (abs_nonneg _) hqabs m
      have hle : q y y' ^ m ≤ K ^ m + (9 : ℝ) ^ m := by
        nlinarith [hqle, pow_nonneg (le_of_lt hKpos) m]
      simpa [hy] using hle
    · have hqabs := hgood y y' hy
      calc
        q y y' ^ m ≤ |q y y' ^ m| := le_abs_self _
        _ = |q y y'| ^ m := by rw [abs_pow]
        _ ≤ K ^ m := pow_le_pow_left₀ (abs_nonneg _) hqabs m
        _ = K ^ m + 0 := by simp
        _ = K ^ m + (if y' ∈ bad y then 9 ^ m else 0) := by simp [hy]
  have hInner (y : Fin (T.S.N k)) :
      ∑ y', π y' * q y y' ^ m ≤ K ^ m + 9 ^ m * B := by
    have hIndicator :
        ∑ y', π y' * (if y' ∈ bad y then 9 ^ m else 0) =
          9 ^ m * (∑ y' ∈ bad y, π y') := by
      calc
        ∑ y', π y' * (if y' ∈ bad y then 9 ^ m else 0) =
            ∑ y', if y' ∈ bad y then π y' * 9 ^ m else 0 := by
          simp_rw [mul_ite, mul_zero]
        _ = ∑ y' ∈ bad y, π y' * 9 ^ m := by
          rw [Finset.sum_ite_mem_eq]
        _ = (∑ y' ∈ bad y, π y') * 9 ^ m := by
          rw [← Finset.sum_mul]
        _ = 9 ^ m * (∑ y' ∈ bad y, π y') := by ring
    calc
      ∑ y', π y' * q y y' ^ m ≤
          ∑ y', π y' * (K ^ m + if y' ∈ bad y then 9 ^ m else 0) := by
        apply Finset.sum_le_sum
        intro y' hy'
        exact mul_le_mul_of_nonneg_left (hqpow y y') ((S.π l).nonneg y')
      _ ≤ K ^ m + 9 ^ m * B := by
        simp_rw [mul_add]
        rw [Finset.sum_add_distrib]
        have hFirst : ∑ y', π y' * K ^ m = K ^ m := by
          rw [← Finset.sum_mul]
          rw [(S.π l).sum_eq_one]
          ring
        rw [hFirst, hIndicator]
        have hmass := hbad y
        have hscaleMass := mul_le_mul_of_nonneg_left hmass
          (pow_nonneg (by norm_num : (0 : ℝ) ≤ 9) m)
        calc
          K ^ m + 9 ^ m * (∑ y' ∈ bad y, π y') =
              9 ^ m * (∑ y' ∈ bad y, π y') + K ^ m := by ring
          _ ≤ 9 ^ m * B + K ^ m := add_le_add_left hscaleMass _
          _ = K ^ m + 9 ^ m * B := by ring
  have hSecond :
      ∑ xs : Fin u → Fin (T.S.N k),
        prodW S.τ.w xs * (inter (T.S.E k) c π J xs) ^ 2 ≤
          K ^ m + 9 ^ m * B := by
    have hid := inter_second_moment_identity (T.S.E k) c S.τ π J
    rw [hid]
    calc
      ∑ y, ∑ y', π y * π y' * q y y' ^ m ≤
          ∑ y, π y * (K ^ m + 9 ^ m * B) := by
        apply Finset.sum_le_sum
        intro y hy
        calc
          ∑ y', π y * π y' * q y y' ^ m = π y * (∑ y', π y' * q y y' ^ m) := by
            calc
              ∑ y', π y * π y' * q y y' ^ m =
                  ∑ y', π y * (π y' * q y y' ^ m) := by
                apply Finset.sum_congr rfl
                intro y' hy'
                ring
              _ = π y * (∑ y', π y' * q y y' ^ m) := by rw [← Finset.mul_sum]
          _ ≤ π y * (K ^ m + 9 ^ m * B) :=
            mul_le_mul_of_nonneg_left (hInner y) ((S.π l).nonneg y)
      _ = K ^ m + 9 ^ m * B := by
        rw [← Finset.sum_mul]
        rw [(S.π l).sum_eq_one]
        ring
  let n : ℝ := T.S.n k
  let e : ℝ := (J.card : ℝ)
  have hmcast : (2 : ℝ) ≤ e := by
    change (2 : ℝ) ≤ (J.card : ℝ)
    exact_mod_cast hJ
  have hJlecast : e ≤ u := by
    change (J.card : ℝ) ≤ (u : ℝ)
    exact_mod_cast hJu
  have hFirst : K ^ m ≤ n ^ (-(0.8 : ℝ) * e) / 2 := by
    have hpowK : K ^ m ≤ (n ^ (-(0.9 : ℝ))) ^ m :=
      pow_le_pow_left₀ (by positivity) (by simpa [K, n] using hK) m
    have hpowEq : (n ^ (-(0.9 : ℝ))) ^ m = n ^ (-(0.9 : ℝ) * e) := by
      simpa [e] using (Real.rpow_mul_natCast (by positivity : 0 ≤ n)
        (-(0.9 : ℝ)) m).symm
    have hsmallPow : n ^ (-(0.1 : ℝ) * e) ≤ 1 / 2 := by
      calc
        n ^ (-(0.1 : ℝ) * e) ≤ n ^ (-(0.2 : ℝ)) :=
          Real.rpow_le_rpow_of_exponent_le (by linarith : 1 ≤ n) (by nlinarith)
        _ ≤ 1 / 2 := by simpa [n] using hhalf
    have hsplit : n ^ (-(0.9 : ℝ) * e) =
        n ^ (-(0.8 : ℝ) * e) * n ^ (-(0.1 : ℝ) * e) := by
      rw [← Real.rpow_add (by positivity : 0 < n)]
      congr 1
      ring
    calc
      K ^ m ≤ n ^ (-(0.9 : ℝ) * e) := hpowK.trans_eq hpowEq
      _ = n ^ (-(0.8 : ℝ) * e) * n ^ (-(0.1 : ℝ) * e) := hsplit
      _ ≤ n ^ (-(0.8 : ℝ) * e) * (1 / 2) :=
        mul_le_mul_of_nonneg_left hsmallPow (Real.rpow_nonneg (by positivity) _)
      _ = n ^ (-(0.8 : ℝ) * e) / 2 := by ring
  have hwidthExp : n ^ (κ.xs / 4) - κ.α * n ≤ -(2 * κ.α * n / 3) := by
    dsimp [n]
    linarith [hwidth]
  have hExpTerm : 9 ^ m * B ≤ n ^ (-(0.8 : ℝ) * e) / 2 := by
    have hpow9 : (9 : ℝ) ^ m ≤ (9 : ℝ) ^ u := by
      exact pow_le_pow_right₀ (by norm_num) hJu
    have hnPow : n ^ (0.8 * e) ≤ n ^ (0.8 * (u : ℝ)) :=
      Real.rpow_le_rpow_of_exponent_le (by linarith : 1 ≤ n) (by nlinarith)
    have hscale : (9 ^ m * B) * n ^ (0.8 * e) ≤ 1 / 2 := by
      have hmul : 9 ^ m * n ^ (0.8 * e) ≤ 9 ^ u * n ^ (0.8 * (u : ℝ)) :=
        mul_le_mul hpow9 hnPow (by positivity) (by positivity)
      calc
        (9 ^ m * B) * n ^ (0.8 * e) ≤
            9 ^ m * (6 * Real.exp (-(2 * κ.α * n / 3))) * n ^ (0.8 * e) := by
          dsimp [B]
          gcongr
        _ = 6 * Real.exp (-(2 * κ.α * n / 3)) *
            (9 ^ m * n ^ (0.8 * e)) := by ring
        _ ≤ 6 * Real.exp (-(2 * κ.α * n / 3)) *
            (9 ^ u * n ^ (0.8 * (u : ℝ))) :=
          mul_le_mul_of_nonneg_left hmul (by positivity)
        _ = 6 * 9 ^ u * n ^ (0.8 * (u : ℝ)) *
            Real.exp (-(2 * κ.α * n / 3)) := by ring
        _ ≤ 1 / 2 := by simpa [n] using hpoly
    have hnpowpos : 0 < n ^ (0.8 * e) := Real.rpow_pos_of_pos (by linarith : 0 < n) _
    have hdiv := (le_div_iff₀ hnpowpos).2 hscale
    have hinv : (n ^ (0.8 * e))⁻¹ = n ^ (-(0.8 * e)) := by
      exact (Real.rpow_neg (by positivity : 0 ≤ n) (0.8 * e)).symm
    calc
      9 ^ m * B ≤ (1 / 2) / n ^ (0.8 * e) := hdiv
      _ = n ^ (-(0.8 : ℝ) * e) / 2 := by rw [div_eq_mul_inv, hinv]; ring
  have hSecondBound :
      K ^ m + 9 ^ m * B ≤ n ^ (-(0.8 : ℝ) * e) := by
    calc
      K ^ m + 9 ^ m * B ≤
          n ^ (-(0.8 : ℝ) * e) / 2 + n ^ (-(0.8 : ℝ) * e) / 2 :=
        add_le_add hFirst hExpTerm
      _ = n ^ (-(0.8 : ℝ) * e) := by ring
  let wgt : (Fin u → Fin (T.S.N k)) → ℝ := fun xs => prodW S.τ.w xs
  have hwgt (xs : Fin u → Fin (T.S.N k)) : 0 ≤ wgt xs := by
    dsimp [wgt, prodW]
    exact Finset.prod_nonneg fun i hi => S.τ.nonneg (xs i)
  have hnorm : ∑ xs : Fin u → Fin (T.S.N k), wgt xs = 1 := by
    dsimp [wgt, prodW]
    rw [← Fintype.prod_sum]
    simp [S.τ.sum_eq_one]
  have hSecondMoment :
      ∑ xs : Fin u → Fin (T.S.N k), wgt xs *
        (inter (T.S.E k) c π J xs) ^ 2 ≤ n ^ (-(0.8 : ℝ) * e) := by
    dsimp [wgt]
    exact hSecond.trans hSecondBound
  have hcs :
      (∑ xs : Fin u → Fin (T.S.N k),
        wgt xs * |inter (T.S.E k) c π J xs|) ^ 2 ≤
        (∑ xs : Fin u → Fin (T.S.N k), wgt xs *
          (inter (T.S.E k) c π J xs) ^ 2) *
      (∑ xs : Fin u → Fin (T.S.N k), wgt xs) := by
    let f : (Fin u → Fin (T.S.N k)) → ℝ := fun xs => Real.sqrt (wgt xs)
    let g : (Fin u → Fin (T.S.N k)) → ℝ := fun xs =>
      Real.sqrt (wgt xs) * |inter (T.S.E k) c π J xs|
    have h := Finset.sum_mul_sq_le_sq_mul_sq Finset.univ f g
    have hsqrt (xs : Fin u → Fin (T.S.N k)) : f xs * f xs = wgt xs := by
      dsimp [f]
      nlinarith [Real.sq_sqrt (hwgt xs)]
    have hleft :
        (∑ xs, wgt xs * |inter (T.S.E k) c π J xs|) = ∑ xs, f xs * g xs := by
      apply Finset.sum_congr rfl
      intro xs hxs
      dsimp [f, g]
      calc
        wgt xs * |inter (T.S.E k) c π J xs| =
            (Real.sqrt (wgt xs) * Real.sqrt (wgt xs)) *
              |inter (T.S.E k) c π J xs| := by rw [hsqrt xs]
        _ = Real.sqrt (wgt xs) *
            (Real.sqrt (wgt xs) * |inter (T.S.E k) c π J xs|) := by ring
    have hsumF : ∑ xs, f xs ^ 2 = ∑ xs, wgt xs := by
      apply Finset.sum_congr rfl
      intro xs hxs
      dsimp [f]
      exact Real.sq_sqrt (hwgt xs)
    have hsumG : ∑ xs, g xs ^ 2 =
        ∑ xs, wgt xs * (inter (T.S.E k) c π J xs) ^ 2 := by
      apply Finset.sum_congr rfl
      intro xs hxs
      dsimp [g]
      rw [mul_pow, Real.sq_sqrt (hwgt xs), sq_abs]
    calc
      (∑ xs, wgt xs * |inter (T.S.E k) c π J xs|) ^ 2 =
          (∑ xs, f xs * g xs) ^ 2 := by rw [hleft]
      _ ≤ (∑ xs, f xs ^ 2) * ∑ xs, g xs ^ 2 := h
      _ = (∑ xs, wgt xs) *
            (∑ xs, wgt xs * (inter (T.S.E k) c π J xs) ^ 2) := by
          rw [hsumF, hsumG]
      _ = (∑ xs, wgt xs * (inter (T.S.E k) c π J xs) ^ 2) *
            (∑ xs, wgt xs) := by ring
  have hTargetSq :
      (n ^ (-0.4 * e)) ^ 2 = n ^ (-(0.8 : ℝ) * e) := by
    rw [← Real.rpow_natCast (n ^ (-0.4 * e)) 2,
      ← Real.rpow_mul (by positivity : 0 ≤ n)]
    congr 1
    ring
  have hLnonneg : 0 ≤ ∑ xs : Fin u → Fin (T.S.N k),
      wgt xs * |inter (T.S.E k) c π J xs| :=
    Finset.sum_nonneg fun xs hxs => mul_nonneg (hwgt xs) (abs_nonneg _)
  have hTnonneg : 0 ≤ n ^ (-0.4 * e) := Real.rpow_nonneg (by positivity) _
  have hCauchyBound :
      (∑ xs : Fin u → Fin (T.S.N k),
        wgt xs * |inter (T.S.E k) c π J xs|) ^ 2 ≤ n ^ (-(0.8 : ℝ) * e) := by
    calc
      (∑ xs : Fin u → Fin (T.S.N k),
        wgt xs * |inter (T.S.E k) c π J xs|) ^ 2 ≤
          (∑ xs : Fin u → Fin (T.S.N k), wgt xs *
            (inter (T.S.E k) c π J xs) ^ 2) *
            (∑ xs : Fin u → Fin (T.S.N k), wgt xs) := hcs
      _ = ∑ xs : Fin u → Fin (T.S.N k), wgt xs *
            (inter (T.S.E k) c π J xs) ^ 2 := by rw [hnorm]; ring
      _ ≤ n ^ (-(0.8 : ℝ) * e) := hSecondMoment
  have hresult :
      ∑ xs : Fin u → Fin (T.S.N k),
        wgt xs * |inter (T.S.E k) c π J xs| ≤ n ^ (-0.4 * e) := by
    nlinarith [hCauchyBound, hTargetSq, hLnonneg, hTnonneg]
  simpa [wgt, n, e] using hresult

theorem prove_corr_tail_two (κ : CConsts) (hκ : κ.Admissible) (T : Stage)
    (hDeep : DeepDisc T κ.xs κ.α 0.04) (c : Colour) (u : ℕ)
    (C0 : ℝ) (hC0 : 1 ≤ C0) :
    ∀ᶠ k in atTop,
      ∀ (S : InterSetting T k (κ.xs / 4)) (l : Fin S.d),
        ∑ z, ∑ z',
          (if (T.S.n k : ℝ) ^ (-(1.03 : ℝ)) <
              |corr (T.S.E k) c (S.π l).w z z'|
           then S.τ.w z * S.τ.w z' else 0) ≤
            Real.exp (-((T.S.n k : ℝ) ^ (0.4 : ℝ))) := by
  have hx : 0 < κ.xs := hκ.xs_rng.1
  have hSmallExp := eventually_small_exp_vs_bstar T κ hx
  have hCost := eventually_conditioning_cost T κ hκ
  have hn : ∀ᶠ k in atTop, 1 ≤ (T.S.n k : ℝ) :=
    tendsto_stage_n_real T |>.eventually (eventually_ge_atTop (1 : ℝ))
  have hSampleExp := eventually_rpow_le_mul T (p := -(1.67 : ℝ))
    (q := 0) (c := 1 / 27) (by norm_num) (by norm_num)
  have hRatioExp := eventually_rpow_le_mul T (p := -(0.96 : ℝ))
    (q := -(0.905 : ℝ)) (c := 1 / 12) (by norm_num) (by norm_num)
  filter_upwards [hDeep, hSmallExp, hCost, hn, hSampleExp, hRatioExp]
    with k hD hSmallExp hCost hn hSampleExp hRatioExp
  let n : ℝ := T.S.n k
  let t : ℕ := Nat.ceil (n ^ (0.25 : ℝ))
  have hnpos : 0 < n := lt_of_lt_of_le (by norm_num) hn
  have hnQuarter : 1 ≤ n ^ (0.25 : ℝ) := by
    calc
      1 = n ^ (0 : ℝ) := by simp
      _ ≤ n ^ (0.25 : ℝ) := Real.rpow_le_rpow_of_exponent_le hn (by norm_num)
  have htLower : n ^ (0.25 : ℝ) ≤ (t : ℝ) := by
    dsimp [t]
    exact Nat.le_ceil _
  have htUpper : (t : ℝ) ≤ 3 * n ^ (0.25 : ℝ) := by
    have hceil : (t : ℝ) < n ^ (0.25 : ℝ) + 1 := by
      dsimp [t]
      exact Nat.ceil_lt_add_one (by positivity)
    linarith [hnQuarter]
  have ht : 0 < t := by
    have htcast : 1 ≤ (t : ℝ) := le_trans hnQuarter htLower
    exact_mod_cast (show 0 < (t : ℝ) by linarith)
  have hbEq : bstar T k = n ^ (-(0.96 : ℝ)) := by
    dsimp [bstar, n]
    congr 1
    norm_num
  have hpow96 : (n ^ (-(0.96 : ℝ))) ^ 2 = n ^ (-(1.92 : ℝ)) := by
    rw [← Real.rpow_natCast (n ^ (-(0.96 : ℝ))) 2,
      ← Real.rpow_mul (by positivity : 0 ≤ n)]
    congr 1
    norm_num
  have hpowSample : n ^ (0.25 : ℝ) * n ^ (-(1.92 : ℝ)) =
      n ^ (-(1.67 : ℝ)) := by
    rw [← Real.rpow_add (by positivity : 0 < n)]
    congr 1
    norm_num
  have hcoefSq : (3 * n ^ (-(0.96 : ℝ))) ^ 2 =
      9 * n ^ (-(1.92 : ℝ)) := by
    calc
      (3 * n ^ (-(0.96 : ℝ))) ^ 2 = 9 * (n ^ (-(0.96 : ℝ))) ^ 2 := by ring
      _ = 9 * n ^ (-(1.92 : ℝ)) := by rw [hpow96]
  have hsample : (t : ℝ) * (3 * n ^ (-(0.96 : ℝ))) ^ 2 ≤ 1 := by
    calc
      (t : ℝ) * (3 * n ^ (-(0.96 : ℝ))) ^ 2 ≤
          (3 * n ^ (0.25 : ℝ)) * (3 * n ^ (-(0.96 : ℝ))) ^ 2 :=
        mul_le_mul_of_nonneg_right htUpper (by positivity)
      _ = 27 * n ^ (-(1.67 : ℝ)) := by
        rw [hcoefSq]
        calc
          3 * n ^ (0.25 : ℝ) * (9 * n ^ (-(1.92 : ℝ))) =
              27 * (n ^ (0.25 : ℝ) * n ^ (-(1.92 : ℝ))) := by ring
          _ = 27 * n ^ (-(1.67 : ℝ)) := by rw [hpowSample]
      _ ≤ 1 := by
        have hsmall : n ^ (-(1.67 : ℝ)) ≤ 1 / 27 := by
          simpa [n] using hSampleExp
        calc
          27 * n ^ (-(1.67 : ℝ)) ≤ 27 * (1 / 27) :=
            mul_le_mul_of_nonneg_left hsmall (by norm_num)
          _ = 1 := by norm_num
  have hpow125 : (n ^ (0.125 : ℝ)) ^ 2 = n ^ (0.25 : ℝ) := by
    rw [← Real.rpow_natCast (n ^ (0.125 : ℝ)) 2,
      ← Real.rpow_mul (by positivity : 0 ≤ n)]
    congr 1
    norm_num
  have hsqrtLower : n ^ (0.125 : ℝ) ≤ Real.sqrt (t : ℝ) :=
    Real.le_sqrt_of_sq_le (by rw [hpow125]; exact htLower)
  have hpowRatio : n ^ (-(1.03 : ℝ)) * n ^ (0.125 : ℝ) =
      n ^ (-(0.905 : ℝ)) := by
    rw [← Real.rpow_add (by positivity : 0 < n)]
    congr 1
    norm_num
  have hratio : 6 * n ^ (-(0.96 : ℝ)) <
      n ^ (-(1.03 : ℝ)) * Real.sqrt (t : ℝ) := by
    have hsmall : n ^ (-(0.96 : ℝ)) ≤
        (1 / 12) * n ^ (-(0.905 : ℝ)) := by
      simpa [n] using hRatioExp
    have hstrict : 6 * n ^ (-(0.96 : ℝ)) < n ^ (-(0.905 : ℝ)) := by
      calc
        6 * n ^ (-(0.96 : ℝ)) ≤ 6 * ((1 / 12) * n ^ (-(0.905 : ℝ))) :=
          mul_le_mul_of_nonneg_left hsmall (by norm_num)
        _ = (1 / 2) * n ^ (-(0.905 : ℝ)) := by ring
        _ < n ^ (-(0.905 : ℝ)) := by
          have hpos := Real.rpow_pos_of_pos hnpos (-(0.905 : ℝ))
          calc
            (1 / 2) * n ^ (-(0.905 : ℝ)) <
                1 * n ^ (-(0.905 : ℝ)) :=
              mul_lt_mul_of_pos_right (by norm_num) hpos
            _ = n ^ (-(0.905 : ℝ)) := by ring
    calc
      6 * n ^ (-(0.96 : ℝ)) < n ^ (-(0.905 : ℝ)) := hstrict
      _ = n ^ (-(1.03 : ℝ)) * n ^ (0.125 : ℝ) := hpowRatio.symm
      _ ≤ n ^ (-(1.03 : ℝ)) * Real.sqrt (t : ℝ) :=
        mul_le_mul_of_nonneg_left hsqrtLower (by positivity)
  have hcontr : (t : ℝ) * n ^ (-(1.03 : ℝ)) >
      6 * n ^ (-(0.96 : ℝ)) * Real.sqrt (t : ℝ) := by
    have htReal : 0 < (t : ℝ) := by exact_mod_cast ht
    have hmul := mul_lt_mul_of_pos_right hratio (Real.sqrt_pos.mpr htReal)
    have hsquare : (Real.sqrt (t : ℝ)) ^ 2 = (t : ℝ) :=
      Real.sq_sqrt (Nat.cast_nonneg t)
    calc
      (t : ℝ) * n ^ (-(1.03 : ℝ)) =
          (n ^ (-(1.03 : ℝ)) * Real.sqrt (t : ℝ)) * Real.sqrt (t : ℝ) := by
        calc
          (t : ℝ) * n ^ (-(1.03 : ℝ)) =
              (Real.sqrt (t : ℝ)) ^ 2 * n ^ (-(1.03 : ℝ)) := by rw [hsquare]
          _ = (n ^ (-(1.03 : ℝ)) * Real.sqrt (t : ℝ)) * Real.sqrt (t : ℝ) := by ring
      _ > 6 * n ^ (-(0.96 : ℝ)) * Real.sqrt (t : ℝ) := by
        nlinarith [hmul]
  intro S l
  have hMeanData : ∀ (A : Finset (Fin (T.S.N k)))
      (hA : 0 < ∑ x ∈ A, S.τ.w x),
      (T.S.n k : ℝ) ^ (κ.xs / 4) - Real.log (∑ x ∈ A, S.τ.w x) ≤
        κ.α * T.S.n k →
      ∑ y, (S.π l).w y *
        (∑ x, (S.τ.restrict A hA).w x * fv (T.S.E k) c x y) ^ 2 ≤
          (3 * (T.S.n k : ℝ) ^ (-(0.96 : ℝ))) ^ 2 := by
    intro A hA hwidth
    have h := fv_conditional_l2_at_k T κ k hn hD hSmallExp c
      S.τ_supp S.τ_width (S.π_supp l) (S.π_width l) A hA hwidth
    have hbEq : bstar T k = (T.S.n k : ℝ) ^ (-(0.96 : ℝ)) := by
      dsimp [bstar]
      congr 1
      norm_num
    simpa [hbEq] using h
  have hCost' : ∀ (A : Finset (Fin (T.S.N k)))
      (hA : 0 < ∑ x ∈ A, S.τ.w x),
      (Real.exp (-((T.S.n k : ℝ) ^ (0.4 : ℝ))) / 4) ^ (t + 1) / 2 ≤
        ∑ x ∈ A, S.τ.w x →
      (T.S.n k : ℝ) ^ (κ.xs / 4) - Real.log (∑ x ∈ A, S.τ.w x) ≤
        κ.α * T.S.n k := by
    intro A hA hmass
    have hbase : Real.exp (-((T.S.n k : ℝ) ^ (0.4 : ℝ))) / 8 ≤
        Real.exp (-((T.S.n k : ℝ) ^ (0.4 : ℝ))) / 4 := by
      calc
        _ = Real.exp (-((T.S.n k : ℝ) ^ (0.4 : ℝ))) * (1 / 8) := by ring
        _ ≤ Real.exp (-((T.S.n k : ℝ) ^ (0.4 : ℝ))) * (1 / 4) :=
          mul_le_mul_of_nonneg_left (by norm_num) (Real.exp_pos _).le
        _ = Real.exp (-((T.S.n k : ℝ) ^ (0.4 : ℝ))) / 4 := by ring
    have hpow := pow_le_pow_left₀ (by positivity) hbase (t + 1)
    have hmass8 :
        (Real.exp (-((T.S.n k : ℝ) ^ (0.4 : ℝ))) / 8) ^ (t + 1) / 2 ≤
          ∑ x ∈ A, S.τ.w x := by
      calc
        _ ≤ (Real.exp (-((T.S.n k : ℝ) ^ (0.4 : ℝ))) / 4) ^ (t + 1) / 2 :=
          div_le_div_of_nonneg_right hpow (by norm_num)
        _ ≤ ∑ x ∈ A, S.τ.w x := hmass
    exact hCost S.τ A (by simpa [n, t] using hmass8)
  exact corr_tail_two_at_k (T.S.n k : ℝ) κ.xs κ.α hn S.τ (S.π l)
    (T.S.E k) c (by simpa [n, t] using hCost') hMeanData (by simpa [t] using ht)
    (by simpa [n, t] using hsample) (by simpa [n, t] using hcontr)
    (fun x y => fv_abs_bound (T.S.E k) c x y)

private theorem inter_tail_two_at_k (κ : CConsts) (T : Stage) (k : ℕ)
    (hD : TwoBudgetDisc T k ((T.S.n k : ℝ) ^ κ.xs)
      (κ.α * T.S.n k) (bstar T k))
    (hn : 1 ≤ (T.S.n k : ℝ))
    (hSmallExp : 2 * Real.exp ((T.S.n k : ℝ) ^ (κ.xs / 4) -
      (T.S.n k : ℝ) ^ κ.xs) ≤ bstar T k ^ 2)
    (hCost : ∀ (S : InterSetting T k (κ.xs / 4)) (l : Fin S.d)
      (A : Finset (Fin (T.S.N k)))
      (hA : 0 < ∑ x ∈ A, S.τ.w x),
      (Real.exp (-((T.S.n k : ℝ) ^ (0.4 : ℝ))) / 8) ^
        (Nat.ceil ((T.S.n k : ℝ) ^ (0.25 : ℝ)) + 1) / 2 ≤
          ∑ x ∈ A, S.τ.w x →
      (T.S.n k : ℝ) ^ (κ.xs / 4) -
        Real.log (∑ x ∈ A, S.τ.w x) ≤ κ.α * T.S.n k)
    (c : Colour) (u : ℕ) (C0 : ℝ) (hC0 : 1 ≤ C0)
    (hSampleExp : (T.S.n k : ℝ) ^ (-(1.67 : ℝ)) ≤
      3 / (10 + 72 * C0 ^ 2))
    (hRatioExp : (T.S.n k : ℝ) ^ (-(0.96 : ℝ)) ≤
      (1 / (24 * 3 ^ u * Real.sqrt (10 + 72 * C0 ^ 2))) *
        (T.S.n k : ℝ) ^ (-(0.905 : ℝ)) )
    (hscale : C0 * bstar T k ≤ 1 / 6)
    (S : InterSetting T k (κ.xs / 4)) (l : Fin S.d)
    (J : Finset (Fin u)) (i₀ i₁ : Fin u)
    (hi₀ : i₀ ∈ J) (hi₁ : i₁ ∈ J) (hi01 : i₀ ≠ i₁)
    (hJ : 2 ≤ J.card) (xs : Fin u → Fin (T.S.N k))
    (hothers : ∀ i ∈ J, i ≠ i₀ → i ≠ i₁ →
      DegGate (T.S.E k) c (S.π l).w C0 (bstar T k) (xs i)) :
    ∑ z, ∑ z',
      (if DegGate (T.S.E k) c (S.π l).w C0 (bstar T k) z ∧
          DegGate (T.S.E k) c (S.π l).w C0 (bstar T k) z' ∧
          (T.S.n k : ℝ) ^ (-(1.03 : ℝ)) <
            |inter (T.S.E k) c (S.π l).w J
              (Function.update (Function.update xs i₀ z) i₁ z')|
       then S.τ.w z * S.τ.w z' else 0) ≤
      Real.exp (-((T.S.n k : ℝ) ^ (0.4 : ℝ))) := by
  classical
  let n : ℝ := T.S.n k
  let t : ℕ := Nat.ceil (n ^ (0.25 : ℝ))
  let δ : ℝ := n ^ (-(1.03 : ℝ))
  let p : ℝ := Real.exp (-(n ^ (0.4 : ℝ)))
  let M : ℝ := 3 ^ u
  let Q : ℝ := 10 + 72 * C0 ^ 2
  let eps : ℝ := Real.sqrt Q * Real.sqrt M * bstar T k
  let B : ℝ := 3 * Real.sqrt M
  let δ' : ℝ := δ / 2
  let p' : ℝ := p / 2
  let π := (S.π l).w
  let Gate (z : Fin (T.S.N k)) :=
    DegGate (T.S.E k) c π C0 (bstar T k) z
  let R := (J.erase i₀).erase i₁
  let H (y : Fin (T.S.N k)) : ℝ :=
    ∏ i ∈ R, acoef (T.S.E k) c π (xs i) y
  let Fplus (y : Fin (T.S.N k)) : ℝ :=
    if 0 ≤ H y then H y else 0
  let Fminus (y : Fin (T.S.N k)) : ℝ :=
    if H y < 0 then -H y else 0
  let gF (F : Fin (T.S.N k) → ℝ) (z y : Fin (T.S.N k)) : ℝ :=
    if Gate z then Real.sqrt (F y) * acoef (T.S.E k) c π z y else 0
  let Kof (F : Fin (T.S.N k) → ℝ) (z z' : Fin (T.S.N k)) : ℝ :=
    ∑ y, π y * gF F z y * gF F z' y
  let Kplus (z z' : Fin (T.S.N k)) : ℝ := Kof Fplus z z'
  let Kminus (z z' : Fin (T.S.N k)) : ℝ := Kof Fminus z z'
  let npos : ℝ := n
  have hnpos : 0 < n := lt_of_lt_of_le (by norm_num) hn
  have hbstar : bstar T k = n ^ (-(0.96 : ℝ)) := by
    dsimp [bstar, n]
    congr 1
    norm_num
  have hMpos : 0 < M := by dsimp [M]; positivity
  have hQpos : 0 < Q := by dsimp [Q]; positivity
  have hQnonneg : 0 ≤ Q := hQpos.le
  have hMnonneg : 0 ≤ M := hMpos.le
  have hBpos : 0 < B := by dsimp [B]; positivity
  have hepsNonneg : 0 ≤ eps :=
    mul_nonneg (mul_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _))
      (le_of_lt (Real.rpow_pos_of_pos hnpos _))
  have hδpos : 0 < δ := by dsimp [δ]; exact Real.rpow_pos_of_pos hnpos _
  have hp : 0 < p := by dsimp [p]; positivity
  have hp1 : p ≤ 1 := by
    dsimp [p]
    apply Real.exp_le_one_iff.mpr
    exact neg_nonpos.mpr (Real.rpow_nonneg (by linarith) _)
  have hp' : 0 < p' := by dsimp [p']; positivity
  have hp'1 : p' ≤ 1 := by dsimp [p']; nlinarith [hp1]
  have hδ' : 0 < δ' := by dsimp [δ']; positivity
  have hDlo (z : Fin (T.S.N k)) (hz : Gate z) :
      (1 / 3 : ℝ) ≤ deg (T.S.E k) c π z := by
    change |deg (T.S.E k) c π z - 1 / 2| ≤ C0 * bstar T k at hz
    rw [abs_le] at hz
    nlinarith [hscale, hz.1, hz.2]
  have hRcard : R.card ≤ u := by
    have hle : R.card ≤ Fintype.card (Fin u) := Finset.card_le_univ R
    simpa using hle
  have hfactor (i : Fin u) (hi : i ∈ R) (y : Fin (T.S.N k)) :
      |acoef (T.S.E k) c π (xs i) y| ≤ 3 := by
    rcases Finset.mem_erase.mp hi with ⟨hi₁, hiRest⟩
    rcases Finset.mem_erase.mp hiRest with ⟨hi₀, hiJ⟩
    have hgi := hothers i hiJ hi₀ hi₁
    exact acoef_abs_le_three_of_degree (T.S.E k) c π (xs i) y
      (hDlo (xs i) hgi)
  have hHbound (y : Fin (T.S.N k)) : |H y| ≤ M := by
    dsimp [H, M]
    rw [Finset.abs_prod]
    calc
      ∏ i ∈ R, |acoef (T.S.E k) c π (xs i) y| ≤
          ∏ i ∈ R, (3 : ℝ) :=
        Finset.prod_le_prod₀ (fun i hi => abs_nonneg _)
          (fun i hi => hfactor i hi y)
      _ = (3 : ℝ) ^ R.card := by simp
      _ ≤ (3 : ℝ) ^ u := pow_le_pow_right₀ (by norm_num) hRcard
  have hFplusNonneg (y : Fin (T.S.N k)) : 0 ≤ Fplus y := by
    dsimp [Fplus]
    split_ifs <;> linarith
  have hFminusNonneg (y : Fin (T.S.N k)) : 0 ≤ Fminus y := by
    dsimp [Fminus]
    split_ifs with h
    · linarith [h]
    · exact le_rfl
  have hFplusBound (y : Fin (T.S.N k)) : Fplus y ≤ M := by
    dsimp [Fplus]
    split_ifs with h
    · exact (le_abs_self (H y)).trans (hHbound y)
    · exact le_trans (by norm_num) hMnonneg
  have hFminusBound (y : Fin (T.S.N k)) : Fminus y ≤ M := by
    dsimp [Fminus]
    split_ifs with h
    · have hh := hHbound y
      rw [abs_of_neg h] at hh
      exact hh
    · exact le_trans (by norm_num) hMnonneg
  have hFsplit (y : Fin (T.S.N k)) : H y = Fplus y - Fminus y := by
    by_cases h : 0 ≤ H y
    · simp [Fplus, Fminus, h, not_lt_of_ge h]
    · have h' : H y < 0 := lt_of_not_ge h
      simp [Fplus, Fminus, h, h']
  have hsqrtM : Real.sqrt M > 0 := Real.sqrt_pos.mpr hMpos
  have hsqrtQ : Real.sqrt Q > 0 := Real.sqrt_pos.mpr hQpos
  have hBbound (F : Fin (T.S.N k) → ℝ)
      (hF0 : ∀ y, 0 ≤ F y) (hFM : ∀ y, F y ≤ M)
      (z y : Fin (T.S.N k)) : |gF F z y| ≤ B := by
    by_cases hz : Gate z
    · have hsqrtF : Real.sqrt (F y) ≤ Real.sqrt M := Real.sqrt_le_sqrt (hFM y)
      have hacoef := acoef_abs_le_three_of_degree (T.S.E k) c π z y (hDlo z hz)
      have hg : gF F z y = Real.sqrt (F y) * acoef (T.S.E k) c π z y := by
        simp [gF, hz]
      rw [hg, abs_mul, abs_of_nonneg (Real.sqrt_nonneg _)]
      calc
        Real.sqrt (F y) * |acoef (T.S.E k) c π z y| ≤ Real.sqrt M * 3 :=
          mul_le_mul hsqrtF hacoef (abs_nonneg _) (by norm_num)
        _ = B := by dsimp [B]; ring
    · simp [gF, hz, B]
  have hKsym (F : Fin (T.S.N k) → ℝ) (z z' : Fin (T.S.N k)) :
      (∑ y, π y * gF F z y * gF F z' y) =
        (∑ y, π y * gF F z' y * gF F z y) := by
    apply Finset.sum_congr rfl
    intro y hy
    ring
  have hKcorr (F : Fin (T.S.N k) → ℝ) (hF0 : ∀ y, 0 ≤ F y)
      (z z' : Fin (T.S.N k)) (hz : Gate z) (hz' : Gate z') :
      Kof F z z' =
        ∑ y, π y * F y * acoef (T.S.E k) c π z y * acoef (T.S.E k) c π z' y := by
    dsimp [Kof]
    apply Finset.sum_congr rfl
    intro y hy
    have hgz : gF F z y = Real.sqrt (F y) * acoef (T.S.E k) c π z y := by
      simp [gF, hz]
    have hgz' : gF F z' y = Real.sqrt (F y) * acoef (T.S.E k) c π z' y := by
      simp [gF, hz']
    calc
      π y * gF F z y * gF F z' y =
          π y * (Real.sqrt (F y) * acoef (T.S.E k) c π z y) *
            (Real.sqrt (F y) * acoef (T.S.E k) c π z' y) := by rw [hgz, hgz']
      _ =
        π y * (Real.sqrt (F y)) ^ 2 * acoef (T.S.E k) c π z y *
          acoef (T.S.E k) c π z' y := by ring
      _ = π y * F y * acoef (T.S.E k) c π z y *
          acoef (T.S.E k) c π z' y := by rw [Real.sq_sqrt (hF0 y)]
  have hMeanFor (F : Fin (T.S.N k) → ℝ)
      (hF0 : ∀ y, 0 ≤ F y) (hFM : ∀ y, F y ≤ M) :
      ∀ (A : Finset (Fin (T.S.N k)))
        (hA : 0 < ∑ x ∈ A, S.τ.w x),
        (p' / 4) ^ (t + 1) / 2 ≤ ∑ x ∈ A, S.τ.w x →
        (∀ x ∈ A, Gate x) →
        ∑ y, π y *
          (∑ x, (S.τ.restrict A hA).w x * gF F x y) ^ 2 ≤ eps ^ 2 := by
    intro A hA hmass hAactive
    have hbase : p' / 4 = Real.exp (-(n ^ (0.4 : ℝ))) / 8 := by
      dsimp [p', p]
      ring
    have hcost := hCost S l A hA (by simpa [hbase, n, t] using hmass)
    have hwidth0 := Law.cond_widthLE S.τ A hA S.τ_width
    have hwidth : (S.τ.restrict A hA).WidthLE (κ.α * T.S.n k) := by
      intro x
      have hcost' : (T.S.n k : ℝ) ^ (κ.xs / 4) +
          Real.log (1 / ∑ x ∈ A, S.τ.w x) ≤ κ.α * T.S.n k := by
        simpa [Real.log_inv] using hcost
      calc
        (S.τ.restrict A hA).w x ≤
            Real.exp ((T.S.n k : ℝ) ^ (κ.xs / 4) +
              Real.log (1 / ∑ x ∈ A, S.τ.w x)) / T.S.N k := hwidth0 x
        _ ≤ Real.exp (κ.α * T.S.n k) / T.S.N k :=
          div_le_div_of_nonneg_right (Real.exp_le_exp.mpr hcost') (by positivity)
    have hσsupp : (S.τ.restrict A hA).SupportedIn (T.X k) := by
      intro x hx
      by_cases hxA : x ∈ A
      · simp [Law.restrict, hxA, S.τ_supp x hx]
      · simp [Law.restrict, hxA]
    have hfv := fv_mean_l2_at_k T κ k hn hD hSmallExp c
      hσsupp hwidth (S.π_supp l) (S.π_width l)
    let σ := S.τ.restrict A hA
    let mA (y : Fin (T.S.N k)) : ℝ := ∑ x, σ.w x * acoef (T.S.E k) c π x y
    let mF (y : Fin (T.S.N k)) : ℝ := ∑ x, σ.w x * fv (T.S.E k) c x y
    have hcloseTerm (x y : Fin (T.S.N k)) :
        |σ.w x * (acoef (T.S.E k) c π x y - fv (T.S.E k) c x y)| ≤
          σ.w x * (6 * C0 * bstar T k) := by
      by_cases hxA : x ∈ A
      · rw [abs_mul, abs_of_nonneg (σ.nonneg x)]
        exact mul_le_mul_of_nonneg_left
          (acoef_fv_close_of_gate (T.S.E k) c π C0 (bstar T k) x y
            (hAactive x hxA) hscale) (σ.nonneg x)
      · have hzero : σ.w x = 0 := by simp [σ, Law.restrict, hxA]
        simp [hzero]
    have hmeanClose (y : Fin (T.S.N k)) :
        |mA y - mF y| ≤ 6 * C0 * bstar T k := by
      have hsum : mA y - mF y =
          ∑ x, σ.w x * (acoef (T.S.E k) c π x y - fv (T.S.E k) c x y) := by
        dsimp [mA, mF]
        rw [← Finset.sum_sub_distrib]
        apply Finset.sum_congr rfl
        intro x hx
        ring
      rw [hsum]
      calc
        |∑ x, σ.w x *
            (acoef (T.S.E k) c π x y - fv (T.S.E k) c x y)| ≤
            ∑ x, |σ.w x *
              (acoef (T.S.E k) c π x y - fv (T.S.E k) c x y)| :=
          Finset.abs_sum_le_sum_abs _ _
        _ ≤ ∑ x, σ.w x * (6 * C0 * bstar T k) :=
          Finset.sum_le_sum (fun x hx => hcloseTerm x y)
        _ = 6 * C0 * bstar T k := by
          rw [← Finset.sum_mul, σ.sum_eq_one]
          ring
    have hmeanSq (y : Fin (T.S.N k)) :
        mA y ^ 2 ≤ 2 * mF y ^ 2 + 2 * (6 * C0 * bstar T k) ^ 2 := by
      let e : ℝ := mA y - mF y
      have he := hmeanClose y
      have he' : |e| ≤ 6 * C0 * bstar T k := by simpa [e] using he
      have habs := abs_le.mp he'
      have heSq : e ^ 2 ≤ (6 * C0 * bstar T k) ^ 2 := by
        nlinarith [sq_nonneg (e - 6 * C0 * bstar T k),
          sq_nonneg (e + 6 * C0 * bstar T k), habs.1, habs.2]
      have heq : mA y = mF y + e := by dsimp [e]; ring
      rw [heq]
      nlinarith [sq_nonneg (mF y - e), heSq]
    have hmeanA :
        ∑ y, π y * mA y ^ 2 ≤ Q * bstar T k ^ 2 := by
      calc
        ∑ y, π y * mA y ^ 2 ≤
            ∑ y, π y * (2 * mF y ^ 2 + 2 * (6 * C0 * bstar T k) ^ 2) := by
          apply Finset.sum_le_sum
          intro y hy
          exact mul_le_mul_of_nonneg_left (hmeanSq y) ((S.π l).nonneg y)
        _ = 2 * (∑ y, π y * mF y ^ 2) + 2 * (6 * C0 * bstar T k) ^ 2 := by
          calc
            ∑ y, π y * (2 * mF y ^ 2 + 2 * (6 * C0 * bstar T k) ^ 2) =
                ∑ y, (2 * (π y * mF y ^ 2) +
                  π y * (2 * (6 * C0 * bstar T k) ^ 2)) := by
              apply Finset.sum_congr rfl
              intro y hy
              ring
            _ = 2 * (∑ y, π y * mF y ^ 2) +
                (∑ y, π y * (2 * (6 * C0 * bstar T k) ^ 2)) := by
              rw [Finset.sum_add_distrib, ← Finset.mul_sum]
            _ = 2 * (∑ y, π y * mF y ^ 2) +
                2 * (6 * C0 * bstar T k) ^ 2 := by
              rw [← Finset.sum_mul, (S.π l).sum_eq_one]
              ring
        _ ≤ 2 * (5 * bstar T k ^ 2) +
            2 * (6 * C0 * bstar T k) ^ 2 := by
          have hfv' : ∑ y, π y * mF y ^ 2 ≤ 5 * bstar T k ^ 2 := by
            simpa [σ, mF] using hfv
          exact add_le_add (mul_le_mul_of_nonneg_left hfv' (by norm_num)) le_rfl
        _ = Q * bstar T k ^ 2 := by dsimp [Q]; ring
    have hmeanG (y : Fin (T.S.N k)) :
        ∑ x, σ.w x * gF F x y = Real.sqrt (F y) * mA y := by
      calc
        ∑ x, σ.w x * gF F x y =
            ∑ x, σ.w x * (Real.sqrt (F y) * acoef (T.S.E k) c π x y) := by
          apply Finset.sum_congr rfl
          intro x hx
          by_cases hxA : x ∈ A
          · simp [gF, hAactive x hxA]
          · have hzero : σ.w x = 0 := by simp [σ, Law.restrict, hxA]
            simp [gF, hxA, hzero]
        _ = Real.sqrt (F y) * mA y := by
          calc
            ∑ x, σ.w x * (Real.sqrt (F y) * acoef (T.S.E k) c π x y) =
                ∑ x, Real.sqrt (F y) * (σ.w x * acoef (T.S.E k) c π x y) := by
              apply Finset.sum_congr rfl
              intro x hx
              ring
            _ = Real.sqrt (F y) * mA y := by
              dsimp [mA]
              rw [← Finset.mul_sum]
    calc
      ∑ y, π y * (∑ x, σ.w x * gF F x y) ^ 2 =
          ∑ y, π y * F y * mA y ^ 2 := by
        apply Finset.sum_congr rfl
        intro y hy
        rw [hmeanG y, mul_pow, Real.sq_sqrt (hF0 y)]
        ring
      _ ≤ ∑ y, π y * M * mA y ^ 2 := by
        apply Finset.sum_le_sum
        intro y hy
        exact mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_left (hFM y) ((S.π l).nonneg y)) (sq_nonneg (mA y))
      _ = M * ∑ y, π y * mA y ^ 2 := by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro y hy
        ring
      _ ≤ M * (Q * bstar T k ^ 2) := mul_le_mul_of_nonneg_left hmeanA hMnonneg
      _ = eps ^ 2 := by
        dsimp [eps]
        calc
          M * (Q * bstar T k ^ 2) =
              (Real.sqrt Q) ^ 2 * (Real.sqrt M) ^ 2 * bstar T k ^ 2 := by
            rw [Real.sq_sqrt hQnonneg, Real.sq_sqrt hMnonneg]
            ring
          _ = (Real.sqrt Q * Real.sqrt M * bstar T k) ^ 2 := by ring
  have hsample : (t : ℝ) * eps ^ 2 ≤ B ^ 2 := by
    have hpow96 : (n ^ (-(0.96 : ℝ))) ^ 2 = n ^ (-(1.92 : ℝ)) := by
      rw [← Real.rpow_natCast (n ^ (-(0.96 : ℝ))) 2,
        ← Real.rpow_mul (by positivity : 0 ≤ n)]
      congr 1
      norm_num
    have hpowSample : n ^ (0.25 : ℝ) * n ^ (-(1.92 : ℝ)) =
        n ^ (-(1.67 : ℝ) : ℝ) := by
      rw [← Real.rpow_add (by positivity : 0 < n)]
      congr 1
      norm_num
    have hepsSq : eps ^ 2 = M * Q * n ^ (-(1.92 : ℝ)) := by
      calc
        eps ^ 2 =
            (Real.sqrt Q) ^ 2 * (Real.sqrt M) ^ 2 * (bstar T k) ^ 2 := by
          dsimp [eps]
          ring
        _ = M * Q * n ^ (-(1.92 : ℝ)) := by
          rw [Real.sq_sqrt hQnonneg, Real.sq_sqrt hMnonneg, hbstar, hpow96]
          ring
    have hBsq : B ^ 2 = 9 * M := by
      calc
        B ^ 2 = 9 * (Real.sqrt M) ^ 2 := by dsimp [B]; ring
        _ = 9 * M := by rw [Real.sq_sqrt hMnonneg]
    calc
      (t : ℝ) * eps ^ 2 ≤ (3 * n ^ (0.25 : ℝ)) * eps ^ 2 :=
        mul_le_mul_of_nonneg_right (by
          have hceil : n ^ (0.25 : ℝ) ≤ (t : ℝ) := by
            dsimp [t]
            exact Nat.le_ceil _
          have hnQuarter : 1 ≤ n ^ (0.25 : ℝ) := by
            calc
              1 = n ^ (0 : ℝ) := by simp
              _ ≤ n ^ (0.25 : ℝ) := Real.rpow_le_rpow_of_exponent_le hn (by norm_num)
          have hceilUpper : (t : ℝ) ≤ 3 * n ^ (0.25 : ℝ) := by
            have htmp : (t : ℝ) < n ^ (0.25 : ℝ) + 1 := by
              dsimp [t]
              exact Nat.ceil_lt_add_one (by positivity)
            linarith [hnQuarter]
          exact hceilUpper) (by positivity)
      _ = 3 * M * Q * n ^ (-(1.67 : ℝ)) := by
        calc
          (3 * n ^ (0.25 : ℝ)) * eps ^ 2 =
              3 * M * Q * (n ^ (0.25 : ℝ) * n ^ (-(1.92 : ℝ))) := by
            rw [hepsSq]
            ring
          _ = 3 * M * Q * n ^ (-(1.67 : ℝ)) := by rw [hpowSample]
      _ ≤ 9 * M := by
        calc
          3 * M * Q * n ^ (-(1.67 : ℝ)) ≤ 3 * M * Q * (3 / Q) :=
            mul_le_mul_of_nonneg_left hSampleExp (by positivity)
          _ = 9 * M := by field_simp [ne_of_gt hQpos]; ring
      _ = B ^ 2 := hBsq.symm
  have hpow125 : (n ^ (0.125 : ℝ)) ^ 2 = n ^ (0.25 : ℝ) := by
    rw [← Real.rpow_natCast (n ^ (0.125 : ℝ)) 2,
      ← Real.rpow_mul (by positivity : 0 ≤ n)]
    congr 1
    norm_num
  have hsqrtLower : n ^ (0.125 : ℝ) ≤ Real.sqrt (t : ℝ) := by
    apply Real.le_sqrt_of_sq_le
    rw [hpow125]
    have hceil : n ^ (0.25 : ℝ) ≤ (t : ℝ) := by
      dsimp [t]
      exact Nat.le_ceil _
    exact hceil
  have hpowRatio : n ^ (-(1.03 : ℝ)) * n ^ (0.125 : ℝ) =
      n ^ (-(0.905 : ℝ)) := by
    rw [← Real.rpow_add (by positivity : 0 < n)]
    congr 1
    norm_num
  have hratio : 12 * M * Real.sqrt Q * n ^ (-(0.96 : ℝ)) <
      n ^ (-(0.905 : ℝ)) := by
    calc
      12 * M * Real.sqrt Q * n ^ (-(0.96 : ℝ)) ≤
          12 * M * Real.sqrt Q *
            ((1 / (24 * M * Real.sqrt Q)) * n ^ (-(0.905 : ℝ))) :=
        mul_le_mul_of_nonneg_left hRatioExp (by positivity)
      _ = (1 / 2) * n ^ (-(0.905 : ℝ)) := by
        field_simp [ne_of_gt hMpos, ne_of_gt hsqrtQ]
        ring
      _ < n ^ (-(0.905 : ℝ)) := by
        calc
          (1 / 2) * n ^ (-(0.905 : ℝ)) <
              1 * n ^ (-(0.905 : ℝ)) :=
            mul_lt_mul_of_pos_right (by norm_num) (Real.rpow_pos_of_pos hnpos _)
          _ = n ^ (-(0.905 : ℝ)) := by ring
  have hfac : 12 * M * Real.sqrt Q * bstar T k < δ * Real.sqrt (t : ℝ) := by
    calc
      12 * M * Real.sqrt Q * bstar T k =
          12 * M * Real.sqrt Q * n ^ (-(0.96 : ℝ)) := by rw [hbstar]
      _ < n ^ (-(0.905 : ℝ)) := hratio
      _ = δ * n ^ (0.125 : ℝ) := by
        dsimp [δ]
        rw [hpowRatio]
      _ ≤ δ * Real.sqrt (t : ℝ) :=
        mul_le_mul_of_nonneg_left hsqrtLower (le_of_lt hδpos)
  have hcontr : (t : ℝ) * δ' >
      2 * eps * B * Real.sqrt (t : ℝ) := by
    have htReal : 0 < (t : ℝ) := by
      have hceil : n ^ (0.25 : ℝ) ≤ (t : ℝ) := by
        dsimp [t]
        exact Nat.le_ceil _
      have hnQuarter : 0 < n ^ (0.25 : ℝ) := Real.rpow_pos_of_pos hnpos _
      linarith
    have hsqrtPos := Real.sqrt_pos.mpr htReal
    have hmul := mul_lt_mul_of_pos_right hfac hsqrtPos
    have hsquare : Real.sqrt (t : ℝ) ^ 2 = (t : ℝ) :=
      Real.sq_sqrt (Nat.cast_nonneg t)
    have hmul' : 12 * M * Real.sqrt Q * bstar T k * Real.sqrt (t : ℝ) <
        δ * (t : ℝ) := by
      calc
        12 * M * Real.sqrt Q * bstar T k * Real.sqrt (t : ℝ) <
            δ * Real.sqrt (t : ℝ) * Real.sqrt (t : ℝ) := hmul
        _ = δ * (Real.sqrt (t : ℝ)) ^ 2 := by ring
        _ = δ * (t : ℝ) := by rw [hsquare]
    have hcoef : 2 * eps * B * Real.sqrt (t : ℝ) =
        6 * M * Real.sqrt Q * bstar T k * Real.sqrt (t : ℝ) := by
      dsimp [eps, B]
      calc
        2 * (Real.sqrt Q * Real.sqrt M * bstar T k) *
            (3 * Real.sqrt M) * Real.sqrt (t : ℝ) =
            6 * Real.sqrt Q * bstar T k * (Real.sqrt M) ^ 2 *
              Real.sqrt (t : ℝ) := by ring
        _ = 6 * M * Real.sqrt Q * bstar T k * Real.sqrt (t : ℝ) := by
          rw [Real.sq_sqrt hMnonneg]
          ring
    rw [hcoef]
    dsimp [δ']
    nlinarith [hmul']
  have hthreshold (z z' : Fin (T.S.N k)) (hz : Gate z) (hz' : Gate z') :
      inter (T.S.E k) c π J (Function.update (Function.update xs i₀ z) i₁ z') =
        Kplus z z' - Kminus z z' := by
    have hprod (y : Fin (T.S.N k)) :
        (∏ i ∈ J,
          acoef (T.S.E k) c π (Function.update (Function.update xs i₀ z) i₁ z' i) y) =
          H y * acoef (T.S.E k) c π z y * acoef (T.S.E k) c π z' y := by
      have hupdate (i : Fin u) (hi : i ∈ R) :
          Function.update (Function.update xs i₀ z) i₁ z' i = xs i := by
        rcases Finset.mem_erase.mp hi with ⟨hine₁, hiRest⟩
        rcases Finset.mem_erase.mp hiRest with ⟨hine₀, _⟩
        rw [Function.update_of_ne hine₁, Function.update_of_ne hine₀]
      have hi₁' : i₁ ∈ J.erase i₀ := Finset.mem_erase.mpr ⟨Ne.symm hi01, hi₁⟩
      rw [← Finset.prod_erase_mul J
        (fun i => acoef (T.S.E k) c π
          (Function.update (Function.update xs i₀ z) i₁ z' i) y) hi₀]
      rw [← Finset.prod_erase_mul (J.erase i₀)
        (fun i => acoef (T.S.E k) c π
          (Function.update (Function.update xs i₀ z) i₁ z' i) y) hi₁']
      have hrest :
          ∏ i ∈ R,
            acoef (T.S.E k) c π
              (Function.update (Function.update xs i₀ z) i₁ z' i) y = H y := by
        dsimp [H]
        apply Finset.prod_congr rfl
        intro i hi
        rw [hupdate i hi]
      have hAt₁ : Function.update (Function.update xs i₀ z) i₁ z' i₁ = z' := by
        simp
      have hAt₀ : Function.update (Function.update xs i₀ z) i₁ z' i₀ = z := by
        rw [Function.update_of_ne hi01, Function.update_self]
      rw [hrest, hAt₁, hAt₀]
      ring
    have hinter : inter (T.S.E k) c π J
        (Function.update (Function.update xs i₀ z) i₁ z') =
        ∑ y, π y * H y * acoef (T.S.E k) c π z y * acoef (T.S.E k) c π z' y := by
      unfold inter
      apply Finset.sum_congr rfl
      intro y hy
      rw [hprod y]
      ring
    calc
      inter (T.S.E k) c π J (Function.update (Function.update xs i₀ z) i₁ z') =
          ∑ y, π y * H y * acoef (T.S.E k) c π z y * acoef (T.S.E k) c π z' y := hinter
      _ = ∑ y,
          (π y * Fplus y * acoef (T.S.E k) c π z y * acoef (T.S.E k) c π z' y -
            π y * Fminus y * acoef (T.S.E k) c π z y * acoef (T.S.E k) c π z' y) := by
        apply Finset.sum_congr rfl
        intro y hy
        rw [hFsplit y]
        ring
      _ = (∑ y, π y * Fplus y * acoef (T.S.E k) c π z y *
              acoef (T.S.E k) c π z' y) -
            (∑ y, π y * Fminus y * acoef (T.S.E k) c π z y *
              acoef (T.S.E k) c π z' y) := by
        rw [Finset.sum_sub_distrib]
      _ = Kplus z z' - Kminus z z' := by
        rw [← hKcorr Fplus hFplusNonneg z z' hz hz',
          ← hKcorr Fminus hFminusNonneg z z' hz hz']
  have hkernelBound (F : Fin (T.S.N k) → ℝ)
      (hF0 : ∀ y, 0 ≤ F y) (hFM : ∀ y, F y ≤ M) :
      ∑ z, ∑ z',
        (if δ' < |Kof F z z'| then S.τ.w z * S.τ.w z' else 0) ≤ p' := by
    have hKsymF (z z' : Fin (T.S.N k)) :
        (∑ y, π y * gF F z y * gF F z' y) =
          (∑ y, π y * gF F z' y * gF F z y) := by
      apply Finset.sum_congr rfl
      intro y hy
      ring
    have hMeanF : ∀ (A : Finset (Fin (T.S.N k)))
        (hA : 0 < ∑ x ∈ A, S.τ.w x),
        (p' / 4) ^ (t + 1) / 2 ≤ ∑ x ∈ A, S.τ.w x →
        (∀ x ∈ A, Gate x) →
        ∑ y, π y * (∑ x, (S.τ.restrict A hA).w x * gF F x y) ^ 2 ≤ eps ^ 2 :=
      hMeanFor F hF0 hFM
    have hBoundFor := hBbound F hF0 hFM
    have h := pair_tail_from_mean S.τ (S.π l) (gF F) δ' p' eps B t
      Gate (by intro z hz y; simp [gF, hz]) hδ' hp' hp'1 hBpos
      hBoundFor hepsNonneg hsample (by
        have hnQuarter : 1 ≤ n ^ (0.25 : ℝ) := by
          calc
            1 = n ^ (0 : ℝ) := by simp
            _ ≤ n ^ (0.25 : ℝ) := Real.rpow_le_rpow_of_exponent_le hn (by norm_num)
        have htLower : n ^ (0.25 : ℝ) ≤ (t : ℝ) := by
          dsimp [t]
          exact Nat.le_ceil _
        have htpos : 0 < t := by exact_mod_cast (show 0 < (t : ℝ) by linarith)
        exact htpos) hcontr hKsymF hMeanF
    simpa [Kof, gF] using h
  have hplusTail :
      ∑ z, ∑ z',
        (if δ' < |Kplus z z'| then S.τ.w z * S.τ.w z' else 0) ≤ p' := by
    simpa [Kplus] using hkernelBound Fplus hFplusNonneg hFplusBound
  have hminusTail :
      ∑ z, ∑ z',
        (if δ' < |Kminus z z'| then S.τ.w z * S.τ.w z' else 0) ≤ p' := by
    simpa [Kminus] using hkernelBound Fminus hFminusNonneg hFminusBound
  have hpoint (z z' : Fin (T.S.N k)) :
      (if Gate z ∧ Gate z' ∧ δ <
          |inter (T.S.E k) c π J
            (Function.update (Function.update xs i₀ z) i₁ z')|
       then S.τ.w z * S.τ.w z' else 0) ≤
        (if δ' < |Kplus z z'| then S.τ.w z * S.τ.w z' else 0) +
        (if δ' < |Kminus z z'| then S.τ.w z * S.τ.w z' else 0) := by
    by_cases he : Gate z ∧ Gate z' ∧ δ <
        |inter (T.S.E k) c π J (Function.update (Function.update xs i₀ z) i₁ z')|
    · have hsum := abs_sub (Kplus z z') (Kminus z z')
      have hlarge : δ' < |Kplus z z'| ∨ δ' < |Kminus z z'| := by
        by_contra hnone
        push_neg at hnone
        have hsumle : |Kplus z z'| + |Kminus z z'| ≤ δ := by
          dsimp [δ'] at hnone
          linarith
        have hinter := he.2.2
        rw [hthreshold z z' he.1 he.2.1] at hinter
        linarith
      have hw : 0 ≤ S.τ.w z * S.τ.w z' :=
        mul_nonneg (S.τ.nonneg z) (S.τ.nonneg z')
      rcases hlarge with hp | hm
      · simp [he, hp]
        positivity
      · simp [he, hm]
        positivity
    · have hw : 0 ≤ S.τ.w z * S.τ.w z' :=
        mul_nonneg (S.τ.nonneg z) (S.τ.nonneg z')
      simp [he]
      positivity
  have hwhole :
      (∑ z, ∑ z',
        (if Gate z ∧ Gate z' ∧ δ <
            |inter (T.S.E k) c π J
              (Function.update (Function.update xs i₀ z) i₁ z')|
         then S.τ.w z * S.τ.w z' else 0)) ≤
        (∑ z, ∑ z',
          (if δ' < |Kplus z z'| then S.τ.w z * S.τ.w z' else 0)) +
        (∑ z, ∑ z',
          (if δ' < |Kminus z z'| then S.τ.w z * S.τ.w z' else 0)) := by
    calc
      _ ≤ ∑ z, ∑ z',
          ((if δ' < |Kplus z z'| then S.τ.w z * S.τ.w z' else 0) +
            (if δ' < |Kminus z z'| then S.τ.w z * S.τ.w z' else 0)) := by
        apply Finset.sum_le_sum
        intro z hz
        apply Finset.sum_le_sum
        intro z' hz'
        exact hpoint z z'
      _ = _ := by simp_rw [Finset.sum_add_distrib]
  calc
    _ ≤ (∑ z, ∑ z',
        (if δ' < |Kplus z z'| then S.τ.w z * S.τ.w z' else 0)) +
      (∑ z, ∑ z',
        (if δ' < |Kminus z z'| then S.τ.w z * S.τ.w z' else 0)) := hwhole
    _ ≤ p' + p' := add_le_add hplusTail hminusTail
    _ = Real.exp (-((T.S.n k : ℝ) ^ (0.4 : ℝ))) := by dsimp [p', p, n]; ring

theorem prove_inter_tail_two (κ : CConsts) (hκ : κ.Admissible) (T : Stage)
    (hDeep : DeepDisc T κ.xs κ.α 0.04) (c : Colour) (u : ℕ)
    (C0 : ℝ) (hC0 : 1 ≤ C0) :
    ∀ᶠ k in atTop,
      ∀ (S : InterSetting T k (κ.xs / 4)) (l : Fin S.d)
        (J : Finset (Fin u)) (i₀ i₁ : Fin u),
        i₀ ∈ J → i₁ ∈ J → i₀ ≠ i₁ → 2 ≤ J.card →
        ∀ xs : Fin u → Fin (T.S.N k),
          (∀ i ∈ J, i ≠ i₀ → i ≠ i₁ →
            DegGate (T.S.E k) c (S.π l).w C0 (bstar T k) (xs i)) →
          ∑ z, ∑ z',
            (if DegGate (T.S.E k) c (S.π l).w C0 (bstar T k) z ∧
                DegGate (T.S.E k) c (S.π l).w C0 (bstar T k) z' ∧
                (T.S.n k : ℝ) ^ (-(1.03 : ℝ)) <
                  |inter (T.S.E k) c (S.π l).w J
                    (Function.update (Function.update xs i₀ z) i₁ z')|
             then S.τ.w z * S.τ.w z' else 0) ≤
            Real.exp (-((T.S.n k : ℝ) ^ (0.4 : ℝ))) := by
  have hx : 0 < κ.xs := hκ.xs_rng.1
  have hSmallExp := eventually_small_exp_vs_bstar T κ hx
  have hCost := eventually_conditioning_cost T κ hκ
  have hn : ∀ᶠ k in atTop, 1 ≤ (T.S.n k : ℝ) :=
    tendsto_stage_n_real T |>.eventually (eventually_ge_atTop (1 : ℝ))
  let Qc : ℝ := 10 + 72 * C0 ^ 2
  have hSampleExp := eventually_rpow_le_mul T (p := -(1.67 : ℝ))
    (q := 0) (c := 3 / Qc) (by norm_num) (by positivity)
  have hRatioExp := eventually_rpow_le_mul T (p := -(0.96 : ℝ))
    (q := -(0.905 : ℝ))
    (c := 1 / (24 * 3 ^ u * Real.sqrt Qc)) (by norm_num) (by positivity)
  have hscale : ∀ᶠ k in atTop, C0 * bstar T k ≤ 1 / 6 := by
    have hpNeg : (-1 + (0.04 : ℝ)) < 0 := by norm_num
    have hs := eventually_rpow_le_mul T (p := -1 + (0.04 : ℝ))
      (q := 0) (c := 1 / (6 * C0)) hpNeg (by positivity)
    filter_upwards [hs, hn] with k hs hk
    have hmul := mul_le_mul_of_nonneg_left hs (by linarith : 0 ≤ C0)
    have hpow : (T.S.n k : ℝ) ^ (-1 + (0.04 : ℝ)) = bstar T k := rfl
    rw [Real.rpow_zero, hpow] at hmul
    have hmul' : C0 * bstar T k ≤ C0 * (1 / (6 * C0)) := by
      simpa [hpow] using hmul
    calc
      C0 * bstar T k ≤ C0 * (1 / (6 * C0)) := hmul'
      _ = 1 / 6 := by field_simp [ne_of_gt (by linarith : 0 < C0)]
  filter_upwards [hDeep, hSmallExp, hCost, hn, hSampleExp, hRatioExp, hscale]
    with k hD hSmallExp hCost hn hSampleExp hRatioExp hscale
  let n : ℝ := T.S.n k
  let t : ℕ := Nat.ceil (n ^ (0.25 : ℝ))
  have hCost' : ∀ (S : InterSetting T k (κ.xs / 4)) (l : Fin S.d)
      (A : Finset (Fin (T.S.N k)))
      (hA : 0 < ∑ x ∈ A, S.τ.w x),
      (Real.exp (-(n ^ (0.4 : ℝ))) / 8) ^ (t + 1) / 2 ≤
        ∑ x ∈ A, S.τ.w x →
      n ^ (κ.xs / 4) - Real.log (∑ x ∈ A, S.τ.w x) ≤ κ.α * n := by
    intro S l A hA hmass
    exact hCost S.τ A (by simpa [n, t] using hmass)
  have hSampleExp' : n ^ (-(1.67 : ℝ)) ≤ 3 / (10 + 72 * C0 ^ 2) := by
    simpa [n, Qc] using hSampleExp
  have hRatioExp' : n ^ (-(0.96 : ℝ)) ≤
      (1 / (24 * 3 ^ u * Real.sqrt (10 + 72 * C0 ^ 2))) *
        n ^ (-(0.905 : ℝ)) := by
    simpa [n, Qc] using hRatioExp
  intro S l J i₀ i₁ hi₀ hi₁ hi01 hJ xs hothers
  exact inter_tail_two_at_k κ T k hD hn hSmallExp hCost' c u C0 hC0
    hSampleExp' hRatioExp' hscale S l J i₀ i₁ hi₀ hi₁ hi01 hJ xs hothers

theorem prove_inter_mean (κ : CConsts) (hκ : κ.Admissible) (T : Stage)
    (hDeep : DeepDisc T κ.xs κ.α 0.04) (c : Colour) (u : ℕ)
    (C0 : ℝ) (hC0 : 1 ≤ C0) :
    ∀ᶠ k in atTop,
      ∀ (S : InterSetting T k (κ.xs / 4)) (l : Fin S.d)
        (J : Finset (Fin u)),
        2 ≤ J.card → J.card ≤ u → S.DegOK c C0 →
        ∑ xs : Fin u → Fin (T.S.N k),
          prodW S.τ.w xs * |inter (T.S.E k) c (S.π l).w J xs| ≤
            (T.S.n k : ℝ) ^ (-0.4 * (J.card : ℝ)) := by
  have hx : 0 < κ.xs := hκ.xs_rng.1
  have hα : 0 < κ.α := hκ.α_rng.1
  have hpGap : κ.xs / 4 < κ.xs := by linarith
  have hgap := eventually_rpow_le_mul T hpGap (by norm_num : (0 : ℝ) < 1 / 2)
  have hpLinear : κ.xs / 4 < 1 := by nlinarith [hκ.xs_rng.2]
  have hwidth := eventually_rpow_le_mul T hpLinear (by positivity : 0 < κ.α / 3)
  have hexp := eventually_exp_linear_ge T (a := κ.α / 3) (C := 6)
    (by positivity : 0 < κ.α / 3)
  have hlarge := eventually_rpow_ge T (q := κ.xs) (C := 6) hx
  have hn : ∀ᶠ k in atTop, 1 ≤ (T.S.n k : ℝ) :=
    tendsto_stage_n_real T |>.eventually (eventually_ge_atTop (1 : ℝ))
  have hgate : ∀ᶠ k in atTop, C0 * bstar T k ≤ 1 / 6 := by
    have hs := eventually_rpow_le_mul T (p := -1 + (0.04 : ℝ))
      (q := 0) (c := 1 / (6 * C0)) (by norm_num) (by positivity)
    filter_upwards [hs, hn] with k hs hk
    have hmul := mul_le_mul_of_nonneg_left hs (by linarith : 0 ≤ C0)
    have hpow : (T.S.n k : ℝ) ^ (-1 + (0.04 : ℝ)) = bstar T k := rfl
    rw [Real.rpow_zero, hpow] at hmul
    calc
      C0 * bstar T k ≤ C0 * (1 / (6 * C0)) := by simpa using hmul
      _ = 1 / 6 := by field_simp [ne_of_gt (by linarith : 0 < C0)]
  let K : ℝ := 100 * (C0 + 1)
  have hK : ∀ᶠ k in atTop,
      100 * (C0 + 1) * bstar T k ≤ (T.S.n k : ℝ) ^ (-(0.9 : ℝ)) := by
    have hconstant : 0 < K := by dsimp [K]; positivity
    have hp : (-1 + (0.04 : ℝ)) < -(0.9 : ℝ) := by norm_num
    have hs := eventually_rpow_le_mul T (p := -1 + (0.04 : ℝ))
      (q := -(0.9 : ℝ)) (c := 1 / K) hp (by positivity)
    filter_upwards [hs] with k hs
    have hmul := mul_le_mul_of_nonneg_left hs (le_of_lt hconstant)
    have hpow : (T.S.n k : ℝ) ^ (-1 + (0.04 : ℝ)) = bstar T k := rfl
    calc
      K * bstar T k ≤ K * ((1 / K) * (T.S.n k : ℝ) ^ (-(0.9 : ℝ))) := by
        simpa [hpow] using hmul
      _ = (T.S.n k : ℝ) ^ (-(0.9 : ℝ)) := by
        have hcancel : K * (1 / K) = 1 := by field_simp [ne_of_gt hconstant]
        calc
          K * ((1 / K) * (T.S.n k : ℝ) ^ (-(0.9 : ℝ))) =
              (K * (1 / K)) * (T.S.n k : ℝ) ^ (-(0.9 : ℝ)) := by ring
          _ = (T.S.n k : ℝ) ^ (-(0.9 : ℝ)) := by rw [hcancel, one_mul]
  have hhalf : ∀ᶠ k in atTop,
      (T.S.n k : ℝ) ^ (-(0.2 : ℝ)) ≤ 1 / 2 := by
    have hs := eventually_rpow_le_mul T (p := -(0.2 : ℝ))
      (q := 0) (c := 1 / 2) (by norm_num) (by norm_num)
    filter_upwards [hs] with k hk
    simpa [Real.rpow_zero] using hk
  have hpoly : ∀ᶠ k in atTop,
      6 * 9 ^ u * (T.S.n k : ℝ) ^ (0.8 * (u : ℝ)) *
        Real.exp (-(2 * κ.α * T.S.n k / 3)) ≤ 1 / 2 := by
    have ha : 0 < 2 * κ.α / 3 := by positivity
    have hlim := (tendsto_rpow_mul_exp_neg_mul_atTop_nhds_zero
      (0.8 * (u : ℝ)) (2 * κ.α / 3) ha).comp (tendsto_stage_n_real T)
    have hc : 0 < 1 / (12 * (9 : ℝ) ^ u) := by positivity
    have hs := hlim.eventually (gt_mem_nhds hc)
    filter_upwards [hs] with k hk
    have hmul := mul_le_mul_of_nonneg_left (le_of_lt hk)
      (by positivity : 0 ≤ 6 * (9 : ℝ) ^ u)
    have heq : 6 * (9 : ℝ) ^ u * (1 / (12 * (9 : ℝ) ^ u)) = 1 / 2 := by
      field_simp [ne_of_gt (by positivity : 0 < (9 : ℝ) ^ u)] <;> norm_num
    have hexpArg : -(2 * κ.α * T.S.n k / 3) =
        -((2 * κ.α / 3) * (T.S.n k : ℝ)) := by ring
    have hexpEq : Real.exp (-(2 * κ.α * T.S.n k / 3)) =
        Real.exp (-((2 * κ.α / 3) * (T.S.n k : ℝ))) := by rw [hexpArg]
    calc
      6 * 9 ^ u * (T.S.n k : ℝ) ^ (0.8 * (u : ℝ)) *
          Real.exp (-(2 * κ.α * T.S.n k / 3)) ≤
      6 * (9 : ℝ) ^ u * ((T.S.n k : ℝ) ^ (0.8 * (u : ℝ)) *
            Real.exp (-((2 * κ.α / 3) * (T.S.n k : ℝ)))) := by
        rw [hexpEq]
        exact le_of_eq (by ring)
      _ ≤ 1 / 2 := by
        calc
          6 * (9 : ℝ) ^ u * ((T.S.n k : ℝ) ^ (0.8 * (u : ℝ)) *
              Real.exp (-((2 * κ.α / 3) * (T.S.n k : ℝ)))) ≤
              6 * (9 : ℝ) ^ u *
                ((T.S.n k : ℝ) ^ (0.8 * (u : ℝ)) *
                  Real.exp (-((2 * κ.α / 3) * (T.S.n k : ℝ)))) := le_rfl
          _ ≤ 6 * (9 : ℝ) ^ u * (1 / (12 * (9 : ℝ) ^ u)) := by
            simpa [mul_assoc] using hmul
          _ = 1 / 2 := heq
  filter_upwards [hDeep, hgap, hwidth, hexp, hlarge, hn, hgate, hK, hhalf, hpoly]
    with k hD hgap hwidth hexp hlarge hn hgate hK hhalf hpoly
  have hgap' : (T.S.n k : ℝ) ^ (κ.xs / 4) ≤
      (T.S.n k : ℝ) ^ κ.xs / 2 := by
    convert hgap using 1 <;> ring
  have hwidth' : (T.S.n k : ℝ) ^ (κ.xs / 4) ≤
      κ.α * T.S.n k / 3 := by
    rw [Real.rpow_one] at hwidth
    convert hwidth using 1 <;> ring
  have hexp' : 6 ≤ Real.exp (κ.α * T.S.n k / 3) := by
    convert hexp using 1 <;> ring
  intro S l J hJ hJu hDegOK
  exact inter_mean_at_k κ hκ T k hD hn hgap' hwidth' hexp' hlarge
    c u C0 hC0 hgate hK hhalf hpoly S l hDegOK J hJ hJu

end HypercubeRamsey.Lane_q_s12_tails
