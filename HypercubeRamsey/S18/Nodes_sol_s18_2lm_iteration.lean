import HypercubeRamsey.S18.Nodes_sol_s18_2lm_blocks

namespace HypercubeRamsey.S18.Lane_sol_s18_2lm

open Classical Filter
open scoped BigOperators

set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 400000

variable {κ : CConsts} {T : Stage} {k : ℕ} {PT : ProfiledTiling κ T k}
  {hPT : PT.Valid} {D : LateData hPT} {X : CriticalTransferData D}

/-- The exceptional squared multiplier costs only an exponential in the
size of its responding block. -/
theorem crude_multiplier_square (m : ℕ) :
    (2 / (0.15 : ℝ) ^ m + 1) ^ 2 ≤
      Real.exp ((Real.log 9 - 2 * Real.log (0.15 : ℝ)) * (m + 1 : ℝ)) := by
  have ha : 0 < (0.15 : ℝ) ^ m := pow_pos (by norm_num) _
  have ha1 : (0.15 : ℝ) ^ m ≤ 1 := pow_le_one₀ (by norm_num) (by norm_num)
  have hsum : 2 / (0.15 : ℝ) ^ m + 1 ≤ 3 / (0.15 : ℝ) ^ m := by
    apply (le_div_iff₀ ha).mpr
    have hmul : (2 / (0.15 : ℝ) ^ m) * (0.15 : ℝ) ^ m = 2 := div_mul_cancel₀ _ ha.ne'
    nlinarith
  have hsq : (2 / (0.15 : ℝ) ^ m + 1) ^ 2 ≤ (3 / (0.15 : ℝ) ^ m) ^ 2 := by
    have hnon : 0 ≤ 2 / (0.15 : ℝ) ^ m + 1 := by positivity
    nlinarith only [hsum, hnon]
  have hexact : (3 / (0.15 : ℝ) ^ m) ^ 2 =
      Real.exp (Real.log 9 - 2 * (m : ℝ) * Real.log (0.15 : ℝ)) := by
    rw [Real.exp_sub, Real.exp_log (by norm_num : (0 : ℝ) < 9)]
    have hp : Real.exp (2 * (m : ℝ) * Real.log (0.15 : ℝ)) = ((0.15 : ℝ) ^ m) ^ 2 := by
      rw [show 2 * (m : ℝ) * Real.log (0.15 : ℝ) =
        ((2 * m : ℕ) : ℝ) * Real.log (0.15 : ℝ) by push_cast; ring,
        mul_comm (((2 * m : ℕ) : ℝ)) (Real.log (0.15 : ℝ)),
        ← Real.rpow_def_of_pos (by norm_num : (0 : ℝ) < 0.15), Real.rpow_natCast]
      rw [mul_comm 2 m, pow_mul]
    rw [hp, div_pow]
    norm_num
  rw [hexact] at hsq
  have hl9 : 0 ≤ Real.log 9 := Real.log_nonneg (by norm_num)
  have hl15 : Real.log (0.15 : ℝ) ≤ 0 := Real.log_nonpos (by norm_num) (by norm_num)
  have hnon : 0 ≤ (m : ℝ) * Real.log 9 := mul_nonneg (Nat.cast_nonneg m) hl9
  exact hsq.trans (Real.exp_le_exp.mpr (by nlinarith only [hnon, hl15]))

/-- The exceptional contribution to the finite iteration tends to zero
uniformly over the actual low-mode block size. -/
theorem exceptional_budget_eventually (hκ : κ.Admissible) (T : Stage)
    (c d : ℝ) (hc : 0 < c) (hcd : c < d) :
    ∀ᶠ k in atTop, ∀ PT : ProfiledTiling κ T k, ∀ hPT : PT.Valid, ∀ D : LateData hPT,
      ∀ i : Fin PT.tiling.m,
      (T.S.n k : ℝ) * Real.log (T.S.n k : ℝ) ^ 20 *
        (Real.exp (Real.rpow (T.S.n k : ℝ) c) ^ 2 *
          (2 / (0.15 : ℝ) ^ (max 1 (PT.tiling.P i).h * D.geom.r) + 1) ^ 2) *
        Real.exp (-Real.rpow (T.S.n k : ℝ) d) ≤ 1 / 2 := by
  let M := 8 * κ.A0 + 1
  let C := Real.log 9 - 2 * Real.log (0.15 : ℝ)
  have hA : 0 ≤ κ.A0 := (show (0 : ℝ) ≤ 10 ^ 6 * (κ.R : ℝ) by positivity).trans hκ.A0_big
  have hC : 0 ≤ C := by
    dsimp [C]
    have h9 := Real.log_nonneg (by norm_num : (1 : ℝ) ≤ 9)
    have h15 := Real.log_nonpos (by norm_num : (0 : ℝ) ≤ 0.15) (by norm_num : (0.15 : ℝ) ≤ 1)
    linarith
  have hn : Tendsto (fun k => (T.S.n k : ℝ)) atTop atTop :=
    tendsto_natCast_atTop_atTop.comp T.S.n_tendsto
  have hL := (Real.tendsto_log_atTop.comp hn).eventually_ge_atTop 4
  have hevent := (barrier_error_tendsto T 20 2 (C * (M + 1)) c d hc hcd).eventually
    (Iio_mem_nhds (by norm_num : (0 : ℝ) < 1 / 2))
  filter_upwards [hL, hevent] with k hL hsmall
  intro PT hPT D i
  dsimp only [Function.comp_def] at hL
  have hm := block_size_polylog hκ D hL i
  have hLsq : 1 ≤ Real.log (T.S.n k : ℝ) ^ 2 := one_le_pow₀ (by linarith)
  have hcap : (2 / (0.15 : ℝ) ^ (max 1 (PT.tiling.P i).h * D.geom.r) + 1) ^ 2 ≤
      Real.exp (C * (M + 1) * Real.log (T.S.n k : ℝ) ^ 2) := by
    apply (crude_multiplier_square _).trans
    apply Real.exp_le_exp.mpr
    have hmul := mul_le_mul_of_nonneg_left
      (show (((max 1 (PT.tiling.P i).h : ℕ) : ℝ) * (D.geom.r : ℝ)) + 1 ≤
        (M + 1) * Real.log (T.S.n k : ℝ) ^ 2 by dsimp [M] at *; nlinarith only [hm, hLsq]) hC
    simpa only [C, mul_assoc, Nat.cast_mul] using hmul
  calc
    _ ≤ (T.S.n k : ℝ) * Real.log (T.S.n k : ℝ) ^ 20 *
        (Real.exp (Real.rpow (T.S.n k : ℝ) c) ^ 2 *
          Real.exp (C * (M + 1) * Real.log (T.S.n k : ℝ) ^ 2)) *
        Real.exp (-Real.rpow (T.S.n k : ℝ) d) := by gcongr
    _ = (T.S.n k : ℝ) * Real.log (T.S.n k : ℝ) ^ 20 *
        Real.exp (C * (M + 1) * Real.log (T.S.n k : ℝ) ^ 2 +
          2 * Real.rpow (T.S.n k : ℝ) c - Real.rpow (T.S.n k : ℝ) d) := by
      have hprod : Real.exp (Real.rpow (T.S.n k : ℝ) c) ^ 2 *
          Real.exp (C * (M + 1) * Real.log (T.S.n k : ℝ) ^ 2) *
          Real.exp (-Real.rpow (T.S.n k : ℝ) d) =
          Real.exp (C * (M + 1) * Real.log (T.S.n k : ℝ) ^ 2 +
            2 * Real.rpow (T.S.n k : ℝ) c - Real.rpow (T.S.n k : ℝ) d) := by
        rw [← Real.exp_nat_mul, ← Real.exp_add, ← Real.exp_add]
        congr 1
        norm_num
        ring
      calc
        _ = ((T.S.n k : ℝ) * Real.log (T.S.n k : ℝ) ^ 20) *
            (Real.exp (Real.rpow (T.S.n k : ℝ) c) ^ 2 *
              Real.exp (C * (M + 1) * Real.log (T.S.n k : ℝ) ^ 2) *
                Real.exp (-Real.rpow (T.S.n k : ℝ) d)) := by ring
        _ = _ := by rw [hprod]
    _ ≤ 1 / 2 := hsmall.le

/-- The full stopped second-moment iteration for an actual protocol. Its
remaining input is precisely the integrated raw factor-exception budget. -/
theorem second_moment_of_exception_budget (hgeom : TransferGeometry X) (hsurv : SurvivalFacts X)
    (P : TransferProtocol X) (c d : ℝ) (seed : P.Seed) (pair : Bool)
    (hregular : let δ := κ.KB *
        (((max 1 (PT.tiling.P (D.geom.patchOf X.target)).h : ℕ) : ℝ) * (D.geom.r : ℝ)) * bstar T k
      0 ≤ δ ∧ δ < 1 ∧ (⌈Real.log (T.S.n k : ℝ) ^ 20⌉₊ : ℝ) * δ ≤ 1 / 2 ∧
        (T.S.n k : ℝ) * Real.log (T.S.n k : ℝ) ^ 20 * (2 * δ ^ 2) ≤ 1 / 2)
    (hexceptional : (T.S.n k : ℝ) * Real.log (T.S.n k : ℝ) ^ 20 *
        (Real.exp (Real.rpow (T.S.n k : ℝ) c) ^ 2 *
          (2 / (0.15 : ℝ) ^ (max 1 (PT.tiling.P (D.geom.patchOf X.target)).h * D.geom.r) + 1) ^ 2) *
        Real.exp (-Real.rpow (T.S.n k : ℝ) d) ≤ 1 / 2)
    (hraw : ∀ t, t < P.steps → witnessMean X pair (fun x z => if X.allowed x z then
        X.rawLaw.pr (fun s => factorException P seed x z s (t + 1)) else 0) ≤
      Real.exp (-Real.rpow (T.S.n k : ℝ) d)) :
    ∀ t, witnessMean X pair (fun x z => if X.allowed x z then X.rawLaw.E (fun s =>
      likelihood P seed x z s (min t (stoppingTime P seed x z s c)) ^ 2) else 0) ≤ 2 := by
  let δ := κ.KB * (((max 1 (PT.tiling.P (D.geom.patchOf X.target)).h : ℕ) : ℝ) * (D.geom.r : ℝ)) * bstar T k
  let G := 2 / (0.15 : ℝ) ^ (max 1 (PT.tiling.P (D.geom.patchOf X.target)).h * D.geom.r)
  let e := Real.exp (Real.rpow (T.S.n k : ℝ) c) ^ 2 * (G + 1) ^ 2
  let ε := Real.exp (-Real.rpow (T.S.n k : ℝ) d)
  obtain ⟨hδ0, hδ1, hcall, hreg⟩ := hregular
  apply stopped_second_moment_of_updates P c seed pair (δ ^ 2) e ε
    (sq_nonneg _) (by dsimp [e]; positivity) (Real.exp_pos _).le
    (fun t x z s => factorException P seed x z s (t + 1))
  · intro t ht x z hx s hw hstop
    apply stopped_increment_bound P seed x z c G δ rfl hδ0 hδ1 t s hstop
    exact Blocks.multiplier_crude_bound hgeom hsurv P seed s x z hx c δ rfl hδ0 hδ1 hcall t hstop hw
  · exact hraw
  · have hbudget := add_le_add hreg hexceptional
    have hs := mul_le_mul_of_nonneg_right P.steps_bound (show 0 ≤ 2 * δ ^ 2 + e * ε by
      dsimp [e, ε]; positivity)
    dsimp only [e, ε, G] at hs ⊢
    nlinarith only [hbudget, hs]

/-- The deterministic second-moment budget is uniform in stages, data,
seeds and witness types. Only the raw exception estimate remains probabilistic. -/
theorem second_moment_eventually_of_exception_budget (hκ : κ.Admissible) (T : Stage)
    (c d : ℝ) (hc : 0 < c) (hcd : c < d) :
    ∀ᶠ k in atTop, ∀ PT : ProfiledTiling κ T k, ∀ hPT : PT.Valid, ∀ D : LateData hPT,
      ∀ X : CriticalTransferData D, TransferGeometry X → SurvivalFacts X →
      ∀ P : TransferProtocol X,
      (∀ seed pair t, t < P.steps → witnessMean X pair (fun x z => if X.allowed x z then
          X.rawLaw.pr (fun s => factorException P seed x z s (t + 1)) else 0) ≤
        Real.exp (-Real.rpow (T.S.n k : ℝ) d)) →
      ∀ seed pair t, witnessMean X pair (fun x z => if X.allowed x z then X.rawLaw.E (fun s =>
        likelihood P seed x z s (min t (stoppingTime P seed x z s c)) ^ 2) else 0) ≤ 2 := by
  filter_upwards [regular_budgets_eventually hκ T, exceptional_budget_eventually hκ T c d hc hcd]
    with k hreg hexc
  intro PT hPT D X hgeom hsurv P hraw seed pair
  exact second_moment_of_exception_budget hgeom hsurv P c d seed pair
    (hreg PT hPT D (D.geom.patchOf X.target)) (hexc PT hPT D (D.geom.patchOf X.target)) (hraw seed pair)

end HypercubeRamsey.S18.Lane_sol_s18_2lm
