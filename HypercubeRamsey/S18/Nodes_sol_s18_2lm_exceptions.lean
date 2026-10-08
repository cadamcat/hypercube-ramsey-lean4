import HypercubeRamsey.S18.Nodes_sol_s18_2lm_witnesses

namespace HypercubeRamsey.S18.Lane_sol_s18_2lm

open Classical Filter
open scoped BigOperators

set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 400000

variable {κ : CConsts} {T : Stage} {k : ℕ} {PT : ProfiledTiling κ T k}
  {hPT : PT.Valid} {D : LateData hPT} {X : CriticalTransferData D}

/-- A stopped multiplier exception has at most the barrier times the crude
block multiplier as its likelihood, including an exception at the last step. -/
theorem stopped_exception_likelihood_bound (hgeom : TransferGeometry X) (hsurv : SurvivalFacts X)
    (P : TransferProtocol X) (seed : P.Seed) (x : Fin (T.S.N k))
    (z : Option (Fin (T.S.N k))) (hx : X.allowed x z) (c δ : ℝ)
    (hδdef : δ = κ.KB * (((max 1 (PT.tiling.P (D.geom.patchOf X.target)).h : ℕ) : ℝ) *
      (D.geom.r : ℝ)) * bstar T k) (hδ0 : 0 ≤ δ) (hδ1 : δ < 1)
    (hcall : (⌈Real.log (T.S.n k : ℝ) ^ 20⌉₊ : ℝ) * δ ≤ 1 / 2)
    (s : X.Raw) (hw : 0 < X.rawLaw.w s)
    (hbad : factorException P seed x z s (stoppingTime P seed x z s c)) :
    likelihood P seed x z s (stoppingTime P seed x z s c) ≤
      Real.exp (Real.rpow (T.S.n k : ℝ) c) *
        (2 / (0.15 : ℝ) ^ (max 1 (PT.tiling.P (D.geom.patchOf X.target)).h * D.geom.r)) := by
  let τ := stoppingTime P seed x z s c
  have hτpos : 0 < τ := hbad.1
  have hprev : τ - 1 < stoppingTime P seed x z s c := by omega
  have hpos := likelihood_positive_before_stop P seed x z c
    (by rw [← hδdef]; exact hδ1) s (τ - 1) hprev
  have hB : likelihood P seed x z s (τ - 1) ≤ Real.exp (Real.rpow (T.S.n k : ℝ) c) :=
    le_of_not_gt (fun h => no_stop_trigger_before P seed x z s c hprev (Or.inr h))
  have hG := Blocks.multiplier_crude_bound hgeom hsurv P seed s x z hx c δ hδdef hδ0 hδ1
    hcall (τ - 1) (by dsimp [τ]; omega) hw
  have he : τ - 1 + 1 = τ := by omega
  rw [he] at hG
  have h := (div_le_iff₀ hpos).mp hG
  have hmul := mul_le_mul_of_nonneg_left hB (show 0 ≤
      2 / (0.15 : ℝ) ^ (max 1 (PT.tiling.P (D.geom.patchOf X.target)).h * D.geom.r) by positivity)
  exact h.trans (by simpa [mul_comm] using hmul)

/-- Change of measure at the stop only pays B*G for an exception event.
The raw estimate is integrated over witnesses, as in the paper. -/
theorem stopped_exception_of_raw (hgeom : TransferGeometry X) (hsurv : SurvivalFacts X)
    (P : TransferProtocol X) (c δ ε : ℝ) (seed : P.Seed) (pair : Bool)
    (hδdef : δ = κ.KB * (((max 1 (PT.tiling.P (D.geom.patchOf X.target)).h : ℕ) : ℝ) *
      (D.geom.r : ℝ)) * bstar T k) (hδ0 : 0 ≤ δ) (hδ1 : δ < 1)
    (hcall : (⌈Real.log (T.S.n k : ℝ) ^ 20⌉₊ : ℝ) * δ ≤ 1 / 2)
    (hraw : ∀ t, t < P.steps → witnessMean X pair (fun x z => if X.allowed x z then
      X.rawLaw.pr (fun s => factorException P seed x z s (t + 1)) else 0) ≤ ε) :
    witnessMean X pair (fun x z => if X.allowed x z then (tiltedLaw X x z).pr
      (fun s => factorException P seed x z s (stoppingTime P seed x z s c)) else 0) ≤
        Real.exp (Real.rpow (T.S.n k : ℝ) c) *
          (2 / (0.15 : ℝ) ^ (max 1 (PT.tiling.P (D.geom.patchOf X.target)).h * D.geom.r)) *
          P.steps * ε := by
  let B := Real.exp (Real.rpow (T.S.n k : ℝ) c)
  let G := 2 / (0.15 : ℝ) ^ (max 1 (PT.tiling.P (D.geom.patchOf X.target)).h * D.geom.r)
  have hpoint (x : Fin (T.S.N k)) (z : Option (Fin (T.S.N k))) (hx : X.allowed x z) :
      (tiltedLaw X x z).pr (fun s => factorException P seed x z s (stoppingTime P seed x z s c)) ≤
        B * G * ∑ t ∈ Finset.range P.steps, X.rawLaw.pr (fun s => factorException P seed x z s (t + 1)) := by
    let E := fun s => factorException P seed x z s (stoppingTime P seed x z s c)
    have hchange := stopped_change_measure P seed x z c (fun s => if E s then 1 else 0) (by
      intro t ht s s' hs hs' he
      have hf := factorException_prefix_eq P seed x z s s' le_rfl he
      simp only [E, hs, hs', hf])
    have hPr : (tiltedLaw X x z).E (fun s => if E s then 1 else 0) = (tiltedLaw X x z).pr E := by
      simp only [FinLaw.E, FinLaw.pr, mul_ite, mul_one, mul_zero]
    rw [hPr] at hchange
    rw [← hchange]
    unfold FinLaw.E FinLaw.pr
    simp_rw [Finset.mul_sum]
    rw [Finset.sum_comm]
    apply Finset.sum_le_sum
    intro s _
    by_cases hw : 0 < X.rawLaw.w s
    · by_cases hs : E s
      · have hcap := stopped_exception_likelihood_bound hgeom hsurv P seed x z hx c δ hδdef hδ0 hδ1 hcall s hw hs
        have hmem : stoppingTime P seed x z s c - 1 ∈ Finset.range P.steps := by
          have hp := hs.1
          have hle := Lane_q_s18_n3.stoppingTime_le_steps P seed x z s c
          exact Finset.mem_range.mpr (by omega)
        have hsum : B * G * X.rawLaw.w s ≤ ∑ t ∈ Finset.range P.steps,
            B * G * (if factorException P seed x z s (t + 1) then X.rawLaw.w s else 0) := by
          have he : stoppingTime P seed x z s c - 1 + 1 = stoppingTime P seed x z s c := by have := hs.1; omega
          calc
            _ = B * G * (if factorException P seed x z s
                (stoppingTime P seed x z s c - 1 + 1) then X.rawLaw.w s else 0) := by rw [he, if_pos hs]
            _ ≤ _ := Finset.single_le_sum
              (s := Finset.range P.steps)
              (f := fun t => B * G * (if factorException P seed x z s (t + 1) then X.rawLaw.w s else 0))
              (fun t _ => by split_ifs <;> positivity) hmem
        simp only [hs, ↓reduceIte, mul_one]
        have hm := mul_le_mul_of_nonneg_left hcap hw.le
        exact hm.trans (by simpa [B, G, mul_comm, mul_left_comm, mul_assoc] using hsum)
      · simp only [hs, ↓reduceIte, mul_zero]
        exact Finset.sum_nonneg fun t _ => by split_ifs <;> positivity
    · have hz : X.rawLaw.w s = 0 := le_antisymm (le_of_not_gt hw) (X.rawLaw.nonneg s)
      simp [hz]
  have hpoint' : witnessMean X pair (fun x z => if X.allowed x z then (tiltedLaw X x z).pr
      (fun s => factorException P seed x z s (stoppingTime P seed x z s c)) else 0) ≤
      B * G * witnessMean X pair (fun x z => ∑ t ∈ Finset.range P.steps,
        if X.allowed x z then X.rawLaw.pr (fun s => factorException P seed x z s (t + 1)) else 0) := by
    rw [← witnessMean_mul_left]
    apply witnessMean_mono
    intro x z
    by_cases hx : X.allowed x z
    · simp only [hx, ↓reduceIte]
      exact hpoint x z hx
    · simp [hx]
  have hsum : witnessMean X pair (fun x z => ∑ t ∈ Finset.range P.steps,
      if X.allowed x z then X.rawLaw.pr (fun s => factorException P seed x z s (t + 1)) else 0) ≤
        P.steps * ε := by
    have heq : witnessMean X pair (fun x z => ∑ t ∈ Finset.range P.steps,
        if X.allowed x z then X.rawLaw.pr (fun s => factorException P seed x z s (t + 1)) else 0) =
        ∑ t ∈ Finset.range P.steps, witnessMean X pair (fun x z => if X.allowed x z then
          X.rawLaw.pr (fun s => factorException P seed x z s (t + 1)) else 0) := by
      exact Witnesses.mean_sum (Finset.range P.steps) pair (fun t x z => if X.allowed x z then
        X.rawLaw.pr (fun s => factorException P seed x z s (t + 1)) else 0)
    rw [heq]
    calc
      _ ≤ ∑ t ∈ Finset.range P.steps, ε := Finset.sum_le_sum fun t ht => hraw t (Finset.mem_range.mp ht)
      _ = _ := by simp
  exact hpoint'.trans (by
    have hm := mul_le_mul_of_nonneg_left hsum (show 0 ≤ B * G by dsimp [B, G]; positivity)
    simpa only [B, G, mul_assoc] using hm)

noncomputable def exceptionCapConstant (κ : CConsts) : ℝ :=
  (Real.log 9 - 2 * Real.log (0.15 : ℝ)) * (8 * κ.A0 + 2)

/-- A uniform exponential-in-log-squared bound for the crude multiplier. -/
theorem multiplier_exponential_cap (hκ : κ.Admissible) (D : LateData hPT)
    (i : Fin PT.tiling.m) (hL : 4 ≤ Real.log (T.S.n k : ℝ)) :
    2 / (0.15 : ℝ) ^ (max 1 (PT.tiling.P i).h * D.geom.r) ≤
      Real.exp (exceptionCapConstant κ * Real.log (T.S.n k : ℝ) ^ 2) := by
  let G := 2 / (0.15 : ℝ) ^ (max 1 (PT.tiling.P i).h * D.geom.r)
  let C := Real.log 9 - 2 * Real.log (0.15 : ℝ)
  have hG : 0 ≤ G := by dsimp [G]; positivity
  have hC : 0 ≤ C := by
    have h9 := Real.log_nonneg (by norm_num : (1 : ℝ) ≤ 9)
    have h15 := Real.log_nonpos (by norm_num : (0 : ℝ) ≤ 0.15) (by norm_num : (0.15 : ℝ) ≤ 1)
    dsimp [C]; linarith
  have hm := block_size_polylog hκ D hL i
  have hpow : 1 ≤ Real.log (T.S.n k : ℝ) ^ 2 := one_le_pow₀ (by linarith)
  have hbound : ((max 1 (PT.tiling.P i).h * D.geom.r : ℕ) : ℝ) + 1 ≤
      (8 * κ.A0 + 2) * Real.log (T.S.n k : ℝ) ^ 2 := by
    simp only [Nat.cast_mul]
    nlinarith only [hm, hpow]
  have hmul := mul_le_mul_of_nonneg_left hbound hC
  calc
    _ ≤ (G + 1) ^ 2 := by change G ≤ (G + 1) ^ 2; nlinarith [sq_nonneg G]
    _ ≤ Real.exp (C * (((max 1 (PT.tiling.P i).h * D.geom.r : ℕ) : ℝ) + 1)) := crude_multiplier_square _
    _ ≤ _ := Real.exp_le_exp.mpr (by simpa only [exceptionCapConstant, C, mul_assoc] using hmul)

/-- The larger raw exponent absorbs the barrier, the block cap and every
protocol step, leaving the desired exception-stop exponent. -/
theorem exception_stop_budget_eventually (hκ : κ.Admissible) (T : Stage)
    (c d : ℝ) (hc : 0 < c) (hcd : c < d) :
    ∀ᶠ k in atTop, ∀ PT : ProfiledTiling κ T k, ∀ hPT : PT.Valid, ∀ D : LateData hPT,
      ∀ i : Fin PT.tiling.m, ∀ nsteps : ℕ,
      (nsteps : ℝ) ≤ (T.S.n k : ℝ) * Real.log (T.S.n k : ℝ) ^ 20 →
      Real.exp (Real.rpow (T.S.n k : ℝ) c) *
        (2 / (0.15 : ℝ) ^ (max 1 (PT.tiling.P i).h * D.geom.r)) * nsteps *
          Real.exp (-Real.rpow (T.S.n k : ℝ) d) ≤ Real.exp (-Real.rpow (T.S.n k : ℝ) c) := by
  have hn : Tendsto (fun k => (T.S.n k : ℝ)) atTop atTop :=
    tendsto_natCast_atTop_atTop.comp T.S.n_tendsto
  have hL := (Real.tendsto_log_atTop.comp hn).eventually_ge_atTop 4
  have hsmall := (barrier_error_tendsto T 20 2 (exceptionCapConstant κ) c d hc hcd).eventually
    (Iio_mem_nhds (by norm_num : (0 : ℝ) < 1))
  filter_upwards [hL, hsmall] with k hL hsmall
  dsimp only [Function.comp_def] at hL
  intro PT hPT D i nsteps hs
  let B := Real.exp (Real.rpow (T.S.n k : ℝ) c)
  let G := 2 / (0.15 : ℝ) ^ (max 1 (PT.tiling.P i).h * D.geom.r)
  let E := Real.exp (-Real.rpow (T.S.n k : ℝ) d)
  let A := exceptionCapConstant κ * Real.log (T.S.n k : ℝ) ^ 2
  have hcap := multiplier_exponential_cap hκ D i hL
  have hstep := mul_le_mul_of_nonneg_left hs (show 0 ≤ B * G * E by dsimp [B, G, E]; positivity)
  have hG := mul_le_mul_of_nonneg_left hcap (show 0 ≤
      (T.S.n k : ℝ) * Real.log (T.S.n k : ℝ) ^ 20 * B * E by dsimp [B, E]; positivity)
  have hprod : B * Real.exp A * E =
      Real.exp (A + Real.rpow (T.S.n k : ℝ) c - Real.rpow (T.S.n k : ℝ) d) := by
    dsimp [B, E]
    rw [← Real.exp_add, ← Real.exp_add]
    congr 1; ring
  have hlarge : Real.exp (A + 2 * Real.rpow (T.S.n k : ℝ) c - Real.rpow (T.S.n k : ℝ) d) *
      Real.exp (-Real.rpow (T.S.n k : ℝ) c) =
      Real.exp (A + Real.rpow (T.S.n k : ℝ) c - Real.rpow (T.S.n k : ℝ) d) := by
    rw [← Real.exp_add]
    congr 1; ring
  calc
    _ ≤ ((T.S.n k : ℝ) * Real.log (T.S.n k : ℝ) ^ 20) * (B * Real.exp A * E) := by
      dsimp only [A, B, G, E] at hstep hG ⊢
      simp only [Real.rpow_eq_pow] at hstep hG ⊢
      nlinarith only [hstep, hG]
    _ = ((T.S.n k : ℝ) * Real.log (T.S.n k : ℝ) ^ 20) *
        Real.exp (A + Real.rpow (T.S.n k : ℝ) c - Real.rpow (T.S.n k : ℝ) d) := by rw [hprod]
    _ = (((T.S.n k : ℝ) * Real.log (T.S.n k : ℝ) ^ 20) *
        Real.exp (A + 2 * Real.rpow (T.S.n k : ℝ) c - Real.rpow (T.S.n k : ℝ) d)) *
          Real.exp (-Real.rpow (T.S.n k : ℝ) c) := by rw [mul_assoc ((T.S.n k : ℝ) * Real.log (T.S.n k : ℝ) ^ 20), hlarge]
    _ ≤ 1 * Real.exp (-Real.rpow (T.S.n k : ℝ) c) :=
      mul_le_mul_of_nonneg_right hsmall.le (Real.exp_pos _).le
    _ = _ := one_mul _

end HypercubeRamsey.S18.Lane_sol_s18_2lm
