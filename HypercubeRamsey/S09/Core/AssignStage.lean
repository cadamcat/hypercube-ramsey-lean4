import HypercubeRamsey.S09.Core.GainStage
import HypercubeRamsey.S07.TagStage
import HypercubeRamsey.S03.GatedPosterior
import HypercubeRamsey.S03.ClockSampling
import HypercubeRamsey.Tools.ScatteredUnion
import HypercubeRamsey.S09.Core.AssignStage_q_s09_assign1
import HypercubeRamsey.S09.Core.AssignStage_q_s09_assign2

/-!
# Proposition 9.2, core: predictive tests, anchor avoidance, odd injection, even rows (P9.2-assignA–C)

Source: `sections/09-intermediate-powers-of-bias.tex`, lines 296–350; blueprint `research/blueprint/PART-B.md`
§3.9, P9.2-assignA, P9.2-assignB, P9.2-assignC.  Lemma 3.4 is `S07.cond_product_bound` (product form with free
coordinates), Lemma 3.6 is `scatteredMoments_union_labels`, Lemma 3.7 is `gated_posterior`, Lemma 3.10 is
`clock_sampling`.
-/

namespace HypercubeRamsey

open OAI.HypercubeRamsey Classical
open scoped BigOperators

/-- Monotonicity of the large regime in its constants. -/
theorem largeAt_mono9 {n₀ n₀' : ℕ} {C₀ C₀' : ℝ} {n N : ℕ} (h : LargeAt n₀ C₀ n N)
    (hn : n₀' ≤ n₀) (hC : C₀' ≤ C₀) : LargeAt n₀' C₀' n N :=
  ⟨le_trans hn h.1, le_trans (mul_le_mul_of_nonneg_right hC (by positivity)) h.2.1, h.2.2⟩

/-! ## P9.2-assignA (09:296–320) -/

set_option maxHeartbeats 5000000 in
/-- P9.2-assignA, predictive alarm mean (09:305–310): with everything but `W_*` fixed, `M_v` and `P⁻` do not
depend on `W_*` (the deletion kernels erase the target ID), the alarm at `W_* = x` integrates to
`∑_y M_v(y) 1[predictive failure]`, and the first assertion of Lemma 3.7 (`gated_posterior`,
`ε = e^{-c₄ n a_*/4}`, reference law `P⁻`) bounds it. -/
theorem p92_alarm_mean {P : Params9} {n N : ℕ} {M : TagMix N} (S : Setup9 P n N M)
    (I : IDMap9 P n) (E : Fin N → Fin N → Prop) (G : Colour) : AlarmMean9 S I E G := by
  classical
  intro ω v
  let t : I.ID := I.center v.1
  let μ : Law N := siteFirst9 S v.1
  let F : Fin N → (StarOdd9 v → Fin N) → ℝ := fun x ys => starLik9 S E G ω v x ys
  let Q : FinProb (StarOdd9 v → Fin N) :=
    FinProb.pi (fun b : StarOdd9 v => delLaw9 S E G ω b.1 t)
  let ε : ℝ := Real.exp (-(gainConst9 * n * P.aStar n / 4))
  have hε : 0 < ε := by positivity
  have hupd (x x' : Fin N) : updAnc9 (updAnc9 ω t x) t x' = updAnc9 ω t x' := by
    unfold updAnc9
    change Function.update (Function.update ω (Sum.inl t) x) (Sum.inl t) x' =
      Function.update ω (Sum.inl t) x'
    exact Function.update_idem (a := Sum.inl t) (v := x) (w := x') (f := ω)
  have hanc (x : Fin N) (c : I.ID) (hc : c ≠ t) :
      anc9 (updAnc9 ω t x) c = anc9 ω c := by
    have hne : (Sum.inl c : I.ID ⊕ OddSites9 n) ≠ Sum.inl t := by
      intro h
      exact hc (Sum.inl.inj h)
    unfold anc9 updAnc9
    change Function.update ω (Sum.inl t) x (Sum.inl c) = ω (Sum.inl c)
    exact Function.update_of_ne hne x ω
  have hmasked (x : Fin N) (b : OddSites9 n) :
      maskedLaw9 S (updAnc9 ω t x) b = maskedLaw9 S ω b := by
    have hne : Sum.inr b ≠ Sum.inl t := by simp
    unfold maskedLaw9 msk9 updAnc9
    rw [Function.update_of_ne hne]
  have hhit (x : Fin N) (b : OddSites9 n) :
      hitSet9 E G (updAnc9 ω t x) ((I.seen b.1).erase t) =
        hitSet9 E G ω ((I.seen b.1).erase t) := by
    ext y
    simp only [hitSet9, Finset.mem_filter, Finset.mem_univ, true_and]
    congr 1
    apply forall_congr'
    intro c
    apply forall_congr'
    intro hc
    rw [hanc x c (Finset.ne_of_mem_erase hc)]
  have hdel (x : Fin N) (b : OddSites9 n) :
      delLaw9 S E G (updAnc9 ω t x) b t = delLaw9 S E G ω b t := by
    simp [delLaw9, hmasked, hhit]
  have hlik (x x' : Fin N) (ys : StarOdd9 v → Fin N) :
      starLik9 S E G (updAnc9 ω t x) v x' ys = starLik9 S E G ω v x' ys := by
    unfold starLik9
    rw [show I.center v.1 = t by rfl]
    simp_rw [hupd x x']
  have hmarg (x : Fin N) (ys : StarOdd9 v → Fin N) :
      starMarg9 S E G (updAnc9 ω t x) v ys = starMarg9 S E G ω v ys := by
    simp [starMarg9, hlik]
  have href (x : Fin N) (ys : StarOdd9 v → Fin N) :
      starRef9 S E G (updAnc9 ω t x) v ys = starRef9 S E G ω v ys := by
    unfold starRef9
    apply Finset.prod_congr rfl
    intro b hb
    exact congrArg (fun L : Law N => L.w (ys b)) (hdel x b.1)
  have hfail (x : Fin N) (ys : StarOdd9 v → Fin N) :
      predFail9 S E G (updAnc9 ω t x) v ys = predFail9 S E G ω v ys := by
    simp [predFail9, hmarg, href]
  have hF0 : ∀ x ys, 0 ≤ F x ys := by
    intro x ys
    dsimp [F, starLik9]
    apply mul_nonneg
    · split_ifs <;> norm_num
    · exact Finset.prod_nonneg fun b _ =>
        (rowLaw9 S E G (updAnc9 ω t x) b.1).nonneg (ys b)
  have hgate := gated_posterior μ F hF0 Q ε 0 hε
  have hmean (ys : StarOdd9 v → Fin N) :
      (∑ x, μ.w x * F x ys) = starMarg9 S E G ω v ys := by
    rfl
  have hq (ys : StarOdd9 v → Fin N) : Q.w ys = starRef9 S E G ω v ys := by
    rfl
  have hbad :
      (∑ ys, if predFail9 S E G ω v ys then starMarg9 S E G ω v ys else 0) ≤ ε := by
    have hgate' :
        (∑ ys, if starMarg9 S E G ω v ys = 0 ∨
          starMarg9 S E G ω v ys < ε * starRef9 S E G ω v ys
          then starMarg9 S E G ω v ys else 0) ≤ ε := by
      have hh := hgate.1
      dsimp only at hh
      simp_rw [hmean, hq] at hh
      simpa [or_comm] using hh
    calc
      (∑ ys, if predFail9 S E G ω v ys then starMarg9 S E G ω v ys else 0) =
          ∑ ys, if starMarg9 S E G ω v ys = 0 ∨
            starMarg9 S E G ω v ys < ε * starRef9 S E G ω v ys
            then starMarg9 S E G ω v ys else 0 := by
              apply Finset.sum_congr rfl
              intro ys hys
              by_cases h : starMarg9 S E G ω v ys = 0 ∨
                  starMarg9 S E G ω v ys <
                    Real.exp (-(gainConst9 * n * P.aStar n / 4)) * starRef9 S E G ω v ys
              · simp [predFail9, ε, h]
              · simp [predFail9, ε, h]
      _ ≤ ε := hgate'
  calc
    (∑ x, μ.w x * alarm9 S E G (updAnc9 ω t x) v) =
        ∑ ys, if predFail9 S E G ω v ys then
          (∑ x, μ.w x * starLik9 S E G ω v x ys) else 0 := by
      simp only [alarm9]
      simp_rw [Finset.mul_sum]
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro ys hys
      simp_rw [hfail]
      have hactual (x : Fin N) : anc9 (updAnc9 ω t x) (I.center v.1) = x := by
        unfold anc9 updAnc9
        rw [show I.center v.1 = t by rfl]
        exact Function.update_self (Sum.inl t) x ω
      simp_rw [hactual, hlik]
      by_cases hf : predFail9 S E G ω v ys
      · simp [hf, Finset.sum_mul, mul_assoc]
      · simp [hf]
    _ = ∑ ys, if predFail9 S E G ω v ys then starMarg9 S E G ω v ys else 0 := by
      apply Finset.sum_congr rfl
      intro ys hys
      by_cases hf : predFail9 S E G ω v ys
      · simp only [if_pos hf]
        simpa [F] using hmean ys
      · simp [hf]
    _ ≤ ε := hbad

set_option maxHeartbeats 5000000 in
/-- P9.2-assignA, star events (09:309–312): the star event fails validity with raw probability `e^{-c₀ n^u}`
(`GainCert9`); the alarm reads `W_*` (law `μ_{i_{z(v)}}`, independent of the other inputs) and Markov with
`AlarmMean9` bounds the alarm event by `e^{-c₄ n a_*/8}`, which is `≤ e^{-n^u}` for large `n`
(`ScalesAt9`). -/
theorem p92_star_bad_prob (P : Params9) (hP : P.Valid) (c₀ : ℝ) (hc₀ : 0 < c₀) :
    ∃ c > (0 : ℝ), ∃ n₀ : ℕ, ∀ n ≥ n₀, ∀ {N : ℕ} {E : Fin N → Fin N → Prop}
      {X Y : Finset (Fin N)} {κ : ℝ} {G : Colour} {M : TagMix N} (S : Setup9 P n N M)
      (I : IDMap9 P n),
      CoreInput9 P κ E X Y G M S I → GainCert9 S I E G c₀ → AlarmMean9 S I E G →
        ∀ v : EvenSites9 n, (rawLaw9 S I).pr (fun ω => StarBad9 S E G ω v) ≤ P.tail c n := by
  have hexps := Lane_q_s09_assign1.scaleExpsOfValid9 P hP
  let c : ℝ := min c₀ 1 / 2
  have hc : 0 < c := by dsimp [c]; positivity
  have hcBounds : 2 * c ≤ c₀ ∧ 2 * c ≤ 1 := by
    constructor <;> dsimp [c] <;> nlinarith [min_le_left c₀ 1, min_le_right c₀ 1]
  have hu : 0 < P.u := hexps.2.2.1
  have htendsto : Filter.Tendsto (fun n : ℕ => (n : ℝ) ^ P.u) Filter.atTop Filter.atTop :=
    (tendsto_rpow_atTop hu).comp tendsto_natCast_atTop_atTop
  obtain ⟨nTail, hTail⟩ :=
    Filter.eventually_atTop.1 (htendsto.eventually_ge_atTop (Real.log 2 / c))
  refine ⟨c, hc, max 1 nTail, ?_⟩
  intro n hn N E X Y κ G M S I hcore hgain hAM v
  have hnTail : nTail ≤ n := le_trans (le_max_right _ _) hn
  have hpowLarge : Real.log 2 / c ≤ (n : ℝ) ^ P.u := hTail n hnTail
  rcases hcore with ⟨hN, _, _, _, _, _, _, hscales⟩
  rcases hscales with ⟨hnpos, _, _, _, _, _, _, hmargin⟩
  have hlog0 : 0 ≤ Real.log ((n : ℝ) + 1) := by
    apply Real.log_nonneg
    have hnR : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hnpos
    linarith
  have hradius0 : 0 ≤ (P.radius n : ℝ) + 8 := by positivity
  have hxS0 : 0 ≤ (n : ℝ) ^ (P.xS : ℝ) := by positivity
  have hpowerMargin : 4 * (n : ℝ) ^ P.u ≤ gainConst9 * n * P.aStar n / 100 := by
    nlinarith [hmargin, mul_nonneg hradius0 hlog0]
  have hgainLarge : (n : ℝ) ^ P.u ≤ gainConst9 * n * P.aStar n / 8 := by
    have htpos : 0 < (n : ℝ) ^ P.u := by positivity
    have hApos : 0 ≤ gainConst9 * n * P.aStar n := by nlinarith [hpowerMargin, htpos]
    have hsmall : (n : ℝ) ^ P.u ≤ gainConst9 * n * P.aStar n / 400 := by
      nlinarith [hpowerMargin]
    have hcoeff : gainConst9 * n * P.aStar n / 400 ≤
        gainConst9 * n * P.aStar n / 8 := by
      calc
        gainConst9 * n * P.aStar n / 400 =
            (gainConst9 * n * P.aStar n) * (1 / 400 : ℝ) := by ring
        _ ≤ (gainConst9 * n * P.aStar n) * (1 / 8 : ℝ) :=
            mul_le_mul_of_nonneg_left (by norm_num) hApos
        _ = gainConst9 * n * P.aStar n / 8 := by ring
    exact hsmall.trans hcoeff
  let θ : ℝ := Real.exp (-(gainConst9 * n * P.aStar n / 8))
  have hθ : 0 < θ := by positivity
  have hθTail : θ ≤ Real.exp (-((n : ℝ) ^ P.u)) := by
    dsimp [θ]
    exact Real.exp_le_exp.mpr (by linarith [hgainLarge])
  have hθSmall : θ ≤ Real.exp (-((2 * c) * (n : ℝ) ^ P.u)) := by
    have hcoef := mul_le_mul_of_nonneg_right hcBounds.2 (le_of_lt (by positivity : 0 < (n : ℝ) ^ P.u))
    calc
      θ ≤ Real.exp (-((n : ℝ) ^ P.u)) := hθTail
      _ ≤ Real.exp (-((2 * c) * (n : ℝ) ^ P.u)) :=
        Real.exp_le_exp.mpr (by nlinarith [hcoef])
  let μ : Law N := siteFirst9 S v.1
  let t : I.ID := I.center v.1
  let j : I.ID ⊕ OddSites9 n := Sum.inl t
  let e : Outcome9 I N ≃ Fin N ×
      (∀ i : {i : I.ID ⊕ OddSites9 n // i ≠ j}, Val9 I N i.1) :=
    Lane_q_s09_assign1.coordSplitEquiv (Ω := Val9 I N) j
  let restLaw : ∀ i : {i : I.ID ⊕ OddSites9 n // i ≠ j},
      FinProb (Val9 I N i.1) := fun i => inputLaw9 S I i.1
  let R := FinProb.pi restLaw
  have hcoord : inputLaw9 S I j = μ := by
    simp [inputLaw9, μ, siteFirst9, j, t, I.center_slice]
    rfl
  have hraw :
      (rawLaw9 S I).expect (fun ω => alarm9 S E G ω v) =
        ∑ x, μ.w x * R.expect (fun τ => alarm9 S E G (e.symm (x, τ)) v) := by
    have hs := Lane_q_s09_assign1.pi_expect_split_coord (inputLaw9 S I) j
      (fun ω => alarm9 S E G ω v)
    rw [hcoord] at hs
    change (FinProb.pi (inputLaw9 S I)).expect (fun ω => alarm9 S E G ω v) =
      ∑ x, μ.w x * (FinProb.pi (fun i : {i // i ≠ j} => inputLaw9 S I i.1)).expect
        (fun τ => alarm9 S E G
          ((Lane_q_s09_assign1.coordSplitEquiv j).symm (x, τ)) v) at hs
    change (FinProb.pi (inputLaw9 S I)).expect (fun ω => alarm9 S E G ω v) =
      ∑ x, μ.w x * (FinProb.pi (fun i : {i // i ≠ j} => inputLaw9 S I i.1)).expect
        (fun τ => alarm9 S E G
          ((Lane_q_s09_assign1.coordSplitEquiv j).symm (x, τ)) v)
    simpa only [rawLaw9, R, restLaw, e] using hs
  have hupdate (x x' : Fin N) (τ : ∀ i : {i // i ≠ j}, Val9 I N i.1) :
      updAnc9 (e.symm (x, τ)) t x' = e.symm (x', τ) := by
    have hfirst (a : Fin N) : (e.symm (a, τ)) j = a := by
      have h := congrArg Prod.fst (e.apply_symm_apply (a, τ))
      change (e.symm (a, τ)) j = a at h
      exact h
    have hsecond (a : Fin N) (i : I.ID ⊕ OddSites9 n) (hi : i ≠ j) :
        (e.symm (a, τ)) i = τ ⟨i, hi⟩ := by
      have h := congrArg (fun p : Fin N × (∀ i : {i // i ≠ j}, Val9 I N i.1) => p.2 ⟨i, hi⟩)
        (e.apply_symm_apply (a, τ))
      change (e.symm (a, τ)) i = τ ⟨i, hi⟩ at h
      exact h
    funext i
    by_cases hi : i = j
    · subst i
      change Function.update (e.symm (x, τ)) (Sum.inl t)
        (show Val9 I N (Sum.inl t) from x') (Sum.inl t) = e.symm (x', τ) (Sum.inl t)
      rw [Function.update_self]
      simpa [j] using (hfirst x').symm
    · have hi' : i ≠ Sum.inl t := by simpa [j] using hi
      change Function.update (e.symm (x, τ)) (Sum.inl t)
        (show Val9 I N (Sum.inl t) from x') i = e.symm (x', τ) i
      rw [Function.update_of_ne hi']
      exact (hsecond x i hi).trans (hsecond x' i hi').symm
  have hNpos : 0 < N := hN
  let x₀ : Fin N := ⟨0, hNpos⟩
  have hinner (τ : ∀ i : {i // i ≠ j}, Val9 I N i.1) :
      (∑ x, μ.w x * alarm9 S E G (e.symm (x, τ)) v) ≤
        Real.exp (-(gainConst9 * n * P.aStar n / 4)) := by
    have hupdate' (x : Fin N) :
        updAnc9 (e.symm (x₀, τ)) (I.center v.1) x = e.symm (x, τ) := by
      simpa [t] using hupdate x₀ x τ
    have hh := hAM (e.symm (x₀, τ)) v
    change (∑ x, (siteFirst9 S v.1).w x * alarm9 S E G
      (e.symm (x, τ)) v) ≤ Real.exp (-(gainConst9 * n * P.aStar n / 4))
    calc
      (∑ x, (siteFirst9 S v.1).w x * alarm9 S E G (e.symm (x, τ)) v) =
          ∑ x, (siteFirst9 S v.1).w x * alarm9 S E G
            (updAnc9 (e.symm (x₀, τ)) (I.center v.1) x) v := by
              apply Finset.sum_congr rfl
              intro x hx
              rw [← hupdate' x]
      _ ≤ Real.exp (-(gainConst9 * n * P.aStar n / 4)) := hh
  have hchange :
      (∑ x, μ.w x * R.expect (fun τ => alarm9 S E G (e.symm (x, τ)) v)) =
        R.expect (fun τ => ∑ x, μ.w x * alarm9 S E G (e.symm (x, τ)) v) := by
    simp only [FinProb.expect]
    calc
      (∑ x, μ.w x * ∑ τ, R.w τ * alarm9 S E G (e.symm (x, τ)) v) =
          ∑ x, ∑ τ, μ.w x * (R.w τ * alarm9 S E G (e.symm (x, τ)) v) := by
            apply Finset.sum_congr rfl
            intro x hx
            rw [Finset.mul_sum]
      _ = ∑ τ, ∑ x, μ.w x * (R.w τ * alarm9 S E G (e.symm (x, τ)) v) := by
            rw [Finset.sum_comm]
      _ = ∑ τ, R.w τ * ∑ x, μ.w x * alarm9 S E G (e.symm (x, τ)) v := by
            apply Finset.sum_congr rfl
            intro τ hτ
            rw [Finset.mul_sum]
            apply Finset.sum_congr rfl
            intro x hx
            ring
  have hAlarmMean :
      (rawLaw9 S I).expect (fun ω => alarm9 S E G ω v) ≤
        Real.exp (-(gainConst9 * n * P.aStar n / 4)) := by
    rw [hraw, hchange]
    calc
      R.expect (fun τ => ∑ x, μ.w x * alarm9 S E G (e.symm (x, τ)) v) ≤
          R.expect (fun _ => Real.exp (-(gainConst9 * n * P.aStar n / 4))) :=
            FinProb.expect_mono R (fun τ => hinner τ)
      _ = Real.exp (-(gainConst9 * n * P.aStar n / 4)) := FinProb.expect_const R _
  have hlikNonneg (ω : Outcome9 I N) (ys : StarOdd9 v → Fin N) :
      0 ≤ starLik9 S E G ω v (anc9 ω t) ys := by
    unfold starLik9
    apply mul_nonneg
    · split_ifs <;> norm_num
    · exact Finset.prod_nonneg fun b _ =>
        (rowLaw9 S E G (updAnc9 ω t (anc9 ω t)) b.1).nonneg (ys b)
  have halarmNonneg (ω : Outcome9 I N) : 0 ≤ alarm9 S E G ω v := by
    unfold alarm9
    apply Finset.sum_nonneg
    intro ys hys
    exact mul_nonneg (hlikNonneg ω ys) (by split_ifs <;> norm_num)
  have hmarkov := FinProb.markov (rawLaw9 S I) (fun ω => alarm9 S E G ω v) θ
    halarmNonneg hθ
  have hprweak :
      (rawLaw9 S I).pr (fun ω => θ < alarm9 S E G ω v) ≤
        (rawLaw9 S I).pr (fun ω => θ ≤ alarm9 S E G ω v) :=
    Lane_q_s09_assign1.pr_mono (rawLaw9 S I) _ _ (fun ω h => le_of_lt h)
  have halarmProb :
      (rawLaw9 S I).pr (fun ω => θ < alarm9 S E G ω v) ≤ θ := by
    calc
      (rawLaw9 S I).pr (fun ω => θ < alarm9 S E G ω v) ≤
          (rawLaw9 S I).pr (fun ω => θ ≤ alarm9 S E G ω v) := hprweak
      _ ≤ ((rawLaw9 S I).expect (fun ω => alarm9 S E G ω v)) / θ := hmarkov
      _ ≤ Real.exp (-(gainConst9 * n * P.aStar n / 4)) / θ :=
        div_le_div_of_nonneg_right hAlarmMean hθ.le
      _ = θ := by
        dsimp [θ]
        rw [← Real.exp_sub]
        congr 1 <;> ring
  have hbadUnion :
      (rawLaw9 S I).pr (fun ω => StarBad9 S E G ω v) ≤ P.tail c₀ n + θ := by
    calc
      (rawLaw9 S I).pr (fun ω => StarBad9 S E G ω v) =
          (rawLaw9 S I).pr (fun ω =>
            ¬ starValid9 S E G ω v ∨ θ < alarm9 S E G ω v) := by
              apply congrArg (fun A => (rawLaw9 S I).pr A)
              funext ω
              simp [StarBad9, θ]
      _ ≤ (rawLaw9 S I).pr (fun ω => ¬ starValid9 S E G ω v) +
          (rawLaw9 S I).pr (fun ω => θ < alarm9 S E G ω v) :=
            FinProb.pr_union _ _ _
      _ ≤ P.tail c₀ n + θ := add_le_add (hgain v) halarmProb
  have htpos : 0 < (n : ℝ) ^ P.u := by positivity
  have hfirst : P.tail c₀ n ≤ Real.exp (-((2 * c) * (n : ℝ) ^ P.u)) := by
    dsimp [Params9.tail]
    have hcoef := mul_le_mul_of_nonneg_right hcBounds.1 htpos.le
    exact Real.exp_le_exp.mpr (by nlinarith [hcoef])
  have hsum : P.tail c₀ n + θ ≤ 2 * Real.exp (-((2 * c) * (n : ℝ) ^ P.u)) := by
    linarith [hfirst, hθSmall]
  have hct : Real.log 2 ≤ c * (n : ℝ) ^ P.u := by
    have hmul := mul_le_mul_of_nonneg_left hpowLarge hc.le
    have hcancel : c * (Real.log 2 / c) = Real.log 2 := by field_simp [hc.ne']
    nlinarith [hmul, hcancel]
  have hexp2 : 2 ≤ Real.exp (c * (n : ℝ) ^ P.u) := by
    calc
      2 = Real.exp (Real.log 2) := (Real.exp_log (by norm_num : (0 : ℝ) < 2)).symm
      _ ≤ Real.exp (c * (n : ℝ) ^ P.u) := Real.exp_le_exp.mpr hct
  have hqhalf : Real.exp (-(c * (n : ℝ) ^ P.u)) ≤ 1 / 2 := by
    rw [Real.exp_neg]
    simpa [one_div] using one_div_le_one_div_of_le (by norm_num) hexp2
  have hqnonneg : 0 ≤ Real.exp (-(c * (n : ℝ) ^ P.u)) := Real.exp_nonneg _
  have hexpDouble :
      Real.exp (-((2 * c) * (n : ℝ) ^ P.u)) =
        Real.exp (-(c * (n : ℝ) ^ P.u)) * Real.exp (-(c * (n : ℝ) ^ P.u)) := by
    calc
      Real.exp (-((2 * c) * (n : ℝ) ^ P.u)) =
          Real.exp (-(c * (n : ℝ) ^ P.u) + -(c * (n : ℝ) ^ P.u)) := by congr 1 <;> ring
      _ = _ := Real.exp_add _ _
  have hfactor : 2 * Real.exp (-((2 * c) * (n : ℝ) ^ P.u)) ≤
      Real.exp (-(c * (n : ℝ) ^ P.u)) := by
    rw [hexpDouble]
    have h2q : 2 * Real.exp (-(c * (n : ℝ) ^ P.u)) ≤ 1 := by linarith [hqhalf]
    calc
      2 * (Real.exp (-(c * (n : ℝ) ^ P.u)) * Real.exp (-(c * (n : ℝ) ^ P.u))) =
          (2 * Real.exp (-(c * (n : ℝ) ^ P.u))) * Real.exp (-(c * (n : ℝ) ^ P.u)) := by ring
      _ ≤ 1 * Real.exp (-(c * (n : ℝ) ^ P.u)) :=
        mul_le_mul_of_nonneg_right h2q hqnonneg
      _ = _ := by ring
  have hfinalTail : P.tail c₀ n + θ ≤ P.tail c n := by
    calc
      P.tail c₀ n + θ ≤ 2 * Real.exp (-((2 * c) * (n : ℝ) ^ P.u)) := hsum
      _ ≤ Real.exp (-(c * (n : ℝ) ^ P.u)) := hfactor
      _ = P.tail c n := by rfl
  exact (hbadUnion.trans hfinalTail)

/-- P9.2-assignA, locality (09:314–316): the star event of `v` reads only the anchors of IDs seen at its odd
neighbours and their masks; a shared ID or mask forces special distance at most `4` and residual distance at
most `2r + 4` (`IDMap9.center_slice`, `IDMap9.center_near`), so at most `(m+1)^4 (n-m+1)^{2r+4} ≤ (n+1)^{2r+8}`
other star events meet it. -/
theorem p92_star_scope {P : Params9} {n N : ℕ} {M : TagMix N} (S : Setup9 P n N M)
    (I : IDMap9 P n) (E : Fin N → Fin N → Prop) (G : Colour) : StarScopeFacts9 S I E G := by
  classical
  refine ⟨?_, ?_⟩
  · intro v
    intro ω ω' hω
    exact Lane_q_s09_assign1.starScopeBadEq9 S E G ω ω' hω
  · intro v
    let R : ℕ := 2 * P.radius n + 8
    let C : Finset (EvenSites9 n) := Finset.univ.filter (fun v' : EvenSites9 n =>
      v' ≠ v ∧ ¬ Disjoint (starScope9 I v) (starScope9 I v'))
    let B : Finset (CubeVertex n) := Finset.univ.filter
      (fun w => _root_.hammingDist v.1 w ≤ R)
    have hsubset : C.image Subtype.val ⊆ B := by
      intro w hw
      rcases Finset.mem_image.mp hw with ⟨v', hv', rfl⟩
      have hoverlap := (Finset.mem_filter.mp hv').2.2
      have hd := Lane_q_s09_assign1.starScopeOverlapRadius9 v v' hoverlap
      exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, by simpa [R] using hd⟩
    have himage : (C.image Subtype.val).card = C.card :=
      Finset.card_image_of_injective C Subtype.val_injective
    have hball : B.card ≤ (n + 1) ^ R := by
      simpa [B] using Lane_q_s09_assign1.hammingBallCardBound9 (r := R) v.1
    calc
      C.card = (C.image Subtype.val).card := himage.symm
      _ ≤ B.card := Finset.card_le_card hsubset
      _ ≤ (n + 1) ^ R := hball
      _ = lllDegree9 P n := by simp [R, lllDegree9]

/-- P9.2-assignA, the local-lemma input (09:316–318): charges `x = e^{-c₁ n^u/2}` meet
`e^{-c₁ n^u} ≤ x (1 - x)^{(n+1)^{2r+8}}` for large `n`, since `r log n = o(n^u)` (`σ < u`). -/
theorem p92_anchor_lll (P : Params9) (hP : P.Valid) (c₁ : ℝ) (hc₁ : 0 < c₁) :
    ∃ n₀ : ℕ, ∀ n ≥ n₀, ∀ {N : ℕ} {E : Fin N → Fin N → Prop} {M : TagMix N}
      (S : Setup9 P n N M) (I : IDMap9 P n) (G : Colour),
      (∀ v : EvenSites9 n, (rawLaw9 S I).pr (fun ω => StarBad9 S E G ω v) ≤ P.tail c₁ n) →
      StarScopeFacts9 S I E G → AnchorLLL9 S I E G (c₁ / 2) := by
  have hexps := Lane_q_s09_assign1.scaleExpsOfValid9 P hP
  obtain ⟨nLog, hLog⟩ := Lane_q_s09_assign1.degreeLogSmall9 P hexps hc₁
  have hu : 0 < P.u := hexps.2.2.1
  have htendsto : Filter.Tendsto (fun n : ℕ => (n : ℝ) ^ P.u) Filter.atTop Filter.atTop :=
    (tendsto_rpow_atTop hu).comp tendsto_natCast_atTop_atTop
  obtain ⟨nCharge, hCharge⟩ := Filter.eventually_atTop.1
    (htendsto.eventually_ge_atTop (Real.log 2 / (c₁ / 4)))
  refine ⟨max 1 (max nLog nCharge), ?_⟩
  intro n hn N E M S I G hprob hscope
  have hn1 : 1 ≤ n := le_trans (le_max_left _ _) hn
  have hnLog : nLog ≤ n := le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) hn
  have hnCharge : nCharge ≤ n := le_trans (le_trans (le_max_right _ _) (le_max_right _ _)) hn
  have hlogQuarter : Real.log 2 ≤ (c₁ / 4) * (n : ℝ) ^ P.u := by
    have h := (div_le_iff₀ (by positivity : (0 : ℝ) < c₁ / 4)).1 (hCharge n hnCharge)
    nlinarith [h]
  have hlogHalf : Real.log 2 ≤ (c₁ / 2) * (n : ℝ) ^ P.u := by
    have hcoef : c₁ / 4 ≤ c₁ / 2 := by linarith
    have hmul := mul_le_mul_of_nonneg_right hcoef (by positivity : 0 ≤ (n : ℝ) ^ P.u)
    linarith
  let q : ℝ := P.tail (c₁ / 2) n
  let D : ℕ := lllDegree9 P n
  have hqpos : 0 < q := by
    dsimp [q, Params9.tail]
    exact Real.exp_pos _
  have hqhalf : q ≤ 1 / 2 := by
    calc
      q = Real.exp (-((c₁ / 2) * (n : ℝ) ^ P.u)) := rfl
      _ ≤ Real.exp (-Real.log 2) := Real.exp_le_exp.mpr (by linarith [hlogHalf])
      _ = 1 / 2 := by
        rw [Real.exp_neg, Real.exp_log (by norm_num : (0 : ℝ) < 2)]
        norm_num
  have hlogD : Real.log (D : ℝ) =
      (2 * (P.radius n : ℝ) + 8) * Real.log ((n : ℝ) + 1) := by
    simp [D, lllDegree9, Real.log_pow, Nat.cast_add, Nat.cast_mul]
  have hDpos : 0 < (D : ℝ) := by
    dsimp [D, lllDegree9]
    positivity
  have hlogBound : Real.log (D : ℝ) ≤ (c₁ / 4) * (n : ℝ) ^ P.u := by
    rw [hlogD]
    exact hLog n hnLog
  have hDq : (D : ℝ) * q ≤ 1 / 2 := by
    calc
      (D : ℝ) * q = Real.exp (Real.log (D : ℝ)) * q := by rw [Real.exp_log hDpos]
      _ = Real.exp (Real.log (D : ℝ) + -((c₁ / 2) * (n : ℝ) ^ P.u)) := by
        dsimp [q, Params9.tail]
        rw [← Real.exp_add]
      _ ≤ Real.exp (-Real.log 2) := Real.exp_le_exp.mpr (by
        rw [hlogD]
        linarith [hlogBound, hlogQuarter])
      _ = 1 / 2 := by
        rw [Real.exp_neg, Real.exp_log (by norm_num : (0 : ℝ) < 2)]
        norm_num
  have hBern : 1 - (D : ℝ) * q ≤ (1 - q) ^ D := by
    have h := one_add_mul_le_pow (a := -q) (by linarith [hqhalf]) D
    convert h using 1 <;> ring
  have hqlePow : q ≤ (1 - q) ^ D := by
    have hleft : 1 / 2 ≤ 1 - (D : ℝ) * q := by nlinarith [hDq]
    linarith [hBern, hqhalf]
  have htailEq : P.tail c₁ n = q ^ 2 := by
    dsimp [q, Params9.tail]
    rw [pow_two]
    rw [← Real.exp_add]
    congr 1
    ring
  have hprob' (v : EvenSites9 n) : (rawLaw9 S I).pr (fun ω => StarBad9 S E G ω v) ≤
      q * (1 - q) ^ D := by
    calc
      (rawLaw9 S I).pr (fun ω => StarBad9 S E G ω v) ≤ P.tail c₁ n := hprob v
      _ = q ^ 2 := htailEq
      _ ≤ q * (1 - q) ^ D := by
        calc
          q ^ 2 = q * q := by ring
          _ ≤ q * (1 - q) ^ D := mul_le_mul_of_nonneg_left hqlePow hqpos.le
  change S07.LLLInput (inputLaw9 S I) (fun v ω => StarBad9 S E G ω v)
    (starScope9 I) (P.tail (c₁ / 2) n) (lllDegree9 P n)
  rcases hscope with ⟨hdep, hdegree⟩
  refine ⟨by positivity, ?_, hdep, ?_, ?_⟩
  · dsimp [Params9.tail]
    calc
      Real.exp (-((c₁ / 2) * (n : ℝ) ^ P.u)) < Real.exp 0 :=
      Real.exp_lt_exp.mpr (neg_lt_zero.mpr (by positivity : 0 < (c₁ / 2) * (n : ℝ) ^ P.u))
      _ = 1 := by simp
  · intro i
    letI : ∀ a : EvenSites9 n, Decidable (a = i) := fun a => Classical.propDecidable _
    refine Nat.le_trans ?_ (hdegree i)
    apply Finset.card_le_card
    intro j hj
    have hjDep := (Finset.mem_filter.mp hj).2
    simpa only [Finset.mem_filter, Finset.mem_univ, true_and] using hjDep
  · intro v
    simpa [q, D, rawLaw9] using hprob' v

/-! ## P9.2-assignB (09:322–329) -/

/-- Row widths (09:162, 09:323): every odd row has an even neighbour whose masked full order passes its tests,
so each successive hit retains at least `.49` (`b_* ≤ 1/200`) and the full filter keeps mass at least
`.49^{T+m}` of the masked law (`IDMap9.odd_ids`); the masked law has width at most `S_s + n^u + log 2`
(`MasksOK9`, `Prep9`), so `N p_b ≤ e^{P.filterBudget n} ≤ e^{S_d}`. -/
theorem p92_row_cap (P : Params9) (hP : P.Valid) :
    ∃ n₀ : ℕ, ∀ n ≥ n₀, ∀ {N : ℕ} {E : Fin N → Fin N → Prop} {X Y : Finset (Fin N)} {κ : ℝ}
      {G : Colour} {M : TagMix N} (S : Setup9 P n N M) (I : IDMap9 P n),
      CoreInput9 P κ E X Y G M S I → RowCap9 S I E G := by
  refine ⟨1, ?_⟩
  intro n hn N E X Y κ G M S I hcore
  rcases hcore with ⟨hN, hPrep, hDeep, hTags, hMasks, hDeepTools, hExps, hScales⟩
  rcases hScales with ⟨hnScales, hmle, hradius, hShallow, hFilterBudget, hDeepMargin, hbStar, hGain⟩
  intro ω hω hregular b y
  have hnpos : 0 < n := by omega
  let j : Fin n := ⟨0, hnpos⟩
  let v : EvenSites9 n := ⟨cubeFlip b.1 j, (cubeFlip_parity b.1 j).2 b.2⟩
  have hAdj : (cube n).Adj v.1 b.1 := by
    simpa [v] using (cubeFlip_adj b.1 j).symm
  have horderRegular :
      orderRegular9 E G ω (maskedLaw9 S ω b) (fullOrder9 I v b) :=
    (hregular v b hAdj).1
  let μ : Law N := maskedLaw9 S ω b
  let order : List I.ID := fullOrder9 I v b
  have hret := Lane_q_s09_assign1.orderHitMassLower9 E G ω μ order horderRegular hbStar
    order.length (le_rfl)
  have hsetFinal :
      Lane_q_s09_assign1.orderHitSet9 E G ω order order.length =
        hitSet9 E G ω (I.seen b.1) := by
    unfold Lane_q_s09_assign1.orderHitSet9
    rw [List.take_length, Lane_q_s09_assign1.fullOrderToFinsetEqSeen9 hAdj]
  have hfinal : (49 / 100 : ℝ) ^ order.length ≤
      ∑ z ∈ hitSet9 E G ω (I.seen b.1), μ.w z := by
    simpa [Lane_q_s09_assign1.orderHitMass9, hsetFinal] using hret
  have hfinalPos : 0 < ∑ z ∈ hitSet9 E G ω (I.seen b.1), μ.w z :=
    lt_of_lt_of_le (pow_pos (by norm_num : (0 : ℝ) < 49 / 100) _) hfinal
  have hrowRestrict : rowLaw9 S E G ω b =
      Law.restrict μ (hitSet9 E G ω (I.seen b.1)) hfinalPos := by
    unfold rowLaw9 restrictOr9
    rw [dif_pos hfinalPos]
  have hνwidth : (siteSecond9 S b.1).WidthLE (P.Ss (n : ℝ)) := by
    rcases hPrep with ⟨_, hPrep⟩
    have htag := hTags (specialWord9 (P.m n) b.1)
    rcases hPrep (S.tag (specialWord9 (P.m n) b.1)) htag with
      ⟨_, _, _, hwidth, _⟩
    simpa [siteSecond9] using hwidth
  have hprod :
      (∏ i : I.ID ⊕ OddSites9 n, (inputLaw9 S I i).w (ω i)) ≠ 0 := by
    simpa [rawLaw9, FinProb.pi] using hω
  have hmaskWeight : (S.maskLaw b).w (msk9 ω b) ≠ 0 := by
    have hcoord := (Finset.prod_ne_zero_iff.mp hprod) (Sum.inr b) (Finset.mem_univ _)
    simpa [inputLaw9, msk9] using hcoord
  have hmaskLower : (1 / 2 : ℝ) * Real.exp (-((n : ℝ) ^ P.u)) ≤
      ∑ z ∈ msk9 ω b, (siteSecond9 S b.1).w z := hMasks.1 b (msk9 ω b) hmaskWeight
  have hmaskArgPos : 0 < (1 / 2 : ℝ) * Real.exp (-((n : ℝ) ^ P.u)) := by positivity
  have hmaskMassPos : 0 < ∑ z ∈ msk9 ω b, (siteSecond9 S b.1).w z :=
    lt_of_lt_of_le hmaskArgPos hmaskLower
  have hmaskLog : Real.log ((1 / 2 : ℝ) * Real.exp (-((n : ℝ) ^ P.u))) =
      -((n : ℝ) ^ P.u) - Real.log 2 := by
    rw [Real.log_mul (by norm_num : (1 / 2 : ℝ) ≠ 0)
      (ne_of_gt (Real.exp_pos (-((n : ℝ) ^ P.u))))]
    rw [show (1 / 2 : ℝ) = (2 : ℝ)⁻¹ by norm_num, Real.log_inv, Real.log_exp]
    ring
  have hmaskLogLe :
      Real.log ((1 / 2 : ℝ) * Real.exp (-((n : ℝ) ^ P.u))) ≤
        Real.log (∑ z ∈ msk9 ω b, (siteSecond9 S b.1).w z) :=
    Real.log_le_log hmaskArgPos hmaskLower
  let baseWidth : ℝ := P.Ss (n : ℝ) + (n : ℝ) ^ P.u + Real.log 2
  have hmaskedParam : P.Ss (n : ℝ) -
      Real.log (∑ z ∈ msk9 ω b, (siteSecond9 S b.1).w z) ≤ baseWidth := by
    rw [hmaskLog] at hmaskLogLe
    dsimp [baseWidth]
    linarith
  have hmaskedEq : maskedLaw9 S ω b =
      Law.restrict (siteSecond9 S b.1) (msk9 ω b) hmaskMassPos := by
    unfold maskedLaw9 restrictOr9
    rw [dif_pos hmaskMassPos]
  have hmaskedWidth : μ.WidthLE baseWidth := by
    dsimp [μ]
    rw [hmaskedEq]
    exact Law.WidthLE.mono (Law.WidthLE.restrict hνwidth hmaskMassPos) hmaskedParam
  have hlen : (order.length : ℝ) ≤ P.idBudget n + (P.m n : ℝ) := by
    have hseen : ((I.seen b.1).card : ℝ) ≤ P.idBudget n + (P.m n : ℝ) := by
      simpa [IDMap9.seen] using I.odd_ids b.1 b.2
    change ((fullOrder9 I v b).length : ℝ) ≤ _
    rw [Lane_q_s09_assign1.fullOrderLengthEqSeenCard9 hAdj]
    exact hseen
  have hlogCoeff : 0 ≤ Real.log (100 / 49 : ℝ) :=
    Real.log_nonneg (by norm_num : (1 : ℝ) ≤ 100 / 49)
  have hbudget : baseWidth + (order.length : ℝ) * Real.log (100 / 49 : ℝ) ≤
      P.filterBudget n := by
    calc
      baseWidth + (order.length : ℝ) * Real.log (100 / 49 : ℝ) ≤
          baseWidth + (P.idBudget n + (P.m n : ℝ)) * Real.log (100 / 49 : ℝ) :=
        by
          have hmul := mul_le_mul_of_nonneg_right hlen hlogCoeff
          linarith
      _ = P.filterBudget n := by
        simp [baseWidth, Params9.filterBudget]
        ring
  have hlogPow : Real.log ((49 / 100 : ℝ) ^ order.length) =
      -((order.length : ℝ) * Real.log (100 / 49 : ℝ)) := by
    rw [Real.log_pow]
    have hratio : (49 / 100 : ℝ) = (100 / 49 : ℝ)⁻¹ := by norm_num
    rw [hratio, Real.log_inv]
    ring
  have hlogFinal : Real.log ((49 / 100 : ℝ) ^ order.length) ≤
      Real.log (∑ z ∈ hitSet9 E G ω (I.seen b.1), μ.w z) :=
    Real.log_le_log (pow_pos (by norm_num : (0 : ℝ) < 49 / 100) _) hfinal
  have hwidthParam : P.Ss (n : ℝ) + (n : ℝ) ^ P.u + Real.log 2 -
      Real.log (∑ z ∈ hitSet9 E G ω (I.seen b.1), μ.w z) ≤ P.Sd (n : ℝ) := by
    have hretainedLog := hlogFinal
    rw [hlogPow] at hretainedLog
    have hbase : baseWidth -
        Real.log (∑ z ∈ hitSet9 E G ω (I.seen b.1), μ.w z) ≤
          baseWidth + (order.length : ℝ) * Real.log (100 / 49 : ℝ) := by
      dsimp [baseWidth]
      linarith
    have hsd : P.filterBudget n ≤ P.Sd (n : ℝ) := by
      have hpow : 0 ≤ (n : ℝ) ^ P.u := by positivity
      linarith
    calc
      _ = baseWidth -
          Real.log (∑ z ∈ hitSet9 E G ω (I.seen b.1), μ.w z) := by
            simp [baseWidth]
      _ ≤ baseWidth + (order.length : ℝ) * Real.log (100 / 49 : ℝ) := hbase
      _ ≤ P.filterBudget n := hbudget
      _ ≤ P.Sd (n : ℝ) := hsd
  have hrowWidth : (rowLaw9 S E G ω b).WidthLE (P.Sd (n : ℝ)) := by
    rw [hrowRestrict]
    exact Law.WidthLE.mono (Law.WidthLE.restrict hmaskedWidth hfinalPos) hwidthParam
  have hNposR : (0 : ℝ) < N := Nat.cast_pos.mpr hN
  calc
    (N : ℝ) * (rowLaw9 S E G ω b).w y ≤
        (N : ℝ) * (Real.exp (P.Sd (n : ℝ)) / N) :=
      mul_le_mul_of_nonneg_left (hrowWidth y) (Nat.cast_nonneg N)
    _ = Real.exp (P.Sd (n : ℝ)) := by field_simp [ne_of_gt hNposR]

/-- P9.2-assignB, odd moments (09:324–327): separated odd rows (`¬ siteNear9`) have disjoint inputs (anchors of
the IDs they see and their own masks); removing the star events touching these inputs (at most
`(n+1)^{2r+8}` per row, factor `2` per row for large `n`, `S07.CondProductBound`) leaves independent raw inputs,
whose product integral is `∏ N R_b(y)`. -/
theorem p92_odd_moment (P : Params9) (hP : P.Valid) (c : ℝ) (hc : 0 < c) :
    ∃ n₀ : ℕ, ∀ n ≥ n₀, ∀ {N : ℕ} {E : Fin N → Fin N → Prop} {M : TagMix N} {G : Colour}
      (S : Setup9 P n N M) (I : IDMap9 P n),
      S07.CondProductBound → AnchorLLL9 S I E G c → StarScopeFacts9 S I E G →
        OddMoment9 S I E G := by
  have hexps := Lane_q_s09_assign1.scaleExpsOfValid9 P hP
  obtain ⟨nLog, hLog⟩ := Lane_q_s09_assign1.degreeLogSmall9 P hexps hc
  have hu : 0 < P.u := hexps.2.2.1
  have htendsto : Filter.Tendsto (fun n : ℕ => (n : ℝ) ^ P.u)
      Filter.atTop Filter.atTop :=
    (tendsto_rpow_atTop hu).comp tendsto_natCast_atTop_atTop
  obtain ⟨nCharge, hCharge⟩ := Filter.eventually_atTop.1
    (htendsto.eventually_ge_atTop (Real.log 4 / (3 * c / 4)))
  refine ⟨max 1 (max nLog nCharge), ?_⟩
  intro n hn N E M G S I hCPB hAnchor hScope
  have hn1 : 1 ≤ n := le_trans (le_max_left _ _) hn
  have hnCore : max nLog nCharge ≤ n := le_trans (le_max_right _ _) hn
  have hnLog : nLog ≤ n := le_trans (le_max_left _ _) hnCore
  have hnCharge : nCharge ≤ n := le_trans (le_max_right _ _) hnCore
  let D : ℕ := lllDegree9 P n
  let x : ℝ := P.tail c n
  have hDpos : 0 < (D : ℝ) := by dsimp [D, lllDegree9]; positivity
  have hlogD : Real.log (D : ℝ) =
      (2 * (P.radius n : ℝ) + 8) * Real.log ((n : ℝ) + 1) := by
    simp [D, lllDegree9, Real.log_pow, Nat.cast_add, Nat.cast_mul]
  have hlogDBound : Real.log (D : ℝ) ≤ (c / 4) * (n : ℝ) ^ P.u := by
    rw [hlogD]
    exact hLog n hnLog
  have hcharge : Real.log 4 ≤ (3 * c / 4) * (n : ℝ) ^ P.u := by
    have h := (div_le_iff₀ (by positivity : (0 : ℝ) < 3 * c / 4)).1
      (hCharge n hnCharge)
    nlinarith [h]
  have hsmallExp : Real.exp (-((3 * c / 4) * (n : ℝ) ^ P.u)) ≤ 1 / 4 := by
    calc
      Real.exp (-((3 * c / 4) * (n : ℝ) ^ P.u)) ≤ Real.exp (-Real.log 4) :=
        Real.exp_le_exp.mpr (by linarith [hcharge])
      _ = 1 / 4 := by
        rw [Real.exp_neg, Real.exp_log (by norm_num : (0 : ℝ) < 4)]
        norm_num
  have hDtail : (D : ℝ) * x ≤ Real.exp (-((3 * c / 4) * (n : ℝ) ^ P.u)) := by
    calc
      (D : ℝ) * x =
          Real.exp (Real.log (D : ℝ)) * Real.exp (-(c * (n : ℝ) ^ P.u)) := by
            change (D : ℝ) * Real.exp (-(c * (n : ℝ) ^ P.u)) =
              Real.exp (Real.log (D : ℝ)) * Real.exp (-(c * (n : ℝ) ^ P.u))
            exact congrArg (fun z : ℝ => z * Real.exp (-(c * (n : ℝ) ^ P.u)))
              (Real.exp_log hDpos).symm
      _ = Real.exp (Real.log (D : ℝ) - c * (n : ℝ) ^ P.u) := by
            rw [← Real.exp_add]
            congr 1 <;> ring
      _ ≤ Real.exp (-((3 * c / 4) * (n : ℝ) ^ P.u)) := Real.exp_le_exp.mpr (by
            nlinarith [hlogDBound])
  have hxSmall : x ≤ Real.exp (-((3 * c / 4) * (n : ℝ) ^ P.u)) := by
    dsimp [x, Params9.tail]
    apply Real.exp_le_exp.mpr
    have hpow : 0 ≤ (n : ℝ) ^ P.u := by positivity
    nlinarith [mul_nonneg (by positivity : (0 : ℝ) ≤ c / 4) hpow]
  have hsmall : ((D : ℝ) + 1) * x ≤ 1 / 2 := by
    calc
      ((D : ℝ) + 1) * x = (D : ℝ) * x + x := by ring
      _ ≤ 2 * Real.exp (-((3 * c / 4) * (n : ℝ) ^ P.u)) := by
        nlinarith [hDtail, hxSmall]
      _ ≤ 1 / 2 := by linarith [hsmallExp]
  have hxpos : 0 < x := by dsimp [x, Params9.tail]; exact Real.exp_pos _
  have hxlt : x < 1 := by
    dsimp [x, Params9.tail]
    calc
      Real.exp (-(c * (n : ℝ) ^ P.u)) < Real.exp 0 :=
        Real.exp_lt_exp.mpr (neg_lt_zero.mpr (by positivity : 0 < c * (n : ℝ) ^ P.u))
      _ = 1 := by simp
  have hBern : 1 - ((D : ℝ) + 1) * x ≤ (1 - x) ^ (D + 1) := by
    have h := one_add_mul_le_pow (a := -x) (by linarith [hxlt]) (D + 1)
    have h' := h
    rw [Nat.cast_add, Nat.cast_one] at h'
    have h'' : 1 + ((D : ℝ) + 1) * (-x) ≤ (1 - x) ^ (D + 1) := by
      simpa [sub_eq_add_neg] using h'
    calc
      1 - ((D : ℝ) + 1) * x = 1 + ((D : ℝ) + 1) * (-x) := by ring
      _ ≤ (1 - x) ^ (D + 1) := h''
  have hden : (1 / 2 : ℝ) ≤ (1 - x) ^ (D + 1) := by linarith [hBern, hsmall]
  have hbasePos : 0 < (1 - x) ^ (D + 1) := pow_pos (by linarith [hxlt]) _
  have hbaseInv : ((1 - x) ^ (D + 1))⁻¹ ≤ 2 := by
    simpa [one_div] using one_div_le_one_div_of_le
      (by norm_num : (0 : ℝ) < 1 / 2) hden
  have hpowCost : ∀ k : ℕ,
      (1 / 2 : ℝ) ^ k ≤ (1 - x) ^ (k * (D + 1)) := by
    intro k
    have hpow : ∀ m : ℕ, (1 / 2 : ℝ) ^ m ≤ ((1 - x) ^ (D + 1)) ^ m := by
      intro m
      induction m with
      | zero => simp
      | succ m ih =>
          rw [pow_succ, pow_succ]
          calc
            (1 / 2 : ℝ) ^ m * (1 / 2 : ℝ) ≤ ((1 - x) ^ (D + 1)) ^ m * (1 / 2 : ℝ) :=
              mul_le_mul_of_nonneg_right ih (by norm_num)
            _ ≤ ((1 - x) ^ (D + 1)) ^ m * (1 - x) ^ (D + 1) :=
              mul_le_mul_of_nonneg_left hden (pow_nonneg (by linarith [hden]) m)
    calc
      (1 / 2 : ℝ) ^ k ≤ ((1 - x) ^ (D + 1)) ^ k :=
        hpow k
      _ = (1 - x) ^ (k * (D + 1)) := by
        calc
          ((1 - x) ^ (D + 1)) ^ k = (1 - x) ^ ((D + 1) * k) := by rw [pow_mul]
          _ = (1 - x) ^ (k * (D + 1)) := by
            congr 1
            exact Nat.mul_comm _ _
  intro y k hk s hsep
  let j₀ : Fin n := ⟨0, by omega⟩
  let starAt : Fin k → EvenSites9 n := fun i =>
    ⟨cubeFlip (s i).1 j₀, (cubeFlip_parity (s i).1 j₀).2 (s i).2⟩
  have hAdj (i : Fin k) : (cube n).Adj (starAt i).1 (s i).1 := by
    simpa [starAt] using (cubeFlip_adj (s i).1 j₀).symm
  let U : Finset (I.ID ⊕ OddSites9 n) :=
    (Finset.univ : Finset (Fin k)).biUnion (fun i => starScope9 I (starAt i))
  let scopes : Fin k → Finset (I.ID ⊕ OddSites9 n) :=
    fun i => Lane_q_s09_assign1.oddRowInputs9 (I := I) (s i)
  have hscopeSub (i : Fin k) : scopes i ⊆ U := by
    calc
      scopes i ⊆ starScope9 I (starAt i) :=
        Lane_q_s09_assign1.oddRowInputsSubsetStarScope9 (hAdj i)
      _ ⊆ U := Finset.subset_biUnion_of_mem (fun j => starScope9 I (starAt j))
        (Finset.mem_univ i)
  let rowFn : Fin k → Outcome9 I N → ℝ := fun i ω =>
    (N : ℝ) * (rowLaw9 S E G ω (s i)).w y
  let Φ : Outcome9 I N → ℝ := fun ω => ∏ i, rowFn i ω
  have hrowDep (i : Fin k) : FinProb.DependsOn (rowFn i) (scopes i) := by
    intro ω ω' hagree
    have hrow := Lane_q_s09_assign1.rowLawDependsOnInputs9 S E G (s i) ω ω' hagree
    simpa [rowFn] using congrArg (fun L : Law N => (N : ℝ) * L.w y) hrow
  have hΦDep : FinProb.DependsOn Φ U := by
    intro ω ω' hagree
    unfold Φ
    apply Finset.prod_congr rfl
    intro i hi
    exact hrowDep i ω ω' (fun q hq => hagree q (hscopeSub i hq))
  have hΦNonneg (ω : Outcome9 I N) : 0 ≤ Φ ω := by
    unfold Φ rowFn
    apply Finset.prod_nonneg
    intro i hi
    exact mul_nonneg (Nat.cast_nonneg N) ((rowLaw9 S E G ω (s i)).nonneg y)
  have hnotNear (i j : Fin k) (hij : i ≠ j) :
      ¬ siteNear9 P n (s i).1 (s j).1 := by
    by_cases hji : j < i
    · exact hsep i j hji
    · have hij' : i < j := by omega
      intro hnear
      exact hsep j i hij' (by simpa [siteNear9, _root_.hammingDist_comm] using hnear)
  have hrowDisjoint (i j : Fin k) (hij : i ≠ j) : Disjoint (scopes i) (scopes j) :=
    Lane_q_s09_assign1.oddRowInputsDisjointOfNotNear9 (s i) (s j) (hnotNear i j hij)
  have hprodFactor := Lane_q_s09_assign1.piExpectProdDisjoint9 (inputLaw9 S I)
    rowFn scopes hrowDep hrowDisjoint (Finset.univ : Finset (Fin k))
  have hmean (i : Fin k) :
      (FinProb.pi (inputLaw9 S I)).expect (rowFn i) =
        (N : ℝ) * (rawRowLaw9 S I E G (s i)).w y := by
    simp only [FinProb.expect, FinProb.pi, rowFn, rawRowLaw9, Law.mix, rawLaw9]
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro ω hω
    ring
  have hrawFactor :
      (rawLaw9 S I).expect Φ =
        ∏ i, (N : ℝ) * (rawRowLaw9 S I E G (s i)).w y := by
    calc
      (rawLaw9 S I).expect Φ = (FinProb.pi (inputLaw9 S I)).expect Φ := rfl
      _ = ∏ i ∈ (Finset.univ : Finset (Fin k)),
          (FinProb.pi (inputLaw9 S I)).expect (rowFn i) := hprodFactor
      _ = ∏ i, (N : ℝ) * (rawRowLaw9 S I E G (s i)).w y := by
          apply Finset.prod_congr rfl
          intro i hi
          exact hmean i
  let B : ℝ := ∏ i, (N : ℝ) * (rawRowLaw9 S I E G (s i)).w y
  have hBNonneg : 0 ≤ B := by
    unfold B
    apply Finset.prod_nonneg
    intro i hi
    exact mul_nonneg (Nat.cast_nonneg N) ((rawRowLaw9 S I E G (s i)).nonneg y)
  have hfree (ω₀ : Outcome9 I N) :
      (∑ a : (∀ i : U, Val9 I N i.1),
        (∏ i : U, (inputLaw9 S I i.1).w (a i)) * Φ (S07.glue U ω₀ a)) ≤ B := by
    calc
      _ = (rawLaw9 S I).expect Φ :=
        Lane_q_s09_assign1.piExpectGlue9 (inputLaw9 S I) U Φ ω₀ hΦDep
      _ = B := by simpa [B] using hrawFactor
      _ ≤ B := le_rfl
  have hCostInput : S07.LLLInput (inputLaw9 S I)
      (fun v ω => StarBad9 S E G ω v) (starScope9 I) x D := by
    simpa [AnchorLLL9, x, D] using hAnchor
  have hcond := hCPB (inputLaw9 S I) (fun v ω => StarBad9 S E G ω v)
    (starScope9 I) x D hCostInput
  let T : Finset (EvenSites9 n) := Finset.univ.filter (fun v : EvenSites9 n =>
    ¬ Disjoint (starScope9 I v) U)
  have hTBound : T.card ≤ k * (D + 1) := by
    simpa [T, U, D] using
      (Lane_q_s09_assign1.starEventsTouchingOddNeighborhoods9 S E G hScope starAt)
  have hqpow : (1 / 2 : ℝ) ^ k ≤ (1 - x) ^ T.card := by
    calc
      (1 / 2 : ℝ) ^ k ≤ (1 - x) ^ (k * (D + 1)) := hpowCost k
      _ ≤ (1 - x) ^ T.card :=
        pow_le_pow_of_le_one (by linarith [hxpos, hxlt]) (by linarith [hxpos]) hTBound
  have hcost : ((1 - x) ^ T.card)⁻¹ ≤ (2 : ℝ) ^ k := by
    have hOneDiv := one_div_le_one_div_of_le
      (pow_pos (by norm_num : (0 : ℝ) < 1 / 2) k) hqpow
    calc
      ((1 - x) ^ T.card)⁻¹ = 1 / (1 - x) ^ T.card := by rw [one_div]
      _ ≤ 1 / (1 / 2 : ℝ) ^ k := hOneDiv
      _ = (2 : ℝ) ^ k := by
        have hhalf : (1 / 2 : ℝ) ^ k * (2 : ℝ) ^ k = 1 := by
          rw [← mul_pow]
          norm_num
        field_simp [one_div, pow_ne_zero k (by norm_num : (2 : ℝ) ≠ 0)]
        nlinarith [hhalf]
  have hbound := hcond.2 U Φ hΦNonneg B hfree
  have hanchorEq : anchorLaw9 S I E G =
      S07.condOr (FinProb.pi (inputLaw9 S I))
        (fun ω => ∀ v : EvenSites9 n, ¬ StarBad9 S E G ω v) := rfl
  have hbound' : (anchorLaw9 S I E G).expect Φ ≤ ((1 - x) ^ T.card)⁻¹ * B := by
    rw [hanchorEq]
    simpa [T] using hbound
  have hfinal : (anchorLaw9 S I E G).expect Φ ≤ (2 : ℝ) ^ k * B := by
    calc
      (anchorLaw9 S I E G).expect Φ ≤ ((1 - x) ^ T.card)⁻¹ * B := hbound'
      _ ≤ (2 : ℝ) ^ k * B := mul_le_mul_of_nonneg_right hcost hBNonneg
  simpa [Φ, rowFn, B] using hfinal

set_option maxHeartbeats 5000000 in
/-- P9.2-assignB, odd column sums (09:322–327): Lemma 3.6 with weights `N p_b(y)`, cap `e^{S_d}` on the
avoidance event (`RowCap9`), near fraction at most `(n+1)^{4r+12} 2^{1-n}` (and
`n (n+1)^{4r+12} 2^{1-n} e^{S_d} ≤ 1`), comparison means `N R_b(y) ≤ (1 + e^{-n^u}) N ν_{i_{z(b)}}(y)` of average at
most `2 · tagLoadConst9 κ` (`MasksOK9`, `TagsOK9`), and a union over the at most `n 2^n` labels; the column sum is
`2^{n-1}/N` times the normalized average, at most `θ₀ = 10⁻⁸` once `N ≥ C₀ 2^n`. -/
theorem p92_odd_loads (P : Params9) (hP : P.Valid) (κ : ℝ) (hκ : 0 < κ) :
    ∃ n₀ : ℕ, ∃ C₀ : ℝ, ∀ n N : ℕ, LargeAt n₀ C₀ n N →
      ∀ {E : Fin N → Fin N → Prop} {X Y : Finset (Fin N)} {G : Colour} {M : TagMix N}
        (S : Setup9 P n N M) (I : IDMap9 P n) (cT : ℝ),
        CoreInput9 P κ E X Y G M S I → TagsOK9 κ E G cT S.tag → RowCap9 S I E G →
        OddMoment9 S I E G → 0 < (rawLaw9 S I).pr (fun ω => ∀ v, ¬ StarBad9 S E G ω v) →
        (anchorLaw9 S I E G).pr (fun ω => ∃ y, (1e-8 : ℝ) < oddColumn9 S E G ω y) ≤
          (n : ℝ) * 2 ^ n * (1 / 4 : ℝ) ^ n := by
  obtain ⟨nDeep, hDeep⟩ := Lane_q_s09_assign1.deepWidthSmall9 P hP
  obtain ⟨nLog, hLog⟩ := Lane_q_s09_assign1.natLogSmall9
  let n₀ := max 2 (max nDeep nLog)
  let D₀ : ℝ := 4 * tagLoadConst9 κ
  let threshold : ℝ := 4 * 2 * (D₀ + 1)
  let C₀ : ℝ := threshold / (1e-8 : ℝ) + 1
  have hκ0 : 0 < κ := hκ
  have hD₀ : 0 ≤ D₀ := by
    dsimp [D₀, tagLoadConst9]
    positivity
  have hThreshold : 0 < threshold := by dsimp [threshold]; positivity
  have hC₀ : 0 < C₀ := by dsimp [C₀]; positivity
  refine ⟨n₀, C₀, ?_⟩
  intro n N hLarge E X Y G M S I cT hCore hTags hRowCap hOddMoment hAvoidPos
  have hn₀₂ : 2 ≤ n₀ := by
    dsimp [n₀]
    exact le_max_left _ _
  have hn₀Deep : nDeep ≤ n₀ := by
    dsimp [n₀]
    exact le_trans (le_max_left _ _) (le_max_right _ _)
  have hn₀Log : nLog ≤ n₀ := by
    dsimp [n₀]
    exact le_trans (le_max_right _ _) (le_max_right _ _)
  have hn₂ : 2 ≤ n := le_trans hn₀₂ hLarge.1
  have hnDeep : nDeep ≤ n := le_trans hn₀Deep hLarge.1
  have hnLog : nLog ≤ n := le_trans hn₀Log hLarge.1
  have hn : 0 < n := by omega
  have hnR : 0 < (n : ℝ) := by exact_mod_cast hn
  have hnR1 : 1 ≤ (n : ℝ) := by exact_mod_cast (show 1 ≤ n by omega)
  rcases hCore with ⟨hNpos, hPrep, hDeepAt, hTagPos, hMasks, hDeepTools, hExps, hScales⟩
  rcases hScales with ⟨hnScales, hmle, hradius, hShallow, hFilterBudget,
    hDeepMargin, hbStar, hGain⟩
  rcases hTags with ⟨hTagPositive, hTagLoad, hTagBad⟩
  rcases hTagLoad with ⟨hTagFirst, hTagSecond⟩
  rcases hMasks with ⟨hMaskMass, hRawMean⟩
  rcases hP with ⟨_, hBias, _, _, _, _, _⟩
  rcases hBias with ⟨hMinusPos, hMinusPlus, hPlusLess⟩
  have hPlusPos : 0 < (P.hPlus : ℝ) := by exact_mod_cast hMinusPos.trans hMinusPlus
  have hStarPow : (n : ℝ) ^ (-(P.hPlus : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos hnR1 (by linarith)
  have hStar : P.aStar n ≤ 1 / 2 := by
    dsimp [Params9.aStar]
    nlinarith
  have hLogNonneg : 0 ≤ Real.log ((n : ℝ) + 1) := by
    apply Real.log_nonneg
    linarith
  have hNatLog : Real.log (n : ℝ) ≤ (n : ℝ) / 100 := hLog n hnLog
  have hDeepWidth : P.Sd (n : ℝ) ≤ (n : ℝ) / 10 := hDeep n hnDeep
  let R : ℕ := 4 * P.radius n + 12
  let f : ℝ := ((n : ℝ) + 1) ^ R / (2 : ℝ) ^ (n - 1)
  let L : ℝ := Real.exp (P.Sd (n : ℝ))
  have hRadiusPlus : (R : ℝ) ≤ 4 * ((P.radius n : ℝ) + 8) := by
    dsimp [R]
    push_cast
    nlinarith
  have hRadiusLog : ((P.radius n : ℝ) + 8) * Real.log ((n : ℝ) + 1) ≤
      (n : ℝ) / 400 := by
    have hGainRhs : gainConst9 * (n : ℝ) * P.aStar n / 100 ≤ (n : ℝ) / 400 := by
      rw [gainConst9]
      nlinarith [hStar]
    have hRestNonneg : 0 ≤
        (n : ℝ) ^ (P.xS : ℝ) + 4 * (n : ℝ) ^ P.u := by positivity
    nlinarith [hGain, hGainRhs, hRestNonneg]
  have hRLog : (R : ℝ) * Real.log ((n : ℝ) + 1) ≤ (n : ℝ) / 100 := by
    calc
      (R : ℝ) * Real.log ((n : ℝ) + 1) ≤
          4 * ((P.radius n : ℝ) + 8) * Real.log ((n : ℝ) + 1) :=
            mul_le_mul_of_nonneg_right hRadiusPlus hLogNonneg
      _ ≤ 4 * ((n : ℝ) / 400) :=
        calc
          4 * ((P.radius n : ℝ) + 8) * Real.log ((n : ℝ) + 1) =
              4 * (((P.radius n : ℝ) + 8) * Real.log ((n : ℝ) + 1)) := by ring
          _ ≤ 4 * ((n : ℝ) / 400) :=
            mul_le_mul_of_nonneg_left hRadiusLog (show (0 : ℝ) ≤ (4 : ℝ) by norm_num)
      _ = (n : ℝ) / 100 := by ring
  have hnearExp :
      Real.exp ((R : ℝ) * Real.log ((n : ℝ) + 1)) = ((n : ℝ) + 1) ^ R := by
    calc
      Real.exp ((R : ℝ) * Real.log ((n : ℝ) + 1)) =
          Real.exp (Real.log ((n : ℝ) + 1)) ^ R := by rw [Real.exp_nat_mul]
      _ = ((n : ℝ) + 1) ^ R := by rw [Real.exp_log (by positivity)]
  have hDenExp : (2 : ℝ) ^ (n - 1) =
      Real.exp (((n - 1 : ℕ) : ℝ) * Real.log 2) := by
    calc
      (2 : ℝ) ^ (n - 1) = Real.exp (Real.log 2) ^ (n - 1) := by
        rw [Real.exp_log (by norm_num : (0 : ℝ) < 2)]
      _ = Real.exp (((n - 1 : ℕ) : ℝ) * Real.log 2) :=
        (Real.exp_nat_mul (Real.log 2) (n - 1)).symm
  have hlogTwo : (1 / 2 : ℝ) ≤ Real.log 2 := by
    linarith [Real.log_two_gt_d9]
  have hNatSubCast : ((n - 1 : ℕ) : ℝ) = (n : ℝ) - 1 := by
    have h := Nat.sub_add_cancel (show 1 ≤ n by omega)
    have h' : ((n - 1 : ℕ) : ℝ) + 1 = (n : ℝ) := by exact_mod_cast h
    linarith
  have hDenArg : ((n - 1 : ℕ) : ℝ) * Real.log 2 ≥ ((n : ℝ) - 1) / 2 := by
    rw [hNatSubCast]
    have hlogTwo' : (2 : ℝ)⁻¹ ≤ Real.log 2 := by norm_num [one_div] at hlogTwo ⊢ <;> linarith
    exact mul_le_mul_of_nonneg_left hlogTwo' (by linarith : 0 ≤ (n : ℝ) - 1)
  have hnR₂ : 2 ≤ (n : ℝ) := by exact_mod_cast hn₂
  have hExponent : Real.log (n : ℝ) + (R : ℝ) * Real.log ((n : ℝ) + 1) +
      P.Sd (n : ℝ) - ((n - 1 : ℕ) : ℝ) * Real.log 2 ≤ 0 := by
    linarith [hNatLog, hRLog, hDeepWidth, hDenArg, hnR₂]
  have hNumerExp : (n : ℝ) * ((n : ℝ) + 1) ^ R * L =
      Real.exp (Real.log (n : ℝ) + (R : ℝ) * Real.log ((n : ℝ) + 1) + P.Sd (n : ℝ)) := by
    dsimp [L]
    calc
      (n : ℝ) * ((n : ℝ) + 1) ^ R * Real.exp (P.Sd (n : ℝ)) =
          Real.exp (Real.log (n : ℝ)) *
            Real.exp ((R : ℝ) * Real.log ((n : ℝ) + 1)) * Real.exp (P.Sd (n : ℝ)) := by
              rw [Real.exp_log hnR, ← hnearExp]
      _ = Real.exp (Real.log (n : ℝ) + (R : ℝ) * Real.log ((n : ℝ) + 1) +
            P.Sd (n : ℝ)) := by rw [← Real.exp_add, ← Real.exp_add]
  have hFracSmall : (n : ℝ) * f * L ≤ 1 := by
    dsimp [f]
    calc
      (n : ℝ) * (((n : ℝ) + 1) ^ R / (2 : ℝ) ^ (n - 1)) * L =
          ((n : ℝ) * ((n : ℝ) + 1) ^ R * L) / (2 : ℝ) ^ (n - 1) := by ring
      _ = Real.exp (Real.log (n : ℝ) + (R : ℝ) * Real.log ((n : ℝ) + 1) +
            P.Sd (n : ℝ)) /
          Real.exp (((n - 1 : ℕ) : ℝ) * Real.log 2) := by rw [hNumerExp, hDenExp]
      _ = Real.exp (Real.log (n : ℝ) + (R : ℝ) * Real.log ((n : ℝ) + 1) +
            P.Sd (n : ℝ) - ((n - 1 : ℕ) : ℝ) * Real.log 2) := by rw [Real.exp_sub]
      _ ≤ 1 := Real.exp_le_one_iff.mpr hExponent
  let avoid : Outcome9 I N → Prop := fun ω => ∀ v, ¬ StarBad9 S E G ω v
  let succ : Finset (Outcome9 I N) := Finset.univ.filter (fun ω =>
    (rawLaw9 S I).w ω ≠ 0 ∧ avoid ω)
  let Q : FinProb (Outcome9 I N) := anchorLaw9 S I E G
  have hQw (ω : Outcome9 I N) : Q.w ω =
      (if avoid ω then (rawLaw9 S I).w ω else 0) /
        (rawLaw9 S I).pr avoid := by
    change (S07.condOr (rawLaw9 S I) avoid).w ω = _
    have hAvoidPos' : 0 < (rawLaw9 S I).pr avoid := by
      simpa [avoid] using hAvoidPos
    have hcond : S07.condOr (rawLaw9 S I) avoid =
        (rawLaw9 S I).cond avoid hAvoidPos' := by
      unfold S07.condOr
      rw [dif_pos hAvoidPos']
    rw [hcond]
    by_cases hA : avoid ω <;> simp [FinProb.cond, hA]
  have hQzero (ω : Outcome9 I N) (hω : ω ∉ succ) : Q.w ω = 0 := by
    by_cases ha : avoid ω
    · have hr : (rawLaw9 S I).w ω = 0 := by
        by_contra hr
        apply hω
        exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, ⟨hr, ha⟩⟩
      simp [hQw, ha, hr]
    · simp [hQw, ha]
  have hQsupport (ω : Outcome9 I N) (hω : Q.w ω ≠ 0) : ω ∈ succ := by
    by_contra hnot
    exact hω (hQzero ω hnot)
  let near : OddSites9 n → Finset (OddSites9 n) := fun b =>
    Finset.univ.filter (fun b' => siteNear9 P n b.1 b'.1)
  have hself : ∀ b, b ∈ near b := by
    intro b
    have hsite : siteNear9 P n b.1 b.1 := by
      unfold siteNear9
      rw [_root_.hammingDist_self, _root_.hammingDist_self]
      constructor <;> omega
    change b ∈ Finset.univ.filter (fun b' : OddSites9 n => siteNear9 P n b.1 b'.1)
    rw [Finset.mem_filter]
    exact ⟨Finset.mem_univ b, hsite⟩
  have hnear : ∀ b, ((near b).card : ℝ) ≤ f * Fintype.card (OddSites9 n) := by
    intro b
    have hNearCount := Lane_q_s09_assign1.oddNearCardBound9 P n b
    have hcast : ((near b).card : ℝ) ≤ ((n : ℝ) + 1) ^ R := by
      dsimp [near, R] at hNearCount ⊢
      exact_mod_cast hNearCount
    have hOddCard : Fintype.card (OddSites9 n) = 2 ^ (n - 1) :=
      Lane_q_s09_assign1.oddSitesCardPow9 hn
    calc
      ((near b).card : ℝ) ≤ ((n : ℝ) + 1) ^ R := hcast
      _ = f * (Fintype.card (OddSites9 n) : ℝ) := by
        dsimp [f]
        rw [hOddCard]
        field_simp
        norm_num
  let d : OddSites9 n → Fin N → ℝ := fun b y =>
    (N : ℝ) * (rawRowLaw9 S I E G b).w y
  have hd : ∀ b y, 0 ≤ d b y := by
    intro b y
    exact mul_nonneg (Nat.cast_nonneg N) ((rawRowLaw9 S I E G b).nonneg y)
  have hmean : ∀ y, (Fintype.card (OddSites9 n) : ℝ)⁻¹ *
      ∑ b, d b y ≤ D₀ := by
    intro y
    let g : CubeVertex (P.m n) → ℝ := fun z =>
      (N : ℝ) * (M.ν (S.tag z)).w y
    have hg : ∀ z, 0 ≤ g z := by
      intro z
      exact mul_nonneg (Nat.cast_nonneg N) ((M.ν (S.tag z)).nonneg y)
    have hsite : (Fintype.card (OddSites9 n) : ℝ)⁻¹ *
        ∑ b : OddSites9 n, (N : ℝ) * (siteSecond9 S b.1).w y ≤
          2 * tagLoadConst9 κ := by
      have havg := Lane_q_s09_assign1.oddSpecialAverageBound9 hmle hn g hg
      have htagMean : (Fintype.card (CubeVertex (P.m n)) : ℝ)⁻¹ *
          ∑ z, g z ≤ tagLoadConst9 κ := by
        simpa [g] using hTagSecond y
      have htagBound : 2 * ((Fintype.card (CubeVertex (P.m n)) : ℝ)⁻¹ *
          ∑ z, g z) ≤ 2 * tagLoadConst9 κ :=
        mul_le_mul_of_nonneg_left htagMean (show (0 : ℝ) ≤ (2 : ℝ) by norm_num)
      calc
        _ ≤ 2 * (Fintype.card (CubeVertex (P.m n)) : ℝ)⁻¹ * ∑ z, g z := by
          simpa [g, siteSecond9] using havg
        _ = 2 * ((Fintype.card (CubeVertex (P.m n)) : ℝ)⁻¹ * ∑ z, g z) := by ring
        _ ≤ 2 * tagLoadConst9 κ := htagBound
    have hExpLe : Real.exp (-((n : ℝ) ^ P.u)) ≤ 1 := by
      apply Real.exp_le_one_iff.mpr
      have hpow : 0 ≤ (n : ℝ) ^ P.u := by positivity
      exact neg_nonpos.mpr hpow
    have hfactor : 1 + Real.exp (-((n : ℝ) ^ P.u)) ≤ 2 := by linarith
    have hcompare (b : OddSites9 n) :
        (N : ℝ) * (rawRowLaw9 S I E G b).w y ≤
          2 * ((N : ℝ) * (siteSecond9 S b.1).w y) := by
      have hcmp := hRawMean b y
      calc
        _ ≤ (N : ℝ) * ((1 + Real.exp (-((n : ℝ) ^ P.u))) *
              (siteSecond9 S b.1).w y) := mul_le_mul_of_nonneg_left hcmp (Nat.cast_nonneg N)
        _ ≤ (N : ℝ) * (2 * (siteSecond9 S b.1).w y) := by
          apply mul_le_mul_of_nonneg_left
          · exact mul_le_mul_of_nonneg_right hfactor ((siteSecond9 S b.1).nonneg y)
          · exact Nat.cast_nonneg N
        _ = 2 * ((N : ℝ) * (siteSecond9 S b.1).w y) := by ring
    have hsumCompare : (∑ b : OddSites9 n, d b y) ≤
        ∑ b : OddSites9 n, 2 * ((N : ℝ) * (siteSecond9 S b.1).w y) := by
      apply Finset.sum_le_sum
      intro b hb
      exact hcompare b
    calc
      (Fintype.card (OddSites9 n) : ℝ)⁻¹ * ∑ b, d b y ≤
          (Fintype.card (OddSites9 n) : ℝ)⁻¹ *
            ∑ b : OddSites9 n, 2 * ((N : ℝ) * (siteSecond9 S b.1).w y) :=
        mul_le_mul_of_nonneg_left hsumCompare (inv_nonneg.mpr (Nat.cast_nonneg _))
      _ = 2 * ((Fintype.card (OddSites9 n) : ℝ)⁻¹ *
            ∑ b : OddSites9 n, (N : ℝ) * (siteSecond9 S b.1).w y) := by
        rw [← Finset.mul_sum]
        ring
      _ ≤ 2 * (2 * tagLoadConst9 κ) := mul_le_mul_of_nonneg_left hsite (by norm_num)
      _ = D₀ := by dsimp [D₀]; ring
  let Z : OddSites9 n → Fin N → Outcome9 I N → ℝ := fun b y ω =>
    (N : ℝ) * (rowLaw9 S E G ω b).w y
  have hZ0 : ∀ b y ω, 0 ≤ Z b y ω := by
    intro b y ω
    exact mul_nonneg (Nat.cast_nonneg N) ((rowLaw9 S E G ω b).nonneg y)
  have hL : 0 ≤ L := by dsimp [L]; positivity
  have hZL : ∀ b y ω, ω ∈ succ → Z b y ω ≤ L := by
    intro b y ω hω
    rcases Finset.mem_filter.mp hω with ⟨_, ⟨hRaw, hAvoid⟩⟩
    have hregular : ∀ v, starRegular9 S E G ω v := by
      intro v
      have hnot := hAvoid v
      unfold StarBad9 at hnot
      have hvalid : starValid9 S E G ω v := by
        by_contra hv
        exact hnot (Or.inl hv)
      exact hvalid.1
    have hcap := hRowCap ω hRaw hregular b y
    simpa [Z, L] using hcap
  have hK : 1 ≤ (2 : ℝ) := by norm_num
  have hd0 : 0 ≤ D₀ := hD₀
  have hjoint : ∀ y (k : ℕ), k ≤ n → ∀ s : Fin k → OddSites9 n,
      (∀ i j : Fin k, j < i → s i ∉ near (s j)) →
        ∑ ω ∈ succ, Q.w ω * ∏ i, Z (s i) y ω ≤
          (2 : ℝ) ^ k * ∏ i, d (s i) y := by
    intro y k hk s hsep
    have hsep' : ∀ i j : Fin k, j < i →
        ¬ siteNear9 P n (s i).1 (s j).1 := by
      intro i j hji
      intro hnear
      have hsymm : siteNear9 P n (s j).1 (s i).1 := by
        rcases hnear with ⟨hs, hr⟩
        exact ⟨by simpa [siteNear9, _root_.hammingDist_comm] using hs,
          by simpa [siteNear9, _root_.hammingDist_comm] using hr⟩
      have hmem : s i ∈ near (s j) := by
        change s i ∈ Finset.univ.filter
          (fun b' : OddSites9 n => siteNear9 P n (s j).1 b'.1)
        exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, hsymm⟩
      exact hsep i j hji hmem
    have hmom := hOddMoment y k hk s hsep'
    have hΦnonneg (ω : Outcome9 I N) : 0 ≤ ∏ i, Z (s i) y ω := by
      apply Finset.prod_nonneg
      intro i hi
      exact hZ0 (s i) y ω
    have hsubset :
        (∑ ω ∈ succ, Q.w ω * ∏ i, Z (s i) y ω) ≤
          ∑ ω, Q.w ω * ∏ i, Z (s i) y ω := by
      apply Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ succ)
      intro ω hω hnot
      exact mul_nonneg (Q.nonneg ω) (hΦnonneg ω)
    calc
      (∑ ω ∈ succ, Q.w ω * ∏ i, Z (s i) y ω) ≤
          (anchorLaw9 S I E G).expect (fun ω => ∏ i, (N : ℝ) *
            (rowLaw9 S E G ω (s i)).w y) := by
              simpa [FinProb.expect, Z] using hsubset
      _ ≤ (2 : ℝ) ^ k * ∏ i, (N : ℝ) * (rawRowLaw9 S I E G (s i)).w y := hmom
      _ = (2 : ℝ) ^ k * ∏ i, d (s i) y := by simp [d]
  have hlabels : (Fintype.card (Fin N) : ℝ) ≤ (n : ℝ) * 2 ^ n := by
    simp only [Fintype.card_fin]
    exact_mod_cast hLarge.2.2
  have hsmall := hFracSmall
  have hf : 0 ≤ f := by dsimp [f]; positivity
  have hOddNonempty : Nonempty (OddSites9 n) := by
    let v : CubeVertex n := fun _ => false
    let j : Fin n := ⟨0, by omega⟩
    have hv : IsEvenRole v := by simp [v, IsEvenRole]
    have hflip : ¬ IsEvenRole (cubeFlip v j) := by
      intro h
      exact (cubeFlip_parity v j).mp h hv
    exact ⟨⟨cubeFlip v j, hflip⟩⟩
  letI : Nonempty (OddSites9 n) := hOddNonempty
  have htail := scatteredMoments_union_labels Q succ Z hZ0 L hL hZL near hself f
    hf hnear n hn (2 : ℝ) D₀ hK hD₀ d hd hmean hjoint hsmall hlabels
  let average : Fin N → Outcome9 I N → ℝ := fun y ω =>
    (Fintype.card (OddSites9 n) : ℝ)⁻¹ * ∑ b, Z b y ω
  let largeAverage : Outcome9 I N → Prop := fun ω =>
    ω ∈ succ ∧ ∃ y, threshold < average y ω
  have htailProb : Q.pr largeAverage ≤ (n : ℝ) * 2 ^ n * (1 / 4 : ℝ) ^ n := by
    simpa [largeAverage, FinProb.pr, average, threshold, Z] using htail
  let target : Outcome9 I N → Prop := fun ω =>
    ∃ y, (1e-8 : ℝ) < oddColumn9 S E G ω y
  have htargetSupport : Q.pr target = Q.pr (fun ω => target ω ∧ ω ∈ succ) := by
    unfold FinProb.pr
    apply Finset.sum_congr rfl
    intro ω hω
    by_cases ht : target ω
    · by_cases hs : ω ∈ succ
      · simp [ht, hs]
      · have hzero := hQzero ω hs
        simp [ht, hs, hzero]
    · simp [ht]
  have hOddCardNat : Fintype.card (OddSites9 n) = 2 ^ (n - 1) :=
    Lane_q_s09_assign1.oddSitesCardPow9 hn
  have hOddCard : (Fintype.card (OddSites9 n) : ℝ) = (2 : ℝ) ^ (n - 1) := by
    exact_mod_cast hOddCardNat
  have hOddCardPos : 0 < (Fintype.card (OddSites9 n) : ℝ) := by rw [hOddCard]; positivity
  have hpowTwo : (2 : ℝ) ^ n = 2 * (2 : ℝ) ^ (n - 1) := by
    have hnPow : n = n - 1 + 1 := by omega
    calc
      (2 : ℝ) ^ n = (2 : ℝ) ^ (n - 1 + 1) :=
        congrArg (fun k : ℕ => (2 : ℝ) ^ k) hnPow
      _ = (2 : ℝ) ^ (n - 1) * 2 := by rw [pow_succ]
      _ = 2 * (2 : ℝ) ^ (n - 1) := by ring
  have hratioEq : C₀ * (2 : ℝ) ^ n /
      (Fintype.card (OddSites9 n) : ℝ) = 2 * C₀ := by
    rw [hOddCard, hpowTwo]
    field_simp [pow_ne_zero (n - 1) (by norm_num : (2 : ℝ) ≠ 0)]
  have hratio : 2 * C₀ ≤ (N : ℝ) / (Fintype.card (OddSites9 n) : ℝ) := by
    calc
      2 * C₀ = C₀ * (2 : ℝ) ^ n /
          (Fintype.card (OddSites9 n) : ℝ) := hratioEq.symm
      _ ≤ (N : ℝ) / (Fintype.card (OddSites9 n) : ℝ) :=
        div_le_div_of_nonneg_right hLarge.2.1 hOddCardPos.le
  have hratioPos : 0 < (N : ℝ) / (Fintype.card (OddSites9 n) : ℝ) :=
    lt_of_lt_of_le (mul_pos (by norm_num) hC₀) hratio
  have hEpsPos : 0 < (1e-8 : ℝ) := by norm_num
  have hC₀Eps : C₀ * (1e-8 : ℝ) = threshold + (1e-8 : ℝ) := by
    dsimp [C₀]
    field_simp
  have hThresholdBelow : threshold < 2 * C₀ * (1e-8 : ℝ) := by
    calc
      threshold < 2 * (threshold + (1e-8 : ℝ)) := by nlinarith [hThreshold, hEpsPos]
      _ = 2 * (C₀ * (1e-8 : ℝ)) := by rw [← hC₀Eps]
      _ = 2 * C₀ * (1e-8 : ℝ) := by ring
  have hAverageEq (ω : Outcome9 I N) (y : Fin N) :
      average y ω = (N : ℝ) / (Fintype.card (OddSites9 n) : ℝ) *
        oddColumn9 S E G ω y := by
    have hsum : (∑ b : OddSites9 n, (N : ℝ) * (rowLaw9 S E G ω b).w y) =
        (N : ℝ) * oddColumn9 S E G ω y := by
      calc
        (∑ b : OddSites9 n, (N : ℝ) * (rowLaw9 S E G ω b).w y) =
            ∑ b : OddSites9 n, (rowLaw9 S E G ω b).w y * (N : ℝ) := by
              apply Finset.sum_congr rfl
              intro b hb
              ring
        _ = (∑ b : OddSites9 n, (rowLaw9 S E G ω b).w y) * (N : ℝ) := by
              rw [Finset.sum_mul]
        _ = (N : ℝ) * oddColumn9 S E G ω y := by
              simp [oddColumn9]
              ring
    dsimp [average, Z]
    rw [hsum]
    ring
  have htargetToAverage : ∀ ω, target ω ∧ ω ∈ succ → largeAverage ω := by
    intro ω ⟨hTarget, hsucc⟩
    obtain ⟨y, hy⟩ := hTarget
    refine ⟨hsucc, y, ?_⟩
    rw [hAverageEq ω y]
    calc
      threshold < 2 * C₀ * (1e-8 : ℝ) := hThresholdBelow
      _ ≤ (N : ℝ) / (Fintype.card (OddSites9 n) : ℝ) * (1e-8 : ℝ) :=
        mul_le_mul_of_nonneg_right hratio (le_of_lt hEpsPos)
      _ < (N : ℝ) / (Fintype.card (OddSites9 n) : ℝ) * oddColumn9 S E G ω y :=
        mul_lt_mul_of_pos_left hy hratioPos
  calc
    (anchorLaw9 S I E G).pr target = Q.pr (fun ω => target ω ∧ ω ∈ succ) := htargetSupport
    _ ≤ Q.pr largeAverage := Lane_q_s09_assign1.pr_mono Q _ _ htargetToAverage
    _ ≤ (n : ℝ) * 2 ^ n * (1 / 4 : ℝ) ^ n := htailProb

set_option maxHeartbeats 5000000 in
/-- P9.2-assignB, odd injection (09:327–329): at a successful prehistory, Lemma 3.10 (`clock_sampling`, `B = 3`)
applies to the odd rows (probability laws with atoms `≤ e^{S_d}/N ≤ n^{-A}`, column sums `≤ θ₀`), with the
predictive failures of the even stars as predicates (each reads its `n` odd neighbours, each row is read by `n`
predicates, product-law probability equal to the alarm `≤ e^{-c₄ n a_*/8} ≤ n^{-P}`); it gives an injective odd
assignment avoiding every predictive failure with joint comparison `1 + ε n ≤ 2` on at most `n³` rows. -/
theorem p92_odd_clock (P : Params9) (hP : P.Valid) :
    ∃ n₀ : ℕ, ∃ C₀ : ℝ, ∀ n N : ℕ, LargeAt n₀ C₀ n N →
      ∀ {E : Fin N → Fin N → Prop} {X Y : Finset (Fin N)} {κ : ℝ} {G : Colour} {M : TagMix N}
        (S : Setup9 P n N M) (I : IDMap9 P n),
        CoreInput9 P κ E X Y G M S I → RowCap9 S I E G →
        ∀ ω : Outcome9 I N, GoodPre9 S E G ω → ∃ J, ClockOK9 S E G ω J := by
  obtain ⟨Aclock, Pclock, nClock, ε, hε, hclock⟩ :=
    clock_sampling 3 2 (by norm_num : 1 ≤ (3 : ℝ))
  have hExps := Lane_q_s09_assign1.scaleExpsOfValid9 P hP
  obtain ⟨nDeep, hDeep⟩ := Lane_q_s09_assign1.deepWidthSmall9 P hP
  obtain ⟨nLog, hLog⟩ := Lane_q_s09_assign1.natLogSmall9
  let Abar : ℝ := |Aclock| + 1
  let etaA : ℝ := 1 / (100 * Abar)
  obtain ⟨nAlog, hAlog⟩ := Lane_q_s09_assign1.natLogLeConst9 etaA (by dsimp [etaA, Abar]; positivity)
  let Pbar : ℝ := |Pclock| + 1
  let cDegree : ℝ := min 1 (2000 / Pbar)
  have hcDegree : 0 < cDegree := by dsimp [cDegree, Pbar]; positivity
  obtain ⟨nDegree, hDegree⟩ := Lane_q_s09_assign1.degreeLogSmall9 P hExps hcDegree
  obtain ⟨nEps, hEpsSmall⟩ := Filter.eventually_atTop.1
    (hε.eventually (Iio_mem_nhds (by norm_num : (0 : ℝ) < 1)))
  let n₀ := max 2 (max nClock (max nDeep (max nLog (max nAlog (max nDegree nEps)))))
  refine ⟨n₀, 1, ?_⟩
  intro n N hLarge E X Y κ G M S I hCore hRowCap ω hPre
  have hn₀2 : 2 ≤ n₀ := by dsimp [n₀]; omega
  have hn0clock : nClock ≤ n₀ := by dsimp [n₀]; omega
  have hn0deep : nDeep ≤ n₀ := by dsimp [n₀]; omega
  have hn0log : nLog ≤ n₀ := by dsimp [n₀]; omega
  have hn0Alog : nAlog ≤ n₀ := by dsimp [n₀]; omega
  have hn0Degree : nDegree ≤ n₀ := by dsimp [n₀]; omega
  have hn0Eps : nEps ≤ n₀ := by dsimp [n₀]; omega
  have hn₂ : 2 ≤ n := le_trans hn₀2 hLarge.1
  have hnClock : nClock ≤ n := le_trans hn0clock hLarge.1
  have hnDeep : nDeep ≤ n := le_trans hn0deep hLarge.1
  have hnLog : nLog ≤ n := le_trans hn0log hLarge.1
  have hnAlog : nAlog ≤ n := le_trans hn0Alog hLarge.1
  have hnDegree : nDegree ≤ n := le_trans hn0Degree hLarge.1
  have hnEps : nEps ≤ n := le_trans hn0Eps hLarge.1
  have hn : 0 < n := by omega
  have hnR : 0 < (n : ℝ) := by exact_mod_cast hn
  have hnR1 : 1 ≤ (n : ℝ) := by exact_mod_cast (show 1 ≤ n by omega)
  have hnR₂ : 2 ≤ (n : ℝ) := by exact_mod_cast hn₂
  rcases hCore with ⟨hNpos, hPrep, hDeepAt, hTagPos, hMasks, hDeepTools, hScaleExps, hScales⟩
  rcases hScales with ⟨hnScales, hmle, hradius, hShallow, hFilterBudget,
    hDeepMargin, hbStar, hGain⟩
  rcases hPre with ⟨hRaw, hNoBad, hOddColumn⟩
  let rows : OddSites9 n → FinProb (Fin N) := fun b => rowLaw9 S E G ω b
  let lab : OddSites9 n → Fin N → Fin N := fun _ y => y
  let scope : EvenSites9 n → Finset (OddSites9 n) := fun v =>
    Finset.univ.filter (fun b => (cube n).Adj v.1 b.1)
  let failure : EvenSites9 n → (OddSites9 n → Fin N) → Prop := fun v f =>
    predFail9 S E G ω v (nbrLabels9 (v := v) f)
  have hregular : ∀ v : EvenSites9 n, starRegular9 S E G ω v := by
    intro v
    have hnot := hNoBad v
    unfold StarBad9 at hnot
    have hvalid : starValid9 S E G ω v := by
      by_contra hv
      exact hnot (Or.inl hv)
    exact hvalid.1
  have hclockColumn : ∀ y, ∑ b, labMarg (rows b) (lab b) y ≤ (1e-8 : ℝ) := by
    intro y
    have hEq (b : OddSites9 n) : labMarg (rows b) (lab b) y =
        (rowLaw9 S E G ω b).w y := by
      simp [labMarg, rows, lab]
    calc
      ∑ b, labMarg (rows b) (lab b) y = oddColumn9 S E G ω y := by
        simp_rw [hEq]
        rfl
      _ ≤ (1e-8 : ℝ) := hOddColumn y
  have hscopeDist (v : EvenSites9 n) (b : StarOdd9 v) : b.1 ∈ scope v := by
    unfold scope
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, b.2⟩
  have hdepends : ∀ v : EvenSites9 n, FinProb.DependsOn (failure v) (scope v) := by
    intro v f f' hagree
    have hlabels : nbrLabels9 (v := v) f = nbrLabels9 (v := v) f' := by
      funext b
      exact hagree b.1 (hscopeDist v b)
    change predFail9 S E G ω v (nbrLabels9 (v := v) f) =
      predFail9 S E G ω v (nbrLabels9 (v := v) f')
    rw [hlabels]
  have hballNat (v : EvenSites9 n) : (scope v).card ≤ n + 1 := by
    let B := Finset.univ.filter (fun b : CubeVertex n => _root_.hammingDist v.1 b ≤ 1)
    have hsubset : (scope v).image Subtype.val ⊆ B := by
      intro b hb
      rcases Finset.mem_image.mp hb with ⟨b', hb', rfl⟩
      have hadj := (Finset.mem_filter.mp hb').2
      have hdist : _root_.hammingDist v.1 b'.1 = 1 := by
        change _root_.hammingDist v.1 b'.1 = 1 at hadj
        exact hadj
      have hle : _root_.hammingDist v.1 b'.1 ≤ 1 := by rw [hdist]
      exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, hle⟩
    have himage : ((scope v).image Subtype.val).card = (scope v).card :=
      Finset.card_image_of_injective (scope v) Subtype.val_injective
    have hBall : B.card ≤ n + 1 := by
      simpa [B] using Lane_q_s09_assign1.hammingBallCardBound9 (r := 1) v.1
    calc
      (scope v).card = ((scope v).image Subtype.val).card := himage.symm
      _ ≤ B.card := Finset.card_le_card hsubset
      _ ≤ n + 1 := hBall
  have hnCube : (n : ℝ) + 1 ≤ (n : ℝ) ^ 3 := by
    have hnSq : 4 ≤ (n : ℝ) ^ 2 := by nlinarith
    have hmul := mul_le_mul_of_nonneg_left hnSq hnR.le
    nlinarith
  have hscopeSize : ∀ v : EvenSites9 n, ((scope v).card : ℝ) ≤ (n : ℝ) ^ (3 : ℝ) := by
    intro v
    have hcast : ((scope v).card : ℝ) ≤ (n : ℝ) + 1 := by exact_mod_cast hballNat v
    have hbound := hcast.trans hnCube
    simpa using hbound
  have hincNat (b : OddSites9 n) :
      (Finset.univ.filter (fun v : EvenSites9 n => b ∈ scope v)).card ≤ n + 1 := by
    let C := Finset.univ.filter (fun v : EvenSites9 n => b ∈ scope v)
    let B := Finset.univ.filter (fun v : CubeVertex n => _root_.hammingDist b.1 v ≤ 1)
    have hsubset : C.image Subtype.val ⊆ B := by
      intro x hx
      rcases Finset.mem_image.mp hx with ⟨v, hv, rfl⟩
      have hscopeMem := (Finset.mem_filter.mp hv).2
      have hadj := (Finset.mem_filter.mp hscopeMem).2
      have hdist : _root_.hammingDist v.1 b.1 = 1 := by
        change _root_.hammingDist v.1 b.1 = 1 at hadj
        exact hadj
      have hdist' : _root_.hammingDist b.1 v.1 = 1 := by
        rw [_root_.hammingDist_comm]
        exact hdist
      have hle : _root_.hammingDist b.1 v.1 ≤ 1 := by rw [hdist']
      exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, hle⟩
    have himage : (C.image Subtype.val).card = C.card :=
      Finset.card_image_of_injective C Subtype.val_injective
    have hBall : B.card ≤ n + 1 := by
      simpa [B] using Lane_q_s09_assign1.hammingBallCardBound9 (r := 1) b.1
    calc
      C.card = (C.image Subtype.val).card := himage.symm
      _ ≤ B.card := Finset.card_le_card hsubset
      _ ≤ n + 1 := hBall
  have hincidence : ∀ b : OddSites9 n,
      ((Finset.univ.filter (fun v : EvenSites9 n => b ∈ scope v)).card : ℝ) ≤ (n : ℝ) ^ (3 : ℝ) := by
    intro b
    have hcast : ((Finset.univ.filter (fun v : EvenSites9 n => b ∈ scope v)).card : ℝ) ≤
        (n : ℝ) + 1 := by exact_mod_cast hincNat b
    have hbound := hcast.trans hnCube
    simpa using hbound
  have hNUpper : (N : ℝ) ≤ (n : ℝ) * (2 : ℝ) ^ n := by exact_mod_cast hLarge.2.2
  have hlog2 : Real.log (2 : ℝ) ≤ 1 := by
    have h := Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 2)
    linarith
  have hlogn : Real.log (n : ℝ) ≤ (n : ℝ) := Real.log_le_self hnR.le
  have hlogN : Real.log (N : ℝ) ≤ 2 * (n : ℝ) := by
    calc
      Real.log (N : ℝ) ≤ Real.log ((n : ℝ) * (2 : ℝ) ^ n) :=
        Real.log_le_log (by positivity) hNUpper
      _ = Real.log (n : ℝ) + (n : ℝ) * Real.log 2 := by
        rw [Real.log_mul hnR.ne' (pow_ne_zero _ (by norm_num : (2 : ℝ) ≠ 0)), Real.log_pow]
      _ ≤ (n : ℝ) + (n : ℝ) := by
        apply add_le_add hlogn
        calc
          (n : ℝ) * Real.log 2 ≤ (n : ℝ) * 1 := mul_le_mul_of_nonneg_left hlog2 hnR.le
          _ = (n : ℝ) := by ring
      _ = 2 * (n : ℝ) := by ring
  have hRowCapAt : ∀ b y, (N : ℝ) * (rows b).w y ≤ Real.exp (P.Sd (n : ℝ)) := by
    intro b y
    exact hRowCap ω hRaw hregular b y
  have hLogNNonneg : 0 ≤ Real.log (n : ℝ) := Real.log_nonneg (by exact_mod_cast hnR1)
  have hAcoeff : |Aclock| * etaA ≤ 1 / 100 := by
    dsimp [etaA, Abar]
    have hAbs : 0 ≤ |Aclock| := abs_nonneg _
    have hDen : 0 < 100 * (|Aclock| + 1) := by positivity
    field_simp
    nlinarith
  have hAlogBound : Aclock * Real.log (n : ℝ) ≤ (n : ℝ) / 100 := by
    have hsmallLog := hAlog n hnAlog
    calc
      Aclock * Real.log (n : ℝ) ≤ |Aclock| * Real.log (n : ℝ) :=
        mul_le_mul_of_nonneg_right (le_abs_self Aclock) hLogNNonneg
      _ ≤ |Aclock| * (etaA * (n : ℝ)) :=
        mul_le_mul_of_nonneg_left hsmallLog (abs_nonneg _)
      _ = (|Aclock| * etaA) * (n : ℝ) := by ring
      _ ≤ (1 / 100) * (n : ℝ) :=
        mul_le_mul_of_nonneg_right hAcoeff hnR.le
      _ = (n : ℝ) / 100 := by ring
  have hPowTwoExp : (2 : ℝ) ^ n = Real.exp ((n : ℝ) * Real.log 2) := by
    calc
      (2 : ℝ) ^ n = Real.exp (Real.log 2) ^ n := by
        rw [Real.exp_log (by norm_num : (0 : ℝ) < 2)]
      _ = Real.exp ((n : ℝ) * Real.log 2) :=
        (Real.exp_nat_mul (Real.log 2) n).symm
  have hNLower : (2 : ℝ) ^ n ≤ (N : ℝ) := by simpa using hLarge.2.1
  have hNposR : 0 < (N : ℝ) := by exact_mod_cast hNpos
  have hRowCapRatio (b : OddSites9 n) (y : Fin N) :
      (rows b).w y ≤ Real.exp (P.Sd (n : ℝ)) / (N : ℝ) := by
    have hnum : (rows b).w y * (N : ℝ) ≤ Real.exp (P.Sd (n : ℝ)) := by
      simpa [rows, mul_comm] using hRowCapAt b y
    calc
      (rows b).w y = (rows b).w y * (N : ℝ) / (N : ℝ) := by
        field_simp [ne_of_gt hNposR]
      _ ≤ Real.exp (P.Sd (n : ℝ)) / (N : ℝ) :=
        div_le_div_of_nonneg_right hnum hNposR.le
  have hInvN : (N : ℝ)⁻¹ ≤ ((2 : ℝ) ^ n)⁻¹ := by
    simpa [one_div] using one_div_le_one_div_of_le (by positivity) hNLower
  have hRatioDen : Real.exp (P.Sd (n : ℝ)) / (N : ℝ) ≤
      Real.exp (P.Sd (n : ℝ)) / (2 : ℝ) ^ n := by
    rw [div_eq_mul_inv, div_eq_mul_inv]
    exact mul_le_mul_of_nonneg_left hInvN (by positivity)
  have hlogTwoLower : (2 : ℝ)⁻¹ ≤ Real.log 2 := by
    have h := Real.log_two_gt_d9
    norm_num [one_div] at h ⊢ <;> linarith
  have hAtomExp : P.Sd (n : ℝ) - (n : ℝ) * Real.log 2 ≤
      -(Aclock * Real.log (n : ℝ)) := by
    have hDen : (n : ℝ) / 2 ≤ (n : ℝ) * Real.log 2 :=
      mul_le_mul_of_nonneg_left hlogTwoLower hnR.le
    linarith [hDeep n hnDeep, hAlogBound, hDen]
  have hPowerExp : Real.exp (-(Aclock * Real.log (n : ℝ))) =
      (n : ℝ) ^ (-Aclock) := by
    rw [Real.rpow_def_of_pos hnR]
    ring
  have hAtom : ∀ b y, labMarg (rows b) (lab b) y ≤ (n : ℝ) ^ (-Aclock) := by
    intro b y
    have hMarg : labMarg (rows b) (lab b) y = (rows b).w y := by
      simp [labMarg, rows, lab]
    calc
      labMarg (rows b) (lab b) y = (rows b).w y := hMarg
      _ ≤ Real.exp (P.Sd (n : ℝ)) / (N : ℝ) := hRowCapRatio b y
      _ ≤ Real.exp (P.Sd (n : ℝ)) / (2 : ℝ) ^ n := hRatioDen
      _ = Real.exp (P.Sd (n : ℝ) - (n : ℝ) * Real.log 2) := by
        rw [hPowTwoExp, Real.exp_sub]
      _ ≤ Real.exp (-(Aclock * Real.log (n : ℝ))) := Real.exp_le_exp.mpr hAtomExp
      _ = (n : ℝ) ^ (-Aclock) := hPowerExp
  have hfailDepends : ∀ v, FinProb.DependsOn (failure v) (scope v) := hdepends
  have hSuccessfulAlarm (v : EvenSites9 n) :
      alarm9 S E G ω v ≤ Real.exp (-(gainConst9 * (n : ℝ) * P.aStar n / 8)) := by
    have hnot := hNoBad v
    unfold StarBad9 at hnot
    have hnotAlarm : ¬ Real.exp (-(gainConst9 * (n : ℝ) * P.aStar n / 8)) <
        alarm9 S E G ω v := by
      intro h
      exact hnot (Or.inr h)
    exact le_of_not_gt hnotAlarm
  have hFailureProb : ∀ v, (FinProb.pi rows).pr (failure v) ≤ (n : ℝ) ^ (-Pclock) := by
    intro v
    have hPbarPos : 0 < Pbar := by dsimp [Pbar]; positivity
    have hcDegBound : Pbar * cDegree ≤ 2000 := by
      have hmin : cDegree ≤ 2000 / Pbar := min_le_right _ _
      calc
        Pbar * cDegree ≤ Pbar * (2000 / Pbar) :=
          mul_le_mul_of_nonneg_left hmin hPbarPos.le
        _ = 2000 := by field_simp [ne_of_gt hPbarPos]
    have hLogNonneg : 0 ≤ Real.log (n : ℝ) := by
      apply Real.log_nonneg
      exact hnR1
    have hLogPlusNonneg : 0 ≤ Real.log ((n : ℝ) + 1) := by
      apply Real.log_nonneg
      linarith
    have hPowNonneg : 0 ≤ (n : ℝ) ^ P.u := by positivity
    have hDegreeAt := hDegree n hnDegree
    have hRadiusLower : 10 ≤ 2 * (P.radius n : ℝ) + 8 := by
      have hr : (1 : ℝ) ≤ P.radius n := by exact_mod_cast hradius
      nlinarith
    have hTenLog : 10 * Real.log ((n : ℝ) + 1) ≤
        (2 * (P.radius n : ℝ) + 8) * Real.log ((n : ℝ) + 1) :=
      mul_le_mul_of_nonneg_right hRadiusLower hLogPlusNonneg
    have hLogNear : Real.log (n : ℝ) ≤ Real.log ((n : ℝ) + 1) :=
      Real.log_le_log hnR (by linarith)
    have hLogDegree : Real.log ((n : ℝ) + 1) ≤ (cDegree / 40) * (n : ℝ) ^ P.u := by
      calc
        Real.log ((n : ℝ) + 1) =
            10 * Real.log ((n : ℝ) + 1) / 10 := by field_simp
        _ ≤ ((2 * (P.radius n : ℝ) + 8) * Real.log ((n : ℝ) + 1)) / 10 :=
          div_le_div_of_nonneg_right hTenLog (by norm_num)
        _ ≤ (cDegree / 4 * (n : ℝ) ^ P.u) / 10 :=
          div_le_div_of_nonneg_right hDegreeAt (by norm_num)
        _ = (cDegree / 40) * (n : ℝ) ^ P.u := by ring
    have hPLog : Pclock * Real.log (n : ℝ) ≤ 50 * (n : ℝ) ^ P.u := by
      have hPclockLe : Pclock ≤ Pbar := by
        dsimp [Pbar]
        exact le_trans (le_abs_self Pclock) (le_add_of_nonneg_right (by norm_num))
      calc
        Pclock * Real.log (n : ℝ) ≤ Pbar * Real.log (n : ℝ) :=
          mul_le_mul_of_nonneg_right hPclockLe hLogNonneg
        _ ≤ Pbar * Real.log ((n : ℝ) + 1) :=
          mul_le_mul_of_nonneg_left hLogNear hPbarPos.le
        _ ≤ Pbar * ((cDegree / 40) * (n : ℝ) ^ P.u) :=
          mul_le_mul_of_nonneg_left hLogDegree hPbarPos.le
        _ ≤ 50 * (n : ℝ) ^ P.u := by
          have hcoef : Pbar * (cDegree / 40) ≤ 50 := by nlinarith [hcDegBound]
          nlinarith [mul_le_mul_of_nonneg_right hcoef hPowNonneg]
    have hBaseGain : 4 * (n : ℝ) ^ P.u ≤
        gainConst9 * (n : ℝ) * P.aStar n / 100 := by
      have hnonneg : 0 ≤
          ((P.radius n : ℝ) + 8) * Real.log ((n : ℝ) + 1) +
            (n : ℝ) ^ (P.xS : ℝ) := by positivity
      linarith [hGain, hnonneg]
    have hGainLarge : 50 * (n : ℝ) ^ P.u ≤
        gainConst9 * (n : ℝ) * P.aStar n / 8 := by
      nlinarith [hBaseGain]
    have hExpTail : Real.exp (-(gainConst9 * (n : ℝ) * P.aStar n / 8)) ≤
        (n : ℝ) ^ (-Pclock) := by
      calc
        Real.exp (-(gainConst9 * (n : ℝ) * P.aStar n / 8)) ≤
            Real.exp (-50 * (n : ℝ) ^ P.u) :=
          Real.exp_le_exp.mpr (by nlinarith [hGainLarge])
        _ ≤ Real.exp (-(Pclock * Real.log (n : ℝ))) :=
          Real.exp_le_exp.mpr (by nlinarith [hPLog])
        _ = (n : ℝ) ^ (-Pclock) := by rw [Real.rpow_def_of_pos hnR]; congr 1 <;> ring
    have hAlarmEq : (FinProb.pi rows).pr (failure v) = alarm9 S E G ω v := by
      let Scope := {b : OddSites9 n // b ∈ scope v}
      let e : StarOdd9 v ≃ Scope := {
        toFun := fun b => ⟨b.1, hscopeDist v b⟩
        invFun := fun b => ⟨b.1, (Finset.mem_filter.mp b.2).2⟩
        left_inv := by intro b; apply Subtype.ext; rfl
        right_inv := by intro b; apply Subtype.ext; rfl }
      let eFun : (∀ i : Scope, Fin N) ≃ (StarOdd9 v → Fin N) := {
        toFun := fun a b => a (e b)
        invFun := fun ys i => ys (e.symm i)
        left_inv := by intro a; funext i; simp [e]
        right_inv := by intro ys; funext b; simp [e] }
      let base : OddSites9 n → Fin N := fun _ => ⟨0, by omega⟩
      have hMarginal := Lane_q_s09_assign1.piPrDependsEq9 rows (scope v)
        (failure v) base (hdepends v)
      have hLift (a : ∀ i : Scope, Fin N) (b : StarOdd9 v) :
          S07.glue (scope v) base a b.1 = (eFun a) b := by
        have hb : b.1 ∈ scope v := hscopeDist v b
        simp [S07.glue, eFun, e, hb]
      have hEvent (ys : StarOdd9 v → Fin N) :
          failure v (S07.glue (scope v) base (eFun.symm ys)) =
            predFail9 S E G ω v ys := by
        change predFail9 S E G ω v
            (nbrLabels9 (v := v) (S07.glue (scope v) base (eFun.symm ys))) = _
        congr 1
        funext b
        change (S07.glue (scope v) base (eFun.symm ys)) b.1 = ys b
        exact hLift (eFun.symm ys) b
      have hLocal :
          (FinProb.pi (fun i : Scope => rows i.1)).pr
              (fun a => failure v (S07.glue (scope v) base a)) =
            (FinProb.pi (fun b : StarOdd9 v => rows b.1)).pr
              (fun ys => predFail9 S E G ω v ys) := by
        classical
        unfold FinProb.pr FinProb.pi
        apply Fintype.sum_equiv eFun
        intro a
        have hEv : failure v (S07.glue (scope v) base a) =
            predFail9 S E G ω v (eFun a) := by
          simpa [eFun] using hEvent (eFun a)
        have hWeight :
            (∏ i : Scope, (rows i.1).w (a i)) =
              ∏ b : StarOdd9 v, (rows b.1).w ((eFun a) b) := by
          exact Fintype.prod_equiv e.symm
            (fun i => (rows i.1).w (a i))
            (fun b => (rows b.1).w ((eFun a) b))
            (by intro i; simp [eFun, e])
        simp [hEv, hWeight]
      have hStarValid : starValid9 S E G ω v := by
        have hnot := hNoBad v
        unfold StarBad9 at hnot
        by_contra hbad
        exact hnot (Or.inl hbad)
      have hUpdate : updAnc9 ω (I.center v.1) (anc9 ω (I.center v.1)) = ω := by
        funext i
        by_cases hi : i = Sum.inl (I.center v.1)
        · subst i
          simp [updAnc9, anc9]
        · simp [updAnc9, anc9, hi]
      have hLik (ys : StarOdd9 v → Fin N) :
          starLik9 S E G ω v (anc9 ω (I.center v.1)) ys =
            ∏ b : StarOdd9 v, (rows b.1).w (ys b) := by
        simp [starLik9, hUpdate, hStarValid, rows]
      have hAlarm : alarm9 S E G ω v =
          (FinProb.pi (fun b : StarOdd9 v => rows b.1)).pr
            (fun ys => predFail9 S E G ω v ys) := by
        simp [alarm9, FinProb.pr, FinProb.pi, hLik]
      calc
        (FinProb.pi rows).pr (failure v) =
            (FinProb.pi (fun i : Scope => rows i.1)).pr
              (fun a => failure v (S07.glue (scope v) base a)) := hMarginal
        _ = (FinProb.pi (fun b : StarOdd9 v => rows b.1)).pr
              (fun ys => predFail9 S E G ω v ys) := hLocal
        _ = alarm9 S E G ω v := hAlarm.symm
    calc
      (FinProb.pi rows).pr (failure v) = alarm9 S E G ω v := hAlarmEq
      _ ≤ Real.exp (-(gainConst9 * (n : ℝ) * P.aStar n / 8)) := hSuccessfulAlarm v
      _ ≤ (n : ℝ) ^ (-Pclock) := hExpTail
  have hEpsBound : 1 + ε n ≤ 2 := by linarith [hEpsSmall n hnEps]
  obtain ⟨J, hJSupport, hJJoint⟩ := hclock n hnClock N hlogN lab rows failure scope
    hclockColumn hAtom hfailDepends hscopeSize hincidence hFailureProb
  refine ⟨J, ?_⟩
  constructor
  · intro f hf
    rcases hJSupport f hf with ⟨hinj, hNoFailure⟩
    refine ⟨?_, ?_⟩
    · simpa [lab] using hinj
    · intro v
      simpa [failure] using hNoFailure v
  · intro T o hT
    have hTReal : (T.card : ℝ) ≤ (n : ℝ) ^ (3 : ℝ) := by simpa using hT
    have hjointBound := hJJoint T o hTReal
    calc
      J.pr (fun f => ∀ b ∈ T, f b = o b) ≤
          (1 + ε n) * ∏ b ∈ T, (rows b).w (o b) := by
            simpa [lab, rows] using hjointBound
      _ ≤ 2 * ∏ b ∈ T, (rowLaw9 S E G ω b).w (o b) :=
        mul_le_mul_of_nonneg_right hEpsBound (Finset.prod_nonneg fun b hb =>
          (rowLaw9 S E G ω b).nonneg (o b))

/-! ## P9.2-assignC (09:331–350) -/

/-- The likelihood bound (09:303–304): on `𝒱` (recomputed with `W_* = x`) every filter is a genuine restriction,
`p_b = del_b|_{N_G(x)}` with `del_b(N_G(x)) = q_b`, so `∏ p_b(y_b) ≤ P⁻(y) / ∏ q_b ≤ 2^n e^{-c₄ n a_*} P⁻(y)` by
(9.1); off `𝒱` the left side is zero. -/
theorem p92_star_lik_bound (P : Params9) (hP : P.Valid) :
    ∃ n₀ : ℕ, ∀ n ≥ n₀, ∀ {N : ℕ} {E : Fin N → Fin N → Prop} {X Y : Finset (Fin N)} {κ : ℝ}
      {G : Colour} {M : TagMix N} (S : Setup9 P n N M) (I : IDMap9 P n),
      CoreInput9 P κ E X Y G M S I → StarLikBound9 S I E G := by
  exact Lane_q_s09_assign2.p92_star_lik_bound_core P hP

/-- P9.2-assignC, posterior rows (09:331–335): on predictive success `M_v > 0`, so the posterior row is a
probability law; a nonzero entry at `x` forces `𝒱` with `W_* = x`, hence every neighbour label hits `x`
(the target ID is seen at every odd neighbour); and `N μ_{i_z}(x) ≤ e^{n^{x_s} + O(log n)} ≤ e^{c₄ n a_*/4}` with
the likelihood bound and `M_v ≥ e^{-c₄ n a_*/4} P⁻` give the cap `2^n e^{-c₄ n a_*/2}`. -/
theorem p92_even_rows (P : Params9) (hP : P.Valid) :
    ∃ n₀ : ℕ, ∀ n ≥ n₀, ∀ {N : ℕ} {E : Fin N → Fin N → Prop} {X Y : Finset (Fin N)} {κ : ℝ}
      {G : Colour} {M : TagMix N} (S : Setup9 P n N M) (I : IDMap9 P n),
      CoreInput9 P κ E X Y G M S I → StarLikBound9 S I E G →
        EvenRowLaw9 S I E G ∧ EvenRowCap9 S I E G := by
  obtain ⟨n₀, hcap⟩ := Lane_q_s09_assign2.p92_even_row_cap_core P hP
  refine ⟨n₀, ?_⟩
  intro n hn N E X Y κ G M S I hCore hSLB
  have hcap' : EvenRowCap9 S I E G := hcap n hn S I hCore hSLB
  rcases hCore with ⟨_, _, _, _, _, _, _, hscales⟩
  rcases hscales with ⟨_, _, _, _, _, _, hbStar, _⟩
  exact ⟨Lane_q_s09_assign2.evenRowLaw9_core S E G hbStar, hcap'⟩

/-- P9.2-assignC, cancellation (09:342–346): integrating the target anchor turns the gated neighbour product into
`M_v`, which cancels the posterior denominator: `∑_y M_v(y) F_x(y) μ(x)/M_v(y) ≤ μ(x) ∑_y F_x(y) ≤ μ(x)`
(third assertion of `gated_posterior`); predictive success only decreases the integral. -/
theorem p92_star_cancel {P : Params9} {n N : ℕ} {M : TagMix N} (S : Setup9 P n N M)
    (I : IDMap9 P n) (E : Fin N → Fin N → Prop) (G : Colour) : StarCancel9 S I E G := by
  exact Lane_q_s09_assign2.starCancel9_core S E G

/-- P9.2-assignC, clock comparison (09:337–341): separated even sites have disjoint odd neighbourhoods (at most
`n²` labels in all), the clock law is supported on predictive success, and its joint comparison replaces the
injection by independent draws from the odd rows; on a successful prehistory every star gate is open, so the
integral is at most twice the product of the star integrals. -/
theorem p92_clock_factor {P : Params9} {n N : ℕ} {M : TagMix N} (S : Setup9 P n N M)
    (I : IDMap9 P n) (E : Fin N → Fin N → Prop) (G : Colour)
    (J : Outcome9 I N → FinProb (OddSites9 n → Fin N))
    (hJ : ∀ ω, GoodPre9 S E G ω → ClockOK9 S E G ω (J ω)) : ClockFactor9 S I E G J := by
  exact Lane_q_s09_assign2.p92_clock_factor_core S E G J hJ

/-- P9.2-assignC, anchor integral (09:341–347): remove the star events touching the separated target IDs (at
most `(n+1)^{2r+8}` each, factor `2` per site for large `n`); the remaining events do not read the targets, each
star integral reads only its own target among them (separation and the fixed-map locality), so the targets
integrate independently and `StarCancel9` bounds each factor by `N μ_{i_{z(v)}}(x)`. -/
theorem p92_even_anchor_integral (P : Params9) (hP : P.Valid) (c : ℝ) (hc : 0 < c) :
    ∃ n₀ : ℕ, ∀ n ≥ n₀, ∀ {N : ℕ} {E : Fin N → Fin N → Prop} {M : TagMix N} {G : Colour}
      (S : Setup9 P n N M) (I : IDMap9 P n),
      S07.CondProductBound → AnchorLLL9 S I E G c → StarScopeFacts9 S I E G →
        StarCancel9 S I E G → EvenAnchorIntegral9 S I E G := by
  exact Lane_q_s09_assign2.p92_even_anchor_integral_core P hP c hc

/-- P9.2-assignC, assembled moment (09:347–349): the clock comparison at every successful prehistory and the
anchor integral give `4^k ∏ N μ_{i_{z(v)}}(x)`. -/
theorem p92_even_moment {P : Params9} {n N : ℕ} {M : TagMix N} (S : Setup9 P n N M)
    (I : IDMap9 P n) (E : Fin N → Fin N → Prop) (G : Colour)
    (J : Outcome9 I N → FinProb (OddSites9 n → Fin N))
    (hfac : ClockFactor9 S I E G J) (hint : EvenAnchorIntegral9 S I E G) : EvenMoment9 S I E G J := by
  exact Lane_q_s09_assign2.p92_even_moment_helper S I E G J hfac hint

/-- P9.2-assignC, even column sums (09:347–350): Lemma 3.6 with near = `siteNear9` (fraction
`(n+1)^{4r+12} 2^{1-n}`), cap `2^n e^{-c₄ n a_*/2}` on predictive success (`EvenRowCap9`; repeat cost
`e^{O(r log n) - c₄ n a_*/2} = o(1)`), comparison means `N μ_{i_{z(v)}}(x)` of average at most `tagLoadConst9 κ`
(`TagsOK9`), and a union over labels; even column sums are `2^{n-1}/N` times the normalized average, at most one
once `N ≥ C₀ 2^n`. -/
theorem p92_even_loads (P : Params9) (hP : P.Valid) (κ : ℝ) (hκ : 0 < κ) :
    ∃ n₀ : ℕ, ∃ C₀ : ℝ, ∀ n N : ℕ, LargeAt n₀ C₀ n N →
      ∀ {E : Fin N → Fin N → Prop} {X Y : Finset (Fin N)} {G : Colour} {M : TagMix N}
        (S : Setup9 P n N M) (I : IDMap9 P n) (cT : ℝ)
        (J : Outcome9 I N → FinProb (OddSites9 n → Fin N)),
        CoreInput9 P κ E X Y G M S I → TagsOK9 κ E G cT S.tag → EvenRowCap9 S I E G →
        (∀ ω, GoodPre9 S E G ω → ClockOK9 S E G ω (J ω)) → EvenMoment9 S I E G J →
        ∑ ω, (anchorLaw9 S I E G).w ω *
            (if GoodPre9 S E G ω then (J ω).pr (fun f => ∃ x, 1 < evenColumn9 S E G ω f x) else 0) ≤
          (n : ℝ) * 2 ^ n * (1 / 4 : ℝ) ^ n := by
  exact Lane_q_s09_assign2.p92_even_loads_core P hP κ hκ

/-- P9.2-assignB/C averaged (09:327–350): if the avoidance event has positive raw mass, the odd column sums
exceed `θ₀` with anchor-law probability at most `δ = n 2^n 4^{-n}`, successful prehistories admit clock-sampler
laws, and every clock-sampler family has even column sums above one with probability at most `δ`, then (as
`2δ < 1`) some outcome and odd assignment avoid every star event, are injective, avoid every predictive failure
and have even column sums at most one. -/
theorem p92_realization :
    ∃ n₀ : ℕ, ∀ n ≥ n₀, ∀ {P : Params9} {N : ℕ} {M : TagMix N} {E : Fin N → Fin N → Prop}
      {G : Colour} (S : Setup9 P n N M) (I : IDMap9 P n), 0 < N →
      0 < (rawLaw9 S I).pr (fun ω => ∀ v, ¬ StarBad9 S E G ω v) →
      (anchorLaw9 S I E G).pr (fun ω => ∃ y, (1e-8 : ℝ) < oddColumn9 S E G ω y) ≤
        (n : ℝ) * 2 ^ n * (1 / 4 : ℝ) ^ n →
      (∀ ω : Outcome9 I N, GoodPre9 S E G ω → ∃ J, ClockOK9 S E G ω J) →
      (∀ J : Outcome9 I N → FinProb (OddSites9 n → Fin N),
        (∀ ω, GoodPre9 S E G ω → ClockOK9 S E G ω (J ω)) →
        ∑ ω, (anchorLaw9 S I E G).w ω *
            (if GoodPre9 S E G ω then (J ω).pr (fun f => ∃ x, 1 < evenColumn9 S E G ω f x) else 0) ≤
          (n : ℝ) * 2 ^ n * (1 / 4 : ℝ) ^ n) →
      ∃ (ω : Outcome9 I N) (f : OddSites9 n → Fin N), (∀ v, ¬ StarBad9 S E G ω v) ∧
        Function.Injective f ∧ (∀ v, ¬ predFail9 S E G ω v (nbrLabels9 f)) ∧
        ∀ x, evenColumn9 S E G ω f x ≤ 1 := by
  refine ⟨3, ?_⟩
  intro n hn P N M E G S I hN havoid hodd hsampler heven
  have hδ := Lane_q_s09_assign2.p92_delta_lt_half hn
  have hδ' : 2 * ((n : ℝ) * 2 ^ n * (1 / 4 : ℝ) ^ n) < 1 := by
    linarith
  exact Lane_q_s09_assign2.p92_realization_core S hN havoid hodd hsampler heven hδ'

/-- F-HallEmbed (09:349–350): the posterior even rows of a good realization are probability laws on the common
neighbourhoods of the injective odd labels with column sums at most one. -/
theorem p92_hall9 {P : Params9} {n N : ℕ} {M : TagMix N} (S : Setup9 P n N M) (I : IDMap9 P n)
    (E : Fin N → Fin N → Prop) (G : Colour) (hlaw : EvenRowLaw9 S I E G) (ω : Outcome9 I N)
    (f : OddSites9 n → Fin N) (hinj : Function.Injective f)
    (hpf : ∀ v, ¬ predFail9 S E G ω v (nbrLabels9 f)) (hcol : ∀ x, evenColumn9 S E G ω f x ≤ 1) :
    CubeAt n N E :=
  cubeAt_of_rows E G f hinj (fun v x => evenRow9 S E G ω f v x)
    (fun v x => (hlaw ω f v (hpf v)).1 x) (fun v => (hlaw ω f v (hpf v)).2.1)
    (fun v x hx b hb => (hlaw ω f v (hpf v)).2.2 x hx b hb) hcol

/-- The assignment stage assembled (09:296–350): with the tags, the masks and the gain bound, the one-shot
experiment produces a monochromatic cube. -/
theorem p92_assign_stage (P : Params9) (hP : P.Valid) (κ : ℝ) (hκ : 0 < κ) (c₀ : ℝ) (hc₀ : 0 < c₀) :
    ∃ n₀ : ℕ, ∃ C₀ : ℝ, ∀ n N : ℕ, LargeAt n₀ C₀ n N →
      ∀ {E : Fin N → Fin N → Prop} {X Y : Finset (Fin N)} {G : Colour} {M : TagMix N}
        (S : Setup9 P n N M) (I : IDMap9 P n) (cT : ℝ),
        CoreInput9 P κ E X Y G M S I → TagsOK9 κ E G cT S.tag → GainCert9 S I E G c₀ →
          CubeAt n N E := by
  obtain ⟨c₁, hc₁, n₁, hsb⟩ := p92_star_bad_prob P hP c₀ hc₀
  obtain ⟨n₂, hlll⟩ := p92_anchor_lll P hP c₁ hc₁
  obtain ⟨n₃, hrc⟩ := p92_row_cap P hP
  obtain ⟨n₄, hom⟩ := p92_odd_moment P hP (c₁ / 2) (by positivity)
  obtain ⟨n₅, C₅, hol⟩ := p92_odd_loads P hP κ hκ
  obtain ⟨n₆, C₆, hck⟩ := p92_odd_clock P hP
  obtain ⟨n₇, hslb⟩ := p92_star_lik_bound P hP
  obtain ⟨n₈, her⟩ := p92_even_rows P hP
  obtain ⟨n₉, heai⟩ := p92_even_anchor_integral P hP (c₁ / 2) (by positivity)
  obtain ⟨n₁₀, C₁₀, hel⟩ := p92_even_loads P hP κ hκ
  obtain ⟨n₁₁, hreal⟩ := p92_realization
  refine ⟨max (max (max n₁ n₂) (max n₃ n₄)) (max (max n₅ n₆) (max (max n₇ n₈) (max n₉ (max n₁₀ n₁₁)))),
    max (max C₅ C₆) C₁₀, ?_⟩
  intro n N hL E X Y G M S I cT hin htags hgain
  have hn := hL.1
  have h1 : n₁ ≤ n := by omega
  have h2 : n₂ ≤ n := by omega
  have h3 : n₃ ≤ n := by omega
  have h4 : n₄ ≤ n := by omega
  have h7 : n₇ ≤ n := by omega
  have h8 : n₈ ≤ n := by omega
  have h9 : n₉ ≤ n := by omega
  have h11 : n₁₁ ≤ n := by omega
  have hL5 : LargeAt n₅ C₅ n N :=
    largeAt_mono9 hL (by omega) (le_trans (le_max_left _ _) (le_max_left _ _))
  have hL6 : LargeAt n₆ C₆ n N :=
    largeAt_mono9 hL (by omega) (le_trans (le_max_right _ _) (le_max_left _ _))
  have hL10 : LargeAt n₁₀ C₁₀ n N := largeAt_mono9 hL (by omega) (le_max_right _ _)
  have hAM := p92_alarm_mean S I E G
  have hSB := hsb n h1 S I hin hgain hAM
  have hSF := p92_star_scope S I E G
  have hLLL := hlll n h2 S I G hSB hSF
  have hpos := (S07.cond_product_bound _ _ _ _ _ hLLL).1
  have hRC := hrc n h3 S I hin
  have hOM := hom n h4 S I S07.cond_product_bound hLLL hSF
  have hOL := hol n N hL5 S I cT hin htags hRC hOM hpos
  have hCK := hck n N hL6 S I hin hRC
  have hSLB := hslb n h7 S I hin
  obtain ⟨hERL, hERC⟩ := her n h8 S I hin hSLB
  have hEAI := heai n h9 S I S07.cond_product_bound hLLL hSF (p92_star_cancel S I E G)
  have hEL : ∀ J : Outcome9 I N → FinProb (OddSites9 n → Fin N),
      (∀ ω, GoodPre9 S E G ω → ClockOK9 S E G ω (J ω)) →
      ∑ ω, (anchorLaw9 S I E G).w ω *
          (if GoodPre9 S E G ω then (J ω).pr (fun f => ∃ x, 1 < evenColumn9 S E G ω f x) else 0) ≤
        (n : ℝ) * 2 ^ n * (1 / 4 : ℝ) ^ n := fun J hJ =>
    hel n N hL10 S I cT J hin htags hERC hJ
      (p92_even_moment S I E G J (p92_clock_factor S I E G J hJ) hEAI)
  obtain ⟨ω, f, _hgood, hinj, hpf, hcol⟩ := hreal n h11 S I hin.1 hpos hOL hCK hEL
  exact p92_hall9 S I E G hERL ω f hinj hpf hcol

end HypercubeRamsey
