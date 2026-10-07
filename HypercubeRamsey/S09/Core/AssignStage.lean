import HypercubeRamsey.S09.Core.GainStage
import HypercubeRamsey.S07.TagStage
import HypercubeRamsey.S03.GatedPosterior
import HypercubeRamsey.S03.ClockSampling
import HypercubeRamsey.Tools.ScatteredUnion
import HypercubeRamsey.S09.Core.AssignStage_q_s09_assign1

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

set_option maxHeartbeats 1000000 in
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
    sorry

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
  sorry

/-- P9.2-assignB, odd moments (09:324–327): separated odd rows (`¬ siteNear9`) have disjoint inputs (anchors of
the IDs they see and their own masks); removing the star events touching these inputs (at most
`(n+1)^{2r+8}` per row, factor `2` per row for large `n`, `S07.CondProductBound`) leaves independent raw inputs,
whose product integral is `∏ N R_b(y)`. -/
theorem p92_odd_moment (P : Params9) (hP : P.Valid) (c : ℝ) (hc : 0 < c) :
    ∃ n₀ : ℕ, ∀ n ≥ n₀, ∀ {N : ℕ} {E : Fin N → Fin N → Prop} {M : TagMix N} {G : Colour}
      (S : Setup9 P n N M) (I : IDMap9 P n),
      S07.CondProductBound → AnchorLLL9 S I E G c → StarScopeFacts9 S I E G →
        OddMoment9 S I E G := by
  sorry

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
  sorry

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
  sorry

/-! ## P9.2-assignC (09:331–350) -/

/-- The likelihood bound (09:303–304): on `𝒱` (recomputed with `W_* = x`) every filter is a genuine restriction,
`p_b = del_b|_{N_G(x)}` with `del_b(N_G(x)) = q_b`, so `∏ p_b(y_b) ≤ P⁻(y) / ∏ q_b ≤ 2^n e^{-c₄ n a_*} P⁻(y)` by
(9.1); off `𝒱` the left side is zero. -/
theorem p92_star_lik_bound (P : Params9) (hP : P.Valid) :
    ∃ n₀ : ℕ, ∀ n ≥ n₀, ∀ {N : ℕ} {E : Fin N → Fin N → Prop} {X Y : Finset (Fin N)} {κ : ℝ}
      {G : Colour} {M : TagMix N} (S : Setup9 P n N M) (I : IDMap9 P n),
      CoreInput9 P κ E X Y G M S I → StarLikBound9 S I E G := by
  sorry

/-- P9.2-assignC, posterior rows (09:331–335): on predictive success `M_v > 0`, so the posterior row is a
probability law; a nonzero entry at `x` forces `𝒱` with `W_* = x`, hence every neighbour label hits `x`
(the target ID is seen at every odd neighbour); and `N μ_{i_z}(x) ≤ e^{n^{x_s} + O(log n)} ≤ e^{c₄ n a_*/4}` with
the likelihood bound and `M_v ≥ e^{-c₄ n a_*/4} P⁻` give the cap `2^n e^{-c₄ n a_*/2}`. -/
theorem p92_even_rows (P : Params9) (hP : P.Valid) :
    ∃ n₀ : ℕ, ∀ n ≥ n₀, ∀ {N : ℕ} {E : Fin N → Fin N → Prop} {X Y : Finset (Fin N)} {κ : ℝ}
      {G : Colour} {M : TagMix N} (S : Setup9 P n N M) (I : IDMap9 P n),
      CoreInput9 P κ E X Y G M S I → StarLikBound9 S I E G →
        EvenRowLaw9 S I E G ∧ EvenRowCap9 S I E G := by
  sorry

/-- P9.2-assignC, cancellation (09:342–346): integrating the target anchor turns the gated neighbour product into
`M_v`, which cancels the posterior denominator: `∑_y M_v(y) F_x(y) μ(x)/M_v(y) ≤ μ(x) ∑_y F_x(y) ≤ μ(x)`
(third assertion of `gated_posterior`); predictive success only decreases the integral. -/
theorem p92_star_cancel {P : Params9} {n N : ℕ} {M : TagMix N} (S : Setup9 P n N M)
    (I : IDMap9 P n) (E : Fin N → Fin N → Prop) (G : Colour) : StarCancel9 S I E G := by
  sorry

/-- P9.2-assignC, clock comparison (09:337–341): separated even sites have disjoint odd neighbourhoods (at most
`n²` labels in all), the clock law is supported on predictive success, and its joint comparison replaces the
injection by independent draws from the odd rows; on a successful prehistory every star gate is open, so the
integral is at most twice the product of the star integrals. -/
theorem p92_clock_factor {P : Params9} {n N : ℕ} {M : TagMix N} (S : Setup9 P n N M)
    (I : IDMap9 P n) (E : Fin N → Fin N → Prop) (G : Colour)
    (J : Outcome9 I N → FinProb (OddSites9 n → Fin N))
    (hJ : ∀ ω, GoodPre9 S E G ω → ClockOK9 S E G ω (J ω)) : ClockFactor9 S I E G J := by
  sorry

/-- P9.2-assignC, anchor integral (09:341–347): remove the star events touching the separated target IDs (at
most `(n+1)^{2r+8}` each, factor `2` per site for large `n`); the remaining events do not read the targets, each
star integral reads only its own target among them (separation and the fixed-map locality), so the targets
integrate independently and `StarCancel9` bounds each factor by `N μ_{i_{z(v)}}(x)`. -/
theorem p92_even_anchor_integral (P : Params9) (hP : P.Valid) (c : ℝ) (hc : 0 < c) :
    ∃ n₀ : ℕ, ∀ n ≥ n₀, ∀ {N : ℕ} {E : Fin N → Fin N → Prop} {M : TagMix N} {G : Colour}
      (S : Setup9 P n N M) (I : IDMap9 P n),
      S07.CondProductBound → AnchorLLL9 S I E G c → StarScopeFacts9 S I E G →
        StarCancel9 S I E G → EvenAnchorIntegral9 S I E G := by
  sorry

/-- P9.2-assignC, assembled moment (09:347–349): the clock comparison at every successful prehistory and the
anchor integral give `4^k ∏ N μ_{i_{z(v)}}(x)`. -/
theorem p92_even_moment {P : Params9} {n N : ℕ} {M : TagMix N} (S : Setup9 P n N M)
    (I : IDMap9 P n) (E : Fin N → Fin N → Prop) (G : Colour)
    (J : Outcome9 I N → FinProb (OddSites9 n → Fin N))
    (hfac : ClockFactor9 S I E G J) (hint : EvenAnchorIntegral9 S I E G) : EvenMoment9 S I E G J := by
  sorry

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
  sorry

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
  sorry

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
