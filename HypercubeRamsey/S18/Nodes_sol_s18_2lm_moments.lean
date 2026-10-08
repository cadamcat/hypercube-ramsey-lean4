import HypercubeRamsey.S18.Nodes_sol_s18_2lm

namespace HypercubeRamsey.S18.Lane_sol_s18_2lm

open Classical Filter
open scoped BigOperators

set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 400000

variable {κ : CConsts} {T : Stage} {k : ℕ} {PT : ProfiledTiling κ T k}
  {hPT : PT.Valid} {D : LateData hPT} {X : CriticalTransferData D}

theorem witnessMean_nonneg (pair : Bool)
    (f : Fin (T.S.N k) → Option (Fin (T.S.N k)) → ℝ)
    (hf : ∀ x z, 0 ≤ f x z) : 0 ≤ witnessMean X pair f := by
  have h := witnessMean_mono (X := X) pair (fun _ _ => 0) f hf
  simpa [witnessMean] using h

/-- The stopped square gains exactly the squared increment. The cross term
vanishes against the indicator of not having stopped before this update. -/
theorem stopped_square_increment (P : TransferProtocol X) (seed : P.Seed)
    (x : Fin (T.S.N k)) (z : Option (Fin (T.S.N k))) (c : ℝ) (t : ℕ) :
    X.rawLaw.E (fun s => likelihood P seed x z s
        (min (t + 1) (stoppingTime P seed x z s c)) ^ 2) =
      X.rawLaw.E (fun s => likelihood P seed x z s
        (min t (stoppingTime P seed x z s c)) ^ 2) +
      X.rawLaw.E (fun s => if t + 1 ≤ stoppingTime P seed x z s c then
        (likelihood P seed x z s (t + 1) - likelihood P seed x z s t) ^ 2 else 0) := by
  let R := fun (s : X.Raw) (j : ℕ) => likelihood P seed x z s j
  let τ := fun s => stoppingTime P seed x z s c
  have hpoint (s : X.Raw) :
      R s (min (t + 1) (τ s)) ^ 2 = R s (min t (τ s)) ^ 2 +
        2 * ((R s (t + 1) - R s t) * (if t + 1 ≤ τ s then R s t else 0)) +
        (if t + 1 ≤ τ s then (R s (t + 1) - R s t) ^ 2 else 0) := by
    by_cases h : t + 1 ≤ τ s
    · rw [if_pos h, if_pos h, Nat.min_eq_left h,
        Nat.min_eq_left (by omega : t ≤ τ s)]
      ring
    · rw [if_neg h, if_neg h, Nat.min_eq_right (by omega : τ s ≤ t + 1),
        Nat.min_eq_right (by omega : τ s ≤ t)]
      ring
  have hlinear := stopped_linear_term_zero P seed x z c (t + 1)
  simp only [Nat.add_sub_cancel] at hlinear
  change X.rawLaw.E (fun s => R s (min (t + 1) (τ s)) ^ 2) = _
  simp_rw [hpoint]
  simp only [FinLaw.E, mul_add, Finset.sum_add_distrib]
  have hlin : (∑ s, X.rawLaw.w s *
      (2 * ((R s (t + 1) - R s t) * (if t + 1 ≤ τ s then R s t else 0)))) = 0 := by
    calc
      _ = 2 * X.rawLaw.E (fun s => (R s (t + 1) - R s t) *
          (if t + 1 ≤ τ s then R s t else 0)) := by
        simp only [FinLaw.E, Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro s _
        ring
      _ = 0 := by rw [hlinear]; ring
  rw [hlin, add_zero]

/-- A bound on squared updates needs only the integrated next-exception
probability; it need not hold conditionally on each earlier transcript. -/
theorem stopped_square_step (P : TransferProtocol X) (seed : P.Seed)
    (x : Fin (T.S.N k)) (z : Option (Fin (T.S.N k))) (c : ℝ) (t : ℕ)
    (a e : ℝ) (ha : 0 ≤ a) (E : X.Raw → Prop)
    (hinc : ∀ s, 0 < X.rawLaw.w s → t + 1 ≤ stoppingTime P seed x z s c →
      (likelihood P seed x z s (t + 1) - likelihood P seed x z s t) ^ 2 ≤
        a * likelihood P seed x z s t ^ 2 + (if E s then e else 0))
    (he : 0 ≤ e) :
    X.rawLaw.E (fun s => likelihood P seed x z s
        (min (t + 1) (stoppingTime P seed x z s c)) ^ 2) ≤
      (1 + a) * X.rawLaw.E (fun s => likelihood P seed x z s
        (min t (stoppingTime P seed x z s c)) ^ 2) + e * X.rawLaw.pr E := by
  rw [stopped_square_increment]
  have hbound : X.rawLaw.E (fun s => if t + 1 ≤ stoppingTime P seed x z s c then
        (likelihood P seed x z s (t + 1) - likelihood P seed x z s t) ^ 2 else 0) ≤
      a * X.rawLaw.E (fun s => likelihood P seed x z s
        (min t (stoppingTime P seed x z s c)) ^ 2) + e * X.rawLaw.pr E := by
    unfold FinLaw.E FinLaw.pr
    rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
    apply Finset.sum_le_sum
    intro s _
    dsimp only
    by_cases hw : 0 < X.rawLaw.w s
    · by_cases h : t + 1 ≤ stoppingTime P seed x z s c
      · have hi := mul_le_mul_of_nonneg_left (hinc s hw h) (X.rawLaw.nonneg s)
        rw [Nat.min_eq_left (by omega : t ≤ stoppingTime P seed x z s c)]
        simp only [h, ↓reduceIte]
        by_cases hs : E s <;> simp only [hs, ↓reduceIte] at hi ⊢ <;> nlinarith only [hi]
      · simp only [h, ↓reduceIte, mul_zero]
        have hreg := mul_nonneg ha (mul_nonneg (X.rawLaw.nonneg s)
          (sq_nonneg (likelihood P seed x z s (min t (stoppingTime P seed x z s c)))))
        split_ifs <;> nlinarith [mul_nonneg he (X.rawLaw.nonneg s)]
    · have hz : X.rawLaw.w s = 0 := le_antisymm (le_of_not_gt hw) (X.rawLaw.nonneg s)
      simp [hz]
  nlinarith only [hbound]

/-- An elementary recurrence suffices when the total increment budget is at
most one. This avoids introducing an exponential Gronwall constant. -/
theorem finite_square_iteration (U : ℕ → ℝ) (N : ℕ) (a e : ℝ)
    (ha : 0 ≤ a) (he : 0 ≤ e) (hzero : U 0 ≤ 1)
    (hstep : ∀ t, t < N → U (t + 1) ≤ (1 + a) * U t + e)
    (htotal : (N : ℝ) * (2 * a + e) ≤ 1) :
    ∀ t, t ≤ N → U t ≤ 1 + (t : ℝ) * (2 * a + e) := by
  intro t
  induction t with
  | zero => intro _; simpa using hzero
  | succ t ih =>
    intro ht
    have hprev := ih (by omega)
    have hsize : U t ≤ 2 := by
      have hle : (t : ℝ) * (2 * a + e) ≤ (N : ℝ) * (2 * a + e) :=
        mul_le_mul_of_nonneg_right (by exact_mod_cast (show t ≤ N by omega)) (by positivity)
      linarith
    have hmul := mul_le_mul_of_nonneg_left hsize ha
    have hnext := hstep t (by omega)
    rw [Nat.cast_succ]
    nlinarith only [hprev, hmul, hnext]

/-- Actual stopped moments, averaged over independently chosen witnesses,
are bounded by two once the finite squared-update budgets are supplied. -/
theorem stopped_second_moment_of_updates (P : TransferProtocol X) (c : ℝ)
    (seed : P.Seed) (pair : Bool) (a e ε : ℝ)
    (ha : 0 ≤ a) (he : 0 ≤ e) (hε : 0 ≤ ε)
    (E : ℕ → Fin (T.S.N k) → Option (Fin (T.S.N k)) → X.Raw → Prop)
    (hinc : ∀ t, t < P.steps → ∀ x z, X.allowed x z → ∀ s,
      0 < X.rawLaw.w s → t + 1 ≤ stoppingTime P seed x z s c →
      (likelihood P seed x z s (t + 1) - likelihood P seed x z s t) ^ 2 ≤
        a * likelihood P seed x z s t ^ 2 + (if E t x z s then e else 0))
    (hex : ∀ t, t < P.steps → witnessMean X pair (fun x z => if X.allowed x z then
      X.rawLaw.pr (E t x z) else 0) ≤ ε)
    (htotal : (P.steps : ℝ) * (2 * a + e * ε) ≤ 1) :
    ∀ t, witnessMean X pair (fun x z => if X.allowed x z then X.rawLaw.E (fun s =>
      likelihood P seed x z s (min t (stoppingTime P seed x z s c)) ^ 2) else 0) ≤ 2 := by
  let U := fun t => witnessMean X pair (fun x z => if X.allowed x z then X.rawLaw.E (fun s =>
    likelihood P seed x z s (min t (stoppingTime P seed x z s c)) ^ 2) else 0)
  have hzero : U 0 ≤ 1 := by
    calc
      _ ≤ witnessMean X pair (fun _ _ => 1) := by
        apply witnessMean_mono
        intro x z
        split_ifs
        · simp [Lane_q_s18_n3.likelihood_one_at_zero, FinLaw.E, X.rawLaw.sum_one]
        · norm_num
      _ = 1 := witnessMean_one pair
  have hstep : ∀ t, t < P.steps → U (t + 1) ≤ (1 + a) * U t + e * ε := by
    intro t ht
    have hpoint : U (t + 1) ≤ witnessMean X pair (fun x z =>
        (1 + a) * (if X.allowed x z then X.rawLaw.E (fun s =>
          likelihood P seed x z s (min t (stoppingTime P seed x z s c)) ^ 2) else 0) +
        e * (if X.allowed x z then X.rawLaw.pr (E t x z) else 0)) := by
      apply witnessMean_mono
      intro x z
      by_cases hx : X.allowed x z
      · simp only [hx, ↓reduceIte]
        exact stopped_square_step P seed x z c t a e ha (E t x z) (hinc t ht x z hx) he
      · simp [hx]
    rw [witnessMean_add, witnessMean_mul_left, witnessMean_mul_left] at hpoint
    have hm := mul_le_mul_of_nonneg_left (hex t ht) he
    change U (t + 1) ≤ (1 + a) * U t + e *
      witnessMean X pair (fun x z => if X.allowed x z then X.rawLaw.pr (E t x z) else 0) at hpoint
    linarith only [hpoint, hm]
  have hiter := finite_square_iteration U P.steps a (e * ε) ha (mul_nonneg he hε)
    hzero hstep htotal
  intro t
  have htau (s : X.Raw) (x : Fin (T.S.N k)) (z : Option (Fin (T.S.N k))) :
      min t (stoppingTime P seed x z s c) =
        min (min t P.steps) (stoppingTime P seed x z s c) := by
    rw [Nat.min_assoc, Nat.min_eq_right (Lane_q_s18_n3.stoppingTime_le_steps P seed x z s c)]
  simp only [htau]
  have hi := hiter (min t P.steps) (Nat.min_le_right _ _)
  have hnum : ((min t P.steps : ℕ) : ℝ) * (2 * a + e * ε) ≤
      (P.steps : ℝ) * (2 * a + e * ε) :=
    mul_le_mul_of_nonneg_right (by exact_mod_cast Nat.min_le_right t P.steps) (by positivity)
  exact hi.trans (by linarith)

/-- No multiplier or barrier trigger occurs strictly before the actual stop. -/
theorem no_stop_trigger_before (P : TransferProtocol X) (seed : P.Seed)
    (x : Fin (T.S.N k)) (z : Option (Fin (T.S.N k))) (s : X.Raw) (c : ℝ)
    {t : ℕ} (ht : t < stoppingTime P seed x z s c) :
    ¬ (factorException P seed x z s t ∨
      Real.exp (Real.rpow (T.S.n k : ℝ) c) < likelihood P seed x z s t) := by
  intro h
  have hsteps := Lane_q_s18_n3.stoppingTime_le_steps P seed x z s c
  let stops := (Finset.range (P.steps + 1)).filter fun j =>
    factorException P seed x z s j ∨
      Real.exp (Real.rpow (T.S.n k : ℝ) c) < likelihood P seed x z s j
  have hmem : t ∈ stops := Finset.mem_filter.mpr ⟨Finset.mem_range.mpr (by omega), h⟩
  have hne : stops.Nonempty := ⟨t, hmem⟩
  have hle : stoppingTime P seed x z s c ≤ t := by
    dsimp only [stoppingTime]
    split_ifs with hn
    · exact Finset.min'_le _ t (by simpa only [stops] using hmem)
    · exact False.elim (hn (by simpa only [stops] using hne))
  omega

/-- Before the first multiplier exception, the likelihood remains positive.
Only the tolerance being less than one is needed here. -/
theorem likelihood_positive_before_stop (P : TransferProtocol X) (seed : P.Seed)
    (x : Fin (T.S.N k)) (z : Option (Fin (T.S.N k))) (c : ℝ)
    (hδ : κ.KB * (((max 1 (PT.tiling.P (D.geom.patchOf X.target)).h : ℕ) : ℝ) * (D.geom.r : ℝ)) *
      bstar T k < 1) (s : X.Raw) :
    ∀ t, t < stoppingTime P seed x z s c → 0 < likelihood P seed x z s t := by
  intro t
  induction t with
  | zero => intro _; rw [Lane_q_s18_n3.likelihood_one_at_zero]; norm_num
  | succ t ih =>
    intro ht
    have hprev := ih (by omega)
    have hn := no_stop_trigger_before P seed x z s c ht
    have hfac : ¬ factorException P seed x z s (t + 1) := fun h => hn (Or.inl h)
    have hclose : |likelihood P seed x z s (t + 1) / likelihood P seed x z s t - 1| ≤
        κ.KB * (((max 1 (PT.tiling.P (D.geom.patchOf X.target)).h : ℕ) : ℝ) * (D.geom.r : ℝ)) *
          bstar T k := by
      apply le_of_not_gt
      intro h
      exact hfac ⟨by omega, by simpa only [Nat.add_sub_cancel] using h⟩
    have hratio : 0 < likelihood P seed x z s (t + 1) / likelihood P seed x z s t := by
      have hlo := (abs_le.mp hclose).1
      linarith
    exact (div_pos_iff.mp hratio).elim (fun h => h.1) (fun h => False.elim (not_lt_of_ge hprev.le h.2))

/-- The elementary square bound behind the stopped recurrence. The large
error term is paid only on the next multiplier exception. -/
theorem multiplier_square_bound (r z B δ G : ℝ)
    (hr : 0 ≤ r) (hB : r ≤ B) (hδ : 0 ≤ δ) (hz : 0 ≤ z) (hG : z ≤ G) :
    (r * z - r) ^ 2 ≤ δ ^ 2 * r ^ 2 +
      (if δ < |z - 1| then B ^ 2 * (G + 1) ^ 2 else 0) := by
  have hB0 : 0 ≤ B := hr.trans hB
  have hG0 : 0 ≤ G := hz.trans hG
  have habs : |z - 1| ≤ G + 1 := by
    apply abs_le.mpr
    constructor <;> linarith
  have habsr : |r| ≤ B := by simpa [abs_of_nonneg hr] using hB
  by_cases h : δ < |z - 1|
  · rw [if_pos h]
    have hprod : |r * (z - 1)| ≤ B * (G + 1) := by
      rw [abs_mul]
      exact mul_le_mul habsr habs (abs_nonneg _) hB0
    have hsq : (r * (z - 1)) ^ 2 ≤ (B * (G + 1)) ^ 2 := by
      have hpow := pow_le_pow_left₀ (abs_nonneg (r * (z - 1))) hprod 2
      simpa only [sq_abs] using hpow
    nlinarith [mul_nonneg (sq_nonneg δ) (sq_nonneg r)]
  · rw [if_neg h]
    have hprod : |r * (z - 1)| ≤ r * δ := by
      rw [abs_mul, abs_of_nonneg hr]
      exact mul_le_mul_of_nonneg_left (le_of_not_gt h) hr
    have hsq : (r * (z - 1)) ^ 2 ≤ (r * δ) ^ 2 := by
      have hpow := pow_le_pow_left₀ (abs_nonneg (r * (z - 1))) hprod 2
      simpa only [sq_abs] using hpow
    nlinarith only [hsq]

/-- At an update before or at the stop, a crude multiplier cap supplies the
squared-update premise using the protocol's actual exception event. -/
theorem stopped_increment_bound (P : TransferProtocol X) (seed : P.Seed)
    (x : Fin (T.S.N k)) (z : Option (Fin (T.S.N k))) (c G : ℝ)
    (δ : ℝ) (hδdef : δ = κ.KB *
      (((max 1 (PT.tiling.P (D.geom.patchOf X.target)).h : ℕ) : ℝ) * (D.geom.r : ℝ)) * bstar T k)
    (hδ0 : 0 ≤ δ) (hδ1 : δ < 1) (t : ℕ) (s : X.Raw)
    (ht : t + 1 ≤ stoppingTime P seed x z s c)
    (hG : likelihood P seed x z s (t + 1) / likelihood P seed x z s t ≤ G) :
    (likelihood P seed x z s (t + 1) - likelihood P seed x z s t) ^ 2 ≤
      δ ^ 2 * likelihood P seed x z s t ^ 2 +
      (if factorException P seed x z s (t + 1) then
        Real.exp (Real.rpow (T.S.n k : ℝ) c) ^ 2 * (G + 1) ^ 2 else 0) := by
  have hbefore : t < stoppingTime P seed x z s c := by omega
  have hpos := likelihood_positive_before_stop P seed x z c (by rw [← hδdef]; exact hδ1) s t hbefore
  have hbar : likelihood P seed x z s t ≤ Real.exp (Real.rpow (T.S.n k : ℝ) c) := by
    have hn := no_stop_trigger_before P seed x z s c hbefore
    exact le_of_not_gt (fun h => hn (Or.inr h))
  have hz := div_nonneg (Lane_q_s18_n3.likelihood_nonneg P seed x z s (t + 1)) hpos.le
  have heq : likelihood P seed x z s t *
      (likelihood P seed x z s (t + 1) / likelihood P seed x z s t) =
      likelihood P seed x z s (t + 1) := by field_simp
  have h := multiplier_square_bound _ _ _ δ G hpos.le hbar hδ0 hz hG
  rw [heq] at h
  simpa only [factorException, show t + 1 > 0 by omega, true_and,
    Nat.add_sub_cancel, ← hδdef] using h

/-- The regular squared-update budget tends to zero for every fixed
polylogarithmic block bound. The remaining power of n is n^(-23/25). -/
theorem polylog_squared_bstar_tendsto (T : Stage) (p q : ℕ) (K : ℝ) :
    Tendsto (fun k => (T.S.n k : ℝ) * Real.log (T.S.n k : ℝ) ^ p *
      (K * Real.log (T.S.n k : ℝ) ^ q * bstar T k) ^ 2) atTop (nhds 0) := by
  have hn : Tendsto (fun k => (T.S.n k : ℝ)) atTop atTop :=
    tendsto_natCast_atTop_atTop.comp T.S.n_tendsto
  have hlog := ((isLittleO_log_rpow_rpow_atTop ((p + 2 * q : ℕ) : ℝ)
    (by norm_num : (0 : ℝ) < 23 / 25)).tendsto_div_nhds_zero).comp hn
  have hlim : Tendsto (fun k => K ^ 2 *
      (Real.log (T.S.n k : ℝ) ^ (p + 2 * q) /
        Real.rpow (T.S.n k : ℝ) (23 / 25 : ℝ))) atTop (nhds 0) := by
    simpa only [Function.comp_def, Real.rpow_natCast, Real.rpow_eq_pow, mul_zero] using tendsto_const_nhds.mul hlog
  apply hlim.congr'
  filter_upwards [T.S.n_tendsto.eventually_ge_atTop 1] with k hk
  have hnpos : 0 < (T.S.n k : ℝ) := by exact_mod_cast (show 0 < T.S.n k by omega)
  have hb : (T.S.n k : ℝ) * bstar T k ^ 2 =
      1 / Real.rpow (T.S.n k : ℝ) (23 / 25 : ℝ) := by
    unfold bstar
    simp only [Real.rpow_eq_pow]
    calc
      _ = (T.S.n k : ℝ) ^ (1 + (-1 + (0.04 : ℝ)) * 2) := by
        rw [Real.rpow_add hnpos (1 : ℝ) ((-1 + (0.04 : ℝ)) * 2),
          Real.rpow_mul hnpos.le (-1 + (0.04 : ℝ)) (2 : ℝ)]
        simp only [Real.rpow_two, Real.rpow_one]
      _ = (T.S.n k : ℝ) ^ (-(23 / 25 : ℝ)) := by congr 1; norm_num
      _ = _ := by rw [Real.rpow_neg hnpos.le, one_div]
  symm
  rw [pow_add, pow_mul]
  calc
    _ = K ^ 2 * (Real.log (T.S.n k : ℝ) ^ p *
        (Real.log (T.S.n k : ℝ) ^ q) ^ 2) *
        ((T.S.n k : ℝ) * bstar T k ^ 2) := by ring
    _ = _ := by rw [hb]; ring

/-- A fixed polylogarithm is negligible against any positive power. -/
theorem polylog_le_power_eventually (T : Stage) (q : ℕ) (C d : ℝ) (hd : 0 < d) :
    ∀ᶠ k in atTop, C * Real.log (T.S.n k : ℝ) ^ q ≤
      Real.rpow (T.S.n k : ℝ) d := by
  have hsmall := (isLittleO_log_rpow_rpow_atTop (q : ℝ) hd).const_mul_left C
  have hn : Tendsto (fun k => (T.S.n k : ℝ)) atTop atTop :=
    tendsto_natCast_atTop_atTop.comp T.S.n_tendsto
  filter_upwards [hn.eventually hsmall.eventuallyLE] with k hk
  rw [Real.rpow_natCast, Real.norm_eq_abs,
    Real.norm_of_nonneg (Real.rpow_nonneg (Nat.cast_nonneg _) _)] at hk
  exact (le_abs_self _).trans hk

/-- The barrier and a crude exponential-in-block-size cap are absorbed by
an exception probability with a larger positive exponent. -/
theorem barrier_error_tendsto (T : Stage) (p q : ℕ) (C c d : ℝ)
    (hc : 0 < c) (hcd : c < d) :
    Tendsto (fun k => (T.S.n k : ℝ) * Real.log (T.S.n k : ℝ) ^ p *
      Real.exp (C * Real.log (T.S.n k : ℝ) ^ q +
        2 * Real.rpow (T.S.n k : ℝ) c - Real.rpow (T.S.n k : ℝ) d)) atTop (nhds 0) := by
  have hd : 0 < d := hc.trans hcd
  have hn : Tendsto (fun k => (T.S.n k : ℝ)) atTop atTop :=
    tendsto_natCast_atTop_atTop.comp T.S.n_tendsto
  have hratio : Tendsto (fun k => 8 * Real.rpow (T.S.n k : ℝ) (c - d))
      atTop (nhds 0) := by
    have h := (tendsto_rpow_neg_atTop (by linarith : (0 : ℝ) < d - c)).comp hn
    simpa only [Function.comp_def, neg_sub, Real.rpow_eq_pow, mul_zero] using tendsto_const_nhds.mul h
  have hsmallpow : ∀ᶠ k in atTop,
      2 * Real.rpow (T.S.n k : ℝ) c ≤ Real.rpow (T.S.n k : ℝ) d / 4 := by
    filter_upwards [hratio.eventually (Iio_mem_nhds (by norm_num : (0 : ℝ) < 1)),
      T.S.n_tendsto.eventually_ge_atTop 1] with k hk hn1
    have hnpos : 0 < (T.S.n k : ℝ) := by exact_mod_cast (show 0 < T.S.n k by omega)
    simp only [Real.rpow_eq_pow] at hk ⊢
    rw [Real.rpow_sub hnpos] at hk
    have hp : 0 < Real.rpow (T.S.n k : ℝ) d := Real.rpow_pos_of_pos hnpos d
    have h := (div_lt_iff₀ hp).mp (show 8 * Real.rpow (T.S.n k : ℝ) c /
        Real.rpow (T.S.n k : ℝ) d < 1 by simpa only [Real.rpow_eq_pow, mul_div_assoc] using hk)
    simp only [Real.rpow_eq_pow] at h
    linarith
  have hC := polylog_le_power_eventually T q (4 * C) d hd
  have hp := polylog_le_power_eventually T 1 (4 * (p + 1 : ℝ)) d hd
  have hbound : ∀ᶠ k in atTop,
      (T.S.n k : ℝ) * Real.log (T.S.n k : ℝ) ^ p *
        Real.exp (C * Real.log (T.S.n k : ℝ) ^ q +
          2 * Real.rpow (T.S.n k : ℝ) c - Real.rpow (T.S.n k : ℝ) d) ≤
      Real.exp (-Real.rpow (T.S.n k : ℝ) d / 4) := by
    filter_upwards [hC, hp, hsmallpow, T.S.n_tendsto.eventually_ge_atTop 1] with k hC hp hpow hn1
    have hnpos : 0 < (T.S.n k : ℝ) := by exact_mod_cast (show 0 < T.S.n k by omega)
    have hL : 0 ≤ Real.log (T.S.n k : ℝ) := Real.log_nonneg (by exact_mod_cast hn1)
    have hLn : Real.log (T.S.n k : ℝ) ≤ (T.S.n k : ℝ) :=
      (Real.log_le_sub_one_of_pos hnpos).trans (by linarith)
    have hpref : (T.S.n k : ℝ) * Real.log (T.S.n k : ℝ) ^ p ≤
        Real.exp ((p + 1 : ℝ) * Real.log (T.S.n k : ℝ)) := by
      calc
        _ ≤ (T.S.n k : ℝ) * (T.S.n k : ℝ) ^ p := by gcongr
        _ = (T.S.n k : ℝ) ^ (p + 1) := by rw [pow_succ]; ring
        _ = _ := by rw [← Real.rpow_natCast, Real.rpow_def_of_pos hnpos, Nat.cast_add, Nat.cast_one]; ring_nf
    calc
      _ ≤ Real.exp ((p + 1 : ℝ) * Real.log (T.S.n k : ℝ)) *
          Real.exp (C * Real.log (T.S.n k : ℝ) ^ q +
            2 * Real.rpow (T.S.n k : ℝ) c - Real.rpow (T.S.n k : ℝ) d) :=
        mul_le_mul_of_nonneg_right hpref (Real.exp_pos _).le
      _ = Real.exp ((p + 1 : ℝ) * Real.log (T.S.n k : ℝ) +
          C * Real.log (T.S.n k : ℝ) ^ q +
            2 * Real.rpow (T.S.n k : ℝ) c - Real.rpow (T.S.n k : ℝ) d) := by
        rw [← Real.exp_add]; congr 1; ring
      _ ≤ _ := Real.exp_le_exp.mpr (by simp only [pow_one] at hp; linarith)
  have hdecay : Tendsto (fun k => Real.exp (-Real.rpow (T.S.n k : ℝ) d / 4))
      atTop (nhds 0) := by
    apply Real.tendsto_exp_atBot.comp
    have hpow := (tendsto_rpow_atTop hd).comp hn
    simpa only [Function.comp_def, Real.rpow_eq_pow, neg_div] using tendsto_neg_atTop_atBot.comp
      (Filter.Tendsto.atTop_div_const (by norm_num : (0 : ℝ) < 4) hpow)
  exact squeeze_zero' (Eventually.of_forall (fun k => by
    have hlog : 0 ≤ Real.log (T.S.n k : ℝ) ^ p := by
      by_cases hn0 : T.S.n k = 0
      · simp [hn0]
      · exact pow_nonneg (Real.log_nonneg (by exact_mod_cast (show 1 ≤ T.S.n k by omega))) _
    exact mul_nonneg (mul_nonneg (Nat.cast_nonneg _) hlog) (Real.exp_pos _).le)) hbound hdecay

/-- Low-mode height and depth give a uniform quadratic-log block bound. -/
theorem block_size_polylog (hκ : κ.Admissible) (D : LateData hPT)
    (hL : 4 ≤ Real.log (T.S.n k : ℝ)) (i : Fin PT.tiling.m) :
    (((max 1 (PT.tiling.P i).h : ℕ) : ℝ) * (D.geom.r : ℝ)) ≤
      (8 * κ.A0 + 1) * Real.log (T.S.n k : ℝ) ^ 2 := by
  let L := Real.log (T.S.n k : ℝ)
  have hL1 : 1 ≤ L := by dsimp [L]; linarith
  have hCb : 100 < κ.Cb := by
    have hratio : 0 < 100 * κ.aC / κ.aB :=
      div_pos (mul_pos (by norm_num) hκ.aC_rng.1) hκ.aB_rng.1
    linarith [hκ.Cb_big]
  have hMlo : 0 < (κ.Mlo : ℝ) := by linarith [hκ.Mlo_big]
  have hcm : κ.cq * (κ.Mlo : ℝ) < 1 := by
    have h := (lt_div_iff₀ (show 0 < 20 * (κ.Mlo : ℝ) by positivity)).mp hκ.cq_rng.2
    nlinarith
  have hheight : ((PT.tiling.P i).h : ℝ) ≤ 2 * L := by
    cases hm : PT.tiling.mode with
    | bounded =>
      obtain ⟨_, hall⟩ := hPT.tiling_valid.bounded_data hm
      obtain ⟨_, hh, _, _, _⟩ := hall i
      simp only [hh, Nat.cast_zero]
      positivity
    | lowDirect =>
      obtain ⟨_, _, _, _, hh, _, _⟩ := hPT.tiling_valid.direct_data (Or.inl hm) i
      simp only [hh, Nat.cast_zero]
      positivity
    | lowCluster =>
      obtain ⟨_, _, _, _, _, _, _, _, hh, hq, _, _⟩ :=
        hPT.tiling_valid.cluster_data (Or.inl hm) i
      have hq' : ((PT.tiling.P i).q : ℝ) ≤ Real.rpow L κ.cq := hq.mp hm
      have hpow : Real.rpow ((PT.tiling.P i).q : ℝ) (κ.Mlo : ℝ) ≤ L := by
        calc
          _ ≤ Real.rpow (Real.rpow L κ.cq) (κ.Mlo : ℝ) :=
            Real.rpow_le_rpow (Nat.cast_nonneg _) hq' (Nat.cast_nonneg _)
          _ = Real.rpow L (κ.cq * (κ.Mlo : ℝ)) := (Real.rpow_mul (by linarith) _ _).symm
          _ ≤ Real.rpow L 1 := Real.rpow_le_rpow_of_exponent_le hL1 hcm.le
          _ = L := Real.rpow_one _
      have hh' : ((PT.tiling.P i).h : ℝ) <
          2 * Real.rpow ((PT.tiling.P i).q : ℝ) (κ.Mlo : ℝ) := by simpa [hm] using hh
      linarith
    | highDirect => have hl := D.low_mode; simp [Mode.isLow, hm] at hl
    | highSmall => have hl := D.low_mode; simp [Mode.isLow, hm] at hl
    | highLarge => have hl := D.low_mode; simp [Mode.isLow, hm] at hl
  have hmax : ((max 1 (PT.tiling.P i).h : ℕ) : ℝ) ≤ 2 * L := by
    rw [Nat.cast_max, Nat.cast_one]
    exact max_le (by linarith) hheight
  have hA : 0 ≤ κ.A0 := (show (0 : ℝ) ≤ 10 ^ 6 * (κ.R : ℝ) by positivity).trans hκ.A0_big
  have hdepth : (D.geom.r : ℝ) ≤ 4 * κ.A0 * L := by
    have hlog2 : (1 / 2 : ℝ) ≤ Real.log 2 := by linarith [Real.log_two_gt_d9]
    have hr := D.l16_valid.r_upper
    dsimp [L]
    nlinarith [show (0 : ℝ) ≤ (D.geom.r : ℝ) from Nat.cast_nonneg D.geom.r]
  calc
    _ ≤ (2 * L) * (4 * κ.A0 * L) := mul_le_mul hmax hdepth (Nat.cast_nonneg _) (by positivity)
    _ ≤ _ := by dsimp [L]; nlinarith [sq_nonneg (Real.log (T.S.n k : ℝ))]

/-- The accumulated regular multiplier drift for a block is negligible. -/
theorem polylog_bstar_tendsto (T : Stage) (q : ℕ) (K : ℝ) :
    Tendsto (fun k => K * Real.log (T.S.n k : ℝ) ^ q * bstar T k) atTop (nhds 0) := by
  have hn : Tendsto (fun k => (T.S.n k : ℝ)) atTop atTop :=
    tendsto_natCast_atTop_atTop.comp T.S.n_tendsto
  have hlog := ((isLittleO_log_rpow_rpow_atTop (q : ℝ)
    (by norm_num : (0 : ℝ) < 24 / 25)).tendsto_div_nhds_zero).comp hn
  have hlim : Tendsto (fun k => K * (Real.log (T.S.n k : ℝ) ^ q /
      Real.rpow (T.S.n k : ℝ) (24 / 25 : ℝ))) atTop (nhds 0) := by
    simpa only [Function.comp_def, Real.rpow_natCast, Real.rpow_eq_pow, mul_zero] using tendsto_const_nhds.mul hlog
  apply hlim.congr'
  filter_upwards [T.S.n_tendsto.eventually_ge_atTop 1] with k hk
  have hnpos : 0 < (T.S.n k : ℝ) := by exact_mod_cast (show 0 < T.S.n k by omega)
  unfold bstar
  norm_num
  rw [Real.rpow_neg hnpos.le, div_eq_mul_inv]
  ring

/-- The total regular budget and the number-of-calls budget hold uniformly
for every low-mode late datum, before choosing a protocol. -/
theorem regular_budgets_eventually (hκ : κ.Admissible) (T : Stage) :
    ∀ᶠ k in atTop, ∀ PT : ProfiledTiling κ T k, ∀ hPT : PT.Valid, ∀ D : LateData hPT,
      ∀ i : Fin PT.tiling.m,
      let δ := κ.KB * (((max 1 (PT.tiling.P i).h : ℕ) : ℝ) * (D.geom.r : ℝ)) * bstar T k
      0 ≤ δ ∧ δ < 1 ∧ (⌈Real.log (T.S.n k : ℝ) ^ 20⌉₊ : ℝ) * δ ≤ 1 / 2 ∧
        (T.S.n k : ℝ) * Real.log (T.S.n k : ℝ) ^ 20 * (2 * δ ^ 2) ≤ 1 / 2 := by
  let K := κ.KB * (8 * κ.A0 + 1)
  have hKB : 0 ≤ κ.KB := (show (0 : ℝ) ≤ 10 ^ 6 * (κ.R : ℝ) by positivity).trans hκ.KB_big
  have hA : 0 ≤ κ.A0 := (show (0 : ℝ) ≤ 10 ^ 6 * (κ.R : ℝ) by positivity).trans hκ.A0_big
  have hn : Tendsto (fun k => (T.S.n k : ℝ)) atTop atTop :=
    tendsto_natCast_atTop_atTop.comp T.S.n_tendsto
  have hL := (Real.tendsto_log_atTop.comp hn).eventually_ge_atTop 4
  have hδ := (polylog_bstar_tendsto T 2 K).eventually (Iio_mem_nhds (by norm_num : (0 : ℝ) < 1))
  have hcall := (polylog_bstar_tendsto T 22 (2 * K)).eventually
    (Iio_mem_nhds (by norm_num : (0 : ℝ) < 1 / 2))
  have hsq : ∀ᶠ k in atTop, 2 * ((T.S.n k : ℝ) * Real.log (T.S.n k : ℝ) ^ 20 *
      (K * Real.log (T.S.n k : ℝ) ^ 2 * bstar T k) ^ 2) < 1 / 2 := by
    have hlim := (tendsto_const_nhds (x := (2 : ℝ)) (f := atTop)).mul
      (polylog_squared_bstar_tendsto T 20 2 K)
    have hlim' : Tendsto (fun k => 2 * ((T.S.n k : ℝ) * Real.log (T.S.n k : ℝ) ^ 20 *
        (K * Real.log (T.S.n k : ℝ) ^ 2 * bstar T k) ^ 2)) atTop (nhds 0) := by simpa using hlim
    exact hlim'.eventually (Iio_mem_nhds (by norm_num : (0 : ℝ) < 1 / 2))
  filter_upwards [hL, hδ, hcall, hsq] with k hL hδ hcall hsq
  intro PT hPT D i
  dsimp only [Function.comp_def] at hL
  dsimp only
  let δ := κ.KB * (((max 1 (PT.tiling.P i).h : ℕ) : ℝ) * (D.geom.r : ℝ)) * bstar T k
  have hδ0 : 0 ≤ δ := mul_nonneg (mul_nonneg hKB (mul_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _))) (by unfold bstar; positivity)
  have hδbound : δ ≤ K * Real.log (T.S.n k : ℝ) ^ 2 * bstar T k := by
    have h := mul_le_mul_of_nonneg_left (block_size_polylog hκ D hL i) hKB
    have h' := mul_le_mul_of_nonneg_right h (show 0 ≤ bstar T k by unfold bstar; positivity)
    simpa only [δ, K, mul_assoc] using h'
  have hceil : (⌈Real.log (T.S.n k : ℝ) ^ 20⌉₊ : ℝ) ≤ 2 * Real.log (T.S.n k : ℝ) ^ 20 := by
    have hpow : 1 ≤ Real.log (T.S.n k : ℝ) ^ 20 := one_le_pow₀ (by linarith)
    have h := (Nat.ceil_lt_add_one (pow_nonneg (by linarith : 0 ≤ Real.log (T.S.n k : ℝ)) 20)).le
    linarith
  refine ⟨hδ0, hδbound.trans_lt hδ, ?_, ?_⟩
  · calc
      _ ≤ (2 * Real.log (T.S.n k : ℝ) ^ 20) *
          (K * Real.log (T.S.n k : ℝ) ^ 2 * bstar T k) :=
        mul_le_mul hceil hδbound hδ0 (by positivity)
      _ = 2 * K * Real.log (T.S.n k : ℝ) ^ 22 * bstar T k := by ring
      _ ≤ 1 / 2 := hcall.le
  · have hsqbound : δ ^ 2 ≤ (K * Real.log (T.S.n k : ℝ) ^ 2 * bstar T k) ^ 2 := by
      nlinarith only [hδ0, hδbound]
    have h := mul_le_mul_of_nonneg_left hsqbound
      (show 0 ≤ 2 * (T.S.n k : ℝ) * Real.log (T.S.n k : ℝ) ^ 20 by positivity)
    nlinarith only [h, hsq]

end HypercubeRamsey.S18.Lane_sol_s18_2lm
