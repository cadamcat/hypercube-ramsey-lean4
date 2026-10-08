import HypercubeRamsey.S10.ClusterExclusion_p_s10_1k

namespace HypercubeRamsey.Lane_q_s10_d3

open scoped BigOperators

/-- Expectations commute with a finite image law. -/
theorem expect_map {α β : Type*} [Fintype α] [Fintype β] [DecidableEq β]
    (P : HypercubeRamsey.FinProb α) (f : α → β) (g : β → ℝ) :
    (HypercubeRamsey.FinProb.map P f).expect g = P.expect (g ∘ f) := by
  classical
  unfold HypercubeRamsey.FinProb.expect HypercubeRamsey.FinProb.map
  calc
    (∑ b, (∑ a, if f a = b then P.w a else 0) * g b) =
        ∑ b, ∑ a, (if f a = b then P.w a else 0) * g b := by
      apply Finset.sum_congr rfl
      intro b hb
      rw [Finset.sum_mul]
    _ = ∑ a, ∑ b, (if f a = b then P.w a else 0) * g b := Finset.sum_comm
    _ = ∑ a, P.w a * g (f a) := by
      apply Finset.sum_congr rfl
      intro a ha
      simp

/-- A coarse exponential upper bound for powers of two. -/
theorem twoPow_le_exp_two (k : ℕ) :
    (2 : ℝ) ^ k ≤ Real.exp (2 * (k : ℝ)) := by
  have hlog : Real.log 2 ≤ 2 := by
    have h := Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 2)
    linarith
  have hbase : (2 : ℝ) ≤ Real.exp 2 := Real.le_exp_of_log_le hlog
  calc
    (2 : ℝ) ^ k ≤ (Real.exp 2) ^ k := pow_le_pow_left₀ (by norm_num) hbase k
    _ = Real.exp (2 * (k : ℝ)) := by
      rw [← Real.exp_nat_mul]
      ring_nf

/-- A polynomial power is dominated by an exponential of any larger power. -/
theorem power_exp_neg_tendsto {a b c : ℝ}
    (ha : 0 < a) (hba : b < a) (hc : 0 < c) :
    Filter.Tendsto (fun n : ℕ => (n : ℝ) ^ b * Real.exp (-c * (n : ℝ) ^ a))
      Filter.atTop (nhds 0) := by
  have hpow : Filter.Tendsto (fun n : ℕ => (n : ℝ) ^ a)
      Filter.atTop Filter.atTop :=
    (_root_.tendsto_rpow_atTop ha).comp tendsto_natCast_atTop_atTop
  have hscaled : Filter.Tendsto
      (fun n : ℕ => ((n : ℝ) ^ a) ^ (b / a) *
        Real.exp (-c * (n : ℝ) ^ a)) Filter.atTop (nhds 0) :=
    (tendsto_rpow_mul_exp_neg_mul_atTop_nhds_zero (b / a) c hc).comp hpow
  have heq :
      (fun n : ℕ => (n : ℝ) ^ b * Real.exp (-c * (n : ℝ) ^ a)) =ᶠ[Filter.atTop]
        (fun n : ℕ => ((n : ℝ) ^ a) ^ (b / a) *
          Real.exp (-c * (n : ℝ) ^ a)) := by
    filter_upwards [Filter.eventually_atTop.2 ⟨1, fun _ hn => hn⟩] with n hn
    have hnpos : 0 < (n : ℝ) := by exact_mod_cast (by omega : 0 < n)
    have hexp : a * (b / a) = b := by field_simp [ne_of_gt ha]
    have hpower : (n : ℝ) ^ b = ((n : ℝ) ^ a) ^ (b / a) := by
      calc
        (n : ℝ) ^ b = (n : ℝ) ^ (a * (b / a)) := by rw [hexp]
        _ = ((n : ℝ) ^ a) ^ (b / a) := Real.rpow_mul hnpos.le a (b / a)
    simp [hpower]
  exact Filter.Tendsto.congr' heq.symm hscaled

/-- The budget for a list of any positive size up to the Section 10 block
count is eventually below one half. -/
noncomputable def retainedBudgetUpper (n : ℕ) (δ : ℝ) : ℝ :=
  Real.exp (-(n : ℝ) ^ (300 * δ)) +
    3 * (n : ℝ) ^ (200 * δ) *
      (Real.exp (-((6 / 25 : ℝ) * (n : ℝ) ^ (299 * δ))) +
        Real.exp (-((2 / 5 : ℝ) * (n : ℝ) ^ (300 * δ))))

theorem eventually_retainedBudgetUpper_lt_half {δ : ℝ} (hδ : 0 < δ) :
    ∀ᶠ n : ℕ in Filter.atTop, retainedBudgetUpper n δ < 1 / 2 := by
  have hfirst : Filter.Tendsto
      (fun n : ℕ => Real.exp (-1 * (n : ℝ) ^ (300 * δ)))
      Filter.atTop (nhds 0) := by
    have hpow : Filter.Tendsto (fun n : ℕ => (n : ℝ) ^ (300 * δ))
        Filter.atTop Filter.atTop :=
      (_root_.tendsto_rpow_atTop (by positivity)).comp tendsto_natCast_atTop_atTop
    have hbase := Real.tendsto_exp_atBot.comp
      (Filter.tendsto_neg_atTop_atBot.comp hpow)
    have heq :
        (fun n : ℕ => Real.exp (-1 * (n : ℝ) ^ (300 * δ))) =ᶠ[Filter.atTop]
          (fun n : ℕ => Real.exp (-(n : ℝ) ^ (300 * δ))) := by
      filter_upwards with n
      congr 1
      ring
    exact Filter.Tendsto.congr' heq.symm hbase
  have hown : Filter.Tendsto
      (fun n : ℕ => 3 * (n : ℝ) ^ (200 * δ) *
        Real.exp (-((6 / 25 : ℝ) * (n : ℝ) ^ (299 * δ))))
      Filter.atTop (nhds 0) := by
    have h := power_exp_neg_tendsto (a := 299 * δ) (b := 200 * δ)
      (c := 6 / 25) (by positivity) (by nlinarith) (by norm_num)
    simpa [mul_assoc, mul_left_comm, mul_comm] using h.const_mul (3 : ℝ)
  have hexternal : Filter.Tendsto
      (fun n : ℕ => 3 * (n : ℝ) ^ (200 * δ) *
        Real.exp (-((2 / 5 : ℝ) * (n : ℝ) ^ (300 * δ))))
      Filter.atTop (nhds 0) := by
    have h := power_exp_neg_tendsto (a := 300 * δ) (b := 200 * δ)
      (c := 2 / 5) (by positivity) (by nlinarith) (by norm_num)
    simpa [mul_assoc, mul_left_comm, mul_comm] using h.const_mul (3 : ℝ)
  have htotal : Filter.Tendsto (retainedBudgetUpper · δ)
      Filter.atTop (nhds 0) := by
    have heq : (retainedBudgetUpper · δ) =ᶠ[Filter.atTop]
        (fun n => Real.exp (-1 * (n : ℝ) ^ (300 * δ)) +
          3 * (n : ℝ) ^ (200 * δ) *
            Real.exp (-((6 / 25 : ℝ) * (n : ℝ) ^ (299 * δ))) +
          3 * (n : ℝ) ^ (200 * δ) *
            Real.exp (-((2 / 5 : ℝ) * (n : ℝ) ^ (300 * δ)))) := by
      filter_upwards with n
      simp [retainedBudgetUpper]
      ring
    simpa using Filter.Tendsto.congr' heq.symm ((hfirst.add hown).add hexternal)
  exact htotal.eventually (Iio_mem_nhds (by norm_num))

/-- A smaller real power is eventually dominated by a larger one. -/
theorem eventually_power_gap {a b c : ℝ} (hab : a < b) (hc : 0 < c) :
    ∀ᶠ n : ℕ in Filter.atTop, c * (n : ℝ) ^ a ≤ (n : ℝ) ^ b := by
  have hpow : Filter.Tendsto (fun n : ℕ => (n : ℝ) ^ (b - a))
      Filter.atTop Filter.atTop :=
    (_root_.tendsto_rpow_atTop (sub_pos.mpr hab)).comp
      tendsto_natCast_atTop_atTop
  have hlarge : ∀ᶠ n : ℕ in Filter.atTop, c ≤ (n : ℝ) ^ (b - a) :=
    hpow.eventually_ge_atTop c
  filter_upwards [hlarge, Filter.eventually_atTop.2 ⟨1, fun n hn => hn⟩] with n hn hn1
  have hnpos : 0 < (n : ℝ) := by exact_mod_cast hn1
  have hfactor : (n : ℝ) ^ b = (n : ℝ) ^ a * (n : ℝ) ^ (b - a) := by
    rw [← Real.rpow_add hnpos]
    congr 1
    ring
  calc
    c * (n : ℝ) ^ a ≤ (n : ℝ) ^ (b - a) * (n : ℝ) ^ a :=
      mul_le_mul_of_nonneg_right hn (Real.rpow_nonneg (le_of_lt hnpos) _)
    _ = (n : ℝ) ^ b := by rw [mul_comm, ← hfactor]

/-- The sum of the set-bit positions of `n` is at most quadratic in `log₂ n`.
This controls the residual projection fiber used for an odd group. -/
theorem bitIndicesExponent_le {d : ℕ} :
    (∑ i : Fin d.bitIndices.length, d.bitIndices.get i) ≤ (Nat.log 2 d + 1) ^ 2 := by
  classical
  let L := Nat.log 2 d
  have hidx (i : ℕ) (hi : i ∈ d.bitIndices) : i ≤ L := by
    have hp : 2 ^ i ≤ d := Nat.two_pow_le_of_mem_bitIndices hi
    exact Nat.le_log_of_pow_le (by norm_num : 1 < 2) hp
  have hlen : d.bitIndices.length ≤ L + 1 := by
    have hsub : d.bitIndices.toFinset ⊆ Finset.range (L + 1) := by
      intro i hi
      exact Finset.mem_range.mpr (Nat.lt_succ_of_le (hidx i (List.mem_toFinset.mp hi)))
    have hcard := Finset.card_le_card hsub
    rw [List.toFinset_card_of_nodup Nat.bitIndices_nodup] at hcard
    simpa [L, Finset.card_range] using hcard
  have hsumBound : ∀ l : List ℕ, (∀ i ∈ l, i ≤ L) → l.sum ≤ l.length * L := by
    intro l
    induction l with
    | nil => intro; simp
    | cons x xs ih =>
      intro h
      have hx : x ≤ L := h x (by simp)
      have hxs : xs.sum ≤ xs.length * L := ih (by
        intro y hy
        exact h y (by simp [hy]))
      simp only [List.sum_cons, List.length_cons]
      nlinarith
  have hsumList : d.bitIndices.sum ≤ d.bitIndices.length * L :=
    hsumBound d.bitIndices (fun i hi => hidx i hi)
  have hsumIdx : (∑ i : Fin d.bitIndices.length, d.bitIndices.get i) = d.bitIndices.sum := by
    simpa using (Fin.sum_univ_fun_getElem d.bitIndices id)
  rw [hsumIdx]
  calc
    d.bitIndices.sum ≤ d.bitIndices.length * L := hsumList
    _ ≤ (L + 1) * L := Nat.mul_le_mul_right L hlen
    _ ≤ (L + 1) ^ 2 := by nlinarith

/-- The logarithmic residual fiber factor is negligible compared with every
positive real power of the dimension. -/
theorem eventually_log_fiber_gap {ζ : ℝ} (hζ : 0 < ζ) :
    ∀ᶠ n : ℕ in Filter.atTop,
      2 * ((Nat.log 2 n : ℝ) + 1) ^ 2 ≤ (n : ℝ) ^ ζ / 8 := by
  let ε : ℝ := ζ / 8
  let C : ℝ := 1 / (ε * Real.log 2)
  have hε : 0 < ε := by dsimp [ε]; positivity
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hC : 0 < C := by dsimp [C]; positivity
  have hgap := eventually_power_gap (a := ζ / 4) (b := ζ)
    (c := 16 * (C + 1) ^ 2) (by linarith) (by positivity)
  filter_upwards [hgap, Filter.eventually_atTop.2 ⟨2, fun n hn => hn⟩] with n hgap hn
  have hnreal : 1 ≤ (n : ℝ) := by exact_mod_cast (by omega : 1 ≤ n)
  have hlognat : (Nat.log 2 n : ℝ) ≤ Real.log (n : ℝ) / Real.log 2 := by
    calc
      (Nat.log 2 n : ℝ) = (Nat.log2 n : ℝ) := by rw [Nat.log2_eq_log_two]
      _ ≤ Real.logb 2 n := Real.log2_le_logb n
      _ = Real.log (n : ℝ) / Real.log 2 := by rfl
  have hlogpow := Real.log_le_rpow_div (Nat.cast_nonneg n) hε
  have hpowone : 1 ≤ (n : ℝ) ^ ε := by
    calc
      1 = (n : ℝ) ^ (0 : ℝ) := by rw [Real.rpow_zero]
      _ ≤ (n : ℝ) ^ ε := Real.rpow_le_rpow_of_exponent_le hnreal (by positivity)
  have hL : (Nat.log 2 n : ℝ) + 1 ≤ (C + 1) * (n : ℝ) ^ ε := by
    have hdiv : Real.log (n : ℝ) / Real.log 2 ≤ C * (n : ℝ) ^ ε := by
      apply (div_le_iff₀ hlog2).2
      calc
        Real.log (n : ℝ) ≤ (n : ℝ) ^ ε / ε := hlogpow
        _ = C * (n : ℝ) ^ ε * Real.log 2 := by
          have hCeq : C * Real.log 2 = 1 / ε := by
            dsimp [C]
            field_simp [ne_of_gt hε, ne_of_gt hlog2]
          calc
            (n : ℝ) ^ ε / ε = (n : ℝ) ^ ε * (1 / ε) := by ring
            _ = (n : ℝ) ^ ε * (C * Real.log 2) := by rw [hCeq]
            _ = C * (n : ℝ) ^ ε * Real.log 2 := by ring
    calc
      (Nat.log 2 n : ℝ) + 1 ≤ C * (n : ℝ) ^ ε + 1 := by linarith [hlognat.trans hdiv]
      _ ≤ C * (n : ℝ) ^ ε + (n : ℝ) ^ ε := by linarith [hpowone]
      _ = (C + 1) * (n : ℝ) ^ ε := by ring
  have hpowSq : ((n : ℝ) ^ ε) ^ 2 = (n : ℝ) ^ (ζ / 4) := by
    rw [pow_two, ← Real.rpow_add (by positivity : 0 < (n : ℝ))]
    congr 1
    dsimp [ε]
    ring
  have hquad : 2 * ((Nat.log 2 n : ℝ) + 1) ^ 2 ≤
      2 * (C + 1) ^ 2 * (n : ℝ) ^ (ζ / 4) := by
    have hsquare := mul_le_mul_of_nonneg hL hL (by positivity) (by positivity)
    nlinarith [hpowSq]
  have hgap' : 16 * (C + 1) ^ 2 * (n : ℝ) ^ (ζ / 4) ≤ (n : ℝ) ^ ζ := by
    simpa [mul_assoc, mul_left_comm, mul_comm] using hgap
  calc
    2 * ((Nat.log 2 n : ℝ) + 1) ^ 2 ≤
        2 * (C + 1) ^ 2 * (n : ℝ) ^ (ζ / 4) := hquad
    _ ≤ (n : ℝ) ^ ζ / 8 := by nlinarith [hgap']

end HypercubeRamsey.Lane_q_s10_d3
