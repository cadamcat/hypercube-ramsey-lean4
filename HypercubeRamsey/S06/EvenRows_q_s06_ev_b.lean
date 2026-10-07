import HypercubeRamsey.S06.EvenRows_q_s06_even

namespace HypercubeRamsey.S06.Lane_q_s06_ev_b

open Classical
open Filter
open scoped BigOperators

/-- Normalize a nonnegative row after restricting it to a set of mass at least `19/100`.
The cap loses at most the reciprocal of that retained mass. -/
theorem normalized_restriction_bounds {α : Type*} [Fintype α]
    (f : α → ℝ) (A : α → Prop) (B : ℝ)
    (hf : ∀ a, 0 ≤ f a)
    (hmass : 19 / 100 ≤ ∑ a, if A a then f a else 0)
    (hcap : ∀ a, A a → f a ≤ B) :
    (∀ a, 0 ≤ (if A a then f a else 0) / (∑ a, if A a then f a else 0)) ∧
    (∑ a, (if A a then f a else 0) / (∑ a, if A a then f a else 0) = 1) ∧
    (∀ a, (if A a then f a else 0) / (∑ a, if A a then f a else 0) ≤ (100 / 19) * B) := by
  let m : ℝ := ∑ a, if A a then f a else 0
  have hm : 0 < m := by
    dsimp [m]
    linarith
  have hnonneg : ∀ a, 0 ≤ if A a then f a else 0 := by
    intro a
    split_ifs <;> simp [hf a]
  have hA : ∃ a, A a := by
    by_contra hnone
    push_neg at hnone
    have hzero : m = 0 := by
      dsimp [m]
      apply Finset.sum_eq_zero
      intro a _
      simp [hnone a]
    linarith
  have hB : 0 ≤ B := by
    obtain ⟨a, ha⟩ := hA
    linarith [hcap a ha, hf a]
  refine ⟨?_, ?_, ?_⟩
  · intro a
    exact div_nonneg (hnonneg a) hm.le
  · change (∑ a, (if A a then f a else 0) / m) = 1
    rw [← Finset.sum_div]
    exact div_self hm.ne'
  · intro a
    by_cases ha : A a
    · have hB : 0 ≤ B := by
        have := hcap a ha
        linarith [hf a]
      have hden : B / m ≤ B / (19 / 100 : ℝ) := by
        rw [div_le_div_iff₀ hm (by norm_num)]
        nlinarith [hB, hmass]
      have hbound : f a / m ≤ (100 / 19 : ℝ) * B := by
        calc
          f a / m ≤ B / m := div_le_div_of_nonneg_right (hcap a ha) hm.le
          _ ≤ B / (19 / 100 : ℝ) := hden
          _ = (100 / 19 : ℝ) * B := by norm_num; ring
      simpa [m, ha] using hbound
    · simp [ha]
      positivity

/-- Exponential moment of the number of coordinates in a set under a uniform product law. -/
theorem uniform_pi_hit_moment_le {k N : ℕ} (U : FinProb (Fin N))
    (hU : ∀ x, U.w x = (N : ℝ)⁻¹) (S : Finset (Fin N)) (theta : ℝ)
    (htheta : 1 ≤ theta) :
    (FinProb.pi (fun _ : Fin k => U)).expect
        (fun x => theta ^ (Finset.univ.filter (fun i : Fin k => x i ∈ S)).card) ≤
      (1 + theta * ((S.card : ℝ) / N)) ^ k := by
  classical
  let P : FinProb (Fin k → Fin N) := FinProb.pi fun _ => U
  let g : Fin N → ℝ := fun x => if x ∈ S then theta else 1
  have hpow (x : Fin k → Fin N) :
      theta ^ (Finset.univ.filter (fun i : Fin k => x i ∈ S)).card = ∏ i, g (x i) := by
    calc
      theta ^ (Finset.univ.filter (fun i : Fin k => x i ∈ S)).card =
          ∏ i ∈ Finset.univ.filter (fun i : Fin k => x i ∈ S), theta := by simp
      _ = ∏ i, if x i ∈ S then theta else 1 := by
        rw [← Finset.prod_filter]
      _ = ∏ i, g (x i) := by simp [g]
  have hfactor :
      P.expect (fun x => theta ^ (Finset.univ.filter (fun i : Fin k => x i ∈ S)).card) =
        ∏ i : Fin k, U.expect g := by
    unfold FinProb.expect
    change (∑ x : (Fin k → Fin N), (∏ i, U.w (x i)) *
      theta ^ (Finset.univ.filter (fun i : Fin k => x i ∈ S)).card) = _
    calc
      _ = ∑ ω : (Fin k → Fin N), ∏ i : Fin k, U.w (ω i) * g (ω i) := by
        apply Finset.sum_congr rfl
        intro ω hω
        calc
          (∏ i : Fin k, U.w (ω i)) * theta ^ (Finset.univ.filter
              (fun i : Fin k => ω i ∈ S)).card =
              (∏ i : Fin k, U.w (ω i)) * ∏ i : Fin k, g (ω i) := by rw [hpow ω]
          _ = ∏ i : Fin k, U.w (ω i) * g (ω i) := by rw [← Finset.prod_mul_distrib]
      _ = ∏ i : Fin k, ∑ y : Fin N, U.w y * g y := by
        let f : Fin k → Fin N → ℝ := fun _ y => U.w y * g y
        change (∑ ω : (∀ i : Fin k, Fin N), ∏ i, f i (ω i)) = ∏ i, ∑ y, f i y
        rw [← Fintype.prod_sum]
      _ = ∏ i : Fin k, U.expect g := by rfl
  have hmass : U.pr (fun x => x ∈ S) = (S.card : ℝ) / N := by
    calc
      U.pr (fun x => x ∈ S) = ∑ x ∈ S, U.w x := by
        unfold FinProb.pr
        letI : DecidablePred (fun x : Fin N => x ∈ S) :=
          fun x => Classical.propDecidable (x ∈ S)
        change (∑ x : Fin N, if x ∈ S then U.w x else 0) = _
        exact Finset.sum_ite_mem_eq S U.w
      _ = ∑ _x ∈ S, (N : ℝ)⁻¹ := by
        apply Finset.sum_congr rfl
        intro x hx
        exact hU x
      _ = (S.card : ℝ) / N := by simp [div_eq_mul_inv]
  have hsingle : U.expect g ≤ 1 + theta * ((S.card : ℝ) / N) := by
    unfold FinProb.expect
    calc
      (∑ x, U.w x * g x) ≤ ∑ x, (U.w x + if x ∈ S then theta * U.w x else 0) := by
        apply Finset.sum_le_sum
        intro x hx
        by_cases hxS : x ∈ S
        · simp [g, hxS]
          have : 0 ≤ U.w x := U.nonneg x
          nlinarith [htheta]
        · simp [g, hxS]
      _ = 1 + theta * (U.pr (fun x => x ∈ S)) := by
        rw [Finset.sum_add_distrib, U.sum_eq_one]
        simp [FinProb.pr, Finset.mul_sum]
      _ = 1 + theta * ((S.card : ℝ) / N) := by rw [hmass]
  change P.expect (fun x => theta ^ (Finset.univ.filter (fun i : Fin k => x i ∈ S)).card) ≤ _
  rw [hfactor]
  calc
    (∏ i : Fin k, U.expect g) ≤ ∏ _i : Fin k, (1 + theta * ((S.card : ℝ) / N)) := by
      apply Finset.prod_le_prod₀
      · intro i hi
        unfold FinProb.expect
        exact Finset.sum_nonneg fun x _ => mul_nonneg (U.nonneg x) (by
          dsimp [g]
          split_ifs <;> linarith [htheta])
      · intro i hi
        exact hsingle
    _ = (1 + theta * ((S.card : ℝ) / N)) ^ k := by simp

/-- An atomwise density bound against a uniform product law transfers to a large-hit tail bound. -/
theorem hit_tail_of_uniform_product_density {k N : ℕ} (U : FinProb (Fin N))
    (hU : ∀ x, U.w x = (N : ℝ)⁻¹) (S : Finset (Fin N)) (theta D : ℝ) (r : ℕ)
    (htheta : 1 ≤ theta) (hD : 0 ≤ D) (Q : FinProb (Fin k → Fin N))
    (hQ : ∀ x, Q.w x ≤ D * (FinProb.pi (fun _ : Fin k => U)).w x) :
    Q.pr (fun x => r ≤ (Finset.univ.filter (fun i : Fin k => x i ∈ S)).card) ≤
      D * ((1 + theta * ((S.card : ℝ) / N) ) ^ k) / theta ^ r := by
  classical
  let P : FinProb (Fin k → Fin N) := FinProb.pi fun _ => U
  let count : (Fin k → Fin N) → ℕ :=
    fun x => (Finset.univ.filter (fun i : Fin k => x i ∈ S)).card
  have htheta0 : 0 < theta := lt_of_lt_of_le (by norm_num) htheta
  have hden : 0 < theta ^ r := pow_pos htheta0 r
  have hdom : Q.pr (fun x => r ≤ count x) ≤ D * P.pr (fun x => r ≤ count x) := by
    letI : DecidablePred (fun x : Fin k → Fin N => r ≤ count x) :=
      fun x => Classical.propDecidable (r ≤ count x)
    unfold FinProb.pr
    calc
      (∑ x, if r ≤ count x then Q.w x else 0) ≤
          ∑ x, if r ≤ count x then D * P.w x else 0 := by
        apply Finset.sum_le_sum
        intro x hx
        by_cases he : r ≤ count x
        · simp [he]
          simpa [P] using hQ x
        · simp [he]
      _ = D * P.pr (fun x => r ≤ count x) := by
        calc
          (∑ x, if r ≤ count x then D * P.w x else 0) =
              ∑ x, D * (if r ≤ count x then P.w x else 0) := by
            apply Finset.sum_congr rfl
            intro x hx
            by_cases he : r ≤ count x <;> simp [he]
          _ = D * P.pr (fun x => r ≤ count x) := by
            rw [FinProb.pr, ← Finset.mul_sum]
  have hmark : P.pr (fun x => r ≤ count x) ≤
      P.expect (fun x => theta ^ count x) / theta ^ r := by
    letI : DecidablePred (fun x : Fin k → Fin N => r ≤ count x) :=
      fun x => Classical.propDecidable (r ≤ count x)
    unfold FinProb.pr FinProb.expect
    calc
      (∑ x, if r ≤ count x then P.w x else 0) ≤
          ∑ x, (P.w x * theta ^ count x) / theta ^ r := by
        apply Finset.sum_le_sum
        intro x hx
        by_cases he : r ≤ count x
        · simp only [if_pos he]
          have hpow : theta ^ r ≤ theta ^ count x := by
            have htail : 1 ≤ theta ^ (count x - r) := one_le_pow₀ htheta
            calc
              theta ^ r = theta ^ r * 1 := by ring
              _ ≤ theta ^ r * theta ^ (count x - r) :=
                mul_le_mul_of_nonneg_left htail (pow_nonneg (le_of_lt htheta0) r)
              _ = theta ^ count x := by rw [← pow_add]; congr 1; omega
          have hratio : 1 ≤ theta ^ count x / theta ^ r :=
            (le_div_iff₀ hden).2 (by simpa using hpow)
          calc
            P.w x ≤ P.w x * (theta ^ count x / theta ^ r) :=
              by simpa using mul_le_mul_of_nonneg_left hratio (P.nonneg x)
            _ = (P.w x * theta ^ count x) / theta ^ r := by ring
        · simp only [if_neg he]
          exact div_nonneg
            (mul_nonneg (P.nonneg x) (pow_nonneg (le_of_lt htheta0) _)) hden.le
      _ = P.expect (fun x => theta ^ count x) / theta ^ r := by
        rw [FinProb.expect, ← Finset.sum_div]
  calc
    Q.pr (fun x => r ≤ count x) ≤ D * P.pr (fun x => r ≤ count x) := hdom
    _ ≤ D * (P.expect (fun x => theta ^ count x) / theta ^ r) :=
      mul_le_mul_of_nonneg_left hmark hD
    _ ≤ D * ((1 + theta * ((S.card : ℝ) / N)) ^ k / theta ^ r) := by
      apply mul_le_mul_of_nonneg_left _ hD
      exact div_le_div_of_nonneg_right
        (uniform_pi_hit_moment_le U hU S theta htheta) hden.le
    _ = D * ((1 + theta * ((S.card : ℝ) / N)) ^ k) / theta ^ r := by ring

/-- Atom bound for a tagged tuple whose label coordinates are sampled independently. -/
theorem bind_pi_atom_bound {ι : Type*} [Fintype ι] {k N : ℕ}
    (T : FinProb ι) (L : ι → FinProb (Fin N)) (C : ℝ)
    (hL : ∀ i x, (L i).w x ≤ C / N) :
    ∀ i (x : Fin k → Fin N),
      (FinProb.bind T (fun i => FinProb.pi fun _ : Fin k => L i)).w (i, x) ≤
        T.w i * (C / N) ^ k := by
  classical
  intro i x
  change T.w i * (∏ j : Fin k, (L i).w (x j)) ≤ T.w i * (C / N) ^ k
  apply mul_le_mul_of_nonneg_left _ (T.nonneg i)
  calc
    (∏ j : Fin k, (L i).w (x j)) ≤ ∏ _j : Fin k, C / N := by
      apply Finset.prod_le_prod₀
      · intro j hj
        exact (L i).nonneg (x j)
      · intro j hj
        exact hL i (x j)
    _ = (C / N) ^ k := by rw [div_pow]; simp

/-- A sublinear width exponent is absorbed into a small linear exponential. -/
theorem eventually_width_exp_bound {γ : ℝ} (hγ : γ < 1) :
    ∃ n₀ : ℕ, ∀ n ≥ n₀,
      400 * Real.exp ((n : ℝ) ^ γ) ≤ Real.exp ((4 / 100 : ℝ) * n) := by
  have hpow : Tendsto (fun n : ℕ => (n : ℝ) ^ γ / (n : ℝ)) atTop (nhds 0) := by
    have hneg : Tendsto (fun n : ℕ => (n : ℝ) ^ (-(1 - γ))) atTop (nhds 0) :=
      (tendsto_rpow_neg_atTop (sub_pos.mpr hγ)).comp tendsto_natCast_atTop_atTop
    refine Tendsto.congr' ?_ hneg
    filter_upwards [eventually_gt_atTop 0] with n hn
    have hnR : (0 : ℝ) < n := by exact_mod_cast hn
    calc
      (n : ℝ) ^ γ / n = (n : ℝ) ^ (γ - 1) := (Real.rpow_sub_one hnR.ne' γ).symm
      _ = (n : ℝ) ^ (-(1 - γ)) := by congr 1 <;> ring
  have hconst : Tendsto (fun n : ℕ => Real.log 400 / (n : ℝ)) atTop (nhds 0) :=
    tendsto_const_div_atTop_nhds_zero_nat (Real.log 400)
  have hpEvent : ∀ᶠ n : ℕ in atTop, (n : ℝ) ^ γ / n < 1 / 100 :=
    hpow.eventually (Iio_mem_nhds (by norm_num))
  have hcEvent : ∀ᶠ n : ℕ in atTop, Real.log 400 / (n : ℝ) < 1 / 100 :=
    hconst.eventually (Iio_mem_nhds (by norm_num))
  obtain ⟨np, hp⟩ := Filter.eventually_atTop.mp hpEvent
  obtain ⟨nc, hc⟩ := Filter.eventually_atTop.mp hcEvent
  refine ⟨max (max np nc) 1, ?_⟩
  intro n hn
  have hnp : np ≤ n := le_trans (le_trans (le_max_left np nc) (le_max_left (max np nc) 1)) hn
  have hnc : nc ≤ n := le_trans (le_trans (le_max_right np nc) (le_max_left (max np nc) 1)) hn
  have hn1Nat : 1 ≤ n := le_trans (le_max_right (max np nc) 1) hn
  have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast hn1Nat
  have hnpos : (0 : ℝ) < n := lt_of_lt_of_le (by norm_num) hn1
  have hp' : (n : ℝ) ^ γ / n < 1 / 100 := hp n hnp
  have hc' : Real.log 400 / n < 1 / 100 := hc n hnc
  have hp'' : (n : ℝ) ^ γ < (1 / 100 : ℝ) * n := (div_lt_iff₀ hnpos).mp hp'
  have hc'' : Real.log 400 < (1 / 100 : ℝ) * n := (div_lt_iff₀ hnpos).mp hc'
  have hexp : Real.log 400 + (n : ℝ) ^ γ ≤ (4 / 100 : ℝ) * n := by linarith
  calc
    400 * Real.exp ((n : ℝ) ^ γ) = Real.exp (Real.log 400 + (n : ℝ) ^ γ) := by
      rw [Real.exp_add, Real.exp_log (by norm_num)]
    _ ≤ Real.exp ((4 / 100 : ℝ) * n) := Real.exp_le_exp.mpr hexp

end HypercubeRamsey.S06.Lane_q_s06_ev_b
