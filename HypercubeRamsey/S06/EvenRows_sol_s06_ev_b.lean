import HypercubeRamsey.S06.EvenRows_q_s06_ev_b

namespace HypercubeRamsey.S06.Lane_sol_s06_ev_b
open Classical Filter OAI.HypercubeRamsey
open scoped BigOperators

noncomputable section

theorem pr_mem_set {α : Type*} [Fintype α] [DecidableEq α] (P : FinProb α) (S : Finset α) :
    P.pr (fun a => a ∈ S) = ∑ a ∈ S, P.w a := by
  classical
  unfold FinProb.pr
  calc
    _ = ∑ a, if a ∈ S then P.w a else 0 := by
      apply Finset.sum_congr rfl
      intro a ha
      by_cases h : a ∈ S <;> simp [h]
    _ = _ := Finset.sum_ite_mem_eq S P.w

def empirical {k N : ℕ} (x : Fin k → Fin N) (a : Fin N) : ℝ :=
  ((Finset.univ.filter fun r => x r = a).card : ℝ) / k

theorem empirical_sum {k N : ℕ} (hk : 0 < k) (x : Fin k → Fin N) :
    ∑ a, empirical x a = 1 := by
  have hcount : ∑ a : Fin N, ((Finset.univ.filter fun r => x r = a).card : ℝ) = k := by
    simp only [Finset.card_filter, Nat.cast_sum, Nat.cast_ite, Nat.cast_one, Nat.cast_zero]
    rw [Finset.sum_comm]
    simp
  simp only [empirical, ← Finset.sum_div, hcount]
  exact div_self (by exact_mod_cast hk.ne')

theorem empirical_set {k N : ℕ} (x : Fin k → Fin N) (S : Finset (Fin N)) :
    ∑ a ∈ S, empirical x a =
      ((Finset.univ.filter fun r => x r ∈ S).card : ℝ) / k := by
  simp only [empirical, ← Finset.sum_div]
  congr 1
  simp only [Finset.card_filter, Nat.cast_sum, Nat.cast_ite, Nat.cast_one, Nat.cast_zero]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro r hr
  simp

theorem empirical_nonneg {k N : ℕ} (x : Fin k → Fin N) (a : Fin N) :
    0 ≤ empirical x a := by unfold empirical; positivity

theorem map_snd_empirical {ι : Type*} [Fintype ι] {k N : ℕ}
    (P : FinProb (ι × (Fin k → Fin N))) (a : Fin N) :
    ∑ x, (P.map Prod.snd).w x * empirical x a = ∑ z, P.w z * empirical z.2 a := by
  change (∑ x, (∑ z, if z.2 = x then P.w z else 0) * empirical x a) = _
  simp_rw [Finset.sum_mul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro z hz
  simp [ite_mul]

theorem light_mass {k n N : ℕ} (hk : 0 < k) (hn : 10000 ≤ n)
    (U : FinProb (Fin N)) (hU : ∀ a, U.w a = (N : ℝ)⁻¹)
    (Q : FinProb (Fin k → Fin N))
    (hQ : ∀ x, Q.w x ≤ Real.exp ((4 / 10 : ℝ) * k * n) *
      (FinProb.pi fun _ : Fin k => U).w x) :
    let f := fun a => ∑ x, Q.w x * empirical x a
    let S := Finset.univ.filter fun a => Real.exp ((55 / 100 : ℝ) * n) < (N : ℝ) * f a
    (19 / 100 : ℝ) ≤ ∑ a ∈ Finset.univ.filter (fun a => a ∉ S), f a := by
  intro f S
  have hkR : (0 : ℝ) < k := by exact_mod_cast hk
  have hnR : (10000 : ℝ) ≤ n := by exact_mod_cast hn
  have hN : (0 : ℝ) < N := by
    have : (N : ℝ) ≠ 0 := by
      intro h
      have hzero : ∑ a, U.w a = 0 := by simp [hU, h]
      linarith [U.sum_eq_one]
    exact lt_of_le_of_ne (Nat.cast_nonneg _) (Ne.symm this)
  have hf : ∀ a, 0 ≤ f a := fun a =>
    Finset.sum_nonneg fun x _ => mul_nonneg (Q.nonneg x) (empirical_nonneg x a)
  have hsum : ∑ a, f a = 1 := by
    dsimp [f]
    rw [Finset.sum_comm]
    simp_rw [← Finset.mul_sum, empirical_sum hk, mul_one]
    exact Q.sum_eq_one
  have hSsum : ∑ a ∈ S, f a ≤ 1 := by
    rw [← hsum]
    exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _) (fun a _ _ => hf a)
  let theta := Real.exp ((55 / 100 : ℝ) * n)
  have htheta : 1 ≤ theta := Real.one_le_exp_iff.mpr (by positivity)
  have hthetaPos : 0 < theta := Real.exp_pos _
  have hsmall : theta * ((S.card : ℝ) / N) ≤ 1 := by
    have hpt : ∀ a ∈ S, theta ≤ (N : ℝ) * f a := by
      intro a ha
      exact (Finset.mem_filter.mp ha).2.le
    have h : (S.card : ℝ) * theta ≤ (N : ℝ) * (∑ a ∈ S, f a) := by
      calc
        (S.card : ℝ) * theta = ∑ _a ∈ S, theta := by simp
        _ ≤ ∑ a ∈ S, (N : ℝ) * f a := Finset.sum_le_sum hpt
        _ = (N : ℝ) * (∑ a ∈ S, f a) := by rw [Finset.mul_sum]
    rw [← mul_div_assoc]
    apply (div_le_iff₀ hN).mpr
    calc
      theta * S.card ≤ (N : ℝ) * (∑ a ∈ S, f a) := by nlinarith [h]
      _ ≤ (N : ℝ) * 1 := mul_le_mul_of_nonneg_left hSsum hN.le
      _ = 1 * (N : ℝ) := by ring
  let r : ℕ := 4 * k / 5 + 1
  have hr : (4 / 5 : ℝ) * k ≤ r := by
    have hdiv := Nat.mod_add_div (4 * k) 5
    have hmod := Nat.mod_lt (4 * k) (by omega : 0 < 5)
    dsimp [r]
    push_cast
    have hdivR : ((4 * k % 5 : ℕ) : ℝ) + 5 * ((4 * k / 5 : ℕ) : ℝ) = 4 * k := by
      exact_mod_cast hdiv
    have hmodR : ((4 * k % 5 : ℕ) : ℝ) < 5 := by exact_mod_cast hmod
    linarith
  let count := fun x : Fin k → Fin N => (Finset.univ.filter fun i => x i ∈ S).card
  have htail : Q.pr (fun x => r ≤ count x) ≤ 1 / 100 := by
    have h := Lane_q_s06_ev_b.hit_tail_of_uniform_product_density U hU S theta
      (Real.exp ((4 / 10 : ℝ) * k * n)) r htheta (Real.exp_pos _).le Q hQ
    have hnum : (1 + theta * ((S.card : ℝ) / N)) ^ k ≤ (2 : ℝ) ^ k :=
      pow_le_pow_left₀ (by positivity) (by linarith) k
    have hden : Real.exp ((44 / 100 : ℝ) * k * n) ≤ theta ^ r := by
      rw [show theta ^ r = Real.exp (((55 / 100 : ℝ) * n) * r) by
        dsimp [theta]; rw [← Real.exp_nat_mul]; congr 1; ring]
      apply Real.exp_le_exp.mpr
      nlinarith
    have h2 : (2 : ℝ) ^ k ≤ Real.exp ((k : ℝ)) := by
      calc
        (2 : ℝ) ^ k ≤ (Real.exp 1) ^ k := pow_le_pow_left₀ (by norm_num) (by
          have := Real.add_one_le_exp (1 : ℝ)
          norm_num at this ⊢
          exact this) k
        _ = Real.exp (k : ℝ) := by rw [← Real.exp_nat_mul]; simp
    have hdenPos := Real.exp_pos ((44 / 100 : ℝ) * k * n)
    calc
      Q.pr (fun x => r ≤ count x) ≤
          Real.exp ((4 / 10 : ℝ) * k * n) *
            (1 + theta * ((S.card : ℝ) / N)) ^ k / theta ^ r := h
      _ ≤ Real.exp ((4 / 10 : ℝ) * k * n) * Real.exp (k : ℝ) /
          Real.exp ((44 / 100 : ℝ) * k * n) := by
        exact div_le_div₀ (by positivity)
          (mul_le_mul_of_nonneg_left (hnum.trans h2) (Real.exp_pos _).le) hdenPos hden
      _ = Real.exp ((1 - (4 / 100 : ℝ) * n) * k) := by
        rw [← Real.exp_add, ← Real.exp_sub]
        congr 1
        ring
      _ ≤ Real.exp (-300) := by
        apply Real.exp_le_exp.mpr
        have hk1 : (1 : ℝ) ≤ k := by exact_mod_cast hk
        nlinarith
      _ ≤ 1 / 100 := by
        rw [Real.exp_neg, inv_eq_one_div]
        apply one_div_le_one_div_of_le (by norm_num)
        have := Real.add_one_le_exp (300 : ℝ)
        linarith
  have hcountBound (x : Fin k → Fin N) :
      (count x : ℝ) / k ≤ (4 / 5 : ℝ) + if r ≤ count x then 1 else 0 := by
    by_cases hx : r ≤ count x
    · rw [if_pos hx]
      have hc : count x ≤ k := (Finset.card_filter_le _ _).trans (by simp)
      have hcR : (count x : ℝ) ≤ k := by exact_mod_cast hc
      rw [div_le_iff₀ hkR]
      nlinarith
    · rw [if_neg hx, add_zero, div_le_iff₀ hkR]
      have hc : 5 * count x ≤ 4 * k := by dsimp [r] at hx; omega
      have hcR : 5 * (count x : ℝ) ≤ 4 * k := by exact_mod_cast hc
      linarith
  have hheavy : ∑ a ∈ S, f a ≤ 81 / 100 := by
    calc
      ∑ a ∈ S, f a = ∑ x, Q.w x * ((count x : ℝ) / k) := by
        dsimp [f]
        rw [Finset.sum_comm]
        simp_rw [← Finset.mul_sum, empirical_set]
        rfl
      _ ≤ ∑ x, Q.w x * ((4 / 5 : ℝ) + if r ≤ count x then 1 else 0) :=
        Finset.sum_le_sum fun x _ => mul_le_mul_of_nonneg_left (hcountBound x) (Q.nonneg x)
      _ = 4 / 5 + Q.pr (fun x => r ≤ count x) := by
        simp only [mul_add, Finset.sum_add_distrib, ← Finset.sum_mul, Q.sum_eq_one, one_mul]
        congr 1
        unfold FinProb.pr
        apply Finset.sum_congr rfl
        intro x hx
        split_ifs <;> simp
      _ ≤ 81 / 100 := by linarith
  have hpartition : (∑ a ∈ Finset.univ.filter (fun a => a ∉ S), f a) + ∑ a ∈ S, f a = 1 := by
    have h := Finset.sum_filter_add_sum_filter_not (s := Finset.univ) (p := fun a => a ∉ S) (f := f)
    simpa [hsum] using h
  linarith

end
end HypercubeRamsey.S06.Lane_sol_s06_ev_b
