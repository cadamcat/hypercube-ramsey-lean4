import HypercubeRamsey.S14.Construction_q_s14_post

namespace HypercubeRamsey.Lane_sol_s14_post
open scoped BigOperators

/-- Jensen's inequality for the exponential, using its tangent at the mean. -/
theorem exp_mean_le {Ω : Type*} [Fintype Ω] (P : FinLaw Ω) (f : Ω → ℝ) :
    Real.exp (P.E f) ≤ P.E (fun w => Real.exp (f w)) := by
  have hpoint (w : Ω) :
      Real.exp (P.E f) * (1 + (f w - P.E f)) ≤ Real.exp (f w) := by
    calc
      _ ≤ Real.exp (P.E f) * Real.exp (f w - P.E f) :=
        mul_le_mul_of_nonneg_left (by linarith only [Real.add_one_le_exp (f w - P.E f)]) (Real.exp_nonneg _)
      _ = _ := by rw [← Real.exp_add]; congr 1 <;> ring
  calc
    _ = Real.exp (P.E f) * (∑ w, P.w w * (1 + (f w - P.E f))) := by
      simp only [mul_add, mul_sub, Finset.sum_add_distrib, Finset.sum_sub_distrib,
        ← Finset.sum_mul, P.sum_one, one_mul, mul_one]
      unfold FinLaw.E
      ring
    _ = ∑ w, P.w w * (Real.exp (P.E f) * (1 + (f w - P.E f))) := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro w hw
      ring
    _ ≤ _ := Finset.sum_le_sum fun w _ =>
      mul_le_mul_of_nonneg_left (hpoint w) (P.nonneg w)

/-- A joint atom cap forces a positive mass of the average coordinate law
below the heavy-label threshold. The exponential moment avoids rounding a
number of coordinates to an integer. -/
theorem light_mass {k N h : ℕ} (hk : 0 < k) (hN : 0 < N)
    (a : ℝ) (ha : 0 < a) (has : a ≤ 1 / 10) (hah : 100 ≤ a * h)
    (P : FinLaw (Fin k → Fin N))
    (hcap : ∀ w, P.w w ≤
      Real.exp ((Real.log 2 - 0.04 * a) * k * h) * ((N : ℝ)⁻¹) ^ k) :
    let f := fun x => ∑ w, P.w w * ((∑ r, if w r = x then (1 : ℝ) else 0) / k)
    a / 200 ≤ ∑ x ∈ Finset.univ.filter
      (fun x => (N : ℝ) * f x ≤ (2 : ℝ) ^ h * Real.exp (-0.02 * a * h)), f x := by
  classical
  intro f
  have hkR : (0 : ℝ) < k := by exact_mod_cast hk
  have hNR : (0 : ℝ) < N := by exact_mod_cast hN
  have hhR : (0 : ℝ) < h := by nlinarith [(Nat.cast_nonneg h : (0 : ℝ) ≤ h)]
  have hloglo : (1 / 2 : ℝ) ≤ Real.log 2 := by
    have hl := Real.one_sub_inv_le_log_of_pos (by norm_num : (0 : ℝ) < 2)
    norm_num at hl ⊢
    linarith
  have hloghi : Real.log 2 ≤ 1 := by
    have hl := Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 2)
    norm_num at hl
    exact hl
  let s := (Real.log 2 - 0.02 * a) * h
  let theta := Real.exp s
  let S := Finset.univ.filter fun x => theta < (N : ℝ) * f x
  have hs : 0 < s := by dsimp [s]; nlinarith
  have ht : 0 < theta := Real.exp_pos _
  have hthetaEq : theta = (2 : ℝ) ^ h * Real.exp (-0.02 * a * h) := by
    dsimp [theta, s]
    rw [show (Real.log 2 - 0.02 * a) * (h : ℝ) =
      (h : ℝ) * Real.log 2 + -0.02 * a * h by ring, Real.exp_add]
    rw [Real.exp_nat_mul, Real.exp_log (by norm_num : (0 : ℝ) < 2)]
  have hf0 (x : Fin N) : 0 ≤ f x := by
    apply Finset.sum_nonneg
    intro w hw
    apply mul_nonneg (P.nonneg w)
    apply div_nonneg _ hkR.le
    exact Finset.sum_nonneg fun r _ => by split_ifs <;> positivity
  have hfSum : ∑ x, f x = 1 := by
    dsimp [f]
    rw [Finset.sum_comm]
    simp_rw [← Finset.mul_sum, ← Finset.sum_div]
    have hcoord (w : Fin k → Fin N) :
        (∑ x, ∑ r, if w r = x then (1 : ℝ) else 0) = k := by
      rw [Finset.sum_comm]
      simp [eq_comm]
    simp_rw [hcoord, div_self hkR.ne', mul_one]
    exact P.sum_one
  have hSSum : ∑ x ∈ S, f x ≤ 1 := by
    rw [← hfSum]
    exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _)
      (fun x _ _ => hf0 x)
  have hsmall : theta * (S.card : ℝ) / N ≤ 1 := by
    apply (div_le_iff₀ hNR).2
    calc
      theta * S.card = ∑ _x ∈ S, theta := by simp [mul_comm]
      _ ≤ ∑ x ∈ S, (N : ℝ) * f x := by
        apply Finset.sum_le_sum
        intro x hx
        exact (Finset.mem_filter.mp hx).2.le
      _ = (N : ℝ) * ∑ x ∈ S, f x := by rw [Finset.mul_sum]
      _ ≤ 1 * (N : ℝ) := by nlinarith
  let count := fun w : Fin k → Fin N =>
    (Finset.univ.filter fun r => w r ∈ S).card
  have hmoment : P.E (fun w => Real.exp (s * count w)) ≤
      Real.exp ((Real.log 2 - 0.04 * a) * k * h) * (2 : ℝ) ^ k := by
    let g := fun x : Fin N => if x ∈ S then theta else 1
    have hprod (w : Fin k → Fin N) :
        Real.exp (s * count w) = ∏ r, g (w r) := by
      rw [mul_comm s, Real.exp_nat_mul]
      change theta ^ (Finset.univ.filter fun r => w r ∈ S).card = _
      rw [← Finset.prod_const, Finset.prod_filter]
    have hsingle : (∑ x : Fin N, (N : ℝ)⁻¹ * g x) ≤ 2 := by
      calc
        _ ≤ ∑ x : Fin N, ((N : ℝ)⁻¹ +
            if x ∈ S then (N : ℝ)⁻¹ * theta else 0) := by
          apply Finset.sum_le_sum
          intro x hx
          by_cases hxS : x ∈ S <;> simp [g, hxS] <;> positivity
        _ = 1 + theta * (S.card : ℝ) / N := by
          rw [Finset.sum_add_distrib]
          simp [Finset.sum_ite_mem, div_eq_mul_inv, hNR.ne']
          ring
        _ ≤ 2 := by linarith
    calc
      _ ≤ ∑ w : Fin k → Fin N,
          (Real.exp ((Real.log 2 - 0.04 * a) * k * h) * ((N : ℝ)⁻¹) ^ k) *
            Real.exp (s * count w) := by
        exact Finset.sum_le_sum fun w _ =>
          mul_le_mul_of_nonneg_right (hcap w) (Real.exp_nonneg _)
      _ = Real.exp ((Real.log 2 - 0.04 * a) * k * h) *
          ∑ w : Fin k → Fin N, ∏ r, (N : ℝ)⁻¹ * g (w r) := by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro w hw
        rw [hprod, Finset.prod_mul_distrib]
        simp
        ring
      _ = Real.exp ((Real.log 2 - 0.04 * a) * k * h) *
          (∑ x : Fin N, (N : ℝ)⁻¹ * g x) ^ k := by
        congr 1
        simpa using (Fintype.prod_sum
          (fun (_r : Fin k) (x : Fin N) => (N : ℝ)⁻¹ * g x)).symm
      _ ≤ _ := by
        apply mul_le_mul_of_nonneg_left _ (Real.exp_nonneg _)
        apply pow_le_pow_left₀ _ hsingle
        exact Finset.sum_nonneg fun x _ => mul_nonneg (by positivity)
          (by dsimp [g]; split_ifs <;> positivity)
  have hmean : s * P.E (fun w => (count w : ℝ)) ≤
      (Real.log 2 - 0.04 * a) * k * h + k * Real.log 2 := by
    apply Real.exp_le_exp.mp
    calc
      _ = Real.exp (P.E (fun w => s * count w)) := by
        congr 1
        simp [FinLaw.E, Finset.mul_sum, mul_left_comm]
      _ ≤ P.E (fun w => Real.exp (s * count w)) := exp_mean_le P _
      _ ≤ Real.exp ((Real.log 2 - 0.04 * a) * k * h) * (2 : ℝ) ^ k := hmoment
      _ = _ := by
        rw [Real.exp_add, Real.exp_nat_mul, Real.exp_log (by norm_num : (0 : ℝ) < 2)]
  have hheavy : ∑ x ∈ S, f x = P.E (fun w => (count w : ℝ)) / k := by
    dsimp [f]
    rw [Finset.sum_comm]
    simp_rw [← Finset.mul_sum, ← Finset.sum_div, ← mul_div_assoc]
    rw [← Finset.sum_div]
    congr 1
    apply Finset.sum_congr rfl
    intro w hw
    congr 1
    rw [Finset.sum_comm]
    simp only [count, Finset.card_filter, Nat.cast_sum, Nat.cast_ite,
      Nat.cast_one, Nat.cast_zero]
    apply Finset.sum_congr rfl
    intro r hr
    simp [eq_comm]
  have hscaled : s * (∑ x ∈ S, f x) ≤
      (Real.log 2 - 0.04 * a) * h + Real.log 2 := by
    rw [hheavy, ← mul_div_assoc]
    apply (div_le_iff₀ hkR).2
    convert hmean using 1 <;> ring
  have hpartition :
      (∑ x ∈ Finset.univ.filter (fun x => x ∉ S), f x) + ∑ x ∈ S, f x = 1 := by
    simpa [S, hfSum] using Finset.sum_filter_add_sum_filter_not
      (s := Finset.univ) (p := fun x => x ∉ S) (f := f)
  have hlight : a / 200 ≤ ∑ x ∈ Finset.univ.filter (fun x => x ∉ S), f x := by
    have hbound : s ≤ (h : ℝ) := by dsimp [s]; nlinarith
    have hgap : 0.01 * a * h ≤ s *
        (∑ x ∈ Finset.univ.filter (fun x => x ∉ S), f x) := by
      have heq : s * (∑ x ∈ Finset.univ.filter (fun x => x ∉ S), f x) =
          s - s * (∑ x ∈ S, f x) := by
        have he := congrArg (fun z : ℝ => s * z) hpartition
        nlinarith only [he]
      rw [heq]
      dsimp [s] at hscaled ⊢
      nlinarith
    have hlight0 : 0 ≤ ∑ x ∈ Finset.univ.filter (fun x => x ∉ S), f x :=
      Finset.sum_nonneg fun x _ => hf0 x
    have hm := mul_le_mul_of_nonneg_right hbound hlight0
    have hfinal : 0.01 * a ≤ ∑ x ∈ Finset.univ.filter (fun x => x ∉ S), f x := by
      exact le_of_mul_le_mul_right (by nlinarith only [hm, hgap]) hhR
    linarith only [hfinal, ha]
  simpa [S, hthetaEq, not_lt] using hlight

theorem E_mono {Ω : Type*} [Fintype Ω] (P : FinLaw Ω) (f g : Ω → ℝ)
    (hfg : ∀ w, f w ≤ g w) : P.E f ≤ P.E g :=
  Finset.sum_le_sum fun w _ => mul_le_mul_of_nonneg_left (hfg w) (P.nonneg w)

theorem E_le_const {Ω : Type*} [Fintype Ω] (P : FinLaw Ω) (f : Ω → ℝ)
    (b : ℝ) (hf : ∀ w, f w ≤ b) : P.E f ≤ b := by
  calc
    _ ≤ P.E (fun _ => b) := E_mono P f _ hf
    _ = b := by simp [FinLaw.E, ← Finset.sum_mul, P.sum_one]

theorem pi_E_split {ι : Type*} [Fintype ι] [DecidableEq ι]
    {α : ι → Type*} [∀ i, Fintype (α i)] (P : ∀ i, FinLaw (α i))
    (i₀ : ι) (f : (∀ i, α i) → ℝ) :
    (FinLaw.pi P).E f =
      (FinLaw.pi fun i : {j // j ≠ i₀} => P i.1).E (fun rest =>
        (P i₀).E (fun a => f ((Equiv.piSplitAt i₀ α).symm (a, rest)))) := by
  rw [FinLaw.E]
  change (∑ w, (∏ i, (P i).w (w i)) * f w) = _
  rw [Lane_q_s14_post.sum_pi_splitAt (fun i => (P i).w) i₀ f]
  simp_rw [Finset.mul_sum]
  rw [Finset.sum_comm]
  unfold FinLaw.E
  change (∑ rest, ∑ a, (P i₀).w a *
      ((∏ i : {j // j ≠ i₀}, (P i.1).w (rest i)) *
        f ((Equiv.piSplitAt i₀ α).symm (a, rest)))) = _
  apply Finset.sum_congr rfl
  intro rest hr
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro a ha
  dsimp only [FinLaw.pi]
  ring

end HypercubeRamsey.Lane_sol_s14_post
