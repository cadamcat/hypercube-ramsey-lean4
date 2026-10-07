import HypercubeRamsey.S11.Core.OuterMoment_q_s11_outer_sampling
import HypercubeRamsey.Tools.SignedTest
import HypercubeRamsey.Framework.LawLemmas

namespace HypercubeRamsey.S11.Core.sol_s11_outer

open Classical
open scoped BigOperators

/-- The first and second moments of an iid vector sum. -/
theorem iid_second_moment_le {N M t : ℕ} (Q : Law N) (P : Law M)
    (f : Fin N → Fin M → ℝ) (A B : ℝ)
    (hA : ∑ y, P.w y * ∑ x, Q.w x * (f x y)^2 ≤ A)
    (hB : ∑ y, P.w y * (∑ x, Q.w x * f x y)^2 ≤ B) :
    (∑ z : Fin t → Fin N, (∏ i, Q.w (z i)) *
      ∑ y, P.w y * (∑ i, f (z i) y)^2) ≤ (t : ℝ)*A + (t : ℝ)^2*B := by
  classical
  rw [OuterMoment_q_s11_outer.iid_sum_square_expectation]
  calc
    _ ≤ ∑ y, P.w y * ((t : ℝ) * (∑ x, Q.w x * (f x y)^2) +
        (t : ℝ)^2 * (∑ x, Q.w x * f x y)^2) := by
      apply Finset.sum_le_sum
      intro y hy
      apply mul_le_mul_of_nonneg_left _ (P.nonneg y)
      calc
        (∑ i : Fin t, ∑ j : Fin t, if i = j then ∑ x, Q.w x * (f x y)^2
            else (∑ x, Q.w x * f x y)^2) ≤
            ∑ i : Fin t, ∑ j : Fin t,
              ((if i = j then ∑ x, Q.w x * (f x y)^2 else 0) +
                (∑ x, Q.w x * f x y)^2) := by
          apply Finset.sum_le_sum
          intro i hi
          apply Finset.sum_le_sum
          intro j hj
          split_ifs <;> nlinarith [sq_nonneg (∑ x, Q.w x * f x y)]
        _ = _ := by
          simp [Finset.sum_add_distrib, Finset.sum_ite_eq', pow_two]
          ring
    _ = (t : ℝ)*(∑ y, P.w y * ∑ x, Q.w x * (f x y)^2) +
        (t : ℝ)^2 * (∑ y, P.w y * (∑ x, Q.w x * f x y)^2) := by
      simp_rw [mul_add, Finset.sum_add_distrib]
      congr 1 <;> rw [Finset.mul_sum] <;> apply Finset.sum_congr rfl <;>
        intro y hy <;> ring
    _ ≤ _ := add_le_add
      (mul_le_mul_of_nonneg_left hA (Nat.cast_nonneg t))
      (mul_le_mul_of_nonneg_left hB (sq_nonneg _))

/-- A norm bound on average leaves at least half the mass below twice the bound. -/
theorem half_mass_good {Ω : Type*} [Fintype Ω] (P : FinProb Ω)
    (v : Ω → ℝ) (V : ℝ) (hV : 0 < V) (hv : ∀ z, 0 ≤ v z)
    (havg : ∑ z, P.w z * v z ≤ V / 2) :
    (1 / 2 : ℝ) ≤ ∑ z, P.w z * (if v z ≤ V then 1 else 0) := by
  classical
  have hpoint (z : Ω) : V * P.w z * (1 - (if v z ≤ V then (1 : ℝ) else 0)) ≤
      P.w z * v z := by
    by_cases h : v z ≤ V
    · simp [h, mul_nonneg (P.nonneg z) (hv z)]
    · have := le_of_lt (lt_of_not_ge h)
      simp only [if_neg h]
      nlinarith [P.nonneg z, mul_le_mul_of_nonneg_left this (P.nonneg z)]
  have hs := Finset.sum_le_sum (fun z (_ : z ∈ Finset.univ) => hpoint z)
  have hid : (∑ z, V * P.w z * (1 - (if v z ≤ V then (1 : ℝ) else 0))) =
      V * (1 - ∑ z, P.w z * (if v z ≤ V then 1 else 0)) := by
    simp_rw [mul_sub, mul_one, Finset.sum_sub_distrib, mul_assoc,
      ← Finset.mul_sum, P.sum_eq_one]
    ring
  rw [hid] at hs
  nlinarith

/-- Transfer conditioned good tuples to one raw tuple with a large common fiber. -/
theorem common_fiber_tuple {N t : ℕ} (P : Law N) (A : Finset (Fin N))
    (F : Fin N → Finset (Fin N)) (rho : ℝ) (hrho : 0 < rho)
    (hA : rho ≤ ∑ x ∈ A, P.w x)
    (hF : ∀ x ∈ A, rho ≤ ∑ z ∈ F x, P.w z)
    (good : (Fin t → Fin N) → Prop)
    (hgood : ∀ (x : Fin N) (hx : x ∈ A),
      let Q := Law.restrict P (F x) (lt_of_lt_of_le hrho (hF x hx))
      (1 / 2 : ℝ) ≤ ∑ z : Fin t → Fin N, (∏ i, Q.w (z i)) *
        (if good z then 1 else 0)) :
    ∃ z : Fin t → Fin N, good z ∧ (∏ i, P.w (z i)) ≠ 0 ∧
      rho^(t+1)/4 < ∑ x ∈ A.filter (fun x => ∀ i, z i ∈ F x), P.w x := by
  classical
  let W (z : Fin t → Fin N) := ∏ i, P.w (z i)
  let D (z : Fin t → Fin N) := A.filter (fun x => ∀ i, z i ∈ F x)
  have hW (z) : 0 ≤ W z := Finset.prod_nonneg (fun i _ => P.nonneg _)
  have hWsum : ∑ z, W z = 1 := (FinProb.pi (fun _ : Fin t => P)).sum_eq_one
  have hrow (x : Fin N) (hx : x ∈ A) :
      rho^t / 2 ≤ ∑ z : Fin t → Fin N, W z *
        (if good z ∧ ∀ i, z i ∈ F x then 1 else 0) := by
    let m := ∑ z ∈ F x, P.w z
    have hm : 0 < m := lt_of_lt_of_le hrho (hF x hx)
    let Q := Law.restrict P (F x) hm
    have hpoint (z : Fin t → Fin N) : W z *
        (if good z ∧ ∀ i, z i ∈ F x then (1 : ℝ) else 0) =
        m^t * (∏ i, Q.w (z i)) * (if good z then 1 else 0) := by
      by_cases hz : ∀ i, z i ∈ F x
      · have hprod : (∏ i, Q.w (z i)) = W z / m^t := by
          simp only [Q, Law.restrict, hz, ite_eq_left]
          rw [Finset.prod_div_distrib]
          simp [W, m]
        rw [hprod]
        field_simp [ne_of_gt hm]
        by_cases hg : good z <;> simp [hg, hz] <;> ring
      · obtain ⟨i, hi⟩ := not_forall.mp hz
        have hzero : (∏ k, Q.w (z k)) = 0 := by
          apply Finset.prod_eq_zero (Finset.mem_univ i)
          simp [Q, Law.restrict, hi]
        simp [hz, hzero]
    have heq : (∑ z : Fin t → Fin N, W z *
        (if good z ∧ ∀ i, z i ∈ F x then (1 : ℝ) else 0)) =
        m^t * ∑ z : Fin t → Fin N, (∏ i, Q.w (z i)) *
          (if good z then 1 else 0) := by
      simp_rw [hpoint, mul_assoc]
      rw [Finset.mul_sum]
    rw [heq]
    calc
      rho^t / 2 ≤ m^t / 2 := by
        exact div_le_div_of_nonneg_right (pow_le_pow_left₀ hrho.le (hF x hx) _) (by norm_num)
      _ ≤ _ := by
        have hg := hgood x hx
        change (1 / 2 : ℝ) ≤ ∑ z : Fin t → Fin N, (∏ i, Q.w (z i)) *
          (if good z then 1 else 0) at hg
        nlinarith [mul_le_mul_of_nonneg_left hg (pow_nonneg hm.le t)]
  have hjoint : rho^(t+1) / 2 ≤
      ∑ z : Fin t → Fin N, W z * (if good z then ∑ x ∈ D z, P.w x else 0) := by
    calc
      rho^(t+1)/2 = rho * (rho^t/2) := by rw [pow_succ]; ring
      _ ≤ (∑ x ∈ A, P.w x) * (rho^t/2) :=
        mul_le_mul_of_nonneg_right hA (by positivity)
      _ ≤ ∑ x ∈ A, P.w x * ∑ z : Fin t → Fin N, W z *
          (if good z ∧ ∀ i, z i ∈ F x then 1 else 0) := by
        rw [Finset.sum_mul]
        exact Finset.sum_le_sum (fun x hx => mul_le_mul_of_nonneg_left (hrow x hx) (P.nonneg x))
      _ = _ := by
        simp_rw [Finset.mul_sum]
        rw [Finset.sum_comm]
        apply Finset.sum_congr rfl
        intro z hz
        by_cases hg : good z
        · simp only [hg, true_and, ite_eq_left]
          rw [Finset.mul_sum]
          change (∑ x ∈ A, P.w x * (W z * (if ∀ i, z i ∈ F x then 1 else 0))) = _
          rw [Finset.sum_filter]
          apply Finset.sum_congr rfl
          intro x hx
          by_cases hf : ∀ i, z i ∈ F x <;> simp [hf] <;> ring
        · simp [hg]
  by_contra hnone
  have hupper : (∑ z : Fin t → Fin N, W z *
      (if good z then ∑ x ∈ D z, P.w x else 0)) ≤ rho^(t+1)/4 := by
    calc
      _ ≤ ∑ z : Fin t → Fin N, W z * (rho^(t+1)/4) := by
        apply Finset.sum_le_sum
        intro z hz
        by_cases hg : good z
        · by_cases hw : W z = 0
          · simp [hw]
          · have hd : (∑ x ∈ D z, P.w x) ≤ rho^(t+1)/4 := by
              apply le_of_not_gt
              intro hd
              exact hnone ⟨z, hg, hw, hd⟩
            simpa [hg] using mul_le_mul_of_nonneg_left hd (hW z)
        · simp [hg, mul_nonneg (hW z) (by positivity : 0 ≤ rho^(t+1)/4)]
      _ = _ := by rw [← Finset.sum_mul, hWsum]; ring
  have hp : 0 < rho^(t+1) := pow_pos hrho _
  linarith

private theorem fv_density {N : ℕ} (E : Fin N → Fin N → Prop) (G : Colour)
    (μ ν : Law N) :
    (∑ x, μ.w x * ∑ y, ν.w y * fv E G x y) = 2 * dens E G μ ν - 1 := by
  classical
  simp only [fv, hit, dens]
  simp only [mul_sub, mul_one, Finset.sum_sub_distrib, ← Finset.sum_mul,
    ν.sum_eq_one, μ.sum_eq_one]
  congr 1
  simp only [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro x hx
  apply Finset.sum_congr rfl
  intro y hy
  ring

/-- Positive tilting pays for its actual normalizer in the discrepancy bound. -/
theorem centered_nonneg_test {N : ℕ} {E : Fin N → Fin N → Prop}
    {X Y : Finset (Fin N)} {wX wY err B : ℝ} (G : Colour)
    (hdisc : DiscOne E X Y wX wY err) (μ π : Law N)
    (hμX : μ.SupportedIn X) (hπY : π.SupportedIn Y)
    (hμ : μ.WidthLE wX) (hπ : π.WidthLE (wY - Real.log (B+1)))
    (hB : 0 ≤ B) (hN : 0 < (N : ℝ))
    (h : Fin N → ℝ) (hh : ∀ y, 0 ≤ h y ∧ h y ≤ B) :
    |∑ x, μ.w x * ∑ y, π.w y * (fv E G x y - sMean E G π.w x) * h y| ≤
      4 * (1 + ∑ y, π.w y * h y) * err := by
  classical
  let Z : ℝ := 1 + ∑ y, π.w y * h y
  have hZ : 1 ≤ Z := by
    have := Finset.sum_nonneg (fun y (_ : y ∈ Finset.univ) => mul_nonneg (π.nonneg y) (hh y).1)
    dsimp [Z]
    linarith
  have hZpos : 0 < Z := by linarith
  have hnorm : ∑ y, π.w y * (1 + h y) = Z := by
    simp_rw [mul_add, mul_one, Finset.sum_add_distrib, π.sum_eq_one]
    rfl
  let ν : Law N := {
    w := fun y => π.w y * (1 + h y) / Z
    nonneg := fun y => div_nonneg (mul_nonneg (π.nonneg y) (by linarith [(hh y).1])) hZpos.le
    sum_eq_one := by rw [← Finset.sum_div, hnorm, div_self hZpos.ne']
  }
  have hνY : ν.SupportedIn Y := by
    intro y hy
    simp [ν, hπY y hy]
  have hνW : ν.WidthLE wY := by
    intro y
    change π.w y * (1 + h y) / Z ≤ _
    have hratio : (1 + h y) / Z ≤ B+1 := by
      apply (div_le_iff₀ hZpos).2
      nlinarith [(hh y).2, mul_le_mul_of_nonneg_left hZ (by linarith : 0 ≤ B+1)]
    calc
      _ = π.w y * ((1 + h y) / Z) := by ring
      _ ≤ π.w y * (B+1) := mul_le_mul_of_nonneg_left hratio (π.nonneg y)
      _ ≤ (Real.exp (wY - Real.log (B+1)) / N) * (B+1) :=
        mul_le_mul_of_nonneg_right (hπ y) (by linarith)
      _ = Real.exp wY / N := by
        rw [Real.exp_sub, Real.exp_log (by linarith : 0 < B+1)]
        field_simp [hN.ne']
        <;> ring
  have hπW : π.WidthLE wY := Law.WidthLE.mono hπ (by
    have hlog : 0 ≤ Real.log (B+1) := Real.log_nonneg (by linarith)
    linarith)
  have hdν := hdisc μ ν hμX hνY hμ hνW G
  have hdπ := hdisc μ π hμX hπY hμ hπW G
  have hdiff : |dens E G μ ν - dens E G μ π| ≤ 2*err := by
    calc
      _ = |(dens E G μ ν - 1/2) - (dens E G μ π - 1/2)| := by congr 1; ring
      _ ≤ _ := abs_sub _ _
      _ ≤ _ := by linarith
  have hrow (x : Fin N) : Z * (∑ y, ν.w y * fv E G x y) =
      sMean E G π.w x + ∑ y, π.w y * fv E G x y * h y := by
    rw [Finset.mul_sum]
    calc
      _ = ∑ y, (π.w y * fv E G x y + π.w y * fv E G x y * h y) := by
        apply Finset.sum_congr rfl
        intro y hy
        change Z * (π.w y * (1 + h y) / Z * fv E G x y) = _
        field_simp [hZpos.ne']
        <;> ring
      _ = _ := by rw [Finset.sum_add_distrib]; rfl
  have hcenter (x : Fin N) :
      (∑ y, π.w y * (fv E G x y - sMean E G π.w x) * h y) =
        Z * ((∑ y, ν.w y * fv E G x y) - ∑ y, π.w y * fv E G x y) := by
    have hm : ∑ y, π.w y * sMean E G π.w x * h y =
        sMean E G π.w x * ∑ y, π.w y * h y := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro y hy
      ring
    simp only [sub_mul, mul_sub, Finset.sum_sub_distrib]
    rw [hm]
    change _ = Z * (∑ y, ν.w y * fv E G x y) - Z * sMean E G π.w x
    have := hrow x
    dsimp [Z] at *
    nlinarith
  have hid : (∑ x, μ.w x * ∑ y, π.w y *
      (fv E G x y - sMean E G π.w x) * h y) =
      2*Z*(dens E G μ ν - dens E G μ π) := by
    simp_rw [hcenter, mul_sub, Finset.sum_sub_distrib]
    have hscale (ν' : Law N) :
        (∑ x, μ.w x * (Z * ∑ y, ν'.w y * fv E G x y)) =
          Z * (∑ x, μ.w x * ∑ y, ν'.w y * fv E G x y) := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro x hx
      ring
    rw [hscale, hscale, fv_density, fv_density]
    ring
  rw [hid, abs_mul, abs_of_pos (by positivity : 0 < 2*Z)]
  calc
    _ ≤ (2*Z)*(2*err) := mul_le_mul_of_nonneg_left hdiff (by positivity)
    _ = _ := by dsimp [Z]; ring

/-- Signed centered tests depend on their L¹ norm; only their width uses the supremum. -/
theorem centered_signed_test {N : ℕ} {E : Fin N → Fin N → Prop}
    {X Y : Finset (Fin N)} {wX wY err B L : ℝ} (G : Colour)
    (hdisc : DiscOne E X Y wX wY err) (μ π : Law N)
    (hμX : μ.SupportedIn X) (hπY : π.SupportedIn Y)
    (hμ : μ.WidthLE wX) (hπ : π.WidthLE (wY - Real.log (B+1)))
    (hB : 0 ≤ B) (hN : 0 < (N : ℝ)) (herr : 0 ≤ err)
    (T : Fin N → ℝ) (hT : ∀ y, |T y| ≤ B)
    (hL : 1 ≤ L) (hTL : ∑ y, π.w y * |T y| ≤ L) :
    |∑ x, μ.w x * ∑ y, π.w y * (fv E G x y - sMean E G π.w x) * T y| ≤
      12 * L * err := by
  classical
  let p (y : Fin N) := max (T y) 0
  let m (y : Fin N) := max (-T y) 0
  have hp (y) : 0 ≤ p y ∧ p y ≤ B := by dsimp [p]; constructor; positivity; exact max_le (le_of_abs_le (hT y)) hB
  have hm (y) : 0 ≤ m y ∧ m y ≤ B := by dsimp [m]; constructor; positivity; exact max_le (by have := (abs_le.mp (hT y)).1; linarith) hB
  have hpm (y) : p y - m y = T y ∧ p y + m y = |T y| := by
    dsimp [p, m]
    by_cases h : 0 ≤ T y
    · simp [max_eq_left h, max_eq_right (by linarith : -T y ≤ 0), abs_of_nonneg h]
    · have hh : T y ≤ 0 := le_of_not_ge h
      simp [max_eq_right hh, max_eq_left (by linarith : 0 ≤ -T y), abs_of_nonpos hh]
  have hsplit : (∑ x, μ.w x * ∑ y, π.w y * (fv E G x y - sMean E G π.w x) * T y) =
      (∑ x, μ.w x * ∑ y, π.w y * (fv E G x y - sMean E G π.w x) * p y) -
      (∑ x, μ.w x * ∑ y, π.w y * (fv E G x y - sMean E G π.w x) * m y) := by
    simp only [← (hpm _).1, mul_sub, Finset.sum_sub_distrib]
  have hsum : (∑ y, π.w y * p y) + (∑ y, π.w y * m y) ≤ L := by
    rw [← Finset.sum_add_distrib]
    calc
      _ = ∑ y, π.w y * |T y| := by
        apply Finset.sum_congr rfl
        intro y hy
        rw [← mul_add, (hpm y).2]
      _ ≤ L := hTL
  rw [hsplit]
  calc
    _ ≤ _ := abs_sub _ _
    _ ≤ 4*(1+∑ y, π.w y*p y)*err + 4*(1+∑ y, π.w y*m y)*err :=
      add_le_add (centered_nonneg_test G hdisc μ π hμX hπY hμ hπ hB hN p hp)
        (centered_nonneg_test G hdisc μ π hμX hπY hμ hπ hB hN m hm)
    _ ≤ _ := by nlinarith [mul_le_mul_of_nonneg_right hsum herr,
      mul_le_mul_of_nonneg_right hL herr]

theorem weighted_abs_le_of_second_moment {Ω : Type*} [Fintype Ω]
    (P : FinProb Ω) (f : Ω → ℝ) (L : ℝ) (hL : 0 ≤ L)
    (hsecond : ∑ y, P.w y * (f y)^2 ≤ L^2) :
    ∑ y, P.w y * |f y| ≤ L := by
  classical
  have hcs := Finset.sum_mul_sq_le_sq_mul_sq (Finset.univ : Finset Ω)
    (fun y => Real.sqrt (P.w y)) (fun y => Real.sqrt (P.w y) * |f y|)
  have heq (y : Ω) : Real.sqrt (P.w y) * (Real.sqrt (P.w y) * |f y|) = P.w y * |f y| := by
    calc
      _ = (Real.sqrt (P.w y))^2 * |f y| := by ring
      _ = _ := by rw [Real.sq_sqrt (P.nonneg y)]
  have hsq (y : Ω) : (Real.sqrt (P.w y) * |f y|)^2 = P.w y * (f y)^2 := by
    rw [mul_pow, Real.sq_sqrt (P.nonneg y), sq_abs]
  simp_rw [heq, Real.sq_sqrt (P.nonneg _), hsq, P.sum_eq_one, one_mul] at hcs
  have hn : 0 ≤ ∑ y, P.w y * |f y| := Finset.sum_nonneg (fun y _ => mul_nonneg (P.nonneg y) (abs_nonneg _))
  exact (sq_le_sq₀ hn hL).mp (hcs.trans hsecond)

/-- The bounded inverse-degree reweighting used in the two-free projection. -/
theorem inverse_degree_test {N : ℕ} {E : Fin N → Fin N → Prop}
    {X Y S : Finset (Fin N)} {wX wY err B L : ℝ} (G : Colour)
    (hdisc : DiscOne E X Y wX wY err) (Q π : Law N) (hS : S ⊆ X)
    (hQ : Q.SupportedIn S) (hπY : π.SupportedIn Y)
    (hQW : Q.WidthLE (wX - Real.log 3))
    (hπW : π.WidthLE (wY - Real.log (B+1)))
    (hB : 0 ≤ B) (hN : 0 < (N : ℝ)) (herr : 0 ≤ err)
    (r : Fin N → ℝ) (hr : ∀ x ∈ S, 2/3 ≤ r x ∧ r x ≤ 2)
    (hidentity : ∀ x ∈ S, ∀ y, aF E G π.w x y =
      r x * (fv E G x y - sMean E G π.w x))
    (T : Fin N → ℝ) (hT : ∀ y, |T y| ≤ B)
    (hL : 1 ≤ L) (hTL : ∑ y, π.w y * |T y| ≤ L) :
    |∑ x, Q.w x * ∑ y, π.w y * aF E G π.w x y * T y| ≤ 24*L*err := by
  classical
  let R (x : Fin N) := if x ∈ S then r x else 0
  have hR (x : Fin N) : 0 ≤ R x := by
    by_cases hx : x ∈ S
    · simp only [R, ite_eq_left hx]
      linarith [(hr x hx).1]
    · simp [R, hx]
  let c : ℝ := ∑ x, Q.w x * R x
  have hc : 2/3 ≤ c ∧ c ≤ 2 := by
    have hlo : ∑ x, Q.w x * (2/3) ≤ c := by
      apply Finset.sum_le_sum
      intro x hx
      by_cases hs : x ∈ S
      · simpa [R, hs] using mul_le_mul_of_nonneg_left (hr x hs).1 (Q.nonneg x)
      · simp [hQ x hs]
    have hhi : c ≤ ∑ x, Q.w x * 2 := by
      apply Finset.sum_le_sum
      intro x hx
      by_cases hs : x ∈ S
      · simpa [R, hs] using mul_le_mul_of_nonneg_left (hr x hs).2 (Q.nonneg x)
      · simp [hQ x hs]
    rw [← Finset.sum_mul, Q.sum_eq_one, one_mul] at hlo hhi
    exact ⟨hlo, hhi⟩
  have hcpos : 0 < c := by linarith [hc.1]
  let μ : Law N := {
    w := fun x => Q.w x * R x / c
    nonneg := fun x => div_nonneg (mul_nonneg (Q.nonneg x) (hR x)) hcpos.le
    sum_eq_one := by rw [← Finset.sum_div]; change c/c=1; exact div_self hcpos.ne'
  }
  have hμX : μ.SupportedIn X := by
    intro x hx
    have hs : x ∉ S := fun hs => hx (hS hs)
    simp [μ, hQ x hs]
  have hμW : μ.WidthLE wX := by
    intro x
    have hratio : R x / c ≤ 3 := by
      apply (div_le_iff₀ hcpos).2
      by_cases hs : x ∈ S
      · simp only [R, ite_eq_left hs]
        linarith [(hr x hs).2, hc.1]
      · simp [R, hs]
        positivity
    change Q.w x * R x / c ≤ _
    calc
      _ = Q.w x * (R x / c) := by ring
      _ ≤ Q.w x * 3 := mul_le_mul_of_nonneg_left hratio (Q.nonneg x)
      _ ≤ (Real.exp (wX-Real.log 3)/N)*3 := mul_le_mul_of_nonneg_right (hQW x) (by norm_num)
      _ = _ := by
        rw [Real.exp_sub, Real.exp_log (by norm_num : (0 : ℝ) < 3)]
        field_simp [hN.ne']
        <;> ring
  have hid : (∑ x, Q.w x * ∑ y, π.w y * aF E G π.w x y * T y) =
      c * (∑ x, μ.w x * ∑ y, π.w y * (fv E G x y - sMean E G π.w x) * T y) := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro x hx
    by_cases hs : x ∈ S
    · simp_rw [hidentity x hs, Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro y hy
      change Q.w x * (π.w y * (r x * _) * T y) =
        c * (Q.w x * R x / c * (π.w y * _ * T y))
      simp only [R, ite_eq_left hs]
      field_simp [hcpos.ne']
      <;> ring
    · simp [hQ x hs, μ]
  have ht := centered_signed_test G hdisc μ π hμX hπY hμW hπW hB hN herr T hT hL hTL
  rw [hid, abs_mul, abs_of_pos hcpos]
  calc
    _ ≤ c*(12*L*err) := mul_le_mul_of_nonneg_left ht hcpos.le
    _ ≤ 2*(12*L*err) := mul_le_mul_of_nonneg_right hc.2 (by positivity)
    _ = _ := by ring

end HypercubeRamsey.S11.Core.sol_s11_outer
