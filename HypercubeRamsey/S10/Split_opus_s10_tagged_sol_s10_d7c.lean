import HypercubeRamsey.Framework.FinProbLemmas
import HypercubeRamsey.S14.Construction_sol_s14_post
import HypercubeRamsey.S10.ClusterExclusion_p_s10_1k
import HypercubeRamsey.S06.EvenRows_select_sol_s06_ev_b

/-!
Finite posterior integration for the even comparison mean in Section 10.
The data mass is allowed to vanish. A subdensity with total mass at most one
then bounds the integrated posterior by its prior, including after a bounded
data-dependent normalization or gate.
-/

namespace HypercubeRamsey.Lane_sol_s10_d7c

open scoped BigOperators

variable {W Y : Type*} [Fintype W]

/-- Cancellation at one data value, including a zero data marginal. -/
theorem posterior_cancel (π : FinProb W) (F : W → Y → ℝ)
    (hF : ∀ w y, 0 ≤ F w y) (w : W) (y : Y) :
    π.expect (fun u => F u y) *
      (π.w w * F w y / π.expect (fun u => F u y)) = π.w w * F w y := by
  classical
  by_cases hm : π.expect (fun u => F u y) = 0
  · have hle : π.w w * F w y ≤ π.expect (fun u => F u y) := by
      exact Finset.single_le_sum
        (fun u _ => mul_nonneg (π.nonneg u) (hF u y)) (Finset.mem_univ w)
    have hz : π.w w * F w y = 0 :=
      le_antisymm (by simpa [hm] using hle) (mul_nonneg (π.nonneg w) (hF w y))
    simp [hm, hz]
  · field_simp [hm]

variable [Fintype Y]

/-- The finite integration identity, with arbitrary data-dependent test values. -/
theorem posterior_integration_identity (π : FinProb W) (F : W → Y → ℝ)
    (hF : ∀ w y, 0 ≤ F w y) (f : W → Y → ℝ) :
    (∑ y, π.expect (fun w => F w y) *
      ∑ w, f w y * (π.w w * F w y / π.expect (fun u => F u y))) =
        ∑ w, ∑ y, π.w w * f w y * F w y := by
  classical
  simp_rw [Finset.mul_sum]
  calc
    (∑ y, ∑ w, π.expect (fun u => F u y) *
      (f w y * (π.w w * F w y / π.expect (fun u => F u y)))) =
        ∑ y, ∑ w, π.w w * f w y * F w y := by
      apply Finset.sum_congr rfl
      intro y _
      apply Finset.sum_congr rfl
      intro w _
      rw [show π.expect (fun u => F u y) *
        (f w y * (π.w w * F w y / π.expect (fun u => F u y))) =
          f w y * (π.expect (fun u => F u y) *
            (π.w w * F w y / π.expect (fun u => F u y))) by ring,
        posterior_cancel π F hF w y]
      ring
    _ = _ := Finset.sum_comm

/-- A subdensity integrates the posterior of a nonnegative test to at most
its prior expectation. The total subdensity is the candidate's gate probability. -/
theorem posterior_mean_le_prior (π : FinProb W) (F : W → Y → ℝ)
    (hF : ∀ w y, 0 ≤ F w y) (hgate : ∀ w, ∑ y, F w y ≤ 1)
    (f : W → ℝ) (hf : ∀ w, 0 ≤ f w) :
    (∑ y, π.expect (fun w => F w y) *
      ∑ w, f w * (π.w w * F w y / π.expect (fun u => F u y))) ≤
        π.expect f := by
  rw [posterior_integration_identity π F hF (fun w _ => f w)]
  unfold FinProb.expect
  apply Finset.sum_le_sum
  intro w _
  rw [← Finset.mul_sum]
  exact mul_le_of_le_one_right (mul_nonneg (π.nonneg w) (hf w)) (hgate w)

/-- Gating and light-part normalization cost at most their pointwise bound. -/
theorem bounded_posterior_mean_le_prior (π : FinProb W) (F : W → Y → ℝ)
    (hF : ∀ w y, 0 ≤ F w y) (hgate : ∀ w, ∑ y, F w y ≤ 1)
    (f : W → ℝ) (hf : ∀ w, 0 ≤ f w)
    (g : Y → ℝ) (C : ℝ) (hC : 0 ≤ C) (hg : ∀ y, g y ≤ C) :
    (∑ y, π.expect (fun w => F w y) *
      (g y * ∑ w, f w * (π.w w * F w y / π.expect (fun u => F u y)))) ≤
        C * π.expect f := by
  have hm (y : Y) : 0 ≤ π.expect (fun w => F w y) :=
    Finset.sum_nonneg fun w _ => mul_nonneg (π.nonneg w) (hF w y)
  have hp (y : Y) :
      0 ≤ ∑ w, f w * (π.w w * F w y / π.expect (fun u => F u y)) :=
    Finset.sum_nonneg fun w _ => mul_nonneg (hf w)
      (div_nonneg (mul_nonneg (π.nonneg w) (hF w y)) (hm y))
  calc
    _ ≤ ∑ y, π.expect (fun w => F w y) *
        (C * ∑ w, f w * (π.w w * F w y / π.expect (fun u => F u y))) := by
      apply Finset.sum_le_sum
      intro y _
      exact mul_le_mul_of_nonneg_left
        (mul_le_mul_of_nonneg_right (hg y) (hp y)) (hm y)
    _ = C * ∑ y, π.expect (fun w => F w y) *
        ∑ w, f w * (π.w w * F w y / π.expect (fun u => F u y)) := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro y _
      ring
    _ ≤ C * π.expect f := mul_le_mul_of_nonneg_left
      (posterior_mean_le_prior π F hF hgate f hf) hC

end HypercubeRamsey.Lane_sol_s10_d7c

namespace HypercubeRamsey.Lane_sol_s10_d7c

open scoped BigOperators

theorem light_mass_bound {k N n : ℕ} (hk : 0 < k) (hN : 0 < N)
    (a : ℝ) (ha : 0 < a) (has : a ≤ 1 / 10) (han : 100 ≤ a * n)
    (P : FinProb (Fin k → Fin N))
    (hcap : ∀ w, P.w w ≤
      Real.exp ((Real.log 2 - (4 / 100 : ℝ) * a) * k * n) * ((N : ℝ)⁻¹) ^ k) :
    let f := fun x => ∑ w, P.w w *
      (((Finset.univ.filter fun j => w j = x).card : ℝ) / k)
    a / 200 ≤ ∑ x ∈ Finset.univ.filter
      (fun x => N * f x ≤ Real.exp ((Real.log 2 - (2 / 100 : ℝ) * a) * n)), f x := by
  classical
  let P' : FinLaw (Fin k → Fin N) := ⟨P.w, P.nonneg, P.sum_eq_one⟩
  have hcap' : ∀ w, P'.w w ≤
      Real.exp ((Real.log 2 - 0.04 * a) * k * n) * ((N : ℝ)⁻¹) ^ k := by
    intro w
    convert hcap w using 1 <;> norm_num [P']
  have h := Lane_sol_s14_post.light_mass hk hN a ha has han P' hcap'
  have hc (w : Fin k → Fin N) (x : Fin N) :
      ((Finset.univ.filter fun j => w j = x).card : ℝ) =
        ∑ j, if w j = x then (1 : ℝ) else 0 := by
    simp only [Finset.card_filter, Nat.cast_sum, Nat.cast_ite, Nat.cast_one, Nat.cast_zero]
  have hexp : Real.exp ((Real.log 2 - (2 / 100 : ℝ) * a) * n) =
      (2 : ℝ) ^ n * Real.exp (-(2 / 100 : ℝ) * a * n) := by
    rw [show (Real.log 2 - (2 / 100 : ℝ) * a) * n =
      (n : ℝ) * Real.log 2 + -(2 / 100 : ℝ) * a * n by ring,
      Real.exp_add, Real.exp_nat_mul, Real.exp_log (by norm_num : (0 : ℝ) < 2)]
  simp only [P', hc, hexp] at h ⊢
  norm_num at h ⊢
  exact h

theorem pi_expect_split {ι A : Type*} [Fintype ι] [DecidableEq ι] [Fintype A]
    (P : ι → FinProb A) (i : ι) (f : (ι → A) → ℝ) :
    (FinProb.pi P).expect f =
      (FinProb.pi (fun j : {j // j ≠ i} => P j.1)).expect (fun rest =>
        (P i).expect (fun a => f ((Equiv.piSplitAt i (fun _ => A)).symm (a, rest)))) := by
  let P' (j : ι) : FinLaw A := ⟨(P j).w, (P j).nonneg, (P j).sum_eq_one⟩
  exact Lane_sol_s14_post.pi_E_split P' i f

theorem pi_expect_resample {ι A : Type*} [Fintype ι] [DecidableEq ι] [Fintype A]
    (P : ι → FinProb A) (i : ι) (f : (ι → A) → ℝ) :
    (FinProb.pi P).expect (fun v => (P i).expect (fun a => f (Function.update v i a))) =
      (FinProb.pi P).expect f := by
  classical
  have hu (a b : A) (rest : {j // j ≠ i} → A) :
      Function.update ((Equiv.piSplitAt i (fun _ => A)).symm (a, rest)) i b =
        (Equiv.piSplitAt i (fun _ => A)).symm (b, rest) := by
    funext j
    by_cases hj : j = i
    · subst j; simp
    · simp [Equiv.piSplitAt, hj]
  rw [pi_expect_split P i, pi_expect_split P i]
  apply Finset.sum_congr rfl
  intro rest _
  congr 1
  simp_rw [hu]
  exact FinProb.expect_const (P i) _

theorem coordinate_average_prior {A : Type*} [Fintype A] [DecidableEq A]
    (μ : FinProb A) {k : ℕ} (hk : 0 < k) (x : A) :
    (FinProb.pi (fun _ : Fin k => μ)).expect (fun w =>
      (((Finset.univ.filter fun j => w j = x).card : ℝ) / k)) = μ.w x := by
  classical
  have hcoord (j : Fin k) :
      (FinProb.pi (fun _ : Fin k => μ)).expect
        (fun w => if w j = x then (1 : ℝ) else 0) = μ.w x := by
    rw [pi_expect_split (fun _ : Fin k => μ) j]
    have heval (a : A) (rest : {i : Fin k // i ≠ j} → A) :
        (Equiv.piSplitAt j (fun _ : Fin k => A)).symm (a, rest) j = a := by
      simp [Equiv.piSplitAt]
    simp only [heval]
    have he : μ.expect (fun a => if a = x then (1 : ℝ) else 0) = μ.w x := by
      simp [FinProb.expect]
    simp_rw [he]
    exact FinProb.expect_const _ _
  simp only [Finset.card_filter, Nat.cast_sum, Nat.cast_ite, Nat.cast_one, Nat.cast_zero]
  unfold FinProb.expect at hcoord ⊢
  simp_rw [← mul_div_assoc]
  rw [← Finset.sum_div]
  simp_rw [Finset.mul_sum]
  rw [Finset.sum_comm]
  simp_rw [hcoord]
  simp [ne_of_gt (show (0 : ℝ) < k by exact_mod_cast hk)]

end HypercubeRamsey.Lane_sol_s10_d7c

namespace HypercubeRamsey.Lane_sol_s10_d7c
open scoped BigOperators

/-- Exchange a product coordinate with an independent draw from its own law. -/
theorem pi_weight_swap {ι A : Type*} [Fintype ι] [DecidableEq ι] [Fintype A]
    (P : ι → FinProb A) (i : ι) (v : ι → A) (a : A) :
    (FinProb.pi P).w (Function.update v i a) * (P i).w (v i) =
      (FinProb.pi P).w v * (P i).w a := by
  classical
  have hf (v : ι → A) : (∏ j, (P j).w (v j)) =
      (P i).w (v i) * ∏ j ∈ Finset.univ.erase i, (P j).w (v j) :=
    (Finset.mul_prod_erase Finset.univ (fun j => (P j).w (v j))
      (Finset.mem_univ i)).symm
  change (∏ j, (P j).w (Function.update v i a j)) * (P i).w (v i) =
    (∏ j, (P j).w (v j)) * (P i).w a
  rw [hf, hf]
  simp only [Function.update_self]
  have he : (∏ j ∈ Finset.univ.erase i, (P j).w (Function.update v i a j)) =
      ∏ j ∈ Finset.univ.erase i, (P j).w (v j) := by
    apply Finset.prod_congr rfl
    intro j hj
    rw [Function.update_of_ne (Finset.mem_erase.mp hj).1]
  rw [he]
  ring

/-- Resampling an independent component preserves the raw law. -/
theorem resample_identity {H W : Type*} [Fintype H] [Fintype W]
    (P : FinProb H) (π : FinProb W) (get : H → W) (put : H → W → H)
    (hget : ∀ h w, get (put h w) = w)
    (hput : ∀ h w w', put (put h w) w' = put h w')
    (hself : ∀ h, put h (get h) = h)
    (hswap : ∀ h w, P.w (put h w) * π.w (get h) = P.w h * π.w w)
    (f : H → ℝ) :
    P.expect (fun h => π.expect (fun w => f (put h w))) = P.expect f := by
  classical
  let e : H × W ≃ H × W := {
    toFun := fun hw => (put hw.1 hw.2, get hw.1)
    invFun := fun hw => (put hw.1 hw.2, get hw.1)
    left_inv := by intro hw; simp only [hget, hput, hself]
    right_inv := by intro hw; simp only [hget, hput, hself] }
  let F : H × W → ℝ := fun hw => P.w hw.1 * π.w hw.2 * f hw.1
  have he := Equiv.sum_comp e F
  have hp (hw : H × W) : F (e hw) = P.w hw.1 * π.w hw.2 * f (put hw.1 hw.2) := by
    dsimp [F, e]
    rw [hswap]
  simp_rw [hp] at he
  simp only [F, Fintype.sum_prod_type] at he
  have hr : (∑ h, ∑ w, P.w h * π.w w * f h) = P.expect f := by
    simp [FinProb.expect, mul_right_comm, ← Finset.mul_sum, π.sum_eq_one]
  rw [hr] at he
  convert he using 1
  simp only [FinProb.expect, Finset.mul_sum, mul_assoc]

/-- Integrated posterior with a uniform bound on the subdensity's total mass. -/
theorem bounded_posterior_mean_le_prior_mul {W Y : Type*} [Fintype W] [Fintype Y]
    (π : FinProb W) (F : W → Y → ℝ) (hF : ∀ w y, 0 ≤ F w y)
    (B : ℝ) (hgate : ∀ w, ∑ y, F w y ≤ B)
    (f : W → ℝ) (hf : ∀ w, 0 ≤ f w)
    (g : Y → ℝ) (C : ℝ) (hC : 0 ≤ C) (hg : ∀ y, g y ≤ C) :
    (∑ y, π.expect (fun w => F w y) *
      (g y * ∑ w, f w * (π.w w * F w y / π.expect (fun u => F u y)))) ≤
        C * π.expect f * B := by
  have hm (y : Y) : 0 ≤ π.expect (fun w => F w y) :=
    Finset.sum_nonneg fun w _ => mul_nonneg (π.nonneg w) (hF w y)
  have hp (y : Y) :
      0 ≤ ∑ w, f w * (π.w w * F w y / π.expect (fun u => F u y)) :=
    Finset.sum_nonneg fun w _ => mul_nonneg (hf w)
      (div_nonneg (mul_nonneg (π.nonneg w) (hF w y)) (hm y))
  calc
    _ ≤ ∑ y, π.expect (fun w => F w y) *
        (C * ∑ w, f w * (π.w w * F w y / π.expect (fun u => F u y))) := by
      exact Finset.sum_le_sum fun y _ => mul_le_mul_of_nonneg_left
        (mul_le_mul_of_nonneg_right (hg y) (hp y)) (hm y)
    _ = C * ∑ y, π.expect (fun w => F w y) *
        ∑ w, f w * (π.w w * F w y / π.expect (fun u => F u y)) := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro y _
      ring
    _ = C * ∑ w, ∑ y, π.w w * f w * F w y := by
      rw [posterior_integration_identity π F hF (fun w _ => f w)]
    _ ≤ C * ∑ w, π.w w * f w * B := by
      apply mul_le_mul_of_nonneg_left _ hC
      apply Finset.sum_le_sum
      intro w _
      rw [← Finset.mul_sum]
      exact mul_le_mul_of_nonneg_left (hgate w) (mul_nonneg (π.nonneg w) (hf w))
    _ = _ := by rw [← Finset.sum_mul]; change C * (π.expect f * B) = _; ring

open Classical in
/-- Integrate a posterior component after resampling its candidate tuple. -/
theorem raw_posterior_component {H W Y : Type*} [Fintype H] [Fintype W] [Fintype Y]
    (P : FinProb H) (π : FinProb W) (put : H → W → H)
    (R : H → FinProb Y) (gate : H → Prop) (F : H → W → Y → ℝ)
    (hF : ∀ h w y, 0 ≤ F h w y)
    (hFgate : ∀ h w y, F h w y = if gate (put h w) then (R (put h w)).w y else 0)
    (hinvariant : ∀ h w w' y, F (put h w) w' y = F h w' y)
    (hstat : ∀ f, P.expect (fun h => π.expect (fun w => f (put h w))) = P.expect f)
    (f : W → ℝ) (hf : ∀ w, 0 ≤ f w)
    (g : H → Y → ℝ) (hginv : ∀ h w y, g (put h w) y = g h y)
    (C : ℝ) (hC : 0 ≤ C) (hg : ∀ h y, g h y ≤ C)
    (B : H → ℝ) (hB : ∀ h w, ∑ y, F h w y ≤ B h) :
    P.expect (fun h => (R h).expect (fun y => if gate h then g h y *
      (∑ w, f w * (π.w w * F h w y / π.expect (fun u => F h u y))) else 0)) ≤
        C * π.expect f * P.expect B := by
  classical
  let A (h : H) (y : Y) : ℝ :=
    ∑ w, f w * (π.w w * F h w y / π.expect (fun u => F h u y))
  have hAinv (h : H) (w : W) (y : Y) : A (put h w) y = A h y := by
    simp only [A, hinvariant]
  change P.expect (fun h => (R h).expect (fun y =>
    if gate h then g h y * A h y else 0)) ≤ _
  rw [← hstat]
  simp only [hginv, hAinv]
  calc
    _ = P.expect (fun h => ∑ y, π.expect (fun w => F h w y) *
        (g h y * A h y)) := by
      apply Finset.sum_congr rfl
      intro h _
      congr 1
      simp only [FinProb.expect, Finset.mul_sum]
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro y _
      rw [Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro w _
      rw [hFgate]
      split_ifs <;> ring
    _ ≤ P.expect (fun h => C * π.expect f * B h) :=
      FinProb.expect_mono P fun h =>
        bounded_posterior_mean_le_prior_mul π (F h) (hF h) (B h) (hB h)
          f hf (g h) C hC (hg h)
    _ = _ := by simp only [FinProb.expect_smul]

end HypercubeRamsey.Lane_sol_s10_d7c

namespace HypercubeRamsey.Lane_sol_s10_d7c
open scoped BigOperators
open Classical

noncomputable def groupedLaw {G C B A : Type*} [Fintype G] [DecidableEq G]
    [Fintype C] [Fintype B] [DecidableEq B] [Fintype A]
    (P : G → FinProb C) (D : G → C → FinProb A) (grp : B → G) : FinProb (B → A) where
  w y := ∑ c : G → C, (FinProb.pi P).w c *
    (FinProb.pi (fun b => D (grp b) (c (grp b)))).w y
  nonneg y := Finset.sum_nonneg fun c _ =>
    mul_nonneg ((FinProb.pi P).nonneg c) ((FinProb.pi _).nonneg y)
  sum_eq_one := by
    rw [Finset.sum_comm]
    simp_rw [← Finset.mul_sum, FinProb.sum_eq_one, mul_one]
    exact (FinProb.pi P).sum_eq_one

theorem groupedLaw_expect {G C B A : Type*} [Fintype G] [DecidableEq G]
    [Fintype C] [Fintype B] [DecidableEq B] [Fintype A]
    (P : G → FinProb C) (D : G → C → FinProb A) (grp : B → G) (f : (B → A) → ℝ) :
    (groupedLaw P D grp).expect f = ∑ c : G → C, (FinProb.pi P).w c *
      (FinProb.pi (fun b => D (grp b) (c (grp b)))).expect f := by
  unfold FinProb.expect groupedLaw
  simp_rw [Finset.sum_mul]
  rw [Finset.sum_comm]
  simp_rw [Finset.mul_sum, mul_assoc]

theorem groupedLaw_weight {G C B A : Type*} [Fintype G] [DecidableEq G]
    [Fintype C] [Fintype B] [DecidableEq B] [Fintype A]
    (P : G → FinProb C) (D : G → C → FinProb A) (grp : B → G) (y : B → A) :
    (groupedLaw P D grp).w y =
      ∏ q ∈ Finset.univ.image grp, (P q).expect (fun c =>
        ∏ b ∈ Finset.univ.filter (fun b => grp b = q), (D q c).w (y b)) := by
  classical
  change (∑ c : G → C, (∏ q, (P q).w (c q)) *
    ∏ b, (D (grp b) (c (grp b))).w (y b)) = _
  rw [Lane_q_s14_post.sum_pi_grouped grp (fun q c => (P q).w c)
    (fun q c a => (D q c).w a) y]
  simp_rw [← Finset.prod_filter]
  apply Eq.symm
  apply Finset.prod_subset (Finset.subset_univ _)
  intro q _ hq
  have hempty : Finset.univ.filter (fun b => grp b = q) = ∅ := by
    apply Finset.eq_empty_iff_forall_notMem.mpr
    intro b hb
    exact hq (Finset.mem_image.mpr ⟨b, Finset.mem_univ b, (Finset.mem_filter.mp hb).2⟩)
  simp only [hempty, Finset.prod_empty, mul_one]
  exact FinProb.expect_const (P q) 1

theorem groupedLaw_marginal {G C B A : Type*} [Fintype G] [DecidableEq G]
    [Fintype C] [Fintype B] [DecidableEq B] [Fintype A]
    (P : G → FinProb C) (D : G → C → FinProb A) (grp : B → G)
    (S : Finset B) (a₀ : A) (f : (B → A) → ℝ) (hf : FinProb.DependsOn f S) :
    (groupedLaw P D grp).expect f =
      (groupedLaw P D (fun b : {b // b ∈ S} => grp b.1)).expect
        (fun y => f (fun b => if hb : b ∈ S then y ⟨b, hb⟩ else a₀)) := by
  classical
  rw [groupedLaw_expect, groupedLaw_expect]
  apply Finset.sum_congr rfl
  intro c _
  congr 1
  have he (y : B → A) : f y =
      f (fun b => if hb : b ∈ S then y b else a₀) := by
    apply hf
    intro b hb
    simp [hb]
  conv_lhs => arg 2; ext y; rw [he y]
  exact FinProb.pi_marginal_expect (fun b => D (grp b) (c (grp b))) S
    (fun y => f (fun b => if hb : b ∈ S then y ⟨b, hb⟩ else a₀))

end HypercubeRamsey.Lane_sol_s10_d7c

namespace HypercubeRamsey.Lane_sol_s10_d7c
open scoped BigOperators

/-- Pointwise predictive domination; the reference weights need not normalize. -/
theorem posterior_domination {W : Type*} [Fintype W]
    (π : FinProb W) (F : W → ℝ) (Z Q ε A : ℝ)
    (hZ : 0 < Z) (hε : 0 < ε) (hA : 0 ≤ A)
    (hF : ∀ w, F w ≤ A * Q) (hpredict : ε * Q ≤ Z) (w : W) :
    π.w w * F w / Z ≤ A / ε * π.w w := by
  apply (div_le_iff₀ hZ).2
  have hc : 0 ≤ A / ε * π.w w := mul_nonneg (div_nonneg hA hε.le) (π.nonneg w)
  calc
    π.w w * F w ≤ π.w w * (A * Q) :=
      mul_le_mul_of_nonneg_left (hF w) (π.nonneg w)
    _ = (A / ε * π.w w) * (ε * Q) := by field_simp [hε.ne'] <;> ring
    _ ≤ _ := mul_le_mul_of_nonneg_left hpredict hc

end HypercubeRamsey.Lane_sol_s10_d7c

namespace HypercubeRamsey.Lane_sol_s10_d7c
open Filter

private theorem power_gap {p q C : ℝ} (hpq : p < q) (hC : 0 < C) :
    ∀ᶠ n : ℕ in atTop, C * (n : ℝ) ^ p ≤ (n : ℝ) ^ q := by
  have ht := (tendsto_rpow_atTop (sub_pos.mpr hpq)).comp tendsto_natCast_atTop_atTop
  filter_upwards [ht.eventually_ge_atTop C, eventually_ge_atTop (1 : ℕ)] with n h hn
  have hn0 : 0 < (n : ℝ) := by exact_mod_cast (by omega : 0 < n)
  calc
    _ ≤ (n : ℝ) ^ (q - p) * (n : ℝ) ^ p :=
      mul_le_mul_of_nonneg_right h (Real.rpow_nonneg hn0.le _)
    _ = _ := by rw [← Real.rpow_add hn0]; congr 1; ring

/-- All scale inequalities needed by the even posterior mean. -/
theorem mean_scales (δ : ℝ) (hδ : 0 < δ) (hδs : δ < 1 / 2000) :
    ∀ᶠ n : ℕ in atTop,
      2 ≤ n ∧ (n : ℝ) ^ (-δ) ≤ 1 / 10 ∧
      100 ≤ (n : ℝ) ^ (-δ) * n ∧
      (n : ℝ) ^ δ ≤ (1 / 100 : ℝ) * (n : ℝ) ^ (-δ) * n ∧
      200 / (n : ℝ) ^ (-δ) * ((topScale n δ (8 * δ) + 1 : ℕ) : ℝ) *
        (2 * (n : ℝ) ^ 10) * Real.exp ((n : ℝ) ^ δ) ≤
          Real.exp (((min ⌊(n : ℝ) ^ (200 * δ)⌋₊ n : ℕ) : ℝ) / 10) := by
  have h200 : 0 < 200 * δ := by positivity
  have hg : 0 < 1 - δ := by linarith
  have hcast : Tendsto (fun n : ℕ => (n : ℝ)) atTop atTop := tendsto_natCast_atTop_atTop
  have hsmall := ((tendsto_rpow_neg_atTop hδ).comp hcast).eventually_lt_const
    (by norm_num : (0 : ℝ) < 1 / 10)
  have hlarge := ((tendsto_rpow_atTop hg).comp hcast).eventually_ge_atTop (100 : ℝ)
  have hwidth := power_gap (show δ < 1 - δ by linarith) (by norm_num : (0 : ℝ) < 100)
  have hpower := power_gap (show δ < 200 * δ by linarith) (by norm_num : (0 : ℝ) < 100)
  have hconst := ((tendsto_rpow_atTop h200).comp hcast).eventually_ge_atTop
    (max 2 (100 * Real.log 2000))
  have hlog := (isLittleO_log_rpow_atTop h200).bound
    (show (0 : ℝ) < 1 / (100 * (12 + δ)) by positivity)
  filter_upwards [eventually_ge_atTop (2 : ℕ), hsmall, hlarge, hwidth,
    hpower, hconst, hcast.eventually hlog] with n hn has han hw hp hc hl
  have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast (show 1 ≤ n by omega)
  have hn0 : 0 < (n : ℝ) := by linarith
  let T := (n : ℝ) ^ (200 * δ)
  have hT2 : 2 ≤ T := (le_max_left _ _).trans hc
  have hTc : 100 * Real.log 2000 ≤ T := (le_max_right _ _).trans hc
  have hgain : (n : ℝ) ^ (-δ) * n = (n : ℝ) ^ (1 - δ) := by
    calc
      _ = (n : ℝ) ^ (-δ) * (n : ℝ) ^ (1 : ℝ) := by rw [Real.rpow_one]
      _ = _ := by rw [← Real.rpow_add hn0]; congr 1; ring
  have hwidth' : (n : ℝ) ^ δ ≤ (1 / 100 : ℝ) * (n : ℝ) ^ (-δ) * n := by
    rw [← hgain] at hw
    linarith
  have hTn : ⌊(n : ℝ) ^ (200 * δ)⌋₊ ≤ n := by
    have hTle : T ≤ (n : ℝ) := by
      simpa [T] using Real.rpow_le_rpow_of_exponent_le hn1
        (show 200 * δ ≤ (1 : ℝ) by linarith)
    exact_mod_cast (Nat.floor_le (Real.rpow_nonneg hn0.le (200 * δ))).trans hTle
  have hfloor : T / 2 ≤ (⌊(n : ℝ) ^ (200 * δ)⌋₊ : ℝ) := by
    have hf := Nat.lt_floor_add_one T
    nlinarith
  simp only [Real.norm_eq_abs] at hl
  rw [abs_of_nonneg (Real.log_nonneg hn1), abs_of_nonneg (Real.rpow_nonneg hn0.le _)] at hl
  have hlog' : 100 * (12 + δ) * Real.log n ≤ T := by
    have hd : (0 : ℝ) < 100 * (12 + δ) := by positivity
    have hl' : Real.log n ≤ T / (100 * (12 + δ)) := by
      simpa [T, div_eq_mul_inv, mul_comm] using hl
    simpa only [mul_comm] using (le_div_iff₀ hd).mp hl'
  have hpoly : 2000 * (n : ℝ) ^ (12 + δ) * Real.exp ((n : ℝ) ^ δ) ≤
      Real.exp (T / 20) := by
    calc
      _ = Real.exp (Real.log 2000 + (12 + δ) * Real.log n + (n : ℝ) ^ δ) := by
        rw [Real.exp_add, Real.exp_add, Real.exp_log (by norm_num : (0 : ℝ) < 2000)]
        rw [Real.rpow_def_of_pos hn0]
        rw [mul_comm (Real.log (n : ℝ)) (12 + δ)]
      _ ≤ _ := Real.exp_le_exp.mpr (by dsimp [T] at *; nlinarith)
  have hH : ((topScale n δ (8 * δ) + 1 : ℕ) : ℝ) ≤ 5 * (n : ℝ) ^ 2 := by
    have ht := S06.Lane_sol_s06_ev_b.topScale_bound hn
      (show δ ≤ 1 by linarith) (show 0 ≤ 8 * δ by positivity)
    have htc := (Nat.cast_le (α := ℝ)).mpr ht
    push_cast at htc ⊢
    nlinarith
  refine ⟨hn, has.le, ?_, hwidth', ?_⟩
  · rwa [hgain]
  · calc
      _ ≤ 200 / (n : ℝ) ^ (-δ) * (5 * (n : ℝ) ^ 2) *
          (2 * (n : ℝ) ^ 10) * Real.exp ((n : ℝ) ^ δ) := by gcongr
      _ = 2000 * (n : ℝ) ^ (12 + δ) * Real.exp ((n : ℝ) ^ δ) := by
        rw [Real.rpow_neg hn0.le, div_inv_eq_mul]
        rw [Real.rpow_add hn0, Real.rpow_ofNat]
        ring
      _ ≤ Real.exp (T / 20) := hpoly
      _ ≤ _ := by
        rw [min_eq_left hTn]
        exact Real.exp_le_exp.mpr (by linarith)

end HypercubeRamsey.Lane_sol_s10_d7c

namespace HypercubeRamsey.Lane_sol_s10_d7c
open scoped BigOperators

theorem expect_sum {I H : Type*} [Fintype I] [Fintype H]
    (P : FinProb H) (f : I → H → ℝ) :
    P.expect (fun h => ∑ i, f i h) = ∑ i, P.expect (f i) := by
  simp only [FinProb.expect, Finset.mul_sum]
  exact Finset.sum_comm

end HypercubeRamsey.Lane_sol_s10_d7c
