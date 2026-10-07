import HypercubeRamsey.S09.Core.Experiment
import HypercubeRamsey.Tools.Concentration
import HypercubeRamsey.Framework.LawLemmas
import HypercubeRamsey.Framework.FinProbLemmas
import HypercubeRamsey.S03.Clock.Steps_p_clock_r4

namespace HypercubeRamsey.Lane_sol_s09_cov

open Classical Filter
open scoped BigOperators Topology

theorem expect_const {Ω : Type*} [Fintype Ω] (Q : FinProb Ω) (a : ℝ) :
    Q.expect (fun _ => a) = a := by
  simp [FinProb.expect, ← Finset.sum_mul, Q.sum_eq_one]

theorem expect_mono {Ω : Type*} [Fintype Ω] (Q : FinProb Ω) {f g : Ω → ℝ}
    (h : ∀ x, f x ≤ g x) : Q.expect f ≤ Q.expect g := by
  exact Finset.sum_le_sum fun x _ => mul_le_mul_of_nonneg_left (h x) (Q.nonneg x)

theorem expect_add {Ω : Type*} [Fintype Ω] (Q : FinProb Ω) (f g : Ω → ℝ) :
    Q.expect (fun x => f x + g x) = Q.expect f + Q.expect g := by
  simp [FinProb.expect, mul_add, Finset.sum_add_distrib]

theorem expect_sub {Ω : Type*} [Fintype Ω] (Q : FinProb Ω) (f g : Ω → ℝ) :
    Q.expect (fun x => f x - g x) = Q.expect f - Q.expect g := by
  simp [FinProb.expect, mul_sub, Finset.sum_sub_distrib]

theorem expect_mul_const {Ω : Type*} [Fintype Ω] (Q : FinProb Ω) (f : Ω → ℝ) (a : ℝ) :
    Q.expect (fun x => f x * a) = Q.expect f * a := by
  simp [FinProb.expect, mul_assoc, Finset.sum_mul]

theorem expect_sum {Ω ι : Type*} [Fintype Ω] [Fintype ι] (Q : FinProb Ω)
    (f : ι → Ω → ℝ) : Q.expect (fun x => ∑ i, f i x) = ∑ i, Q.expect (f i) := by
  simp only [FinProb.expect, Finset.mul_sum]
  rw [Finset.sum_comm]

noncomputable def tilt {N : ℕ} (lam : Law N) (f : Fin N → ℝ)
    (hf : ∀ y, 0 ≤ f y) (hZ : 0 < lam.expect f) : Law N where
  w y := f y * lam.w y / lam.expect f
  nonneg y := div_nonneg (mul_nonneg (hf y) (lam.nonneg y)) hZ.le
  sum_eq_one := by
    rw [← Finset.sum_div]
    have hsum : ∑ y, f y * lam.w y = lam.expect f := by
      simp [FinProb.expect, mul_comm]
    rw [hsum, div_self hZ.ne']

theorem tilt_supported {N : ℕ} (lam : Law N) (f : Fin N → ℝ)
    (hf : ∀ y, 0 ≤ f y) (hZ : 0 < lam.expect f) {Y : Finset (Fin N)}
    (hY : lam.SupportedIn Y) : (tilt lam f hf hZ).SupportedIn Y := by
  intro y hy
  simp [tilt, hY y hy]

theorem tilt_width {N : ℕ} (lam : Law N) (f : Fin N → ℝ)
    (hf : ∀ y, 0 ≤ f y) (hZ : 0 < lam.expect f) {s W : ℝ}
    (hlam : lam.WidthLE s) (hcap : ∀ y, f y / lam.expect f ≤ Real.exp (W - s)) :
    (tilt lam f hf hZ).WidthLE W := by
  intro y
  change f y * lam.w y / lam.expect f ≤ Real.exp W / N
  calc
    _ = (f y / lam.expect f) * lam.w y := by ring
    _ ≤ Real.exp (W - s) * (Real.exp s / N) :=
      mul_le_mul (hcap y) (hlam y) (lam.nonneg y) (Real.exp_nonneg _)
    _ = Real.exp W / N := by
      rw [← mul_div_assoc, ← Real.exp_add]
      congr 2
      ring

/-- The two positive tilts of a mean-zero test have the same normalizer. -/
theorem tilt_normalizers {N : ℕ} (lam : Law N) (S : Fin N → ℝ) (L : ℝ)
    (hmean : lam.expect S = 0) :
    lam.expect (fun y => L + max (S y) 0) =
      lam.expect (fun y => L + max (-S y) 0) := by
  have hpoint (y : Fin N) : max (S y) 0 - max (-S y) 0 = S y := by
    by_cases h : 0 ≤ S y
    · rw [max_eq_left h, max_eq_right (by linarith)]
      ring
    · rw [max_eq_right (by linarith), max_eq_left (by linarith)]
      ring
  have hd := expect_sub lam (fun y => max (S y) 0) (fun y => max (-S y) 0)
  simp only [hpoint, hmean] at hd
  simp only [expect_add, expect_const]
  linarith

/-- Applying discrepancy separately to the two tilts retains the normalizer-sized bound. -/
theorem centered_test_bound {N : ℕ} {E : Fin N → Fin N → Prop}
    {X Y : Finset (Fin N)} {wX wY err : ℝ}
    (hdisc : DiscOne E X Y wX wY err) (G : Colour) (mu lam : Law N)
    (hmuX : mu.SupportedIn X) (hlamY : lam.SupportedIn Y) (hmuW : mu.WidthLE wX)
    (S : Fin N → ℝ) (L : ℝ) (hL : 0 < L) (hmean : lam.expect S = 0)
    (hpW : (tilt lam (fun y => L + max (S y) 0)
      (by intro y; positivity)
      (by have := expect_mono lam (f := fun _ => L) (g := fun y => L + max (S y) 0)
            (by intro y; have := le_max_right (S y) 0; linarith)
          rw [expect_const] at this; exact lt_of_lt_of_le hL this)).WidthLE wY)
    (hmW : (tilt lam (fun y => L + max (-S y) 0)
      (by intro y; positivity)
      (by have := expect_mono lam (f := fun _ => L) (g := fun y => L + max (-S y) 0)
            (by intro y; have := le_max_right (-S y) 0; linarith)
          rw [expect_const] at this; exact lt_of_lt_of_le hL this)).WidthLE wY) :
    |mu.expect (fun x => lam.expect (fun y => hitInd9 E G x y * S y))| ≤
      2 * err * lam.expect (fun y => L + max (S y) 0) := by
  let fp := fun y => L + max (S y) 0
  let fm := fun y => L + max (-S y) 0
  have hp : ∀ y, 0 ≤ fp y := by intro y; dsimp [fp]; positivity
  have hm : ∀ y, 0 ≤ fm y := by intro y; dsimp [fm]; positivity
  have hZp : 0 < lam.expect fp := by
    have h := expect_mono lam (f := fun _ => L) (g := fp)
      (by intro y; dsimp [fp]; have := le_max_right (S y) 0; linarith)
    rw [expect_const] at h
    exact lt_of_lt_of_le hL h
  have hZm : 0 < lam.expect fm := by
    have h := expect_mono lam (f := fun _ => L) (g := fm)
      (by intro y; dsimp [fm]; have := le_max_right (-S y) 0; linarith)
    rw [expect_const] at h
    exact lt_of_lt_of_le hL h
  let plus := tilt lam fp hp hZp
  let minus := tilt lam fm hm hZm
  have hnorm : lam.expect fp = lam.expect fm := tilt_normalizers lam S L hmean
  have hpdisc := hdisc mu plus hmuX (tilt_supported lam fp hp hZp hlamY) hmuW hpW G
  have hmdisc := hdisc mu minus hmuX (tilt_supported lam fm hm hZm hlamY) hmuW hmW G
  have hd : |dens E G mu plus - dens E G mu minus| ≤ 2 * err := by
    calc
      _ = |(dens E G mu plus - 1 / 2) - (dens E G mu minus - 1 / 2)| := by congr 1; ring
      _ ≤ |dens E G mu plus - 1 / 2| + |dens E G mu minus - 1 / 2| := abs_sub _ _
      _ ≤ err + err := add_le_add hpdisc hmdisc
      _ = 2 * err := by ring
  have hpoint (y : Fin N) : fp y - fm y = S y := by
    dsimp [fp, fm]
    by_cases hy : 0 ≤ S y
    · rw [max_eq_left hy, max_eq_right (by linarith)]; ring
    · rw [max_eq_right (by linarith), max_eq_left (by linarith)]; ring
  have hidentity : mu.expect (fun x => lam.expect (fun y => hitInd9 E G x y * S y)) =
      lam.expect fp * (dens E G mu plus - dens E G mu minus) := by
    unfold FinProb.expect dens
    rw [← Finset.sum_sub_distrib, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro x hx
    rw [← Finset.sum_sub_distrib, Finset.mul_sum, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro y hy
    change mu.w x * (lam.w y * (hitInd9 E G x y * S y)) =
      lam.expect fp * (mu.w x * (fp y * lam.w y / lam.expect fp) * hitInd9 E G x y -
        mu.w x * (fm y * lam.w y / lam.expect fm) * hitInd9 E G x y)
    rw [← hnorm]
    have := hpoint y
    field_simp [hZp.ne']
    rw [← hpoint y]
  rw [hidentity, abs_mul, abs_of_pos hZp]
  calc
    _ ≤ lam.expect fp * (2 * err) := mul_le_mul_of_nonneg_left hd hZp.le
    _ = _ := by ring


theorem expect_const_mul {Ω : Type*} [Fintype Ω] (Q : FinProb Ω) (a : ℝ) (f : Ω → ℝ) :
    Q.expect (fun x => a * f x) = a * Q.expect f := by
  simp [FinProb.expect, ← Finset.mul_sum, mul_left_comm]

private theorem iid_expect_cons {α : Type*} [Fintype α] {n : ℕ}
    (Q : FinProb α) (f : (Fin (n + 1) → α) → ℝ) :
    (FinProb.pi (fun _ : Fin (n+1) => Q)).expect f =
      Q.expect (fun a => (FinProb.pi (fun _ : Fin n => Q)).expect
        (fun x => f (Fin.cons a x))) := by
  have hsumCons (g : (Fin (n+1) → α) → ℝ) :
      (∑ x, g x) = ∑ a : α, ∑ y : Fin n → α, g (Fin.cons a y) := by
    rw [← Equiv.sum_comp (Fin.consEquiv (fun _ : Fin (n+1) => α)) g]
    rw [Fintype.sum_prod_type]
    rfl
  unfold FinProb.expect
  rw [hsumCons]
  simp [FinProb.pi, Finset.mul_sum, Fin.prod_univ_succ, mul_assoc, mul_comm, mul_left_comm]

theorem iid_sum_expect {α : Type*} [Fintype α] (Q : FinProb α) (f : α → ℝ) (t : ℕ) :
    (FinProb.pi (fun _ : Fin t => Q)).expect (fun w => ∑ j, f (w j)) = t * Q.expect f := by
  induction t with
  | zero => simpa using expect_const (FinProb.pi (fun _ : Fin 0 => Q)) 0
  | succ t ih =>
      rw [iid_expect_cons]
      simp_rw [Fin.sum_univ_succ, Fin.cons_zero, Fin.cons_succ, expect_add, expect_const, ih]
      push_cast
      ring

theorem iid_sum_square {α : Type*} [Fintype α] (Q : FinProb α) (f : α → ℝ) (t : ℕ) :
    (FinProb.pi (fun _ : Fin t => Q)).expect (fun w => (∑ j, f (w j)) ^ 2) =
      t * Q.expect (fun a => (f a)^2) + ((t : ℝ)^2 - t) * (Q.expect f)^2 := by
  induction t with
  | zero => simpa using expect_const (FinProb.pi (fun _ : Fin 0 => Q)) 0
  | succ t ih =>
      rw [iid_expect_cons]
      simp_rw [Fin.sum_univ_succ, Fin.cons_zero, Fin.cons_succ, add_sq, expect_add,
        expect_const, expect_const_mul, iid_sum_expect, ih]
      simp only [expect_mul_const, expect_const_mul]
      push_cast
      ring


/-- Select one good tuple with a large fiber of simultaneous witnesses. -/
theorem select_good_fiber {α β : Type*} [Fintype α] [Fintype β]
    (mu : FinProb α) (Q : FinProb β) (A : α → Prop) (B : α → β → Prop)
    (good : β → Prop) (q : ℝ) (hq : 0 < q) (hA : 0 < mu.pr A)
    (h : ∀ x, A x → q ≤ Q.pr (fun z => good z ∧ B x z)) :
    ∃ z, good z ∧ q * mu.pr A / 2 ≤ mu.pr (fun x => A x ∧ B x z) := by
  let fiber := fun z => mu.pr (fun x => A x ∧ B x z)
  have hmass : q * mu.pr A ≤ Q.expect (fun z => if good z then fiber z else 0) := by
    have hlower : q * mu.pr A ≤
        ∑ x, if A x then mu.w x * Q.pr (fun z => good z ∧ B x z) else 0 := by
      unfold FinProb.pr
      rw [Finset.mul_sum]
      apply Finset.sum_le_sum
      intro x hx
      by_cases hAx : A x
      · simp only [hAx, if_true]
        exact le_trans (by ring_nf; exact le_refl _) (mul_le_mul_of_nonneg_left (h x hAx) (mu.nonneg x))
      · simp [hAx]
    calc
      _ ≤ _ := hlower
      _ = Q.expect (fun z => if good z then fiber z else 0) := by
        have hleft (x : α) :
            (if A x then mu.w x * Q.pr (fun z => good z ∧ B x z) else 0) =
              ∑ z, Q.w z * (if good z then (if A x ∧ B x z then mu.w x else 0) else 0) := by
          by_cases hAx : A x
          · simp only [hAx, true_and, if_true]
            unfold FinProb.pr
            rw [Finset.mul_sum]
            apply Finset.sum_congr rfl
            intro z hz
            by_cases hg : good z <;> by_cases hBx : B x z <;>
              simp [hg, hBx, mul_comm]
          · simp [hAx]
        simp_rw [hleft]
        rw [Finset.sum_comm]
        unfold FinProb.expect fiber FinProb.pr
        apply Finset.sum_congr rfl
        intro z hz
        by_cases hg : good z
        · simp only [hg, if_true]
          rw [Finset.mul_sum]
          apply Finset.sum_congr rfl
          intro x hx
          by_cases ha : A x ∧ B x z <;> simp [ha]
        · simp [hg]
  by_contra! hnone
  have hqA : 0 < q * mu.pr A := mul_pos hq hA
  have hupper : Q.expect (fun z => if good z then fiber z else 0) ≤ q * mu.pr A / 2 := by
    calc
      _ ≤ Q.expect (fun _ => q * mu.pr A / 2) := expect_mono Q (by
        intro z
        by_cases hg : good z
        · simp only [hg, if_true]
          exact (hnone z hg).le
        · simp only [hg, if_false]
          positivity)
      _ = _ := expect_const Q _
  linarith

theorem iid_conditioned_event {α : Type*} [Fintype α] (Q : FinProb α)
    (B : α → Prop) (hB : 0 < Q.pr B) (t : ℕ) (good : (Fin t → α) → Prop) :
    (FinProb.pi (fun _ : Fin t => Q)).pr (fun w => good w ∧ ∀ j, B (w j)) =
      (Q.pr B)^t * (FinProb.pi (fun _ : Fin t => Q.cond B hB)).pr good := by
  have hw (w : Fin t → α) :
      (Q.pr B)^t * (FinProb.pi (fun _ : Fin t => Q.cond B hB)).w w =
        if ∀ j, B (w j) then (FinProb.pi (fun _ : Fin t => Q)).w w else 0 := by
    by_cases hall : ∀ j, B (w j)
    · simp only [FinProb.pi, FinProb.cond, hall, if_true]
      rw [Finset.prod_div_distrib]
      simp [hB.ne', mul_div_cancel₀]
    · obtain ⟨j, hj⟩ := not_forall.mp hall
      have hz : (FinProb.pi (fun _ : Fin t => Q.cond B hB)).w w = 0 := by
        apply Finset.prod_eq_zero (Finset.mem_univ j)
        simp [FinProb.cond, hj]
      simp [hall, hz]
  unfold FinProb.pr
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro w hwmem
  by_cases hg : good w
  · simp only [hg, true_and, if_true]
    exact (hw w).symm
  · simp [hg]


theorem expect_square_sub {Ω : Type*} [Fintype Ω] (Q : FinProb Ω) (f : Ω → ℝ) (a : ℝ) :
    Q.expect (fun x => (f x - a)^2) = Q.expect (fun x => (f x)^2) - 2*a*Q.expect f + a^2 := by
  calc
    _ = Q.expect (fun x => (f x)^2 - 2*a*f x + a^2) := by
      congr 1; funext x; ring
    _ = _ := by rw [expect_add, expect_sub, expect_const_mul, expect_const]

theorem variance_le_tail {Ω : Type*} [Fintype Ω] (Q : FinProb Ω) (f : Ω → ℝ)
    (hf : ∀ x, 0 ≤ f x ∧ f x ≤ 1) (eps eta : ℝ) (heps : 0 ≤ eps)
    (htail : Q.pr (fun x => eps < |f x - 1/2|) ≤ eta) :
    Q.expect (fun x => (f x - Q.expect f)^2) ≤ eps^2 + eta := by
  have hpoint (x : Ω) : (f x - 1/2)^2 ≤ eps^2 +
      (if eps < |f x - 1/2| then (1 : ℝ) else 0) := by
    by_cases h : eps < |f x - 1/2|
    · simp only [h, if_true]
      have hx := hf x
      have hs := sq_nonneg eps
      nlinarith
    · simp only [h, if_false, add_zero]
      have ha : |f x - 1/2| ≤ eps := le_of_not_gt h
      simpa only [sq_abs] using (sq_le_sq₀ (abs_nonneg _) heps).2 ha
  have hshift : Q.expect (fun x => (f x - 1/2)^2) ≤ eps^2 + eta := by
    calc
      _ ≤ Q.expect (fun x => eps^2 +
          (if eps < |f x - 1/2| then (1 : ℝ) else 0)) := expect_mono Q hpoint
      _ = eps^2 + Q.pr (fun x => eps < |f x - 1/2|) := by
        rw [expect_add, expect_const]
        congr 1
        simp [FinProb.expect, FinProb.pr, mul_ite]
      _ ≤ _ := add_le_add le_rfl htail
  rw [expect_square_sub] at hshift ⊢
  nlinarith [sq_nonneg (Q.expect f - 1/2)]

theorem expect_abs_sq_le {Ω : Type*} [Fintype Ω] (Q : FinProb Ω) (f : Ω → ℝ) :
    (Q.expect (fun x => |f x|))^2 ≤ Q.expect (fun x => (f x)^2) := by
  have h := Finset.sum_sq_le_sum_mul_sum_of_sq_le_mul (R := ℝ) Finset.univ
    (r := fun x => Q.w x * |f x|) (f := Q.w) (g := fun x => Q.w x * (f x)^2)
    (fun x _ => Q.nonneg x)
    (fun x _ => mul_nonneg (Q.nonneg x) (sq_nonneg _))
    (fun x _ => by rw [mul_pow, sq_abs]; nlinarith)
  simpa [FinProb.expect, Q.sum_eq_one] using h

theorem pr_good_of_expect_le {Ω : Type*} [Fintype Ω] (Q : FinProb Ω)
    (f : Ω → ℝ) (hf : ∀ x, 0 ≤ f x) (C : ℝ) (hC : 0 < C)
    (hm : Q.expect f ≤ C) : 1/2 ≤ Q.pr (fun x => f x ≤ 2*C) := by
  let bad := fun x => 2*C < f x
  have hp : 2*C * Q.pr bad ≤ Q.expect f := by
    unfold FinProb.pr FinProb.expect
    rw [Finset.mul_sum]
    apply Finset.sum_le_sum
    intro x hx
    by_cases h : bad x
    · simp only [h, if_true]
      exact le_trans (by ring_nf; exact le_refl _) (mul_le_mul_of_nonneg_left h.le (Q.nonneg x))
    · simp only [h, if_false, mul_zero]
      exact mul_nonneg (Q.nonneg x) (hf x)
  have hcomplement : Q.pr (fun x => f x ≤ 2*C) + Q.pr bad = 1 := by
    unfold FinProb.pr
    rw [← Finset.sum_add_distrib, ← Q.sum_eq_one]
    apply Finset.sum_congr rfl
    intro x hx
    by_cases h : bad x <;> simp_all [bad]
  nlinarith


noncomputable def testSum {N : ℕ} {α : Type*} {t : ℕ} (lam : Law N)
    (K : α → Fin N → ℝ) (z : Fin t → α) (y : Fin N) : ℝ :=
  ∑ j, (K (z j) y - lam.expect (K (z j)))

noncomputable def testCov {N : ℕ} {α : Type*} (lam : Law N)
    (K : α → Fin N → ℝ) (J : Fin N → Fin N → ℝ) (x : Fin N) (w : α) : ℝ :=
  lam.expect (fun y => K w y * J x y) - lam.expect (K w) * lam.expect (J x)

theorem testSum_mean {N : ℕ} {α : Type*} {t : ℕ} (lam : Law N)
    (K : α → Fin N → ℝ) (z : Fin t → α) : lam.expect (testSum lam K z) = 0 := by
  unfold testSum
  rw [expect_sum]
  simp_rw [expect_sub, expect_const, sub_self]
  simp

theorem testSum_cov {N : ℕ} {α : Type*} {t : ℕ} (lam : Law N)
    (K : α → Fin N → ℝ) (J : Fin N → Fin N → ℝ) (x : Fin N) (z : Fin t → α) :
    lam.expect (fun y => J x y * testSum lam K z y) = ∑ j, testCov lam K J x (z j) := by
  simp only [testSum, Finset.mul_sum]
  rw [expect_sum]
  apply Finset.sum_congr rfl
  intro j hj
  simp only [mul_sub, expect_sub, expect_mul_const, testCov]
  congr 1
  · unfold FinProb.expect
    apply Finset.sum_congr rfl
    intro y hy
    ring
  · ring

private theorem pr_nonneg {Ω : Type*} [Fintype Ω] (Q : FinProb Ω) (A : Ω → Prop) :
    0 ≤ Q.pr A := by
  unfold FinProb.pr
  exact Finset.sum_nonneg fun x _ => by split_ifs <;> simp [Q.nonneg]

private theorem pr_le_one {Ω : Type*} [Fintype Ω] (Q : FinProb Ω) (A : Ω → Prop) :
    Q.pr A ≤ 1 := by
  unfold FinProb.pr
  rw [← Q.sum_eq_one]
  exact Finset.sum_le_sum fun x _ => by split_ifs <;> simp [Q.nonneg]

private theorem expect_indicator {Ω : Type*} [Fintype Ω] (Q : FinProb Ω) (A : Ω → Prop) :
    Q.expect (fun x => if A x then (1 : ℝ) else 0) = Q.pr A := by
  simp [FinProb.expect, FinProb.pr, mul_ite]

/-- A bad pair event of mass above `2 rho` has at least `rho` mass of large fibers. -/
theorem large_fibers {α β : Type*} [Fintype α] [Fintype β]
    (mu : FinProb α) (Q : FinProb β) (B : α → β → Prop) (rho : ℝ) (hrho : 0 ≤ rho)
    (hbad : 2*rho < mu.expect (fun x => Q.pr (B x))) :
    rho < mu.pr (fun x => rho ≤ Q.pr (B x)) := by
  let A := fun x => rho ≤ Q.pr (B x)
  have hupper : mu.expect (fun x => Q.pr (B x)) ≤ rho + mu.pr A := by
    calc
      _ ≤ mu.expect (fun x => rho + if A x then (1 : ℝ) else 0) := expect_mono mu (by
        intro x
        by_cases h : A x
        · simp only [h, if_true]
          linarith [pr_le_one Q (B x)]
        · simp only [h, if_false, add_zero]
          exact (lt_of_not_ge h).le)
      _ = _ := by rw [expect_add, expect_const, expect_indicator]
  change rho < mu.pr A
  linarith

private theorem cond_expect_lower {Ω : Type*} [Fintype Ω] (Q : FinProb Ω)
    (A : Ω → Prop) (hA : 0 < Q.pr A) (f : Ω → ℝ) (d : ℝ)
    (h : ∀ x, A x → d ≤ f x) : d ≤ (Q.cond A hA).expect f := by
  have hsum : (Q.cond A hA).expect (fun _ => d) ≤ (Q.cond A hA).expect f := by
    unfold FinProb.expect
    apply Finset.sum_le_sum
    intro x hx
    by_cases ha : A x
    · exact mul_le_mul_of_nonneg_left (h x ha) ((Q.cond A hA).nonneg x)
    · simp [FinProb.cond, ha]
  simpa [expect_const] using hsum

/-- Finite dependent sampling and Fubini reduce a signed covariance tail to one fixed signed test. -/
theorem covariance_amplification {N : ℕ} {α : Type*} [Fintype α]
    (mu : Law N) (Q : FinProb α) (lam : Law N)
    (K : α → Fin N → ℝ) (J : Fin N → Fin N → ℝ)
    (t : ℕ) (ht : 0 < t) (rho delta R : ℝ) (hrho : 0 < rho)
    (hR : R < (t : ℝ)*delta)
    (hnorm : ∀ (B : α → Prop) (hB : 0 < Q.pr B), rho ≤ Q.pr B →
      (FinProb.pi (fun _ : Fin t => Q.cond B hB)).expect
        (fun z => lam.expect (fun y => (testSum lam K z y)^2)) ≤ 2*t)
    (htest : ∀ (A : Fin N → Prop) (hA : 0 < mu.pr A), rho^(t+1)/4 ≤ mu.pr A →
      ∀ z : Fin t → α, lam.expect (fun y => (testSum lam K z y)^2) ≤ 4*t →
      |(mu.cond A hA).expect (fun x => lam.expect (fun y => J x y * testSum lam K z y))| ≤ R) :
    mu.expect (fun x => Q.pr (fun w => delta < testCov lam K J x w)) ≤ 2*rho := by
  by_contra hnot
  have hbad : 2*rho < mu.expect (fun x => Q.pr (fun w => delta < testCov lam K J x w)) :=
    lt_of_not_ge hnot
  let B := fun x w => delta < testCov lam K J x w
  let A := fun x => rho ≤ Q.pr (B x)
  let raw := FinProb.pi (fun _ : Fin t => Q)
  let norm := fun z : Fin t → α => lam.expect (fun y => (testSum lam K z y)^2)
  let good := fun z => norm z ≤ 4*t
  have hA : rho < mu.pr A := large_fibers mu Q B rho hrho.le hbad
  have hApos : 0 < mu.pr A := lt_trans hrho hA
  have hraw (x : Fin N) (hx : A x) :
      rho^t/2 ≤ raw.pr (fun z => good z ∧ ∀ j, B x (z j)) := by
    have hp : 0 < Q.pr (B x) := lt_of_lt_of_le hrho hx
    let cond := FinProb.pi (fun _ : Fin t => Q.cond (B x) hp)
    have hmoment : cond.expect norm ≤ 2*t := hnorm (B x) hp hx
    have hgood : 1/2 ≤ cond.pr good := by
      have h := pr_good_of_expect_le cond norm
        (by intro z; exact Finset.sum_nonneg fun y _ => mul_nonneg (lam.nonneg y) (sq_nonneg _))
        (2*t) (by exact_mod_cast (show 0 < 2*t by omega)) hmoment
      simpa only [good, norm, ← mul_assoc, show (2 : ℝ) * 2 = 4 by norm_num] using h
    rw [iid_conditioned_event Q (B x) hp]
    have hpow : rho^t ≤ (Q.pr (B x))^t := pow_le_pow_left₀ hrho.le hx _
    calc
      rho^t/2 = rho^t*(1/2) := by ring
      _ ≤ (Q.pr (B x))^t * cond.pr good :=
        mul_le_mul hpow hgood (by norm_num) (pow_nonneg (pr_nonneg Q _) _)
      _ = _ := rfl
  obtain ⟨z, hzgood, hzmass⟩ := select_good_fiber mu raw A
    (fun x z => ∀ j, B x (z j)) good (rho^t/2) (by positivity) hApos hraw
  let A0 := fun x => A x ∧ ∀ j, B x (z j)
  have hmass : rho^(t+1)/4 ≤ mu.pr A0 := by
    have hmul := mul_le_mul_of_nonneg_left hA.le (pow_nonneg hrho.le t)
    rw [pow_succ]
    dsimp [A0] at *
    nlinarith
  have hmasspos : 0 < mu.pr A0 := lt_of_lt_of_le (by positivity) hmass
  have htestz := htest A0 hmasspos hmass z hzgood
  have hforced : (t : ℝ)*delta ≤ (mu.cond A0 hmasspos).expect
      (fun x => lam.expect (fun y => J x y * testSum lam K z y)) := by
    apply cond_expect_lower mu A0 hmasspos
    intro x hx
    rw [testSum_cov]
    calc
      (t : ℝ)*delta = ∑ _ : Fin t, delta := by simp
      _ ≤ ∑ j, testCov lam K J x (z j) :=
        Finset.sum_le_sum fun j _ => (hx.2 j).le
  have hforcedAbs := le_trans hforced (le_abs_self _)
  linarith


theorem expect_interval {Ω : Type*} [Fintype Ω] (Q : FinProb Ω) (f : Ω → ℝ)
    (hf : ∀ x, 0 ≤ f x ∧ f x ≤ 1) : 0 ≤ Q.expect f ∧ Q.expect f ≤ 1 := by
  constructor
  · simpa [expect_const] using expect_mono Q (f := fun _ => 0) (g := f) (fun x => (hf x).1)
  · simpa [expect_const] using expect_mono Q (f := f) (g := fun _ => 1) (fun x => (hf x).2)

theorem centered_iid_moment {N : ℕ} {α : Type*} [Fintype α]
    (Q : FinProb α) (lam : Law N) (K : α → Fin N → ℝ)
    (hK : ∀ w y, 0 ≤ K w y ∧ K w y ≤ 1) (t : ℕ) (V : ℝ) (hV : 0 ≤ V)
    (hvar : lam.expect (fun y =>
      (Q.expect (fun w => K w y) - lam.expect (fun u => Q.expect (fun w => K w u)))^2) ≤ V) :
    (FinProb.pi (fun _ : Fin t => Q)).expect
      (fun z => lam.expect (fun y => (testSum lam K z y)^2)) ≤ t + (t : ℝ)^2 * V := by
  let f := fun y w => K w y - lam.expect (K w)
  let m := fun y => Q.expect (fun w => K w y)
  have hswap : Q.expect (fun w => lam.expect (K w)) = lam.expect m := by
    simp only [FinProb.expect, m, Finset.mul_sum]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro y hy
    apply Finset.sum_congr rfl
    intro w hw
    ring
  have hm (y : Fin N) : Q.expect (f y) = m y - lam.expect m := by
    dsimp [f, m]
    rw [expect_sub, hswap]
  have h2 (y : Fin N) : Q.expect (fun w => (f y w)^2) ≤ 1 := by
    have hpoint (w : α) : (f y w)^2 ≤ 1 := by
      have hr := hK w y
      have hmean := expect_interval lam (K w) (hK w)
      dsimp [f]
      have hproduct := mul_nonneg
        (show 0 ≤ 1 - (K w y - lam.expect (K w)) by linarith)
        (show 0 ≤ 1 + (K w y - lam.expect (K w)) by linarith)
      nlinarith
    simpa [expect_const] using expect_mono Q hpoint
  have hcoeff : 0 ≤ (t : ℝ)^2 - t := by
    cases t with
    | zero => norm_num
    | succ t => push_cast; nlinarith [Nat.cast_nonneg (α := ℝ) t]
  have hmoment : (FinProb.pi (fun _ : Fin t => Q)).expect
      (fun z => lam.expect (fun y => (testSum lam K z y)^2)) =
      lam.expect (fun y => (t : ℝ)*Q.expect (fun w => (f y w)^2) +
        ((t : ℝ)^2-t)*(m y-lam.expect m)^2) := by
    have hcomm : (FinProb.pi (fun _ : Fin t => Q)).expect
        (fun z => lam.expect (fun y => (testSum lam K z y)^2)) =
        lam.expect (fun y => (FinProb.pi (fun _ : Fin t => Q)).expect
          (fun z => (testSum lam K z y)^2)) := by
      unfold FinProb.expect
      simp_rw [Finset.mul_sum]
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro y hy
      apply Finset.sum_congr rfl
      intro z hz
      ring
    rw [hcomm]
    congr 1
    funext y
    have h := iid_sum_square Q (f y) t
    simpa [testSum, f, hm y] using h
  rw [hmoment]
  calc
    _ ≤ lam.expect (fun y => (t : ℝ) + ((t : ℝ)^2-t)*(m y-lam.expect m)^2) :=
      expect_mono lam (fun y => add_le_add
        (by simpa using mul_le_mul_of_nonneg_left (h2 y) (Nat.cast_nonneg t)) le_rfl)
    _ = (t : ℝ) + ((t : ℝ)^2-t)*lam.expect (fun y => (m y-lam.expect m)^2) := by
      rw [expect_add, expect_const, expect_const_mul]
    _ ≤ (t : ℝ) + ((t : ℝ)^2-t)*V :=
      add_le_add le_rfl (mul_le_mul_of_nonneg_left hvar hcoeff)
    _ ≤ (t : ℝ) + (t : ℝ)^2*V := by nlinarith [Nat.cast_nonneg (α := ℝ) t]


theorem cond_supported {N : ℕ} (mu : Law N) (A : Fin N → Prop) (hA : 0 < mu.pr A)
    {X : Finset (Fin N)} (hX : mu.SupportedIn X) : Law.SupportedIn (mu.cond A hA) X := by
  intro x hx
  simp [FinProb.cond, hX x hx]

theorem cond_width {N : ℕ} (mu : Law N) (A : Fin N → Prop) (hA : 0 < mu.pr A)
    (w d : ℝ) (hW : mu.WidthLE w) (hMass : Real.exp (-d) ≤ mu.pr A) :
    Law.WidthLE (mu.cond A hA) (w+d) := by
  intro x
  by_cases hx : A x
  · change (if A x then mu.w x else 0) / mu.pr A ≤ _
    rw [if_pos hx]
    calc
      mu.w x / mu.pr A ≤ mu.w x / Real.exp (-d) :=
        div_le_div_of_nonneg_left (mu.nonneg x) (Real.exp_pos _) hMass
      _ ≤ (Real.exp w / N) / Real.exp (-d) :=
        div_le_div_of_nonneg_right (hW x) (Real.exp_nonneg _)
      _ = Real.exp (w+d)/N := by
        rw [Real.exp_neg, div_inv_eq_mul, div_mul_eq_mul_div, ← Real.exp_add]
  · simp [FinProb.cond, hx]
    positivity

private theorem tilt_cap {N : ℕ} (lam : Law N) (f : Fin N → ℝ) (L T : ℝ)
    (hL : 0 < L) (hf : ∀ y, L ≤ f y) (hbound : ∀ y, f y ≤ L+T) :
    ∀ y, f y / lam.expect f ≤ (L+T)/L := by
  have hZ : L ≤ lam.expect f := by
    simpa [expect_const] using expect_mono lam (f := fun _ => L) hf
  intro y
  calc
    _ ≤ f y / L := div_le_div_of_nonneg_left (le_trans hL.le (hf y)) hL hZ
    _ ≤ _ := div_le_div_of_nonneg_right (hbound y) hL.le

theorem centered_test_bound_of_norm {N : ℕ} {E : Fin N → Fin N → Prop}
    {X Y : Finset (Fin N)} {wX wY err s : ℝ}
    (hdisc : DiscOne E X Y wX wY err) (G : Colour) (mu lam : Law N)
    (hmuX : mu.SupportedIn X) (hlamY : lam.SupportedIn Y) (hmuW : mu.WidthLE wX)
    (hlamW : lam.WidthLE s) (S : Fin N → ℝ) (t : ℕ) (ht : 0 < t) (herr : 0 ≤ err)
    (hmean : lam.expect S = 0) (hbound : ∀ y, |S y| ≤ t)
    (hnorm : lam.expect (fun y => (S y)^2) ≤ 4*t)
    (hwidth : s + Real.log (1 + Real.sqrt t) ≤ wY) :
    |mu.expect (fun x => lam.expect (fun y => hitInd9 E G x y * S y))| ≤
      6 * err * Real.sqrt t := by
  let L := Real.sqrt (t : ℝ)
  have htR : (0 : ℝ) < t := by exact_mod_cast ht
  have hL : 0 < L := Real.sqrt_pos.2 htR
  have hLsq : L^2 = t := Real.sq_sqrt htR.le
  have hratio : (L + t)/L = 1 + L := by
    apply (div_eq_iff hL.ne').2
    nlinarith
  have hcap : 1 + L ≤ Real.exp (wY-s) := by
    have hh : Real.log (1+L) ≤ wY-s := by dsimp [L] at *; linarith
    have hh' := Real.exp_le_exp.mpr hh
    rwa [Real.exp_log (by positivity)] at hh'
  have hfp : ∀ y, L ≤ L+max (S y) 0 := by intro y; have := le_max_right (S y) 0; linarith
  have hfm : ∀ y, L ≤ L+max (-S y) 0 := by intro y; have := le_max_right (-S y) 0; linarith
  have hfpUpper : ∀ y, L+max (S y) 0 ≤ L+t := by
    intro y
    have hb := abs_le.mp (hbound y)
    have hmax : max (S y) 0 ≤ t := max_le hb.2 htR.le
    linarith
  have hfmUpper : ∀ y, L+max (-S y) 0 ≤ L+t := by
    intro y
    have hb := abs_le.mp (hbound y)
    have hmax : max (-S y) 0 ≤ t := max_le (by linarith) htR.le
    linarith
  have hp : ∀ y, 0 ≤ L+max (S y) 0 := fun y => le_trans hL.le (hfp y)
  have hm : ∀ y, 0 ≤ L+max (-S y) 0 := fun y => le_trans hL.le (hfm y)
  have hpZ : 0 < lam.expect (fun y => L+max (S y) 0) := by
    have h := expect_mono lam (f := fun _ => L) hfp
    rw [expect_const] at h
    exact lt_of_lt_of_le hL h
  have hmZ : 0 < lam.expect (fun y => L+max (-S y) 0) := by
    have h := expect_mono lam (f := fun _ => L) hfm
    rw [expect_const] at h
    exact lt_of_lt_of_le hL h
  have hpW : (tilt lam (fun y => L+max (S y) 0) hp hpZ).WidthLE wY := by
    apply tilt_width lam _ hp hpZ hlamW
    intro y
    calc
      _ ≤ (L+t)/L := tilt_cap lam _ L t hL hfp hfpUpper y
      _ = 1+L := hratio
      _ ≤ _ := hcap
  have hmW : (tilt lam (fun y => L+max (-S y) 0) hm hmZ).WidthLE wY := by
    apply tilt_width lam _ hm hmZ hlamW
    intro y
    calc
      _ ≤ (L+t)/L := tilt_cap lam _ L t hL hfm hfmUpper y
      _ = 1+L := hratio
      _ ≤ _ := hcap
  have htest := centered_test_bound hdisc G mu lam hmuX hlamY hmuW S L hL hmean hpW hmW
  have hL1sq := expect_abs_sq_le lam S
  have hL1pos : 0 ≤ lam.expect (fun y => |S y|) :=
    Finset.sum_nonneg fun y _ => mul_nonneg (lam.nonneg y) (abs_nonneg _)
  have hL1 : lam.expect (fun y => |S y|) ≤ 2*L := by nlinarith
  have hZ : lam.expect (fun y => L+max (S y) 0) ≤ 3*L := by
    calc
      _ ≤ lam.expect (fun y => L+|S y|) := expect_mono lam (by
        intro y
        exact add_le_add le_rfl (max_le (le_abs_self _) (abs_nonneg _)))
      _ = L + lam.expect (fun y => |S y|) := by rw [expect_add, expect_const]
      _ ≤ _ := by linarith
  calc
    _ ≤ 2*err*lam.expect (fun y => L+max (S y) 0) := htest
    _ ≤ 2*err*(3*L) := mul_le_mul_of_nonneg_left hZ (by positivity)
    _ = _ := by dsimp [L]; ring


theorem testSum_abs_le {N : ℕ} {α : Type*} {t : ℕ} (lam : Law N)
    (K : α → Fin N → ℝ) (hK : ∀ w y, 0 ≤ K w y ∧ K w y ≤ 1) (z : Fin t → α) :
    ∀ y, |testSum lam K z y| ≤ t := by
  intro y
  have hpoint (j : Fin t) : |K (z j) y - lam.expect (K (z j))| ≤ 1 := by
    have hb := hK (z j) y
    have hm := expect_interval lam (K (z j)) (hK (z j))
    rw [abs_le]
    constructor <;> linarith
  calc
    _ ≤ ∑ j, |K (z j) y - lam.expect (K (z j))| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _ : Fin t, (1 : ℝ) := Finset.sum_le_sum fun j _ => hpoint j
    _ = _ := by simp

theorem fixed_law_signed_tail {N : ℕ} {E : Fin N → Fin N → Prop}
    {X Y : Finset (Fin N)} {wX wY err s w d delta eta : ℝ}
    (hdisc : DiscOne E X Y wX wY err) (G H : Colour) (mu beta lam : Law N)
    (hmuX : mu.SupportedIn X) (hbetaX : beta.SupportedIn X) (hlamY : lam.SupportedIn Y)
    (hmuW : mu.WidthLE w) (hbetaW : beta.WidthLE w) (hlamW : lam.WidthLE s)
    (t : ℕ) (ht : 0 < t) (herr : 0 ≤ err) (heta : 0 ≤ eta)
    (hfirstCond : w+d ≤ wX) (hfirstTarget : w+Real.log 4+(t+1)*d ≤ wX)
    (hsecond : s+Real.log (1+Real.sqrt t) ≤ wY)
    (hmoment : (t : ℝ)*((2*err)^2+eta) ≤ 1)
    (hgap : 6*err*Real.sqrt t < (t : ℝ)*delta)
    (hreverse : ∀ sigma : Law N, sigma.SupportedIn X → sigma.WidthLE wX →
      lam.pr (fun y => 2*err < |colDeg E G sigma y-1/2|) ≤ eta) :
    mu.expect (fun x => beta.pr (fun a => delta <
      testCov lam (hitInd9 E G) (hitInd9 E H) x a)) ≤ 2*Real.exp (-d) := by
  let K := hitInd9 E G
  let J := hitInd9 E H
  have hK : ∀ a y, 0 ≤ K a y ∧ K a y ≤ 1 := by
    intro a y
    dsimp [K, hitInd9]
    split_ifs <;> norm_num
  apply covariance_amplification mu beta lam K J t ht (Real.exp (-d)) delta
    (6*err*Real.sqrt t) (Real.exp_pos _) hgap
  · intro B hB hMass
    let sigma : Law N := beta.cond B hB
    have hsigmaX : sigma.SupportedIn X := cond_supported beta B hB hbetaX
    have hsigmaW : sigma.WidthLE wX :=
      Law.WidthLE.mono (cond_width beta B hB w d hbetaW hMass) hfirstCond
    have htail := hreverse sigma hsigmaX hsigmaW
    have hvar := variance_le_tail lam (colDeg E G sigma)
      (fun y => expect_interval sigma (fun a => K a y) (fun a => hK a y))
      (2*err) eta (by positivity) htail
    let V := (2*err)^2+eta
    have hV : 0 ≤ V := by dsimp [V]; positivity
    have hvar' : lam.expect (fun y =>
        (sigma.expect (fun a => K a y)-lam.expect (fun u => sigma.expect (fun a => K a u)))^2) ≤ V := hvar
    have hbound := centered_iid_moment sigma lam K hK t V hV hvar'
    change (FinProb.pi (fun _ : Fin t => sigma)).expect
      (fun z => lam.expect (fun y => (testSum lam K z y)^2)) ≤ 2*t
    have hmult : (t : ℝ)^2*V ≤ t := by
      have h := mul_le_mul_of_nonneg_left hmoment (Nat.cast_nonneg t : (0 : ℝ) ≤ t)
      dsimp [V] at *
      nlinarith
    linarith
  · intro A hA hMass z hnorm
    let D := Real.log 4 + (t+1)*d
    have hExp : Real.exp (-D) = (Real.exp (-d))^(t+1)/4 := by
      rw [show -D = ((t+1 : ℕ) : ℝ)*(-d)-Real.log 4 by dsimp [D]; push_cast; ring]
      rw [Real.exp_sub, Real.exp_nat_mul, Real.exp_log (by norm_num : (0 : ℝ) < 4)]
    have hMass' : Real.exp (-D) ≤ mu.pr A := by rw [hExp]; exact hMass
    let target : Law N := mu.cond A hA
    have htargetX : target.SupportedIn X := cond_supported mu A hA hmuX
    have htargetW : target.WidthLE wX :=
      Law.WidthLE.mono (cond_width mu A hA w D hmuW hMass')
        (by dsimp [D]; linarith [hfirstTarget])
    exact centered_test_bound_of_norm hdisc H target lam htargetX hlamY htargetW hlamW
      (testSum lam K z) t ht herr (testSum_mean lam K z) (testSum_abs_le lam K hK z) hnorm hsecond


theorem hitInd_not {N : ℕ} (E : Fin N → Fin N → Prop) (G : Colour) (x y : Fin N) :
    hitInd9 E (!G) x y = 1-hitInd9 E G x y := by
  cases G <;> by_cases h : E x y <;> simp [hitInd9, Hits, h]

theorem testCov_not {N : ℕ} (E : Fin N → Fin N → Prop) (G : Colour)
    (lam : Law N) (x a : Fin N) :
    testCov lam (hitInd9 E G) (hitInd9 E (!G)) x a =
      -testCov lam (hitInd9 E G) (hitInd9 E G) x a := by
  have hfun : hitInd9 E (!G) x = fun y => 1-hitInd9 E G x y :=
    funext (fun y => hitInd_not E G x y)
  unfold testCov
  rw [hfun]
  simp only [mul_sub, mul_one, expect_sub, expect_const]
  ring

theorem fixed_law_abs_tail {N : ℕ} {E : Fin N → Fin N → Prop}
    {X Y : Finset (Fin N)} {wX wY err s w d delta eta : ℝ}
    (hdisc : DiscOne E X Y wX wY err) (G : Colour) (mu beta lam : Law N)
    (hmuX : mu.SupportedIn X) (hbetaX : beta.SupportedIn X) (hlamY : lam.SupportedIn Y)
    (hmuW : mu.WidthLE w) (hbetaW : beta.WidthLE w) (hlamW : lam.WidthLE s)
    (t : ℕ) (ht : 0 < t) (herr : 0 ≤ err) (heta : 0 ≤ eta)
    (hfirstCond : w+d ≤ wX) (hfirstTarget : w+Real.log 4+(t+1)*d ≤ wX)
    (hsecond : s+Real.log (1+Real.sqrt t) ≤ wY)
    (hmoment : (t : ℝ)*((2*err)^2+eta) ≤ 1)
    (hgap : 6*err*Real.sqrt t < (t : ℝ)*delta)
    (hreverse : ∀ sigma : Law N, sigma.SupportedIn X → sigma.WidthLE wX →
      lam.pr (fun y => 2*err < |colDeg E G sigma y-1/2|) ≤ eta) :
    mu.expect (fun x => beta.pr (fun a => delta <
      |testCov lam (hitInd9 E G) (hitInd9 E G) x a|)) ≤ 4*Real.exp (-d) := by
  let cov := testCov lam (hitInd9 E G) (hitInd9 E G)
  have hp := fixed_law_signed_tail hdisc G G mu beta lam hmuX hbetaX hlamY hmuW hbetaW
    hlamW t ht herr heta hfirstCond hfirstTarget hsecond hmoment hgap hreverse
  have hm := fixed_law_signed_tail hdisc G (!G) mu beta lam hmuX hbetaX hlamY hmuW hbetaW
    hlamW t ht herr heta hfirstCond hfirstTarget hsecond hmoment hgap hreverse
  simp only [testCov_not] at hm
  have hpoint (x : Fin N) : beta.pr (fun a => delta < |cov x a|) ≤
      beta.pr (fun a => delta < cov x a) + beta.pr (fun a => delta < -cov x a) := by
    unfold FinProb.pr
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_le_sum
    intro a ha
    by_cases hb : delta < |cov x a|
    · have hor := lt_abs.mp hb
      rcases hor with hpos | hneg
      · simp only [hb, hpos, if_true]
        have hn : 0 ≤ if delta < -cov x a then beta.w a else 0 := by split_ifs <;> simp [beta.nonneg]
        linarith
      · simp only [hb, hneg, if_true]
        have hn : 0 ≤ if delta < cov x a then beta.w a else 0 := by split_ifs <;> simp [beta.nonneg]
        linarith
    · simp only [hb, if_false]
      have h1 : 0 ≤ if delta < cov x a then beta.w a else 0 := by split_ifs <;> simp [beta.nonneg]
      have h2 : 0 ≤ if delta < -cov x a then beta.w a else 0 := by split_ifs <;> simp [beta.nonneg]
      linarith
  calc
    _ ≤ mu.expect (fun x => beta.pr (fun a => delta < cov x a) +
        beta.pr (fun a => delta < -cov x a)) := expect_mono mu hpoint
    _ = _ := expect_add mu _ _
    _ ≤ 2*Real.exp (-d) + 2*Real.exp (-d) := add_le_add hp hm
    _ = _ := by ring


private theorem law_restrict_degree_mass9 {N : ℕ} (E : Fin N → Fin N → Prop) (G : Colour)
    (μ : Law N) (A : Finset (Fin N)) (x : Fin N)
    (hm : 0 < ∑ y ∈ A, μ.w y) :
    (∑ y ∈ A.filter (fun y => Hits E G x y), μ.w y) =
      (∑ y ∈ A, μ.w y) * rowDeg E G x (μ.restrict A hm) := by
  classical
  let m : ℝ := ∑ y ∈ A, μ.w y
  have hm' : 0 < m := hm
  have hdegree : rowDeg E G x (μ.restrict A hm) =
      (∑ y ∈ A.filter (fun y => Hits E G x y), μ.w y) / m := by
    unfold rowDeg
    simp only [Law.restrict]
    have hfilter : Finset.univ.filter (fun y : Fin N => y ∈ A ∧ Hits E G x y) =
        A.filter (fun y => Hits E G x y) := by
      ext y
      simp
    calc
      (∑ y, (if y ∈ A then μ.w y / m else 0) *
          (if Hits E G x y then 1 else 0)) =
          ∑ y, if y ∈ A ∧ Hits E G x y then μ.w y / m else 0 := by
            apply Finset.sum_congr rfl
            intro y hy
            by_cases hA : y ∈ A <;> by_cases hHit : Hits E G x y <;> simp [hA, hHit]
      _ = ∑ y ∈ A.filter (fun y => Hits E G x y), μ.w y / m := by
            rw [← Finset.sum_filter, hfilter]
      _ = (∑ y ∈ A.filter (fun y => Hits E G x y), μ.w y) / m := by
            rw [Finset.sum_div]
  calc
    (∑ y ∈ A.filter (fun y => Hits E G x y), μ.w y) =
        m * ((∑ y ∈ A.filter (fun y => Hits E G x y), μ.w y) / m) := by
          rw [mul_div_cancel₀ _ (ne_of_gt hm')]
    _ = (∑ y ∈ A, μ.w y) * rowDeg E G x (μ.restrict A hm) := by
          rw [hdegree]

private noncomputable def prefixMass9 {P : Params9} {n N : ℕ} {I : IDMap9 P n}
    (E : Fin N → Fin N → Prop) (G : Colour)
    (ω : Outcome9 I N) (base : Law N) (ord : List I.ID) (k : ℕ) : ℝ :=
  ∑ y ∈ hitSet9 E G ω (ord.take k).toFinset, base.w y

private theorem prefixMass_lower9 {P : Params9} {n N : ℕ} {M : TagMix N}
    (S : Setup9 P n N M) (I : IDMap9 P n) (E : Fin N → Fin N → Prop) (G : Colour)
    (ω : Outcome9 I N) (base : Law N) (ord : List I.ID) :
    ∀ k : ℕ, k ≤ ord.length →
      (∀ j c', j < k → ord[j]? = some c' →
        (49 / 100 : ℝ) ≤ rowDeg E G (anc9 ω c') (prefixLaw9 E G ω base ord j)) →
      (49 / 100 : ℝ) ^ k ≤ prefixMass9 E G ω base ord k := by
  classical
  intro k
  induction k with
  | zero =>
      intro hk hprev
      have hmass : prefixMass9 E G ω base ord 0 = 1 := by
        simp [prefixMass9, hitSet9, base.sum_eq_one]
      rw [hmass]
      norm_num
  | succ k ih =>
      intro hk hprev
      have hklen : k < ord.length := by omega
      let c : I.ID := ord[k]
      have hkc : ord[k]? = some c := by simp [c]
      have hcurrent := hprev k c (by omega) hkc
      have hprev' : ∀ j c', j < k → ord[j]? = some c' →
          (49 / 100 : ℝ) ≤ rowDeg E G (anc9 ω c') (prefixLaw9 E G ω base ord j) := by
        intro j c' hj hget
        exact hprev j c' (by omega) hget
      have hmassPrev := ih (by omega) hprev'
      have hmassPrevPos : 0 < prefixMass9 E G ω base ord k := by
        exact lt_of_lt_of_le (by positivity : 0 < (49 / 100 : ℝ) ^ k) hmassPrev
      let A := hitSet9 E G ω (ord.take k).toFinset
      have hmassA : 0 < ∑ y ∈ A, base.w y := by
        change 0 < prefixMass9 E G ω base ord k at hmassPrevPos
        simpa [prefixMass9, A] using hmassPrevPos
      have hprefix : prefixLaw9 E G ω base ord k = base.restrict A hmassPrevPos := by
        change restrictOr9 base A = base.restrict A hmassPrevPos
        unfold restrictOr9
        rw [dif_pos hmassA]
      have htake : ord.take k ++ [ord[k]] = ord.take (k + 1) :=
        List.take_concat_get' ord k hklen
      have hids : (ord.take (k + 1)).toFinset = insert c (ord.take k).toFinset := by
        calc
          (ord.take (k + 1)).toFinset = (ord.take k ++ [ord[k]]).toFinset := by rw [← htake]
          _ = insert c (ord.take k).toFinset := by
            rw [List.toFinset_append]
            simp [c, Finset.union_comm]
      have hset : hitSet9 E G ω (insert c (ord.take k).toFinset) =
          (hitSet9 E G ω (ord.take k).toFinset).filter
            (fun y => Hits E G (anc9 ω c) y) := by
        ext y
        simp [hitSet9, c, Finset.mem_insert, and_left_comm, and_comm, and_assoc]
      have hrec : prefixMass9 E G ω base ord (k + 1) =
          prefixMass9 E G ω base ord k * rowDeg E G (anc9 ω c) (base.restrict A hmassPrevPos) := by
        unfold prefixMass9
        rw [hids]
        rw [hset]
        exact law_restrict_degree_mass9 E G base A (anc9 ω c) hmassA
      rw [hprefix] at hcurrent
      rw [hrec]
      have hdegree_nonneg : 0 ≤ rowDeg E G (anc9 ω c) (base.restrict A hmassPrevPos) :=
        le_trans (by norm_num) hcurrent
      calc
        (49 / 100 : ℝ) ^ (k + 1) = (49 / 100 : ℝ) ^ k * (49 / 100 : ℝ) := by rw [pow_succ]
        _ ≤ prefixMass9 E G ω base ord k *
            rowDeg E G (anc9 ω c) (base.restrict A hmassPrevPos) :=
          mul_le_mul hmassPrev hcurrent (by norm_num) (le_trans (by positivity) hmassPrev)

theorem prefix_width_of_previous_hits9 {P : Params9} {n N : ℕ} {M : TagMix N}
    (S : Setup9 P n N M) (I : IDMap9 P n) (E : Fin N → Fin N → Prop) (G : Colour)
    (omega : Outcome9 I N) (base : Law N) (ord : List I.ID) (k : ℕ)
    (hk : k ≤ ord.length) (w : ℝ) (hW : base.WidthLE w)
    (hprev : ∀ j c, j < k → ord[j]? = some c →
      (49/100 : ℝ) ≤ rowDeg E G (anc9 omega c) (prefixLaw9 E G omega base ord j)) :
    (prefixLaw9 E G omega base ord k).WidthLE (w+k*Real.log (100/49)) := by
  have hmass := prefixMass_lower9 S I E G omega base ord k hk hprev
  have hpos : 0 < prefixMass9 E G omega base ord k :=
    lt_of_lt_of_le (by positivity) hmass
  have hlog := Real.log_le_log (by positivity : (0 : ℝ) < (49/100 : ℝ)^k) hmass
  have hlogrho : Real.log (49/100 : ℝ) = -Real.log (100/49 : ℝ) := by
    rw [show (49/100 : ℝ) = (100/49 : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [Real.log_pow, hlogrho] at hlog
  change 0 < ∑ x ∈ hitSet9 E G omega (ord.take k).toFinset, base.w x at hpos
  unfold prefixLaw9 restrictOr9
  rw [dif_pos hpos]
  exact Law.WidthLE.mono (Law.WidthLE.restrict hW hpos) (by
    change w-Real.log (prefixMass9 E G omega base ord k) ≤ _
    linarith)

theorem pi_resample_subset_expect {iota : Type*} [Fintype iota] [DecidableEq iota]
    {beta : iota → Type*} [∀ i, Fintype (beta i)] (P : ∀ i, FinProb (beta i))
    (s : Finset iota) (f : (∀ i, beta i) → ℝ) :
    (FinProb.pi P).expect f = (FinProb.pi P).expect (fun omega =>
      (FinProb.pi (fun i : {i // i ∈ s} => P i.1)).expect (fun a =>
        f ((Equiv.piEquivPiSubtypeProd (fun i => i ∈ s) beta).symm
          (a, (Equiv.piEquivPiSubtypeProd (fun i => i ∈ s) beta omega).2)))) := by
  let e := Equiv.piEquivPiSubtypeProd (fun i => i ∈ s) beta
  let Ps := FinProb.pi (fun i : {i // i ∈ s} => P i.1)
  let Pc := FinProb.pi (fun i : {i // i ∉ s} => P i.1)
  let G := fun omega => Ps.expect (fun a => f (e.symm (a, (e omega).2)))
  change (FinProb.pi P).expect f = (FinProb.pi P).expect G
  rw [Clock.pi_expect_split_p_clock_r4 P s f, Clock.pi_expect_split_p_clock_r4 P s G]
  change (∑ a, ∑ b, Ps.w a * Pc.w b * f (e.symm (a,b))) =
    ∑ a, ∑ b, Ps.w a * Pc.w b * G (e.symm (a,b))
  simp only [G, e.apply_symm_apply]
  have hleft : (∑ a, ∑ b, Ps.w a * Pc.w b * f (e.symm (a,b))) =
      ∑ b, Pc.w b * Ps.expect (fun a => f (e.symm (a,b))) := by
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro b hb
    unfold FinProb.expect
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro a ha
    ring
  rw [hleft]
  symm
  calc
    _ = ∑ a, Ps.w a * ∑ b, Pc.w b * Ps.expect (fun a => f (e.symm (a,b))) := by
      apply Finset.sum_congr rfl
      intro a ha
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro b hb
      ring
    _ = _ := by rw [← Finset.sum_mul, Ps.sum_eq_one, one_mul]

private theorem eventual_covariance_power_decay {d A eps : ℝ} (hd : 0 < d) (heps : 0 < eps) :
    ∃ n0 : ℕ, ∀ n ≥ n0, A*(n : ℝ)^(-d) < eps := by
  have hlim : Tendsto (fun n : ℕ => A*(n : ℝ)^(-d)) atTop (𝓝 0) := by
    simpa [mul_assoc] using Tendsto.const_mul A
      ((tendsto_rpow_neg_atTop hd).comp tendsto_natCast_atTop_atTop)
  have hsmall : ∀ᶠ n : ℕ in atTop, A*(n : ℝ)^(-d) < eps :=
    hlim.eventually (Iio_mem_nhds heps)
  obtain ⟨n0, hn0⟩ := eventually_atTop.1 hsmall
  exact ⟨n0, fun n hn => hn0 n hn⟩

theorem eventual_covariance_gain_margin9 (P : Params9) (hP : P.Valid) :
    ∃ n0 : ℕ, ∀ n ≥ n0,
      12*P.bStar n < P.aStar n * (n : ℝ)^(-(2*(P.χ : ℝ))) * (n : ℝ)^(4*(P.χ : ℝ)) := by
  rcases hP with ⟨hx, hh, hwidth, hsigma, hchi, hgap, hcase⟩
  have hchiR : (0 : ℝ) < P.χ := by exact_mod_cast hchi.1
  have hgapR : (P.hPlus : ℝ)-(P.hMinus : ℝ) < (P.χ : ℝ)/10 := by exact_mod_cast hgap
  let d := 2*(P.χ : ℝ)-((P.hPlus : ℝ)-(P.hMinus : ℝ))
  have hd : 0 < d := by dsimp [d]; linarith
  obtain ⟨n0, hsmall⟩ := eventual_covariance_power_decay
    (d := d) (A := 24) (eps := 1) hd (by norm_num)
  refine ⟨max 1 n0, ?_⟩
  intro n hn
  have hn1 : 1 ≤ n := le_trans (le_max_left 1 n0) hn
  have hn0 : n0 ≤ n := le_trans (le_max_right 1 n0) hn
  have hnR : (0 : ℝ) < n := by exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one hn1)
  have hs := hsmall n hn0
  have hratio : (n : ℝ)^(-d) = P.bStar n / (n : ℝ)^(-(P.hPlus : ℝ)+2*(P.χ : ℝ)) := by
    dsimp [Params9.bStar]
    rw [← Real.rpow_sub hnR]
    congr 1
    dsimp [d]
    ring
  rw [hratio, ← mul_div_assoc,
    div_lt_iff₀ (Real.rpow_pos_of_pos hnR (-(P.hPlus : ℝ)+2*(P.χ : ℝ)))] at hs
  have hprod : P.aStar n * (n : ℝ)^(-(2*(P.χ : ℝ))) * (n : ℝ)^(4*(P.χ : ℝ)) =
      (n : ℝ)^(-(P.hPlus : ℝ)+2*(P.χ : ℝ))/2 := by
    dsimp [Params9.aStar]
    calc
      _ = ((n : ℝ)^(-(P.hPlus : ℝ)) * (n : ℝ)^(-(2*(P.χ : ℝ))) *
        (n : ℝ)^(4*(P.χ : ℝ)))/2 := by ring
      _ = _ := by
        rw [← Real.rpow_add hnR, ← Real.rpow_add hnR]
        congr 2
        ring
  rw [hprod]
  nlinarith

private theorem covariance_power_exp_decay {s u c : ℝ} (hu : 0 < u) (hc : 0 < c) :
    Tendsto (fun n : ℕ => (n : ℝ) ^ s * Real.exp (-c * (n : ℝ) ^ u)) atTop (𝓝 0) := by
  have hn : Tendsto (fun n : ℕ => (n : ℝ) ^ u) atTop atTop :=
    (tendsto_rpow_atTop hu).comp tendsto_natCast_atTop_atTop
  have hbase :=
    (tendsto_rpow_mul_exp_neg_mul_atTop_nhds_zero (s / u) c hc).comp hn
  apply Tendsto.congr' ?_ hbase
  filter_upwards [eventually_gt_atTop (0 : ℕ)] with n hn0
  have hnR : 0 < (n : ℝ) := by exact_mod_cast hn0
  have hpow : (n : ℝ) ^ s = ((n : ℝ) ^ u) ^ (s / u) := by
    rw [← Real.rpow_mul hnR.le]
    congr 1
    field_simp [ne_of_gt hu]
  change ((n : ℝ) ^ u) ^ (s / u) * Real.exp (-c * (n : ℝ) ^ u) =
    (n : ℝ) ^ s * Real.exp (-c * (n : ℝ) ^ u)
  rw [← hpow]

theorem eventual_covariance_moment_margin9 (P : Params9) (hP : P.Valid) :
    ∃ n0 : ℕ, ∀ n ≥ n0,
      2*(n : ℝ)^(8*(P.χ : ℝ)) * (4*(P.bStar n)^2+2*Real.exp (-(n : ℝ)^P.u)) ≤ 1 := by
  rcases hP with ⟨hx, hh, hwidth, hsigma, hchi, hgap, hcase⟩
  have hchiR : (0 : ℝ) < P.χ := by exact_mod_cast hchi.1
  have hxR : (0 : ℝ) < P.xS := by exact_mod_cast hx.1
  have hu : 0 < P.u := by dsimp [Params9.u]; linarith
  have hmin : min P.xS (min P.hMinus (1-P.hPlus)) ≤ P.hMinus :=
    le_trans (min_le_right _ _) (min_le_left _ _)
  have hchiminusQ : 100*P.χ < P.hMinus := by linarith [hchi.2]
  have hchiminus : 100*(P.χ : ℝ) < P.hMinus := by exact_mod_cast hchiminusQ
  let d := 2*(P.hMinus : ℝ)-8*(P.χ : ℝ)
  have hd : 0 < d := by dsimp [d]; linarith
  obtain ⟨nPower, hPower⟩ := eventual_covariance_power_decay
    (d := d) (A := 8) (eps := 1/2) hd (by norm_num)
  have hlim : Tendsto (fun n : ℕ => 4*(n : ℝ)^(8*(P.χ : ℝ))*Real.exp (-(n : ℝ)^P.u))
      atTop (𝓝 0) := by
    simpa [mul_assoc] using Tendsto.const_mul 4
      (covariance_power_exp_decay (s := 8*(P.χ : ℝ)) (c := 1) hu (by norm_num))
  obtain ⟨nExp, hExp⟩ := eventually_atTop.1
    (hlim.eventually (Iio_mem_nhds (by norm_num : (0 : ℝ) < 1/2)))
  refine ⟨max 1 (max nPower nExp), ?_⟩
  intro n hn
  have hn1 : 1 ≤ n := le_trans (le_max_left _ _) hn
  have hnRest : max nPower nExp ≤ n := le_trans (le_max_right _ _) hn
  have hnPower : nPower ≤ n := le_trans (le_max_left _ _) hnRest
  have hnExp : nExp ≤ n := le_trans (le_max_right _ _) hnRest
  have hnR : (0 : ℝ) < n := by exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one hn1)
  have hp := hPower n hnPower
  have he := hExp n hnExp
  have hsquare : (P.bStar n)^2 = (n : ℝ)^(-2*(P.hMinus : ℝ)) := by
    dsimp [Params9.bStar]
    rw [← Real.rpow_mul_natCast hnR.le (-(P.hMinus : ℝ)) 2]
    congr 1
    ring
  have hid : 8*(n : ℝ)^(8*(P.χ : ℝ))*(P.bStar n)^2 = 8*(n : ℝ)^(-d) := by
    rw [hsquare, mul_assoc, ← Real.rpow_add hnR]
    congr 2
    dsimp [d]
    ring
  rw [← hid] at hp
  nlinarith

theorem eventual_covariance_width_margins9 (P : Params9) (hP : P.Valid) :
    ∃ n0 : ℕ, ∀ n ≥ n0,
      Real.log 4 + (2*(n : ℝ)^(8*(P.χ : ℝ))+1)*(n : ℝ)^P.u/100 ≤
        (n : ℝ)^(P.u+8*(P.χ : ℝ)) ∧
      2*(n : ℝ)^(8*(P.χ : ℝ)) ≤ (n : ℝ)^P.u := by
  rcases hP with ⟨hx, hh, hwidth, hsigma, hchi, hgap, hcase⟩
  have hchiR : (0 : ℝ) < P.χ := by exact_mod_cast hchi.1
  have hxR : (0 : ℝ) < P.xS := by exact_mod_cast hx.1
  have hu : 0 < P.u := by dsimp [Params9.u]; linarith
  have hmin : min P.xS (min P.hMinus (1-P.hPlus)) ≤ P.xS := min_le_left _ _
  have hchixsQ : 100*P.χ < P.xS := by linarith [hchi.2]
  have hchixs : 100*(P.χ : ℝ) < P.xS := by exact_mod_cast hchixsQ
  let dSecond := P.u-8*(P.χ : ℝ)
  let dFirst := P.u+8*(P.χ : ℝ)
  have hdSecond : 0 < dSecond := by dsimp [dSecond, Params9.u]; linarith
  have hdFirst : 0 < dFirst := by dsimp [dFirst]; positivity
  obtain ⟨nSecond, hSecond⟩ := eventual_covariance_power_decay
    (d := dSecond) (A := 2) (eps := 1) hdSecond (by norm_num)
  obtain ⟨nFirst, hFirst⟩ := eventual_covariance_power_decay
    (d := dFirst) (A := 2*Real.log 4) (eps := 1) hdFirst (by norm_num)
  refine ⟨max 1 (max nSecond nFirst), ?_⟩
  intro n hn
  have hn1 : 1 ≤ n := le_trans (le_max_left _ _) hn
  have hnRest : max nSecond nFirst ≤ n := le_trans (le_max_right _ _) hn
  have hnSecond : nSecond ≤ n := le_trans (le_max_left _ _) hnRest
  have hnFirst : nFirst ≤ n := le_trans (le_max_right _ _) hnRest
  have hnR : (0 : ℝ) < n := by exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one hn1)
  have hnR1 : (1 : ℝ) ≤ n := by exact_mod_cast hn1
  have hs := hSecond n hnSecond
  have hf := hFirst n hnFirst
  have hratio : (n : ℝ)^(-dSecond) =
      (n : ℝ)^(8*(P.χ : ℝ))/(n : ℝ)^P.u := by
    rw [← Real.rpow_sub hnR]
    congr 1
    dsimp [dSecond]
    ring
  rw [hratio, ← mul_div_assoc, div_lt_iff₀ (Real.rpow_pos_of_pos hnR P.u)] at hs
  rw [Real.rpow_neg hnR.le, ← div_eq_mul_inv,
    div_lt_iff₀ (Real.rpow_pos_of_pos hnR dFirst)] at hf
  dsimp [dFirst] at hf
  have hq : (1 : ℝ) ≤ (n : ℝ)^(8*(P.χ : ℝ)) :=
    Real.one_le_rpow hnR1 (by positivity)
  have hm : (2*(n : ℝ)^(8*(P.χ : ℝ))+1)*(n : ℝ)^P.u ≤
      3*(n : ℝ)^(P.u+8*(P.χ : ℝ)) := by
    calc
      _ ≤ (3*(n : ℝ)^(8*(P.χ : ℝ)))*(n : ℝ)^P.u :=
        mul_le_mul_of_nonneg_right (by linarith) (Real.rpow_nonneg hnR.le _)
      _ = _ := by
        rw [mul_assoc, ← Real.rpow_add hnR]
        congr 2
        ring
  constructor
  · have hnonneg := Real.rpow_nonneg hnR.le (P.u+8*(P.χ : ℝ))
    nlinarith
  · simpa using hs.le

theorem prefix_supported9 {P : Params9} {n N : ℕ} {I : IDMap9 P n}
    (E : Fin N → Fin N → Prop) (G : Colour) (omega : Outcome9 I N)
    (base : Law N) (ord : List I.ID) (k : ℕ) (Y : Finset (Fin N)) (hbase : base.SupportedIn Y) :
    Law.SupportedIn (prefixLaw9 E G omega base ord k) Y := by
  unfold prefixLaw9 restrictOr9
  split_ifs with hm
  · intro y hy
    simp [Law.restrict, hbase y hy]
  · exact hbase

theorem hitSet_update_of_not_mem9 {P : Params9} {n N : ℕ} {I : IDMap9 P n}
    (E : Fin N → Fin N → Prop) (G : Colour) (omega : Outcome9 I N)
    (ids : Finset I.ID) (c : I.ID) (x : Fin N) (hc : c ∉ ids) :
    hitSet9 E G (updAnc9 omega c x) ids = hitSet9 E G omega ids := by
  have hanc (a : I.ID) (ha : a ∈ ids) : anc9 (updAnc9 omega c x) a = anc9 omega a := by
    have hne : a ≠ c := by intro h; subst a; exact hc ha
    have hsum : (Sum.inl a : I.ID ⊕ OddSites9 n) ≠ Sum.inl c := by
      intro h; exact hne (Sum.inl.inj h)
    simp [anc9, updAnc9, Function.update, hsum] <;> rfl
  ext y
  simp only [hitSet9, Finset.mem_filter, Finset.mem_univ, true_and]
  constructor
  · intro h a ha
    have hh := h a ha
    rw [hanc a ha] at hh
    exact hh
  · intro h a ha
    rw [hanc a ha]
    exact h a ha

theorem prefix_update_of_not_mem9 {P : Params9} {n N : ℕ} {I : IDMap9 P n}
    (E : Fin N → Fin N → Prop) (G : Colour) (omega : Outcome9 I N)
    (base : Law N) (ord : List I.ID) (k : ℕ) (c : I.ID) (x : Fin N)
    (hc : c ∉ (ord.take k).toFinset) :
    prefixLaw9 E G (updAnc9 omega c x) base ord k = prefixLaw9 E G omega base ord k := by
  unfold prefixLaw9
  rw [hitSet_update_of_not_mem9 E G omega _ c x hc]

theorem pi_resample_coordinate_expect {iota : Type*} [Fintype iota] [DecidableEq iota]
    {beta : iota → Type*} [∀ i, Fintype (beta i)] (P : ∀ i, FinProb (beta i))
    (i : iota) (f : (∀ i, beta i) → ℝ) :
    (FinProb.pi P).expect f = (FinProb.pi P).expect (fun omega =>
      (P i).expect (fun a => f (Function.update omega i a))) := by
  let S : Finset iota := {i}
  let J := {j // j ∈ S}
  letI : Unique J := ⟨⟨i, by simp [S]⟩, fun j => by
    apply Subtype.ext
    exact Finset.mem_singleton.mp (by simpa [S] using j.2)⟩
  let j0 : J := default
  let e := Equiv.piEquivPiSubtypeProd (fun j => j ∈ S) beta
  let Ps := FinProb.pi (fun j : J => P j.1)
  have hsplice (omega : ∀ i, beta i) (a : ∀ j : J, beta j.1) :
      e.symm (a, (e omega).2) = Function.update omega i (a j0) := by
    funext j
    by_cases hj : j = i
    · subst j
      simp [e, S, j0, Equiv.piEquivPiSubtypeProd]
      have hsub : (⟨i, by simp [S]⟩ : J) = j0 := Subsingleton.elim _ _
      change a (⟨i, by simp [S]⟩ : J) = a j0
      cases hsub
      rfl
    · simp [Function.update, hj, e, S, Equiv.piEquivPiSubtypeProd_symm_apply]
  have hweight (a : ∀ j : J, beta j.1) : Ps.w a = (P i).w (a j0) := by
    change (∏ j : J, (P j.1).w (a j)) = _
    simp [J, j0, S]
  let ea : (∀ j : J, beta j.1) ≃ beta i := Equiv.piUnique (fun j : J => beta j.1)
  have heval (a : beta i) : (ea.symm a) j0 = a := by simp [ea, j0]
  rw [pi_resample_subset_expect P S f]
  change (FinProb.pi P).expect (fun omega => Ps.expect (fun a => f (e.symm (a,(e omega).2)))) = _
  congr 1
  funext omega
  unfold FinProb.expect
  rw [← Equiv.sum_comp ea.symm]
  apply Finset.sum_congr rfl
  intro a ha
  change Ps.w (ea.symm a) * f (e.symm (ea.symm a, (e omega).2)) =
    (P i).w a * f (Function.update omega i a)
  rw [hweight, hsplice, heval]

set_option maxHeartbeats 400000 in
theorem covariance_tail_at_filter_budget9 (P : Params9) (hP : P.Valid) :
    ∃ n0 : ℕ, ∀ n ≥ n0, ∀ {N : ℕ} {E : Fin N → Fin N → Prop} {X Y : Finset (Fin N)},
      P.DeepAt n N E X Y → DeepTools9 P n N E X Y → ScalesAt9 P n →
      ∀ (G : Colour) (mu beta lam : Law N), mu.SupportedIn X → beta.SupportedIn X →
      lam.SupportedIn Y →
      mu.WidthLE ((n : ℝ)^(P.xS : ℝ)+(P.hPlus : ℝ)*Real.log n+1) →
      beta.WidthLE ((n : ℝ)^(P.xS : ℝ)+(P.hPlus : ℝ)*Real.log n+1) →
      lam.WidthLE (P.filterBudget n) →
      mu.expect (fun x => beta.pr (fun a => P.aStar n*(n : ℝ)^(-(2*(P.χ : ℝ))) <
        |testCov lam (hitInd9 E G) (hitInd9 E G) x a|)) ≤
      4*Real.exp (-((n : ℝ)^P.u/100)) := by
  obtain ⟨nGain, hGain⟩ := eventual_covariance_gain_margin9 P hP
  obtain ⟨nMoment, hMoment⟩ := eventual_covariance_moment_margin9 P hP
  obtain ⟨nWidth, hWidth⟩ := eventual_covariance_width_margins9 P hP
  have hchiR : (0 : ℝ) < P.χ := by exact_mod_cast hP.2.2.2.2.1.1
  refine ⟨max nGain (max nMoment nWidth), ?_⟩
  intro n hn N E X Y hdeep htools hscales G mu beta lam hmuX hbetaX hlamY hmuW hbetaW hlamW
  have hnGain : nGain ≤ n := le_trans (le_max_left _ _) hn
  have hnRest : max nMoment nWidth ≤ n := le_trans (le_max_right _ _) hn
  have hnMoment : nMoment ≤ n := le_trans (le_max_left _ _) hnRest
  have hnWidth : nWidth ≤ n := le_trans (le_max_right _ _) hnRest
  have hg := hGain n hnGain
  have hm := hMoment n hnMoment
  have hw := hWidth n hnWidth
  rcases hscales with ⟨hn1, hmDim, hr, hload, hfilter, hfirst, hbsmall, hgain⟩
  have hnR : (0 : ℝ) < n := by exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one hn1)
  have hnR1 : (1 : ℝ) ≤ n := by exact_mod_cast hn1
  let q := (n : ℝ)^(8*(P.χ : ℝ))
  let t : ℕ := ⌈q⌉₊
  let d := (n : ℝ)^P.u/100
  let delta := P.aStar n*(n : ℝ)^(-(2*(P.χ : ℝ)))
  let w := (n : ℝ)^(P.xS : ℝ)+(P.hPlus : ℝ)*Real.log n+1
  have hqPos : 0 < q := Real.rpow_pos_of_pos hnR _
  have hqOne : 1 ≤ q := Real.one_le_rpow hnR1 (by positivity)
  have htLo : q ≤ (t : ℝ) := Nat.le_ceil q
  have htHi : (t : ℝ) ≤ 2*q := Nat.ceil_le_two_mul (by linarith)
  have htR : (0 : ℝ) < t := lt_of_lt_of_le hqPos htLo
  have ht : 0 < t := by exact_mod_cast htR
  have htR1 : (1 : ℝ) ≤ t := by exact_mod_cast (Nat.succ_le_iff.mpr ht)
  have hd : 0 ≤ d := by dsimp [d]; positivity
  have hb : 0 ≤ P.bStar n := by dsimp [Params9.bStar]; positivity
  have hdelta : 0 ≤ delta := by dsimp [delta, Params9.aStar]; positivity
  have hroot : (Real.sqrt (t : ℝ))^2 = t := Real.sq_sqrt htR.le
  have hrootPos : 0 < Real.sqrt (t : ℝ) := Real.sqrt_pos.2 htR
  have hrootOne : 1 ≤ Real.sqrt (t : ℝ) := by nlinarith only [hroot, htR1, hrootPos]
  have hrootSelf : Real.sqrt (t : ℝ) ≤ t := by
    nlinarith only [hroot, mul_nonneg (sub_nonneg.mpr hrootOne) hrootPos.le]
  have hlog : Real.log (1+Real.sqrt (t : ℝ)) ≤ (n : ℝ)^P.u := by
    have hl := Real.log_le_sub_one_of_pos (by positivity : 0 < 1+Real.sqrt (t : ℝ))
    have htw : (t : ℝ) ≤ (n : ℝ)^P.u := le_trans htHi hw.2
    linarith only [hl, hrootSelf, htw]
  have hsecond : P.filterBudget n+Real.log (1+Real.sqrt (t : ℝ)) ≤ P.Sd n := by
    linarith only [hfilter, hlog]
  have hcost : Real.log 4+((t : ℝ)+1)*d ≤ (n : ℝ)^(P.u+8*(P.χ : ℝ)) := by
    have hmul := mul_le_mul_of_nonneg_right (add_le_add htHi (show (1 : ℝ) ≤ 1 from le_rfl)) hd
    have hwidth := hw.1
    dsimp [d, q] at hmul
    dsimp [d]
    nlinarith only [hmul, hwidth]
  have hfirstTarget : w+Real.log 4+((t : ℝ)+1)*d ≤ (n : ℝ)^(P.xD : ℝ) := by
    dsimp [w]
    linarith only [hfirst, hcost]
  have hfirstCond : w+d ≤ (n : ℝ)^(P.xD : ℝ) := by
    have hlog4 : 0 ≤ Real.log (4 : ℝ) := Real.log_nonneg (by norm_num)
    nlinarith only [hfirstTarget, hlog4, mul_nonneg (Nat.cast_nonneg t : (0 : ℝ) ≤ t) hd]
  have hmoment : (t : ℝ)*((2*P.bStar n)^2+2*Real.exp (-(n : ℝ)^P.u)) ≤ 1 := by
    have hmul := mul_le_mul_of_nonneg_right htHi
      (by positivity : 0 ≤ (2*P.bStar n)^2+2*Real.exp (-(n : ℝ)^P.u))
    dsimp [q] at hmul
    nlinarith only [hmul, hm]
  have hpowSq : ((n : ℝ)^(4*(P.χ : ℝ)))^2 = q := by
    rw [← Real.rpow_mul_natCast hnR.le (4*(P.χ : ℝ)) 2]
    congr 1
    dsimp [q]
    ring
  have hpowPos : 0 ≤ (n : ℝ)^(4*(P.χ : ℝ)) := Real.rpow_nonneg hnR.le _
  have hpowRoot : (n : ℝ)^(4*(P.χ : ℝ)) ≤ Real.sqrt (t : ℝ) := by
    nlinarith only [hpowSq, htLo, hroot, hpowPos, hrootPos]
  have hforced : 6*P.bStar n < delta*Real.sqrt (t : ℝ) := by
    have hbase : 6*P.bStar n < delta*(n : ℝ)^(4*(P.χ : ℝ)) := by
      dsimp [delta]
      linarith only [hg, hb]
    exact lt_of_lt_of_le hbase (mul_le_mul_of_nonneg_left hpowRoot hdelta)
  have hgap : 6*P.bStar n*Real.sqrt (t : ℝ) < (t : ℝ)*delta := by
    have hmul := mul_lt_mul_of_pos_right hforced hrootPos
    calc
      _ < delta*Real.sqrt (t : ℝ)*Real.sqrt (t : ℝ) := hmul
      _ = _ := by rw [mul_assoc, ← pow_two, hroot]; ring
  have hreverse (sigma : Law N) (hsigmaX : sigma.SupportedIn X)
      (hsigmaW : sigma.WidthLE ((n : ℝ)^(P.xD : ℝ))) :
      lam.pr (fun y => 2*P.bStar n < |colDeg E G sigma y-1/2|) ≤
        2*Real.exp (-(n : ℝ)^P.u) := by
    have htest := htools.2 G sigma hsigmaX hsigmaW lam hlamY (P.filterBudget n) hlamW
      (by have hp := Real.rpow_nonneg hnR.le P.u; linarith)
    calc
      _ = ∑ y ∈ Finset.univ.filter (fun y => 2*P.bStar n < |colDeg E G sigma y-1/2|), lam.w y := by
        simp [FinProb.pr, Finset.sum_filter]
      _ ≤ 2*Real.exp (P.filterBudget n-P.Sd n) := htest
      _ ≤ _ := by
        apply mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr ?_) (by norm_num)
        linarith
  exact fixed_law_abs_tail hdeep G mu beta lam hmuX hbetaX hlamY hmuW hbetaW hlamW
    t ht hb (by positivity) hfirstCond hfirstTarget hsecond hmoment hgap hreverse

theorem anc_update_ne9 {P : Params9} {n N : ℕ} {I : IDMap9 P n}
    (omega : Outcome9 I N) (c a : I.ID) (x : Fin N) (hne : a ≠ c) :
    anc9 (updAnc9 omega c x) a = anc9 omega a := by
  have hsum : (Sum.inl a : I.ID ⊕ OddSites9 n) ≠ Sum.inl c := by
    intro h; exact hne (Sum.inl.inj h)
  simp [anc9, updAnc9, Function.update, hsum] <;> rfl

def previousHits9 {P : Params9} {n N : ℕ} {I : IDMap9 P n}
    (E : Fin N → Fin N → Prop) (G : Colour) (omega : Outcome9 I N)
    (base : Law N) (ord : List I.ID) (k : ℕ) : Prop :=
  ∀ j a, j < k → ord[j]? = some a →
    (49/100 : ℝ) ≤ rowDeg E G (anc9 omega a) (prefixLaw9 E G omega base ord j)

theorem previousHits_update_of_not_mem9 {P : Params9} {n N : ℕ} {I : IDMap9 P n}
    (E : Fin N → Fin N → Prop) (G : Colour) (omega : Outcome9 I N)
    (base : Law N) (ord : List I.ID) (k : ℕ) (c : I.ID) (x : Fin N)
    (hord : ord.Nodup) (hc : c ∉ (ord.take k).toFinset) :
    previousHits9 E G (updAnc9 omega c x) base ord k ↔ previousHits9 E G omega base ord k := by
  have hcList : c ∉ ord.take k := by simpa using hc
  have hstep (j : ℕ) (a : I.ID) (hj : j < k) (ha : ord[j]? = some a) :
      rowDeg E G (anc9 (updAnc9 omega c x) a) (prefixLaw9 E G (updAnc9 omega c x) base ord j) =
        rowDeg E G (anc9 omega a) (prefixLaw9 E G omega base ord j) := by
    rcases List.getElem?_eq_some_iff.mp ha with ⟨hjLen, hval⟩
    have hself : a ∈ ord := by
      rw [← hval]
      exact List.mem_iff_getElem.mpr ⟨j, hjLen, rfl⟩
    have hidx : ord.idxOf a = j := by rw [← hval]; exact hord.idxOf_getElem j hjLen
    have hmem : a ∈ (ord.take k).toFinset := by
      apply List.mem_toFinset.mpr
      apply (List.mem_take_iff_idxOf_lt hself).mpr
      rw [hidx]
      exact hj
    have hne : a ≠ c := by intro h; exact hc (h ▸ hmem)
    have htake : (ord.take k).take j = ord.take j := by
      rw [List.take_take, Nat.min_eq_left hj.le]
    have hcj : c ∉ (ord.take j).toFinset := by
      intro hmem
      have hmem' : c ∈ ord.take j := List.mem_toFinset.mp hmem
      rw [← htake] at hmem'
      exact hcList (List.mem_of_mem_take hmem')
    rw [anc_update_ne9 omega c a x hne, prefix_update_of_not_mem9 E G omega base ord j c x hcj]
  constructor
  · intro h j a hj ha
    have hh := h j a hj ha
    rw [hstep j a hj ha] at hh
    exact hh
  · intro h j a hj ha
    rw [hstep j a hj ha]
    exact h j a hj ha

theorem pi_two_coordinate_pr_le {iota : Type*} [Fintype iota] [DecidableEq iota]
    {beta : iota → Type*} [∀ i, Fintype (beta i)] (P : ∀ i, FinProb (beta i))
    (i j : iota) (A : (∀ i, beta i) → Prop) (B : ℝ)
    (hbound : ∀ omega, (P i).expect (fun a => (P j).expect (fun b =>
      if A (Function.update (Function.update omega i a) j b) then (1 : ℝ) else 0)) ≤ B) :
    (FinProb.pi P).pr A ≤ B := by
  let f := fun omega => if A omega then (1 : ℝ) else 0
  have hprob : (FinProb.pi P).pr A = (FinProb.pi P).expect f := by
    simp [f, FinProb.pr, FinProb.expect, mul_ite]
  calc
    _ = (FinProb.pi P).expect f := hprob
    _ = (FinProb.pi P).expect (fun omega => (P j).expect (fun b => f (Function.update omega j b))) :=
      pi_resample_coordinate_expect P j f
    _ = (FinProb.pi P).expect (fun omega => (P i).expect (fun a => (P j).expect
        (fun b => f (Function.update (Function.update omega i a) j b)))) :=
      pi_resample_coordinate_expect P i _
    _ ≤ (FinProb.pi P).expect (fun _ => B) := expect_mono _ hbound
    _ = B := expect_const _ _

set_option maxHeartbeats 400000 in
theorem raw_good_prefix_covariance_bound9 (P : Params9) (hP : P.Valid) :
    ∃ n0 : ℕ, ∀ n ≥ n0, ∀ {N : ℕ} {E : Fin N → Fin N → Prop}
      {X Y : Finset (Fin N)} {kappa : ℝ} {G : Colour} {M : TagMix N}
      (S : Setup9 P n N M) (I : IDMap9 P n), CoreInput9 P kappa E X Y G M S I →
      ∀ (v : EvenSites9 n) (b : OddSites9 n) (k : ℕ) (a : I.ID),
      (coreOrder9 I v b)[k]? = some a →
      (rawLaw9 S I).pr (fun omega =>
        previousHits9 E G omega (siteSecond9 S b.1) (coreOrder9 I v b) k ∧
        P.aStar n*(n : ℝ)^(-(2*(P.χ : ℝ))) < |coreCov9 S E G omega v b k|) ≤
        4*Real.exp (-((n : ℝ)^P.u/100)) := by
  obtain ⟨n0, hbudget⟩ := covariance_tail_at_filter_budget9 P hP
  refine ⟨n0, ?_⟩
  intro n hn N E X Y kappa G M S I hin v b k a hget
  rcases hin with ⟨hN, hprep, hdeep, htags, hmasks, htools, hexps, hscales⟩
  let ord := coreOrder9 I v b
  let base := siteSecond9 S b.1
  let target := I.center v.1
  let mu : Law N := M.μ (S.tag target.slice)
  let beta : Law N := M.μ (S.tag a.slice)
  let lam := fun omega : Outcome9 I N => prefixLaw9 E G omega base ord k
  let phi := fun omega : Outcome9 I N => previousHits9 E G omega base ord k
  let delta := P.aStar n*(n : ℝ)^(-(2*(P.χ : ℝ)))
  have hord : ord.Nodup := Finset.nodup_toList _
  change ord[k]? = some a at hget
  rcases List.getElem?_eq_some_iff.mp hget with ⟨hkLen, hval⟩
  have haSelf : a ∈ ord := List.mem_iff_getElem.mpr ⟨k, hkLen, hval⟩
  have haIdx : ord.idxOf a = k := by rw [← hval]; exact hord.idxOf_getElem k hkLen
  have haAvoid : a ∉ (ord.take k).toFinset := by
    intro hmem
    have hlt := (List.mem_take_iff_idxOf_lt haSelf).mp (List.mem_toFinset.mp hmem)
    rw [haIdx] at hlt
    omega
  have htAbsent : target ∉ ord := by simp [ord, coreOrder9, coreIDs9, target]
  have htAvoid : target ∉ (ord.take k).toFinset := by
    intro hmem
    exact htAbsent (List.mem_of_mem_take (List.mem_toFinset.mp hmem))
  have haNe : a ≠ target := by intro h; exact htAbsent (h ▸ haSelf)
  obtain ⟨hmuX, hmuY, hmuW, hmuSecondW, hmuDegree⟩ :=
    hprep.2 (S.tag target.slice) (htags target.slice)
  obtain ⟨hbetaX, hbetaY, hbetaW, hbetaSecondW, hbetaDegree⟩ :=
    hprep.2 (S.tag a.slice) (htags a.slice)
  obtain ⟨hbaseX, hbaseY, hbaseFirstW, hbaseW, hbaseDegree⟩ :=
    hprep.2 (S.tag (specialWord9 (P.m n) b.1)) (htags _)
  have hbaseY' : base.SupportedIn Y := hbaseY
  have hbaseW' : base.WidthLE (P.Ss n) := hbaseW
  have hsubset : coreIDs9 I v b ⊆ I.seen b.1 := by
    intro z hz
    simp only [coreIDs9, Finset.mem_erase, Finset.mem_inter] at hz
    exact hz.2.1
  have hlen : (ord.length : ℝ) ≤ (I.seen b.1).card := by
    dsimp [ord, coreOrder9]
    rw [Finset.length_toList]
    exact_mod_cast Finset.card_le_card hsubset
  have hkBudget : (k : ℝ) ≤ P.idBudget n+(P.m n : ℝ) := by
    have hkCast : (k : ℝ) ≤ ord.length := by exact_mod_cast hkLen.le
    exact le_trans hkCast (le_trans hlen (I.odd_ids b.1 b.2))
  have hlamY (omega : Outcome9 I N) : (lam omega).SupportedIn Y :=
    prefix_supported9 E G omega base ord k Y hbaseY'
  have hlamW (omega : Outcome9 I N) (hphi : phi omega) : (lam omega).WidthLE (P.filterBudget n) := by
    have hw := prefix_width_of_previous_hits9 S I E G omega base ord k hkLen.le (P.Ss n) hbaseW' hphi
    apply Law.WidthLE.mono hw
    have hl : 0 ≤ Real.log (100/49 : ℝ) := Real.log_nonneg (by norm_num)
    have hmul := mul_le_mul_of_nonneg_right hkBudget hl
    have hnu : 0 ≤ (n : ℝ)^P.u := by positivity
    have hl2 : 0 ≤ Real.log (2 : ℝ) := Real.log_nonneg (by norm_num)
    dsimp [Params9.filterBudget]
    nlinarith only [hmul, hnu, hl2]
  change (FinProb.pi (inputLaw9 S I)).pr (fun omega => phi omega ∧ delta < |coreCov9 S E G omega v b k|) ≤ _
  apply pi_two_coordinate_pr_le (inputLaw9 S I) (Sum.inl target) (Sum.inl a)
  intro omega
  let upd := fun x y => updAnc9 (updAnc9 omega target x) a y
  have hphiUpd (x y : Fin N) : phi (upd x y) ↔ phi omega :=
    (previousHits_update_of_not_mem9 E G (updAnc9 omega target x) base ord k a y hord haAvoid).trans
      (previousHits_update_of_not_mem9 E G omega base ord k target x hord htAvoid)
  have hlamUpd (x y : Fin N) : lam (upd x y) = lam omega := by
    dsimp [lam, upd]
    rw [prefix_update_of_not_mem9 E G (updAnc9 omega target x) base ord k a y haAvoid,
      prefix_update_of_not_mem9 E G omega base ord k target x htAvoid]
  have hancA (x y : Fin N) : anc9 (upd x y) a = y := by
    simp [upd, anc9, updAnc9, Function.update] <;> rfl
  have hancT (x y : Fin N) : anc9 (upd x y) target = x := by
    dsimp [upd]
    rw [anc_update_ne9 (updAnc9 omega target x) a target y haNe.symm]
    simp [anc9, updAnc9, Function.update] <;> rfl
  have hcovUpd (x y : Fin N) : coreCov9 S E G (upd x y) v b k =
      testCov (lam omega) (hitInd9 E G) (hitInd9 E G) x y := by
    unfold coreCov9
    rw [hget]
    change (lam (upd x y)).expect (fun z => hitInd9 E G (anc9 (upd x y) a) z *
      hitInd9 E G (anc9 (upd x y) target) z) -
      (lam (upd x y)).expect (hitInd9 E G (anc9 (upd x y) a)) *
      (lam (upd x y)).expect (hitInd9 E G (anc9 (upd x y) target)) = _
    rw [hlamUpd, hancA, hancT]
    rfl
  change mu.expect (fun x => beta.expect (fun y =>
    @ite ℝ (phi (upd x y) ∧ delta < |coreCov9 S E G (upd x y) v b k|)
      (Classical.propDecidable _) 1 0)) ≤ _
  by_cases hphi : phi omega
  · have hind (x y : Fin N) :
        (@ite ℝ (phi (upd x y) ∧ delta < |coreCov9 S E G (upd x y) v b k|)
          (Classical.propDecidable _) 1 0) =
        (if delta < |testCov (lam omega) (hitInd9 E G) (hitInd9 E G) x y| then (1 : ℝ) else 0) := by
      have hp := (hphiUpd x y).mpr hphi
      rw [hcovUpd]
      simp [hp]
    simp_rw [hind]
    have hpr (x : Fin N) : beta.expect (fun y =>
        if delta < |testCov (lam omega) (hitInd9 E G) (hitInd9 E G) x y| then (1 : ℝ) else 0) =
        beta.pr (fun y => delta < |testCov (lam omega) (hitInd9 E G) (hitInd9 E G) x y|) := by
      simp [FinProb.expect, FinProb.pr, mul_ite]
    simp_rw [hpr]
    exact hbudget n hn hdeep htools hscales G mu beta (lam omega) hmuX hbetaX (hlamY omega)
      hmuW hbetaW (hlamW omega hphi)
  · have hfalse (x y : Fin N) : ¬ phi (upd x y) := by
      intro hp
      exact hphi ((hphiUpd x y).mp hp)
    simp [hfalse, expect_const]
    positivity

private theorem pr_imp_le {Omega : Type*} [Fintype Omega] (Q : FinProb Omega)
    (A B : Omega → Prop) (h : ∀ omega, A omega → B omega) : Q.pr A ≤ Q.pr B := by
  unfold FinProb.pr
  apply Finset.sum_le_sum
  intro omega homega
  by_cases ha : A omega
  · simp [ha, h omega ha]
  · simp only [ha, if_false]
    split_ifs <;> simp [Q.nonneg]

private theorem regular_order_lower9 {P : Params9} {n N : ℕ} {I : IDMap9 P n}
    (E : Fin N → Fin N → Prop) (G : Colour) (omega : Outcome9 I N)
    (base : Law N) (ord : List I.ID) (hregular : orderRegular9 E G omega base ord)
    (hsmall : P.bStar n ≤ 1/200) :
    ∀ k a, ord[k]? = some a → (49/100 : ℝ) ≤ rowDeg E G (anc9 omega a) (prefixLaw9 E G omega base ord k) := by
  intro k
  induction k using Nat.strong_induction_on with
  | h k ih =>
    intro a hget
    have hstep := hregular k a hget (by
      intro j a' hj hget'
      exact ih j hj a' hget')
    have hlow := (abs_le.mp hstep).1
    linarith only [hlow, hsmall]

set_option maxHeartbeats 400000 in
theorem covariance_certificate9 (P : Params9) (hP : P.Valid) (c0 : ℝ) (hc0 : 0 < c0) :
    ∃ c > (0 : ℝ), ∃ n0 : ℕ, ∀ n ≥ n0, ∀ {N : ℕ} {E : Fin N → Fin N → Prop}
      {X Y : Finset (Fin N)} {kappa : ℝ} {G : Colour} {M : TagMix N}
      (S : Setup9 P n N M) (I : IDMap9 P n),
      CoreInput9 P kappa E X Y G M S I → RegularityCert9 S I E G c0 → CovCert9 S I E G c := by
  have hxs : (0 : ℝ) < P.xS := by exact_mod_cast hP.1.1
  have hu : 0 < P.u := by dsimp [Params9.u]; linarith
  let C := min c0 (1/100 : ℝ)
  have hC : 0 < C := lt_min hc0 (by norm_num)
  let c := C/2
  have hc : 0 < c := by dsimp [c]; positivity
  have hlim : Tendsto (fun n : ℕ => Real.exp (-(c*(n : ℝ)^P.u))) atTop (𝓝 0) := by
    simpa [neg_mul] using (covariance_power_exp_decay (s := 0) (c := c) hu hc)
  obtain ⟨nTail, hTail⟩ := eventually_atTop.1
    (hlim.eventually (Iio_mem_nhds (by norm_num : (0 : ℝ) < 1/5)))
  obtain ⟨nRaw, hRaw⟩ := raw_good_prefix_covariance_bound9 P hP
  refine ⟨c, hc, max nRaw nTail, ?_⟩
  intro n hn N E X Y kappa G M S I hin hreg v b hadj k
  have hnRaw : nRaw ≤ n := le_trans (le_max_left _ _) hn
  have hnTail : nTail ≤ n := le_trans (le_max_right _ _) hn
  let delta := P.aStar n*(n : ℝ)^(-(2*(P.χ : ℝ)))
  let bad := fun omega : Outcome9 I N => delta < |coreCov9 S E G omega v b k|
  change (rawLaw9 S I).pr bad ≤ P.tail c n
  have hdelta : 0 ≤ delta := by dsimp [delta, Params9.aStar]; positivity
  by_cases hnone : (coreOrder9 I v b)[k]? = none
  · have hfalse (omega : Outcome9 I N) : ¬ bad omega := by
      dsimp [bad]
      simp only [coreCov9, hnone, abs_zero]
      exact not_lt_of_ge hdelta
    have hzero : (rawLaw9 S I).pr bad = 0 := by
      unfold FinProb.pr
      apply Finset.sum_eq_zero
      intro omega homega
      simp [hfalse omega]
    rw [hzero]
    exact Real.exp_nonneg _
  · obtain ⟨a, hget⟩ := Option.ne_none_iff_exists'.mp hnone
    let phi := fun omega : Outcome9 I N =>
      previousHits9 E G omega (siteSecond9 S b.1) (coreOrder9 I v b) k
    have hscales : ScalesAt9 P n := by
      rcases hin with ⟨hN, hp, hd, ht, hm, htools, hexps, hs⟩
      exact hs
    rcases hscales with ⟨hn1, hmDim, hr, hw, hfilter, hfirst, hbsmall, hgain⟩
    have hregularPhi (omega : Outcome9 I N) (hstar : starRegular9 S E G omega v) : phi omega := by
      intro j a' hj hget'
      exact regular_order_lower9 E G omega (siteSecond9 S b.1) (coreOrder9 I v b)
        (hstar b hadj).2.2 hbsmall j a' hget'
    have hgood := hRaw n hnRaw S I hin v b k a hget
    have hsplit : (rawLaw9 S I).pr bad ≤
        P.tail c0 n+4*Real.exp (-((n : ℝ)^P.u/100)) := by
      have himp : ∀ omega, bad omega → ¬ starRegular9 S E G omega v ∨ (phi omega ∧ bad omega) := by
        intro omega hbad
        by_cases hs : starRegular9 S E G omega v
        · exact Or.inr ⟨hregularPhi omega hs, hbad⟩
        · exact Or.inl hs
      calc
        _ ≤ (rawLaw9 S I).pr (fun omega => ¬ starRegular9 S E G omega v ∨ (phi omega ∧ bad omega)) :=
          pr_imp_le _ _ _ himp
        _ ≤ (rawLaw9 S I).pr (fun omega => ¬ starRegular9 S E G omega v)+
            (rawLaw9 S I).pr (fun omega => phi omega ∧ bad omega) := FinProb.pr_union _ _ _
        _ ≤ _ := add_le_add (hreg v) hgood
    have hnu : 0 ≤ (n : ℝ)^P.u := by positivity
    have hC0 : C ≤ c0 := min_le_left _ _
    have hC1 : C ≤ (1/100 : ℝ) := min_le_right _ _
    have hbase : P.tail c0 n+4*Real.exp (-((n : ℝ)^P.u/100)) ≤
        5*Real.exp (-(C*(n : ℝ)^P.u)) := by
      have h0 : P.tail c0 n ≤ Real.exp (-(C*(n : ℝ)^P.u)) := by
        apply Real.exp_le_exp.mpr
        nlinarith only [mul_le_mul_of_nonneg_right hC0 hnu]
      have h1 : Real.exp (-((n : ℝ)^P.u/100)) ≤ Real.exp (-(C*(n : ℝ)^P.u)) := by
        apply Real.exp_le_exp.mpr
        nlinarith only [mul_le_mul_of_nonneg_right hC1 hnu]
      nlinarith only [h0, h1]
    let e := Real.exp (-(c*(n : ℝ)^P.u))
    have he : 0 < e := Real.exp_pos _
    have hes : e < 1/5 := hTail n hnTail
    have hexp : Real.exp (-(C*(n : ℝ)^P.u)) = e*e := by
      dsimp [e, c]
      rw [← Real.exp_add]
      congr 1
      ring
    have hfinal : 5*Real.exp (-(C*(n : ℝ)^P.u)) ≤ P.tail c n := by
      rw [hexp]
      change 5*(e*e) ≤ e
      nlinarith only [hes, he, mul_nonneg (show 0 ≤ 1-5*e by linarith) he.le]
    exact le_trans hsplit (le_trans hbase hfinal)

end HypercubeRamsey.Lane_sol_s09_cov
