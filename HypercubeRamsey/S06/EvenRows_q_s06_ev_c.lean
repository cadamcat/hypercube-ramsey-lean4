import HypercubeRamsey.S06.OddLoads
import HypercubeRamsey.S06.EvenRows_q_s06_even


namespace HypercubeRamsey.S06.Lane_q_s06_ev_c

open Classical
open OAI.HypercubeRamsey
open scoped BigOperators

noncomputable section

/-- Complete a nonnegative subprobability row by placing its missing mass at a fixed label. -/
def completeSubprob6 {Ω : Type*} [Fintype Ω] (f : Ω → ℝ) (ω₀ : Ω)
    (hf : ∀ ω, 0 ≤ f ω) (hs : ∑ ω, f ω ≤ 1) : FinProb Ω where
  w ω := f ω + if ω = ω₀ then 1 - ∑ x, f x else 0
  nonneg ω := by
    by_cases h : ω = ω₀
    · subst ω
      simp only [if_pos rfl]
      exact add_nonneg (hf ω₀) (sub_nonneg.mpr hs)
    · simpa [h] using hf ω
  sum_eq_one := by
    rw [Finset.sum_add_distrib]
    have hmiss : (∑ ω, if ω = ω₀ then 1 - ∑ x, f x else 0) =
        1 - ∑ x, f x := by simp
    rw [hmiss]
    ring

theorem completeSubprob6_ge {Ω : Type*} [Fintype Ω] (f : Ω → ℝ) (ω₀ x : Ω)
    (hf : ∀ ω, 0 ≤ f ω) (hs : ∑ ω, f ω ≤ 1) :
    f x ≤ (completeSubprob6 f ω₀ hf hs).w x := by
  unfold completeSubprob6
  by_cases h : x = ω₀
  · subst x
    simp only [if_pos rfl]
    exact le_add_of_nonneg_right (sub_nonneg.mpr hs)
  · simp [h]

theorem completeSubprob6_eq_of_sum {Ω : Type*} [Fintype Ω] (f : Ω → ℝ) (ω₀ x : Ω)
    (hf : ∀ ω, 0 ≤ f ω) (hs : ∑ ω, f ω = 1) :
    (completeSubprob6 f ω₀ hf (by rw [hs])).w x = f x := by
  simp [completeSubprob6, hs]

/-- Expectation under a product of two finite laws, expanded by its first coordinate. -/
theorem expect_prod6 {α β : Type*} [Fintype α] [Fintype β]
    (P : FinProb α) (Q : FinProb β) (f : α → β → ℝ) :
    (FinProb.prod P Q).expect (fun ab => f ab.1 ab.2) =
      ∑ a, P.w a * Q.expect (f a) := by
  classical
  unfold FinProb.expect
  change (∑ ab : α × β, P.w ab.1 * Q.w ab.2 * f ab.1 ab.2) = _
  rw [Fintype.sum_prod_type]
  apply Finset.sum_congr rfl
  intro a ha
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro b hb
  ring

/-- Exchange a finite weighted sum with expectation under another finite law. -/
theorem expect_sum_swap6 {α β : Type*} [Fintype α] [Fintype β]
    (P : FinProb α) (Q : FinProb β) (f : α → β → ℝ) :
    (∑ a, P.w a * Q.expect (f a)) =
      Q.expect (fun b => ∑ a, P.w a * f a b) := by
  classical
  unfold FinProb.expect
  calc
    (∑ a, P.w a * ∑ b, Q.w b * f a b) =
        ∑ a, ∑ b, P.w a * Q.w b * f a b := by
          apply Finset.sum_congr rfl
          intro a ha
          rw [Finset.mul_sum]
          apply Finset.sum_congr rfl
          intro b hb
          ring
    _ = ∑ b, ∑ a, P.w a * Q.w b * f a b := by rw [Finset.sum_comm]
    _ = ∑ b, Q.w b * ∑ a, P.w a * f a b := by
          apply Finset.sum_congr rfl
          intro b hb
          rw [Finset.mul_sum]
          apply Finset.sum_congr rfl
          intro a ha
          ring
    _ = Q.expect (fun b => ∑ a, P.w a * f a b) := rfl

/-- Pull the last finite sum through four independent weighted sums. -/
theorem sum_pull_last5 {A B C D Z : Type*} [Fintype A] [Fintype B] [Fintype C]
    [Fintype D] [Fintype Z]
    (p : A → ℝ) (q : B → ℝ) (r : C → ℝ) (s : D → ℝ) (w : Z → ℝ)
    (f : A → B → C → D → Z → ℝ) :
    (∑ a, p a * ∑ b, q b * ∑ c, r c * ∑ d, s d * ∑ z, w z * f a b c d z) =
      ∑ z, w z * ∑ a, p a * ∑ b, q b * ∑ c, r c * ∑ d, s d * f a b c d z := by
  classical
  let g : A → B → C → D → Z → ℝ := fun a b c d z =>
    p a * q b * r c * s d * w z * f a b c d z
  have hsum :
      (∑ a, ∑ b, ∑ c, ∑ d, ∑ z, g a b c d z) =
        ∑ z, ∑ a, ∑ b, ∑ c, ∑ d, g a b c d z := by
    calc
      (∑ a, ∑ b, ∑ c, ∑ d, ∑ z, g a b c d z) =
          ∑ a, ∑ b, ∑ c, ∑ z, ∑ d, g a b c d z := by
            apply Finset.sum_congr rfl
            intro a ha
            apply Finset.sum_congr rfl
            intro b hb
            apply Finset.sum_congr rfl
            intro c hc
            rw [Finset.sum_comm]
      _ = ∑ a, ∑ b, ∑ z, ∑ c, ∑ d, g a b c d z := by
            apply Finset.sum_congr rfl
            intro a ha
            apply Finset.sum_congr rfl
            intro b hb
            rw [Finset.sum_comm]
      _ = ∑ a, ∑ z, ∑ b, ∑ c, ∑ d, g a b c d z := by
            apply Finset.sum_congr rfl
            intro a ha
            rw [Finset.sum_comm]
      _ = ∑ z, ∑ a, ∑ b, ∑ c, ∑ d, g a b c d z := by rw [Finset.sum_comm]
  have hleft :
      (∑ a, p a * ∑ b, q b * ∑ c, r c * ∑ d, s d * ∑ z, w z * f a b c d z) =
        ∑ a, ∑ b, ∑ c, ∑ d, ∑ z, g a b c d z := by
    simp_rw [Finset.mul_sum]
    simp [g, mul_assoc, mul_left_comm, mul_comm]
  have hright :
      (∑ z, w z * ∑ a, p a * ∑ b, q b * ∑ c, r c * ∑ d, s d * f a b c d z) =
        ∑ z, ∑ a, ∑ b, ∑ c, ∑ d, g a b c d z := by
    simp_rw [Finset.mul_sum]
    simp [g, mul_assoc, mul_left_comm, mul_comm]
  calc
    (∑ a, p a * ∑ b, q b * ∑ c, r c * ∑ d, s d * ∑ z, w z * f a b c d z) =
        ∑ a, ∑ b, ∑ c, ∑ d, ∑ z, g a b c d z := hleft
    _ = ∑ z, ∑ a, ∑ b, ∑ c, ∑ d, g a b c d z := hsum
    _ = ∑ z, w z * ∑ a, p a * ∑ b, q b * ∑ c, r c * ∑ d, s d * f a b c d z := hright.symm

variable {γ p₀ K : ℝ} {n N : ℕ} {E : Fin N → Fin N → Prop} {G : Colour} {M : TagMix N}
variable (X : Ctx6 γ p₀ K n N E G M)

/-- Expand the centre law into its independent position, tuple, activation and tie inputs. -/
theorem centre_expect6 (H : X.Hist) (f : X.Centre → ℝ) :
    (X.centreLaw H).expect f =
      ∑ P, X.hp.posLaw.w P *
        ∑ D, (X.dataLaw X.Loc H).w D *
          ∑ A, X.hp.actLaw.w A *
            ∑ T, X.hp.tieLaw.w T * f (((P, D), A), T) := by
  have h1 : (X.centreLaw H).expect f =
      ∑ q, ((FinProb.prod (FinProb.prod X.hp.posLaw (X.dataLaw X.Loc H)) X.hp.actLaw).w q) *
        X.hp.tieLaw.expect (fun T => f (q, T)) := by
    change (FinProb.prod
      (FinProb.prod (FinProb.prod X.hp.posLaw (X.dataLaw X.Loc H)) X.hp.actLaw)
      X.hp.tieLaw).expect f = _
    exact expect_prod6 _ _ (fun q T => f (q, T))
  rw [h1]
  change (FinProb.prod (FinProb.prod X.hp.posLaw (X.dataLaw X.Loc H)) X.hp.actLaw).expect
      (fun q => X.hp.tieLaw.expect (fun T => f (q, T))) = _
  rw [expect_prod6 (FinProb.prod X.hp.posLaw (X.dataLaw X.Loc H)) X.hp.actLaw
    (fun q A => X.hp.tieLaw.expect (fun T => f ((q, A), T)))]
  change (FinProb.prod X.hp.posLaw (X.dataLaw X.Loc H)).expect
      (fun q => X.hp.actLaw.expect (fun A => X.hp.tieLaw.expect (fun T => f ((q, A), T)))) = _
  rw [expect_prod6 X.hp.posLaw (X.dataLaw X.Loc H)
    (fun P D => X.hp.actLaw.expect (fun A =>
      X.hp.tieLaw.expect (fun T => f (((P, D), A), T))))]
  simp only [FinProb.expect]

/-- Reorder the independent centre inputs so the tuple-array expectation is innermost. -/
theorem centre_expect_data_last6 (H : X.Hist)
    (f : (X.Loc → Bool) → X.Data X.Loc → (X.Loc → Bool) → X.hp.Ties → ℝ) :
    (X.centreLaw H).expect (fun C => f (X.pos C) (X.tup C) (X.act C) (X.ties C)) =
      ∑ P, X.hp.posLaw.w P *
        ∑ A, X.hp.actLaw.w A *
          ∑ T, X.hp.tieLaw.w T *
            (X.dataLaw X.Loc H).expect (fun D => f P D A T) := by
  rw [centre_expect6 X H (fun C => f (X.pos C) (X.tup C) (X.act C) (X.ties C))]
  simp only [Ctx6.pos, Ctx6.tup, Ctx6.act, Ctx6.ties]
  apply Finset.sum_congr rfl
  intro P hP
  congr 1
  simp only [FinProb.expect]
  let g := fun D A T =>
    (X.dataLaw X.Loc H).w D * X.hp.actLaw.w A * X.hp.tieLaw.w T * f P D A T
  have hleft :
      (∑ D, (X.dataLaw X.Loc H).w D *
        ∑ A, X.hp.actLaw.w A * ∑ T, X.hp.tieLaw.w T * f P D A T) =
      ∑ D, ∑ A, ∑ T, g D A T := by
    calc
      (∑ D, (X.dataLaw X.Loc H).w D *
          ∑ A, X.hp.actLaw.w A * ∑ T, X.hp.tieLaw.w T * f P D A T) =
        ∑ D, ∑ A, ∑ T,
          (X.dataLaw X.Loc H).w D * X.hp.actLaw.w A * X.hp.tieLaw.w T * f P D A T := by
            apply Finset.sum_congr rfl
            intro D hD
            rw [Finset.mul_sum]
            apply Finset.sum_congr rfl
            intro A hA
            rw [← mul_assoc, Finset.mul_sum]
            apply Finset.sum_congr rfl
            intro T hT
            ring
      _ = ∑ D, ∑ A, ∑ T, g D A T := by rfl
  rw [hleft]
  calc
    (∑ D, ∑ A, ∑ T,
        (X.dataLaw X.Loc H).w D * X.hp.actLaw.w A * X.hp.tieLaw.w T * f P D A T) =
      ∑ A, ∑ D, ∑ T,
        (X.dataLaw X.Loc H).w D * X.hp.actLaw.w A * X.hp.tieLaw.w T * f P D A T := by
          rw [Finset.sum_comm]
    _ = ∑ A, ∑ T, ∑ D,
          (X.dataLaw X.Loc H).w D * X.hp.actLaw.w A * X.hp.tieLaw.w T * f P D A T := by
          apply Finset.sum_congr rfl
          intro A hA
          rw [Finset.sum_comm]
    _ = ∑ A, X.hp.actLaw.w A * ∑ T, X.hp.tieLaw.w T *
          (∑ D, (X.dataLaw X.Loc H).w D * f P D A T) := by
            apply Finset.sum_congr rfl
            intro A hA
            calc
              (∑ T, ∑ D, (X.dataLaw X.Loc H).w D * X.hp.actLaw.w A *
                    X.hp.tieLaw.w T * f P D A T) =
                ∑ T, (X.hp.actLaw.w A * X.hp.tieLaw.w T) *
                    (∑ D, (X.dataLaw X.Loc H).w D * f P D A T) := by
                  apply Finset.sum_congr rfl
                  intro T hT
                  calc
                    (∑ D, (X.dataLaw X.Loc H).w D * X.hp.actLaw.w A *
                        X.hp.tieLaw.w T * f P D A T) =
                      ∑ D, (X.hp.actLaw.w A * X.hp.tieLaw.w T) *
                        ((X.dataLaw X.Loc H).w D * f P D A T) := by
                          apply Finset.sum_congr rfl
                          intro D hD
                          ring
                    _ = X.hp.actLaw.w A * X.hp.tieLaw.w T *
                          (∑ D, (X.dataLaw X.Loc H).w D * f P D A T) := by rw [Finset.mul_sum]
              _ = X.hp.actLaw.w A * ∑ T, X.hp.tieLaw.w T *
                    (∑ D, (X.dataLaw X.Loc H).w D * f P D A T) := by
                  symm
                  rw [Finset.mul_sum]
                  apply Finset.sum_congr rfl
                  intro T hT
                  ring

/-- The finite posterior likelihood cancels against its marginal subdensity. -/
theorem posterior_cancel6 {Z Y : Type*} [Fintype Z] [Fintype Y]
    (P : FinProb Z) (L : Z → Y → ℝ) (g : Z → ℝ)
    (hL : ∀ z y, 0 ≤ L z y) (hg : ∀ z, 0 ≤ g z) (y : Y) :
    (∑ z₀, P.w z₀ * L z₀ y *
      (∑ z, P.w z * L z y / (∑ z, P.w z * L z y) * g z)) =
      ∑ z, P.w z * L z y * g z := by
  classical
  let m : ℝ := ∑ z, P.w z * L z y
  by_cases hm : m = 0
  · have hterm : ∀ z, P.w z * L z y = 0 := by
      intro z
      have hz : 0 ≤ P.w z * L z y := mul_nonneg (P.nonneg z) (hL z y)
      have hsum := Finset.single_le_sum (fun j hj =>
        mul_nonneg (P.nonneg j) (hL j y)) (Finset.mem_univ z)
      have hsum' : P.w z * L z y ≤ 0 := by
        simpa [m] using hsum.trans_eq hm
      exact le_antisymm hsum' hz
    simp [m, hm, hterm]
  · have hsum : ∑ z, P.w z * L z y = m := rfl
    have hinner :
        (∑ z, P.w z * L z y / m * g z) * m =
          ∑ z, P.w z * L z y * g z := by
      rw [Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro z hz
      field_simp [hm]
    calc
      (∑ z₀, P.w z₀ * L z₀ y *
          (∑ z, P.w z * L z y / (∑ z, P.w z * L z y) * g z)) =
        (∑ z₀, P.w z₀ * L z₀ y) *
        (∑ z, P.w z * L z y / m * g z) := by
            rw [Finset.sum_mul]
      _ = m * (∑ z, P.w z * L z y / m * g z) := by rw [hsum]
      _ = ∑ z, P.w z * L z y * g z := by
            rw [mul_comm, hinner]

/-- One coordinate of an iid product law has its original marginal. -/
theorem pi_coord_mass6 {ι α : Type*} [Fintype ι] [DecidableEq ι] [Fintype α]
    (P : FinProb α) (a₀ a : α) (i : ι) :
    (FinProb.pi (fun _ : ι => P)).expect (fun x => if x i = a then 1 else 0) = P.w a := by
  classical
  let s : Finset ι := {i}
  let Is := {j // j ∈ s}
  letI : Unique Is := {
    default := ⟨i, by simp [s]⟩
    uniq := by
      intro j
      apply Subtype.ext
      exact Finset.mem_singleton.mp (by simpa [s] using j.property) }
  let e : (Is → α) ≃ α := Equiv.piUnique (fun _ : Is => α)
  have hdep : FinProb.DependsOn (fun x : ι → α => if x i = a then (1 : ℝ) else 0) s := by
    intro x y hxy
    simp [hxy i (by simp [s])]
  have havg := FinProb.pi_expect_depends (fun _ : ι => P) s
    (fun x : ι → α => if x i = a then (1 : ℝ) else 0) (fun _ => a₀) hdep
  rw [havg]
  have hcoord (x : Is → α) :
      (Equiv.piEquivPiSubtypeProd (fun j : ι => j ∈ s) (fun _ : ι => α)).symm
          (x, fun _ : {j // j ∉ s} => a₀) i = x ⟨i, by simp [s]⟩ := by
    simp [s]
  simp only [FinProb.expect, FinProb.pi]
  simp_rw [hcoord]
  rw [← Equiv.sum_comp e.symm (fun x : Is → α =>
    (∏ j : Is, P.w (x j)) * (if x ⟨i, by simp [s]⟩ = a then 1 else 0))]
  simp [e, Equiv.piUnique]

def empiricalFreq6 {α : Type*} [Fintype α] [DecidableEq α]
    (k : ℕ) (a : α) (x : Fin k → α) : ℝ :=
  ((Finset.univ.filter fun r : Fin k => x r = a).card : ℝ) / (k : ℝ)

/-- The expected empirical frequency of a label in an iid tuple is its one-coordinate mass. -/
theorem pi_empirical_mass6 {α : Type*} [Fintype α] [DecidableEq α]
    (P : FinProb α) (a₀ a : α) (k : ℕ) :
    (FinProb.pi (fun _ : Fin k => P)).expect (empiricalFreq6 k a) =
      if k = 0 then 0 else P.w a := by
  classical
  by_cases hk : k = 0
  · subst k
    simp [empiricalFreq6, FinProb.expect, FinProb.pi]
  · have hkpos : 0 < k := Nat.pos_of_ne_zero hk
    have hkreal : (k : ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hkpos)
    change (FinProb.pi (fun _ : Fin k => P)).expect
        (fun x => ((Finset.univ.filter fun r : Fin k => x r = a).card : ℝ) / (k : ℝ)) = _
    have hcard (x : Fin k → α) :
        ((Finset.univ.filter fun r : Fin k => x r = a).card : ℝ) =
          ∑ r : Fin k, if x r = a then (1 : ℝ) else 0 := by
      have hnat : (Finset.univ.filter fun r : Fin k => x r = a).card =
          ∑ r : Fin k, if x r = a then 1 else 0 := by
        rw [Finset.card_eq_sum_ones]
        rw [Finset.sum_filter]
      exact_mod_cast hnat
    have hfreq (x : Fin k → α) :
        ((Finset.univ.filter fun r : Fin k => x r = a).card : ℝ) / (k : ℝ) =
          ∑ r : Fin k, if x r = a then (1 : ℝ) / (k : ℝ) else 0 := by
      rw [hcard, Finset.sum_div]
      apply Finset.sum_congr rfl
      intro r hr
      split_ifs <;> ring
    unfold FinProb.expect
    simp_rw [FinProb.pi]
    calc
      (∑ x : Fin k → α, (∏ j : Fin k, P.w (x j)) *
          (((Finset.univ.filter fun r : Fin k => x r = a).card : ℝ) / (k : ℝ))) =
        ∑ x : Fin k → α, (∏ j : Fin k, P.w (x j)) *
          (∑ r : Fin k, if x r = a then (1 : ℝ) / (k : ℝ) else 0) := by
          apply Finset.sum_congr rfl
          intro x hx
          rw [hfreq x]
      _ = ∑ x : Fin k → α, ∑ r : Fin k,
            (∏ j : Fin k, P.w (x j)) * (if x r = a then (1 : ℝ) / (k : ℝ) else 0) := by
          apply Finset.sum_congr rfl
          intro x hx
          rw [Finset.mul_sum]
      _ = ∑ r : Fin k, ∑ x : Fin k → α,
            (∏ j : Fin k, P.w (x j)) * (if x r = a then (1 : ℝ) / (k : ℝ) else 0) := by
          rw [Finset.sum_comm]
      _ = ∑ r : Fin k, (1 : ℝ) / (k : ℝ) * P.w a := by
          apply Finset.sum_congr rfl
          intro r hr
          calc
            (∑ x : Fin k → α,
                (∏ j : Fin k, P.w (x j)) * (if x r = a then (1 : ℝ) / (k : ℝ) else 0)) =
              (1 : ℝ) / (k : ℝ) *
                ∑ x : Fin k → α, (∏ j : Fin k, P.w (x j)) * (if x r = a then 1 else 0) := by
                  rw [Finset.mul_sum]
                  apply Finset.sum_congr rfl
                  intro x hx
                  split_ifs <;> ring
            _ = (1 : ℝ) / (k : ℝ) * P.w a := by
                  congr 1
                  simpa [FinProb.expect, FinProb.pi] using pi_coord_mass6 P a₀ a r
      _ = (k : ℝ) * ((1 : ℝ) / (k : ℝ) * P.w a) := by
          simp [Finset.sum_const, nsmul_eq_mul]
      _ = P.w a := by field_simp [hkreal]
      _ = if k = 0 then 0 else P.w a := by simp [hk]

/-- Restricting a law to an event of mass at least `c` costs at most a factor `1/c` pointwise. -/
theorem restrictOr6_weight_le {α : Type*} [Fintype α] (P : FinProb α) (A : α → Prop)
    (a₀ a : α) (S : Finset α) (c : ℝ) (hc : 0 < c)
    (hS : ∀ x, A x ↔ x ∈ S)
    (hmass : c ≤ ∑ x ∈ S, P.w x) :
    (restrictOr6 P A a₀).w a ≤ P.w a / c := by
  classical
  let m : ℝ := ∑ x, if A x then P.w x else 0
  have hm : c ≤ m := by
    simpa [m, ← Finset.sum_filter, hS] using hmass
  have hmpos : 0 < m := lt_of_lt_of_le hc hm
  have hmax (x : α) : max 0 (if A x then P.w x else 0) = if A x then P.w x else 0 := by
    by_cases hx : A x
    · simp [hx, P.nonneg x]
    · simp [hx]
  have hclip : (∑ x, max 0 (if A x then P.w x else 0)) = m := by
    apply Finset.sum_congr rfl
    intro x hx
    rw [hmax x]
  have hnorm : (restrictOr6 P A a₀).w a = (if A a then P.w a else 0) / m := by
    unfold restrictOr6 normalize6
    rw [dif_pos (by rw [hclip]; exact hmpos)]
    simp [hmax, hclip, m]
  by_cases ha : A a
  · rw [hnorm, if_pos ha]
    exact div_le_div_of_nonneg_left (P.nonneg a) hc hm
  · rw [hnorm, if_neg ha]
    simpa using div_nonneg (P.nonneg a) hc.le

/-- Split a product-law expectation at one distinguished coordinate. -/
theorem pi_expect_split_coord6 {ι Ω : Type*} [Fintype ι] [DecidableEq ι] [Fintype Ω]
    (P : ι → FinProb Ω) (j : ι) (f : (ι → Ω) → ℝ) :
    (FinProb.pi P).expect f =
      ∑ z, (P j).w z *
        (FinProb.pi (fun i : {i // i ∉ ({j} : Finset ι)} => P i.1)).expect
          (fun b => f (fun i => if h : i = j then z else b ⟨i, by simpa using h⟩)) := by
  classical
  let s : Finset ι := {j}
  let Is := {i // i ∈ s}
  letI : Unique Is := {
    default := ⟨j, by simp [s]⟩
    uniq := by
      intro i
      apply Subtype.ext
      exact Finset.mem_singleton.mp (by simpa [s] using i.property) }
  let e : (Is → Ω) ≃ Ω := Equiv.piUnique (fun _ : Is => Ω)
  have hdefault : (default : Is).1 = j := rfl
  rw [HypercubeRamsey.S06.Lane_q_s06_even.pi_expect_split_even P s f]
  have hlocal (x : Is → Ω) :
      (FinProb.pi (fun i : Is => P i.1)).w x = (P j).w (e x) := by
    simp [FinProb.pi, e, Equiv.piUnique, hdefault]
  have hfull (x : Is → Ω) (b : {i // i ∉ s} → Ω) :
      (Equiv.piEquivPiSubtypeProd (fun i : ι => i ∈ s) (fun _ : ι => Ω)).symm (x, b) =
        (fun i => if h : i = j then e x else b ⟨i, by simpa [s] using h⟩) := by
    funext i
    by_cases h : i = j
    · subst i
      have heq : (⟨j, by simp [s]⟩ : Is) = default := Subsingleton.elim _ _
      simp [s, e, Equiv.piUnique, hdefault, heq]
    · have hi : i ∉ s := by simp [s, h]
      have hright :
          (if hEq : i = j then e x else b ⟨i, by simpa [s] using hEq⟩) = b ⟨i, hi⟩ := by
        have hsub : (⟨i, by simpa [s] using h⟩ : {i // i ∉ s}) = ⟨i, hi⟩ :=
          Subtype.ext rfl
        simpa only [dif_neg h] using congrArg b hsub
      calc
        (Equiv.piEquivPiSubtypeProd (fun i : ι => i ∈ s) (fun _ : ι => Ω)).symm (x, b) i =
            b ⟨i, hi⟩ := by simp only [Equiv.piEquivPiSubtypeProd_symm_apply, dif_neg hi]
        _ = if hEq : i = j then e x else b ⟨i, by simpa [s] using hEq⟩ := hright.symm
  rw [← Equiv.sum_comp e.symm (fun x : Is → Ω =>
    ∑ b : {i // i ∉ s} → Ω,
      (FinProb.pi (fun i : Is => P i.1)).w x *
        (FinProb.pi (fun i : {i // i ∉ s} => P i.1)).w b *
          f ((Equiv.piEquivPiSubtypeProd (fun i : ι => i ∈ s) (fun _ : ι => Ω)).symm (x, b)))]
  simp_rw [hfull]
  have hlocal' (z : Ω) :
      (FinProb.pi (fun i : Is => P i.1)).w (e.symm z) = (P j).w z := by
    simpa [e] using hlocal (e.symm z)
  calc
    (∑ z, ∑ b : {i // i ∉ s} → Ω,
        (FinProb.pi (fun i : Is => P i.1)).w (e.symm z) *
          (FinProb.pi (fun i : {i // i ∉ s} => P i.1)).w b *
          f (fun i => if h : i = j then e (e.symm z) else b ⟨i, by simpa [s] using h⟩)) =
      ∑ z, (P j).w z *
        ∑ b : {i // i ∉ s} → Ω,
          (FinProb.pi (fun i : {i // i ∉ s} => P i.1)).w b *
            f (fun i => if h : i = j then z else b ⟨i, by simpa [s] using h⟩) := by
          apply Finset.sum_congr rfl
          intro z hz
          rw [hlocal', Equiv.apply_symm_apply]
          rw [Finset.mul_sum]
          apply Finset.sum_congr rfl
          intro b hb
          ring
    _ = ∑ z, (P j).w z *
          (FinProb.pi (fun i : {i // i ∉ s} => P i.1)).expect
            (fun b => f (fun i => if h : i = j then z else b ⟨i, by simpa [s] using h⟩)) := by
          apply Finset.sum_congr rfl
          intro z hz
          apply congrArg (fun t : ℝ => (P j).w z * t)
          unfold FinProb.expect
          apply Finset.sum_congr rfl
          intro b hb
          rfl

/-- The tuple's empirical label mass is bounded by its tag mixture, using `Step2Supp`'s common-hit mass. -/
theorem tuple_empirical_bound6 {γ p₀ K : ℝ} {n N : ℕ} {E : Fin N → Fin N → Prop}
    {G : Colour} {M : TagMix N} (X : Ctx6 γ p₀ K n N E G M)
    (H : X.Hist) (β : X.Ty) (a : Fin N)
    (hT : ∀ i, 0 < (X.Tβ H β).w i →
      c₁ / 2 ≤ ∑ x ∈ X.reqNbhd H (reqNames6 β), (M.μ i).w x) :
    (X.tupleLaw H β).expect
        (fun z => ((Finset.univ.filter fun r : Fin X.k => z.2 r = a).card : ℝ) / (X.k : ℝ)) ≤
      (2 / c₁) * ∑ i, (X.Tβ H β).w i * (M.μ i).w a := by
  classical
  let T := X.Tβ H β
  let labels (i : X.ι) := X.labelLaw H (reqNames6 β) i
  let emp := empiricalFreq6 X.k a
  have hemp (i : X.ι) : (FinProb.pi (fun _ : Fin X.k => labels i)).expect emp =
      if X.k = 0 then 0 else (labels i).w a := by
    simpa [emp] using pi_empirical_mass6 (labels i) X.y₀ a X.k
  have hempEmp (i : X.ι) : (FinProb.pi (fun _ : Fin X.k => labels i)).expect emp =
      if X.k = 0 then 0 else (labels i).w a := by
    exact hemp i
  have hlabel (i : X.ι) (hi : 0 < T.w i) : (labels i).w a ≤ (M.μ i).w a / (c₁ / 2) := by
    exact restrictOr6_weight_le (M.μ i) (fun x => x ∈ X.reqNbhd H (reqNames6 β))
      X.y₀ a (X.reqNbhd H (reqNames6 β)) (c₁ / 2)
        (by norm_num [c₁, c₀]) (by intro x; rfl) (hT i hi)
  have hc1 : c₁ ≠ 0 := by norm_num [c₁, c₀]
  have hc1pos : 0 < c₁ := by norm_num [c₁, c₀]
  have hbind : (X.tupleLaw H β).expect (fun z => emp z.2) =
      ∑ i, T.w i * (FinProb.pi (fun _ : Fin X.k => labels i)).expect emp := by
    change (FinProb.bind T (fun i => FinProb.pi (fun _ : Fin X.k => labels i))).expect
      (fun z => emp z.2) = _
    simpa using FinProb.bind_expect T (fun i => FinProb.pi (fun _ : Fin X.k => labels i))
      (fun _ xs => emp xs)
  change (X.tupleLaw H β).expect (fun z => emp z.2) ≤ _
  rw [hbind]
  calc
    (∑ i, T.w i * (FinProb.pi (fun _ : Fin X.k => labels i)).expect emp) ≤
        ∑ i, (2 / c₁) * (T.w i * (M.μ i).w a) := by
          apply Finset.sum_le_sum
          intro i hi
          by_cases hiT : 0 < T.w i
          · by_cases hk : X.k = 0
            · have hzero : (FinProb.pi (fun _ : Fin X.k => labels i)).expect emp = 0 := by
                rw [hempEmp i]
                simp [hk]
              rw [hzero]
              simp
              have hfactor : 0 ≤ 2 / c₁ := div_nonneg (by norm_num) hc1pos.le
              exact mul_nonneg hfactor (mul_nonneg (T.nonneg i) ((M.μ i).nonneg a))
            · have hcomp : (FinProb.pi (fun _ : Fin X.k => labels i)).expect emp = (labels i).w a := by
                rw [hempEmp i, if_neg hk]
              rw [hcomp]
              calc
                T.w i * (labels i).w a ≤ T.w i * ((M.μ i).w a / (c₁ / 2)) :=
                  mul_le_mul_of_nonneg_left (hlabel i hiT) (T.nonneg i)
                _ = (2 / c₁) * (T.w i * (M.μ i).w a) := by field_simp [hc1]
          · have hzero : T.w i = 0 := le_antisymm (not_lt.mp hiT) (T.nonneg i)
            simp [hzero]
    _ = (2 / c₁) * ∑ i, T.w i * (M.μ i).w a := by rw [← Finset.mul_sum]

variable {γ p₀ K : ℝ} {n N : ℕ} {E : Fin N → Fin N → Prop} {G : Colour} {M : TagMix N}
variable (X : Ctx6 γ p₀ K n N E G M)

/-- The odd row, filled with a point mass when the state is invalid. -/
def oddRowProb6 (H : X.Hist) (C : X.Centre) (u : CubeVertex n) : FinProb (Fin N) :=
  let b := X.g.L.stateOf u
  if h : X.OddValid H C X.Rlong b then
    match X.stMode b with
    | .low => X.lowRow H (X.pos C) b (X.actDesc H C X.Rlong b) (X.tup C)
    | .high => X.s3Post H b (X.actDesc H C X.Rlong b) (X.tup C)
  else pointMass6 X.y₀

theorem oddRow_eq_oddRowProb6_of_valid (H : X.Hist) (C : X.Centre) (u : CubeVertex n)
    (hu : X.OddValid H C X.Rlong (X.g.L.stateOf u)) (y : Fin N) :
    X.oddRow H C u y = (oddRowProb6 X H C u).w y := by
  simp only [Ctx6.oddRow, Ctx6.oddRowAt, oddRowProb6, if_pos hu, dif_pos hu]
  cases X.stMode (X.g.L.stateOf u) <;> rfl

theorem oddRowProb6_nonneg (H : X.Hist) (C : X.Centre) (u : CubeVertex n) (y : Fin N) :
    0 ≤ (oddRowProb6 X H C u).w y :=
  (oddRowProb6 X H C u).nonneg y

theorem oddRow_le_oddRowProb6 (H : X.Hist) (C : X.Centre) (u : CubeVertex n) (y : Fin N) :
    X.oddRow H C u y ≤ (oddRowProb6 X H C u).w y := by
  by_cases hu : X.OddValid H C X.Rlong (X.g.L.stateOf u)
  · rw [oddRow_eq_oddRowProb6_of_valid X H C u hu y]
  · have hzero : X.oddRow H C u y = 0 := by
      simp [Ctx6.oddRow, Ctx6.oddRowAt, hu]
    rw [hzero]
    exact oddRowProb6_nonneg X H C u y

theorem oddRow_nonneg6 (H : X.Hist) (C : X.Centre) (u : CubeVertex n) (y : Fin N) :
    0 ≤ X.oddRow H C u y := by
  by_cases hu : X.OddValid H C X.Rlong (X.g.L.stateOf u)
  · rw [oddRow_eq_oddRowProb6_of_valid X H C u hu y]
    exact oddRowProb6_nonneg X H C u y
  · simp [Ctx6.oddRow, Ctx6.oddRowAt, hu]

theorem oddRow_sum_le_one6 (H : X.Hist) (C : X.Centre) (u : CubeVertex n) :
    ∑ y, X.oddRow H C u y ≤ 1 := by
  by_cases hu : X.OddValid H C X.Rlong (X.g.L.stateOf u)
  · calc
      ∑ y, X.oddRow H C u y = ∑ y, (oddRowProb6 X H C u).w y := by
        apply Finset.sum_congr rfl
        intro y hy
        exact oddRow_eq_oddRowProb6_of_valid X H C u hu y
      _ = 1 := (oddRowProb6 X H C u).sum_eq_one
      _ ≤ 1 := le_rfl
  · simp [Ctx6.oddRow, Ctx6.oddRowAt, hu]

end

end HypercubeRamsey.S06.Lane_q_s06_ev_c
