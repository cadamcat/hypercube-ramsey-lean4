import HypercubeRamsey.S05.History_q_s05_h5l
import HypercubeRamsey.S05.History_sol_s05_h1

namespace HypercubeRamsey.Lane_sol_s05_h5l

open Classical OAI.HypercubeRamsey

noncomputable section
set_option synthInstance.maxSize 1024
set_option maxHeartbeats 800000

/-- Coordinate density losses apply only to the coordinates actually read by the integrand. -/
theorem pi_expect_density_scope {I : Type*} [Fintype I] [DecidableEq I]
    {A : I → Type*} [∀ i, Fintype (A i)]
    (P Q : ∀ i, FinProb (A i)) (S : Finset I) (c : ℝ) (hc : 0 ≤ c)
    (hPQ : ∀ i ∈ S, ∀ a, (Q i).w a ≤ c * (P i).w a)
    (F : (∀ i, A i) → ℝ) (hF : ∀ a, 0 ≤ F a)
    (hdep : FinProb.DependsOn F S) (a₀ : ∀ i, A i) :
    (FinProb.pi Q).expect F ≤ c ^ S.card * (FinProb.pi P).expect F := by
  rw [FinProb.pi_expect_depends Q S F a₀ hdep,
    FinProb.pi_expect_depends P S F a₀ hdep]
  unfold FinProb.expect
  rw [Finset.mul_sum]
  apply Finset.sum_le_sum
  intro a ha
  have hprod : (∏ i : S, (Q i.1).w (a i)) ≤
      c ^ S.card * ∏ i : S, (P i.1).w (a i) := by
    calc
      _ ≤ ∏ i : S, c * (P i.1).w (a i) := by
        apply Finset.prod_le_prod₀
        · intro i hi; exact (Q i.1).nonneg (a i)
        · intro i hi; exact hPQ i.1 i.2 (a i)
      _ = _ := by rw [Finset.prod_mul_distrib]; simp
  have hW : 0 ≤ F ((Equiv.piEquivPiSubtypeProd (fun i => i ∈ S) A).symm
      (a, fun i => a₀ i.1)) := hF _
  have hh := mul_le_mul_of_nonneg_right hprod hW
  simpa only [FinProb.pi, mul_assoc] using hh

/-- An alarm under independently trimmed coordinates pays at most two per coordinate in its scope. -/
theorem pi_pr_trimmed_scope {I : Type*} [Fintype I] [DecidableEq I]
    {A : I → Type*} [∀ i, Fintype (A i)]
    (P Q : ∀ i, FinProb (A i)) (S : Finset I)
    (hPQ : ∀ i ∈ S, ∀ a, (Q i).w a ≤ 2 * (P i).w a)
    (Bad : (∀ i, A i) → Prop) (hdep : FinProb.DependsOn Bad S) (a₀ : ∀ i, A i) :
    (FinProb.pi Q).pr Bad ≤ (2 : ℝ) ^ S.card * (FinProb.pi P).pr Bad := by
  have hF : FinProb.DependsOn (fun a => if Bad a then (1 : ℝ) else 0) S := by
    intro a b hab
    change (if Bad a then (1 : ℝ) else 0) = (if Bad b then 1 else 0)
    rw [hdep a b hab]
  simpa only [FinProb.pr, FinProb.expect, mul_ite, mul_one, mul_zero] using
    pi_expect_density_scope P Q S 2 (by norm_num) hPQ
      (fun a => if Bad a then (1 : ℝ) else 0) (by intro a; split_ifs <;> norm_num) hF a₀

/-- A one-target first moment survives an independent pretrim at factor two. -/
theorem trimmed_target_moment {A : Type*} [Fintype A] (P Q : FinProb A)
    (hPQ : ∀ a, Q.w a ≤ 2 * P.w a) (f : A → ℝ) (hf : ∀ a, 0 ≤ f a)
    (ε : ℝ) (hε : P.expect f ≤ ε) : Q.expect f ≤ 2 * ε := by
  calc
    Q.expect f ≤ 2 * P.expect f := by
      unfold FinProb.expect
      rw [Finset.mul_sum]
      apply Finset.sum_le_sum
      intro a ha
      have hh := mul_le_mul_of_nonneg_right (hPQ a) (hf a)
      simpa only [mul_assoc] using hh
    _ ≤ _ := mul_le_mul_of_nonneg_left hε (by norm_num)

/-- Markov for a strictly positive conditional-rate threshold. -/
theorem trimmed_target_alarm {A : Type*} [Fintype A] (P Q : FinProb A)
    (hPQ : ∀ a, Q.w a ≤ 2 * P.w a) (f : A → ℝ) (hf : ∀ a, 0 ≤ f a)
    (ε t : ℝ) (hε : P.expect f ≤ ε) (ht : 0 < t) :
    Q.pr (fun a => t < f a) ≤ 2 * ε / t := by
  have hmono := FinProb.pr_mono Q (fun a => t < f a) (fun a => t ≤ f a)
    (fun a ha => ha.le)
  exact (hmono.trans (FinProb.markov Q f t hf ht)).trans
    (div_le_div_of_nonneg_right (trimmed_target_moment P Q hPQ f hf ε hε) ht.le)



/-- The low Step 3 Markov alarm retains three quarters of the raw exponent after pretrimming. -/
theorem low_rate_alarm {A : Type*} [Fintype A] (P Q : FinProb A)
    (hPQ : ∀ a, Q.w a ≤ 2 * P.w a) (f : A → ℝ) (hf : ∀ a, 0 ≤ f a)
    (c k : ℝ) (hraw : P.expect f ≤ Real.exp (-(c * k))) :
    Q.pr (fun a => Real.exp (-(c / 4 * k)) < f a) ≤
      2 * Real.exp (-(3 * c / 4 * k)) := by
  have hh := trimmed_target_alarm P Q hPQ f hf (Real.exp (-(c * k)))
    (Real.exp (-(c / 4 * k))) hraw (Real.exp_pos _)
  have he : 2 * Real.exp (-(c * k)) / Real.exp (-(c / 4 * k)) =
      2 * Real.exp (-(3 * c / 4 * k)) := by
    rw [div_eq_mul_inv, ← Real.exp_neg]
    calc
      _ = 2 * (Real.exp (-(c * k)) * Real.exp (-(-(c / 4 * k)))) := by ring
      _ = _ := by rw [← Real.exp_add]; congr 2; ring
  rw [he] at hh
  exact hh

/-- Conditioning a product law whose coordinates are dominated preserves the original support. -/
theorem pi_support_of_density {I : Type*} [Fintype I] [DecidableEq I]
    {A : I → Type*} [∀ i, Fintype (A i)]
    (P Q : ∀ i, FinProb (A i)) (c : ℝ)
    (hPQ : ∀ i a, (Q i).w a ≤ c * (P i).w a)
    (a : ∀ i, A i) (ha : (FinProb.pi Q).w a ≠ 0) :
    ∀ i, (P i).w (a i) ≠ 0 := by
  intro i hi
  have hQ : (Q i).w (a i) ≠ 0 :=
    (Finset.prod_ne_zero_iff.mp ha) i (Finset.mem_univ i)
  have hh := hPQ i (a i)
  rw [hi, mul_zero] at hh
  exact hQ (le_antisymm hh ((Q i).nonneg (a i)))

variable {γ K' χ : ℝ} {n N : ℕ} {E : Fin N → Fin N → Prop} {G : Colour}
    (X : Setup5 γ K' χ n N E G)

abbrev LowCoordinates := CoarseKey5 n × CubeVertex (X.p.m n) × Fin (X.p.J n + 1)

def lowTypeScope (K : X.Ty) : Finset (LowCoordinates X) :=
  Finset.univ.filter fun k => Sum.inl k ∈ K.2.1

/-- A Step 2 failure reads exactly the low part of its type list once the high keys are fixed. -/
theorem step2_low_depends (b : X.Base)
    (hi : CoarseKey5 n → Fin (X.p.s n) → Fin N) (K : X.Ty) :
    FinProb.DependsOn
      (fun lo : LowCoordinates X → Fin 1 → Fin N =>
        X.step2Fail (b, fun ℓ => match ℓ with | .inl k => lo k | .inr i => hi i) K)
      (lowTypeScope X K) := by
  intro lo lo' hagree
  apply Lane_sol_s05_h1.step2Fail_depends X b K _ _
  intro ℓ hℓ
  cases ℓ with
  | inl k =>
    exact hagree k (by simp [lowTypeScope, hℓ])
  | inr i => rfl

/-- The low part of a type has no more coordinates than the full list. -/
theorem lowTypeScope_card (K : X.Ty) : (lowTypeScope X K).card ≤ K.2.1.card := by
  have hsub : (lowTypeScope X K).image (fun k => (Sum.inl k : X.Key)) ⊆ K.2.1 := by
    intro ℓ hℓ
    obtain ⟨k, hk, rfl⟩ := Finset.mem_image.mp hℓ
    exact (Finset.mem_filter.mp hk).2
  have hinj : Function.Injective (fun k : LowCoordinates X => (Sum.inl k : X.Key)) :=
    Sum.inl_injective
  rw [← Finset.card_image_of_injective _ hinj]
  exact Finset.card_le_card hsub

/-- Optional pretrims multiply a Step 2 failure rate by at most two per low key in its list. -/
theorem step2_pretrim_bound (b : X.Base)
    (hi : CoarseKey5 n → Fin (X.p.s n) → Fin N) (tr : LowCoordinates X → Law N)
    (htr : ∀ k y, (tr k).w y ≤ 2 * (X.prior b (.inl k)).w y) (K : X.Ty) :
    (FinProb.pi (fun k : LowCoordinates X => FinProb.pi (fun _ : Fin 1 => tr k))).pr
        (fun lo => X.step2Fail (b, fun ℓ => match ℓ with | .inl k => lo k | .inr i => hi i) K) ≤
      (2 : ℝ) ^ (lowTypeScope X K).card *
        (FinProb.pi (fun k : LowCoordinates X =>
          FinProb.pi (fun _ : Fin 1 => X.prior b (.inl k)))).pr
          (fun lo => X.step2Fail (b, fun ℓ => match ℓ with | .inl k => lo k | .inr i => hi i) K) := by
  apply pi_pr_trimmed_scope _ _ (lowTypeScope X K) _ _ (step2_low_depends X b hi K)
    (fun _ _ => X.y₀)
  intro k hk θ
  simpa only [FinProb.pi, Fintype.prod_unique] using htr k (θ default)

end
end HypercubeRamsey.Lane_sol_s05_h5l
