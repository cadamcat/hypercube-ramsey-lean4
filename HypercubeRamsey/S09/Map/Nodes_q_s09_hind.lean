import HypercubeRamsey.S09.Map.Device
import HypercubeRamsey.S03.Clock.Steps_p_clock_r4
import HypercubeRamsey.S07.TagStage
import HypercubeRamsey.S07.TagStage

/-!
Lane-local helpers for the Section 9 height induction.  In particular, these isolate the deterministic facts
about the path maximum from the probabilistic multiscale estimate.
-/

namespace HypercubeRamsey.Lane_q_s09_hind

open HypercubeRamsey
open OAI.HypercubeRamsey

private theorem finProb_pr_union {α : Type*} [Fintype α] (μ : FinProb α)
    (A B : α → Prop) : μ.pr (fun ω => A ω ∨ B ω) ≤ μ.pr A + μ.pr B := by
  classical
  letI : DecidablePred A := fun ω => Classical.propDecidable _
  letI : DecidablePred B := fun ω => Classical.propDecidable _
  letI : DecidablePred (fun ω => A ω ∨ B ω) := fun ω => Classical.propDecidable _
  unfold FinProb.pr
  calc
    (∑ ω, if A ω ∨ B ω then μ.w ω else 0) ≤
        ∑ ω, ((if A ω then μ.w ω else 0) + (if B ω then μ.w ω else 0)) := by
      apply Finset.sum_le_sum
      intro ω hω
      by_cases hA : A ω <;> by_cases hB : B ω <;>
        simp [hA, hB, μ.nonneg ω] <;> nlinarith [μ.nonneg ω]
    _ = (∑ ω, if A ω then μ.w ω else 0) + ∑ ω, if B ω then μ.w ω else 0 := by
      rw [Finset.sum_add_distrib]

private theorem finProb_pr_nonneg {α : Type*} [Fintype α] (μ : FinProb α) (A : α → Prop) :
    0 ≤ μ.pr A := by
  classical
  unfold FinProb.pr
  apply Finset.sum_nonneg
  intro ω hω
  by_cases hA : A ω <;> simp [hA, μ.nonneg ω]

private theorem finProb_prod_pr_and {α β : Type*} [Fintype α] [Fintype β]
    (μ : FinProb α) (ν : FinProb β) (A : α → Prop) (B : β → Prop) :
    (μ.prod ν).pr (fun ω => A ω.1 ∧ B ω.2) = μ.pr A * ν.pr B := by
  classical
  let E : α × β → Prop := fun ω => A ω.1 ∧ B ω.2
  let W : α × β → ℝ := fun ω =>
    @ite ℝ (E ω) (Classical.propDecidable (E ω)) (μ.w ω.1 * ν.w ω.2) 0
  unfold FinProb.pr FinProb.prod
  rw [Fintype.sum_prod_type]
  change (∑ a, ∑ b, W (a, b)) = _
  calc
    (∑ a, ∑ b, W (a, b)) =
        ∑ a, (if A a then μ.w a else 0) * (∑ b, if B b then ν.w b else 0) := by
      apply Finset.sum_congr rfl
      intro a ha
      by_cases hA : A a
      · have heq (b : β) : E (a, b) = B b := by simp [E, hA]
        have hsum : (∑ b, W (a, b)) =
            μ.w a * (∑ b, if B b then ν.w b else 0) := by
          calc
            (∑ b, W (a, b)) =
                ∑ b, (if B b then μ.w a * ν.w b else 0) := by
              apply Finset.sum_congr rfl
              intro b hb
              simp [W, heq b]
            _ =
                ∑ b, μ.w a * (if B b then ν.w b else 0) := by
              apply Finset.sum_congr rfl
              intro b hb
              by_cases hB : B b <;> simp [hB]
            _ = μ.w a * (∑ b, if B b then ν.w b else 0) := by rw [Finset.mul_sum]
        simp [hA, hsum]
      · simp [W, E, hA]
    _ = (∑ a, if A a then μ.w a else 0) * (∑ b, if B b then ν.w b else 0) := by
      symm
      exact Finset.sum_mul Finset.univ (fun a => if A a then μ.w a else 0)
        (∑ b, if B b then ν.w b else 0)

private noncomputable def heightPairLaw9 {P : Params9} {hc : HeightChoice9 P} {n : ℕ} :
    FinProb (Pos9 P hc n → Bool × Bool) :=
  FinProb.pi (fun _ : Pos9 P hc n =>
    FinProb.prod (FinProb.bernoulli ((n : ℝ) ^ (10 : ℝ) /
      (residualBall9 P n : ℝ)))
      (FinProb.bernoulli ((n : ℝ) ^ (hc.b₀ - 10))))

private def heightFieldsEquiv9 {P : Params9} {hc : HeightChoice9 P} {n : ℕ} :
    ((Pos9 P hc n → Bool) × (Pos9 P hc n → Bool)) ≃
      (Pos9 P hc n → Bool × Bool) where
  toFun ω c := (ω.1 c, ω.2 c)
  invFun ω := (fun c => (ω c).1, fun c => (ω c).2)
  left_inv ω := by cases ω; rfl
  right_inv ω := by
    funext c
    change ((ω c).1, (ω c).2) = ω c
    rcases ω c with ⟨a, b⟩
    rfl

private theorem heightPairLaw9_weight {P : Params9} {hc : HeightChoice9 P} {n : ℕ}
    (ω : (Pos9 P hc n → Bool) × (Pos9 P hc n → Bool)) :
    (heightLaw9 P hc n).w ω =
      (heightPairLaw9 (P := P) (hc := hc) (n := n)).w (heightFieldsEquiv9 ω) := by
  change
    (∏ c : Pos9 P hc n,
      (FinProb.bernoulli ((n : ℝ) ^ (10 : ℝ) / (residualBall9 P n : ℝ))).w (ω.1 c)) *
      ∏ c : Pos9 P hc n, (FinProb.bernoulli ((n : ℝ) ^ (hc.b₀ - 10))).w (ω.2 c) =
    ∏ c : Pos9 P hc n,
      (FinProb.bernoulli ((n : ℝ) ^ (10 : ℝ) / (residualBall9 P n : ℝ))).w (ω.1 c) *
        (FinProb.bernoulli ((n : ℝ) ^ (hc.b₀ - 10))).w (ω.2 c)
  exact Finset.prod_mul_distrib.symm

private theorem heightLaw9_pr_eq_heightPairLaw9 {P : Params9} {hc : HeightChoice9 P} {n : ℕ}
    (E : ((Pos9 P hc n → Bool) × (Pos9 P hc n → Bool)) → Prop) :
    (heightLaw9 P hc n).pr E =
      (heightPairLaw9 (P := P) (hc := hc) (n := n)).pr
        (fun ω => E ((heightFieldsEquiv9 (P := P) (hc := hc) (n := n)).symm ω)) := by
  classical
  unfold FinProb.pr
  calc
    (∑ ω, if E ω then (heightLaw9 P hc n).w ω else 0) =
        ∑ ω, if E ω then
          (heightPairLaw9 (P := P) (hc := hc) (n := n)).w (heightFieldsEquiv9 ω) else 0 := by
            apply Finset.sum_congr rfl
            intro ω hω
            rw [heightPairLaw9_weight]
    _ = ∑ ω, if E ((heightFieldsEquiv9 (P := P) (hc := hc) (n := n)).symm ω) then
          (heightPairLaw9 (P := P) (hc := hc) (n := n)).w ω else 0 := by
            exact Fintype.sum_equiv (heightFieldsEquiv9 (P := P) (hc := hc) (n := n))
              _ _ (by intro ω; rw [Equiv.symm_apply_apply])

private theorem finProb_pr_mono {α : Type*} [Fintype α] (μ : FinProb α)
    {A B : α → Prop} (hAB : ∀ x, A x → B x) : μ.pr A ≤ μ.pr B := by
  classical
  unfold FinProb.pr
  apply Finset.sum_le_sum
  intro x hx
  by_cases hA : A x
  · have hB := hAB x hA
    simp [hA, hB]
  · by_cases hB : B x
    · simp [hA, hB, μ.nonneg x]
    · simp [hA, hB]

private theorem finProb_pr_exists_finset_le_sum {α ι : Type*} [Fintype α]
    (μ : FinProb α) (S : Finset ι) (E : ι → α → Prop) :
    μ.pr (fun ω => ∃ i ∈ S, E i ω) ≤ ∑ i ∈ S, μ.pr (E i) := by
  classical
  induction S using Finset.induction_on with
  | empty => simp [FinProb.pr]
  | @insert a S ha ih =>
      have hsplit : (fun ω => ∃ i ∈ insert a S, E i ω) =
          (fun ω => E a ω ∨ ∃ i ∈ S, E i ω) := by
        funext ω
        simp
      calc
        μ.pr (fun ω => ∃ i ∈ insert a S, E i ω) =
            μ.pr (fun ω => E a ω ∨ ∃ i ∈ S, E i ω) := by rw [hsplit]
        _ ≤ μ.pr (E a) + μ.pr (fun ω => ∃ i ∈ S, E i ω) := finProb_pr_union μ _ _
        _ ≤ μ.pr (E a) + ∑ i ∈ S, μ.pr (E i) := by
          calc
            μ.pr (E a) + μ.pr (fun ω => ∃ i ∈ S, E i ω) =
                μ.pr (fun ω => ∃ i ∈ S, E i ω) + μ.pr (E a) := by ring
            _ ≤
                (∑ i ∈ S, μ.pr (E i)) + μ.pr (E a) := by
              have h := add_le_add_right ih (μ.pr (E a))
              nlinarith [h]
            _ = μ.pr (E a) + ∑ i ∈ S, μ.pr (E i) := by ring
        _ = ∑ i ∈ insert a S, μ.pr (E i) := by simp [ha]

private theorem prod_pr_fst {α β : Type*} [Fintype α] [Fintype β]
    (μ : FinProb α) (ν : FinProb β) (A : α → Prop) :
    (μ.prod ν).pr (fun ω => A ω.1) = μ.pr A := by
  classical
  unfold FinProb.pr FinProb.prod
  rw [Fintype.sum_prod_type]
  calc
    (∑ a, ∑ b, if A a then μ.w a * ν.w b else 0) =
        ∑ a, (if A a then μ.w a else 0) * (∑ b, ν.w b) := by
      apply Finset.sum_congr rfl
      intro a ha
      by_cases h : A a
      · simp only [h, ↓reduceIte]
        rw [Finset.mul_sum]
      · simp [h]
    _ = ∑ a, if A a then μ.w a else 0 := by simp [ν.sum_eq_one]

private theorem finProb_pi_pr_forall {ι : Type*} [Fintype ι] [DecidableEq ι]
    {α : ι → Type*} [∀ i, Fintype (α i)]
    (Q : ∀ i, FinProb (α i)) (C : ∀ i, α i → Prop) :
    (FinProb.pi Q).pr (fun x => ∀ i, C i (x i)) = ∏ i, (Q i).pr (C i) := by
  classical
  let Ev : (∀ i, α i) → Prop := fun x => ∀ i, C i (x i)
  letI : DecidablePred Ev := fun x => Classical.propDecidable _
  have hweight (x : ∀ i, α i) :
      (if Ev x then ∏ i, (Q i).w (x i) else 0) =
        ∏ i, if C i (x i) then (Q i).w (x i) else 0 := by
    by_cases hall : Ev x
    · simp [Ev, hall]
    · have hex : ∃ i, ¬ C i (x i) := by
        simpa [Ev, not_forall] using hall
      obtain ⟨i, hi⟩ := hex
      rw [if_neg hall]
      symm
      apply Finset.prod_eq_zero (Finset.mem_univ i)
      simp [hi]
  change (∑ x : (∀ i, α i), if Ev x then ∏ i, (Q i).w (x i) else 0) =
    ∏ i, (Q i).pr (C i)
  calc
    (∑ x : (∀ i, α i), if Ev x then ∏ i, (Q i).w (x i) else 0) =
        ∑ x : (∀ i, α i), ∏ i, if C i (x i) then (Q i).w (x i) else 0 := by
      apply Finset.sum_congr rfl
      intro x hx
      exact hweight x
    _ = ∏ i, ∑ a : α i, if C i a then (Q i).w a else 0 :=
      (Fintype.prod_sum (fun i a => if C i a then (Q i).w a else 0)).symm
    _ = ∏ i, (Q i).pr (C i) := by simp only [FinProb.pr]

private theorem bernoulli_pi_true_on_finset_le {ι : Type*} [Fintype ι] [DecidableEq ι]
    (p : ℝ) (hp : 0 ≤ p) (S : Finset ι) :
    (FinProb.pi (fun _ : ι => FinProb.bernoulli p)).pr
      (fun ω => ∀ i ∈ S, ω i = true) ≤ p ^ S.card := by
  classical
  let q := max 0 (min p 1)
  have hq_nonneg : 0 ≤ q := le_max_left _ _
  have hq_le : q ≤ p := max_le hp (min_le_left p 1)
  have hcoord (i : ι) :
      (FinProb.bernoulli p).pr (fun b => i ∈ S → b = true) =
        if i ∈ S then q else 1 := by
    by_cases hi : i ∈ S
    · simp [FinProb.pr, FinProb.bernoulli, q, hi]
    · simp [FinProb.pr, FinProb.bernoulli, q, hi]
  calc
    (FinProb.pi (fun _ : ι => FinProb.bernoulli p)).pr
      (fun ω => ∀ i ∈ S, ω i = true) =
        ∏ i, (FinProb.bernoulli p).pr (fun b => i ∈ S → b = true) := by
      simpa using (finProb_pi_pr_forall (fun _ : ι => FinProb.bernoulli p)
        (fun i b => i ∈ S → b = true))
    _ = ∏ i, if i ∈ S then q else 1 := by simp_rw [hcoord]
    _ = q ^ S.card := by simp [Finset.prod_ite_mem_eq]
    _ ≤ p ^ S.card := pow_le_pow_left₀ hq_nonneg hq_le _


theorem badAt9_with_eligible_size_bound {P : Params9} {hc : HeightChoice9 P} {n : ℕ}
    {c : ℝ} (hbase : HeightBase9 P hc n c)
    (v : CubeVertex n) (j : Fin (hc.levels n + 1)) :
    (heightLaw9 P hc n).pr (fun ω =>
      badAt9 (P := P) (hc := hc) (n := n) ω.1 ω.2 v j ∧
        (1 / 8 : ℝ) * (n : ℝ) ^ (10 : ℝ) ≤ (eligCount9 Finset.univ ω.1 v j : ℝ)) ≤
      Real.exp (-((n : ℝ) ^ c)) := by
  have h := hbase Finset.univ 1 (1 / 8) (by norm_num) (by norm_num) (by norm_num) v j
  simpa [badAt9, badIn9] using h

theorem badAt9_with_degraded_eligible_size_bound {P : Params9} {hc : HeightChoice9 P} {n : ℕ}
    {c t : ℝ} (hbase : HeightBase9 P hc n c)
    (ht₁ : 1 / 3 ≤ t) (ht₂ : t ≤ 1)
    (v : CubeVertex n) (j : Fin (hc.levels n + 1)) :
    (heightLaw9 P hc n).pr (fun ω =>
      badAt9 (P := P) (hc := hc) (n := n) ω.1 ω.2 v j ∧
        (1 / 8 : ℝ) * (n : ℝ) ^ (10 : ℝ) ≤ (eligCount9 Finset.univ ω.1 v j : ℝ)) ≤
      Real.exp (-((n : ℝ) ^ c)) := by
  have h := hbase Finset.univ t (1 / 8) ht₁ ht₂ (by norm_num) v j
  have hbad (ω : (Pos9 P hc n → Bool) × (Pos9 P hc n → Bool)) :
      badAt9 (P := P) (hc := hc) (n := n) ω.1 ω.2 v j →
        badIn9 Finset.univ t ω.1 ω.2 v j := by
    intro hb
    change badIn9 Finset.univ 1 ω.1 ω.2 v j at hb
    change badIn9 Finset.univ t ω.1 ω.2 v j
    rcases hb with hh | ⟨j', hj', hcrowd⟩
    · exact Or.inl hh
    · refine Or.inr ⟨j', hj', ?_⟩
      rcases hcrowd with hs | ha | hl
      · apply Or.inl
        have hp := Real.rpow_nonneg (Nat.cast_nonneg n) ((P.χ : ℝ) / 2)
        have hle := mul_le_mul_of_nonneg_right ht₂ hp
        simpa only [one_mul] using lt_of_le_of_lt hle hs
      · apply Or.inr
        apply Or.inl
        have hp := Real.rpow_nonneg (Nat.cast_nonneg n) ((P.χ : ℝ) / 2)
        have hle := mul_le_mul_of_nonneg_right ht₂ hp
        simpa only [one_mul] using lt_of_le_of_lt hle ha
      · apply Or.inr
        apply Or.inr
        have hp := Real.rpow_nonneg (Nat.cast_nonneg n) (1 - (P.σ : ℝ) + hc.eps')
        have hle := mul_le_mul_of_nonneg_right ht₂ hp
        simpa only [one_mul] using lt_of_le_of_lt hle hl
  calc
    (heightLaw9 P hc n).pr (fun ω =>
        badAt9 (P := P) (hc := hc) (n := n) ω.1 ω.2 v j ∧
          (1 / 8 : ℝ) * (n : ℝ) ^ (10 : ℝ) ≤ (eligCount9 Finset.univ ω.1 v j : ℝ)) ≤
        (heightLaw9 P hc n).pr (fun ω =>
          badIn9 Finset.univ t ω.1 ω.2 v j ∧
            (1 / 8 : ℝ) * (n : ℝ) ^ (10 : ℝ) ≤ (eligCount9 Finset.univ ω.1 v j : ℝ)) :=
      finProb_pr_mono (heightLaw9 P hc n) (by
        intro ω hω
        exact ⟨hbad ω hω.1, hω.2⟩)
    _ ≤ Real.exp (-((n : ℝ) ^ c)) := h

theorem badAt9_finite_union_degraded {P : Params9} {hc : HeightChoice9 P} {n : ℕ}
    {c t : ℝ} (hbase : HeightBase9 P hc n c)
    (ht₁ : 1 / 3 ≤ t) (ht₂ : t ≤ 1)
    (S : Finset (CubeVertex n × Fin (hc.levels n + 1))) :
    (heightLaw9 P hc n).pr (fun ω => ∃ x ∈ S,
      badAt9 (P := P) (hc := hc) (n := n) ω.1 ω.2 x.1 x.2 ∧
        (1 / 8 : ℝ) * (n : ℝ) ^ (10 : ℝ) ≤
          (eligCount9 Finset.univ ω.1 x.1 x.2 : ℝ)) ≤
      (S.card : ℝ) * Real.exp (-((n : ℝ) ^ c)) := by
  classical
  calc
    (heightLaw9 P hc n).pr (fun ω => ∃ x ∈ S,
        badAt9 (P := P) (hc := hc) (n := n) ω.1 ω.2 x.1 x.2 ∧
          (1 / 8 : ℝ) * (n : ℝ) ^ (10 : ℝ) ≤
            (eligCount9 Finset.univ ω.1 x.1 x.2 : ℝ)) ≤
        ∑ x ∈ S, (heightLaw9 P hc n).pr (fun ω =>
          badAt9 (P := P) (hc := hc) (n := n) ω.1 ω.2 x.1 x.2 ∧
            (1 / 8 : ℝ) * (n : ℝ) ^ (10 : ℝ) ≤
              (eligCount9 Finset.univ ω.1 x.1 x.2 : ℝ)) :=
      finProb_pr_exists_finset_le_sum (heightLaw9 P hc n) S (fun x ω =>
        badAt9 (P := P) (hc := hc) (n := n) ω.1 ω.2 x.1 x.2 ∧
          (1 / 8 : ℝ) * (n : ℝ) ^ (10 : ℝ) ≤
            (eligCount9 Finset.univ ω.1 x.1 x.2 : ℝ))
    _ ≤ ∑ x ∈ S, Real.exp (-((n : ℝ) ^ c)) := by
      apply Finset.sum_le_sum
      intro x hx
      exact badAt9_with_degraded_eligible_size_bound hbase ht₁ ht₂ x.1 x.2
    _ = (S.card : ℝ) * Real.exp (-((n : ℝ) ^ c)) := by simp

theorem badIn9_with_eligible_size_bound {P : Params9} {hc : HeightChoice9 P} {n : ℕ}
    {c t : ℝ} (hbase : HeightBase9 P hc n c)
    (ht₁ : 1 / 3 ≤ t) (ht₂ : t ≤ 1)
    (v : CubeVertex n) (j : Fin (hc.levels n + 1)) :
    (heightLaw9 P hc n).pr (fun ω =>
      badIn9 Finset.univ t ω.1 ω.2 v j ∧
        (1 / 8 : ℝ) * (n : ℝ) ^ (10 : ℝ) ≤ (eligCount9 Finset.univ ω.1 v j : ℝ)) ≤
      Real.exp (-((n : ℝ) ^ c)) := by
  have h := hbase Finset.univ t (1 / 8) ht₁ ht₂ (by norm_num) v j
  simpa using h

theorem badIn9_finite_union {P : Params9} {hc : HeightChoice9 P} {n : ℕ}
    {c t : ℝ} (hbase : HeightBase9 P hc n c)
    (ht₁ : 1 / 3 ≤ t) (ht₂ : t ≤ 1)
    (S : Finset (CubeVertex n × Fin (hc.levels n + 1))) :
    (heightLaw9 P hc n).pr (fun ω => ∃ x ∈ S,
      badIn9 Finset.univ t ω.1 ω.2 x.1 x.2 ∧
        (1 / 8 : ℝ) * (n : ℝ) ^ (10 : ℝ) ≤
          (eligCount9 Finset.univ ω.1 x.1 x.2 : ℝ)) ≤
      (S.card : ℝ) * Real.exp (-((n : ℝ) ^ c)) := by
  classical
  calc
    (heightLaw9 P hc n).pr (fun ω => ∃ x ∈ S,
        badIn9 Finset.univ t ω.1 ω.2 x.1 x.2 ∧
          (1 / 8 : ℝ) * (n : ℝ) ^ (10 : ℝ) ≤
            (eligCount9 Finset.univ ω.1 x.1 x.2 : ℝ)) ≤
        ∑ x ∈ S, (heightLaw9 P hc n).pr (fun ω =>
          badIn9 Finset.univ t ω.1 ω.2 x.1 x.2 ∧
            (1 / 8 : ℝ) * (n : ℝ) ^ (10 : ℝ) ≤
              (eligCount9 Finset.univ ω.1 x.1 x.2 : ℝ)) :=
      finProb_pr_exists_finset_le_sum (heightLaw9 P hc n) S (fun x ω =>
        badIn9 Finset.univ t ω.1 ω.2 x.1 x.2 ∧
          (1 / 8 : ℝ) * (n : ℝ) ^ (10 : ℝ) ≤
            (eligCount9 Finset.univ ω.1 x.1 x.2 : ℝ))
    _ ≤ ∑ x ∈ S, Real.exp (-((n : ℝ) ^ c)) := by
      apply Finset.sum_le_sum
      intro x hx
      exact badIn9_with_eligible_size_bound hbase ht₁ ht₂ x.1 x.2
    _ = (S.card : ℝ) * Real.exp (-((n : ℝ) ^ c)) := by simp

theorem badIn9_finite_union_on_counts {P : Params9} {hc : HeightChoice9 P} {n : ℕ}
    {c t : ℝ} (hbase : HeightBase9 P hc n c) (hcounts : HeightCounts9 P hc n)
    (ht₁ : 1 / 3 ≤ t) (ht₂ : t ≤ 1)
    (S : Finset (CubeVertex n × Fin (hc.levels n + 1))) :
    (heightLaw9 P hc n).pr (fun ω => ∃ x ∈ S, badIn9 Finset.univ t ω.1 ω.2 x.1 x.2) ≤
      (S.card : ℝ) * Real.exp (-((n : ℝ) ^ c)) + Real.exp (-(n : ℝ)) := by
  classical
  let small (Pp : Pos9 P hc n → Bool) : Prop :=
    ∃ v : CubeVertex n, ∃ j : Fin (hc.levels n + 1),
      (eligCount9 Finset.univ Pp v j : ℝ) < (n : ℝ) ^ (10 : ℝ) / 2
  let enough (Pp : Pos9 P hc n → Bool) : Prop :=
    ∀ v : CubeVertex n, ∀ j : Fin (hc.levels n + 1),
      (n : ℝ) ^ (10 : ℝ) / 2 ≤ (eligCount9 Finset.univ Pp v j : ℝ)
  let qualified (ω : (Pos9 P hc n → Bool) × (Pos9 P hc n → Bool)) : Prop :=
    ∃ x ∈ S, badIn9 Finset.univ t ω.1 ω.2 x.1 x.2 ∧
      (1 / 8 : ℝ) * (n : ℝ) ^ (10 : ℝ) ≤ (eligCount9 Finset.univ ω.1 x.1 x.2 : ℝ)
  have hqual : (heightLaw9 P hc n).pr qualified ≤
      (S.card : ℝ) * Real.exp (-((n : ℝ) ^ c)) := by
    simpa [qualified] using badIn9_finite_union hbase ht₁ ht₂ S
  have hsmall : (heightLaw9 P hc n).pr (fun ω => small ω.1) ≤ Real.exp (-(n : ℝ)) := by
    calc
      (heightLaw9 P hc n).pr (fun ω => small ω.1) =
          (heightPosLaw9 P hc n).pr small := by
            simpa [heightLaw9] using
              (prod_pr_fst (heightPosLaw9 P hc n) (heightActLaw9 P hc n) small)
      _ ≤ Real.exp (-(n : ℝ)) := by
        simpa [HeightCounts9, small] using hcounts
  have hgoodCount (ω : (Pos9 P hc n → Bool) × (Pos9 P hc n → Bool))
      (hg : enough ω.1) (x : CubeVertex n × Fin (hc.levels n + 1)) :
      (1 / 8 : ℝ) * (n : ℝ) ^ (10 : ℝ) ≤
        (eligCount9 Finset.univ ω.1 x.1 x.2 : ℝ) := by
    have h := hg x.1 x.2
    have hnonneg : 0 ≤ (n : ℝ) ^ (10 : ℝ) := Real.rpow_nonneg (Nat.cast_nonneg n) _
    nlinarith
  have hsubset (ω : (Pos9 P hc n → Bool) × (Pos9 P hc n → Bool)) :
      (∃ x ∈ S, badIn9 Finset.univ t ω.1 ω.2 x.1 x.2) →
        qualified ω ∨ small ω.1 := by
    intro hbad
    by_cases hg : enough ω.1
    · obtain ⟨x, hx, hb⟩ := hbad
      exact Or.inl ⟨x, hx, hb, hgoodCount ω hg x⟩
    · right
      unfold enough at hg
      push_neg at hg
      simpa [small] using hg
  calc
    (heightLaw9 P hc n).pr (fun ω => ∃ x ∈ S, badIn9 Finset.univ t ω.1 ω.2 x.1 x.2) ≤
        (heightLaw9 P hc n).pr (fun ω => qualified ω ∨ small ω.1) :=
      finProb_pr_mono (heightLaw9 P hc n) hsubset
    _ ≤ (heightLaw9 P hc n).pr qualified +
        (heightLaw9 P hc n).pr (fun ω => small ω.1) := finProb_pr_union _ _ _
    _ ≤ (S.card : ℝ) * Real.exp (-((n : ℝ) ^ c)) + Real.exp (-(n : ℝ)) :=
      add_le_add hqual hsmall

private def diffSet9H {d : ℕ} (v u : CubeVertex d) : Finset (Fin d) :=
  Finset.univ.filter (fun i => u i ≠ v i)

private def vertexOfDiff9H {d : ℕ} (v : CubeVertex d) (s : Finset (Fin d)) : CubeVertex d :=
  fun i => if i ∈ s then !(v i) else v i

private def diffEquiv9H {d : ℕ} (v : CubeVertex d) : CubeVertex d ≃ Finset (Fin d) where
  toFun := diffSet9H v
  invFun := vertexOfDiff9H v
  left_inv := by
    intro u
    funext i
    by_cases hi : u i = v i
    · simp [vertexOfDiff9H, diffSet9H, hi]
    · have hmem : i ∈ diffSet9H v u := by simp [diffSet9H, hi]
      have hbool : v i = !(u i) := by
        cases hu : u i <;> cases hv : v i <;> simp_all
      simp [vertexOfDiff9H, hmem, hbool]
  right_inv := by
    intro s
    ext i
    by_cases hi : i ∈ s
    · simp [diffSet9H, vertexOfDiff9H, hi]
    · simp [diffSet9H, vertexOfDiff9H, hi]

private theorem diffSet9H_card {d : ℕ} (v u : CubeVertex d) :
    (diffSet9H v u).card = _root_.hammingDist u v := by
  simp [diffSet9H, _root_.hammingDist, ne_comm]

private def ballToSubsets9H {d r : ℕ} (v : CubeVertex d) :
    {u : CubeVertex d // _root_.hammingDist u v ≤ r} ≃ {s : Finset (Fin d) // s.card ≤ r} where
  toFun u := ⟨diffSet9H v u.1, by rw [diffSet9H_card]; exact u.2⟩
  invFun s := ⟨vertexOfDiff9H v s.1, by
    rw [← diffSet9H_card]
    simp [diffSet9H, vertexOfDiff9H]
    exact s.2⟩
  left_inv := by
    intro u
    apply Subtype.ext
    exact (diffEquiv9H v).left_inv u.1
  right_inv := by
    intro s
    apply Subtype.ext
    exact (diffEquiv9H v).right_inv s.1

private def smallSubsetFiberEquiv9H (d r : ℕ) (i : Fin (r + 1)) :
    {s : {s : Finset (Fin d) // s.card ≤ r} // (⟨s.1.card, by omega⟩ : Fin (r + 1)) = i} ≃
      {s : Finset (Fin d) // s.card = i.val} where
  toFun s := ⟨s.1.1, by
    have h := congrArg Fin.val s.2
    simpa using h⟩
  invFun s := ⟨⟨s.1, by rw [s.2]; omega⟩, by
    apply Fin.ext
    exact s.2⟩
  left_inv := by
    intro s
    apply Subtype.ext
    apply Subtype.ext
    rfl
  right_inv := by
    intro s
    apply Subtype.ext
    rfl

private def subsetsSmallEquiv9H (d r : ℕ) :
    {s : Finset (Fin d) // s.card ≤ r} ≃
      Σ i : Fin (r + 1), {s : Finset (Fin d) // s.card = i.val} := by
  let f : {s : Finset (Fin d) // s.card ≤ r} → Fin (r + 1) :=
    fun s => ⟨s.1.card, by omega⟩
  exact (Equiv.sigmaFiberEquiv f).symm.trans
    (Equiv.sigmaCongrRight (smallSubsetFiberEquiv9H d r))

private theorem card_small_subsets9H (d r : ℕ) :
    Fintype.card {s : Finset (Fin d) // s.card ≤ r} =
      ∑ i ∈ Finset.range (r + 1), Nat.choose d i := by
  classical
  rw [Fintype.card_congr (subsetsSmallEquiv9H d r), Fintype.card_sigma]
  have hfiber (i : Fin (r + 1)) :
      Fintype.card {s : Finset (Fin d) // s.card = i.val} = Nat.choose d i.val := by
    let S : Finset (Finset (Fin d)) := Finset.univ.powersetCard i.val
    let e : {s : Finset (Fin d) // s.card = i.val} ≃ S :=
      { toFun := fun s => ⟨s.1, by
          rw [Finset.mem_powersetCard]
          exact ⟨Finset.subset_univ _, s.2⟩⟩
        invFun := fun s => ⟨s.1, (Finset.mem_powersetCard.mp s.2).2⟩
        left_inv := by intro s; apply Subtype.ext; rfl
        right_inv := by intro s; apply Subtype.ext; rfl }
    calc
      Fintype.card {s : Finset (Fin d) // s.card = i.val} = Fintype.card S := Fintype.card_congr e
      _ = S.card := Fintype.card_coe S
      _ = Nat.choose d i.val := by simp [S, Finset.card_powersetCard]
  simp_rw [hfiber]
  rw [← Fin.sum_univ_eq_sum_range]

private theorem hammingBall9H_card (d r : ℕ) (v : CubeVertex d) :
    (Finset.univ.filter (fun u : CubeVertex d => _root_.hammingDist u v ≤ r)).card =
      ∑ i ∈ Finset.range (r + 1), Nat.choose d i := by
  classical
  have hcard : Fintype.card {u : CubeVertex d // _root_.hammingDist u v ≤ r} =
      (Finset.univ.filter (fun u : CubeVertex d => _root_.hammingDist u v ≤ r)).card := by
    simpa using (Fintype.card_subtype (fun u : CubeVertex d => _root_.hammingDist u v ≤ r))
  exact hcard.symm.trans ((Fintype.card_congr (ballToSubsets9H v)).trans
    (card_small_subsets9H d r))

private theorem hammingBall9H_card_le (d r : ℕ) (v : CubeVertex d) :
    (Finset.univ.filter (fun u : CubeVertex d => _root_.hammingDist u v ≤ r)).card ≤
      (r + 1) * (d + 1) ^ r := by
  classical
  rw [hammingBall9H_card]
  have hterm (i : ℕ) (hi : i ∈ Finset.range (r + 1)) : Nat.choose d i ≤ (d + 1) ^ r := by
    have hir : i ≤ r := by simp only [Finset.mem_range] at hi; omega
    calc
      Nat.choose d i ≤ Nat.choose (d + 1) i := Nat.choose_le_succ d i
      _ ≤ (d + 1) ^ i := Nat.choose_le_pow _ _
      _ ≤ (d + 1) ^ r := Nat.pow_le_pow_right (by omega) hir
  calc
    (∑ i ∈ Finset.range (r + 1), Nat.choose d i) ≤
        ∑ i ∈ Finset.range (r + 1), (d + 1) ^ r := by
          apply Finset.sum_le_sum
          intro i hi
          exact hterm i hi
    _ = (r + 1) * (d + 1) ^ r := by simp

private abbrev HeightState9 (P : Params9) (hc : HeightChoice9 P) (n : ℕ) :=
  CubeVertex n × Fin (hc.levels n + 1)

private def heightStep9 {P : Params9} {hc : HeightChoice9 P} {n : ℕ}
    (bad : HeightState9 P hc n → Prop) (x y : HeightState9 P hc n) : Prop :=
  (x.1 = y.1 ∧ y.2.val = x.2.val + 1 ∧ bad x) ∨
    (x.2.val = y.2.val + 1 ∧ _root_.hammingDist x.1 y.1 ≤ 2)

private def heightMetric9 {P : Params9} {hc : HeightChoice9 P} {n : ℕ}
    (x y : HeightState9 P hc n) : ℕ :=
  max (Nat.dist x.2.val y.2.val) ((_root_.hammingDist x.1 y.1 + 1) / 2)

private theorem heightMetric9_triangle {P : Params9} {hc : HeightChoice9 P} {n : ℕ}
    (x y z : HeightState9 P hc n) :
    heightMetric9 x z ≤ heightMetric9 x y + heightMetric9 y z := by
  have hlevel := Nat.dist.triangle_inequality x.2.val y.2.val z.2.val
  have hsite := _root_.hammingDist_triangle x.1 y.1 z.1
  have hsite' : (_root_.hammingDist x.1 z.1 + 1) / 2 ≤
      (_root_.hammingDist x.1 y.1 + 1) / 2 +
        (_root_.hammingDist y.1 z.1 + 1) / 2 := by omega
  unfold heightMetric9
  apply max_le
  · exact hlevel.trans (Nat.add_le_add (le_max_left _ _) (le_max_left _ _))
  · exact hsite'.trans (Nat.add_le_add (le_max_right _ _) (le_max_right _ _))

private theorem heightStep9_metric_le_one {P : Params9} {hc : HeightChoice9 P} {n : ℕ}
    {bad : HeightState9 P hc n → Prop} {x y : HeightState9 P hc n}
    (h : heightStep9 bad x y) : heightMetric9 x y ≤ 1 := by
  rcases h with ⟨hsite, hlevel, _⟩ | ⟨hlevel, hsite⟩
  · have hdist : Nat.dist x.2.val y.2.val = 1 := by rw [hlevel]; simp [Nat.dist]
    have hham : _root_.hammingDist x.1 y.1 = 0 := by rw [hsite]; simp
    simp [heightMetric9, hdist, hham]
  · have hdist : Nat.dist x.2.val y.2.val = 1 := by rw [hlevel]; simp [Nat.dist]
    have hham : (_root_.hammingDist x.1 y.1 + 1) / 2 ≤ 1 := by omega
    simp [heightMetric9, hdist, hham]

private theorem heightMetric9_comm {P : Params9} {hc : HeightChoice9 P} {n : ℕ}
    (x y : HeightState9 P hc n) : heightMetric9 x y = heightMetric9 y x := by
  simp [heightMetric9, Nat.dist_comm, _root_.hammingDist_comm]

private inductive HeightPath9 {P : Params9} {hc : HeightChoice9 P} {n : ℕ}
    (step : HeightState9 P hc n → HeightState9 P hc n → Prop) :
    List (HeightState9 P hc n) → HeightState9 P hc n → Prop
  | singleton (x : HeightState9 P hc n) : HeightPath9 step [x] x
  | cons {x y : HeightState9 P hc n} {l : List (HeightState9 P hc n)} {start : HeightState9 P hc n}
      (hxy : step y x) (hp : HeightPath9 step (y :: l) start) :
      HeightPath9 step (x :: y :: l) start

private theorem heightPath9_firstExit9 {P : Params9} {hc : HeightChoice9 P} {n : ℕ}
    {bad : HeightState9 P hc n → HeightState9 P hc n → Prop}
    {l : List (HeightState9 P hc n)} {start : HeightState9 P hc n}
    (hp : HeightPath9 bad l start)
    (hstepUnit : ∀ x y, bad x y → heightMetric9 x y ≤ 1)
    (R : ℕ) (hR : 0 < R)
    (hexit : ∃ x ∈ l, R ≤ heightMetric9 x start) :
    ∃ endpoint rest, HeightPath9 bad (endpoint :: rest) start ∧
      (∀ z ∈ endpoint :: rest, z ∈ l) ∧
      (∀ z ∈ rest, heightMetric9 z start < R) ∧
      R ≤ heightMetric9 endpoint start ∧ heightMetric9 endpoint start ≤ R := by
  induction hp generalizing R with
  | singleton x =>
      obtain ⟨z, hz, hge⟩ := hexit
      have hzx : z = x := by simpa using hz
      subst z
      have hzero : heightMetric9 x x = 0 := by simp [heightMetric9]
      omega
  | @cons head next tail start hstep htail ih =>
      by_cases htailExit : ∃ z ∈ next :: tail, R ≤ heightMetric9 z start
      · obtain ⟨endpoint, rest, hpath, hsub, hclose, hge, hle⟩ := ih R hR htailExit
        refine ⟨endpoint, rest, hpath, ?_, hclose, hge, hle⟩
        intro z hz
        exact List.mem_cons_of_mem _ (hsub z hz)
      · have hcloseTail : ∀ z ∈ next :: tail, heightMetric9 z start < R := by
          intro z hz
          by_contra hnot
          exact htailExit ⟨z, hz, Nat.le_of_not_gt hnot⟩
        obtain ⟨z, hz, hge⟩ := hexit
        have hheadExit : R ≤ heightMetric9 head start := by
          rcases List.mem_cons.mp hz with hEq | hzTail
          · simpa [hEq] using hge
          · exact False.elim (htailExit ⟨z, hzTail, hge⟩)
        have hstep' : heightMetric9 head next ≤ 1 := by
          simpa [heightMetric9_comm] using hstepUnit next head hstep
        have hnext : heightMetric9 next start < R := hcloseTail next (by simp)
        have hnextle : heightMetric9 next start ≤ R - 1 := by omega
        have htriangle := heightMetric9_triangle head next start
        have hupper : heightMetric9 head start ≤ R := by
          calc
            heightMetric9 head start ≤ heightMetric9 head next + heightMetric9 next start := htriangle
            _ ≤ 1 + (R - 1) := Nat.add_le_add hstep' hnextle
            _ ≤ R := by omega
        refine ⟨head, next :: tail, HeightPath9.cons hstep htail, ?_, ?_, hheadExit, hupper⟩
        · intro z hz
          exact hz
        · intro z hz
          simp only [List.mem_cons] at hz
          rcases hz with rfl | hz
          · exact hnext
          · exact hcloseTail z (List.mem_cons_of_mem _ hz)

private def scaleBad9 {P : Params9} {hc : HeightChoice9 P} {n : ℕ}
    (C : Finset (Pos9 P hc n)) (t s : ℝ) (Pp A : Pos9 P hc n → Bool)
    (x : HeightState9 P hc n) : Prop :=
  badIn9 C t Pp A x.1 x.2 ∧
    s * (n : ℝ) ^ (10 : ℝ) ≤ (eligCount9 C Pp x.1 x.2 : ℝ)

private def scaleFailure9 {P : Params9} {hc : HeightChoice9 P} {n : ℕ}
    (C : Finset (Pos9 P hc n)) (t s η : ℝ) (R : ℕ)
    (Pp A : Pos9 P hc n → Bool) (start : HeightState9 P hc n) : Prop :=
  ∃ endpoint : HeightState9 P hc n, ∃ rest : List (HeightState9 P hc n),
    HeightPath9 (heightStep9 (scaleBad9 C t s Pp A)) (endpoint :: rest) start ∧
    (∀ x ∈ endpoint :: rest, _root_.hammingDist x.1 start.1 ≤ 16 * R) ∧
    (∀ x ∈ endpoint :: rest, Nat.dist x.2.val start.2.val ≤ 8 * R) ∧
    R ≤ max (Nat.dist endpoint.2.val start.2.val)
      ((_root_.hammingDist endpoint.1 start.1 + 1) / 2) ∧
    (start.2.val : ℝ) ≤ (endpoint.2.val : ℝ) + η * (R : ℝ)

private noncomputable def scaleBall9 {P : Params9} {hc : HeightChoice9 P} {n : ℕ}
    (start : HeightState9 P hc n) (R : ℕ) : Finset (HeightState9 P hc n) :=
  Finset.univ.filter (fun x => _root_.hammingDist x.1 start.1 ≤ 16 * R ∧
    Nat.dist x.2.val start.2.val ≤ 8 * R)

private theorem scaleBall9_card_le {P : Params9} {hc : HeightChoice9 P} {n : ℕ}
    (start : HeightState9 P hc n) (R : ℕ) :
    (scaleBall9 start R).card ≤
      (hc.levels n + 1) * (16 * R + 1) * (n + 1) ^ (16 * R) := by
  classical
  let B : Finset (CubeVertex n) :=
    Finset.univ.filter (fun v => _root_.hammingDist v start.1 ≤ 16 * R)
  have hsub : scaleBall9 start R ⊆ B ×ˢ (Finset.univ : Finset (Fin (hc.levels n + 1))) := by
    intro x hx
    have hx' : _root_.hammingDist x.1 start.1 ≤ 16 * R ∧
        Nat.dist x.2.val start.2.val ≤ 8 * R := by
      simpa [scaleBall9] using (Finset.mem_filter.mp hx).2
    simp only [Finset.mem_product, B, Finset.mem_filter, Finset.mem_univ,
      true_and]
    exact ⟨hx'.1, trivial⟩
  have hcard : (scaleBall9 start R).card ≤ B.card * (hc.levels n + 1) := by
    calc
      (scaleBall9 start R).card ≤
          (B ×ˢ (Finset.univ : Finset (Fin (hc.levels n + 1)))).card :=
        Finset.card_le_card hsub
      _ = B.card * (hc.levels n + 1) := by simp [Finset.card_product]
  have hball := hammingBall9H_card_le n (16 * R) start.1
  calc
    (scaleBall9 start R).card ≤ B.card * (hc.levels n + 1) := hcard
    _ ≤ ((16 * R + 1) * (n + 1) ^ (16 * R)) * (hc.levels n + 1) :=
      Nat.mul_le_mul_right _ (by simpa [B] using hball)
    _ = (hc.levels n + 1) * (16 * R + 1) * (n + 1) ^ (16 * R) := by ring

private theorem heightPath9_head_bounds_of_good {P : Params9} {hc : HeightChoice9 P} {n : ℕ}
    {bad : HeightState9 P hc n → Prop} {l : List (HeightState9 P hc n)}
    {start : HeightState9 P hc n}
    (hp : HeightPath9 (heightStep9 bad) l start) (hgood : ∀ x ∈ l, ¬ bad x) :
    ∃ endpoint, l.head? = some endpoint ∧ endpoint.2.val ≤ start.2.val ∧
      _root_.hammingDist endpoint.1 start.1 ≤ 2 * (start.2.val - endpoint.2.val) := by
  induction hp with
  | singleton x => exact ⟨x, by simp, by omega, by simp⟩
  | @cons x y rest start hstep htail ih =>
      have hygood : ¬ bad y := hgood y (by simp)
      have hgoodTail : ∀ z ∈ y :: rest, ¬ bad z := by
        intro z hz
        exact hgood z (by simp [hz])
      obtain ⟨endpoint, hhead, hlevel, hspace⟩ := ih hgoodTail
      have hendpoint : endpoint = y := by simpa using hhead.symm
      subst endpoint
      rcases hstep with ⟨hsite, hstepLevel, hbad⟩ | ⟨hstepLevel, hstepSite⟩
      · exact False.elim (hygood hbad)
      · refine ⟨x, by simp, ?_, ?_⟩
        · omega
        · have hstepSite' : _root_.hammingDist x.1 y.1 ≤ 2 := by
            simpa [_root_.hammingDist_comm] using hstepSite
          have htri := _root_.hammingDist_triangle x.1 y.1 start.1
          calc
            _root_.hammingDist x.1 start.1 ≤
                _root_.hammingDist x.1 y.1 + _root_.hammingDist y.1 start.1 := htri
            _ ≤ 2 + 2 * (start.2.val - y.2.val) := Nat.add_le_add hstepSite' hspace
            _ = 2 * (start.2.val - x.2.val) := by omega

private theorem scaleFailure9_forces_bad {P : Params9} {hc : HeightChoice9 P} {n : ℕ}
    {C : Finset (Pos9 P hc n)} {t s η : ℝ} {R : ℕ}
    {Pp A : Pos9 P hc n → Bool} {start : HeightState9 P hc n}
    (hfail : scaleFailure9 C t s η R Pp A start)
    (hηlt : η < 1) (hR : 0 < R) :
    ∃ x ∈ scaleBall9 start R, scaleBad9 C t s Pp A x := by
  classical
  by_contra hnone
  push_neg at hnone
  obtain ⟨endpoint, rest, hpath, hsite, hlevel, hmetric, hrise⟩ := hfail
  have hgood : ∀ x ∈ endpoint :: rest, ¬ scaleBad9 C t s Pp A x := by
    intro x hx hbad
    have hxball : x ∈ scaleBall9 start R := by
      simp [scaleBall9, hsite x hx, hlevel x hx]
    exact hnone x hxball hbad
  have hbounds := heightPath9_head_bounds_of_good hpath hgood
  obtain ⟨head, hhead, hheadLevel, hheadSpace⟩ := hbounds
  have hheadEq : head = endpoint := by simpa using hhead.symm
  subst head
  let k := start.2.val - endpoint.2.val
  have hdistLevel : Nat.dist endpoint.2.val start.2.val = k := by
    dsimp [k]
    exact Nat.dist_eq_sub_of_le hheadLevel
  have hspaceMetric : (_root_.hammingDist endpoint.1 start.1 + 1) / 2 ≤ k := by
    dsimp [k] at hheadSpace ⊢
    omega
  have hmax : max (Nat.dist endpoint.2.val start.2.val)
      ((_root_.hammingDist endpoint.1 start.1 + 1) / 2) ≤ k := by
    exact max_le (by rw [hdistLevel]) hspaceMetric
  have hkcast : (k : ℝ) ≤ η * (R : ℝ) := by
    have hkEq : (k : ℝ) = (start.2.val : ℝ) - (endpoint.2.val : ℝ) := by
      dsimp [k]
      rw [Nat.cast_sub hheadLevel]
    rw [hkEq]
    linarith [hrise]
  have hRk : R ≤ k := hmetric.trans hmax
  have hRposReal : 0 < (R : ℝ) := by exact_mod_cast hR
  have hηRlt : η * (R : ℝ) < (R : ℝ) := by
    calc
      η * (R : ℝ) < 1 * (R : ℝ) := mul_lt_mul_of_pos_right hηlt hRposReal
      _ = (R : ℝ) := by ring
  have hklt : (k : ℝ) < (R : ℝ) := hkcast.trans_lt hηRlt
  have hRkReal : (R : ℝ) ≤ (k : ℝ) := by exact_mod_cast hRk
  linarith

private theorem scaleBad9_finite_union_probability {P : Params9} {hc : HeightChoice9 P} {n : ℕ}
    {c t s : ℝ} (hbase : HeightBase9 P hc n c)
    (ht₁ : 1 / 3 ≤ t) (ht₂ : t ≤ 1) (hs : 1 / 8 ≤ s)
    (C : Finset (Pos9 P hc n)) (S : Finset (HeightState9 P hc n)) :
    (heightLaw9 P hc n).pr (fun ω => ∃ x ∈ S,
      scaleBad9 C t s ω.1 ω.2 x) ≤ (S.card : ℝ) * Real.exp (-((n : ℝ) ^ c)) := by
  calc
    (heightLaw9 P hc n).pr (fun ω => ∃ x ∈ S, scaleBad9 C t s ω.1 ω.2 x) ≤
        ∑ x ∈ S, (heightLaw9 P hc n).pr (fun ω => scaleBad9 C t s ω.1 ω.2 x) :=
      finProb_pr_exists_finset_le_sum (heightLaw9 P hc n) S
        (fun x ω => scaleBad9 C t s ω.1 ω.2 x)
    _ ≤ ∑ x ∈ S, Real.exp (-((n : ℝ) ^ c)) := by
      apply Finset.sum_le_sum
      intro x hx
      simpa [scaleBad9] using hbase C t s ht₁ ht₂ hs x.1 x.2
    _ = (S.card : ℝ) * Real.exp (-((n : ℝ) ^ c)) := by simp

private theorem scaleFailure9_fixed_start_probability {P : Params9} {hc : HeightChoice9 P}
    {n : ℕ} {c t s η : ℝ} {R : ℕ}
    (hbase : HeightBase9 P hc n c)
    (ht₁ : 1 / 3 ≤ t) (ht₂ : t ≤ 1) (hs : 1 / 8 ≤ s)
    (hηlt : η < 1) (hR : 0 < R)
    (C : Finset (Pos9 P hc n)) (start : HeightState9 P hc n) :
    (heightLaw9 P hc n).pr (fun ω => scaleFailure9 C t s η R ω.1 ω.2 start) ≤
      ((scaleBall9 start R).card : ℝ) * Real.exp (-((n : ℝ) ^ c)) := by
  calc
    (heightLaw9 P hc n).pr (fun ω => scaleFailure9 C t s η R ω.1 ω.2 start) ≤
        (heightLaw9 P hc n).pr (fun ω => ∃ x ∈ scaleBall9 start R,
          scaleBad9 C t s ω.1 ω.2 x) := by
            apply finProb_pr_mono (heightLaw9 P hc n)
            intro ω hω
            exact scaleFailure9_forces_bad hω hηlt hR
    _ ≤ ((scaleBall9 start R).card : ℝ) * Real.exp (-((n : ℝ) ^ c)) :=
      scaleBad9_finite_union_probability hbase ht₁ ht₂ hs C (scaleBall9 start R)

private theorem reach_level_le_for_path9 {P : Params9} {hc : HeightChoice9 P} {n : ℕ}
    (Pp A : Pos9 P hc n → Bool) (vq : CubeVertex n) (R : ℕ)
    {v : CubeVertex n} {j : ℕ}
    (h : Reach9 (P := P) (hc := hc) (n := n) Pp A vq R v j) : j ≤ hc.levels n := by
  induction h with
  | start v hdist => simp
  | up v j hj hreach hbad ih => omega
  | down v v' j hreach hdistRoot hstep ih => omega

private theorem reach9_to_heightPath {P : Params9} {hc : HeightChoice9 P} {n : ℕ}
    (Pp A : Pos9 P hc n → Bool) (vq : CubeVertex n) (R : ℕ)
    {v : CubeVertex n} {j : ℕ}
    (h : Reach9 (P := P) (hc := hc) (n := n) Pp A vq R v j) :
    ∃ start : HeightState9 P hc n, ∃ l : List (HeightState9 P hc n),
      HeightPath9 (heightStep9 (fun x => badAt9 (P := P) (hc := hc) (n := n) Pp A x.1 x.2))
        ((v, ⟨j, by have := reach_level_le_for_path9 Pp A vq R h; omega⟩) :: l) start ∧
      start.2.val = 0 ∧
      (∀ x ∈ ((v, ⟨j, by have := reach_level_le_for_path9 Pp A vq R h; omega⟩) :: l),
        _root_.hammingDist x.1 vq ≤ R) := by
  induction h with
  | start v hdist =>
      refine ⟨(v, ⟨0, by omega⟩), ⟨[], ?_⟩⟩
      constructor
      · simpa using (HeightPath9.singleton (step := heightStep9
          (fun x => badAt9 (P := P) (hc := hc) (n := n) Pp A x.1 x.2)) (v, ⟨0, by omega⟩))
      · constructor
        · rfl
        · intro x hx
          simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
          subst x
          exact hdist
  | @up v j hj hreach hbad ih =>
      obtain ⟨start, l, hp, hstart, hlocal⟩ := ih
      let x : HeightState9 P hc n := (v, ⟨j, by omega⟩)
      let y : HeightState9 P hc n := (v, ⟨j + 1, by omega⟩)
      refine ⟨start, ⟨x :: l, ?_⟩⟩
      constructor
      · have hedge : heightStep9
            (fun z => badAt9 (P := P) (hc := hc) (n := n) Pp A z.1 z.2) x y := by
          left
          exact ⟨rfl, rfl, hbad⟩
        simpa [x, y] using HeightPath9.cons hedge hp
      · constructor
        · exact hstart
        · intro z hz
          simp only [List.mem_cons] at hz
          rcases hz with rfl | hz
          · have hxlocal := hlocal x (by simp [x])
            simpa [x, y] using hxlocal
          · exact hlocal _ (by simpa [x] using hz)
  | @down v v' j hreach hdistRoot hstep ih =>
      obtain ⟨start, l, hp, hstart, hlocal⟩ := ih
      have hjle : j + 1 ≤ hc.levels n := reach_level_le_for_path9 Pp A vq R hreach
      let x : HeightState9 P hc n := (v, ⟨j + 1, by omega⟩)
      let y : HeightState9 P hc n := (v', ⟨j, by omega⟩)
      refine ⟨start, ⟨x :: l, ?_⟩⟩
      constructor
      · have hedge : heightStep9
            (fun z => badAt9 (P := P) (hc := hc) (n := n) Pp A z.1 z.2) x y := by
          right
          exact ⟨rfl, hstep⟩
        simpa [x, y] using HeightPath9.cons hedge hp
      · constructor
        · exact hstart
        · intro z hz
          simp only [List.mem_cons] at hz
          rcases hz with rfl | hz
          · exact hdistRoot
          · exact hlocal _ (by simpa [x] using hz)

private theorem heightPath9_suffix {P : Params9} {hc : HeightChoice9 P} {n : ℕ}
    {bad : HeightState9 P hc n → HeightState9 P hc n → Prop}
    {l : List (HeightState9 P hc n)} {start : HeightState9 P hc n}
    (hp : HeightPath9 bad l start) {x : HeightState9 P hc n} (hx : x ∈ l) :
    ∃ rest, HeightPath9 bad (x :: rest) start ∧ ∀ z ∈ x :: rest, z ∈ l := by
  induction hp generalizing x with
  | singleton y =>
      simp only [List.mem_singleton] at hx
      subst x
      exact ⟨[], HeightPath9.singleton y, by simp⟩
  | @cons head next tail start hstep htail ih =>
      simp only [List.mem_cons] at hx
      rcases hx with rfl | hx
      · refine ⟨next :: tail, HeightPath9.cons hstep htail, ?_⟩
        intro z hz
        exact hz
      · have hxTail : x ∈ next :: tail := by
          simpa only [List.mem_cons] using hx
        obtain ⟨suffix, hsuffix, hsub⟩ := ih hxTail
        refine ⟨suffix, hsuffix, ?_⟩
        intro z hz
        exact List.mem_cons_of_mem _ (hsub z hz)

private theorem heightPath9_segmentFromMember {P : Params9} {hc : HeightChoice9 P} {n : ℕ}
    {bad : HeightState9 P hc n → HeightState9 P hc n → Prop}
    {l : List (HeightState9 P hc n)} {root : HeightState9 P hc n}
    (hp : HeightPath9 bad l root) {y : HeightState9 P hc n} (hy : y ∈ l) :
    ∃ head suffix tail, l = (head :: suffix) ++ tail ∧ l.head? = some head ∧
      HeightPath9 bad (head :: suffix) y ∧ ∀ z ∈ head :: suffix, z ∈ l := by
  induction hp generalizing y with
  | singleton x =>
      have hyx : y = x := by simpa using hy
      subst y
      exact ⟨x, [], [], by simp, by simp, HeightPath9.singleton x, by simp⟩
  | @cons head next rest root hstep htail ih =>
      rcases List.mem_cons.mp hy with hyHead | hyTail
      · subst y
        exact ⟨head, [], next :: rest, by simp, by simp, HeightPath9.singleton head, by simp⟩
      · obtain ⟨segmentHead, suffix, tail, hprefix, hhead, hpath, hsub⟩ := ih hyTail
        have hhead' : segmentHead = next := by simpa using hhead.symm
        subst segmentHead
        refine ⟨head, next :: suffix, tail, ?_, by simp, HeightPath9.cons hstep hpath, ?_⟩
        · simpa using congrArg (List.cons head) hprefix
        · intro z hz
          rcases List.mem_cons.mp hz with rfl | hz
          · simp
          · exact List.mem_cons_of_mem _ (hsub z hz)

private theorem heightPath9_has_intermediate_level {P : Params9} {hc : HeightChoice9 P} {n : ℕ}
    {bad : HeightState9 P hc n → HeightState9 P hc n → Prop}
    {l : List (HeightState9 P hc n)} {start : HeightState9 P hc n}
    (hstepUnit : ∀ x y, bad x y → heightMetric9 x y ≤ 1)
    (hp : HeightPath9 bad l start) :
    ∃ endpoint, l.head? = some endpoint ∧
      ∀ j, min start.2.val endpoint.2.val ≤ j → j ≤ max start.2.val endpoint.2.val →
        ∃ x ∈ l, x.2.val = j := by
  induction hp with
  | singleton x =>
      refine ⟨x, by simp, ?_⟩
      intro j hlow hhigh
      have hj : j = x.2.val := by omega
      exact ⟨x, by simp, hj.symm⟩
  | @cons head next rest start hstep htail ih =>
      obtain ⟨tailHead, htailHead, htailRange⟩ := ih
      have htailHead' : tailHead = next := by simpa using htailHead.symm
      subst tailHead
      refine ⟨head, by simp, ?_⟩
      intro j hlow hhigh
      by_cases hjeq : j = head.2.val
      · exact ⟨head, by simp, hjeq.symm⟩
      · have hstepMetric := hstepUnit next head hstep
        have hlevels : Nat.dist next.2.val head.2.val ≤ 1 :=
          (Nat.le_max_left _ _).trans hstepMetric
        have hstepLevels : next.2.val ≤ head.2.val + 1 ∧
            head.2.val ≤ next.2.val + 1 := by
          rcases le_total next.2.val head.2.val with h | h
          · rw [Nat.dist_eq_sub_of_le h] at hlevels
            constructor <;> omega
          · rw [Nat.dist_eq_sub_of_le_right h] at hlevels
            constructor <;> omega
        rcases hstepLevels with ⟨hnextHead, hheadNext⟩
        have hlow' : min start.2.val next.2.val ≤ j := by omega
        have hhigh' : j ≤ max start.2.val next.2.val := by omega
        obtain ⟨x, hx, hxlevel⟩ := htailRange j hlow' hhigh'
        exact ⟨x, List.mem_cons_of_mem _ hx, hxlevel⟩

private theorem heightPath9_levelBandSegment9 {P : Params9} {hc : HeightChoice9 P} {n : ℕ}
    {bad : HeightState9 P hc n → Prop} {l : List (HeightState9 P hc n)}
    {start : HeightState9 P hc n}
    (hp : HeightPath9 (heightStep9 bad) l start) :
    ∃ endpoint, l.head? = some endpoint ∧
      ∀ j, start.2.val ≤ j → j ≤ endpoint.2.val →
        ∃ childStart suffix,
          HeightPath9 (heightStep9 bad) (endpoint :: suffix) childStart ∧
          childStart.2.val = j ∧
          (∀ z ∈ endpoint :: suffix, j ≤ z.2.val) ∧
          (∀ z ∈ endpoint :: suffix, z ∈ l) := by
  induction hp with
  | singleton x =>
      refine ⟨x, by simp, ?_⟩
      intro j hstart hj
      have hjEq : j = x.2.val := by omega
      subst j
      exact ⟨x, [], HeightPath9.singleton x, rfl, by simp, by simp⟩
  | @cons head next rest start hstep htail ih =>
      obtain ⟨tailHead, htailHead, htailBand⟩ := ih
      have htailHead' : tailHead = next := by simpa using htailHead.symm
      subst tailHead
      refine ⟨head, by simp, ?_⟩
      intro j hstart hj
      by_cases hjHead : j = head.2.val
      · subst j
        exact ⟨head, [], HeightPath9.singleton head, rfl, by intro z hz; simp at hz; subst z; omega,
          by simp⟩
      · have hstepMetric := heightStep9_metric_le_one hstep
        have hlevelDist : Nat.dist next.2.val head.2.val ≤ 1 :=
          (Nat.le_max_left _ _).trans hstepMetric
        have hheadLe : head.2.val ≤ next.2.val + 1 := by
          have hsymm : Nat.dist head.2.val next.2.val ≤ 1 := by
            simpa [Nat.dist_comm] using hlevelDist
          have htri := Nat.dist_tri_left' head.2.val next.2.val
          omega
        have hjNext : j ≤ next.2.val := by omega
        by_cases hjNextEq : j = next.2.val
        · subst j
          refine ⟨next, [next], HeightPath9.cons hstep (HeightPath9.singleton next), rfl, ?_, by simp⟩
          intro z hz
          simp only [List.mem_cons] at hz
          rcases hz with rfl | hz
          · omega
          · simp at hz
            subst z
            rfl
        · obtain ⟨childStart, suffix, hpath, hchildLevel, hband, hsub⟩ :=
            htailBand j hstart hjNext
          have hchildHead : childStart.2.val = j := hchildLevel
          refine ⟨childStart, next :: suffix, HeightPath9.cons hstep hpath,
            hchildHead, ?_, ?_⟩
          · intro z hz
            rcases List.mem_cons.mp hz with rfl | hz'
            · omega
            · exact hband z hz'
          · intro z hz
            rcases List.mem_cons.mp hz with rfl | hz'
            · simp
            · exact List.mem_cons_of_mem _ (hsub z hz')

private theorem heightPath9_has_intermediate_value9 {P : Params9} {hc : HeightChoice9 P} {n : ℕ}
    {bad : HeightState9 P hc n → Prop} {l : List (HeightState9 P hc n)}
    {start : HeightState9 P hc n} (f : HeightState9 P hc n → ℕ)
    (hstep : ∀ x y, heightStep9 bad x y → Nat.dist (f x) (f y) ≤ 1)
    (hp : HeightPath9 (heightStep9 bad) l start) :
    ∃ endpoint, l.head? = some endpoint ∧
      ∀ k, min (f start) (f endpoint) ≤ k → k ≤ max (f start) (f endpoint) →
        ∃ x ∈ l, f x = k := by
  induction hp with
  | singleton x =>
      refine ⟨x, by simp, ?_⟩
      intro k hlow hhigh
      have hk : f x = k := by omega
      exact ⟨x, by simp, hk⟩
  | @cons head next rest start hstep' htail ih =>
      obtain ⟨tailHead, htailHead, htailRange⟩ := ih
      have htailHead' : tailHead = next := by simpa using htailHead.symm
      subst tailHead
      refine ⟨head, by simp, ?_⟩
      intro k hlow hhigh
      by_cases hkHead : k = f head
      · exact ⟨head, by simp, hkHead.symm⟩
      · have hstepDist : Nat.dist (f next) (f head) ≤ 1 := hstep next head hstep'
        have hstepValues : f next ≤ f head + 1 ∧ f head ≤ f next + 1 := by
          rcases le_total (f next) (f head) with h | h
          · rw [Nat.dist_eq_sub_of_le h] at hstepDist
            constructor <;> omega
          · rw [Nat.dist_eq_sub_of_le_right h] at hstepDist
            constructor <;> omega
        rcases hstepValues with ⟨hnextHead, hheadNext⟩
        have hlow' : min (f start) (f next) ≤ k := by omega
        have hhigh' : k ≤ max (f start) (f next) := by omega
        obtain ⟨x, hx, hfx⟩ := htailRange k hlow' hhigh'
        exact ⟨x, List.mem_cons_of_mem _ hx, hfx⟩

private theorem heightPath9_firstExitValue9 {P : Params9} {hc : HeightChoice9 P} {n : ℕ}
    {bad : HeightState9 P hc n → Prop} {l : List (HeightState9 P hc n)}
    {start : HeightState9 P hc n} (f : HeightState9 P hc n → ℕ)
    (hstep : ∀ x y, heightStep9 bad x y → Nat.dist (f x) (f y) ≤ 1)
    (hp : HeightPath9 (heightStep9 bad) l start) (R : ℕ)
    (hstart : f start ≤ R) (hexit : ∃ x ∈ l, R ≤ f x) :
    ∃ endpoint rest, HeightPath9 (heightStep9 bad) (endpoint :: rest) start ∧
      (∀ z ∈ endpoint :: rest, z ∈ l) ∧
      (∀ z ∈ rest, f z < R) ∧ f endpoint = R := by
  induction hp generalizing R with
  | singleton x =>
      obtain ⟨z, hz, hzR⟩ := hexit
      have hzx : z = x := by simpa using hz
      subst z
      have hxR : f x = R := by omega
      exact ⟨x, [], HeightPath9.singleton x, by simp, by simp, hxR⟩
  | @cons head next tail start hstep' htail ih =>
      by_cases htailExit : ∃ z ∈ next :: tail, R ≤ f z
      · obtain ⟨endpoint, rest, hpath, hsub, hclose, heq⟩ := ih R hstart htailExit
        refine ⟨endpoint, rest, hpath, ?_, hclose, heq⟩
        intro z hz
        exact List.mem_cons_of_mem _ (hsub z hz)
      · have htailLess : ∀ z ∈ next :: tail, f z < R := by
          intro z hz
          by_contra hnot
          exact htailExit ⟨z, hz, Nat.le_of_not_gt hnot⟩
        obtain ⟨z, hz, hzR⟩ := hexit
        have hzHead : z = head := by
          rcases List.mem_cons.mp hz with hzEq | hzTail
          · exact hzEq
          · exact False.elim (htailExit ⟨z, hzTail, hzR⟩)
        subst z
        have hstepDist : Nat.dist (f next) (f head) ≤ 1 := hstep next head hstep'
        have hheadLe : f head ≤ f next + 1 := by
          rcases le_total (f next) (f head) with h | h
          · rw [Nat.dist_eq_sub_of_le h] at hstepDist
            omega
          · omega
        have hnextLess : f next < R := htailLess next (by simp)
        have hheadEq : f head = R := by omega
        refine ⟨head, next :: tail, HeightPath9.cons hstep' htail, ?_, ?_, hheadEq⟩
        · intro z hz
          exact hz
        · intro z hz
          simp only [List.mem_cons] at hz
          rcases hz with rfl | hz
          · exact hnextLess
          · exact htailLess z (List.mem_cons_of_mem _ hz)

private theorem list_split_first_match9 {α : Type*} (f : α → ℕ) (r : ℕ) (l : List α)
    (h : ∃ x ∈ l, f x = r) :
    ∃ pre x post, l = pre ++ x :: post ∧ f x = r ∧ ∀ z ∈ pre, f z ≠ r := by
  induction l with
  | nil => simp at h
  | cons head tail ih =>
      by_cases hhead : f head = r
      · exact ⟨[], head, tail, by simp, hhead, by simp⟩
      · have htail : ∃ x ∈ tail, f x = r := by
          rcases h with ⟨x, hx, hfx⟩
          rcases List.mem_cons.mp hx with hxeq | hxtail
          · subst x
            exact (hhead hfx).elim
          · exact ⟨x, hxtail, hfx⟩
        obtain ⟨pre, x, post, hsplit, hfx, hpre⟩ := ih htail
        refine ⟨head :: pre, x, post, ?_, hfx, ?_⟩
        · simp [hsplit]
        · intro z hz
          simp only [List.mem_cons] at hz
          rcases hz with hzeq | hzpre
          · subst z
            exact hhead
          · exact hpre z hzpre

private theorem heightPath9_firstValueSegment9 {P : Params9} {hc : HeightChoice9 P} {n : ℕ}
    {bad : HeightState9 P hc n → Prop} {l : List (HeightState9 P hc n)}
    {start : HeightState9 P hc n} (f : HeightState9 P hc n → ℕ)
    (hp : HeightPath9 (heightStep9 bad) l start) {r : ℕ}
    (hmatch : ∃ x ∈ l, f x = r) :
    ∃ pre x post, l = (pre ++ [x]) ++ post ∧ f x = r ∧
      (∀ z ∈ pre, f z ≠ r) ∧
      HeightPath9 (heightStep9 bad) (pre ++ [x]) x := by
  induction hp generalizing r with
  | singleton x =>
      obtain ⟨z, hz, hzval⟩ := hmatch
      have hzx : z = x := by simpa using hz
      subst z
      refine ⟨[], x, [], ?_, hzval, ?_, HeightPath9.singleton x⟩
      · simp
      · simp
  | @cons head next rest start hstep htail ih =>
      by_cases hhead : f head = r
      · refine ⟨[], head, next :: rest, ?_, hhead, by simp, ?_⟩
        · simp
        · simpa using (HeightPath9.singleton head)
      · have htailMatch : ∃ x ∈ next :: rest, f x = r := by
          rcases hmatch with ⟨x, hx, hfx⟩
          rcases List.mem_cons.mp hx with hxeq | hxtail
          · subst x
            exact (hhead hfx).elim
          · exact ⟨x, hxtail, hfx⟩
        obtain ⟨pre, x, post, hsplit, hfx, hpre, hpath⟩ := ih htailMatch
        refine ⟨head :: pre, x, post, ?_, hfx, ?_, ?_⟩
        · calc
            head :: next :: rest = head :: ((pre ++ [x]) ++ post) := by rw [hsplit]
            _ = ((head :: pre) ++ [x]) ++ post := by simp [List.append_assoc]
        · intro z hz
          simp only [List.mem_cons] at hz
          rcases hz with rfl | hz
          · exact hhead
          · exact hpre z hz
        · cases pre with
          | nil =>
              have hsplit' : next :: rest = x :: post := by simpa using hsplit
              have hnextEq : next = x := (List.cons.inj hsplit').1
              subst next
              have hpath' : HeightPath9 (heightStep9 bad) [x] x := by simpa using hpath
              simpa using HeightPath9.cons hstep hpath'
          | cons first preTail =>
              have hsplit' : next :: rest = first :: ((preTail ++ [x]) ++ post) := by
                simpa [List.append_assoc] using hsplit
              have hnextEq : next = first := (List.cons.inj hsplit').1
              subst first
              have hpath' : HeightPath9 (heightStep9 bad) (next :: (preTail ++ [x])) x := by
                simpa [List.append_assoc] using hpath
              simpa [List.append_assoc] using HeightPath9.cons hstep hpath'

private inductive ListRadialUnit9 {α : Type*} (f : α → ℕ) : List α → Prop
  | nil : ListRadialUnit9 f []
  | one (x : α) : ListRadialUnit9 f [x]
  | cons {x y : α} {tail : List α} (hxy : Nat.dist (f x) (f y) ≤ 1)
      (htail : ListRadialUnit9 f (y :: tail)) : ListRadialUnit9 f (x :: y :: tail)

private theorem heightPath9_radialUnitList9 {P : Params9} {hc : HeightChoice9 P} {n : ℕ}
    {bad : HeightState9 P hc n → Prop} {l : List (HeightState9 P hc n)}
    {start : HeightState9 P hc n} (f : HeightState9 P hc n → ℕ)
    (hstep : ∀ x y, heightStep9 bad x y → Nat.dist (f x) (f y) ≤ 1)
    (hp : HeightPath9 (heightStep9 bad) l start) : ListRadialUnit9 f l := by
  induction hp with
  | singleton x => exact ListRadialUnit9.one x
  | @cons head next rest start hstep' htail ih =>
      have hxy : Nat.dist (f head) (f next) ≤ 1 := by
        simpa [Nat.dist_comm] using hstep next head hstep'
      exact ListRadialUnit9.cons hxy ih

private theorem listRadialUnit9_prefix {α : Type*} {f : α → ℕ} {pre post : List α}
    (h : ListRadialUnit9 f (pre ++ post)) : ListRadialUnit9 f pre := by
  induction pre generalizing post with
  | nil => exact ListRadialUnit9.nil
  | cons head tail ih =>
      cases tail with
      | nil => exact ListRadialUnit9.one head
      | cons next rest =>
          have h' : ListRadialUnit9 f (head :: next :: (rest ++ post)) := by
            simpa [List.append_assoc] using h
          cases h' with
          | cons hstep htail =>
              exact ListRadialUnit9.cons hstep (by simpa [List.append_assoc] using ih htail)

private theorem listRadialUnit9_lower_bound {α : Type*} {f : α → ℕ} {r : ℕ}
    {l : List α} (hunit : ListRadialUnit9 f l)
    (hno : ∀ z ∈ l, f z ≠ r)
    (hstart : ∀ x, l.head? = some x → r ≤ f x) :
    ∀ z ∈ l, r ≤ f z := by
  induction hunit with
  | nil => simp
  | one x =>
      intro z hz
      have hzEq : z = x := by simpa using hz
      subst z
      exact hstart x (by simp)
  | @cons x y tail hxy htail ih =>
      have hfx : r ≤ f x := hstart x (by simp)
      have hfxne : f x ≠ r := hno x (by simp)
      have hfxgt : r < f x := by omega
      have hyge : r ≤ f y := by
        by_contra hy
        have hylt : f y < r := Nat.lt_of_not_ge hy
        have hyx : f y ≤ f x := by omega
        rw [Nat.dist_eq_sub_of_le_right hyx] at hxy
        omega
      have hnoTail : ∀ z ∈ y :: tail, f z ≠ r := by
        intro z hz
        exact hno z (List.mem_cons_of_mem _ hz)
      have hstartTail : ∀ z, (y :: tail).head? = some z → r ≤ f z := by
        intro z hz
        have hzEq : z = y := by simpa using hz.symm
        subst z
        exact hyge
      have hallTail := ih hnoTail hstartTail
      intro z hz
      rcases List.mem_cons.mp hz with rfl | hzTail
      · exact hfx
      · exact hallTail z hzTail

private theorem heightPath9_start_mem {P : Params9} {hc : HeightChoice9 P} {n : ℕ}
    {bad : HeightState9 P hc n → HeightState9 P hc n → Prop}
    {l : List (HeightState9 P hc n)} {start : HeightState9 P hc n}
    (hp : HeightPath9 bad l start) : start ∈ l := by
  induction hp with
  | singleton x => simp
  | cons hstep htail ih => exact List.mem_cons_of_mem _ ih

private theorem heightPath9_annularBlock9 {P : Params9} {hc : HeightChoice9 P} {n : ℕ}
    {bad : HeightState9 P hc n → Prop} {l : List (HeightState9 P hc n)}
    {start : HeightState9 P hc n} (f : HeightState9 P hc n → ℕ)
    (hstep : ∀ x y, heightStep9 bad x y → Nat.dist (f x) (f y) ≤ 1)
    (hp : HeightPath9 (heightStep9 bad) l start) {inner outer : ℕ}
    (hstart : f start = inner) (hgap : inner < outer)
    (hexit : ∃ x ∈ l, outer ≤ f x) :
    ∃ outerHit innerHit blockRest,
      f outerHit = outer ∧ f innerHit = inner ∧
      HeightPath9 (heightStep9 bad) (outerHit :: blockRest) innerHit ∧
      (∀ z ∈ outerHit :: blockRest, inner ≤ f z ∧ f z ≤ outer) ∧
      (∀ z ∈ outerHit :: blockRest, z ∈ l) := by
  have hstartle : f start ≤ outer := by omega
  obtain ⟨outerHit, outerRest, houterPath, houterSub, houterClose, houterEq⟩ :=
    heightPath9_firstExitValue9 f hstep hp outer hstartle hexit
  have hinnerMem : start ∈ outerHit :: outerRest := heightPath9_start_mem houterPath
  obtain ⟨pre, innerHit, post, hsplit, hinnerEq, hpreNo, hblock⟩ :=
    heightPath9_firstValueSegment9 f houterPath ⟨start, hinnerMem, hstart⟩
  have hunitBlock := heightPath9_radialUnitList9 f hstep hblock
  have hunitPre : ListRadialUnit9 f pre :=
    listRadialUnit9_prefix (pre := pre) (post := [innerHit]) hunitBlock
  have hpreNonempty : pre ≠ [] := by
    intro hnil
    have hsplit' : outerHit :: outerRest = innerHit :: post := by
      simpa [hnil] using hsplit
    have heq : outerHit = innerHit := (List.cons.inj hsplit').1
    have : outer = inner := by rw [← houterEq, heq, hinnerEq]
    omega
  cases pre with
  | nil => exact (hpreNonempty rfl).elim
  | cons first preTail =>
      have hsplit' : outerHit :: outerRest =
          first :: ((preTail ++ [innerHit]) ++ post) := by
        simpa [List.append_assoc] using hsplit
      have hfirstEq : first = outerHit := (List.cons.inj hsplit').1.symm
      subst first
      have hstartPre : ∀ x, (outerHit :: preTail).head? = some x → inner ≤ f x := by
        intro x hx
        have hxEq : x = outerHit := by simpa using hx.symm
        subst x
        rw [houterEq]
        omega
      have hlowPre := listRadialUnit9_lower_bound hunitPre hpreNo hstartPre
      have hlow : ∀ z ∈ outerHit :: preTail ++ [innerHit], inner ≤ f z := by
        intro z hz
        rcases List.mem_append.mp hz with hzpre | hzlast
        · exact hlowPre z hzpre
        · have hzeq : z = innerHit := by simpa using hzlast
          subst z
          rw [hinnerEq]
      have hblockSub : ∀ z ∈ outerHit :: preTail ++ [innerHit], z ∈ outerHit :: outerRest := by
        intro z hz
        rw [hsplit']
        exact List.mem_append.mpr (Or.inl hz)
      have hupper : ∀ z ∈ outerHit :: preTail ++ [innerHit], f z ≤ outer := by
        intro z hz
        have hz' := hblockSub z hz
        rcases List.mem_cons.mp hz' with rfl | hzRest
        · rw [houterEq]
        · exact le_of_lt (houterClose z hzRest)
      let blockRest := preTail ++ [innerHit]
      have hblock' : HeightPath9 (heightStep9 bad) (outerHit :: blockRest) innerHit := by
        simpa [blockRest, List.append_assoc] using hblock
      refine ⟨outerHit, innerHit, blockRest, houterEq, hinnerEq, hblock', ?_, ?_⟩
      · intro z hz
        exact ⟨hlow z (by simpa [blockRest, List.append_assoc] using hz),
          hupper z (by simpa [blockRest, List.append_assoc] using hz)⟩
      · intro z hz
        exact houterSub z (hblockSub z (by simpa [blockRest, List.append_assoc] using hz))

private theorem heightMetric9_radialVariation_le {P : Params9} {hc : HeightChoice9 P} {n : ℕ}
    (root x y : HeightState9 P hc n) :
    Nat.dist (heightMetric9 x root) (heightMetric9 y root) ≤ heightMetric9 x y := by
  have hxy := heightMetric9_triangle x y root
  have hyx := heightMetric9_triangle y x root
  have hyx' : heightMetric9 y root ≤ heightMetric9 x y + heightMetric9 x root := by
    simpa [heightMetric9_comm] using hyx
  rcases le_total (heightMetric9 x root) (heightMetric9 y root) with h | h
  · rw [Nat.dist_eq_sub_of_le h]
    omega
  · rw [Nat.dist_eq_sub_of_le_right h]
    omega

private theorem heightMetric9_ge_radial_gap {P : Params9} {hc : HeightChoice9 P} {n : ℕ}
    (root x y : HeightState9 P hc n) {r s D : ℕ}
    (hx : heightMetric9 x root = r) (hy : heightMetric9 y root = s)
    (hgap : D ≤ Nat.dist r s) : D ≤ heightMetric9 x y := by
  have hradial := heightMetric9_radialVariation_le root x y
  rw [hx, hy] at hradial
  exact hgap.trans hradial

private inductive HeightAnnularChain9 {P : Params9} {hc : HeightChoice9 P} {n : ℕ}
    (bad : HeightState9 P hc n → Prop) (root : HeightState9 P hc n) (gap : ℕ)
    (endpoint : HeightState9 P hc n) : ℕ → HeightState9 P hc n → ℤ → Prop
  | terminal {x : HeightState9 P hc n} {suffix : List (HeightState9 P hc n)}
      (hp : HeightPath9 (heightStep9 bad) (endpoint :: suffix) x) :
      HeightAnnularChain9 bad root gap endpoint 0 x
        ((x.2.val : ℤ) - (endpoint.2.val : ℤ))
  | cons {m : ℕ} {x inner outer : HeightState9 P hc n} {drop : ℤ}
      {preRest blockRest : List (HeightState9 P hc n)}
      (hinner : heightMetric9 inner root = heightMetric9 x root)
      (houter : heightMetric9 outer root = heightMetric9 x root + gap)
      (hpre : HeightPath9 (heightStep9 bad) (inner :: preRest) x)
      (hblock : HeightPath9 (heightStep9 bad) (outer :: blockRest) inner)
      (hannular : ∀ z ∈ outer :: blockRest,
        heightMetric9 x root ≤ heightMetric9 z root ∧
          heightMetric9 z root ≤ heightMetric9 x root + gap)
      (htail : HeightAnnularChain9 bad root gap endpoint m outer drop) :
      HeightAnnularChain9 bad root gap endpoint (m + 1) x
        ((x.2.val : ℤ) - (outer.2.val : ℤ) + drop)

private theorem heightPath9_annularChain_exists9 {P : Params9} {hc : HeightChoice9 P} {n : ℕ}
    {bad : HeightState9 P hc n → Prop} {l : List (HeightState9 P hc n)}
    {start endpoint : HeightState9 P hc n}
    (hp : HeightPath9 (heightStep9 bad) (endpoint :: l) start)
    (root : HeightState9 P hc n) (r gap q : ℕ)
    (hstep : ∀ x y, heightStep9 bad x y →
      Nat.dist (heightMetric9 x root) (heightMetric9 y root) ≤ 1)
    (hgap : 0 < gap)
    (hstart : heightMetric9 start root = r)
    (hreach : r + q * gap ≤ heightMetric9 endpoint root) :
    ∃ drop, HeightAnnularChain9 bad root gap endpoint q start drop ∧
      drop = (start.2.val : ℤ) - (endpoint.2.val : ℤ) := by
  induction q generalizing start l r hp hstart with
  | zero =>
      refine ⟨(start.2.val : ℤ) - (endpoint.2.val : ℤ), HeightAnnularChain9.terminal hp, rfl⟩
  | succ q ih =>
      have hmul : (q + 1) * gap = q * gap + gap := by
        rw [Nat.add_mul]
        simp
      have hreach' := hreach
      rw [hmul] at hreach'
      have houterReach : r + gap ≤ heightMetric9 endpoint root := by omega
      obtain ⟨outerHit, innerHit, blockRest, houterEq, hinnerEq, hblock,
        hannular, hblockSub⟩ :=
        heightPath9_annularBlock9 (fun x => heightMetric9 x root) hstep hp
          hstart (by omega) ⟨endpoint, by simp, houterReach⟩
      have hinnerMem : innerHit ∈ endpoint :: l :=
        hblockSub innerHit (heightPath9_start_mem hblock)
      obtain ⟨preRest, hpre, _hpreSub⟩ := heightPath9_suffix hp hinnerMem
      have houterMem : outerHit ∈ endpoint :: l := hblockSub outerHit (by simp)
      obtain ⟨segHead, suffix, _tail, _hsplit, hhead, htail, _htailSub⟩ :=
        heightPath9_segmentFromMember hp houterMem
      have hheadEq : segHead = endpoint := by
        simpa using hhead.symm.trans (by simp : (endpoint :: l).head? = some endpoint)
      subst segHead
      have hremaining : (r + gap) + q * gap ≤ heightMetric9 endpoint root := by omega
      have houterStart : heightMetric9 outerHit root = r + gap := houterEq
      obtain ⟨drop, htailChain, hdrop⟩ := ih htail (r + gap) houterStart hremaining
      let drop' : ℤ := (start.2.val : ℤ) - (outerHit.2.val : ℤ) + drop
      refine ⟨drop', HeightAnnularChain9.cons ?_ ?_ hpre hblock ?_ htailChain, ?_⟩
      · calc
          heightMetric9 innerHit root = r := hinnerEq
          _ = heightMetric9 start root := hstart.symm
      · calc
          heightMetric9 outerHit root = r + gap := houterEq
          _ = heightMetric9 start root + gap := by rw [hstart]
      · intro z hz
        have hzBounds := hannular z hz
        constructor
        · simpa [hstart] using hzBounds.1
        · simpa [hstart] using hzBounds.2
      · dsimp [drop']
        rw [hdrop]
        ring

private theorem heightPath9_has_intermediate_radius9 {P : Params9} {hc : HeightChoice9 P} {n : ℕ}
    {bad : HeightState9 P hc n → Prop} {l : List (HeightState9 P hc n)}
    {start : HeightState9 P hc n} (hp : HeightPath9 (heightStep9 bad) l start)
    {endpoint : HeightState9 P hc n} (hhead : l.head? = some endpoint) (R : ℕ)
    (hR : R ≤ heightMetric9 endpoint start) :
    ∀ r ≤ R, ∃ x ∈ l, heightMetric9 x start = r := by
  obtain ⟨head, hhead', hrange⟩ := heightPath9_has_intermediate_value9
    (fun x => heightMetric9 x start)
    (fun x y h => (heightMetric9_radialVariation_le start x y).trans
      (heightStep9_metric_le_one h)) hp
  have hheadEq : head = endpoint := by simpa using hhead'.symm.trans hhead
  subst head
  intro r hr
  have hlow : min (heightMetric9 start start) (heightMetric9 endpoint start) ≤ r := by
    simp [heightMetric9]
  have hhigh : r ≤ max (heightMetric9 start start) (heightMetric9 endpoint start) := by
    have hr' : r ≤ heightMetric9 endpoint start := hr.trans hR
    simpa [heightMetric9] using hr'
  exact hrange r hlow hhigh

private theorem heightPath9_radialFamily9 {P : Params9} {hc : HeightChoice9 P} {n : ℕ}
    {bad : HeightState9 P hc n → Prop} {l : List (HeightState9 P hc n)}
    {start : HeightState9 P hc n} (hp : HeightPath9 (heightStep9 bad) l start)
    {endpoint : HeightState9 P hc n} (hhead : l.head? = some endpoint) (R : ℕ)
    (hR : R ≤ heightMetric9 endpoint start) :
    ∃ f : Fin (R + 1) → HeightState9 P hc n,
      ∀ r, f r ∈ l ∧ heightMetric9 (f r) start = r.val := by
  have hstates : ∀ r : Fin (R + 1), ∃ x ∈ l, heightMetric9 x start = r.val := by
    intro r
    exact heightPath9_has_intermediate_radius9 hp hhead R hR r.val (by omega)
  choose f hf using hstates
  exact ⟨f, hf⟩

private theorem heightPath9_nextRadialState9 {P : Params9} {hc : HeightChoice9 P} {n : ℕ}
    {bad : HeightState9 P hc n → Prop} {l : List (HeightState9 P hc n)}
    {start : HeightState9 P hc n} (hp : HeightPath9 (heightStep9 bad) l start)
    {endpoint : HeightState9 P hc n} (hhead : l.head? = some endpoint)
    (root : HeightState9 P hc n) (r gap : ℕ)
    (hstart : heightMetric9 start root = r)
    (hgap : r + gap ≤ heightMetric9 endpoint root) :
    ∃ next suffix, next ∈ l ∧ heightMetric9 next root = r + gap ∧
      HeightPath9 (heightStep9 bad) (endpoint :: suffix) next ∧
      (∀ z ∈ endpoint :: suffix, z ∈ l) := by
  have hstepRadial : ∀ x y, heightStep9 bad x y →
      Nat.dist (heightMetric9 x root) (heightMetric9 y root) ≤ 1 := by
    intro x y hxy
    exact (heightMetric9_radialVariation_le root x y).trans (heightStep9_metric_le_one hxy)
  obtain ⟨head, hhead', hrange⟩ :=
    heightPath9_has_intermediate_value9 (fun x => heightMetric9 x root) hstepRadial hp
  have hheadEq : head = endpoint := by simpa using hhead'.symm.trans hhead
  subst head
  have hlow : min (heightMetric9 start root) (heightMetric9 endpoint root) ≤ r + gap := by
    rw [hstart]
    omega
  have hhigh : r + gap ≤ max (heightMetric9 start root) (heightMetric9 endpoint root) := by
    rw [hstart]
    omega
  obtain ⟨next, hnext, hnextRadial⟩ := hrange (r + gap) hlow hhigh
  obtain ⟨segmentHead, suffix, _tail, _hprefix, hsegmentHead, hsegment, hsegmentSub⟩ :=
    heightPath9_segmentFromMember hp hnext
  have hsegmentHead' : segmentHead = endpoint := by simpa using hsegmentHead.symm.trans hhead
  subst segmentHead
  refine ⟨next, suffix, hnext, hnextRadial, hsegment, ?_⟩
  exact hsegmentSub

private inductive HeightRadialChain9 {P : Params9} {hc : HeightChoice9 P} {n : ℕ}
    (bad : HeightState9 P hc n → Prop) (root : HeightState9 P hc n) (gap : ℕ)
    (endpoint : HeightState9 P hc n) : ℕ → HeightState9 P hc n → ℤ → Prop
  | terminal {x : HeightState9 P hc n} {suffix : List (HeightState9 P hc n)}
      (hp : HeightPath9 (heightStep9 bad) (endpoint :: suffix) x) :
      HeightRadialChain9 bad root gap endpoint 0 x
        ((x.2.val : ℤ) - (endpoint.2.val : ℤ))
  | cons {m : ℕ} {x y : HeightState9 P hc n} {drop : ℤ}
      {suffix : List (HeightState9 P hc n)}
      (hxy : heightMetric9 y root = heightMetric9 x root + gap)
      (hsegment : HeightPath9 (heightStep9 bad) (y :: suffix) x)
      (hy : HeightRadialChain9 bad root gap endpoint m y drop) :
      HeightRadialChain9 bad root gap endpoint (m + 1) x
        ((x.2.val : ℤ) - (y.2.val : ℤ) + drop)

private theorem heightPath9_radialChain_exists9 {P : Params9} {hc : HeightChoice9 P} {n : ℕ}
    {bad : HeightState9 P hc n → Prop} {l : List (HeightState9 P hc n)}
    {start : HeightState9 P hc n} {endpoint : HeightState9 P hc n}
    (hp : HeightPath9 (heightStep9 bad) (endpoint :: l) start)
    (root : HeightState9 P hc n) (r gap q : ℕ)
    (hstart : heightMetric9 start root = r)
    (hreach : r + q * gap ≤ heightMetric9 endpoint root) :
    ∃ z suffix drop,
      HeightRadialChain9 bad root gap endpoint q start drop ∧
      HeightPath9 (heightStep9 bad) (endpoint :: suffix) z ∧
      (∀ x ∈ endpoint :: suffix, x ∈ endpoint :: l) ∧
      heightMetric9 z root = r + q * gap ∧
      drop = (start.2.val : ℤ) - (endpoint.2.val : ℤ) := by
  induction q generalizing start l r hp hstart with
  | zero =>
      refine ⟨start, l, (start.2.val : ℤ) - (endpoint.2.val : ℤ),
        HeightRadialChain9.terminal hp, hp, ?_, ?_, ?_⟩
      · intro x hx
        exact hx
      · simpa using hstart
      · rfl
  | succ q ih =>
      have hmul : (q + 1) * gap = q * gap + gap := by
        rw [Nat.add_mul]
        simp
      have hreach' := hreach
      rw [hmul] at hreach'
      have hnextReach : r + gap ≤ heightMetric9 endpoint root := by omega
      have hhead : (endpoint :: l).head? = some endpoint := by simp
      obtain ⟨next, suffix₁, hnext, hnextRadius, hpath₁, hsub₁⟩ :=
        heightPath9_nextRadialState9 hp hhead root r gap hstart hnextReach
      have hremaining : (r + gap) + q * gap ≤ heightMetric9 endpoint root := by omega
      obtain ⟨z, suffix₂, drop₂, hchain, hpath₂, hsub₂, hradial, hdrop⟩ :=
        ih hpath₁ (r + gap) hnextRadius hremaining
      have hnextRadius' : heightMetric9 next root = heightMetric9 start root + gap := by
        rw [hstart]
        exact hnextRadius
      obtain ⟨blockRest, hblock, _hblockSub⟩ := heightPath9_suffix hp hnext
      have hsub : ∀ x ∈ endpoint :: suffix₂, x ∈ endpoint :: l := by
        intro x hx
        exact hsub₁ x (hsub₂ x hx)
      let drop₁ : ℤ := (start.2.val : ℤ) - (next.2.val : ℤ) + drop₂
      refine ⟨z, suffix₂, drop₁, ?_, hpath₂, hsub, ?_, ?_⟩
      · simpa [drop₁] using HeightRadialChain9.cons hnextRadius' hblock hchain
      · omega
      · dsimp [drop₁]
        rw [hdrop]
        ring

private theorem heightPath9_radialFamily_separated9 {P : Params9} {hc : HeightChoice9 P} {n R : ℕ}
    {l : List (HeightState9 P hc n)}
    {start : HeightState9 P hc n} (f : Fin (R + 1) → HeightState9 P hc n)
    (hf : ∀ r, f r ∈ l ∧ heightMetric9 (f r) start = r.val)
    (r s : Fin (R + 1)) {D : ℕ} (hgap : D ≤ Nat.dist r.val s.val) :
    D ≤ heightMetric9 (f r) (f s) := by
  exact heightMetric9_ge_radial_gap start (f r) (f s) (hf r).2 (hf s).2 hgap

private theorem scaleFailure9_from_levelBand {P : Params9} {hc : HeightChoice9 P} {n : ℕ}
    {C : Finset (Pos9 P hc n)} {t s η : ℝ} {R : ℕ}
    (Pp A : Pos9 P hc n → Bool) {l : List (HeightState9 P hc n)}
    {start : HeightState9 P hc n} (hp : HeightPath9 (heightStep9 (scaleBad9 C t s Pp A)) l start)
    (j : ℕ) (hstart : start.2.val ≤ j)
    {endpoint : HeightState9 P hc n} (hhead : l.head? = some endpoint)
    (hend : j + R ≤ endpoint.2.val) (hη : 0 ≤ η) (hR : 0 < R) :
    ∃ childStart : HeightState9 P hc n,
      childStart ∈ l ∧ childStart.2.val = j ∧
        scaleFailure9 C t s η R Pp A childStart := by
  obtain ⟨head, hhead', hband⟩ :=
    heightPath9_levelBandSegment9 hp
  have hheadEq : head = endpoint := by simpa using hhead'.symm.trans hhead
  subst head
  have hjendpoint : j ≤ endpoint.2.val := by omega
  obtain ⟨childStart, suffix, hchildPath, hchildLevel, hchildBand, hchildSub⟩ :=
    hband j hstart hjendpoint
  have hchildStartSeg : childStart ∈ endpoint :: suffix := by
    exact heightPath9_start_mem hchildPath
  have hchildMem : childStart ∈ l := hchildSub childStart hchildStartSeg
  have htopMem : endpoint ∈ endpoint :: suffix := by simp
  have htopDist : R ≤ Nat.dist endpoint.2.val childStart.2.val := by
    rw [hchildLevel, Nat.dist_eq_sub_of_le_right hjendpoint]
    omega
  have hexit : ∃ x ∈ endpoint :: suffix, R ≤ heightMetric9 x childStart :=
    ⟨endpoint, htopMem, htopDist.trans (Nat.le_max_left _ _)⟩
  obtain ⟨childEnd, rest, hfirstPath, hfirstSub, hclose, hge, hle⟩ :=
    heightPath9_firstExit9 hchildPath (fun _ _ h => heightStep9_metric_le_one h) R hR hexit
  have hmetricAll : ∀ z ∈ childEnd :: rest, heightMetric9 z childStart ≤ R := by
    intro z hz
    rcases List.mem_cons.mp hz with rfl | hz
    · exact hle
    · exact Nat.le_of_lt (hclose z hz)
  have hmetricEq : heightMetric9 childEnd childStart = R := by omega
  have hmetricEq' : max (Nat.dist childEnd.2.val childStart.2.val)
      ((_root_.hammingDist childEnd.1 childStart.1 + 1) / 2) = R := by
    simpa [heightMetric9] using hmetricEq
  have hsite : ∀ z ∈ childEnd :: rest, _root_.hammingDist z.1 childStart.1 ≤ 16 * R := by
    intro z hz
    have hzmetric := hmetricAll z hz
    have hzspace : (_root_.hammingDist z.1 childStart.1 + 1) / 2 ≤ R := by
      exact (Nat.le_max_right _ _).trans hzmetric
    omega
  have hlevel : ∀ z ∈ childEnd :: rest, Nat.dist z.2.val childStart.2.val ≤ 8 * R := by
    intro z hz
    have hzmetric := hmetricAll z hz
    have hzlevel : Nat.dist z.2.val childStart.2.val ≤ R :=
      (Nat.le_max_left _ _).trans hzmetric
    omega
  have hchildEndBand : j ≤ childEnd.2.val :=
    hchildBand childEnd (hfirstSub childEnd (by simp))
  have hrise : (childStart.2.val : ℝ) ≤ (childEnd.2.val : ℝ) + η * (R : ℝ) := by
    rw [hchildLevel]
    have hjreal : (j : ℝ) ≤ (childEnd.2.val : ℝ) := by exact_mod_cast hchildEndBand
    have hηR : 0 ≤ η * (R : ℝ) := mul_nonneg hη (Nat.cast_nonneg _)
    linarith
  refine ⟨childStart, hchildMem, hchildLevel, ?_⟩
  exact ⟨childEnd, rest, hfirstPath, hsite, hlevel, hmetricEq'.ge, hrise⟩

private theorem scaleFailure9_of_metricExit9 {P : Params9} {hc : HeightChoice9 P} {n : ℕ}
    {C : Finset (Pos9 P hc n)} {t s η : ℝ} {R : ℕ}
    (Pp A : Pos9 P hc n → Bool) {l : List (HeightState9 P hc n)}
    {start endpoint : HeightState9 P hc n}
    (hp : HeightPath9 (heightStep9 (scaleBad9 C t s Pp A)) (endpoint :: l) start)
    (hmetricEq : heightMetric9 endpoint start = R)
    (hmetricAll : ∀ z ∈ endpoint :: l, heightMetric9 z start ≤ R)
    (hrise : (start.2.val : ℝ) ≤ (endpoint.2.val : ℝ) + η * (R : ℝ)) :
    scaleFailure9 C t s η R Pp A start := by
  have hmetricEq' : max (Nat.dist endpoint.2.val start.2.val)
      ((_root_.hammingDist endpoint.1 start.1 + 1) / 2) = R := by
    simpa [heightMetric9] using hmetricEq
  have hsite : ∀ z ∈ endpoint :: l, _root_.hammingDist z.1 start.1 ≤ 16 * R := by
    intro z hz
    have hzmetric := hmetricAll z hz
    have hzspace : (_root_.hammingDist z.1 start.1 + 1) / 2 ≤ R :=
      (Nat.le_max_right _ _).trans hzmetric
    omega
  have hlevel : ∀ z ∈ endpoint :: l, Nat.dist z.2.val start.2.val ≤ 8 * R := by
    intro z hz
    have hzmetric := hmetricAll z hz
    have hzlevel : Nat.dist z.2.val start.2.val ≤ R :=
      (Nat.le_max_left _ _).trans hzmetric
    omega
  refine ⟨endpoint, l, hp, hsite, hlevel, ?_, hrise⟩
  exact hmetricEq'.ge

private theorem scaleFailure9_from_longPath9 {P : Params9} {hc : HeightChoice9 P} {n : ℕ}
    {C : Finset (Pos9 P hc n)} {t s ηp η : ℝ} {R q₀ : ℕ}
    (Pp A : Pos9 P hc n → Bool) (hη : 0 ≤ η) (hR : 0 < R)
    (hmargin : ηp * ((q₀ * R : ℕ) : ℝ) - η * ((q₀ * R : ℕ) : ℝ) ≤ -(R : ℝ))
    {l : List (HeightState9 P hc n)} {start endpoint : HeightState9 P hc n}
    (hp : HeightPath9 (heightStep9 (scaleBad9 C t s Pp A)) (endpoint :: l) start)
    (hbudget : (start.2.val : ℝ) ≤ (endpoint.2.val : ℝ) + ηp * ((q₀ * R : ℕ) : ℝ))
    (hmetric : q₀ * R ≤ heightMetric9 endpoint start) :
    ∃ childStart ∈ endpoint :: l, scaleFailure9 C t s η R Pp A childStart := by
  have hmain : ∀ q : ℕ, ∀ budget : ℝ,
      ∀ {xs : List (HeightState9 P hc n)} {x : HeightState9 P hc n},
      HeightPath9 (heightStep9 (scaleBad9 C t s Pp A)) (endpoint :: xs) x →
      (x.2.val : ℝ) ≤ (endpoint.2.val : ℝ) + budget →
      q * R ≤ heightMetric9 endpoint x →
      budget - η * ((q * R : ℕ) : ℝ) ≤ -(R : ℝ) →
      ∃ childStart ∈ endpoint :: xs, scaleFailure9 C t s η R Pp A childStart := by
    intro q
    induction q using Nat.strong_induction_on with
    | h q ih =>
        intro budget xs x hp' hbudget' hmetric' hmargin'
        by_cases hqzero : q = 0
        · subst q
          have hbudgetR : budget ≤ -(R : ℝ) := by simpa using hmargin'
          have hendRise : x.2.val + R ≤ endpoint.2.val := by
            have hcast := hbudget'
            push_cast at hcast
            exact_mod_cast (by linarith : (x.2.val : ℝ) + (R : ℝ) ≤ (endpoint.2.val : ℝ))
          obtain ⟨childStart, hmem, hlevel, hfail⟩ :=
            scaleFailure9_from_levelBand Pp A hp' x.2.val (by omega)
              (by simp) hendRise hη hR
          exact ⟨childStart, hmem, hfail⟩
        · have hqpos : 1 ≤ q := by omega
          have hRle : R ≤ q * R := by
            have hm := Nat.mul_le_mul_right R hqpos
            simpa using hm
          have hexit : ∃ z ∈ endpoint :: xs, R ≤ heightMetric9 z x :=
            ⟨endpoint, by simp, hRle.trans hmetric'⟩
          obtain ⟨next, rest, hfirst, hfirstSub, hclose, hge, hle⟩ :=
            heightPath9_firstExit9 hp' (fun _ _ h => heightStep9_metric_le_one h) R hR hexit
          have hmetricEq : heightMetric9 next x = R := by omega
          have hmetricAll : ∀ z ∈ next :: rest, heightMetric9 z x ≤ R := by
            intro z hz
            rcases List.mem_cons.mp hz with rfl | hz
            · exact hle
            · exact Nat.le_of_lt (hclose z hz)
          by_cases hgood : (x.2.val : ℝ) ≤ (next.2.val : ℝ) + η * (R : ℝ)
          · have hfail := scaleFailure9_of_metricExit9 Pp A hfirst hmetricEq hmetricAll hgood
            exact ⟨x, heightPath9_start_mem hp', hfail⟩
          · have hbad : (next.2.val : ℝ) + η * (R : ℝ) < (x.2.val : ℝ) :=
              lt_of_not_ge hgood
            have hnextMem : next ∈ endpoint :: xs := hfirstSub next (by simp)
            obtain ⟨segHead, suffix, _tail, _hsegPrefix, hsegHead, hseg, _hsegSub⟩ :=
              heightPath9_segmentFromMember hp' hnextMem
            have hsegHead' : segHead = endpoint := by
              simpa using hsegHead.symm.trans (by simp : (endpoint :: xs).head? = some endpoint)
            subst segHead
            have htri := heightMetric9_triangle endpoint next x
            have hmul : q * R = (q - 1) * R + R := by
              have hq : (q - 1) + 1 = q := by omega
              rw [← hq, Nat.add_mul]
              simp
            have hmetricNext : (q - 1) * R ≤ heightMetric9 endpoint next := by
              have htri' : heightMetric9 endpoint x ≤ heightMetric9 endpoint next + R := by
                simpa [hmetricEq] using htri
              omega
            let budgetNext := budget - η * (R : ℝ)
            have hbudgetNext : (next.2.val : ℝ) ≤ (endpoint.2.val : ℝ) + budgetNext := by
              dsimp [budgetNext]
              linarith [hbudget', hbad]
            have hmulReal : ((q * R : ℕ) : ℝ) =
                (((q - 1) * R : ℕ) : ℝ) + (R : ℝ) := by exact_mod_cast hmul
            have hmarginNext : budgetNext - η * ((((q - 1) * R : ℕ) : ℝ)) ≤ -(R : ℝ) := by
              calc
                budgetNext - η * ((((q - 1) * R : ℕ) : ℝ)) =
                    budget - η * ((((q - 1) * R : ℕ) : ℝ) + (R : ℝ)) := by
                      dsimp [budgetNext]
                      ring
                _ = budget - η * ((q * R : ℕ) : ℝ) := by rw [← hmulReal]
                _ ≤ -(R : ℝ) := hmargin'
            obtain ⟨childStart, hchildMem, hchildFail⟩ :=
              ih (q - 1) (by omega) budgetNext hseg hbudgetNext hmetricNext hmarginNext
            have hchildMem' : childStart ∈ endpoint :: xs :=
              _hsegSub childStart hchildMem
            exact ⟨childStart, hchildMem', hchildFail⟩
  exact hmain q₀ (ηp * ((q₀ * R : ℕ) : ℝ)) hp hbudget hmetric hmargin

private theorem heightRadialChain9_edge_yields_child
    {P : Params9} {hc : HeightChoice9 P} {n : ℕ} {C : Finset (Pos9 P hc n)}
    {t s ηp η : ℝ} {q₀ R : ℕ} (Pp A : Pos9 P hc n → Bool)
    (hη : 0 ≤ η) (hR : 0 < R)
    (hmargin : ηp * ((q₀ * R : ℕ) : ℝ) - η * ((q₀ * R : ℕ) : ℝ) ≤ -(R : ℝ))
    {suffix : List (HeightState9 P hc n)}
    {start endpoint root : HeightState9 P hc n}
    (hpath : HeightPath9 (heightStep9 (scaleBad9 C t s Pp A)) (endpoint :: suffix) start)
    (hend : heightMetric9 endpoint root = heightMetric9 start root + q₀ * R)
    (hbudget : (start.2.val : ℝ) ≤ (endpoint.2.val : ℝ) +
      ηp * ((q₀ * R : ℕ) : ℝ)) :
    ∃ childStart ∈ endpoint :: suffix,
      scaleFailure9 C t s η R Pp A childStart := by
  have hstart : heightMetric9 start root = heightMetric9 start root := rfl
  have hgap : q₀ * R ≤ Nat.dist (heightMetric9 start root) (heightMetric9 endpoint root) := by
    rw [hend]
    have hle : heightMetric9 start root ≤ heightMetric9 start root + q₀ * R := by omega
    rw [Nat.dist_eq_sub_of_le hle]
    omega
  have hgap' : q₀ * R ≤ Nat.dist (heightMetric9 start root)
      (heightMetric9 start root + q₀ * R) := by simpa [hend] using hgap
  have hmetric : q₀ * R ≤ heightMetric9 endpoint start :=
    by simpa [heightMetric9_comm] using
      heightMetric9_ge_radial_gap root start endpoint hstart hend hgap'
  exact scaleFailure9_from_longPath9 Pp A hη hR hmargin hpath hbudget hmetric

private theorem heightPath9_annularBlock_childLocalized9
    {P : Params9} {hc : HeightChoice9 P} {n : ℕ} {C : Finset (Pos9 P hc n)}
    {t s ηp η : ℝ} {q₀ R : ℕ} (Pp A : Pos9 P hc n → Bool)
    (hη : 0 ≤ η) (hR : 0 < R)
    (hmargin : ηp * ((q₀ * R : ℕ) : ℝ) - η * ((q₀ * R : ℕ) : ℝ) ≤ -(R : ℝ))
    {root start endpoint : HeightState9 P hc n} {suffix : List (HeightState9 P hc n)}
    (hpath : HeightPath9 (heightStep9 (scaleBad9 C t s Pp A)) (endpoint :: suffix) start)
    (r : ℕ) (hstart : heightMetric9 start root = r)
    (hend : heightMetric9 endpoint root = r + q₀ * R)
    (hbudget : (start.2.val : ℝ) ≤ (endpoint.2.val : ℝ) +
      ηp * ((q₀ * R : ℕ) : ℝ))
    (hannular : ∀ z ∈ endpoint :: suffix,
      r ≤ heightMetric9 z root ∧ heightMetric9 z root ≤ r + q₀ * R) :
    ∃ childStart ∈ endpoint :: suffix,
      scaleFailure9 C t s η R Pp A childStart ∧
      r ≤ heightMetric9 childStart root ∧ heightMetric9 childStart root ≤ r + q₀ * R := by
  obtain ⟨childStart, hmem, hfail⟩ := heightRadialChain9_edge_yields_child
    Pp A hη hR hmargin hpath (by rw [hstart]; exact hend) hbudget
  exact ⟨childStart, hmem, hfail, (hannular childStart hmem).1, (hannular childStart hmem).2⟩

private theorem heightPath9_to_reach9 {P : Params9} {hc : HeightChoice9 P} {n : ℕ}
    (Pp A : Pos9 P hc n → Bool) (root : CubeVertex n) (R : ℕ)
    {l : List (HeightState9 P hc n)} {start : HeightState9 P hc n}
    (hp : HeightPath9 (heightStep9 (fun x => badAt9 (P := P) (hc := hc) (n := n)
        Pp A x.1 x.2)) l start)
    (hstart : start.2.val = 0) (hlocal : ∀ x ∈ l, _root_.hammingDist x.1 root ≤ R) :
    ∃ endpoint : HeightState9 P hc n, l.head? = some endpoint ∧
      Reach9 (P := P) (hc := hc) (n := n) Pp A root R endpoint.1 endpoint.2.val := by
  induction hp with
  | singleton x =>
      refine ⟨x, by simp, ?_⟩
      have hx0 : x.2.val = 0 := by simpa using hstart
      simpa [hx0] using (Reach9.start x.1 (hlocal x (by simp)))
  | @cons x y rest start hstep htail ih =>
      have hlocalTail : ∀ z ∈ y :: rest, _root_.hammingDist z.1 root ≤ R := by
        intro z hz
        exact hlocal z (by simp [hz])
      obtain ⟨endpoint, hend, hreach⟩ := ih hstart hlocalTail
      have hEndpoint : endpoint = y := by simpa using hend.symm
      subst endpoint
      have hlocalX : _root_.hammingDist x.1 root ≤ R := hlocal x (by simp)
      refine ⟨x, by simp, ?_⟩
      rcases hstep with ⟨hsite, hlevel, hbad⟩ | ⟨hlevel, hdist⟩
      · have hlt : y.2.val < hc.levels n := by
          have hxlt := x.2.isLt
          omega
        have hnew : x = (y.1, ⟨y.2.val + 1, by omega⟩) := by
          apply Prod.ext
          · exact hsite.symm
          · apply Fin.ext
            exact hlevel
        rw [hnew]
        exact Reach9.up y.1 y.2.val hlt hreach hbad
      · have hDown : y.2.val = x.2.val + 1 := hlevel
        have hreach' : Reach9 (P := P) (hc := hc) (n := n) Pp A root R y.1
            (x.2.val + 1) := by simpa [hDown] using hreach
        exact Reach9.down y.1 x.1 x.2.val hreach' hlocalX hdist

private def rootScaleFailure9 {P : Params9} {hc : HeightChoice9 P} {n : ℕ}
    (C : Finset (Pos9 P hc n)) (t s η : ℝ) (R : ℕ)
    (Pp A : Pos9 P hc n → Bool) (root : CubeVertex n) : Prop :=
  ∃ start : HeightState9 P hc n,
    _root_.hammingDist start.1 root ≤ 4 * R + 2 ∧
      scaleFailure9 C t s η R Pp A start

private theorem rootScaleFailure9_of_path {P : Params9} {hc : HeightChoice9 P} {n : ℕ}
    {t s η : ℝ} {R : ℕ} (Pp A : Pos9 P hc n → Bool) (root : CubeVertex n)
    (start endpoint : HeightState9 P hc n) (rest : List (HeightState9 P hc n))
    (hroot : _root_.hammingDist start.1 root ≤ 4 * R + 2)
    (hpath : HeightPath9 (heightStep9 (scaleBad9 Finset.univ t s Pp A))
      (endpoint :: rest) start)
    (hsite : ∀ x ∈ endpoint :: rest, _root_.hammingDist x.1 start.1 ≤ 16 * R)
    (hlevel : ∀ x ∈ endpoint :: rest, Nat.dist x.2.val start.2.val ≤ 8 * R)
    (hmetric : R ≤ max (Nat.dist endpoint.2.val start.2.val)
      ((_root_.hammingDist endpoint.1 start.1 + 1) / 2))
    (hrise : (start.2.val : ℝ) ≤ (endpoint.2.val : ℝ) + η * (R : ℝ)) :
    rootScaleFailure9 Finset.univ t s η R Pp A root := by
  refine ⟨start, ?_⟩
  constructor
  · exact hroot
  · refine ⟨endpoint, ⟨rest, ?_⟩⟩
    constructor
    · exact hpath
    constructor
    · exact hsite
    constructor
    · exact hlevel
    constructor
    · exact hmetric
    · exact hrise

private theorem heightStep9_mono {P : Params9} {hc : HeightChoice9 P} {n : ℕ}
    {bad bad' : HeightState9 P hc n → Prop}
    (hbad : ∀ x, bad x → bad' x) (x y : HeightState9 P hc n)
    (h : heightStep9 bad x y) : heightStep9 bad' x y := by
  rcases h with ⟨hxy, hlevel, hb⟩ | hdown
  · exact Or.inl ⟨hxy, hlevel, hbad x hb⟩
  · exact Or.inr hdown

private theorem heightPath9_mono {P : Params9} {hc : HeightChoice9 P} {n : ℕ}
    {bad bad' : HeightState9 P hc n → Prop}
    (hbad : ∀ x, bad x → bad' x) {l : List (HeightState9 P hc n)}
    {start : HeightState9 P hc n} (h : HeightPath9 (heightStep9 bad) l start) :
    HeightPath9 (heightStep9 bad') l start := by
  induction h with
  | singleton x => exact HeightPath9.singleton x
  | cons hstep hpath ih =>
      exact HeightPath9.cons (heightStep9_mono hbad _ _ hstep) ih

private theorem heightPath9_mono_local {P : Params9} {hc : HeightChoice9 P} {n : ℕ}
    {bad bad' : HeightState9 P hc n → Prop} {l : List (HeightState9 P hc n)}
    {start : HeightState9 P hc n}
    (hbad : ∀ x ∈ l, bad x → bad' x)
    (hpath : HeightPath9 (heightStep9 bad) l start) :
    HeightPath9 (heightStep9 bad') l start := by
  induction hpath with
  | singleton x => exact HeightPath9.singleton x
  | @cons x y rest start hstep htail ih =>
      apply HeightPath9.cons
      · rcases hstep with ⟨hsite, hlevel, hb⟩ | hdown
        · exact Or.inl ⟨hsite, hlevel, hbad y (by simp) hb⟩
        · exact Or.inr hdown
      · apply ih
        intro z hz hb
        have hz' : z = y ∨ z ∈ rest := by
          simpa only [List.mem_cons] using hz
        exact hbad z (by simp only [List.mem_cons]; exact Or.inr hz') hb

private theorem badAt9_implies_badIn9_degraded {P : Params9} {hc : HeightChoice9 P} {n : ℕ}
    {t : ℝ} (ht₁ : 1 / 3 ≤ t) (ht₂ : t ≤ 1)
    (Pp A : Pos9 P hc n → Bool) (v : CubeVertex n) (j : Fin (hc.levels n + 1))
    (hb : badAt9 (P := P) (hc := hc) (n := n) Pp A v j) :
    badIn9 Finset.univ t Pp A v j := by
  change badIn9 Finset.univ 1 Pp A v j at hb
  change badIn9 Finset.univ t Pp A v j
  rcases hb with hh | ⟨j', hj', hcrowd⟩
  · exact Or.inl hh
  · refine Or.inr ⟨j', hj', ?_⟩
    rcases hcrowd with hs | ha | hl
    · apply Or.inl
      have hp := Real.rpow_nonneg (Nat.cast_nonneg n) ((P.χ : ℝ) / 2)
      have hle := mul_le_mul_of_nonneg_right ht₂ hp
      simpa only [one_mul] using lt_of_le_of_lt hle hs
    · apply Or.inr
      apply Or.inl
      have hp := Real.rpow_nonneg (Nat.cast_nonneg n) ((P.χ : ℝ) / 2)
      have hle := mul_le_mul_of_nonneg_right ht₂ hp
      simpa only [one_mul] using lt_of_le_of_lt hle ha
    · apply Or.inr
      apply Or.inr
      have hp := Real.rpow_nonneg (Nat.cast_nonneg n) (1 - (P.σ : ℝ) + hc.eps')
      have hle := mul_le_mul_of_nonneg_right ht₂ hp
      simpa only [one_mul] using lt_of_le_of_lt hle hl

private theorem scaleBad9_of_badAt9_counts {P : Params9} {hc : HeightChoice9 P} {n : ℕ}
    {t s : ℝ} (ht₁ : 1 / 3 ≤ t) (ht₂ : t ≤ 1) (hs : s ≤ 1 / 2)
    (Pp A : Pos9 P hc n → Bool)
    (hcounts : ∀ v : CubeVertex n, ∀ j : Fin (hc.levels n + 1),
      (1 / 2 : ℝ) * (n : ℝ) ^ (10 : ℝ) ≤
        (eligCount9 Finset.univ Pp v j : ℝ))
    (x : HeightState9 P hc n)
    (hbad : badAt9 (P := P) (hc := hc) (n := n) Pp A x.1 x.2) :
    scaleBad9 Finset.univ t s Pp A x := by
  refine ⟨badAt9_implies_badIn9_degraded ht₁ ht₂ Pp A x.1 x.2 hbad, ?_⟩
  have hcount := hcounts x.1 x.2
  have hn : 0 ≤ (n : ℝ) ^ (10 : ℝ) := Real.rpow_nonneg (Nat.cast_nonneg n) _
  nlinarith

private theorem reach9_top_implies_rootScaleFailure9 {P : Params9} {hc : HeightChoice9 P} {n : ℕ}
    {t s η : ℝ} (ht₁ : 1 / 3 ≤ t) (ht₂ : t ≤ 1) (hs : s ≤ 1 / 2) (hη : 0 ≤ η)
    (Pp A : Pos9 P hc n → Bool)
    (hcounts : ∀ v : CubeVertex n, ∀ j : Fin (hc.levels n + 1),
      (1 / 2 : ℝ) * (n : ℝ) ^ (10 : ℝ) ≤
        (eligCount9 Finset.univ Pp v j : ℝ))
    (root : CubeVertex n)
    (hreach : Reach9 (P := P) (hc := hc) (n := n) Pp A root (4 * hc.levels n)
      root (hc.levels n)) :
    rootScaleFailure9 Finset.univ t s η (hc.levels n) Pp A root := by
  obtain ⟨start, rest, hpath, hstart0, hlocal⟩ :=
    reach9_to_heightPath Pp A root (4 * hc.levels n) hreach
  have hstartMem : start ∈ (root, ⟨hc.levels n, by omega⟩) :: rest :=
    heightPath9_start_mem hpath
  have hstartRoot : _root_.hammingDist start.1 root ≤ 4 * hc.levels n :=
    hlocal start hstartMem
  have hstep : ∀ x, badAt9 (P := P) (hc := hc) (n := n) Pp A x.1 x.2 →
      scaleBad9 Finset.univ t s Pp A x :=
    fun x hb => scaleBad9_of_badAt9_counts ht₁ ht₂ hs Pp A hcounts x hb
  have hpath' := heightPath9_mono hstep hpath
  let endpoint : HeightState9 P hc n :=
    (root, ⟨hc.levels n, by omega⟩)
  have hpath'' : HeightPath9 (heightStep9 (scaleBad9 Finset.univ t s Pp A))
      (endpoint :: rest) start := by
    simpa only [endpoint] using hpath'
  refine ⟨start, ?_⟩
  constructor
  · exact hstartRoot.trans (by omega)
  · refine ⟨endpoint, ⟨rest, ?_⟩⟩
    constructor
    · exact hpath''
    constructor
    · intro x hx
      have hdist := hlocal x hx
      have hstartdist := hlocal start (heightPath9_start_mem hpath)
      have hstartdist' : _root_.hammingDist root start.1 ≤ 4 * hc.levels n := by
        simpa [_root_.hammingDist_comm] using hstartdist
      have htri := _root_.hammingDist_triangle x.1 root start.1
      calc
        _root_.hammingDist x.1 start.1 ≤
            _root_.hammingDist x.1 root + _root_.hammingDist root start.1 := htri
        _ ≤ 4 * hc.levels n + 4 * hc.levels n := Nat.add_le_add hdist hstartdist'
        _ ≤ 16 * hc.levels n := by omega
    constructor
    · intro x hx
      have hxlevel := x.2.isLt
      have hx0 : start.2.val = 0 := hstart0
      simp only [hx0, Nat.dist_zero_right]
      omega
    constructor
    · have hx0 : start.2.val = 0 := hstart0
      have hend : endpoint.2.val = hc.levels n := by simp [endpoint]
      have hd : Nat.dist endpoint.2.val start.2.val = hc.levels n := by
        rw [hend, hx0, Nat.dist_zero_right]
      rw [hd]
      exact Nat.le_max_left _ _
    · have hx0 : start.2.val = 0 := hstart0
      have hend : endpoint.2.val = hc.levels n := by simp [endpoint]
      rw [hx0, hend]
      have hHnon : 0 ≤ (hc.levels n : ℝ) := Nat.cast_nonneg _
      have hprod : 0 ≤ η * (hc.levels n : ℝ) := mul_nonneg hη hHnon
      simpa using add_nonneg hHnon hprod

private noncomputable def scaleRootSupport9 {P : Params9} {hc : HeightChoice9 P} {n : ℕ}
    (root : CubeVertex n) (R : ℕ) : Finset (Pos9 P hc n) :=
  consulted9 (P := P) (hc := hc) (n := n) root (10 * R + 2)

private noncomputable def scaleSupport9 {P : Params9} {hc : HeightChoice9 P} {n : ℕ}
    (start : HeightState9 P hc n) (R : ℕ) : Finset (Pos9 P hc n) :=
  (consulted9 (P := P) (hc := hc) (n := n) start.1 (8 * R)).filter
    (fun c => Nat.dist c.level.val start.2.val ≤ 8 * R + 2)

private theorem natDist9_triangle (a b c : ℕ) :
    Nat.dist a c ≤ Nat.dist a b + Nat.dist b c := by
  by_cases hca : c ≤ a
  · rw [Nat.dist_eq_sub_of_le_right hca]
    have hab : a ≤ Nat.dist a b + b := Nat.dist_tri_left' a b
    have hbc : b ≤ Nat.dist b c + c := Nat.dist_tri_left' b c
    omega
  · have hac : a ≤ c := Nat.le_of_not_ge hca
    rw [Nat.dist_eq_sub_of_le hac]
    have hcb : c ≤ Nat.dist c b + b := Nat.dist_tri_left' c b
    have hba : b ≤ Nat.dist b a + a := Nat.dist_tri_left' b a
    have hcb' : c ≤ Nat.dist b c + b := by simpa [Nat.dist_comm] using hcb
    have hba' : b ≤ Nat.dist a b + a := by simpa [Nat.dist_comm] using hba
    omega

private theorem scaleSupport9_disjoint_of_level_separated {P : Params9} {hc : HeightChoice9 P}
    {n R : ℕ} (start start' : HeightState9 P hc n)
    (hsep : 16 * R + 4 < Nat.dist start.2.val start'.2.val) :
    Disjoint (scaleSupport9 start R) (scaleSupport9 start' R) := by
  classical
  rw [Finset.disjoint_left]
  intro c hleft hright
  have hleft' := (Finset.mem_filter.mp hleft).2
  have hright' := (Finset.mem_filter.mp hright).2
  have hleft'' : Nat.dist start.2.val c.level.val ≤ 8 * R + 2 := by
    simpa [Nat.dist_comm] using hleft'
  have hright'' : Nat.dist c.level.val start'.2.val ≤ 8 * R + 2 := hright'
  have htri := natDist9_triangle start.2.val c.level.val start'.2.val
  omega

private theorem scaleSupport9_inter_card_le {P : Params9} {hc : HeightChoice9 P} {n R : ℕ}
    (start start' : HeightState9 P hc n) :
    (scaleSupport9 start R ∩ scaleSupport9 start' R).card ≤
      (consulted9 (P := P) (hc := hc) (n := n) start.1 (8 * R) ∩
        consulted9 start'.1 (8 * R)).card := by
  apply Finset.card_le_card
  intro c hc
  rcases Finset.mem_inter.mp hc with ⟨hc₁, hc₂⟩
  exact Finset.mem_inter.mpr ⟨(Finset.mem_filter.mp hc₁).1, (Finset.mem_filter.mp hc₂).1⟩

private def HeightDepends9 {P : Params9} {hc : HeightChoice9 P} {n : ℕ}
    (f : ((Pos9 P hc n → Bool) × (Pos9 P hc n → Bool)) → ℝ)
    (S : Finset (Pos9 P hc n)) : Prop :=
  ∀ ω ω', (∀ c ∈ S, ω.1 c = ω'.1 c ∧ ω.2 c = ω'.2 c) → f ω = f ω'

private theorem finProb_expect_congr9 {α : Type*} [Fintype α] (μ : FinProb α)
    (f g : α → ℝ) (h : ∀ x, f x = g x) : μ.expect f = μ.expect g := by
  unfold FinProb.expect
  apply Finset.sum_congr rfl
  intro x hx
  rw [h x]

private theorem finProb_prod_expect9 {α β : Type*} [Fintype α] [Fintype β]
    (μ : FinProb α) (ν : FinProb β) (f : α × β → ℝ) :
    (FinProb.prod μ ν).expect f = μ.expect (fun a => ν.expect (fun b => f (a, b))) := by
  classical
  unfold FinProb.expect FinProb.prod
  rw [Fintype.sum_prod_type]
  calc
    (∑ a, ∑ b, μ.w a * ν.w b * f (a, b)) =
        ∑ a, μ.w a * (∑ b, ν.w b * f (a, b)) := by
          apply Finset.sum_congr rfl
          intro a ha
          rw [Finset.mul_sum]
          apply Finset.sum_congr rfl
          intro b hb
          ring
    _ = μ.expect (fun a => ν.expect (fun b => f (a, b))) := rfl

private theorem heightLaw9_expect_mul_of_disjoint {P : Params9} {hc : HeightChoice9 P} {n : ℕ}
    {S T : Finset (Pos9 P hc n)} (f g :
      (Pos9 P hc n → Bool) × (Pos9 P hc n → Bool) → ℝ)
    (hf : HeightDepends9 f S) (hg : HeightDepends9 g T) (hST : Disjoint S T) :
    (heightLaw9 P hc n).expect (fun ω => f ω * g ω) =
      (heightLaw9 P hc n).expect f * (heightLaw9 P hc n).expect g := by
  classical
  let fAct : (Pos9 P hc n → Bool) → ℝ := fun Pp =>
    (heightActLaw9 P hc n).expect (fun A => f (Pp, A))
  let gAct : (Pos9 P hc n → Bool) → ℝ := fun Pp =>
    (heightActLaw9 P hc n).expect (fun A => g (Pp, A))
  have hfAct : FinProb.DependsOn fAct S := by
    intro Pp Pp' hPp
    apply finProb_expect_congr9
    intro A
    apply hf
    intro c hc
    exact ⟨hPp c hc, rfl⟩
  have hgAct : FinProb.DependsOn gAct T := by
    intro Pp Pp' hPp
    apply finProb_expect_congr9
    intro A
    apply hg
    intro c hc
    exact ⟨hPp c hc, rfl⟩
  have hact (Pp : Pos9 P hc n → Bool) :
      (heightActLaw9 P hc n).expect (fun A => f (Pp, A) * g (Pp, A)) =
        fAct Pp * gAct Pp := by
    have hfA : FinProb.DependsOn (fun A => f (Pp, A)) S := by
      intro A A' hA
      apply hf
      intro c hc
      exact ⟨rfl, hA c hc⟩
    have hgA : FinProb.DependsOn (fun A => g (Pp, A)) T := by
      intro A A' hA
      apply hg
      intro c hc
      exact ⟨rfl, hA c hc⟩
    simpa [heightActLaw9, fAct, gAct] using
      (FinProb.pi_expect_mul_of_disjoint
        (fun _ : Pos9 P hc n => FinProb.bernoulli ((n : ℝ) ^ (hc.b₀ - 10)))
        (fun A => f (Pp, A)) (fun A => g (Pp, A)) S T hfA hgA hST)
  have hfPos : FinProb.DependsOn fAct S := hfAct
  have hgPos : FinProb.DependsOn gAct T := hgAct
  have hpos : (heightPosLaw9 P hc n).expect (fun Pp => fAct Pp * gAct Pp) =
      (heightPosLaw9 P hc n).expect fAct * (heightPosLaw9 P hc n).expect gAct := by
    simpa [heightPosLaw9] using
      (FinProb.pi_expect_mul_of_disjoint
        (fun _ : Pos9 P hc n =>
          FinProb.bernoulli ((n : ℝ) ^ (10 : ℝ) / (residualBall9 P n : ℝ)))
        fAct gAct S T hfPos hgPos hST)
  have hfMarginal : (heightLaw9 P hc n).expect f =
      (heightPosLaw9 P hc n).expect fAct := by
    simpa [heightLaw9, fAct] using
      (finProb_prod_expect9 (heightPosLaw9 P hc n) (heightActLaw9 P hc n)
        (fun ω => f ω))
  have hgMarginal : (heightLaw9 P hc n).expect g =
      (heightPosLaw9 P hc n).expect gAct := by
    simpa [heightLaw9, gAct] using
      (finProb_prod_expect9 (heightPosLaw9 P hc n) (heightActLaw9 P hc n)
        (fun ω => g ω))
  calc
    (heightLaw9 P hc n).expect (fun ω => f ω * g ω) =
        (heightPosLaw9 P hc n).expect
          (fun Pp => (heightActLaw9 P hc n).expect (fun A => f (Pp, A) * g (Pp, A))) := by
            simpa [heightLaw9] using
              (finProb_prod_expect9 (heightPosLaw9 P hc n) (heightActLaw9 P hc n)
                (fun ω => f ω * g ω))
    _ = (heightPosLaw9 P hc n).expect (fun Pp => fAct Pp * gAct Pp) := by
          apply finProb_expect_congr9
          exact hact
    _ = (heightPosLaw9 P hc n).expect fAct * (heightPosLaw9 P hc n).expect gAct := hpos
    _ = (heightLaw9 P hc n).expect f * (heightLaw9 P hc n).expect g := by
          rw [← hfMarginal, ← hgMarginal]

private theorem heightLaw9_pr_as_expect_indicator {P : Params9} {hc : HeightChoice9 P} {n : ℕ}
    (E : ((Pos9 P hc n → Bool) × (Pos9 P hc n → Bool)) → Prop) :
    (heightLaw9 P hc n).pr E =
      (heightLaw9 P hc n).expect
        (fun ω => @ite ℝ (E ω) (Classical.propDecidable (E ω)) 1 0) := by
  classical
  unfold FinProb.pr FinProb.expect
  apply Finset.sum_congr rfl
  intro ω hω
  by_cases h : E ω <;> simp [h]

private theorem heightLaw9_pr_and_of_disjoint {P : Params9} {hc : HeightChoice9 P} {n : ℕ}
    {S T : Finset (Pos9 P hc n)}
    (E F : ((Pos9 P hc n → Bool) × (Pos9 P hc n → Bool)) → Prop)
    (hE : ∀ ω ω', (∀ c ∈ S, ω.1 c = ω'.1 c ∧ ω.2 c = ω'.2 c) → E ω = E ω')
    (hF : ∀ ω ω', (∀ c ∈ T, ω.1 c = ω'.1 c ∧ ω.2 c = ω'.2 c) → F ω = F ω')
    (hST : Disjoint S T) :
    (heightLaw9 P hc n).pr (fun ω => E ω ∧ F ω) =
      (heightLaw9 P hc n).pr E * (heightLaw9 P hc n).pr F := by
  classical
  let f : _ → ℝ := fun ω => if E ω then 1 else 0
  let g : _ → ℝ := fun ω => if F ω then 1 else 0
  have hf : HeightDepends9 f S := by
    intro ω ω' hω
    simp [f, hE ω ω' hω]
  have hg : HeightDepends9 g T := by
    intro ω ω' hω
    simp [g, hF ω ω' hω]
  have hprod := heightLaw9_expect_mul_of_disjoint f g hf hg hST
  have hind (ω : (Pos9 P hc n → Bool) × (Pos9 P hc n → Bool)) :
      @ite ℝ (E ω ∧ F ω) (Classical.propDecidable _) 1 0 = f ω * g ω := by
    by_cases hEω : E ω <;> by_cases hFω : F ω <;> simp [f, g, hEω, hFω]
  calc
    (heightLaw9 P hc n).pr (fun ω => E ω ∧ F ω) =
        (heightLaw9 P hc n).expect (fun ω => f ω * g ω) := by
          rw [heightLaw9_pr_as_expect_indicator]
          apply finProb_expect_congr9
          exact hind
    _ = (heightLaw9 P hc n).expect f * (heightLaw9 P hc n).expect g := hprod
    _ = (heightLaw9 P hc n).pr E * (heightLaw9 P hc n).pr F := by
          rw [← heightLaw9_pr_as_expect_indicator E, ← heightLaw9_pr_as_expect_indicator F]

private theorem heightLaw9_pr_forall_disjoint {P : Params9} {hc : HeightChoice9 P} {n : ℕ}
    {κ : Type*} [Fintype κ] [DecidableEq κ]
    (I : Finset κ)
    (E : κ → ((Pos9 P hc n → Bool) × (Pos9 P hc n → Bool)) → Prop)
    (S : κ → Finset (Pos9 P hc n))
    (hE : ∀ i ω ω', (∀ c ∈ S i, ω.1 c = ω'.1 c ∧ ω.2 c = ω'.2 c) → E i ω = E i ω')
    (hdisj : ∀ i j, i ≠ j → Disjoint (S i) (S j)) :
    (heightLaw9 P hc n).pr (fun ω => ∀ i ∈ I, E i ω) =
      ∏ i ∈ I, (heightLaw9 P hc n).pr (E i) := by
  classical
  induction I using Finset.induction_on with
  | empty => simp [FinProb.pr, (heightLaw9 P hc n).sum_eq_one]
  | @insert a I ha ih =>
      let Erest : ((Pos9 P hc n → Bool) × (Pos9 P hc n → Bool)) → Prop :=
        fun ω => ∀ i ∈ I, E i ω
      let Srest : Finset (Pos9 P hc n) := I.biUnion S
      have hErest : ∀ ω ω',
          (∀ c ∈ Srest, ω.1 c = ω'.1 c ∧ ω.2 c = ω'.2 c) → Erest ω = Erest ω' := by
        intro ω ω' hagree
        apply propext
        constructor <;> intro hall i hi
        · have hsi : S i ⊆ Srest := by
            intro c hc
            exact Finset.mem_biUnion.mpr ⟨i, hi, hc⟩
          have heq := hE i ω ω' (fun c hc => hagree c (hsi hc))
          rw [← heq]
          exact hall i hi
        · have hsi : S i ⊆ Srest := by
            intro c hc
            exact Finset.mem_biUnion.mpr ⟨i, hi, hc⟩
          have heq := hE i ω ω' (fun c hc => hagree c (hsi hc))
          rw [heq]
          exact hall i hi
      have hdisjRest : Disjoint (S a) Srest := by
        apply Finset.disjoint_left.mpr
        intro c hca hcrest
        rcases Finset.mem_biUnion.mp hcrest with ⟨i, hi, hci⟩
        have hne : a ≠ i := by
          intro hEq
          subst i
          exact ha hi
        exact (Finset.disjoint_left.mp (hdisj a i hne)) hca hci
      have hrewrite (ω : (Pos9 P hc n → Bool) × (Pos9 P hc n → Bool)) :
          (∀ i ∈ insert a I, E i ω) = (E a ω ∧ Erest ω) := by
        simp [Erest, ha]
      calc
        (heightLaw9 P hc n).pr (fun ω => ∀ i ∈ insert a I, E i ω) =
            (heightLaw9 P hc n).pr (fun ω => E a ω ∧ Erest ω) := by
              congr 1
              funext ω
              exact hrewrite ω
        _ = (heightLaw9 P hc n).pr (E a) * (heightLaw9 P hc n).pr Erest := by
              exact heightLaw9_pr_and_of_disjoint (E a) Erest (hE a) hErest hdisjRest
        _ = (heightLaw9 P hc n).pr (E a) * ∏ i ∈ I, (heightLaw9 P hc n).pr (E i) := by
              rw [ih]
        _ = ∏ i ∈ insert a I, (heightLaw9 P hc n).pr (E i) := by simp [ha]

private theorem specialWord9_hammingDist_le {m n : ℕ} (hmn : m ≤ n)
    (v w : CubeVertex n) :
    _root_.hammingDist (specialWord9 m v) (specialWord9 m w) ≤ _root_.hammingDist v w := by
  classical
  let S : Finset (Fin m) := Finset.univ.filter
    (fun i => specialWord9 m v i ≠ specialWord9 m w i)
  let T : Finset (Fin n) := Finset.univ.filter (fun i => v i ≠ w i)
  let f : Fin m → Fin n := fun i => ⟨i.val, lt_of_lt_of_le i.isLt hmn⟩
  have hmaps : ∀ i ∈ S, f i ∈ T := by
    intro i hi
    have hi' := (Finset.mem_filter.mp hi).2
    have hv : specialWord9 m v i = v (f i) := by
      simp [specialWord9, f, lt_of_lt_of_le i.isLt hmn]
    have hw : specialWord9 m w i = w (f i) := by
      simp [specialWord9, f, lt_of_lt_of_le i.isLt hmn]
    simp only [T, Finset.mem_filter, Finset.mem_univ, true_and]
    rw [← hv, ← hw]
    exact hi'
  have hinj : Set.InjOn f S := by
    intro i hi j hj h
    apply Fin.ext
    simpa [f] using congrArg Fin.val h
  have hcard := Finset.card_le_card_of_injOn f hmaps hinj
  simpa [S, T, _root_.hammingDist]
    using hcard

private theorem residualWord9_hammingDist_le {m n : ℕ} (hmn : m ≤ n)
    (v w : CubeVertex n) :
    _root_.hammingDist (residualWord9 m v) (residualWord9 m w) ≤ _root_.hammingDist v w := by
  classical
  let S : Finset (Fin (n - m)) := Finset.univ.filter
    (fun i => residualWord9 m v i ≠ residualWord9 m w i)
  let T : Finset (Fin n) := Finset.univ.filter (fun i => v i ≠ w i)
  let f : Fin (n - m) → Fin n := fun i => ⟨m + i.val, by have := i.isLt; omega⟩
  have hmaps : ∀ i ∈ S, f i ∈ T := by
    intro i hi
    have hi' := (Finset.mem_filter.mp hi).2
    have hv : residualWord9 m v i = v (f i) := by
      rfl
    have hw : residualWord9 m w i = w (f i) := by
      rfl
    simp only [T, Finset.mem_filter, Finset.mem_univ, true_and]
    rw [← hv, ← hw]
    exact hi'
  have hinj : Set.InjOn f S := by
    intro i hi j hj h
    apply Fin.ext
    have hval := congrArg Fin.val h
    dsimp [f] at hval
    omega
  have hcard := Finset.card_le_card_of_injOn f hmaps hinj
  simpa [S, T, _root_.hammingDist]
    using hcard

private theorem scaleSupport9_mem_of_relevant {P : Params9} {hc : HeightChoice9 P} {n : ℕ}
    (hmn : P.m n ≤ n) (start : HeightState9 P hc n) (R : ℕ)
    (site : CubeVertex n) (j : Fin (hc.levels n + 1))
    (hsite : _root_.hammingDist site start.1 ≤ 16 * R)
    (hlevel : Nat.dist j.val start.2.val ≤ 8 * R + 2)
    (c : Pos9 P hc n)
    (hslice : _root_.hammingDist c.slice (specialWord9 (P.m n) site) ≤ 1)
    (hres : _root_.hammingDist c.location (residualWord9 (P.m n) site) ≤ P.radius n + 1)
    (hcLevel : c.level = j) :
    c ∈ scaleSupport9 start R := by
  have hspecialProj := specialWord9_hammingDist_le hmn site start.1
  have hresidualProj := residualWord9_hammingDist_le hmn site start.1
  have hspecial := _root_.hammingDist_triangle c.slice
    (specialWord9 (P.m n) site) (specialWord9 (P.m n) start.1)
  have hresidual := _root_.hammingDist_triangle c.location
    (residualWord9 (P.m n) site) (residualWord9 (P.m n) start.1)
  have hsliceRoot : _root_.hammingDist c.slice (specialWord9 (P.m n) start.1) ≤ 16 * R + 1 := by
    exact (hspecial.trans (Nat.add_le_add hslice hspecialProj)).trans (by omega)
  have hlocationRoot : _root_.hammingDist c.location (residualWord9 (P.m n) start.1) ≤
      (P.radius n + 1) + 16 * R := by
    exact (hresidual.trans (Nat.add_le_add hres hresidualProj)).trans (by omega)
  have hlevelRoot : Nat.dist c.level.val start.2.val ≤ 8 * R + 2 := by
    simpa [hcLevel] using hlevel
  simp only [scaleSupport9, consulted9, Finset.mem_filter, Finset.mem_univ,
    true_and, and_true]
  exact ⟨⟨by omega, by omega⟩, hlevelRoot⟩

private theorem filter_card_eq_after_support9 {α : Type*} [DecidableEq α]
    (C S : Finset α) (pred : α → Prop) [DecidablePred pred]
    (hrel : ∀ c ∈ C, pred c → c ∈ S) :
    (C.filter pred).card = ((C ∩ S).filter pred).card := by
  classical
  have hset : C.filter pred = (C ∩ S).filter pred := by
    ext c
    simp only [Finset.mem_filter, Finset.mem_inter]
    constructor
    · rintro ⟨hc, hp⟩
      exact ⟨⟨hc, hrel c hc hp⟩, hp⟩
    · rintro ⟨⟨hc, hs⟩, hp⟩
      exact ⟨hc, hp⟩
  exact congrArg Finset.card hset

private theorem filter_card_eq_of_mem_iff9 {α : Type*} [DecidableEq α]
    (C : Finset α) (p q : α → Prop) [DecidablePred p] [DecidablePred q]
    (hpq : ∀ x ∈ C, p x ↔ q x) :
    (C.filter p).card = (C.filter q).card := by
  classical
  apply congrArg Finset.card
  ext x
  simp only [Finset.mem_filter]
  constructor
  · rintro ⟨hx, hp⟩
    exact ⟨hx, (hpq x hx).mp hp⟩
  · rintro ⟨hx, hq⟩
    exact ⟨hx, (hpq x hx).mpr hq⟩

private theorem eligCount9_congr_on_C {P : Params9} {hc : HeightChoice9 P} {n : ℕ}
    (C : Finset (Pos9 P hc n)) (Pp Pp' : Pos9 P hc n → Bool)
    (hP : ∀ c ∈ C, Pp c = Pp' c) (v : CubeVertex n) (j : Fin (hc.levels n + 1)) :
    eligCount9 C Pp v j = eligCount9 C Pp' v j := by
  classical
  unfold eligCount9
  apply filter_card_eq_of_mem_iff9
  intro c hc'
  constructor
  · rintro ⟨hp, hs, hr, hj⟩
    refine ⟨?_, hs, hr, hj⟩
    rw [← hP c hc']
    exact hp
  · rintro ⟨hp, hs, hr, hj⟩
    refine ⟨?_, hs, hr, hj⟩
    rw [hP c hc']
    exact hp

private theorem crowdSame9_congr_on_C {P : Params9} {hc : HeightChoice9 P} {n : ℕ}
    (C : Finset (Pos9 P hc n)) (Pp Pp' A A' : Pos9 P hc n → Bool)
    (hP : ∀ c ∈ C, Pp c = Pp' c) (hA : ∀ c ∈ C, A c = A' c)
    (v : CubeVertex n) (j : Fin (hc.levels n + 1)) (ρ : ℕ) :
    crowdSame9 C Pp A v j ρ = crowdSame9 C Pp' A' v j ρ := by
  classical
  unfold crowdSame9
  apply filter_card_eq_of_mem_iff9
  intro c hc'
  simp only [activeAt9]
  constructor
  · rintro ⟨⟨hp, ha⟩, hs, hr, hj⟩
    refine ⟨⟨?_, ?_⟩, hs, hr, hj⟩
    · rw [← hP c hc']; exact hp
    · rw [← hA c hc']; exact ha
  · rintro ⟨⟨hp, ha⟩, hs, hr, hj⟩
    refine ⟨⟨?_, ?_⟩, hs, hr, hj⟩
    · rw [hP c hc']; exact hp
    · rw [hA c hc']; exact ha

private theorem crowdAdj9_congr_on_C {P : Params9} {hc : HeightChoice9 P} {n : ℕ}
    (C : Finset (Pos9 P hc n)) (Pp Pp' A A' : Pos9 P hc n → Bool)
    (hP : ∀ c ∈ C, Pp c = Pp' c) (hA : ∀ c ∈ C, A c = A' c)
    (v : CubeVertex n) (j : Fin (hc.levels n + 1)) :
    crowdAdj9 C Pp A v j = crowdAdj9 C Pp' A' v j := by
  classical
  unfold crowdAdj9
  apply filter_card_eq_of_mem_iff9
  intro c hc'
  simp only [activeAt9]
  constructor
  · rintro ⟨⟨hp, ha⟩, hs, hr, hj⟩
    refine ⟨⟨?_, ?_⟩, hs, hr, hj⟩
    · rw [← hP c hc']; exact hp
    · rw [← hA c hc']; exact ha
  · rintro ⟨⟨hp, ha⟩, hs, hr, hj⟩
    refine ⟨⟨?_, ?_⟩, hs, hr, hj⟩
    · rw [hP c hc']; exact hp
    · rw [hA c hc']; exact ha

private theorem activeAt9_congr_on_C {P : Params9} {hc : HeightChoice9 P} {n : ℕ}
    (C : Finset (Pos9 P hc n)) (Pp Pp' A A' : Pos9 P hc n → Bool)
    (hP : ∀ c ∈ C, Pp c = Pp' c) (hA : ∀ c ∈ C, A c = A' c)
    (c : Pos9 P hc n) (hc' : c ∈ C) :
    activeAt9 Pp A c ↔ activeAt9 Pp' A' c := by
  simp [activeAt9, hP c hc', hA c hc']

private theorem holeIn9_congr_on_C {P : Params9} {hc : HeightChoice9 P} {n : ℕ}
    (C : Finset (Pos9 P hc n)) (Pp Pp' A A' : Pos9 P hc n → Bool)
    (hP : ∀ c ∈ C, Pp c = Pp' c) (hA : ∀ c ∈ C, A c = A' c)
    (v : CubeVertex n) (j : Fin (hc.levels n + 1)) :
    holeIn9 C Pp A v j ↔ holeIn9 C Pp' A' v j := by
  unfold holeIn9
  constructor <;> intro h c hc' hslice hres hj
  · intro hactive'
    exact h c hc' hslice hres hj
      ((activeAt9_congr_on_C C Pp Pp' A A' hP hA c hc').mpr hactive')
  · intro hactive
    exact h c hc' hslice hres hj
      ((activeAt9_congr_on_C C Pp Pp' A A' hP hA c hc').mp hactive)

private theorem badIn9_congr_on_C {P : Params9} {hc : HeightChoice9 P} {n : ℕ}
    (C : Finset (Pos9 P hc n)) (t : ℝ) (Pp Pp' A A' : Pos9 P hc n → Bool)
    (hP : ∀ c ∈ C, Pp c = Pp' c) (hA : ∀ c ∈ C, A c = A' c)
    (v : CubeVertex n) (j : Fin (hc.levels n + 1)) :
    badIn9 C t Pp A v j ↔ badIn9 C t Pp' A' v j := by
  have hhole := holeIn9_congr_on_C C Pp Pp' A A' hP hA v j
  have hsame := crowdSame9_congr_on_C C Pp Pp' A A' hP hA
  have hadj := crowdAdj9_congr_on_C C Pp Pp' A A' hP hA
  unfold badIn9
  constructor
  · intro hbad
    rcases hbad with hh | ⟨j', hwin, hcrowd⟩
    · exact Or.inl (hhole.mp hh)
    · refine Or.inr ⟨j', hwin, ?_⟩
      rcases hcrowd with hs | ha | hl
      · exact Or.inl (by simpa [hsame v j' (P.radius n)] using hs)
      · exact Or.inr (Or.inl (by simpa [hadj v j'] using ha))
      · exact Or.inr (Or.inr (by simpa [hsame v j' (P.radius n + 1)] using hl))
  · intro hbad
    rcases hbad with hh | ⟨j', hwin, hcrowd⟩
    · exact Or.inl (hhole.mpr hh)
    · refine Or.inr ⟨j', hwin, ?_⟩
      rcases hcrowd with hs | ha | hl
      · exact Or.inl (by simpa [hsame v j' (P.radius n)] using hs)
      · exact Or.inr (Or.inl (by simpa [hadj v j'] using ha))
      · exact Or.inr (Or.inr (by simpa [hsame v j' (P.radius n + 1)] using hl))

private theorem scaleBad9_congr_on_C {P : Params9} {hc : HeightChoice9 P} {n : ℕ}
    (C : Finset (Pos9 P hc n)) (t s : ℝ) (Pp Pp' A A' : Pos9 P hc n → Bool)
    (hP : ∀ c ∈ C, Pp c = Pp' c) (hA : ∀ c ∈ C, A c = A' c)
    (x : HeightState9 P hc n) :
    scaleBad9 C t s Pp A x ↔ scaleBad9 C t s Pp' A' x := by
  have hbad := badIn9_congr_on_C C t Pp Pp' A A' hP hA x.1 x.2
  have hcount := eligCount9_congr_on_C C Pp Pp' hP x.1 x.2
  simp only [scaleBad9]
  rw [hbad, hcount]

private theorem scaleFailure9_congr_on_C {P : Params9} {hc : HeightChoice9 P} {n : ℕ}
    (C : Finset (Pos9 P hc n)) (t s η : ℝ) (R : ℕ)
    (Pp Pp' A A' : Pos9 P hc n → Bool)
    (hP : ∀ c ∈ C, Pp c = Pp' c) (hA : ∀ c ∈ C, A c = A' c)
    (start : HeightState9 P hc n) :
    scaleFailure9 C t s η R Pp A start ↔ scaleFailure9 C t s η R Pp' A' start := by
  constructor
  · rintro ⟨endpoint, rest, hpath, hsite, hlevel, hmetric, hrise⟩
    refine ⟨endpoint, rest, ?_, hsite, hlevel, hmetric, hrise⟩
    exact heightPath9_mono (fun x hb =>
      (scaleBad9_congr_on_C C t s Pp Pp' A A' hP hA x).mp hb) hpath
  · rintro ⟨endpoint, rest, hpath, hsite, hlevel, hmetric, hrise⟩
    refine ⟨endpoint, rest, ?_, hsite, hlevel, hmetric, hrise⟩
    exact heightPath9_mono (fun x hb =>
      (scaleBad9_congr_on_C C t s Pp Pp' A A' hP hA x).mpr hb) hpath

private theorem eligCount9_restrictLocal {P : Params9} {hc : HeightChoice9 P} {n : ℕ}
    (hmn : P.m n ≤ n) (C : Finset (Pos9 P hc n)) (Pp : Pos9 P hc n → Bool)
    (start state : HeightState9 P hc n) (R : ℕ)
    (hsite : _root_.hammingDist state.1 start.1 ≤ 16 * R)
    (hlevel : Nat.dist state.2.val start.2.val ≤ 8 * R + 2) :
    eligCount9 C Pp state.1 state.2 =
      eligCount9 (C ∩ scaleSupport9 start R) Pp state.1 state.2 := by
  classical
  unfold eligCount9
  apply filter_card_eq_after_support9
  intro c hc hmem
  rcases hmem with ⟨_, hslice, hres, hclevel⟩
  apply scaleSupport9_mem_of_relevant hmn start R state.1 state.2 hsite hlevel c
  · rw [hslice]
    simp
  · exact le_trans hres (by omega)
  · exact hclevel

private theorem crowdSame9_restrictLocal {P : Params9} {hc : HeightChoice9 P} {n : ℕ}
    (hmn : P.m n ≤ n) (C : Finset (Pos9 P hc n)) (Pp A : Pos9 P hc n → Bool)
    (start state : HeightState9 P hc n) (R ρ : ℕ)
    (hsite : _root_.hammingDist state.1 start.1 ≤ 16 * R)
    (hlevel : Nat.dist state.2.val start.2.val ≤ 8 * R + 2)
    (hρ : ρ ≤ P.radius n + 1) :
    crowdSame9 C Pp A state.1 state.2 ρ =
      crowdSame9 (C ∩ scaleSupport9 start R) Pp A state.1 state.2 ρ := by
  classical
  unfold crowdSame9
  apply filter_card_eq_after_support9
  intro c hc hmem
  rcases hmem with ⟨_, hslice, hres, hclevel⟩
  apply scaleSupport9_mem_of_relevant hmn start R state.1 state.2 hsite hlevel c
  · rw [hslice]
    simp
  · exact le_trans hres hρ
  · exact hclevel

private theorem crowdAdj9_restrictLocal {P : Params9} {hc : HeightChoice9 P} {n : ℕ}
    (hmn : P.m n ≤ n) (C : Finset (Pos9 P hc n)) (Pp A : Pos9 P hc n → Bool)
    (start state : HeightState9 P hc n) (R : ℕ)
    (hsite : _root_.hammingDist state.1 start.1 ≤ 16 * R)
    (hlevel : Nat.dist state.2.val start.2.val ≤ 8 * R + 2) :
    crowdAdj9 C Pp A state.1 state.2 =
      crowdAdj9 (C ∩ scaleSupport9 start R) Pp A state.1 state.2 := by
  classical
  unfold crowdAdj9
  apply filter_card_eq_after_support9
  intro c hc hmem
  rcases hmem with ⟨_, hslice, hres, hclevel⟩
  apply scaleSupport9_mem_of_relevant hmn start R state.1 state.2 hsite hlevel c
  · exact hslice.le
  · exact le_trans hres (by omega)
  · exact hclevel

private theorem holeIn9_restrictLocal {P : Params9} {hc : HeightChoice9 P} {n : ℕ}
    (hmn : P.m n ≤ n) (C : Finset (Pos9 P hc n)) (Pp A : Pos9 P hc n → Bool)
    (start state : HeightState9 P hc n) (R : ℕ)
    (hsite : _root_.hammingDist state.1 start.1 ≤ 16 * R)
    (hlevel : Nat.dist state.2.val start.2.val ≤ 8 * R + 2) :
    holeIn9 C Pp A state.1 state.2 ↔
      holeIn9 (C ∩ scaleSupport9 start R) Pp A state.1 state.2 := by
  constructor
  · intro h c hc' hslice hres hclevel
    exact h c (Finset.mem_inter.mp hc').1 hslice hres hclevel
  · intro h c hc' hslice hres hclevel
    have hsupport := scaleSupport9_mem_of_relevant hmn start R state.1 state.2 hsite hlevel c
      (by rw [hslice]; simp) (le_trans hres (by omega)) hclevel
    exact h c (Finset.mem_inter.mpr ⟨hc', hsupport⟩) hslice hres hclevel

private theorem scaleLevelWindow9 {P : Params9} {hc : HeightChoice9 P} {n : ℕ}
    {start state : HeightState9 P hc n} {R : ℕ}
    (hlevel : Nat.dist state.2.val start.2.val ≤ 8 * R)
    {j : Fin (hc.levels n + 1)} (hwindow : Nat.dist state.2.val j.val ≤ 2) :
    Nat.dist j.val start.2.val ≤ 8 * R + 2 := by
  have hwindow' : Nat.dist j.val state.2.val ≤ 2 := by
    simpa [Nat.dist_comm] using hwindow
  calc
    Nat.dist j.val start.2.val ≤
        Nat.dist j.val state.2.val + Nat.dist state.2.val start.2.val :=
      Nat.dist.triangle_inequality _ _ _
    _ ≤ 2 + 8 * R := Nat.add_le_add hwindow' hlevel
    _ = 8 * R + 2 := by omega

private theorem badIn9_restrictLocal {P : Params9} {hc : HeightChoice9 P} {n : ℕ}
    (hmn : P.m n ≤ n) (C : Finset (Pos9 P hc n)) (t : ℝ) (Pp A : Pos9 P hc n → Bool)
    (start state : HeightState9 P hc n) (R : ℕ)
    (hsite : _root_.hammingDist state.1 start.1 ≤ 16 * R)
    (hlevel : Nat.dist state.2.val start.2.val ≤ 8 * R) :
    badIn9 C t Pp A state.1 state.2 ↔
      badIn9 (C ∩ scaleSupport9 start R) t Pp A state.1 state.2 := by
  have hlevel' : Nat.dist state.2.val start.2.val ≤ 8 * R + 2 := by omega
  have hhole := holeIn9_restrictLocal hmn C Pp A start state R hsite hlevel'
  unfold badIn9
  constructor
  · intro hb
    rcases hb with hh | ⟨j, hj, hcrowd⟩
    · exact Or.inl (hhole.mp hh)
    · right
      refine ⟨j, hj, ?_⟩
      have hjwindow := scaleLevelWindow9 hlevel hj
      have hsame := crowdSame9_restrictLocal hmn C Pp A start (state.1, j) R
        (P.radius n) hsite hjwindow (by omega)
      have hadj := crowdAdj9_restrictLocal hmn C Pp A start (state.1, j) R
        hsite hjwindow
      have hlarge := crowdSame9_restrictLocal hmn C Pp A start (state.1, j) R
        (P.radius n + 1) hsite hjwindow (by omega)
      rcases hcrowd with hs | ha | hl
      · left
        simpa [hsame] using hs
      · right
        left
        simpa [hadj] using ha
      · right
        right
        simpa [hlarge] using hl
  · intro hb
    rcases hb with hh | ⟨j, hj, hcrowd⟩
    · exact Or.inl (hhole.mpr hh)
    · right
      refine ⟨j, hj, ?_⟩
      have hjwindow := scaleLevelWindow9 hlevel hj
      have hsame := crowdSame9_restrictLocal hmn C Pp A start (state.1, j) R
        (P.radius n) hsite hjwindow (by omega)
      have hadj := crowdAdj9_restrictLocal hmn C Pp A start (state.1, j) R
        hsite hjwindow
      have hlarge := crowdSame9_restrictLocal hmn C Pp A start (state.1, j) R
        (P.radius n + 1) hsite hjwindow (by omega)
      rcases hcrowd with hs | ha | hl
      · left
        simpa [← hsame] using hs
      · right
        left
        simpa [← hadj] using ha
      · right
        right
        simpa [← hlarge] using hl

private theorem scaleBad9_restrictLocal {P : Params9} {hc : HeightChoice9 P} {n : ℕ}
    (hmn : P.m n ≤ n) (C : Finset (Pos9 P hc n)) (t s : ℝ)
    (Pp A : Pos9 P hc n → Bool) (start state : HeightState9 P hc n) (R : ℕ)
    (hsite : _root_.hammingDist state.1 start.1 ≤ 16 * R)
    (hlevel : Nat.dist state.2.val start.2.val ≤ 8 * R) :
    scaleBad9 C t s Pp A state ↔
      scaleBad9 (C ∩ scaleSupport9 start R) t s Pp A state := by
  simp only [scaleBad9]
  rw [badIn9_restrictLocal hmn C t Pp A start state R hsite hlevel]
  rw [eligCount9_restrictLocal hmn C Pp start state R hsite (by omega)]

private theorem scaleFailure9_restrictLocal {P : Params9} {hc : HeightChoice9 P} {n : ℕ}
    (hmn : P.m n ≤ n) (C : Finset (Pos9 P hc n)) (t s η : ℝ) (R : ℕ)
    (Pp A : Pos9 P hc n → Bool) (start : HeightState9 P hc n) :
    scaleFailure9 C t s η R Pp A start ↔
      scaleFailure9 (C ∩ scaleSupport9 start R) t s η R Pp A start := by
  constructor
  · rintro ⟨endpoint, rest, hpath, hsite, hlevel, hmetric, hrise⟩
    refine ⟨endpoint, rest, ?_, hsite, hlevel, hmetric, hrise⟩
    apply heightPath9_mono_local ?_ hpath
    intro x hx hbad
    exact (scaleBad9_restrictLocal hmn C t s Pp A start x R
      (hsite x hx) (hlevel x hx)).mp hbad
  · rintro ⟨endpoint, rest, hpath, hsite, hlevel, hmetric, hrise⟩
    refine ⟨endpoint, rest, ?_, hsite, hlevel, hmetric, hrise⟩
    apply heightPath9_mono_local ?_ hpath
    intro x hx hbad
    exact (scaleBad9_restrictLocal hmn C t s Pp A start x R
      (hsite x hx) (hlevel x hx)).mpr hbad

private theorem scaleSupport9_subset_rootSupport9 {P : Params9} {hc : HeightChoice9 P}
    {n : ℕ} (hmn : P.m n ≤ n) (root : CubeVertex n) (start : HeightState9 P hc n)
    (R : ℕ) (hstart : _root_.hammingDist start.1 root ≤ 4 * R + 2) :
    scaleSupport9 start R ⊆ scaleRootSupport9 root R := by
  intro c hc
  simp only [scaleSupport9, Finset.mem_filter] at hc
  have hconsult' : _root_.hammingDist c.slice (specialWord9 (P.m n) start.1) ≤
        2 * (8 * R) + 1 ∧
      _root_.hammingDist c.location (residualWord9 (P.m n) start.1) ≤
        P.radius n + 2 * (8 * R) + 1 := by
    simpa only [consulted9, Finset.mem_filter, Finset.mem_univ, true_and] using hc.1
  have hconsult : _root_.hammingDist c.slice (specialWord9 (P.m n) start.1) ≤ 16 * R + 1 ∧
      _root_.hammingDist c.location (residualWord9 (P.m n) start.1) ≤ P.radius n + 16 * R + 1 := by
    rcases hconsult' with ⟨hsp, hres⟩
    exact ⟨by omega, by omega⟩
  have hspProj := specialWord9_hammingDist_le hmn start.1 root
  have hresProj := residualWord9_hammingDist_le hmn start.1 root
  have hspTri := _root_.hammingDist_triangle c.slice
    (specialWord9 (P.m n) start.1) (specialWord9 (P.m n) root)
  have hresTri := _root_.hammingDist_triangle c.location
    (residualWord9 (P.m n) start.1) (residualWord9 (P.m n) root)
  have hsp : _root_.hammingDist c.slice (specialWord9 (P.m n) root) ≤ 20 * R + 5 := by
    calc
      _root_.hammingDist c.slice (specialWord9 (P.m n) root) ≤
          _root_.hammingDist c.slice (specialWord9 (P.m n) start.1) +
            _root_.hammingDist (specialWord9 (P.m n) start.1) (specialWord9 (P.m n) root) := hspTri
      _ ≤ (16 * R + 1) + (4 * R + 2) := Nat.add_le_add hconsult.1 (le_trans hspProj hstart)
      _ ≤ 20 * R + 5 := by omega
  have hres : _root_.hammingDist c.location (residualWord9 (P.m n) root) ≤
      P.radius n + 20 * R + 5 := by
    calc
      _root_.hammingDist c.location (residualWord9 (P.m n) root) ≤
          _root_.hammingDist c.location (residualWord9 (P.m n) start.1) +
            _root_.hammingDist (residualWord9 (P.m n) start.1) (residualWord9 (P.m n) root) := hresTri
      _ ≤ (P.radius n + 16 * R + 1) + (4 * R + 2) :=
        Nat.add_le_add hconsult.2 (le_trans hresProj hstart)
      _ ≤ P.radius n + 20 * R + 5 := by omega
  simp only [scaleRootSupport9, consulted9, Finset.mem_filter, Finset.mem_univ,
    true_and]
  exact ⟨by omega, by omega⟩

private theorem scaleFailure9_dependsOnSupport {P : Params9} {hc : HeightChoice9 P}
    {n : ℕ} (hmn : P.m n ≤ n) (C S : Finset (Pos9 P hc n)) (t s η : ℝ) (R : ℕ)
    (Pp Pp' A A' : Pos9 P hc n → Bool) (start : HeightState9 P hc n)
    (hsubset : scaleSupport9 start R ⊆ S)
    (hagree : ∀ c ∈ S, Pp c = Pp' c ∧ A c = A' c) :
    scaleFailure9 C t s η R Pp A start ↔ scaleFailure9 C t s η R Pp' A' start := by
  have hlocal := scaleFailure9_restrictLocal hmn C t s η R Pp A start
  have hlocal' := scaleFailure9_restrictLocal hmn C t s η R Pp' A' start
  have hP : ∀ c ∈ C ∩ scaleSupport9 start R, Pp c = Pp' c := by
    intro c hc
    exact (hagree c (hsubset (Finset.mem_inter.mp hc).2)).1
  have hA : ∀ c ∈ C ∩ scaleSupport9 start R, A c = A' c := by
    intro c hc
    exact (hagree c (hsubset (Finset.mem_inter.mp hc).2)).2
  have hcongr := scaleFailure9_congr_on_C (C ∩ scaleSupport9 start R)
    t s η R Pp Pp' A A' hP hA start
  constructor
  · intro h
    exact hlocal'.mpr (hcongr.mp (hlocal.mp h))
  · intro h
    exact hlocal.mpr (hcongr.mpr (hlocal'.mp h))

private theorem rootScaleFailure9_dependsOn_rootSupport {P : Params9} {hc : HeightChoice9 P}
    {n : ℕ} (hmn : P.m n ≤ n) (t s η : ℝ) (R : ℕ)
    (Pp Pp' A A' : Pos9 P hc n → Bool) (root : CubeVertex n)
    (hagree : ∀ c ∈ scaleRootSupport9 root R,
      Pp c = Pp' c ∧ A c = A' c) :
    rootScaleFailure9 Finset.univ t s η R Pp A root ↔
      rootScaleFailure9 Finset.univ t s η R Pp' A' root := by
  unfold rootScaleFailure9
  constructor
  · rintro ⟨start, hstart, hfail⟩
    refine ⟨start, hstart, ?_⟩
    exact (scaleFailure9_dependsOnSupport hmn Finset.univ (scaleRootSupport9 root R)
      t s η R Pp Pp' A A' start (scaleSupport9_subset_rootSupport9 hmn root start R hstart)
      hagree).mp hfail
  · rintro ⟨start, hstart, hfail⟩
    refine ⟨start, hstart, ?_⟩
    exact (scaleFailure9_dependsOnSupport hmn Finset.univ (scaleRootSupport9 root R)
      t s η R Pp Pp' A A' start (scaleSupport9_subset_rootSupport9 hmn root start R hstart)
      hagree).mpr hfail

private def rootCountFailure9 {P : Params9} {hc : HeightChoice9 P} {n : ℕ}
    (root : CubeVertex n) (Pp : Pos9 P hc n → Bool) : Prop :=
  ∃ x : HeightState9 P hc n,
    _root_.hammingDist x.1 root ≤ 16 * hc.levels n ∧
      (eligCount9 Finset.univ Pp x.1 x.2 : ℝ) < (n : ℝ) ^ (10 : ℝ) / 2

private def rootBadPair9 {P : Params9} {hc : HeightChoice9 P} {n : ℕ}
    (t s η : ℝ) (root : CubeVertex n)
    (ω : Pos9 P hc n → Bool × Bool) : Prop :=
  let fields := (heightFieldsEquiv9 (P := P) (hc := hc) (n := n)).symm ω
  rootScaleFailure9 Finset.univ t s η (hc.levels n) fields.1 fields.2 root ∨
    rootCountFailure9 root fields.1

private theorem rootCountFailure9_dependsOn_rootSupport {P : Params9} {hc : HeightChoice9 P}
    {n : ℕ} (hmn : P.m n ≤ n) (root : CubeVertex n)
    (Pp Pp' : Pos9 P hc n → Bool)
    (hagree : ∀ c ∈ scaleRootSupport9 root (hc.levels n), Pp c = Pp' c) :
    rootCountFailure9 root Pp ↔ rootCountFailure9 root Pp' := by
  let start : HeightState9 P hc n := (root, ⟨0, by omega⟩)
  have hsubset : scaleSupport9 start (hc.levels n) ⊆
      scaleRootSupport9 root (hc.levels n) := by
    exact scaleSupport9_subset_rootSupport9 hmn root start (hc.levels n) (by simp [start])
  have hcountEq {x : HeightState9 P hc n}
      (hx : _root_.hammingDist x.1 root ≤ 16 * hc.levels n) :
      eligCount9 Finset.univ Pp x.1 x.2 = eligCount9 Finset.univ Pp' x.1 x.2 := by
    have hxlevel : Nat.dist x.2.val start.2.val ≤ 8 * hc.levels n + 2 := by
      have hxlt := x.2.isLt
      simp [start, Nat.dist_zero_right]
      omega
    have hleft := eligCount9_restrictLocal hmn Finset.univ Pp start x
      (hc.levels n) hx hxlevel
    have hright := eligCount9_restrictLocal hmn Finset.univ Pp' start x
      (hc.levels n) hx hxlevel
    have hP : ∀ c ∈ Finset.univ ∩ scaleSupport9 start (hc.levels n),
        Pp c = Pp' c := by
      intro c hc'
      exact hagree c (hsubset (Finset.mem_inter.mp hc').2)
    calc
      eligCount9 Finset.univ Pp x.1 x.2 =
          eligCount9 (Finset.univ ∩ scaleSupport9 start (hc.levels n)) Pp x.1 x.2 := hleft
      _ = eligCount9 (Finset.univ ∩ scaleSupport9 start (hc.levels n)) Pp' x.1 x.2 :=
        eligCount9_congr_on_C _ Pp Pp' hP x.1 x.2
      _ = eligCount9 Finset.univ Pp' x.1 x.2 := hright.symm
  constructor
  · rintro ⟨x, hx, hlow⟩
    exact ⟨x, hx, by rw [← hcountEq hx]; exact hlow⟩
  · rintro ⟨x, hx, hlow⟩
    exact ⟨x, hx, by rw [hcountEq hx]; exact hlow⟩

private theorem rootBadPair9_dependsOn_rootSupport {P : Params9} {hc : HeightChoice9 P}
    {n : ℕ} {t s η : ℝ} (hmn : P.m n ≤ n) (root : CubeVertex n)
    (ω ω' : Pos9 P hc n → Bool × Bool)
    (hagree : ∀ c ∈ scaleRootSupport9 root (hc.levels n), ω c = ω' c) :
    rootBadPair9 t s η root ω = rootBadPair9 t s η root ω' := by
  let fields := (heightFieldsEquiv9 (P := P) (hc := hc) (n := n)).symm ω
  let fields' := (heightFieldsEquiv9 (P := P) (hc := hc) (n := n)).symm ω'
  have hfields : ∀ c ∈ scaleRootSupport9 root (hc.levels n),
      fields.1 c = fields'.1 c ∧ fields.2 c = fields'.2 c := by
    intro c hc'
    have heq := hagree c hc'
    constructor
    · simpa [fields, fields', heightFieldsEquiv9] using congrArg Prod.fst heq
    · simpa [fields, fields', heightFieldsEquiv9] using congrArg Prod.snd heq
  have hscale := rootScaleFailure9_dependsOn_rootSupport hmn t s η
    (hc.levels n) fields.1 fields'.1 fields.2 fields'.2 root hfields
  have hcount := rootCountFailure9_dependsOn_rootSupport hmn root fields.1 fields'.1
    (fun c hc' => (hfields c hc').1)
  unfold rootBadPair9
  dsimp only
  rw [hscale, hcount]

private theorem rootCountFailure9_probability {P : Params9} {hc : HeightChoice9 P} {n : ℕ}
    (hcounts : HeightCounts9 P hc n) (root : CubeVertex n) :
    (heightLaw9 P hc n).pr (fun ω => rootCountFailure9 root ω.1) ≤ Real.exp (-(n : ℝ)) := by
  let global (Pp : Pos9 P hc n → Bool) : Prop :=
    ∃ v : CubeVertex n, ∃ j : Fin (hc.levels n + 1),
      (eligCount9 Finset.univ Pp v j : ℝ) < (n : ℝ) ^ (10 : ℝ) / 2
  calc
    (heightLaw9 P hc n).pr (fun ω => rootCountFailure9 root ω.1) ≤
        (heightLaw9 P hc n).pr (fun ω => global ω.1) := by
          apply finProb_pr_mono (heightLaw9 P hc n)
          intro ω hω
          obtain ⟨x, hx, hlow⟩ := hω
          exact ⟨x.1, x.2, hlow⟩
    _ = (heightPosLaw9 P hc n).pr global := by
      simpa [heightLaw9] using
        (prod_pr_fst (heightPosLaw9 P hc n) (heightActLaw9 P hc n) global)
    _ ≤ Real.exp (-(n : ℝ)) := by
      simpa [global, HeightCounts9] using hcounts

private theorem rootBadPair9_scope {P : Params9} {hc : HeightChoice9 P} {n : ℕ}
    {t s η : ℝ} (hmn : P.m n ≤ n) (root : CubeVertex n) :
    FinProb.DependsOn (rootBadPair9 (P := P) (hc := hc) (n := n) t s η root)
      (scaleRootSupport9 (P := P) (hc := hc) (n := n) root (hc.levels n)) := by
  intro ω ω' hagree
  exact rootBadPair9_dependsOn_rootSupport (P := P) (hc := hc) (n := n)
    hmn root ω ω' hagree

private theorem rootBadPair9_probability {P : Params9} {hc : HeightChoice9 P} {n : ℕ}
    {t s η : ℝ} (hcounts : HeightCounts9 P hc n) (root : CubeVertex n)
    (ε : ℝ)
    (hscale : (heightLaw9 P hc n).pr
      (fun ω => rootScaleFailure9 Finset.univ t s η (hc.levels n) ω.1 ω.2 root) ≤ ε) :
    (heightPairLaw9 (P := P) (hc := hc) (n := n)).pr (rootBadPair9 t s η root) ≤
      ε + Real.exp (-(n : ℝ)) := by
  let E : ((Pos9 P hc n → Bool) × (Pos9 P hc n → Bool)) → Prop :=
    fun fields => rootScaleFailure9 Finset.univ t s η (hc.levels n)
        fields.1 fields.2 root ∨ rootCountFailure9 root fields.1
  have htrans : (heightLaw9 P hc n).pr E =
      (heightPairLaw9 (P := P) (hc := hc) (n := n)).pr (rootBadPair9 t s η root) := by
    calc
      (heightLaw9 P hc n).pr E =
          (heightPairLaw9 (P := P) (hc := hc) (n := n)).pr
            (fun ω => E ((heightFieldsEquiv9 (P := P) (hc := hc) (n := n)).symm ω)) :=
        heightLaw9_pr_eq_heightPairLaw9 E
      _ = (heightPairLaw9 (P := P) (hc := hc) (n := n)).pr (rootBadPair9 t s η root) := by
        apply congrArg (FinProb.pr (heightPairLaw9 (P := P) (hc := hc) (n := n)))
        funext ω
        simp [E, rootBadPair9, heightFieldsEquiv9]
  have hE : (heightLaw9 P hc n).pr E ≤
      (heightLaw9 P hc n).pr
          (fun ω => rootScaleFailure9 Finset.univ t s η (hc.levels n) ω.1 ω.2 root) +
        (heightLaw9 P hc n).pr (fun ω => rootCountFailure9 root ω.1) := by
    simpa [E] using finProb_pr_union (heightLaw9 P hc n)
      (fun ω => rootScaleFailure9 Finset.univ t s η (hc.levels n) ω.1 ω.2 root)
      (fun ω => rootCountFailure9 root ω.1)
  calc
    (heightPairLaw9 (P := P) (hc := hc) (n := n)).pr (rootBadPair9 t s η root) =
        (heightLaw9 P hc n).pr E := htrans.symm
    _ ≤ (heightLaw9 P hc n).pr
          (fun ω => rootScaleFailure9 Finset.univ t s η (hc.levels n) ω.1 ω.2 root) +
        (heightLaw9 P hc n).pr (fun ω => rootCountFailure9 root ω.1) := hE
    _ ≤ ε + Real.exp (-(n : ℝ)) :=
      add_le_add hscale (rootCountFailure9_probability hcounts root)

private theorem heightRootLLLInput9 {P : Params9} {hc : HeightChoice9 P} {n : ℕ}
    {t s η ε x : ℝ} {Δ : ℕ}
    (hmn : P.m n ≤ n) (hcounts : HeightCounts9 P hc n)
    (hx0 : 0 ≤ x) (hx1 : x < 1)
    (hdegree : ∀ root : CubeVertex n,
      (Finset.univ.filter
        (fun root' => root' ≠ root ∧ ¬ Disjoint
          (scaleRootSupport9 (P := P) (hc := hc) (n := n) root (hc.levels n))
          (scaleRootSupport9 (P := P) (hc := hc) (n := n) root' (hc.levels n)))).card ≤ Δ)
    (hscale : ∀ root : CubeVertex n,
      (heightLaw9 P hc n).pr (fun ω =>
        rootScaleFailure9 Finset.univ t s η (hc.levels n) ω.1 ω.2 root) ≤ ε)
    (hcharge : ε + Real.exp (-(n : ℝ)) ≤ x * (1 - x) ^ Δ) :
    S07.LLLInput
      (fun _ : Pos9 P hc n => FinProb.prod
        (FinProb.bernoulli ((n : ℝ) ^ (10 : ℝ) / (residualBall9 P n : ℝ)))
        (FinProb.bernoulli ((n : ℝ) ^ (hc.b₀ - 10))))
      (fun root ω => rootBadPair9 (P := P) (hc := hc) (n := n) t s η root ω)
      (fun root => scaleRootSupport9 (P := P) (hc := hc) (n := n) root (hc.levels n)) x Δ := by
  refine ⟨hx0, hx1, ?_, ?_, ?_⟩
  · intro root
    exact rootBadPair9_scope (P := P) (hc := hc) (n := n) hmn root
  · intro root
    simpa using hdegree root
  · intro root
    change (heightPairLaw9 (P := P) (hc := hc) (n := n)).pr
        (rootBadPair9 (P := P) (hc := hc) (n := n) t s η root) ≤ x * (1 - x) ^ Δ
    exact (rootBadPair9_probability hcounts root ε (hscale root)).trans hcharge

private theorem one_sub_pow_lower9 {x : ℝ} (hx0 : 0 ≤ x) (hx1 : x ≤ 1) (k : ℕ) :
    1 - (k : ℝ) * x ≤ (1 - x) ^ k := by
  induction k with
  | zero => simp
  | succ k ih =>
      have hbase0 : 0 ≤ 1 - x := by linarith
      have hbase1 : 1 - x ≤ 1 := by linarith
      have hpow1 : (1 - x) ^ k ≤ 1 := pow_le_one₀ hbase0 hbase1
      calc
        1 - ((k + 1 : ℕ) : ℝ) * x = (1 - (k : ℝ) * x) - x := by push_cast; ring
        _ ≤ (1 - x) ^ k - x := sub_le_sub_right ih x
        _ ≤ (1 - x) ^ k * (1 - x) := by
          have hmul := mul_nonneg hx0 (sub_nonneg.mpr hpow1)
          nlinarith
        _ = (1 - x) ^ (k + 1) := by rw [pow_succ]

private theorem local_lemma_charge9 (Δ : ℕ) (p : ℝ)
    (hp : p ≤ 1 / (4 * ((Δ + 1 : ℕ) : ℝ))) :
    ∃ x : ℝ, 0 ≤ x ∧ x < 1 ∧ p ≤ x * (1 - x) ^ Δ := by
  let x : ℝ := 1 / (2 * ((Δ + 1 : ℕ) : ℝ))
  have hden : 0 < 2 * ((Δ + 1 : ℕ) : ℝ) := by positivity
  have hx0 : 0 ≤ x := by dsimp [x]; positivity
  have hx1 : x < 1 := by
    dsimp [x]
    have hΔ : 1 ≤ ((Δ + 1 : ℕ) : ℝ) := by exact_mod_cast (Nat.le_add_left 1 Δ)
    rw [div_lt_one hden]
    nlinarith
  have hΔx : ((Δ : ℝ) * x) ≤ 1 / 2 := by
    have hΔle : (Δ : ℝ) ≤ ((Δ + 1 : ℕ) : ℝ) := by exact_mod_cast (Nat.le_add_right Δ 1)
    calc
      (Δ : ℝ) * x = (Δ : ℝ) / (2 * ((Δ + 1 : ℕ) : ℝ)) := by dsimp [x]; ring
      _ ≤ ((Δ + 1 : ℕ) : ℝ) / (2 * ((Δ + 1 : ℕ) : ℝ)) :=
        div_le_div_of_nonneg_right hΔle (by positivity)
      _ = 1 / 2 := by field_simp [ne_of_gt hden]
  have hpow : 1 / 2 ≤ (1 - x) ^ Δ := by
    have h := one_sub_pow_lower9 hx0 (le_of_lt hx1) Δ
    push_cast at h
    linarith
  refine ⟨x, hx0, hx1, ?_⟩
  calc
    p ≤ 1 / (4 * ((Δ + 1 : ℕ) : ℝ)) := hp
    _ = x / 2 := by dsimp [x]; field_simp; norm_num
    _ ≤ x * (1 - x) ^ Δ := by nlinarith [hx0, hpow]

private theorem heightRootLLLInput9_of_small {P : Params9} {hc : HeightChoice9 P} {n : ℕ}
    {t s η ε : ℝ} {Δ : ℕ}
    (hmn : P.m n ≤ n) (hcounts : HeightCounts9 P hc n)
    (hdegree : ∀ root : CubeVertex n,
      (Finset.univ.filter
        (fun root' => root' ≠ root ∧ ¬ Disjoint
          (scaleRootSupport9 (P := P) (hc := hc) (n := n) root (hc.levels n))
          (scaleRootSupport9 (P := P) (hc := hc) (n := n) root' (hc.levels n)))).card ≤ Δ)
    (hscale : ∀ root : CubeVertex n,
      (heightLaw9 P hc n).pr (fun ω =>
        rootScaleFailure9 Finset.univ t s η (hc.levels n) ω.1 ω.2 root) ≤ ε)
    (hsmall : ε + Real.exp (-(n : ℝ)) ≤ 1 / (4 * ((Δ + 1 : ℕ) : ℝ))) :
    ∃ x : ℝ, 0 ≤ x ∧ x < 1 ∧ S07.LLLInput
      (fun _ : Pos9 P hc n => FinProb.prod
        (FinProb.bernoulli ((n : ℝ) ^ (10 : ℝ) / (residualBall9 P n : ℝ)))
        (FinProb.bernoulli ((n : ℝ) ^ (hc.b₀ - 10))))
      (fun root ω => rootBadPair9 t s η root ω)
      (fun root => scaleRootSupport9 (P := P) (hc := hc) (n := n) root (hc.levels n)) x Δ := by
  obtain ⟨x, hx0, hx1, hcharge⟩ :=
    local_lemma_charge9 Δ (ε + Real.exp (-(n : ℝ))) hsmall
  exact ⟨x, hx0, hx1,
    heightRootLLLInput9 hmn hcounts hx0 hx1 hdegree hscale hcharge⟩

private theorem exists_pair_fields_avoiding_rootBad9 {P : Params9} {hc : HeightChoice9 P}
    {n : ℕ} {t s η x : ℝ} {Δ : ℕ}
    (hinput : S07.LLLInput
      (fun _ : Pos9 P hc n => FinProb.prod
        (FinProb.bernoulli ((n : ℝ) ^ (10 : ℝ) / (residualBall9 P n : ℝ)))
        (FinProb.bernoulli ((n : ℝ) ^ (hc.b₀ - 10))))
      (fun root ω => rootBadPair9 t s η root ω)
      (fun root => scaleRootSupport9 (P := P) (hc := hc) (n := n) root (hc.levels n)) x Δ) :
    ∃ ω : Pos9 P hc n → Bool × Bool, ∀ root, ¬ rootBadPair9 t s η root ω := by
  let coord : Pos9 P hc n → FinProb (Bool × Bool) := fun _ =>
    FinProb.prod
      (FinProb.bernoulli ((n : ℝ) ^ (10 : ℝ) / (residualBall9 P n : ℝ)))
      (FinProb.bernoulli ((n : ℝ) ^ (hc.b₀ - 10)))
  let Bad : CubeVertex n → (Pos9 P hc n → Bool × Bool) → Prop :=
    fun root ω => rootBadPair9 t s η root ω
  let scopes : CubeVertex n → Finset (Pos9 P hc n) :=
    fun root => scaleRootSupport9 root (hc.levels n)
  rcases S07.cond_product_bound coord Bad scopes x Δ hinput with ⟨hpositive, _⟩
  change 0 < (heightPairLaw9 (P := P) (hc := hc) (n := n)).pr
    (fun ω => ∀ root, ¬ rootBadPair9 t s η root ω) at hpositive
  by_contra hnone
  push_neg at hnone
  have hzero : (heightPairLaw9 (P := P) (hc := hc) (n := n)).pr
      (fun ω => ∀ root, ¬ rootBadPair9 t s η root ω) = 0 := by
    unfold FinProb.pr
    apply Finset.sum_eq_zero
    intro ω hω
    have hnot : ¬ (∀ root, ¬ rootBadPair9 t s η root ω) := by
      intro hall
      obtain ⟨root, hbad⟩ := hnone ω
      exact hall root hbad
    simp [hnot]
  linarith

private theorem rootSupport9_overlap_projection_bounds {P : Params9} {hc : HeightChoice9 P}
    {n R : ℕ} (hmn : P.m n ≤ n) (root root' : CubeVertex n)
    (hoverlap : ¬ Disjoint (scaleRootSupport9 (P := P) (hc := hc) (n := n) root R)
      (scaleRootSupport9 (P := P) (hc := hc) (n := n) root' R)) :
    _root_.hammingDist (specialWord9 (P.m n) root) (specialWord9 (P.m n) root') ≤ 40 * R + 10 ∧
      _root_.hammingDist (residualWord9 (P.m n) root) (residualWord9 (P.m n) root') ≤
        2 * P.radius n + 40 * R + 10 := by
  obtain ⟨c, hcRoot, hcRoot'⟩ := Finset.not_disjoint_iff.mp hoverlap
  simp only [scaleRootSupport9, consulted9, Finset.mem_filter, Finset.mem_univ,
    true_and] at hcRoot hcRoot'
  rcases hcRoot with ⟨hsp₁, hres₁⟩
  rcases hcRoot' with ⟨hsp₂, hres₂⟩
  have hspRootRaw : _root_.hammingDist (specialWord9 (P.m n) root) c.slice ≤
      2 * (10 * R + 2) + 1 := by
    simpa [_root_.hammingDist_comm] using hsp₁
  have hspRoot : _root_.hammingDist (specialWord9 (P.m n) root) c.slice ≤ 20 * R + 5 := by
    omega
  have hspRoot' : _root_.hammingDist c.slice (specialWord9 (P.m n) root') ≤ 20 * R + 5 := by
    omega
  have hresRootRaw : _root_.hammingDist (residualWord9 (P.m n) root) c.location ≤
      P.radius n + 2 * (10 * R + 2) + 1 := by
    simpa [_root_.hammingDist_comm] using hres₁
  have hresRoot : _root_.hammingDist (residualWord9 (P.m n) root) c.location ≤
      P.radius n + 20 * R + 5 := by omega
  have hresRoot' : _root_.hammingDist c.location (residualWord9 (P.m n) root') ≤
      P.radius n + 20 * R + 5 := by omega
  constructor
  · calc
      _root_.hammingDist (specialWord9 (P.m n) root) (specialWord9 (P.m n) root') ≤
          _root_.hammingDist (specialWord9 (P.m n) root) c.slice +
            _root_.hammingDist c.slice (specialWord9 (P.m n) root') :=
        _root_.hammingDist_triangle _ _ _
      _ ≤ 40 * R + 10 := by omega
  · calc
      _root_.hammingDist (residualWord9 (P.m n) root) (residualWord9 (P.m n) root') ≤
          _root_.hammingDist (residualWord9 (P.m n) root) c.location +
            _root_.hammingDist c.location (residualWord9 (P.m n) root') :=
        _root_.hammingDist_triangle _ _ _
      _ ≤ 2 * P.radius n + 40 * R + 10 := by omega

private theorem splitVertexMap9_injective {m n : ℕ} (hmn : m ≤ n) :
    Function.Injective (fun v : CubeVertex n => (specialWord9 m v, residualWord9 m v)) := by
  intro v w h
  funext i
  by_cases hi : i.val < m
  · have hsp := congrArg Prod.fst h
    have hbit := congrFun hsp (⟨i.val, hi⟩ : Fin m)
    have hn : i.val < n := lt_of_lt_of_le hi hmn
    simpa [specialWord9, hn] using hbit
  · let k : Fin (n - m) := ⟨i.val - m, by have := i.isLt; omega⟩
    have hres := congrArg Prod.snd h
    have hbit := congrFun hres k
    change v ⟨m + k.val, by have := k.isLt; omega⟩ =
      w ⟨m + k.val, by have := k.isLt; omega⟩ at hbit
    have hidx : (⟨m + k.val, by have := k.isLt; omega⟩ : Fin n) = i := by
      apply Fin.ext
      dsimp [k]
      omega
    simpa [hidx] using hbit

private theorem rootSupport9_degree_bound {P : Params9} {hc : HeightChoice9 P} {n R : ℕ}
    (hmn : P.m n ≤ n) (root : CubeVertex n) :
    (Finset.univ.filter (fun root' : CubeVertex n => root' ≠ root ∧
      ¬ Disjoint (scaleRootSupport9 (P := P) (hc := hc) (n := n) root R)
        (scaleRootSupport9 root' R))).card ≤
      ((40 * R + 11) * (P.m n + 1) ^ (40 * R + 10)) *
        ((2 * P.radius n + 40 * R + 11) *
          (n - P.m n + 1) ^ (2 * P.radius n + 40 * R + 10)) := by
  classical
  let sr := 40 * R + 10
  let rr := 2 * P.radius n + 40 * R + 10
  let Bspecial : Finset (CubeVertex (P.m n)) :=
    Finset.univ.filter (fun w =>
      _root_.hammingDist w (specialWord9 (P.m n) root) ≤ sr)
  let Bresidual : Finset (CubeVertex (n - P.m n)) :=
    Finset.univ.filter (fun w =>
      _root_.hammingDist w (residualWord9 (P.m n) root) ≤ rr)
  let U : Finset (CubeVertex n) := Finset.univ.filter (fun root' =>
    _root_.hammingDist (specialWord9 (P.m n) root') (specialWord9 (P.m n) root) ≤ sr ∧
    _root_.hammingDist (residualWord9 (P.m n) root') (residualWord9 (P.m n) root) ≤ rr)
  let split : CubeVertex n → CubeVertex (P.m n) × CubeVertex (n - P.m n) :=
    fun v => (specialWord9 (P.m n) v, residualWord9 (P.m n) v)
  have hmaps : ∀ v ∈ U, split v ∈ Bspecial ×ˢ Bresidual := by
    intro v hv
    simp only [U, Finset.mem_filter, Finset.mem_univ, true_and] at hv
    simp only [Finset.mem_product, Bspecial, Bresidual, Finset.mem_filter,
      Finset.mem_univ, true_and, split]
    exact hv
  have hinj : Set.InjOn split U := by
    intro v hv w hw heq
    exact splitVertexMap9_injective hmn heq
  have hcardU : U.card ≤ Bspecial.card * Bresidual.card := by
    calc
      U.card ≤ (Bspecial ×ˢ Bresidual).card :=
        Finset.card_le_card_of_injOn split hmaps hinj
      _ = Bspecial.card * Bresidual.card := Finset.card_product Bspecial Bresidual
  have hspecial := hammingBall9H_card_le (P.m n) sr (specialWord9 (P.m n) root)
  have hresidual := hammingBall9H_card_le (n - P.m n) rr (residualWord9 (P.m n) root)
  have hBspecial : Bspecial.card ≤ (sr + 1) * (P.m n + 1) ^ sr := by
    simpa [Bspecial, sr] using hspecial
  have hBresidual : Bresidual.card ≤ (rr + 1) * (n - P.m n + 1) ^ rr := by
    simpa [Bresidual, rr] using hresidual
  let Dset : Finset (CubeVertex n) := Finset.univ.filter (fun root' => root' ≠ root ∧
    ¬ Disjoint (scaleRootSupport9 (P := P) (hc := hc) (n := n) root R)
      (scaleRootSupport9 root' R))
  have hDsub : Dset ⊆ U := by
    intro root' hroot'
    simp only [Dset, Finset.mem_filter, Finset.mem_univ, true_and] at hroot'
    have hproj := rootSupport9_overlap_projection_bounds hmn root root' hroot'.2
    simp only [U, Finset.mem_filter, Finset.mem_univ, true_and]
    simpa [sr, rr, _root_.hammingDist_comm] using hproj
  calc
    (Finset.univ.filter (fun root' : CubeVertex n => root' ≠ root ∧
        ¬ Disjoint (scaleRootSupport9 (P := P) (hc := hc) (n := n) root R)
          (scaleRootSupport9 root' R))).card = Dset.card := by rfl
    _ ≤ U.card := Finset.card_le_card hDsub
    _ ≤ Bspecial.card * Bresidual.card := hcardU
    _ ≤ ((sr + 1) * (P.m n + 1) ^ sr) *
        ((rr + 1) * (n - P.m n + 1) ^ rr) := Nat.mul_le_mul hBspecial hBresidual
    _ = ((40 * R + 11) * (P.m n + 1) ^ (40 * R + 10)) *
        ((2 * P.radius n + 40 * R + 11) *
          (n - P.m n + 1) ^ (2 * P.radius n + 40 * R + 10)) := by
            simp [sr, rr]

private theorem bernoulli_pi_count_ge_le {ι : Type*} [Fintype ι] [DecidableEq ι]
    (p : ℝ) (hp : 0 ≤ p) (S : Finset ι) (t : ℕ) :
    (FinProb.pi (fun _ : ι => FinProb.bernoulli p)).pr
      (fun ω => t ≤ (S.filter (fun i => ω i = true)).card) ≤
        ((S.card : ℝ) * p) ^ t := by
  classical
  let μ := FinProb.pi (fun _ : ι => FinProb.bernoulli p)
  let Event (f : Fin t ↪ {i // i ∈ S}) (ω : ∀ i, Bool) : Prop :=
    ∀ k, ω (f k).val = true
  have hsubset : ∀ ω, t ≤ (S.filter (fun i => ω i = true)).card →
      ∃ f : Fin t ↪ {i // i ∈ S}, Event f ω := by
    intro ω hcount
    let T := S.filter (fun i => ω i = true)
    have ht : t ≤ T.card := by simpa [T] using hcount
    have hcard : Fintype.card (Fin t) ≤ Fintype.card {i // i ∈ T} := by
      simpa [Fintype.card_subtype] using ht
    obtain ⟨f⟩ := Function.Embedding.nonempty_of_card_le hcard
    let e : {i // i ∈ T} ↪ {i // i ∈ S} :=
      ⟨fun i => (⟨i.1, (Finset.mem_filter.mp i.2).1⟩ : {i // i ∈ S}), by
        intro a b hab
        exact Subtype.ext (by
          simpa using congrArg (fun x : {i // i ∈ S} => x.1) hab)⟩
    refine ⟨f.trans e, ?_⟩
    intro k
    exact (Finset.mem_filter.mp (f k).property).2
  have htuple (f : Fin t ↪ {i // i ∈ S}) : μ.pr (Event f) ≤ p ^ t := by
    let U : Finset ι := Finset.univ.image (fun k : Fin t => (f k).val)
    have hU : U.card = t := by
      have hinj : Function.Injective (fun k : Fin t => (f k).val) := by
        intro k l hkl
        apply f.injective
        exact Subtype.ext hkl
      rw [Finset.card_image_of_injective _ hinj]
      simp
    have hEq : μ.pr (Event f) = μ.pr (fun ω => ∀ i ∈ U, ω i = true) := by
      congr 1
      funext ω
      apply propext
      constructor
      · intro h i hi
        rcases Finset.mem_image.mp hi with ⟨k, hk, rfl⟩
        exact h k
      · intro h k
        apply h
        exact Finset.mem_image.mpr ⟨k, Finset.mem_univ _, rfl⟩
    calc
      μ.pr (Event f) = μ.pr (fun ω => ∀ i ∈ U, ω i = true) := hEq
      _ ≤ p ^ U.card := bernoulli_pi_true_on_finset_le p hp U
      _ = p ^ t := by rw [hU]
  have hunion : μ.pr (fun ω => ∃ f : Fin t ↪ {i // i ∈ S}, Event f ω) ≤
      ∑ f : Fin t ↪ {i // i ∈ S}, μ.pr (Event f) := by
    simpa [Event] using (finProb_pr_exists_finset_le_sum μ Finset.univ
      (fun f ω => Event f ω))
  have hcardEmb : Fintype.card (Fin t ↪ {i // i ∈ S}) ≤ S.card ^ t := by
    calc
      Fintype.card (Fin t ↪ {i // i ∈ S}) ≤
          Fintype.card (Fin t → {i // i ∈ S}) :=
        Fintype.card_le_of_injective (fun f : Fin t ↪ {i // i ∈ S} => (f : Fin t → {i // i ∈ S}))
          Function.Embedding.coe_injective
      _ = S.card ^ t := by simp [Fintype.card_subtype]
  calc
    μ.pr (fun ω => t ≤ (S.filter (fun i => ω i = true)).card) ≤
        μ.pr (fun ω => ∃ f : Fin t ↪ {i // i ∈ S}, Event f ω) :=
      finProb_pr_mono μ hsubset
    _ ≤ ∑ f : Fin t ↪ {i // i ∈ S}, μ.pr (Event f) := hunion
    _ ≤ ∑ _f : Fin t ↪ {i // i ∈ S}, p ^ t := by
      apply Finset.sum_le_sum
      intro f hf
      exact htuple f
    _ = (Fintype.card (Fin t ↪ {i // i ∈ S}) : ℝ) * p ^ t := by simp
    _ ≤ (S.card : ℝ) ^ t * p ^ t := by
      gcongr
      exact_mod_cast hcardEmb
    _ = ((S.card : ℝ) * p) ^ t := by rw [mul_pow]

private theorem bernoulli_pi_pair_active_count_ge_le {ι : Type*} [Fintype ι] [DecidableEq ι]
    (p q : ℝ) (hp : 0 ≤ p) (hq : 0 ≤ q) (S : Finset ι) (t : ℕ) :
    ((FinProb.pi (fun _ : ι => FinProb.bernoulli p)).prod
      (FinProb.pi (fun _ : ι => FinProb.bernoulli q))).pr
      (fun ω => t ≤ (S.filter (fun i => ω.1 i = true ∧ ω.2 i = true)).card) ≤
        ((S.card : ℝ) * p * q) ^ t := by
  classical
  let μ : FinProb ((ι → Bool) × (ι → Bool)) :=
    (FinProb.pi (fun _ : ι => FinProb.bernoulli p)).prod
      (FinProb.pi (fun _ : ι => FinProb.bernoulli q))
  let Event (f : Fin t ↪ {i // i ∈ S}) (ω : (ι → Bool) × (ι → Bool)) : Prop :=
    ∀ k, ω.1 (f k).val = true ∧ ω.2 (f k).val = true
  have hsubset : ∀ ω, t ≤ (S.filter (fun i => ω.1 i = true ∧ ω.2 i = true)).card →
      ∃ f : Fin t ↪ {i // i ∈ S}, Event f ω := by
    intro ω hcount
    let T := S.filter (fun i => ω.1 i = true ∧ ω.2 i = true)
    have ht : t ≤ T.card := by simpa [T] using hcount
    have hcard : Fintype.card (Fin t) ≤ Fintype.card {i // i ∈ T} := by
      simpa [Fintype.card_subtype] using ht
    obtain ⟨f⟩ := Function.Embedding.nonempty_of_card_le hcard
    let e : {i // i ∈ T} ↪ {i // i ∈ S} :=
      ⟨fun i => (⟨i.1, (Finset.mem_filter.mp i.2).1⟩ : {i // i ∈ S}), by
        intro a b hab
        exact Subtype.ext (by
          simpa using congrArg (fun x : {i // i ∈ S} => x.1) hab)⟩
    refine ⟨f.trans e, ?_⟩
    intro k
    exact (Finset.mem_filter.mp (f k).property).2
  have htuple (f : Fin t ↪ {i // i ∈ S}) : μ.pr (Event f) ≤ (p * q) ^ t := by
    let U : Finset ι := Finset.univ.image (fun k : Fin t => (f k).val)
    have hU : U.card = t := by
      have hinj : Function.Injective (fun k : Fin t => (f k).val) := by
        intro k l hkl
        apply f.injective
        exact Subtype.ext hkl
      rw [Finset.card_image_of_injective _ hinj]
      simp
    let EP : (ι → Bool) → Prop := fun x => ∀ k, x (f k).val = true
    let EA : (ι → Bool) → Prop := fun x => ∀ k, x (f k).val = true
    have hEP : (FinProb.pi (fun _ : ι => FinProb.bernoulli p)).pr EP ≤ p ^ t := by
      have heq : EP = (fun x => ∀ i ∈ U, x i = true) := by
        funext x
        apply propext
        constructor
        · intro h i hi
          rcases Finset.mem_image.mp hi with ⟨k, hk, rfl⟩
          exact h k
        · intro h k
          apply h
          exact Finset.mem_image.mpr ⟨k, Finset.mem_univ _, rfl⟩
      calc
        (FinProb.pi (fun _ : ι => FinProb.bernoulli p)).pr EP =
            (FinProb.pi (fun _ : ι => FinProb.bernoulli p)).pr
              (fun x => ∀ i ∈ U, x i = true) := by
            exact congrArg (fun E => (FinProb.pi (fun _ : ι => FinProb.bernoulli p)).pr E) heq
        _ ≤ p ^ U.card := bernoulli_pi_true_on_finset_le p hp U
        _ = p ^ t := by rw [hU]
    have hEA : (FinProb.pi (fun _ : ι => FinProb.bernoulli q)).pr EA ≤ q ^ t := by
      have heq : EA = (fun x => ∀ i ∈ U, x i = true) := by
        funext x
        apply propext
        constructor
        · intro h i hi
          rcases Finset.mem_image.mp hi with ⟨k, hk, rfl⟩
          exact h k
        · intro h k
          apply h
          exact Finset.mem_image.mpr ⟨k, Finset.mem_univ _, rfl⟩
      calc
        (FinProb.pi (fun _ : ι => FinProb.bernoulli q)).pr EA =
            (FinProb.pi (fun _ : ι => FinProb.bernoulli q)).pr
              (fun x => ∀ i ∈ U, x i = true) := by
            exact congrArg (fun E => (FinProb.pi (fun _ : ι => FinProb.bernoulli q)).pr E) heq
        _ ≤ q ^ U.card := bernoulli_pi_true_on_finset_le q hq U
        _ = q ^ t := by rw [hU]
    have hE : Event f = (fun ω => EP ω.1 ∧ EA ω.2) := by
      funext ω
      apply propext
      simp [Event, EP, EA, forall_and]
    have hrect : μ.pr (Event f) =
        (FinProb.pi (fun _ : ι => FinProb.bernoulli p)).pr (EP) *
          (FinProb.pi (fun _ : ι => FinProb.bernoulli q)).pr (EA) := by
      calc
        μ.pr (Event f) = μ.pr (fun ω => EP ω.1 ∧ EA ω.2) :=
          congrArg μ.pr hE
        _ = _ := finProb_prod_pr_and _ _ _ _
    calc
      μ.pr (Event f) =
          (FinProb.pi (fun _ : ι => FinProb.bernoulli p)).pr EP *
            (FinProb.pi (fun _ : ι => FinProb.bernoulli q)).pr EA := hrect
      _ ≤ p ^ t * q ^ t :=
        mul_le_mul hEP hEA (finProb_pr_nonneg _ _) (pow_nonneg hp _)
      _ = (p * q) ^ t := by rw [← mul_pow]
  have hunion : μ.pr (fun ω => ∃ f : Fin t ↪ {i // i ∈ S}, Event f ω) ≤
      ∑ f : Fin t ↪ {i // i ∈ S}, μ.pr (Event f) := by
    simpa [Event] using (finProb_pr_exists_finset_le_sum μ Finset.univ
      (fun f ω => Event f ω))
  have hcardEmb : Fintype.card (Fin t ↪ {i // i ∈ S}) ≤ S.card ^ t := by
    calc
      Fintype.card (Fin t ↪ {i // i ∈ S}) ≤
          Fintype.card (Fin t → {i // i ∈ S}) :=
        Fintype.card_le_of_injective (fun f : Fin t ↪ {i // i ∈ S} => (f : Fin t → {i // i ∈ S}))
          Function.Embedding.coe_injective
      _ = S.card ^ t := by simp [Fintype.card_subtype]
  calc
    μ.pr (fun ω => t ≤ (S.filter (fun i => ω.1 i = true ∧ ω.2 i = true)).card) ≤
        μ.pr (fun ω => ∃ f : Fin t ↪ {i // i ∈ S}, Event f ω) :=
      finProb_pr_mono μ hsubset
    _ ≤ ∑ f : Fin t ↪ {i // i ∈ S}, μ.pr (Event f) := hunion
    _ ≤ ∑ _f : Fin t ↪ {i // i ∈ S}, (p * q) ^ t := by
      apply Finset.sum_le_sum
      intro f hf
      exact htuple f
    _ = (Fintype.card (Fin t ↪ {i // i ∈ S}) : ℝ) * (p * q) ^ t := by simp
    _ ≤ (S.card : ℝ) ^ t * (p * q) ^ t := by
      gcongr
      exact_mod_cast hcardEmb
    _ = ((S.card : ℝ) * p * q) ^ t := by
      rw [mul_pow]
      congr 1
      ring


theorem fixed_bad_site_probability {P : Params9} {hc : HeightChoice9 P} {n : ℕ} {c : ℝ}
    (hbase : HeightBase9 P hc n c) (hcounts : HeightCounts9 P hc n)
    (v : CubeVertex n) (j : Fin (hc.levels n + 1)) :
    (heightLaw9 P hc n).pr (fun ω => badAt9 (P := P) (hc := hc) (n := n) ω.1 ω.2 v j) ≤
      Real.exp (-((n : ℝ) ^ c)) + Real.exp (-(n : ℝ)) := by
  classical
  let μ := heightLaw9 P hc n
  let Bad : ((Pos9 P hc n → Bool) × (Pos9 P hc n → Bool)) → Prop :=
    fun ω => badAt9 (P := P) (hc := hc) (n := n) ω.1 ω.2 v j
  let Low : ((Pos9 P hc n → Bool) × (Pos9 P hc n → Bool)) → Prop :=
    fun ω => (eligCount9 Finset.univ ω.1 v j : ℝ) < (n : ℝ) ^ (10 : ℝ) / 2
  have hcountsJoint : μ.pr (fun ω => ∃ v' : CubeVertex n,
      ∃ j' : Fin (hc.levels n + 1),
        (eligCount9 Finset.univ ω.1 v' j' : ℝ) < (n : ℝ) ^ (10 : ℝ) / 2) ≤
      Real.exp (-(n : ℝ)) := by
    calc
      μ.pr (fun ω => ∃ v' : CubeVertex n, ∃ j' : Fin (hc.levels n + 1),
          (eligCount9 Finset.univ ω.1 v' j' : ℝ) < (n : ℝ) ^ (10 : ℝ) / 2) =
          (heightPosLaw9 P hc n).pr (fun Pp => ∃ v' : CubeVertex n,
            ∃ j' : Fin (hc.levels n + 1),
              (eligCount9 Finset.univ Pp v' j' : ℝ) < (n : ℝ) ^ (10 : ℝ) / 2) := by
        simpa [μ, heightLaw9] using
          (prod_pr_fst (heightPosLaw9 P hc n) (heightActLaw9 P hc n)
            (fun Pp => ∃ v' : CubeVertex n, ∃ j' : Fin (hc.levels n + 1),
              (eligCount9 Finset.univ Pp v' j' : ℝ) < (n : ℝ) ^ (10 : ℝ) / 2))
      _ ≤ Real.exp (-(n : ℝ)) := hcounts
  have hlow : μ.pr (fun ω => Bad ω ∧ Low ω) ≤ Real.exp (-(n : ℝ)) := by
    apply le_trans (finProb_pr_mono μ ?_) hcountsJoint
    intro ω hω
    exact ⟨v, j, hω.2⟩
  have hlarge : μ.pr (fun ω => Bad ω ∧ ¬ Low ω) ≤ Real.exp (-((n : ℝ) ^ c)) := by
    apply le_trans (finProb_pr_mono μ ?_) (badAt9_with_eligible_size_bound hbase v j)
    intro ω hω
    have hcount : (n : ℝ) ^ (10 : ℝ) / 2 ≤ (eligCount9 Finset.univ ω.1 v j : ℝ) :=
      le_of_not_gt (by intro hgt; exact hω.2 hgt)
    have hn : 0 ≤ (n : ℝ) ^ (10 : ℝ) := by positivity
    have hsize : (1 / 8 : ℝ) * (n : ℝ) ^ (10 : ℝ) ≤
        (eligCount9 Finset.univ ω.1 v j : ℝ) := by nlinarith
    exact ⟨hω.1, hsize⟩
  have hsplit : μ.pr Bad = μ.pr (fun ω => (Bad ω ∧ Low ω) ∨ (Bad ω ∧ ¬ Low ω)) := by
    congr 1
    funext ω
    apply propext
    constructor
    · intro hbad
      by_cases hlow : Low ω
      · exact Or.inl ⟨hbad, hlow⟩
      · exact Or.inr ⟨hbad, hlow⟩
    · intro h
      rcases h with ⟨hbad, _⟩ | ⟨hbad, _⟩ <;> exact hbad
  calc
    μ.pr Bad = μ.pr (fun ω => (Bad ω ∧ Low ω) ∨ (Bad ω ∧ ¬ Low ω)) := hsplit
    _ ≤ μ.pr (fun ω => Bad ω ∧ Low ω) + μ.pr (fun ω => Bad ω ∧ ¬ Low ω) :=
      finProb_pr_union μ _ _
    _ ≤ Real.exp (-(n : ℝ)) + Real.exp (-((n : ℝ) ^ c)) := add_le_add hlow hlarge
    _ = Real.exp (-((n : ℝ) ^ c)) + Real.exp (-(n : ℝ)) := by ring

theorem badAt9_finite_union_probability {P : Params9} {hc : HeightChoice9 P} {n : ℕ} {c : ℝ}
    (hbase : HeightBase9 P hc n c) (hcounts : HeightCounts9 P hc n)
    (S : Finset (CubeVertex n × Fin (hc.levels n + 1))) :
    (heightLaw9 P hc n).pr (fun ω => ∃ x ∈ S,
      badAt9 (P := P) (hc := hc) (n := n) ω.1 ω.2 x.1 x.2) ≤
      (S.card : ℝ) * (Real.exp (-((n : ℝ) ^ c)) + Real.exp (-(n : ℝ))) := by
  classical
  calc
    (heightLaw9 P hc n).pr (fun ω => ∃ x ∈ S,
        badAt9 (P := P) (hc := hc) (n := n) ω.1 ω.2 x.1 x.2) ≤
        ∑ x ∈ S, (heightLaw9 P hc n).pr
          (fun ω => badAt9 (P := P) (hc := hc) (n := n) ω.1 ω.2 x.1 x.2) :=
      finProb_pr_exists_finset_le_sum (heightLaw9 P hc n) S
        (fun x ω => badAt9 (P := P) (hc := hc) (n := n) ω.1 ω.2 x.1 x.2)
    _ ≤ ∑ _x ∈ S, (Real.exp (-((n : ℝ) ^ c)) + Real.exp (-(n : ℝ))) := by
      apply Finset.sum_le_sum
      intro x hx
      exact fixed_bad_site_probability hbase hcounts x.1 x.2
    _ = (S.card : ℝ) * (Real.exp (-((n : ℝ) ^ c)) + Real.exp (-(n : ℝ))) := by
      simp [Finset.sum_const, nsmul_eq_mul]
      ring

theorem consulted_overlap_total_bound {P : Params9} {hc : HeightChoice9 P} {n : ℕ}
    {K c₀ : ℝ} (hover : HeightOverlap9 P hc n K c₀)
    (v v' : CubeVertex n) (R' : ℕ) (hR : 1 ≤ R')
    (hsep : K * R' ≤ (_root_.hammingDist v v' : ℝ)) :
    ((consulted9 (P := P) (hc := hc) (n := n) v R' ∩ consulted9 v' R').card : ℝ) ≤
      ((hc.levels n + 1 : ℕ) : ℝ) * (residualBall9 P n : ℝ) * Real.exp (-(c₀ * R')) := by
  classical
  let S := consulted9 (P := P) (hc := hc) (n := n) v R' ∩ consulted9 v' R'
  have hcard : S.card = ∑ j ∈ Finset.univ,
      (S.filter (fun c => c.level = j)).card := by
    simpa [S] using (Finset.card_eq_sum_card_fiberwise
      (s := S) (t := Finset.univ) (f := fun c : Pos9 P hc n => c.level)
      (by intro c hc; exact Finset.mem_univ _))
  calc
    (S.card : ℝ) = ∑ j ∈ Finset.univ, ((S.filter (fun c => c.level = j)).card : ℝ) := by
      exact_mod_cast hcard
    _ ≤ ∑ j ∈ Finset.univ,
          (residualBall9 P n : ℝ) * Real.exp (-(c₀ * R')) := by
      apply Finset.sum_le_sum
      intro j hj
      exact hover v v' R' j hR hsep
    _ = ((hc.levels n + 1 : ℕ) : ℝ) * (residualBall9 P n : ℝ) *
          Real.exp (-(c₀ * R')) := by
      simp
      ring

private theorem scaleSupport9_inter_overlap_bound_of_metric_separation
    {P : Params9} {hc : HeightChoice9 P} {n R Knat : ℕ} {K c₀ : ℝ}
    (hover : HeightOverlap9 P hc n K c₀) (hK : K ≤ (Knat : ℝ))
    (hR : 1 ≤ R) (start start' : HeightState9 P hc n)
    (hsep : 16 * R + 4 + 4 * Knat * R + 1 ≤ heightMetric9 start start') :
    ((scaleSupport9 start R ∩ scaleSupport9 start' R).card : ℝ) ≤
      ((hc.levels n + 1 : ℕ) : ℝ) * (residualBall9 P n : ℝ) *
        Real.exp (- (c₀ * (8 * R : ℕ))) := by
  by_cases hlevel : 16 * R + 4 < Nat.dist start.2.val start'.2.val
  · have hdisj := scaleSupport9_disjoint_of_level_separated start start' hlevel
    have hempty : scaleSupport9 start R ∩ scaleSupport9 start' R = ∅ :=
      Finset.disjoint_iff_inter_eq_empty.mp hdisj
    have hcard : (scaleSupport9 start R ∩ scaleSupport9 start' R).card = 0 := by
      rw [hempty]
      simp
    have hnonneg : 0 ≤
        ((hc.levels n + 1 : ℕ) : ℝ) * (residualBall9 P n : ℝ) *
          Real.exp (- (c₀ * (8 * R : ℕ))) := by positivity
    rw [hcard]
    simpa using hnonneg
  · have hlevel' : Nat.dist start.2.val start'.2.val ≤ 16 * R + 4 :=
      Nat.le_of_not_gt hlevel
    have hspace : 16 * R + 4 + 4 * Knat * R + 1 ≤
        (_root_.hammingDist start.1 start'.1 + 1) / 2 := by
      unfold heightMetric9 at hsep
      rcases le_total (Nat.dist start.2.val start'.2.val)
          ((_root_.hammingDist start.1 start'.1 + 1) / 2) with hls | hsl
      · rw [max_eq_right hls] at hsep
        exact hsep
      · rw [max_eq_left hsl] at hsep
        omega
    have hham : 8 * Knat * R ≤ _root_.hammingDist start.1 start'.1 := by
      have hspace2 : 2 * (16 * R + 4 + 4 * Knat * R + 1) ≤
          _root_.hammingDist start.1 start'.1 + 1 := by
        calc
          2 * (16 * R + 4 + 4 * Knat * R + 1) ≤
              2 * ((_root_.hammingDist start.1 start'.1 + 1) / 2) :=
            Nat.mul_le_mul_left 2 hspace
          _ ≤ _root_.hammingDist start.1 start'.1 + 1 := by omega
      have hcoef : 8 * Knat * R = 2 * (4 * Knat * R) := by ring
      rw [hcoef]
      omega
    have hsepReal : K * ((8 * R : ℕ) : ℝ) ≤
        (_root_.hammingDist start.1 start'.1 : ℝ) := by
      have hmul := mul_le_mul_of_nonneg_right hK
        (by positivity : 0 ≤ ((8 * R : ℕ) : ℝ))
      have hcast : (Knat : ℝ) * ((8 * R : ℕ) : ℝ) =
          ((8 * Knat * R : ℕ) : ℝ) := by
        push_cast
        ring
      calc
        K * ((8 * R : ℕ) : ℝ) ≤ (Knat : ℝ) * ((8 * R : ℕ) : ℝ) := hmul
        _ = ((8 * Knat * R : ℕ) : ℝ) := hcast
        _ ≤ (_root_.hammingDist start.1 start'.1 : ℝ) := by exact_mod_cast hham
    have hoverBound := consulted_overlap_total_bound hover start.1 start'.1 (8 * R)
      (by omega) hsepReal
    calc
      ((scaleSupport9 start R ∩ scaleSupport9 start' R).card : ℝ) ≤
          ((consulted9 (P := P) (hc := hc) (n := n) start.1 (8 * R) ∩
            consulted9 start'.1 (8 * R)).card : ℝ) := by
        exact_mod_cast scaleSupport9_inter_card_le start start'
      _ ≤ ((hc.levels n + 1 : ℕ) : ℝ) * (residualBall9 P n : ℝ) *
          Real.exp (- (c₀ * (8 * R : ℕ))) := hoverBound

private theorem heightPath9_radialSupport_overlap_bound9
    {P : Params9} {hc : HeightChoice9 P} {n Q R Knat : ℕ} {K c₀ : ℝ}
    (hover : HeightOverlap9 P hc n K c₀) (hK : K ≤ (Knat : ℝ)) (hR : 1 ≤ R)
    {l : List (HeightState9 P hc n)}
    {start : HeightState9 P hc n} (f : Fin (Q + 1) → HeightState9 P hc n)
    (hf : ∀ r, f r ∈ l ∧ heightMetric9 (f r) start = r.val)
    (r s : Fin (Q + 1))
    (hgap : 16 * R + 4 + 4 * Knat * R + 1 ≤ Nat.dist r.val s.val) :
    ((scaleSupport9 (f r) R ∩ scaleSupport9 (f s) R).card : ℝ) ≤
      ((hc.levels n + 1 : ℕ) : ℝ) * (residualBall9 P n : ℝ) *
        Real.exp (- (c₀ * (8 * R : ℕ))) := by
  apply scaleSupport9_inter_overlap_bound_of_metric_separation hover hK hR
  exact heightPath9_radialFamily_separated9 f hf r s hgap

private theorem annularSupport9_overlap_bound
    {P : Params9} {hc : HeightChoice9 P} {n R Knat : ℕ} {K c₀ : ℝ}
    (hover : HeightOverlap9 P hc n K c₀) (hK : K ≤ (Knat : ℝ)) (hR : 1 ≤ R)
    (root child child' : HeightState9 P hc n) {r s width : ℕ}
    (hchild : r ≤ heightMetric9 child root ∧ heightMetric9 child root ≤ r + width)
    (hchild' : s ≤ heightMetric9 child' root ∧ heightMetric9 child' root ≤ s + width)
    (hgap : r + width + (16 * R + 4 + 4 * Knat * R + 1) ≤ s) :
    ((scaleSupport9 child R ∩ scaleSupport9 child' R).card : ℝ) ≤
      ((hc.levels n + 1 : ℕ) : ℝ) * (residualBall9 P n : ℝ) *
        Real.exp (- (c₀ * (8 * R : ℕ))) := by
  have hradGap : 16 * R + 4 + 4 * Knat * R + 1 ≤
      Nat.dist (heightMetric9 child root) (heightMetric9 child' root) := by
    have hle : heightMetric9 child root ≤ heightMetric9 child' root := by omega
    rw [Nat.dist_eq_sub_of_le hle]
    omega
  have hmetric := hradGap.trans (heightMetric9_radialVariation_le root child child')
  exact scaleSupport9_inter_overlap_bound_of_metric_separation hover hK hR child child' hmetric

theorem position_overlap_count_tail {P : Params9} {hc : HeightChoice9 P} {n : ℕ}
    (v v' : CubeVertex n) (R' t : ℕ) :
    (heightPosLaw9 P hc n).pr (fun Pp =>
      t ≤ ((consulted9 (P := P) (hc := hc) (n := n) v R' ∩ consulted9 v' R').filter
        (fun c => Pp c = true)).card) ≤
      (((consulted9 (P := P) (hc := hc) (n := n) v R' ∩ consulted9 v' R').card : ℝ) *
        ((n : ℝ) ^ (10 : ℝ) / (residualBall9 P n : ℝ))) ^ t := by
  let S := consulted9 (P := P) (hc := hc) (n := n) v R' ∩ consulted9 v' R'
  have hp : 0 ≤ (n : ℝ) ^ (10 : ℝ) / (residualBall9 P n : ℝ) := by positivity
  simpa [S, heightPosLaw9] using
    (bernoulli_pi_count_ge_le ((n : ℝ) ^ (10 : ℝ) / (residualBall9 P n : ℝ)) hp S t)

theorem active_overlap_count_tail {P : Params9} {hc : HeightChoice9 P} {n : ℕ}
    (v v' : CubeVertex n) (R' t : ℕ) :
    (heightLaw9 P hc n).pr (fun ω =>
      t ≤ ((consulted9 (P := P) (hc := hc) (n := n) v R' ∩ consulted9 v' R').filter
        (fun c => ω.1 c = true ∧ ω.2 c = true)).card) ≤
      (((consulted9 (P := P) (hc := hc) (n := n) v R' ∩ consulted9 v' R').card : ℝ) *
        ((n : ℝ) ^ (10 : ℝ) / (residualBall9 P n : ℝ)) * (n : ℝ) ^ (hc.b₀ - 10)) ^ t := by
  let S := consulted9 (P := P) (hc := hc) (n := n) v R' ∩ consulted9 v' R'
  have hp : 0 ≤ (n : ℝ) ^ (10 : ℝ) / (residualBall9 P n : ℝ) := by positivity
  have hq : 0 ≤ (n : ℝ) ^ (hc.b₀ - 10) := by positivity
  simpa [S, heightLaw9, heightPosLaw9, heightActLaw9] using
    (bernoulli_pi_pair_active_count_ge_le
      ((n : ℝ) ^ (10 : ℝ) / (residualBall9 P n : ℝ))
      ((n : ℝ) ^ (hc.b₀ - 10)) hp hq S t)

theorem position_overlap_count_tail_of_small_mean {P : Params9} {hc : HeightChoice9 P}
    {n : ℕ} {K c₀ : ℝ} (hover : HeightOverlap9 P hc n K c₀)
    (v v' : CubeVertex n) (R' : ℕ) (hR : 1 ≤ R')
    (hsep : K * R' ≤ (_root_.hammingDist v v' : ℝ)) (t : ℕ)
    (hmean : ((hc.levels n + 1 : ℕ) : ℝ) * (residualBall9 P n : ℝ) *
        Real.exp (-(c₀ * R')) * ((n : ℝ) ^ (10 : ℝ) / (residualBall9 P n : ℝ)) ≤
          Real.exp (-(c₀ * R' / 2))) :
    (heightPosLaw9 P hc n).pr (fun Pp =>
      t ≤ ((consulted9 (P := P) (hc := hc) (n := n) v R' ∩ consulted9 v' R').filter
        (fun c => Pp c = true)).card) ≤ (Real.exp (-(c₀ * R' / 2)) ^ t) := by
  classical
  let S := consulted9 (P := P) (hc := hc) (n := n) v R' ∩ consulted9 v' R'
  let p := (n : ℝ) ^ (10 : ℝ) / (residualBall9 P n : ℝ)
  have hp : 0 ≤ p := by dsimp [p]; positivity
  have hcard := consulted_overlap_total_bound hover v v' R' hR hsep
  have hcoeff : (S.card : ℝ) * p ≤ Real.exp (-(c₀ * R' / 2)) := by
    have hcard' : (S.card : ℝ) * p ≤
        (((hc.levels n + 1 : ℕ) : ℝ) * (residualBall9 P n : ℝ) *
          Real.exp (-(c₀ * R'))) * p :=
      mul_le_mul_of_nonneg_right (by simpa [S] using hcard) hp
    calc
      (S.card : ℝ) * p ≤
          (((hc.levels n + 1 : ℕ) : ℝ) * (residualBall9 P n : ℝ) *
            Real.exp (-(c₀ * R'))) * p := hcard'
      _ ≤ Real.exp (-(c₀ * R' / 2)) := by simpa [p, mul_assoc] using hmean
  have hpow := pow_le_pow_left₀ (mul_nonneg (Nat.cast_nonneg _) hp) hcoeff t
  calc
    (heightPosLaw9 P hc n).pr (fun Pp =>
        t ≤ (S.filter (fun c => Pp c = true)).card) ≤ ((S.card : ℝ) * p) ^ t := by
      simpa [S, p, heightPosLaw9] using (bernoulli_pi_count_ge_le p hp S t)
    _ ≤ Real.exp (-(c₀ * R' / 2)) ^ t := hpow

theorem active_overlap_count_tail_of_small_mean {P : Params9} {hc : HeightChoice9 P}
    {n : ℕ} {K c₀ : ℝ} (hover : HeightOverlap9 P hc n K c₀)
    (v v' : CubeVertex n) (R' : ℕ) (hR : 1 ≤ R')
    (hsep : K * R' ≤ (_root_.hammingDist v v' : ℝ)) (t : ℕ)
    (hmean : ((hc.levels n + 1 : ℕ) : ℝ) * (residualBall9 P n : ℝ) *
        Real.exp (-(c₀ * R')) *
          ((n : ℝ) ^ (10 : ℝ) / (residualBall9 P n : ℝ)) * (n : ℝ) ^ (hc.b₀ - 10) ≤
          Real.exp (-(c₀ * R' / 2))) :
    (heightLaw9 P hc n).pr (fun ω =>
      t ≤ ((consulted9 (P := P) (hc := hc) (n := n) v R' ∩ consulted9 v' R').filter
        (fun c => ω.1 c = true ∧ ω.2 c = true)).card) ≤
      (Real.exp (-(c₀ * R' / 2)) ^ t) := by
  classical
  let S := consulted9 (P := P) (hc := hc) (n := n) v R' ∩ consulted9 v' R'
  let p := (n : ℝ) ^ (10 : ℝ) / (residualBall9 P n : ℝ)
  let q := (n : ℝ) ^ (hc.b₀ - 10)
  have hp : 0 ≤ p := by dsimp [p]; positivity
  have hq : 0 ≤ q := by dsimp [q]; positivity
  have hcard := consulted_overlap_total_bound hover v v' R' hR hsep
  have hcoeff : (S.card : ℝ) * p * q ≤ Real.exp (-(c₀ * R' / 2)) := by
    have hcard₁ : (S.card : ℝ) * p ≤
        (((hc.levels n + 1 : ℕ) : ℝ) * (residualBall9 P n : ℝ) *
          Real.exp (-(c₀ * R'))) * p :=
      mul_le_mul_of_nonneg_right (by simpa [S] using hcard) hp
    have hcard₂ : ((S.card : ℝ) * p) * q ≤
        ((((hc.levels n + 1 : ℕ) : ℝ) * (residualBall9 P n : ℝ) *
          Real.exp (-(c₀ * R'))) * p) * q :=
      mul_le_mul_of_nonneg_right hcard₁ hq
    calc
      (S.card : ℝ) * p * q = ((S.card : ℝ) * p) * q := by ring
      _ ≤ ((((hc.levels n + 1 : ℕ) : ℝ) * (residualBall9 P n : ℝ) *
          Real.exp (-(c₀ * R'))) * p) * q := hcard₂
      _ = ((hc.levels n + 1 : ℕ) : ℝ) * (residualBall9 P n : ℝ) *
          Real.exp (-(c₀ * R')) * p * q := by ring
      _ ≤ Real.exp (-(c₀ * R' / 2)) := by simpa [p, q, mul_assoc] using hmean
  have hpow := pow_le_pow_left₀ (mul_nonneg (mul_nonneg (Nat.cast_nonneg _) hp) hq) hcoeff t
  calc
    (heightLaw9 P hc n).pr (fun ω =>
        t ≤ (S.filter (fun c => ω.1 c = true ∧ ω.2 c = true)).card) ≤
        ((S.card : ℝ) * p * q) ^ t := by
      simpa [S, p, q, heightLaw9, heightPosLaw9, heightActLaw9] using
        (bernoulli_pi_pair_active_count_ge_le p q hp hq S t)
    _ ≤ Real.exp (-(c₀ * R' / 2)) ^ t := hpow

private theorem topScale_le_of_candidate (n : ℕ) (σ ζ : ℝ) (i : ℕ)
    (hcand : ⌈(n : ℝ) ^ (1 - ζ)⌉₊ ≤
      (max 2 ⌈(n : ℝ) ^ σ⌉₊) ^ i * max 1 ⌈Real.log (n : ℝ) ^ 2⌉₊) :
    topScale n σ ζ ≤
      (max 2 ⌈(n : ℝ) ^ σ⌉₊) ^ i * max 1 ⌈Real.log (n : ℝ) ^ 2⌉₊ := by
  unfold topScale
  have hexists : ∃ j : ℕ, ⌈(n : ℝ) ^ (1 - ζ)⌉₊ ≤
      (max 2 ⌈(n : ℝ) ^ σ⌉₊) ^ j * max 1 ⌈Real.log (n : ℝ) ^ 2⌉₊ :=
    ⟨i, hcand⟩
  apply Nat.mul_le_mul_right
  exact pow_le_pow_right₀ (by omega)
    (Nat.find_min' hexists hcand)

private theorem scaleIndex_exists9 (M R target : ℕ) (hM : 2 ≤ M) (hR : 1 ≤ R) :
    ∃ i : ℕ, target ≤ M ^ i * R := by
  have hM0 : M ≠ 0 := by omega
  induction target with
  | zero => exact ⟨0, by simp⟩
  | succ target ih =>
      obtain ⟨i, hi⟩ := ih
      let x := M ^ i * R
      have hx0 : x ≠ 0 := by
        dsimp [x]
        exact Nat.mul_ne_zero (pow_ne_zero _ hM0) (by omega)
      have hx : 1 ≤ x := by omega
      have hstep : x + 1 ≤ 2 * x := by omega
      have hmult : 2 * x ≤ M * x := Nat.mul_le_mul_right x hM
      refine ⟨i + 1, ?_⟩
      calc
        target + 1 ≤ x + 1 := Nat.succ_le_succ hi
        _ ≤ 2 * x := hstep
        _ ≤ M * x := hmult
        _ = M ^ (i + 1) * R := by dsimp [x]; rw [pow_succ]; ring

private theorem topScale_le_logbase_add_product_target (n : ℕ) (σ ζ : ℝ) :
    topScale n σ ζ ≤
      max 1 ⌈Real.log (n : ℝ) ^ 2⌉₊ +
        (max 2 ⌈(n : ℝ) ^ σ⌉₊) * ⌈(n : ℝ) ^ (1 - ζ)⌉₊ := by
  classical
  let R₀ : ℕ := max 1 ⌈Real.log (n : ℝ) ^ 2⌉₊
  let M : ℕ := max 2 ⌈(n : ℝ) ^ σ⌉₊
  let target : ℕ := ⌈(n : ℝ) ^ (1 - ζ)⌉₊
  have hM : 2 ≤ M := by dsimp [M]; omega
  have hR : 1 ≤ R₀ := by dsimp [R₀]; omega
  have hexists := scaleIndex_exists9 M R₀ target hM hR
  let k := Nat.find hexists
  have hspec : target ≤ M ^ k * R₀ := Nat.find_spec hexists
  change M ^ k * R₀ ≤ R₀ + M * target
  by_cases hk0 : k = 0
  · have hkpow : M ^ k * R₀ = R₀ := by rw [hk0, pow_zero]; simp
    rw [hkpow]
    omega
  · have hkpos : 0 < k := Nat.pos_of_ne_zero hk0
    have hprevNot : ¬ target ≤ M ^ (k - 1) * R₀ :=
      Nat.find_min hexists (Nat.sub_lt hkpos (by omega))
    have hprev : M ^ (k - 1) * R₀ < target := Nat.lt_of_not_ge hprevNot
    have hpow : M ^ k * R₀ = M * (M ^ (k - 1) * R₀) := by
      have hkEq : (k - 1) + 1 = k := by omega
      calc
        M ^ k * R₀ = M ^ ((k - 1) + 1) * R₀ := by rw [hkEq]
        _ = (M ^ (k - 1) * M) * R₀ := by rw [pow_succ]
        _ = M * (M ^ (k - 1) * R₀) := by ring
    rw [hpow]
    calc
      M * (M ^ (k - 1) * R₀) ≤ M * target := Nat.mul_le_mul_left _ hprev.le
      _ ≤ R₀ + M * target := Nat.le_add_left _ _

private theorem topScale_target_le (n : ℕ) (σ ζ : ℝ) :
    ⌈(n : ℝ) ^ (1 - ζ)⌉₊ ≤ topScale n σ ζ := by
  let R₀ : ℕ := max 1 ⌈Real.log (n : ℝ) ^ 2⌉₊
  let M : ℕ := max 2 ⌈(n : ℝ) ^ σ⌉₊
  let target : ℕ := ⌈(n : ℝ) ^ (1 - ζ)⌉₊
  have hM : 2 ≤ M := by dsimp [M]; omega
  have hR : 1 ≤ R₀ := by dsimp [R₀]; omega
  have hexists := scaleIndex_exists9 M R₀ target hM hR
  let k := Nat.find hexists
  change target ≤ M ^ k * R₀
  exact Nat.find_spec hexists

private theorem logSq9_le_power {x δ : ℝ} (hx : 1 ≤ x) (hδ : 0 < δ) :
    (Real.log x) ^ 2 ≤ (2 / δ) ^ 2 * x ^ δ := by
  have hxpos : 0 < x := lt_of_lt_of_le zero_lt_one hx
  let ε : ℝ := δ / 2
  have hε : 0 < ε := by dsimp [ε]; positivity
  have hlogNonneg : 0 ≤ Real.log x := Real.log_nonneg hx
  have hlog := Real.log_le_rpow_div (le_of_lt hxpos) hε
  have hpow : (x ^ ε) ^ 2 = x ^ δ := by
    calc
      (x ^ ε) ^ 2 = (x ^ ε) ^ (2 : ℝ) := (Real.rpow_natCast (x ^ ε) 2).symm
      _ = x ^ (ε * 2) := (Real.rpow_mul hxpos.le ε 2).symm
      _ = x ^ δ := by rw [show ε * 2 = δ by dsimp [ε]; ring]
  have hsq : (Real.log x) ^ 2 ≤ (x ^ ε / ε) ^ 2 := by
    rw [pow_two, pow_two]
    exact mul_le_mul hlog hlog
      hlogNonneg (div_nonneg (Real.rpow_nonneg hxpos.le ε) hε.le)
  calc
    (Real.log x) ^ 2 ≤ (x ^ ε / ε) ^ 2 := hsq
    _ = (x ^ ε) ^ 2 / ε ^ 2 := by ring
    _ = x ^ δ / ε ^ 2 := by rw [hpow]
    _ = (2 / δ) ^ 2 * x ^ δ := by
      dsimp [ε]
      field_simp [ne_of_gt hδ]

private theorem topScale_le_power9 (n : ℕ) {σ ζ : ℝ}
    (hσ : 0 < σ) (hσζ : σ < ζ) (hζsmall : ζ ≤ 1 / 100) (hn : 1 ≤ n) :
    (topScale n σ ζ : ℝ) ≤ ((2 / ((ζ - σ) / 8)) ^ 2 + 8) *
      (n : ℝ) ^ (1 - (ζ - σ)) := by
  let d := ζ - σ
  let δ := d / 8
  have hd : 0 < d := sub_pos.mpr hσζ
  have hδ : 0 < δ := by dsimp [δ, d]; positivity
  have hsmallExp : δ ≤ 1 - d := by dsimp [δ, d]; linarith
  have hnReal : 1 ≤ (n : ℝ) := by exact_mod_cast hn
  have hNpos : 0 < (n : ℝ) := lt_of_lt_of_le zero_lt_one hnReal
  have hR0 : ((max 1 ⌈Real.log (n : ℝ) ^ 2⌉₊ : ℕ) : ℝ) ≤
      (Real.log (n : ℝ)) ^ 2 + 2 := by
    rw [Nat.cast_max]
    apply max_le
    · have hsq : 0 ≤ (Real.log (n : ℝ)) ^ 2 := sq_nonneg _
      have hreal : (1 : ℝ) ≤ (Real.log (n : ℝ)) ^ 2 + 2 := by nlinarith [hsq]
      simpa using hreal
    · exact (Nat.ceil_lt_add_one (sq_nonneg (Real.log (n : ℝ)))).le.trans
        (by ring_nf; linarith)
  have hM : ((max 2 ⌈(n : ℝ) ^ σ⌉₊ : ℕ) : ℝ) ≤
      (n : ℝ) ^ σ + 2 := by
    rw [Nat.cast_max]
    apply max_le
    · have hnonneg : 0 ≤ (n : ℝ) ^ σ := Real.rpow_nonneg (Nat.cast_nonneg n) σ
      have hreal : (2 : ℝ) ≤ (n : ℝ) ^ σ + 2 := by linarith
      simpa using hreal
    · exact (Nat.ceil_lt_add_one (Real.rpow_nonneg (Nat.cast_nonneg n) σ)).le.trans
        (by linarith)
  have htarget : (⌈(n : ℝ) ^ (1 - ζ)⌉₊ : ℝ) ≤
      (n : ℝ) ^ (1 - ζ) + 1 :=
    (Nat.ceil_lt_add_one (Real.rpow_nonneg (Nat.cast_nonneg n) _)).le
  have htargetLower : 1 ≤ (n : ℝ) ^ (1 - ζ) := by
    calc
      1 = (n : ℝ) ^ (0 : ℝ) := by simp
      _ ≤ (n : ℝ) ^ (1 - ζ) :=
        Real.rpow_le_rpow_of_exponent_le hnReal (by linarith)
  have htargetUpper : (n : ℝ) ^ (1 - ζ) + 1 ≤ 2 * (n : ℝ) ^ (1 - ζ) := by linarith
  have hMupper : (n : ℝ) ^ σ + 2 ≤ 3 * (n : ℝ) ^ σ := by
    have hp := Real.rpow_le_rpow_of_exponent_le hnReal hσ.le
    have hpow : (1 : ℝ) ≤ (n : ℝ) ^ σ := by simpa using hp
    have htwiceRaw := mul_le_mul_of_nonneg_left hpow (by norm_num : (0 : ℝ) ≤ 2)
    have htwice : (2 : ℝ) ≤ 2 * (n : ℝ) ^ σ := by simpa using htwiceRaw
    have hplus := add_le_add_left htwice ((n : ℝ) ^ σ)
    calc
      (n : ℝ) ^ σ + 2 ≤ (n : ℝ) ^ σ + 2 * (n : ℝ) ^ σ := by
        simpa [add_comm, add_left_comm, add_assoc] using hplus
      _ = 3 * (n : ℝ) ^ σ := by ring
  have hlog := logSq9_le_power hnReal hδ
  have hlogUpper : (Real.log (n : ℝ)) ^ 2 + 2 ≤
      ((2 / δ) ^ 2 + 2) * (n : ℝ) ^ δ := by
    have hpow : 1 ≤ (n : ℝ) ^ δ := by
      calc
        1 = (n : ℝ) ^ (0 : ℝ) := by simp
        _ ≤ (n : ℝ) ^ δ := Real.rpow_le_rpow_of_exponent_le hnReal hδ.le
    nlinarith [hlog]
  have htop := topScale_le_logbase_add_product_target n σ ζ
  have htopReal : (topScale n σ ζ : ℝ) ≤
      ((max 1 ⌈Real.log (n : ℝ) ^ 2⌉₊ : ℕ) : ℝ) +
        ((max 2 ⌈(n : ℝ) ^ σ⌉₊ : ℕ) : ℝ) * (⌈(n : ℝ) ^ (1 - ζ)⌉₊ : ℝ) := by
    exact_mod_cast htop
  have hmain : (n : ℝ) ^ δ ≤ (n : ℝ) ^ (1 - d) :=
    Real.rpow_le_rpow_of_exponent_le hnReal hsmallExp
  have hpowAdd : (n : ℝ) ^ σ * (n : ℝ) ^ (1 - ζ) = (n : ℝ) ^ (1 - d) := by
    rw [← Real.rpow_add hNpos]
    congr 1
    dsimp [d]
    ring
  calc
    (topScale n σ ζ : ℝ) ≤
        ((Real.log (n : ℝ)) ^ 2 + 2) + ((n : ℝ) ^ σ + 2) *
          ((n : ℝ) ^ (1 - ζ) + 1) := by
          exact htopReal.trans (add_le_add hR0
            (mul_le_mul hM htarget (by positivity) (by positivity)))
    _ ≤ ((2 / δ) ^ 2 + 2) * (n : ℝ) ^ δ +
          (3 * (n : ℝ) ^ σ) * (2 * (n : ℝ) ^ (1 - ζ)) :=
        add_le_add hlogUpper (mul_le_mul hMupper htargetUpper
          (by positivity) (by positivity))
    _ = ((2 / δ) ^ 2 + 2) * (n : ℝ) ^ δ +
          6 * ((n : ℝ) ^ σ * (n : ℝ) ^ (1 - ζ)) := by ring
    _ = ((2 / δ) ^ 2 + 2) * (n : ℝ) ^ δ + 6 * (n : ℝ) ^ (1 - d) := by rw [hpowAdd]
    _ ≤ ((2 / δ) ^ 2 + 8) * (n : ℝ) ^ (1 - d) := by
        have hcoef : 0 ≤ (2 / δ) ^ 2 + 2 := by positivity
        have hterm := mul_le_mul_of_nonneg_left hmain hcoef
        nlinarith
    _ = ((2 / ((ζ - σ) / 8)) ^ 2 + 8) *
          (n : ℝ) ^ (1 - (ζ - σ)) := by simp [d, δ]

private theorem radius9_le_height9 {P : Params9} {hc : HeightChoice9 P}
    (hP : P.Valid) (hadm : hc.Admissible) {n : ℕ} (hn : 1 ≤ n) :
    P.radius n ≤ hc.levels n := by
  rcases hP with ⟨hcommon, hminus, hxd, hσ, hχ, hhp, hcase⟩
  rcases hcommon with ⟨hxS, hxSd, hxD⟩
  rcases hσ with ⟨hσpos, hσsmall⟩
  rcases hadm with ⟨hσh, hσζ, hζ1, hθ, hθ1, hgap, hab, hχgap,
    hb0, hb0eps, heps, hcaseAdm⟩
  have hPσsmall : (P.σ : ℝ) < 1 / 100 := by
    have hxSsmall : P.xS < (1 : ℚ) / 10 := lt_trans hxSd hxD
    have hσq : P.σ < (1 : ℚ) / 100 := by nlinarith
    have hσreal : ((P.σ : ℚ) : ℝ) < (((1 : ℚ) / 100) : ℝ) := by exact_mod_cast hσq
    simpa using hσreal
  have hepsσ : P.eps ≤ (P.σ : ℝ) / 2 := by
    cases hcase' : P.case with
    | sub yS yD yM =>
        simp [Params9.eps, hcase']
        exact div_le_div_of_nonneg_right (min_le_left _ _) (by norm_num)
    | lin αS αD hB yB => simp [Params9.eps, hcase']
  have hζa : hc.ζ < hc.a := by
    have hpos : 0 < 1 - hc.θ := by linarith
    linarith
  have hζsmall : hc.ζ < 1 / 100 := by
    have hchain : hc.ζ < (P.σ : ℝ) / 2 := by
      calc
        hc.ζ < hc.a := hζa
        _ < hc.b₀ := hab
        _ < hc.eps' := hb0eps
        _ < P.eps := heps
        _ ≤ (P.σ : ℝ) / 2 := hepsσ
    linarith
  have hexp : (P.σ : ℝ) ≤ 1 - hc.ζ := by linarith
  have hnReal : 1 ≤ (n : ℝ) := by exact_mod_cast hn
  have hradReal : (P.radius n : ℝ) ≤ (n : ℝ) ^ (P.σ : ℝ) := by
    unfold Params9.radius
    exact Nat.floor_le (Real.rpow_nonneg (Nat.cast_nonneg n) _)
  have hrpow : (n : ℝ) ^ (P.σ : ℝ) ≤ (n : ℝ) ^ (1 - hc.ζ) :=
    Real.rpow_le_rpow_of_exponent_le hnReal hexp
  have hceil : (n : ℝ) ^ (1 - hc.ζ) ≤
      (⌈(n : ℝ) ^ (1 - hc.ζ)⌉₊ : ℝ) := Nat.le_ceil _
  have hreal : (P.radius n : ℝ) ≤ (⌈(n : ℝ) ^ (1 - hc.ζ)⌉₊ : ℝ) :=
    hradReal.trans (hrpow.trans hceil)
  have hnat : P.radius n ≤ ⌈(n : ℝ) ^ (1 - hc.ζ)⌉₊ := by exact_mod_cast hreal
  exact hnat.trans (topScale_target_le n hc.σh hc.ζ)

private theorem topScale_add_one_le_polynomial (σ ζ : ℝ)
    (hσ : 0 < σ) (hσζ : σ < ζ) (hζ : 0 < ζ) (hζ1 : ζ < 1)
    (n : ℕ) (hn : 2 ≤ n) :
    topScale n σ ζ + 1 ≤ n ^ (Nat.ceil (1 / σ) + 4) := by
  classical
  let N : ℕ := Nat.ceil (1 / σ) + 1
  let R₀ : ℕ := max 1 ⌈Real.log (n : ℝ) ^ 2⌉₊
  let M : ℕ := max 2 ⌈(n : ℝ) ^ σ⌉₊
  let target : ℕ := ⌈(n : ℝ) ^ (1 - ζ)⌉₊
  have hnReal : (1 : ℝ) ≤ n := by exact_mod_cast (show 1 ≤ n by omega)
  have hσceil : 1 ≤ σ * (Nat.ceil (1 / σ) : ℝ) := by
    have hc := Nat.le_ceil (1 / σ)
    have hmul := mul_le_mul_of_nonneg_left hc hσ.le
    have hinv : σ * (1 / σ) = 1 := by field_simp [ne_of_gt hσ]
    rw [hinv] at hmul
    exact hmul
  have hσN : 1 ≤ σ * (N : ℝ) := by
    dsimp [N]
    push_cast
    nlinarith [hσceil, hσ]
  have hR₀lower : 1 ≤ R₀ := by dsimp [R₀]; omega
  have hlogNonneg : 0 ≤ Real.log (n : ℝ) :=
    (Real.log_nonneg_iff (by positivity)).2 hnReal
  have hlogLe : Real.log (n : ℝ) ≤ n := Real.log_le_self (by positivity)
  have hlogSq : Real.log (n : ℝ) ^ 2 ≤ (n : ℝ) ^ 2 := by nlinarith
  have hR₀upper : R₀ ≤ n ^ 2 := by
    dsimp [R₀]
    apply max_le
    · exact Nat.one_le_iff_ne_zero.mpr (pow_ne_zero 2 (by omega))
    · rw [Nat.ceil_le]
      exact_mod_cast hlogSq
  have hσle1 : σ ≤ 1 := (hσζ.trans hζ1).le
  have hpowσ : (n : ℝ) ^ σ ≤ n := by
    calc
      (n : ℝ) ^ σ ≤ (n : ℝ) ^ (1 : ℝ) :=
        Real.rpow_le_rpow_of_exponent_le hnReal hσle1
      _ = n := by simp
  have hMupper : M ≤ n := by
    dsimp [M]
    apply max_le
    · omega
    · rw [Nat.ceil_le]
      exact_mod_cast hpowσ
  have hMlower : (n : ℝ) ^ σ ≤ (M : ℝ) := by
    calc
      (n : ℝ) ^ σ ≤ (Nat.ceil ((n : ℝ) ^ σ) : ℝ) := Nat.le_ceil _
      _ ≤ (M : ℝ) := by
        dsimp [M]
        exact_mod_cast (le_max_right 2 (Nat.ceil ((n : ℝ) ^ σ)))
  have htargetPow : (n : ℝ) ^ (1 - ζ) ≤ n := by
    calc
      (n : ℝ) ^ (1 - ζ) ≤ (n : ℝ) ^ (1 : ℝ) :=
        Real.rpow_le_rpow_of_exponent_le hnReal (by linarith)
      _ = n := by simp
  have htarget : target ≤ n := by
    dsimp [target]
    rw [Nat.ceil_le]
    exact_mod_cast htargetPow
  have hnPow : (n : ℝ) ≤ (n : ℝ) ^ (σ * (N : ℝ)) := by
    calc
      (n : ℝ) = (n : ℝ) ^ (1 : ℝ) := by simp
      _ ≤ (n : ℝ) ^ (σ * (N : ℝ)) :=
        Real.rpow_le_rpow_of_exponent_le hnReal hσN
  have hMpow : (n : ℝ) ^ (σ * (N : ℝ)) ≤ (M : ℝ) ^ (N : ℝ) := by
    calc
      (n : ℝ) ^ (σ * (N : ℝ)) = ((n : ℝ) ^ σ) ^ (N : ℝ) :=
        Real.rpow_mul (x := (n : ℝ)) (by positivity) σ (N : ℝ)
      _ ≤ (M : ℝ) ^ (N : ℝ) :=
        Real.rpow_le_rpow (Real.rpow_nonneg (by positivity) σ) hMlower (by positivity)
  have hnleM : n ≤ M ^ N := by
    have hreal : (n : ℝ) ≤ (M ^ N : ℕ) := by
      calc
        (n : ℝ) ≤ (n : ℝ) ^ (σ * (N : ℝ)) := hnPow
        _ ≤ (M : ℝ) ^ (N : ℝ) := hMpow
        _ = (M ^ N : ℕ) := by simp [Real.rpow_natCast]
    exact_mod_cast hreal
  have hcandidate : target ≤ M ^ N * R₀ := by
    calc
      target ≤ n := htarget
      _ ≤ M ^ N := hnleM
      _ = M ^ N * 1 := by simp
      _ ≤ M ^ N * R₀ := Nat.mul_le_mul_left _ hR₀lower
  have htop : topScale n σ ζ ≤ M ^ N * R₀ := by
    exact topScale_le_of_candidate n σ ζ N (by simpa [M, R₀, target] using hcandidate)
  have hpowM : M ^ N ≤ n ^ N := Nat.pow_le_pow_left hMupper N
  have htopPoly : topScale n σ ζ ≤ n ^ (N + 2) := by
    calc
      topScale n σ ζ ≤ M ^ N * R₀ := htop
      _ ≤ n ^ N * n ^ 2 := Nat.mul_le_mul hpowM hR₀upper
      _ = n ^ (N + 2) := (pow_add n N 2).symm
  have hpowerPos : 0 < n ^ (N + 2) := Nat.pow_pos (by omega)
  have hdouble : 2 * n ^ (N + 2) ≤ n ^ (N + 2) * n := by
    have hmul := Nat.mul_le_mul_left (n ^ (N + 2)) hn
    nlinarith
  calc
    topScale n σ ζ + 1 ≤ n ^ (N + 2) + 1 := Nat.add_le_add_right htopPoly 1
    _ ≤ 2 * n ^ (N + 2) := by nlinarith
    _ ≤ n ^ (N + 2) * n := hdouble
    _ = n ^ (N + 3) := by
      rw [show N + 3 = (N + 2) + 1 by omega, pow_succ]
      ring
    _ = n ^ (Nat.ceil (1 / σ) + 4) := by simp [N]

private theorem overlap_small_mean_eventually {P : Params9} {hc : HeightChoice9 P}
    (hadm : hc.Admissible) {c₀ : ℝ} (hc₀ : 0 < c₀) :
    ∃ n₀ : ℕ, ∀ n ≥ n₀, ∀ R' : ℕ, (Real.log (n : ℝ)) ^ 2 ≤ R' →
      ((hc.levels n + 1 : ℕ) : ℝ) * (residualBall9 P n : ℝ) *
        Real.exp (-((c₀ * R') : ℝ)) *
          ((n : ℝ) ^ (10 : ℝ) / (residualBall9 P n : ℝ)) *
            (n : ℝ) ^ (hc.b₀ - 10) ≤ Real.exp (-((c₀ * R') / 2)) := by
  classical
  have hσ : 0 < hc.σh := hadm.1
  have hσζ : hc.σh < hc.ζ := hadm.2.1
  have hζ1 : hc.ζ < 1 := hadm.2.2.1
  have hζ : 0 < hc.ζ := lt_trans hσ hσζ
  let Cn : ℕ := Nat.ceil (1 / hc.σh) + 4
  let C : ℝ := (Cn : ℝ)
  let L : ℝ := max 1 (2 * (C + hc.b₀ + 1) / c₀)
  let n₀ : ℕ := Nat.ceil (Real.exp L) + 2
  refine ⟨n₀, ?_⟩
  intro n hn R' hR'
  have hn2 : 2 ≤ n := by dsimp [n₀] at hn; omega
  have hnReal : (1 : ℝ) ≤ n := by exact_mod_cast (show 1 ≤ n by omega)
  have hnPos : 0 < (n : ℝ) := by positivity
  have hceilExp : Nat.ceil (Real.exp L) ≤ n := by
    dsimp [n₀] at hn
    omega
  have hExpLe : Real.exp L ≤ (n : ℝ) := by
    exact (Nat.le_ceil (Real.exp L)).trans (by exact_mod_cast hceilExp)
  have hlogLower : L ≤ Real.log (n : ℝ) := by
    have h := Real.log_le_log (Real.exp_pos L) hExpLe
    simpa using h
  have hlogNonneg : 0 ≤ Real.log (n : ℝ) := by
    have hL : 1 ≤ L := by dsimp [L]; exact le_max_left _ _
    linarith
  have hLratio : 2 * (C + hc.b₀ + 1) / c₀ ≤ L := by
    dsimp [L]
    exact le_max_right _ _
  have hRatioMul := mul_le_mul_of_nonneg_left (hLratio.trans hlogLower) hc₀.le
  have hCancel : c₀ * (2 * (C + hc.b₀ + 1) / c₀) = 2 * (C + hc.b₀ + 1) := by
    field_simp [ne_of_gt hc₀]
  rw [hCancel] at hRatioMul
  have hRatio : C + hc.b₀ + 1 ≤ c₀ * Real.log (n : ℝ) / 2 := by
    nlinarith [hRatioMul]
  have hCoeffLog : (C + hc.b₀) * Real.log (n : ℝ) ≤
      c₀ * (Real.log (n : ℝ)) ^ 2 / 2 := by
    have hBase : C + hc.b₀ ≤ c₀ * Real.log (n : ℝ) / 2 := by linarith
    have hmul := mul_le_mul_of_nonneg_right hBase hlogNonneg
    calc
      (C + hc.b₀) * Real.log (n : ℝ) ≤
          (c₀ * Real.log (n : ℝ) / 2) * Real.log (n : ℝ) := hmul
      _ = c₀ * (Real.log (n : ℝ)) ^ 2 / 2 := by ring
  have hExpCompare : Real.exp (c₀ * (Real.log (n : ℝ)) ^ 2 / 2) ≤
      Real.exp (c₀ * R' / 2) := by
    apply Real.exp_le_exp.mpr
    have hmul := mul_le_mul_of_nonneg_left hR' hc₀.le
    nlinarith [hmul]
  have hlevelNat : hc.levels n + 1 ≤ n ^ Cn := by
    simpa [HeightChoice9.levels, Cn] using
      (topScale_add_one_le_polynomial hc.σh hc.ζ hσ hσζ hζ hζ1 n hn2)
  have hlevelReal : ((hc.levels n + 1 : ℕ) : ℝ) ≤ (n : ℝ) ^ C := by
    calc
      ((hc.levels n + 1 : ℕ) : ℝ) ≤ (n : ℝ) ^ Cn := by exact_mod_cast hlevelNat
      _ = (n : ℝ) ^ C := by simp [C, Real.rpow_natCast]
  have hpoly : ((hc.levels n + 1 : ℕ) : ℝ) * (n : ℝ) ^ hc.b₀ ≤
      Real.exp (c₀ * R' / 2) := by
    calc
      ((hc.levels n + 1 : ℕ) : ℝ) * (n : ℝ) ^ hc.b₀ ≤
          (n : ℝ) ^ C * (n : ℝ) ^ hc.b₀ :=
        mul_le_mul_of_nonneg_right hlevelReal (Real.rpow_nonneg (Nat.cast_nonneg n) _)
      _ = (n : ℝ) ^ (C + hc.b₀) := (Real.rpow_add hnPos C hc.b₀).symm
      _ = Real.exp (Real.log (n : ℝ) * (C + hc.b₀)) := by
        rw [Real.rpow_def_of_pos hnPos]
      _ ≤ Real.exp (c₀ * (Real.log (n : ℝ)) ^ 2 / 2) :=
        Real.exp_le_exp.mpr (by nlinarith [hCoeffLog])
      _ ≤ Real.exp (c₀ * R' / 2) := hExpCompare
  have hVpos : 0 < residualBall9 P n := by
    unfold residualBall9
    have hzero : 0 ∈ Finset.range (P.radius n + 1) := by simp
    have hsum : 1 ≤ ∑ i ∈ Finset.range (P.radius n + 1),
        Nat.choose (n - P.m n) i := by
      calc
        1 = Nat.choose (n - P.m n) 0 := by simp
        _ ≤ ∑ i ∈ Finset.range (P.radius n + 1), Nat.choose (n - P.m n) i :=
          Finset.single_le_sum (fun i hi => Nat.zero_le _) hzero
    omega
  have hcancelV : (residualBall9 P n : ℝ) *
      ((n : ℝ) ^ (10 : ℝ) / (residualBall9 P n : ℝ)) = (n : ℝ) ^ (10 : ℝ) := by
    field_simp [ne_of_gt (by exact_mod_cast hVpos : (0 : ℝ) < (residualBall9 P n : ℝ))]
  have hpower : (n : ℝ) ^ (10 : ℝ) * (n : ℝ) ^ (hc.b₀ - 10) =
      (n : ℝ) ^ hc.b₀ := by
    calc
      (n : ℝ) ^ (10 : ℝ) * (n : ℝ) ^ (hc.b₀ - 10) =
          (n : ℝ) ^ (hc.b₀ - 10) * (n : ℝ) ^ (10 : ℝ) := by ring
      _ = (n : ℝ) ^ ((hc.b₀ - 10) + 10) :=
        (Real.rpow_add hnPos (hc.b₀ - 10) (10 : ℝ)).symm
      _ = (n : ℝ) ^ hc.b₀ := by congr 1 <;> ring
  have hfactor : (residualBall9 P n : ℝ) *
      ((n : ℝ) ^ (10 : ℝ) / (residualBall9 P n : ℝ)) *
        (n : ℝ) ^ (hc.b₀ - 10) = (n : ℝ) ^ hc.b₀ := by
    calc
      (residualBall9 P n : ℝ) *
          ((n : ℝ) ^ (10 : ℝ) / (residualBall9 P n : ℝ)) *
            (n : ℝ) ^ (hc.b₀ - 10) =
          (n : ℝ) ^ (10 : ℝ) * (n : ℝ) ^ (hc.b₀ - 10) := by rw [hcancelV]
      _ = (n : ℝ) ^ hc.b₀ := hpower
  calc
    ((hc.levels n + 1 : ℕ) : ℝ) * (residualBall9 P n : ℝ) *
        Real.exp (-(c₀ * R')) * ((n : ℝ) ^ (10 : ℝ) / (residualBall9 P n : ℝ)) *
        (n : ℝ) ^ (hc.b₀ - 10) =
        ((hc.levels n + 1 : ℕ) : ℝ) * (n : ℝ) ^ hc.b₀ * Real.exp (-(c₀ * R')) := by
      calc
        _ = ((hc.levels n + 1 : ℕ) : ℝ) *
            ((residualBall9 P n : ℝ) *
              ((n : ℝ) ^ (10 : ℝ) / (residualBall9 P n : ℝ)) *
                (n : ℝ) ^ (hc.b₀ - 10)) * Real.exp (-(c₀ * R')) := by ring
        _ = ((hc.levels n + 1 : ℕ) : ℝ) * (n : ℝ) ^ hc.b₀ *
              Real.exp (-(c₀ * R')) := by rw [hfactor]
    _ ≤ Real.exp (c₀ * R' / 2) * Real.exp (-(c₀ * R')) :=
      mul_le_mul_of_nonneg_right hpoly (Real.exp_nonneg _)
    _ = Real.exp (-(c₀ * R' / 2)) := by
      rw [← Real.exp_add]
      congr 1
      ring

theorem active_overlap_count_tail_eventually {P : Params9} {hc : HeightChoice9 P}
    (hadm : hc.Admissible) {K c₀ : ℝ} (hc₀ : 0 < c₀) :
    ∃ n₀ : ℕ, ∀ n ≥ n₀, ∀ (hover : HeightOverlap9 P hc n K c₀)
      (v v' : CubeVertex n) (R' : ℕ),
      1 ≤ R' → (Real.log (n : ℝ)) ^ 2 ≤ R' →
      K * R' ≤ (_root_.hammingDist v v' : ℝ) → ∀ t : ℕ,
      (heightLaw9 P hc n).pr (fun ω =>
        t ≤ ((consulted9 (P := P) (hc := hc) (n := n) v R' ∩ consulted9 v' R').filter
          (fun c => ω.1 c = true ∧ ω.2 c = true)).card) ≤
        (Real.exp (-(c₀ * R' / 2)) ^ t) := by
  obtain ⟨n₀, hsmall⟩ := overlap_small_mean_eventually hadm hc₀
  refine ⟨n₀, ?_⟩
  intro n hn hover v v' R' hR hRlog hsep t
  exact active_overlap_count_tail_of_small_mean hover v v' R' hR hsep t
    (hsmall n hn R' hRlog)

private theorem reach_level_le {P : Params9} {hc : HeightChoice9 P} {n : ℕ}
    (Pp A : Pos9 P hc n → Bool) (vq : CubeVertex n) (R : ℕ)
    {v : CubeVertex n} {j : ℕ}
    (h : Reach9 (P := P) (hc := hc) (n := n) Pp A vq R v j) : j ≤ hc.levels n := by
  induction h with
  | start v hdist => simp
  | up v j hj hreach hbad ih => omega
  | down v v' j hreach hdist hstep ih => omega

private theorem reach_le_height {P : Params9} {hc : HeightChoice9 P} {n : ℕ}
    (Pp A : Pos9 P hc n → Bool) (v : CubeVertex n)
    {j : ℕ} (h : Reach9 (P := P) (hc := hc) (n := n) Pp A v (4 * hc.levels n) v j) :
    j ≤ height9 (P := P) (hc := hc) (n := n) Pp A v := by
  classical
  have hj := reach_level_le Pp A v (4 * hc.levels n) h
  unfold height9
  change id j ≤ _
  exact Finset.le_sup (Finset.mem_filter.mpr ⟨Finset.mem_range.mpr (by omega), h⟩)

private theorem height_reachable {P : Params9} {hc : HeightChoice9 P} {n : ℕ}
    (Pp A : Pos9 P hc n → Bool) (v : CubeVertex n) :
    Reach9 (P := P) (hc := hc) (n := n) Pp A v (4 * hc.levels n) v
      (height9 (P := P) (hc := hc) (n := n) Pp A v) := by
  classical
  let S := (Finset.range (hc.levels n + 1)).filter
    (fun j => Reach9 (P := P) (hc := hc) (n := n) Pp A v (4 * hc.levels n) v j)
  have hS : S.Nonempty := by
    refine ⟨0, ?_⟩
    simp only [S, Finset.mem_filter, Finset.mem_range]
    exact ⟨by omega, Reach9.start v (by simp)⟩
  have hmem : S.sup id ∈ id '' (↑S) := Finset.sup_mem_of_nonempty (f := id) hS
  rw [Set.mem_image] at hmem
  rcases hmem with ⟨j, hj, hjval⟩
  have hj' : j = height9 (P := P) (hc := hc) (n := n) Pp A v := by
    simpa [S, height9] using hjval
  subst j
  simpa [S, height9] using (Finset.mem_filter.mp hj).2

private theorem height_le_levels {P : Params9} {hc : HeightChoice9 P} {n : ℕ}
    (Pp A : Pos9 P hc n → Bool) (v : CubeVertex n) :
    height9 (P := P) (hc := hc) (n := n) Pp A v ≤ hc.levels n := by
  classical
  unfold height9
  apply Finset.sup_le
  intro j hj
  have hj' := (Finset.mem_filter.mp hj).1
  simp only [Finset.mem_range] at hj'
  exact Nat.le_of_lt_succ hj'

private theorem height_lt_levels_of_not_reach_top {P : Params9} {hc : HeightChoice9 P} {n : ℕ}
    (Pp A : Pos9 P hc n → Bool) (v : CubeVertex n)
    (hnot : ¬ Reach9 (P := P) (hc := hc) (n := n) Pp A v (4 * hc.levels n) v (hc.levels n)) :
    height9 (P := P) (hc := hc) (n := n) Pp A v < hc.levels n := by
  have hle := height_le_levels Pp A v
  have hne : height9 (P := P) (hc := hc) (n := n) Pp A v ≠ hc.levels n := by
    intro heq
    apply hnot
    simpa [heq] using height_reachable Pp A v
  omega

private theorem height_good_at_max {P : Params9} {hc : HeightChoice9 P} {n : ℕ}
    (Pp A : Pos9 P hc n → Bool) (v : CubeVertex n)
    (hlt : height9 (P := P) (hc := hc) (n := n) Pp A v < hc.levels n) :
    ¬ badAt9 (P := P) (hc := hc) (n := n) Pp A v
      ⟨height9 (P := P) (hc := hc) (n := n) Pp A v, by omega⟩ := by
  intro hbad
  have hreach := height_reachable Pp A v
  have hup : Reach9 (P := P) (hc := hc) (n := n) Pp A v (4 * hc.levels n) v
      (height9 (P := P) (hc := hc) (n := n) Pp A v + 1) := by
    exact Reach9.up v _ hlt hreach hbad
  have hle := reach_le_height Pp A v hup
  omega

private theorem height9_le_neighbor_of_no_rootScaleFailure
    {P : Params9} {hc : HeightChoice9 P} {n : ℕ} {t s η : ℝ}
    (ht₁ : 1 / 3 ≤ t) (ht₂ : t ≤ 1) (hs : s ≤ 1 / 2) (hη : 0 ≤ η)
    (hH : 0 < hc.levels n) (Pp A : Pos9 P hc n → Bool)
    (hcounts : ∀ v : CubeVertex n, ∀ j : Fin (hc.levels n + 1),
      (1 / 2 : ℝ) * (n : ℝ) ^ (10 : ℝ) ≤
        (eligCount9 Finset.univ Pp v j : ℝ))
    (hno : ∀ root : CubeVertex n,
      ¬ rootScaleFailure9 Finset.univ t s η (hc.levels n) Pp A root)
    (v v' : CubeVertex n) (hvv' : _root_.hammingDist v v' ≤ 2) :
    height9 (P := P) (hc := hc) (n := n) Pp A v ≤
      height9 (P := P) (hc := hc) (n := n) Pp A v' + 1 := by
  let H := hc.levels n
  have hH' : 0 < H := hH
  have hReach := height_reachable Pp A v
  have hmaxle := height_le_levels Pp A v
  obtain ⟨start, rest, hpath, hstart0, hlocal⟩ :=
    reach9_to_heightPath Pp A v (4 * H) hReach
  let endpoint : HeightState9 P hc n := (v, ⟨height9 (P := P) (hc := hc) (n := n) Pp A v, by omega⟩)
  have hendpoint_mem : endpoint ∈ endpoint :: rest := by simp
  have hstart_mem : start ∈ endpoint :: rest := by
    exact heightPath9_start_mem hpath
  have hstart_v : _root_.hammingDist start.1 v ≤ 4 * H := by
    exact hlocal start hstart_mem
  have hbadTransfer : ∀ x : HeightState9 P hc n,
      badAt9 (P := P) (hc := hc) (n := n) Pp A x.1 x.2 →
        scaleBad9 Finset.univ t s Pp A x := by
    intro x hb
    exact scaleBad9_of_badAt9_counts ht₁ ht₂ hs Pp A hcounts x hb
  have hmetricSmall : ∀ x ∈ endpoint :: rest,
      max (Nat.dist x.2.val start.2.val) ((_root_.hammingDist x.1 start.1 + 1) / 2) < H := by
    intro x hx
    by_contra hnot
    have hge : H ≤ max (Nat.dist x.2.val start.2.val)
        ((_root_.hammingDist x.1 start.1 + 1) / 2) := Nat.le_of_not_gt hnot
    obtain ⟨suffix, hprefix, hsub⟩ := heightPath9_suffix hpath hx
    have hprefix' : HeightPath9 (heightStep9 (scaleBad9 Finset.univ t s Pp A))
        (x :: suffix) start := heightPath9_mono hbadTransfer hprefix
    have hsite : ∀ y ∈ x :: suffix, _root_.hammingDist y.1 start.1 ≤ 16 * H := by
      intro y hy
      have hyorig := hsub y hy
      have hyroot := hlocal y hyorig
      have hrootstart := hlocal start hstart_mem
      have hrootstart' : _root_.hammingDist v start.1 ≤ 4 * H := by
        simpa [_root_.hammingDist_comm] using hrootstart
      have htri := _root_.hammingDist_triangle y.1 v start.1
      calc
        _root_.hammingDist y.1 start.1 ≤ _root_.hammingDist y.1 v +
            _root_.hammingDist v start.1 := htri
        _ ≤ 4 * H + 4 * H := Nat.add_le_add hyroot hrootstart'
        _ ≤ 16 * H := by omega
    have hlevel : ∀ y ∈ x :: suffix, Nat.dist y.2.val start.2.val ≤ 8 * H := by
      intro y hy
      have _hyorig := hsub y hy
      have hylt := y.2.isLt
      rw [hstart0, Nat.dist_zero_right]
      omega
    have hrise : (start.2.val : ℝ) ≤ (x.2.val : ℝ) + η * (H : ℝ) := by
      rw [hstart0]
      have hxnonneg : 0 ≤ (x.2.val : ℝ) := Nat.cast_nonneg _
      have hHnonneg : 0 ≤ (H : ℝ) := Nat.cast_nonneg _
      exact le_trans (by norm_num) (add_nonneg hxnonneg (mul_nonneg hη hHnonneg))
    have hfail := rootScaleFailure9_of_path Pp A v start x suffix
      (hstart_v.trans (by omega))
      hprefix' hsite hlevel hge hrise
    exact (hno v) hfail
  have hspatialBound : ∀ x ∈ endpoint :: rest,
      _root_.hammingDist x.1 start.1 ≤ 2 * H - 2 := by
    intro x hx
    have hm := hmetricSmall x hx
    have hsp := lt_of_le_of_lt (Nat.le_max_right _ _) hm
    omega
  have hstartEndpoint : _root_.hammingDist start.1 v ≤ 2 * H - 2 := by
    have h := hspatialBound endpoint hendpoint_mem
    simpa [endpoint, _root_.hammingDist_comm] using h
  have hstartV' : _root_.hammingDist start.1 v' ≤
      _root_.hammingDist start.1 v + _root_.hammingDist v v' :=
    _root_.hammingDist_triangle start.1 v v'
  have hlocal' : ∀ x ∈ endpoint :: rest, _root_.hammingDist x.1 v' ≤ 4 * H := by
    intro x hx
    have hxstart := hspatialBound x hx
    calc
      _root_.hammingDist x.1 v' ≤ _root_.hammingDist x.1 start.1 +
          _root_.hammingDist start.1 v' := _root_.hammingDist_triangle x.1 start.1 v'
      _ ≤ (2 * H - 2) + ((2 * H - 2) + 2) := by omega
      _ ≤ 4 * H := by omega
  obtain ⟨endpt, hendpt, hreachAtV'⟩ :=
    heightPath9_to_reach9 Pp A v' (4 * H) hpath hstart0 hlocal'
  have hendpt' : endpt = endpoint := by simpa using hendpt.symm
  subst endpt
  by_cases hzero : height9 (P := P) (hc := hc) (n := n) Pp A v = 0
  · simp [hzero]
  · have hpos : 1 ≤ height9 (P := P) (hc := hc) (n := n) Pp A v := by omega
    have hreachLow : Reach9 (P := P) (hc := hc) (n := n) Pp A v'
        (4 * H) v' (height9 (P := P) (hc := hc) (n := n) Pp A v - 1) := by
      exact Reach9.down v v' (height9 (P := P) (hc := hc) (n := n) Pp A v - 1)
        (by simpa [Nat.sub_add_cancel hpos] using hreachAtV')
        (by simp)
        hvv'
    have hle := reach_le_height Pp A v' hreachLow
    omega

private theorem height9_lipschitz_of_no_rootScaleFailure
    {P : Params9} {hc : HeightChoice9 P} {n : ℕ} {t s η : ℝ}
    (ht₁ : 1 / 3 ≤ t) (ht₂ : t ≤ 1) (hs : s ≤ 1 / 2) (hη : 0 ≤ η)
    (hH : 0 < hc.levels n) (Pp A : Pos9 P hc n → Bool)
    (hcounts : ∀ v : CubeVertex n, ∀ j : Fin (hc.levels n + 1),
      (1 / 2 : ℝ) * (n : ℝ) ^ (10 : ℝ) ≤
        (eligCount9 Finset.univ Pp v j : ℝ))
    (hno : ∀ root : CubeVertex n,
      ¬ rootScaleFailure9 Finset.univ t s η (hc.levels n) Pp A root)
    (v v' : CubeVertex n) (hvv' : _root_.hammingDist v v' ≤ 2) :
    Nat.dist (height9 (P := P) (hc := hc) (n := n) Pp A v)
      (height9 (P := P) (hc := hc) (n := n) Pp A v') ≤ 1 := by
  have hforward := height9_le_neighbor_of_no_rootScaleFailure
    ht₁ ht₂ hs hη hH Pp A hcounts hno v v' hvv'
  have hsymm : _root_.hammingDist v' v ≤ 2 := by
    simpa [_root_.hammingDist_comm] using hvv'
  have hbackward := height9_le_neighbor_of_no_rootScaleFailure
    ht₁ ht₂ hs hη hH Pp A hcounts hno v' v hsymm
  unfold Nat.dist
  omega

private theorem heightLevels9_pos {P : Params9} {hc : HeightChoice9 P} (n : ℕ) :
    0 < hc.levels n := by
  unfold HeightChoice9.levels topScale
  dsimp only
  positivity

private theorem goodHeights9_of_no_rootScaleFailure
    {P : Params9} {hc : HeightChoice9 P} {n : ℕ}
    (Pp A : Pos9 P hc n → Bool)
    (hcounts : ∀ v : CubeVertex n, ∀ j : Fin (hc.levels n + 1),
      (1 / 2 : ℝ) * (n : ℝ) ^ (10 : ℝ) ≤
        (eligCount9 Finset.univ Pp v j : ℝ))
    (hno : ∀ root : CubeVertex n,
      ¬ rootScaleFailure9 Finset.univ (1 / 3) (1 / 8) (1 / 4)
        (hc.levels n) Pp A root) :
    GoodHeights9 (P := P) (hc := hc) (n := n) Pp A := by
  have hnot : ∀ v : CubeVertex n,
      ¬ Reach9 (P := P) (hc := hc) (n := n) Pp A v (4 * hc.levels n) v
        (hc.levels n) := by
    intro v hreach
    have hfail : rootScaleFailure9 Finset.univ (1 / 3) (1 / 8) (1 / 4)
        (hc.levels n) Pp A v :=
      reach9_top_implies_rootScaleFailure9 (t := 1 / 3) (s := 1 / 8) (η := 1 / 4)
        (by norm_num) (by norm_num) (by norm_num) (by norm_num)
        Pp A hcounts v hreach
    exact hno v hfail
  have hlip : ∀ v v' : CubeVertex n, _root_.hammingDist v v' ≤ 2 →
      Nat.dist (height9 (P := P) (hc := hc) (n := n) Pp A v)
        (height9 (P := P) (hc := hc) (n := n) Pp A v') ≤ 1 := by
    intro v v' hvv'
    exact height9_lipschitz_of_no_rootScaleFailure
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (heightLevels9_pos n) Pp A hcounts hno v v' hvv'
  intro v
  have hlt := height_lt_levels_of_not_reach_top Pp A v (hnot v)
  refine ⟨hlt, height_good_at_max Pp A v hlt, ?_⟩
  intro v' hvv'
  exact hlip v v' hvv'

private theorem goodHeights9_of_no_rootBadPair9 {P : Params9} {hc : HeightChoice9 P} {n : ℕ}
    (ω : Pos9 P hc n → Bool × Bool)
    (hno : ∀ root : CubeVertex n, ¬ rootBadPair9 (1 / 3) (1 / 8) (1 / 4) root ω) :
    GoodHeights9 (P := P) (hc := hc) (n := n)
      ((heightFieldsEquiv9 (P := P) (hc := hc) (n := n)).symm ω).1
      ((heightFieldsEquiv9 (P := P) (hc := hc) (n := n)).symm ω).2 := by
  let fields := (heightFieldsEquiv9 (P := P) (hc := hc) (n := n)).symm ω
  have hcounts : ∀ v : CubeVertex n, ∀ j : Fin (hc.levels n + 1),
      (1 / 2 : ℝ) * (n : ℝ) ^ (10 : ℝ) ≤
        (eligCount9 Finset.univ fields.1 v j : ℝ) := by
    intro v j
    by_contra h
    have hlow : (eligCount9 Finset.univ fields.1 v j : ℝ) < (n : ℝ) ^ (10 : ℝ) / 2 := by
      nlinarith
    have hcount : rootCountFailure9 v fields.1 := by
      refine ⟨(v, j), ?_, hlow⟩
      simp
    have hbad : rootBadPair9 (1 / 3) (1 / 8) (1 / 4) v ω := Or.inr hcount
    exact hno v hbad
  have hnoScale : ∀ root : CubeVertex n,
      ¬ rootScaleFailure9 Finset.univ (1 / 3) (1 / 8) (1 / 4)
        (hc.levels n) fields.1 fields.2 root := by
    intro root hfail
    exact hno root (Or.inl hfail)
  exact goodHeights9_of_no_rootScaleFailure fields.1 fields.2 hcounts hnoScale

private theorem exists_goodHeights9_of_small_root_events {P : Params9} {hc : HeightChoice9 P}
    {n : ℕ} {ε : ℝ} {Δ : ℕ} (hmn : P.m n ≤ n) (hcounts : HeightCounts9 P hc n)
    (hdegree : ∀ root : CubeVertex n,
      (Finset.univ.filter
        (fun root' => root' ≠ root ∧ ¬ Disjoint
          (scaleRootSupport9 (P := P) (hc := hc) (n := n) root (hc.levels n))
          (scaleRootSupport9 (P := P) (hc := hc) (n := n) root' (hc.levels n)))).card ≤ Δ)
    (hscale : ∀ root : CubeVertex n,
      (heightLaw9 P hc n).pr (fun ω =>
        rootScaleFailure9 Finset.univ (1 / 3) (1 / 8) (1 / 4)
          (hc.levels n) ω.1 ω.2 root) ≤ ε)
    (hsmall : ε + Real.exp (-(n : ℝ)) ≤ 1 / (4 * ((Δ + 1 : ℕ) : ℝ))) :
    ∃ Pp A : Pos9 P hc n → Bool, GoodHeights9 Pp A := by
  obtain ⟨x, hx0, hx1, hinput⟩ := heightRootLLLInput9_of_small
    hmn hcounts hdegree hscale hsmall
  obtain ⟨ω, hno⟩ := exists_pair_fields_avoiding_rootBad9 hinput
  let fields := (heightFieldsEquiv9 (P := P) (hc := hc) (n := n)).symm ω
  exact ⟨fields.1, fields.2, goodHeights9_of_no_rootBadPair9 ω hno⟩

theorem goodHeights_of_no_top_reach {P : Params9} {hc : HeightChoice9 P} {n : ℕ}
    (Pp A : Pos9 P hc n → Bool)
    (hnot : ∀ v : CubeVertex n,
      ¬ Reach9 (P := P) (hc := hc) (n := n) Pp A v (4 * hc.levels n) v (hc.levels n))
    (hlip : ∀ v v' : CubeVertex n, _root_.hammingDist v v' ≤ 2 →
      Nat.dist (height9 (P := P) (hc := hc) (n := n) Pp A v)
        (height9 (P := P) (hc := hc) (n := n) Pp A v') ≤ 1) :
    GoodHeights9 (P := P) (hc := hc) (n := n) Pp A := by
  intro v
  have hlt := height_lt_levels_of_not_reach_top Pp A v (hnot v)
  refine ⟨hlt, height_good_at_max Pp A v hlt, ?_⟩
  intro v' hvv'
  exact hlip v v' hvv'

end HypercubeRamsey.Lane_q_s09_hind
