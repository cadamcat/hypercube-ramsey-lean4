import HypercubeRamsey.S09.Map.Device
import HypercubeRamsey.S03.Clock.Steps_p_clock_r4

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

private inductive HeightPath9 {P : Params9} {hc : HeightChoice9 P} {n : ℕ}
    (step : HeightState9 P hc n → HeightState9 P hc n → Prop) :
    List (HeightState9 P hc n) → HeightState9 P hc n → Prop
  | singleton (x : HeightState9 P hc n) : HeightPath9 step [x] x
  | cons {x y : HeightState9 P hc n} {l : List (HeightState9 P hc n)} {start : HeightState9 P hc n}
      (hxy : step y x) (hp : HeightPath9 step (y :: l) start) :
      HeightPath9 step (x :: y :: l) start

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
      (∀ x ∈ ((v, ⟨j, by have := reach_level_le_for_path9 Pp A vq R h; omega⟩) :: l),
        _root_.hammingDist x.1 vq ≤ R) := by
  induction h with
  | start v hdist =>
      refine ⟨(v, ⟨0, by omega⟩), ⟨[], ?_⟩⟩
      constructor
      · simpa using (HeightPath9.singleton (step := heightStep9
          (fun x => badAt9 (P := P) (hc := hc) (n := n) Pp A x.1 x.2)) (v, ⟨0, by omega⟩))
      · intro x hx
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
        subst x
        exact hdist
  | @up v j hj hreach hbad ih =>
      obtain ⟨start, l, hp, hlocal⟩ := ih
      let x : HeightState9 P hc n := (v, ⟨j, by omega⟩)
      let y : HeightState9 P hc n := (v, ⟨j + 1, by omega⟩)
      refine ⟨start, ⟨x :: l, ?_⟩⟩
      constructor
      · have hedge : heightStep9
            (fun z => badAt9 (P := P) (hc := hc) (n := n) Pp A z.1 z.2) x y := by
          left
          exact ⟨rfl, rfl, hbad⟩
        simpa [x, y] using HeightPath9.cons hedge hp
      · intro z hz
        simp only [List.mem_cons] at hz
        rcases hz with rfl | hz
        · have hxlocal := hlocal x (by simp [x])
          simpa [x, y] using hxlocal
        · exact hlocal _ (by simpa [x] using hz)
  | @down v v' j hreach hdistRoot hstep ih =>
      obtain ⟨start, l, hp, hlocal⟩ := ih
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
      · intro z hz
        simp only [List.mem_cons] at hz
        rcases hz with rfl | hz
        · exact hdistRoot
        · exact hlocal _ (by simpa [x] using hz)

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

private noncomputable def scaleSupport9 {P : Params9} {hc : HeightChoice9 P} {n : ℕ}
    (start : HeightState9 P hc n) (R : ℕ) : Finset (Pos9 P hc n) :=
  (consulted9 (P := P) (hc := hc) (n := n) start.1 (8 * R)).filter
    (fun c => Nat.dist c.level.val start.2.val ≤ 8 * R + 2)

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
