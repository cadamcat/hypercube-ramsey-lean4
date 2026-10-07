import HypercubeRamsey.S09.Map.Device
import HypercubeRamsey.Framework.FinProbLemmas

/-!
Lane-local helpers for the Section 9 height induction.  In particular, these isolate the deterministic facts
about the path maximum from the probabilistic multiscale estimate.
-/

namespace HypercubeRamsey.Lane_q_s09_hind

open HypercubeRamsey
open OAI.HypercubeRamsey

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

theorem badAt9_with_eligible_size_bound {P : Params9} {hc : HeightChoice9 P} {n : ℕ}
    {c : ℝ} (hbase : HeightBase9 P hc n c)
    (v : CubeVertex n) (j : Fin (hc.levels n + 1)) :
    (heightLaw9 P hc n).pr (fun ω =>
      badAt9 (P := P) (hc := hc) (n := n) ω.1 ω.2 v j ∧
        (1 / 8 : ℝ) * (n : ℝ) ^ (10 : ℝ) ≤ (eligCount9 Finset.univ ω.1 v j : ℝ)) ≤
      Real.exp (-((n : ℝ) ^ c)) := by
  have h := hbase Finset.univ 1 (1 / 8) (by norm_num) (by norm_num) (by norm_num) v j
  simpa [badAt9, badIn9] using h

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
        _ ≤ μ.pr (E a) + μ.pr (fun ω => ∃ i ∈ S, E i ω) := FinProb.pr_union μ _ _
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
      FinProb.pr_union μ _ _
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
