import HypercubeRamsey.S04.Experiment

/-!
# Lemma 4.1 core: small proved helpers

Probability monotonicity, the greedy maximal disjoint family (D4.5's marking rule), cube adjacency of even and
odd roles, and monotonicity of the host regime.  All proofs are complete.
-/

namespace HypercubeRamsey.S04

open Classical OAI.HypercubeRamsey
open scoped BigOperators

/-- Probability is monotone in the event. -/
theorem pr_mono {Ω : Type*} [Fintype Ω] (P : FinProb Ω) {A B : Ω → Prop} (h : ∀ ω, A ω → B ω) :
    P.pr A ≤ P.pr B := by
  unfold FinProb.pr
  apply Finset.sum_le_sum
  intro ω _
  by_cases hA : A ω
  · simp [hA, h ω hA]
  · by_cases hB : B ω
    · simp [hA, hB, P.nonneg ω]
    · simp [hA, hB]

/-- Probabilities are nonnegative. -/
theorem pr_nonneg {Ω : Type*} [Fintype Ω] (P : FinProb Ω) (A : Ω → Prop) : 0 ≤ P.pr A := by
  unfold FinProb.pr
  apply Finset.sum_nonneg
  intro ω _
  split_ifs
  · exact P.nonneg ω
  · exact le_rfl

/-- `P(A) + P(¬A) = 1`. -/
theorem pr_add_pr_not {Ω : Type*} [Fintype Ω] (P : FinProb Ω) (A : Ω → Prop) :
    P.pr A + P.pr (fun ω => ¬ A ω) = 1 := by
  unfold FinProb.pr
  rw [← Finset.sum_add_distrib, ← P.sum_eq_one]
  apply Finset.sum_congr rfl
  intro ω _
  by_cases hA : A ω <;> simp [hA]

theorem greedy_foldl_spec {α : Type*} [DecidableEq α] (L : List (Finset α)) (F : Finset (Finset α)) :
    F ⊆ L.foldl greedyStep F ∧
      (∀ A ∈ L.foldl greedyStep F, A ∈ F ∨ A ∈ L) ∧
      ((∀ A ∈ F, ∀ B ∈ F, A ≠ B → Disjoint A B) →
        ∀ A ∈ L.foldl greedyStep F, ∀ B ∈ L.foldl greedyStep F, A ≠ B → Disjoint A B) ∧
      (∀ D ∈ L, D.Nonempty → ∃ A ∈ L.foldl greedyStep F, ¬ Disjoint A D) := by
  induction L generalizing F with
  | nil =>
    refine ⟨subset_refl _, fun A hA => Or.inl hA, fun h => h, ?_⟩
    intro D hD
    simp at hD
  | cons D L ih =>
    obtain ⟨h1, h2, h3, h4⟩ := ih (greedyStep F D)
    have hFF' : F ⊆ greedyStep F D := by
      unfold greedyStep
      split_ifs
      · exact Finset.subset_insert _ _
      · exact subset_refl _
    have hF'mem : ∀ A ∈ greedyStep F D, A ∈ F ∨ A = D := by
      intro A hA
      unfold greedyStep at hA
      split_ifs at hA
      · rcases Finset.mem_insert.mp hA with h | h
        · exact Or.inr h
        · exact Or.inl h
      · exact Or.inl hA
    simp only [List.foldl_cons]
    refine ⟨hFF'.trans h1, ?_, ?_, ?_⟩
    · intro A hA
      rcases h2 A hA with h | h
      · rcases hF'mem A h with h' | h'
        · exact Or.inl h'
        · exact Or.inr (by simp [h'])
      · exact Or.inr (List.mem_cons_of_mem _ h)
    · intro hF
      apply h3
      intro A hA B hB hAB
      unfold greedyStep at hA hB
      by_cases hdisj : ∀ A ∈ F, Disjoint A D
      · rw [if_pos hdisj] at hA hB
        rcases Finset.mem_insert.mp hA with rfl | hA'
        · rcases Finset.mem_insert.mp hB with rfl | hB'
          · exact absurd rfl hAB
          · exact (hdisj B hB').symm
        · rcases Finset.mem_insert.mp hB with rfl | hB'
          · exact hdisj A hA'
          · exact hF A hA' B hB' hAB
      · rw [if_neg hdisj] at hA hB
        exact hF A hA B hB hAB
    · intro D' hD' hne
      rcases List.mem_cons.mp hD' with rfl | hD'L
      · by_cases hdisj : ∀ A ∈ F, Disjoint A D'
        · refine ⟨D', h1 ?_, ?_⟩
          · unfold greedyStep
            rw [if_pos hdisj]
            exact Finset.mem_insert_self _ _
          · rw [Finset.disjoint_self_iff_empty]
            exact hne.ne_empty
        · push_neg at hdisj
          obtain ⟨A, hA, hAD⟩ := hdisj
          exact ⟨A, h1 (hFF' hA), hAD⟩
      · exact h4 D' hD'L hne

/-- The greedy family consists of members of the list, is pairwise disjoint, and meets every nonempty member of
the list (maximality, 04:304–308). -/
theorem greedy_spec {α : Type*} [DecidableEq α] (L : List (Finset α)) :
    (∀ A ∈ greedy L, A ∈ L) ∧ (∀ A ∈ greedy L, ∀ B ∈ greedy L, A ≠ B → Disjoint A B) ∧
      (∀ D ∈ L, D.Nonempty → ∃ A ∈ greedy L, ¬ Disjoint A D) := by
  obtain ⟨_, h2, h3, h4⟩ := greedy_foldl_spec L ∅
  refine ⟨fun A hA => ?_, h3 (by simp), h4⟩
  rcases h2 A hA with h | h
  · simp at h
  · exact h

/-- A neighbour of an even role is one of its coordinate flips. -/
theorem exists_oddNbr_of_adj {n : ℕ} (a : EvenRole n) (b : OddRole n) (h : (cube n).Adj a.1 b.1) :
    ∃ j, b = oddNbr a j := by
  have hone : (Finset.univ.filter fun i : Fin n => a.1 i ≠ b.1 i).card = 1 := h
  obtain ⟨j, hj⟩ := Finset.card_eq_one.mp hone
  refine ⟨j, Subtype.ext ?_⟩
  funext i
  change b.1 i = cubeFlip a.1 j i
  by_cases hij : i = j
  · subst hij
    have hmem : i ∈ Finset.univ.filter fun i : Fin n => a.1 i ≠ b.1 i := by
      rw [hj]; exact Finset.mem_singleton_self _
    have hne : a.1 i ≠ b.1 i := (Finset.mem_filter.mp hmem).2
    simp only [cubeFlip, Function.update_self]
    cases ha : a.1 i <;> cases hb : b.1 i <;> simp_all
  · have hnot : i ∉ Finset.univ.filter fun i : Fin n => a.1 i ≠ b.1 i := by
      rw [hj]; simpa using hij
    have heq : a.1 i = b.1 i := by
      by_contra hne
      exact hnot (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hne⟩)
    simp only [cubeFlip, Function.update_of_ne hij]
    exact heq.symm

/-- Monotonicity of the host regime in its constant. -/
theorem largeHost_mono {C C' : ℝ} {n N : ℕ} (h : LargeHost C n N) (hC : C' ≤ C) :
    LargeHost C' n N :=
  ⟨le_trans (mul_le_mul_of_nonneg_right hC (by positivity)) h.1, h.2⟩

end HypercubeRamsey.S04
