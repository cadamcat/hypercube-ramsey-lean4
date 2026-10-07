import HypercubeRamsey.PartC.Core

namespace HypercubeRamsey.Lane_q_s15_c3

open scoped BigOperators

theorem even_prefix_card_le {n ell : ℕ} (w : CubePos n)
    (E : Finset {v : CubePos n // IsEvenRole v})
    (hE : ∀ a ∈ E, ∀ j : Fin n, j.val < ell → a.1 j = w j)
    (hell : ell ≤ n) : E.card ≤ 2 ^ (n - ell) := by
  classical
  let code : {a : {v : CubePos n // IsEvenRole v} // a ∈ E} → CubePos (n - ell) :=
    fun a j => a.1.1 ⟨ell + j.val, by omega⟩
  have hcode : Function.Injective code := by
    intro a b hab
    apply Subtype.ext
    apply Subtype.ext
    funext j
    by_cases hj : j.val < ell
    · exact (hE a.1 a.2 j hj).trans (hE b.1 b.2 j hj).symm
    · let t : Fin (n - ell) := ⟨j.val - ell, by omega⟩
      have ht : (⟨ell + t.val, by omega⟩ : Fin n) = j := by
        apply Fin.ext
        simp [t]
        omega
      have htail := congrFun hab t
      change a.1.1 ⟨ell + t.val, by omega⟩ = b.1.1 ⟨ell + t.val, by omega⟩ at htail
      rw [ht] at htail
      exact htail
  calc
    E.card = Fintype.card {a : {v : CubePos n // IsEvenRole v} // a ∈ E} := by simp
    _ ≤ Fintype.card (CubePos (n - ell)) := Fintype.card_le_of_injective code hcode
    _ = 2 ^ (n - ell) := by simp [CubePos]

theorem nat_sq_le_two_pow (n : ℕ) (hn : 4 ≤ n) :
    (n : ℝ) ^ 2 ≤ (2 : ℝ) ^ n := by
  induction n with
  | zero => omega
  | succ n ih =>
      by_cases hsmall : n < 4
      · interval_cases n <;> norm_num at *
      · have hnprev : 4 ≤ n := by omega
        have hprev := ih hnprev
        have hstep : ((n + 1 : ℕ) : ℝ) ^ 2 ≤ 2 * (n : ℝ) ^ 2 := by
          have hn3 : (3 : ℝ) ≤ n := by exact_mod_cast (by omega : 3 ≤ n)
          push_cast
          nlinarith
        calc
          ((n + 1 : ℕ) : ℝ) ^ 2 ≤ 2 * (n : ℝ) ^ 2 := hstep
          _ ≤ 2 * (2 : ℝ) ^ n := mul_le_mul_of_nonneg_left hprev (by positivity)
          _ = (2 : ℝ) ^ (n + 1) := by rw [pow_succ]; ring

theorem finLaw_pr_exists_le_sum {ι Ω : Type*} [Fintype ι] [Fintype Ω]
    [DecidableEq ι] [DecidableEq Ω] (P : FinLaw Ω) (E : ι → Ω → Prop) :
    P.pr (fun ω => ∃ i, E i ω) ≤ ∑ i, P.pr (E i) := by
  classical
  letI : DecidablePred (fun ω => ∃ i, E i ω) := fun ω => Fintype.decidableExistsFintype
  unfold FinLaw.pr
  calc
    (∑ ω, @ite ℝ (∃ i, E i ω) (Classical.propDecidable _) (P.w ω) 0) ≤
        ∑ ω, ∑ i, if E i ω then P.w ω else 0 := by
      apply Finset.sum_le_sum
      intro ω hω
      by_cases hex : ∃ i, E i ω
      · obtain ⟨i, hi⟩ := hex
        have hnonneg : ∀ j ∈ (Finset.univ : Finset ι),
            0 ≤ if E j ω then P.w ω else 0 := by
          intro j hj
          split_ifs with h
          · exact P.nonneg ω
          · exact le_rfl
        have hsingle := Finset.single_le_sum hnonneg (Finset.mem_univ i)
        rw [if_pos ⟨i, hi⟩]
        simpa [hi] using hsingle
      · rw [if_neg hex]
        have hnonneg : 0 ≤ ∑ i, if E i ω then P.w ω else 0 := by
          apply Finset.sum_nonneg
          intro i hi
          split_ifs with h
          · exact P.nonneg ω
          · exact le_rfl
        exact hnonneg
    _ = ∑ i, P.pr (E i) := by
      rw [Finset.sum_comm]
      rfl

theorem finLaw_pr_pos_exists {Ω : Type*} [Fintype Ω] [DecidableEq Ω]
    (P : FinLaw Ω) (A : Ω → Prop) (hA : 0 < P.pr A) :
    ∃ ω, P.w ω ≠ 0 ∧ A ω := by
  classical
  by_contra h
  have hzero : ∀ ω, (if A ω then P.w ω else 0) = 0 := by
    intro ω
    by_cases hmem : A ω
    · have hw : P.w ω = 0 := by
        by_contra hw
        exact h ⟨ω, hw, hmem⟩
      simp [hmem, hw]
    · simp [hmem]
  have hsum : (∑ ω, if A ω then P.w ω else 0) = 0 := by
    apply Finset.sum_eq_zero
    intro ω hω
    exact hzero ω
  unfold FinLaw.pr at hA
  rw [hsum] at hA
  linarith

theorem finLaw_pr_mono {Ω : Type*} [Fintype Ω] [DecidableEq Ω]
    (P : FinLaw Ω) (A B : Ω → Prop) (hAB : ∀ ω, A ω → B ω) :
    P.pr A ≤ P.pr B := by
  classical
  unfold FinLaw.pr
  apply Finset.sum_le_sum
  intro ω hω
  by_cases hA : A ω
  · have hB := hAB ω hA
    simp [hA, hB]
  · by_cases hB : B ω
    · simpa [hA, hB] using P.nonneg ω
    · simp [hA, hB]

theorem finLaw_pr_union {Ω : Type*} [Fintype Ω] [DecidableEq Ω]
    (P : FinLaw Ω) (A B : Ω → Prop) :
    P.pr (fun ω => A ω ∨ B ω) ≤ P.pr A + P.pr B := by
  classical
  unfold FinLaw.pr
  calc
    (∑ ω, @ite ℝ (A ω ∨ B ω) (Classical.propDecidable _) (P.w ω) 0) ≤
        ∑ ω, ((if A ω then P.w ω else 0) + (if B ω then P.w ω else 0)) := by
      apply Finset.sum_le_sum
      intro ω hω
      by_cases hAB : A ω ∨ B ω
      · rw [if_pos hAB]
        by_cases hA : A ω
        · have hnonneg : 0 ≤ if B ω then P.w ω else 0 := by
            split_ifs with h
            · exact P.nonneg ω
            · exact le_rfl
          simp [hA]
          linarith
        · have hB : B ω := hAB.resolve_left hA
          simp [hA, hB]
      · have hA : ¬ A ω := fun h => hAB (Or.inl h)
        have hB : ¬ B ω := fun h => hAB (Or.inr h)
        simp [hA, hB]
    _ = (∑ ω, if A ω then P.w ω else 0) +
        ∑ ω, if B ω then P.w ω else 0 := by rw [Finset.sum_add_distrib]
    _ = P.pr A + P.pr B := by rfl

theorem finLaw_pr_markov {Ω : Type*} [Fintype Ω] [DecidableEq Ω]
    (P : FinLaw Ω) (H : Ω → Prop) [DecidablePred H] (F : Ω → ℝ)
    (hF : ∀ ω, H ω → 0 ≤ F ω) (t : ℝ) (ht : 0 < t) (m : ℕ) :
    P.pr (fun ω => H ω ∧ t < F ω) ≤
      P.E (fun ω => if H ω then F ω ^ m else 0) / t ^ m := by
  have htpow : 0 < t ^ m := pow_pos ht _
  unfold FinLaw.pr FinLaw.E
  calc
    (∑ ω, @ite ℝ (H ω ∧ t < F ω) (Classical.propDecidable _) (P.w ω) 0) ≤
        ∑ ω, (P.w ω * (if H ω then F ω ^ m else 0)) / t ^ m := by
      apply Finset.sum_le_sum
      intro ω hω
      by_cases hev : H ω ∧ t < F ω
      · rw [if_pos hev, if_pos hev.1]
        have hpow : t ^ m ≤ F ω ^ m :=
          pow_le_pow_left₀ (le_of_lt ht) (le_of_lt hev.2) m
        have hmul := mul_le_mul_of_nonneg_left hpow (P.nonneg ω)
        exact (le_div_iff₀ htpow).2 hmul
      · rw [if_neg hev]
        have hnonneg : 0 ≤ P.w ω * (if H ω then F ω ^ m else 0) := by
          by_cases hH : H ω
          · simp only [if_pos hH]
            exact mul_nonneg (P.nonneg ω) (pow_nonneg (hF ω hH) _)
          · simp [hH]
        exact div_nonneg hnonneg htpow.le
    _ = (∑ ω, P.w ω * (if H ω then F ω ^ m else 0)) / t ^ m := by
      rw [Finset.sum_div (s := Finset.univ)]

theorem finLaw_cond_E_eq {Ω : Type*} [Fintype Ω] [DecidableEq Ω]
    (P : FinLaw Ω) (A : Finset Ω) (hA : 0 < ∑ ω ∈ A, P.w ω)
    (F : Ω → ℝ) :
    (FinLaw.cond P A hA).E F =
      (∑ ω ∈ A, P.w ω * F ω) / (∑ ω ∈ A, P.w ω) := by
  letI : DecidableEq Ω := Classical.decEq Ω
  simp only [FinLaw.E, FinLaw.cond]
  calc
    (∑ ω, ((if ω ∈ A then P.w ω else 0) / (∑ x ∈ A, P.w x)) * F ω) =
        ∑ ω, ((if ω ∈ A then P.w ω else 0) * F ω) / (∑ x ∈ A, P.w x) := by
          apply Finset.sum_congr rfl
          intro ω hω
          by_cases hmem : ω ∈ A
          · simp [hmem]
            ring
          · simp [hmem]
    _ = (∑ ω, (if ω ∈ A then P.w ω else 0) * F ω) / (∑ x ∈ A, P.w x) := by
          rw [Finset.sum_div]
    _ = (∑ ω ∈ A, P.w ω * F ω) / (∑ x ∈ A, P.w x) := by
          congr 1
          simp [Finset.sum_ite_mem, Finset.univ_inter]

theorem finLaw_cond_E_le {Ω : Type*} [Fintype Ω] [DecidableEq Ω]
    (P : FinLaw Ω) (A : Finset Ω) (hA : 0 < ∑ ω ∈ A, P.w ω)
    (F : Ω → ℝ) (hF : ∀ ω, 0 ≤ F ω) :
    (FinLaw.cond P A hA).E F ≤ P.E F / (∑ ω ∈ A, P.w ω) := by
  rw [finLaw_cond_E_eq]
  apply (div_le_div_of_nonneg_right _ hA.le)
  apply Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ A)
  intro ω hω hnot
  exact mul_nonneg (P.nonneg ω) (hF ω)

end HypercubeRamsey.Lane_q_s15_c3
