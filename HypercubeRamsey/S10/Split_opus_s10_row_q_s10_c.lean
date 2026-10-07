import HypercubeRamsey.Framework.FinProbLemmas

/-!
# Lane q-s10-c helpers for the Section 10 tagged-to-typical step
-/

namespace HypercubeRamsey.Lane_q_s10_c

open scoped BigOperators

/-- Under a product law, a finite product of functions with pairwise disjoint
coordinate scopes has expectation equal to the product of their expectations.
This is the finite-family form of `FinProb.pi_expect_mul_of_disjoint`. -/
theorem pi_expect_prod_pairwise_disjoint {ι ξ : Type*} [Fintype ι] [DecidableEq ι]
    [Fintype ξ] [DecidableEq ξ] {Ω : ι → Type*} [∀ i, Fintype (Ω i)]
    (P : ∀ i, FinProb (Ω i)) (s : Finset ξ)
    (f : ξ → (∀ i, Ω i) → ℝ) (scope : ξ → Finset ι)
    (hf : ∀ j, FinProb.DependsOn (f j) (scope j))
    (hdisj : ∀ j ∈ s, ∀ k ∈ s, j ≠ k → Disjoint (scope j) (scope k)) :
    (FinProb.pi P).expect (fun ω => ∏ j ∈ s, f j ω) =
      ∏ j ∈ s, (FinProb.pi P).expect (f j) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [FinProb.expect, (FinProb.pi P).sum_eq_one]
  | @insert j s hj ih =>
      let otherScope := s.biUnion scope
      have hOther : FinProb.DependsOn (fun ω => ∏ k ∈ s, f k ω) otherScope := by
        intro ω ω' hagree
        apply Finset.prod_congr rfl
        intro k hk
        apply hf k
        intro i hi
        exact hagree i (Finset.mem_biUnion.mpr ⟨k, hk, hi⟩)
      have hSeparate : Disjoint (scope j) otherScope := by
        rw [Finset.disjoint_left]
        intro i hi hrest
        rcases Finset.mem_biUnion.mp hrest with ⟨k, hk, hik⟩
        have hjk : j ≠ k := by
          intro heq
          subst k
          exact hj hk
        exact (Finset.disjoint_left.mp
          (hdisj j (Finset.mem_insert_self j s) k (Finset.mem_insert_of_mem hk) hjk)) hi hik
      have hdisjS : ∀ k ∈ s, ∀ l ∈ s, k ≠ l → Disjoint (scope k) (scope l) := by
        intro k hk l hl hkl
        exact hdisj k (Finset.mem_insert_of_mem hk) l (Finset.mem_insert_of_mem hl) hkl
      calc
        (FinProb.pi P).expect (fun ω => ∏ k ∈ insert j s, f k ω) =
            (FinProb.pi P).expect (fun ω => f j ω * ∏ k ∈ s, f k ω) := by
          congr 1
          funext ω
          rw [Finset.prod_insert hj]
        _ = (FinProb.pi P).expect (f j) *
              (FinProb.pi P).expect (fun ω => ∏ k ∈ s, f k ω) :=
          FinProb.pi_expect_mul_of_disjoint P (f j) (fun ω => ∏ k ∈ s, f k ω)
            (scope j) otherScope (hf j) hOther hSeparate
        _ = ∏ k ∈ insert j s, (FinProb.pi P).expect (f k) := by
          rw [ih hdisjS]
          rw [Finset.prod_insert hj]

end HypercubeRamsey.Lane_q_s10_c
