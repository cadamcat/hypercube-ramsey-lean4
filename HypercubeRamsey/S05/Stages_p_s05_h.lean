import HypercubeRamsey.Framework.FinProbLemmas

namespace HypercubeRamsey

open Classical
open scoped BigOperators

/- The probability of a complement is one minus the probability of the event. -/
theorem FinProb.pr_compl5 {Ω : Type*} [Fintype Ω] (P : FinProb Ω) (A : Ω → Prop) :
    P.pr (fun ω => ¬ A ω) = 1 - P.pr A := by
  classical
  have hparts : P.pr (fun ω => ¬ A ω) + P.pr A = 1 := by
    unfold FinProb.pr
    calc
      _ = ∑ ω, P.w ω := by
        rw [← Finset.sum_add_distrib]
        apply Finset.sum_congr rfl
        intro ω hω
        by_cases hA : A ω <;> simp [hA]
      _ = 1 := P.sum_eq_one
  linarith [hparts]

/- A probability strictly below one leaves positive mass on the complement. -/
theorem FinProb.pr_compl_pos5 {Ω : Type*} [Fintype Ω] (P : FinProb Ω) (A : Ω → Prop)
    (hA : P.pr A < 1) : 0 < P.pr (fun ω => ¬ A ω) := by
  rw [FinProb.pr_compl5]
  linarith

/- Conditioning a finite law on an event removes the complementary event from its support. -/
theorem FinProb.condition_away5 {Ω : Type*} [Fintype Ω] (P : FinProb Ω) (A : Ω → Prop)
    (hA : P.pr A < 1) :
    ∃ Q : FinProb Ω, ∀ ω, Q.w ω ≠ 0 → ¬ A ω := by
  classical
  have hcompl : 0 < P.pr (fun ω => ¬ A ω) := FinProb.pr_compl_pos5 P A hA
  let Q : FinProb Ω := FinProb.cond P (fun ω => ¬ A ω) hcompl
  refine ⟨Q, ?_⟩
  intro ω hω hAω
  have hzero : Q.w ω = 0 := by
    simp [Q, FinProb.cond, hAω]
  exact hω hzero

/- Finite union bound for the alarm events indexed by a finite type. -/
theorem FinProb.pr_exists_le_sum5 {ι Ω : Type*} [Fintype ι] [Fintype Ω]
    (P : FinProb Ω) (E : ι → Ω → Prop) :
    P.pr (fun ω => ∃ i, E i ω) ≤ ∑ i, P.pr (E i) := by
  classical
  have hbound : ∀ s : Finset ι,
      P.pr (fun ω => ∃ i ∈ s, E i ω) ≤ ∑ i ∈ s, P.pr (E i) := by
    intro s
    induction s using Finset.induction_on with
    | empty => simp [FinProb.pr]
    | @insert a s ha ih =>
      have hevent :
          (fun ω => ∃ i ∈ insert a s, E i ω) =
            (fun ω => E a ω ∨ ∃ i ∈ s, E i ω) := by
        funext ω
        apply propext
        simp [Finset.mem_insert]
      rw [hevent]
      calc
        P.pr (fun ω => E a ω ∨ ∃ i ∈ s, E i ω) ≤
            P.pr (E a) + P.pr (fun ω => ∃ i ∈ s, E i ω) :=
          FinProb.pr_union P (E a) (fun ω => ∃ i ∈ s, E i ω)
        _ ≤ P.pr (E a) + ∑ i ∈ s, P.pr (E i) := by linarith
        _ = ∑ i ∈ insert a s, P.pr (E i) := by
          simp [Finset.sum_insert, ha]
  simpa using hbound Finset.univ

end HypercubeRamsey
