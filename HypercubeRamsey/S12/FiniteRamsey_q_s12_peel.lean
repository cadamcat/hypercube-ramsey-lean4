import Mathlib

namespace HypercubeRamsey.S12

open scoped BigOperators

def RamseyClique {α : Type*} (R : α → α → Prop) (s : ℕ) (C : Finset α) : Prop :=
  C.card = s ∧ ∀ x ∈ C, ∀ y ∈ C, x ≠ y → R x y

def RamseyIndependent {α : Type*} (R : α → α → Prop) (t : ℕ) (C : Finset α) : Prop :=
  C.card = t ∧ ∀ x ∈ C, ∀ y ∈ C, x ≠ y → ¬ R x y

/-- Finite Ramsey bound with the elementary binomial estimate. -/
theorem finite_ramsey_exists {α : Type*} [DecidableEq α]
    (R : α → α → Prop) [DecidableRel R]
    (hSymm : ∀ x y, R x y → R y x) :
    ∀ s t : ℕ, 0 < s → 0 < t → ∀ V : Finset α,
      Nat.choose (s + t - 2) (s - 1) ≤ V.card →
        (∃ C ⊆ V, RamseyClique R s C) ∨
        (∃ C ⊆ V, RamseyIndependent R t C) := by
  classical
  intro s t hs ht V hcard
  induction hsum : s + t using Nat.strong_induction_on generalizing s t V with
  | h n ih =>
      by_cases hs1 : s = 1
      · subst s
        have hVpos : 0 < V.card := by
          have hcard1 : 1 ≤ V.card := by simpa [Nat.choose_zero_right] using hcard
          omega
        obtain ⟨v, hv⟩ := Finset.card_pos.mp hVpos
        left
        refine ⟨{v}, ?_, ?_⟩
        · intro x hx
          simp only [Finset.mem_singleton] at hx
          subst x
          exact hv
        · constructor
          · simp
          · intro x hx y hy hxy
            simp only [Finset.mem_singleton] at hx hy
            subst x
            subst y
            exact False.elim (hxy rfl)
      · by_cases ht1 : t = 1
        · subst t
          have hVpos : 0 < V.card := by
            have hn : s + 1 - 2 = s - 1 := by omega
            have hcard1 : 1 ≤ V.card := by
              rw [hn] at hcard
              simpa [Nat.choose_self] using hcard
            omega
          obtain ⟨v, hv⟩ := Finset.card_pos.mp hVpos
          right
          refine ⟨{v}, ?_, ?_⟩
          · intro x hx
            simp only [Finset.mem_singleton] at hx
            subst x
            exact hv
          · constructor
            · simp
            · intro x hx y hy hxy
              simp only [Finset.mem_singleton] at hx hy
              subst x
              subst y
              exact False.elim (hxy rfl)
        · have hs2 : 2 ≤ s := by omega
          have ht2 : 2 ≤ t := by omega
          have hVpos : 0 < V.card := by
            have hchoosePos : 0 < Nat.choose (s + t - 2) (s - 1) :=
              Nat.choose_pos (by omega)
            exact lt_of_lt_of_le hchoosePos hcard
          obtain ⟨v, hv⟩ := Finset.card_pos.mp hVpos
          let V' := V.erase v
          let A := V'.filter fun y => R v y
          let B := V'.filter fun y => ¬ R v y
          have hvnotV' : v ∉ V' := by simp [V']
          have hAcard : A.card + B.card = V.card - 1 := by
            calc
              A.card + B.card = V'.card := by
                simp [A, B, V', Finset.card_filter_add_card_filter_not]
              _ = V.card - 1 := Finset.card_erase_of_mem hv
          have hPascal :
              Nat.choose (s + t - 2) (s - 1) =
                Nat.choose (s + t - 3) (s - 2) +
                  Nat.choose (s + t - 3) (s - 1) := by
            have hn : s + t - 2 = (s + t - 3) + 1 := by omega
            have hk : s - 1 = (s - 2) + 1 := by omega
            rw [hn, hk, Nat.choose_succ_succ']
          have hAorB :
              Nat.choose (s + t - 3) (s - 2) ≤ A.card ∨
                Nat.choose (s + t - 3) (s - 1) ≤ B.card := by
            by_contra h
            have hA : A.card < Nat.choose (s + t - 3) (s - 2) := by omega
            have hB : B.card < Nat.choose (s + t - 3) (s - 1) := by omega
            omega
          rcases hAorB with hA | hB
          · have hArec : Nat.choose ((s - 1) + t - 2) ((s - 1) - 1) ≤ A.card := by
              have hn : (s - 1) + t - 2 = s + t - 3 := by omega
              have hk : (s - 1) - 1 = s - 2 := by omega
              rw [hn, hk]
              exact hA
            have hrec := ih (s - 1 + t) (by omega) (s - 1) t (by omega) ht A hArec rfl
            rcases hrec with ⟨C, hCsub, hCclique⟩ | ⟨C, hCsub, hCind⟩
            · left
              refine ⟨insert v C, ?_, ?_⟩
              · intro x hx
                rcases Finset.mem_insert.mp hx with hxv | hxC
                · subst x
                  exact hv
                · exact Finset.erase_subset _ _ (Finset.mem_filter.mp (hCsub hxC)).1
              · constructor
                · rw [Finset.card_insert_of_notMem]
                  · have hCcard : C.card = s - 1 := hCclique.1
                    omega
                  · intro hvC
                    have hvA : v ∈ A := hCsub hvC
                    exact hvnotV' (Finset.mem_filter.mp hvA).1
                · intro x hx y hy hxy
                  rcases Finset.mem_insert.mp hx with hxv | hxC
                  · subst x
                    rcases Finset.mem_insert.mp hy with hyv | hyC
                    · subst y
                      exact False.elim (hxy rfl)
                    · have hyA : y ∈ A := hCsub hyC
                      exact (Finset.mem_filter.mp hyA).2
                  · rcases Finset.mem_insert.mp hy with hyv | hyC
                    · subst y
                      have hxA : x ∈ A := hCsub hxC
                      exact hSymm v x ((Finset.mem_filter.mp hxA).2)
                    · exact hCclique.2 x hxC y hyC hxy
            · right
              exact ⟨C, fun x hx => Finset.erase_subset _ _
                (Finset.mem_filter.mp (hCsub hx)).1, hCind⟩
          · have hBrec : Nat.choose (s + (t - 1) - 2) (s - 1) ≤ B.card := by
              have hn : s + (t - 1) - 2 = s + t - 3 := by omega
              rw [hn]
              exact hB
            have hrec := ih (s + (t - 1)) (by omega) s (t - 1) hs (by omega) B hBrec rfl
            rcases hrec with ⟨C, hCsub, hCclique⟩ | ⟨C, hCsub, hCind⟩
            · left
              exact ⟨C, fun x hx => Finset.erase_subset _ _
                (Finset.mem_filter.mp (hCsub hx)).1, hCclique⟩
            · right
              refine ⟨insert v C, ?_, ?_⟩
              · intro x hx
                rcases Finset.mem_insert.mp hx with hxv | hxC
                · subst x
                  exact hv
                · exact Finset.erase_subset _ _ (Finset.mem_filter.mp (hCsub hxC)).1
              · constructor
                · rw [Finset.card_insert_of_notMem]
                  · have hCcard : C.card = t - 1 := hCind.1
                    omega
                  · intro hvC
                    have hvB : v ∈ B := hCsub hvC
                    exact hvnotV' (Finset.mem_filter.mp hvB).1
                · intro x hx y hy hxy
                  rcases Finset.mem_insert.mp hx with hxv | hxC
                  · subst x
                    rcases Finset.mem_insert.mp hy with hyv | hyC
                    · subst y
                      exact False.elim (hxy rfl)
                    · have hyB : y ∈ B := hCsub hyC
                      exact (Finset.mem_filter.mp hyB).2
                  · rcases Finset.mem_insert.mp hy with hyv | hyC
                    · subst y
                      have hxB : x ∈ B := hCsub hxC
                      have hnot : ¬ R v x := (Finset.mem_filter.mp hxB).2
                      exact fun hRxv => hnot (hSymm x v hRxv)
                    · exact hCind.2 x hxC y hyC hxy

end HypercubeRamsey.S12
