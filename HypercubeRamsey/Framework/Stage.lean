import HypercubeRamsey.Framework.Embedding

/-!
# Stages: a bad sequence with retained sides

Subsequences, orientation swap, label removals of size `o(N)`, and the refinement relation between stages.
-/

namespace HypercubeRamsey

open OAI.HypercubeRamsey Filter

/-- Orientation swap of a bad sequence. -/
def BadSeq.swap (S : BadSeq) : BadSeq where
  n := S.n
  N := S.N
  E k := transposeRel (S.E k)
  n_tendsto := S.n_tendsto
  ratio_tendsto := S.ratio_tendsto
  N_pos := S.N_pos
  N_le := S.N_le
  no_cube k c h := S.no_cube k c (copy_transpose (S.E k) c h)

/-- A stage: a bad sequence with retained sides; all but `o(N)` labels are retained. Normalizations keep
using the original `N`. -/
structure Stage where
  S : BadSeq
  X : ∀ k, Finset (Fin (S.N k))
  Y : ∀ k, Finset (Fin (S.N k))
  small : Tendsto (fun k => (((X k)ᶜ.card + (Y k)ᶜ.card : ℕ) : ℝ) / S.N k) atTop (nhds 0)

def Stage.ofBadSeq (S : BadSeq) : Stage where
  S := S
  X _ := Finset.univ
  Y _ := Finset.univ
  small := by simp

def Stage.sub (T : Stage) (φ : ℕ → ℕ) (hφ : StrictMono φ) : Stage where
  S := T.S.comp φ hφ
  X k := T.X (φ k)
  Y k := T.Y (φ k)
  small := T.small.comp hφ.tendsto_atTop

def Stage.swap (T : Stage) : Stage where
  S := T.S.swap
  X := T.Y
  Y := T.X
  small := by
    refine T.small.congr (fun k => ?_)
    change ((((T.X k)ᶜ.card + (T.Y k)ᶜ.card : ℕ) : ℝ)) / T.S.N k =
      ((((T.Y k)ᶜ.card + (T.X k)ᶜ.card : ℕ) : ℝ)) / T.S.N k
    rw [Nat.add_comm]

/-- Refinement: subsequences and further `o(N)` removals. -/
inductive Stage.Refines : Stage → Stage → Prop
  | refl (T : Stage) : Stage.Refines T T
  | sub (T : Stage) (φ : ℕ → ℕ) (hφ : StrictMono φ) : Stage.Refines (T.sub φ hφ) T
  | remove (T : Stage) (X' Y' : ∀ k, Finset (Fin (T.S.N k)))
      (hX : ∀ k, X' k ⊆ T.X k) (hY : ∀ k, Y' k ⊆ T.Y k)
      (hsmall : Tendsto (fun k => (((X' k)ᶜ.card + (Y' k)ᶜ.card : ℕ) : ℝ) / T.S.N k)
        atTop (nhds 0)) :
      Stage.Refines ⟨T.S, X', Y', hsmall⟩ T
  | trans {A B C : Stage} : Stage.Refines A B → Stage.Refines B C → Stage.Refines A C

theorem Stage.Refines.swap {A B : Stage} (h : A.Refines B) : A.swap.Refines B.swap := sorry

/-- Host-size regime at one index: `C₀ 2^n ≤ N ≤ n 2^n`. -/
def LargeHost (C₀ : ℝ) (n N : ℕ) : Prop := C₀ * 2 ^ n ≤ (N : ℝ) ∧ N ≤ n * 2 ^ n

theorem BadSeq.eventually_large (S : BadSeq) (C₀ : ℝ) (n₀ : ℕ) :
    ∀ᶠ k in atTop, n₀ ≤ S.n k ∧ LargeHost C₀ (S.n k) (S.N k) := sorry

end HypercubeRamsey
