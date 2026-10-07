import OAI.Combinatorics.Ramsey.Hypercube

/-!
# Counterexample sequences

Colours, the colour relation `Hits`, and the paper's counterexample sequence (Lemma 2.1) as a structure.
-/

namespace HypercubeRamsey

open OAI.HypercubeRamsey

/-- A colour: `true` is red (the relation `E`), `false` is blue (its negation). -/
abbrev Colour := Bool

/-- `Hits E c x y`: the first-side label `x` and the second-side label `y` are joined in colour `c`. -/
def Hits {N : ℕ} (E : Fin N → Fin N → Prop) (c : Colour) (x y : Fin N) : Prop :=
  if c then E x y else ¬ E x y

/-- The paper's counterexample sequence (Lemma 2.1). -/
structure BadSeq where
  n : ℕ → ℕ
  N : ℕ → ℕ
  E : ∀ k, Fin (N k) → Fin (N k) → Prop
  n_tendsto : Filter.Tendsto n Filter.atTop Filter.atTop
  ratio_tendsto : Filter.Tendsto (fun k => (N k : ℝ) / 2 ^ n k) Filter.atTop Filter.atTop
  N_pos : ∀ k, 0 < N k
  N_le : ∀ k, N k ≤ n k * 2 ^ n k
  no_cube : ∀ k (c : Colour), ¬ Nonempty ((cube (n k)).Copy (crossGraph (Hits (E k) c)))

/-- A subsequence of a bad sequence. -/
def BadSeq.comp (S : BadSeq) (φ : ℕ → ℕ) (hφ : StrictMono φ) : BadSeq where
  n k := S.n (φ k)
  N k := S.N (φ k)
  E k := S.E (φ k)
  n_tendsto := S.n_tendsto.comp hφ.tendsto_atTop
  ratio_tendsto := S.ratio_tendsto.comp hφ.tendsto_atTop
  N_pos _ := S.N_pos _
  N_le _ := S.N_le _
  no_cube _ c := S.no_cube _ c

/-- If the hypercube Ramsey number is not linear, a bad sequence exists. -/
theorem badSeq_of_not_linear
    (hnot : ¬ ∃ C : ℝ, 0 < C ∧ ∀ n : ℕ, (ramseyNumber (cube n) : ℝ) ≤ C * (2 : ℝ) ^ n) :
    Nonempty BadSeq := sorry

end HypercubeRamsey
