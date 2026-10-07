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

/-- Transposed relation (orientation swap). -/
def transposeRel {N : ℕ} (E : Fin N → Fin N → Prop) : Fin N → Fin N → Prop := fun x y => E y x

theorem hits_transpose {N : ℕ} (E : Fin N → Fin N → Prop) (c : Colour) (x y : Fin N) :
    Hits (transposeRel E) c x y ↔ Hits E c y x := by
  cases c <;> simp [Hits, transposeRel]

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
    Nonempty BadSeq := by
  obtain ⟨d, N, E, hd, hratio, hpos, hbound, hno⟩ :=
    counterexample_sequence_of_not_linear hnot
  refine ⟨{
    n := d
    N := N
    E := E
    n_tendsto := hd
    ratio_tendsto := hratio
    N_pos := hpos
    N_le := hbound
    no_cube := ?_ }⟩
  intro k c
  cases c with
  | false =>
      change ¬ Nonempty ((cube (d k)).Copy
        (crossGraph (fun x y => ¬ E k x y)))
      exact (hno k).2
  | true =>
      change ¬ Nonempty ((cube (d k)).Copy (crossGraph (E k)))
      exact (hno k).1

end HypercubeRamsey
