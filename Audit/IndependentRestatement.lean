import HypercubeRamsey.Bridge
import Mathlib.InformationTheory.Hamming

/-!
# Independent restatement of the target (statement-fidelity probe)

`Indep` restates the paper's Theorem 1.1 without any Formal Conjectures or OpenAI definition:
vertices of `Q_n` are functions `Fin n → Bool`, adjacency is Mathlib's Hamming distance `1`,
a red-blue colouring of `K_M` is a symmetric `Fin M → Fin M → Bool` (diagonal values unused), and
a monochromatic, not necessarily induced, copy of `Q_n` is an injective map whose Hamming-1 pairs
all receive one colour. "R(Q_n) ≤ C 2^n" is stated as "some M ≤ C 2^n has the Ramsey property",
which avoids `sInf` altogether.

`fc_iff_indep` proves the Formal Conjectures statement (as written in `Challenge.lean`, over the
proof's verbatim copy of the definitions) equivalent to `Indep`. The direction `→` uses only that the
Ramsey set is nonempty, obtained from the kernel-checked lower bound `2^n ≤ R(Q_n)`.
-/

namespace FidelityProbe

open SimpleGraph

/-- Paper Theorem 1.1 in elementary vocabulary. -/
def Indep : Prop :=
  ∃ C : ℝ, 0 < C ∧ ∀ n : ℕ, ∃ M : ℕ, (M : ℝ) ≤ C * 2 ^ n ∧
    ∀ c : Fin M → Fin M → Bool, (∀ x y, c x y = c y x) →
      ∃ b : Bool, ∃ f : (Fin n → Bool) → Fin M, Function.Injective f ∧
        ∀ u v : Fin n → Bool, hammingDist u v = 1 → c (f u) (f v) = b

/-- The target statement, typed exactly as in `Challenge.lean`. -/
def FCStatement : Prop :=
  ∃ C > (0 : ℝ), ∀ n : ℕ,
    (diagonalGraphRamsey (hypercube n) : ℝ) ≤ C * 2 ^ n

theorem hypercube_adj_iff_hammingDist {n : ℕ} (u v : Fin n → Bool) :
    (hypercube n).Adj u v ↔ hammingDist u v = 1 := Iff.rfl

/-- `R(Q_n)` as defined by Formal Conjectures belongs to its own Ramsey set (the set is nonempty). -/
theorem mem_ramseySet (n : ℕ) :
    diagonalGraphRamsey (hypercube n) ∈
      {m : ℕ | ∀ G : SimpleGraph (Fin m), (hypercube n).IsContained G ∨ (hypercube n).IsContained Gᶜ} := by
  have hlow : 2 ^ n ≤ diagonalGraphRamsey (hypercube n) := by
    rw [HypercubeRamsey.diagonalGraphRamsey_hypercube]
    exact (OAI.HypercubeRamsey.elementary_cube_bounds n).1
  apply Nat.sInf_mem
  by_contra hne
  rw [Set.not_nonempty_iff_eq_empty] at hne
  have h0 : diagonalGraphRamsey (hypercube n) = 0 := by
    unfold diagonalGraphRamsey graphRamsey
    rw [hne, Nat.sInf_empty]
  have : 0 < 2 ^ n := Nat.two_pow_pos n
  omega

theorem fc_to_indep (h : FCStatement) : Indep := by
  obtain ⟨C, hC, hb⟩ := h
  refine ⟨C, hC, fun n => ⟨diagonalGraphRamsey (hypercube n), hb n, ?_⟩⟩
  intro c hc
  let G : SimpleGraph (Fin (diagonalGraphRamsey (hypercube n))) :=
    { Adj := fun x y => x ≠ y ∧ c x y = true
      symm := ⟨fun x y h => ⟨h.1.symm, (hc y x).trans h.2⟩⟩
      loopless := ⟨fun x h => h.1 rfl⟩ }
  rcases mem_ramseySet n G with hG | hG
  · obtain ⟨f⟩ := hG
    refine ⟨true, f, f.injective, fun u v huv => ?_⟩
    exact (f.toHom.map_adj ((hypercube_adj_iff_hammingDist u v).2 huv)).2
  · obtain ⟨f⟩ := hG
    refine ⟨false, f, f.injective, fun u v huv => ?_⟩
    have h1 := f.toHom.map_adj ((hypercube_adj_iff_hammingDist u v).2 huv)
    rw [compl_adj] at h1
    have h2 : ¬ (c (f u) (f v) = true) := fun h => h1.2 ⟨h1.1, h⟩
    simpa using h2

theorem indep_to_fc (h : Indep) : FCStatement := by
  classical
  obtain ⟨C, hC, hb⟩ := h
  refine ⟨C, hC, fun n => ?_⟩
  obtain ⟨M, hM, hprop⟩ := hb n
  have hmem : M ∈
      {m : ℕ | ∀ G : SimpleGraph (Fin m), (hypercube n).IsContained G ∨
        (hypercube n).IsContained Gᶜ} := by
    intro G
    obtain ⟨b, f, hf, hmono⟩ :=
      hprop (fun x y => decide (G.Adj x y)) (fun x y => by simp [G.adj_comm])
    cases b
    · right
      refine ⟨⟨⟨f, fun {u v} huv => ?_⟩, hf⟩⟩
      have h1 := hmono u v ((hypercube_adj_iff_hammingDist u v).1 huv)
      rw [compl_adj]
      exact ⟨hf.ne huv.ne, by simpa using h1⟩
    · left
      refine ⟨⟨⟨f, fun {u v} huv => ?_⟩, hf⟩⟩
      have h1 := hmono u v ((hypercube_adj_iff_hammingDist u v).1 huv)
      simpa using h1
  have hle : diagonalGraphRamsey (hypercube n) ≤ M := Nat.sInf_le hmem
  calc (diagonalGraphRamsey (hypercube n) : ℝ) ≤ M := by exact_mod_cast hle
    _ ≤ C * 2 ^ n := hM

theorem fc_iff_indep : FCStatement ↔ Indep := ⟨fc_to_indep, indep_to_fc⟩

/-- Unfolding `FCStatement` gives back the statement exactly as `Challenge.lean` types it. -/
example : FCStatement = (∃ C > (0 : ℝ), ∀ n : ℕ,
    (diagonalGraphRamsey (hypercube n) : ℝ) ≤ C * 2 ^ n) := rfl

/-- Boundary witnesses distinguishing readings of the definitions. -/
-- `Q_0` is one vertex, so `R(Q_0) = 1` (not `0`): the `sInf ∅ = 0` and `M = 0` cases do not arise.
example : diagonalGraphRamsey (hypercube 0) = 1 := by
  rw [HypercubeRamsey.diagonalGraphRamsey_hypercube]; exact OAI.HypercubeRamsey.ramseyNumber_cube_zero
-- `0` is not in the Ramsey set for any `n` (no map from a nonempty vertex type into `Fin 0`).
example (n : ℕ) : ¬ ∀ G : SimpleGraph (Fin 0), (hypercube n).IsContained G ∨
    (hypercube n).IsContained Gᶜ := by
  intro h
  rcases h ⊥ with hG | hG <;> obtain ⟨f⟩ := hG <;> exact (f (fun _ => false)).elim0
-- Non-induced: a copy need not preserve non-adjacency, so the edgeless graph on four vertices is
-- contained in `Q_2` (an induced copy would not exist).
example : (⊥ : SimpleGraph (Fin 4)).IsContained (hypercube 2) := by
  refine ⟨⟨⟨fun i => ![decide (i.val / 2 = 1), decide (i.val % 2 = 1)], fun {a b} h => absurd h (by simp)⟩, ?_⟩⟩
  decide
-- Direction of `IsContained`: `G.IsContained C` maps `G` into `C`. `Q_1 ⊑ K_2` holds, while `K_3 ⊑ Q_1`
-- fails (`Q_1` has two vertices); with the direction reversed the second would hold.
example : (hypercube 1).IsContained (⊤ : SimpleGraph (Fin 2)) := by
  refine ⟨⟨⟨fun u => if u 0 then 1 else 0, fun {u v} h => ?_⟩, ?_⟩⟩
  · rw [hypercube_adj] at h; rw [top_adj]; revert h; revert u v; decide
  · decide
example : ¬ (⊤ : SimpleGraph (Fin 3)).IsContained (hypercube 1) := by
  rintro ⟨f⟩
  have := Fintype.card_le_of_injective f f.injective
  simp at this

end FidelityProbe

#print axioms FidelityProbe.fc_iff_indep
#print axioms FidelityProbe.mem_ramseySet
