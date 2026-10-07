import HypercubeRamsey.S07.Support
import HypercubeRamsey.S07.GridGeometry
import HypercubeRamsey.S07.CellFilters
import HypercubeRamsey.Framework.OneShot

/-!
# Lemma 7.1: small-grid purity exclusion

The internal probability nodes are stated in `GridNodes.lean`. The exported one-shot theorem uses the aggregate
Hall-data bridge below and then applies the framework's `cubeAt_of_rows` theorem.
-/

namespace HypercubeRamsey.S07

open Classical
open OAI.HypercubeRamsey

/-- The one-dimension hypothesis (7.1), with `c = d / 80`. -/
def Eq71At (D₀ d : ℝ) (n N : ℕ) (E : Fin N → Fin N → Prop)
    (X Y : Finset (Fin N)) : Prop :=
  ∀ σ τ : Law N, σ.SupportedIn X → τ.SupportedIn Y →
    σ.CapLE ((n : ℝ) ^ D₀) → τ.WidthLE ((n : ℝ) ^ ((1 : ℝ) / 4)) →
    ∀ col : Colour, (n : ℝ) ^ (-(d / 80)) < dens E col σ τ

/-- The conclusion of the probabilistic construction in L7.1i, before applying Hall's embedding theorem. -/
def GridHallData {n N : ℕ} (E : Fin N → Fin N → Prop) (G : Colour) : Prop :=
  ∃ (fB : {v : CubeVertex n // ¬ IsEvenRole v} → Fin N)
    (p : {v : CubeVertex n // IsEvenRole v} → Fin N → ℝ),
      Function.Injective fB ∧
      (∀ a x, 0 ≤ p a x) ∧
      (∀ a, ∑ x, p a x = 1) ∧
      (∀ a x, p a x ≠ 0 → ∀ b : {v : CubeVertex n // ¬ IsEvenRole v},
        (cube n).Adj a.1 b.1 → Hits E G x (fB b)) ∧
      (∀ x, ∑ a, p a x ≤ 1)

/-- Aggregate bridge from the one-shot hypotheses to Hall data. The statement-only chain in `GridNodes.lean`
is not yet assembled into this bridge. -/
theorem grid_hall_data_from_input
    (D₀ d p₀ κ : ℝ) (hD₀ : 0 < D₀) (hD₀' : D₀ < 1 / 10)
    (hd : 0 < d) (hd' : d < D₀ / 1000) (hp₀ : 0 < p₀) (hκ : 0 < κ) :
    ∃ n₀ : ℕ, ∃ C₀ : ℝ, ∀ n N : ℕ, ∀ E : Fin N → Fin N → Prop,
      ∀ X Y : Finset (Fin N), ∀ G : Colour,
        LargeAt n₀ C₀ n N → Eq71At D₀ d n N E X Y →
        AvailableAt κ (PGridPure G d p₀).toPatch n N E X Y → GridHallData (n := n) E G := by
  sorry

/-- L7.1 (07:41–391), the one-shot small-grid purity exclusion. -/
theorem small_grid_purity
    (D₀ d p₀ κ : ℝ) (hD₀ : 0 < D₀) (hD₀' : D₀ < 1 / 10)
    (hd : 0 < d) (hd' : d < D₀ / 1000) (hp₀ : 0 < p₀) (hκ : 0 < κ) :
    ∃ n₀ : ℕ, ∃ C₀ : ℝ, ∀ n N : ℕ, ∀ E : Fin N → Fin N → Prop,
      ∀ X Y : Finset (Fin N), ∀ G : Colour,
        LargeAt n₀ C₀ n N → Eq71At D₀ d n N E X Y →
        AvailableAt κ (PGridPure G d p₀).toPatch n N E X Y → CubeAt n N E := by
  obtain ⟨n₀, C₀, hnode⟩ := by
    exact grid_hall_data_from_input D₀ d p₀ κ hD₀ hD₀' hd hd' hp₀ hκ
  refine ⟨n₀, C₀, ?_⟩
  intro n N E X Y G hlarge h71 havail
  obtain ⟨fB, p, hinj, hp0, hp1, hsupp, hload⟩ :=
    hnode n N E X Y G hlarge h71 havail
  exact cubeAt_of_rows E G fB hinj p hp0 hp1 hsupp hload

end HypercubeRamsey.S07
