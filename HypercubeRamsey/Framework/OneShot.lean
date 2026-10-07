import HypercubeRamsey.Framework.Disc

/-!
# Single-dimension statements and their bridge to stages

Blueprint part B's conventions (`research/blueprint/PART-B.md` §1.2, §6): every embedding lemma is stated at one
dimension `(n, N, E, X, Y)` in the large regime `LargeAt`, concluding `CubeAt`; `OneShot` lemmas turn such
statements into non-availability along a stage. One stabilization covers a fixed countable family of properties.
-/

namespace HypercubeRamsey

open OAI.HypercubeRamsey Filter

/-- Discrepancy at one dimension: every pair of laws supported in `X`, `Y` within the width budgets has both
colour densities within `err` of `1/2`. -/
def DiscOne {N : ℕ} (E : Fin N → Fin N → Prop) (X Y : Finset (Fin N)) (wX wY err : ℝ) : Prop :=
  ∀ μ ν : Law N, μ.SupportedIn X → ν.SupportedIn Y → μ.WidthLE wX → ν.WidthLE wY →
    ∀ c : Colour, |dens E c μ ν - 1 / 2| ≤ err

theorem discAt_iff_eventually_discOne (T : Stage) (wX wY err : ℝ → ℝ) :
    DiscAt T wX wY err ↔ ∀ᶠ k in atTop, DiscOne (T.S.E k) (T.X k) (T.Y k)
      (wX (T.S.n k)) (wY (T.S.n k)) (err (T.S.n k)) := sorry

/-- Availability at a single dimension with tolerance `κ`. -/
def AvailableAt (κ : ℝ) (P : PatchProp) (n N : ℕ) (E : Fin N → Fin N → Prop)
    (X Y : Finset (Fin N)) : Prop :=
  ∀ RX RY : Finset (Fin N), (RX.card : ℝ) ≤ κ * N → (RY.card : ℝ) ≤ κ * N →
    ∃ A B, (A, B) ∈ P n N E ∧ A ⊆ X \ RX ∧ B ⊆ Y \ RY

theorem available_iff_availableAt (T : Stage) (P : PatchProp) :
    Available T P ↔ ∃ κ > (0 : ℝ), ∀ᶠ k in atTop,
      AvailableAt κ P (T.S.n k) (T.S.N k) (T.S.E k) (T.X k) (T.Y k) := Iff.rfl

/-- A monochromatic cube at one dimension, in either colour. -/
def CubeAt (n N : ℕ) (E : Fin N → Fin N → Prop) : Prop :=
  ∃ c : Colour, Nonempty ((cube n).Copy (crossGraph (Hits E c)))

/-- The large regime of a one-shot statement. -/
def LargeAt (n₀ : ℕ) (C₀ : ℝ) (n N : ℕ) : Prop :=
  n₀ ≤ n ∧ C₀ * 2 ^ n ≤ (N : ℝ) ∧ N ≤ n * 2 ^ n

/-- A finite tag mixture of patch laws. -/
structure TagMix (N : ℕ) where
  ι : Type
  [fin : Fintype ι]
  Λ : ι → ℝ
  Λ_nonneg : ∀ i, 0 ≤ Λ i
  Λ_sum : ∑ i, Λ i = 1
  μ : ι → Law N
  ν : ι → Law N

attribute [instance] TagMix.fin

/-- Balance: both pointwise tag averages are at most `K / N`. -/
def TagMix.Balanced {N : ℕ} (M : TagMix N) (K : ℝ) : Prop :=
  (∀ x, (N : ℝ) * ∑ i, M.Λ i * (M.μ i).w x ≤ K) ∧ (∀ y, (N : ℝ) * ∑ i, M.Λ i * (M.ν i).w y ≤ K)

/-- Stabilization on a set of patch properties. -/
def StabilizedOn (T : Stage) (F : Set PatchProp) : Prop :=
  ∀ P ∈ F, Available T P ∨ EventuallyAbsent T P

/-- Pair-law property: a support pair carries a witness when two laws supported in it satisfy `Q`. -/
def PairProp := ∀ (n N : ℕ), (Fin N → Fin N → Prop) → Law N → Law N → Prop

def PairProp.toPatch (Q : PairProp) : PatchProp :=
  fun n N E => {AB | ∃ μ ν : Law N, μ.SupportedIn AB.1 ∧ ν.SupportedIn AB.2 ∧ Q n N E μ ν}

/-- A patch property read in the reversed orientation. -/
def PatchProp.swap (P : PatchProp) : PatchProp :=
  fun n N E => {AB | (AB.2, AB.1) ∈ P n N (transposeRel E)}

/-- Power and linear width budgets. -/
noncomputable def pw (x : ℝ) : ℝ → ℝ := fun n => n ^ x
def lw (α : ℝ) : ℝ → ℝ := fun n => α * n

/-- F-OneShot: a single-dimension embedding statement whose side conditions hold eventually along the stage
excludes availability. -/
theorem not_available_of_oneShot {T : Stage} {P : PatchProp} {κ : ℝ} (hκ : 0 < κ)
    (side : ∀ (n N : ℕ), (Fin N → Fin N → Prop) → Finset (Fin N) → Finset (Fin N) → Prop)
    (hside : ∀ᶠ k in atTop, side (T.S.n k) (T.S.N k) (T.S.E k) (T.X k) (T.Y k))
    (n₀ : ℕ) (C₀ : ℝ)
    (hshot : ∀ n N (E : Fin N → Fin N → Prop) (X Y : Finset (Fin N)), LargeAt n₀ C₀ n N →
      side n N E X Y → AvailableAt κ P n N E X Y → CubeAt n N E) :
    ¬ (∀ᶠ k in atTop, AvailableAt κ P (T.S.n k) (T.S.N k) (T.S.E k) (T.X k) (T.Y k)) := sorry

/-- F-OneShot, packaged for `Available`: the one-shot statement holds for every tolerance. -/
theorem not_available_of_oneShot' {T : Stage} {P : PatchProp}
    (side : ∀ (n N : ℕ), (Fin N → Fin N → Prop) → Finset (Fin N) → Finset (Fin N) → Prop)
    (hside : ∀ᶠ k in atTop, side (T.S.n k) (T.S.N k) (T.S.E k) (T.X k) (T.Y k))
    (hshot : ∀ κ > (0 : ℝ), ∃ n₀ C₀, ∀ n N (E : Fin N → Fin N → Prop) (X Y : Finset (Fin N)),
      LargeAt n₀ C₀ n N → side n N E X Y → AvailableAt κ P n N E X Y → CubeAt n N E) :
    ¬ Available T P := sorry

/-- F-UnionAvail. -/
theorem AvailableAt.union {κ : ℝ} {P Q : PatchProp} {n N : ℕ} {E : Fin N → Fin N → Prop}
    {X Y : Finset (Fin N)}
    (h : AvailableAt κ (fun n N E => P n N E ∪ Q n N E) n N E X Y) :
    AvailableAt (κ / 2) P n N E X Y ∨ AvailableAt (κ / 2) Q n N E X Y := sorry

/-- F-AvailMono. -/
theorem AvailableAt.mono {κ : ℝ} {P Q : PatchProp} {n N : ℕ} {E : Fin N → Fin N → Prop}
    {X Y : Finset (Fin N)} (hPQ : P n N E ⊆ Q n N E) (h : AvailableAt κ P n N E X Y) :
    AvailableAt κ Q n N E X Y := sorry

theorem Available.mono {T : Stage} {P Q : PatchProp} (hPQ : ∀ n N E, P n N E ⊆ Q n N E)
    (h : Available T P) : Available T Q := sorry

/-- F-SwapAvail. -/
theorem available_swap_iff (T : Stage) (P : PatchProp) :
    Available T P.swap ↔ Available T.swap P := sorry

theorem eventuallyAbsent_swap_iff (T : Stage) (P : PatchProp) :
    EventuallyAbsent T P.swap ↔ EventuallyAbsent T.swap P := sorry

/-- F-SwapStab. -/
theorem StabilizedOn.swap {T : Stage} {F : Set PatchProp} (h : StabilizedOn T F)
    (hF : ∀ P ∈ F, P.swap ∈ F) : StabilizedOn T.swap F := sorry

theorem StabilizedOn.refine {T T' : Stage} {F : Set PatchProp} (h : StabilizedOn T F)
    (hr : T'.Refines T) : StabilizedOn T' F := sorry

theorem StabilizedOn.subset {T : Stage} {F G : Set PatchProp} (h : StabilizedOn T G) (hFG : F ⊆ G) :
    StabilizedOn T F := sorry

/-- Master stabilization for a countable family. -/
theorem exists_stabilizedOn (T : Stage) (F : Set PatchProp) (hF : F.Countable) :
    ∃ T', T'.Refines T ∧ StabilizedOn T' F := sorry

/-- F-DensCompl and degree forms. -/
theorem dens_false {N : ℕ} (E : Fin N → Fin N → Prop) (μ ν : Law N) :
    dens E false μ ν = 1 - dens E true μ ν := sorry

theorem colDeg_transpose {N : ℕ} (E : Fin N → Fin N → Prop) (c : Colour) (μ : Law N) (x : Fin N) :
    colDeg (transposeRel E) c μ x = rowDeg E c x μ := sorry

/-- F-CubeSwap. -/
theorem CubeAt.of_transpose {n N : ℕ} {E : Fin N → Fin N → Prop} (h : CubeAt n N (transposeRel E)) :
    CubeAt n N E := sorry

/-- F-DiscMono at one dimension. -/
theorem DiscOne.mono {N : ℕ} {E : Fin N → Fin N → Prop} {X Y : Finset (Fin N)} {wX wY err wX' wY' err' : ℝ}
    (h : DiscOne E X Y wX wY err) (h₁ : wX' ≤ wX) (h₂ : wY' ≤ wY) (h₃ : err ≤ err') :
    DiscOne E X Y wX' wY' err' := sorry

/-- Swapping orientation at one dimension. -/
theorem DiscOne.transpose_iff {N : ℕ} (E : Fin N → Fin N → Prop) (X Y : Finset (Fin N)) (wX wY err : ℝ) :
    DiscOne (transposeRel E) Y X wY wX err ↔ DiscOne E X Y wX wY err := sorry

open Classical in
/-- F-HallEmbed: an injective odd map and even probability rows on common neighbourhoods with column sums at most
one give a cube (even roles on the first side). -/
theorem cubeAt_of_rows {n N : ℕ} (E : Fin N → Fin N → Prop) (c : Colour)
    (fB : {v : CubeVertex n // ¬ IsEvenRole v} → Fin N) (hB : Function.Injective fB)
    (p : {v : CubeVertex n // IsEvenRole v} → Fin N → ℝ)
    (hp0 : ∀ a x, 0 ≤ p a x) (hp1 : ∀ a, ∑ x, p a x = 1)
    (hsupp : ∀ a x, p a x ≠ 0 → ∀ b : {v : CubeVertex n // ¬ IsEvenRole v}, (cube n).Adj a.1 b.1 →
      Hits E c x (fB b))
    (hcol : ∀ x, ∑ a, p a x ≤ 1) : CubeAt n N E := sorry

end HypercubeRamsey
