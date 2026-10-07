import HypercubeRamsey.Framework.Stage
import HypercubeRamsey.Framework.Law

/-!
# Patch properties, availability and eventual absence (Definition 3.1)
-/

namespace HypercubeRamsey

open Filter

/-- A patch property: at dimension `n`, side size `N` and colouring `E`, the support pairs carrying a witness. -/
def PatchProp := ∀ (n N : ℕ), (Fin N → Fin N → Prop) → Set (Finset (Fin N) × Finset (Fin N))

/-- A property of law pairs. -/
def LawProp := ∀ (n N : ℕ), (Fin N → Fin N → Prop) → Set (Law N × Law N)

/-- A law-pair property as a patch property: some witness pair supported in the support pair. -/
def LawProp.toPatchProp (P : LawProp) : PatchProp := fun n N E =>
  {AB | ∃ p ∈ P n N E, p.1.SupportedIn AB.1 ∧ p.2.SupportedIn AB.2}

def PatchProp.union {ι : Type} (P : ι → PatchProp) : PatchProp := fun n N E =>
  {AB | ∃ i, AB ∈ P i n N E}

/-- Availability along a stage (Definition 3.1). -/
def Available (T : Stage) (P : PatchProp) : Prop :=
  ∃ κ > (0 : ℝ), ∀ᶠ k in atTop, ∀ RX RY : Finset (Fin (T.S.N k)),
    (RX.card : ℝ) ≤ κ * T.S.N k → (RY.card : ℝ) ≤ κ * T.S.N k →
    ∃ A B, (A, B) ∈ P (T.S.n k) (T.S.N k) (T.S.E k) ∧ A ⊆ T.X k \ RX ∧ B ⊆ T.Y k \ RY

/-- Eventual absence. -/
def EventuallyAbsent (T : Stage) (P : PatchProp) : Prop :=
  ∀ᶠ k in atTop, ∀ A B, (A, B) ∈ P (T.S.n k) (T.S.N k) (T.S.E k) → ¬ (A ⊆ T.X k ∧ B ⊆ T.Y k)

end HypercubeRamsey
