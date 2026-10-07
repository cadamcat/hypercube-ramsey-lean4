import HypercubeRamsey.Framework.Patch

/-!
# Lemma 3.2: stabilization and finite menus

Source: `sections/03-…tex`, Lemma 3.2 (`lem:stabilization`) and its proof.
-/

namespace HypercubeRamsey

open Filter

/-- Lemma 3.2, first clause: a countable list of patch properties can be stabilized. -/
theorem stabilization (T : Stage) (P : ℕ → PatchProp) :
    ∃ T', T'.Refines T ∧ ∀ j, Available T' (P j) ∨ EventuallyAbsent T' (P j) := sorry

/-- Lemma 3.2, persistence of availability (with a smaller tolerance). -/
theorem Available.refine {T T' : Stage} {P : PatchProp} (h : Available T P)
    (hr : T'.Refines T) : Available T' P := sorry

/-- Absence persists under every refinement. -/
theorem EventuallyAbsent.refine {T T' : Stage} {P : PatchProp} (h : EventuallyAbsent T P)
    (hr : T'.Refines T) : EventuallyAbsent T' P := sorry

theorem Available.not_absent {T : Stage} {P : PatchProp} (h₁ : Available T P)
    (h₂ : EventuallyAbsent T P) : False := sorry

/-- Lemma 3.2, finite unions: an available finite union has an available member after refinement. -/
theorem Available.union_fin {T : Stage} {m : ℕ} {P : Fin m → PatchProp}
    (h : Available T (PatchProp.union P)) :
    ∃ T', T'.Refines T ∧ ∃ i, Available T' (P i) := sorry

/-- Lemma 3.2, finite menus: one witness per removal pair at each large index. -/
theorem Available.menu {T : Stage} {P : LawProp} (h : Available T P.toPatchProp) :
    ∃ κ > (0 : ℝ), ∀ᶠ k in atTop, ∃ w : Finset (Fin (T.S.N k)) × Finset (Fin (T.S.N k)) →
        Law (T.S.N k) × Law (T.S.N k),
      ∀ RX RY : Finset (Fin (T.S.N k)), (RX.card : ℝ) ≤ κ * T.S.N k → (RY.card : ℝ) ≤ κ * T.S.N k →
        w (RX, RY) ∈ P (T.S.n k) (T.S.N k) (T.S.E k) ∧
          (w (RX, RY)).1.SupportedIn (T.X k \ RX) ∧ (w (RX, RY)).2.SupportedIn (T.Y k \ RY) := sorry

end HypercubeRamsey
