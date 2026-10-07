import HypercubeRamsey.S05.Posterior

/-!
# L5.1e: finite observation records

These record codes keep array IDs, array types, exceptional neighboring states, and the low mask separate.
Actual IDs range over the polynomial position universe; history tests use canonical IDs in `Fin T`.
-/

namespace HypercubeRamsey

noncomputable section

/-- Actual low-state record: IDs/types, exceptional chunk states, and a selected high-pool mask. -/
structure LowActualRecord5 (n T j m kstar : ℕ) where
  ids : Fin T → Fin (n ^ 3)
  arrayTypes : Fin T → Fin (n ^ 3)
  exceptionalStates : Fin (j + 1) → Fin m
  mask : Fin kstar → Bool
  deriving Fintype

/-- Canonical low-state record after IDs are renamed into `[T]`. -/
structure LowAbstractRecord5 (T j m kstar : ℕ) where
  ids : Fin T → Fin T
  arrayTypes : Fin T → Fin T
  exceptionalStates : Fin (j + 1) → Fin m
  mask : Fin kstar → Bool
  deriving Fintype

/-- Actual high-state record. Optional low-key combinations are recorded; extracted subset indices are
computed from the recorded full pools and are not independently enumerated. -/
structure HighActualRecord5 (n T J : ℕ) where
  ids : Fin T → Fin (n ^ 3)
  arrayTypes : Fin T → Fin (n ^ 3)
  optionalKeys : Fin (J + 1) → Fin T
  deriving Fintype

/-- Canonical high-state record with IDs renamed into `[T]`. -/
structure HighAbstractRecord5 (T J m : ℕ) where
  ids : Fin T → Fin T
  arrayTypes : Fin T → Fin T
  optionalKeys : Fin (J + 1) → Fin m
  deriving Fintype

/-- L5.1e: actual and abstract record counts have logarithms bounded by the Section 5 enumeration costs.

The low mask contributes `O(k_*)`; at high states the possible optional-key data is counted without
enumerating all subsets of a full pool. -/
theorem L5_1e_record_count (n T j J m kstar : ℕ)
    (hn : 2 ≤ n) (hT : 1 ≤ T) (hm : 1 ≤ m) :
    Real.log (Fintype.card (LowActualRecord5 n T j m kstar) : ℝ) ≤
        6 * T * Real.log n + (j + 1) * Real.log m + kstar * Real.log 2 ∧
    Real.log (Fintype.card (LowAbstractRecord5 T j m kstar) : ℝ) ≤
        2 * T * Real.log T + (j + 1) * Real.log m + kstar * Real.log 2 ∧
    Real.log (Fintype.card (HighActualRecord5 n T J) : ℝ) ≤
        6 * T * Real.log n + (J + 1) * Real.log T ∧
    Real.log (Fintype.card (HighAbstractRecord5 T J m) : ℝ) ≤
        2 * T * Real.log T + (J + 1) * Real.log m := by
  sorry

end
end HypercubeRamsey
