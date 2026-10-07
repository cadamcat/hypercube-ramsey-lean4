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
  classical
  let eLA : LowActualRecord5 n T j m kstar ≃
      ((Fin T → Fin (n ^ 3)) × ((Fin T → Fin (n ^ 3)) ×
        ((Fin (j + 1) → Fin m) × (Fin kstar → Bool)))) := {
    toFun r := (r.ids, (r.arrayTypes, (r.exceptionalStates, r.mask)))
    invFun x := ⟨x.1, x.2.1, x.2.2.1, x.2.2.2⟩
    left_inv r := by cases r; rfl
    right_inv x := by rcases x with ⟨ids, arr, states, mask⟩; rfl
  }
  let eLX : LowAbstractRecord5 T j m kstar ≃
      ((Fin T → Fin T) × ((Fin T → Fin T) ×
        ((Fin (j + 1) → Fin m) × (Fin kstar → Bool)))) := {
    toFun r := (r.ids, (r.arrayTypes, (r.exceptionalStates, r.mask)))
    invFun x := ⟨x.1, x.2.1, x.2.2.1, x.2.2.2⟩
    left_inv r := by cases r; rfl
    right_inv x := by rcases x with ⟨ids, arr, states, mask⟩; rfl
  }
  let eHA : HighActualRecord5 n T J ≃
      ((Fin T → Fin (n ^ 3)) × ((Fin T → Fin (n ^ 3)) × (Fin (J + 1) → Fin T))) := {
    toFun r := (r.ids, (r.arrayTypes, r.optionalKeys))
    invFun x := ⟨x.1, x.2.1, x.2.2⟩
    left_inv r := by cases r; rfl
    right_inv x := by rcases x with ⟨ids, arr, keys⟩; rfl
  }
  let eHX : HighAbstractRecord5 T J m ≃
      ((Fin T → Fin T) × ((Fin T → Fin T) × (Fin (J + 1) → Fin m))) := {
    toFun r := (r.ids, (r.arrayTypes, r.optionalKeys))
    invFun x := ⟨x.1, x.2.1, x.2.2⟩
    left_inv r := by cases r; rfl
    right_inv x := by rcases x with ⟨ids, arr, keys⟩; rfl
  }
  have hLA : Fintype.card (LowActualRecord5 n T j m kstar) =
      (n ^ 3) ^ T * (n ^ 3) ^ T * m ^ (j + 1) * 2 ^ kstar := by
    rw [Fintype.card_congr eLA]
    simp [Fintype.card_fun] <;> ring
  have hLX : Fintype.card (LowAbstractRecord5 T j m kstar) =
      T ^ T * T ^ T * m ^ (j + 1) * 2 ^ kstar := by
    rw [Fintype.card_congr eLX]
    simp [Fintype.card_fun] <;> ring
  have hHA : Fintype.card (HighActualRecord5 n T J) =
      (n ^ 3) ^ T * (n ^ 3) ^ T * T ^ (J + 1) := by
    rw [Fintype.card_congr eHA]
    simp [Fintype.card_fun] <;> ring
  have hHX : Fintype.card (HighAbstractRecord5 T J m) =
      T ^ T * T ^ T * m ^ (J + 1) := by
    rw [Fintype.card_congr eHX]
    simp [Fintype.card_fun] <;> ring
  have hn0 : (0 : ℝ) < n := by exact_mod_cast (by omega : 0 < n)
  have hT0 : (0 : ℝ) < T := by exact_mod_cast hT
  have hm0 : (0 : ℝ) < m := by exact_mod_cast hm
  have hlogLA : Real.log (Fintype.card (LowActualRecord5 n T j m kstar) : ℝ) =
      6 * T * Real.log n + (j + 1) * Real.log m + kstar * Real.log 2 := by
    rw [hLA]
    push_cast
    rw [Real.log_mul (by positivity) (by positivity),
      Real.log_mul (by positivity) (by positivity),
      Real.log_mul (by positivity) (by positivity)]
    simp only [Real.log_pow]
    push_cast
    ring
  have hlogLX : Real.log (Fintype.card (LowAbstractRecord5 T j m kstar) : ℝ) =
      2 * T * Real.log T + (j + 1) * Real.log m + kstar * Real.log 2 := by
    rw [hLX]
    push_cast
    rw [Real.log_mul (by positivity) (by positivity),
      Real.log_mul (by positivity) (by positivity),
      Real.log_mul (by positivity) (by positivity)]
    simp only [Real.log_pow]
    push_cast
    ring
  have hlogHA : Real.log (Fintype.card (HighActualRecord5 n T J) : ℝ) =
      6 * T * Real.log n + (J + 1) * Real.log T := by
    rw [hHA]
    push_cast
    rw [Real.log_mul (by positivity) (by positivity),
      Real.log_mul (by positivity) (by positivity)]
    simp only [Real.log_pow]
    push_cast
    ring
  have hlogHX : Real.log (Fintype.card (HighAbstractRecord5 T J m) : ℝ) =
      2 * T * Real.log T + (J + 1) * Real.log m := by
    rw [hHX]
    push_cast
    rw [Real.log_mul (by positivity) (by positivity),
      Real.log_mul (by positivity) (by positivity)]
    simp only [Real.log_pow]
    push_cast
    ring
  exact ⟨le_of_eq hlogLA, ⟨le_of_eq hlogLX, ⟨le_of_eq hlogHA, le_of_eq hlogHX⟩⟩⟩

end
end HypercubeRamsey
