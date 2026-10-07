import HypercubeRamsey.S03.Clock.Inputs

namespace HypercubeRamsey.Clock

open scoped BigOperators

/-- The coordinatewise meet of two clock constraints, retaining the stronger absence cutoff. -/
def qClockConstraintMeet {T : ℕ} {α : Type*} (C D : EdgeConstraint T α) : EdgeConstraint T α :=
  match C, D with
  | .unrestricted, c => c
  | c, .unrestricted => c
  | .absentBefore h₁, .absentBefore h₂ => .absentBefore (max h₁ h₂)
  | .exactArrival t o, _ => .exactArrival t o
  | _, .exactArrival t o => .exactArrival t o

/-- A common point makes the meet constraint exactly the intersection of its two coordinate conditions. -/
theorem qClockConstraintMeet_allows {T : ℕ} {α : Type*}
    (C D : EdgeConstraint T α) (x₀ x : MeshClockValue T α)
    (hC : C.Allows x₀) (hD : D.Allows x₀) :
    (qClockConstraintMeet C D).Allows x ↔ C.Allows x ∧ D.Allows x := by
  cases C <;> cases D <;> cases x₀ <;> cases x <;>
    simp_all [qClockConstraintMeet, EdgeConstraint.Allows, max_le_iff]

theorem qClockConstraintMeet_inspected {T : ℕ} {α : Type*}
    (C D : EdgeConstraint T α) :
    (qClockConstraintMeet C D).inspected ↔ C.inspected ∨ D.inspected := by
  cases C <;> cases D <;> simp [qClockConstraintMeet, EdgeConstraint.inspected]

theorem qClockConstraintMeet_isHit {T : ℕ} {α : Type*}
    (C D : EdgeConstraint T α) :
    (qClockConstraintMeet C D).isHit ↔ C.isHit ∨ D.isHit := by
  cases C <;> cases D <;> simp [qClockConstraintMeet, EdgeConstraint.isHit]

/-- The arithmetic cutoff used by `Truncated.edgeCutoff`, written with row and label coordinates exposed. -/
noncomputable def qClockCutoffValue {T : ℕ} {R : Type*} [Fintype R] [DecidableEq R] {g : ℕ}
    (H : ℕ) (a : R) (y : Fin g) : ℕ :=
  min T ((H - (((Fintype.equivFin R) a).val * g + y.val) + Fintype.card R * g - 1) /
    (Fintype.card R * g))

/-- A tick is below the cutoff exactly when its event key is below the requested horizon. -/
theorem qClockCutoffValue_le_iff {T : ℕ} {R : Type*} [Fintype R] [DecidableEq R] {g H : ℕ}
    {Ω : R → Type*} (a : R) (y : Fin g) (t : Fin T) (o : Ω a) :
    qClockCutoffValue (T := T) H a y ≤ t.val ↔
      H ≤ eventPriority (⟨a, y, t, o⟩ : ClockCandidate T R g Ω) := by
  classical
  let m : ℕ := Fintype.card R * g
  let d : ℕ := ((Fintype.equivFin R) a).val * g + y.val
  have hR : 0 < Fintype.card R := Fintype.card_pos_iff.mpr ⟨a⟩
  have hy : y.val < g := y.isLt
  have hg : 0 < g := by omega
  have hm : 0 < m := by dsimp [m]; exact Nat.mul_pos hR hg
  have hd : d < m := by
    dsimp [d, m]
    calc
      ((Fintype.equivFin R) a).val * g + y.val <
          ((Fintype.equivFin R) a).val * g + g := Nat.add_lt_add_left y.isLt _
      _ = (((Fintype.equivFin R) a).val + 1) * g := by rw [Nat.add_mul, Nat.one_mul]
      _ ≤ Fintype.card R * g := Nat.mul_le_mul_right g (Nat.succ_le_of_lt ((Fintype.equivFin R a).isLt))
  have hkey : eventPriority (⟨a, y, t, o⟩ : ClockCandidate T R g Ω) = t.val * m + d := by
    simp [eventPriority, m, d, Nat.add_assoc]
  constructor
  · intro hcut
    have hq : (H - d + m - 1) / m ≤ t.val := by
      dsimp [qClockCutoffValue, d, m] at hcut ⊢
      by_cases hqT : (H - d + m - 1) / m ≤ T
      · rw [Nat.min_eq_right hqT] at hcut
        exact hcut
      · have hTq : T ≤ (H - d + m - 1) / m := Nat.le_of_not_ge hqT
        rw [Nat.min_eq_left hTq] at hcut
        omega
    have hnum := (Nat.div_le_iff_le_mul hm).mp hq
    rw [hkey]
    omega
  · intro hkeyH
    have hkeyH' : H ≤ t.val * m + d := by simpa [hkey] using hkeyH
    have hsub : H - d ≤ t.val * m := by
      omega
    have hnum : H - d + m - 1 ≤ t.val * m + m - 1 := by omega
    have hq : (H - d + m - 1) / m ≤ t.val := (Nat.div_le_iff_le_mul hm).2 hnum
    calc
      qClockCutoffValue H a y ≤ (H - d + m - 1) / m := Nat.min_le_right _ _
      _ ≤ t.val := hq

end HypercubeRamsey.Clock
