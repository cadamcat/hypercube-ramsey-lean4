import HypercubeRamsey.Interface
import HypercubeRamsey.S11.Needs_p_s11_a

/-!
Section 9 exports consumed by Section 11. These declarations are lane-local shared contracts because the
Section 9 modules are not present on this branch.
-/

namespace HypercubeRamsey.S11

open HypercubeRamsey

/-- SHARED: P9.2a — under stabilization, the power-bias exponent cannot be below one. -/
theorem not_HdagLtOne (T : Stage) : StabilizedOn T FamB → ¬ HdagLtOne T := by
  intro hT
  exact _root_.HypercubeRamsey.not_HdagLtOne T hT

/-- SHARED: P9.2b — the intermediate linear-bias regime is impossible. -/
theorem not_intermediate_linear (T : Stage) :
    StabilizedOn T FamB → ¬ HdagLtOne T → HLdagLtOne T → ¬ HLdagZero T → False := by
  intro hT hNoH hHL hNotZero
  exact _root_.HypercubeRamsey.not_intermediate_linear T hT hNoH hHL hNotZero

/-- SHARED: D9.1(iii) — stabilized absence of a linear-bias patch gives discrepancy. -/
theorem disc_of_unavailable_linear (T : Stage) (hT : StabilizedOn T FamB)
    (x α h : ℚ) (hx : 0 < x) (hx1 : x < 1) (hα : 0 < α) (hh : 0 < h)
    (havail : ¬ AvL T x α h) :
    DiscAt T (pw x) (lw α) (fun n => n ^ (-(h : ℝ))) := by
  exact _root_.HypercubeRamsey.discAt_of_not_AvL hT hx hα hh havail

/-- SHARED: X-RamseyBinom — the binomial Ramsey bound used by L11.2b and L11.3d. -/
theorem graph_ramsey_binomial_bound {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (s t : ℕ) (hs : 0 < s) (ht : 0 < t)
    (hcard : Nat.choose (s + t - 2) (s - 1) ≤ Fintype.card V) :
    (∃ S : Finset V, S.card = s ∧
        ∀ ⦃x y : V⦄, x ∈ S → y ∈ S → x ≠ y → G.Adj x y) ∨
      (∃ S : Finset V, S.card = t ∧
        ∀ ⦃x y : V⦄, x ∈ S → y ∈ S → x ≠ y → ¬ G.Adj x y) := by
  classical
  have hs' : 1 ≤ s := Nat.one_le_iff_ne_zero.mpr (Nat.ne_of_gt hs)
  have ht' : 1 ≤ t := Nat.one_le_iff_ne_zero.mpr (Nat.ne_of_gt ht)
  rcases _root_.HypercubeRamsey.xRamseyBinom G s t hs' ht' hcard with hclique | hindependent
  · rcases hclique with ⟨S, hS, hAdj⟩
    left
    refine ⟨S, hS, ?_⟩
    intro x y hx hy hxy
    exact hAdj x hx y hy hxy
  · rcases hindependent with ⟨S, hS, hNotAdj⟩
    right
    refine ⟨S, hS, ?_⟩
    intro x y hx hy hxy
    exact hNotAdj x hx y hy hxy

end HypercubeRamsey.S11
