import HypercubeRamsey.Interface

/-!
Section 9 exports consumed by Section 11. These declarations are lane-local shared contracts because the
Section 9 modules are not present on this branch.
-/

namespace HypercubeRamsey.S11

open HypercubeRamsey

/-- SHARED: P9.2a — under stabilization, the power-bias exponent cannot be below one. -/
theorem not_HdagLtOne (T : Stage) : StabilizedOn T FamB → ¬ HdagLtOne T := by
  sorry

/-- SHARED: P9.2b — the intermediate linear-bias regime is impossible. -/
theorem not_intermediate_linear (T : Stage) :
    StabilizedOn T FamB → ¬ HdagLtOne T → HLdagLtOne T → ¬ HLdagZero T → False := by
  sorry

/-- SHARED: D9.1(iii) — stabilized absence of a linear-bias patch gives discrepancy. -/
theorem disc_of_unavailable_linear (T : Stage) (hT : StabilizedOn T FamB)
    (x α h : ℚ) (hx : 0 < x) (hx1 : x < 1) (hα : 0 < α) (hh : 0 < h)
    (havail : ¬ AvL T x α h) :
    DiscAt T (pw x) (lw α) (fun n => n ^ (-(h : ℝ))) := by
  sorry

/-- SHARED: X-RamseyBinom — the binomial Ramsey bound used by L11.2b and L11.3d. -/
theorem graph_ramsey_binomial_bound {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (s t : ℕ) (hs : 0 < s) (ht : 0 < t)
    (hcard : Nat.choose (s + t - 2) (s - 1) ≤ Fintype.card V) :
    (∃ S : Finset V, S.card = s ∧
        ∀ ⦃x y : V⦄, x ∈ S → y ∈ S → x ≠ y → G.Adj x y) ∨
      (∃ S : Finset V, S.card = t ∧
        ∀ ⦃x y : V⦄, x ∈ S → y ∈ S → x ≠ y → ¬ G.Adj x y) := by
  sorry

end HypercubeRamsey.S11
