import HypercubeRamsey.Framework.Props

/-!
# Definition 9.1: availability exponents

`Hpow` and `Hlin` are the capped infima from the framework.  These lemmas are
the rational-parameter facts used by the two selection nodes below.
-/

namespace HypercubeRamsey

/-- D9.1(i) (09:11–20): availability is monotone in power widths and bias threshold. -/
theorem AvP.mono {T : Stage} {x y h x' y' h' : ℝ}
    (ha : AvP T x y h) (hx : x ≤ x') (hy : y ≤ y') (hh : h ≤ h') :
    AvP T x' y' h' := by
  sorry

/-- D9.1(i) (09:11–20): availability is monotone in power/linear widths and bias threshold. -/
theorem AvL.mono {T : Stage} {x α h x' α' h' : ℝ}
    (ha : AvL T x α h) (hx : x ≤ x') (hα : α ≤ α') (hh : h ≤ h') :
    AvL T x' α' h' := by
  sorry

/-- D9.1(ii): an exponent strictly above the capped infimum is available. -/
theorem Hpow_lt_available {T : Stage} {x y h : ℝ}
    (hh : Hpow T x y < h) (hpos : 0 < h) (hcap : h ≤ 2) : AvP T x y h := by
  sorry

/-- D9.1(ii): a positive rational exponent strictly below the capped infimum is unavailable. -/
theorem Hpow_gt_not_available {T : Stage} {x y : ℝ} {h : ℚ}
    (hpos : 0 < h) (hh : (h : ℝ) < Hpow T x y) : ¬ AvP T x y h := by
  sorry

/-- D9.1(ii): an exponent strictly above the capped linear infimum is available. -/
theorem Hlin_lt_available {T : Stage} {x α h : ℝ}
    (hh : Hlin T x α < h) (hpos : 0 < h) (hcap : h ≤ 2) : AvL T x α h := by
  sorry

/-- D9.1(ii): a positive rational exponent strictly below the capped linear infimum is unavailable. -/
theorem Hlin_gt_not_available {T : Stage} {x α : ℝ} {h : ℚ}
    (hpos : 0 < h) (hh : (h : ℝ) < Hlin T x α) : ¬ AvL T x α h := by
  sorry

/-- D9.1(ii): `Hpow` is antitone in its first width parameter. -/
theorem Hpow_antitone_x {T : Stage} {x x' y : ℝ} (hxx : x ≤ x') :
    Hpow T x' y ≤ Hpow T x y := by
  sorry

/-- D9.1(ii): `Hpow` is antitone in its second width parameter. -/
theorem Hpow_antitone_y {T : Stage} {x y y' : ℝ} (hyy : y ≤ y') :
    Hpow T x y' ≤ Hpow T x y := by
  sorry

/-- D9.1(ii): `Hlin` is antitone in its first width parameter. -/
theorem Hlin_antitone_x {T : Stage} {x x' α : ℝ} (hxx : x ≤ x') :
    Hlin T x' α ≤ Hlin T x α := by
  sorry

/-- D9.1(ii): `Hlin` is antitone in its linear width parameter. -/
theorem Hlin_antitone_α {T : Stage} {x α α' : ℝ} (hα : α ≤ α') :
    Hlin T x α' ≤ Hlin T x α := by
  sorry

/-- D9.1(iii): stabilization turns unavailable power bias into discrepancy. -/
theorem discAt_of_not_AvP {T : Stage} (hT : StabilizedOn T FamB)
    {x y h : ℚ} (hx : 0 < x) (hy : 0 < y) (hh : 0 < h)
    (hnot : ¬ AvP T x y h) :
    DiscAt T (pw x) (pw y) (fun n => (n : ℝ) ^ (-(h : ℝ))) := by
  sorry

/-- D9.1(iii): stabilization turns unavailable linear bias into discrepancy. -/
theorem discAt_of_not_AvL {T : Stage} (hT : StabilizedOn T FamB)
    {x α h : ℚ} (hx : 0 < x) (hα : 0 < α) (hh : 0 < h)
    (hnot : ¬ AvL T x α h) :
    DiscAt T (pw x) (lw α) (fun n => (n : ℝ) ^ (-(h : ℝ))) := by
  sorry

/-- D9.1(iv): stronger discrepancy excludes availability at a smaller exponent. -/
theorem not_AvP_of_discAt {T : Stage} {x y h h₀ : ℚ}
    (hxy : 0 < x ∧ 0 < y) (hh : 0 < h) (h₀h : h < h₀)
    (hd : DiscAt T (pw x) (pw y) (fun n => (n : ℝ) ^ (-(h₀ : ℝ)))) :
    ¬ AvP T x y h := by
  sorry

/-- D9.1(iv): stronger linear discrepancy excludes availability at a smaller exponent. -/
theorem not_AvL_of_discAt {T : Stage} {x α h h₀ : ℚ}
    (hxα : 0 < x ∧ 0 < α) (hh : 0 < h) (h₀h : h < h₀)
    (hd : DiscAt T (pw x) (lw α) (fun n => (n : ℝ) ^ (-(h₀ : ℝ)))) :
    ¬ AvL T x α h := by
  sorry

end HypercubeRamsey
