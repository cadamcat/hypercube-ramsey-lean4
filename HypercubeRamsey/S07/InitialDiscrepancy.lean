import HypercubeRamsey.S07.SmallGridPurity
import HypercubeRamsey.S07.InitialDiscrepancy_p_s07_d

/-!
# Corollary 7.2: initial discrepancy

This file follows the three reductions in the blueprint: sparse rectangles are absent by E7.1, purity is
excluded by C7.2a–b, and the consumed L4.1 statement converts purity absence to bias absence and then to
discrepancy.
-/

namespace HypercubeRamsey.S07

open Filter

/-- E7.1 (07:9–39), using the universal exponent supplied by L6.1. -/
theorem sparse_rect_not_available_of_L6
    (Dstar D₀ c : ℝ) (hDstar : 0 < Dstar) (hD₀ : 0 < D₀)
    (hD₀star : D₀ < Dstar / 2) (hc : 0 < c)
    (hL6 : Needs.BroadSideProperty Dstar) :
    ∀ T : Stage, ¬ Available T (PViol D₀ c).toPatch := by
  exact sparse_rect_not_available_of_L6_p_s07_d
    Dstar D₀ c hDstar hD₀ hD₀star hc hL6

/-- E7.1 packaged with the constant from L6.1. -/
theorem sparse_rect_not_available :
    ∃ Dstar : ℝ, 0 < Dstar ∧
      ∀ D₀ c : ℝ, 0 < D₀ → D₀ < Dstar / 2 → 0 < c →
        ∀ T : Stage, ¬ Available T (PViol D₀ c).toPatch := by
  obtain ⟨Dstar, hDstar, hL6⟩ := Needs.small_polynomial_broad_side
  refine ⟨Dstar, hDstar, ?_⟩
  intro D₀ c hD₀ hD₀star hc T
  exact sparse_rect_not_available_of_L6 Dstar D₀ c hDstar hD₀ hD₀star hc hL6 T

/-- C7.2a (07:395–403): convert two-colour purity to one-colour grid purity. -/
theorem purity_to_grid_purity (β h : ℝ) (hβ : 0 < β) (hh : 0 < h) :
    ∃ n₀ : ℕ, ∀ n ≥ n₀, ∀ κ : ℝ, 0 < κ → ∀ N : ℕ,
      ∀ E : Fin N → Fin N → Prop, ∀ X Y : Finset (Fin N),
        AvailableAt κ (PPure β β h).toPatch n N E X Y →
        ∃ G : Colour, AvailableAt (κ / 2) (PGridPure G (4 * β) (h / 2)).toPatch n N E X Y := by
  exact purity_to_grid_purity_p_s07_d β h hβ hh

/-- Membership witnesses for the rational Section 7 properties in the stabilized family. -/
theorem pviol_mem_FamB (D₀ c : ℚ) :
    (PViol (D₀ : ℝ) (c : ℝ)).toPatch ∈ FamB := by
  simp only [FamB, Set.mem_union, Set.mem_ofPred_eq]
  exact Or.inl (Or.inl (Or.inl (Or.inl ⟨D₀, c, Or.inl rfl⟩)))

theorem ppure_mem_FamB (β γ h : ℚ) :
    (PPure (β : ℝ) (γ : ℝ) (h : ℝ)).toPatch ∈ FamB := by
  simp only [FamB, Set.mem_union, Set.mem_ofPred_eq]
  exact Or.inl (Or.inl (Or.inl (Or.inr ⟨β, γ, h, Or.inl rfl⟩)))

theorem pbias_mem_FamB (β γ h : ℚ) :
    (PBias (pw (β : ℝ)) (pw (γ : ℝ)) (h : ℝ)).toPatch ∈ FamB := by
  simp only [FamB, Set.mem_union, Set.mem_ofPred_eq]
  exact Or.inl (Or.inl (Or.inr ⟨β, γ, h, Or.inl rfl⟩))

/-- From E7.1 and stabilization, obtain (7.1) eventually on the retained sides. -/
theorem eq71_of_stabilized (T : Stage) (hT : StabilizedOn T FamB)
    (D₀ d : ℚ)
    (hNoViol : ¬ Available T (PViol (D₀ : ℝ) ((d / 80 : ℚ) : ℝ)).toPatch) :
    ∀ᶠ k in atTop, Eq71At (D₀ : ℝ) (d : ℝ) (T.S.n k) (T.S.N k)
      (T.S.E k) (T.X k) (T.Y k) := by
  have hmem := pviol_mem_FamB D₀ (d / 80)
  have habsence : EventuallyAbsent T (PViol (D₀ : ℝ) ((d / 80 : ℚ) : ℝ)).toPatch := by
    rcases hT _ hmem with hav | habs
    · exact False.elim (hNoViol hav)
    · exact habs
  filter_upwards [habsence] with k hk
  intro σ τ hσ hτ hCap hWidth col
  apply lt_of_not_ge
  intro hlow
  have hcast : ((d / 80 : ℚ) : ℝ) = (d : ℝ) / 80 := by push_cast; ring
  let A := lawSupport σ
  let B := lawSupport τ
  have hpair : (A, B) ∈ (PViol (D₀ : ℝ) ((d / 80 : ℚ) : ℝ)).toPatch
      (T.S.n k) (T.S.N k) (T.S.E k) := by
    refine ⟨σ, τ, law_supportedIn_support σ, law_supportedIn_support τ, ?_⟩
    exact ⟨hCap, hWidth, ⟨col, by simpa only [hcast] using hlow⟩⟩
  have hnot := hk A B hpair
  apply hnot
  exact ⟨law_support_subset hσ, law_support_subset hτ⟩

/-- C7.2b: on a stabilized stage satisfying (7.1), the Section 4 purity property is absent. -/
theorem no_ppure_available
    (T : Stage) (hT : StabilizedOn T FamB)
    (D₀ d h' : ℚ) (hD₀ : 0 < (D₀ : ℝ)) (hD₀small : (D₀ : ℝ) < 1 / 10)
    (hd : 0 < (d : ℝ))
    (hdtiny : (d : ℝ) < (D₀ : ℝ) / 1000) (hh' : 0 < (h' : ℝ))
    (hNoViol : ¬ Available T (PViol (D₀ : ℝ) ((d / 80 : ℚ) : ℝ)).toPatch) :
    ¬ Available T (PPure ((d / 4 : ℚ) : ℝ) ((d / 4 : ℚ) : ℝ) (h' : ℝ)).toPatch := by
  have h71 := eq71_of_stabilized T hT D₀ d hNoViol
  have hshot :
      ∀ κ : ℝ, 0 < κ →
        ∃ n₀ : ℕ, ∃ C₀ : ℝ,
          ∀ n N : ℕ, ∀ E : Fin N → Fin N → Prop, ∀ X Y : Finset (Fin N),
            LargeAt n₀ C₀ n N →
              Eq71At (D₀ : ℝ) (d : ℝ) n N E X Y →
              AvailableAt κ (PPure ((d / 4 : ℚ) : ℝ) ((d / 4 : ℚ) : ℝ) (h' : ℝ)).toPatch n N E X Y →
              CubeAt n N E := by
    intro κ hκ
    have hdq : 0 < d := by exact_mod_cast hd
    have hβq : 0 < d / 4 := div_pos hdq (by norm_num)
    obtain ⟨nGrid, hConvert⟩ := purity_to_grid_purity
      ((d / 4 : ℚ) : ℝ) (h' : ℝ) (by exact_mod_cast hβq) hh'
    obtain ⟨nShot, C₀, hGrid⟩ := small_grid_purity
      (D₀ : ℝ) (d : ℝ) ((h' : ℝ) / 2) (κ / 2)
      hD₀ hD₀small hd hdtiny (by positivity) (by positivity)
    refine ⟨max nGrid nShot, C₀, ?_⟩
    intro n N E X Y hlarge hEq71 hPure
    obtain ⟨hn, hlow, hhigh⟩ := hlarge
    have hnGrid : nGrid ≤ n := le_trans (Nat.le_max_left _ _) hn
    have hnShot : nShot ≤ n := le_trans (Nat.le_max_right _ _) hn
    obtain ⟨G', hGridPure⟩ := hConvert n hnGrid (κ) hκ N E X Y hPure
    have hlargeShot : LargeAt nShot C₀ n N := ⟨hnShot, hlow, hhigh⟩
    have hGridPure' : AvailableAt (κ / 2) (PGridPure G' (d : ℝ) ((h' : ℝ) / 2)).toPatch
        n N E X Y := by
      have heq : 4 * ((d / 4 : ℚ) : ℝ) = (d : ℝ) := by push_cast; ring
      simpa only [heq] using hGridPure
    exact hGrid n N E X Y G' hlargeShot hEq71 hGridPure'
  exact not_available_of_oneShot' (T := T)
    (P := (PPure ((d / 4 : ℚ) : ℝ) ((d / 4 : ℚ) : ℝ) (h' : ℝ)).toPatch)
    (side := fun n N E X Y => Eq71At (D₀ : ℝ) (d : ℝ) n N E X Y)
    h71 hshot

/-- A bias-absence statement yields equal-width discrepancy, including both colours. -/
theorem discAt_of_bias_absent
    (T : Stage) (β h η : ℝ) (hηβ : η ≤ β) (hηh : η ≤ h)
    (hAbs : EventuallyAbsent T (PBias (pw β) (pw β) h).toPatch) :
    DiscAt T (pw η) (pw η) (fun n => n ^ (-η)) := by
  have hn : ∀ᶠ k in atTop, 1 ≤ (T.S.n k : ℝ) := by
    filter_upwards [T.S.n_tendsto.eventually_ge_atTop 1] with k hk
    exact_mod_cast hk
  filter_upwards [hAbs, hn] with k hkAbs hk
  intro c μ ν hμ hν hμw hνw
  have hpowηβ : (T.S.n k : ℝ) ^ η ≤ (T.S.n k : ℝ) ^ β :=
    Real.rpow_le_rpow_of_exponent_le hk hηβ
  have hpowhη : (T.S.n k : ℝ) ^ (-h) ≤ (T.S.n k : ℝ) ^ (-η) :=
    Real.rpow_le_rpow_of_exponent_le hk (by linarith)
  have hμβ : μ.WidthLE ((T.S.n k : ℝ) ^ β) := by
    intro x
    exact (hμw x).trans
      (div_le_div_of_nonneg_right (Real.exp_le_exp.mpr hpowηβ) (by positivity))
  have hνβ : ν.WidthLE ((T.S.n k : ℝ) ^ β) := by
    intro y
    exact (hνw y).trans
      (div_le_div_of_nonneg_right (Real.exp_le_exp.mpr hpowηβ) (by positivity))
  have htrue : |dens (T.S.E k) true μ ν - 1 / 2| ≤ (T.S.n k : ℝ) ^ (-h) := by
    apply le_of_not_ge
    intro hlarge
    let A := lawSupport μ
    let B := lawSupport ν
    have hpair : (A, B) ∈
        (PBias (pw β) (pw β) h).toPatch (T.S.n k) (T.S.N k) (T.S.E k) := by
      refine ⟨μ, ν, law_supportedIn_support μ, law_supportedIn_support ν, ?_⟩
      exact ⟨by simpa [pw] using hμβ, by simpa [pw] using hνβ, hlarge⟩
    have hnot := hkAbs A B hpair
    apply hnot
    exact ⟨law_support_subset hμ, law_support_subset hν⟩
  have hcol : |dens (T.S.E k) c μ ν - 1 / 2| ≤ (T.S.n k : ℝ) ^ (-h) := by
    cases c with
    | true => exact htrue
    | false =>
      have hcomp : dens (T.S.E k) false μ ν - 1 / 2 =
          -(dens (T.S.E k) true μ ν - 1 / 2) := by
        rw [dens_false]
        ring
      rw [hcomp, abs_neg]
      exact htrue
  exact le_trans hcol hpowhη

/-- Corollary 7.2 (07:395–425), with exactly the interface type. -/
theorem initial_discrepancy_proof :
    ∃ η₀ > (0 : ℝ), ∀ T : Stage, StabilizedOn T FamB →
      DiscAt T (pw η₀) (pw η₀) (fun n => n ^ (-η₀)) := by
  obtain ⟨Dstar, hDstar, hE71⟩ := sparse_rect_not_available
  have hupper : 0 < min (1 / 10 : ℝ) (Dstar / 2) := by
    apply lt_min
    · norm_num
    · linarith
  obtain ⟨D₀, hD₀, hD₀upper⟩ := exists_rat_btwn hupper
  have hdt : 0 < (D₀ : ℝ) / 1000 := by positivity
  obtain ⟨d, hd, hdtiny⟩ := exists_rat_btwn hdt
  let βq : ℚ := d / 4
  let β : ℝ := (βq : ℝ)
  have hdq : 0 < d := by exact_mod_cast hd
  have hβ : 0 < β := by
    have hβq : 0 < βq := by dsimp [βq]; exact div_pos hdq (by norm_num)
    change (0 : ℝ) < (βq : ℝ)
    exact_mod_cast hβq
  have hβone : β < 1 := by
    have hD₀small : (D₀ : ℝ) < 1 / 10 := lt_of_lt_of_le hD₀upper (min_le_left _ _)
    have hdsmall : (d : ℝ) < 1 := by nlinarith [hdtiny, hD₀small]
    have hβeq : β = (d : ℝ) / 4 := by
      dsimp [β, βq]
      push_cast
      ring
    rw [hβeq]
    nlinarith [hdsmall]
  obtain ⟨h, hh, hL4⟩ := Needs.L4_1_consumed β β hβ le_rfl hβone
  obtain ⟨hq, hhq, hhq'⟩ := exists_rat_btwn hh
  let η₀ : ℝ := min β (hq : ℝ)
  have hη₀ : 0 < η₀ := lt_min hβ (by exact_mod_cast hhq)
  have hηβ : η₀ ≤ β := min_le_left _ _
  have hηh : η₀ ≤ (hq : ℝ) := min_le_right _ _
  refine ⟨η₀, hη₀, ?_⟩
  intro T hT
  have hD₀small : (D₀ : ℝ) < 1 / 10 := lt_of_lt_of_le hD₀upper (min_le_left _ _)
  have hD₀star : (D₀ : ℝ) < Dstar / 2 := lt_of_lt_of_le hD₀upper (min_le_right _ _)
  have hc : 0 < ((d / 80 : ℚ) : ℝ) := by
    exact_mod_cast (div_pos hdq (by norm_num : (0 : ℚ) < 80))
  have hNoViol := hE71 (D₀ : ℝ) ((d / 80 : ℚ) : ℝ) hD₀ hD₀star hc T
  have hNoPure := no_ppure_available T hT D₀ d hq hD₀ hD₀small
    (by exact_mod_cast hd) hdtiny (by exact_mod_cast hhq) hNoViol
  have hPureAbs : EventuallyAbsent T
      (PPure (βq : ℝ) (βq : ℝ) (hq : ℝ)).toPatch := by
    rcases hT _ (ppure_mem_FamB βq βq hq) with hav | habs
    · exact False.elim (hNoPure hav)
    · exact habs
  have hBiasMem := pbias_mem_FamB βq βq hq
  have hBiasAbs : EventuallyAbsent T (PBias (pw β) (pw β) (hq : ℝ)).toPatch := by
    rcases hT _ hBiasMem with hav | habs
    · exact False.elim (hL4 (hq : ℝ) (by exact_mod_cast hhq) (le_of_lt hhq') T hav hPureAbs)
    · exact habs
  exact discAt_of_bias_absent T β (hq : ℝ) η₀ hηβ hηh hBiasAbs

end HypercubeRamsey.S07
