import HypercubeRamsey.S09.Defs
import HypercubeRamsey.S09.Regime
import HypercubeRamsey.S09.Nodes_p_s09_select
import HypercubeRamsey.S09.Map.Nodes
import HypercubeRamsey.S09.Core.TagStage
import HypercubeRamsey.S09.Core.AssignStage

/-!
# Proposition 9.2 nodes and the one-dimension core

Parameter selection (proved), the admissible upgrade of a sublinear selection, patch preparation (proved), and the
assembly of the one-shot core `intermediate_core` from the ID map (`Map.Nodes`), the tags and masks
(`Core.TagStage`), the gain stage (`Core.GainStage`) and the assignment stage (`Core.AssignStage`).  The assembly
has no `sorry` of its own.
-/

namespace HypercubeRamsey

open Filter OAI.HypercubeRamsey Classical

/-- P9.2-selS (09:43–49): select the shallow and deep sublinear budgets. -/
theorem p92_select_sublinear (T : Stage) (hT : StabilizedOn T FamB)
    (hH : HdagLtOne T) :
    ∃ P : Params9, P.Valid ∧ P.IsSublinear ∧ P.SubSelection T := by
  exact p92_select_sublinear_impl T hT hH

/-- P9.2-selL (09:51–59): select the shallow and deep linear budgets and broad test. -/
theorem p92_select_linear (T : Stage) (hT : StabilizedOn T FamB)
    (hNoH : ¬ HdagLtOne T) (hHL : HLdagLtOne T) (hNotZero : ¬ HLdagZero T) :
    ∃ P : Params9, P.Valid ∧ P.IsLinear ∧ P.LinearSelection T := by
  exact p92_select_linear_impl T hT hNoH hHL hNotZero

/-- P9.2-selS, admissible form (09:44–49): a valid sublinear selection can be upgraded so that `x_s < y_m`
(`Params9.CoreAdmissible`), by replacing `y_m` with a rational in `(max(y_s, x_s, y_m), 1 - σ)`; this interval is
nonempty because `y_s < y_m < 1 - σ` and `x_s < 1/10 < 1 - σ`.  Availability, the deep test and the other
constraints do not involve `y_m`. -/
theorem p92_admissible_sublinear (T : Stage) (P : Params9) (hP : P.Valid) (hSel : P.SubSelection T) :
    ∃ P' : Params9, P'.Valid ∧ P'.IsSublinear ∧ P'.SubSelection T ∧ P'.CoreAdmissible := by
  classical
  rcases hSel with ⟨yS, yD, yM, hcase, hAvail, hDeep⟩
  simp only [Params9.Valid, hcase] at hP
  rcases hP with ⟨⟨hxs0, hxsxd, hxd010⟩, ⟨hm0, hmm, hmp1⟩, hmargin,
    ⟨hsig0, hsigxs⟩, ⟨hchi0, hchibound⟩, hgap,
    hys0, hsym, hymupper, hysigd, hyd1, hchiSig⟩
  have hxsUpper : (P.xS : ℝ) < 1 - (P.σ : ℝ) := by
    have hx : (P.xS : ℝ) < 1 / 10 := by
      have hx1 : (P.xS : ℝ) < (P.xD : ℝ) := by exact_mod_cast hxsxd
      have hx2cast : (P.xD : ℝ) < ((1 / 10 : ℚ) : ℝ) := by exact_mod_cast hxd010
      have hx2 : (P.xD : ℝ) < (1 / 10 : ℝ) := by simpa using hx2cast
      exact lt_trans hx1 hx2
    have hs : (P.σ : ℝ) < 1 / 100 := by
      have : (P.σ : ℝ) < (P.xS : ℝ) / 10 := by exact_mod_cast hsigxs
      linarith
    linarith
  have hymUpperR : (yM : ℝ) < 1 - (P.σ : ℝ) := by exact_mod_cast hymupper
  have hysUpper : (yS : ℝ) < 1 - (P.σ : ℝ) := by
    have hsymR : (yS : ℝ) < (yM : ℝ) := by exact_mod_cast hsym
    exact lt_trans hsymR hymUpperR
  let low : ℝ := max (max (yS : ℝ) (P.xS : ℝ)) (yM : ℝ)
  have hlow : low < 1 - (P.σ : ℝ) := by
    dsimp [low]
    exact max_lt (max_lt hysUpper hxsUpper) hymUpperR
  obtain ⟨yM', hlowNew, hnewUpper⟩ := exists_rat_btwn hlow
  have hysNew : yS < yM' := by
    have h : (yS : ℝ) ≤ low := by
      dsimp [low]
      exact le_trans (le_max_left _ _) (le_max_left _ _)
    exact_mod_cast lt_of_le_of_lt h hlowNew
  have hxsNew : P.xS < yM' := by
    have h : (P.xS : ℝ) ≤ low := by
      dsimp [low]
      exact le_trans (le_max_right _ _) (le_max_left _ _)
    exact_mod_cast lt_of_le_of_lt h hlowNew
  have hxsNewR : (P.xS : ℝ) < (yM' : ℝ) := by exact_mod_cast hxsNew
  have hymNew : yM < yM' := by
    have h : (yM : ℝ) ≤ low := by dsimp [low]; exact le_max_right _ _
    exact_mod_cast lt_of_le_of_lt h hlowNew
  let P' : Params9 := { P with case := .sub yS yD yM' }
  have hValid' : P'.Valid := by
    simp only [Params9.Valid, P']
    refine ⟨⟨hxs0, hxsxd, hxd010⟩, ⟨hm0, hmm, hmp1⟩, hmargin,
      ⟨hsig0, hsigxs⟩, ⟨hchi0, hchibound⟩, hgap, ?_⟩
    exact ⟨hys0, hysNew, (by exact_mod_cast hnewUpper), hysigd, hyd1, hchiSig⟩
  have hSub : P'.IsSublinear := ⟨yS, yD, yM', rfl⟩
  have hSel' : P'.SubSelection T := by
    refine ⟨yS, yD, yM', rfl, hAvail, ?_⟩
    have hDeep' : DiscAt T (pw (P.xD : ℝ)) (fun n => n ^ (yD : ℝ))
        (fun n => (n : ℝ) ^ (-(P.hMinus : ℝ))) := by
      simpa [Params9.DeepOnStage, Params9.Sd, hcase] using hDeep
    simpa [Params9.DeepOnStage, Params9.Sd, P'] using hDeep'
  have hAdmissible : P'.CoreAdmissible := by
    simpa [Params9.CoreAdmissible, P'] using hxsNewR
  exact ⟨P', hValid', hSub, hSel', hAdmissible⟩

/-- P9.2-prep (09:61): balanced tag mixture with a colour and surplus rows. -/
theorem p92_patch_preparation {P : Params9} {κ : ℝ} {n N : ℕ}
    {E : Fin N → Fin N → Prop} {X Y : Finset (Fin N)}
    (hP : P.Valid) (hκ : 0 < κ) (hN : 0 < N)
    (hAvail : AvailableAt κ P.BiasProperty n N E X Y) :
    ∃ G : Colour, ∃ M : TagMix N,
      M.Balanced (8 / κ) ∧
      (∀ i, 0 < M.Λ i → (M.μ i).SupportedIn X ∧ (M.ν i).SupportedIn Y ∧
        (M.μ i).WidthLE ((n : ℝ) ^ (P.xS : ℝ) +
          (P.hPlus : ℝ) * Real.log (n : ℝ) + 1) ∧
        (M.ν i).WidthLE (P.Ss (n : ℝ)) ∧
        ∀ x, (M.μ i).w x ≠ 0 →
          1 / 2 + (n : ℝ) ^ (-(P.hPlus : ℝ)) / 2 ≤ rowDeg E G x (M.ν i)) := by
  exact p92_patch_preparation_impl hP hκ hN hAvail

/-- P9.2c (09:30–352): the one-dimension core.  For admissible valid parameters and `κ > 0`, at all large
dimensions with `N ≥ C₀ 2^n`, deep discrepancy (with the broad test in the linear case) and availability of the
shallow bias property at tolerance `κ` give a monochromatic cube.  Assembled from P9.2-prep, the ID map
(P9.2-map1/map2), the tags and masks (P9.2-tags), the gain stage (P9.2-reg … P9.2-gain) and the assignment stage
(P9.2-assignA–C). -/
theorem intermediate_core (P : Params9) (hP : P.Valid) (hA : P.CoreAdmissible) (κ : ℝ) (hκ : 0 < κ) :
    ∃ n₀ C₀, ∀ n N (E : Fin N → Fin N → Prop) (X Y : Finset (Fin N)),
      LargeAt n₀ C₀ n N → P.DeepAt n N E X Y → P.BroadAt n N E X Y →
      AvailableAt κ P.BiasProperty n N E X Y → CubeAt n N E := by
  obtain ⟨nI, hI⟩ := p92_idmap P hP
  obtain ⟨cT, hcT, nT, htags⟩ := p92_tags P hP hA κ hκ
  obtain ⟨c₀, hc₀, nG, hgain⟩ := p92_gain_stage P hP cT hcT
  obtain ⟨nA, CA, hassign⟩ := p92_assign_stage P hP κ hκ c₀ hc₀
  obtain ⟨hExps, nS, hScales⟩ := scales_eventually9 P hP
  refine ⟨max (max nI nT) (max nG (max nA nS)), max CA 1, ?_⟩
  intro n N E X Y hL hDeep hBroad hAvail
  have hn : max (max nI nT) (max nG (max nA nS)) ≤ n := hL.1
  have hNreal : (1 : ℝ) * 2 ^ n ≤ N :=
    le_trans (mul_le_mul_of_nonneg_right (le_max_right CA 1) (by positivity)) hL.2.1
  have hN : 0 < N := by
    have h2 : (0 : ℝ) < 1 * 2 ^ n := by positivity
    exact_mod_cast lt_of_lt_of_le h2 hNreal
  obtain ⟨G, M, hBal, hRows⟩ := p92_patch_preparation hP hκ hN hAvail
  have hprep : Prep9 P κ n N E X Y G M := ⟨hBal, hRows⟩
  obtain ⟨I⟩ := hI n (by omega)
  obtain ⟨tag, htag⟩ := htags n (by omega) hN hL.2.2 hprep hDeep hBroad
  obtain ⟨maskLaw, hmask⟩ := p92_masks E G I tag hN
  let S : Setup9 P n N M := ⟨tag, maskLaw⟩
  have hin : CoreInput9 P κ E X Y G M S I :=
    ⟨hN, hprep, hDeep, htag.1, hmask, deep_tools9 hDeep, hExps, hScales n (by omega)⟩
  have hG := hgain n (by omega) S I hin htag
  exact hassign n N (largeAt_mono9 hL (by omega) (le_max_left _ _)) S I cT hin htag hG

end HypercubeRamsey
