import HypercubeRamsey.S09.Defs
import HypercubeRamsey.S09.Regime
import HypercubeRamsey.S09.Needs
import HypercubeRamsey.S09.Map2Counterexample_p_s09_maps
import HypercubeRamsey.S03.Mixtures
import HypercubeRamsey.S03.ConditionalAvoidance
import HypercubeRamsey.S03.ScatteredMoments
import HypercubeRamsey.S03.GatedPosterior
import HypercubeRamsey.S03.ClockSampling
import HypercubeRamsey.Framework.Hall
import HypercubeRamsey.Framework.Minimax
import HypercubeRamsey.S09.Core.Stages

/-!
# Proposition 9.2 nodes

Parameter selection, patch preparation, the height/ID maps, and the one-shot
boundary are stated separately.  The remaining anchor, filter, gain, and
assignment argument is represented by the core one-shot node.
-/

namespace HypercubeRamsey

open Filter OAI.HypercubeRamsey Classical

/-- P9.2-selS (09:43–49): select the shallow and deep sublinear budgets. -/
theorem p92_select_sublinear (T : Stage) (hT : StabilizedOn T FamB)
    (hH : HdagLtOne T) :
    ∃ P : Params9, P.Valid ∧ P.IsSublinear ∧ P.SubSelection T := by
  sorry

/-- P9.2-selL (09:51–59): select the shallow and deep linear budgets and broad test. -/
theorem p92_select_linear (T : Stage) (hT : StabilizedOn T FamB)
    (hNoH : ¬ HdagLtOne T) (hHL : HLdagLtOne T) (hNotZero : ¬ HLdagZero T) :
    ∃ P : Params9, P.Valid ∧ P.IsLinear ∧ P.LinearSelection T := by
  sorry

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
  sorry

/-- P9.2-map1 (09:63–102): good heights with distance-two regularity.  The
`HeightGood9` predicate records active eligibility and all three crowd tests. -/
theorem p92_map1 (P : Params9) (hP : P.Valid) :
    ∃ n₀, ∀ n, n₀ ≤ n → Nonempty (HeightWitness9 P n) := by
  exact height_general9 P hP

/-- P9.2-map2 (09:102–118): the ID records a special slice, residual location,
and selected height level. -/
theorem p92_map2 (P : Params9) (hP : P.Valid) {n r : ℕ}
    (W : HeightWitness9 P n) (hr : W.radius = r) :
    ∃ T : ℕ, (n : ℝ) ^ (1 - (P.σ : ℝ) + W.ε) ≤ T ∧
      ∃ c : CubeVertex n → CenterID9 W.specialBits n W.levels,
        (∀ v, (c v).slice = specialWord9 W.specialBits_le v ∧
          residualDistance9 W.specialBits (c v).location v ≤ r ∧
          (c v).level = W.height v ∧ c v ∈ W.active) ∧
        (∀ b : CubeVertex n, ¬ IsEvenRole b →
          (seenIDs9 c b).card ≤ T + W.specialBits) ∧
        (∀ v : CubeVertex n, IsEvenRole v →
          ∃ C : Finset (CenterID9 W.specialBits n W.levels), c v ∈ C ∧
            (C.card : ℝ) ≤ (n : ℝ) ^ (P.χ : ℝ) ∧
            ∀ id, id ∉ C →
              ((Finset.univ.filter (fun b : CubeVertex n =>
                ¬ IsEvenRole b ∧ (cube n).Adj v b ∧ id ∈ seenIDs9 c b)).card : ℕ) ≤ r + 3) := by
  classical
  let exp := (1 : ℝ) - (P.σ : ℝ) + W.ε
  let T : ℕ := Fintype.card (CubeVertex n) + ⌈(n : ℝ) ^ exp⌉₊
  have hT : (n : ℝ) ^ exp ≤ T := by
    dsimp [T]
    calc
      (n : ℝ) ^ exp ≤ (⌈(n : ℝ) ^ exp⌉₊ : ℕ) := Nat.le_ceil _
      _ ≤ (Fintype.card (CubeVertex n) + ⌈(n : ℝ) ^ exp⌉₊ : ℕ) := by
        exact_mod_cast (Nat.le_add_left ⌈(n : ℝ) ^ exp⌉₊
          (Fintype.card (CubeVertex n)))
  have hselect (v : CubeVertex n) :
      ∃ id, id ∈ W.active ∧ id.slice = specialWord9 W.specialBits_le v ∧
        residualDistance9 W.specialBits id.location v ≤ r ∧ id.level = W.height v := by
    simpa [hr] using (W.height_good v).1
  let c : CubeVertex n → CenterID9 W.specialBits n W.levels :=
    fun v => Classical.choose (hselect v)
  have hc (v : CubeVertex n) :
      c v ∈ W.active ∧ (c v).slice = specialWord9 W.specialBits_le v ∧
        residualDistance9 W.specialBits (c v).location v ≤ r ∧
        (c v).level = W.height v :=
    Classical.choose_spec (hselect v)
  refine ⟨T, hT, c, ?_, ?_, ?_⟩
  · intro v
    rcases hc v with ⟨hactive, hslice, hdist, hlevel⟩
    exact ⟨hslice, hdist, hlevel, hactive⟩
  · intro b hb
    have hseen : (seenIDs9 c b).card ≤ Fintype.card (CubeVertex n) := by
      unfold seenIDs9
      calc
        ((Finset.univ.filter (fun a : CubeVertex n => (cube n).Adj a b)).image c).card ≤
            (Finset.univ.filter (fun a : CubeVertex n => (cube n).Adj a b)).card :=
          Finset.card_image_le
        _ ≤ Fintype.card (CubeVertex n) := Finset.card_le_univ _
    dsimp [T]
    omega
  · sorry

/-- P9.2-tags through P9.2-assignC (09:120–350): the fixed tag, anchor, mask,
regularity, conditional-mean, erasure, covariance, gain and assignment
certificates compose to the one-shot embedding.  This assembly interface
includes the broad test only in the linear case. -/
theorem intermediate_core (P : Params9) (hP : P.Valid) (κ : ℝ) (hκ : 0 < κ) :
    ∃ n₀ C₀, ∀ n N (E : Fin N → Fin N → Prop) (X Y : Finset (Fin N)),
      LargeAt n₀ C₀ n N → P.DeepAt n N E X Y → P.BroadAt n N E X Y →
      AvailableAt κ P.BiasProperty n N E X Y → CubeAt n N E := by
  classical
  obtain ⟨nHeight, hHeight⟩ := p92_map1 P hP
  let C₀ : ℝ := 32 / κ + 1
  refine ⟨max nHeight 1, C₀, ?_⟩
  intro n N E X Y hLarge hDeep hBroad hAvail
  rcases hLarge with ⟨hn₀, hNLower, _hNUpper⟩
  have hn : 1 ≤ n := le_trans (le_max_right nHeight 1) hn₀
  have hnHeight : nHeight ≤ n := le_trans (le_max_left nHeight 1) hn₀
  have hLargeSmall : LargeAt 1 C₀ n N := ⟨hn, hNLower, _hNUpper⟩
  have hC₀ : 32 / κ ≤ C₀ := by dsimp [C₀]; linarith
  have hC₀pos : 0 < C₀ := by dsimp [C₀]; positivity
  have hNreal : 0 < (N : ℝ) :=
    lt_of_lt_of_le (mul_pos hC₀pos (by positivity : 0 < (2 : ℝ) ^ n)) hNLower
  have hN : 0 < N := by exact_mod_cast hNreal
  obtain ⟨W⟩ := hHeight n hnHeight
  obtain ⟨idMap⟩ := p92_bounded_idmap9 P hP n W
  obtain ⟨G, M, hBalanced, hMixRows⟩ :=
    p92_patch_preparation hP hκ hN hAvail
  have hMix : M.Balanced (8 / κ) ∧
      ∀ i, 0 < M.Λ i → (M.μ i).SupportedIn X ∧ (M.ν i).SupportedIn Y ∧
        (M.μ i).WidthLE ((n : ℝ) ^ (P.xS : ℝ) +
          (P.hPlus : ℝ) * Real.log (n : ℝ) + 1) ∧
        (M.ν i).WidthLE (P.Ss (n : ℝ)) ∧
        ∀ x, (M.μ i).w x ≠ 0 →
          1 / 2 + (n : ℝ) ^ (-(P.hPlus : ℝ)) / 2 ≤ rowDeg E G x (M.ν i) :=
    ⟨hBalanced, hMixRows⟩
  obtain ⟨S, hTagSupport, hTagSliceLoad, hLinearTags⟩ :=
    p92_tags (P := P) (κ := κ) hκ hP hn hN hDeep hBroad hAvail G M hMix W idMap
  have hLoads := p92_tag_loads (P := P) (κ := κ) S hBalanced hTagSupport hTagSliceLoad
  have hRegular := p92_regularity (P := P) S hP hLargeSmall hn hDeep hTagSupport
  have hMean := p92_conditional_mean S hRegular
  have hErase := p92_erase_core (κ := κ) S hRegular hMean hLoads
  have hCov := p92_covariance (P := P) S hP hn hDeep hRegular hMean hErase
  obtain ⟨hGain⟩ := p92_gain (κ := κ) S hP hRegular hLinearTags hLoads hMean hErase hCov
  have hPredictive := p92_predictive_tests S hP hRegular hGain
  obtain ⟨hAvoid⟩ := p92_anchor_avoidance S hP hn hLinearTags hRegular hGain hPredictive
  obtain ⟨candidates⟩ := p92_odd_candidates (P := P) (κ := κ) (C₀ := C₀)
    S hC₀ hLargeSmall hTagSupport hLoads hAvoid
  obtain ⟨odd⟩ := p92_odd_injection (P := P) (κ := κ) S hκ hP hn C₀ hLargeSmall
    hDeep hBroad hAvail
    hTagSupport hLinearTags hLoads hGain hAvoid candidates
  obtain ⟨rows⟩ := p92_even_rows S X Y odd hP κ hκ hn C₀ hLargeSmall hDeep hBroad hAvail
    hLinearTags hLoads hGain hAvoid
  exact p92_hall_embed X Y odd rows

end HypercubeRamsey
