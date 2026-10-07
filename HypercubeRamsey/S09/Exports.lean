import HypercubeRamsey.S09.Nodes

/-!
# Proposition 9.2 exports

The exported statements are assembled from parameter selection (upgraded to admissible
parameters in the sublinear case) and the single-dimension core.  The assembly proofs
themselves have no `sorry`.
-/

namespace HypercubeRamsey

open Filter

/-- P9.2a/b assembly: the core and the one-shot bridge exclude availability of the shallow bias property. -/
theorem no_available_of_intermediate_core (T : Stage) (P : Params9)
    (hP : P.Valid) (hA : P.CoreAdmissible) (hDeep : P.DeepOnStage T) (hBroad : P.BroadOnStage T) :
    ¬ Available T P.BiasProperty := by
  have hDeepEvent : ∀ᶠ k in atTop,
      P.DeepAt (T.S.n k) (T.S.N k) (T.S.E k) (T.X k) (T.Y k) := by
    exact (discAt_iff_eventually_discOne T (pw (P.xD : ℝ))
      (fun n => P.Sd n) (fun n => (n : ℝ) ^ (-(P.hMinus : ℝ)))).mp hDeep
  have hSide : ∀ᶠ k in atTop,
      P.SideAt (T.S.n k) (T.S.N k) (T.S.E k) (T.X k) (T.Y k) := by
    cases hc : P.case with
    | sub yS yD yM =>
        filter_upwards [hDeepEvent] with k hk
        exact ⟨hk, by simp [Params9.BroadAt, hc]⟩
    | lin αS αD hB yB =>
        have hBroadEvent : ∀ᶠ k in atTop,
            P.BroadAt (T.S.n k) (T.S.N k) (T.S.E k) (T.X k) (T.Y k) := by
          simpa [Params9.BroadAt, pw, hc] using
            (discAt_iff_eventually_discOne T (pw (P.xD : ℝ))
              (pw (yB : ℝ)) (fun n => (n : ℝ) ^ (-(hB : ℝ)))).mp
                (by simpa [Params9.BroadOnStage, hc] using hBroad)
        filter_upwards [hDeepEvent, hBroadEvent] with k hkD hkB
        exact ⟨hkD, hkB⟩
  have hshot : ∀ κ > (0 : ℝ), ∃ n₀ C₀,
      ∀ n N (E : Fin N → Fin N → Prop) (X Y : Finset (Fin N)),
        LargeAt n₀ C₀ n N → P.SideAt n N E X Y →
          AvailableAt κ P.BiasProperty n N E X Y → CubeAt n N E := by
    intro κ hκ
    obtain ⟨n₀, C₀, hcore⟩ := intermediate_core P hP hA κ hκ
    refine ⟨n₀, C₀, ?_⟩
    intro n N E X Y hLarge hSide hAvail
    exact hcore n N E X Y hLarge hSide.1 hSide.2 hAvail
  exact not_available_of_oneShot' (T := T) (P := P.BiasProperty)
    (side := fun n N E X Y => P.SideAt n N E X Y) hSide hshot

/-- P9.2a (09:22–28): exclude `H† < 1` in the chosen orientation. -/
theorem not_HdagLtOne (T : Stage) (hT : StabilizedOn T FamB) : ¬ HdagLtOne T := by
  intro hH
  obtain ⟨P₀, hP₀, _hSub₀, hSel₀⟩ := p92_select_sublinear T hT hH
  obtain ⟨P, hP, _hSub, hSel, hA⟩ := p92_admissible_sublinear T P₀ hP₀ hSel₀
  obtain ⟨yS, yD, yM, hcase, hAvail, hDeep⟩ := hSel
  have hDeepP : P.DeepOnStage T := hDeep
  have hBroadP : P.BroadOnStage T := by
    simp [Params9.BroadOnStage, hcase]
  have hNo := no_available_of_intermediate_core T P hP hA hDeepP hBroadP
  have hAvailP : Available T P.BiasProperty := by
    simpa [AvP, Params9.BiasProperty, hcase] using hAvail
  exact hNo hAvailP

/-- P9.2b (09:22–28): exclude an intermediate linear-bias exponent. -/
theorem not_intermediate_linear (T : Stage) (hT : StabilizedOn T FamB)
    (hNoH : ¬ HdagLtOne T) (hHL : HLdagLtOne T) (hNotZero : ¬ HLdagZero T) : False := by
  obtain ⟨P, hP, hLinear, hSel⟩ := p92_select_linear T hT hNoH hHL hNotZero
  obtain ⟨αS, αD, hB, yB, hcase, hAvail, hDeep, hBroad⟩ := hSel
  have hDeepP : P.DeepOnStage T := hDeep
  have hBroadP : P.BroadOnStage T := hBroad
  have hA : P.CoreAdmissible := by simp [Params9.CoreAdmissible, hcase]
  have hNo := no_available_of_intermediate_core T P hP hA hDeepP hBroadP
  have hAvailP : Available T P.BiasProperty := by
    simpa [AvL, Params9.BiasProperty, hcase] using hAvail
  exact hNo hAvailP

end HypercubeRamsey
