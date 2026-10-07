import HypercubeRamsey.Framework.Props

/-!
# Section 9 parameters

The two cases are kept disjoint: sublinear parameters carry three second-side
exponents, while the linear case carries its two linear widths and broad-test
parameters.  Rational fields match the stabilized family `FamB`.
-/

namespace HypercubeRamsey

/-- P9.2c (09:32–39): the sublinear or linear width regime. -/
inductive Case9 where
  | sub (yS yD yM : ℚ)
  | lin (αS αD hB yB : ℚ)
  deriving DecidableEq

/-- P9.2c (09:32–39): rational parameters satisfying C-common and one of C-sub/C-lin. -/
structure Params9 where
  xS : ℚ
  xD : ℚ
  hMinus : ℚ
  hPlus : ℚ
  σ : ℚ
  χ : ℚ
  case : Case9

namespace Params9

/-- P9.2c: the selected parameter record is in the sublinear case. -/
def IsSublinear (P : Params9) : Prop := ∃ yS yD yM, P.case = .sub yS yD yM

/-- P9.2c: the selected parameter record is in the linear case. -/
def IsLinear (P : Params9) : Prop := ∃ αS αD hB yB, P.case = .lin αS αD hB yB

/-- P9.2c (09:32–39): C-common together with the validity inequalities for
the selected branch. The branch-specific conditions are not imposed together. -/
def Valid (P : Params9) : Prop :=
  (0 < P.xS ∧ P.xS < P.xD ∧ P.xD < 1 / 10) ∧
  (0 < P.hMinus ∧ P.hMinus < P.hPlus ∧ P.hPlus < 1) ∧
  P.xD < (1 - P.hPlus) / 10 ∧
  (0 < P.σ ∧ P.σ < P.xS / 10) ∧
  (0 < P.χ ∧ P.χ < min P.xS (min P.hMinus (1 - P.hPlus)) / 100) ∧
  P.hPlus - P.hMinus < P.χ / 10 ∧
  (match P.case with
   | .sub yS yD yM =>
       0 < yS ∧ yS < yM ∧ yM < 1 - P.σ ∧ 1 - P.σ < yD ∧ yD < 1 ∧
         P.χ < P.σ / 10
   | .lin αS αD hB yB =>
       0 < 100 * αS ∧ 100 * αS < αD ∧ αD < 1 / 100 ∧
         P.σ < P.χ / 10 ∧ P.hPlus < hB ∧ hB < 1 ∧ 0 < yB ∧ yB < 1)

/-- P9.2c: shallow second-side width `n^yS` or `αS n`. -/
noncomputable def Ss (P : Params9) (n : ℝ) : ℝ :=
  match P.case with
  | .sub yS _ _ => n ^ (yS : ℝ)
  | .lin αS _ _ _ => (αS : ℝ) * n

/-- P9.2c: deep second-side width `n^yD` or `αD n`. -/
noncomputable def Sd (P : Params9) (n : ℝ) : ℝ :=
  match P.case with
  | .sub _ yD _ => n ^ (yD : ℝ)
  | .lin _ αD _ _ => (αD : ℝ) * n

/-- P9.2c: the shallow absolute-bias property consumed by the one-shot core. -/
def BiasProperty (P : Params9) : PatchProp :=
  match P.case with
  | .sub yS _ _ =>
      (PBias (pw (P.xS : ℝ)) (pw (yS : ℝ)) (P.hPlus : ℝ)).toPatch
  | .lin αS _ _ _ =>
      (PBias (pw (P.xS : ℝ)) (lw (αS : ℝ)) (P.hPlus : ℝ)).toPatch

/-- P9.2c: deep discrepancy condition at one dimension. -/
def DeepAt (P : Params9) (n N : ℕ) (E : Fin N → Fin N → Prop)
    (X Y : Finset (Fin N)) : Prop :=
  DiscOne E X Y ((n : ℝ) ^ (P.xD : ℝ)) (P.Sd (n : ℝ)) ((n : ℝ) ^ (-(P.hMinus : ℝ)))

/-- P9.2c (09:120–144): the extra linear-case broad test. -/
def BroadAt (P : Params9) (n N : ℕ) (E : Fin N → Fin N → Prop)
    (X Y : Finset (Fin N)) : Prop :=
  match P.case with
  | .sub _ _ _ => True
  | .lin _ _ hB yB =>
      DiscOne E X Y ((n : ℝ) ^ (P.xD : ℝ)) ((n : ℝ) ^ (yB : ℝ))
        ((n : ℝ) ^ (-(hB : ℝ)))

/-- P9.2c: the side conditions used by the one-shot bridge. -/
def SideAt (P : Params9) (n N : ℕ) (E : Fin N → Fin N → Prop)
    (X Y : Finset (Fin N)) : Prop := P.DeepAt n N E X Y ∧ P.BroadAt n N E X Y

/-- D9.1(iii), P9.2c: deep discrepancy along a stabilized stage. -/
def DeepOnStage (P : Params9) (T : Stage) : Prop :=
  DiscAt T (pw (P.xD : ℝ)) (fun n => P.Sd n)
    (fun n => (n : ℝ) ^ (-(P.hMinus : ℝ)))

/-- P9.2-selL: linear-case broad discrepancy along a stage. -/
def BroadOnStage (P : Params9) (T : Stage) : Prop :=
  match P.case with
  | .sub _ _ _ => True
  | .lin _ _ hB yB =>
      DiscAt T (pw (P.xD : ℝ)) (pw (yB : ℝ)) (fun n => (n : ℝ) ^ (-(hB : ℝ)))

/-- P9.2-selS (09:43–49): shallow availability and deep discrepancy in the
sublinear branch. -/
def SubSelection (P : Params9) (T : Stage) : Prop :=
  ∃ yS yD yM : ℚ, P.case = .sub yS yD yM ∧
    AvP T (P.xS : ℝ) (yS : ℝ) (P.hPlus : ℝ) ∧
    P.DeepOnStage T

/-- P9.2-selL (09:51–59): shallow linear availability, deep discrepancy, and
the broad test in the linear branch. -/
def LinearSelection (P : Params9) (T : Stage) : Prop :=
  ∃ αS αD hB yB : ℚ, P.case = .lin αS αD hB yB ∧
    AvL T (P.xS : ℝ) (αS : ℝ) (P.hPlus : ℝ) ∧
    P.DeepOnStage T ∧ P.BroadOnStage T

end Params9

end HypercubeRamsey
