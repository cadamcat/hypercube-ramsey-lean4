import HypercubeRamsey.S18.Completion_sol_s18_n5
import HypercubeRamsey.S18.Tower_sol_s18_n4

namespace HypercubeRamsey.S18.Lane_sol_s18_n5
open Classical
open scoped BigOperators
variable {κ : CConsts} {T : Stage} {k : ℕ} {PT : ProfiledTiling κ T k} {hPT : PT.Valid}

private theorem reference_mass_before_congr (D : LateData hPT)
    (h : D.encoding.base.History (Fin.last D.geom.r))
    (j j' : Fin (D.geom.r + 1)) (hj : j.val ≤ D.geom.r) (hj' : j'.val ≤ D.geom.r)
    (heq : j = j') :
    (D.encoding.kernels.refRun h.1).pr (D.agreesWithHistory (D.beforeHistory h j hj)) =
      (D.encoding.kernels.refRun h.1).pr (D.agreesWithHistory (D.beforeHistory h j' hj')) := by
  subst j'
  rfl

/-- A reached prefix has positive mass under the full reference run.
Only the last executed transition is needed: its entering check gives
the previous reference mass, and reference_support gives the next factor. -/
theorem reached_reference_positive (D : LateData hPT) {δ ε : ℝ}
    (C : TerminalCertificate D δ ε) (A : ClassSamplerData D δ)
    (x : D.encoding.InitInput) (h : D.encoding.base.History (Fin.last D.geom.r))
    (hw : (FinLaw.bind (D.encoding.terminalLaw (terminalSet D δ) C.positive)
      (fun x => D.encoding.base.runFull A.act (D.encoding.initialState x))).w (x, h) ≠ 0)
    (j : Fin D.geom.r) (hr : reached D δ j h) :
    0 < (D.encoding.kernels.refRun
      (D.beforeHistory h j.castSucc (Nat.le_of_lt j.isLt)).1).pr
        (D.agreesWithHistory (D.beforeHistory h j.castSucc (Nat.le_of_lt j.isLt))) := by
  obtain ⟨hx, hh⟩ := mul_ne_zero_iff.mp hw
  obtain ⟨hinit, hsteps⟩ := runFrom_support D A.act (D.encoding.initialState x)
    D.geom.r le_rfl h hh
  by_cases hz : j.val = 0
  · have hi : j.castSucc = (0 : Fin (D.geom.r + 1)) := Fin.ext hz
    change 0 < (D.encoding.kernels.refRun h.1).pr
      (D.agreesWithHistory (D.beforeHistory h j.castSucc (Nat.le_of_lt j.isLt)))
    rw [reference_mass_before_congr D h j.castSucc 0 _ (by simp) hi,
      beforeHistory_zero, hinit]
    exact (terminal_initial_incoming D C x (terminal_input_support D C x hx).1).1
  · let s : Fin D.geom.r := ⟨j.val - 1, by omega⟩
    have hs : s.val < j.val := by dsimp [s]; omega
    have hval : s.val + 1 = j.val := by dsimp [s]; omega
    have hi : s.succ = j.castSucc := Fin.ext hval
    have he := hr s hs
    have hout := A.reference_support s _ _ he (hsteps s s.isLt)
    have hp : 0 < (D.encoding.kernels.referenceTransition s
        (D.beforeHistory h s.castSucc (Nat.le_of_lt s.isLt))).w (D.pastRows h s s.isLt) :=
      lt_of_le_of_ne (FinLaw.nonneg _ _) hout.symm
    have hmass := mul_pos he.1 hp
    rw [← HypercubeRamsey.Lane_sol_s18_n4.refRunExtendedHistoryMass D] at hmass
    rw [extend_beforeHistory] at hmass
    change 0 < (D.encoding.kernels.refRun h.1).pr
      (D.agreesWithHistory (D.beforeHistory h s.succ _)) at hmass
    rw [reference_mass_before_congr D h s.succ j.castSucc _ _ hi] at hmass
    exact hmass

theorem reached_incoming (D : LateData hPT) {δ ε : ℝ}
    (C : TerminalCertificate D δ ε) (A : ClassSamplerData D δ)
    (x : D.encoding.InitInput) (h : D.encoding.base.History (Fin.last D.geom.r))
    (hw : (FinLaw.bind (D.encoding.terminalLaw (terminalSet D δ) C.positive)
      (fun x => D.encoding.base.runFull A.act (D.encoding.initialState x))).w (x, h) ≠ 0)
    (j : Fin D.geom.r) (hr : reached D δ j h) :
    let before := D.beforeHistory h j.castSucc (Nat.le_of_lt j.isLt)
    0 < (D.encoding.kernels.refRun before.1).pr (D.agreesWithHistory before) ∧
      ∀ f : LateEvent D, j.val ≤ f.2.1.val → D.futureRisk f before ≤ D.threshold δ j.val := by
  exact ⟨reached_reference_positive D C A x h hw j hr,
    reached_futureRisk D C A x h hw j hr⟩

end HypercubeRamsey.S18.Lane_sol_s18_n5
