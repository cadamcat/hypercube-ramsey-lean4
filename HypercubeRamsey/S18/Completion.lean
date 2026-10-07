import HypercubeRamsey.S18.Terminal

namespace HypercubeRamsey.S18
open Classical Filter
open scoped BigOperators
variable {κ : CConsts} {T : Stage} {k : ℕ} {PT : ProfiledTiling κ T k} {hPT : PT.Valid}

namespace LateData
variable (D : LateData hPT)
noncomputable def threshold (δ : ℝ) (q : ℕ) :=
  Real.exp (-Real.rpow (T.S.n k : ℝ) δ + q * Real.rpow (T.S.n k : ℝ) δ / (2 * D.geom.r))
noncomputable def agreesWithHistory {j : Fin (D.geom.r + 1)} (h : D.encoding.base.History j)
    (full : D.encoding.base.History (Fin.last D.geom.r)) : Prop :=
  D.beforeHistory full j (Nat.le_of_lt_succ j.isLt) = h
/-- Reference conditional probability, evaluated at the actual entering
history. The zero convention is used only off reference support. -/
noncomputable def futureRisk (f : LateEvent D) {j : Fin (D.geom.r + 1)}
    (h : D.encoding.base.History j) : ℝ :=
  (D.encoding.kernels.refRun h.1).pr (fun full => D.agreesWithHistory h full ∧ lateFailure D f full) /
    (D.encoding.kernels.refRun h.1).pr (D.agreesWithHistory h)
noncomputable def columnSum (j : Fin D.geom.r) (h : D.encoding.base.History j.castSucc)
    (y : Fin (T.S.N k)) : ℝ :=
  ∑ b, (D.encoding.kernels.refK j b h).pr (fun out => D.encoding.base.rowLabel out = y)
noncomputable def enter (δ : ℝ) (j : Fin D.geom.r) (h : D.encoding.base.History j.castSucc) : Prop :=
  (0 < (D.encoding.kernels.refRun h.1).pr (D.agreesWithHistory h)) ∧
  (∀ f : LateEvent D, j.val ≤ f.2.1.val → D.futureRisk f h ≤ D.threshold δ j.val) ∧
  (∀ y, D.columnSum j h y ≤ κ.θ0)
noncomputable def bad (j : Fin D.geom.r) (h : D.encoding.base.History j.castSucc) :
    Finset (D.encoding.base.ClassRows j) :=
  Finset.univ.filter fun out => ∃ b, D.gate j b.1 h ∧
    (¬ D.R1 j (out b) ∨ ¬ D.R2 j h (out b) ∨
      (D.R1 j (out b) ∧ D.R2 j h (out b) ∧ ¬ D.R3 j h (out b)))
noncomputable def alarm (δ : ℝ) (j : Fin D.geom.r) (h : D.encoding.base.History j.castSucc) :
    Finset (D.encoding.base.ClassRows j) :=
  Finset.univ.filter fun out => ∃ f : LateEvent D, j.val < f.2.1.val ∧
    D.threshold δ (j.val + 1) < D.futureRisk f (D.encoding.base.extend j h out)
noncomputable def oddAt (h : D.encoding.base.History (Fin.last D.geom.r))
    (b : {v : Pos T k // ¬ IsEvenRole v}) : Fin (T.S.N k) :=
  if hb : b.1 ∈ D.encoding.base.processed (Fin.last D.geom.r) then
    D.encoding.base.rowLabel (h.2 ⟨b.1, hb⟩) else D.earlyLabel h.1 b.1

/-- Successful completion is a specific sequence of reached, injective,
bad/alarm-avoiding class assignments with the true-hit/deletion conclusions. -/
noncomputable def full (δ : ℝ) (x : D.encoding.InitInput)
    (h : D.encoding.base.History (Fin.last D.geom.r)) : Prop :=
  x ∈ terminalSet D δ ∧ x.1 ∈ permPools D.geom ∧ 0 < D.encoding.permLaw.w x ∧ h.1 = D.encoding.initialState x ∧
  (∀ v, IsEvenRole v → D.initialValid v h.1) ∧ Function.Injective (D.oddAt h) ∧
  ∀ j : Fin D.geom.r,
    let before := D.beforeHistory h j.castSucc (Nat.le_of_lt j.isLt)
    let out := D.pastRows h j j.isLt
    D.enter δ j before ∧ Function.Injective (fun b => D.encoding.base.rowLabel (out b)) ∧
      out ∉ D.bad j before ∧ out ∉ D.alarm δ j before ∧
      ∀ b, D.gate j b.1 before ∧ D.R3 j before (out b) ∧ D.deletionConclusion j (out b)
end LateData

structure ClassSamplerData (D : LateData hPT) (δ : ℝ) where
  act : ∀ j : Fin D.geom.r, D.encoding.base.History j.castSucc → FinLaw (D.encoding.base.ClassRows j)
  sampler : D.encoding.SamplerSpec act (D.enter δ) D.bad (D.alarm δ)
  reference_support : ∀ j h out, D.enter δ j h → (act j h).w out ≠ 0 →
    (D.encoding.kernels.referenceTransition j h).w out ≠ 0

def FullRunProbability (D : LateData hPT) {δ εterm : ℝ}
    (C : TerminalCertificate D δ εterm) (A : ClassSamplerData D δ) (εrun : ℝ) : Prop :=
  (FinLaw.bind (D.encoding.terminalLaw (terminalSet D δ) C.positive)
    (fun x => D.encoding.base.runFull A.act (D.encoding.initialState x))).pr
      (fun z => D.full δ z.1 z.2) ≥ 1 - εrun

structure CompletionCertificate (D : LateData hPT) {δ εterm : ℝ}
    (C : TerminalCertificate D δ εterm) (εrun : ℝ) where
  samplers : ClassSamplerData D δ
  fullRun : FullRunProbability D C samplers εrun

end HypercubeRamsey.S18
