import HypercubeRamsey.S18.Lists

namespace HypercubeRamsey.S18
open Classical
open scoped BigOperators
variable {κ : CConsts} {T : Stage} {k : ℕ} {PT : ProfiledTiling κ T k} {hPT : PT.Valid}

namespace LateData
variable (D : LateData hPT)

/-- External tests singly, the nonempty internal batch last; also move each
external test to the end. No permutations other than the stated orders. -/
noncomputable def testOrders (b : Pos T k) : List (List (Finset (Fin (T.S.n k)))) :=
  let intern := PT.tiling.Icoord (D.geom.patchOf b)
  let extern := Finset.univ \ intern
  let base := extern.toList.map (fun a => {a}) ++ (if intern = ∅ then [] else [intern])
  base :: extern.toList.map (fun a => base.filter (fun B => B ≠ {a}) ++ [{a}])
noncomputable def prefixTests (D : LateData hPT) (order : List (Finset (Fin (T.S.n k)))) (q : ℕ) :=
  (order.take q).foldl (fun A B => A ∪ B) ∅
noncomputable def sketchHit {b : Pos T k} (side : D.encoding.base.RowOut b)
    (a : Fin (T.S.n k)) (y : Fin (T.S.N k)) : ℝ :=
  (∑ t, if Hits (T.S.E k) PT.tiling.c (side.2.1 a t) y then (1 : ℝ) else 0) /
    sketchLength T k
noncomputable def maskWeight {b : Pos T k} (side : D.encoding.base.RowOut b)
    (y : Fin (T.S.N k)) : ℝ := if y ∈ side.1.1 then 1 / (side.1.1.card : ℝ) else 0
noncomputable def passes (j : Fin D.geom.r) {b : Pos T k}
    (side : D.encoding.base.RowOut b) (tests : Finset (Fin (T.S.n k))) (y : Fin (T.S.N k)) : Prop :=
  ∀ a ∈ tests, 1 / 2 - D.error (flipPos b a) j ≤ D.sketchHit side a y
noncomputable def retainedMass (j : Fin D.geom.r) {b : Pos T k}
    (side : D.encoding.base.RowOut b) (tests : Finset (Fin (T.S.n k))) : ℝ :=
  ∑ y, if D.passes j side tests y then D.maskWeight side y else 0
noncomputable def labelWeight (j : Fin D.geom.r) {b : Pos T k}
    (side : D.encoding.base.RowOut b) (tests : Finset (Fin (T.S.n k))) (y : Fin (T.S.N k)) : ℝ :=
  if Real.exp (-(κ.α / 100) * (T.S.n k : ℝ)) ≤ D.retainedMass j side tests then
    if D.passes j side tests y then D.maskWeight side y / D.retainedMass j side tests else 0
  else D.maskWeight side y
noncomputable def R1 (j : Fin D.geom.r) {b : Pos T k} (side : D.encoding.base.RowOut b) : Prop :=
  ∀ a, (∑ t, ∑ u, if ¬ D.nonconflict (flipPos b a) (side.2.1 a t) (side.2.1 a u)
    then (1 : ℝ) else 0) / (sketchLength T k : ℝ) ^ 2 ≤ 2 * D.error (flipPos b a) j ^ 4
noncomputable def prefixMoments (j : Fin D.geom.r) {b : Pos T k}
    (h : D.encoding.base.History j.castSucc) (side : D.encoding.base.RowOut b)
    (order : List (Finset (Fin (T.S.n k)))) (q : ℕ) (a : Fin (T.S.n k)) : Prop :=
  let w := flipPos b a
  let tests := D.prefixTests order q
  let mass := D.retainedMass j side tests
  Real.exp (-(κ.α / 100) * (T.S.n k : ℝ)) ≤ mass →
    (∀ x, (D.initialPrior w h.1).w x ≠ 0 →
      |(∑ y, (if D.passes j side tests y ∧ Hits (T.S.E k) PT.tiling.c x y
        then D.maskWeight side y else 0)) / mass - 1 / 2| ≤ 10 * bstar T k) ∧
    (∀ x z, (D.initialPrior w h.1).w x ≠ 0 → (D.initialPrior w h.1).w z ≠ 0 →
      D.nonconflict w x z →
      |(∑ y, (if D.passes j side tests y ∧ Hits (T.S.E k) PT.tiling.c x y ∧
        Hits (T.S.E k) PT.tiling.c z y then D.maskWeight side y else 0)) / mass - 1 / 4| ≤
          10 * bstar T k)
noncomputable def R2 (j : Fin D.geom.r) {b : Pos T k}
    (h : D.encoding.base.History j.castSucc) (side : D.encoding.base.RowOut b) : Prop :=
  ∀ order ∈ D.testOrders b, ∀ q, q < order.length → ∀ a ∈ order.getD q ∅,
    D.prefixMoments j h side order q a
noncomputable def R3 (j : Fin D.geom.r) {b : Pos T k}
    (h : D.encoding.base.History j.castSucc) (side : D.encoding.base.RowOut b) : Prop :=
  ∀ a, 1 / 2 - 3 * D.error (flipPos b a) j ≤
    colDeg (T.S.E k) PT.tiling.c (D.currentPrior j (flipPos b a) h) (D.encoding.base.rowLabel side)

/-- Exactly the deletions specified by the paper: one external test or the
whole internal batch, with the actual mask/sketch side data unchanged. -/
noncomputable def deletionConclusion (j : Fin D.geom.r) {b : Pos T k}
    (side : D.encoding.base.RowOut b) : Prop :=
  ∀ a : Fin (T.S.n k),
    let intern := PT.tiling.Icoord (D.geom.patchOf b)
    let omitted := if a ∈ intern then intern else {a}
    let l := if a ∈ intern then (PT.tiling.P (D.geom.patchOf b)).h else 1
    ∀ y, D.labelWeight j side Finset.univ y ≤
      Real.exp (1000 * (l : ℝ) * D.error (flipPos b a) j) *
        D.labelWeight j side (Finset.univ \ omitted) y
noncomputable def gate (j : Fin D.geom.r) (b : Pos T k)
    (h : D.encoding.base.History j.castSucc) : Prop :=
  (∀ w ∈ cubeBall b (6 * D.geom.r), IsEvenRole w → D.initialValid w h.1) ∧
  (∀ s : Fin D.geom.r, ∀ hs : s.val < j.val,
    ∀ b' : {x : Pos T k // x ∈ D.encoding.base.classes s}, b'.1 ∈ cubeBall b (6 * D.geom.r) →
      D.R3 s (D.beforeHistory h s.castSucc (Nat.le_of_lt hs)) (D.pastRows h s hs b') ∧
      D.deletionConclusion s (D.pastRows h s hs b'))

end LateData

/-- Construction specification for the product row experiment, not a freely
chosen event table. Its full weight fixes masks, iid sketches and label draws. -/
structure TransitionData (D : LateData hPT) : Prop where
  reference_formula : ∀ j b h out,
    (D.encoding.kernels.refK j b h).w out =
      (D.encoding.kernels.maskProfile b.1).w out.1 *
      (∏ a, ∏ t, (D.currentPrior j (flipPos b.1 a) h).w (out.2.1 a t)) *
      D.labelWeight j out Finset.univ (D.encoding.base.rowLabel out)

/-- One fixed Requirement-2 failure, with its actual order, prefix and target. -/
abbrev PrefixIndex (D : LateData hPT) :=
  Σ j : Fin D.geom.r, {b : Pos T k // b ∈ D.encoding.base.classes j} ×
    Fin (T.S.n k + 1) × Fin (T.S.n k + 1) × Fin (T.S.n k)
noncomputable instance (D : LateData hPT) : Fintype (PrefixIndex D) := inferInstance
namespace LateData
variable (D : LateData hPT)
noncomputable def prefixOrder (f : PrefixIndex D) := (D.testOrders f.2.1.1).getD f.2.2.1.val []
noncomputable def prefixValid (f : PrefixIndex D) : Prop :=
  f.2.2.1.val < (D.testOrders f.2.1.1).length ∧ f.2.2.2.1.val < (D.prefixOrder f).length ∧
    f.2.2.2.2 ∈ (D.prefixOrder f).getD f.2.2.2.1.val ∅
noncomputable def prefixFailure (f : PrefixIndex D)
    (h : D.encoding.base.History (Fin.last D.geom.r)) : Prop :=
  D.prefixValid f ∧ D.gate f.1 f.2.1.1 (D.beforeHistory h f.1.castSucc (Nat.le_of_lt f.1.isLt)) ∧
    ¬ D.prefixMoments f.1 (D.beforeHistory h f.1.castSucc (Nat.le_of_lt f.1.isLt))
      (D.pastRows h f.1 f.1.isLt f.2.1) (D.prefixOrder f) f.2.2.2.1.val f.2.2.2.2
end LateData

/-- Kind 0 = sketch, 1 = this prefix, 2 = true-hit failure. Redundant indices
for kinds 0 and 2 only repeat the same actual row event. -/
abbrev LateEvent (D : LateData hPT) := Fin 3 × PrefixIndex D
noncomputable def lateFailure (D : LateData hPT) (f : LateEvent D)
    (h : D.encoding.base.History (Fin.last D.geom.r)) : Prop :=
  let p := f.2
  let before := D.beforeHistory h p.1.castSucc (Nat.le_of_lt p.1.isLt)
  let out := D.pastRows h p.1 p.1.isLt p.2.1
  D.gate p.1 p.2.1.1 before ∧
    (if f.1.val = 0 then ¬ D.R1 p.1 out else if f.1.val = 1 then D.prefixFailure p h
    else D.R1 p.1 out ∧ D.R2 p.1 before out ∧ ¬ D.R3 p.1 before out)

def CurrentListCapFacts (D : LateData hPT) : Prop :=
  ∀ j b h, D.gate j b h → b ∈ D.encoding.base.classes j → ∀ a x,
    (D.currentPrior j (flipPos b a) h).w x ≤ 8 * κ.KB / densityScale T k *
      Real.exp (-199 * PT.tiling.gain (D.geom.patchOf (flipPos b a))) *
        Real.rpow 2 (-(D.remainingNeighbors (flipPos b a) j : ℝ))

/-- The sketch labels of a side output lie in the initial-prior support. The paper samples sketches from the
current prior (18:89–108), which on the gate lies in the initial support; R2's moments apply only there (18:195–204). -/
def InitialSketchSupport (D : LateData hPT) (j : Fin D.geom.r) {b : Pos T k}
    (h : D.encoding.base.History j.castSucc) (side : D.encoding.base.RowOut b) : Prop :=
  ∀ a t, (D.initialPrior (flipPos b a) h.1).w (side.2.1 a t) ≠ 0

/-- eq. (27) is carried explicitly as well as broadness and deletion, for side outputs whose sketches are supported
(`InitialSketchSupport`; without it the variance step fails, see lane sol-s18-1b). -/
def BroadDeletionFacts (D : LateData hPT) (K27 : ℝ) : Prop :=
  ∀ (j : Fin D.geom.r) (b : Pos T k) (h : D.encoding.base.History j.castSucc)
    (side : D.encoding.base.RowOut b), b ∈ D.encoding.base.classes j → D.gate j b h →
    InitialSketchSupport D j h side → D.R1 j side → D.R2 j h side →
    (∀ order ∈ D.testOrders b, ∀ q, q ≤ order.length →
      Real.exp (-(κ.α / 100) * (T.S.n k : ℝ)) ≤ D.retainedMass j side (D.prefixTests order q)) ∧
    D.deletionConclusion j side ∧
    (∀ a x, (D.initialPrior (flipPos b a) h.1).w x ≠ 0 →
      let l := if a ∈ PT.tiling.Icoord (D.geom.patchOf b) then (PT.tiling.P (D.geom.patchOf b)).h else 1
      (∑ y, if Hits (T.S.E k) PT.tiling.c x y then D.labelWeight j side Finset.univ y else 0) ≤
        (1 / 2) * Real.exp (K27 * l * D.error (flipPos b a) j)) ∧
    (∀ a x z, (D.initialPrior (flipPos b a) h.1).w x ≠ 0 →
      (D.initialPrior (flipPos b a) h.1).w z ≠ 0 → D.nonconflict (flipPos b a) x z →
      let l := if a ∈ PT.tiling.Icoord (D.geom.patchOf b) then (PT.tiling.P (D.geom.patchOf b)).h else 1
      (∑ y, if Hits (T.S.E k) PT.tiling.c x y ∧ Hits (T.S.E k) PT.tiling.c z y
        then D.labelWeight j side Finset.univ y else 0) ≤
          (1 / 4) * Real.exp (K27 * l * D.error (flipPos b a) j))

def LocalTransitionFacts (D : LateData hPT) (K27 : ℝ) : Prop :=
  CurrentListCapFacts D ∧ BroadDeletionFacts D K27 ∧
  (∀ j b h, D.gate j b.1 h → (D.encoding.kernels.refK j b h).pr (fun out => ¬ D.R1 j out) ≤
    Real.exp (-Real.rpow (T.S.n k : ℝ) 0.04)) ∧
  (∀ j b h, D.gate j b.1 h → (D.encoding.kernels.refK j b h).pr
    (fun out => D.R1 j out ∧ D.R2 j h out ∧ ¬ D.R3 j h out) ≤
      Real.exp (-Real.rpow (T.S.n k : ℝ) 0.04))

/-- Balance means the filtered label marginal under the *full iid-slot
initial process and reference run*, not uniform mass within a mask. -/
def MaskBalance (D : LateData hPT) : Prop :=
  ∀ j b y, (D.encoding.baseline).pr (fun z =>
    D.encoding.base.rowLabel (D.pastRows z.2 j j.isLt b) = y) ≤
      2 / (D.encoding.base.latePool j).card

end HypercubeRamsey.S18
