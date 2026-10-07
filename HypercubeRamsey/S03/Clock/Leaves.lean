import HypercubeRamsey.S03.Clock.Exploration
import HypercubeRamsey.S03.Clock.Leaves_p_clock_r2

/-!
# Product-rectangle exploration leaves

A leaf records, per row-label edge, either no inspection, a no-arrival condition through a horizon, or the
exact arrival tick and mark. Its event is therefore a product rectangle in the independent edge-clock data.
The active-endpoint fields encode the exploration dependency graph used for the lopsided coupling.
-/

namespace HypercubeRamsey.Clock

open scoped BigOperators

/-- One coordinate condition in an exploration leaf. -/
inductive EdgeConstraint (T : ℕ) (α : Type*) where
  | unrestricted : EdgeConstraint T α
  | absentBefore (horizon : Fin (T + 1)) : EdgeConstraint T α
  | exactArrival (tick : Fin T) (mark : α) : EdgeConstraint T α
  deriving DecidableEq

/-- Whether a clock value satisfies one coordinate condition. -/
def EdgeConstraint.Allows {T : ℕ} {α : Type*}
    (C : EdgeConstraint T α) (x : MeshClockValue T α) : Prop :=
  match C, x with
  | .unrestricted, _ => True
  | .absentBefore _, .noArrival => True
  | .absentBefore h, .tick t _ => h.val ≤ t.val
  | .exactArrival t a, x => x = .tick t a

/-- Whether this constraint records an inspection of the edge. -/
def EdgeConstraint.inspected {T : ℕ} {α : Type*} : EdgeConstraint T α → Prop
  | .unrestricted => False
  | .absentBefore _ => True
  | .exactArrival _ _ => True

/-- Whether this constraint records a hit. -/
def EdgeConstraint.isHit {T : ℕ} {α : Type*} : EdgeConstraint T α → Prop
  | .exactArrival _ _ => True
  | _ => False

/-- A rectangle leaf, together with its active endpoints. -/
structure ClockLeaf (T : ℕ) (R : Type*) (g : ℕ) (Ω : R → Type*) where
  constraint : ∀ e : RowLabel R g, EdgeConstraint T (Ω e.1)
  active : Finset (Endpoint R g)
  inspected_touches_active : ∀ e, (constraint e).inspected →
    Sum.inl e.1 ∈ active ∨ Sum.inr e.2 ∈ active
  hits_activate_both : ∀ e, (constraint e).isHit →
    Sum.inl e.1 ∈ active ∧ Sum.inr e.2 ∈ active

/-- The cylinder event specified by a leaf. -/
def ClockLeaf.Event {T : ℕ} {R : Type*} {g : ℕ} {Ω : R → Type*}
    (L : ClockLeaf T R g Ω) (ξ : ClockField T R g Ω) : Prop :=
  ∀ e, (L.constraint e).Allows (ξ e)

/-- The leaf event is explicitly a product of one-edge coordinate conditions. -/
theorem clockLeaf_rect {T : ℕ} {R : Type*} {g : ℕ} {Ω : R → Type*}
    (L : ClockLeaf T R g Ω) (ξ : ClockField T R g Ω) :
    L.Event ξ ↔ ∀ e, (L.constraint e).Allows (ξ e) := Iff.rfl

/-- Two leaves are nonneighbors when their active endpoint sets are disjoint. -/
def ClockLeaf.Nonneighbor {T : ℕ} {R : Type*} {g : ℕ} {Ω : R → Type*}
    (L L' : ClockLeaf T R g Ω) : Prop := Disjoint L.active L'.active

/-- Avoid every leaf in a finite family. -/
def avoidsLeaves {T : ℕ} {R : Type*} {g : ℕ} {Ω : R → Type*}
    (leaves : List (ClockLeaf T R g Ω)) (ξ : ClockField T R g Ω) : Prop :=
  ∀ L, L ∈ leaves → ¬ L.Event ξ

/-- For a finite product of mesh clocks, forcing a positive leaf cannot increase the probability of avoiding
any finite family of nonneighbor leaves. The coupling delays clocks on shared absence coordinates. -/
theorem leaf_forcing_coupling {T : ℕ} {R : Type*} [Fintype R] [DecidableEq R]
    {g : ℕ} {Ω : R → Type*} [∀ a, Fintype (Ω a)] [∀ a, DecidableEq (Ω a)]
    (edgeLaw : ∀ e : RowLabel R g, FinProb (MeshClockValue T (Ω e.1)))
    (L : ClockLeaf T R g Ω) (bad : List (ClockLeaf T R g Ω))
    (hpositive : 0 < (clockFieldLaw edgeLaw).pr L.Event)
    (hnonneighbor : ∀ L' ∈ bad, L.Nonneighbor L') :
    (clockFieldLaw edgeLaw).pr (fun ξ => L.Event ξ ∧ avoidsLeaves bad ξ) /
      (clockFieldLaw edgeLaw).pr L.Event ≤
        (clockFieldLaw edgeLaw).pr (avoidsLeaves bad) := by
  classical
  let allowed : ∀ e : RowLabel R g, MeshClockValue T (Ω e.1) → Prop :=
    fun e x => (L.constraint e).Allows x
  have hpositive' :
      0 < (FinProb.pi edgeLaw).pr (fun ξ => ∀ e : RowLabel R g, allowed e (ξ e)) := by
    change 0 < (clockFieldLaw edgeLaw).pr L.Event
    exact hpositive
  have hrectProb : (clockFieldLaw edgeLaw).pr L.Event =
      ∏ e : RowLabel R g, (edgeLaw e).pr (allowed e) := by
    change (FinProb.pi edgeLaw).pr (fun ξ => ∀ e : RowLabel R g, allowed e (ξ e)) = _
    exact FinProb.pi_pr_forall edgeLaw allowed
  have hrectPos :
      0 < ∏ e : RowLabel R g, (edgeLaw e).pr (allowed e) := by
    rw [← hrectProb]
    change 0 < (FinProb.pi edgeLaw).pr (fun ξ => ∀ e : RowLabel R g, allowed e (ξ e))
    exact hpositive'
  have hallowedPos (e : RowLabel R g) : 0 < (edgeLaw e).pr (allowed e) := by
    by_contra hnot
    have hnonneg : 0 ≤ (edgeLaw e).pr (allowed e) :=
      FinProb.pr_nonneg (edgeLaw e) (allowed e)
    have heq : (edgeLaw e).pr (allowed e) = 0 := le_antisymm (le_of_not_gt hnot) hnonneg
    have hzeroProduct : (∏ e' : RowLabel R g, (edgeLaw e').pr (allowed e')) = 0 :=
      Finset.prod_eq_zero (Finset.mem_univ e) heq
    rw [hzeroProduct] at hrectPos
    exact (lt_irrefl 0) hrectPos
  let conditioned : ∀ e : RowLabel R g, FinProb (MeshClockValue T (Ω e.1)) :=
    fun e => (edgeLaw e).cond (allowed e) (hallowedPos e)
  have hconditioned :
      (clockFieldLaw edgeLaw).cond L.Event hpositive = FinProb.pi conditioned := by
    change (FinProb.pi edgeLaw).cond (fun ξ => ∀ e : RowLabel R g, allowed e (ξ e)) hpositive' =
      FinProb.pi conditioned
    exact FinProb.pi_cond_forall edgeLaw allowed hallowedPos hpositive'
  let delay : ∀ e : RowLabel R g,
      MeshClockValue T (Ω e.1) → MeshClockValue T (Ω e.1) → MeshClockValue T (Ω e.1) :=
    fun e x y =>
      match L.constraint e with
      | .unrestricted => x
      | .absentBefore h =>
          if allowed e x then x else if allowed e y then y else .noArrival
      | .exactArrival t a => .tick t a
  have hdelayStay (e : RowLabel R g) (x y : MeshClockValue T (Ω e.1))
      (hx : allowed e x) : delay e x y = x := by
    cases hc : L.constraint e with
    | unrestricted => simp [delay, hc, EdgeConstraint.Allows]
    | absentBefore h =>
        have hx' : (EdgeConstraint.absentBefore h).Allows x := by simpa [allowed, hc] using hx
        simp [delay, hc, allowed, hx']
    | exactArrival t a =>
        have hx' : x = .tick t a := by
          simpa [allowed, hc, EdgeConstraint.Allows] using hx
        simp [delay, hc, hx']
  have hdelayNext (e : RowLabel R g) (x y : MeshClockValue T (Ω e.1))
      (hx : ¬ allowed e x) (hy : allowed e y) : delay e x y = y := by
    cases hc : L.constraint e with
    | unrestricted =>
        have hx' : allowed e x := by simp [allowed, hc, EdgeConstraint.Allows]
        exact False.elim (hx hx')
    | absentBefore h =>
        have hx' : ¬ (EdgeConstraint.absentBefore h).Allows x := by simpa [allowed, hc] using hx
        have hy' : (EdgeConstraint.absentBefore h).Allows y := by simpa [allowed, hc] using hy
        simp [delay, hc, allowed, hx', hy']
    | exactArrival t a =>
        have hy' : y = .tick t a := by
          simpa [allowed, hc, EdgeConstraint.Allows] using hy
        simp [delay, hc, hy']
  have hdelayLaw (e : RowLabel R g) :
      FinProb.map (FinProb.bind (edgeLaw e) (fun _ => conditioned e)) (fun xy => delay e xy.1 xy.2) =
        conditioned e := by
    exact FinProb.map_bind_condition_delay (edgeLaw e) (allowed e) (hallowedPos e)
      (delay e) (hdelayStay e) (hdelayNext e)
  have hbaseLaw (e : RowLabel R g) :
      FinProb.map (FinProb.bind (edgeLaw e) (fun _ => conditioned e)) Prod.fst = edgeLaw e := by
    simpa [conditioned] using FinProb.map_bind_fst (edgeLaw e) (conditioned e)
  let PairValue := fun e : RowLabel R g =>
    MeshClockValue T (Ω e.1) × MeshClockValue T (Ω e.1)
  let pairLaw : ∀ e : RowLabel R g, FinProb (PairValue e) := fun e =>
    FinProb.bind (edgeLaw e) (fun _ => conditioned e)
  let pairField := ∀ e : RowLabel R g, PairValue e
  let source : FinProb pairField := FinProb.pi pairLaw
  let baseField : pairField → ClockField T R g Ω := fun z e => (z e).1
  let delayedField : pairField → ClockField T R g Ω := fun z e => delay e (z e).1 (z e).2
  have hpiCongr {p q : ∀ e : RowLabel R g, FinProb (MeshClockValue T (Ω e.1))}
      (h : ∀ e, p e = q e) : FinProb.pi p = FinProb.pi q := by
    apply FinProb.ext
    intro z
    simp only [FinProb.pi]
    apply Finset.prod_congr rfl
    intro e he
    exact congrArg (fun law => law.w (z e)) (h e)
  have hbaseField : FinProb.map source baseField = clockFieldLaw edgeLaw := by
    have hpi := FinProb.map_pi
      (instFun := (inferInstance : DecidableEq (ClockField T R g Ω))) pairLaw
      (fun e xy => xy.1)
    change FinProb.map (FinProb.pi pairLaw) (fun z e => (z e).1) = FinProb.pi edgeLaw
    calc
      FinProb.map (FinProb.pi pairLaw) (fun z e => (z e).1) =
          FinProb.pi (fun e => FinProb.map (pairLaw e) Prod.fst) := hpi
      _ = FinProb.pi edgeLaw := hpiCongr hbaseLaw
  have hdelayedField : FinProb.map source delayedField = FinProb.pi conditioned := by
    change FinProb.map (FinProb.pi pairLaw) (fun z e => delay e (z e).1 (z e).2) =
      FinProb.pi conditioned
    have hpi := FinProb.map_pi
      (instFun := (inferInstance : DecidableEq (ClockField T R g Ω))) pairLaw
      (fun e xy => delay e xy.1 xy.2)
    calc
      FinProb.map (FinProb.pi pairLaw) (fun z e => delay e (z e).1 (z e).2) =
          FinProb.pi (fun e => FinProb.map (pairLaw e) (fun xy => delay e xy.1 xy.2)) := hpi
      _ = FinProb.pi conditioned := hpiCongr hdelayLaw
  have hNoCommon (L' : ClockLeaf T R g Ω) (hN : L.Nonneighbor L')
      (v : Endpoint R g) (hv : v ∈ L.active) (hv' : v ∈ L'.active) : False :=
    (Finset.disjoint_left.mp hN) hv hv'
  have hleafEventMono (L' : ClockLeaf T R g Ω) (hN : L.Nonneighbor L')
      (z : pairField) (hevent : L'.Event (baseField z)) :
      L'.Event (delayedField z) := by
    intro e
    have he := hevent e
    cases hc : L.constraint e with
    | unrestricted =>
        simpa [baseField, delayedField, delay, hc] using he
    | exactArrival t a =>
        have hnoInspect : ¬ (L'.constraint e).inspected := by
          intro hInspect
          have hLhit := L.hits_activate_both e (by simp [hc, EdgeConstraint.isHit])
          rcases L'.inspected_touches_active e hInspect with hRow | hLabel
          · exact hNoCommon L' hN (Sum.inl e.1) hLhit.1 hRow
          · exact hNoCommon L' hN (Sum.inr e.2) hLhit.2 hLabel
        have hUnrestricted : L'.constraint e = .unrestricted := by
          cases h' : L'.constraint e with
          | unrestricted => rfl
          | absentBefore h' => exact False.elim (hnoInspect (by simp [h', EdgeConstraint.inspected]))
          | exactArrival t' a' => exact False.elim (hnoInspect (by simp [h', EdgeConstraint.inspected]))
        simp [hUnrestricted, EdgeConstraint.Allows]
    | absentBefore h =>
        have hnoHit : ¬ (L'.constraint e).isHit := by
          intro hHit
          have hLtouch := L.inspected_touches_active e (by simp [hc, EdgeConstraint.inspected])
          have hL'hit := L'.hits_activate_both e hHit
          rcases hLtouch with hRow | hLabel
          · exact hNoCommon L' hN (Sum.inl e.1) hRow hL'hit.1
          · exact hNoCommon L' hN (Sum.inr e.2) hLabel hL'hit.2
        cases hb : L'.constraint e with
        | unrestricted => simp [EdgeConstraint.Allows]
        | exactArrival t a =>
            have hHit : (L'.constraint e).isHit := by simp [hb, EdgeConstraint.isHit]
            exact False.elim (hnoHit hHit)
        | absentBefore k =>
            have hbaseK : (EdgeConstraint.absentBefore k).Allows ((z e).1) := by
              simpa [hb] using he
            change (EdgeConstraint.absentBefore k).Allows (delay e (z e).1 (z e).2)
            by_cases hx : allowed e ((z e).1)
            · rw [hdelayStay e (z e).1 (z e).2 hx]
              exact hbaseK
            · cases hbaseVal : (z e).1 with
              | noArrival => exact False.elim (hx (by simp [allowed, hc, hbaseVal, EdgeConstraint.Allows]))
              | tick s a =>
                have hnotH : ¬ h.val ≤ s.val := by
                  simpa [allowed, hc, hbaseVal, EdgeConstraint.Allows] using hx
                have hK : k.val ≤ s.val := by
                  simpa [hbaseVal, EdgeConstraint.Allows] using hbaseK
                have hKh : k.val < h.val := by omega
                have hxTick : ¬ allowed e (MeshClockValue.tick s a) := by
                  simpa [hbaseVal] using hx
                by_cases hy : allowed e ((z e).2)
                · rw [hdelayNext e (MeshClockValue.tick s a) (z e).2 hxTick hy]
                  cases hyVal : (z e).2 with
                  | noArrival => simp [EdgeConstraint.Allows]
                  | tick t b =>
                    have hHt : h.val ≤ t.val := by
                      simpa [allowed, hc, hyVal, EdgeConstraint.Allows] using hy
                    have hKt : k.val ≤ t.val := by omega
                    simpa [hyVal, EdgeConstraint.Allows] using hKt
                · have hyAbs : ¬ (EdgeConstraint.absentBefore h).Allows (z e).2 := by
                    simpa [allowed, hc] using hy
                  have hd : delay e (MeshClockValue.tick s a) (z e).2 = .noArrival := by
                    simp only [delay, hc]
                    simp [allowed, hc, hxTick, hyAbs]
                  rw [hd]
                  simp [EdgeConstraint.Allows]
  have havoidMono : ∀ z : pairField,
      avoidsLeaves bad (delayedField z) → avoidsLeaves bad (baseField z) := by
    intro z hz L' hmem
    intro hbase
    have he := hleafEventMono L' (hnonneighbor L' hmem) z hbase
    exact (hz L' hmem) he
  have hprobMono : source.pr (fun z => avoidsLeaves bad (delayedField z)) ≤
      source.pr (fun z => avoidsLeaves bad (baseField z)) := by
    unfold FinProb.pr
    apply Finset.sum_le_sum
    intro z hz
    by_cases hleft : avoidsLeaves bad (delayedField z)
    · have hright := havoidMono z hleft
      simp [hleft, hright]
    · by_cases hright : avoidsLeaves bad (baseField z)
      · simp only [if_neg hleft, if_pos hright]
        exact source.nonneg z
      · simp [hleft, hright]
  have hcompared : FinProb.pr ((clockFieldLaw edgeLaw).cond L.Event hpositive)
      (avoidsLeaves bad) ≤ (clockFieldLaw edgeLaw).pr (avoidsLeaves bad) := by
    calc
      FinProb.pr ((clockFieldLaw edgeLaw).cond L.Event hpositive) (avoidsLeaves bad) =
          (FinProb.map source delayedField).pr (avoidsLeaves bad) := by
        rw [hconditioned, ← hdelayedField]
      _ = source.pr (fun z => avoidsLeaves bad (delayedField z)) :=
          FinProb.map_pr source delayedField (avoidsLeaves bad)
      _ ≤ source.pr (fun z => avoidsLeaves bad (baseField z)) := hprobMono
      _ = (FinProb.map source baseField).pr (avoidsLeaves bad) :=
          (FinProb.map_pr source baseField (avoidsLeaves bad)).symm
      _ = (clockFieldLaw edgeLaw).pr (avoidsLeaves bad) := by rw [hbaseField]
  have hcondPr := FinProb.cond_pr (clockFieldLaw edgeLaw) L.Event (avoidsLeaves bad) hpositive
  rw [hcondPr] at hcompared
  exact hcompared

end HypercubeRamsey.Clock
