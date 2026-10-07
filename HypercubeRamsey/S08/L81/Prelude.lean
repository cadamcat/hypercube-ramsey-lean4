import HypercubeRamsey.Framework.FinProb
import HypercubeRamsey.Framework.FinProbLemmas
import HypercubeRamsey.S08.L81.Prelude_q_s08_trim
import HypercubeRamsey.S03.ConditionalAvoidance

/-!
# Lemma 8.1: finite-probability helpers

Normalized laws with a fallback (`normOr`), conditioning with a fallback (`condOr`), and the local-lemma interface on
a product law (`LLLInput`, `CondProductBound`, Lemma 3.4 with independent variables).  The last two have the same
form as the Section 7 re-split (`S07/Experiment.lean` on branch `lane/opus-s07`); the coordinator may unify them.
-/

namespace HypercubeRamsey.S08

open Classical
open HypercubeRamsey.LocalLemma
open scoped BigOperators

/-- Normalize a nonnegative weight; the law `P` when the total mass is zero. -/
noncomputable def normOr {Ω : Type*} [Fintype Ω] (f : Ω → ℝ) (hf : ∀ ω, 0 ≤ f ω) (P : FinProb Ω) :
    FinProb Ω where
  w ω := if ∑ ω', f ω' = 0 then P.w ω else f ω / ∑ ω', f ω'
  nonneg ω := by
    by_cases h : ∑ ω', f ω' = 0
    · simp only [h, ↓reduceIte]; exact P.nonneg ω
    · simp only [h, ↓reduceIte]; exact div_nonneg (hf ω) (Finset.sum_nonneg fun ω' _ => hf ω')
  sum_eq_one := by
    by_cases h : ∑ ω', f ω' = 0
    · simp only [h, ↓reduceIte]; exact P.sum_eq_one
    · simp only [h, ↓reduceIte]; rw [← Finset.sum_div]; exact div_self h

/-- Conditioning on an event, keeping the law when the event has mass zero. -/
noncomputable def condOr {Ω : Type*} [Fintype Ω] (P : FinProb Ω) (A : Ω → Prop) : FinProb Ω :=
  if h : 0 < P.pr A then P.cond A h else P

/-- Probabilities are nonnegative. -/
theorem pr_nonneg {Ω : Type*} [Fintype Ω] (P : FinProb Ω) (A : Ω → Prop) : 0 ≤ P.pr A := by
  classical
  unfold FinProb.pr
  exact Finset.sum_nonneg fun ω _ => by split_ifs <;> simp [P.nonneg ω]

/-- Replace the coordinates in `U` of `ω` by `a`. -/
noncomputable def glue {V : Type*} {α : V → Type*} (U : Finset V) (ω : ∀ v, α v) (a : ∀ v : U, α v) :
    ∀ v, α v :=
  fun v => by classical exact if h : v ∈ U then a ⟨v, h⟩ else ω v

/-- Local-lemma input on a product law (Lemma 3.4 with independent variables): scopes, dependency degree at
most `Δ` (events adjacent when their scopes meet), and probabilities at most `x (1 - x)^Δ`. -/
structure LLLInput {V : Type} [Fintype V] [DecidableEq V] {α : V → Type} [∀ v, Fintype (α v)]
    (P : ∀ v, FinProb (α v)) {I : Type} [Fintype I] (Bad : I → (∀ v, α v) → Prop)
    (sc : I → Finset V) (x : ℝ) (Δ : ℕ) : Prop where
  x_nonneg : 0 ≤ x
  x_lt_one : x < 1
  scope : ∀ i, FinProb.DependsOn (Bad i) (sc i)
  degree : ∀ i, (Finset.univ.filter fun j => j ≠ i ∧ ¬ Disjoint (sc i) (sc j)).card ≤ Δ
  prob : ∀ i, (FinProb.pi P).pr (Bad i) ≤ x * (1 - x) ^ Δ

/-- Conditional avoidance on a product law with free coordinates (Lemma 3.4 and its independent-variables case):
the avoidance event has positive mass, and conditioning on it costs at most `(1 - x)^{-#T}` against any bound `B`
for the integral over the coordinates `U`, where `T` is the set of events whose scopes meet `U`. -/
def CondProductBound : Prop :=
  ∀ {V : Type} [Fintype V] [DecidableEq V] {α : V → Type} [∀ v, Fintype (α v)]
    [∀ v, DecidableEq (α v)] (P : ∀ v, FinProb (α v)) {I : Type} [Fintype I] [DecidableEq I]
    (Bad : I → (∀ v, α v) → Prop) (sc : I → Finset V) (x : ℝ) (Δ : ℕ),
    LLLInput P Bad sc x Δ →
      0 < (FinProb.pi P).pr (fun ω => ∀ i, ¬ Bad i ω) ∧
      ∀ (U : Finset V) (Φ : (∀ v, α v) → ℝ), (∀ ω, 0 ≤ Φ ω) → ∀ B : ℝ,
        (∀ ω, ∑ a : (∀ v : U, α v), (∏ v : U, (P v).w (a v)) * Φ (glue U ω a) ≤ B) →
        (condOr (FinProb.pi P) (fun ω => ∀ i, ¬ Bad i ω)).expect Φ ≤
          ((1 - x) ^ (Finset.univ.filter fun i => ¬ Disjoint (sc i) U).card)⁻¹ * B

set_option maxHeartbeats 1000000

/-- SHARED (Lemma 3.4, `S03/ConditionalAvoidance.lean`, independent-variables case; same statement as the
Section 7 node `S07.cond_product_bound`): with events joined when their scopes meet, the avoidance event has
positive mass; removing the events whose scopes meet `U` costs `∏ (1 - x)^{-1}`, and the remaining events do
not read the coordinates in `U`. -/
theorem cond_product_bound : CondProductBound := by
  classical
  intro V _ _ α _ _ P I _ _ Bad sc x Δ hI
  let w : (∀ v, α v) → ℝ := fun ω => ∏ v, (P v).w (ω v)
  let Ev : I → Finset (∀ v, α v) := fun i => Finset.univ.filter (Bad i)
  let adj : I → I → Prop := fun i j => j ≠ i ∧ ¬ Disjoint (sc i) (sc j)
  let pb : I → ℝ := fun i => (FinProb.pi P).pr (Bad i)
  let xx : I → ℝ := fun _ => x
  let Avo (S : Finset I) : (∀ v, α v) → Prop := fun ω => ∀ i ∈ S, ¬ Bad i ω
  let q : ∀ v, α v → ℝ := fun v a => (P v).w a
  letI : DecidableRel adj := Classical.decRel _
  have hw0 : ∀ ω, 0 ≤ w ω := by
    intro ω
    exact Finset.prod_nonneg fun v _ => (P v).nonneg (ω v)
  have hw1 : (∑ ω, w ω) = 1 := by
    simpa [w, FinProb.pi] using (FinProb.pi P).sum_eq_one
  have hq0 : ∀ v a, 0 ≤ q v a := fun v a => (P v).nonneg a
  have hq1 : ∀ v, ∑ a, q v a = 1 := fun v => (P v).sum_eq_one
  have hprobEq (i : I) : mass w (Ev i) = pb i := by
    simp [mass, Ev, pb, w, FinProb.pr, FinProb.pi, Finset.sum_filter]
  have hscope (i : I) (ω ω' : ∀ v, α v)
      (heq : ∀ v ∈ sc i, ω v = ω' v) : (ω ∈ Ev i ↔ ω' ∈ Ev i) := by
    have h := hI.scope i ω ω' heq
    simpa [Ev] using h
  have hadjSymm : ∀ i j, adj i j → adj j i := by
    intro i j hij
    refine ⟨Ne.symm hij.1, ?_⟩
    intro h
    apply hij.2
    apply Finset.disjoint_left.mpr
    intro v hvI hvJ
    exact (Finset.disjoint_left.mp h) hvJ hvI
  have hadjIrr : ∀ i, ¬ adj i i := by
    intro i hi
    exact hi.1 rfl
  have hdisjOfNonadj : ∀ i (S : Finset I), i ∉ S →
      (∀ j ∈ S, ¬ adj i j) → ∀ j ∈ S, Disjoint (sc i) (sc j) := by
    intro i S hi hnon j hj
    by_contra hdis
    have hji : j ≠ i := by
      intro hji
      apply hi
      simpa [hji] using hj
    exact hnon j hj ⟨hji, hdis⟩
  have hind (i : I) (S : Finset I) (hi : i ∉ S)
      (hnon : ∀ j ∈ S, ¬ adj i j) :
      mass w (Ev i ∩ avoid Ev S) = pb i * mass w (avoid Ev S) := by
    calc
      mass w (Ev i ∩ avoid Ev S) =
          mass w (Ev i ∩ avoid Ev S) := rfl
      _ = mass w (Ev i) * mass w (avoid Ev S) :=
        mass_inter_avoid_of_disjoint_scopes q hq0 hq1 Ev sc hscope i S
          (hdisjOfNonadj i S hi hnon)
      _ = pb i * mass w (avoid Ev S) := by rw [hprobEq]
  have hprobBound (i : I) : pb i ≤ x * (1 - x) ^ Δ := by
    change (FinProb.pi P).pr (Bad i) ≤ x * (1 - x) ^ Δ
    exact hI.prob i
  have hneighbors (i : I) : (Finset.univ.filter (adj i)).card ≤ Δ := by
    simpa [adj] using hI.degree i
  have hpx : ∀ i, pb i ≤ xx i *
      ∏ j ∈ Finset.univ.filter (adj i), (1 - xx j) := by
    intro i
    have hbase0 : 0 ≤ 1 - x := by linarith [hI.x_lt_one]
    have hbase1 : 1 - x ≤ 1 := by linarith [hI.x_nonneg]
    have hpow : (1 - x) ^ Δ ≤
        (1 - x) ^ (Finset.univ.filter (adj i)).card :=
      pow_le_pow_of_le_one hbase0 hbase1 (hneighbors i)
    have hprod : (∏ j ∈ Finset.univ.filter (adj i), (1 - xx j)) =
        (1 - x) ^ (Finset.univ.filter (adj i)).card := by
      simp [xx, Finset.prod_const]
    calc
      pb i ≤ x * (1 - x) ^ Δ := hprobBound i
      _ ≤ x * (1 - x) ^ (Finset.univ.filter (adj i)).card :=
        mul_le_mul_of_nonneg_left hpow hI.x_nonneg
      _ = xx i * ∏ j ∈ Finset.univ.filter (adj i), (1 - xx j) := by
        rw [hprod]
  have hlocal : ∀ i (S : Finset I), i ∉ S → (∀ j ∈ S, ¬ adj i j) →
      mass w (Ev i ∩ avoid Ev S) ≤ pb i * mass w (avoid Ev S) := by
    intro i S hi hnon
    rw [hind i S hi hnon]
  have hLLL := conditional_avoidance w hw0 hw1 Ev adj hadjSymm hadjIrr
    pb xx hlocal (fun _ => hI.x_nonneg) (fun _ => hI.x_lt_one) hpx
  rcases hLLL with ⟨hAvoidPos, hLLLCond, hLLLCompare, hLLLF⟩
  have hmass (S : Finset I) : mass w (avoid Ev S) =
      (FinProb.pi P).pr (Avo S) := by
    letI : DecidablePred (Avo S) := fun ω => Classical.propDecidable (Avo S ω)
    have havoid : avoid Ev S = Finset.univ.filter (Avo S) := by
      ext ω
      simp [avoid, Ev, Avo]
    rw [havoid]
    unfold mass
    rw [FinProb.pr, Finset.sum_filter]
    apply Finset.sum_congr rfl
    intro ω hω
    change (if Avo S ω then w ω else 0) =
      if Avo S ω then (FinProb.pi P).w ω else 0
    by_cases h : Avo S ω
    · simp [h, w, FinProb.pi]
    · simp [h, w, FinProb.pi]
  have hpos : 0 < (FinProb.pi P).pr (Avo Finset.univ) := by
    rw [← hmass Finset.univ]
    exact hAvoidPos
  refine ⟨?_, ?_⟩
  · simpa [Avo] using hpos
  · intro U Φ hΦ B hFiber
    let S : Finset I := Finset.univ.filter fun i => Disjoint (sc i) U
    let T : Finset I := Finset.univ.filter fun i => ¬ Disjoint (sc i) U
    have hST : Disjoint S T := by
      apply Finset.disjoint_left.mpr
      intro i hiS hiT
      exact (Finset.mem_filter.mp hiT).2 (Finset.mem_filter.mp hiS).2
    have hUnion : S ∪ T = Finset.univ := by
      ext i
      by_cases hi : Disjoint (sc i) U <;> simp [S, T, hi]
    have hSscope : ∀ i ∈ S, Disjoint (sc i) U := by
      intro i hi
      exact (Finset.mem_filter.mp hi).2
    have hAvoidDepends : FinProb.DependsOn (Avo S) (Finset.univ \ U) := by
      intro ω ω' hwEq
      apply propext
      constructor
      · intro hω i hi
        have hcoord : ∀ v ∈ sc i, ω v = ω' v := by
          intro v hv
          have hvU : v ∉ U := by
            intro hvU
            exact (Finset.disjoint_left.mp (hSscope i hi)) hv hvU
          exact hwEq v (Finset.mem_sdiff.mpr ⟨Finset.mem_univ _, hvU⟩)
        have hbadEq := hI.scope i ω ω' hcoord
        simpa [hbadEq] using hω i hi
      · intro hω i hi
        have hcoord : ∀ v ∈ sc i, ω' v = ω v := by
          intro v hv
          have hvU : v ∉ U := by
            intro hvU
            exact (Finset.disjoint_left.mp (hSscope i hi)) hv hvU
          exact (hwEq v (Finset.mem_sdiff.mpr ⟨Finset.mem_univ _, hvU⟩)).symm
        have hbadEq := hI.scope i ω' ω hcoord
        simpa [hbadEq] using hω i hi
    let e := Equiv.piEquivPiSubtypeProd (fun v : V => v ∈ U) α
    have hΩne : Nonempty (∀ v, α v) := by
      by_contra hn
      haveI : IsEmpty (∀ v, α v) := ⟨fun ω => hn ⟨ω⟩⟩
      have hs : (∑ ω, (FinProb.pi P).w ω) = 0 := by simp
      rw [(FinProb.pi P).sum_eq_one] at hs
      norm_num at hs
    obtain ⟨ω₀⟩ := hΩne
    let a₀ : ∀ v : U, α v := fun v => ω₀ v.1
    let ωb (b : ∀ v : {v // v ∉ U}, α v) : ∀ v, α v := e.symm (a₀, b)
    let qU (a : ∀ v : U, α v) : ℝ := ∏ v : U, (P v.1).w (a v)
    let qC (b : ∀ v : {v // v ∉ U}, α v) : ℝ :=
      ∏ v : {v // v ∉ U}, (P v.1).w (b v)
    have hqU : ∑ a, qU a = 1 := by
      simpa [qU, FinProb.pi] using
        (FinProb.pi (fun v : U => P v.1)).sum_eq_one
    have hglue (a : ∀ v : U, α v) (b : ∀ v : {v // v ∉ U}, α v) :
        glue U (ωb b) a = e.symm (a, b) := by
      funext v
      by_cases hv : v ∈ U <;> simp [glue, ωb, e, hv]
    have hAvoidSame (a : ∀ v : U, α v) (b : ∀ v : {v // v ∉ U}, α v) :
        Avo S (e.symm (a, b)) = Avo S (ωb b) := by
      have hout : ∀ v, v ∈ Finset.univ \ U → e.symm (a, b) v = ωb b v := by
        intro v hv
        have hvU : v ∉ U := (Finset.mem_sdiff.mp hv).2
        simp [e, ωb, hvU]
      exact hAvoidDepends (e.symm (a, b)) (ωb b) hout
    have hFiberB (b : ∀ v : {v // v ∉ U}, α v) :
        (∑ a : (∀ v : U, α v), qU a * Φ (e.symm (a, b))) ≤ B := by
      calc
        (∑ a : (∀ v : U, α v), qU a * Φ (e.symm (a, b))) =
            ∑ a : (∀ v : U, α v),
              (∏ v : U, (P v.1).w (a v)) * Φ (glue U (ωb b) a) := by
          apply Finset.sum_congr rfl
          intro a ha
          rw [hglue]
        _ ≤ B := hFiber (ωb b)
    let indicator : (∀ v, α v) → ℝ := fun ω => if Avo S ω then 1 else 0
    have hNumSplit :
        (FinProb.pi P).expect (fun ω => indicator ω * Φ ω) =
          ∑ b : (∀ v : {v // v ∉ U}, α v),
            qC b * indicator (ωb b) *
              (∑ a : (∀ v : U, α v), qU a * Φ (e.symm (a, b))) := by
      rw [FinProb.pi_expect_split_q_s08_trim P U (fun ω => indicator ω * Φ ω)]
      rw [Finset.sum_comm]
      apply Fintype.sum_congr
      intro b
      calc
        (∑ a : (∀ v : U, α v),
          (FinProb.pi (fun v : U => P v.1)).w a * qC b *
            (indicator (e.symm (a, b)) * Φ (e.symm (a, b)))) =
            ∑ a : (∀ v : U, α v),
              (qU a * Φ (e.symm (a, b))) * (qC b * indicator (ωb b)) := by
          apply Finset.sum_congr rfl
          intro a ha
          rw [show indicator (e.symm (a, b)) = indicator (ωb b) by
            simp [indicator, hAvoidSame a b]]
          simp [qU, FinProb.pi]
          ring
        _ = (∑ a : (∀ v : U, α v), qU a * Φ (e.symm (a, b))) *
              (qC b * indicator (ωb b)) := by rw [← Finset.sum_mul]
        _ = qC b * indicator (ωb b) *
              (∑ a : (∀ v : U, α v), qU a * Φ (e.symm (a, b))) := by ring
    have hDenSplit :
        (FinProb.pi P).expect indicator =
          ∑ b : (∀ v : {v // v ∉ U}, α v), qC b * indicator (ωb b) := by
      rw [FinProb.pi_expect_split_q_s08_trim P U indicator]
      rw [Finset.sum_comm]
      apply Fintype.sum_congr
      intro b
      calc
        (∑ a : (∀ v : U, α v),
          (FinProb.pi (fun v : U => P v.1)).w a * qC b * indicator (e.symm (a, b))) =
            (qC b * indicator (ωb b)) * (∑ a : (∀ v : U, α v), qU a) := by
          calc
            _ = ∑ a : (∀ v : U, α v), qU a * (qC b * indicator (ωb b)) := by
              apply Finset.sum_congr rfl
              intro a ha
              rw [show indicator (e.symm (a, b)) = indicator (ωb b) by
                simp [indicator, hAvoidSame a b]]
              simp [qU, FinProb.pi]
              ring
            _ = (∑ a : (∀ v : U, α v), qU a) * (qC b * indicator (ωb b)) := by
              rw [← Finset.sum_mul]
            _ = (qC b * indicator (ωb b)) * (∑ a : (∀ v : U, α v), qU a) := by ring
        _ = qC b * indicator (ωb b) := by rw [hqU, mul_one]
    have hnumSet (F : (∀ v, α v) → ℝ) (S' : Finset I) :
        (FinProb.pi P).expect (fun ω => (if Avo S' ω then 1 else 0) * F ω) =
          ∑ ω ∈ avoid Ev S', w ω * F ω := by
      classical
      unfold FinProb.expect
      change (∑ ω, (FinProb.pi P).w ω * ((if Avo S' ω then 1 else 0) * F ω)) = _
      calc
        (∑ ω, (FinProb.pi P).w ω * ((if Avo S' ω then 1 else 0) * F ω)) =
            ∑ ω, if Avo S' ω then w ω * F ω else 0 := by
          apply Finset.sum_congr rfl
          intro ω hω
          by_cases ha : Avo S' ω <;> simp [w, FinProb.pi, ha]
        _ = ∑ ω ∈ Finset.univ.filter (Avo S'), w ω * F ω := by rw [Finset.sum_filter]
        _ = ∑ ω ∈ avoid Ev S', w ω * F ω := by
          congr 1
          ext ω
          simp [avoid, Ev, Avo]
    have hdenSet (S' : Finset I) :
        (FinProb.pi P).expect (fun ω => if Avo S' ω then 1 else 0) =
          mass w (avoid Ev S') := by
      calc
        (FinProb.pi P).expect (fun ω => if Avo S' ω then 1 else 0) =
            (FinProb.pi P).expect (fun ω => (if Avo S' ω then 1 else 0) * 1) := by simp
        _ = ∑ ω ∈ avoid Ev S', w ω * 1 := hnumSet (fun _ => 1) S'
        _ = mass w (avoid Ev S') := by simp [mass]
    have hnumBound :
        (FinProb.pi P).expect (fun ω => indicator ω * Φ ω) ≤
          B * (FinProb.pi P).expect indicator := by
      rw [hNumSplit, hDenSplit]
      calc
        (∑ b, qC b * indicator (ωb b) *
            (∑ a, qU a * Φ (e.symm (a, b)))) ≤
            ∑ b, B * (qC b * indicator (ωb b)) := by
          apply Finset.sum_le_sum
          intro b hb
          have hqC : 0 ≤ qC b := Finset.prod_nonneg fun v _ => (P v.1).nonneg (b v)
          have hind : 0 ≤ indicator (ωb b) := by
            dsimp [indicator]
            split_ifs <;> norm_num
          calc
            qC b * indicator (ωb b) * (∑ a, qU a * Φ (e.symm (a, b))) ≤
                (qC b * indicator (ωb b)) * B :=
              mul_le_mul_of_nonneg_left (hFiberB b) (mul_nonneg hqC hind)
            _ = B * (qC b * indicator (ωb b)) := by ring
        _ = B * (∑ b, qC b * indicator (ωb b)) := by rw [Finset.mul_sum]
    have hfree :
        (∑ ω ∈ avoid Ev S, w ω * Φ ω) ≤ B * mass w (avoid Ev S) := by
      calc
        (∑ ω ∈ avoid Ev S, w ω * Φ ω) =
            (FinProb.pi P).expect (fun ω => indicator ω * Φ ω) := (hnumSet Φ S).symm
        _ ≤ B * (FinProb.pi P).expect indicator := hnumBound
        _ = B * mass w (avoid Ev S) := by rw [hdenSet S]
    have hmassSpos : 0 < mass w (avoid Ev S) := by
      have hsub : avoid Ev Finset.univ ⊆ avoid Ev S := by
        intro ω hω
        simp only [avoid, Finset.mem_filter] at hω ⊢
        constructor
        · simp
        · intro i hi
          exact hω.2 i (Finset.mem_univ i)
      have hmono : mass w (avoid Ev Finset.univ) ≤ mass w (avoid Ev S) := by
        unfold mass
        exact Finset.sum_le_sum_of_subset_of_nonneg hsub (fun ω _ _ => hw0 ω)
      exact lt_of_lt_of_le hAvoidPos hmono
    have hfreeCond :
        (∑ ω ∈ avoid Ev S, w ω * Φ ω) / mass w (avoid Ev S) ≤ B :=
      (div_le_iff₀ hmassSpos).2 hfree
    have hcmp := hLLLCompare S T hST Φ hΦ
    rw [hUnion] at hcmp
    have hprobPos : 0 < (FinProb.pi P).pr (Avo Finset.univ) := by
      simpa [hmass] using hAvoidPos
    have hcondExpect :
        (condOr (FinProb.pi P) (Avo Finset.univ)).expect Φ =
          (∑ ω ∈ avoid Ev Finset.univ, w ω * Φ ω) /
            mass w (avoid Ev Finset.univ) := by
      have hcondCore (Q : FinProb (∀ v, α v)) (A : (∀ v, α v) → Prop)
          (hA : 0 < Q.pr A) (F : (∀ v, α v) → ℝ) :
          (Q.cond A hA).expect F = Q.condExp F A := by
        classical
        change (∑ ω, ((if A ω then Q.w ω else 0) / Q.pr A) * F ω) =
          (∑ ω, Q.w ω * ((if A ω then 1 else 0) * F ω)) / Q.pr A
        rw [Finset.sum_div]
        apply Finset.sum_congr rfl
        intro ω hω
        by_cases ha : A ω <;> simp [ha] <;> ring
      calc
        (condOr (FinProb.pi P) (Avo Finset.univ)).expect Φ =
            (FinProb.pi P).condExp Φ (Avo Finset.univ) := by
          simpa [condOr, hprobPos] using hcondCore (FinProb.pi P) (Avo Finset.univ) hprobPos Φ
        _ = (FinProb.pi P).expect
              (fun ω => (if Avo Finset.univ ω then 1 else 0) * Φ ω) /
              (FinProb.pi P).pr (Avo Finset.univ) := by
          unfold FinProb.condExp
          apply congrArg (fun z : ℝ => z / (FinProb.pi P).pr (Avo Finset.univ))
          unfold FinProb.expect
          apply Finset.sum_congr rfl
          intro ω hω
          by_cases h : Avo Finset.univ ω <;> simp [h]
        _ = (∑ ω ∈ avoid Ev Finset.univ, w ω * Φ ω) /
              mass w (avoid Ev Finset.univ) := by
          have hnum := hnumSet Φ Finset.univ
          have hden : (FinProb.pi P).pr (Avo Finset.univ) =
              mass w (avoid Ev Finset.univ) := (hmass Finset.univ).symm
          calc
            ((FinProb.pi P).expect
                (fun ω => (if Avo Finset.univ ω then 1 else 0) * Φ ω)) /
                (FinProb.pi P).pr (Avo Finset.univ) =
                (∑ ω ∈ avoid Ev Finset.univ, w ω * Φ ω) /
                (FinProb.pi P).pr (Avo Finset.univ) := by
              exact congrArg (fun z : ℝ => z / (FinProb.pi P).pr (Avo Finset.univ)) hnum
            _ = (∑ ω ∈ avoid Ev Finset.univ, w ω * Φ ω) /
                mass w (avoid Ev Finset.univ) := by rw [hden]
    have hprodT : (∏ j ∈ T, (1 - x)) = (1 - x) ^ T.card := by simp [Finset.prod_const]
    have hfinal : (condOr (FinProb.pi P) (Avo Finset.univ)).expect Φ ≤
        ((1 - x) ^ T.card)⁻¹ * B := by
      calc
        (condOr (FinProb.pi P) (Avo Finset.univ)).expect Φ =
            (∑ ω ∈ avoid Ev Finset.univ, w ω * Φ ω) /
              mass w (avoid Ev Finset.univ) := hcondExpect
        _ ≤ (∏ j ∈ T, (1 - x))⁻¹ * B := by
          calc
            _ ≤ (∏ j ∈ T, (1 - x))⁻¹ *
                ((∑ ω ∈ avoid Ev S, w ω * Φ ω) / mass w (avoid Ev S)) := hcmp
            _ ≤ (∏ j ∈ T, (1 - x))⁻¹ * B :=
              mul_le_mul_of_nonneg_left hfreeCond (inv_nonneg.mpr
                (Finset.prod_nonneg fun j _ => sub_nonneg.mpr (le_of_lt hI.x_lt_one)))
        _ = ((1 - x) ^ T.card)⁻¹ * B := by rw [hprodT]
    simpa [Avo, T] using hfinal

end HypercubeRamsey.S08
