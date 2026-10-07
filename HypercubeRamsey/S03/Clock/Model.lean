import HypercubeRamsey.S03.NearProductInjection

/-!
# Finite mesh clocks for Lemma 3.10

The mesh has ticks `1, …, T` (represented by `Fin T`) and a no-arrival value.  A marked edge of rate `r`
whose mark masses sum to `r` has first-arrival mass
`(1 - δ r)^t * δ * markMass`; the remaining mass is `(1 - δ r)^T`.  This is the exact discrete survival
law `(1 - δ r)^t`, with no continuous-time limit.
-/

namespace HypercubeRamsey.Clock

open scoped BigOperators

/-- A finite mesh on `[0, K₀ log n]` with step `δ = exp(-n²)` and the least integer number of ticks
covering that horizon. The final mesh time is less than one step past the truncation horizon. -/
structure FiniteMeshPlan (n : ℕ) (K₀ : ℝ) where
  δ : ℝ
  horizon : ℝ
  ticks : ℕ
  δ_eq : δ = Real.exp (-((n : ℝ) ^ 2))
  horizon_eq : horizon = K₀ * Real.log (n : ℝ)
  covers_horizon : horizon ≤ (ticks : ℝ) * δ
  least_cover : (ticks : ℝ) * δ < horizon + δ

/-- The mesh with exponentially small step and a cutoff of `K₀ log n`. -/
theorem finiteMeshPlan_exists (n : ℕ) (K₀ : ℝ) (hn : 2 ≤ n) (hK₀ : 0 < K₀) :
    Nonempty (FiniteMeshPlan n K₀) := by
  sorry

/-- The finite mesh time coordinate. `tick t` means arrival at time `(t.val + 1) * δ`. -/
inductive MeshClockValue (T : ℕ) (α : Type*) where
  | noArrival : MeshClockValue T α
  | tick (t : Fin T) (mark : α) : MeshClockValue T α
  deriving DecidableEq, Fintype

/-- Survival through `t` mesh steps for an edge of rate `r`. -/
def survival (δ r : ℝ) (t : ℕ) : ℝ := (1 - δ * r) ^ t

/-- The first-arrival and mark weights for one edge. -/
def markedClockWeight {T : ℕ} {α : Type*} [Fintype α]
    (δ r : ℝ) (markMass : α → ℝ) : MeshClockValue T α → ℝ
  | .noArrival => survival δ r T
  | .tick t a => survival δ r t.val * δ * markMass a

/-- The finite geometric first-arrival weights sum to one. -/
theorem markedClockWeight_sum {T : ℕ} {α : Type*} [Fintype α]
    (δ r : ℝ) (markMass : α → ℝ)
    (hδ : 0 ≤ δ) (hbase : 0 ≤ 1 - δ * r)
    (hr : 0 ≤ r) (hmark : ∀ a, 0 ≤ markMass a)
    (hmarks : ∑ a, markMass a = r) :
    ∑ x : MeshClockValue T α, markedClockWeight δ r markMass x = 1 := by
  sorry

/-- A probability law for a finite-mesh first arrival with an independent mark conditional on the edge. -/
noncomputable def markedClockLaw {T : ℕ} {α : Type*} [Fintype α]
    (δ r : ℝ) (markMass : α → ℝ)
    (hδ : 0 ≤ δ) (hbase : 0 ≤ 1 - δ * r)
    (hr : 0 ≤ r) (hmark : ∀ a, 0 ≤ markMass a)
    (hmarks : ∑ a, markMass a = r) : FinProb (MeshClockValue T α) where
  w := markedClockWeight δ r markMass
  nonneg x := by
    cases x with
    | noArrival => exact pow_nonneg hbase T
    | tick t a => exact mul_nonneg (mul_nonneg (pow_nonneg hbase _) hδ) (hmark a)
  sum_eq_one := markedClockWeight_sum δ r markMass hδ hbase hr hmark hmarks

/-- The exact no-arrival probability through `t` ticks. -/
theorem markedClockLaw_survival {T : ℕ} {α : Type*} [Fintype α] [DecidableEq α]
    (δ r : ℝ) (markMass : α → ℝ)
    (hδ : 0 ≤ δ) (hbase : 0 ≤ 1 - δ * r)
    (hr : 0 ≤ r) (hmark : ∀ a, 0 ≤ markMass a)
    (hmarks : ∑ a, markMass a = r) (t : ℕ) (ht : t ≤ T) :
    (∑ x : MeshClockValue T α,
      if x = .noArrival then (markedClockLaw δ r markMass hδ hbase hr hmark hmarks).w x else
        match x with
        | .noArrival => 0
        | .tick s _ => if s.val < t then 0 else
            (markedClockLaw δ r markMass hδ hbase hr hmark hmarks).w x) =
      survival δ r t := by
  sorry

/-- A row-label edge in the bipartite row/label graph. -/
abbrev RowLabel (R : Type*) (g : ℕ) := R × Fin g

/-- The independent first-arrival data on every row-label edge. -/
abbrev ClockField (T : ℕ) (R : Type*) (g : ℕ) (Ω : R → Type*) :=
  ∀ e : RowLabel R g, MeshClockValue T (Ω e.1)

/-- Product law for independent edge clocks, with a possibly different mark law on each row-label edge. -/
noncomputable def clockFieldLaw {T : ℕ} {R : Type*} [Fintype R] [DecidableEq R]
    {g : ℕ} {Ω : R → Type*} [∀ a, Fintype (Ω a)] [∀ a, DecidableEq (Ω a)]
    (edgeLaw : ∀ e : RowLabel R g, FinProb (MeshClockValue T (Ω e.1))) :
    FinProb (ClockField T R g Ω) :=
  FinProb.pi edgeLaw

/-- The label-specific mark masses induced by a row output law. -/
def outputMarkMass {Ω : Type*} [Fintype Ω] {g : ℕ} (p : FinProb Ω)
    (lab : Ω → Fin g) (y : Fin g) : Ω → ℝ :=
  fun o => if lab o = y then p.w o else 0

theorem outputMarkMass_sum {Ω : Type*} [Fintype Ω] {g : ℕ} (p : FinProb Ω)
    (lab : Ω → Fin g) (y : Fin g) :
    ∑ o, outputMarkMass p lab y o = labMarg p lab y := rfl

theorem labMarg_nonneg {Ω : Type*} [Fintype Ω] {g : ℕ} (p : FinProb Ω)
    (lab : Ω → Fin g) (y : Fin g) : 0 ≤ labMarg p lab y := by
  unfold labMarg
  exact Finset.sum_nonneg fun o _ => by
    split_ifs
    · exact p.nonneg o
    · exact le_rfl

theorem labMarg_le_one {Ω : Type*} [Fintype Ω] {g : ℕ} (p : FinProb Ω)
    (lab : Ω → Fin g) (y : Fin g) : labMarg p lab y ≤ 1 := by
  unfold labMarg
  calc
    (∑ o, if lab o = y then p.w o else 0) ≤ ∑ o, p.w o := by
      apply Finset.sum_le_sum
      intro o ho
      split_ifs
      · exact le_rfl
      · exact p.nonneg o
    _ = 1 := p.sum_eq_one

/-- The edge clock with rate `labMarg p lab y` and an output mark sampled from the conditional label law. -/
noncomputable def outputEdgeClockLaw {Ω : Type*} [Fintype Ω] [DecidableEq Ω] {g T : ℕ}
    (δ : ℝ) (hδ : 0 ≤ δ) (p : FinProb Ω) (lab : Ω → Fin g) (y : Fin g)
    (hbase : 0 ≤ 1 - δ * labMarg p lab y) : FinProb (MeshClockValue T Ω) :=
  markedClockLaw δ (labMarg p lab y) (outputMarkMass p lab y)
    hδ hbase (labMarg_nonneg p lab y)
    (fun o => by
      unfold outputMarkMass
      split_ifs
      · exact p.nonneg o
      · exact le_rfl)
    (outputMarkMass_sum p lab y)

/-- Column rate at a label, before the finite-mesh clocks are generated. -/
noncomputable def columnRate {R : Type*} [Fintype R] {g : ℕ}
    {Ω : R → Type*} [∀ a, Fintype (Ω a)]
    (p : ∀ a, FinProb (Ω a)) (lab : ∀ a, Ω a → Fin g) (y : Fin g) : ℝ :=
  ∑ a, labMarg (p a) (lab a) y

/-- A completed column system has the common total rate `θ` at every label. -/
def CompletedColumns {R : Type*} [Fintype R] {g : ℕ}
    {Ω : R → Type*} [∀ a, Fintype (Ω a)]
    (p : ∀ a, FinProb (Ω a)) (lab : ∀ a, Ω a → Fin g) (θ : ℝ) : Prop :=
  ∀ y, columnRate p lab y = θ

end HypercubeRamsey.Clock
