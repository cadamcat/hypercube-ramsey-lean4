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
  let δ : ℝ := Real.exp (-((n : ℝ) ^ 2))
  let horizon : ℝ := K₀ * Real.log (n : ℝ)
  let ticks : ℕ := Nat.ceil (horizon / δ)
  have hn' : (1 : ℝ) < n := by exact_mod_cast (lt_of_lt_of_le (by decide : 1 < 2) hn)
  have hlog : 0 < Real.log (n : ℝ) := Real.log_pos hn'
  have hhorizon : 0 < horizon := mul_pos hK₀ hlog
  have hδ : 0 < δ := Real.exp_pos _
  have hq : 0 ≤ horizon / δ := div_nonneg hhorizon.le hδ.le
  refine ⟨⟨δ, horizon, ticks, rfl, rfl, ?_, ?_⟩⟩
  · dsimp [ticks]
    have hceil : horizon / δ ≤ (Nat.ceil (horizon / δ) : ℝ) := Nat.le_ceil _
    calc
      horizon = (horizon / δ) * δ := by rw [div_mul_cancel₀ _ hδ.ne']
      _ ≤ (Nat.ceil (horizon / δ) : ℝ) * δ := mul_le_mul_of_nonneg_right hceil hδ.le
      _ = (Nat.ceil (horizon / δ) : ℝ) * δ := rfl
  · dsimp [ticks]
    have hceil := Nat.ceil_lt_add_one hq
    calc
      (Nat.ceil (horizon / δ) : ℝ) * δ < (horizon / δ + 1) * δ :=
        mul_lt_mul_of_pos_right hceil hδ
      _ = horizon + δ := by rw [add_mul, div_mul_cancel₀ _ hδ.ne']; ring

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
  classical
  let b : ℝ := 1 - δ * r
  have hgeom : (∑ t ∈ Finset.range T, b ^ t) * (1 - b) = 1 - b ^ T :=
    geom_sum_mul_neg b T
  have hgeom' : (∑ t ∈ Finset.range T, b ^ t) * (δ * r) = 1 - b ^ T := by
    simpa [b] using hgeom
  let e : MeshClockValue T α ≃ Unit ⊕ (Fin T × α) :=
    { toFun := fun x => match x with
        | .noArrival => Sum.inl ()
        | .tick t a => Sum.inr (t, a)
      invFun := fun x => match x with
        | .inl _ => .noArrival
        | .inr (t, a) => .tick t a
      left_inv := by intro x; cases x <;> rfl
      right_inv := by intro x; cases x <;> rfl }
  have hinner (t : Fin T) :
      (∑ a, survival δ r t.val * δ * markMass a) = b ^ t.val * (δ * r) := by
    rw [show survival δ r t.val = b ^ t.val by rfl]
    calc
      (∑ a, b ^ t.val * δ * markMass a) = b ^ t.val * δ * ∑ a, markMass a := by
        rw [Finset.mul_sum]
      _ = b ^ t.val * (δ * r) := by rw [hmarks]; ring
  calc
    (∑ x : MeshClockValue T α, markedClockWeight δ r markMass x) =
        ∑ x : Unit ⊕ (Fin T × α), markedClockWeight δ r markMass (e.symm x) := by
          exact Fintype.sum_equiv e _ _ (by intro x; rw [e.symm_apply_apply])
    _ = survival δ r T + ∑ t : Fin T, ∑ a : α,
          survival δ r t.val * δ * markMass a := by
          simp [e, Fintype.sum_sum_type, Fintype.sum_prod_type, markedClockWeight]
    _ = b ^ T + ∑ t : Fin T, b ^ t.val * (δ * r) := by
          rw [show survival δ r T = b ^ T by rfl]
          congr 1
          apply Finset.sum_congr rfl
          intro t _
          exact hinner t
    _ = b ^ T + (∑ t ∈ Finset.range T, b ^ t) * (δ * r) := by
          rw [← Fin.sum_univ_eq_sum_range]
          rw [Finset.sum_mul]
    _ = b ^ T + (1 - b ^ T) := by rw [hgeom']
    _ = 1 := by ring

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
  classical
  let b : ℝ := 1 - δ * r
  let q : ℝ := δ * r
  let e : MeshClockValue T α ≃ Unit ⊕ (Fin T × α) :=
    { toFun := fun x => match x with
        | .noArrival => Sum.inl ()
        | .tick s a => Sum.inr (s, a)
      invFun := fun x => match x with
        | .inl _ => .noArrival
        | .inr (s, a) => .tick s a
      left_inv := by intro x; cases x <;> rfl
      right_inv := by intro x; cases x <;> rfl }
  have hgeom (N : ℕ) : (∑ i ∈ Finset.range N, b ^ i) * q = 1 - b ^ N := by
    simpa [b, q] using (geom_sum_mul_neg b N)
  have hinner (s : Fin T) :
      (∑ a, survival δ r s.val * δ * markMass a) = b ^ s.val * q := by
    rw [show survival δ r s.val = b ^ s.val by rfl]
    calc
      (∑ a, b ^ s.val * δ * markMass a) = b ^ s.val * δ * ∑ a, markMass a := by
        rw [Finset.mul_sum]
      _ = b ^ s.val * q := by rw [hmarks]; ring
  have htail : (∑ i ∈ Finset.Ico t T, b ^ i * q) = b ^ t - b ^ T := by
    calc
      (∑ i ∈ Finset.Ico t T, b ^ i * q) =
          (∑ i ∈ Finset.Ico t T, b ^ i) * q := by rw [Finset.sum_mul]
      _ = ((∑ i ∈ Finset.range T, b ^ i) - (∑ i ∈ Finset.range t, b ^ i)) * q := by
          rw [Finset.sum_Ico_eq_sub _ ht]
      _ = (1 - b ^ T) - (1 - b ^ t) := by rw [sub_mul, hgeom T, hgeom t]
      _ = b ^ t - b ^ T := by ring
  have hfilter :
      (∑ s : Fin T, if s.val < t then 0 else b ^ s.val * q) =
        ∑ i ∈ Finset.Ico t T, b ^ i * q := by
    change (∑ s : Fin T, (fun i : ℕ => if i < t then 0 else b ^ i * q) s.val) = _
    rw [Fin.sum_univ_eq_sum_range (fun i : ℕ => if i < t then 0 else b ^ i * q) T]
    have hset : (Finset.range T).filter (fun i => t ≤ i) = Finset.Ico t T := by
      ext i
      simp [Nat.not_lt, and_comm]
    rw [← hset, Finset.sum_filter]
    apply Finset.sum_congr rfl
    intro i hi
    by_cases h : t ≤ i <;> simp [h, Nat.not_lt]
  let f : MeshClockValue T α → ℝ := fun x =>
    if x = .noArrival then (markedClockLaw δ r markMass hδ hbase hr hmark hmarks).w x else
      match x with
      | .noArrival => 0
      | .tick s _ => if s.val < t then 0 else
          (markedClockLaw δ r markMass hδ hbase hr hmark hmarks).w x
  have hunroll :
      (∑ x : Unit ⊕ (Fin T × α), f (e.symm x)) =
        survival δ r T + ∑ s : Fin T, ∑ a : α,
          if s.val < t then 0 else survival δ r s.val * δ * markMass a := by
    simp [f, e, Fintype.sum_sum_type, Fintype.sum_prod_type,
      markedClockLaw, markedClockWeight]
  change (∑ x : MeshClockValue T α, f x) = survival δ r t
  calc
    (∑ x : MeshClockValue T α, f x) =
        ∑ x : Unit ⊕ (Fin T × α), f (e.symm x) := by
          exact Fintype.sum_equiv e f _ (by intro x; rw [e.symm_apply_apply])
    _ = survival δ r T + ∑ s : Fin T, ∑ a : α,
        if s.val < t then 0 else survival δ r s.val * δ * markMass a := hunroll
    _ = b ^ T + ∑ s : Fin T, if s.val < t then 0 else b ^ s.val * q := by
          rw [show survival δ r T = b ^ T by rfl]
          congr 1
          apply Finset.sum_congr rfl
          intro s _
          by_cases hs : s.val < t
          · simp [hs]
          · simpa [hs] using hinner s
    _ = b ^ T + ∑ i ∈ Finset.Ico t T, b ^ i * q := by rw [hfilter]
    _ = b ^ t := by rw [htail]; ring
    _ = survival δ r t := rfl

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
