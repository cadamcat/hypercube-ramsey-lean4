import HypercubeRamsey.S03.Clock.Inputs
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import HypercubeRamsey.S03.Clock.Steps_p_clock_r4

/-!
# Lemma 3.10, Steps 2–8

Each proof node refers to the finite mesh objects in `Model`, `Matching`, `Exploration`, `Leaves`, and
`Inputs`. Steps 4–7 are separated into path, branching-tail, background-tracking, and target-product
obligations. Step 8 is assembled: `step8_bad_leaf_avoidance` (used by `clock_sampling`) combines Step 1, the
renormalization bound and `step8_trimmed_core`; the core combines `clock_raw_sampler` (the clock construction
and its incidence bound) with `leaf_avoidance_transfer` (Lemma 3.5).
-/

namespace HypercubeRamsey.Clock

open Filter
open scoped BigOperators

/-- The parts of Step 2 that are reused by later estimates. -/
structure Step2Certificate {T : ℕ} {R K : Type*} [Fintype R] [DecidableEq R] [Fintype K]
    {g : ℕ} {Ω : R → Type*} [∀ a, Fintype (Ω a)] [∀ a, DecidableEq (Ω a)]
    (F : K → (∀ a, Ω a) → Prop) (scope : K → Finset R)
    (ξ : ClockField T R g Ω) : Prop where
  ordered : (clockEventList ξ).Pairwise (fun e f => eventPriority e ≤ eventPriority f)
  labels_injective : ∀ a b y oa ob,
    (greedyMatching ξ).assignment a = some (y, oa) →
    (greedyMatching ξ).assignment b = some (y, ob) → a = b
  test_closure : ∀ t ξ', agreesOnActiveEdges scope t ξ ξ' →
      (testFails F scope (greedyMatching ξ) t ↔ testFails F scope (greedyMatching ξ') t)

/-- L3.10b (03:844–874): fixed tie order, greedy matching, and decreasing-horizon backward closure. -/
theorem step2_clock_matching_exploration {T : ℕ} {R K : Type*}
    [Fintype R] [DecidableEq R] [Fintype K] {g : ℕ}
    {Ω : R → Type*} [∀ a, Fintype (Ω a)] [∀ a, DecidableEq (Ω a)]
    (F : K → (∀ a, Ω a) → Prop) (scope : K → Finset R)
    (ξ : ClockField T R g Ω) : Step2Certificate F scope ξ := by
  refine ⟨clockEventList_sorted ξ, greedyMatching_label_injective ξ, ?_⟩
  exact fun t ξ' h => backwardClosure_determines_test F scope ξ ξ' t h

/-- L3.10c (03:876–905): forcing a positive product-rectangle leaf cannot increase avoidance of a finite
family of nonneighbor bad leaves. -/
theorem step3_leaf_rectangles_forcing {T : ℕ} {R : Type*} [Fintype R] [DecidableEq R]
    {g : ℕ} {Ω : R → Type*} [∀ a, Fintype (Ω a)] [∀ a, DecidableEq (Ω a)]
    (edgeLaw : ∀ e : RowLabel R g, FinProb (MeshClockValue T (Ω e.1)))
    (L : ClockLeaf T R g Ω) (bad : List (ClockLeaf T R g Ω))
    (hpositive : 0 < (clockFieldLaw edgeLaw).pr L.Event)
    (hnonneighbor : ∀ L' ∈ bad, L.Nonneighbor L') :
    (clockFieldLaw edgeLaw).pr (fun ξ => L.Event ξ ∧ avoidsLeaves bad ξ) /
      (clockFieldLaw edgeLaw).pr L.Event ≤
        (clockFieldLaw edgeLaw).pr (avoidsLeaves bad) := by
  exact leaf_forcing_coupling edgeLaw L bad hpositive hnonneighbor

/-- The rate of a step between row/label endpoints, in either orientation. -/
def transitionRate {R : Type*} {g : ℕ} (r : R → Fin g → ℝ) :
    Endpoint R g → Endpoint R g → ℝ
  | .inl a, .inr y => r a y
  | .inr y, .inl a => r a y
  | _, _ => 0

/-- The rate product along a finite endpoint walk. -/
noncomputable def walkRate {m : ℕ} {R : Type*} {g : ℕ}
    (r : R → Fin g → ℝ) (w : Fin (m + 1) → Endpoint R g) : ℝ :=
  ∏ i : Fin m, transitionRate r (w i.castSucc) (w i.succ)

/-- Total rate weight of length-`m` walks from one endpoint. -/
noncomputable def rootedWalkMass {m : ℕ} {R : Type*} [Fintype R] {g : ℕ}
    (r : R → Fin g → ℝ) (u : Endpoint R g) : ℝ := by
  classical
  exact
  ∑ w : Fin (m + 1) → Endpoint R g, if w 0 = u then walkRate r w else 0

/-- L3.10d (03:907–944): reversed walk weights are controlled by the alternating row/label rates. -/
theorem step4_path_insertion_bound {R : Type*} [Fintype R] {g : ℕ}
    (r : R → Fin g → ℝ) (θ : ℝ)
    (hr0 : ∀ a y, 0 ≤ r a y)
    (hrow : ∀ a, ∑ y, r a y = 1)
    (hcol : ∀ y, ∑ a, r a y = θ)
    (hθ0 : 0 ≤ θ) (hθ1 : θ ≤ 1) :
    ∀ (m : ℕ) (u : Endpoint R g), rootedWalkMass (m := m) r u ≤ θ ^ (m / 2) := by
  classical
  intro m u
  let seqEquiv (n : ℕ) :
      (Endpoint R g × (Fin n → Endpoint R g)) ≃ (Fin (n + 1) → Endpoint R g) := {
    toFun p := Fin.cons (α := fun _ : Fin (n + 1) => Endpoint R g) p.1 p.2
    invFun w := (w 0, fun i => w i.succ)
    left_inv := by rintro ⟨x, f⟩; simp
    right_inv := by
      intro w
      funext i
      exact Fin.cases (by simp) (fun j => by simp) i
  }
  have hwalkCons {k : ℕ} (x : Endpoint R g)
      (w : Fin (k + 1) → Endpoint R g) :
      walkRate (m := k + 1) r
          (Fin.cons (α := fun _ : Fin (k + 2) => Endpoint R g) x w) =
        transitionRate r x (w 0) * walkRate (m := k) r w := by
    simp [walkRate, Fin.prod_univ_succ, Fin.cons]
  have hmassTail {k : ℕ} (x : Endpoint R g) :
      rootedWalkMass (m := k) r x =
        ∑ tail : Fin k → Endpoint R g,
          walkRate (m := k) r
            (Fin.cons (α := fun _ : Fin (k + 1) => Endpoint R g) x tail) := by
    unfold rootedWalkMass
    calc
      (∑ w : Fin (k + 1) → Endpoint R g,
          if w 0 = x then walkRate (m := k) r w else 0) =
          ∑ p : Endpoint R g × (Fin k → Endpoint R g),
            if (Fin.cons (α := fun _ : Fin (k + 1) => Endpoint R g) p.1 p.2) 0 = x then
              walkRate (m := k) r
                (Fin.cons (α := fun _ : Fin (k + 1) => Endpoint R g) p.1 p.2) else 0 := by
        symm
        exact Fintype.sum_equiv (seqEquiv k) _ _ (by intro p; simp [seqEquiv])
      _ = ∑ tail : Fin k → Endpoint R g,
            walkRate (m := k) r
              (Fin.cons (α := fun _ : Fin (k + 1) => Endpoint R g) x tail) := by
        rw [Fintype.sum_prod_type]
        rw [Finset.sum_comm]
        simp [Fin.cons, eq_comm]
  have hrec {k : ℕ} (x : Endpoint R g) :
      rootedWalkMass (m := k + 1) r x =
        ∑ v : Endpoint R g,
          transitionRate r x v * rootedWalkMass (m := k) r v := by
    calc
      rootedWalkMass (m := k + 1) r x =
          ∑ tail : Fin (k + 1) → Endpoint R g,
            transitionRate r x (tail 0) * walkRate (m := k) r tail := by
        rw [hmassTail]
        simp_rw [hwalkCons]
      _ = ∑ v : Endpoint R g,
            transitionRate r x v * rootedWalkMass (m := k) r v := by
        symm
        unfold rootedWalkMass
        simp_rw [show ∀ v : Endpoint R g,
          transitionRate r x v *
              (∑ w : Fin (k + 1) → Endpoint R g,
                if w 0 = v then walkRate (m := k) r w else 0) =
            ∑ w : Fin (k + 1) → Endpoint R g,
              transitionRate r x v *
                (if w 0 = v then walkRate (m := k) r w else 0) from
          fun v => Finset.mul_sum Finset.univ _ _]
        simp_rw [mul_ite, mul_zero]
        rw [Finset.sum_comm]
        simp [eq_comm]
  have hrecRow {k : ℕ} (a : R) :
      rootedWalkMass (m := k + 1) r (Sum.inl a) =
        ∑ y : Fin g, r a y * rootedWalkMass (m := k) r (Sum.inr y) := by
    rw [hrec]
    simp [transitionRate, Fintype.sum_sum_type]
  have hrecLabel {k : ℕ} (y : Fin g) :
      rootedWalkMass (m := k + 1) r (Sum.inr y) =
        ∑ a : R, r a y * rootedWalkMass (m := k) r (Sum.inl a) := by
    rw [hrec]
    simp [transitionRate, Fintype.sum_sum_type]
  have hzero (x : Endpoint R g) : rootedWalkMass (m := 0) r x = 1 := by
    rw [hmassTail]
    simp [walkRate]
  have hbounds (k : ℕ) :
      (∀ a : R, rootedWalkMass (m := k) r (Sum.inl a) ≤ θ ^ (k / 2)) ∧
      (∀ y : Fin g, rootedWalkMass (m := k) r (Sum.inr y) ≤ θ ^ ((k + 1) / 2)) := by
    induction k with
    | zero =>
        constructor
        · intro a
          rw [hzero]
          simp
        · intro y
          rw [hzero]
          simp
    | succ k ih =>
        constructor
        · intro a
          rw [hrecRow]
          calc
            (∑ y : Fin g,
                r a y * rootedWalkMass (m := k) r (Sum.inr y)) ≤
                ∑ y : Fin g, r a y * θ ^ ((k + 1) / 2) := by
              apply Finset.sum_le_sum
              intro y _
              exact mul_le_mul_of_nonneg_left (ih.2 y) (hr0 a y)
            _ = (∑ y : Fin g, r a y) * θ ^ ((k + 1) / 2) := by
              rw [Finset.sum_mul]
            _ = θ ^ ((k + 1) / 2) := by rw [hrow a]; simp
        · intro y
          rw [hrecLabel]
          calc
            (∑ a : R, r a y * rootedWalkMass (m := k) r (Sum.inl a)) ≤
                ∑ a : R, r a y * θ ^ (k / 2) := by
              apply Finset.sum_le_sum
              intro a _
              exact mul_le_mul_of_nonneg_left (ih.1 a) (hr0 a y)
            _ = (∑ a : R, r a y) * θ ^ (k / 2) := by
              rw [Finset.sum_mul]
            _ = θ * θ ^ (k / 2) := by rw [hcol y]
            _ = θ ^ (k / 2 + 1) := by rw [pow_succ]; ring
            _ = θ ^ ((k + 2) / 2) := by congr 1 <;> omega
  rcases u with a | y
  · exact (hbounds m).1 a
  · exact le_trans ((hbounds m).2 y)
      (pow_le_pow_of_le_one hθ0 hθ1 (by omega))

/-- L3.10e (03:946–989): the exponential-moment estimate for a two-type branching forest gives a giant-tail
bound at the active-endpoint cutoff. -/
theorem step5_giant_tail {Ω : Type*} [Fintype Ω]
    (P : FinProb Ω) (size : Ω → ℕ) (δ roots L η : ℝ)
    (hδ : 0 < δ)
    (hmoment : P.expect (fun ω => Real.exp (δ * (size ω : ℝ))) ≤ Real.exp (δ * roots + η)) :
    P.pr (fun ω => L ≤ (size ω : ℝ)) ≤ Real.exp (-δ * (L - roots) + η) := by
  classical
  let X : Ω → ℝ := fun ω => Real.exp (δ * (size ω : ℝ))
  let threshold : ℝ := Real.exp (δ * L)
  have hthreshold : 0 < threshold := by
    dsimp [threshold]
    exact Real.exp_pos _
  have htail : ∀ ω, L ≤ (size ω : ℝ) → threshold ≤ X ω := by
    intro ω hω
    dsimp [threshold, X]
    apply Real.exp_le_exp.mpr
    exact mul_le_mul_of_nonneg_left hω (le_of_lt hδ)
  have hprob :
      P.pr (fun ω => L ≤ (size ω : ℝ)) ≤ P.pr (fun ω => threshold ≤ X ω) := by
    unfold FinProb.pr
    apply Finset.sum_le_sum
    intro ω _
    by_cases hω : L ≤ (size ω : ℝ)
    · have hX := htail ω hω
      simp [hω, hX]
    · by_cases hX : threshold ≤ X ω
      · simpa [hω, hX] using P.nonneg ω
      · simp [hω, hX]
  have hmarkovPoint :
      threshold * P.pr (fun ω => threshold ≤ X ω) ≤ P.expect X := by
    change threshold * (∑ ω, if threshold ≤ X ω then P.w ω else 0) ≤
      ∑ ω, P.w ω * X ω
    rw [Finset.mul_sum]
    calc
      (∑ ω, threshold * (if threshold ≤ X ω then P.w ω else 0)) =
          ∑ ω, P.w ω * (if threshold ≤ X ω then threshold else 0) := by
        apply Finset.sum_congr rfl
        intro ω _
        by_cases hX : threshold ≤ X ω
        · simp [hX, mul_comm]
        · simp [hX, mul_comm]
      _ ≤ ∑ ω, P.w ω * X ω := by
        apply Finset.sum_le_sum
        intro ω _
        by_cases hX : threshold ≤ X ω
        · have hmul : threshold * P.w ω ≤ X ω * P.w ω :=
            mul_le_mul_of_nonneg_right hX (P.nonneg ω)
          simpa [hX, mul_comm] using hmul
        · have hX0 : 0 ≤ X ω := (Real.exp_pos _).le
          simpa [hX] using mul_nonneg (P.nonneg ω) hX0
  have hmarkov :
      P.pr (fun ω => threshold ≤ X ω) ≤ P.expect X / threshold := by
    apply (le_div_iff₀ hthreshold).2
    calc
      P.pr (fun ω => threshold ≤ X ω) * threshold =
          threshold * P.pr (fun ω => threshold ≤ X ω) := by ring
      _ ≤ P.expect X := hmarkovPoint
  have hmoment' : P.expect X ≤ Real.exp (δ * roots + η) := by
    simpa [X] using hmoment
  have hquot : P.expect X / threshold ≤ Real.exp (δ * roots + η) / threshold :=
    div_le_div_of_nonneg_right hmoment' hthreshold.le
  have hratio : Real.exp (δ * roots + η) / threshold =
      Real.exp (-δ * (L - roots) + η) := by
    rw [show threshold = Real.exp (δ * L) by rfl, ← Real.exp_sub]
    congr 1 <;> ring
  calc
    P.pr (fun ω => L ≤ (size ω : ℝ)) ≤ P.pr (fun ω => threshold ≤ X ω) := hprob
    _ ≤ P.expect X / threshold := hmarkov
    _ ≤ Real.exp (δ * roots + η) / threshold := hquot
    _ = Real.exp (-δ * (L - roots) + η) := hratio

/-- One Euler step for the finite-mesh background equations `q'=-θzq`, `z'=-qz`. -/
def backgroundStep (δ θ : ℝ) (s : ℝ × ℝ) : ℝ × ℝ :=
  (s.1 - δ * θ * s.2 * s.1, s.2 - δ * s.1 * s.2)

/-- The deterministic discrete background trajectory, starting from `(q,z)=(1,1)`. -/
def backgroundTrajectory (δ θ : ℝ) : ℕ → ℝ × ℝ
  | 0 => (1, 1)
  | t + 1 => backgroundStep δ θ (backgroundTrajectory δ θ t)

/-- A process of free-row and free-label masses on the finite mesh. -/
structure BackgroundProcess (T : ℕ) (Ω : Type*) where
  rowMass : Fin (T + 1) → Ω → ℝ
  labelMass : Fin (T + 1) → Ω → ℝ

/-- Deterministic error propagation for the finite-mesh background recursion. Both masses are normalized as
the trajectory `(q, z)`: `labelMass` plays `z = R_y / θ` (TeX 03:1001–1004), so it starts at `1`, and the
drift hypothesis applies `backgroundStep` to `(rowMass, labelMass)`. -/
theorem background_trajectory_stability {T : ℕ} {Ω : Type*} [Fintype Ω]
    (P : FinProb Ω) (X : BackgroundProcess T Ω) (δ θ : ℝ)
    (η : ℝ) (hη : 0 ≤ η) (hδ0 : 0 ≤ δ) (hδ1 : δ ≤ 1)
    (hθ0 : 0 ≤ θ) (hθ1 : θ ≤ 1)
    (hrow0 : ∀ ω, X.rowMass 0 ω = 1)
    (hlabel0 : ∀ ω, X.labelMass 0 ω = 1)
    (hstate : ∀ (t : Fin (T + 1)) ω,
      0 ≤ X.rowMass t ω ∧ X.rowMass t ω ≤ 1 ∧
      0 ≤ X.labelMass t ω ∧ X.labelMass t ω ≤ 1)
    (hdrift : ∀ t : Fin T, ∀ ω,
      |X.rowMass t.succ ω - (backgroundStep δ θ
        (X.rowMass t.castSucc ω, X.labelMass t.castSucc ω)).1| ≤ η ∧
      |X.labelMass t.succ ω - (backgroundStep δ θ
        (X.rowMass t.castSucc ω, X.labelMass t.castSucc ω)).2| ≤ η) :
    P.pr (fun ω => ∀ t : Fin (T + 1),
      |X.rowMass t ω - (backgroundTrajectory δ θ t.val).1| ≤
          η * (T : ℝ) * (1 + δ) ^ T ∧
      |X.labelMass t ω - (backgroundTrajectory δ θ t.val).2| ≤
          η * (T : ℝ) * (1 + δ) ^ T) = 1 := by
  sorry

/-- The background greedy matching through a mesh horizon (TeX 03:992–994): the arrivals with tick strictly
before `horizon` on the edges whose row is not in `removedRows` and whose label is not in `removedLabels`,
processed in the fixed event order. With both sets empty this is the prefix of the ordinary matching. -/
noncomputable def matchingThrough {T : ℕ} {R : Type*} [Fintype R] [DecidableEq R]
    {g : ℕ} {Ω : R → Type*} [∀ a, Fintype (Ω a)] [∀ a, DecidableEq (Ω a)]
    (ξ : ClockField T R g Ω) (removedRows : Finset R) (removedLabels : Finset (Fin g))
    (horizon : Fin (T + 1)) : GreedyState R g Ω := by
  classical
  exact runGreedy ξ ((clockEventList ξ).filter (fun e =>
    e.2.2.1.val < horizon.val ∧ e.1 ∉ removedRows ∧ e.2.1 ∉ removedLabels))

/-- The available label mass `X_a(t)` of a row (TeX 03:994–999): the rates to labels that are free in the
background, i.e. neither removed nor matched. Defined for every row, including matched and removed rows. -/
noncomputable def availableRowRate {T : ℕ} {R : Type*} [Fintype R] [DecidableEq R]
    {g : ℕ} {Ω : R → Type*} [∀ a, Fintype (Ω a)] [∀ a, DecidableEq (Ω a)]
    (rates : R → Fin g → ℝ) (ξ : ClockField T R g Ω)
    (removedRows : Finset R) (removedLabels : Finset (Fin g)) (a : R) (horizon : Fin (T + 1)) : ℝ := by
  classical
  let M := matchingThrough ξ removedRows removedLabels horizon
  exact ∑ y, if y ∉ removedLabels ∧ ¬ labelUsed M y then rates a y else 0

/-- The available row mass `R_y(t)` at a label (TeX 03:994–999): the rates from rows that are free in the
background, i.e. neither removed nor matched. Defined for every label, including matched and removed labels;
it does not depend on the label's own status. -/
noncomputable def availableLabelRate {T : ℕ} {R : Type*} [Fintype R] [DecidableEq R]
    {g : ℕ} {Ω : R → Type*} [∀ a, Fintype (Ω a)] [∀ a, DecidableEq (Ω a)]
    (rates : R → Fin g → ℝ) (ξ : ClockField T R g Ω)
    (removedRows : Finset R) (removedLabels : Finset (Fin g)) (y : Fin g)
    (horizon : Fin (T + 1)) : ℝ := by
  classical
  let M := matchingThrough ξ removedRows removedLabels horizon
  exact ∑ a, if a ∉ removedRows ∧ M.assignment a = none then rates a y else 0

/-- Prescribed clock values on finitely many edges replace the random ones. On the finite mesh this is the
Poisson insertion of TeX 03:912–918 and 03:992–993: conditioning independent edge clocks on prescribed values
of a few edges is the product law with those coordinates replaced. -/
def insertArrivals {T : ℕ} {R : Type*} {g : ℕ} {Ω : R → Type*}
    (ins : ∀ e : RowLabel R g, Option (MeshClockValue T (Ω e.1))) (ξ : ClockField T R g Ω) :
    ClockField T R g Ω :=
  fun e => (ins e).getD (ξ e)

/-- The number of edges whose clock value an insertion prescribes. -/
noncomputable def insertionSize {T : ℕ} {R : Type*} [Fintype R] {g : ℕ} {Ω : R → Type*}
    (ins : ∀ e : RowLabel R g, Option (MeshClockValue T (Ω e.1))) : ℕ := by
  classical
  exact (Finset.univ.filter fun e => (ins e).isSome).card

/-- Independent marked mesh clocks generated from the row laws and labels. -/
noncomputable def samplingEdgeClockLaw {T : ℕ} {R : Type*} {g : ℕ}
    {Ω : R → Type*} [∀ a, Fintype (Ω a)] [∀ a, DecidableEq (Ω a)]
    (δ : ℝ) (hδ : 0 ≤ δ) (hδ1 : δ ≤ 1)
    (p : ∀ a, FinProb (Ω a)) (lab : ∀ a, Ω a → Fin g) :
    ∀ e : RowLabel R g, FinProb (MeshClockValue T (Ω e.1)) := by
  classical
  exact fun e => outputEdgeClockLaw δ hδ (p e.1) (lab e.1) e.2 (by
    have hm := labMarg_le_one (p e.1) (lab e.1) e.2
    have hmul : δ * labMarg (p e.1) (lab e.1) e.2 ≤ δ := by
      simpa only [mul_one] using mul_le_mul_of_nonneg_left hm hδ
    exact sub_nonneg.mpr (le_trans hmul hδ1))

/-- L3.10f (03:991–1040): for a fixed prescription removing at most `2n^B` endpoints and inserting `O(log n)`
clock values, under independent first-arrival clocks with column rate `θ` and small atoms, every free mass
tracks the discrete background recursion, with exponentially small failure. The threshold `n₀` depends only on
the constants (`log g ≤ C_g n` permits the union over endpoints, 03:1032), and is uniform over the
prescriptions (03:1011–1012). -/
theorem step6_background_tracking (B A C_g K₀ : ℝ) (hB : 1 ≤ B) (hK₀ : 0 < K₀)
    (hA : 10 * (B + K₀) < A) :
    ∃ n₀ : ℕ, ∀ n ≥ n₀, ∀ (mesh : FiniteMeshPlan n K₀) (hδ : 0 ≤ mesh.δ) (hδ1 : mesh.δ ≤ 1)
      {R : Type} [Fintype R] [DecidableEq R] {g : ℕ} {Ω : R → Type} [∀ a, Fintype (Ω a)]
      [∀ a, DecidableEq (Ω a)] (p : ∀ a, FinProb (Ω a)) (lab : ∀ a, Ω a → Fin g) (θ : ℝ),
      Real.log g ≤ C_g * n →
      (∀ y, ∑ a, labMarg (p a) (lab a) y = θ) → θ ≤ 2e-6 →
      (∀ a y, labMarg (p a) (lab a) y ≤ (n : ℝ) ^ (-A)) →
      ∀ (removedRows : Finset R) (removedLabels : Finset (Fin g)),
      ((removedRows.card + removedLabels.card : ℕ) : ℝ) ≤ 2 * (n : ℝ) ^ B →
      ∀ ins : ∀ e : RowLabel R g, Option (MeshClockValue mesh.ticks (Ω e.1)),
      (insertionSize ins : ℝ) ≤ (K₀ + 1) ^ 2 * Real.log n →
      (clockFieldLaw (samplingEdgeClockLaw (T := mesh.ticks) mesh.δ hδ hδ1 p lab)).pr
        (fun ξ => ∀ t : Fin (mesh.ticks + 1),
          (∀ a, |availableRowRate (fun a y => labMarg (p a) (lab a) y) (insertArrivals ins ξ)
              removedRows removedLabels a t - (backgroundTrajectory mesh.δ θ t.val).1| ≤
            (n : ℝ) ^ (-3 * B)) ∧
          (∀ y, |availableLabelRate (fun a y => labMarg (p a) (lab a) y) (insertArrivals ins ξ)
              removedRows removedLabels y t - θ * (backgroundTrajectory mesh.δ θ t.val).2| ≤
            (n : ℝ) ^ (-3 * B))) ≥
        1 - Real.exp (-((n : ℝ) ^ (A / 3))) := by
  sorry

/-- A target assignment is realized when the greedy matching gives every queried row its prescribed output. -/
def matchesTargets {T : ℕ} {R : Type*} {g : ℕ} {Ω : R → Type*}
    [Fintype R] [DecidableEq R] [∀ a, Fintype (Ω a)] [∀ a, DecidableEq (Ω a)]
    (ξ : ClockField T R g Ω) (S : Finset R) (o : ∀ a, Ω a) : Prop :=
  ∀ a ∈ S, ∃ y, (greedyMatching ξ).assignment a = some (y, o a)

/-- The targets are realized through ordinary arrivals: under the insertion, each queried row is matched with
its prescribed output along an edge whose value the insertion does not prescribe (TeX 03:1043–1045,
03:1086–1088). With the empty insertion this is `matchesTargets`. -/
def matchesTargetsOrdinarily {T : ℕ} {R : Type*} {g : ℕ} {Ω : R → Type*}
    [Fintype R] [DecidableEq R] [∀ a, Fintype (Ω a)] [∀ a, DecidableEq (Ω a)]
    (ins : ∀ e : RowLabel R g, Option (MeshClockValue T (Ω e.1)))
    (ξ : ClockField T R g Ω) (S : Finset R) (o : ∀ a, Ω a) : Prop :=
  ∀ a ∈ S, ∃ y, (greedyMatching (insertArrivals ins ξ)).assignment a = some (y, o a) ∧ ins (a, y) = none

/-- L3.10g (03:1042–1078): at most `n^B` prescribed distinct-label targets, realized by ordinary arrivals
under a fixed short insertion, retain their product upper bound under the finite-mesh matching law. The empty
insertion gives the raw joint target bound used at 03:1109–1110 and 03:1127–1128. -/
theorem step7_target_product_bound (B A C_g K₀ : ℝ) (hB : 1 ≤ B) (hK₀ : 0 < K₀)
    (hA : 10 * (B + K₀) < A) :
    ∃ n₀ : ℕ, ∀ n ≥ n₀, ∀ (mesh : FiniteMeshPlan n K₀) (hδ : 0 ≤ mesh.δ) (hδ1 : mesh.δ ≤ 1)
      {R : Type} [Fintype R] [DecidableEq R] {g : ℕ} {Ω : R → Type} [∀ a, Fintype (Ω a)]
      [∀ a, DecidableEq (Ω a)] (p : ∀ a, FinProb (Ω a)) (lab : ∀ a, Ω a → Fin g) (θ : ℝ),
      Real.log g ≤ C_g * n →
      (∀ y, ∑ a, labMarg (p a) (lab a) y = θ) → θ ≤ 2e-6 →
      (∀ a y, labMarg (p a) (lab a) y ≤ (n : ℝ) ^ (-A)) →
      ∀ ins : ∀ e : RowLabel R g, Option (MeshClockValue mesh.ticks (Ω e.1)),
      (insertionSize ins : ℝ) ≤ (K₀ + 1) ^ 2 * Real.log n →
      ∀ (S : Finset R) (o : ∀ a, Ω a), Set.InjOn (fun a => lab a (o a)) S →
      (S.card : ℝ) ≤ (n : ℝ) ^ B →
      (clockFieldLaw (samplingEdgeClockLaw (T := mesh.ticks) mesh.δ hδ hδ1 p lab)).pr
        (fun ξ => matchesTargetsOrdinarily ins ξ S o) ≤
        (1 + (n : ℝ)⁻¹) * ∏ a ∈ S, (p a).w (o a) := by
  classical
  refine ⟨2, ?_⟩
  intro n hn mesh hδ hδ1 R _ _ g Ω _ _ p lab θ hlogg hcolumns hθ hsmall ins hins S o hInj hS
  let law := clockFieldLaw (samplingEdgeClockLaw (T := mesh.ticks) mesh.δ hδ hδ1 p lab)
  by_cases hg0 : g = 0
  · subst g
    have hSempty : S = ∅ := by
      ext a
      constructor
      · intro _
        exact Fin.elim0 (lab a (o a))
      · intro ha
        simp at ha
    subst S
    have hprob : law.pr (fun _ : ClockField mesh.ticks R 0 Ω => True) = 1 := by
      simpa [FinProb.pr] using law.sum_eq_one
    have hInv : 0 ≤ (n : ℝ)⁻¹ := inv_nonneg.mpr (by positivity)
    have hgoal : law.pr (fun _ : ClockField mesh.ticks R 0 Ω => True) ≤
        (1 + (n : ℝ)⁻¹) * ∏ a ∈ (∅ : Finset R), (p a).w (o a) := by
      rw [hprob]
      simp only [Finset.prod_empty]
      nlinarith
    simpa [matchesTargetsOrdinarily] using hgoal
  · sorry

set_option maxHeartbeats 800000 in
/-- L3.10g, unmatched singleton (03:1079–1082): under a fixed short insertion a row stays unmatched with
probability at most `n^{-(1-θ)K₀}` up to a constant factor, since its free label mass stays above `1 - θ`. -/
theorem step7_unmatched_singleton (B A C_g K₀ : ℝ) (hB : 1 ≤ B) (hK₀ : 0 < K₀)
    (hA : 10 * (B + K₀) < A) :
    ∃ n₀ : ℕ, ∀ n ≥ n₀, ∀ (mesh : FiniteMeshPlan n K₀) (hδ : 0 ≤ mesh.δ) (hδ1 : mesh.δ ≤ 1)
      {R : Type} [Fintype R] [DecidableEq R] {g : ℕ} {Ω : R → Type} [∀ a, Fintype (Ω a)]
      [∀ a, DecidableEq (Ω a)] (p : ∀ a, FinProb (Ω a)) (lab : ∀ a, Ω a → Fin g) (θ : ℝ),
      Real.log g ≤ C_g * n →
      (∀ y, ∑ a, labMarg (p a) (lab a) y = θ) → θ ≤ 2e-6 →
      (∀ a y, labMarg (p a) (lab a) y ≤ (n : ℝ) ^ (-A)) →
      ∀ ins : ∀ e : RowLabel R g, Option (MeshClockValue mesh.ticks (Ω e.1)),
      (insertionSize ins : ℝ) ≤ (K₀ + 1) ^ 2 * Real.log n →
      ∀ a : R,
      (clockFieldLaw (samplingEdgeClockLaw (T := mesh.ticks) mesh.δ hδ hδ1 p lab)).pr
        (fun ξ => (greedyMatching (insertArrivals ins ξ)).assignment a = none) ≤
        2 * (n : ℝ) ^ (-((1 - θ) * K₀)) := by
  classical
  obtain ⟨n₆, htrack⟩ := step6_background_tracking B A C_g K₀ hB hK₀ hA
  have hBexp : 0 < 3 * B - 1 := by linarith
  have hAexp : 0 < A - 2 := by linarith
  let err (n : ℕ) : ℝ :=
    (K₀ + 1) * (n : ℝ) ^ (1 - 3 * B) +
      (K₀ + 1) ^ 3 * (n : ℝ) ^ (2 - A)
  have hErr1 : Tendsto (fun n : ℕ => (n : ℝ) ^ (1 - 3 * B)) atTop (nhds 0) := by
    have h := (tendsto_rpow_neg_atTop hBexp).comp tendsto_natCast_atTop_atTop
    simpa [Function.comp_def, neg_sub] using h
  have hErr2 : Tendsto (fun n : ℕ => (n : ℝ) ^ (2 - A)) atTop (nhds 0) := by
    have h := (tendsto_rpow_neg_atTop hAexp).comp tendsto_natCast_atTop_atTop
    simpa [Function.comp_def, neg_sub] using h
  have hErr : Tendsto err atTop (nhds 0) := by
    dsimp [err]
    simpa using hErr1.const_mul (K₀ + 1) |>.add (hErr2.const_mul ((K₀ + 1) ^ 3))
  have hlog32 : 0 < Real.log (3 / 2 : ℝ) := Real.log_pos (by norm_num)
  obtain ⟨nErr, hnErr⟩ := Filter.eventually_atTop.1
    (hErr.eventually (Iio_mem_nhds hlog32))
  have hAexp3 : 0 < A / 3 - 1 := by linarith
  have hlarge : Tendsto (fun n : ℕ => (n : ℝ) ^ (A / 3 - 1)) atTop atTop := by
    exact (tendsto_rpow_atTop hAexp3).comp tendsto_natCast_atTop_atTop
  have hBadEvent : ∀ᶠ n : ℕ in atTop, K₀ + 1 ≤ (n : ℝ) ^ (A / 3 - 1) :=
    Filter.tendsto_atTop.1 hlarge (K₀ + 1)
  obtain ⟨nBad, hnBad⟩ := Filter.eventually_atTop.1 hBadEvent
  have hq : 0 < A / 3 := by linarith
  have hpowAtTop : Tendsto (fun n : ℕ => (n : ℝ) ^ (A / 3)) atTop atTop := by
    exact (tendsto_rpow_atTop hq).comp tendsto_natCast_atTop_atTop
  have hpolyExp : Tendsto
      (fun n : ℕ => ((n : ℝ) ^ (A / 3)) ^ (K₀ / (A / 3)) *
        Real.exp (-((n : ℝ) ^ (A / 3)))) atTop (nhds 0) := by
    simpa only [Function.comp_def, one_mul, neg_one_mul] using
      (tendsto_rpow_mul_exp_neg_mul_atTop_nhds_zero
        (K₀ / (A / 3)) 1 one_pos).comp hpowAtTop
  obtain ⟨nTail, hnTail⟩ := Filter.eventually_atTop.1
    (hpolyExp.eventually (Iio_mem_nhds (by norm_num : (0 : ℝ) < 1 / 2)))
  let nBase := max n₆ (max nErr (max nBad 2))
  let n₀ := max nTail nBase
  refine ⟨n₀, ?_⟩
  intro n hn mesh hδ hδ1 R _ _ g Ω _ _ p lab θ hlogg hcolumns hθ hsmall ins hins a
  have hErrn₀ : nErr ≤ n₀ := by
    apply le_trans _ (le_max_right _ _)
    change nErr ≤ max n₆ (max nErr (max nBad 2))
    exact le_trans (le_max_left _ _) (le_max_right _ _)
  have hBadn₀ : nBad ≤ n₀ := by
    apply le_trans _ (le_max_right _ _)
    change nBad ≤ max n₆ (max nErr (max nBad 2))
    exact le_trans (le_max_left _ _) (le_trans (le_max_right _ _) (le_max_right _ _))
  have hn2₀ : 2 ≤ n₀ := by
    apply le_trans _ (le_max_right _ _)
    change 2 ≤ max n₆ (max nErr (max nBad 2))
    exact le_trans (le_max_right _ _) (le_trans (le_max_right _ _) (le_max_right _ _))
  have hn6 : n₆ ≤ n :=
    le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) hn
  have hnErr0 : nErr ≤ n := le_trans hErrn₀ hn
  have hnBad0 : nBad ≤ n := le_trans hBadn₀ hn
  have hnTail0 : nTail ≤ n := le_trans (le_max_left _ _) hn
  have hn2 : 2 ≤ n := le_trans hn2₀ hn
  by_cases hg0 : g = 0
  · subst g
    have hΩ : Nonempty (Ω a) := by
      by_contra hnone
      haveI : IsEmpty (Ω a) := ⟨fun o => hnone ⟨o⟩⟩
      have hsum := (p a).sum_eq_one
      simp at hsum
    exact Fin.elim0 (lab a (Classical.choice hΩ))
  · have hg : 0 < g := Nat.pos_of_ne_zero hg0
    have hinsert (ζ ζ' : ClockField mesh.ticks R g Ω)
        (hζ : ∀ b y, b ≠ a → ζ (b, y) = ζ' (b, y)) :
        ∀ b y, b ≠ a → insertArrivals ins ζ (b, y) = insertArrivals ins ζ' (b, y) := by
      intro b y hb
      simp [insertArrivals, hζ b y hb]
    have hprocess : ∀ (ζ ζ' : ClockField mesh.ticks R g Ω),
        (∀ b y, b ≠ a → ζ (b, y) = ζ' (b, y)) →
        ∀ (s : GreedyState R g Ω) (e : ClockCandidate mesh.ticks R g Ω),
          e.1 ≠ a → processArrival ζ s e = processArrival ζ' s e := by
      intro ζ ζ' hζ s e he
      have hca : candidateIsArrival ζ e ↔ candidateIsArrival ζ' e := by
        unfold candidateIsArrival
        rw [hζ e.1 e.2.1 he]
      unfold processArrival
      rw [hca]
    have hfold (ζ ζ' : ClockField mesh.ticks R g Ω)
        (hζ : ∀ b y, b ≠ a → ζ (b, y) = ζ' (b, y))
        (events : List (ClockCandidate mesh.ticks R g Ω))
        (s : GreedyState R g Ω) (hout : ∀ e ∈ events, e.1 ≠ a) :
        events.foldl (fun s e => processArrival ζ s e) s =
          events.foldl (fun s e => processArrival ζ' s e) s := by
      induction events generalizing s with
      | nil => rfl
      | cons e events ih =>
          simp only [List.foldl_cons]
          have he := hout e (by simp)
          have hout' : ∀ f ∈ events, f.1 ≠ a := by
            intro f hf
            exact hout f (by simp [hf])
          rw [hprocess ζ ζ' hζ s e he]
          exact ih (processArrival ζ' s e) hout'
    have hfilter (ζ : ClockField mesh.ticks R g Ω) (t : Fin (mesh.ticks + 1)) :
        (clockEventList ζ).filter (fun e =>
          e.2.2.1.val < t.val ∧ e.1 ∉ ({a} : Finset R) ∧
            e.2.1 ∉ (∅ : Finset (Fin g))) =
          ((clockEventList ζ).filter (fun e => e.1 ≠ a)).filter
            (fun e => e.2.2.1.val < t.val) := by
      simp [List.filter_filter, Finset.mem_singleton, and_assoc, and_left_comm, and_comm,
        Bool.and_assoc, Bool.and_left_comm, Bool.and_comm]
    have hbackground (ζ ζ' : ClockField mesh.ticks R g Ω)
        (hζ : ∀ b y, b ≠ a → ζ (b, y) = ζ' (b, y))
        (t : Fin (mesh.ticks + 1)) :
        matchingThrough (insertArrivals ins ζ) {a} (∅ : Finset (Fin g)) t =
          matchingThrough (insertArrivals ins ζ') {a} (∅ : Finset (Fin g)) t := by
      unfold matchingThrough
      rw [hfilter, hfilter]
      rw [clockEventList_filter_row_eq _ _ a (hinsert ζ ζ' hζ)]
      apply hfold (insertArrivals ins ζ) (insertArrivals ins ζ') (hinsert ζ ζ' hζ)
      intro e he
      have he' := (List.mem_filter.mp he).1
      exact of_decide_eq_true (List.mem_filter.mp he').2
    let y₀ : Fin g := ⟨0, hg⟩
    have hθ0 : 0 ≤ θ := by
      rw [← hcolumns y₀]
      exact Finset.sum_nonneg fun b hb => labMarg_nonneg (p b) (lab b) y₀
    have hθ1 : θ ≤ 1 := by linarith
    have htrajectory_bounds (m : ℕ) :
        0 ≤ (backgroundTrajectory mesh.δ θ m).1 ∧
        (backgroundTrajectory mesh.δ θ m).1 ≤ 1 ∧
        0 ≤ (backgroundTrajectory mesh.δ θ m).2 ∧
        (backgroundTrajectory mesh.δ θ m).2 ≤ 1 := by
      induction m with
      | zero => simp [backgroundTrajectory]
      | succ m ih =>
          rcases ih with ⟨hx0, hx1, hz0, hz1⟩
          simp only [backgroundTrajectory, backgroundStep]
          have hxform :
              (backgroundTrajectory mesh.δ θ m).1 - mesh.δ * θ *
                  (backgroundTrajectory mesh.δ θ m).2 *
                  (backgroundTrajectory mesh.δ θ m).1 =
                (backgroundTrajectory mesh.δ θ m).1 *
                  (1 - mesh.δ * θ * (backgroundTrajectory mesh.δ θ m).2) := by ring
          have hzform :
              (backgroundTrajectory mesh.δ θ m).2 - mesh.δ *
                  (backgroundTrajectory mesh.δ θ m).1 *
                  (backgroundTrajectory mesh.δ θ m).2 =
                (backgroundTrajectory mesh.δ θ m).2 *
                  (1 - mesh.δ * (backgroundTrajectory mesh.δ θ m).1) := by ring
          rw [hxform, hzform]
          have hδθ : mesh.δ * θ ≤ 1 :=
            mul_le_one₀ hδ1 hθ0 hθ1
          have hfx0 : 0 ≤ 1 - mesh.δ * θ * (backgroundTrajectory mesh.δ θ m).2 := by
            have hmul := mul_le_one₀ hδθ hz0 hz1
            linarith
          have hfx1 : 1 - mesh.δ * θ * (backgroundTrajectory mesh.δ θ m).2 ≤ 1 := by
            have hprod0 : 0 ≤ mesh.δ * θ * (backgroundTrajectory mesh.δ θ m).2 :=
              mul_nonneg (mul_nonneg hδ hθ0) hz0
            linarith
          have hfz0 : 0 ≤ 1 - mesh.δ * (backgroundTrajectory mesh.δ θ m).1 := by
            have hmul := mul_le_one₀ hδ1 hx0 hx1
            linarith
          have hfz1 : 1 - mesh.δ * (backgroundTrajectory mesh.δ θ m).1 ≤ 1 := by
            have hprod0 : 0 ≤ mesh.δ * (backgroundTrajectory mesh.δ θ m).1 :=
              mul_nonneg hδ hx0
            linarith
          exact ⟨mul_nonneg hx0 hfx0, mul_le_one₀ hx1 hfx0 hfx1,
            mul_nonneg hz0 hfz0, mul_le_one₀ hz1 hfz0 hfz1⟩
    have htrajectory_invariant (m : ℕ) :
        (backgroundTrajectory mesh.δ θ m).1 -
            θ * (backgroundTrajectory mesh.δ θ m).2 = 1 - θ := by
      induction m with
      | zero => simp [backgroundTrajectory]
      | succ m ih =>
          simp only [backgroundTrajectory, backgroundStep]
          calc
            (backgroundTrajectory mesh.δ θ m).1 -
                  mesh.δ * θ * (backgroundTrajectory mesh.δ θ m).2 *
                    (backgroundTrajectory mesh.δ θ m).1 -
                θ * ((backgroundTrajectory mesh.δ θ m).2 -
                  mesh.δ * (backgroundTrajectory mesh.δ θ m).1 *
                    (backgroundTrajectory mesh.δ θ m).2) =
                (backgroundTrajectory mesh.δ θ m).1 -
                  θ * (backgroundTrajectory mesh.δ θ m).2 := by ring
            _ = 1 - θ := ih
    have htrajectory_lower (m : ℕ) :
        1 - θ ≤ (backgroundTrajectory mesh.δ θ m).1 := by
      have hinv := htrajectory_invariant m
      have hz0 := (htrajectory_bounds m).2.2.1
      nlinarith [mul_nonneg hθ0 hz0]
    have hErrSmall : err n ≤ Real.log (3 / 2 : ℝ) := (hnErr n hnErr0).le
    have hBadLarge : K₀ + 1 ≤ (n : ℝ) ^ (A / 3 - 1) := hnBad n hnBad0
    have hcard :
        (((({a} : Finset R).card + (∅ : Finset (Fin g)).card : ℕ) : ℝ)) ≤
          2 * (n : ℝ) ^ B := by
      simp
      have hn1 : 1 ≤ n := le_trans (by norm_num) hn2
      have hnR : (1 : ℝ) ≤ n := by exact_mod_cast hn1
      have hpow : 1 ≤ (n : ℝ) ^ B := Real.one_le_rpow hnR (by linarith)
      nlinarith
    let Good : ClockField mesh.ticks R g Ω → Prop := fun ζ =>
      ∀ t : Fin (mesh.ticks + 1),
        (∀ b, |availableRowRate (fun b y => labMarg (p b) (lab b) y)
          (insertArrivals ins ζ) {a} (∅ : Finset (Fin g)) b t -
            (backgroundTrajectory mesh.δ θ t.val).1| ≤ (n : ℝ) ^ (-3 * B)) ∧
        (∀ y, |availableLabelRate (fun b y => labMarg (p b) (lab b) y)
          (insertArrivals ins ζ) {a} (∅ : Finset (Fin g)) y t -
            θ * (backgroundTrajectory mesh.δ θ t.val).2| ≤ (n : ℝ) ^ (-3 * B))
    have hGoodProb :
        (clockFieldLaw (samplingEdgeClockLaw (T := mesh.ticks) mesh.δ hδ hδ1 p lab)).pr Good ≥
          1 - Real.exp (-((n : ℝ) ^ (A / 3))) := by
      simpa [Good] using htrack n hn6 mesh hδ hδ1 p lab θ hlogg hcolumns hθ hsmall
        {a} (∅ : Finset (Fin g)) hcard ins hins
    have hGoodInvariant (ζ ζ' : ClockField mesh.ticks R g Ω)
        (hζ : ∀ b y, b ≠ a → ζ (b, y) = ζ' (b, y)) : Good ζ ↔ Good ζ' := by
      have hbg := hbackground ζ ζ' hζ
      constructor <;> intro hG t
      · rcases hG t with ⟨hrow, hlabel⟩
        refine ⟨?_, ?_⟩
        · intro b
          have hb := hrow b
          simpa [availableRowRate, hbg t] using hb
        · intro y
          have hy := hlabel y
          simpa [availableLabelRate, hbg t] using hy
      · rcases hG t with ⟨hrow, hlabel⟩
        refine ⟨?_, ?_⟩
        · intro b
          have hb := hrow b
          simpa [availableRowRate, (hbg t).symm] using hb
        · intro y
          have hy := hlabel y
          simpa [availableLabelRate, (hbg t).symm] using hy
    let edgeLaw := samplingEdgeClockLaw (T := mesh.ticks) mesh.δ hδ hδ1 p lab
    let law := clockFieldLaw edgeLaw
    let rowEdges : Finset (RowLabel R g) := Finset.univ.filter (fun e => e.1 = a)
    let unmatched (ζ : ClockField mesh.ticks R g Ω) : Prop :=
      (greedyMatching (insertArrivals ins ζ)).assignment a = none
    let indicator (ζ : ClockField mesh.ticks R g Ω) : ℝ :=
      if unmatched ζ then 1 else 0
    have hprExpect : law.pr unmatched = law.expect indicator := by
      unfold FinProb.pr FinProb.expect
      apply Finset.sum_congr rfl
      intro ζ hζ
      by_cases h : unmatched ζ <;> simp [indicator, h] <;> ring
    have hsplit : law.expect indicator =
        ∑ r : (∀ e : {e // e ∈ rowEdges}, MeshClockValue mesh.ticks (Ω e.1.1)),
          ∑ b : (∀ e : {e // e ∉ rowEdges}, MeshClockValue mesh.ticks (Ω e.1.1)),
            (FinProb.pi (fun e : {e // e ∈ rowEdges} => edgeLaw e.1)).w r *
              (FinProb.pi (fun e : {e // e ∉ rowEdges} => edgeLaw e.1)).w b *
              indicator ((Equiv.piEquivPiSubtypeProd (fun e => e ∈ rowEdges)
                (fun e => MeshClockValue mesh.ticks (Ω e.1))).symm (r, b)) := by
      simpa [law, edgeLaw, clockFieldLaw] using
        (pi_expect_split_p_clock_r4 edgeLaw rowEdges indicator)
    let rowIndex := {e : RowLabel R g // e ∈ rowEdges}
    let outsideIndex := {e : RowLabel R g // e ∉ rowEdges}
    let splitEquiv := Equiv.piEquivPiSubtypeProd (fun e : RowLabel R g => e ∈ rowEdges)
      (fun e => MeshClockValue mesh.ticks (Ω e.1))
    let rowDefault : ∀ e : rowIndex, MeshClockValue mesh.ticks (Ω e.1.1) := fun _ => .noArrival
    let fill (r : ∀ e : rowIndex, MeshClockValue mesh.ticks (Ω e.1.1))
        (b : ∀ e : outsideIndex, MeshClockValue mesh.ticks (Ω e.1.1)) :
        ClockField mesh.ticks R g Ω := splitEquiv.symm (r, b)
    let outsideBackground (b : ∀ e : outsideIndex, MeshClockValue mesh.ticks (Ω e.1.1)) :=
      matchingThrough (insertArrivals ins (fill rowDefault b)) {a} (∅ : Finset (Fin g))
        (Fin.last mesh.ticks)
    let required (b : ∀ e : outsideIndex, MeshClockValue mesh.ticks (Ω e.1.1))
        (e : rowIndex) : Prop :=
      ins e.1 = none ∧ ¬ labelUsed (outsideBackground b) e.1.2
    let NoHit (b : ∀ e : outsideIndex, MeshClockValue mesh.ticks (Ω e.1.1))
        (r : ∀ e : rowIndex, MeshClockValue mesh.ticks (Ω e.1.1)) : Prop :=
      ∀ e : rowIndex, required b e → r e = .noArrival
    let rowEquiv : rowIndex ≃ Fin g := {
      toFun := fun e => e.1.2
      invFun := fun y => ⟨(a, y), by simp [rowEdges]⟩
      left_inv := by
        intro e
        rcases e with ⟨⟨b, y⟩, he⟩
        have hb : b = a := (Finset.mem_filter.mp he).2
        apply Subtype.ext
        simp [hb]
      right_inv := by intro y; rfl
    }
    have hNoHitProb (b : ∀ e : outsideIndex, MeshClockValue mesh.ticks (Ω e.1.1)) :
        (FinProb.pi (fun e : rowIndex => edgeLaw e.1)).pr (NoHit b) =
          ∏ e : rowIndex, if ins e.1 = none ∧
            ¬ labelUsed (outsideBackground b) e.1.2 then
              (edgeLaw e.1).pr (fun x => x = .noArrival) else 1 := by
      simp only [NoHit]
      exact pi_pr_required_coordinate_eq
        (P := fun e : rowIndex => edgeLaw e.1)
        (required := required b)
        (z := fun _ => MeshClockValue.noArrival)
    let edgeRate (e : rowIndex) : ℝ := labMarg (p e.1.1) (lab e.1.1) e.1.2
    have hEdgeNoArrival (e : rowIndex) :
        (edgeLaw e.1).pr (fun x => x = MeshClockValue.noArrival) =
          survival mesh.δ (edgeRate e) mesh.ticks := by
      have hr0 : 0 ≤ edgeRate e := by simp [edgeRate, labMarg_nonneg]
      have hr1 : edgeRate e ≤ 1 := by simp [edgeRate, labMarg_le_one]
      have hbase : 0 ≤ 1 - mesh.δ * edgeRate e := by
        apply sub_nonneg.mpr
        have hmul := mul_le_one₀ hδ1 hr0 hr1
        simpa [edgeRate] using hmul
      simpa [edgeLaw, samplingEdgeClockLaw, edgeRate] using
        (outputEdgeClockLaw_noArrival_prob mesh.δ hδ (p e.1.1) (lab e.1.1)
          e.1.2 hbase)
    have hNoHitProbExp (b : ∀ e : outsideIndex, MeshClockValue mesh.ticks (Ω e.1.1)) :
        (FinProb.pi (fun e : rowIndex => edgeLaw e.1)).pr (NoHit b) ≤
          Real.exp (-mesh.δ * (mesh.ticks : ℝ) *
            ∑ e : rowIndex, if required b e then edgeRate e else 0) := by
      rw [hNoHitProb b]
      have hsum :
          (∑ e : rowIndex, if required b e then -mesh.δ * edgeRate e * (mesh.ticks : ℝ) else 0) =
            -mesh.δ * (mesh.ticks : ℝ) *
              ∑ e : rowIndex, if required b e then edgeRate e else 0 := by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro e he
        split_ifs <;> ring
      have hterm (e : rowIndex) :
          (if required b e then
            Real.exp (-mesh.δ * edgeRate e * (mesh.ticks : ℝ)) else 1) =
            Real.exp (if required b e then
              -mesh.δ * edgeRate e * (mesh.ticks : ℝ) else 0) := by
        split_ifs <;> simp
      calc
        (∏ e : rowIndex,
            if required b e then (edgeLaw e.1).pr (fun x => x = MeshClockValue.noArrival) else 1) =
            ∏ e : rowIndex, if required b e then survival mesh.δ (edgeRate e) mesh.ticks else 1 := by
              apply Finset.prod_congr rfl
              intro e he
              by_cases hreq : required b e <;> simp [hreq, hEdgeNoArrival e]
        _ ≤ ∏ e : rowIndex,
              if required b e then Real.exp (-mesh.δ * edgeRate e * (mesh.ticks : ℝ)) else 1 := by
              apply Finset.prod_le_prod₀
              · intro e he
                by_cases hreq : required b e
                · simp [hreq]
                  have hbase : 0 ≤ 1 - mesh.δ * edgeRate e :=
                    sub_nonneg.mpr (mul_le_one₀ hδ1
                      (labMarg_nonneg (p e.1.1) (lab e.1.1) e.1.2)
                      (labMarg_le_one (p e.1.1) (lab e.1.1) e.1.2))
                  unfold survival
                  exact pow_nonneg hbase _
                · simp [hreq]
              · intro e he
                by_cases hreq : required b e
                · simp [hreq]
                  simpa [edgeRate, mul_assoc, mul_comm, mul_left_comm, neg_mul] using
                    (survival_le_exp (T := mesh.ticks) hδ hδ1
                      (labMarg_nonneg (p e.1.1) (lab e.1.1) e.1.2)
                      (labMarg_le_one (p e.1.1) (lab e.1.1) e.1.2))
                · simp [hreq]
        _ = Real.exp (-mesh.δ * (mesh.ticks : ℝ) *
              ∑ e : rowIndex, if required b e then edgeRate e else 0) := by
              simp_rw [hterm]
              rw [← Real.exp_sum, hsum]
    let rateSum (b : ∀ e : outsideIndex, MeshClockValue mesh.ticks (Ω e.1.1)) : ℝ :=
      ∑ e : rowIndex, if required b e then edgeRate e else 0
    have hrateSum (b : ∀ e : outsideIndex, MeshClockValue mesh.ticks (Ω e.1.1)) :
        rateSum b = ∑ y : Fin g,
          if ins (a, y) = none ∧ ¬ labelUsed (outsideBackground b) y then
            labMarg (p a) (lab a) y else 0 := by
      dsimp [rateSum]
      exact Fintype.sum_equiv rowEquiv _ _ (by
        intro e
        rcases e with ⟨⟨b, y⟩, he⟩
        have hrow : b = a := (Finset.mem_filter.mp he).2
        subst b
        simp [required, edgeRate, rowEquiv])
    let freeLabel (b : ∀ e : outsideIndex, MeshClockValue mesh.ticks (Ω e.1.1))
        (y : Fin g) : Prop := ¬ labelUsed (outsideBackground b) y
    have hAvailableEq (b : ∀ e : outsideIndex, MeshClockValue mesh.ticks (Ω e.1.1)) :
        availableRowRate (fun b y => labMarg (p b) (lab b) y)
            (insertArrivals ins (fill rowDefault b)) {a} (∅ : Finset (Fin g)) a
            (Fin.last mesh.ticks) =
          ∑ y : Fin g, if freeLabel b y then labMarg (p a) (lab a) y else 0 := by
      simp [availableRowRate, outsideBackground, freeLabel]
    have hAvailableLower (b : ∀ e : outsideIndex, MeshClockValue mesh.ticks (Ω e.1.1))
        (hG : Good (fill rowDefault b)) :
        1 - θ - (n : ℝ) ^ (-3 * B) ≤
          availableRowRate (fun b y => labMarg (p b) (lab b) y)
            (insertArrivals ins (fill rowDefault b)) {a} (∅ : Finset (Fin g)) a
            (Fin.last mesh.ticks) := by
      have htrackRow := (hG (Fin.last mesh.ticks)).1 a
      have htrackRow' :
          |availableRowRate (fun b y => labMarg (p b) (lab b) y)
              (insertArrivals ins (fill rowDefault b)) {a} (∅ : Finset (Fin g)) a
              (Fin.last mesh.ticks) - (backgroundTrajectory mesh.δ θ mesh.ticks).1| ≤
            (n : ℝ) ^ (-3 * B) := by simpa using htrackRow
      have htraj := htrajectory_lower mesh.ticks
      have hlow := (abs_le.mp htrackRow').1
      linarith
    let prescribedLabels : Finset (Fin g) :=
      Finset.univ.filter (fun y => (ins (a, y)).isSome)
    have hpresCard : prescribedLabels.card ≤ insertionSize ins := by
      have hinj : Function.Injective (fun y : Fin g => (a, y)) := by
        intro y z h
        exact congrArg Prod.snd h
      have hsub : prescribedLabels.image (fun y => (a, y)) ⊆
          Finset.univ.filter (fun e : RowLabel R g => (ins e).isSome) := by
        intro e he
        obtain ⟨y, hy, rfl⟩ := Finset.mem_image.mp he
        exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, (Finset.mem_filter.mp hy).2⟩
      unfold insertionSize
      calc
        prescribedLabels.card = (prescribedLabels.image (fun y => (a, y))).card :=
          (Finset.card_image_of_injective _ hinj).symm
        _ ≤ (Finset.univ.filter (fun e : RowLabel R g => (ins e).isSome)).card :=
          Finset.card_le_card hsub
    have hpresRate (b : ∀ e : outsideIndex, MeshClockValue mesh.ticks (Ω e.1.1)) :
        (∑ y : Fin g,
          if (ins (a, y)).isSome ∧ freeLabel b y then labMarg (p a) (lab a) y else 0) ≤
            (prescribedLabels.card : ℝ) * (n : ℝ) ^ (-A) := by
      calc
        (∑ y : Fin g,
          if (ins (a, y)).isSome ∧ freeLabel b y then labMarg (p a) (lab a) y else 0) ≤
            ∑ y : Fin g, if (ins (a, y)).isSome then (n : ℝ) ^ (-A) else 0 := by
              apply Finset.sum_le_sum
              intro y hy
              by_cases hi : (ins (a, y)).isSome
              · by_cases hf : freeLabel b y
                · simp [hi, hf]
                  exact hsmall a y
                · simp [hi, hf]
                  positivity
              · simp [hi]
        _ = (prescribedLabels.card : ℝ) * (n : ℝ) ^ (-A) := by
              change (∑ y ∈ (Finset.univ : Finset (Fin g)),
                if (ins (a, y)).isSome then (n : ℝ) ^ (-A) else 0) = _
              rw [← Finset.sum_filter]
              simp [prescribedLabels, mul_comm]
    have hrateLower (b : ∀ e : outsideIndex, MeshClockValue mesh.ticks (Ω e.1.1))
        (hG : Good (fill rowDefault b)) :
        1 - θ - ((n : ℝ) ^ (-3 * B) + (K₀ + 1) ^ 2 * (n : ℝ) ^ (1 - A)) ≤
          rateSum b := by
      have hdiff :
          availableRowRate (fun b y => labMarg (p b) (lab b) y)
              (insertArrivals ins (fill rowDefault b)) {a} (∅ : Finset (Fin g)) a
              (Fin.last mesh.ticks) - rateSum b =
            ∑ y : Fin g,
              if (ins (a, y)).isSome ∧ freeLabel b y then labMarg (p a) (lab a) y else 0 := by
        rw [hAvailableEq b, hrateSum b]
        rw [← Finset.sum_sub_distrib]
        apply Finset.sum_congr rfl
        intro y hy
        by_cases hf : freeLabel b y <;> cases ho : ins (a, y) <;>
          simp [required, freeLabel, hf, ho]
      have hlow := hAvailableLower b hG
      have hpres := hpresRate b
      have hpres' : (prescribedLabels.card : ℝ) * (n : ℝ) ^ (-A) ≤
          (K₀ + 1) ^ 2 * (n : ℝ) ^ (1 - A) := by
        have hnR : (1 : ℝ) ≤ n := by exact_mod_cast (le_trans (by norm_num) hn2)
        have hlog : Real.log (n : ℝ) ≤ n := Real.log_le_self (by positivity)
        have hcount : (prescribedLabels.card : ℝ) ≤ (K₀ + 1) ^ 2 * Real.log n :=
          le_trans (by exact_mod_cast hpresCard) hins
        have hpow : (n : ℝ) * (n : ℝ) ^ (-A) = (n : ℝ) ^ (1 - A) := by
          calc
            (n : ℝ) * (n : ℝ) ^ (-A) = (n : ℝ) ^ (1 : ℝ) * (n : ℝ) ^ (-A) := by
              rw [Real.rpow_one]
            _ = (n : ℝ) ^ (1 + (-A)) := (Real.rpow_add (by positivity) 1 (-A)).symm
            _ = (n : ℝ) ^ (1 - A) := by congr 1 <;> ring
        calc
          (prescribedLabels.card : ℝ) * (n : ℝ) ^ (-A) ≤
              (K₀ + 1) ^ 2 * Real.log n * (n : ℝ) ^ (-A) :=
                mul_le_mul_of_nonneg_right hcount (by positivity)
          _ ≤ (K₀ + 1) ^ 2 * n * (n : ℝ) ^ (-A) := by
                gcongr
          _ = (K₀ + 1) ^ 2 * (n : ℝ) ^ (1 - A) := by rw [mul_assoc, hpow]
      linarith
    let loss : ℝ := (n : ℝ) ^ (-3 * B) + (K₀ + 1) ^ 2 * (n : ℝ) ^ (1 - A)
    let dT : ℝ := (mesh.ticks : ℝ) * mesh.δ
    have hnpos : 0 < (n : ℝ) := by positivity
    have hnR : (1 : ℝ) ≤ n := by exact_mod_cast (le_trans (by norm_num) hn2)
    have hlogn : Real.log (n : ℝ) ≤ n := Real.log_le_self hnpos.le
    have hdt0 : 0 ≤ dT := by positivity
    have htimeLower : K₀ * Real.log (n : ℝ) ≤ dT := by
      simpa [dT, mesh.horizon_eq] using mesh.covers_horizon
    have htimeUpper : dT ≤ (K₀ + 1) * n := by
      have hcover := mesh.least_cover
      rw [mesh.horizon_eq] at hcover
      have hmid : K₀ * Real.log (n : ℝ) + mesh.δ ≤ K₀ * n + 1 := by
        exact add_le_add (mul_le_mul_of_nonneg_left hlogn hK₀.le) hδ1
      have hlast : K₀ * n + 1 ≤ (K₀ + 1) * n := by nlinarith
      exact (lt_of_lt_of_le (by simpa [dT] using hcover) (le_trans hmid hlast)).le
    have hpowErr1 : (n : ℝ) * (n : ℝ) ^ (-3 * B) = (n : ℝ) ^ (1 - 3 * B) := by
      calc
        (n : ℝ) * (n : ℝ) ^ (-3 * B) = (n : ℝ) ^ (1 : ℝ) * (n : ℝ) ^ (-3 * B) := by
          rw [Real.rpow_one]
        _ = (n : ℝ) ^ (1 + (-3 * B)) := (Real.rpow_add hnpos 1 (-3 * B)).symm
        _ = (n : ℝ) ^ (1 - 3 * B) := by congr 1 <;> ring
    have hpowErr2 : (n : ℝ) * (n : ℝ) ^ (1 - A) = (n : ℝ) ^ (2 - A) := by
      calc
        (n : ℝ) * (n : ℝ) ^ (1 - A) = (n : ℝ) ^ (1 : ℝ) * (n : ℝ) ^ (1 - A) := by
          rw [Real.rpow_one]
        _ = (n : ℝ) ^ (1 + (1 - A)) := (Real.rpow_add hnpos 1 (1 - A)).symm
        _ = (n : ℝ) ^ (2 - A) := by congr 1 <;> ring
    have htimeErr : dT * loss ≤ err n := by
      calc
        dT * loss ≤ (K₀ + 1) * n * loss :=
          mul_le_mul_of_nonneg_right htimeUpper (by positivity)
        _ = (K₀ + 1) * ((n : ℝ) * (n : ℝ) ^ (-3 * B)) +
              (K₀ + 1) ^ 3 * ((n : ℝ) * (n : ℝ) ^ (1 - A)) := by
              dsimp [loss]
              ring
        _ = err n := by rw [hpowErr1, hpowErr2]
    have hcoeff0 : 0 ≤ 1 - θ := by linarith
    have hExpUpper : -dT * (1 - θ - loss) ≤
        -K₀ * Real.log (n : ℝ) * (1 - θ) + err n := by
      have hfirst : -dT * (1 - θ) ≤ -K₀ * Real.log (n : ℝ) * (1 - θ) := by
        have hmul := mul_nonneg (sub_nonneg.mpr htimeLower) hcoeff0
        nlinarith [htimeLower]
      calc
        -dT * (1 - θ - loss) = -dT * (1 - θ) + dT * loss := by ring
        _ ≤ -K₀ * Real.log (n : ℝ) * (1 - θ) + err n :=
          add_le_add hfirst htimeErr
    have hGoodExpConst :
        Real.exp (-dT * (1 - θ - loss)) ≤
          (3 / 2 : ℝ) * (n : ℝ) ^ (-((1 - θ) * K₀)) := by
      have hExp := Real.exp_le_exp.mpr hExpUpper
      have hErrExponent :
          -K₀ * Real.log (n : ℝ) * (1 - θ) + err n ≤
            -K₀ * Real.log (n : ℝ) * (1 - θ) + Real.log (3 / 2 : ℝ) := by
        linarith [hErrSmall]
      have hExpErr :
          Real.exp (-K₀ * Real.log (n : ℝ) * (1 - θ) + err n) ≤
            Real.exp (-K₀ * Real.log (n : ℝ) * (1 - θ) + Real.log (3 / 2 : ℝ)) :=
        Real.exp_le_exp.mpr hErrExponent
      have hpowEq : Real.exp (-K₀ * Real.log (n : ℝ) * (1 - θ)) =
          (n : ℝ) ^ (-((1 - θ) * K₀)) := by
        calc
          Real.exp (-K₀ * Real.log (n : ℝ) * (1 - θ)) =
              Real.exp (Real.log (n : ℝ) * (-((1 - θ) * K₀))) := by congr 1 <;> ring
          _ = (n : ℝ) ^ (-((1 - θ) * K₀)) :=
              (Real.rpow_def_of_pos hnpos _).symm
      calc
        Real.exp (-dT * (1 - θ - loss)) ≤
            Real.exp (-K₀ * Real.log (n : ℝ) * (1 - θ) + err n) := hExp
        _ ≤ Real.exp (-K₀ * Real.log (n : ℝ) * (1 - θ) + Real.log (3 / 2 : ℝ)) := hExpErr
        _ = (3 / 2 : ℝ) * (n : ℝ) ^ (-((1 - θ) * K₀)) := by
              rw [Real.exp_add, hpowEq, Real.exp_log (by norm_num : (0 : ℝ) < 3 / 2)]
              ring
    have hfillRow (r : ∀ e : rowIndex, MeshClockValue mesh.ticks (Ω e.1.1))
        (b : ∀ e : outsideIndex, MeshClockValue mesh.ticks (Ω e.1.1))
        (e : rowIndex) : fill r b e.1 = r e := by
      simp [fill, splitEquiv, e.2]
    have hfillOutside (r r' : ∀ e : rowIndex, MeshClockValue mesh.ticks (Ω e.1.1))
        (b : ∀ e : outsideIndex, MeshClockValue mesh.ticks (Ω e.1.1))
        (b₀ : R) (y : Fin g) (hb₀ : b₀ ≠ a) :
        fill r b (b₀, y) = fill r' b (b₀, y) := by
      have hnot : (b₀, y) ∉ rowEdges := by simp [rowEdges, hb₀]
      simp [fill, splitEquiv, hnot]
    have hfields (r r' : ∀ e : rowIndex, MeshClockValue mesh.ticks (Ω e.1.1))
        (b : ∀ e : outsideIndex, MeshClockValue mesh.ticks (Ω e.1.1)) :
        ∀ b₀ y, b₀ ≠ a →
          insertArrivals ins (fill r b) (b₀, y) =
            insertArrivals ins (fill r' b) (b₀, y) := by
      intro b₀ y hb₀
      simp [insertArrivals, hfillOutside r r' b b₀ y hb₀]
    have hNoHitEvent :
        ∀ (r : ∀ e : rowIndex, MeshClockValue mesh.ticks (Ω e.1.1))
          (b : ∀ e : outsideIndex, MeshClockValue mesh.ticks (Ω e.1.1)),
          unmatched (fill r b) → NoHit b r := by
      intro r b hunmatched
      let field := insertArrivals ins (fill r b)
      have hbg := hbackground (fill r b) (fill rowDefault b)
        (hfillOutside r rowDefault b) (Fin.last mesh.ticks)
      have hthrough : matchingThrough field {a} (∅ : Finset (Fin g))
          (Fin.last mesh.ticks) =
          runGreedy field ((clockEventList field).filter (fun e => e.1 ≠ a)) := by
        unfold matchingThrough
        rw [hfilter]
        simp
      have hrow : (runGreedy field (clockEventList field)).assignment a = none := by
        simpa [unmatched, greedyMatching, field] using hunmatched
      have harr : ∀ e ∈ clockEventList field, candidateIsArrival field e := by
        intro e he
        exact (clockEventList_mem_iff_p_clock_r4 field e).1 he
      intro e hre
      rcases hre with ⟨hinsNone, hfreeBG⟩
      have hfree : ¬ labelUsed (runGreedy field
          ((clockEventList field).filter (fun e => e.1 ≠ a))) e.1.2 := by
        rw [← hthrough, hbg]
        exact hfreeBG
      have hno := runGreedy_unmatched_row_no_arrival_to_free_label field
        (clockEventList field) a e.1.2 hrow hfree harr
      have hrowEq : e.1.1 = a := (Finset.mem_filter.mp e.2).2
      cases hval : r e with
      | noArrival => rfl
      | tick t mark =>
          have hclock : field e.1 = .tick t mark := by
            simp [field, insertArrivals, hinsNone, hfillRow r b e, hval]
          let candidate : ClockCandidate mesh.ticks R g Ω := ⟨e.1.1, e.1.2, t, mark⟩
          have hmem : candidate ∈ clockEventList field := by
            apply (clockEventList_mem_iff_p_clock_r4 field candidate).2
            exact hclock
          have hfalse := hno candidate hmem hrowEq rfl
          exact False.elim hfalse
    let eventGood (ζ : ClockField mesh.ticks R g Ω) : Prop := unmatched ζ ∧ Good ζ
    let indicatorGood (ζ : ClockField mesh.ticks R g Ω) : ℝ :=
      if eventGood ζ then 1 else 0
    have hprGood : law.pr eventGood = law.expect indicatorGood := by
      unfold FinProb.pr FinProb.expect
      apply Finset.sum_congr rfl
      intro ζ hζ
      by_cases h : eventGood ζ <;> simp [indicatorGood, h] <;> ring
    have hsplitGood : law.expect indicatorGood =
        ∑ r : (∀ e : rowIndex, MeshClockValue mesh.ticks (Ω e.1.1)),
          ∑ b : (∀ e : outsideIndex, MeshClockValue mesh.ticks (Ω e.1.1)),
          (FinProb.pi (fun e : rowIndex => edgeLaw e.1)).w r *
            (FinProb.pi (fun e : outsideIndex => edgeLaw e.1)).w b *
            indicatorGood (fill r b) := by
      simpa [law, edgeLaw, clockFieldLaw, indicatorGood, fill, splitEquiv] using
        (pi_expect_split_p_clock_r4 edgeLaw rowEdges indicatorGood)
    have hGoodNoHitIndicator (r : ∀ e : rowIndex, MeshClockValue mesh.ticks (Ω e.1.1))
        (b : ∀ e : outsideIndex, MeshClockValue mesh.ticks (Ω e.1.1)) :
        indicatorGood (fill r b) ≤
          if Good (fill rowDefault b) then (if NoHit b r then 1 else 0) else 0 := by
      classical
      by_cases hG : Good (fill rowDefault b)
      · by_cases hE : eventGood (fill r b)
        · have hN : NoHit b r := hNoHitEvent r b hE.1
          change (if eventGood (fill r b) then 1 else 0) ≤ _
          rw [if_pos hE, if_pos hG, if_pos hN]
        · change (if eventGood (fill r b) then 1 else 0) ≤ _
          rw [if_neg hE, if_pos hG]
          by_cases hN : NoHit b r <;> simp [hN]
      · have hG' : ¬ Good (fill r b) := by
          intro h
          exact hG ((hGoodInvariant (fill r b) (fill rowDefault b)
            (hfillOutside r rowDefault b)).mp h)
        change (if eventGood (fill r b) then 1 else 0) ≤ _
        have hE : ¬ eventGood (fill r b) := by
          intro h
          exact hG' h.2
        rw [if_neg hE, if_neg hG]
    let rowLaw := FinProb.pi (fun e : rowIndex => edgeLaw e.1)
    let outLaw := FinProb.pi (fun e : outsideIndex => edgeLaw e.1)
    have hInner (b : ∀ e : outsideIndex, MeshClockValue mesh.ticks (Ω e.1.1)) :
        (∑ r : (∀ e : rowIndex, MeshClockValue mesh.ticks (Ω e.1.1)),
          rowLaw.w r * indicatorGood (fill r b)) ≤
          if Good (fill rowDefault b) then rowLaw.pr (NoHit b) else 0 := by
      calc
        _ ≤ ∑ r : (∀ e : rowIndex, MeshClockValue mesh.ticks (Ω e.1.1)),
            rowLaw.w r * (if Good (fill rowDefault b) then
              (if NoHit b r then 1 else 0) else 0) := by
                apply Finset.sum_le_sum
                intro r hr
                exact mul_le_mul_of_nonneg_left (hGoodNoHitIndicator r b) (rowLaw.nonneg r)
        _ = if Good (fill rowDefault b) then rowLaw.pr (NoHit b) else 0 := by
              by_cases hG : Good (fill rowDefault b)
              · simp only [hG, if_true, FinProb.pr]
                apply Finset.sum_congr rfl
                intro r hr
                by_cases hN : NoHit b r <;> simp [hN, rowLaw]
              · simp [hG]
    have hInnerMajorant (b : ∀ e : outsideIndex, MeshClockValue mesh.ticks (Ω e.1.1)) :
        (∑ r : (∀ e : rowIndex, MeshClockValue mesh.ticks (Ω e.1.1)),
          rowLaw.w r * (if Good (fill rowDefault b) then
            (if NoHit b r then 1 else 0) else 0)) ≤
          if Good (fill rowDefault b) then rowLaw.pr (NoHit b) else 0 := by
      classical
      by_cases hG : Good (fill rowDefault b)
      · simp only [hG, if_true, FinProb.pr]
        apply le_of_eq
        apply Finset.sum_congr rfl
        intro r hr
        by_cases hN : NoHit b r <;> simp [hN, rowLaw]
      · simp [hG]
    have hNoHitConditional (b : ∀ e : outsideIndex, MeshClockValue mesh.ticks (Ω e.1.1))
        (hG : Good (fill rowDefault b)) :
        rowLaw.pr (NoHit b) ≤ (3 / 2 : ℝ) * (n : ℝ) ^ (-((1 - θ) * K₀)) := by
      change (FinProb.pi (fun e : rowIndex => edgeLaw e.1)).pr (NoHit b) ≤ _
      calc
        _ ≤ Real.exp (-mesh.δ * (mesh.ticks : ℝ) * rateSum b) := hNoHitProbExp b
        _ ≤ Real.exp (-dT * (1 - θ - loss)) := by
              apply Real.exp_le_exp.mpr
              have hmul := mul_le_mul_of_nonpos_left (hrateLower b hG)
                (neg_nonpos.mpr hdt0)
              calc
                -mesh.δ * (mesh.ticks : ℝ) * rateSum b = -dT * rateSum b := by
                  dsimp [dT]
                  ring
                _ ≤ -dT * (1 - θ - loss) := hmul
        _ ≤ (3 / 2 : ℝ) * (n : ℝ) ^ (-((1 - θ) * K₀)) := hGoodExpConst
    have hGoodEventBound :
        law.pr eventGood ≤ (3 / 2 : ℝ) * (n : ℝ) ^ (-((1 - θ) * K₀)) := by
      rw [hprGood, hsplitGood]
      calc
        (∑ r : (∀ e : rowIndex, MeshClockValue mesh.ticks (Ω e.1.1)),
          ∑ b : (∀ e : outsideIndex, MeshClockValue mesh.ticks (Ω e.1.1)),
            rowLaw.w r * outLaw.w b * indicatorGood (fill r b)) ≤
          ∑ r, ∑ b, rowLaw.w r * outLaw.w b *
            (if Good (fill rowDefault b) then (if NoHit b r then 1 else 0) else 0) := by
              apply Finset.sum_le_sum
              intro r hr
              apply Finset.sum_le_sum
              intro b hb
              exact mul_le_mul_of_nonneg_left (hGoodNoHitIndicator r b)
                (mul_nonneg (rowLaw.nonneg r) (outLaw.nonneg b))
        _ = ∑ b : (∀ e : outsideIndex, MeshClockValue mesh.ticks (Ω e.1.1)),
              outLaw.w b *
                ∑ r : (∀ e : rowIndex, MeshClockValue mesh.ticks (Ω e.1.1)),
                  rowLaw.w r *
                    (if Good (fill rowDefault b) then (if NoHit b r then 1 else 0) else 0) := by
              rw [Finset.sum_comm]
              apply Finset.sum_congr rfl
              intro b hb
              calc
                (∑ r : (∀ e : rowIndex, MeshClockValue mesh.ticks (Ω e.1.1)),
                    rowLaw.w r * outLaw.w b *
                      (if Good (fill rowDefault b) then (if NoHit b r then 1 else 0) else 0)) =
                    ∑ r, outLaw.w b * (rowLaw.w r *
                      (if Good (fill rowDefault b) then (if NoHit b r then 1 else 0) else 0)) := by
                        apply Finset.sum_congr rfl
                        intro r hr
                        ring
                _ = outLaw.w b * ∑ r, rowLaw.w r *
                      (if Good (fill rowDefault b) then (if NoHit b r then 1 else 0) else 0) := by
                        rw [Finset.mul_sum]
        _ ≤ ∑ b : (∀ e : outsideIndex, MeshClockValue mesh.ticks (Ω e.1.1)),
              outLaw.w b * (if Good (fill rowDefault b) then rowLaw.pr (NoHit b) else 0) := by
              apply Finset.sum_le_sum
              intro b hb
              exact mul_le_mul_of_nonneg_left (hInnerMajorant b) (outLaw.nonneg b)
        _ ≤ ∑ b : (∀ e : outsideIndex, MeshClockValue mesh.ticks (Ω e.1.1)),
              outLaw.w b * ((3 / 2 : ℝ) * (n : ℝ) ^ (-((1 - θ) * K₀))) := by
              apply Finset.sum_le_sum
              intro b hb
              have hfactor :
                  (if Good (fill rowDefault b) then rowLaw.pr (NoHit b) else 0) ≤
                    (3 / 2 : ℝ) * (n : ℝ) ^ (-((1 - θ) * K₀)) := by
                by_cases hG : Good (fill rowDefault b)
                · simp [hG]
                  exact hNoHitConditional b hG
                · simp [hG]
                  positivity
              exact mul_le_mul_of_nonneg_left hfactor (outLaw.nonneg b)
        _ = (3 / 2 : ℝ) * (n : ℝ) ^ (-((1 - θ) * K₀)) := by
              rw [← Finset.sum_mul, outLaw.sum_eq_one]
              ring
    have hnotGood : law.pr (fun ζ => ¬ Good ζ) ≤ Real.exp (-((n : ℝ) ^ (A / 3))) := by
      have hpartition : law.pr Good + law.pr (fun ζ => ¬ Good ζ) = 1 := by
        classical
        unfold FinProb.pr
        rw [← Finset.sum_add_distrib]
        calc
          _ = Finset.univ.sum law.w := by
                apply Finset.sum_congr rfl
                intro z hz
                by_cases hG : Good z <;> simp [hG]
          _ = 1 := law.sum_eq_one
      linarith [hGoodProb]
    have htotal : law.pr unmatched ≤
        Real.exp (-((n : ℝ) ^ (A / 3))) +
          (3 / 2 : ℝ) * (n : ℝ) ^ (-((1 - θ) * K₀)) := by
      have hmono : law.pr unmatched ≤ law.pr (fun ζ => ¬ Good ζ ∨ eventGood ζ) := by
        apply finProb_pr_mono
        intro ζ hU
        by_cases hG : Good ζ
        · exact Or.inr ⟨hU, hG⟩
        · exact Or.inl hG
      calc
        law.pr unmatched ≤ law.pr (fun ζ => ¬ Good ζ ∨ eventGood ζ) := hmono
        _ ≤ law.pr (fun ζ => ¬ Good ζ) + law.pr eventGood :=
              FinProb.pr_union law _ _
        _ ≤ _ := add_le_add hnotGood hGoodEventBound
    have hOneMinusTheta : 1 - θ ≤ 1 := by linarith [hθ0]
    have hαle : (1 - θ) * K₀ ≤ K₀ := by
      simpa only [one_mul] using
        (mul_le_mul_of_nonneg_right hOneMinusTheta hK₀.le)
    have hApos : 0 < A := by linarith [hq]
    have hpowEq : ((n : ℝ) ^ (A / 3)) ^ (K₀ / (A / 3)) = (n : ℝ) ^ K₀ := by
      rw [← Real.rpow_mul hnpos.le]
      congr 1
      field_simp [ne_of_gt hq, ne_of_gt hApos]
    have hTailProduct :
        ((n : ℝ) ^ (A / 3)) ^ (K₀ / (A / 3)) *
          Real.exp (-((n : ℝ) ^ (A / 3))) < 1 / 2 := hnTail n hnTail0
    have hExpDiv :
        Real.exp (-((n : ℝ) ^ (A / 3))) < (1 / 2 : ℝ) / ((n : ℝ) ^ K₀) := by
      rw [lt_div_iff₀ (Real.rpow_pos_of_pos hnpos K₀)]
      calc
        Real.exp (-((n : ℝ) ^ (A / 3))) * (n : ℝ) ^ K₀ =
            ((n : ℝ) ^ (A / 3)) ^ (K₀ / (A / 3)) *
              Real.exp (-((n : ℝ) ^ (A / 3))) := by rw [hpowEq]; ring
        _ < 1 / 2 := hTailProduct
    have hExpPower :
        Real.exp (-((n : ℝ) ^ (A / 3))) <
          (1 / 2 : ℝ) * (n : ℝ) ^ (-K₀) := by
      simpa [div_eq_mul_inv, Real.rpow_neg hnpos.le] using hExpDiv
    have hPowerCompare : (n : ℝ) ^ (-K₀) ≤
        (n : ℝ) ^ (-((1 - θ) * K₀)) :=
      Real.rpow_le_rpow_of_exponent_le hnR (by linarith [hαle])
    have hTailFinal : Real.exp (-((n : ℝ) ^ (A / 3))) ≤
        (1 / 2 : ℝ) * (n : ℝ) ^ (-((1 - θ) * K₀)) :=
      le_trans hExpPower.le
        (mul_le_mul_of_nonneg_left hPowerCompare (by norm_num))
    calc
      law.pr unmatched ≤ Real.exp (-((n : ℝ) ^ (A / 3))) +
          (3 / 2 : ℝ) * (n : ℝ) ^ (-((1 - θ) * K₀)) := htotal
      _ ≤ (1 / 2 : ℝ) * (n : ℝ) ^ (-((1 - θ) * K₀)) +
          (3 / 2 : ℝ) * (n : ℝ) ^ (-((1 - θ) * K₀)) :=
            add_le_add hTailFinal le_rfl
      _ = 2 * (n : ℝ) ^ (-((1 - θ) * K₀)) := by ring

/-- What the finite-mesh clock construction delivers before conditioning (TeX 03:1113–1128), stated
abstractly: a finite probability space with a real-output map; finitely many bad events, each with a nonempty
dependency set of at most `L` vertices (the active endpoints of a bad exploration leaf), total probability at
most `κ` at every vertex (03:898–902), and the forcing property against bad events with disjoint dependency
sets (03:885–896); avoiding all bad events gives distinct labels and avoids every predicate (03:1117–1119);
and every joint target event on at most `n^B` rows is covered, on the avoidance event, by finitely many
forcing events with dependency sets of at most `n^B L` vertices whose probabilities sum to at most `(1 + η)`
times the target product (03:1121–1128). -/
structure RawSampler {n g : ℕ} {R K : Type} [Fintype R] [DecidableEq R] [Fintype K]
    {Ω : R → Type} [∀ a, Fintype (Ω a)] [∀ a, DecidableEq (Ω a)]
    (I : SamplingInstance n g R K Ω) (q : ∀ a, FinProb (Ω a)) (B L κ η : ℝ) where
  Space : Type
  [spaceFintype : Fintype Space]
  [spaceDecEq : DecidableEq Space]
  law : FinProb Space
  out : Space → ∀ a, Ω a
  Vertex : Type
  [vertexDecEq : DecidableEq Vertex]
  Bad : Type
  [badFintype : Fintype Bad]
  [badDecEq : DecidableEq Bad]
  bad : Bad → Space → Prop
  act : Bad → Finset Vertex
  act_nonempty : ∀ i, (act i).Nonempty
  act_card : ∀ i, ((act i).card : ℝ) ≤ L
  incidence : ∀ v, ∑ i ∈ Finset.univ.filter (fun i => v ∈ act i), law.pr (bad i) ≤ κ
  forcing : ∀ i (S : Finset Bad), (∀ j ∈ S, Disjoint (act i) (act j)) →
    law.pr (fun x => bad i x ∧ ∀ j ∈ S, ¬ bad j x) ≤
      law.pr (bad i) * law.pr (fun x => ∀ j ∈ S, ¬ bad j x)
  good : ∀ x, (∀ i, ¬ bad i x) →
    Function.Injective (fun a => I.lab a (out x a)) ∧ ∀ k, ¬ I.failure k (out x)
  target : ∀ (S : Finset R) (o : ∀ a, Ω a), (S.card : ℝ) ≤ (n : ℝ) ^ B →
    ∃ (m : ℕ) (rect : Fin m → Space → Prop) (actR : Fin m → Finset Vertex),
      (∀ r, ((actR r).card : ℝ) ≤ (n : ℝ) ^ B * L) ∧
      (∀ r (S' : Finset Bad), (∀ j ∈ S', Disjoint (actR r) (act j)) →
        law.pr (fun x => rect r x ∧ ∀ j ∈ S', ¬ bad j x) ≤
          law.pr (rect r) * law.pr (fun x => ∀ j ∈ S', ¬ bad j x)) ∧
      (∀ x, (∀ i, ¬ bad i x) → (∀ a ∈ S, out x a = o a) → ∃ r, rect r x) ∧
      ∑ r, law.pr (rect r) ≤ (1 + η) * ∏ a ∈ S, (q a).w (o a)

attribute [instance] RawSampler.spaceFintype RawSampler.spaceDecEq RawSampler.vertexDecEq
  RawSampler.badFintype RawSampler.badDecEq

/-- L3.10h, avoidance (TeX 03:1113–1128): Lemma 3.5 with charges `2 Pr(E)` turns a raw sampler into a law on
real outputs supported on injective, predicate-avoiding assignments; each forcing event costs at most `∏ (1 -
x_j)⁻¹ ≤ exp (4 n^B L κ)` against its neighbours. -/
theorem leaf_avoidance_transfer {n g : ℕ} {R K : Type} [Fintype R] [DecidableEq R] [Fintype K]
    {Ω : R → Type} [∀ a, Fintype (Ω a)] [∀ a, DecidableEq (Ω a)]
    (I : SamplingInstance n g R K Ω) (q : ∀ a, FinProb (Ω a)) (B L κ η : ℝ)
    (hL : 0 ≤ L) (hκ : 0 ≤ κ) (hLκ : 4 * L * κ ≤ 1) (X : RawSampler I q B L κ η) :
    ∃ J : FinProb (∀ a, Ω a),
      (∀ ω, J.w ω ≠ 0 → Function.Injective (fun a => I.lab a (ω a)) ∧ ∀ k, ¬ I.failure k ω) ∧
      (∀ (S : Finset R) (o : ∀ a, Ω a), (S.card : ℝ) ≤ (n : ℝ) ^ B →
        J.pr (fun ω => ∀ a ∈ S, ω a = o a) ≤
          Real.exp (4 * ((n : ℝ) ^ B * L) * κ) * ((1 + η) * ∏ a ∈ S, (q a).w (o a))) := by
  sorry

/-- L3.10b–h without Step 1 and without the avoidance step (TeX 03:844–1111, 03:1121–1128): from a Step 1
certificate, the completed finite-mesh clock matching (Steps 2–7) with its truncated exploration leaves gives
a raw sampler for the trimmed laws, with `L = ⌈n^{.1K₀}⌉`, `κ = n^{-.6K₀}` in the paper (03:872, 03:898–902),
so that `n^B L κ → 0`. The constants come first, with `4B + 4 ≤ P` so that Step 1 applies. This node still
carries the exploration leaves and the incidence bound of Steps 2–8 and must be split further before proof. -/
theorem clock_raw_sampler (B C_g : ℝ) (hB : 1 ≤ B) :
    ∃ A P : ℝ, ∃ n₀ : ℕ, ∃ L κ : ℕ → ℝ, 4 * B + 4 ≤ P ∧
      Tendsto (fun n : ℕ => (n : ℝ) ^ B * L n * κ n) atTop (nhds 0) ∧
      ∀ n ≥ n₀, 0 ≤ L n ∧ 0 ≤ κ n ∧ 4 * L n * κ n ≤ 1 ∧
      ∀ g : ℕ, Real.log g ≤ C_g * n →
      ∀ {R K : Type} [Fintype R] [DecidableEq R] [Fintype K] {Ω : R → Type} [∀ a, Fintype (Ω a)]
        [∀ a, DecidableEq (Ω a)] (I : SamplingInstance n g R K Ω), I.Admissible B A P →
        ∀ C : TrimCertificate I B A P,
        Nonempty (RawSampler I C.trimmed B (L n) (κ n) (n : ℝ)⁻¹) := by
  sorry

/-- L3.10h without Step 1 (03:844–1128), assembled: the raw sampler of the clock construction, conditioned
through `leaf_avoidance_transfer`, gives a law on real outputs that is injective, avoids every predicate, and
has the joint product bound relative to the trimmed laws. -/
theorem step8_trimmed_core (B C_g : ℝ) (hB : 1 ≤ B) :
    ∃ A P : ℝ, ∃ n₀ : ℕ, ∃ ε : ℕ → ℝ, 4 * B + 4 ≤ P ∧ Tendsto ε atTop (nhds 0) ∧
    ∀ n ≥ n₀, ∀ g : ℕ, Real.log g ≤ C_g * n →
    ∀ {R K : Type} [Fintype R] [DecidableEq R] [Fintype K] {Ω : R → Type} [∀ a, Fintype (Ω a)]
      [∀ a, DecidableEq (Ω a)] (I : SamplingInstance n g R K Ω), I.Admissible B A P →
      ∀ C : TrimCertificate I B A P,
      ∃ J : FinProb (∀ a, Ω a),
        (∀ ω, J.w ω ≠ 0 → Function.Injective (fun a => I.lab a (ω a)) ∧ ∀ k, ¬ I.failure k ω) ∧
        (∀ (S : Finset R) (o : ∀ a, Ω a), ((S.card : ℝ) ≤ (n : ℝ) ^ B) →
          J.pr (fun ω => ∀ a ∈ S, ω a = o a) ≤
            (1 + ε n) * ∏ a ∈ S, (C.trimmed a).w (o a)) := by
  obtain ⟨A, P, n₀, L, κ, hP, hsmall, hraw⟩ := clock_raw_sampler B C_g hB
  refine ⟨A, P, n₀,
    fun n => Real.exp (4 * ((n : ℝ) ^ B * L n) * κ n) * (1 + (n : ℝ)⁻¹) - 1, hP, ?_, ?_⟩
  · have hx : Tendsto (fun n : ℕ => 4 * ((n : ℝ) ^ B * L n) * κ n) atTop (nhds 0) := by
      have h := hsmall.const_mul 4
      simpa [mul_assoc] using h
    have hexp := (Real.continuous_exp.tendsto 0).comp hx
    have hlim := (hexp.mul ((tendsto_const_nhds (x := (1 : ℝ))).add
      (tendsto_inv_atTop_nhds_zero_nat (𝕜 := ℝ)))).sub_const 1
    convert hlim using 2 <;> simp
  · intro n hn g hg R K _ _ _ Ω _ _ I hI C
    obtain ⟨hL0, hκ0, hLκ, hrest⟩ := hraw n hn
    obtain ⟨X⟩ := hrest g hg I hI C
    obtain ⟨J, hJs, hJt⟩ :=
      leaf_avoidance_transfer I C.trimmed B (L n) (κ n) (n : ℝ)⁻¹ hL0 hκ0 hLκ X
    refine ⟨J, hJs, fun S o hS => ?_⟩
    calc J.pr (fun ω => ∀ a ∈ S, ω a = o a)
        ≤ Real.exp (4 * ((n : ℝ) ^ B * L n) * κ n) *
            ((1 + (n : ℝ)⁻¹) * ∏ a ∈ S, (C.trimmed a).w (o a)) := hJt S o hS
      _ = (1 + (Real.exp (4 * ((n : ℝ) ^ B * L n) * κ n) * (1 + (n : ℝ)⁻¹) - 1)) *
            ∏ a ∈ S, (C.trimmed a).w (o a) := by ring

/-- L3.10h (03:1084–1131), assembled: trim and complete (Step 1), run the trimmed core, and pay the
renormalization cost of Step 1 on the queried rows (03:1128–1131). This is the sub-node consumed by the
exported theorem. -/
theorem step8_bad_leaf_avoidance (B C_g : ℝ) (hB : 1 ≤ B) :
    ∃ A P : ℝ, ∃ n₀ : ℕ, ∃ ε : ℕ → ℝ,
    Tendsto ε atTop (nhds 0) ∧ ∀ n ≥ n₀, ∀ g : ℕ, Real.log g ≤ C_g * n →
    ∀ {R K : Type} [Fintype R] [DecidableEq R] [Fintype K] {Ω : R → Type} [∀ a, Fintype (Ω a)]
      [∀ a, DecidableEq (Ω a)] (lab : ∀ a, Ω a → Fin g) (p : ∀ a, FinProb (Ω a))
      (F : K → (∀ a, Ω a) → Prop) (sc : K → Finset R),
      (∀ y, ∑ a, labMarg (p a) (lab a) y ≤ 1e-8) →
      (∀ a y, labMarg (p a) (lab a) y ≤ (n : ℝ) ^ (-A)) →
      (∀ k, FinProb.DependsOn (F k) (sc k)) →
      (∀ k, ((sc k).card : ℝ) ≤ (n : ℝ) ^ B) →
      (∀ a, ((Finset.univ.filter (fun k => a ∈ sc k)).card : ℝ) ≤ (n : ℝ) ^ B) →
      (∀ k, (FinProb.pi p).pr (F k) ≤ (n : ℝ) ^ (-P)) →
      ∃ J : FinProb (∀ a, Ω a),
        (∀ ω, J.w ω ≠ 0 → Function.Injective (fun a => lab a (ω a)) ∧ ∀ k, ¬ F k ω) ∧
        (∀ (S : Finset R) (o : ∀ a, Ω a), ((S.card : ℝ) ≤ (n : ℝ) ^ B) →
          J.pr (fun ω => ∀ a ∈ S, ω a = o a) ≤
            (1 + ε n) * ∏ a ∈ S, (p a).w (o a)) := by
  obtain ⟨A, P, n₀, ε, hP, hε, hcore⟩ := step8_trimmed_core B C_g hB
  refine ⟨A, P, max n₀ 2,
    fun n => (1 + |ε n|) * (1 + 2 * (n : ℝ) ^ (2 * B - P / 2)) - 1, ?_, ?_⟩
  · have hexp : 0 < P / 2 - 2 * B := by linarith
    have hpow : Tendsto (fun n : ℕ => (n : ℝ) ^ (2 * B - P / 2)) atTop (nhds 0) := by
      have h := (tendsto_rpow_neg_atTop hexp).comp tendsto_natCast_atTop_atTop
      simpa [Function.comp_def, neg_sub] using h
    have habs : Tendsto (fun n => |ε n|) atTop (nhds 0) := by
      simpa using hε.abs
    have hlim := ((tendsto_const_nhds (x := (1 : ℝ))).add habs).mul
      ((tendsto_const_nhds (x := (1 : ℝ))).add (hpow.const_mul 2))
    convert hlim.sub_const 1 using 2
    norm_num
  · intro n hn g hg R K _ _ _ Ω _ _ lab p F sc h1 h2 h3 h4 h5 h6
    have hn2 : 2 ≤ n := le_trans (le_max_right _ _) hn
    have hn0 : n₀ ≤ n := le_trans (le_max_left _ _) hn
    let I : SamplingInstance n g R K Ω := ⟨lab, p, F, sc⟩
    have hI : I.Admissible B A P := by
      unfold SamplingInstance.Admissible
      exact ⟨h1, h2, h3, h4, h5, h6⟩
    obtain ⟨C⟩ := step1_trim_and_complete I B A P hn2 (by linarith) hP hI
    obtain ⟨J, hJsupp, hJ⟩ := hcore n hn0 g hg I hI C
    refine ⟨J, hJsupp, fun S o hS => ?_⟩
    have hcoreS := hJ S o hS
    have huntrim := untrim_product_bound I B A P hn2 (by linarith) hP C S o hS
    have hprod : 0 ≤ ∏ a ∈ S, (C.trimmed a).w (o a) :=
      Finset.prod_nonneg fun a _ => (C.trimmed a).nonneg (o a)
    have hfac : 0 ≤ 1 + |ε n| := by positivity
    calc J.pr (fun ω => ∀ a ∈ S, ω a = o a)
        ≤ (1 + ε n) * ∏ a ∈ S, (C.trimmed a).w (o a) := hcoreS
      _ ≤ (1 + |ε n|) * ∏ a ∈ S, (C.trimmed a).w (o a) :=
          mul_le_mul_of_nonneg_right (by linarith [le_abs_self (ε n)]) hprod
      _ ≤ (1 + |ε n|) * ((1 + 2 * (n : ℝ) ^ (2 * B - P / 2)) * ∏ a ∈ S, (p a).w (o a)) :=
          mul_le_mul_of_nonneg_left huntrim hfac
      _ = (1 + ((1 + |ε n|) * (1 + 2 * (n : ℝ) ^ (2 * B - P / 2)) - 1)) *
            ∏ a ∈ S, (p a).w (o a) := by ring

end HypercubeRamsey.Clock
