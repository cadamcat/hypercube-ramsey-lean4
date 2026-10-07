import HypercubeRamsey.S03.Clock.Inputs

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
  sorry

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
  sorry

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
