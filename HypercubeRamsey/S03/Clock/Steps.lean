import HypercubeRamsey.S03.Clock.Inputs
import HypercubeRamsey.S03.ConditionalAvoidance
import HypercubeRamsey.Framework.FinProbLemmas

/-!
# Lemma 3.10, Steps 2–8

Each proof node refers to the finite mesh objects in `Model`, `Matching`, `Exploration`, `Leaves`, and
`Inputs`. Steps 4–7 are separated into path, branching-tail, background-tracking, and target-product
obligations. Step 8 is assembled in `Sampler.lean`: `step8_bad_leaf_avoidance` (used by `clock_sampling`)
combines Step 1, the renormalization bound and `step8_trimmed_core`; the core combines `clock_raw_sampler` (the
clock construction, split over `Truncated`, `Paths`, `Branching` and `Sampler`) with `leaf_avoidance_transfer`
(Lemma 3.5, below).
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
  classical
  let p : X.Bad → ℝ := fun i => X.law.pr (X.bad i)
  let x : X.Bad → ℝ := fun i => 2 * p i
  let adj : X.Bad → X.Bad → Prop := fun i j => i ≠ j ∧ ¬ Disjoint (X.act i) (X.act j)
  haveI : DecidableRel adj := Classical.decRel _
  let E : X.Bad → Finset X.Space := fun i => Finset.univ.filter (X.bad i)
  let Q : X.Space → Prop := fun z => ∀ i, ¬ X.bad i z
  have hp0 (i : X.Bad) : 0 ≤ p i := by
    dsimp [p]
    unfold FinProb.pr
    exact Finset.sum_nonneg fun z _ => by
      split_ifs
      · exact X.law.nonneg z
      · exact le_rfl
  have hE0 (i : X.Bad) : 0 ≤ p i := hp0 i
  have hact_one (i : X.Bad) : (1 : ℝ) ≤ L := by
    have hc : 1 ≤ (X.act i).card := Finset.one_le_card.mpr (X.act_nonempty i)
    exact le_trans (by exact_mod_cast hc) (X.act_card i)
  have hκquarter (i : X.Bad) : κ ≤ 1 / 4 := by
    have hprod : 0 ≤ (L - 1) * κ := mul_nonneg (sub_nonneg.mpr (hact_one i)) hκ
    nlinarith [hLκ]
  have hpκ (i : X.Bad) : p i ≤ κ := by
    obtain ⟨v, hv⟩ := X.act_nonempty i
    have hmem : i ∈ Finset.univ.filter (fun j : X.Bad => v ∈ X.act j) := by
      simp [hv]
    have hsingle := Finset.single_le_sum
      (s := Finset.univ.filter (fun j : X.Bad => v ∈ X.act j))
      (f := fun j => p j) (fun j _ => hp0 j) hmem
    calc
      p i ≤ ∑ j ∈ Finset.univ.filter (fun j : X.Bad => v ∈ X.act j), p j := hsingle
      _ ≤ κ := X.incidence v
  have hx0 (i : X.Bad) : 0 ≤ x i := by simp [x, hp0]
  have hxhalf (i : X.Bad) : x i ≤ 1 / 2 := by
    dsimp [x]
    nlinarith [hpκ i, hκquarter i]
  have hx1 (i : X.Bad) : x i < 1 := lt_of_le_of_lt (hxhalf i) (by norm_num)
  have hincidence_sum (A : Finset X.Vertex) :
      (∑ j ∈ Finset.univ.filter (fun j : X.Bad => ¬ Disjoint A (X.act j)), p j) ≤
        (A.card : ℝ) * κ := by
    let N : Finset X.Bad := Finset.univ.filter (fun j => ¬ Disjoint A (X.act j))
    have hterm (j : X.Bad) (hj : j ∈ N) :
        p j ≤ ∑ v ∈ A, if v ∈ X.act j then p j else 0 := by
      have hshared : ∃ v, v ∈ A ∧ v ∈ X.act j := by
        by_contra h
        have hdis : Disjoint A (X.act j) := by
          apply Finset.disjoint_left.mpr
          intro v hvA hvj
          exact h ⟨v, hvA, hvj⟩
        exact (Finset.mem_filter.mp hj).2 hdis
      obtain ⟨v, hvA, hvj⟩ := hshared
      have hsingle := Finset.single_le_sum
        (s := A) (f := fun v => if v ∈ X.act j then p j else 0)
        (fun v _ => by split_ifs <;> [exact hp0 j; exact le_rfl]) hvA
      simpa [hvj] using hsingle
    calc
      (∑ j ∈ Finset.univ.filter (fun j : X.Bad => ¬ Disjoint A (X.act j)), p j) ≤
          ∑ j ∈ N, ∑ v ∈ A, if v ∈ X.act j then p j else 0 := by
        apply Finset.sum_le_sum
        intro j hj
        exact hterm j (by simpa [N] using hj)
      _ = ∑ v ∈ A, ∑ j ∈ N, if v ∈ X.act j then p j else 0 := by
        rw [Finset.sum_comm]
      _ ≤ ∑ v ∈ A, ∑ j ∈ Finset.univ.filter (fun j : X.Bad => v ∈ X.act j), p j := by
        apply Finset.sum_le_sum
        intro v hv
        calc
          (∑ j ∈ N, if v ∈ X.act j then p j else 0) =
              ∑ j ∈ N.filter (fun j => v ∈ X.act j), p j := by simp [Finset.sum_filter]
          _ ≤ ∑ j ∈ Finset.univ.filter (fun j : X.Bad => v ∈ X.act j), p j := by
            apply Finset.sum_le_sum_of_subset_of_nonneg
              (by
                intro j hj
                exact Finset.mem_filter.mpr
                  ⟨Finset.mem_univ j, (Finset.mem_filter.mp hj).2⟩)
              (by intro j hj _; exact hp0 j)
      _ ≤ ∑ v ∈ A, κ := by
        apply Finset.sum_le_sum
        intro v hv
        simpa [p] using X.incidence v
      _ = (A.card : ℝ) * κ := by simp
  have hprodLower : ∀ (S : Finset X.Bad),
      (∀ j ∈ S, 0 ≤ x j) → (∀ j ∈ S, x j ≤ 1) →
      1 - (∑ j ∈ S, x j) ≤ ∏ j ∈ S, (1 - x j) := by
    intro S
    induction S using Finset.induction_on with
    | empty => intro _ _; simp
    | @insert i S hi ih =>
      intro hnon hle
      have hnonS : ∀ j ∈ S, 0 ≤ x j := fun j hj => hnon j (Finset.mem_insert_of_mem hj)
      have hleS : ∀ j ∈ S, x j ≤ 1 := fun j hj => hle j (Finset.mem_insert_of_mem hj)
      have hsum0 : 0 ≤ ∑ j ∈ S, x j := Finset.sum_nonneg fun j hj => hnonS j hj
      have hi0 : 0 ≤ x i := hnon i (Finset.mem_insert_self i S)
      have hi1 : x i ≤ 1 := hle i (Finset.mem_insert_self i S)
      rw [Finset.sum_insert hi, Finset.prod_insert hi]
      calc
        1 - (x i + ∑ j ∈ S, x j) ≤ (1 - x i) * (1 - ∑ j ∈ S, x j) := by
          nlinarith [mul_nonneg hi0 hsum0]
        _ ≤ (1 - x i) * ∏ j ∈ S, (1 - x j) :=
          mul_le_mul_of_nonneg_left (ih hnonS hleS) (sub_nonneg.mpr hi1)
  have hneighbor_sum (A : Finset X.Vertex) :
      (∑ j ∈ Finset.univ.filter (fun j : X.Bad => ¬ Disjoint A (X.act j)), p j) ≤
        (A.card : ℝ) * κ := hincidence_sum A
  have hmassPr (A : Finset X.Space) :
      LocalLemma.mass X.law.w A = X.law.pr (fun z => z ∈ A) := by
    classical
    letI : DecidablePred (fun z : X.Space => z ∈ A) := fun z => Classical.propDecidable _
    unfold LocalLemma.mass
    unfold FinProb.pr
    exact (Finset.sum_ite_mem_eq A X.law.w).symm
  have hmassAvoid (S : Finset X.Bad) :
      LocalLemma.mass X.law.w (LocalLemma.avoid E S) =
        X.law.pr (fun z => ∀ j ∈ S, ¬ X.bad j z) := by
    rw [hmassPr]
    congr 1
    funext z
    simp [LocalLemma.avoid, E]
  have hmassBad (i : X.Bad) (S : Finset X.Bad) :
      LocalLemma.mass X.law.w (E i ∩ LocalLemma.avoid E S) =
        X.law.pr (fun z => X.bad i z ∧ ∀ j ∈ S, ¬ X.bad j z) := by
    rw [hmassPr]
    congr 1
    funext z
    simp [LocalLemma.avoid, E]
  have hCA := HypercubeRamsey.LocalLemma.conditional_avoidance
    X.law.w (fun z => X.law.nonneg z) X.law.sum_eq_one E adj
    (by
      intro i j hij
      refine ⟨Ne.symm hij.1, ?_⟩
      intro hji
      apply hij.2
      apply Finset.disjoint_left.mpr
      intro v hvi hvj
      exact (Finset.disjoint_left.mp hji) hvj hvi)
    (by
      intro i hi
      exact hi.1 rfl)
    p x
    (by
      intro i S hi hnon
      rw [hmassBad, hmassAvoid]
      apply X.forcing i S
      intro j hj
      have hneq : i ≠ j := by
        intro heq
        apply hi
        simpa [heq] using hj
      by_contra hdis
      exact hnon j hj ⟨hneq, hdis⟩)
    hx0 hx1
    (by
      intro i
      let N := Finset.univ.filter (adj i)
      have hsumP : (∑ j ∈ N, p j) ≤ (X.act i).card * κ := by
        calc
          (∑ j ∈ N, p j) ≤
              ∑ j ∈ Finset.univ.filter
                (fun j : X.Bad => ¬ Disjoint (X.act i) (X.act j)), p j := by
              apply Finset.sum_le_sum_of_subset_of_nonneg
                (by
                  intro j hj
                  have hadj : adj i j := (Finset.mem_filter.mp hj).2
                  exact Finset.mem_filter.mpr ⟨Finset.mem_univ j, hadj.2⟩)
                (by intro j hj _; exact hp0 j)
          _ ≤ (X.act i).card * κ := hincidence_sum (X.act i)
      have hsumX : (∑ j ∈ N, x j) ≤ 2 * ((X.act i).card : ℝ) * κ := by
        dsimp [x]
        calc
          (∑ j ∈ N, 2 * p j) = 2 * ∑ j ∈ N, p j := by rw [Finset.mul_sum]
          _ ≤ 2 * ((X.act i).card : ℝ) * κ := by nlinarith [hsumP]
      have hcardprod : ((X.act i).card : ℝ) * κ ≤ L * κ :=
        mul_le_mul_of_nonneg_right (X.act_card i) hκ
      have hsumXhalf : (∑ j ∈ N, x j) ≤ 1 / 2 := by
        calc
          (∑ j ∈ N, x j) ≤ 2 * ((X.act i).card : ℝ) * κ := hsumX
          _ ≤ 2 * (L * κ) := by nlinarith [hcardprod]
          _ ≤ 1 / 2 := by nlinarith [hLκ]
      have hprod := hprodLower N (fun j hj => hx0 j) (fun j hj => le_trans (hxhalf j) (by norm_num))
      have hprodhalf : 1 / 2 ≤ ∏ j ∈ N, (1 - x j) := by linarith
      have hpi : p i ≤ x i * ∏ j ∈ N, (1 - x j) := by
        have h := mul_nonneg (hp0 i) (sub_nonneg.mpr hprodhalf)
        dsimp [x, p] at *
        nlinarith [h]
      simpa [N, x, p] using hpi)
  have havoid : 0 < X.law.pr Q := by
    have h := hCA.1
    rw [hmassAvoid] at h
    have hEq : X.law.pr (fun z => ∀ j ∈ Finset.univ, ¬ X.bad j z) = X.law.pr Q := by
      congr 1
      funext z
      simp [Q]
    rw [hEq] at h
    exact h
  have havoidMass (S : Finset X.Bad) :
      0 < LocalLemma.mass X.law.w (LocalLemma.avoid E S) := by
    have hsub : LocalLemma.avoid E Finset.univ ⊆ LocalLemma.avoid E S := by
      intro z hz
      have hall : ∀ j ∈ Finset.univ, z ∉ E j := by simpa [LocalLemma.avoid] using hz
      simpa [LocalLemma.avoid] using (show ∀ j ∈ S, z ∉ E j from fun j hj => hall j (Finset.mem_univ j))
    have hmono := Finset.sum_le_sum_of_subset_of_nonneg hsub (by
      intro z hz _
      exact X.law.nonneg z)
    have hpos : 0 < LocalLemma.mass X.law.w (LocalLemma.avoid E Finset.univ) := hCA.1
    exact lt_of_lt_of_le hpos hmono
  have havoidEvent :
      LocalLemma.mass X.law.w (LocalLemma.avoid E Finset.univ) = X.law.pr Q := by
    rw [hmassAvoid]
    congr 1
    funext z
    simp [Q]
  have havoidPos : 0 < LocalLemma.mass X.law.w (LocalLemma.avoid E Finset.univ) := by
    rw [havoidEvent]
    exact havoid
  let Pcond : FinProb X.Space := X.law.cond Q havoid
  have hcondPr (A : X.Space → Prop) :
      Pcond.pr A = X.law.pr (fun z => A z ∧ Q z) / X.law.pr Q := by
    classical
    dsimp [Pcond, FinProb.pr, FinProb.cond]
    rw [Finset.sum_div]
    apply Finset.sum_congr rfl
    intro z hz
    by_cases hA : A z <;> by_cases hQ : Q z <;> simp [Pcond, hA, hQ]
  have hcondRect (A : X.Space → Prop) (S : Finset X.Bad) (T : Finset X.Bad)
      (hdis : Disjoint S T) (hpart : S ∪ T = Finset.univ) (hforcing :
        X.law.pr (fun z => A z ∧ ∀ j ∈ S, ¬ X.bad j z) ≤
          X.law.pr A * X.law.pr (fun z => ∀ j ∈ S, ¬ X.bad j z)) :
      Pcond.pr A ≤ (∏ j ∈ T, (1 - x j))⁻¹ * X.law.pr A := by
    have hCA3 := hCA.2.2.1 S T hdis (fun z => if A z then 1 else 0)
      (by intro z; split_ifs <;> norm_num)
    have hdenS : 0 < X.law.pr (fun z => ∀ j ∈ S, ¬ X.bad j z) := by
      have := havoidMass S
      rw [hmassAvoid] at this
      exact this
    have hdenQ : 0 < X.law.pr Q := havoid
    have hnumAll :
        (∑ z ∈ LocalLemma.avoid E (S ∪ T), X.law.w z * (if A z then 1 else 0)) =
          X.law.pr (fun z => A z ∧ Q z) := by
      rw [show ∑ z ∈ LocalLemma.avoid E (S ∪ T), X.law.w z * (if A z then 1 else 0) =
          LocalLemma.mass X.law.w ((LocalLemma.avoid E (S ∪ T)).filter A) by
        simp [LocalLemma.mass, Finset.sum_filter, mul_ite, mul_one, mul_zero]]
      rw [hmassPr]
      congr 1
      funext z
      rw [hpart]
      simp [LocalLemma.avoid, E, Q, and_comm]
    have hnumS :
        (∑ z ∈ LocalLemma.avoid E S, X.law.w z * (if A z then 1 else 0)) =
          X.law.pr (fun z => A z ∧ ∀ j ∈ S, ¬ X.bad j z) := by
      rw [show ∑ z ∈ LocalLemma.avoid E S, X.law.w z * (if A z then 1 else 0) =
          LocalLemma.mass X.law.w ((LocalLemma.avoid E S).filter A) by
        simp [LocalLemma.mass, Finset.sum_filter, mul_ite, mul_one, mul_zero]]
      rw [hmassPr]
      congr 1
      funext z
      simp [LocalLemma.avoid, E, and_comm, and_left_comm, and_assoc]
    have hforceRatio :
        X.law.pr (fun z => A z ∧ ∀ j ∈ S, ¬ X.bad j z) /
          X.law.pr (fun z => ∀ j ∈ S, ¬ X.bad j z) ≤ X.law.pr A := by
      exact (div_le_iff₀ hdenS).2 (by nlinarith [hforcing])
    have hQeq : X.law.pr Q = X.law.pr (fun z => ∀ j ∈ S ∪ T, ¬ X.bad j z) := by
      congr 1
      funext z
      rw [hpart]
      simp [Q, and_comm]
    rw [hcondPr, hQeq]
    calc
      X.law.pr (fun z => A z ∧ Q z) / X.law.pr (fun z => ∀ j ∈ S ∪ T, ¬ X.bad j z) ≤
          (∏ j ∈ T, (1 - x j))⁻¹ *
            (X.law.pr (fun z => A z ∧ ∀ j ∈ S, ¬ X.bad j z) /
              X.law.pr (fun z => ∀ j ∈ S, ¬ X.bad j z)) := by
        simpa only [hnumAll, hmassAvoid, hnumS] using hCA3
      _ ≤ (∏ j ∈ T, (1 - x j))⁻¹ * X.law.pr A := by
        apply mul_le_mul_of_nonneg_left hforceRatio
        exact le_of_lt (inv_pos.mpr (Finset.prod_pos fun j hj => sub_pos.mpr (hx1 j)))
  have hneighborFactor (A : Finset X.Vertex) (hA : (A.card : ℝ) ≤ (n : ℝ) ^ B * L) :
      (∏ j ∈ Finset.univ.filter (fun j : X.Bad => ¬ Disjoint A (X.act j)),
          (1 - x j))⁻¹ ≤ Real.exp (4 * ((n : ℝ) ^ B * L) * κ) := by
    let N := Finset.univ.filter (fun j : X.Bad => ¬ Disjoint A (X.act j))
    have hsumP : (∑ j ∈ N, p j) ≤ (n : ℝ) ^ B * L * κ := by
      calc
        (∑ j ∈ N, p j) ≤ (A.card : ℝ) * κ := by simpa [N] using hneighbor_sum A
        _ ≤ (n : ℝ) ^ B * L * κ := mul_le_mul_of_nonneg_right hA hκ
    have hper (j : X.Bad) : (1 - x j)⁻¹ ≤ Real.exp (2 * x j) := by
      have hx : 0 ≤ x j := hx0 j
      have hx' : x j ≤ 1 / 2 := hxhalf j
      have hden : 0 < 1 - x j := sub_pos.mpr (lt_of_le_of_lt hx' (by norm_num))
      have hquad : 1 ≤ (1 + 2 * x j) * (1 - x j) := by
        nlinarith [mul_nonneg hx (sub_nonneg.mpr (by nlinarith [hx']))]
      have hexp := Real.add_one_le_exp (2 * x j)
      have hnum : 1 + 2 * x j ≤ Real.exp (2 * x j) := by linarith
      have hmul := mul_le_mul_of_nonneg_right hnum hden.le
      rw [inv_le_iff_one_le_mul₀' hden]
      nlinarith [hquad, hmul]
    have hprod : (∏ j ∈ N, (1 - x j)⁻¹) ≤ ∏ j ∈ N, Real.exp (2 * x j) := by
      induction N using Finset.induction_on with
      | empty => simp
      | @insert j N hj ih =>
        rw [Finset.prod_insert hj, Finset.prod_insert hj]
        have hleft : 0 ≤ ∏ k ∈ N, (1 - x k)⁻¹ :=
          Finset.prod_nonneg fun k hk => inv_nonneg.mpr (sub_nonneg.mpr (le_of_lt (hx1 k)))
        calc
          (1 - x j)⁻¹ * ∏ k ∈ N, (1 - x k)⁻¹ ≤
              Real.exp (2 * x j) * ∏ k ∈ N, (1 - x k)⁻¹ :=
            mul_le_mul_of_nonneg_right (hper j) hleft
          _ ≤ Real.exp (2 * x j) * ∏ k ∈ N, Real.exp (2 * x k) :=
            mul_le_mul_of_nonneg_left ih (Real.exp_pos _).le
    have hsumX : (∑ j ∈ N, 2 * x j) ≤ 4 * ((n : ℝ) ^ B * L) * κ := by
      dsimp [x, p]
      calc
        (∑ j ∈ N, 2 * (2 * X.law.pr (X.bad j))) =
            4 * ∑ j ∈ N, X.law.pr (X.bad j) := by
          rw [Finset.mul_sum]
          apply Finset.sum_congr rfl
          intro j hj
          ring
        _ ≤ 4 * ((n : ℝ) ^ B * L * κ) := by nlinarith [hsumP]
        _ = 4 * ((n : ℝ) ^ B * L) * κ := by ring
    calc
      (∏ j ∈ N, (1 - x j))⁻¹ = ∏ j ∈ N, (1 - x j)⁻¹ := by
        rw [Finset.prod_inv_distrib]
      _ ≤ ∏ j ∈ N, Real.exp (2 * x j) := hprod
      _ = Real.exp (∑ j ∈ N, 2 * x j) := by rw [← Real.exp_sum]
      _ ≤ Real.exp (4 * ((n : ℝ) ^ B * L) * κ) := Real.exp_le_exp.mpr hsumX
  have mapPr (P : FinProb X.Space) (f : X.Space → (∀ a, Ω a))
      (A : (∀ a, Ω a) → Prop) :
      (FinProb.map P f).pr A = P.pr (fun z => A (f z)) := by
    classical
    have hmapPrExpect :
        (FinProb.map P f).pr A =
          (FinProb.map P f).expect (fun y => if A y then 1 else 0) := by
      unfold FinProb.pr FinProb.expect
      apply Finset.sum_congr rfl
      intro y hy
      by_cases hA : A y <;> simp [hA]
    have hprExpect :
        P.expect (fun z => if A (f z) then 1 else 0) = P.pr (fun z => A (f z)) := by
      unfold FinProb.pr FinProb.expect
      apply Finset.sum_congr rfl
      intro z hz
      by_cases hA : A (f z) <;> simp [hA]
    calc
      (FinProb.map P f).pr A =
          (FinProb.map P f).expect (fun y => if A y then 1 else 0) := hmapPrExpect
      _ = P.expect (fun z => if A (f z) then 1 else 0) :=
        FinProb.map_expect P f (fun y => if A y then 1 else 0)
      _ = P.pr (fun z => A (f z)) := hprExpect
  let J : FinProb (∀ a, Ω a) := FinProb.map Pcond X.out
  refine ⟨J, ?_, ?_⟩
  · intro ω hω
    by_contra hgood
    have hzero : J.w ω = 0 := by
      dsimp [J, FinProb.map]
      apply Finset.sum_eq_zero
      intro z hz
      by_cases hout : X.out z = ω
      · have hnotQ : ¬ Q z := by
          intro hq
          have hgoodz := X.good z (by simpa [Q] using hq)
          exact hgood (by simpa [hout] using hgoodz)
        simp [Pcond, FinProb.cond, hnotQ, hout]
      · simp [hout]
    exact hω hzero
  · intro S o hS
    let target : X.Space → Prop := fun z => ∀ a ∈ S, X.out z a = o a
    obtain ⟨m, rect, actR, hcard, hforce, hcover, hrectsum⟩ := X.target S o hS
    have hunion (f : Fin m → X.Space → Prop) :
        Pcond.pr (fun z => ∃ r, f r z) ≤ ∑ r, Pcond.pr (f r) := by
      classical
      letI : DecidablePred (fun z => ∃ r, f r z) := fun z => Classical.propDecidable _
      unfold FinProb.pr
      calc
        (∑ z, if ∃ r, f r z then Pcond.w z else 0) ≤
            ∑ z, ∑ r, if f r z then Pcond.w z else 0 := by
          apply Finset.sum_le_sum
          intro z hz
          by_cases he : ∃ r, f r z
          · obtain ⟨r, hr⟩ := he
            have hsingle := Finset.single_le_sum
              (s := Finset.univ) (f := fun r : Fin m => if f r z then Pcond.w z else 0)
              (fun r _ => by split_ifs <;> [exact Pcond.nonneg z; exact le_rfl])
              (Finset.mem_univ r)
            have hsingle' : Pcond.w z ≤ ∑ r, if f r z then Pcond.w z else 0 := by
              simpa [hr] using hsingle
            rw [if_pos ⟨r, hr⟩]
            exact hsingle'
          · rw [if_neg he]
            apply Finset.sum_nonneg
            intro r hr
            by_cases hfr : f r z <;> simp [hfr, Pcond.nonneg z]
        _ = ∑ r, Pcond.pr (f r) := by
          rw [Finset.sum_comm]
          simp [FinProb.pr]
    have hcondSupport (z : X.Space) (hz : Pcond.w z ≠ 0) : Q z := by
      by_contra hq
      have hz0 : Pcond.w z = 0 := by
        simp [Pcond, FinProb.cond, hq]
      exact hz hz0
    have htargetCover : Pcond.pr target ≤ ∑ r, Pcond.pr (rect r) := by
      apply le_trans ?_ (hunion rect)
      letI : DecidablePred target := fun z => Classical.propDecidable _
      letI : DecidablePred (fun z => ∃ r, rect r z) := fun z => Classical.propDecidable _
      unfold FinProb.pr
      apply Finset.sum_le_sum
      intro z hz
      by_cases ht : target z
      · by_cases hw : Pcond.w z = 0
        · rw [if_pos ht, hw]
          by_cases he : ∃ r, rect r z <;> simp [he, hw]
        · obtain ⟨r, hr⟩ := hcover z (hcondSupport z hw) ht
          rw [if_pos ht, if_pos ⟨r, hr⟩]
      · rw [if_neg ht]
        by_cases he : ∃ r, rect r z
        · rw [if_pos he]
          exact Pcond.nonneg z
        · rw [if_neg he]
    have hrectBound (r : Fin m) :
        Pcond.pr (rect r) ≤ Real.exp (4 * ((n : ℝ) ^ B * L) * κ) * X.law.pr (rect r) := by
      let S0 := Finset.univ.filter (fun j : X.Bad => Disjoint (actR r) (X.act j))
      let T0 := Finset.univ.filter (fun j : X.Bad => ¬ Disjoint (actR r) (X.act j))
      have hdis : Disjoint S0 T0 := by
        apply Finset.disjoint_left.mpr
        intro j hjS hjT
        exact (Finset.mem_filter.mp hjT).2 ((Finset.mem_filter.mp hjS).2)
      have hpart : S0 ∪ T0 = Finset.univ := by
        ext j
        by_cases hd : Disjoint (actR r) (X.act j)
        · simp [S0, T0, hd]
        · simp [S0, T0, hd]
      have hlocal := hcondRect (rect r) S0 T0 hdis hpart (by
        exact hforce r S0 (by intro j hj; exact (Finset.mem_filter.mp hj).2))
      have hfactor := hneighborFactor (actR r) (hcard r)
      have hpr0 : 0 ≤ X.law.pr (rect r) := by
        unfold FinProb.pr
        apply Finset.sum_nonneg
        intro z hz
        by_cases hrz : rect r z <;> simp [hrz, X.law.nonneg z]
      calc
        Pcond.pr (rect r) ≤ (∏ j ∈ T0, (1 - x j))⁻¹ * X.law.pr (rect r) := by
          simpa [S0, T0] using hlocal
        _ ≤ Real.exp (4 * ((n : ℝ) ^ B * L) * κ) * X.law.pr (rect r) :=
          mul_le_mul_of_nonneg_right hfactor hpr0
    have hsumBound : (∑ r, Pcond.pr (rect r)) ≤
        Real.exp (4 * ((n : ℝ) ^ B * L) * κ) *
          ((1 + η) * ∏ a ∈ S, (q a).w (o a)) := by
      calc
        (∑ r, Pcond.pr (rect r)) ≤
            ∑ r, Real.exp (4 * ((n : ℝ) ^ B * L) * κ) * X.law.pr (rect r) :=
              Finset.sum_le_sum fun r _ => hrectBound r
        _ = Real.exp (4 * ((n : ℝ) ^ B * L) * κ) * ∑ r, X.law.pr (rect r) := by
              rw [Finset.mul_sum]
        _ ≤ Real.exp (4 * ((n : ℝ) ^ B * L) * κ) *
              ((1 + η) * ∏ a ∈ S, (q a).w (o a)) :=
              mul_le_mul_of_nonneg_left hrectsum (Real.exp_pos _).le
    calc
      J.pr (fun ω => ∀ a ∈ S, ω a = o a) = Pcond.pr target := by
        rw [mapPr]
      _ ≤ ∑ r, Pcond.pr (rect r) := htargetCover
      _ ≤ Real.exp (4 * ((n : ℝ) ^ B * L) * κ) *
            ((1 + η) * ∏ a ∈ S, (q a).w (o a)) := hsumBound

end HypercubeRamsey.Clock
