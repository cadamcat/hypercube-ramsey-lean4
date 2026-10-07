import HypercubeRamsey.S03.Clock.Inputs

/-!
# Lemma 3.10, Steps 2–8

Each proof node refers to the finite mesh objects in `Model`, `Matching`, `Exploration`, `Leaves`, and
`Inputs`. Steps 4–7 are separated into path, branching-tail, background-tracking, and target-product
obligations. Step 8 is the final bad-leaf/avoidance assembly used by `clock_sampling`.
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
  sorry

/-- L3.10e (03:946–989): the exponential-moment estimate for a two-type branching forest gives a giant-tail
bound at the active-endpoint cutoff. -/
theorem step5_giant_tail {Ω : Type*} [Fintype Ω]
    (P : FinProb Ω) (size : Ω → ℕ) (δ roots L η : ℝ)
    (hδ : 0 < δ)
    (hmoment : P.expect (fun ω => Real.exp (δ * (size ω : ℝ))) ≤ Real.exp (δ * roots + η)) :
    P.pr (fun ω => L ≤ (size ω : ℝ)) ≤ Real.exp (-δ * (L - roots) + η) := by
  sorry

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

/-- Deterministic error propagation for the finite-mesh background recursion. -/
theorem background_trajectory_stability {T : ℕ} {Ω : Type*} [Fintype Ω]
    (P : FinProb Ω) (X : BackgroundProcess T Ω) (δ θ : ℝ)
    (η : ℝ) (hη : 0 ≤ η) (hδ0 : 0 ≤ δ) (hδ1 : δ ≤ 1)
    (hθ0 : 0 ≤ θ) (hθ1 : θ ≤ 1)
    (hrow0 : ∀ ω, X.rowMass 0 ω = 1)
    (hlabel0 : ∀ ω, X.labelMass 0 ω = θ)
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

/-- The greedy matching after all arrivals strictly before a mesh horizon. -/
noncomputable def matchingThrough {T : ℕ} {R : Type*} [Fintype R] [DecidableEq R]
    {g : ℕ} {Ω : R → Type*} [∀ a, Fintype (Ω a)] [∀ a, DecidableEq (Ω a)]
    (ξ : ClockField T R g Ω) (horizon : Fin (T + 1)) : GreedyState R g Ω := by
  classical
  exact runGreedy ξ ((clockEventList ξ).filter (fun e => e.2.2.1.val < horizon.val))

/-- Available label rate at a row after the prefix matching through `horizon`. -/
noncomputable def availableRowRate {T : ℕ} {R : Type*} [Fintype R] [DecidableEq R]
    {g : ℕ} {Ω : R → Type*} [∀ a, Fintype (Ω a)] [∀ a, DecidableEq (Ω a)]
    (rates : R → Fin g → ℝ) (ξ : ClockField T R g Ω) (a : R) (horizon : Fin (T + 1)) : ℝ := by
  classical
  let M := matchingThrough ξ horizon
  exact ∑ y, if labelUsed M y then 0 else rates a y

/-- Available row rate at a label after the prefix matching through `horizon`. -/
noncomputable def availableLabelRate {T : ℕ} {R : Type*} [Fintype R] [DecidableEq R]
    {g : ℕ} {Ω : R → Type*} [∀ a, Fintype (Ω a)] [∀ a, DecidableEq (Ω a)]
    (rates : R → Fin g → ℝ) (ξ : ClockField T R g Ω) (y : Fin g)
    (horizon : Fin (T + 1)) : ℝ := by
  classical
  let M := matchingThrough ξ horizon
  exact if labelUsed M y then 0
  else ∑ a, if M.assignment a = none then rates a y else 0

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

/-- L3.10f (03:991–1040): under independent first-arrival clocks with row rate one, column rate `θ`, and
small atoms, all free masses track the discrete background recursion with exponentially small failure. -/
theorem step6_background_tracking {n : ℕ} {R : Type*} [Fintype R] [DecidableEq R]
    {g : ℕ} {Ω : R → Type*} [∀ a, Fintype (Ω a)] [∀ a, DecidableEq (Ω a)]
    (B A C_g K₀ θ : ℝ) (hB : 1 ≤ B) (hK₀ : 0 < K₀)
    (hA : 10 * (B + K₀) < A) (n₀ : ℕ) (hn : n₀ ≤ n) (hn2 : 2 ≤ n)
    (mesh : FiniteMeshPlan n K₀) (hδ : 0 ≤ mesh.δ) (hδ1 : mesh.δ ≤ 1)
    (p : ∀ a, FinProb (Ω a)) (lab : ∀ a, Ω a → Fin g)
    (hlog : Real.log g ≤ C_g * n)
    (hrow : ∀ a, ∑ y, labMarg (p a) (lab a) y = 1)
    (hcol : ∀ y, ∑ a, labMarg (p a) (lab a) y = θ)
    (hθ : θ ≤ 1e-6)
    (hatom : ∀ a y, labMarg (p a) (lab a) y ≤ (n : ℝ) ^ (-A)) :
    (clockFieldLaw (samplingEdgeClockLaw mesh.δ hδ hδ1 p lab)).pr
      (fun ξ => ∀ t : Fin (mesh.ticks + 1),
        (∀ a, |availableRowRate (fun a y => labMarg (p a) (lab a) y) ξ a t -
          (backgroundTrajectory mesh.δ θ t.val).1| ≤ (n : ℝ) ^ (-3 * B)) ∧
        (∀ y, |availableLabelRate (fun a y => labMarg (p a) (lab a) y) ξ y t -
          θ * (backgroundTrajectory mesh.δ θ t.val).2| ≤ (n : ℝ) ^ (-3 * B))) ≥
      1 - Real.exp (-(n : ℝ) ^ (A / 3)) := by
  sorry

/-- A target assignment is realized when the greedy matching gives every queried row its prescribed output. -/
def matchesTargets {T : ℕ} {R : Type*} {g : ℕ} {Ω : R → Type*}
    [Fintype R] [DecidableEq R] [∀ a, Fintype (Ω a)] [∀ a, DecidableEq (Ω a)]
    (ξ : ClockField T R g Ω) (S : Finset R) (o : ∀ a, Ω a) : Prop :=
  ∀ a ∈ S, ∃ y, (greedyMatching ξ).assignment a = some (y, o a)

/-- L3.10g (03:1042–1082): prescribed distinct-label targets retain their product upper bound under the raw
finite-mesh matching law. -/
theorem step7_target_product_bound {T n : ℕ} {R : Type*} [Fintype R] [DecidableEq R]
    {g : ℕ} {Ω : R → Type*} [∀ a, Fintype (Ω a)] [∀ a, DecidableEq (Ω a)]
    (n₀ : ℕ) (B A C_g K₀ θ : ℝ) (hB : 1 ≤ B) (hK₀ : 0 < K₀)
    (hA : 10 * (B + K₀) < A) (hn : n₀ ≤ n) (hn2 : 2 ≤ n)
    (hlog : Real.log g ≤ C_g * n)
    (mesh : FiniteMeshPlan n K₀) (hT : T = mesh.ticks)
    (hδ : 0 ≤ mesh.δ) (hδ1 : mesh.δ ≤ 1)
    (p : ∀ a, FinProb (Ω a)) (lab : ∀ a, Ω a → Fin g)
    (edgeLaw : ∀ e : RowLabel R g, FinProb (MeshClockValue T (Ω e.1)))
    (hedge : ∀ a y, edgeLaw (a, y) =
      outputEdgeClockLaw mesh.δ hδ (p a) (lab a) y
        (by
          have hm := labMarg_le_one (p a) (lab a) y
          have hmul : mesh.δ * labMarg (p a) (lab a) y ≤ mesh.δ := by
            simpa only [mul_one] using mul_le_mul_of_nonneg_left hm hδ
          exact sub_nonneg.mpr (le_trans hmul hδ1)))
    (hrow : ∀ a, ∑ y, labMarg (p a) (lab a) y = 1)
    (hcol : ∀ y, ∑ a, labMarg (p a) (lab a) y = θ)
    (hθ : θ ≤ 1e-6) (lambdaMax : ℝ)
    (hLambda : ∀ a y, labMarg (p a) (lab a) y ≤ lambdaMax)
    (hLambdaSmall : lambdaMax ≤ (n : ℝ) ^ (-A))
    (S : Finset R) (o : ∀ a, Ω a) (η : ℝ)
    (hη : (n : ℝ)⁻¹ ≤ η) (hη1 : η ≤ 1)
    (hdistinct : Set.InjOn (fun a => lab a (o a)) S)
    (hsize : (S.card : ℝ) ≤ (n : ℝ) ^ B) :
    (clockFieldLaw edgeLaw).pr (fun ξ => matchesTargets ξ S o) ≤
      (1 + η) * ∏ a ∈ S, (p a).w (o a) := by
  sorry

/-- L3.10h (03:1084–1131): combine the leaf incidence bound, conditional avoidance, and target partition to
produce a globally injective, predicate-avoiding law with the joint product comparison. This is the final
sub-node consumed by the exported theorem. -/
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
  sorry

end HypercubeRamsey.Clock
