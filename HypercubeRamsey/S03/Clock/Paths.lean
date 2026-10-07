import HypercubeRamsey.S03.Clock.Steps
import HypercubeRamsey.S03.Clock.Truncated

/-!
# Inserted paths bound the incidence sum (Lemma 3.10, Step 4 on the finite mesh)

Source: `sections/03-…tex`, lines 907–944. Reaching an endpoint `v` from a root `r` requires a path of arrivals
with strictly decreasing keys from `r` to `v` (`IsDecPath`); such a path uses distinct edges. On the finite mesh
the Poisson insertion identity becomes an exact product identity for independent edge clocks
(`insertion_identity`): the probability that the path's arrivals occur together with an event `G` is the product
of their first-arrival weights times the probability of `G` with those arrivals inserted. Summing the weights
over reversed walks from `v` gives the rate product `θ^{⌊j/2⌋}` (`step4_path_insertion_bound`) times the mesh
time sum over non-increasing tick sequences, at most `((T + j) δ)^j / j!` (`decPath_weight_sum`). Paths meeting
two rows of one predicate scope carry an extra factor `D λ / θ` (`two_row_weight_sum`); long paths are controlled
by the factorial tail (`walk_series_tail`).
-/

namespace HypercubeRamsey.Clock

open scoped BigOperators

/-- The clock value a candidate prescribes at an edge, if the candidate lies on that edge. -/
noncomputable def candidateValueAt {T : ℕ} {R : Type*} {g : ℕ} {Ω : R → Type*}
    (c : ClockCandidate T R g Ω) (e : RowLabel R g) : Option (MeshClockValue T (Ω e.1)) := by
  classical
  exact if h : c.1 = e.1 ∧ c.2.1 = e.2 then
    some (cast (congrArg (fun a => MeshClockValue T (Ω a)) h.1) (MeshClockValue.tick c.2.2.1 c.2.2.2))
  else none

/-- The insertion prescribing the arrivals of a candidate sequence (TeX 03:912–918). For a decreasing path the
edges are distinct, so each edge is prescribed by at most one candidate. -/
noncomputable def pathInsertion {T : ℕ} {R : Type*} {g : ℕ} {Ω : R → Type*} {j : ℕ}
    (π : Fin j → ClockCandidate T R g Ω) : ∀ e : RowLabel R g, Option (MeshClockValue T (Ω e.1)) :=
  fun e => (List.ofFn π).findSome? fun c => candidateValueAt c e

/-- A decreasing arrival path of length `j` from the endpoint `r` to the endpoint `v` (TeX 03:909–912): the
candidates `π 0, …, π (j-1)` cross consecutive endpoints `w 0 = r, …, w j = v`, their keys are below the root
horizon and strictly decreasing. This is the certificate by which the backward closure from `r` reaches `v`. -/
def IsDecPath {T : ℕ} {R : Type*} [Fintype R] [DecidableEq R] {g : ℕ} {Ω : R → Type*}
    (r v : Endpoint R g) {j : ℕ} (π : Fin j → ClockCandidate T R g Ω) : Prop :=
  ∃ w : Fin (j + 1) → Endpoint R g, w 0 = r ∧ w (Fin.last j) = v ∧
    (∀ i : Fin j,
      (w i.castSucc = Sum.inl (π i).1 ∧ w i.succ = Sum.inr (π i).2.1) ∨
      (w i.castSucc = Sum.inr (π i).2.1 ∧ w i.succ = Sum.inl (π i).1)) ∧
    (∀ i : Fin j, eventPriority (π i) < rootHorizon T R g) ∧
    (∀ i i' : Fin j, i < i' → eventPriority (π i') < eventPriority (π i))

/-- The decreasing arrival paths of length `j` from `r` to `v`. -/
noncomputable def decPaths {T : ℕ} {R : Type*} [Fintype R] [DecidableEq R] {g : ℕ}
    {Ω : R → Type*} [∀ a, Fintype (Ω a)] (r v : Endpoint R g) (j : ℕ) :
    Finset (Fin j → ClockCandidate T R g Ω) := by
  classical
  exact Finset.univ.filter fun π => IsDecPath r v π

/-- All candidates of the path are realized arrivals. -/
def pathRealized {T : ℕ} {R : Type*} {g : ℕ} {Ω : R → Type*} {j : ℕ}
    (ξ : ClockField T R g Ω) (π : Fin j → ClockCandidate T R g Ω) : Prop :=
  ∀ i, candidateIsArrival ξ (π i)

/-- The product of the first-arrival weights of the path's candidates. -/
noncomputable def pathWeight {T : ℕ} {R : Type*} {g : ℕ} {Ω : R → Type*} [∀ a, Fintype (Ω a)]
    (edgeLaw : ∀ e : RowLabel R g, FinProb (MeshClockValue T (Ω e.1))) {j : ℕ}
    (π : Fin j → ClockCandidate T R g Ω) : ℝ :=
  ∏ i, (edgeLaw ((π i).1, (π i).2.1)).w (MeshClockValue.tick (π i).2.2.1 (π i).2.2.2)

/-- The path visits a row of `sc` other than `r` (TeX 03:928, "meeting two distinct rows of the same test"). -/
def pathMeetsOtherRow {T : ℕ} {R : Type*} {g : ℕ} {Ω : R → Type*} {j : ℕ}
    (π : Fin j → ClockCandidate T R g Ω) (sc : Finset R) (r : R) : Prop :=
  ∃ i, (π i).1 ∈ sc ∧ (π i).1 ≠ r

/-- L3.10d-ins (03:912–918, finite-mesh insertion identity): for independent edge clocks, prescribing the values
of finitely many edges factors out their weights exactly; the remaining event is evaluated with those values
inserted. -/
theorem insertion_identity {T : ℕ} {R : Type*} [Fintype R] [DecidableEq R] {g : ℕ}
    {Ω : R → Type*} [∀ a, Fintype (Ω a)] [∀ a, DecidableEq (Ω a)]
    (edgeLaw : ∀ e : RowLabel R g, FinProb (MeshClockValue T (Ω e.1)))
    (ins : ∀ e : RowLabel R g, Option (MeshClockValue T (Ω e.1)))
    (G : ClockField T R g Ω → Prop) :
    (clockFieldLaw edgeLaw).pr (fun ξ => G ξ ∧ ∀ e x, ins e = some x → ξ e = x) =
      (∏ e, (ins e).elim 1 fun x => (edgeLaw e).w x) *
        (clockFieldLaw edgeLaw).pr (fun ξ => G (insertArrivals ins ξ)) := by
  sorry

/-- A decreasing path prescribes at most `j` edges (its edges are distinct). -/
theorem insertionSize_pathInsertion_le {T : ℕ} {R : Type*} [Fintype R] [DecidableEq R] {g : ℕ}
    {Ω : R → Type*} [∀ a, Fintype (Ω a)] (r v : Endpoint R g) {j : ℕ}
    (π : Fin j → ClockCandidate T R g Ω) (hπ : π ∈ decPaths r v j) :
    insertionSize (pathInsertion π) ≤ j := by
  sorry

/-- L3.10d-path (03:909–918): an endpoint of the closure is reached along a realized decreasing path from a root
(length at most the number of edges, since the edges are distinct); a union bound over the paths and the insertion
identity give, for any event `G`, the path-insertion bound. -/
theorem closure_path_union {T : ℕ} {R : Type*} [Fintype R] [DecidableEq R] {g : ℕ}
    {Ω : R → Type*} [∀ a, Fintype (Ω a)] [∀ a, DecidableEq (Ω a)]
    (edgeLaw : ∀ e : RowLabel R g, FinProb (MeshClockValue T (Ω e.1)))
    (roots : Finset (Endpoint R g)) (v : Endpoint R g) (G : ClockField T R g Ω → Prop) :
    (clockFieldLaw edgeLaw).pr (fun ξ => G ξ ∧ v ∈ closureFrom ξ roots) ≤
      ∑ r ∈ roots, ∑ j ∈ Finset.range (Fintype.card (RowLabel R g) + 1), ∑ π ∈ decPaths r v j,
        pathWeight edgeLaw π *
          (clockFieldLaw edgeLaw).pr (fun ξ => G (insertArrivals (pathInsertion π) ξ)) := by
  sorry

/-- L3.10d-time (03:920–926, discrete): the path weights of length `j` ending at `v`, summed over all starting
endpoints, are at most the reversed-walk rate product `θ^{⌊j/2⌋}` (`step4_path_insertion_bound`; rows have
total rate `1`, labels `θ`) times the mesh time sum: each arrival weight is at most `δ` times its mark mass, and
the ticks along a decreasing path are non-increasing, so there are at most `(T + j)^j / j!` tick sequences. -/
theorem decPath_weight_sum {T : ℕ} {R : Type*} [Fintype R] [DecidableEq R] {g : ℕ}
    {Ω : R → Type*} [∀ a, Fintype (Ω a)] [∀ a, DecidableEq (Ω a)]
    (δ : ℝ) (hδ : 0 ≤ δ) (hδ1 : δ ≤ 1) (p : ∀ a, FinProb (Ω a)) (lab : ∀ a, Ω a → Fin g) (θ : ℝ)
    (hrow : ∀ a, ∑ y, labMarg (p a) (lab a) y = 1) (hcol : ∀ y, ∑ a, labMarg (p a) (lab a) y = θ)
    (hθ0 : 0 ≤ θ) (hθ1 : θ ≤ 1) (v : Endpoint R g) (j : ℕ) :
    ∑ r, ∑ π ∈ decPaths r v j, pathWeight (samplingEdgeClockLaw (T := T) δ hδ hδ1 p lab) π ≤
      θ ^ (j / 2) * (((T + j : ℕ) : ℝ) * δ) ^ j / (j.factorial : ℝ) := by
  sorry

open Classical in
/-- L3.10d-two (03:928–936): paths from a scope row `r` of a predicate meeting another row of that scope. In the
reversed walk from `v`, choose the two positions (at most `j²` pairs) and a predicate containing the earlier row
(at most `D`); the later row is entered from a label with rate at most `D λ` instead of `θ`. -/
theorem two_row_weight_sum {T : ℕ} {R K : Type*} [Fintype R] [DecidableEq R] [Fintype K] {g : ℕ}
    {Ω : R → Type*} [∀ a, Fintype (Ω a)] [∀ a, DecidableEq (Ω a)]
    (δ : ℝ) (hδ : 0 ≤ δ) (hδ1 : δ ≤ 1) (p : ∀ a, FinProb (Ω a)) (lab : ∀ a, Ω a → Fin g) (θ : ℝ)
    (hrow : ∀ a, ∑ y, labMarg (p a) (lab a) y = 1) (hcol : ∀ y, ∑ a, labMarg (p a) (lab a) y = θ)
    (hθ0 : 0 < θ) (hθ1 : θ ≤ 1) (scope : K → Finset R) (D lam : ℝ) (hD : 0 ≤ D) (hlam0 : 0 ≤ lam)
    (hsc : ∀ k, ((scope k).card : ℝ) ≤ D)
    (hdeg : ∀ a, ((Finset.univ.filter fun k => a ∈ scope k).card : ℝ) ≤ D)
    (hlam : ∀ a y, labMarg (p a) (lab a) y ≤ lam) (v : Endpoint R g) (j : ℕ) :
    ∑ k, ∑ r ∈ scope k,
        ∑ π ∈ (decPaths (Sum.inl r) v j).filter (fun π => pathMeetsOtherRow π (scope k) r),
          pathWeight (samplingEdgeClockLaw (T := T) δ hδ hδ1 p lab) π ≤
      (j : ℝ) ^ 2 * D * (D * lam / θ) *
        (θ ^ (j / 2) * (((T + j : ℕ) : ℝ) * δ) ^ j / (j.factorial : ℝ)) := by
  sorry

/-- L3.10d-series (03:922–924): `∑_j θ^{⌊j/2⌋} x^j / j! ≤ e^{√θ x} / √θ`. -/
theorem walk_series_bound (θ x : ℝ) (hθ0 : 0 < θ) (hθ1 : θ ≤ 1) (hx : 0 ≤ x) (M : ℕ) :
    ∑ j ∈ Finset.range M, θ ^ (j / 2) * x ^ j / (j.factorial : ℝ) ≤
      Real.exp (Real.sqrt θ * x) / Real.sqrt θ := by
  sorry

/-- L3.10d-long (03:926–927, factorial tail): if `e² x ≤ J` then the terms of length above `J` sum to at most
`e^{-J}`. -/
theorem walk_series_tail (x : ℝ) (hx : 0 ≤ x) (J : ℕ) (hJ : Real.exp 2 * x ≤ J) (M : ℕ) :
    ∑ j ∈ Finset.Ico (J + 1) M, x ^ j / (j.factorial : ℝ) ≤ Real.exp (-(J : ℝ)) := by
  sorry

end HypercubeRamsey.Clock
