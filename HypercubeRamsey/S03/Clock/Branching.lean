import HypercubeRamsey.S03.Clock.Paths

/-!
# The exploration rarely becomes giant (Lemma 3.10, Step 5 on the finite mesh)

Source: `sections/03-…tex`, lines 946–989. The endpoints of inserted arrivals become extra full-horizon roots
(`closure_insert_subset`): every reached endpoint is connected to a root by ordinary arrivals. Processing the
pending endpoint of largest horizon, its edges to unprocessed endpoints are fresh, so the closure is dominated by
a two-type branching forest whose node with cutoff `c` ticks has, on each incident edge of rate `r`, a child at
tick `t < c` with probability at most `δ r`, the child inheriting cutoff `t + 1`. A pair of functions satisfying
the discrete moment recursion (`BranchingSupersolution`) bounds the exponential moment of the closure size
(`branching_domination`); the explicit pair `1 + 4δ' e^{2√θ c δ}/√θ`, `1 + 4δ' e^{2√θ c δ}` is a supersolution
(`explicit_branching_supersolution`); exponential Markov (`step5_giant_tail`) gives the tail
(`giant_tail_under_insertion`).
-/

namespace HypercubeRamsey.Clock

open scoped BigOperators

/-- The single-root moment bound by endpoint type at cutoff `c`. -/
def endpointMoment {R : Type*} {g : ℕ} (Hrow Hlab : ℕ → ℝ) (c : ℕ) : Endpoint R g → ℝ
  | .inl _ => Hrow c
  | .inr _ => Hlab c

/-- D3.10e (03:963–973, discrete): a supersolution of the two-type branching moment recursion on the mesh.
`Hrow c` bounds `E exp(δ' · progeny)` for a row node whose children arrive at ticks `< c` (each child at tick
`t` has cutoff `t + 1`); rows have total rate at most `1`, labels at most `θ`, and the first-arrival probability
at a tick is at most `δ` times the rate. -/
structure BranchingSupersolution (δ δ' θ : ℝ) (T : ℕ) (Hrow Hlab : ℕ → ℝ) : Prop where
  row_ge_one : ∀ c, 1 ≤ Hrow c
  lab_ge_one : ∀ c, 1 ≤ Hlab c
  row_mono : Monotone Hrow
  lab_mono : Monotone Hlab
  row_step : ∀ c ≤ T, Real.exp (δ' + δ * ∑ t ∈ Finset.range c, (Hlab (t + 1) - 1)) ≤ Hrow c
  lab_step : ∀ c ≤ T, Real.exp (δ' + θ * δ * ∑ t ∈ Finset.range c, (Hrow (t + 1) - 1)) ≤ Hlab c

/-- The endpoints of the edges an insertion prescribes (TeX 03:948: "Include the endpoints of all inserted
arrivals as extra full-horizon roots"). -/
noncomputable def insertedEndpoints {T : ℕ} {R : Type*} [Fintype R] [DecidableEq R] {g : ℕ}
    {Ω : R → Type*} (ins : ∀ e : RowLabel R g, Option (MeshClockValue T (Ω e.1))) :
    Finset (Endpoint R g) := by
  classical
  exact Finset.univ.filter fun u => ∃ e, (ins e).isSome ∧ EdgeIncident u e

/-- Block every prescribed edge: prescribe no arrival where `ins` prescribes a value. -/
def blockInsertion {T : ℕ} {R : Type*} {g : ℕ} {Ω : R → Type*}
    (ins : ∀ e : RowLabel R g, Option (MeshClockValue T (Ω e.1))) :
    ∀ e : RowLabel R g, Option (MeshClockValue T (Ω e.1)) :=
  fun e => (ins e).map fun _ => MeshClockValue.noArrival

/-- L3.10e-roots (03:948–951): with the inserted endpoints as extra full-horizon roots, the closure of the field
with insertions is contained in the closure of the field with the prescribed edges blocked (take the part of a
reaching path after its last inserted edge). -/
theorem closure_insert_subset {T : ℕ} {R : Type*} [Fintype R] [DecidableEq R] {g : ℕ}
    {Ω : R → Type*} (ξ : ClockField T R g Ω)
    (ins : ∀ e : RowLabel R g, Option (MeshClockValue T (Ω e.1))) (roots : Finset (Endpoint R g)) :
    closureFrom (insertArrivals ins ξ) roots ⊆
      closureFrom (insertArrivals (blockInsertion ins) ξ) (roots ∪ insertedEndpoints ins) := by
  sorry

/-- L3.10e-dom (03:953–961, deferred construction on the mesh): for independent first-arrival clocks with row
rate sums at most `1` and column sums at most `θ`, and any insertion that only blocks edges, the exponential
moment of the closure size from full-horizon roots is at most the product of the single-root moments at the full
cutoff `T`. (Process the pending endpoint of largest horizon; its edges to unprocessed endpoints are fresh; its
sole processing is attached to its highest request; overlaps only shrink the closure.) -/
theorem branching_domination {T : ℕ} {R : Type*} [Fintype R] [DecidableEq R] {g : ℕ}
    {Ω : R → Type*} [∀ a, Fintype (Ω a)] [∀ a, DecidableEq (Ω a)]
    (δ : ℝ) (hδ : 0 ≤ δ) (hδ1 : δ ≤ 1) (p : ∀ a, FinProb (Ω a)) (lab : ∀ a, Ω a → Fin g)
    (θ δ' : ℝ) (hδ' : 0 ≤ δ')
    (hrow : ∀ a, ∑ y, labMarg (p a) (lab a) y ≤ 1) (hcol : ∀ y, ∑ a, labMarg (p a) (lab a) y ≤ θ)
    (Hrow Hlab : ℕ → ℝ) (hH : BranchingSupersolution δ δ' θ T Hrow Hlab)
    (ins : ∀ e : RowLabel R g, Option (MeshClockValue T (Ω e.1)))
    (hblock : ∀ e x, ins e = some x → x = MeshClockValue.noArrival)
    (roots : Finset (Endpoint R g)) :
    (clockFieldLaw (samplingEdgeClockLaw (T := T) δ hδ hδ1 p lab)).expect
        (fun ξ => Real.exp (δ' * ((closureFrom (insertArrivals ins ξ) roots).card : ℝ))) ≤
      ∏ u ∈ roots, endpointMoment Hrow Hlab T u := by
  sorry

/-- L3.10e-ode (03:974–978, discrete): the explicit excess bounds `4δ' e^{2√θ cδ}/√θ` (rows) and `4δ' e^{2√θ cδ}`
(labels) form a supersolution, using `e^x - 1 ≤ 2x` on `[0, 1]`, provided the exponents stay below `1` and the
mesh step is small against the growth `e^{2√θ T δ}`. -/
theorem explicit_branching_supersolution (δ δ' θ : ℝ) (T : ℕ) (hθ0 : 0 < θ) (hθ1 : θ ≤ 1)
    (hδ : 0 ≤ δ) (hδ' : 0 ≤ δ')
    (hsmall : δ' + 2 * δ' * Real.exp (2 * Real.sqrt θ * δ) *
        Real.exp (2 * Real.sqrt θ * ((T : ℝ) * δ)) / Real.sqrt θ ≤ 1)
    (hmesh : (Real.exp (2 * Real.sqrt θ * δ) - 1) * Real.exp (2 * Real.sqrt θ * ((T : ℝ) * δ)) ≤ 1 / 2) :
    BranchingSupersolution δ δ' θ T
      (fun c => 1 + 4 * δ' * Real.exp (2 * Real.sqrt θ * ((c : ℝ) * δ)) / Real.sqrt θ)
      (fun c => 1 + 4 * δ' * Real.exp (2 * Real.sqrt θ * ((c : ℝ) * δ))) := by
  sorry

/-- L3.10e (03:979–989): the giant tail under a fixed insertion. With `|roots| + 2·|insertion|` full-horizon
roots, exponential Markov at the moment bound gives
`Pr(|closure| ≥ L) ≤ exp(-δ' L + (|roots| + 2|ins|) · 4δ' e^{2√θ T δ}/√θ)`. Assembled from
`closure_insert_subset`, `branching_domination`, `explicit_branching_supersolution` and `step5_giant_tail`. -/
theorem giant_tail_under_insertion {T : ℕ} {R : Type*} [Fintype R] [DecidableEq R] {g : ℕ}
    {Ω : R → Type*} [∀ a, Fintype (Ω a)] [∀ a, DecidableEq (Ω a)]
    (δ : ℝ) (hδ : 0 ≤ δ) (hδ1 : δ ≤ 1) (p : ∀ a, FinProb (Ω a)) (lab : ∀ a, Ω a → Fin g)
    (θ δ' : ℝ) (hθ0 : 0 < θ) (hθ1 : θ ≤ 1) (hδ' : 0 < δ')
    (hrow : ∀ a, ∑ y, labMarg (p a) (lab a) y ≤ 1) (hcol : ∀ y, ∑ a, labMarg (p a) (lab a) y ≤ θ)
    (hsmall : δ' + 2 * δ' * Real.exp (2 * Real.sqrt θ * δ) *
        Real.exp (2 * Real.sqrt θ * ((T : ℝ) * δ)) / Real.sqrt θ ≤ 1)
    (hmesh : (Real.exp (2 * Real.sqrt θ * δ) - 1) * Real.exp (2 * Real.sqrt θ * ((T : ℝ) * δ)) ≤ 1 / 2)
    (roots : Finset (Endpoint R g)) (ins : ∀ e : RowLabel R g, Option (MeshClockValue T (Ω e.1)))
    (L : ℝ) :
    (clockFieldLaw (samplingEdgeClockLaw (T := T) δ hδ hδ1 p lab)).pr
        (fun ξ => L ≤ ((closureFrom (insertArrivals ins ξ) roots).card : ℝ)) ≤
      Real.exp (-δ' * L + ((roots.card + 2 * insertionSize ins : ℕ) : ℝ) *
        (4 * δ' * Real.exp (2 * Real.sqrt θ * ((T : ℝ) * δ)) / Real.sqrt θ)) := by
  sorry

end HypercubeRamsey.Clock
