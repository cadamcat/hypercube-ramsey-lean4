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
  classical
  intro u hu
  change u ∈ Finset.univ.filter (fun v => ∃ h, inClosureFrom (insertArrivals ins ξ) roots (v, h)) at hu
  rcases Finset.mem_filter.mp hu with ⟨_, ⟨h, hrch⟩⟩
  rcases hrch with ⟨r, hr, hp⟩
  let ρ : ℕ := rootHorizon T R g
  let β : ClockField T R g Ω := insertArrivals (blockInsertion ins) ξ
  have htransfer : ∀ {v : BackwardPoint T R g},
      Relation.ReflTransGen (backwardStep (insertArrivals ins ξ)) (r, ρ) v →
        ∃ k, v.2 ≤ k ∧ k ≤ ρ ∧ inClosureFrom β (roots ∪ insertedEndpoints ins) (v.1, k) := by
    intro v hpath
    induction hpath with
    | refl =>
        refine ⟨ρ, by simp, le_rfl, ?_⟩
        exact ⟨r, Finset.mem_union.mpr (Or.inl hr), Relation.ReflTransGen.refl⟩
    | @tail b c hbc hstep ih =>
        rcases ih with ⟨k, hbk, hkρ, hreach⟩
        rcases hstep with ⟨e, heArr, heKey, hnext, hedges⟩
        let edge : RowLabel R g := (e.1, e.2.1)
        by_cases hnone : ins edge = none
        · have heArrβ : candidateIsArrival β e := by
            simpa [β, candidateIsArrival, insertArrivals, blockInsertion, edge, hnone] using heArr
          rcases hreach with ⟨q, hq, hqpath⟩
          have hβstep : backwardStep β (b.1, k) (c.1, c.2) := by
            refine ⟨e, heArrβ, ?_, hnext, hedges⟩
            exact lt_of_lt_of_le heKey hbk
          refine ⟨c.2, le_rfl, ?_, ⟨q, hq, Relation.ReflTransGen.tail hqpath hβstep⟩⟩
          rw [hnext]
          exact le_trans (Nat.le_of_lt (lt_of_lt_of_le heKey hbk)) hkρ
        · cases hins : ins edge with
          | none => exact False.elim (hnone hins)
          | some x =>
              have hx : x = MeshClockValue.tick e.2.2.1 e.2.2.2 := by
                simpa [candidateIsArrival, insertArrivals, edge, hins] using heArr
              have hdest : c.1 ∈ insertedEndpoints ins := by
                rw [insertedEndpoints, Finset.mem_filter]
                constructor
                · exact Finset.mem_univ _
                · refine ⟨edge, ?_, ?_⟩
                  · simp [edge, hins]
                  · change c.1 = Sum.inl e.1 ∨ c.1 = Sum.inr e.2.1
                    rcases hedges with ⟨_, hd⟩ | ⟨_, hd⟩
                    · exact Or.inr hd
                    · exact Or.inl hd
              refine ⟨ρ, ?_, le_rfl,
                ⟨c.1, Finset.mem_union.mpr (Or.inr hdest), Relation.ReflTransGen.refl⟩⟩
              rw [hnext]
              exact le_trans (Nat.le_of_lt (lt_of_lt_of_le heKey hbk)) hkρ
  obtain ⟨k, huk, hkρ, hclosure⟩ := htransfer hp
  change u ∈ Finset.univ.filter (fun v => ∃ h, inClosureFrom β (roots ∪ insertedEndpoints ins) (v, h))
  apply Finset.mem_filter.mpr
  exact ⟨Finset.mem_univ _, ⟨k, hclosure⟩⟩

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
  let a : ℝ := 2 * Real.sqrt θ * δ
  let q : ℝ := Real.exp a
  let Hrow : ℕ → ℝ := fun c =>
    1 + 4 * δ' * Real.exp (2 * Real.sqrt θ * ((c : ℝ) * δ)) / Real.sqrt θ
  let Hlab : ℕ → ℝ := fun c => 1 + 4 * δ' * Real.exp (2 * Real.sqrt θ * ((c : ℝ) * δ))
  have harg (c : ℕ) : 2 * Real.sqrt θ * ((c : ℝ) * δ) = a * (c : ℝ) := by
    dsimp [a]
    ring
  have hsqrt0 : 0 < Real.sqrt θ := Real.sqrt_pos.2 hθ0
  have hsqrt1 : Real.sqrt θ ≤ 1 := Real.sqrt_le_one.mpr hθ1
  have ha0 : 0 ≤ a := by dsimp [a]; positivity
  have hq1 : 1 ≤ q := by dsimp [q]; exact Real.one_le_exp ha0
  have hqa : a ≤ q - 1 := by
    dsimp [q]
    linarith [Real.add_one_le_exp a]
  have haT : a * (T : ℝ) = 2 * Real.sqrt θ * ((T : ℝ) * δ) := by
    dsimp [a]
    ring
  have hsmall' : δ' + 2 * δ' * q * Real.exp (a * (T : ℝ)) / Real.sqrt θ ≤ 1 := by
    rw [show Real.exp (a * (T : ℝ)) = Real.exp (2 * Real.sqrt θ * ((T : ℝ) * δ)) by
      rw [haT]]
    simpa [q, a] using hsmall
  have hmesh' : (q - 1) * Real.exp (a * (T : ℝ)) ≤ 1 / 2 := by
    rw [show Real.exp (a * (T : ℝ)) = Real.exp (2 * Real.sqrt θ * ((T : ℝ) * δ)) by
      rw [haT]]
    simpa [q, a] using hmesh
  have hgeom (c : ℕ) :
      (q - 1) * (∑ t ∈ Finset.range c, Real.exp (a * ((t + 1 : ℕ) : ℝ))) =
        q * (Real.exp (a * (c : ℝ)) - 1) := by
    induction c with
    | zero => simp [q]
    | succ c ih =>
        rw [Finset.sum_range_succ, mul_add, ih]
        have hfactor : Real.exp (a * ((c + 1 : ℕ) : ℝ)) =
            Real.exp (a * (c : ℝ)) * q := by
          dsimp [q]
          rw [show a * ((c + 1 : ℕ) : ℝ) = a * (c : ℝ) + a by push_cast; ring,
            Real.exp_add]
        rw [hfactor]
        ring
  have hsum_bound (c : ℕ) :
      δ * (∑ t ∈ Finset.range c, Real.exp (a * ((t + 1 : ℕ) : ℝ))) ≤
        q * (Real.exp (a * (c : ℝ)) - 1) / (2 * Real.sqrt θ) := by
    let S : ℝ := ∑ t ∈ Finset.range c, Real.exp (a * ((t + 1 : ℕ) : ℝ))
    have hS0 : 0 ≤ S := by
      dsimp [S]
      exact Finset.sum_nonneg fun t _ => (Real.exp_pos _).le
    have hmain : a * S ≤ q * (Real.exp (a * (c : ℝ)) - 1) := by
      rw [← hgeom c]
      exact mul_le_mul_of_nonneg_right hqa hS0
    have hden : 0 < 2 * Real.sqrt θ := by positivity
    apply (le_div_iff₀ hden).2
    calc
      (δ * S) * (2 * Real.sqrt θ) = a * S := by dsimp [a]; ring
      _ ≤ q * (Real.exp (a * (c : ℝ)) - 1) := hmain

  have hexp_small (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) : Real.exp x ≤ 1 + 2 * x := by
    have habs := Real.abs_exp_sub_one_le (show |x| ≤ 1 by simpa [abs_of_nonneg hx0] using hx1)
    have hlin : Real.exp x - 1 ≤ 2 * x := by
      have hnonneg : 0 ≤ Real.exp x - 1 := by linarith [Real.add_one_le_exp x]
      have := le_trans (le_abs_self (Real.exp x - 1)) habs
      simpa [abs_of_nonneg hx0] using this
    linarith
  have hcz (c : ℕ) (hc : c ≤ T) :
      Real.exp (a * (c : ℝ)) ≤ Real.exp (a * (T : ℝ)) := by
    apply Real.exp_le_exp.mpr
    exact mul_le_mul_of_nonneg_left (by exact_mod_cast hc) ha0
  have hmesh_c (c : ℕ) (hc : c ≤ T) :
      (q - 1) * Real.exp (a * (c : ℝ)) ≤ 1 / 2 := by
    exact le_trans (mul_le_mul_of_nonneg_left (hcz c hc) (sub_nonneg.mpr hq1)) hmesh'
  have hslack (c : ℕ) (hc : c ≤ T) :
      1 / 2 ≤ Real.exp (a * (c : ℝ)) - q * (Real.exp (a * (c : ℝ)) - 1) := by
    have hz : 1 ≤ Real.exp (a * (c : ℝ)) := Real.one_le_exp (mul_nonneg ha0 (by positivity))
    rw [show Real.exp (a * (c : ℝ)) - q * (Real.exp (a * (c : ℝ)) - 1) =
      q - (q - 1) * Real.exp (a * (c : ℝ)) by ring]
    linarith [hmesh_c c hc]
  change BranchingSupersolution δ δ' θ T Hrow Hlab
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro c
    change 1 ≤ 1 + 4 * δ' * Real.exp (2 * Real.sqrt θ * ((c : ℝ) * δ)) / Real.sqrt θ
    exact le_add_of_nonneg_right
      (div_nonneg (mul_nonneg (mul_nonneg (by norm_num) hδ') (Real.exp_pos _).le) hsqrt0.le)
  · intro c
    change 1 ≤ 1 + 4 * δ' * Real.exp (2 * Real.sqrt θ * ((c : ℝ) * δ))
    exact le_add_of_nonneg_right
      (mul_nonneg (mul_nonneg (by norm_num) hδ') (Real.exp_pos _).le)
  · intro c d hcd
    change 1 + 4 * δ' * Real.exp (2 * Real.sqrt θ * ((c : ℝ) * δ)) / Real.sqrt θ ≤
      1 + 4 * δ' * Real.exp (2 * Real.sqrt θ * ((d : ℝ) * δ)) / Real.sqrt θ
    apply add_le_add_right
    have harg : 2 * Real.sqrt θ * ((c : ℝ) * δ) ≤
        2 * Real.sqrt θ * ((d : ℝ) * δ) := by
      apply mul_le_mul_of_nonneg_left
      · exact mul_le_mul_of_nonneg_right (by exact_mod_cast hcd) hδ
      · exact mul_nonneg (by norm_num) (Real.sqrt_nonneg θ)
    have hexp : Real.exp (2 * Real.sqrt θ * ((c : ℝ) * δ)) ≤
        Real.exp (2 * Real.sqrt θ * ((d : ℝ) * δ)) := Real.exp_le_exp.mpr harg
    have hcoef : 0 ≤ 4 * δ' := mul_nonneg (by norm_num) hδ'
    have hterm : 4 * δ' * Real.exp (2 * Real.sqrt θ * ((c : ℝ) * δ)) / Real.sqrt θ ≤
        4 * δ' * Real.exp (2 * Real.sqrt θ * ((d : ℝ) * δ)) / Real.sqrt θ :=
      div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hexp hcoef) hsqrt0.le
    linarith
  · intro c d hcd
    change 1 + 4 * δ' * Real.exp (2 * Real.sqrt θ * ((c : ℝ) * δ)) ≤
      1 + 4 * δ' * Real.exp (2 * Real.sqrt θ * ((d : ℝ) * δ))
    have harg : 2 * Real.sqrt θ * ((c : ℝ) * δ) ≤
        2 * Real.sqrt θ * ((d : ℝ) * δ) := by
      apply mul_le_mul_of_nonneg_left
      · exact mul_le_mul_of_nonneg_right (by exact_mod_cast hcd) hδ
      · positivity
    have hcoef : 0 ≤ 4 * δ' := mul_nonneg (by norm_num) hδ'
    have hterm := mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr harg) hcoef
    linarith
  · intro c hc
    let S : ℝ := ∑ t ∈ Finset.range c, Real.exp (a * ((t + 1 : ℕ) : ℝ))
    have hsum : (∑ t ∈ Finset.range c, (Hlab (t + 1) - 1)) = 4 * δ' * S := by
      rw [show (∑ t ∈ Finset.range c, (Hlab (t + 1) - 1)) =
        ∑ t ∈ Finset.range c, (4 * δ' * Real.exp (a * ((t + 1 : ℕ) : ℝ))) by
          apply Finset.sum_congr rfl
          intro t ht
          simp [Hlab, harg]]
      simp [S, Finset.mul_sum]
    have hx : 0 ≤ δ' + δ * (∑ t ∈ Finset.range c, (Hlab (t + 1) - 1)) := by
      have hsum0 : 0 ≤ ∑ t ∈ Finset.range c, (Hlab (t + 1) - 1) := by
        apply Finset.sum_nonneg
        intro t ht
        simp only [Hlab]
        have hnonneg : 0 ≤ 4 * δ' * Real.exp (2 * Real.sqrt θ * (((t + 1 : ℕ) : ℝ) * δ)) :=
          mul_nonneg (mul_nonneg (by norm_num) hδ')
            (Real.exp_pos (2 * Real.sqrt θ * (((t + 1 : ℕ) : ℝ) * δ))).le
        nlinarith [hnonneg]
      exact add_nonneg hδ' (mul_nonneg hδ hsum0)
    have hxbound : δ' + δ * (∑ t ∈ Finset.range c, (Hlab (t + 1) - 1)) ≤
        δ' + (2 * δ' / Real.sqrt θ) * q * (Real.exp (a * (c : ℝ)) - 1) := by
      rw [hsum]
      have hsc : δ * S ≤ q * (Real.exp (a * (c : ℝ)) - 1) / (2 * Real.sqrt θ) := by
        simpa [S] using hsum_bound c
      have hzle := hcz c hc
      calc
        δ' + δ * (4 * δ' * S) = δ' + 4 * δ' * (δ * S) := by ring
        _ ≤ δ' + (2 * δ' / Real.sqrt θ) * q * (Real.exp (a * (c : ℝ)) - 1) := by
          have hmul := mul_le_mul_of_nonneg_left hsc (by positivity : 0 ≤ 4 * δ')
          have heq : 4 * δ' * (q * (Real.exp (a * (c : ℝ)) - 1) / (2 * Real.sqrt θ)) =
              (2 * δ' / Real.sqrt θ) * q * (Real.exp (a * (c : ℝ)) - 1) := by field_simp; ring
          calc
            δ' + 4 * δ' * (δ * S) ≤
                δ' + 4 * δ' * (q * (Real.exp (a * (c : ℝ)) - 1) / (2 * Real.sqrt θ)) := by linarith [hmul]
            _ = _ := by rw [heq]
        _ ≤ δ' + (2 * δ' / Real.sqrt θ) * q * (Real.exp (a * (c : ℝ)) - 1) := le_rfl
    have hxupper : δ' + δ * (∑ t ∈ Finset.range c, (Hlab (t + 1) - 1)) ≤ 1 := by
      calc
        _ ≤ δ' + (2 * δ' / Real.sqrt θ) * q * (Real.exp (a * (c : ℝ)) - 1) := hxbound
        _ ≤ δ' + (2 * δ' / Real.sqrt θ) * q * (Real.exp (a * (T : ℝ))) := by
          have hterm : Real.exp (a * (c : ℝ)) - 1 ≤ Real.exp (a * (T : ℝ)) := by
            have hz0 : 0 ≤ Real.exp (a * (c : ℝ)) - 1 :=
              sub_nonneg.mpr (Real.one_le_exp (mul_nonneg ha0 (by positivity)))
            linarith [hcz c hc]
          have hmul := mul_le_mul_of_nonneg_left hterm (by positivity :
            0 ≤ (2 * δ' / Real.sqrt θ) * q)
          nlinarith [hmul]
        _ = δ' + 2 * δ' * q * Real.exp (a * (T : ℝ)) / Real.sqrt θ := by ring
        _ ≤ 1 := hsmall'
    have hexp := hexp_small _ hx hxupper
    have hbound : Real.exp (δ' + δ * (∑ t ∈ Finset.range c, (Hlab (t + 1) - 1))) ≤
        1 + 2 * δ' + (4 * δ' / Real.sqrt θ) * q * (Real.exp (a * (c : ℝ)) - 1) := by
      calc
        _ ≤ 1 + 2 * (δ' + δ * (∑ t ∈ Finset.range c, (Hlab (t + 1) - 1))) := hexp
        _ ≤ 1 + 2 * (δ' + (2 * δ' / Real.sqrt θ) * q * (Real.exp (a * (c : ℝ)) - 1)) :=
          by nlinarith [mul_le_mul_of_nonneg_left hxbound (by norm_num : 0 ≤ (2 : ℝ))]
        _ = _ := by ring
    have hK0 : 0 ≤ 4 * δ' / Real.sqrt θ := div_nonneg (mul_nonneg (by norm_num) hδ') hsqrt0.le
    have hhalf : 2 * δ' ≤ (4 * δ' / Real.sqrt θ) / 2 := by
      calc
        2 * δ' ≤ 2 * δ' / Real.sqrt θ := by
          rw [le_div_iff₀ hsqrt0]
          have hprod : 0 ≤ (2 * δ') * (1 - Real.sqrt θ) :=
            mul_nonneg (mul_nonneg (by norm_num) hδ') (sub_nonneg.mpr hsqrt1)
          nlinarith [hprod]
        _ = (4 * δ' / Real.sqrt θ) / 2 := by ring
    have hslack' := mul_le_mul_of_nonneg_left (hslack c hc) hK0
    have hcompare : 1 + 2 * δ' + (4 * δ' / Real.sqrt θ) * q * (Real.exp (a * (c : ℝ)) - 1) ≤
        1 + (4 * δ' / Real.sqrt θ) * Real.exp (a * (c : ℝ)) := by
      nlinarith [hhalf, hslack']
    calc
      Real.exp (δ' + δ * (∑ t ∈ Finset.range c, (Hlab (t + 1) - 1))) ≤
          1 + 2 * δ' + (4 * δ' / Real.sqrt θ) * q * (Real.exp (a * (c : ℝ)) - 1) := hbound
      _ ≤ 1 + (4 * δ' / Real.sqrt θ) * Real.exp (a * (c : ℝ)) := hcompare
      _ = 1 + 4 * δ' * Real.exp (2 * Real.sqrt θ * ((c : ℝ) * δ)) / Real.sqrt θ := by
        have hac : a * (c : ℝ) = 2 * Real.sqrt θ * ((c : ℝ) * δ) := by dsimp [a]; ring
        rw [hac]
        ring
  · intro c hc
    let S : ℝ := ∑ t ∈ Finset.range c, Real.exp (a * ((t + 1 : ℕ) : ℝ))
    have hsum : (∑ t ∈ Finset.range c, (Hrow (t + 1) - 1)) = (4 * δ' / Real.sqrt θ) * S := by
      rw [show (∑ t ∈ Finset.range c, (Hrow (t + 1) - 1)) =
        ∑ t ∈ Finset.range c, ((4 * δ' / Real.sqrt θ) * Real.exp (a * ((t + 1 : ℕ) : ℝ))) by
          apply Finset.sum_congr rfl
          intro t ht
          simp [Hrow, harg]
          ring]
      simp [S, Finset.mul_sum]
    have hx : 0 ≤ δ' + θ * δ * (∑ t ∈ Finset.range c, (Hrow (t + 1) - 1)) := by
      have hsum0 : 0 ≤ ∑ t ∈ Finset.range c, (Hrow (t + 1) - 1) := by
        apply Finset.sum_nonneg
        intro t ht
        simp only [Hrow]
        have hnonneg : 0 ≤ 4 * δ' * Real.exp (2 * Real.sqrt θ * (((t + 1 : ℕ) : ℝ) * δ)) :=
          mul_nonneg (mul_nonneg (by norm_num) hδ')
            (Real.exp_pos (2 * Real.sqrt θ * (((t + 1 : ℕ) : ℝ) * δ))).le
        have hdiv : 0 ≤ (4 * δ' * Real.exp (2 * Real.sqrt θ * (((t + 1 : ℕ) : ℝ) * δ))) /
            Real.sqrt θ := div_nonneg hnonneg hsqrt0.le
        nlinarith [hdiv]
      exact add_nonneg hδ' (mul_nonneg (mul_nonneg hθ0.le hδ) hsum0)
    have hxbound : δ' + θ * δ * (∑ t ∈ Finset.range c, (Hrow (t + 1) - 1)) ≤
        δ' + 2 * δ' * q * (Real.exp (a * (c : ℝ)) - 1) := by
      rw [hsum]
      have hsc : δ * S ≤ q * (Real.exp (a * (c : ℝ)) - 1) / (2 * Real.sqrt θ) := by
        simpa [S] using hsum_bound c
      calc
        δ' + θ * δ * ((4 * δ' / Real.sqrt θ) * S) =
            δ' + 4 * δ' * Real.sqrt θ * (δ * S) := by
              have hdivsqrt : θ / Real.sqrt θ = Real.sqrt θ := by
                apply (div_eq_iff hsqrt0.ne').2
                nlinarith [Real.sq_sqrt hθ0.le]
              calc
                δ' + θ * δ * ((4 * δ' / Real.sqrt θ) * S) =
                    δ' + (θ / Real.sqrt θ) * (4 * δ' * δ * S) := by ring
                _ = δ' + Real.sqrt θ * (4 * δ' * δ * S) := by rw [hdivsqrt]
                _ = δ' + 4 * δ' * Real.sqrt θ * (δ * S) := by ring
        _ ≤ δ' + 2 * δ' * q * (Real.exp (a * (c : ℝ)) - 1) := by
          have hmul := mul_le_mul_of_nonneg_left hsc (by positivity : 0 ≤ 4 * δ' * Real.sqrt θ)
          have heq : 4 * δ' * Real.sqrt θ *
              (q * (Real.exp (a * (c : ℝ)) - 1) / (2 * Real.sqrt θ)) =
              2 * δ' * q * (Real.exp (a * (c : ℝ)) - 1) := by
            field_simp [hsqrt0.ne']
            ring
          calc
            δ' + 4 * δ' * Real.sqrt θ * (δ * S) ≤
                δ' + 4 * δ' * Real.sqrt θ *
                  (q * (Real.exp (a * (c : ℝ)) - 1) / (2 * Real.sqrt θ)) := by linarith [hmul]
            _ = _ := by rw [heq]
    have hxupper : δ' + θ * δ * (∑ t ∈ Finset.range c, (Hrow (t + 1) - 1)) ≤ 1 := by
      calc
        _ ≤ δ' + 2 * δ' * q * (Real.exp (a * (c : ℝ)) - 1) := hxbound
        _ ≤ δ' + 2 * δ' * q * Real.exp (a * (T : ℝ)) / Real.sqrt θ := by
          have hz0 : 0 ≤ Real.exp (a * (c : ℝ)) - 1 :=
            sub_nonneg.mpr (Real.one_le_exp (mul_nonneg ha0 (by positivity)))
          have hT : Real.exp (a * (T : ℝ)) ≤ Real.exp (a * (T : ℝ)) / Real.sqrt θ := by
            rw [le_div_iff₀ hsqrt0]
            have hprod : 0 ≤ Real.exp (a * (T : ℝ)) * (1 - Real.sqrt θ) :=
              mul_nonneg (Real.exp_pos (a * (T : ℝ))).le (sub_nonneg.mpr hsqrt1)
            nlinarith [hprod]
          have hterm : Real.exp (a * (c : ℝ)) - 1 ≤ Real.exp (a * (T : ℝ)) / Real.sqrt θ := by
            exact le_trans (by linarith [hcz c hc]) hT
          have hm := mul_le_mul_of_nonneg_left hterm (by positivity : 0 ≤ 2 * δ' * q)
          calc
            δ' + 2 * δ' * q * (Real.exp (a * (c : ℝ)) - 1) ≤
                δ' + 2 * δ' * q * (Real.exp (a * (T : ℝ)) / Real.sqrt θ) := by linarith [hm]
            _ = δ' + 2 * δ' * q * Real.exp (a * (T : ℝ)) / Real.sqrt θ := by ring
        _ ≤ 1 := hsmall'
    have hexp := hexp_small _ hx hxupper
    have hK0 : 0 ≤ 4 * δ' := by positivity
    have hhalf : 2 * δ' ≤ (4 * δ') / 2 := by nlinarith
    have hslack' := mul_le_mul_of_nonneg_left (hslack c hc) hK0
    have hcompare : 1 + 2 * δ' + 4 * δ' * q * (Real.exp (a * (c : ℝ)) - 1) ≤
        1 + 4 * δ' * Real.exp (a * (c : ℝ)) := by
      nlinarith [hhalf, hslack']
    calc
      Real.exp (δ' + θ * δ * (∑ t ∈ Finset.range c, (Hrow (t + 1) - 1))) ≤
          1 + 2 * δ' + 4 * δ' * q * (Real.exp (a * (c : ℝ)) - 1) := by
            calc
              _ ≤ 1 + 2 * (δ' + θ * δ * (∑ t ∈ Finset.range c, (Hrow (t + 1) - 1))) := hexp
              _ ≤ 1 + 2 * (δ' + 2 * δ' * q * (Real.exp (a * (c : ℝ)) - 1)) :=
                by nlinarith [mul_le_mul_of_nonneg_left hxbound (by norm_num : 0 ≤ (2 : ℝ))]
              _ = _ := by ring
      _ ≤ 1 + 4 * δ' * Real.exp (a * (c : ℝ)) := hcompare
      _ = Hlab c := by
        change 1 + 4 * δ' * Real.exp (a * (c : ℝ)) =
          1 + 4 * δ' * Real.exp (2 * Real.sqrt θ * ((c : ℝ) * δ))
        rw [harg c]

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
  classical
  let E := insertedEndpoints ins
  let roots' := roots ∪ E
  let edges : Finset (RowLabel R g) := Finset.univ.filter fun e => (ins e).isSome
  let ends : RowLabel R g → Finset (Endpoint R g) := fun e => {Sum.inl e.1, Sum.inr e.2}
  let count : ℕ := roots.card + 2 * insertionSize ins
  let C : ℝ := 4 * δ' * Real.exp (2 * Real.sqrt θ * ((T : ℝ) * δ)) / Real.sqrt θ
  let Hrow : ℕ → ℝ := fun c =>
    1 + 4 * δ' * Real.exp (2 * Real.sqrt θ * ((c : ℝ) * δ)) / Real.sqrt θ
  let Hlab : ℕ → ℝ := fun c => 1 + 4 * δ' * Real.exp (2 * Real.sqrt θ * ((c : ℝ) * δ))
  have hEsub : E ⊆ edges.biUnion ends := by
    intro u hu
    change u ∈ Finset.univ.filter (fun v => ∃ e, (ins e).isSome ∧ EdgeIncident v e) at hu
    rcases (Finset.mem_filter.mp hu).2 with ⟨e, he, hincident⟩
    apply Finset.mem_biUnion.mpr
    refine ⟨e, Finset.mem_filter.mpr ⟨Finset.mem_univ _, he⟩, ?_⟩
    simpa [ends, EdgeIncident] using hincident
  have hEcard : (E.card : ℝ) ≤ 2 * insertionSize ins := by
    calc
      (E.card : ℝ) ≤ ((edges.biUnion ends).card : ℝ) :=
        Nat.cast_le.mpr (Finset.card_le_card hEsub)
      _ ≤ ∑ e ∈ edges, ((ends e).card : ℝ) := by
        exact_mod_cast (Finset.card_biUnion_le (s := edges) (t := ends))
      _ ≤ ∑ e ∈ edges, (2 : ℝ) := by
        apply Finset.sum_le_sum
        intro e he
        simp [ends]
      _ = 2 * (edges.card : ℝ) := by simp [Finset.sum_const, nsmul_eq_mul]; ring
      _ = 2 * insertionSize ins := by
        simp [edges, insertionSize, Finset.filter]
  have hEcardNat : E.card ≤ 2 * insertionSize ins := by exact_mod_cast hEcard
  have hrootsCard : roots'.card ≤ count := by
    dsimp [roots', count]
    calc
      (roots ∪ E).card ≤ roots.card + E.card := Finset.card_union_le _ _
      _ ≤ roots.card + 2 * insertionSize ins := Nat.add_le_add_left hEcardNat roots.card
  have hblock : ∀ e x, blockInsertion ins e = some x → x = MeshClockValue.noArrival := by
    intro e x hx
    cases hi : ins e with
    | none => simp [blockInsertion, hi] at hx
    | some v =>
        have hx' : some MeshClockValue.noArrival = some x := by
          simpa [blockInsertion, hi] using hx
        exact (Option.some.inj hx').symm
  have hsuper : BranchingSupersolution δ δ' θ T Hrow Hlab := by
    simpa [Hrow, Hlab] using
      explicit_branching_supersolution δ δ' θ T hθ0 hθ1 hδ hδ'.le hsmall hmesh
  let P := clockFieldLaw (samplingEdgeClockLaw (T := T) δ hδ hδ1 p lab)
  have hblocked : P.expect
      (fun ξ => Real.exp (δ' * ((closureFrom (insertArrivals (blockInsertion ins) ξ) roots').card : ℝ))) ≤
        ∏ u ∈ roots', endpointMoment Hrow Hlab T u := by
    exact branching_domination δ hδ hδ1 p lab θ δ' hδ'.le hrow hcol Hrow Hlab hsuper
      (blockInsertion ins) hblock roots'
  have hC0 : 0 ≤ C := by dsimp [C]; positivity
  have hendpoint : ∀ u : Endpoint R g, endpointMoment Hrow Hlab T u ≤ Real.exp C := by
    intro u
    cases u with
    | inl a =>
        have hlin := Real.add_one_le_exp C
        change 1 + 4 * δ' * Real.exp (2 * Real.sqrt θ * ((T : ℝ) * δ)) / Real.sqrt θ ≤ Real.exp C
        dsimp [C] at hlin ⊢
        linarith
    | inr y =>
        have hlin := Real.add_one_le_exp C
        have hle : 4 * δ' * Real.exp (2 * Real.sqrt θ * ((T : ℝ) * δ)) ≤ C := by
          rw [le_div_iff₀ (Real.sqrt_pos.2 hθ0)]
          have hcoef : 0 ≤ 4 * δ' * Real.exp (2 * Real.sqrt θ * ((T : ℝ) * δ)) :=
            mul_nonneg (mul_nonneg (by norm_num) hδ'.le)
              (Real.exp_pos (2 * Real.sqrt θ * ((T : ℝ) * δ))).le
          have hsqrt1 : Real.sqrt θ ≤ 1 := Real.sqrt_le_one.mpr hθ1
          have hprod := mul_nonneg hcoef (sub_nonneg.mpr hsqrt1)
          nlinarith [hprod]
        change 1 + 4 * δ' * Real.exp (2 * Real.sqrt θ * ((T : ℝ) * δ)) ≤ Real.exp C
        dsimp [C] at hlin ⊢
        linarith
  have hendpointNonneg : ∀ u : Endpoint R g, 0 ≤ endpointMoment Hrow Hlab T u := by
    intro u
    cases u with
    | inl a => exact le_trans (by norm_num) (BranchingSupersolution.row_ge_one hsuper T)
    | inr y => exact le_trans (by norm_num) (BranchingSupersolution.lab_ge_one hsuper T)
  have hprod : ∏ u ∈ roots', endpointMoment Hrow Hlab T u ≤
      ∏ u ∈ roots', Real.exp C := by
    apply Finset.prod_le_prod₀
    · intro u hu
      exact hendpointNonneg u
    · intro u hu
      exact hendpoint u
  have hprodExp : (∏ u ∈ roots', Real.exp C) = Real.exp ((roots'.card : ℝ) * C) := by
    calc
      (∏ u ∈ roots', Real.exp C) = (Real.exp C) ^ roots'.card := by simp
      _ = Real.exp ((roots'.card : ℝ) * C) := by
        rw [← Real.exp_nat_mul C roots'.card]
  have hrootExponent : ((roots'.card : ℝ) * C) ≤ (count : ℝ) * C := by
    exact mul_le_mul_of_nonneg_right (Nat.cast_le.mpr hrootsCard) hC0
  have hmoment : P.expect
      (fun ξ => Real.exp (δ' * ((closureFrom (insertArrivals ins ξ) roots).card : ℝ))) ≤
      Real.exp (δ' * 0 + (count : ℝ) * C) := by
    calc
      P.expect (fun ξ => Real.exp (δ' * ((closureFrom (insertArrivals ins ξ) roots).card : ℝ))) ≤
          P.expect (fun ξ => Real.exp
            (δ' * ((closureFrom (insertArrivals (blockInsertion ins) ξ) roots').card : ℝ))) :=
        FinProb.expect_mono P (fun ξ => by
          have hsub := closure_insert_subset ξ ins roots
          have hcard := Finset.card_le_card hsub
          apply Real.exp_le_exp.mpr
          exact mul_le_mul_of_nonneg_left (Nat.cast_le.mpr hcard) hδ'.le)
      _ ≤ ∏ u ∈ roots', endpointMoment Hrow Hlab T u := hblocked
      _ ≤ ∏ u ∈ roots', Real.exp C := hprod
      _ = Real.exp ((roots'.card : ℝ) * C) := hprodExp
      _ ≤ Real.exp ((count : ℝ) * C) := Real.exp_le_exp.mpr hrootExponent
      _ = Real.exp (δ' * 0 + (count : ℝ) * C) := by ring_nf
  let size : (∀ e : RowLabel R g, MeshClockValue T (Ω e.1)) → ℕ :=
    fun ξ => (closureFrom (insertArrivals ins ξ) roots).card
  have htail := step5_giant_tail P size δ' 0 L ((count : ℝ) * C) hδ' hmoment
  simpa [P, size, C, count, mul_zero] using htail

end HypercubeRamsey.Clock
