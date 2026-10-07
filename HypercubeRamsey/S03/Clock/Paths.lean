import HypercubeRamsey.S03.Clock.Steps
import HypercubeRamsey.S03.Clock.Truncated
import Mathlib.Data.Sym.Card

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
  classical
  let S : Finset (RowLabel R g) := Finset.univ.filter fun e => (ins e).isSome
  let U : Finset (RowLabel R g) := Finset.univ \ S
  let fixed : ClockField T R g Ω → Prop := fun ξ =>
    ∀ e x, ins e = some x → ξ e = x
  let A : ClockField T R g Ω → ℝ := fun ξ => if fixed ξ then 1 else 0
  let B : ClockField T R g Ω → ℝ := fun ξ =>
    if G (insertArrivals ins ξ) then 1 else 0
  let null : ClockField T R g Ω := fun _ => .noArrival
  let val : (∀ i : {e // e ∈ S}, MeshClockValue T (Ω i.1.1)) :=
    fun i => (ins i.1).getD .noArrival
  have hfixedOnS (ξ : ClockField T R g Ω) :
      fixed ξ ↔ ∀ e, e ∈ S → ξ e = (ins e).getD .noArrival := by
    constructor
    · intro h e he
      have hsome : (ins e).isSome := (Finset.mem_filter.mp he).2
      cases hx : ins e with
      | none => simp [hx] at hsome
      | some x => simpa [hx] using h e x hx
    · intro h e x hx
      have he : e ∈ S := by simp [S, hx]
      simpa [hx] using h e he
  have hAdep : FinProb.DependsOn A S := by
    intro ξ ξ' hagree
    have hfixed : fixed ξ ↔ fixed ξ' := by
      constructor
      · intro h e x hx
        have he : e ∈ S := by simp [S, hx]
        calc
          ξ' e = ξ e := (hagree e he).symm
          _ = x := h e x hx
      · intro h e x hx
        have he : e ∈ S := by simp [S, hx]
        calc
          ξ e = ξ' e := hagree e he
          _ = x := h e x hx
    simp [A, hfixed]
  have hBdep : FinProb.DependsOn B U := by
    intro ξ ξ' hagree
    have hfields : insertArrivals ins ξ = insertArrivals ins ξ' := by
      funext e
      cases hx : ins e with
      | some x => simp [insertArrivals, hx]
      | none =>
          have heS : e ∉ S := by simp [S, hx]
          have heU : e ∈ U := by simp [U, heS]
          simpa [insertArrivals, hx] using hagree e heU
    simp [B, hfields]
  have hdisj : Disjoint S U := Finset.disjoint_left.mpr (by
    intro e heS heU
    exact (Finset.mem_sdiff.mp heU).2 heS)
  have hleft :
      (clockFieldLaw edgeLaw).pr (fun ξ => G ξ ∧ fixed ξ) =
        (clockFieldLaw edgeLaw).expect (fun ξ => A ξ * B ξ) := by
    simp only [FinProb.pr, FinProb.expect]
    apply Finset.sum_congr rfl
    intro ξ hξ
    by_cases hf : fixed ξ
    · have hins : insertArrivals ins ξ = ξ := by
        funext e
        cases hx : ins e with
        | none => simp [insertArrivals, hx]
        | some x => simp [insertArrivals, hx, hf e x hx]
      by_cases hg : G ξ <;> simp [A, B, hf, hg, hins]
    · have hEvent : ¬ (G ξ ∧ fixed ξ) := by
        rintro ⟨_, h⟩
        exact hf h
      have hA0 : A ξ = 0 := by simp [A, hf]
      simp only [hEvent, ite_false]
      rw [hA0]
      simp
  have hAon (a : ∀ i : {e // e ∈ S}, MeshClockValue T (Ω i.1.1)) :
      A ((Equiv.piEquivPiSubtypeProd (fun e => e ∈ S)
        (fun e => MeshClockValue T (Ω e.1))).symm (a, fun i => null i.1)) =
        if a = val then 1 else 0 := by
    have hfix : fixed ((Equiv.piEquivPiSubtypeProd (fun e => e ∈ S)
        (fun e => MeshClockValue T (Ω e.1))).symm (a, fun i => null i.1)) ↔ a = val := by
      rw [hfixedOnS]
      constructor
      · intro h
        funext i
        have hi := h i.1 i.2
        simpa [val, Equiv.piEquivPiSubtypeProd_symm_apply, i.2] using hi
      · intro h e he
        have hi := congrFun h ⟨e, he⟩
        simpa [val, Equiv.piEquivPiSubtypeProd_symm_apply, he] using hi
    simp [A, hfix]
  have hAexp :
      (clockFieldLaw edgeLaw).expect A =
        ∏ e, (ins e).elim 1 fun x => (edgeLaw e).w x := by
    calc
      (clockFieldLaw edgeLaw).expect A =
          (FinProb.pi edgeLaw).expect A := rfl
      _ = (FinProb.pi (fun i : {e // e ∈ S} => edgeLaw i.1)).expect
          (fun a => A ((Equiv.piEquivPiSubtypeProd (fun e => e ∈ S)
            (fun e => MeshClockValue T (Ω e.1))).symm (a, fun i => null i.1))) :=
          FinProb.pi_expect_depends edgeLaw S A null hAdep
      _ = ∏ i : {e // e ∈ S}, (edgeLaw i.1).w (val i) := by
          simp [FinProb.expect, FinProb.pi, hAon, val]
      _ = ∏ e, (ins e).elim 1 fun x => (edgeLaw e).w x := by
          calc
            (∏ i : {e // e ∈ S}, (edgeLaw i.1).w (val i)) =
                ∏ e ∈ S, (edgeLaw e).w ((ins e).getD .noArrival) := by
                  rw [Finset.univ_eq_attach]
                  simpa [val] using
                    (Finset.prod_attach S (fun e => (edgeLaw e).w ((ins e).getD .noArrival)))
            _ = ∏ e ∈ Finset.univ.filter (fun e => (ins e).isSome),
                (edgeLaw e).w ((ins e).getD .noArrival) := rfl
            _ = ∏ e, (ins e).elim 1 fun x => (edgeLaw e).w x := by
                  rw [Finset.prod_filter]
                  apply Finset.prod_congr rfl
                  intro e he
                  cases hx : ins e <;> simp [S, hx]
  have hBexp :
      (clockFieldLaw edgeLaw).expect B =
        (clockFieldLaw edgeLaw).pr (fun ξ => G (insertArrivals ins ξ)) := by
    simp [FinProb.expect, FinProb.pr, B]
  calc
    (clockFieldLaw edgeLaw).pr (fun ξ => G ξ ∧ fixed ξ) =
        (clockFieldLaw edgeLaw).expect (fun ξ => A ξ * B ξ) := hleft
    _ = (clockFieldLaw edgeLaw).expect A * (clockFieldLaw edgeLaw).expect B := by
        simpa [clockFieldLaw] using
          (FinProb.pi_expect_mul_of_disjoint edgeLaw A B S U hAdep hBdep hdisj)
    _ = (∏ e, (ins e).elim 1 fun x => (edgeLaw e).w x) *
        (clockFieldLaw edgeLaw).pr (fun ξ => G (insertArrivals ins ξ)) := by
          rw [hAexp, hBexp]

/-- A decreasing path prescribes at most `j` edges (its edges are distinct). -/
theorem insertionSize_pathInsertion_le {T : ℕ} {R : Type*} [Fintype R] [DecidableEq R] {g : ℕ}
    {Ω : R → Type*} [∀ a, Fintype (Ω a)] (r v : Endpoint R g) {j : ℕ}
    (π : Fin j → ClockCandidate T R g Ω) (hπ : π ∈ decPaths r v j) :
    insertionSize (pathInsertion π) ≤ j := by
  classical
  let S : Finset (RowLabel R g) := Finset.univ.filter fun e => (pathInsertion π e).isSome
  have hidx (e : {e // e ∈ S}) : ∃ i : Fin j, (candidateValueAt (π i) e.1).isSome := by
    have he : (pathInsertion π e.1).isSome := (Finset.mem_filter.mp e.2).2
    obtain ⟨c, hc, hsome⟩ := (by simpa [pathInsertion] using he :
      ∃ c, c ∈ List.ofFn π ∧ (candidateValueAt c e.1).isSome)
    obtain ⟨i, rfl⟩ := List.mem_ofFn.mp hc
    exact ⟨i, hsome⟩
  let idx : {e // e ∈ S} → Fin j := fun e => Classical.choose (hidx e)
  have hidxSome (e : {e // e ∈ S}) : (candidateValueAt (π (idx e)) e.1).isSome :=
    Classical.choose_spec (hidx e)
  have hcandidateEdge (c : ClockCandidate T R g Ω) (e : RowLabel R g)
      (h : (candidateValueAt c e).isSome) : e = (c.1, c.2.1) := by
    dsimp [candidateValueAt] at h
    split_ifs at h with hce
    · exact Prod.ext hce.1.symm hce.2.symm
    · simp at h
  have hinj : Function.Injective idx := by
    intro e e' h
    have heq : e.1 = ((π (idx e)).1, (π (idx e)).2.1) :=
      hcandidateEdge _ _ (hidxSome e)
    have heq' : e'.1 = ((π (idx e')).1, (π (idx e')).2.1) :=
      hcandidateEdge _ _ (hidxSome e')
    rw [← h] at heq'
    exact Subtype.ext (heq.trans heq'.symm)
  have hcard : S.card ≤ j := by
    simpa using (Fintype.card_le_of_injective idx hinj)
  simpa [insertionSize, S] using hcard

set_option maxHeartbeats 1000000 in
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
  classical
  let H : ℕ := rootHorizon T R g
  have pathOfReach (ξ : ClockField T R g Ω) {a target : BackwardPoint T R g}
      (h : Relation.ReflTransGen (backwardStep ξ) a target) (ha : a.2 ≤ H) :
      ∃ j, ∃ π : Fin j → ClockCandidate T R g Ω, IsDecPath a.1 target.1 π ∧
        (∀ i, eventPriority (π i) < a.2) ∧ pathRealized ξ π := by
    induction h using Relation.ReflTransGen.head_induction_on with
    | refl =>
        refine ⟨0, Fin.elim0, ?_, ?_, ?_⟩
        · refine ⟨fun _ => target.1, rfl, ?_, ?_, ?_, ?_⟩
          · simp
          · intro i
            exact Fin.elim0 i
          · intro i
            exact Fin.elim0 i
          · intro i i' hii
            exact Fin.elim0 i
        · intro i
          exact Fin.elim0 i
        · intro i
          exact Fin.elim0 i
    | head hab hbc ih =>
        rename_i src mid
        rcases hab with ⟨c, harr, hpriority, hdest, horient⟩
        have hb : mid.2 ≤ H := by
          rw [hdest]
          exact (hpriority.trans_le ha).le
        obtain ⟨j, π, hdec, hbelow, hreal⟩ := ih hb
        rcases hdec with ⟨w, hw0, hwlast, hedges, hrootKeys, hstrict⟩
        let π' : Fin (j + 1) → ClockCandidate T R g Ω := Fin.cons c π
        let w' : Fin (j + 2) → Endpoint R g := Fin.cons src.1 w
        have hstart : w' 0 = src.1 := by simp [w']
        have hend : w' (Fin.last (j + 1)) = target.1 := by
          simpa [w'] using hwlast
        have hedges' : ∀ i : Fin (j + 1),
            (w' i.castSucc = Sum.inl (π' i).1 ∧ w' i.succ = Sum.inr (π' i).2.1) ∨
            (w' i.castSucc = Sum.inr (π' i).2.1 ∧ w' i.succ = Sum.inl (π' i).1) := by
          intro i
          cases i using Fin.cases with
          | zero =>
              simpa [w', π', hw0, Fin.cons] using horient
          | succ i =>
              simpa [w', π', Fin.cons] using hedges i
        have hrootKeys' : ∀ i : Fin (j + 1), eventPriority (π' i) < H := by
          intro i
          cases i using Fin.cases with
          | zero =>
              simp only [π', Fin.cons_zero]
              exact hpriority.trans_le ha
          | succ i =>
              simpa [π'] using (hbelow i).trans_le hb
        have hstrict' : ∀ i i' : Fin (j + 1), i < i' →
            eventPriority (π' i') < eventPriority (π' i) := by
          intro i i' hii'
          cases i using Fin.cases with
          | zero =>
              cases i' using Fin.cases with
              | zero => omega
              | succ i' =>
                  simpa [π', hdest] using hbelow i'
          | succ i =>
              cases i' using Fin.cases with
              | zero => simp at hii'
              | succ i' =>
                  have hii : i < i' := Fin.succ_lt_succ_iff.mp hii'
                  simpa [π'] using hstrict i i' hii
        have hreal' : pathRealized ξ π' := by
          intro i
          cases i using Fin.cases with
          | zero => simpa [π'] using harr
          | succ i => simpa [π'] using hreal i
        refine ⟨j + 1, π', ?_, ?_, hreal'⟩
        · exact ⟨w', hstart, hend, hedges', hrootKeys', hstrict'⟩
        · intro i
          cases i using Fin.cases with
          | zero => simp only [π', Fin.cons_zero]; exact hpriority
          | succ i =>
              have hmid : mid.2 < src.2 := by
                rw [hdest]
                exact hpriority
              simpa [π'] using (hbelow i).trans hmid
  have edgeEq_candidateEq (ξ : ClockField T R g Ω) {j : ℕ}
      (π : Fin j → ClockCandidate T R g Ω) (hreal : pathRealized ξ π)
      (i i' : Fin j) (he : ((π i).1, (π i).2.1) = ((π i').1, (π i').2.1)) :
      π i = π i' := by
    rcases hpi : π i with ⟨a, y, t, o⟩
    rcases hpi' : π i' with ⟨a', y', t', o'⟩
    rw [hpi, hpi'] at he
    change (a, y) = (a', y') at he
    cases he
    have hval : MeshClockValue.tick t o = MeshClockValue.tick t' o' := by
      have h₁ : ξ (a, y) = MeshClockValue.tick t o := by
        have hh := hreal i
        change ξ ((π i).1, (π i).2.1) =
          MeshClockValue.tick (π i).2.2.1 (π i).2.2.2 at hh
        rw [hpi] at hh
        exact hh
      have h₂ : ξ (a, y) = MeshClockValue.tick t' o' := by
        have hh := hreal i'
        change ξ ((π i').1, (π i').2.1) =
          MeshClockValue.tick (π i').2.2.1 (π i').2.2.2 at hh
        rw [hpi'] at hh
        exact hh
      exact h₁.symm.trans h₂
    cases hval
    rfl
  have candidateValueAt_edge (c : ClockCandidate T R g Ω) (e : RowLabel R g)
      (h : (candidateValueAt c e).isSome) : e = (c.1, c.2.1) := by
    dsimp [candidateValueAt] at h
    split_ifs at h with hce
    · exact Prod.ext hce.1.symm hce.2.symm
    · simp at h
  have pathInsertion_at_edge {j : ℕ}
      (π : Fin j → ClockCandidate T R g Ω)
      (hinj : Function.Injective (fun i => ((π i).1, (π i).2.1))) (i : Fin j) :
      pathInsertion π ((π i).1, (π i).2.1) = candidateValueAt (π i) ((π i).1, (π i).2.1) := by
    let e : RowLabel R g := ((π i).1, (π i).2.1)
    have hvalue : (candidateValueAt (π i) e).isSome := by
      simp [candidateValueAt, e]
    have hsome : (pathInsertion π e).isSome := by
      change ((List.ofFn π).findSome? fun c => candidateValueAt c e).isSome
      exact List.findSome?_isSome_iff.mpr
        ⟨π i, List.mem_ofFn.mpr ⟨i, rfl⟩, hvalue⟩
    cases hins : pathInsertion π e with
    | none =>
        simp [hins] at hsome
    | some x =>
        have hfind := List.exists_of_findSome?_eq_some hins
        obtain ⟨c, hc, hcval⟩ := hfind
        obtain ⟨i', rfl⟩ := List.mem_ofFn.mp hc
        have heq : ((π i).1, (π i).2.1) = ((π i').1, (π i').2.1) := by
          calc
            ((π i).1, (π i).2.1) = e := rfl
            _ = ((π i').1, (π i').2.1) := candidateValueAt_edge _ _ (by
              rw [hcval]
              simp)
        have hii' : i = i' := hinj heq
        rw [← hii'] at hcval
        dsimp [e]
        exact hcval.symm
  have pathPins_iff (ξ : ClockField T R g Ω) {j : ℕ}
      (π : Fin j → ClockCandidate T R g Ω)
      (hinj : Function.Injective (fun i => ((π i).1, (π i).2.1))) :
      (∀ e x, pathInsertion π e = some x → ξ e = x) ↔ pathRealized ξ π := by
    constructor
    · intro hpins i
      let e : RowLabel R g := ((π i).1, (π i).2.1)
      have hcv : candidateValueAt (π i) e = some
          (MeshClockValue.tick (π i).2.2.1 (π i).2.2.2) := by
        simp [candidateValueAt, e]
      have hpres : pathInsertion π e =
          some (MeshClockValue.tick (π i).2.2.1 (π i).2.2.2) := by
        rw [pathInsertion_at_edge π hinj i]
        exact hcv
      have hξ := hpins e _ hpres
      simpa [candidateIsArrival, e] using hξ
    · intro hreal e x hins
      have hfind := List.exists_of_findSome?_eq_some hins
      obtain ⟨c, hc, hcv⟩ := hfind
      obtain ⟨i, rfl⟩ := List.mem_ofFn.mp hc
      have heq : e = ((π i).1, (π i).2.1) := candidateValueAt_edge _ _ (by
        rw [hcv]
        simp)
      cases heq
      have hval : MeshClockValue.tick (π i).2.2.1 (π i).2.2.2 = x := by
        simpa [candidateValueAt] using hcv
      have hreal_i : ξ ((π i).1, (π i).2.1) =
          MeshClockValue.tick (π i).2.2.1 (π i).2.2.2 := by
        simpa [candidateIsArrival] using hreal i
      exact hreal_i.trans hval
  have pathInsertion_product_eq
      (edgeLaw : ∀ e : RowLabel R g, FinProb (MeshClockValue T (Ω e.1)))
      {j : ℕ} (π : Fin j → ClockCandidate T R g Ω)
      (hinj : Function.Injective (fun i => ((π i).1, (π i).2.1))) :
      (∏ e, (pathInsertion π e).elim 1 fun x => (edgeLaw e).w x) = pathWeight edgeLaw π := by
    let edge : Fin j → RowLabel R g := fun i => ((π i).1, (π i).2.1)
    let E : Finset (RowLabel R g) := Finset.univ.image edge
    have hE (e : RowLabel R g) : e ∈ E ↔ (pathInsertion π e).isSome := by
      constructor
      · intro he
        obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp he
        have hpin := pathInsertion_at_edge π hinj i
        rw [hpin]
        simp [candidateValueAt]
      · intro he
        have hfind : ∃ c, c ∈ List.ofFn π ∧ (candidateValueAt c e).isSome := by
          simpa [pathInsertion] using he
        obtain ⟨c, hc, hcval⟩ := hfind
        obtain ⟨i, rfl⟩ := List.mem_ofFn.mp hc
        exact Finset.mem_image.mpr ⟨i, Finset.mem_univ i,
          (candidateValueAt_edge _ _ hcval).symm⟩
    let f : RowLabel R g → ℝ := fun e =>
      (edgeLaw e).w ((pathInsertion π e).getD .noArrival)
    have hprodAll :
        (∏ e, (pathInsertion π e).elim 1 fun x => (edgeLaw e).w x) =
          ∏ e, if e ∈ E then f e else 1 := by
      apply Finset.prod_congr rfl
      intro e he
      cases hx : pathInsertion π e with
      | none =>
          have hnot : e ∉ E := by
            intro hmem
            have := (hE e).mp hmem
            simp [hx] at this
          simp [f, hx, hnot]
      | some x =>
          have hmem : e ∈ E := (hE e).mpr (by simp [hx])
          simp [f, hx, hmem]
    have hfilter : (∏ e, if e ∈ E then f e else 1) = ∏ e ∈ E, f e := by
      symm
      simpa [E] using
        (Finset.prod_filter (s := Finset.univ) (p := fun e => e ∈ E) f)
    have himage : (∏ e ∈ E, f e) = ∏ i, f (edge i) := by
      dsimp [E]
      rw [Finset.prod_image (by
        intro i hi i' hi' he
        exact hinj he)]
    have hpoint (i : Fin j) : f (edge i) =
        (edgeLaw (edge i)).w (MeshClockValue.tick (π i).2.2.1 (π i).2.2.2) := by
      change (edgeLaw (edge i)).w ((pathInsertion π (edge i)).getD .noArrival) = _
      rw [pathInsertion_at_edge π hinj i]
      simp [candidateValueAt, edge]
    calc
      (∏ e, (pathInsertion π e).elim 1 fun x => (edgeLaw e).w x) =
          ∏ e, if e ∈ E then f e else 1 := hprodAll
      _ = ∏ e ∈ E, f e := hfilter
      _ = ∏ i, f (edge i) := himage
      _ = pathWeight edgeLaw π := by
          simp [pathWeight, hpoint, edge]
  have pathEdgeInjective (ξ : ClockField T R g Ω) {r : Endpoint R g} {j : ℕ}
      (π : Fin j → ClockCandidate T R g Ω) (hdec : IsDecPath r v π)
      (hreal : pathRealized ξ π) :
      Function.Injective (fun i => ((π i).1, (π i).2.1)) := by
    rcases hdec with ⟨w, hw0, hwlast, hedges, hkeys, hstrict⟩
    intro i i' he
    have hp := edgeEq_candidateEq ξ π hreal i i' he
    by_contra hne
    rcases lt_or_gt_of_ne hne with hlt | hgt
    · have hpriority := hstrict i i' hlt
      rw [hp] at hpriority
      omega
    · have hpriority := hstrict i' i hgt
      rw [hp] at hpriority
      omega
  have pathProbBound {r : Endpoint R g} {j : ℕ}
      (π : Fin j → ClockCandidate T R g Ω) (hdec : IsDecPath r v π) :
      (clockFieldLaw edgeLaw).pr (fun ξ => G ξ ∧ pathRealized ξ π) ≤
        pathWeight edgeLaw π *
          (clockFieldLaw edgeLaw).pr (fun ξ => G (insertArrivals (pathInsertion π) ξ)) := by
    classical
    by_cases hinj : Function.Injective (fun i => ((π i).1, (π i).2.1))
    ·
      have hpr :
          (clockFieldLaw edgeLaw).pr (fun ξ => G ξ ∧ pathRealized ξ π) =
            (clockFieldLaw edgeLaw).pr
              (fun ξ => G ξ ∧ ∀ e x, pathInsertion π e = some x → ξ e = x) := by
        unfold FinProb.pr
        apply Finset.sum_congr rfl
        intro ξ hξ
        have hpins := pathPins_iff ξ π hinj
        have hpinsPair :
            (∀ a b x, pathInsertion π (a, b) = some x → ξ (a, b) = x) ↔
              pathRealized ξ π := by
          constructor
          · intro h
            apply hpins.mp
            intro e x he
            rcases e with ⟨a, b⟩
            exact h a b x he
          · intro h
            have hp := hpins.mpr h
            intro a b x hx
            exact hp (a, b) x hx
        by_cases hG : G ξ <;> simp [hG, hpinsPair]
      calc
        (clockFieldLaw edgeLaw).pr (fun ξ => G ξ ∧ pathRealized ξ π) =
            (clockFieldLaw edgeLaw).pr
              (fun ξ => G ξ ∧ ∀ e x, pathInsertion π e = some x → ξ e = x) := hpr
        _ = (∏ e, (pathInsertion π e).elim 1 fun x => (edgeLaw e).w x) *
            (clockFieldLaw edgeLaw).pr
              (fun ξ => G (insertArrivals (pathInsertion π) ξ)) :=
              insertion_identity edgeLaw (pathInsertion π) G
        _ = pathWeight edgeLaw π *
            (clockFieldLaw edgeLaw).pr
              (fun ξ => G (insertArrivals (pathInsertion π) ξ)) := by
                rw [pathInsertion_product_eq edgeLaw π hinj]
        _ ≤ pathWeight edgeLaw π *
            (clockFieldLaw edgeLaw).pr
              (fun ξ => G (insertArrivals (pathInsertion π) ξ)) := le_rfl
    · have hfalse : ∀ ξ, ¬ (G ξ ∧ pathRealized ξ π) := by
        intro ξ hξ
        exact hinj (pathEdgeInjective ξ π hdec hξ.2)
      have hzero :
          (clockFieldLaw edgeLaw).pr (fun ξ => G ξ ∧ pathRealized ξ π) = 0 := by
        unfold FinProb.pr
        apply Finset.sum_eq_zero
        intro ξ hξ
        simp [hfalse ξ]
      have hweight : 0 ≤ pathWeight edgeLaw π := by
        unfold pathWeight
        exact Finset.prod_nonneg fun i hi => (edgeLaw ((π i).1, (π i).2.1)).nonneg _
      have hprob :
          0 ≤ (clockFieldLaw edgeLaw).pr
            (fun ξ => G (insertArrivals (pathInsertion π) ξ)) := by
        unfold FinProb.pr
        exact Finset.sum_nonneg fun ξ hξ => by
          split_ifs
          · exact (clockFieldLaw edgeLaw).nonneg ξ
          · exact le_rfl
      rw [hzero]
      exact mul_nonneg hweight hprob
  have hcover (ξ : ClockField T R g Ω) :
      (G ξ ∧ v ∈ closureFrom ξ roots) →
        ∃ r ∈ roots, ∃ j ∈ Finset.range (Fintype.card (RowLabel R g) + 1),
          ∃ π : Fin j → ClockCandidate T R g Ω,
            IsDecPath r v π ∧ pathRealized ξ π := by
    rintro ⟨_, hv⟩
    have hv' : ∃ n, inClosureFrom ξ roots (v, n) := by
      simpa [closureFrom] using hv
    obtain ⟨n, hclose⟩ := hv'
    have hroot : ∃ root : Endpoint R g, root ∈ roots ∧
        Relation.ReflTransGen (backwardStep ξ) (root, rootHorizon T R g) (v, n) := by
      simpa [inClosureFrom] using hclose
    let root : Endpoint R g := Classical.choose hroot
    have hrootSpec := Classical.choose_spec hroot
    have hr : root ∈ roots := hrootSpec.1
    have hreach : Relation.ReflTransGen (backwardStep ξ)
        (root, rootHorizon T R g) (v, n) := hrootSpec.2
    obtain ⟨j, π, hdec, hkeys, hreal⟩ := pathOfReach ξ hreach (by rfl)
    have hj : j ≤ Fintype.card (RowLabel R g) := by
      simpa using Fintype.card_le_of_injective
        (fun i => ((π i).1, (π i).2.1)) (pathEdgeInjective ξ π hdec hreal)
    have hj' : j ∈ Finset.range (Fintype.card (RowLabel R g) + 1) := by
      simp only [Finset.mem_range]
      omega
    exact ⟨root, hr, j, hj', π, hdec, hreal⟩
  let PathIndex :=
    Σ r : {r : Endpoint R g // r ∈ roots},
      Σ j : {j : ℕ // j ∈ Finset.range (Fintype.card (RowLabel R g) + 1)},
        {π : Fin j.1 → ClockCandidate T R g Ω // π ∈ decPaths r.1 v j.1}
  let TermVal (r : Endpoint R g) (j : ℕ) (π : Fin j → ClockCandidate T R g Ω) : ℝ :=
    pathWeight edgeLaw π *
      (clockFieldLaw edgeLaw).pr
        (fun ξ => G (insertArrivals (pathInsertion π) ξ))
  let Term (r : {r : Endpoint R g // r ∈ roots})
      (j : {j : ℕ // j ∈ Finset.range (Fintype.card (RowLabel R g) + 1)})
      (π : {π : Fin j.1 → ClockCandidate T R g Ω // π ∈ decPaths r.1 v j.1}) : ℝ :=
    TermVal r.1 j.1 π.1
  let TermTail (r : {r : Endpoint R g // r ∈ roots})
      (q : Σ j : {j : ℕ // j ∈ Finset.range (Fintype.card (RowLabel R g) + 1)},
        {π : Fin j.1 → ClockCandidate T R g Ω // π ∈ decPaths r.1 v j.1}) : ℝ :=
    Term r q.1 q.2
  let pathEvent (q : PathIndex) (ξ : ClockField T R g Ω) : Prop :=
    G ξ ∧ pathRealized ξ q.2.2.1
  let pathTerm (q : PathIndex) : ℝ := TermTail q.1 q.2
  have hcoverIndex (ξ : ClockField T R g Ω)
      (hξ : G ξ ∧ v ∈ closureFrom ξ roots) : ∃ q : PathIndex, pathEvent q ξ := by
    obtain ⟨r, hr, j, hj, π, hdec, hreal⟩ := hcover ξ hξ
    let r' : {r : Endpoint R g // r ∈ roots} := ⟨r, hr⟩
    let j' : {j : ℕ // j ∈ Finset.range (Fintype.card (RowLabel R g) + 1)} := ⟨j, hj⟩
    have hπ : π ∈ decPaths r v j := by simp [decPaths, hdec]
    let π' : {π : Fin j' → ClockCandidate T R g Ω // π ∈ decPaths r'.1 v j'} := ⟨π, hπ⟩
    exact ⟨⟨r', ⟨j', π'⟩⟩, ⟨hξ.1, hreal⟩⟩
  have hunion :
      (clockFieldLaw edgeLaw).pr (fun ξ => ∃ q : PathIndex, pathEvent q ξ) ≤
        ∑ q : PathIndex, (clockFieldLaw edgeLaw).pr (pathEvent q) := by
    simpa using finProb_pr_biUnion_le_sum (clockFieldLaw edgeLaw)
      (Finset.univ : Finset PathIndex) pathEvent
  have hsumPath :
      ∑ q : PathIndex, (clockFieldLaw edgeLaw).pr (pathEvent q) ≤
        ∑ q : PathIndex, pathTerm q := by
    apply Finset.sum_le_sum
    intro q hq
    have hmem := q.2.2.2
    change q.2.2.1 ∈ Finset.univ.filter (fun π => IsDecPath q.1.1 v π) at hmem
    exact pathProbBound q.2.2.1 (Finset.mem_filter.mp hmem).2
  have hsumIndex :
      ∑ q : PathIndex, pathTerm q =
        ∑ r ∈ roots, ∑ j ∈ Finset.range (Fintype.card (RowLabel R g) + 1),
          ∑ π ∈ decPaths r v j,
            pathWeight edgeLaw π *
              (clockFieldLaw edgeLaw).pr
                (fun ξ => G (insertArrivals (pathInsertion π) ξ)) := by
    classical
    have houter :
        (∑ q : PathIndex, pathTerm q) =
          ∑ r : {r : Endpoint R g // r ∈ roots},
            ∑ q : (Σ j : {j : ℕ // j ∈ Finset.range (Fintype.card (RowLabel R g) + 1)},
              {π : Fin j.1 → ClockCandidate T R g Ω // π ∈ decPaths r.1 v j.1}),
              TermTail r q := by
      change (∑ q : (Σ r : {r : Endpoint R g // r ∈ roots},
          Σ j : {j : ℕ // j ∈ Finset.range (Fintype.card (RowLabel R g) + 1)},
            {π : Fin j.1 → ClockCandidate T R g Ω // π ∈ decPaths r.1 v j.1}),
          TermTail q.1 q.2) = _
      rw [Fintype.sum_sigma']
    have hinner (r : {r : Endpoint R g // r ∈ roots}) :
        (∑ q : (Σ j : {j : ℕ // j ∈ Finset.range (Fintype.card (RowLabel R g) + 1)},
          {π : Fin j.1 → ClockCandidate T R g Ω // π ∈ decPaths r.1 v j.1}), TermTail r q) =
            ∑ j : {j : ℕ // j ∈ Finset.range (Fintype.card (RowLabel R g) + 1)},
              ∑ π : {π : Fin j.1 → ClockCandidate T R g Ω // π ∈ decPaths r.1 v j.1}, Term r j π := by
      change (∑ q : (Σ j : {j : ℕ // j ∈ Finset.range (Fintype.card (RowLabel R g) + 1)},
          {π : Fin j.1 → ClockCandidate T R g Ω // π ∈ decPaths r.1 v j.1}), Term r q.1 q.2) = _
      rw [Fintype.sum_sigma']
    have hπattach (r : {r : Endpoint R g // r ∈ roots})
        (j : {j : ℕ // j ∈ Finset.range (Fintype.card (RowLabel R g) + 1)}) :
        (∑ π : {π : Fin j.1 → ClockCandidate T R g Ω // π ∈ decPaths r.1 v j.1}, Term r j π) =
          ∑ π ∈ decPaths r.1 v j.1, TermVal r.1 j.1 π := by
      rw [Finset.univ_eq_attach]
      simpa [Term] using
        (Finset.sum_attach (decPaths r.1 v j.1) (fun π => TermVal r.1 j.1 π))
    have hlenAttach (r : {r : Endpoint R g // r ∈ roots}) :
        (∑ j : {j : ℕ // j ∈ Finset.range (Fintype.card (RowLabel R g) + 1)},
          ∑ π ∈ decPaths r.1 v j.1, TermVal r.1 j.1 π) =
            ∑ j ∈ Finset.range (Fintype.card (RowLabel R g) + 1),
              ∑ π ∈ decPaths r.1 v j, TermVal r.1 j π := by
      rw [Finset.univ_eq_attach]
      simpa using (Finset.sum_attach (Finset.range (Fintype.card (RowLabel R g) + 1))
        (fun j => ∑ π ∈ decPaths r.1 v j, TermVal r.1 j π))
    have hrootAttach :
        (∑ r : {r : Endpoint R g // r ∈ roots},
          ∑ j ∈ Finset.range (Fintype.card (RowLabel R g) + 1),
            ∑ π ∈ decPaths r.1 v j, TermVal r.1 j π) =
          ∑ r ∈ roots, ∑ j ∈ Finset.range (Fintype.card (RowLabel R g) + 1),
            ∑ π ∈ decPaths r v j, TermVal r j π := by
      rw [Finset.univ_eq_attach]
      simpa using (Finset.sum_attach roots (fun r =>
        ∑ j ∈ Finset.range (Fintype.card (RowLabel R g) + 1),
          ∑ π ∈ decPaths r v j, TermVal r j π))
    calc
      (∑ q : PathIndex, pathTerm q) =
          ∑ r : {r : Endpoint R g // r ∈ roots},
            ∑ q : (Σ j : {j : ℕ // j ∈ Finset.range (Fintype.card (RowLabel R g) + 1)},
              {π : Fin j.1 → ClockCandidate T R g Ω // π ∈ decPaths r.1 v j.1}),
              TermTail r q := houter
      _ = ∑ r : {r : Endpoint R g // r ∈ roots},
            ∑ j : {j : ℕ // j ∈ Finset.range (Fintype.card (RowLabel R g) + 1)},
            ∑ π : {π : Fin j.1 → ClockCandidate T R g Ω // π ∈ decPaths r.1 v j.1}, Term r j π := by
          apply Finset.sum_congr rfl
          intro r hr
          exact hinner r
      _ = ∑ r : {r : Endpoint R g // r ∈ roots},
            ∑ j : {j : ℕ // j ∈ Finset.range (Fintype.card (RowLabel R g) + 1)},
              ∑ π ∈ decPaths r.1 v j.1, TermVal r.1 j.1 π := by
          apply Finset.sum_congr rfl
          intro r hr
          apply Finset.sum_congr rfl
          intro j hj
          exact hπattach r j
      _ = ∑ r : {r : Endpoint R g // r ∈ roots},
            ∑ j ∈ Finset.range (Fintype.card (RowLabel R g) + 1),
              ∑ π ∈ decPaths r.1 v j, TermVal r.1 j π := by
          apply Finset.sum_congr rfl
          intro r hr
          exact hlenAttach r
      _ = ∑ r ∈ roots, ∑ j ∈ Finset.range (Fintype.card (RowLabel R g) + 1),
            ∑ π ∈ decPaths r v j, TermVal r j π := hrootAttach
      _ = _ := by simp [TermVal, decPaths]
  have hsubset :
      (clockFieldLaw edgeLaw).pr (fun ξ => G ξ ∧ v ∈ closureFrom ξ roots) ≤
        (clockFieldLaw edgeLaw).pr (fun ξ => ∃ q : PathIndex, pathEvent q ξ) := by
    classical
    apply finProb_pr_mono (clockFieldLaw edgeLaw)
    intro ξ hξ
    obtain ⟨q, hq⟩ := hcoverIndex ξ hξ
    exact ⟨q, hq⟩
  exact hsubset.trans (hunion.trans (hsumPath.trans_eq hsumIndex))

/-- L3.10d-time (03:920–926, discrete): the path weights of length `j` ending at `v`, summed over all starting
endpoints, are at most the reversed-walk rate product `θ^{⌊j/2⌋}` (`step4_path_insertion_bound`; rows have
total rate `1`, labels `θ`) times the mesh time sum: each arrival weight is at most `δ` times its mark mass, and
the ticks along a decreasing path are non-increasing, so there are at most `(T + j)^j / j!` tick sequences. -/
private theorem antitoneTickCount_le (T j : ℕ) :
    (Fintype.card {t : Fin j → Fin T // Antitone fun i => (t i).val} : ℝ) ≤
      ((T + j : ℕ) : ℝ) ^ j / (j.factorial : ℝ) := by
  classical
  let toSym : {t : Fin j → Fin T // Antitone fun i => (t i).val} → Sym (Fin T) j :=
    fun t => ⟨Multiset.ofList (List.ofFn t.1), by simp⟩
  have htoSym : Function.Injective toSym := by
    intro t u h
    apply Subtype.ext
    have hm : Multiset.ofList (List.ofFn t.1) = Multiset.ofList (List.ofFn u.1) :=
      congrArg Subtype.val h
    have hp : (List.ofFn t.1).Perm (List.ofFn u.1) := by
      exact Multiset.coe_eq_coe.mp hm
    have hs₁ : (List.ofFn t.1).SortedGE := List.sortedGE_ofFn_iff.mpr t.2
    have hs₂ : (List.ofFn u.1).SortedGE := List.sortedGE_ofFn_iff.mpr u.2
    exact List.ofFn_injective (hp.eq_of_sortedGE hs₁ hs₂)
  have hcard :
      Fintype.card {t : Fin j → Fin T // Antitone fun i => (t i).val} ≤
        Nat.choose (T + j) j := by
    calc
      Fintype.card {t : Fin j → Fin T // Antitone fun i => (t i).val} ≤
          Fintype.card (Sym (Fin T) j) := Fintype.card_le_of_injective toSym htoSym
      _ = Nat.multichoose T j := by rw [Sym.card_sym_fin_eq_multichoose]
      _ = Nat.choose (T + j - 1) j := Nat.multichoose_eq T j
      _ ≤ Nat.choose (T + j) j := Nat.choose_le_choose j (Nat.sub_le _ _)
  have hchoose := Nat.choose_le_pow_div (α := ℝ) j (T + j)
  have hcard' :
      (Fintype.card {t : Fin j → Fin T // Antitone fun i => (t i).val} : ℝ) ≤
        (Nat.choose (T + j) j : ℝ) := by exact_mod_cast hcard
  exact hcard'.trans hchoose

private theorem eventPriority_tick_le {T : ℕ} {R : Type*} [Fintype R] [DecidableEq R] {g : ℕ}
    {Ω : R → Type*} (c d : ClockCandidate T R g Ω)
    (h : eventPriority d < eventPriority c) : d.2.2.1.val ≤ c.2.2.1.val := by
  let base := Fintype.card R * g
  let low (e : ClockCandidate T R g Ω) := (Fintype.equivFin R e.1).val * g + e.2.1.val
  have hlow (e : ClockCandidate T R g Ω) : low e < base := by
    dsimp [low, base]
    calc
      (Fintype.equivFin R e.1).val * g + e.2.1.val <
          (Fintype.equivFin R e.1).val * g + g := Nat.add_lt_add_left e.2.1.isLt _
      _ = Nat.succ (Fintype.equivFin R e.1).val * g := by rw [Nat.succ_mul]
      _ ≤ Fintype.card R * g :=
        Nat.mul_le_mul_right g (Nat.succ_le_of_lt (Fintype.equivFin R e.1).isLt)
  have hkey (e : ClockCandidate T R g Ω) :
      eventPriority e = e.2.2.1.val * base + low e := by
    simp [eventPriority, base, low, Nat.add_assoc]
  by_contra hnot
  have htime : c.2.2.1.val + 1 ≤ d.2.2.1.val := by omega
  have hcut : (c.2.2.1.val + 1) * base ≤ eventPriority d := by
    rw [hkey d]
    calc
      (c.2.2.1.val + 1) * base ≤ d.2.2.1.val * base := Nat.mul_le_mul_right base htime
      _ ≤ d.2.2.1.val * base + low d := Nat.le_add_right _ _
  have hc : eventPriority c < (c.2.2.1.val + 1) * base := by
    rw [hkey c]
    calc
      c.2.2.1.val * base + low c < c.2.2.1.val * base + base := Nat.add_lt_add_left (hlow c) _
      _ = (c.2.2.1.val + 1) * base := by rw [Nat.succ_mul]
  omega

private theorem pathCandidateTicks_antitone {T : ℕ} {R : Type*} [Fintype R] [DecidableEq R]
    {g : ℕ} {Ω : R → Type*} {j : ℕ} (π : Fin j → ClockCandidate T R g Ω)
    (hstrict : ∀ i i', i < i' → eventPriority (π i') < eventPriority (π i)) :
    Antitone fun i => (π i).2.2.1.val := by
  apply (antitone_iff_forall_lt).2
  intro i i' hii
  exact eventPriority_tick_le (π i) (π i') (hstrict i i' hii)

private theorem decPath_cons_tail {T : ℕ} {R : Type*} [Fintype R] [DecidableEq R] {g n : ℕ}
    {Ω : R → Type*} (r : R) (v : Endpoint R g)
    (π : Fin (n + 1) → ClockCandidate T R g Ω)
    (hπ : IsDecPath (Sum.inl r) v π) :
    (π 0).1 = r ∧ IsDecPath (Sum.inr (π 0).2.1) v (fun i : Fin n => π i.succ) := by
  rcases hπ with ⟨w, hw0, hwlast, hedges, hkeys, hstrict⟩
  have hfirst := hedges (0 : Fin (n + 1))
  have hrow : (π 0).1 = r := by
    rcases hfirst with ⟨h0, _⟩ | ⟨h0, _⟩
    · exact (Sum.inl.inj (hw0.symm.trans h0)).symm
    · exact False.elim (Sum.inl_ne_inr (hw0.symm.trans h0))
  have hlabel : w (Fin.succ (0 : Fin (n + 1))) = Sum.inr (π 0).2.1 := by
    rcases hfirst with ⟨_, h1⟩ | ⟨h0, _⟩
    · exact h1
    · exact False.elim (Sum.inl_ne_inr (hw0.symm.trans h0))
  refine ⟨hrow, ?_⟩
  let w' : Fin (n + 1) → Endpoint R g := fun i => w i.succ
  have hstart : w' 0 = Sum.inr (π 0).2.1 := by simpa [w'] using hlabel
  have hlast : w' (Fin.last n) = v := by
    change w (Fin.last n).succ = v
    have hidx : (Fin.last n).succ = Fin.last (n + 1) := by
      apply Fin.ext
      simp
    rw [hidx]
    exact hwlast
  have hedges' (i : Fin n) :
      (w' i.castSucc = Sum.inl (π i.succ).1 ∧
        w' i.succ = Sum.inr (π i.succ).2.1) ∨
      (w' i.castSucc = Sum.inr (π i.succ).2.1 ∧
        w' i.succ = Sum.inl (π i.succ).1) := by
    have h := hedges i.succ
    simpa [w', Fin.castSucc_succ] using h
  have hkeys' (i : Fin n) : eventPriority (π i.succ) < rootHorizon T R g :=
    hkeys i.succ
  have hstrict' (i i' : Fin n) (hii : i < i') :
      eventPriority (π i'.succ) < eventPriority (π i.succ) :=
    hstrict i.succ i'.succ (Fin.strictMono_succ hii)
  exact ⟨w', hstart, hlast, hedges', hkeys', hstrict'⟩

private theorem samplingTickWeight_le_mark {T : ℕ} {R : Type*} {g : ℕ}
    {Ω : R → Type*} [∀ a, Fintype (Ω a)] [∀ a, DecidableEq (Ω a)]
    (δ : ℝ) (hδ : 0 ≤ δ) (hδ1 : δ ≤ 1) (p : ∀ a, FinProb (Ω a))
    (lab : ∀ a, Ω a → Fin g) (e : RowLabel R g) (t : Fin T) (o : Ω e.1) :
    (samplingEdgeClockLaw (T := T) δ hδ hδ1 p lab e).w (.tick t o) ≤
      δ * outputMarkMass (p e.1) (lab e.1) e.2 o := by
  have hr0 := labMarg_nonneg (p e.1) (lab e.1) e.2
  have hr1 := labMarg_le_one (p e.1) (lab e.1) e.2
  have hδr0 : 0 ≤ δ * labMarg (p e.1) (lab e.1) e.2 := mul_nonneg hδ hr0
  have hδr1 : δ * labMarg (p e.1) (lab e.1) e.2 ≤ 1 := by
    calc
      δ * labMarg (p e.1) (lab e.1) e.2 ≤ δ * 1 := mul_le_mul_of_nonneg_left hr1 hδ
      _ ≤ 1 := by simpa only [mul_one] using hδ1
  have hbase0 : 0 ≤ 1 - δ * labMarg (p e.1) (lab e.1) e.2 := sub_nonneg.mpr hδr1
  have hbase1 : 1 - δ * labMarg (p e.1) (lab e.1) e.2 ≤ 1 := by linarith
  have hsurv : survival δ (labMarg (p e.1) (lab e.1) e.2) t.val ≤ 1 := by
    exact pow_le_one₀ hbase0 hbase1
  have hmark : 0 ≤ outputMarkMass (p e.1) (lab e.1) e.2 o := by
    unfold outputMarkMass
    split_ifs
    · exact (p e.1).nonneg o
    · exact le_rfl
  simpa [samplingEdgeClockLaw, outputEdgeClockLaw, markedClockLaw, markedClockWeight] using
    (calc
      survival δ (labMarg (p e.1) (lab e.1) e.2) t.val * δ *
          outputMarkMass (p e.1) (lab e.1) e.2 o ≤
        1 * δ * outputMarkMass (p e.1) (lab e.1) e.2 o := by
          exact mul_le_mul_of_nonneg_right
            (mul_le_mul_of_nonneg_right hsurv hδ) hmark
      _ = δ * outputMarkMass (p e.1) (lab e.1) e.2 o := by ring)

private theorem pathWeight_le_markProduct {T : ℕ} {R : Type*} [Fintype R] [DecidableEq R]
    {g : ℕ} {Ω : R → Type*} [∀ a, Fintype (Ω a)] [∀ a, DecidableEq (Ω a)]
    (δ : ℝ) (hδ : 0 ≤ δ) (hδ1 : δ ≤ 1) (p : ∀ a, FinProb (Ω a))
    (lab : ∀ a, Ω a → Fin g) {j : ℕ} (π : Fin j → ClockCandidate T R g Ω) :
    pathWeight (samplingEdgeClockLaw (T := T) δ hδ hδ1 p lab) π ≤
      δ ^ j * ∏ i, outputMarkMass (p (π i).1) (lab (π i).1) (π i).2.1 (π i).2.2.2 := by
  classical
  rw [pathWeight]
  calc
    (∏ i, (samplingEdgeClockLaw (T := T) δ hδ hδ1 p lab
        ((π i).1, (π i).2.1)).w
        (MeshClockValue.tick (π i).2.2.1 (π i).2.2.2)) ≤
        ∏ i, δ * outputMarkMass (p (π i).1) (lab (π i).1) (π i).2.1 (π i).2.2.2 := by
          apply Finset.prod_le_prod₀
          · intro i hi
            exact (samplingEdgeClockLaw (T := T) δ hδ hδ1 p lab
              ((π i).1, (π i).2.1)).nonneg _
          · intro i hi
            exact samplingTickWeight_le_mark δ hδ hδ1 p lab
              ((π i).1, (π i).2.1) (π i).2.2.1 (π i).2.2.2
    _ = δ ^ j * ∏ i, outputMarkMass (p (π i).1) (lab (π i).1) (π i).2.1 (π i).2.2.2 := by
          rw [Finset.prod_mul_distrib]
          simp

private theorem samplingFirstArrivalMass_le {T : ℕ} {R : Type*} {g : ℕ}
    {Ω : R → Type*} [∀ a, Fintype (Ω a)] [∀ a, DecidableEq (Ω a)]
    (δ : ℝ) (hδ : 0 ≤ δ) (hδ1 : δ ≤ 1) (p : ∀ a, FinProb (Ω a))
    (lab : ∀ a, Ω a → Fin g) (r : R) (y : Fin g) :
    (∑ t : Fin T, ∑ o : Ω r,
      (samplingEdgeClockLaw (T := T) δ hδ hδ1 p lab (r, y)).w (.tick t o)) ≤
      (T : ℝ) * δ * labMarg (p r) (lab r) y := by
  classical
  calc
    (∑ t : Fin T, ∑ o : Ω r,
      (samplingEdgeClockLaw (T := T) δ hδ hδ1 p lab (r, y)).w (.tick t o)) ≤
        ∑ t : Fin T, ∑ o : Ω r, δ * outputMarkMass (p r) (lab r) y o := by
          apply Finset.sum_le_sum
          intro t ht
          apply Finset.sum_le_sum
          intro o ho
          exact samplingTickWeight_le_mark δ hδ hδ1 p lab (r, y) t o
    _ = (T : ℝ) * δ * labMarg (p r) (lab r) y := by
          calc
            (∑ t : Fin T, ∑ o : Ω r, δ * outputMarkMass (p r) (lab r) y o) =
                ∑ t : Fin T, δ * ∑ o : Ω r, outputMarkMass (p r) (lab r) y o := by
                  apply Finset.sum_congr rfl
                  intro t ht
                  rw [← Finset.mul_sum]
            _ = ∑ _t : Fin T, δ * labMarg (p r) (lab r) y := by
                  simp [outputMarkMass_sum]
            _ = (Fintype.card (Fin T) : ℝ) * (δ * labMarg (p r) (lab r) y) := by
                  simp [Finset.sum_const, nsmul_eq_mul]
            _ = (T : ℝ) * δ * labMarg (p r) (lab r) y := by simp [mul_assoc]

private theorem pathWeight_cons {T : ℕ} {R : Type*} {g : ℕ} {Ω : R → Type*}
    [∀ a, Fintype (Ω a)] {n : ℕ}
    (edgeLaw : ∀ e : RowLabel R g, FinProb (MeshClockValue T (Ω e.1)))
    (c : ClockCandidate T R g Ω) (β : Fin n → ClockCandidate T R g Ω) :
    pathWeight edgeLaw (Fin.cons c β) =
      (edgeLaw (c.1, c.2.1)).w (.tick c.2.2.1 c.2.2.2) * pathWeight edgeLaw β := by
  classical
  simp [pathWeight, Fin.prod_univ_succ, Fin.cons]

private def candidateSeqEquiv {T : ℕ} {R : Type*} {g : ℕ} {Ω : R → Type*} {j : ℕ} :
    (Fin j → ClockCandidate T R g Ω) ≃
      Σ e : Fin j → RowLabel R g, (Fin j → Fin T) × (∀ i, Ω (e i).1) where
  toFun π := Sigma.mk (fun i => Prod.mk (π i).1 (π i).2.1)
    (Prod.mk (fun i => (π i).2.2.1) (fun i => (π i).2.2.2))
  invFun d := fun i => Sigma.mk (d.1 i).1
    (Prod.mk (d.1 i).2 (Prod.mk (d.2.1 i) (d.2.2 i)))
  left_inv π := by
    funext i
    cases h : π i with
    | mk a rest =>
        cases rest with
        | mk y rest =>
          cases rest with
          | mk t o =>
            dsimp
            rw [h]
  right_inv d := by
    rcases d with ⟨e, t, o⟩
    rfl

private theorem outputMarkProduct_sum {R : Type*} {g : ℕ} {Ω : R → Type*}
    [∀ a, Fintype (Ω a)] {j : ℕ} (p : ∀ a, FinProb (Ω a))
    (lab : ∀ a, Ω a → Fin g) (e : Fin j → RowLabel R g) :
    (∑ o : ∀ i, Ω (e i).1,
      ∏ i, outputMarkMass (p (e i).1) (lab (e i).1) (e i).2 (o i)) =
      ∏ i, labMarg (p (e i).1) (lab (e i).1) (e i).2 := by
  classical
  rw [← Fintype.prod_sum]
  apply Finset.prod_congr rfl
  intro i hi
  exact outputMarkMass_sum (p (e i).1) (lab (e i).1) (e i).2

private noncomputable def terminalWalkMass {m : ℕ} {R : Type*} [Fintype R] {g : ℕ}
    (rate : R → Fin g → ℝ) (v : Endpoint R g) : ℝ := by
  classical
  exact ∑ w : Fin (m + 1) → Endpoint R g,
    if w (Fin.last m) = v then walkRate rate w else 0

private theorem terminalWalkMass_succ {k : ℕ} {R : Type*} [Fintype R] {g : ℕ}
    (rate : R → Fin g → ℝ) (v : Endpoint R g) :
    terminalWalkMass (m := k + 1) rate v =
      ∑ u : Endpoint R g, transitionRate rate u v * terminalWalkMass (m := k) rate u := by
  classical
  let e : Endpoint R g × (Fin (k + 1) → Endpoint R g) ≃
      (Fin (k + 2) → Endpoint R g) :=
    Fin.snocEquiv (fun _ : Fin (k + 2) => Endpoint R g)
  have hrate (u : Endpoint R g) (w : Fin (k + 1) → Endpoint R g) :
      walkRate rate (e (u, w)) =
        walkRate rate w * transitionRate rate (w (Fin.last k)) u := by
    let snoc : Fin (k + 2) → Endpoint R g :=
      Fin.snoc (α := fun _ : Fin (k + 2) => Endpoint R g) w u
    change (∏ i : Fin (k + 1),
        transitionRate rate (snoc i.castSucc) (snoc i.succ)) =
      (∏ i : Fin k, transitionRate rate (w i.castSucc) (w i.succ)) *
        transitionRate rate (w (Fin.last k)) u
    rw [Fin.prod_univ_castSucc]
    simp only [snoc, Fin.snoc_castSucc, ← Fin.castSucc_succ]
    have hlast : (Fin.last k).succ = Fin.last (k + 1) := by
      apply Fin.ext
      simp
    rw [hlast, Fin.snoc_last]
  calc
      terminalWalkMass (m := k + 1) rate v =
        ∑ x : Endpoint R g × (Fin (k + 1) → Endpoint R g),
          if x.1 = v then walkRate rate (e x) else 0 := by
            unfold terminalWalkMass
            symm
            exact Fintype.sum_equiv e
              (fun x => if x.1 = v then walkRate rate (e x) else 0)
              (fun w => if w (Fin.last (k + 1)) = v then walkRate rate w else 0)
              (by intro x; simp [e, Fin.snocEquiv, Fin.snoc_last])
    _ = ∑ w : Fin (k + 1) → Endpoint R g,
          walkRate rate w * transitionRate rate (w (Fin.last k)) v := by
            simp_rw [Fintype.sum_prod_type]
            simp_rw [hrate]
            simp
    _ = ∑ u : Endpoint R g,
          transitionRate rate u v * terminalWalkMass (m := k) rate u := by
            unfold terminalWalkMass
            calc
              (∑ w : Fin (k + 1) → Endpoint R g,
                walkRate rate w * transitionRate rate (w (Fin.last k)) v) =
                  ∑ w : Fin (k + 1) → Endpoint R g, ∑ u : Endpoint R g,
                    if w (Fin.last k) = u then transitionRate rate u v * walkRate rate w else 0 := by
                      apply Finset.sum_congr rfl
                      intro w hw
                      simp [eq_comm]
                      ring
              _ = ∑ u : Endpoint R g, ∑ w : Fin (k + 1) → Endpoint R g,
                    if w (Fin.last k) = u then transitionRate rate u v * walkRate rate w else 0 := by
                      rw [Finset.sum_comm]
              _ = ∑ u : Endpoint R g, transitionRate rate u v *
                    ∑ w : Fin (k + 1) → Endpoint R g,
                      if w (Fin.last k) = u then walkRate rate w else 0 := by
                      apply Finset.sum_congr rfl
                      intro u hu
                      rw [Finset.mul_sum]
                      apply Finset.sum_congr rfl
                      intro w hw
                      by_cases heq : w (Fin.last k) = u <;> simp [heq, mul_comm]

private theorem terminalWalkMass_bound {R : Type*} [Fintype R] {g : ℕ}
    (rate : R → Fin g → ℝ) (θ : ℝ)
    (hr0 : ∀ a y, 0 ≤ rate a y) (hrow : ∀ a, ∑ y, rate a y = 1)
    (hcol : ∀ y, ∑ a, rate a y = θ) (hθ0 : 0 ≤ θ) (hθ1 : θ ≤ 1) :
    ∀ (m : ℕ) (v : Endpoint R g), terminalWalkMass (m := m) rate v ≤ θ ^ (m / 2) := by
  classical
  have hzero (u : Endpoint R g) : terminalWalkMass (m := 0) rate u = 1 := by
    classical
    have hcard : Fintype.card {w : Fin 1 → Endpoint R g // w 0 = u} = 1 := by
      apply Fintype.card_eq_one_iff.mpr
      refine ⟨⟨(fun _ => u), rfl⟩, ?_⟩
      intro w
      apply Subtype.ext
      funext i
      have hi : i = 0 := Subsingleton.elim i 0
      subst i
      exact w.2
    have hsum :
        (∑ w : Fin 1 → Endpoint R g, if w 0 = u then 1 else 0) =
          Fintype.card {w : Fin 1 → Endpoint R g // w 0 = u} := by
      rw [Fintype.card_subtype]
      simp [Finset.sum_filter]
    simpa [terminalWalkMass, walkRate, Fin.last] using hsum.trans (by rw [hcard])
  have hbounds (k : ℕ) :
      (∀ a : R, terminalWalkMass (m := k) rate (Sum.inl a) ≤ θ ^ (k / 2)) ∧
      (∀ y : Fin g, terminalWalkMass (m := k) rate (Sum.inr y) ≤ θ ^ ((k + 1) / 2)) := by
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
          rw [terminalWalkMass_succ]
          calc
            (∑ u : Endpoint R g, transitionRate rate u (Sum.inl a) *
              terminalWalkMass (m := k) rate u) =
                ∑ y : Fin g, rate a y * terminalWalkMass (m := k) rate (Sum.inr y) := by
                  simp [transitionRate, Fintype.sum_sum_type]
            _ ≤ ∑ y : Fin g, rate a y * θ ^ ((k + 1) / 2) := by
                  apply Finset.sum_le_sum
                  intro y hy
                  exact mul_le_mul_of_nonneg_left (ih.2 y) (hr0 a y)
            _ = (∑ y : Fin g, rate a y) * θ ^ ((k + 1) / 2) := by rw [Finset.sum_mul]
            _ = θ ^ ((k + 1) / 2) := by rw [hrow a]; simp
        · intro y
          rw [terminalWalkMass_succ]
          calc
            (∑ u : Endpoint R g, transitionRate rate u (Sum.inr y) *
              terminalWalkMass (m := k) rate u) =
                ∑ a : R, rate a y * terminalWalkMass (m := k) rate (Sum.inl a) := by
                  simp [transitionRate, Fintype.sum_sum_type]
            _ ≤ ∑ a : R, rate a y * θ ^ (k / 2) := by
                  apply Finset.sum_le_sum
                  intro a ha
                  exact mul_le_mul_of_nonneg_left (ih.1 a) (hr0 a y)
            _ = (∑ a : R, rate a y) * θ ^ (k / 2) := by rw [Finset.sum_mul]
            _ = θ * θ ^ (k / 2) := by rw [hcol y]
            _ = θ ^ (k / 2 + 1) := by rw [pow_succ]; ring
            _ = θ ^ ((k + 2) / 2) := by congr 1 <;> omega
  intro m v
  rcases v with a | y
  · exact (hbounds m).1 a
  · exact le_trans ((hbounds m).2 y)
      (pow_le_pow_of_le_one hθ0 hθ1 (by omega))

private def walkStepEdge {R : Type*} {g : ℕ} (u v : Endpoint R g)
    (e : RowLabel R g) : Prop :=
  (u = Sum.inl e.1 ∧ v = Sum.inr e.2) ∨ (u = Sum.inr e.2 ∧ v = Sum.inl e.1)

private theorem walkStepEdge_unique {R : Type*} {g : ℕ} {u v : Endpoint R g}
    {e e' : RowLabel R g} (he : walkStepEdge u v e) (he' : walkStepEdge u v e') : e = e' := by
  rcases he with ⟨hu, hv⟩ | ⟨hu, hv⟩ <;>
    rcases he' with ⟨hu', hv'⟩ | ⟨hu', hv'⟩
  · exact Prod.ext (Sum.inl.inj (hu.symm.trans hu')) (Sum.inr.inj (hv.symm.trans hv'))
  · cases hu.symm.trans hu'
  · cases hu.symm.trans hu'
  · exact Prod.ext (Sum.inl.inj (hv.symm.trans hv')) (Sum.inr.inj (hu.symm.trans hu'))

private theorem transitionRate_eq_of_walkStep {R : Type*} {g : ℕ}
    (rate : R → Fin g → ℝ) {u v : Endpoint R g} {e : RowLabel R g}
    (h : walkStepEdge u v e) : transitionRate rate u v = rate e.1 e.2 := by
  rcases h with ⟨hu, hv⟩ | ⟨hu, hv⟩
  · simp [transitionRate, hu, hv]
  · simp [transitionRate, hu, hv]

private theorem transitionRate_eq_zero_of_no_walkStep {R : Type*} {g : ℕ}
    (rate : R → Fin g → ℝ) {u v : Endpoint R g}
    (h : ¬ ∃ e : RowLabel R g, walkStepEdge u v e) : transitionRate rate u v = 0 := by
  cases u with
  | inl a =>
    cases v with
    | inl b => simp [transitionRate]
    | inr y => exact (h ⟨(a, y), by simp [walkStepEdge]⟩).elim
  | inr y =>
    cases v with
    | inl a => exact (h ⟨(a, y), by simp [walkStepEdge]⟩).elim
    | inr z => simp [transitionRate]

private theorem walkEdgeSeqRate_sum {m : ℕ} {R : Type*} [Fintype R] {g : ℕ}
    (rate : R → Fin g → ℝ) (w : Fin (m + 1) → Endpoint R g)
    [DecidablePred (fun e : Fin m → RowLabel R g =>
      ∀ i : Fin m, walkStepEdge (w i.castSucc) (w i.succ) (e i))]
    [Decidable (∀ i : Fin m, ∃ e : RowLabel R g, walkStepEdge (w i.castSucc) (w i.succ) e)] :
    (∑ e : Fin m → RowLabel R g,
      if ∀ i : Fin m, walkStepEdge (w i.castSucc) (w i.succ) (e i) then
        ∏ i, rate (e i).1 (e i).2 else 0) = walkRate rate w := by
  classical
  let edgeOK : (Fin m → RowLabel R g) → Prop := fun e =>
    ∀ i : Fin m, walkStepEdge (w i.castSucc) (w i.succ) (e i)
  letI : DecidablePred edgeOK := inferInstance
  by_cases hvalid : ∀ i : Fin m, ∃ e : RowLabel R g, walkStepEdge (w i.castSucc) (w i.succ) e
  · let edge₀ : Fin m → RowLabel R g := fun i => Classical.choose (hvalid i)
    have hedge₀ (i : Fin m) : walkStepEdge (w i.castSucc) (w i.succ) (edge₀ i) :=
      Classical.choose_spec (hvalid i)
    let E : Finset (Fin m → RowLabel R g) := Finset.univ.filter edgeOK
    let EdgeIndex := {e : Fin m → RowLabel R g // e ∈ E}
    letI : Fintype EdgeIndex := Finset.Subtype.fintype E
    have he₀ : edge₀ ∈ E := by simp [E, edgeOK, hedge₀]
    have hsum :
        (∑ e : EdgeIndex, ∏ i, rate (e.1 i).1 (e.1 i).2) =
          ∏ i, rate (edge₀ i).1 (edge₀ i).2 := by
      rw [Fintype.sum_eq_single ⟨edge₀, he₀⟩ (by
        intro e hne
        have hedge (i : Fin m) : walkStepEdge (w i.castSucc) (w i.succ) (e.1 i) :=
          (Finset.mem_filter.mp e.2).2 i
        have heq : e.1 = edge₀ := by
          funext i
          exact walkStepEdge_unique (hedge i) (hedge₀ i)
        exact (hne (Subtype.ext heq)).elim)]
    calc
      (∑ e : Fin m → RowLabel R g,
        if edgeOK e then ∏ i, rate (e i).1 (e i).2 else 0) =
          ∑ e ∈ E, ∏ i, rate (e i).1 (e i).2 := by
            rw [Finset.sum_filter]
      _ = ∑ e : EdgeIndex, ∏ i, rate (e.1 i).1 (e.1 i).2 := by
            rw [Finset.univ_eq_attach]
            exact (Finset.sum_attach E (fun e => ∏ i, rate (e i).1 (e i).2)).symm
      _ = ∏ i, rate (edge₀ i).1 (edge₀ i).2 := hsum
      _ = walkRate rate w := by
            unfold walkRate
            apply Finset.prod_congr rfl
            intro i hi
            exact (transitionRate_eq_of_walkStep rate (hedge₀ i)).symm
  · have hno (e : Fin m → RowLabel R g) : ¬ edgeOK e := by
      intro he
      exact hvalid (fun i => ⟨e i, he i⟩)
    have hwalkZero : walkRate rate w = 0 := by
      have hbad : ∃ i : Fin m, ¬ ∃ e : RowLabel R g,
          walkStepEdge (w i.castSucc) (w i.succ) e := by
        push_neg at hvalid
        rcases hvalid with ⟨i, hbadI⟩
        refine ⟨i, ?_⟩
        rintro ⟨e, he⟩
        exact hbadI e he
      obtain ⟨i, hi⟩ := hbad
      unfold walkRate
      exact Finset.prod_eq_zero (Finset.mem_univ i)
        (transitionRate_eq_zero_of_no_walkStep rate hi)
    simp [hno, hvalid, edgeOK, hwalkZero]

theorem decPath_weight_sum {T : ℕ} {R : Type*} [Fintype R] [DecidableEq R] {g : ℕ}
    {Ω : R → Type*} [∀ a, Fintype (Ω a)] [∀ a, DecidableEq (Ω a)]
    (δ : ℝ) (hδ : 0 ≤ δ) (hδ1 : δ ≤ 1) (p : ∀ a, FinProb (Ω a)) (lab : ∀ a, Ω a → Fin g) (θ : ℝ)
    (hrow : ∀ a, ∑ y, labMarg (p a) (lab a) y = 1) (hcol : ∀ y, ∑ a, labMarg (p a) (lab a) y = θ)
    (hθ0 : 0 ≤ θ) (hθ1 : θ ≤ 1) (v : Endpoint R g) (j : ℕ) :
    ∑ r, ∑ π ∈ decPaths r v j, pathWeight (samplingEdgeClockLaw (T := T) δ hδ hδ1 p lab) π ≤
      θ ^ (j / 2) * (((T + j : ℕ) : ℝ) * δ) ^ j / (j.factorial : ℝ) := by
  classical
  let PathIndex :=
    Σ r : Endpoint R g, {π : Fin j → ClockCandidate T R g Ω // π ∈ decPaths r v j}
  let WalkBase := (Fin (j + 1) → Endpoint R g) ×
    (Σ e : Fin j → RowLabel R g, (Fin j → Fin T) × (∀ i, Ω (e i).1))
  let WalkPredicate : WalkBase → Prop := fun q =>
    q.1 (Fin.last j) = v ∧
      (∀ i : Fin j, walkStepEdge (q.1 i.castSucc) (q.1 i.succ) (q.2.1 i)) ∧
      Antitone fun i => (q.2.2.1 i).val
  let WalkIndex := {q : WalkBase // q ∈ Finset.univ.filter WalkPredicate}
  letI : Fintype WalkIndex := Finset.Subtype.fintype (Finset.univ.filter WalkPredicate)
  let pathTerm (π : Fin j → ClockCandidate T R g Ω) : ℝ :=
    δ ^ j * ∏ i, outputMarkMass (p (π i).1) (lab (π i).1) (π i).2.1 (π i).2.2.2
  let pathDataTerm (d : Σ e : Fin j → RowLabel R g,
      (Fin j → Fin T) × (∀ i, Ω (e i).1)) : ℝ :=
    δ ^ j * ∏ i, outputMarkMass (p (d.1 i).1) (lab (d.1 i).1) (d.1 i).2 (d.2.2 i)
  have hπattach (r : Endpoint R g) :
      (∑ π : {π : Fin j → ClockCandidate T R g Ω // π ∈ decPaths r v j},
          pathWeight (samplingEdgeClockLaw (T := T) δ hδ hδ1 p lab) π.1) =
        ∑ π ∈ decPaths r v j,
          pathWeight (samplingEdgeClockLaw (T := T) δ hδ hδ1 p lab) π := by
    rw [Finset.univ_eq_attach]
    exact Finset.sum_attach (decPaths r v j) _
  have hsource :
      (∑ r, ∑ π ∈ decPaths r v j,
        pathWeight (samplingEdgeClockLaw (T := T) δ hδ hδ1 p lab) π) =
        ∑ q : PathIndex, pathWeight (samplingEdgeClockLaw (T := T) δ hδ hδ1 p lab) q.2.1 := by
    calc
      (∑ r, ∑ π ∈ decPaths r v j,
          pathWeight (samplingEdgeClockLaw (T := T) δ hδ hδ1 p lab) π) =
          ∑ r, ∑ π : {π : Fin j → ClockCandidate T R g Ω // π ∈ decPaths r v j},
            pathWeight (samplingEdgeClockLaw (T := T) δ hδ hδ1 p lab) π.1 := by
              apply Finset.sum_congr rfl
              intro r hr
              exact (hπattach r).symm
      _ = ∑ q : PathIndex, pathWeight (samplingEdgeClockLaw (T := T) δ hδ hδ1 p lab) q.2.1 := by
            change (∑ r, ∑ π : {π : Fin j → ClockCandidate T R g Ω // π ∈ decPaths r v j},
              pathWeight (samplingEdgeClockLaw (T := T) δ hδ hδ1 p lab) π.1) = _
            rw [← Fintype.sum_sigma']
  have hdec (q : PathIndex) : IsDecPath q.1 v q.2.1 := by
    have hm := q.2.2
    change q.2.1 ∈ Finset.univ.filter (fun π => IsDecPath q.1 v π) at hm
    exact (Finset.mem_filter.mp hm).2
  let selectedWalk (q : PathIndex) : Fin (j + 1) → Endpoint R g :=
    Classical.choose (hdec q)
  have hselected (q : PathIndex) :
      selectedWalk q 0 = q.1 ∧ selectedWalk q (Fin.last j) = v ∧
      (∀ i : Fin j,
        (selectedWalk q i.castSucc = Sum.inl (q.2.1 i).1 ∧
          selectedWalk q i.succ = Sum.inr (q.2.1 i).2.1) ∨
        (selectedWalk q i.castSucc = Sum.inr (q.2.1 i).2.1 ∧
          selectedWalk q i.succ = Sum.inl (q.2.1 i).1)) ∧
      (∀ i : Fin j, eventPriority (q.2.1 i) < rootHorizon T R g) ∧
      (∀ i i' : Fin j, i < i' → eventPriority (q.2.1 i') < eventPriority (q.2.1 i)) := by
    exact Classical.choose_spec (hdec q)
  let toWalk (q : PathIndex) : WalkIndex := by
    refine ⟨(selectedWalk q, candidateSeqEquiv q.2.1), ?_⟩
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    rcases hselected q with ⟨_, hlast, hedges, _, hstrict⟩
    refine ⟨hlast, ?_, ?_⟩
    · simpa [candidateSeqEquiv, walkStepEdge] using hedges
    · simpa [candidateSeqEquiv] using pathCandidateTicks_antitone q.2.1 hstrict
  have htoWalk : Function.Injective toWalk := by
    intro q q' h
    rcases q with ⟨r, π⟩
    rcases q' with ⟨r', π'⟩
    have hpair : (selectedWalk ⟨r, π⟩, candidateSeqEquiv π.1) =
        (selectedWalk ⟨r', π'⟩, candidateSeqEquiv π'.1) :=
      congrArg Subtype.val h
    have hwalk : selectedWalk ⟨r, π⟩ = selectedWalk ⟨r', π'⟩ := congrArg Prod.fst hpair
    have hπ : π.1 = π'.1 := candidateSeqEquiv.injective (congrArg Prod.snd hpair)
    have hroot : r = r' := by
      calc
        r = selectedWalk ⟨r, π⟩ 0 := (hselected ⟨r, π⟩).1.symm
        _ = selectedWalk ⟨r', π'⟩ 0 := by rw [hwalk]
        _ = r' := (hselected ⟨r', π'⟩).1
    cases hroot
    have hπ' : π = π' := Subtype.ext hπ
    cases hπ'
    rfl
  have hmapSum :
      (∑ q : PathIndex, pathWeight (samplingEdgeClockLaw (T := T) δ hδ hδ1 p lab) q.2.1) ≤
        ∑ q : WalkIndex, pathDataTerm q.1.2 := by
    calc
      (∑ q : PathIndex, pathWeight (samplingEdgeClockLaw (T := T) δ hδ hδ1 p lab) q.2.1) ≤
          ∑ q : PathIndex, pathTerm (q.2.1) := by
            apply Finset.sum_le_sum
            intro q hq
            exact pathWeight_le_markProduct δ hδ hδ1 p lab q.2.1
      _ = ∑ q ∈ (Finset.univ.image toWalk), pathDataTerm q.1.2 := by
            symm
            rw [Finset.sum_image htoWalk.injOn]
            simp [toWalk, pathTerm, pathDataTerm, candidateSeqEquiv]
      _ ≤ ∑ q : WalkIndex, pathDataTerm q.1.2 := by
            apply Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _)
            intro q hq hqnot
            dsimp [pathDataTerm]
            apply mul_nonneg (pow_nonneg hδ j)
            exact Finset.prod_nonneg fun i hi => by
              unfold outputMarkMass
              split_ifs
              · exact (p (((q.1.2).1 i).1)).nonneg _
              · exact le_rfl
  have hExpand :
      (∑ q : WalkIndex, pathDataTerm q.1.2) =
        ∑ w : Fin (j + 1) → Endpoint R g,
          ∑ e : Fin j → RowLabel R g,
            ∑ t : Fin j → Fin T,
              ∑ o : (∀ i, Ω (e i).1),
                if w (Fin.last j) = v ∧
                    (∀ i : Fin j, walkStepEdge (w i.castSucc) (w i.succ) (e i)) ∧
                    Antitone fun i => (t i).val then
                  δ ^ j * ∏ i, outputMarkMass (p (e i).1) (lab (e i).1) (e i).2 (o i)
                else 0 := by
    classical
    let f : WalkBase → ℝ := fun z => pathDataTerm z.2
    calc
      (∑ q : WalkIndex, pathDataTerm q.1.2) =
          ∑ z : WalkBase, if WalkPredicate z then f z else 0 := by
            change (∑ z : {z : WalkBase // z ∈ Finset.univ.filter WalkPredicate}, f z.1) = _
            rw [Finset.univ_eq_attach]
            calc
              (∑ z ∈ (Finset.univ.filter WalkPredicate).attach, f z.1) =
                  ∑ z ∈ Finset.univ.filter WalkPredicate, f z :=
                    Finset.sum_attach (Finset.univ.filter WalkPredicate) f
              _ = ∑ z : WalkBase, if WalkPredicate z then f z else 0 := by
                    rw [Finset.sum_filter]
      _ = ∑ w : Fin (j + 1) → Endpoint R g,
          ∑ e : Fin j → RowLabel R g,
            ∑ t : Fin j → Fin T,
              ∑ o : (∀ i, Ω (e i).1),
                if w (Fin.last j) = v ∧
                    (∀ i : Fin j, walkStepEdge (w i.castSucc) (w i.succ) (e i)) ∧
                    Antitone fun i => (t i).val then
                  δ ^ j * ∏ i, outputMarkMass (p (e i).1) (lab (e i).1) (e i).2 (o i)
                else 0 := by
            rw [Fintype.sum_prod_type]
            change (∑ w : Fin (j + 1) → Endpoint R g,
              ∑ d : Σ e : Fin j → RowLabel R g,
                (Fin j → Fin T) × (∀ i, Ω (e i).1),
                if WalkPredicate (w, d) then f (w, d) else 0) = _
            apply Finset.sum_congr rfl
            intro w hw
            let H : (e : Fin j → RowLabel R g) →
                ((Fin j → Fin T) × (∀ i, Ω (e i).1)) → ℝ := fun e tm =>
                  if WalkPredicate (w, ⟨e, tm⟩) then f (w, ⟨e, tm⟩) else 0
            change (∑ d : Σ e : Fin j → RowLabel R g,
              (Fin j → Fin T) × (∀ i, Ω (e i).1), H d.1 d.2) = _
            rw [Fintype.sum_sigma']
            apply Finset.sum_congr rfl
            intro e he
            let G : (Fin j → Fin T) → (∀ i, Ω (e i).1) → ℝ := fun t o => H e (t, o)
            change (∑ tm : (Fin j → Fin T) × (∀ i, Ω (e i).1), G tm.1 tm.2) = _
            exact Fintype.sum_prod_type' G
  let rate : R → Fin g → ℝ := fun a y => labMarg (p a) (lab a) y
  have hmarks :
      (∑ w : Fin (j + 1) → Endpoint R g,
        ∑ e : Fin j → RowLabel R g,
          ∑ t : Fin j → Fin T,
            ∑ o : (∀ i, Ω (e i).1),
              if w (Fin.last j) = v ∧
                  (∀ i : Fin j, walkStepEdge (w i.castSucc) (w i.succ) (e i)) ∧
                  Antitone fun i => (t i).val then
                δ ^ j * ∏ i, outputMarkMass (p (e i).1) (lab (e i).1) (e i).2 (o i)
              else 0) =
        ∑ w : Fin (j + 1) → Endpoint R g,
          ∑ e : Fin j → RowLabel R g,
            ∑ t : Fin j → Fin T,
              if w (Fin.last j) = v ∧
                  (∀ i : Fin j, walkStepEdge (w i.castSucc) (w i.succ) (e i)) ∧
                  Antitone fun i => (t i).val then
                δ ^ j * ∏ i, rate (e i).1 (e i).2 else 0 := by
    apply Finset.sum_congr rfl
    intro w hw
    apply Finset.sum_congr rfl
    intro e he
    apply Finset.sum_congr rfl
    intro t ht
    by_cases h : w (Fin.last j) = v ∧
        (∀ i : Fin j, walkStepEdge (w i.castSucc) (w i.succ) (e i)) ∧
        Antitone fun i => (t i).val
    · simp only [if_pos h]
      rw [← Finset.mul_sum, outputMarkProduct_sum]
    · simp [h]
  let tickPredicate : (Fin j → Fin T) → Prop := fun t => Antitone fun i => (t i).val
  let TickIndex := {t : Fin j → Fin T // tickPredicate t}
  letI : Fintype TickIndex :=
    Fintype.subtype (Finset.univ.filter tickPredicate) (by intro t; simp)
  have hTickCard : Fintype.card TickIndex = (Finset.univ.filter tickPredicate).card := by
    simpa [TickIndex] using (Fintype.card_subtype tickPredicate)
  have hTickCount : (Fintype.card TickIndex : ℝ) ≤
      ((T + j : ℕ) : ℝ) ^ j / (j.factorial : ℝ) := by
    simpa [TickIndex, tickPredicate] using antitoneTickCount_le T j
  have htimeEq (w : Fin (j + 1) → Endpoint R g) (e : Fin j → RowLabel R g) :
      (∑ t : Fin j → Fin T,
        if w (Fin.last j) = v ∧
            (∀ i : Fin j, walkStepEdge (w i.castSucc) (w i.succ) (e i)) ∧ tickPredicate t then
          δ ^ j * ∏ i, rate (e i).1 (e i).2 else 0) =
        if w (Fin.last j) = v ∧
            (∀ i : Fin j, walkStepEdge (w i.castSucc) (w i.succ) (e i)) then
          (Fintype.card TickIndex : ℝ) *
            (δ ^ j * ∏ i, rate (e i).1 (e i).2) else 0 := by
    by_cases hbase : w (Fin.last j) = v ∧
        (∀ i : Fin j, walkStepEdge (w i.castSucc) (w i.succ) (e i))
    · simp [hbase, and_assoc]
      calc
        (∑ t : Fin j → Fin T, if tickPredicate t then
          δ ^ j * ∏ i, rate (e i).1 (e i).2 else 0) =
            ∑ t ∈ Finset.univ.filter tickPredicate,
              δ ^ j * ∏ i, rate (e i).1 (e i).2 := by
              rw [← Finset.sum_filter]
        _ = (Fintype.card TickIndex : ℝ) *
              (δ ^ j * ∏ i, rate (e i).1 (e i).2) := by
              rw [Finset.sum_const]
              simp [nsmul_eq_mul, hTickCard]
    · have hfalse (t : Fin j → Fin T) :
          ¬ (w (Fin.last j) = v ∧
            (∀ i : Fin j, walkStepEdge (w i.castSucc) (w i.succ) (e i)) ∧ tickPredicate t) := by
        intro h
        exact hbase ⟨h.1, h.2.1⟩
      simp [hbase, hfalse]
  have htimeBound :
      (∑ w : Fin (j + 1) → Endpoint R g,
        ∑ e : Fin j → RowLabel R g,
          ∑ t : Fin j → Fin T,
            if w (Fin.last j) = v ∧
                (∀ i : Fin j, walkStepEdge (w i.castSucc) (w i.succ) (e i)) ∧ tickPredicate t then
              δ ^ j * ∏ i, rate (e i).1 (e i).2 else 0) ≤
        ∑ w : Fin (j + 1) → Endpoint R g,
          ∑ e : Fin j → RowLabel R g,
            if w (Fin.last j) = v ∧
                (∀ i : Fin j, walkStepEdge (w i.castSucc) (w i.succ) (e i)) then
              (Fintype.card TickIndex : ℝ) *
                (δ ^ j * ∏ i, rate (e i).1 (e i).2) else 0 := by
    apply Finset.sum_le_sum
    intro w hw
    apply Finset.sum_le_sum
    intro e he
    rw [htimeEq]
  have hEdgeAgg :
      (∑ w : Fin (j + 1) → Endpoint R g,
        ∑ e : Fin j → RowLabel R g,
          if w (Fin.last j) = v ∧
              (∀ i : Fin j, walkStepEdge (w i.castSucc) (w i.succ) (e i)) then
            (Fintype.card TickIndex : ℝ) *
              (δ ^ j * ∏ i, rate (e i).1 (e i).2) else 0) =
        (Fintype.card TickIndex : ℝ) * δ ^ j * terminalWalkMass (m := j) rate v := by
    calc
      (∑ w : Fin (j + 1) → Endpoint R g,
        ∑ e : Fin j → RowLabel R g,
          if w (Fin.last j) = v ∧
              (∀ i : Fin j, walkStepEdge (w i.castSucc) (w i.succ) (e i)) then
            (Fintype.card TickIndex : ℝ) *
              (δ ^ j * ∏ i, rate (e i).1 (e i).2) else 0) =
          ∑ w : Fin (j + 1) → Endpoint R g,
            if w (Fin.last j) = v then
              (Fintype.card TickIndex : ℝ) * δ ^ j *
                (∑ e : Fin j → RowLabel R g,
                  if ∀ i, walkStepEdge (w i.castSucc) (w i.succ) (e i) then
                    ∏ i, rate (e i).1 (e i).2 else 0) else 0 := by
              apply Finset.sum_congr rfl
              intro w hw
              by_cases hlast : w (Fin.last j) = v
              · simp [hlast]
                calc
                  (∑ e : Fin j → RowLabel R g,
                    if ∀ i, walkStepEdge (w i.castSucc) (w i.succ) (e i) then
                      (Fintype.card TickIndex : ℝ) *
                        (δ ^ j * ∏ i, rate (e i).1 (e i).2) else 0) =
                      ∑ e : Fin j → RowLabel R g,
                        (Fintype.card TickIndex : ℝ) * δ ^ j *
                          (if ∀ i, walkStepEdge (w i.castSucc) (w i.succ) (e i) then
                            ∏ i, rate (e i).1 (e i).2 else 0) := by
                              apply Finset.sum_congr rfl
                              intro e he
                              by_cases hedge : ∀ i, walkStepEdge (w i.castSucc) (w i.succ) (e i)
                              · simp [hedge]
                                ring
                              · simp [hedge]
                  _ = (Fintype.card TickIndex : ℝ) * δ ^ j *
                      ∑ e : Fin j → RowLabel R g,
                        if ∀ i, walkStepEdge (w i.castSucc) (w i.succ) (e i) then
                          ∏ i, rate (e i).1 (e i).2 else 0 := by
                            rw [Finset.mul_sum]
              · simp [hlast]
      _ = ∑ w : Fin (j + 1) → Endpoint R g,
            if w (Fin.last j) = v then
              (Fintype.card TickIndex : ℝ) * δ ^ j * walkRate rate w else 0 := by
              apply Finset.sum_congr rfl
              intro w hw
              by_cases hlast : w (Fin.last j) = v
              · simp [hlast, walkEdgeSeqRate_sum]
              · simp [hlast]
      _ = (Fintype.card TickIndex : ℝ) * δ ^ j * terminalWalkMass (m := j) rate v := by
              change (∑ w : Fin (j + 1) → Endpoint R g,
                if w (Fin.last j) = v then
                  (Fintype.card TickIndex : ℝ) * δ ^ j * walkRate rate w else 0) = _
              unfold terminalWalkMass
              rw [Finset.mul_sum]
              apply Finset.sum_congr rfl
              intro w hw
              by_cases hlast : w (Fin.last j) = v <;> simp [hlast, mul_assoc]
  have hpre :
      (∑ r, ∑ π ∈ decPaths r v j,
        pathWeight (samplingEdgeClockLaw (T := T) δ hδ hδ1 p lab) π) ≤
        (Fintype.card TickIndex : ℝ) * δ ^ j * terminalWalkMass (m := j) rate v := by
    calc
      (∑ r, ∑ π ∈ decPaths r v j,
        pathWeight (samplingEdgeClockLaw (T := T) δ hδ hδ1 p lab) π) =
          ∑ q : PathIndex, pathWeight (samplingEdgeClockLaw (T := T) δ hδ hδ1 p lab) q.2.1 := hsource
      _ ≤ ∑ q : WalkIndex, pathDataTerm q.1.2 := hmapSum
      _ = _ := hExpand
      _ = _ := hmarks
      _ ≤ _ := htimeBound
      _ = _ := hEdgeAgg
  have hrateNonneg : ∀ a y, 0 ≤ rate a y := by
    intro a y
    exact labMarg_nonneg (p a) (lab a) y
  have htransitionNonneg (u v : Endpoint R g) : 0 ≤ transitionRate rate u v := by
    cases u <;> cases v <;> simp [transitionRate, hrateNonneg]
  have hmassNonneg : 0 ≤ terminalWalkMass (m := j) rate v := by
    unfold terminalWalkMass
    apply Finset.sum_nonneg
    intro w hw
    by_cases hvw : w (Fin.last j) = v
    · simp only [if_pos hvw]
      exact Finset.prod_nonneg fun i hi => htransitionNonneg (w i.castSucc) (w i.succ)
    · simp [hvw]
  have hmassBound : terminalWalkMass (m := j) rate v ≤ θ ^ (j / 2) :=
    terminalWalkMass_bound rate θ hrateNonneg hrow hcol hθ0 hθ1 j v
  let A : ℝ := (((T + j : ℕ) : ℝ) ^ j) / (j.factorial : ℝ)
  have hA0 : 0 ≤ A := by positivity
  have hδpow : 0 ≤ δ ^ j := pow_nonneg hδ j
  calc
    (∑ r, ∑ π ∈ decPaths r v j,
        pathWeight (samplingEdgeClockLaw (T := T) δ hδ hδ1 p lab) π) ≤
        (Fintype.card TickIndex : ℝ) * δ ^ j * terminalWalkMass (m := j) rate v := hpre
    _ ≤ A * δ ^ j * θ ^ (j / 2) := by
        calc
          (Fintype.card TickIndex : ℝ) * δ ^ j * terminalWalkMass (m := j) rate v =
              (Fintype.card TickIndex : ℝ) * (δ ^ j * terminalWalkMass (m := j) rate v) := by ring
          _ ≤ A * (δ ^ j * terminalWalkMass rate v) :=
            mul_le_mul_of_nonneg_right hTickCount (mul_nonneg hδpow hmassNonneg)
          _ = A * δ ^ j * terminalWalkMass (m := j) rate v := by ring
          _ ≤ A * δ ^ j * θ ^ (j / 2) :=
            mul_le_mul_of_nonneg_left hmassBound (mul_nonneg hA0 hδpow)
    _ = θ ^ (j / 2) * (((T + j : ℕ) : ℝ) * δ) ^ j / (j.factorial : ℝ) := by
        dsimp [A]
        rw [mul_pow]
        ring

set_option maxHeartbeats 1000000 in
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
  classical
  let edgeLaw := samplingEdgeClockLaw (T := T) δ hδ hδ1 p lab
  let allRootWeight (r : R) : ℝ :=
    ∑ π ∈ decPaths (Sum.inl r) v j, pathWeight edgeLaw π
  let badRootWeight (k : K) (r : R) : ℝ :=
    ∑ π ∈ (decPaths (Sum.inl r) v j).filter (fun π => pathMeetsOtherRow π (scope k) r),
      pathWeight edgeLaw π
  have hpathWeight_nonneg (π : Fin j → ClockCandidate T R g Ω) :
      0 ≤ pathWeight edgeLaw π := by
    unfold pathWeight
    exact Finset.prod_nonneg fun i hi =>
      (edgeLaw ((π i).1, (π i).2.1)).nonneg _
  have hweightNonneg (r : R) : 0 ≤ allRootWeight r := by
    unfold allRootWeight pathWeight
    apply Finset.sum_nonneg
    intro π hπ
    exact hpathWeight_nonneg π
  have hbadLe (k : K) (r : R) : badRootWeight k r ≤ allRootWeight r := by
    unfold badRootWeight allRootWeight
    apply Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
    intro π hπ hπnot
    exact hpathWeight_nonneg π
  have hscopeIndicator (k : K) :
      (∑ r ∈ scope k, badRootWeight k r) =
        ∑ r : R, if r ∈ scope k then badRootWeight k r else 0 := by
    let P : R → Prop := fun r => r ∈ scope k
    have hs : scope k = Finset.univ.filter P := by
      ext r
      simp [P]
    calc
      (∑ r ∈ scope k, badRootWeight k r) =
          ∑ r ∈ Finset.univ.filter P, badRootWeight k r := by
            exact Finset.sum_congr hs (by intro r hr; rfl)
      _ = ∑ r : R, if r ∈ scope k then badRootWeight k r else 0 := by rw [Finset.sum_filter]
  have hswap :
      (∑ k, ∑ r ∈ scope k, badRootWeight k r) =
        ∑ r : R, ∑ k : K, if r ∈ scope k then badRootWeight k r else 0 := by
    calc
      (∑ k, ∑ r ∈ scope k, badRootWeight k r) =
          ∑ k, ∑ r : R, if r ∈ scope k then badRootWeight k r else 0 := by
            apply Finset.sum_congr rfl
            intro k hk
            exact hscopeIndicator k
      _ = ∑ r : R, ∑ k : K, if r ∈ scope k then badRootWeight k r else 0 := by
            rw [Finset.sum_comm]
  have hdegreeBound (r : R) :
      (∑ k : K, if r ∈ scope k then badRootWeight k r else 0) ≤ D * allRootWeight r := by
    calc
      (∑ k : K, if r ∈ scope k then badRootWeight k r else 0) ≤
          ∑ k : K, if r ∈ scope k then allRootWeight r else 0 := by
            apply Finset.sum_le_sum
            intro k hk
            by_cases h : r ∈ scope k <;> simp [h]
            exact hbadLe k r
      _ = (Fintype.card {k : K // r ∈ scope k} : ℝ) * allRootWeight r := by
            rw [← Finset.sum_filter]
            simp [Finset.sum_const, nsmul_eq_mul, Fintype.card_subtype]
      _ ≤ D * allRootWeight r := by
            apply mul_le_mul_of_nonneg_right _ (hweightNonneg r)
            have hcard : (Fintype.card {k : K // r ∈ scope k} : ℝ) ≤ D := by
              simpa [Fintype.card_subtype] using hdeg r
            exact hcard
  have hrowWeight :
      (∑ r : R, allRootWeight r) ≤
        θ ^ (j / 2) * (((T + j : ℕ) : ℝ) * δ) ^ j / (j.factorial : ℝ) := by
    calc
      (∑ r : R, allRootWeight r) ≤
          ∑ u : Endpoint R g, ∑ π ∈ decPaths u v j, pathWeight edgeLaw π := by
            rw [Fintype.sum_sum_type]
            apply le_add_of_nonneg_right
            apply Finset.sum_nonneg
            intro y hy
            apply Finset.sum_nonneg
            intro π hπ
            exact hpathWeight_nonneg π
      _ = ∑ r, ∑ π ∈ decPaths r v j, pathWeight edgeLaw π := by rfl
      _ ≤ _ := decPath_weight_sum δ hδ hδ1 p lab θ hrow hcol hθ0.le hθ1 v j
  have hsumRoot :
      (∑ k, ∑ r ∈ scope k,
        ∑ π ∈ (decPaths (Sum.inl r) v j).filter
          (fun π => pathMeetsOtherRow π (scope k) r), pathWeight edgeLaw π) ≤
        D * (θ ^ (j / 2) * (((T + j : ℕ) : ℝ) * δ) ^ j / (j.factorial : ℝ)) := by
    calc
      (∑ k, ∑ r ∈ scope k,
        ∑ π ∈ (decPaths (Sum.inl r) v j).filter
          (fun π => pathMeetsOtherRow π (scope k) r), pathWeight edgeLaw π) =
          ∑ k, ∑ r ∈ scope k, badRootWeight k r := by
            simp [badRootWeight]
      _ = ∑ r : R, ∑ k : K, if r ∈ scope k then badRootWeight k r else 0 := hswap
      _ ≤ ∑ r : R, D * allRootWeight r := by
            apply Finset.sum_le_sum
            intro r hr
            exact hdegreeBound r
      _ = D * ∑ r : R, allRootWeight r := by rw [Finset.mul_sum]
      _ ≤ D * (θ ^ (j / 2) * (((T + j : ℕ) : ℝ) * δ) ^ j / (j.factorial : ℝ)) := by
            exact mul_le_mul_of_nonneg_left hrowWeight hD
  by_cases hj : j = 0
  · subst j
    simp [pathMeetsOtherRow] at *
  by_cases hD0 : D = 0
  · have hempty (k : K) : scope k = ∅ := by
      apply Finset.card_eq_zero.mp
      have hle : ((scope k).card : ℝ) ≤ 0 := by simpa [hD0] using hsc k
      have hreal : ((scope k).card : ℝ) = 0 := le_antisymm hle (by positivity)
      exact_mod_cast hreal
    simp [hempty, hD0]
  by_cases hcoarse : 1 ≤ (j : ℝ) ^ 2 * (D * lam / θ)
  · have hmult : D ≤ (j : ℝ) ^ 2 * D * (D * lam / θ) := by
      calc
        D ≤ D * ((j : ℝ) ^ 2 * (D * lam / θ)) := le_mul_of_one_le_right hD hcoarse
        _ = (j : ℝ) ^ 2 * D * (D * lam / θ) := by ring
    exact le_trans hsumRoot (by
      apply mul_le_mul_of_nonneg_right hmult
      positivity)
  · sorry

/-- L3.10d-series (03:922–924): `∑_j θ^{⌊j/2⌋} x^j / j! ≤ e^{√θ x} / √θ`. -/
theorem walk_series_bound (θ x : ℝ) (hθ0 : 0 < θ) (hθ1 : θ ≤ 1) (hx : 0 ≤ x) (M : ℕ) :
    ∑ j ∈ Finset.range M, θ ^ (j / 2) * x ^ j / (j.factorial : ℝ) ≤
      Real.exp (Real.sqrt θ * x) / Real.sqrt θ := by
  let q : ℝ := Real.sqrt θ
  have hq0 : 0 < q := Real.sqrt_pos.2 hθ0
  have hq1 : q ≤ 1 := by
    dsimp [q]
    simpa using Real.sqrt_le_sqrt hθ1
  have hq2 : q ^ 2 = θ := Real.sq_sqrt hθ0.le
  have hqinv : 1 ≤ (1 : ℝ) / q := by
    apply (le_div_iff₀ hq0).2
    simpa using hq1
  have hcoef (j : ℕ) : θ ^ (j / 2) ≤ q ^ (j - 1) := by
    by_cases hj : j = 0
    · subst j
      simp
    · have hj1 : 1 ≤ j := Nat.one_le_iff_ne_zero.mpr hj
      have hexp : j - 1 ≤ 2 * (j / 2) := by omega
      calc
        θ ^ (j / 2) = (q ^ 2) ^ (j / 2) := by rw [hq2]
        _ = q ^ (2 * (j / 2)) := by rw [pow_mul]
        _ ≤ q ^ (j - 1) := pow_le_pow_of_le_one hq0.le hq1 hexp
  have hterm (j : ℕ) :
      θ ^ (j / 2) * x ^ j / (j.factorial : ℝ) ≤
        ((q * x) ^ j / (j.factorial : ℝ)) / q := by
    by_cases hj : j = 0
    · subst j
      simpa [q] using hqinv
    · have hj1 : 1 ≤ j := Nat.one_le_iff_ne_zero.mpr hj
      have hidx : j - 1 + 1 = j := Nat.sub_add_cancel hj1
      have hpow : q ^ j = q ^ (j - 1) * q := by
        calc
          q ^ j = q ^ (j - 1 + 1) := congrArg (fun n : ℕ => q ^ n) hidx.symm
          _ = q ^ (j - 1) * q := by rw [pow_succ]
      have hmul : q ^ (j - 1) * x ^ j = (q * x) ^ j / q := by
        field_simp [hq0.ne']
        rw [mul_pow, hpow]
        ring

      calc
        θ ^ (j / 2) * x ^ j / (j.factorial : ℝ) ≤
            q ^ (j - 1) * x ^ j / (j.factorial : ℝ) := by
              apply div_le_div_of_nonneg_right _ (by positivity)
              exact mul_le_mul_of_nonneg_right (hcoef j) (pow_nonneg hx j)
        _ = ((q * x) ^ j / (j.factorial : ℝ)) / q := by
              rw [hmul]
              field_simp [hq0.ne', (Nat.factorial_ne_zero j)]
  calc
    ∑ j ∈ Finset.range M, θ ^ (j / 2) * x ^ j / (j.factorial : ℝ) ≤
        ∑ j ∈ Finset.range M, ((q * x) ^ j / (j.factorial : ℝ)) / q := by
          apply Finset.sum_le_sum
          intro j hj
          exact hterm j
    _ = (∑ j ∈ Finset.range M, (q * x) ^ j / (j.factorial : ℝ)) / q := by
          rw [Finset.sum_div]
    _ ≤ Real.exp (q * x) / q := by
          exact div_le_div_of_nonneg_right
            (Real.sum_le_exp_of_nonneg (mul_nonneg hq0.le hx) M) hq0.le
    _ = Real.exp (Real.sqrt θ * x) / Real.sqrt θ := by rfl

/-- L3.10d-long (03:926–927, factorial tail): if `e² x ≤ J` then the terms of length above `J` sum to at most
`e^{-J}`. -/
theorem walk_series_tail (x : ℝ) (hx : 0 ≤ x) (J : ℕ) (hJ : Real.exp 2 * x ≤ J) (M : ℕ) :
    ∑ j ∈ Finset.Ico (J + 1) M, x ^ j / (j.factorial : ℝ) ≤ Real.exp (-(J : ℝ)) := by
  let e : ℝ := Real.exp 1
  let t : ℝ := Real.exp (-1)
  have hepos : 0 < e := Real.exp_pos 1
  have hE2 : Real.exp 2 = e ^ 2 := by
    dsimp [e]
    rw [show (2 : ℝ) = 1 + 1 by norm_num, Real.exp_add]
    ring
  have hEone : 2 ≤ e := by
    dsimp [e]
    have h := Real.add_one_le_exp (1 : ℝ)
    linarith
  have ht0 : 0 ≤ t := Real.exp_nonneg _
  have ht1 : t < 1 := by
    dsimp [t]
    rw [Real.exp_lt_one_iff]
    norm_num
  have htval : t = e⁻¹ := by
    dsimp [t, e]
    rw [Real.exp_neg]
  have htHalf : t ≤ (1 : ℝ) / 2 := by
    rw [htval]
    have hmul := mul_le_mul_of_nonneg_right hEone (inv_nonneg.mpr hepos.le)
    have hinv : e * e⁻¹ = 1 := mul_inv_cancel₀ hepos.ne'
    nlinarith
  have hExpPow : ∀ n : ℕ, t ^ n = Real.exp (-(n : ℝ)) := by
    intro n
    induction n with
    | zero => simp [t]
    | succ n ih =>
        rw [pow_succ, ih, Nat.cast_succ, neg_add, Real.exp_add]
  have htj : t ^ (J + 1) = Real.exp (-(J : ℝ)) * t := by
    rw [pow_succ, hExpPow J]
  have htailGeom :
      ∑ j ∈ Finset.Ico (J + 1) M, t ^ j ≤ t ^ (J + 1) / (1 - t) :=
    geom_sum_Ico_le_of_lt_one ht0 ht1
  have hratio : t / (1 - t) ≤ 1 := by
    apply (div_le_iff₀ (sub_pos.mpr ht1)).2
    linarith [htHalf]
  have hterm (j : ℕ) (hj : j ∈ Finset.Ico (J + 1) M) :
      x ^ j / (j.factorial : ℝ) ≤ t ^ j := by
    have hjmem := Finset.mem_Ico.mp hj
    have hjposN : 0 < j := by omega
    have hjpos : 0 < (j : ℝ) := by exact_mod_cast hjposN
    have hJlt : J < j := by omega
    have hJj : (J : ℝ) ≤ (j : ℝ) := by exact_mod_cast (Nat.le_of_lt hJlt)
    have hE2x : Real.exp 2 * x ≤ (j : ℝ) := le_trans hJ hJj
    have hprod : e * x * e ≤ (j : ℝ) := by
      calc
        e * x * e = Real.exp 2 * x := by rw [hE2]; ring
        _ ≤ (j : ℝ) := hE2x
    have hex : e * x ≤ (j : ℝ) / e := (le_div_iff₀ hepos).2 hprod
    have hquot : e * x / (j : ℝ) ≤ t := by
      rw [htval]
      apply (div_le_iff₀ hjpos).2
      calc
        e * x ≤ (j : ℝ) / e := hex
        _ = e⁻¹ * (j : ℝ) := by ring
    have hbase : 0 ≤ e * x / (j : ℝ) := by positivity
    have hst : Real.sqrt (2 * Real.pi * (j : ℝ)) *
        ((j : ℝ) / e) ^ j ≤ (j.factorial : ℝ) := by
      simpa [e] using (Stirling.le_factorial_stirling j)
    have hrad : 1 ≤ 2 * Real.pi * (j : ℝ) := by
      have hj1 : (1 : ℝ) ≤ (j : ℝ) := by exact_mod_cast (Nat.one_le_of_lt hjposN)
      nlinarith [Real.pi_gt_three]
    have hsqrt : 1 ≤ Real.sqrt (2 * Real.pi * (j : ℝ)) := by
      rw [← Real.sqrt_one]
      exact Real.sqrt_le_sqrt hrad
    have hfac : ((j : ℝ) / e) ^ j ≤ (j.factorial : ℝ) := by
      calc
        ((j : ℝ) / e) ^ j = 1 * ((j : ℝ) / e) ^ j := by ring
        _ ≤ Real.sqrt (2 * Real.pi * (j : ℝ)) * ((j : ℝ) / e) ^ j :=
          mul_le_mul_of_nonneg_right hsqrt (by positivity)
        _ ≤ (j.factorial : ℝ) := hst
    have hpowEq : x ^ j = (e * x / (j : ℝ)) ^ j * ((j : ℝ) / e) ^ j := by
      rw [← mul_pow]
      field_simp [hepos.ne', hjpos.ne']
    have hpowBound : x ^ j ≤ (e * x / (j : ℝ)) ^ j * (j.factorial : ℝ) := by
      rw [hpowEq]
      exact mul_le_mul_of_nonneg_left hfac (pow_nonneg hbase j)
    have hdiv : x ^ j / (j.factorial : ℝ) ≤ (e * x / (j : ℝ)) ^ j :=
      (div_le_iff₀ (by positivity)).2 hpowBound
    exact le_trans hdiv (pow_le_pow_left₀ hbase hquot j)
  calc
    ∑ j ∈ Finset.Ico (J + 1) M, x ^ j / (j.factorial : ℝ) ≤
        ∑ j ∈ Finset.Ico (J + 1) M, t ^ j := by
          apply Finset.sum_le_sum
          intro j hj
          exact hterm j hj
    _ ≤ t ^ (J + 1) / (1 - t) := htailGeom
    _ = Real.exp (-(J : ℝ)) * (t / (1 - t)) := by rw [htj]; ring
    _ ≤ Real.exp (-(J : ℝ)) := by
          calc
            Real.exp (-(J : ℝ)) * (t / (1 - t)) ≤
                Real.exp (-(J : ℝ)) * 1 :=
                  mul_le_mul_of_nonneg_left hratio (Real.exp_nonneg _)
            _ = Real.exp (-(J : ℝ)) := by ring

end HypercubeRamsey.Clock
