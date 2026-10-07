import HypercubeRamsey.S18.Defs

namespace HypercubeRamsey.Lane_sol_s18_n4
open Classical
open scoped BigOperators

variable {κ : CConsts} {T : Stage} {k : ℕ} {PT : ProfiledTiling κ T k}
    {hPT : PT.Valid}

/-- The initial-data specification does not constrain the reference row kernels. -/
theorem specWithKernels (D : S18.LateData hPT) (hD : D.Spec)
    (K : LateKernels D.encoding.base) : (D.withKernels K).Spec := by
  exact {
    corner_mass := hD.corner_mass
    fresh_internal := hD.fresh_internal
    thresholds := hD.thresholds
    calibration := hD.calibration
    upstream_bad := by
      intro f
      have hp : (D.withKernels K).encoding.permLaw = D.encoding.permLaw := rfl
      have hb : (D.withKernels K).upstreamBad f = D.upstreamBad f := by
        funext x
        cases f <;> rfl
      rw [hp, hb]
      exact hD.upstream_bad f
    upstream_bad_pinned := by
      intro C slot bin f
      have hp : (D.withKernels K).encoding.permLaw = D.encoding.permLaw := rfl
      have hb : (D.withKernels K).upstreamBad f = D.upstreamBad f := by
        funext x
        cases f <;> rfl
      rw [hp, hb]
      exact hD.upstream_bad_pinned C slot bin f
    typical_positive := hD.typical_positive
    fresh_singleton := hD.fresh_singleton
    scope_eq := hD.scope_eq
    palette_counts := hD.palette_counts
    palette_separation := hD.palette_separation
    events_eq := hD.events_eq
    initial_cap := hD.initial_cap
    initial_success := hD.initial_success
    prior_local := hD.prior_local }

 theorem lateRiskWithKernels (D : S18.LateData hPT)
    (K : LateKernels D.encoding.base) (F : S18.LateEvent D) (x : D.encoding.InitInput) :
    (D.withKernels K).pLate F x =
      (K.refRun (D.encoding.initialState x)).pr (S18.lateFailure D F) := rfl

/-- Any leaf cover forces every bad input to have a bounded local certificate. -/
theorem leafLocalCertificate (D : S18.LateData hPT) (δ : ℝ)
    (L : S18.LeafCoupling D δ) (f : S18.TerminalIndex D) (x : D.encoding.InitInput)
    (hx : S18.terminalFailure D δ f x) :
    ∃ (domains : Finset (Sigma fun C : D.geom.Cell => Fin (D.geom.nslot C)))
      (tapes : Finset D.geom.Cell),
      ((domains.card + tapes.card : ℕ) : ℝ) ≤
        Real.rpow (T.S.n k : ℝ) (10 * ((κ.Ac + 4) * D.encoding.Ts + D.geom.r)) ∧
      ∀ x' : D.encoding.InitInput,
        (∀ slot ∈ domains, x.1 slot.1 slot.2 = x'.1 slot.1 slot.2) →
        (∀ C ∈ tapes, x.2 C = x'.2 C) → S18.terminalFailure D δ f x' := by
  obtain ⟨i, hreq, hi⟩ := (L.covers f x).1 hx
  refine ⟨L.domains i, L.tapes i, ?_, ?_⟩
  · have hb := L.scope_bound i
    have himage : 0 ≤ ((L.images i).card : ℝ) := Nat.cast_nonneg _
    push_cast at hb ⊢
    linarith
  · intro x' hdom htapes
    have hi' : x' ∈ L.leaf i := (L.depends_on i x x' hdom htapes).1 hi
    exact (L.covers f x').2 ⟨i, hreq, hi'⟩

 theorem noLeafCouplingOfNoSmallCertificate (D : S18.LateData hPT) (δ : ℝ)
    (f : S18.TerminalIndex D) (x : D.encoding.InitInput)
    (hx : S18.terminalFailure D δ f x)
    (hno : ∀ (domains : Finset (Sigma fun C : D.geom.Cell => Fin (D.geom.nslot C)))
      (tapes : Finset D.geom.Cell),
      ((domains.card + tapes.card : ℕ) : ℝ) ≤
        Real.rpow (T.S.n k : ℝ) (10 * ((κ.Ac + 4) * D.encoding.Ts + D.geom.r)) →
      ∃ x' : D.encoding.InitInput,
        (∀ slot ∈ domains, x.1 slot.1 slot.2 = x'.1 slot.1 slot.2) ∧
        (∀ C ∈ tapes, x.2 C = x'.2 C) ∧ ¬ S18.terminalFailure D δ f x') :
    ¬ Nonempty (S18.LeafCoupling D δ) := by
  rintro ⟨L⟩
  obtain ⟨dom, tapes, hbound, hcert⟩ := leafLocalCertificate D δ L f x hx
  obtain ⟨x', hdom, htapes, hgood⟩ := hno dom tapes hbound
  exact hgood (hcert x' hdom htapes)

end HypercubeRamsey.Lane_sol_s18_n4
