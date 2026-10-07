import HypercubeRamsey.S03.Clock.Leaves

/-!
# Clock sampling inputs and Step 1 certificates

This file packages exactly the finite row/output/predicate data from Lemma 3.10.  `TrimCertificate` records
the discarded mass, conditional failure estimates, and the completed label columns used by the independent
edge clocks.
-/

namespace HypercubeRamsey.Clock

open scoped BigOperators

/-- The row laws, output labels, failure predicates and their scopes. -/
structure SamplingInstance (n g : ℕ) (R K : Type*)
    [Fintype R] [DecidableEq R] [Fintype K]
    (Ω : R → Type*) [∀ a, Fintype (Ω a)] [∀ a, DecidableEq (Ω a)] where
  lab : ∀ a, Ω a → Fin g
  p : ∀ a, FinProb (Ω a)
  failure : K → (∀ a, Ω a) → Prop
  scope : K → Finset R

/-- The independent product law of an instance. -/
noncomputable def SamplingInstance.productLaw {n g : ℕ} {R K : Type*}
    [Fintype R] [DecidableEq R] [Fintype K]
    {Ω : R → Type*} [∀ a, Fintype (Ω a)] [∀ a, DecidableEq (Ω a)]
    (I : SamplingInstance n g R K Ω) : FinProb (∀ a, Ω a) := FinProb.pi I.p

/-- The quantitative assumptions in the frozen clock-sampling statement. -/
def SamplingInstance.Admissible {n g : ℕ} {R K : Type*}
    [Fintype R] [DecidableEq R] [Fintype K]
    {Ω : R → Type*} [∀ a, Fintype (Ω a)] [∀ a, DecidableEq (Ω a)]
    (I : SamplingInstance n g R K Ω) (B A P : ℝ) : Prop :=
  (∀ y, ∑ a, labMarg (I.p a) (I.lab a) y ≤ 1e-8) ∧
  (∀ a y, labMarg (I.p a) (I.lab a) y ≤ (n : ℝ) ^ (-A)) ∧
  (∀ k, FinProb.DependsOn (I.failure k) (I.scope k)) ∧
  (∀ k, ((I.scope k).card : ℝ) ≤ (n : ℝ) ^ B) ∧
  (∀ a, ((Finset.univ.filter (fun k => a ∈ I.scope k)).card : ℝ) ≤ (n : ℝ) ^ B) ∧
  (∀ k, I.productLaw.pr (I.failure k) ≤ (n : ℝ) ^ (-P))

/-- A predicate's probability after one scope row has been pinned to an output. -/
noncomputable def pinnedFailureProb {R K : Type*}
    [Fintype R] [DecidableEq R] [Fintype K]
    {Ω : R → Type*} [∀ a, Fintype (Ω a)] [∀ a, DecidableEq (Ω a)]
    (laws : ∀ a, FinProb (Ω a)) (F : K → (∀ a, Ω a) → Prop)
    (k : K) (a : R) (o : Ω a) : ℝ :=
  (FinProb.pi laws).pr (fun ω => F k ω ∧ ω a = o) / (laws a).w o

/-- A certificate for Step 1: trim outputs with large pinned failure probability, renormalize, and complete
all label columns to a common rate `θ` with dummy rows. -/
structure TrimCertificate {n g : ℕ} {R K : Type*}
    [Fintype R] [DecidableEq R] [Fintype K]
    {Ω : R → Type*} [∀ a, Fintype (Ω a)] [∀ a, DecidableEq (Ω a)]
    (I : SamplingInstance n g R K Ω) (B A P : ℝ) where
  keep : ∀ a, Finset (Ω a)
  trimmed : ∀ a, FinProb (Ω a)
  trimmed_supported : ∀ a o, o ∉ keep a → (trimmed a).w o = 0
  /-- The trimmed law is the original law restricted to `keep a` and renormalized (TeX 03:825). -/
  trimmed_eq : ∀ a o, (trimmed a).w o =
    if o ∈ keep a then (I.p a).w o / (I.p a).pr (fun o' => o' ∈ keep a) else 0
  discarded_mass : ∀ a, (I.p a).pr (fun o => o ∉ keep a) ≤ (n : ℝ) ^ (B - P / 2)
  trimmed_atom : ∀ a y, labMarg (trimmed a) (I.lab a) y ≤ 2 * (n : ℝ) ^ (-A)
  trimmed_failure : ∀ k, (FinProb.pi trimmed).pr (I.failure k) ≤ (n : ℝ) ^ (-P / 3)
  trimmed_pinned_failure : ∀ k a, a ∈ I.scope k → ∀ o ∈ keep a,
    pinnedFailureProb trimmed I.failure k a o ≤ (n : ℝ) ^ (-P / 3)
  dummyRows : ℕ
  dummyLaw : Fin dummyRows → Fin g → ℝ
  dummy_nonneg : ∀ i y, 0 ≤ dummyLaw i y
  dummy_row_sum : ∀ i, ∑ y, dummyLaw i y = 1
  theta : ℝ
  theta_lower : 1e-6 ≤ theta
  theta_upper : theta ≤ 1e-6 + 1 / (g : ℝ)
  completed_card : theta * (g : ℝ) = (Fintype.card R + dummyRows : ℝ)
  completed_columns : ∀ y, (∑ a, labMarg (trimmed a) (I.lab a) y) +
    (∑ i, dummyLaw i y) = theta
  dummy_atom : ∀ i y, dummyLaw i y ≤ 2 / (g : ℝ)

/-- L3.10a (03:817–842): discard rare outputs, control the renormalization loss, and complete every label
column to the common rate `θ`. `P` is large in terms of `B` (03:806–807): with `n ≥ 2`, `4B + 4 ≤ P` makes the
per-row loss `n^{B-P/2} ≤ n^{-B-2} ≤ 1/4` and the loss over a scope or query `n^{2B-P/2} ≤ n^{-2} ≤ 1/4`. -/
theorem step1_trim_and_complete {n g : ℕ} {R K : Type*}
    [Fintype R] [DecidableEq R] [Fintype K]
    {Ω : R → Type*} [∀ a, Fintype (Ω a)] [∀ a, DecidableEq (Ω a)]
    (I : SamplingInstance n g R K Ω) (B A P : ℝ)
    (hn : 2 ≤ n) (hB : 0 ≤ B) (hBP : 4 * B + 4 ≤ P)
    (hI : I.Admissible B A P) : Nonempty (TrimCertificate I B A P) := by
  sorry

/-- The renormalization cost of Step 1 on a query of at most `n^B` rows (TeX 03:826–827, 03:1128–1131):
`(1 - n^{B-P/2})^{-n^B} ≤ 1 + 2 n^{2B-P/2}`. -/
theorem untrim_product_bound {n g : ℕ} {R K : Type*}
    [Fintype R] [DecidableEq R] [Fintype K]
    {Ω : R → Type*} [∀ a, Fintype (Ω a)] [∀ a, DecidableEq (Ω a)]
    (I : SamplingInstance n g R K Ω) (B A P : ℝ)
    (hn : 2 ≤ n) (hB : 0 ≤ B) (hBP : 4 * B + 4 ≤ P)
    (C : TrimCertificate I B A P) (S : Finset R) (o : ∀ a, Ω a)
    (hS : (S.card : ℝ) ≤ (n : ℝ) ^ B) :
    ∏ a ∈ S, (C.trimmed a).w (o a) ≤
      (1 + 2 * (n : ℝ) ^ (2 * B - P / 2)) * ∏ a ∈ S, (I.p a).w (o a) := by
  sorry

end HypercubeRamsey.Clock
