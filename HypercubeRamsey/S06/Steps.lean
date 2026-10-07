import HypercubeRamsey.S06.Step3Defs

/-!
# Steps 1–3: the predictive tests and their consequences

L6.1c (06:165–189), L6.1d (06:191–226), L6.1e(iii) (06:265–295), L6.1f (06:297–366), L6.1g (06:368–447).

Each step is a predicate on a context, and each node proves it for all contexts of large dimension, possibly
from the predicates of earlier steps (stated as hypotheses, so that the section assembly uses every node).

* Raw failure bounds (`Step1CapBound`, `Step1DelBound`, `Step2Bound`, `Step3TestLow`, `Step3TestHigh`): each test
  fails, jointly with its true gate, with raw probability at most its threshold.
* Deterministic consequences on passing tests (`TagDom`, `Step2Dom`, `Step2Supp`, `Step3LowBounds`,
  `Step3HighBounds`), at bases in the raw support (`BaseSupp`) or the local part of it (`KeysSupp`).
* Descriptor sizes and counts (`DescSize`, `DescCount`).
-/

namespace HypercubeRamsey
namespace S06

open OAI.HypercubeRamsey
open Classical
open scoped BigOperators

noncomputable section

variable {γ p₀ K : ℝ} {n N : ℕ} {E : Fin N → Fin N → Prop} {G : Colour} {M : TagMix N}
variable (X : Ctx6 γ p₀ K n N E G M)

namespace Ctx6

/-! ### Support of the raw base experiment -/

/-- The base variables on the key list `S` lie in the raw support: `V₀ ∈ supp Π'|_{S₀}`, the candidates at the
bins of `S` in the partner law of `V₀`, the base tags of `S` in their laws. -/
def KeysSupp (b : X.Base) (S : Finset X.Key) : Prop :=
  0 < X.initLaw.w b.1 ∧ (∀ u ∈ X.binsOf S, 0 < (X.candLaw b.1).w (b.2.1 u)) ∧
    ∀ s ∈ S, 0 < (X.tagLawAt (X.parOf b) s).w (b.2.2 s)

/-- The whole base lies in the raw support. -/
def BaseSupp (b : X.Base) : Prop := X.KeysSupp b Finset.univ

/-- The keys whose base variables enter a type's Step 2 objects. -/
def typeKeys (β : X.Ty) : Finset X.Key := insert β.key (β.obs.biUnion fun ℓ => X.C ℓ.1)

/-! ### Step 1 (06:165–189) -/

/-- The base-tag law is dominated: `T₀ ≤ n^{d₀} Λ` whenever the primary is heavy and related to the other
primary (06:96–104, 06:159–160; restriction mass `≥ c₀ − c₁ = c₁`, `η_y ≤ n^{2D_*}Λ`). -/
def TagDom : Prop :=
  ∀ (pv : Par6 X.Bin N) (h : X.Key), pv.val (primaryName6 h) ∈ X.par.heavy →
    related6 E G M (pv.val (primaryName6 h)) (pv.val (otherPrimaryName6 h)) →
      ∀ i, (X.tagLawAt pv h).w i ≤ (n : ℝ) ^ d₀ * M.Λ i

/-- Step 1 cap failure has raw probability `≤ n^{-δ₁/2}` (06:182–189). -/
def Step1CapBound : Prop :=
  ∀ h ∈ X.step1Keys, X.baseLaw.pr (fun b => ¬ X.Step1Cap b h) ≤ (n : ℝ) ^ (-(δ₁ / 2))

/-- Step 1 deletion failure has raw probability `≤ n^{-δ₁/2}` (06:173–181). -/
def Step1DelBound : Prop :=
  ∀ h ∈ X.step1Keys, ∀ s ∈ X.C h, X.baseLaw.pr (fun b => ¬ X.Step1Del b h s) ≤ (n : ℝ) ^ (-(δ₁ / 2))

end Ctx6

/-- L6.1c (base tags, 06:93–104, 06:159–160). -/
theorem L6_1c_tag (γ p₀ K : ℝ) (hadm : Admissible6 γ p₀ K) :
    ForLarge6 γ p₀ K fun _ _ _ _ _ X => X.TagDom := by
  sorry

/-- L6.1c (cap, 06:182–189): uniform references for the bounded candidate list and `Λ` for incoming tags; the
predictive-denominator calculation (L3.7) with `d₀, δ₁ ≪ d₁`. -/
theorem L6_1c_cap (γ p₀ K : ℝ) (hadm : Admissible6 γ p₀ K) :
    ForLarge6 γ p₀ K fun _ _ _ _ _ X => X.TagDom → X.Step1CapBound := by
  sorry

/-- L6.1c (deletion, 06:173–181): the incoming tag has likelihood `≤ n^{d₀} Λ(i)` at every supported parent
value; its predictive density is `< n^{-δ₁}` with probability `≤ n^{-δ₁}`; Bayes off that event. -/
theorem L6_1c_del (γ p₀ K : ℝ) (hadm : Admissible6 γ p₀ K) :
    ForLarge6 γ p₀ K fun _ _ _ _ _ X => X.TagDom → X.Step1DelBound := by
  sorry

namespace Ctx6

/-! ### Step 2 (06:191–226) -/

/-- Step 2 failure has raw probability `≤ n^{-δ₂u_β/2}` at every occurring type (06:201–211: the true-gated
subdensity of `Z_S` relative to `∏ π_{ℓ,−h}` is `m_S`; `(1 + |S|) n^{-δ₂u} ≤ n^{-δ₂u/2}`). -/
def Step2Bound : Prop :=
  ∀ β ∈ X.occTypes, X.rawHist.pr (fun H => X.Step2Fail H β) ≤ (n : ℝ) ^ (-(δ₂ * β.u / 2))

/-- On the Step 2 tests: `T_β ≤ n^{d₂u}Λ` and `T_β ≤ n^{d₂u} T_{β,−ℓ}` (06:212–220; `|S| ≤ 602 u_β`), at any
values of the hidden scalars. -/
def Step2Dom : Prop :=
  ∀ (H : X.Hist) (β : X.Ty), β ∈ X.occTypes → X.KeysSupp H.1 {β.key} → X.Step2Tests H β →
    (∀ i, (X.Tβ H β).w i ≤ (n : ℝ) ^ (d₂ * β.u) * M.Λ i) ∧
      ∀ ℓ ∈ β.obs, ∀ i, (X.Tβ H β).w i ≤ (n : ℝ) ^ (d₂ * β.u) * (X.TβDel H β ℓ).w i

/-- A required name whose primary is the type's own named primary. -/
def MatchName (β : X.Ty) : X.Name → Prop
  | .par p => p = primaryName6 β.key
  | .hid ℓ => primaryName6 ℓ.1 = primaryName6 β.key

/-- On the Step 2 tests every tag in the support of `T_β` sees every matching-primary required variable with
degree `≥ 1 − ε`, and the common-hit set has `μ_i`-mass `≥ c₁/2` (06:220–226). -/
def Step2Supp : Prop :=
  ∀ (H : X.Hist) (β : X.Ty), β ∈ X.occTypes → X.KeysSupp H.1 (X.typeKeys β) → X.Step2Tests H β →
    ∀ i, 0 < (X.Tβ H β).w i →
      c₁ / 2 ≤ ∑ x ∈ X.reqNbhd H (reqNames6 β), (M.μ i).w x ∧
        ∀ nm ∈ reqNames6 β, X.MatchName β nm → 1 - X.ε ≤ colDeg E G (M.μ i) (X.varVal H nm)

end Ctx6

/-- L6.1d (failure, 06:201–211). -/
theorem L6_1d_fail (γ p₀ K : ℝ) (hadm : Admissible6 γ p₀ K) :
    ForLarge6 γ p₀ K fun _ _ _ _ _ X => X.Step2Bound := by
  sorry

/-- L6.1d (domination, 06:212–220): the absolute ratio is `≤ n^{d₀ + d₁|S| + δ₂u}`, the deleted ratio
`≤ n^{d₁ + δ₂u}`, both below `n^{d₂u}`. -/
theorem L6_1d_dom (γ p₀ K : ℝ) (hadm : Admissible6 γ p₀ K) :
    ForLarge6 γ p₀ K fun _ _ _ _ _ X => X.TagDom → X.Step2Dom := by
  sorry

/-- L6.1d (support, 06:220–226): positive likelihood for `Z_{(h',t')}` forces the base tag at `h ∈ C(h')` to see
that value (`≥ 1 − ε` for the same named primary, `≥ c₁` in the crossing case); at most one required column
has degree only `c₁`; `c₁ − O(mε) ≥ c₁/2`. -/
theorem L6_1d_supp (γ p₀ K : ℝ) (hadm : Admissible6 γ p₀ K) :
    ForLarge6 γ p₀ K fun _ _ _ _ _ X => X.Step2Supp := by
  sorry

namespace Ctx6

/-! ### Descriptor sizes and counts (06:265–295) -/

/-- A descriptor at an odd state observes `O(T + J)` tuples (06:270–273). -/
def DescSize : Prop :=
  ∀ (Id : Type) [Fintype Id] [DecidableEq Id] (b : X.State) (perm : X.g.L.stNbr b → Finset Id),
    b ∈ X.g.L.oddStates → ∀ D ∈ X.descsIn b perm, (D.card : ℝ) ≤ 10 ^ 4 * (X.T + X.J + 1)

/-- With at most `P` permitted IDs per neighbouring state, the number of descriptors is
`exp(O(T log(nP) + (J+1) log T))` (06:274–281). -/
def DescCount : Prop :=
  ∀ (Id : Type) [Fintype Id] [DecidableEq Id] (b : X.State) (perm : X.g.L.stNbr b → Finset Id) (P : ℕ),
    b ∈ X.g.L.oddStates → (∀ a, (perm a).card ≤ P) →
      ((X.descsIn b perm).card : ℝ) ≤
        Real.exp (10 ^ 4 * (X.T * Real.log (3 * n * P + 2) + (X.J + 1) * Real.log (X.T + 2)))

end Ctx6

/-- L6.1e (sizes, 06:270–273): constantly many generic types, each with at most `T` IDs; `O(J+1)` exceptional
states, one ID each. -/
theorem L6_1e_size (γ p₀ K : ℝ) (hadm : Admissible6 γ p₀ K) :
    ForLarge6 γ p₀ K fun _ _ _ _ _ X => X.DescSize := by
  sorry

/-- L6.1e (counts, 06:274–281): list the at most `T` IDs, a subset for each generic type, one listed ID for each
exceptional state. -/
theorem L6_1e_count (γ p₀ K : ℝ) (hadm : Admissible6 γ p₀ K) :
    ForLarge6 γ p₀ K fun _ _ _ _ _ X => X.DescCount := by
  sorry

namespace Ctx6

/-! ### Step 3 (06:297–447) -/

/-- Raw Step 3 failure bounds at low targets: for every descriptor of occurring types, each data test fails
jointly with the true-target gate with raw probability `≤ e^{−.02k}` (06:346–353). -/
def Step3TestLow : Prop :=
  ∀ (Id : Type) [Fintype Id] [DecidableEq Id] (b : X.State), b ∈ X.g.L.oddStates → X.stMode b = .low →
    ∀ D : Finset (Id × X.Ty), (∀ e ∈ D, e.2 ∈ X.occTypes) →
      (X.rawHistData Id).pr (fun ω => X.S3TrueGate ω.1 b D ∧ X.s3Mass ω.1 b D ω.2 none < X.s3Thr) ≤ X.s3Thr ∧
      ∀ c ∈ D, (X.rawHistData Id).pr (fun ω => X.S3TrueGate ω.1 b D ∧
        X.s3Mass ω.1 b D ω.2 none < X.s3Thr * X.s3Mass ω.1 b D ω.2 (some c)) ≤ X.s3Thr

/-- Raw Step 3 failure bounds at high targets; the probability integrates `H_loc` too (06:418–426). -/
def Step3TestHigh : Prop :=
  ∀ (Id : Type) [Fintype Id] [DecidableEq Id] (b : X.State), b ∈ X.g.L.oddStates → X.stMode b = .high →
    ∀ D : Finset (Id × X.Ty), (∀ e ∈ D, e.2 ∈ X.occTypes) →
      (X.rawHistData Id).pr (fun ω => X.S3TrueGate ω.1 b D ∧ X.s3Mass ω.1 b D ω.2 none < X.s3Thr) ≤ X.s3Thr ∧
      ∀ c ∈ D, (X.rawHistData Id).pr (fun ω => X.S3TrueGate ω.1 b D ∧
        X.s3Mass ω.1 b D ω.2 none < X.s3Thr * X.s3Mass ω.1 b D ω.2 (some c)) ≤ X.s3Thr

/-- Low Step 3 consequences on the data tests: `L_b ≤ e^{.16k} Q_{−c}` for matching tuples, `N max L_b ≤
e^{m^{.15}/2}`, and every supported candidate hits every observed entry (06:355–366). -/
def Step3LowBounds : Prop :=
  ∀ (Id : Type) [Fintype Id] [DecidableEq Id] (b : X.State) (perm : X.g.L.stNbr b → Finset Id),
    b ∈ X.g.L.oddStates → X.stMode b = .low → ∀ D ∈ X.descsIn b perm, ∀ (H : X.Hist) (o : X.Data Id),
      X.BaseSupp H.1 → X.S3Tests H b D o →
        (∀ c ∈ D, X.Matching b c.2 → ∀ ξ,
          (X.s3Post H b D o).w ξ ≤ Real.exp ((16 / 100) * X.k) * (X.s3Del H b D o c).w ξ) ∧
        (∀ ξ, (N : ℝ) * (X.s3Post H b D o).w ξ ≤ Real.exp ((X.m : ℝ) ^ (15 / 100 : ℝ) / 2)) ∧
        (∀ ξ, 0 < (X.s3Post H b D o).w ξ → ∀ e ∈ D, ∀ r, Hits E G ((o e).2 r) ξ)

/-- High Step 3 consequences: `L_b ≤ e^{.16k} Q_{−c}` for matching tuples, `N max L_b ≤ n^{.05J}`, support
(06:428–447). -/
def Step3HighBounds : Prop :=
  ∀ (Id : Type) [Fintype Id] [DecidableEq Id] (b : X.State) (perm : X.g.L.stNbr b → Finset Id),
    b ∈ X.g.L.oddStates → X.stMode b = .high → ∀ D ∈ X.descsIn b perm, ∀ (H : X.Hist) (o : X.Data Id),
      X.BaseSupp H.1 → X.S3Tests H b D o →
        (∀ c ∈ D, X.Matching b c.2 → ∀ ξ,
          (X.s3Post H b D o).w ξ ≤ Real.exp ((16 / 100) * X.k) * (X.s3Del H b D o c).w ξ) ∧
        (∀ ξ, (N : ℝ) * (X.s3Post H b D o).w ξ ≤ (n : ℝ) ^ ((5 / 100 : ℝ) * X.J)) ∧
        (∀ ξ, 0 < (X.s3Post H b D o).w ξ → ∀ e ∈ D, ∀ r, Hits E G ((o e).2 r) ξ)

end Ctx6

/-- L6.1f (tests, 06:340–353): `M` is the true-gated subdensity relative to `Q^data` and `∫ M_{−c} dQ^data ≤ 1`. -/
theorem L6_1f_tests (γ p₀ K : ℝ) (hadm : Admissible6 γ p₀ K) :
    ForLarge6 γ p₀ K fun _ _ _ _ _ X => X.Step2Supp → X.Step3TestLow := by
  sorry

/-- L6.1f (bounds, 06:324–336, 06:355–366): tuple ratios `n^{d₂u}(1+4ε/c₁)^k` (matching), `n^{d₂u}(2/c₁)^k`
(nonmatching, at most one); prior cap, `O(T+J)` tuples; `O(J² log n) = o(m^{.15})`. -/
theorem L6_1f_bounds (γ p₀ K : ℝ) (hadm : Admissible6 γ p₀ K) :
    ForLarge6 γ p₀ K fun _ _ _ _ _ X => X.Step2Dom → X.Step2Supp → X.DescSize → X.Step3LowBounds := by
  sorry

/-- L6.1g (tests, 06:411–426): the local list is closed under kernel inputs, so its marginal is the product of
its kernels; the deleted density integrates to at most one. -/
theorem L6_1g_tests (γ p₀ K : ℝ) (hadm : Admissible6 γ p₀ K) :
    ForLarge6 γ p₀ K fun _ _ _ _ _ X => X.Step2Supp → X.Step3TestHigh := by
  sorry

/-- L6.1g (bounds, 06:428–447): the width budget `O(1 + d₀ log n) + O(J d₁ log n) + O((T+J) d₂ log n) + o(k) +
k log(2/c₁) + .02k < .05 J log n`. -/
theorem L6_1g_bounds (γ p₀ K : ℝ) (hadm : Admissible6 γ p₀ K) :
    ForLarge6 γ p₀ K fun _ _ _ _ _ X =>
      X.TagDom → X.Step2Dom → X.Step2Supp → X.DescSize → X.Step3HighBounds := by
  sorry

namespace Ctx6

/-- All Step 1–3 predicates (the conjunction assembled in the section proof). -/
def StepFacts : Prop :=
  X.TagDom ∧ X.Step1CapBound ∧ X.Step1DelBound ∧ X.Step2Bound ∧ X.Step2Dom ∧ X.Step2Supp ∧ X.DescSize ∧
    X.DescCount ∧ X.Step3TestLow ∧ X.Step3TestHigh ∧ X.Step3LowBounds ∧ X.Step3HighBounds

end Ctx6

/-- Steps 1–3 assembled from their nodes. -/
theorem stepFacts6 (γ p₀ K : ℝ) (hadm : Admissible6 γ p₀ K) :
    ForLarge6 γ p₀ K fun _ _ _ _ _ X => X.StepFacts := by
  have h := (L6_1c_tag γ p₀ K hadm).and <| (L6_1c_cap γ p₀ K hadm).and <| (L6_1c_del γ p₀ K hadm).and <|
    (L6_1d_fail γ p₀ K hadm).and <| (L6_1d_dom γ p₀ K hadm).and <| (L6_1d_supp γ p₀ K hadm).and <|
    (L6_1e_size γ p₀ K hadm).and <| (L6_1e_count γ p₀ K hadm).and <| (L6_1f_tests γ p₀ K hadm).and <|
    (L6_1g_tests γ p₀ K hadm).and <| (L6_1f_bounds γ p₀ K hadm).and (L6_1g_bounds γ p₀ K hadm)
  refine h.mono ?_
  intro n N E G M X ⟨hT, hC, hD, h2, h2d, h2s, hS, hN, h3l, h3h, hbl, hbh⟩
  exact ⟨hT, hC hT, hD hT, h2, h2d hT, h2s, hS, hN, h3l h2s, h3h h2s, hbl (h2d hT) h2s hS,
    hbh hT (h2d hT) h2s hS⟩

end

end S06
end HypercubeRamsey
