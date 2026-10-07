import HypercubeRamsey.S05.Experiment
import HypercubeRamsey.S05.History_q_s05_hist1

/-!
# L5.1c, d, f, h, l(1–2): raw test bounds and the five conditioning stages

Steps 1–3 bound the raw probability of each test failure (05:192–286, 05:400–470).  The five stages
(05:607–760) then restrict, in order, the parent `V₀`, the coarse base, the high keys, each low key separately,
and the low keys jointly; each stage restricts only its own variables at a fixed entering history.  The
conclusions of each stage are exactly the inputs of the next.  L5.1l(1–2) bound the history-level odd-load
averages under the stage laws (05:1003–1041).
-/

namespace HypercubeRamsey

open Classical OAI.HypercubeRamsey

set_option synthInstance.maxSize 1024

noncomputable section

variable {γ K' χ : ℝ}

/-- A point mass. -/
def FinProb.dirac5 {Ω : Type*} [Fintype Ω] [DecidableEq Ω] (ω₀ : Ω) : FinProb Ω where
  w ω := if ω = ω₀ then 1 else 0
  nonneg ω := by split_ifs <;> norm_num
  sum_eq_one := by simp

/-- An event of probability greater than zero has a support point. -/
theorem FinProb.exists_support_of_pos5 {Ω : Type*} [Fintype Ω] (P : FinProb Ω) (A : Ω → Prop)
    (h : 0 < P.pr A) : ∃ ω, P.w ω ≠ 0 ∧ A ω := by
  classical
  by_contra hno
  push_neg at hno
  have : P.pr A = 0 := by
    unfold FinProb.pr
    apply Finset.sum_eq_zero
    intro ω _
    by_cases hA : A ω
    · by_cases hw : P.w ω = 0
      · simp [hA, hw]
      · exact absurd hA (hno ω hw)
    · simp [hA]
  linarith

/-- A complement event of probability below one has a support point outside it. -/
theorem FinProb.exists_support_of_pr_lt5 {Ω : Type*} [Fintype Ω] (P : FinProb Ω) (A : Ω → Prop)
    (h : P.pr A < 1) : ∃ ω, P.w ω ≠ 0 ∧ ¬ A ω := by
  classical
  apply FinProb.exists_support_of_pos5
  have hsum : P.pr (fun ω => ¬ A ω) + P.pr A = 1 := by
    unfold FinProb.pr
    rw [← Finset.sum_add_distrib]
    calc
      _ = ∑ ω, P.w ω := by
        apply Finset.sum_congr rfl
        intro ω _
        by_cases hA : A ω <;> simp [hA]
      _ = 1 := P.sum_eq_one
  linarith

namespace Setup5

variable {n N : ℕ} {E : Fin N → Fin N → Prop} {G : Colour} (X : Setup5 γ K' χ n N E G)

/-! ### Raw bounds of Steps 1–3 -/

/-- The conclusion of Step 1 (05:199–211): each listed comparison and each prior cap fails with raw
probability at most `e^{-δ L}` at its scale. -/
def Step1Raw : Prop :=
  (∀ K, X.TypeOccurs K → ∀ ℓ ∈ X.gateKeys K,
    X.baseLaw.pr (fun b => X.step1Fail b ℓ K.1.1 (X.p.typeSegs n K)) ≤
      Real.exp (-(X.p.delta * (X.p.q0 * X.p.typeSegs n K)))) ∧
  ∀ ℓ, X.KeyOccurs ℓ →
    X.baseLaw.pr (fun b => X.capFail b ℓ) ≤ Real.exp (-(X.p.delta * (X.p.q0 * X.p.uSeg n (ℓ.level + 1))))

/-- L5.1c (05:192–217): Step 1 for the raw parent-and-stream experiment.  Off a raw event of probability
`e^{-δu}` the prefix-deleted posterior controls `π_ℓ` within `e^{a₁ u}`, and the prior cap holds once the cap
constant `K'` is large. -/
theorem L5_1c : ∃ R : ParamReq5, ∀ p : Params5 γ K' χ, R.Holds p → ∃ n₀ : ℕ, ∀ n ≥ n₀,
    ∀ (N : ℕ) (E : Fin N → Fin N → Prop) (G : Colour) (X : Setup5 γ K' χ n N E G), X.p = p →
      X.Step1Raw := by
  sorry

/-- The conclusion of Step 2 (05:242–259): each Step 2 failure (intersected with the true-block gate) has
raw probability at most its thresholds. -/
def Step2Raw : Prop :=
  (∀ K, X.TypeOccurs K → X.keyLaw.pr (fun H => X.step2Fail H K) ≤
    ((K.2.1.card : ℝ) + 1) * Real.exp (-(X.p.delta * (X.p.q0 * X.p.typeSegs n K)))) ∧
  ∀ K t, X.OptOccurs K t → X.keyLaw.pr (fun H => X.optFail H K t) ≤
    Real.exp (-(X.p.delta * (X.p.q0 * X.p.uStarSeg n)))

/-- L5.1d, raw part (05:219–259): the subdensity calculation for the Step 2 tests. -/
theorem L5_1d : ∀ (n N : ℕ) (E : Fin N → Fin N → Prop) (G : Colour) (X : Setup5 γ K' χ n N E G),
    X.Step2Raw := by
  sorry

/-- Block-density bound `A_K = exp(K''(1 + Σ_S s_ℓ))` (05:263–268). -/
def blockConst (K : X.Ty) : ℝ :=
  Real.exp (X.p.Kpp * (1 + ∑ ℓ ∈ K.2.1, (colLen5 (X.p.s n) ℓ : ℝ)))

/-- The product reference law `R[u]` of a block (05:73–76). -/
def refBlock (K : X.Ty) (z : X.Block K) : ℝ := ∏ s, X.S.reference.w (z s)

/-- The deterministic Step 2 conclusions at a key history passing Step 1 and the Step 2 tests of a type
(05:260–286). -/
def Step2Bounds (H : X.KeyHist) (K : X.Ty) : Prop :=
  (∀ ℓ ∈ K.2.1, ∀ θ, Real.exp (-(X.p.delta * (X.p.q0 * X.p.typeSegs n K)) * colLen5 (X.p.s n) ℓ) *
        X.blockMass H K (K.2.1.erase ℓ) ≤ X.blockMass (X.withCol H ℓ θ) K K.2.1 →
      ∀ z, (X.blockLaw (X.withCol H ℓ θ) K).w z ≤
        Real.exp (X.p.a 2 * (X.p.q0 * X.p.typeSegs n K) * colLen5 (X.p.s n) ℓ) *
          (X.blockLawDel H K ℓ).w z) ∧
  (∀ z, (X.blockLaw H K).w z ≤ X.blockConst K ^ (X.p.q0 * X.p.typeSegs n K) * X.refBlock K z) ∧
  (∀ z, (X.blockLaw H K).w z ≠ 0 → ∀ ℓ ∈ K.2.1, ∀ h, X.BlockHits K z (H.2 ℓ h))

/-- L5.1d, deterministic part (05:260–270, 05:271–286): at a history with `V₀` in the parent support,
passing Step 1, and passing the Step 2 tests of an occurring type, the block law is within `e^{a₂ u s_ℓ}` of each
deleted law (also at replaced values passing their ratio test), within `A_K^u` of `R[u]`, and supported on
blocks that hit every listed column.  The coverage of L5.1e (every listed key reads the type's bin) is an
input. -/
theorem L5_1d_bounds : ∀ (n N : ℕ) (E : Fin N → Fin N → Prop) (G : Colour) (X : Setup5 γ K' χ n N E G),
    (∀ x : CubeVertex n, ∀ ℓ ∈ X.g.typeKeys (X.p.J n) x, (X.g.key x).1 ∈ binList5 ℓ.coarse) →
    ∀ H : X.KeyHist, H.1.1 ∈ X.P.lab0 → X.Step1Pass H.1 →
      ∀ K, X.TypeOccurs K → ¬ X.step2Fail H K → X.Step2Bounds H K := by
  sorry

/-- The Step 3 threshold of a record target: `e^{-c k'_j}` at low targets, `e^{-c s}` at high targets. -/
def step3Scale (c : ℝ) (ℓ : X.Key) : ℝ :=
  match ℓ with
  | .inl k => Real.exp (-(c * X.p.kPrime n k.2.2.val))
  | .inr _ => Real.exp (-(c * X.p.s n))

/-- The conclusion of the Step 3 one-target calculation (05:445–453): integrating the target over its prior
and the fresh arrays at the replaced value, each Step 3 failure costs at most its threshold, at every fixing
of the other keys. -/
def Step3Raw (cL cH : ℝ) : Prop :=
  ∀ H : X.KeyHist, ∀ r : X.AbsRecord, X.RecOccurs r →
    ∑ θ : Fin (colLen5 (X.p.s n) r.1) → Fin N,
      (∏ h, (X.prior H.1 r.1).w (θ h)) * X.step3Rate (X.withCol H r.1 θ) r ≤
        X.step3Scale (match r.1 with | .inl _ => cL | .inr _ => cH) r.1

/-- L5.1f, raw part (05:400–453), with the high-row path tests of L5.1g (05:494–566): fixed rates
`c_{L0}, c_{H0} > 0`, depending only on the constants fixed before `K₁`, for the Step 3 one-target exceptions —
the subdensity calculation for the lower and ratio tests, and at high targets the martingale concentration of
the clipped conditional costs over a finite grid of directions, which yields price feasibility (05:683–686:
increasing `K₂` or `K_s` does not decrease these rates). -/
theorem L5_1f : ∃ cL cH : Pre15 → ℝ, (∀ x, 0 < cL x ∧ 0 < cH x) ∧
    ∃ R : ParamReq5, ∀ p : Params5 γ K' χ, R.Holds p → ∃ n₀ : ℕ, ∀ n ≥ n₀,
      ∀ (N : ℕ) (E : Fin N → Fin N → Prop) (G : Colour) (X : Setup5 γ K' χ n N E G), X.p = p →
        X.Step3Raw (cL p.pre1) (cH p.pre1) := by
  sorry

/-! ### Record counts (05:331–398) -/

/-- The count of abstract records with a given target: logarithm `O(T log T + (j + 1) log m + T k_*)` (the last
term counts the reference subsets of the at most `T` pools and the mask, 05:368–371, 05:451–452). -/
def RecordCount (C : ℝ) : Prop :=
  ∀ ℓ : X.Key, ((Finset.univ.filter fun r : X.AbsRecord => X.RecOccurs r ∧ r.1 = ℓ).card : ℝ) ≤
    Real.exp (C * ((X.p.T n : ℝ) * Real.log (X.p.T n) + ((ℓ.level : ℝ) + 1) * Real.log (X.p.m n) +
      (X.p.T n : ℝ) * (X.p.q0 * X.p.uStarSeg n * X.p.usedBlocks n : ℕ)))

/-- L5.1e, count part (05:344–398): `O(T + j)` low tuples around a low state and `O(T + J)` high references
around a high state, generic variants sharing the ID list, the mask and reference subsets costing `O(k_*)`,
give the abstract record counts. -/
theorem L5_1e_count : ∃ C : ℝ, 0 < C ∧ ∀ p : Params5 γ K' χ, ∃ n₀ : ℕ, ∀ n ≥ n₀,
    ∀ (N : ℕ) (E : Fin N → Fin N → Prop) (G : Colour) (X : Setup5 γ K' χ n N E G), X.p = p →
      X.RecordCount C := by
  sorry

/-! ### Stage 1: the global parent (05:648–664) -/

/-- Parents at which every abstract Step 1 or Step 2 pattern has conditional failure probability at most
`e^{-δ L/2}` (times the number of tests at the pattern). -/
def Stage1Good (v : Fin N) : Prop :=
  (∀ K, X.TypeOccurs K → ∀ ℓ ∈ X.gateKeys K,
    (X.coarseLaw v).pr (fun c => X.step1Fail (v, c) ℓ K.1.1 (X.p.typeSegs n K)) ≤
      Real.exp (-(X.p.delta * (X.p.q0 * X.p.typeSegs n K)) / 2)) ∧
  (∀ ℓ, X.KeyOccurs ℓ → (X.coarseLaw v).pr (fun c => X.capFail (v, c) ℓ) ≤
      Real.exp (-(X.p.delta * (X.p.q0 * X.p.uSeg n (ℓ.level + 1))) / 2)) ∧
  (∀ K, X.TypeOccurs K → (X.keyLawAt v).pr (fun cu => X.step2Fail ((v, cu.1), cu.2) K) ≤
      ((K.2.1.card : ℝ) + 1) * Real.exp (-(X.p.delta * (X.p.q0 * X.p.typeSegs n K)) / 2)) ∧
  ∀ K t, X.OptOccurs K t → (X.keyLawAt v).pr (fun cu => X.optFail ((v, cu.1), cu.2) K t) ≤
      Real.exp (-(X.p.delta * (X.p.q0 * X.p.uStarSeg n)) / 2)

/-- L5.1h1 (05:648–664): Markov per pattern, and the pattern unions modulo bin and sign symmetry (bins are
iid given `V₀`; translating all signs preserves raw failure probabilities), exclude parent mass `o(1)`. -/
theorem L5_1h1 : ∃ R : ParamReq5, ∀ p : Params5 γ K' χ, R.Holds p → ∃ n₀ : ℕ, ∀ n ≥ n₀,
    ∀ (N : ℕ) (E : Fin N → Fin N → Prop) (G : Colour) (X : Setup5 γ K' χ n N E G), X.p = p →
      X.Step1Raw → X.Step2Raw → 99 / 100 ≤ X.P.prior.parent.pr X.Stage1Good := by
  sorry

/-! ### Stage 2: the coarse base (05:666–679) -/

/-- A function of the coarse base that reads only the bins in `B`. -/
def DependsOnBins (f : X.Coarse → ℝ) (B : Finset (BinVector5 n)) : Prop :=
  ∀ c c' : X.Coarse, (∀ w ∈ B, c.1 w = c'.1 w ∧ c.2 w = c'.2 w) → f c = f c'

/-- The Stage 2 conclusions at a selected parent `v`: the coarse-base law passes Step 1, bounds every averaged
Step 2 failure by `e^{-δL/4}`, and costs at most a factor `2` per bin against the raw bin law for functions of
boundedly many bins (the local-lemma comparison used in 05:1016–1023). -/
def Stage2Law (v : Fin N) (ν : FinProb X.Coarse) : Prop :=
  (∀ c, ν.w c ≠ 0 → X.Step1Pass (v, c)) ∧
  (∀ c, ν.w c ≠ 0 → ∀ K, X.TypeOccurs K →
    (X.hiddenLaw (v, c)).pr (fun U => X.step2Fail ((v, c), U) K) ≤
      ((K.2.1.card : ℝ) + 1) * Real.exp (-(X.p.delta * (X.p.q0 * X.p.typeSegs n K)) / 4)) ∧
  (∀ c, ν.w c ≠ 0 → ∀ K t, X.OptOccurs K t →
    (X.hiddenLaw (v, c)).pr (fun U => X.optFail ((v, c), U) K t) ≤
      Real.exp (-(X.p.delta * (X.p.q0 * X.p.uStarSeg n)) / 4)) ∧
  ∀ (B : Finset (BinVector5 n)) (f : X.Coarse → ℝ), (∀ c, 0 ≤ f c) → X.DependsOnBins f B →
    ν.expect f ≤ 2 ^ B.card * (X.coarseLaw v).expect f

/-- L5.1h2 (05:666–679): given a Stage 1 parent, exclude Step 1 failures and the Step 2 alarms (Markov from
Stage 1); bounded-degree grouping by bin and the conditional avoidance lemma with charges `o(1)`. -/
theorem L5_1h2 : ∃ R : ParamReq5, ∀ p : Params5 γ K' χ, R.Holds p → ∃ n₀ : ℕ, ∀ n ≥ n₀,
    ∀ (N : ℕ) (E : Fin N → Fin N → Prop) (G : Colour) (X : Setup5 γ K' χ n N E G), X.p = p →
      ∀ v, X.Stage1Good v → ∃ ν : FinProb X.Coarse, X.Stage2Law v ν := by
  sorry

/-! ### History odd loads, first part (05:1007–1025) -/

/-- The average over odd roles of `N π_{ℓ(b)}(y)`, with weight zero at high roles. -/
def avgLowPrior (b : X.Base) (y : Fin N) : ℝ :=
  (Fintype.card (OddRole5 n) : ℝ)⁻¹ *
    ∑ r : OddRole5 n, if X.g.low (X.p.J n) r.1 then (N : ℝ) * (X.prior b (X.g.roleKey (X.p.J n) r.1)).w y
      else 0

/-- L5.1l(1) (05:1007–1025): under the Stage 2 law, the low odd-role averages of `N π_ℓ` are bounded at every
label with probability `1 - o(1)`: boundary and `j ≥ 1` roles by rarity and the caps, interior `j = 0` roles by
scattered moments (same-bin pairs are rare; distinct bins cost a factor `2` each against the raw bin law, whose
mean posterior is the bounded partner prior), then Markov and the label union. -/
theorem L5_1l1 : ∃ C : ℝ, 0 < C ∧ ∃ R : ParamReq5, ∀ p : Params5 γ K' χ, R.Holds p →
    ∃ n₀ : ℕ, ∀ n ≥ n₀, ∀ (N : ℕ) (E : Fin N → Fin N → Prop) (G : Colour) (X : Setup5 γ K' χ n N E G),
      X.p = p → ChunkEstimates5 X.g → N ≤ n * 2 ^ n →
        ∀ v (ν : FinProb X.Coarse), X.Stage2Law v ν →
          ν.pr (fun c => ∃ y, C < X.avgLowPrior (v, c) y) ≤ 1 / 100 := by
  sorry

/-! ### Stage 3: the high keys (05:681–702) -/

/-- Low key indices. -/
abbrev LowIdx := CoarseKey5 n × CubeVertex (X.p.m n) × Fin (X.p.J n + 1)

/-- Values of the high hidden columns. -/
abbrev HighHid := ∀ i : CoarseKey5 n, Fin (X.p.s n) → Fin N

/-- Values of the low hidden columns. -/
abbrev LowHid := ∀ k : X.LowIdx, Fin 1 → Fin N

/-- Assemble all hidden columns from the high and the low values. -/
def joinHidden (hi : X.HighHid) (lo : X.LowHid) : X.Hidden := fun ℓ =>
  match ℓ with
  | .inl k => lo k
  | .inr i => hi i

/-- The raw law of the high keys at a base. -/
def highLaw (b : X.Base) : FinProb X.HighHid :=
  FinProb.pi fun i => FinProb.pi fun _ => X.prior b (.inr i)

/-- The product law of the low keys with coordinate laws `π`. -/
def lowLawOf (π : X.LowIdx → Law N) : FinProb X.LowHid :=
  FinProb.pi fun k => FinProb.pi fun _ => π k

/-- The raw law of the low keys at a base. -/
def lowLaw (b : X.Base) : FinProb X.LowHid := X.lowLawOf fun k => X.prior b (.inl k)

/-- A type whose list has only high keys (05:691). -/
def HighOnly (K : X.Ty) : Prop := ∀ ℓ ∈ K.2.1, ∃ i, ℓ = .inr i

/-- The Stage 3 conclusions at a base: high-only Step 2 tests pass; the other Step 2 tests, averaged over the
raw low keys, fail with probability at most `e^{-δL/8}`; every high Step 3 failure, averaged over the low keys
and fresh arrays, is at most `e^{-c_{H0} s/2}`. -/
def Stage3Law (b : X.Base) (ν : FinProb X.HighHid) (cH : ℝ) : Prop :=
  (∀ hi, ν.w hi ≠ 0 → ∀ K, X.TypeOccurs K → X.HighOnly K → ∀ lo, ¬ X.step2Fail (b, X.joinHidden hi lo) K) ∧
  (∀ hi, ν.w hi ≠ 0 → ∀ K, X.TypeOccurs K → ¬ X.HighOnly K →
    (X.lowLaw b).pr (fun lo => X.step2Fail (b, X.joinHidden hi lo) K) ≤
      ((K.2.1.card : ℝ) + 1) * Real.exp (-(X.p.delta * (X.p.q0 * X.p.typeSegs n K)) / 8)) ∧
  (∀ hi, ν.w hi ≠ 0 → ∀ K t, X.OptOccurs K t →
    (X.lowLaw b).pr (fun lo => X.optFail (b, X.joinHidden hi lo) K t) ≤
      Real.exp (-(X.p.delta * (X.p.q0 * X.p.uStarSeg n)) / 8)) ∧
  ∀ hi, ν.w hi ≠ 0 → ∀ r : X.AbsRecord, X.RecOccurs r → (∃ i, r.1 = .inr i) →
    (X.lowLaw b).expect (fun lo => X.step3Rate (b, X.joinHidden hi lo) r) ≤
      Real.exp (-(cH * X.p.s n) / 2)

/-- L5.1h3 (05:681–702): given a Stage 2 base, restrict the high keys: Markov from Stage 2 and from the high
Step 3 one-target bound, abstract count `exp(O(T log T + J log m))` beaten by `e^{-c_{H0}s/2}` once `K_s` is large,
bounded-degree grouping by bin, and the conditional avoidance lemma. -/
theorem L5_1h3 : ∀ (C : ℝ) (cL cH : Pre15 → ℝ), (∀ x, 0 < cL x ∧ 0 < cH x) →
    ∃ R : ParamReq5, ∀ p : Params5 γ K' χ, R.Holds p → ∃ n₀ : ℕ, ∀ n ≥ n₀,
      ∀ (N : ℕ) (E : Fin N → Fin N → Prop) (G : Colour) (X : Setup5 γ K' χ n N E G), X.p = p →
        X.RecordCount C → X.Step3Raw (cL p.pre1) (cH p.pre1) →
        ∀ v c, X.Step1Pass (v, c) →
          (∀ K, X.TypeOccurs K → (X.hiddenLaw (v, c)).pr (fun U => X.step2Fail ((v, c), U) K) ≤
            ((K.2.1.card : ℝ) + 1) * Real.exp (-(X.p.delta * (X.p.q0 * X.p.typeSegs n K)) / 4)) →
          (∀ K t, X.OptOccurs K t → (X.hiddenLaw (v, c)).pr (fun U => X.optFail ((v, c), U) K t) ≤
            Real.exp (-(X.p.delta * (X.p.q0 * X.p.uStarSeg n)) / 4)) →
          ∃ ν : FinProb X.HighHid, X.Stage3Law (v, c) ν (cH p.pre1) := by
  sorry

/-! ### Stage 4: separate optional pretrims (05:704–721) -/

/-- The Stage 4 conclusions: each low key gets a trimmed coordinate law with density at most `2` against
`π_ℓ`, supported on values passing every optional small-prefix test in which it is the optional key. -/
def Stage4Laws (b : X.Base) (hi : X.HighHid) (tr : X.LowIdx → Law N) : Prop :=
  (∀ k y, (tr k).w y ≤ 2 * (X.prior b (.inl k)).w y) ∧
  ∀ k y, (tr k).w y ≠ 0 → ∀ K t, X.OptOccurs K t → X.optKeyOf K t = .inl k →
    ∀ lo : X.LowHid, lo k = (fun _ => y) → ¬ X.optFail (b, X.joinHidden hi lo) K t

/-- L5.1h4 (05:704–721): each low key is the optional key of boundedly many patterns, each failing with
probability `o(1)` by Stage 3, so conditioning each key separately costs a density factor `1 + o(1) ≤ 2`. -/
theorem L5_1h4 : ∃ R : ParamReq5, ∀ p : Params5 γ K' χ, R.Holds p → ∃ n₀ : ℕ, ∀ n ≥ n₀,
    ∀ (N : ℕ) (E : Fin N → Fin N → Prop) (G : Colour) (X : Setup5 γ K' χ n N E G), X.p = p →
      ∀ b hi, (∀ K t, X.OptOccurs K t →
          (X.lowLaw b).pr (fun lo => X.optFail (b, X.joinHidden hi lo) K t) ≤
            Real.exp (-(X.p.delta * (X.p.q0 * X.p.uStarSeg n)) / 8)) →
        ∃ tr, X.Stage4Laws b hi tr := by
  sorry

/-! ### Stage 5: the low keys (05:723–744) -/

/-- Resample the low keys in `Λ` from the trimmed laws, keeping the others at `lo`. -/
def resampleLow (tr : X.LowIdx → Law N) (Λ : Finset X.LowIdx) (lo : X.LowHid) : FinProb X.LowHid :=
  FinProb.pi fun k => if k ∈ Λ then FinProb.pi (fun _ => tr k) else FinProb.dirac5 (lo k)

/-- The Stage 5 conclusions: every Step 2 test passes; Step 3 conditional array-failure bounds
`e^{-c_{L0} k'_j / 4}` (low) and `e^{-c_{H0} s / 6}` (high); and dropping the constraints touching a set `Λ` of
low keys costs a factor `2` per key against resampling them from the trimmed laws (05:1031–1035). -/
def Stage5Law (b : X.Base) (hi : X.HighHid) (tr : X.LowIdx → Law N) (ν : FinProb X.LowHid)
    (cL cH : ℝ) : Prop :=
  (∀ lo, ν.w lo ≠ 0 → X.Step2Pass (b, X.joinHidden hi lo)) ∧
  (∀ lo, ν.w lo ≠ 0 → ∀ r : X.AbsRecord, X.RecOccurs r →
    X.step3Rate (b, X.joinHidden hi lo) r ≤
      X.step3Scale (match r.1 with | .inl _ => cL / 4 | .inr _ => cH / 6) r.1) ∧
  ∀ (Λ : Finset X.LowIdx) (W : X.LowHid → ℝ) (M : ℝ), (∀ lo, 0 ≤ W lo) →
    (∀ lo, (X.resampleLow tr Λ lo).expect W ≤ M) → ν.expect W ≤ 2 ^ Λ.card * M

/-- L5.1h5 (05:723–744): from the product of the trimmed laws exclude the remaining Step 2 failures and the
Step 3 alarms (Markov from the one-target bound and Stage 3); grouping by central sign, bin and severity gives
polynomial dependency, and the pattern unions give charges `m^{-K_deg}` once `K₁, K₂, K_s` are large. -/
theorem L5_1h5 : ∀ (C : ℝ) (cL cH : Pre15 → ℝ), (∀ x, 0 < cL x ∧ 0 < cH x) →
    ∃ R : ParamReq5, ∀ p : Params5 γ K' χ, R.Holds p → ∃ n₀ : ℕ, ∀ n ≥ n₀,
      ∀ (N : ℕ) (E : Fin N → Fin N → Prop) (G : Colour) (X : Setup5 γ K' χ n N E G), X.p = p →
        X.RecordCount C → X.Step3Raw (cL p.pre1) (cH p.pre1) →
        ∀ b hi (ν₃ : FinProb X.HighHid), X.Stage3Law b ν₃ (cH p.pre1) → ν₃.w hi ≠ 0 →
          ∀ tr, X.Stage4Laws b hi tr →
            ∃ ν : FinProb X.LowHid, X.Stage5Law b hi tr ν (cL p.pre1) (cH p.pre1) := by
  sorry

/-! ### History odd loads, second part (05:1027–1041) -/

/-- The low index of a key (a fixed default at high keys). -/
def lowIdxOf (ℓ : X.Key) : X.LowIdx :=
  match ℓ with
  | .inl k => k
  | .inr _ => default

/-- The data a proxy-mean functional must provide at a fixed base and high history (05:1030–1037, 05:988–1001):
nonnegative, zero at high roles, capped by `e^{D_L}`; reading low keys only within sign distance
`C_loc √m` of the target; and with the one-target proxy bound `2 N π_ℓ(y)` at every fixing of the other low
keys. -/
structure ProxyMeanData5 (b : X.Base) (hi : X.HighHid) (Z : X.LowHid → OddRole5 n → Fin N → ℝ) : Prop where
  nonneg : ∀ lo r y, 0 ≤ Z lo r y
  high_zero : ∀ lo r y, ¬ X.g.low (X.p.J n) r.1 → Z lo r y = 0
  cap : ∀ lo r y, Z lo r y ≤ Real.exp (X.p.DL n)
  locality : ∃ Cloc : ℕ, ∀ r, FinProb.DependsOn (fun lo => Z lo r)
    (Finset.univ.filter fun k : X.LowIdx =>
      hammingDist k.2.1 (X.g.sign r.1) ≤ Cloc * Nat.sqrt (X.p.m n))
  one_target : ∀ lo r y, X.g.low (X.p.J n) r.1 →
    ∑ y', (X.prior b (X.g.roleKey (X.p.J n) r.1)).w y' *
        Z (Function.update lo (X.lowIdxOf (X.g.roleKey (X.p.J n) r.1)) (fun _ => y')) r y ≤
      2 * (N : ℝ) * (X.prior b (X.g.roleKey (X.p.J n) r.1)).w y

/-- L5.1l(2) (05:1027–1041): under the Stage 5 law, the odd-role averages of a proxy-mean functional are bounded
at every label with probability `1 - o(1)`: near rows (sign distance `O(√m)`) are a `2^{-m+o(m)}` fraction, the
comparison costs `2^n`, separated targets are resampled independently from the trimmed laws with the
one-target bound, and the averages of `N π_ℓ` are bounded by the first part. -/
theorem L5_1l2 : ∀ C₁ : ℝ, 0 < C₁ → ∃ C₂ : ℝ, 0 < C₂ ∧ ∃ R : ParamReq5, ∀ p : Params5 γ K' χ, R.Holds p →
    ∃ n₀ : ℕ, ∀ n ≥ n₀, ∀ (N : ℕ) (E : Fin N → Fin N → Prop) (G : Colour) (X : Setup5 γ K' χ n N E G),
      X.p = p → ChunkEstimates5 X.g → N ≤ n * 2 ^ n →
        ∀ b hi tr (ν : FinProb X.LowHid) (cL cH : ℝ), X.Stage5Law b hi tr ν cL cH → X.Stage4Laws b hi tr →
          (∀ y, X.avgLowPrior b y ≤ C₁) →
          ∀ Z, X.ProxyMeanData5 b hi Z →
            ν.pr (fun lo => ∃ y, C₂ < (Fintype.card (OddRole5 n) : ℝ)⁻¹ * ∑ r, Z lo r y) ≤ 1 / 100 := by
  sorry

/-! ### The successful key history (05:742–744) -/

/-- A good key history (05:742–744): parent in the support, Steps 1 and 2 pass, and every occurring abstract
record has its conditional Step 3 failure bound over fresh arrays. -/
structure KeyGood5 (H : X.KeyHist) (cL cH : ℝ) : Prop where
  parent_mem : H.1.1 ∈ X.P.lab0
  step1 : X.Step1Pass H.1
  step2 : X.Step2Pass H
  step3 : ∀ r : X.AbsRecord, X.RecOccurs r →
    X.step3Rate H r ≤ X.step3Scale (match r.1 with | .inl _ => cL / 4 | .inr _ => cH / 6) r.1

/-- A successful key history: good, and the two history odd-load averages are bounded (the second for a given
proxy-mean functional) (05:1007–1041). -/
structure KeySuccess5 (H : X.KeyHist) (cL cH C : ℝ) (Zbar : X.KeyHist → OddRole5 n → Fin N → ℝ) : Prop where
  good : X.KeyGood5 H cL cH
  load_prior : ∀ y, X.avgLowPrior H.1 y ≤ C
  load_proxy : ∀ y, (Fintype.card (OddRole5 n) : ℝ)⁻¹ * ∑ r, Zbar H r y ≤ C

end Setup5

end

end HypercubeRamsey
