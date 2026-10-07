import HypercubeRamsey.S05.Clock

/-!
# L5.1n–o: even rows by deletion of primitive block values, comparison means, loads

For an even role `v` with selected reference `c` (05:1086–1207) the primitive block values `z` of `c` are
re-sampled from their raw law `P'_0`; every choice, extracted subset and odd kernel is recomputed at `z`.  The
sublikelihood of the neighbouring odd outputs is `F_z(y) = 1_E ∏_{b∼v} p_b(y_b)` with a local gate `E`, and it is
dominated by `e^{a₆ k n}` times a product reference `Q` independent of `z`.  The even row is the normalized
restriction of the posterior average coordinate marginal to labels that are neither prior-heavy nor in
`H₁ = {N μ̄ > e^{τ₁ n}}`.  Comparison means, separated-row factorization and scattered moments then bound the
even column sums (05:1209–1282).
-/

namespace HypercubeRamsey

open Classical OAI.HypercubeRamsey

set_option synthInstance.maxSize 4096

noncomputable section

variable {γ K' χ : ℝ}

namespace Setup5

variable {n N : ℕ} {E : Fin N → Fin N → Prop} {G : Colour} (X : Setup5 γ K' χ n N E G)

/-- The odd neighbours of an even role. -/
def star (v : EvenRole5 n) : Finset (OddRole5 n) :=
  Finset.univ.filter fun b : OddRole5 n => (cube n).Adj v.1 b.1

/-- Block indices of a reference in the array of the role's type. -/
def refIdx (v : EvenRole5 n) (M : Finset (Fin X.blockBound)) :
    Finset (Fin (X.p.typeBlocks n (X.g.evenType (X.p.J n) v.1))) :=
  Finset.univ.filter fun i => ∃ j ∈ M, X.blockIdx _ j = some i

/-- Primitive block values of a reference (05:1088–1094). -/
abbrev RefVal (v : EvenRole5 n) (M : Finset (Fin X.blockBound)) :=
  ∀ _i : X.refIdx v M, X.Block (X.g.evenType (X.p.J n) v.1)

/-- Their raw conditional law `P'_0`: independent `P_K`-blocks. -/
def refLaw (H : X.KeyHist) (v : EvenRole5 n) (M : Finset (Fin X.blockBound)) : FinProb (X.RefVal v M) :=
  FinProb.pi fun _ => X.blockLaw H _

variable {X}
variable {h : X.HeightChoice5}

/-- Replace the primitive block values of a reference. -/
def replaceRef (ω : X.CΩ h) (v : EvenRole5 n) (c : X.CRef h) (z : X.RefVal v c.2) : X.CΩ h :=
  Function.update ω c.1 ((ω c.1).1, (ω c.1).2.1, (ω c.1).2.2.1,
    Function.update (ω c.1).2.2.2 (X.g.evenType (X.p.J n) v.1) fun i =>
      if hi : i ∈ X.refIdx v c.2 then z ⟨i, hi⟩ else (ω c.1).2.2.2 _ i)

variable (X)

/-- Length `k_*` of a used high tuple, in labels. -/
def kStarLen : ℕ := X.p.q0 * X.p.uStarSeg n * X.p.usedBlocks n

/-- The high log cost of an output at a high even role (05:1066–1072): against the smoothed deletion
conditional of the role's reference in the odd role's record. -/
def budgetCost {L : X.CentreLayer5} (HR : X.HighRows5 L) (H : X.KeyHist) (ω : X.CΩ L.ht) (v : EvenRole5 n)
    (b : OddRole5 n) (o : X.OddOut) : ℝ :=
  if (cube n).Adj v.1 b.1 ∧ ¬ X.g.low (X.p.J n) v.1 ∧ ¬ X.g.low (X.p.J n) b.1 then
    match X.evenRefOf (L.elig H) H ω v with
    | some c => X.highCost H (X.actualRecord (L.elig H) H ω b) (arraysOf ω)
        (c.1, X.g.evenType (X.p.J n) v.1, c.2) (HR.row H ω b) o
    | none => 0
  else 0

/-- The imposed high budgets: at most `a₅ k_* n` at every even role (05:1072–1073). -/
def BudgetOK {L : X.CentreLayer5} (HR : X.HighRows5 L) (H : X.KeyHist) (ω : X.CΩ L.ht)
    (O : OddRole5 n → X.OddOut) : Prop :=
  ∀ v, ∑ b, X.budgetCost HR H ω v b (O b) ≤ X.p.a 5 * (X.kStarLen : ℝ) * n

/-- L5.1m, instance part (05:1063–1081): at a successful center outcome the odd rows have atoms
`e^{o(n)}/N ≤ n^{-A}` (`N ≥ 2^n`); the high log costs of each even role are nonnegative, at most `D_H + log 4`
(smoothing and the high-row cap), vanish off its star, and have total mean at most `a₄ k_* n` (the defining
property of the common high law at the role's reference, which is among the needed references by L5.1e);
and the concentration exponent `n k_*² / (D_H + O(1))² = n^{1 - .09α + o(1)}` beats any fixed power of `n`. -/
theorem L5_1m_inputs : ∀ A P : ℝ, ∃ R : ParamReq5, ∀ p : Params5 γ K' χ, R.Holds p → ∃ n₀ : ℕ, ∀ n ≥ n₀,
    ∀ (N : ℕ) (E : Fin N → Fin N → Prop) (G : Colour) (X : Setup5 γ K' χ n N E G), X.p = p →
      2 ^ n ≤ N → N ≤ n * 2 ^ n →
      (∀ x y : CubeVertex n, (cube n).Adj x y →
        X.g.roleKey (X.p.J n) y ∈ X.g.typeKeys (X.p.J n) x ∨
          X.g.optionalKey (X.p.J n) x = some (X.g.roleKey (X.p.J n) y)) →
      ∀ (L : X.CentreLayer5) (cL cH : ℝ) (LR : X.LowRows5 L cL cH) (HR : X.HighRows5 L) (H : X.KeyHist)
        (ω : X.CΩ L.ht), L.success H ω →
        (∀ b x, labMarg (X.oddRowFP LR HR H ω b) Prod.snd x ≤ (n : ℝ) ^ (-A)) ∧
        (∀ v b o, 0 ≤ X.budgetCost HR H ω v b o ∧ X.budgetCost HR H ω v b o ≤ X.p.DH n + Real.log 4) ∧
        (∀ v b o, ¬ (cube n).Adj v.1 b.1 → X.budgetCost HR H ω v b o = 0) ∧
        (∀ v, ∑ b, (X.oddRowFP LR HR H ω b).expect (X.budgetCost HR H ω v b) ≤
          X.p.a 4 * (X.kStarLen : ℝ) * n) ∧
        X.p.a 4 * (X.kStarLen : ℝ) * n ≤ X.p.a 5 * (X.kStarLen : ℝ) * n ∧
        Real.exp (-(2 * (X.p.a 5 * (X.kStarLen : ℝ) * n - X.p.a 4 * (X.kStarLen : ℝ) * n) ^ 2 /
          ((n : ℝ) * (X.p.DH n + Real.log 4) ^ 2))) ≤ (n : ℝ) ^ (-P) := by
  sorry

/-- The local gate `E` and the product reference `Q` (05:1096–1164).  `Q` is the uniform mixture over the
possible records of the deleted references at same-mode neighbours and uniform at opposite-mode neighbours,
hence independent of the primitive values `z`; on the gate the sublikelihood costs at most `e^{a₆ k n}` against
it.  The gate requires legitimate long-rule selection of `c` with its subset, valid neighbouring rows, legal
eligible sets on the long consultation domain, the prior-heavy bound and the high budget; it holds for the
actual reference on the global success event and is local to radius `r + slack`. -/
structure EvenSetup5 {L : X.CentreLayer5} {cL cH : ℝ} (LR : X.LowRows5 L cL cH) (HR : X.HighRows5 L) where
  gate : X.KeyHist → EvenRole5 n → X.CRef L.ht → X.CΩ L.ht → (OddRole5 n → X.OddOut) → Prop
  refQ : X.KeyHist → EvenRole5 n → X.CRef L.ht → X.CΩ L.ht → OddRole5 n → FinProb X.OddOut
  refQ_invariant : ∀ (H : X.KeyHist) (v : EvenRole5 n) (c : X.CRef L.ht) (ω : X.CΩ L.ht)
    (z : X.RefVal v c.2) (b : OddRole5 n),
    refQ H v c (replaceRef (X := X) (h := L.ht) ω v c z) b = refQ H v c ω b
  cost_bound : ∀ (H : X.KeyHist) (v : EvenRole5 n) (c : X.CRef L.ht) (ω : X.CΩ L.ht)
    (O : OddRole5 n → X.OddOut), gate H v c ω O →
    ∏ b ∈ star v, X.oddRow LR HR H ω b (O b) ≤
      Real.exp (X.p.a 6 * (X.refLen (X.g.evenType (X.p.J n) v.1) c.2 : ℝ) * n) *
        ∏ b ∈ star v, (refQ H v c ω b).w (O b)
  gate_select : ∀ (H : X.KeyHist) (v : EvenRole5 n) (c : X.CRef L.ht) (ω : X.CΩ L.ht)
    (O : OddRole5 n → X.OddOut), gate H v c ω O → X.evenRefOf (L.elig H) H ω v = some c
  gate_valid : ∀ (H : X.KeyHist) (v : EvenRole5 n) (c : X.CRef L.ht) (ω : X.CΩ L.ht)
    (O : OddRole5 n → X.OddOut), gate H v c ω O → ∀ b ∈ star v, L.valid H ω b
  gate_legal : ∀ (H : X.KeyHist) (v : EvenRole5 n) (c : X.CRef L.ht) (ω : X.CΩ L.ht)
    (O : OddRole5 n → X.OddOut), gate H v c ω O →
    L.ht.hp.Legal (pos ω) (L.elig H ω) (L.ht.hp.domBall (X.sites L.ht) (X.siteOf v) L.ht.hp.Rlong)
  gate_heavy : ∀ (H : X.KeyHist) (v : EvenRole5 n) (c : X.CRef L.ht) (ω : X.CΩ L.ht)
    (O : OddRole5 n → X.OddOut), gate H v c ω O →
    (X.heavyCount H ω v c : ℝ) ≤ X.p.nu0 * (X.refLen (X.g.evenType (X.p.J n) v.1) c.2 : ℝ)
  gate_success : ∀ (H : X.KeyHist) (ω : X.CΩ L.ht) (O : OddRole5 n → X.OddOut), L.success H ω →
    X.BudgetOK HR H ω O → ∀ (v : EvenRole5 n) (c : X.CRef L.ht),
      X.evenRefOf (L.elig H) H ω v = some c → gate H v c ω O
  gate_local : ∀ (H : X.KeyHist) (v : EvenRole5 n) (c : X.CRef L.ht) (O : OddRole5 n → X.OddOut),
    FinProb.DependsOn (fun ω : X.CΩ L.ht => gate H v c ω O)
      (X.scopeBall (h := L.ht) v.1 (L.ht.hp.r + L.slack + 8))
  gate_outputs : ∀ (H : X.KeyHist) (v : EvenRole5 n) (c : X.CRef L.ht) (ω : X.CΩ L.ht)
    (O O' : OddRole5 n → X.OddOut), (∀ b ∈ star v, O b = O' b) → (gate H v c ω O ↔ gate H v c ω O')
  refQ_local : ∀ (H : X.KeyHist) (v : EvenRole5 n) (c : X.CRef L.ht) (b : OddRole5 n),
    FinProb.DependsOn (fun ω : X.CΩ L.ht => refQ H v c ω b)
      (X.scopeBall (h := L.ht) v.1 (L.ht.hp.r + L.slack + 8))

/-- L5.1n, reference part (05:1103–1164): the gate and the product reference exist.  `Q` uses only retained
primitive data (the deleted components do not read `z`; extracted subsets are recomputed); the likelihood
cost splits into low same-mode neighbours (`e^{a₄ k}` times the actual deletion component, record count within
the reserved margin since `k'_j ≤ k`), high same-mode neighbours (the imposed budget `a₅ k n`, mixture cost
`O(T log n) = o(k_*)`) and `o(n^{.4})` opposite-mode neighbours costing `O(D_L + D_H)` each. -/
theorem L5_1n_setup : ∃ R : ParamReq5, ∀ p : Params5 γ K' χ, R.Holds p → ∃ n₀ : ℕ, ∀ n ≥ n₀,
    ∀ (N : ℕ) (E : Fin N → Fin N → Prop) (G : Colour) (X : Setup5 γ K' χ n N E G), X.p = p →
      ∀ (L : X.CentreLayer5) (cL cH : ℝ) (LR : X.LowRows5 L cL cH) (HR : X.HighRows5 L),
        Nonempty (X.EvenSetup5 LR HR) := by
  sorry

/-! ### The even row (05:1176–1207) -/

variable {L : X.CentreLayer5} {cL cH : ℝ} {LR : X.LowRows5 L cL cH} {HR : X.HighRows5 L}

/-- The joint weight of primitive values `z` and the actual odd outputs: `P'_0(z) F_z(O)`. -/
def evenWeight (ES : X.EvenSetup5 LR HR) (H : X.KeyHist) (ω : X.CΩ L.ht) (v : EvenRole5 n) (c : X.CRef L.ht)
    (O : OddRole5 n → X.OddOut) (z : X.RefVal v c.2) : ℝ :=
  (X.refLaw H v c.2).w z * (if ES.gate H v c (replaceRef (X := X) (h := L.ht) ω v c z) O then 1 else 0) *
    ∏ b ∈ star v, X.oddRow LR HR H (replaceRef (X := X) (h := L.ht) ω v c z) b (O b)

/-- `m_c(y) = ∫ F_z(y) dP'_0(z)`. -/
def evenMass (ES : X.EvenSetup5 LR HR) (H : X.KeyHist) (ω : X.CΩ L.ht) (v : EvenRole5 n) (c : X.CRef L.ht)
    (O : OddRole5 n → X.OddOut) : ℝ :=
  ∑ z, X.evenWeight ES H ω v c O z

/-- The test `m_c > 0` and `m_c ≥ e^{-δ k n} Q` (05:1166–1169). -/
def EvenTest (ES : X.EvenSetup5 LR HR) (H : X.KeyHist) (ω : X.CΩ L.ht) (v : EvenRole5 n) (c : X.CRef L.ht)
    (O : OddRole5 n → X.OddOut) : Prop :=
  0 < X.evenMass ES H ω v c O ∧
    Real.exp (-(X.p.delta * (X.refLen (X.g.evenType (X.p.J n) v.1) c.2 : ℝ) * n)) *
        ∏ b ∈ star v, (ES.refQ H v c ω b).w (O b) ≤ X.evenMass ES H ω v c O

/-- The average coordinate marginal `μ̄` of the posterior `F_z dP'_0 / m_c` (05:1181–1183). -/
def evenMarg (ES : X.EvenSetup5 LR HR) (H : X.KeyHist) (ω : X.CΩ L.ht) (v : EvenRole5 n) (c : X.CRef L.ht)
    (O : OddRole5 n → X.OddOut) (x : Fin N) : ℝ :=
  ∑ z, X.evenWeight ES H ω v c O z / X.evenMass ES H ω v c O *
    (((Finset.univ.filter fun e : X.refIdx v c.2 × Fin (X.p.typeSegs n (X.g.evenType (X.p.J n) v.1)) ×
        Fin X.p.q0 => z e.1 e.2.1 e.2.2 = x).card : ℝ) /
      (X.refLen (X.g.evenType (X.p.J n) v.1) c.2 : ℝ))

/-- Labels kept by the even row: not prior-heavy and outside `H₁ = {N μ̄ > e^{τ₁ n}}` (05:1185–1201). -/
def EvenKeep (ES : X.EvenSetup5 LR HR) (H : X.KeyHist) (ω : X.CΩ L.ht) (v : EvenRole5 n) (c : X.CRef L.ht)
    (O : OddRole5 n → X.OddOut) (x : Fin N) : Prop :=
  ¬ X.PriorHeavy H (X.g.evenType (X.p.J n) v.1) x ∧
    (N : ℝ) * X.evenMarg ES H ω v c O x ≤ Real.exp (X.p.tau1 * n)

/-- The even row: the normalized restriction at the actually selected reference, zero if the actual gate or
the test fails (05:1201–1207). -/
def evenRow (ES : X.EvenSetup5 LR HR) (H : X.KeyHist) (ω : X.CΩ L.ht) (O : OddRole5 n → X.OddOut)
    (v : EvenRole5 n) (x : Fin N) : ℝ :=
  match X.evenRefOf (L.elig H) H ω v with
  | some c =>
    if ES.gate H v c ω O ∧ X.EvenTest ES H ω v c O then
      (if X.EvenKeep ES H ω v c O x then X.evenMarg ES H ω v c O x else 0) /
        ∑ x', (if X.EvenKeep ES H ω v c O x' then X.evenMarg ES H ω v c O x' else 0)
    else 0
  | none => 0

/-- The joint law of the centers and the odd assignment drawn from a clock family. -/
def jointLaw (H : X.KeyHist) (J : X.CΩ L.ht → FinProb (OddRole5 n → X.OddOut)) :
    FinProb (X.CΩ L.ht × (OddRole5 n → X.OddOut)) :=
  FinProb.bind (X.centreLaw L.ht H) J

/-- A clock family at a key history: at every successful center outcome with the odd column bounds, a law on
odd assignments that is injective in labels, keeps the budgets, and is at most `(1 + ε)` times the product of the
odd rows on at most `n²` queried rows (the output of L5.1m). -/
structure ClockFamily5 (H : X.KeyHist) (J : X.CΩ L.ht → FinProb (OddRole5 n → X.OddOut)) (ε : ℝ) : Prop where
  injective : ∀ ω, L.success H ω → X.OddLoadsOK LR HR H ω → ∀ O, (J ω).w O ≠ 0 →
    Function.Injective fun b => (O b).2
  budgets : ∀ ω, L.success H ω → X.OddLoadsOK LR HR H ω → ∀ O, (J ω).w O ≠ 0 → X.BudgetOK HR H ω O
  joint : ∀ ω, L.success H ω → X.OddLoadsOK LR HR H ω → ∀ (S : Finset (OddRole5 n)) (o : OddRole5 n → X.OddOut),
    S.card ≤ n ^ 2 → (J ω).pr (fun O => ∀ b ∈ S, O b = o b) ≤ (1 + ε) * ∏ b ∈ S, X.oddRow LR HR H ω b (o b)

/-- L5.1n, test part (05:1166–1176): per `(v, c)` the exception to the test has probability at most
`(1 + o(1)) e^{-δ k n}` on the entering success event — compare the required outputs to product rows by the
clock bound, discard nonlocal success restrictions retaining the gate, and apply the gated posterior bound
under `P'_0`; the union over roles, IDs and subsets costs `exp(O(n) + O(k_*))`. -/
theorem L5_1n : ∃ R : ParamReq5, ∀ p : Params5 γ K' χ, R.Holds p → ∃ n₀ : ℕ, ∀ n ≥ n₀,
    ∀ (N : ℕ) (E : Fin N → Fin N → Prop) (G : Colour) (X : Setup5 γ K' χ n N E G), X.p = p →
      2 ^ n ≤ N → N ≤ n * 2 ^ n →
      ∀ (L : X.CentreLayer5) (cL cH : ℝ) (LR : X.LowRows5 L cL cH) (HR : X.HighRows5 L)
        (ES : X.EvenSetup5 LR HR) (H : X.KeyHist), X.KeyGood5 H cL cH →
        ∀ (J : X.CΩ L.ht → FinProb (OddRole5 n → X.OddOut)) (ε : ℝ), 0 ≤ ε → ε ≤ 1 →
          X.ClockFamily5 (LR := LR) (HR := HR) H J ε →
          (X.jointLaw H J).pr (fun ωO => L.success H ωO.1 ∧ X.OddLoadsOK LR HR H ωO.1 ∧
            ∃ v c, X.evenRefOf (L.elig H) H ωO.1 v = some c ∧ ¬ X.EvenTest ES H ωO.1 v c ωO.2) ≤ 1 / 100 := by
  sorry

/-- L5.1n, row part (05:1176–1207): on the gate and the test the posterior has density at most `e^{τ₀ k n}`
against product uniform (prior `k(log A_K + n^γ) = o(kn)`), so `μ̄(H₁) ≤ υ₁ + e^{-Ω(kn)}`; with the prior-heavy
bound the kept mass is at least `(1 - υ₀ - υ₁)/2`, and the even row is a probability law on the common
neighbourhood of the star with normalized cap `O(e^{τ₁ n})`. -/
theorem L5_1n_rows : ∃ R : ParamReq5, ∀ p : Params5 γ K' χ, R.Holds p → ∃ n₀ : ℕ, ∀ n ≥ n₀,
    ∀ (N : ℕ) (E : Fin N → Fin N → Prop) (G : Colour) (X : Setup5 γ K' χ n N E G), X.p = p →
      ∀ (L : X.CentreLayer5) (cL cH : ℝ) (LR : X.LowRows5 L cL cH) (HR : X.HighRows5 L)
        (ES : X.EvenSetup5 LR HR) (H : X.KeyHist), (∀ K, X.TypeOccurs K → X.Step2Bounds H K) →
        ∀ ω O v c, X.evenRefOf (L.elig H) H ω v = some c → ES.gate H v c ω O → X.EvenTest ES H ω v c O →
          (∀ x, 0 ≤ X.evenRow ES H ω O v x) ∧ (∑ x, X.evenRow ES H ω O v x = 1) ∧
          (∀ x, X.evenRow ES H ω O v x ≠ 0 → ∀ b ∈ star v, Hits E G x (O b).2) ∧
          (∀ x, (N : ℝ) * X.evenRow ES H ω O v x ≤
            4 / (1 - X.p.nu0 - X.p.nu1) * Real.exp (X.p.tau1 * n)) := by
  sorry

/-- The even column sums at every label are at most one. -/
def EvenLoadsOK (ES : X.EvenSetup5 LR HR) (H : X.KeyHist) (ω : X.CΩ L.ht) (O : OddRole5 n → X.OddOut) : Prop :=
  ∀ x, ∑ v : EvenRole5 n, X.evenRow ES H ω O v x ≤ 1

/-- L5.1o (05:1209–1282): the normalized comparison mean of the even row at a prior-light label is at most
`d_v = O(B_{K(v)} exp(O(k_* 1_{j(v) > J})))` — cancellation of the posterior denominator, the forced-center height
bounds (`3/λ` at level zero, `e^{-n^c}` above), presence sums `λ` per level, unselected marginal `P̄_K ≤ B_K/N`
and `exp(O(k_*))` high subsets — with average `O(1)` over even roles; separated rows (residual distance
`> 2(r + slack + 8)`) factor after the clock comparison on at most `n²` outputs; scattered moments with cap
`O(e^{τ₁ n})` and repeat cost `n e^{-n(log 2 - H(2ρ)) + o(n)} e^{τ₁ n} = o(1)` and the label union, with
`|A|/N ≤ 1/C₀`, bound every even column sum by one with probability `1 - o(1)`. -/
theorem L5_1o : ∃ R : ParamReq5, ∀ p : Params5 γ K' χ, R.Holds p →
    ∃ C₀ : ℝ, 0 < C₀ ∧ ∃ n₀ : ℕ, ∀ n ≥ n₀, ∀ (N : ℕ) (E : Fin N → Fin N → Prop) (G : Colour) (X : Setup5 γ K' χ n N E G),
      X.p = p → ChunkEstimates5 X.g → C₀ * 2 ^ n ≤ (N : ℝ) → N ≤ n * 2 ^ n →
      ∀ (L : X.CentreLayer5) (cL cH : ℝ) (LR : X.LowRows5 L cL cH) (HR : X.HighRows5 L)
        (ES : X.EvenSetup5 LR HR) (H : X.KeyHist), X.KeyGood5 H cL cH → (∀ K, X.TypeOccurs K → X.Step2Bounds H K) →
        ∀ (J : X.CΩ L.ht → FinProb (OddRole5 n → X.OddOut)) (ε : ℝ), 0 ≤ ε → ε ≤ 1 →
          X.ClockFamily5 (LR := LR) (HR := HR) H J ε →
          (X.jointLaw H J).pr (fun ωO => L.success H ωO.1 ∧ X.OddLoadsOK LR HR H ωO.1 ∧
            (∀ v c, X.evenRefOf (L.elig H) H ωO.1 v = some c → X.EvenTest ES H ωO.1 v c ωO.2) ∧
            ¬ X.EvenLoadsOK ES H ωO.1 ωO.2) ≤ 1 / 100 := by
  sorry

end Setup5

end

end HypercubeRamsey
