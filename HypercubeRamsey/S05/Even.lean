import HypercubeRamsey.S05.Even_sol_s05_even
import HypercubeRamsey.S05.Even_refs_sol_s05_even
import HypercubeRamsey.S05.Even_density_scales_sol_s05_even
import HypercubeRamsey.S05.Even_trunc_sol_s05_even
import HypercubeRamsey.S05.Even_test_clock_sol_s05_even
import HypercubeRamsey.S05.Even_test_scales_sol_s05_even
import HypercubeRamsey.S05.Stages_p_s05_h

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
  classical
  intro A P
  refine ⟨Lane_sol_s05_h1.stage1Request, ?_⟩
  intro p _
  obtain ⟨nA, hnA⟩ := Filter.eventually_atTop.mp (Lane_sol_s05_even.eventual_atom_exponent p A)
  obtain ⟨nP, hnP⟩ := Filter.eventually_atTop.mp (Lane_sol_s05_even.eventual_tail_threshold p P)
  refine ⟨max nA nP, ?_⟩
  intro n hn N E G X hp hNlow _ hcover L cL cH LR HR H ω hsucc
  obtain ⟨hn1, hm2, hA⟩ := hnA n ((le_max_left _ _).trans hn)
  obtain ⟨_, _, hP⟩ := hnP n ((le_max_right _ _).trans hn)
  rw [← hp] at hm2 hA hP
  obtain ⟨hs, hk⟩ := Lane_sol_s05_even.high_lengths_positive X.p n hm2
  have hD : 0 ≤ X.p.DH n := by
    unfold Params5.DH
    apply mul_nonneg (mul_nonneg X.p.hKD.le (Nat.cast_nonneg _))
    apply Real.log_nonneg
    exact_mod_cast (show 1 ≤ X.p.m n by omega)
  have hM : 0 ≤ X.p.DH n + Real.log 4 :=
    add_nonneg hD (Real.log_nonneg (by norm_num))
  have ha4 : 0 < X.p.a 4 := by
    have h04 := X.p.ha_order 0 4 (by decide)
    rw [X.p.ha0] at h04
    linarith
  have hbudget0 (v : EvenRole5 n) (b : OddRole5 n) (o : X.OddOut) :
      0 ≤ X.budgetCost HR H ω v b o := by
    unfold budgetCost
    split
    · split
      · exact Lane_sol_s05_even.highCost_nonneg X _ _ _ _ _ _
      · rfl
    · rfl
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro b x
    exact Lane_sol_s05_even.odd_atom_bound X LR HR H ω b
      (L.success_valid H ω hsucc b) A hn1 hm2 hNlow hA x
  · intro v b o
    refine ⟨hbudget0 v b o, ?_⟩
    unfold budgetCost
    split
    · split
      · exact Lane_sol_s05_even.highCost_upper X _ _ _ _ (HR.row H ω b)
          hs hD (HR.row_nonneg H ω b) (HR.row_cap H ω b) o
      · exact hM
    · exact hM
  · intro v b o hadj
    simp [budgetCost, hadj]
  · intro v
    have hpoint (b : OddRole5 n) :
        (X.oddRowFP LR HR H ω b).expect (X.budgetCost HR H ω v b) ≤
          if (cube n).Adj v.1 b.1 then X.p.a 4 * (X.kStarLen : ℝ) else 0 := by
      have hb := L.success_valid H ω hsucc b
      by_cases hadj : (cube n).Adj v.1 b.1
      · rw [if_pos hadj]
        by_cases hv : X.g.low (X.p.J n) v.1
        · simp only [budgetCost, hv, not_true_eq_false, and_false, false_and, if_false, FinProb.expect,
            mul_zero, Finset.sum_const_zero]
          positivity
        · by_cases hbl : X.g.low (X.p.J n) b.1
          · simp only [budgetCost, hbl, not_true_eq_false, and_false, if_false, FinProb.expect,
              mul_zero, Finset.sum_const_zero]
            positivity
          · cases hc : X.evenRefOf (L.elig H) H ω v with
            | none =>
                simp [budgetCost, hadj, hv, hbl, hc, FinProb.expect]
                positivity
            | some c =>
                have href := Lane_sol_s05_even.selected_ref_mem X H ω v b c (L.elig H)
                  hadj hv hbl (hcover v.1 b.1 hadj) hc
                have hcost := HR.row_cost H ω b hb hbl
                  (c.1, X.g.evenType (X.p.J n) v.1, c.2) href
                have hlen := Lane_sol_s05_even.high_ref_length_le X H ω v c (L.elig H) hv hc
                calc
                  _ = ∑ o, HR.row H ω b o * X.highCost H
                      (X.actualRecord (L.elig H) H ω b) (arraysOf ω)
                      (c.1, X.g.evenType (X.p.J n) v.1, c.2) (HR.row H ω b) o := by
                    simp [FinProb.expect, oddRowFP, hb, oddRow,
                      LR.row_high H ω b _ hbl, budgetCost, hadj, hv, hbl, hc]
                  _ ≤ X.p.a 4 * (X.refLen (X.g.evenType (X.p.J n) v.1) c.2 : ℝ) := hcost
                  _ ≤ X.p.a 4 * (X.kStarLen : ℝ) := by
                    apply mul_le_mul_of_nonneg_left _ ha4.le
                    exact_mod_cast hlen
      · simp [budgetCost, hadj, FinProb.expect]
    calc
      (∑ b, (X.oddRowFP LR HR H ω b).expect (X.budgetCost HR H ω v b)) ≤
          ∑ b : OddRole5 n, if (cube n).Adj v.1 b.1 then X.p.a 4 * (X.kStarLen : ℝ) else 0 :=
        Finset.sum_le_sum fun b _ => hpoint b
      _ = ((oddAdjSet5 v).card : ℝ) * (X.p.a 4 * (X.kStarLen : ℝ)) := by
        rw [← Finset.sum_filter]
        simp [oddAdjSet5]
      _ ≤ (n : ℝ) * (X.p.a 4 * (X.kStarLen : ℝ)) := by
        apply mul_le_mul_of_nonneg_right _ (by positivity)
        exact_mod_cast oddAdjSet5_card_le v
      _ = _ := by ring
  · exact mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right (X.p.ha_order 4 5 (by decide)).le (by positivity)) (by positivity)
  · exact Lane_sol_s05_even.tail_bound X.p P n X.kStarLen hn1 hm2 hk hP

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
  refine ⟨Lane_sol_s05_h1.stage1Request, ?_⟩
  intro p _
  obtain ⟨nB, hnB⟩ := Filter.eventually_atTop.mp (Lane_sol_s05_even.eventual_blockBound_threshold p)
  obtain ⟨nK, hnK⟩ := Filter.eventually_atTop.mp (Lane_sol_s05_even.eventual_ref_length_threshold p (12 / p.delta))
  refine ⟨max 301 (max nB nK), ?_⟩
  intro n hn N E G X hp _ _ L cL cH LR HR ES H _ J ε hε0 hε1 CF
  let oddDec : DecidableEq (OddRole5 n) := inferInstance
  classical
  letI : DecidableEq (OddRole5 n) := oddDec
  have hn301 : 301 ≤ n := (le_max_left _ _).trans hn
  obtain ⟨hn1, hm2, hB⟩ := hnB n ((le_max_left _ _).trans ((le_max_right _ _).trans hn))
  obtain ⟨_, hK⟩ := hnK n ((le_max_right _ _).trans ((le_max_right _ _).trans hn))
  rw [← hp] at hm2 hB hK
  have hblock := Lane_sol_s05_even.blockBound_le_dimension X hn1 hm2 hB
  let enter := fun ω : X.CΩ L.ht => L.success H ω ∧ X.OddLoadsOK LR HR H ω
  let event := fun (v : EvenRole5 n) (c : X.CRef L.ht) (a : X.CΩ L.ht × (OddRole5 n → X.OddOut)) =>
    enter a.1 ∧ X.evenRefOf (L.elig H) H a.1 v = some c ∧ ¬ X.EvenTest ES H a.1 v c a.2
  have hfixed (v : EvenRole5 n) (c : X.CRef L.ht) :
      (X.jointLaw H J).pr (event v c) ≤ 2 * Real.exp (-((12 : ℝ) * n)) := by
    by_cases hex : ∃ ω, X.evenRefOf (L.elig H) H ω v = some c
    · obtain ⟨ω₀, hc₀⟩ := hex
      have hlen : 12 / X.p.delta ≤ (X.refLen (X.g.evenType (X.p.J n) v.1) c.2 : ℝ) :=
        hK.trans (Lane_sol_s05_even.selected_ref_length_lower X H ω₀ (L.elig H) v c hc₀ hm2)
      have hδlen : 12 ≤ X.p.delta * (X.refLen (X.g.evenType (X.p.J n) v.1) c.2 : ℝ) := by
        have hh := (div_le_iff₀ X.p.hdelta.1).mp hlen
        nlinarith
      let S := star v
      letI : DecidableEq S := @Subtype.instDecidableEq _ _ oddDec
      let Idx := X.refIdx v c.2
      letI : DecidableEq Idx := @Subtype.instDecidableEq _ _ (instDecidableEqFin _)
      let o₀ : X.OddOut := (0, X.y₀)
      let ext := Lane_sol_s05_even.extendOutputs S o₀
      let replace := fun ω z => replaceRef (X := X) (h := L.ht) ω v c z
      let π := X.refLaw H v c.2
      let select := fun ω : X.CΩ L.ht => X.evenRefOf (L.elig H) H ω v = some c
      let gate := fun ω (d : S → X.OddOut) => ES.gate H v c ω (ext d)
      let F := fun ω (d : S → X.OddOut) =>
        if gate ω d then ∏ b ∈ S, X.oddRow LR HR H ω b (ext d b) else 0
      let Q := fun ω => FinProb.pi (fun b : S => ES.refQ H v c ω b.1)
      let eps := Real.exp (-(X.p.delta * (X.refLen (X.g.evenType (X.p.J n) v.1) c.2 : ℝ) * n))
      let m := fun ω d => ∑ z, π.w z * F (replace ω z) d
      have hreplaceEq (ω : X.CΩ L.ht) (z : X.RefVal v c.2) :
          replace ω z = Lane_sol_s05_even.replaceBlockData X ω c.1
            (X.g.evenType (X.p.J n) v.1) (X.refIdx v c.2) z := rfl
      have hresample (f : X.CΩ L.ht → ℝ) :
          (X.centreLaw L.ht H).expect (fun ω => π.expect (fun z => f (replace ω z))) =
            (X.centreLaw L.ht H).expect f := by
        simpa only [π, Setup5.refLaw, hreplaceEq] using
          Lane_sol_s05_even.centre_expect_resample X H c.1 (X.g.evenType (X.p.J n) v.1) (X.refIdx v c.2) f
      have hreplace (ω : X.CΩ L.ht) (z z' : X.RefVal v c.2) :
          replace (replace ω z) z' = replace ω z' := by
        simp only [hreplaceEq]
        exact Lane_sol_s05_even.replaceBlockData_twice X ω c.1
          (X.g.evenType (X.p.J n) v.1) (X.refIdx v c.2) z z'
      have hQ (ω : X.CΩ L.ht) (z : X.RefVal v c.2) : Q (replace ω z) = Q ω := by
        apply congrArg FinProb.pi
        funext b
        exact ES.refQ_invariant H v c ω z b.1
      have hmass (ω : X.CΩ L.ht) (d : S → X.OddOut) : m ω d = X.evenMass ES H ω v c (ext d) := by
        apply Finset.sum_congr rfl
        intro z _
        unfold evenWeight
        dsimp [F, gate]
        split_ifs <;> ring
      have hqweight (ω : X.CΩ L.ht) (d : S → X.OddOut) :
          (Q ω).w d = ∏ b ∈ S, (ES.refQ H v c ω b).w (ext d b) :=
        Lane_sol_s05_even.pi_query_weight S (ES.refQ H v c ω) o₀ d
      have hqproj (ω : X.CΩ L.ht) (O : OddRole5 n → X.OddOut) :
          (Q ω).w (fun b : S => O b.1) = ∏ b ∈ S, (ES.refQ H v c ω b).w (O b) := by
        rw [hqweight]
        apply Finset.prod_congr rfl
        intro b hb
        rw [show ext (fun b : S => O b.1) b = O b from Lane_sol_s05_even.extend_project S o₀ O b hb]
      have hmassproj (ω : X.CΩ L.ht) (O : OddRole5 n → X.OddOut) :
          m ω (fun b : S => O b.1) = X.evenMass ES H ω v c O := by
        rw [hmass]
        unfold evenMass
        apply Finset.sum_congr rfl
        intro z _
        unfold evenWeight
        have hg := ES.gate_outputs H v c (replace ω z) (ext (fun b : S => O b.1)) O
          (fun b hb => Lane_sol_s05_even.extend_project S o₀ O b hb)
        rw [propext hg]
        congr 1
        apply Finset.prod_congr rfl
        intro b hb
        rw [show ext (fun b : S => O b.1) b = O b from Lane_sol_s05_even.extend_project S o₀ O b hb]
      have htest (ω : X.CΩ L.ht) (O : OddRole5 n → X.OddOut) :
          (0 < m ω (fun b : S => O b.1) ∧ eps * (Q ω).w (fun b : S => O b.1) ≤ m ω (fun b : S => O b.1)) ↔
            X.EvenTest ES H ω v c O := by
        rw [hmassproj, hqproj]
        rfl
      have hS : S.card ≤ n ^ 2 := by
        have hh : S.card ≤ n := oddAdjSet5_card_le v
        exact hh.trans (by simpa [pow_two] using Nat.le_mul_self n)
      have hcompare (ω : X.CΩ L.ht) (he : enter ω) (d : S → X.OddOut) :
          (FinProb.map (J ω) (fun O (b : S) => O b.1)).w d ≤
            2 * ∏ b ∈ S, X.oddRow LR HR H ω b (ext d b) := by
        rw [Lane_sol_s05_even.query_weight S (J ω) o₀ d]
        have hh := CF.joint ω he.1 he.2 S (ext d) hS
        have hprod0 : 0 ≤ ∏ b ∈ S, X.oddRow LR HR H ω b (ext d b) :=
          Finset.prod_nonneg fun b _ => X.oddRow_nonneg LR HR H ω b _
        exact hh.trans (mul_le_mul_of_nonneg_right (by linarith) hprod0)
      have hgate (ω : X.CΩ L.ht) (he : enter ω) (hs : select ω) (O : OddRole5 n → X.OddOut)
          (hO : (J ω).w O ≠ 0) : gate ω (fun b : S => O b.1) := by
        have hb := CF.budgets ω he.1 he.2 O hO
        have hg := ES.gate_success H ω O he.1 hb v c hs
        exact (ES.gate_outputs H v c ω O (ext (fun b : S => O b.1))
          (fun b hb => (Lane_sol_s05_even.extend_project S o₀ O b hb).symm)).mp hg
      have hbound := Lane_sol_s05_even.clock_gated_resampling_bound S o₀ (X.centreLaw L.ht H) π J replace
        hresample hreplace (X.oddRow LR HR H) (X.oddRow_nonneg LR HR H) gate enter select F (fun _ _ => rfl)
        Q hQ hcompare hgate eps (Real.exp_pos _)
      change (X.jointLaw H J).pr (fun a => enter a.1 ∧ select a.1 ∧
        ¬ (0 < m a.1 (fun b : S => a.2 b.1) ∧ eps * (Q a.1).w (fun b : S => a.2 b.1) ≤
          m a.1 (fun b : S => a.2 b.1))) ≤ 2 * eps at hbound
      have hh : (X.jointLaw H J).pr (event v c) ≤ 2 * eps := by
        simpa only [htest, event, select] using hbound
      refine hh.trans (mul_le_mul_of_nonneg_left ?_ (by norm_num))
      dsimp [eps]
      apply Real.exp_le_exp.mpr
      have hnR : 0 ≤ (n : ℝ) := Nat.cast_nonneg n
      nlinarith
    · have hno (ω : X.CΩ L.ht) : X.evenRefOf (L.elig H) H ω v ≠ some c := fun h => hex ⟨ω, h⟩
      have hevent (a : X.CΩ L.ht × (OddRole5 n → X.OddOut)) : ¬ event v c a := by
        intro h
        exact hno a.1 h.2.1
      simp only [FinProb.pr, if_neg (hevent _), Finset.sum_const_zero]
      positivity
  have hevent : (fun a : X.CΩ L.ht × (OddRole5 n → X.OddOut) => enter a.1 ∧
      ∃ v c, X.evenRefOf (L.elig H) H a.1 v = some c ∧ ¬ X.EvenTest ES H a.1 v c a.2) =
      (fun a => ∃ i : EvenRole5 n × X.CRef L.ht, event i.1 i.2 a) := by
    funext a
    apply propext
    constructor
    · rintro ⟨he, v, c, hs, ht⟩
      exact ⟨(v, c), he, hs, ht⟩
    · rintro ⟨⟨v, c⟩, he, hs, ht⟩
      exact ⟨he, v, c, hs, ht⟩
  have hevent0 : (fun a : X.CΩ L.ht × (OddRole5 n → X.OddOut) =>
      L.success H a.1 ∧ X.OddLoadsOK LR HR H a.1 ∧ ∃ v c,
        X.evenRefOf (L.elig H) H a.1 v = some c ∧ ¬ X.EvenTest ES H a.1 v c a.2) =
      (fun a => enter a.1 ∧ ∃ v c,
        X.evenRefOf (L.elig H) H a.1 v = some c ∧ ¬ X.EvenTest ES H a.1 v c a.2) := by
    funext a
    apply propext
    simp only [enter, and_assoc]
  rw [hevent0, hevent]
  calc
    _ ≤ ∑ i : EvenRole5 n × X.CRef L.ht, (X.jointLaw H J).pr (event i.1 i.2) :=
      FinProb.pr_exists_le_sum5 _ _
    _ ≤ ∑ _i : EvenRole5 n × X.CRef L.ht, 2 * Real.exp (-((12 : ℝ) * n)) :=
      Finset.sum_le_sum fun i _ => hfixed i.1 i.2
    _ = (Fintype.card (EvenRole5 n) * Fintype.card (X.CRef L.ht) : ℕ) * (2 * Real.exp (-((12 : ℝ) * n))) := by simp
    _ ≤ (n : ℝ) ^ 3 * (2 : ℝ) ^ (7 * n) * (2 * Real.exp (-((12 : ℝ) * n))) := by
      apply mul_le_mul_of_nonneg_right _ (by positivity)
      exact_mod_cast Lane_sol_s05_even.reference_count_bound X L.ht hn301 hblock
    _ ≤ 1 / 100 := by
      simpa only [mul_one] using Lane_sol_s05_even.test_union_tail n hn301 12 1 (by norm_num)

set_option maxHeartbeats 800000 in
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
  classical
  refine ⟨Lane_sol_s05_h1.stage1Request, ?_⟩
  intro p _
  let Kmin := max 1 (4 * p.tau1 / Lane_sol_s05_even.truncGap p)
  obtain ⟨nD, hnD⟩ := Filter.eventually_atTop.mp (Lane_sol_s05_even.eventual_density_coefficient p)
  obtain ⟨nT, hnT⟩ := Filter.eventually_atTop.mp (Lane_sol_s05_even.eventual_trunc_threshold p)
  obtain ⟨nK, hnK⟩ := Filter.eventually_atTop.mp (Lane_sol_s05_even.eventual_ref_length_threshold p Kmin)
  refine ⟨max nD (max nT nK), ?_⟩
  intro n hn N E G X hp L cL cH LR HR ES H hStep ω O v c hc hgate htest
  obtain ⟨hn1, hm2, hmn, hD⟩ := hnD n ((le_max_left _ _).trans hn)
  obtain ⟨_, hnTlarge, hTsmall⟩ := hnT n ((le_max_left _ _).trans ((le_max_right _ _).trans hn))
  obtain ⟨_, hKlarge⟩ := hnK n ((le_max_right _ _).trans ((le_max_right _ _).trans hn))
  rw [← hp] at hm2 hmn hD hnTlarge hTsmall hKlarge
  have hMprops := Lane_sol_s05_even.selected_ref_props X H ω (L.elig H) v c hc
  have hIdxcard : (X.refIdx v c.2).card = c.2.card :=
    Lane_sol_s05_even.reference_indices_card X (X.g.evenType (X.p.J n) v.1) c.2 hMprops.1
  let I := X.refIdx v c.2
  letI : DecidableEq I := @Subtype.instDecidableEq _ _ (instDecidableEqFin _)
  let seg := X.p.typeSegs n (X.g.evenType (X.p.J n) v.1)
  let k := Fintype.card I * (seg * X.p.q0)
  have hlen : k = X.refLen (X.g.evenType (X.p.J n) v.1) c.2 := by
    simp [k, I, seg, Setup5.refLen, Fintype.card_coe, hIdxcard, Nat.mul_comm, Nat.mul_assoc]
  have hklower : Kmin ≤ (k : ℝ) := by
    rw [hlen]
    exact hKlarge.trans (Lane_sol_s05_even.selected_ref_length_lower X H ω (L.elig H) v c hc hm2)
  have hk1 : 1 ≤ k := by
    exact_mod_cast ((le_max_left _ _).trans hklower : (1 : ℝ) ≤ k)
  have hkR : 0 < (k : ℝ) := by exact_mod_cast (show 0 < k by omega)
  have hN : 0 < N := Fin.pos X.y₀
  have hNpow : 0 < (N : ℝ) ^ k := pow_pos (by exact_mod_cast hN) _
  have hw0 (z : X.RefVal v c.2) : 0 ≤ X.evenWeight ES H ω v c O z := by
    unfold evenWeight
    apply mul_nonneg
    · exact mul_nonneg ((X.refLaw H v c.2).nonneg z) (by split_ifs <;> norm_num)
    · exact Finset.prod_nonneg fun b _ => X.oddRow_nonneg LR HR H _ b (O b)
  let Pz : FinProb (X.RefVal v c.2) := {
    w z := X.evenWeight ES H ω v c O z / X.evenMass ES H ω v c O
    nonneg z := div_nonneg (hw0 z) htest.1.le
    sum_eq_one := by
      rw [← Finset.sum_div]
      change X.evenMass ES H ω v c O / X.evenMass ES H ω v c O = 1
      exact div_self htest.1.ne' }
  let e := Lane_sol_s05_even.arrayEquiv I seg X.p.q0 N
  let P := FinProb.map Pz e
  have hmarg (x : Fin N) : X.evenMarg ES H ω v c O x = averageCoordinateMarginal P x := by
    symm
    change averageCoordinateMarginal (FinProb.map Pz (Lane_sol_s05_even.arrayEquiv I seg X.p.q0 N)) x = _
    rw [Lane_sol_s05_even.array_marginal_count (I := I) (s := seg) (q := X.p.q0) Pz x]
    unfold evenMarg
    rw [← hlen]
    apply Finset.sum_congr rfl
    intro z _
    change Pz.w z * _ / (k : ℝ) = Pz.w z * (_ / (k : ℝ))
    ring
  have hlookup (z : X.RefVal v c.2) (i : X.refIdx v c.2) :
      arr (replaceRef (X := X) (h := L.ht) ω v c z) c.1 (X.g.evenType (X.p.J n) v.1) i.1 = z i := by
    funext s q
    simp [replaceRef, arr, i.2]
  have hPgate (z : X.RefVal v c.2) (hz : Pz.w z ≠ 0) :
      ES.gate H v c (replaceRef (X := X) (h := L.ht) ω v c z) O := by
    by_contra hg
    apply hz
    simp [Pz, evenWeight, hg]
  let d := X.p.Kpp * (1 + ∑ ℓ ∈ (X.g.evenType (X.p.J n) v.1).2.1, (colLen5 (X.p.s n) ℓ : ℝ))
  have hdsmall : d + (n : ℝ) ^ γ ≤ (X.p.tau0 - X.p.a 6 - X.p.delta) * n := by
    have hcoeff := Lane_sol_s05_even.block_coefficient_bound X v hn1 (by omega) hmn
    dsimp [d]
    linarith
  have hblock := hStep (X.g.evenType (X.p.J n) v.1) ⟨v.1, v.2, rfl⟩
  have hrawcap (z : X.RefVal v c.2) :
      (N : ℝ) ^ k * (X.refLaw H v c.2).w z ≤ Real.exp ((d + (n : ℝ) ^ γ) * k) := by
    have hh := Lane_sol_s05_even.product_density (I := I) (X.blockLaw H (X.g.evenType (X.p.J n) v.1))
      ((N : ℝ) ^ (X.p.q0 * seg)) (Real.exp ((d + (n : ℝ) ^ γ) * (X.p.q0 * seg : ℕ)))
      (by positivity) (Lane_sol_s05_even.block_density_uniform X H _ hblock) z
    have hpow : ((N : ℝ) ^ (X.p.q0 * seg)) ^ Fintype.card I = (N : ℝ) ^ k := by
      rw [← pow_mul]
      congr 1
      dsimp [k]
      ring
    have hexp : Real.exp ((d + (n : ℝ) ^ γ) * (X.p.q0 * seg : ℕ)) ^ Fintype.card I =
        Real.exp ((d + (n : ℝ) ^ γ) * k) := by
      rw [← Real.exp_nat_mul]
      congr 1
      dsimp [k]
      push_cast
      ring
    simpa only [hpow, hexp, I, Setup5.refLaw] using hh
  have hpostdom (z : X.RefVal v c.2) : Pz.w z ≤
      Real.exp ((X.p.a 6 + X.p.delta) * (k : ℝ) * n) * (X.refLaw H v c.2).w z := by
    by_cases hg : ES.gate H v c (replaceRef (X := X) (h := L.ht) ω v c z) O
    · have hcost := ES.cost_bound H v c (replaceRef (X := X) (h := L.ht) ω v c z) O hg
      simp only [ES.refQ_invariant H v c ω z, ← hlen] at hcost
      have hmass := htest.2
      rw [← hlen] at hmass
      have hmul := mul_le_mul_of_nonneg_left hmass
        (mul_nonneg (Real.exp_pos ((X.p.a 6 + X.p.delta) * (k : ℝ) * n)).le
          ((X.refLaw H v c.2).nonneg z))
      have heq : Real.exp ((X.p.a 6 + X.p.delta) * (k : ℝ) * n) *
          Real.exp (-(X.p.delta * (k : ℝ) * n)) = Real.exp (X.p.a 6 * (k : ℝ) * n) := by
        rw [← Real.exp_add]
        congr 1
        ring
      change X.evenWeight ES H ω v c O z / X.evenMass ES H ω v c O ≤ _
      apply (div_le_iff₀ htest.1).mpr
      unfold evenWeight
      rw [if_pos hg, mul_one]
      calc
        (X.refLaw H v c.2).w z * ∏ b ∈ star v,
            X.oddRow LR HR H (replaceRef (X := X) (h := L.ht) ω v c z) b (O b) ≤
            (X.refLaw H v c.2).w z * (Real.exp (X.p.a 6 * (k : ℝ) * n) *
              ∏ b ∈ star v, (ES.refQ H v c ω b).w (O b)) :=
          mul_le_mul_of_nonneg_left hcost ((X.refLaw H v c.2).nonneg z)
        _ = (Real.exp ((X.p.a 6 + X.p.delta) * (k : ℝ) * n) * (X.refLaw H v c.2).w z) *
            (Real.exp (-(X.p.delta * (k : ℝ) * n)) * ∏ b ∈ star v, (ES.refQ H v c ω b).w (O b)) := by
          rw [← heq]
          ring
        _ ≤ _ := hmul
    · simp [Pz, evenWeight, hg]
      exact mul_nonneg (Real.exp_pos _).le ((X.refLaw H v c.2).nonneg z)
  have hcap (z : Fin k → Fin N) : (N : ℝ) ^ k * P.w z ≤ Real.exp (X.p.tau0 * k * n) := by
    rw [show P.w z = Pz.w (e.symm z) from Lane_sol_s05_even.map_equiv_weight Pz e z]
    calc
      _ ≤ (N : ℝ) ^ k * (Real.exp ((X.p.a 6 + X.p.delta) * (k : ℝ) * n) *
          (X.refLaw H v c.2).w (e.symm z)) := mul_le_mul_of_nonneg_left (hpostdom _) hNpow.le
      _ = Real.exp ((X.p.a 6 + X.p.delta) * (k : ℝ) * n) *
          ((N : ℝ) ^ k * (X.refLaw H v c.2).w (e.symm z)) := by ring
      _ ≤ Real.exp ((X.p.a 6 + X.p.delta) * (k : ℝ) * n) *
          Real.exp ((d + (n : ℝ) ^ γ) * k) :=
        mul_le_mul_of_nonneg_left (hrawcap _) (Real.exp_pos _).le
      _ ≤ Real.exp (X.p.tau0 * k * n) := by
        rw [← Real.exp_add]
        apply Real.exp_le_exp.mpr
        have hh := mul_le_mul_of_nonneg_right hdsmall hkR.le
        nlinarith
  have hheavycount (z : X.RefVal v c.2) :
      (Finset.univ.filter fun a : I × Fin seg × Fin X.p.q0 =>
        X.PriorHeavy H (X.g.evenType (X.p.J n) v.1) (z a.1 a.2.1 a.2.2)).card =
        X.heavyCount H (replaceRef (X := X) (h := L.ht) ω v c z) v c := by
    have hh := Lane_sol_s05_even.count_array_subtype (X.refIdx v c.2)
      (fun i (a : Fin seg × Fin X.p.q0) => arr (replaceRef (X := X) (h := L.ht) ω v c z) c.1
        (X.g.evenType (X.p.J n) v.1) i a.1 a.2)
      (X.PriorHeavy H (X.g.evenType (X.p.J n) v.1))
    simp only [hlookup] at hh
    simpa only [I, seg, Setup5.refIdx, Setup5.heavyCount, Finset.mem_filter, Finset.mem_univ, true_and] using hh
  have hprior : (∑ x, if X.PriorHeavy H (X.g.evenType (X.p.J n) v.1) x then
      averageCoordinateMarginal P x else 0) ≤ X.p.nu0 := by
    rw [show P = FinProb.map Pz (Lane_sol_s05_even.arrayEquiv I seg X.p.q0 N) from rfl,
      Lane_sol_s05_even.array_set_count (I := I) (s := seg) (q := X.p.q0) Pz
        (X.PriorHeavy H (X.g.evenType (X.p.J n) v.1))]
    calc
      _ ≤ ∑ z, Pz.w z * X.p.nu0 := by
        apply Finset.sum_le_sum
        intro z _
        by_cases hz : Pz.w z = 0
        · simp [hz]
        · have hh := ES.gate_heavy H v c (replaceRef (X := X) (h := L.ht) ω v c z) O (hPgate z hz)
          rw [← hheavycount z, ← hlen] at hh
          apply (div_le_iff₀ hkR).mpr
          nlinarith [mul_le_mul_of_nonneg_left hh (Pz.nonneg z)]
      _ = X.p.nu0 := by rw [← Finset.sum_mul, Pz.sum_eq_one, one_mul]
  have hkT : 4 * X.p.tau1 / Lane_sol_s05_even.truncGap X.p ≤ (k : ℝ) := by
    have hh : 4 * p.tau1 / Lane_sol_s05_even.truncGap p ≤ (k : ℝ) :=
      (le_max_right _ _).trans hklower
    rw [← hp] at hh
    exact hh
  have hheavy := Lane_sol_s05_even.heavy_mass_bound X.p P hN (by omega) hn1 hkT hnTlarge hcap
  have hkeepmass : (1 - X.p.nu0 - X.p.nu1) / 2 ≤
      ∑ x, if X.EvenKeep ES H ω v c O x then X.evenMarg ES H ω v c O x else 0 := by
    have hh := Lane_sol_s05_even.kept_mass_lower P (by omega)
      (X.PriorHeavy H (X.g.evenType (X.p.J n) v.1)) (X.p.tau1 * n)
      X.p.nu0 X.p.nu1 (Real.exp (-(Lane_sol_s05_even.truncGap X.p * n / 2))) hprior hheavy
    simp only [← hmarg] at hh
    have hh' : 1 - X.p.nu0 - X.p.nu1 - Real.exp (-(Lane_sol_s05_even.truncGap X.p * n / 2)) ≤
        ∑ x, if X.EvenKeep ES H ω v c O x then X.evenMarg ES H ω v c O x else 0 := by
      convert hh using 1
      apply Finset.sum_congr rfl
      intro x _
      exact PToolsMisc.ite_decidable_irrel (X.EvenKeep ES H ω v c O x) _ _ _ _
    linarith
  have htol : 0 < (1 - X.p.nu0 - X.p.nu1) / 2 := by linarith [X.p.hnu1.2]
  have hroweq (x : Fin N) : X.evenRow ES H ω O v x =
      (if X.EvenKeep ES H ω v c O x then X.evenMarg ES H ω v c O x else 0) /
        ∑ y, if X.EvenKeep ES H ω v c O y then X.evenMarg ES H ω v c O y else 0 := by
    simp [evenRow, hc, hgate, htest]
  have hnorm := Lane_sol_s05_even.normalized_kept_row (X.evenMarg ES H ω v c O)
    (X.EvenKeep ES H ω v c O) (fun x => by rw [hmarg]; exact Lane_sol_s05_even.marginal_nonneg P x)
    ((1 - X.p.nu0 - X.p.nu1) / 2) (Real.exp (X.p.tau1 * n)) (N : ℝ)
    htol hkeepmass (fun x hx => hx.2) (Real.exp_pos _).le
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro x
    rw [hroweq]
    exact hnorm.1 x
  · simp_rw [hroweq]
    exact hnorm.2.1
  · intro x hx b hb
    by_contra hbad
    have hmarg0 : X.evenMarg ES H ω v c O x = 0 := by
      unfold evenMarg
      apply Finset.sum_eq_zero
      intro z _
      by_cases hz : Pz.w z = 0
      · change Pz.w z * _ = 0
        rw [hz, zero_mul]
      · have hg := hPgate z hz
        have hs := ES.gate_select H v c (replaceRef (X := X) (h := L.ht) ω v c z) O hg
        have hprod : (∏ b ∈ star v, X.oddRow LR HR H (replaceRef (X := X) (h := L.ht) ω v c z) b (O b)) ≠ 0 := by
          intro hzero
          apply hz
          simp [Pz, evenWeight, hzero]
        have hrow : X.oddRow LR HR H (replaceRef (X := X) (h := L.ht) ω v c z) b (O b) ≠ 0 :=
          (Finset.prod_ne_zero_iff.mp hprod) b hb
        have hsupport : ∀ z' ∈ X.refBlocks (replaceRef (X := X) (h := L.ht) ω v c z) v c,
            X.BlockHits (X.g.evenType (X.p.J n) v.1) z' (O b).2 := by
          have hvb : v ∈ evenNbrs b :=
            Finset.mem_filter.mpr ⟨Finset.mem_univ _, (Finset.mem_filter.mp hb).2⟩
          by_cases hlowzero : LR.row H (replaceRef (X := X) (h := L.ht) ω v c z) b (O b) = 0
          · apply HR.row_support H _ b (O b) _ v hvb c hs
            simpa [oddRow, hlowzero] using hrow
          · exact LR.row_support H _ b (O b) hlowzero v hvb c hs
        have hcount0 : (Finset.univ.filter fun a : X.refIdx v c.2 × Fin seg × Fin X.p.q0 =>
            z a.1 a.2.1 a.2.2 = x) = ∅ := by
          apply Finset.filter_eq_empty_iff.mpr
          intro a _ ha
          have hmem : z a.1 ∈ X.refBlocks (replaceRef (X := X) (h := L.ht) ω v c z) v c := by
            apply Finset.mem_image.mpr
            exact ⟨a.1.1, a.1.2, hlookup z a.1⟩
          have hhit := hsupport (z a.1) hmem a.2.1 a.2.2
          exact hbad (ha ▸ hhit)
        rw [hcount0]
        simp
    apply hx
    rw [hroweq, hmarg0]
    simp
  · intro x
    have hh := hnorm.2.2 x
    rw [← hroweq] at hh
    refine hh.trans ?_
    have hden : 0 < 1 - X.p.nu0 - X.p.nu1 := by linarith [X.p.hnu1.2]
    have heq : Real.exp (X.p.tau1 * n) / ((1 - X.p.nu0 - X.p.nu1) / 2) =
        2 / (1 - X.p.nu0 - X.p.nu1) * Real.exp (X.p.tau1 * n) := by
      field_simp
      <;> ring
    rw [heq]
    gcongr
    norm_num

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
