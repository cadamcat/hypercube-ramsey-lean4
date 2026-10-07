import HypercubeRamsey.S05.Experiment
import HypercubeRamsey.S05.History_q_s05_hist2
import HypercubeRamsey.S05.History_q_s05_hist1b
import HypercubeRamsey.S05.History_q_s05_h5l
import HypercubeRamsey.S05.History_sol_s05_h5l
import HypercubeRamsey.S05.Parent_sol_s05_h1

/-!
# L5.1c, d, f, h, l(1–2): raw test bounds and the five conditioning stages

Steps 1–3 bound the raw probability of each test failure (05:192–286, 05:400–470).  The five stages
(05:607–760) then restrict, in order, the parent `V₀`, the coarse base, the high keys, each low key separately,
and the low keys jointly; each stage restricts only its own variables at a fixed entering history.  The
conclusions of each stage are exactly the inputs of the next.  L5.1l(1–2) bound the history-level odd-load
averages under the stage laws (05:1003–1041).
-/

namespace HypercubeRamsey

open Classical Filter OAI.HypercubeRamsey
open scoped Topology

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

/-- L5.1d, deterministic part (05:260–270, 05:271–286): at a history with base data in the raw support,
passing Step 1, and passing the Step 2 tests of an occurring type, the block law is within `e^{a₂ u s_ℓ}` of each
deleted law (also at replaced values passing their ratio test), within `A_K^u` of `R[u]`, and supported on
blocks that hit every listed column.  The coverage of L5.1e (every listed key reads the type's bin) is an
input. -/
theorem L5_1d_bounds : ∀ (n N : ℕ) (E : Fin N → Fin N → Prop) (G : Colour) (X : Setup5 γ K' χ n N E G),
    (∀ x : CubeVertex n, ∀ ℓ ∈ X.g.typeKeys (X.p.J n) x, (X.g.key x).1 ∈ binList5 ℓ.coarse) →
    ∀ H : X.KeyHist, X.baseLaw.w H.1 ≠ 0 → X.Step1Pass H.1 →
      ∀ K, X.TypeOccurs K → ¬ X.step2Fail H K → X.Step2Bounds H K := by
  classical
  intro n N E G X hcover H hbase hpass K hType hnotFail
  have hgateTrue := HypercubeRamsey.Lane_q_s05_hist1b.blockGate_trueBlock_of_step1Pass
    X H K hType hpass
  let qu : ℝ := (X.p.q0 : ℝ) * X.p.typeSegs n K
  let sev : ℝ := ∑ ℓ ∈ K.2.1, (colLen5 (X.p.s n) ℓ : ℝ)
  have hmassLower : Real.exp (-(X.p.delta * qu) * sev) ≤ X.blockMass H K K.2.1 := by
    by_contra h
    have hlt : X.blockMass H K K.2.1 < Real.exp (-(X.p.delta * qu) * sev) := lt_of_not_ge h
    exact hnotFail ⟨hgateTrue, Or.inl (by simpa [qu, sev] using hlt)⟩
  have hmassPos : 0 < X.blockMass H K K.2.1 := by
    exact lt_of_lt_of_le (Real.exp_pos _) hmassLower
  refine ⟨?_, ?_, ?_⟩
  · intro ℓ hℓ θ hratio z
    let x : ℝ := ((X.p.q0 : ℝ) * X.p.typeSegs n K) * colLen5 (X.p.s n) ℓ
    let M : ℝ := X.blockMass (X.withCol H ℓ θ) K K.2.1
    let D : ℝ := X.blockMass H K (K.2.1.erase ℓ)
    let wrep : ℝ := X.blockWeight (X.withCol H ℓ θ) K K.2.1 z
    let wdel : ℝ := X.blockWeight H K (K.2.1.erase ℓ) z
    have hMassDom : X.blockMass H K K.2.1 ≤
        Real.exp (X.p.a 1 * x) * D := by
      have h := HypercubeRamsey.Lane_q_s05_hist1b.blockMass_withCol_le
        X H K ℓ (H.2 ℓ) hℓ
      simpa [Setup5.withCol, Function.update_self, D, x, mul_assoc] using h
    have hDNonneg : 0 ≤ D := by
      dsimp [D, Setup5.blockMass]
      apply Finset.sum_nonneg
      intro z hz
      exact HypercubeRamsey.Lane_q_s05_hist1b.blockWeight_nonneg
        X H K (K.2.1.erase ℓ) z
    have hDPos : 0 < D := by
      by_contra hD
      have hDzero : D = 0 := le_antisymm (le_of_not_gt hD) hDNonneg
      rw [hDzero] at hMassDom
      exact (not_le_of_gt hmassPos) (by simpa [hDzero] using hMassDom)
    have hratio' : Real.exp (-X.p.delta * x) * D ≤ M := by
      simpa [M, D, x, mul_assoc] using hratio
    have hMPos : 0 < M :=
      lt_of_lt_of_le (mul_pos (Real.exp_pos _) hDPos) hratio'
    have hLawRep : (X.blockLaw (X.withCol H ℓ θ) K).w z = wrep / M := by
      simpa [wrep, M, Setup5.blockLaw, Setup5.blockLawOn, Setup5.blockMass] using
        (HypercubeRamsey.Lane_q_s05_hist1b.normalize5_weight_eq_div_of_nonneg
          (f := fun z => X.blockWeight (X.withCol H ℓ θ) K K.2.1 z)
          (X.fallbackBlock K) z
          (fun z => HypercubeRamsey.Lane_q_s05_hist1b.blockWeight_nonneg
            X (X.withCol H ℓ θ) K K.2.1 z)
          (by simpa [M, Setup5.blockMass] using hMPos))
    have hLawDel : (X.blockLawDel H K ℓ).w z = wdel / D := by
      simpa [wdel, D, Setup5.blockLawDel, Setup5.blockLawOn, Setup5.blockMass] using
        (HypercubeRamsey.Lane_q_s05_hist1b.normalize5_weight_eq_div_of_nonneg
          (f := fun z => X.blockWeight H K (K.2.1.erase ℓ) z)
          (X.fallbackBlock K) z
          (fun z => HypercubeRamsey.Lane_q_s05_hist1b.blockWeight_nonneg
            X H K (K.2.1.erase ℓ) z)
          (by simpa [D, Setup5.blockMass] using hDPos))
    have hweight : wrep ≤ Real.exp (X.p.a 1 * x) * wdel := by
      simpa [wrep, wdel, x, mul_assoc] using
        (HypercubeRamsey.Lane_q_s05_hist1b.blockWeight_withCol_le X H K ℓ z θ hℓ)
    have hgap : X.p.a 1 + X.p.delta ≤ X.p.a 2 := by
      have horder := X.p.ha_order (1 : Fin 9) (2 : Fin 9) (by decide)
      have hdelta := X.p.hdelta_a (1 : Fin 9) (2 : Fin 9) (by decide)
      nlinarith
    have hx : 0 ≤ x := by dsimp [x]; positivity
    have hrate : Real.exp ((X.p.a 1 + X.p.delta) * x) ≤ Real.exp (X.p.a 2 * x) :=
      Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_right hgap hx)
    have hwdel : 0 ≤ wdel := by
      exact HypercubeRamsey.Lane_q_s05_hist1b.blockWeight_nonneg
        X H K (K.2.1.erase ℓ) z
    have hwratio : 0 ≤ wdel / D := div_nonneg hwdel hDPos.le
    have hcancel :
        Real.exp ((X.p.a 1 + X.p.delta) * x) * (wdel / D) *
          (Real.exp (-X.p.delta * x) * D) = Real.exp (X.p.a 1 * x) * wdel := by
      calc
        _ = Real.exp ((X.p.a 1 + X.p.delta) * x) * Real.exp (-X.p.delta * x) * wdel := by
          field_simp [ne_of_gt hDPos]
        _ = _ := by
          rw [← Real.exp_add]
          congr 1
          ring
    have hmiddle :
        Real.exp ((X.p.a 1 + X.p.delta) * x) * (wdel / D) *
          (Real.exp (-X.p.delta * x) * D) ≤
        Real.exp (X.p.a 2 * x) * (wdel / D) * M := by
      calc
        _ ≤ Real.exp (X.p.a 2 * x) * (wdel / D) *
            (Real.exp (-X.p.delta * x) * D) := by
              exact mul_le_mul_of_nonneg_right
                (mul_le_mul_of_nonneg_right hrate hwratio)
                (mul_nonneg (Real.exp_nonneg _) hDPos.le)
        _ ≤ _ := mul_le_mul_of_nonneg_left hratio'
          (mul_nonneg (Real.exp_nonneg _) hwratio)
    have hnorm : (Real.exp (X.p.a 1 * x) * wdel) / M ≤
        Real.exp (X.p.a 2 * x) * (wdel / D) := by
      apply (div_le_iff₀ hMPos).2
      calc
        Real.exp (X.p.a 1 * x) * wdel =
            Real.exp ((X.p.a 1 + X.p.delta) * x) * (wdel / D) *
              (Real.exp (-X.p.delta * x) * D) := hcancel.symm
        _ ≤ Real.exp (X.p.a 2 * x) * (wdel / D) * M := hmiddle
    rw [hLawRep, hLawDel]
    simpa [x, mul_assoc] using
      (div_le_div_of_nonneg_right hweight hMPos.le).trans hnorm
  · intro z
    have hLaw : (X.blockLaw H K).w z = X.blockWeight H K K.2.1 z /
        X.blockMass H K K.2.1 := by
      simpa [Setup5.blockLaw, Setup5.blockLawOn, Setup5.blockMass] using
        (HypercubeRamsey.Lane_q_s05_hist1b.normalize5_weight_eq_div_of_nonneg
          (f := fun z => X.blockWeight H K K.2.1 z) (X.fallbackBlock K) z
          (fun z => HypercubeRamsey.Lane_q_s05_hist1b.blockWeight_nonneg
            X H K K.2.1 z)
          (by simpa [Setup5.blockMass] using hmassPos))
    have hpoint := HypercubeRamsey.Lane_q_s05_hist1b.blockWeight_le_exp_refBlock X H K z
    have hK0 : X.p.a 0 ≤ X.p.Kpp :=
      le_trans (le_max_left _ _) X.p.hKpp_budget
    have hK1 : X.p.a 1 + X.p.delta ≤ X.p.Kpp :=
      le_trans (le_max_right _ _) X.p.hKpp_budget
    have hsev : 0 ≤ sev := by
      dsimp [sev]
      exact Finset.sum_nonneg fun ℓ hℓ => Nat.cast_nonneg _
    have hqu : 0 ≤ qu := by dsimp [qu]; positivity
    have harg : X.p.a 0 * qu + X.p.a 1 * qu * sev ≤
        X.p.Kpp * (1 + sev) * qu - X.p.delta * qu * sev := by
      have hcoeff : X.p.a 0 + X.p.a 1 * sev ≤ X.p.Kpp * (1 + sev) - X.p.delta * sev := by
        nlinarith [mul_nonneg (sub_nonneg.mpr hK0) hsev,
          mul_nonneg (sub_nonneg.mpr hK1) hsev]
      nlinarith [mul_le_mul_of_nonneg_right hcoeff hqu]
    have hexp : Real.exp (X.p.a 0 * qu + X.p.a 1 * qu * sev) ≤
        Real.exp (X.p.Kpp * (1 + sev) * qu - X.p.delta * qu * sev) :=
      Real.exp_le_exp.mpr harg
    have hrefNonneg : 0 ≤ ∏ s : Fin (X.p.typeSegs n K), X.S.reference.w (z s) :=
      Finset.prod_nonneg fun s hs => X.S.reference.nonneg (z s)
    have hblockConst : X.blockConst K ^ (X.p.q0 * X.p.typeSegs n K) =
        Real.exp (X.p.Kpp * (1 + sev) * qu) := by
      dsimp [Setup5.blockConst]
      rw [← Real.exp_nat_mul]
      congr 1
      dsimp [qu, sev]
      push_cast
      ring
    have hdenom : Real.exp (X.p.Kpp * (1 + sev) * qu) *
        (∏ s : Fin (X.p.typeSegs n K), X.S.reference.w (z s)) *
        Real.exp (-(X.p.delta * qu) * sev) ≤
          Real.exp (X.p.Kpp * (1 + sev) * qu) *
            (∏ s : Fin (X.p.typeSegs n K), X.S.reference.w (z s)) *
            X.blockMass H K K.2.1 := by
      exact mul_le_mul_of_nonneg_left hmassLower
        (mul_nonneg (Real.exp_nonneg _) hrefNonneg)
    have hcombine : Real.exp (X.p.a 0 * qu + X.p.a 1 * qu * sev) *
        (∏ s : Fin (X.p.typeSegs n K), X.S.reference.w (z s)) ≤
          Real.exp (X.p.Kpp * (1 + sev) * qu) *
            (∏ s : Fin (X.p.typeSegs n K), X.S.reference.w (z s)) *
            X.blockMass H K K.2.1 := by
      calc
        _ ≤ Real.exp (X.p.Kpp * (1 + sev) * qu - X.p.delta * qu * sev) *
            (∏ s : Fin (X.p.typeSegs n K), X.S.reference.w (z s)) :=
              mul_le_mul_of_nonneg_right hexp hrefNonneg
        _ = Real.exp (X.p.Kpp * (1 + sev) * qu) *
            (∏ s : Fin (X.p.typeSegs n K), X.S.reference.w (z s)) *
            Real.exp (-(X.p.delta * qu) * sev) := by
              calc
                _ = (Real.exp (X.p.Kpp * (1 + sev) * qu) *
                      Real.exp (-(X.p.delta * qu) * sev)) *
                      (∏ s : Fin (X.p.typeSegs n K), X.S.reference.w (z s)) := by
                        rw [show X.p.Kpp * (1 + sev) * qu - X.p.delta * qu * sev =
                          X.p.Kpp * (1 + sev) * qu + (-(X.p.delta * qu) * sev) by ring,
                          Real.exp_add]
                _ = _ := by ring
        _ ≤ _ := hdenom
    rw [hLaw]
    apply (div_le_iff₀ hmassPos).2
    rw [hblockConst]
    calc
      X.blockWeight H K K.2.1 z ≤
          Real.exp (X.p.a 0 * qu + X.p.a 1 * qu * sev) *
            (∏ s : Fin (X.p.typeSegs n K), X.S.reference.w (z s)) := by
              simpa [qu, sev] using hpoint
      _ ≤ _ := hcombine
  · intro z hz ℓ hℓ h
    have hLaw : (X.blockLaw H K).w z =
        X.blockWeight H K K.2.1 z / X.blockMass H K K.2.1 := by
      simpa [Setup5.blockLaw, Setup5.blockLawOn, Setup5.blockMass] using
        (HypercubeRamsey.Lane_q_s05_hist1b.normalize5_weight_eq_div_of_nonneg
          (f := fun z => X.blockWeight H K K.2.1 z) (X.fallbackBlock K) z
          (fun z => HypercubeRamsey.Lane_q_s05_hist1b.blockWeight_nonneg X H K K.2.1 z)
          (by simpa [Setup5.blockMass] using hmassPos))
    have hweightNe : X.blockWeight H K K.2.1 z ≠ 0 := by
      intro hzWeight
      apply hz
      rw [hLaw, hzWeight]
      simp
    have hweight := hweightNe
    unfold Setup5.blockWeight at hweight
    have hbaseGateNe : X.blockBase H.1 K z *
        (if X.blockGate H.1 K z then 1 else 0) ≠ 0 :=
      (mul_ne_zero_iff.mp hweight).1
    have hblockNe : X.blockBase H.1 K z ≠ 0 :=
      (mul_ne_zero_iff.mp hbaseGateNe).1
    have hlikprod : ∏ k ∈ K.2.1, X.colLik H.1 K k z (H.2 k) ≠ 0 :=
      (mul_ne_zero_iff.mp hweight).2
    have hlik : X.colLik H.1 K ℓ z (H.2 ℓ) ≠ 0 :=
      (Finset.prod_ne_zero_iff.mp hlikprod) ℓ hℓ
    have hlik' := hlik
    unfold Setup5.colLik at hlik'
    have hcoverBin : K.1.1 ∈ binList5 ℓ.coarse := by
      rcases hType with ⟨x, hx, hK⟩
      have hℓ' := hℓ
      rw [← hK] at hℓ'
      have hmem : ℓ ∈ X.g.typeKeys (X.p.J n) x := by
        simpa [ChunkGeometry5.evenType] using hℓ'
      rw [← hK]
      simpa [ChunkGeometry5.evenType] using hcover x ℓ hmem
    have hprefix := HypercubeRamsey.Lane_q_s05_hist1b.typeSegs_le_keyPrefix5
      X K hType ℓ hℓ
    intro s i
    have hratio : ratio5 ((X.priorRep H.1 ℓ K.1.1 z).w (H.2 ℓ h))
        ((X.priorDel H.1 ℓ K.1.1 (X.p.typeSegs n K)).w (H.2 ℓ h)) ≠ 0 :=
      (Finset.prod_ne_zero_iff.mp hlik') h (Finset.mem_univ _)
    have hrepLaw : (X.priorRep H.1 ℓ K.1.1 z).w (H.2 ℓ h) ≠ 0 := by
      by_cases hdel : (X.priorDel H.1 ℓ K.1.1 (X.p.typeSegs n K)).w (H.2 ℓ h) = 0
      · simp [ratio5, hdel] at hratio
      · have hdiv : (X.priorRep H.1 ℓ K.1.1 z).w (H.2 ℓ h) /
            (X.priorDel H.1 ℓ K.1.1 (X.p.typeSegs n K)).w (H.2 ℓ h) ≠ 0 := by
          simpa [ratio5, hdel] using hratio
        by_contra hnum
        apply hdiv
        simp [hnum]
    have hraw := HypercubeRamsey.Lane_q_s05_hist1b.priorRep_raw_nonzero5
      X H K ℓ z hbase hblockNe hcoverBin (H.2 ℓ h) hrepLaw
    by_cases hbnd : ℓ.coarse.2 = true
    · have hsegment := HypercubeRamsey.Lane_q_s05_hist1b.posterior_boundary_segment_nonzero5
        X H K ℓ z (H.2 ℓ h) hprefix hcoverBin hbnd hraw s
      have hrawBoundary := hraw
      simp [Setup5.colWeight, hbnd] at hrawBoundary
      have hparentNe : X.P.prior.parent.w (H.2 ℓ h) ≠ 0 := hrawBoundary.1
      have hparentMem : H.2 ℓ h ∈ X.P.lab0 := by
        by_contra hnot
        have hzero := X.P.lab0_atom (H.2 ℓ h) hnot
        exact hparentNe hzero
      have hterm := (Finset.prod_ne_zero_iff.mp hrawBoundary.2) K.1.1 hcoverBin
      have hpartnerNe : (X.P.prior.partner (H.2 ℓ h) K.1.1).w
          (H.1.2.1 K.1.1) ≠ 0 := (mul_ne_zero_iff.mp hterm).1
      have hpartnerMem : H.1.2.1 K.1.1 ∈ X.P.prior.partnerSet (H.2 ℓ h) K.1.1 := by
        by_contra hnot
        have hzero := X.P.prior.partner_support (H.2 ℓ h) K.1.1
          (H.1.2.1 K.1.1) hnot
        exact hpartnerNe hzero
      have hpaired := X.partner_related (H.2 ℓ h) hparentMem K.1.1
        (H.1.2.1 K.1.1) hpartnerMem
      have hword : (X.S.segment (H.2 ℓ h) (H.1.2.1 K.1.1)).w (z s) ≠ 0 := by
        simpa [Setup5.segLaw, hpaired] using hsegment
      exact (X.S.segment_hits (H.2 ℓ h) (H.1.2.1 K.1.1) (z s)
        hpaired hword i).1
    · have hfalse : ℓ.coarse.2 = false := by
        cases hb : ℓ.coarse.2 <;> simp_all
      have hsegment := HypercubeRamsey.Lane_q_s05_hist1b.posterior_interior_segment_nonzero5
        X H K ℓ z (H.2 ℓ h) hprefix hcoverBin hfalse hraw s
      have hrawInterior := hraw
      simp [Setup5.colWeight, hfalse] at hrawInterior
      have hpartnerNe : (X.P.prior.partner H.1.1 ℓ.coarse.1).w (H.2 ℓ h) ≠ 0 :=
        hrawInterior.1
      have hparentNe := HypercubeRamsey.Lane_q_s05_hist1b.base_parent_supported X H.1 hbase
      have hparentMem : H.1.1 ∈ X.P.lab0 := by
        by_contra hnot
        exact hparentNe (X.P.lab0_atom H.1.1 hnot)
      have hpartnerMem : H.2 ℓ h ∈ X.P.prior.partnerSet H.1.1 ℓ.coarse.1 := by
        by_contra hnot
        have hzero := X.P.prior.partner_support H.1.1 ℓ.coarse.1 (H.2 ℓ h) hnot
        exact hpartnerNe hzero
      have hpaired := X.partner_related H.1.1 hparentMem ℓ.coarse.1 (H.2 ℓ h) hpartnerMem
      have hword : (X.S.segment H.1.1 (H.2 ℓ h)).w (z s) ≠ 0 := by
        simpa [Setup5.segLaw, hpaired] using hsegment
      exact (X.S.segment_hits H.1.1 (H.2 ℓ h) (z s) hpaired hword i).2

/-- The Step 3 threshold of a record target: `e^{-c k'_j}` at low targets, `e^{-c s}` at high targets. -/
def step3Scale (c : ℝ) (ℓ : X.Key) : ℝ :=
  match ℓ with
  | .inl k => Real.exp (-(c * X.p.kPrime n k.2.2.val))
  | .inr _ => Real.exp (-(c * X.p.s n))

/-- The Step 3 one-target calculation (05:440–448, 05:621–627): at a supported base passing Step 1,
integrate the target over its prior and fresh arrays at the replaced value. Other keys remain arbitrary;
the candidate gate retains the required positive denominators. -/
def Step3Raw (cL cH : ℝ) : Prop :=
  ∀ H : X.KeyHist, X.baseLaw.w H.1 ≠ 0 → X.Step1Pass H.1 →
    ∀ r : X.AbsRecord, X.RecOccurs r →
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

/-- Abstract record counts within a fixed target, central sign and severity (05:382–398). Only low
interface records enumerate a mask. The extra factor `T` in that mask budget absorbs any fixed `K_h`
after increasing `n₀`; high subsets are computed and add no record-count term. -/
def RecordCount (C : ℝ) : Prop :=
  ∀ (ℓ : X.Key) (t : CubeVertex (X.p.m n)) (j : ℕ),
    ((Finset.univ.filter fun r : X.AbsRecord => X.RecOccursAt r t j ∧ r.1 = ℓ).card : ℝ) ≤
    Real.exp (C * ((X.p.T n : ℝ) * Real.log (X.p.T n) + ((ℓ.level : ℝ) + 1) * Real.log (X.p.m n) +
      (if ℓ.isLeft ∧ ℓ.level = X.p.J n then
        (X.p.T n : ℝ) * (X.p.q0 * X.p.uStarSeg n * X.p.usedBlocks n : ℕ) else 0)))

/-- L5.1e, count part (05:344–398): `O(T + j)` low tuples around a low state and `O(T + J)` high reference
designations around a high state give the grouped abstract counts. A low interface mask costs `O(k_*)`
with a constant fixed before `K₁`; high subsets are computed from pools and optional columns. -/
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
  refine ⟨Lane_sol_s05_h1.stage1Request, ?_⟩
  intro p hp
  exact Lane_sol_s05_h1.parent_good_mass p hp

/-! ### Stage 2: the coarse base (05:666–679) -/

/-- A function of the coarse base that reads only the bins in `B`. -/
def DependsOnBins (f : X.Coarse → ℝ) (B : Finset (BinVector5 n)) : Prop :=
  ∀ c c' : X.Coarse, (∀ w ∈ B, c.1 w = c'.1 w ∧ c.2 w = c'.2 w) → f c = f c'

/-- The Stage 2 conclusions at a selected parent `v`: the coarse-base law stays in raw support, passes Step 1,
bounds every averaged
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
  (∀ (B : Finset (BinVector5 n)) (f : X.Coarse → ℝ), (∀ c, 0 ≤ f c) → X.DependsOnBins f B →
    ν.expect f ≤ 2 ^ B.card * (X.coarseLaw v).expect f) ∧
  ∀ c, ν.w c ≠ 0 → (X.coarseLaw v).w c ≠ 0

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
  classical
  refine ⟨8 * (4 / χ ^ 2 + 1) + 1, by positivity, Lane_sol_s05_h5l.loadRequest, ?_⟩
  intro p hp
  obtain ⟨n₀, hn₀⟩ := Filter.eventually_atTop.1 (Lane_sol_s05_h5l.eventually_load_bounds p hp)
  refine ⟨n₀, ?_⟩
  intro n hn N E G X hXp hGeom hN v ν hStage
  obtain ⟨hnpos, hcaps, hexception, hrepeat, htail⟩ := hn₀ n hn
  have hcapsX : ∀ j : ℕ, Real.exp (X.p.Kcap * (X.p.q0 * X.p.uSeg n (j + 1))) ≤
      (n : ℝ) ^ (((j : ℝ) + 5) / 500) := by simpa only [hXp] using hcaps
  have hexceptionX : 2 * (n : ℝ) ^ (-(4 / 100 : ℝ)) +
      2 * (X.p.J n + 1 : ℕ) * (n : ℝ) ^ (-(1 / 10 : ℝ)) ≤ 1 := by
    simpa only [hXp] using hexception
  simpa only [Setup5.avgLowPrior, Lane_sol_s05_h5l.lowWeight] using
    Lane_sol_s05_h5l.low_average_tail X hnpos v ν hGeom hN hStage.1
      hStage.2.2.2.1 hcapsX hexceptionX hrepeat htail

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

/-- The Stage 3 conclusions retain the supported Step 1 base: high-only Step 2 tests pass; the other tests, averaged over the
raw low keys, fail with probability at most `e^{-δL/8}`; every high Step 3 failure, averaged over the low keys
and fresh arrays, is at most `e^{-c_{H0} s/2}`. Restricting the raw high-key law retains coordinate support. -/
def Stage3Law (b : X.Base) (ν : FinProb X.HighHid) (cH : ℝ) : Prop :=
  (∀ hi, ν.w hi ≠ 0 → ∀ K, X.TypeOccurs K → X.HighOnly K → ∀ lo, ¬ X.step2Fail (b, X.joinHidden hi lo) K) ∧
  (∀ hi, ν.w hi ≠ 0 → ∀ K, X.TypeOccurs K → ¬ X.HighOnly K →
    (X.lowLaw b).pr (fun lo => X.step2Fail (b, X.joinHidden hi lo) K) ≤
      ((K.2.1.card : ℝ) + 1) * Real.exp (-(X.p.delta * (X.p.q0 * X.p.typeSegs n K)) / 8)) ∧
  (∀ hi, ν.w hi ≠ 0 → ∀ K t, X.OptOccurs K t →
    (X.lowLaw b).pr (fun lo => X.optFail (b, X.joinHidden hi lo) K t) ≤
      Real.exp (-(X.p.delta * (X.p.q0 * X.p.uStarSeg n)) / 8)) ∧
  (∀ hi, ν.w hi ≠ 0 → ∀ r : X.AbsRecord, X.RecOccurs r → (∃ i, r.1 = .inr i) →
    (X.lowLaw b).expect (fun lo => X.step3Rate (b, X.joinHidden hi lo) r) ≤
      Real.exp (-(cH * X.p.s n) / 2)) ∧
  X.baseLaw.w b ≠ 0 ∧ X.Step1Pass b ∧
    ∀ hi, ν.w hi ≠ 0 → ∀ i h, (X.prior b (.inr i)).w (hi i h) ≠ 0

/-- L5.1h3 (05:681–702): given a Stage 2 base, restrict the high keys: Markov from Stage 2 and from the high
Step 3 one-target bound, abstract count `exp(O(T log T + J log m))` beaten by `e^{-c_{H0}s/2}` once `K_s` is large,
bounded-degree grouping by bin, and the conditional avoidance lemma. -/
theorem L5_1h3 : ∀ (C : ℝ) (cL cH : Pre15 → ℝ), (∀ x, 0 < cL x ∧ 0 < cH x) →
    ∃ R : ParamReq5, ∀ p : Params5 γ K' χ, R.Holds p → ∃ n₀ : ℕ, ∀ n ≥ n₀,
      ∀ (N : ℕ) (E : Fin N → Fin N → Prop) (G : Colour) (X : Setup5 γ K' χ n N E G), X.p = p →
        X.RecordCount C → X.Step3Raw (cL p.pre1) (cH p.pre1) →
        ∀ v c, X.baseLaw.w (v, c) ≠ 0 → X.Step1Pass (v, c) →
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
  classical
  let R : ParamReq5 := {
    Kcap := fun _ => 0
    Kpp := fun _ => 0
    Kh := fun _ => 0
    K1 := fun _ => 0
    K2 := fun _ => 0
    KD := fun _ => 0
    Ks := fun _ => 0
    KB := fun _ => 0
    alpha := fun _ => 1 / 50
    alpha_pos := fun _ => by norm_num
  }
  refine ⟨R, ?_⟩
  intro p _hp
  let M : ℝ := Real.rpow 2 ((2 * 3 ^ coarseChunkCount5 : ℕ) : ℝ)
  have hM : 0 < M := by dsimp [M]; positivity
  have hEps := Params5.tendsto_optTestEps5 p
  have hsmallPositive : 0 < (1 / 2 : ℝ) / M := div_pos (by norm_num) hM
  have hbound : Set.Iio ((1 / 2 : ℝ) / M) ∈ 𝓝 (0 : ℝ) := Iio_mem_nhds hsmallPositive
  have hsmall := Filter.eventually_atTop.1 (hEps.eventually hbound)
  obtain ⟨n₀, hn₀⟩ := hsmall
  refine ⟨n₀, ?_⟩
  intro n hn N E G X hXp b hi htests
  let Tests (k : X.LowIdx) :=
    {K : X.Ty // X.OptOccurs K (k.2.1) ∧ X.optKeyOf K (k.2.1) = .inl k}
  have hTestsCard (k : X.LowIdx) : (Fintype.card (Tests k) : ℝ) ≤ M := by
    letI : Fintype (Tests k) := Subtype.fintype _
    simpa [M, Tests] using Setup5.optPatternCount_le5 X k (inferInstance)
  have hε0 : 0 ≤ Real.exp (-(X.p.delta * (X.p.q0 * X.p.uStarSeg n)) / 8) :=
    (Real.exp_pos _).le
  have hεsmall : Real.exp (-(X.p.delta * (X.p.q0 * X.p.uStarSeg n)) / 8) < 1 / 2 / M := by
    rw [hXp]
    exact hn₀ n hn
  have hTestsSmall (k : X.LowIdx) :
      (Fintype.card (Tests k) : ℝ) * Real.exp (-(X.p.delta * (X.p.q0 * X.p.uStarSeg n)) / 8) < 1 / 2 := by
    calc
      (Fintype.card (Tests k) : ℝ) * Real.exp (-(X.p.delta * (X.p.q0 * X.p.uStarSeg n)) / 8) ≤
          M * Real.exp (-(X.p.delta * (X.p.q0 * X.p.uStarSeg n)) / 8) :=
        mul_le_mul_of_nonneg_right (hTestsCard k) hε0
      _ < M * ((1 / 2 : ℝ) / M) := mul_lt_mul_of_pos_left hεsmall hM
      _ = 1 / 2 := by field_simp [ne_of_gt hM]
  have hOptFail_ext {K : X.Ty} {t : CubeVertex (X.p.m n)} {k : X.LowIdx}
      (hOpt : X.OptOccurs K t) (hKey : X.optKeyOf K t = .inl k)
      (lo lo' : X.LowHid) (hlo : lo k = lo' k) :
      X.optFail (b, X.joinHidden hi lo) K t = X.optFail (b, X.joinHidden hi lo') K t := by
    classical
    have hfacts := X.optOccurs_high_type_keys_near5 K t hOpt
    have hcolsS : ∀ ℓ ∈ K.2.1,
        (b, X.joinHidden hi lo).2 ℓ = (b, X.joinHidden hi lo').2 ℓ := by
      intro ℓ hℓ
      rcases hfacts.2.1 ℓ hℓ with ⟨i, rfl⟩
      rfl
    have hcolsIns : ∀ ℓ ∈ insert (X.optKeyOf K t) K.2.1,
        (b, X.joinHidden hi lo).2 ℓ = (b, X.joinHidden hi lo').2 ℓ := by
      intro ℓ hℓ
      rcases Finset.mem_insert.mp hℓ with hℓ | hℓ
      · subst ℓ
        rw [hKey]
        change lo k = lo' k
        exact hlo
      · exact hcolsS ℓ hℓ
    have hmassS := X.blockMass_ext5 (b, X.joinHidden hi lo) (b, X.joinHidden hi lo') K
      K.2.1 rfl hcolsS
    have hmassIns := X.blockMass_ext5 (b, X.joinHidden hi lo) (b, X.joinHidden hi lo') K
      (insert (X.optKeyOf K t) K.2.1) rfl hcolsIns
    unfold Setup5.optFail
    rw [hmassIns, hmassS]
  have hLowMarg (k : X.LowIdx) (A : Fin N → Prop) :
      (X.lowLaw b).pr (fun lo => A (lo k ⟨0, by omega⟩)) = (X.prior b (.inl k)).pr A := by
    classical
    let i₀ : Fin 1 := ⟨0, by omega⟩
    let P : X.LowIdx → FinProb (Fin 1 → Fin N) :=
      fun k' => FinProb.pi fun _ : Fin 1 => X.prior b (.inl k')
    have htop := FinProb.pi_pr_singleton5 P k (fun col => A (col i₀)) (fun _ => X.y₀)
    have hinner := FinProb.pi_pr_singleton5
      (fun _ : Fin 1 => X.prior b (.inl k)) i₀ A X.y₀
    simpa [P, Setup5.lowLaw, Setup5.lowLawOf, i₀] using htop.trans hinner
  let i₀ : Fin 1 := ⟨0, by omega⟩
  let loAt : X.LowIdx → Fin N → X.LowHid := fun k y =>
    Function.update (fun _ : X.LowIdx => fun _ : Fin 1 => X.y₀) k (fun _ => y)
  let Bad : ∀ k : X.LowIdx, Tests k → Fin N → Prop := fun k q y =>
    X.optFail (b, X.joinHidden hi (loAt k y)) q.1 (k.2.1)
  have hbad (k : X.LowIdx) (q : Tests k) :
      (X.prior b (.inl k)).pr (Bad k q) ≤
        Real.exp (-(X.p.delta * (X.p.q0 * X.p.uStarSeg n)) / 8) := by
    let t₀ := k.2.1
    have hinput := htests q.1 t₀ q.2.1
    have hcoord (lo : X.LowHid) : lo k = (loAt k (lo k i₀)) k := by
      simp only [loAt, Function.update_self]
      funext j
      have hj : j = i₀ := Subsingleton.elim _ _
      rw [hj]
    have hEvent (lo : X.LowHid) :
        X.optFail (b, X.joinHidden hi lo) q.1 t₀ = Bad k q (lo k i₀) := by
      simpa [Bad, t₀] using hOptFail_ext q.2.1 q.2.2 lo (loAt k (lo k i₀)) (hcoord lo)
    have hprEq :
        (X.lowLaw b).pr (fun lo => X.optFail (b, X.joinHidden hi lo) q.1 t₀) =
          (X.lowLaw b).pr (fun lo => Bad k q (lo k i₀)) := by
      unfold FinProb.pr
      apply Finset.sum_congr rfl
      intro lo hlo
      change (if X.optFail (b, X.joinHidden hi lo) q.1 t₀ then (X.lowLaw b).w lo else 0) =
        (if Bad k q (lo k i₀) then (X.lowLaw b).w lo else 0)
      rw [hEvent lo]
    calc
      (X.prior b (.inl k)).pr (Bad k q) =
          (X.lowLaw b).pr (fun lo => Bad k q (lo k i₀)) := (hLowMarg k (Bad k q)).symm
      _ = (X.lowLaw b).pr (fun lo => X.optFail (b, X.joinHidden hi lo) q.1 t₀) := hprEq.symm
      _ ≤ Real.exp (-(X.p.delta * (X.p.q0 * X.p.uStarSeg n)) / 8) := hinput
  have hTrim (k : X.LowIdx) :
      ∃ Q : FinProb (Fin N), (∀ y, Q.w y ≤ 2 * (X.prior b (.inl k)).w y) ∧
        ∀ y, Q.w y ≠ 0 → ∀ q : Tests k, ¬ Bad k q y := by
    letI : Fintype (Tests k) := Subtype.fintype _
    apply FinProb.trimByFiniteFamily5 (X.prior b (.inl k)) (Bad k)
      (Real.exp (-(X.p.delta * (X.p.q0 * X.p.uStarSeg n)) / 8)) hε0
    · exact hbad k
    · exact hTestsSmall k
  let tr : X.LowIdx → Law N := fun k => Classical.choose (hTrim k)
  have htr : ∀ k, (∀ y, (tr k).w y ≤ 2 * (X.prior b (.inl k)).w y) ∧
      ∀ y, (tr k).w y ≠ 0 → ∀ q : Tests k, ¬ Bad k q y := fun k => Classical.choose_spec (hTrim k)
  refine ⟨tr, ?_, ?_⟩
  · intro k y
    exact (htr k).1 y
  · intro k y hy K t hOpt hKey lo hlo
    have ht : t = k.2.1 := by
      have h := hKey
      simp [Setup5.optKeyOf] at h
      exact congrArg Prod.fst (congrArg Prod.snd h)
    have hOpt' : X.OptOccurs K (k.2.1) := by simpa [ht] using hOpt
    have hKey' : X.optKeyOf K (k.2.1) = .inl k := by simpa [ht] using hKey
    let q : Tests k := ⟨K, hOpt', hKey'⟩
    have hgood : ¬ Bad k q y := (htr k).2 y hy q
    have hcoord : lo k = (loAt k y) k := by
      rw [hlo]
      simp [loAt]
    have hEqActual := hOptFail_ext hOpt hKey lo (loAt k y) hcoord
    have hEq : X.optFail (b, X.joinHidden hi lo) K t = Bad k q y := by
      simpa [Bad, q, ht] using hEqActual
    rw [hEq]
    exact hgood

/-! ### Stage 5: the low keys (05:723–744) -/

/-- Resample the low keys in `Λ` from the trimmed laws, keeping the others at `lo`. -/
def resampleLow (tr : X.LowIdx → Law N) (Λ : Finset X.LowIdx) (lo : X.LowHid) : FinProb X.LowHid :=
  FinProb.pi fun k => if k ∈ Λ then FinProb.pi (fun _ => tr k) else FinProb.dirac5 (lo k)

/-- The Stage 5 conclusions: every Step 2 test passes; Step 3 conditional array-failure bounds
`e^{-c_{L0} k'_j / 4}` (low) and `e^{-c_{H0} s / 6}` (high); and dropping the constraints touching a set `Λ` of
low keys costs a factor `2` per key against resampling them from the trimmed laws (05:1031–1035).
The realized low columns remain in their raw prior support (05:704–741). -/
def Stage5Law (b : X.Base) (hi : X.HighHid) (tr : X.LowIdx → Law N) (ν : FinProb X.LowHid)
    (cL cH : ℝ) : Prop :=
  (∀ lo, ν.w lo ≠ 0 → X.Step2Pass (b, X.joinHidden hi lo)) ∧
  (∀ lo, ν.w lo ≠ 0 → ∀ r : X.AbsRecord, X.RecOccurs r →
    X.step3Rate (b, X.joinHidden hi lo) r ≤
      X.step3Scale (match r.1 with | .inl _ => cL / 4 | .inr _ => cH / 6) r.1) ∧
  (∀ (Λ : Finset X.LowIdx) (W : X.LowHid → ℝ) (M : ℝ), (∀ lo, 0 ≤ W lo) →
    (∀ lo, (X.resampleLow tr Λ lo).expect W ≤ M) → ν.expect W ≤ 2 ^ Λ.card * M) ∧
  ∀ lo, ν.w lo ≠ 0 → ∀ k h, (X.prior b (.inl k)).w (lo k h) ≠ 0

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
keys. `Cloc` is an input, fixed before the eventual threshold in L5.1l(2). -/
structure ProxyMeanData5 (Cloc : ℕ) (b : X.Base) (hi : X.HighHid)
    (Z : X.LowHid → OddRole5 n → Fin N → ℝ) : Prop where
  nonneg : ∀ lo r y, 0 ≤ Z lo r y
  high_zero : ∀ lo r y, ¬ X.g.low (X.p.J n) r.1 → Z lo r y = 0
  cap : ∀ lo r y, Z lo r y ≤ Real.exp (X.p.DL n)
  locality : ∀ r, FinProb.DependsOn (fun lo => Z lo r)
    (Finset.univ.filter fun k : X.LowIdx =>
      hammingDist k.2.1 (X.g.sign r.1) ≤ Cloc * Nat.sqrt (X.p.m n))
  one_target : ∀ lo r y, X.g.low (X.p.J n) r.1 →
    ∑ y', (X.prior b (X.g.roleKey (X.p.J n) r.1)).w y' *
        Z (Function.update lo (X.lowIdxOf (X.g.roleKey (X.p.J n) r.1)) (fun _ => y')) r y ≤
      2 * (N : ℝ) * (X.prior b (X.g.roleKey (X.p.J n) r.1)).w y

set_option maxHeartbeats 0
/-- L5.1l(2) (05:1027–1041): under the Stage 5 law, the odd-role averages of a proxy-mean functional are bounded
at every label with probability `1 - o(1)`: near rows (sign distance `O(√m)`) are a `2^{-m+o(m)}` fraction, the
comparison costs `2^n`, separated targets are resampled independently from the trimmed laws with the
one-target bound, and the averages of `N π_ℓ` are bounded by the first part. The threshold is allowed to depend
on the fixed locality constant; the functional cannot choose that constant after seeing `n`. -/
theorem L5_1l2 : ∀ (Cloc : ℕ) (C₁ : ℝ), 0 < C₁ →
    ∃ C₂ : ℝ, 0 < C₂ ∧ ∃ R : ParamReq5, ∀ p : Params5 γ K' χ, R.Holds p →
    ∃ n₀ : ℕ, ∀ n ≥ n₀, ∀ (N : ℕ) (E : Fin N → Fin N → Prop) (G : Colour) (X : Setup5 γ K' χ n N E G),
      X.p = p → ChunkEstimates5 X.g → N ≤ n * 2 ^ n →
            ∀ b hi tr (ν : FinProb X.LowHid) (cL cH : ℝ), X.Stage5Law b hi tr ν cL cH → X.Stage4Laws b hi tr →
          (∀ y, X.avgLowPrior b y ≤ C₁) →
          ∀ Z, X.ProxyMeanData5 Cloc b hi Z →
            ν.pr (fun lo => ∃ y, C₂ < (Fintype.card (OddRole5 n) : ℝ)⁻¹ * ∑ r, Z lo r y) ≤ 1 / 100 := by
  classical
  intro Cloc C₁ hC₁
  let C₂ : ℝ := 32 * (C₁ + 1)
  have hC₂ : 0 < C₂ := by dsimp [C₂]; positivity
  let R : ParamReq5 := {
    Kcap := fun _ => 0
    Kpp := fun _ => 0
    Kh := fun _ => 0
    K1 := fun _ => 0
    K2 := fun _ => 0
    KD := fun _ => 0
    Ks := fun _ => 0
    KB := fun _ => 0
    alpha := fun _ => 1 / 50
    alpha_pos := by intro _; norm_num
  }
  refine ⟨C₂, hC₂, R, ?_⟩
  intro p _hp
  have hRatio := Lane_q_s05_h5l.sqrtRadiusRatio_tendsto p Cloc
  have hRatioSmall : ∀ᶠ n : ℕ in atTop,
      (Cloc : ℝ) * (Nat.sqrt (p.m n) : ℝ) / (p.m n : ℝ) < 1 / 2 :=
    hRatio.eventually (Iio_mem_nhds (by norm_num : (0 : ℝ) < 1 / 2))
  have hEntropy : ∀ᶠ n : ℕ in atTop,
      Real.binEntropy ((Cloc : ℝ) * (Nat.sqrt (p.m n) : ℝ) / (p.m n : ℝ)) <
        Real.log 2 / 2 := Lane_q_s05_h5l.entropySqrtRadius_eventually p Cloc
  have hmTop : Tendsto (fun n : ℕ => (p.m n : ℝ)) atTop atTop := by
    have hpow : Tendsto (fun n : ℕ => (n : ℝ) ^ p.alpha) atTop atTop :=
      (tendsto_rpow_atTop p.halpha.1).comp tendsto_natCast_atTop_atTop
    have hmle (n : ℕ) : (n : ℝ) ^ p.alpha ≤ (p.m n : ℝ) := by
      dsimp [Params5.m]
      exact Nat.le_ceil _
    exact tendsto_atTop_mono hmle hpow
  have hmPositive : ∀ᶠ n : ℕ in atTop, 0 < (p.m n : ℝ) := hmTop.eventually_gt_atTop 0
  have hNearExp := Lane_q_s05_h5l.nearLoadExp_tendsto p
  have hNearSmall : ∀ᶠ n : ℕ in atTop,
      (n : ℝ) * Real.exp ((p.m n : ℝ) ^ (15 / 100 : ℝ) -
        (Real.log 2 / 2) * (p.m n : ℝ)) < 1 :=
    hNearExp.eventually (Iio_mem_nhds (by norm_num : (0 : ℝ) < 1))
  have hTail := Lane_q_s05_h5l.halfPowerTail_tendsto
  have hTailSmall : ∀ᶠ n : ℕ in atTop, (n : ℝ) * (1 / 2 : ℝ) ^ n < 1 / 100 :=
    hTail.eventually (Iio_mem_nhds (by norm_num : (0 : ℝ) < 1 / 100))
  have hEventually := hRatioSmall.and (hEntropy.and (hmPositive.and (hNearSmall.and hTailSmall)))
  obtain ⟨n₀, hn₀⟩ := Filter.eventually_atTop.1 hEventually
  refine ⟨max n₀ 1, ?_⟩
  intro n hn N E G X hXp hGeom hN b hi tr ν cL cH hStage5 hStage4 hAvg Z hZ
  have hn0 : n₀ ≤ n := le_trans (le_max_left _ _) hn
  have hn1 : 1 ≤ n := le_trans (le_max_right _ _) hn
  rcases hn₀ n hn0 with ⟨hR, hEnt, hMpos, hNear, hTailn⟩
  let m : ℕ := X.p.m n
  let rad : ℕ := Cloc * Nat.sqrt m
  have hm : 0 < m := by simpa [m, hXp.symm] using hMpos
  have hradCast : (rad : ℝ) = (Cloc : ℝ) * (Nat.sqrt m : ℝ) := by
    simp [rad, Nat.cast_mul]
  have hratioCast : (rad : ℝ) / (m : ℝ) =
      (Cloc : ℝ) * (Nat.sqrt m : ℝ) / (m : ℝ) := by rw [hradCast]
  have hradReal : (rad : ℝ) < (m : ℝ) / 2 := by
    have hR' : (Cloc : ℝ) * (Nat.sqrt m : ℝ) / (m : ℝ) < 1 / 2 := by
      simpa [m, hXp.symm] using hR
    have hmul := (div_lt_iff₀ (by exact_mod_cast hm : (0 : ℝ) < (m : ℝ))).1 hR'
    rw [hradCast]
    nlinarith [hmul]
  have hradNat : rad ≤ m / 2 := by
    have hmul : (2 * rad : ℕ) < m := by exact_mod_cast (by nlinarith : (2 : ℝ) * rad < m)
    omega
  let t : ℝ := (rad : ℝ) / (m : ℝ)
  let f : ℝ := Real.exp (Real.binEntropy t * (m : ℝ)) / (2 : ℝ) ^ m
  have hfrac : f ≤ Real.exp (-(Real.log 2 / 2) * (m : ℝ)) := by
    dsimp [f, t]
    have hEnt' : Real.binEntropy ((rad : ℝ) / (m : ℝ)) ≤ Real.log 2 / 2 := by
      simpa [t, rad, m, hXp.symm] using hEnt.le
    exact Lane_q_s05_h5l.entropy_fraction_exp_bound hm ((rad : ℝ) / (m : ℝ)) hEnt'
  have hEventBound : (n : ℝ) * f * Real.exp (X.p.DL n) ≤ 1 := by
    have hScaleEq : X.p.DL n = (m : ℝ) ^ (15 / 100 : ℝ) := by
      simp [Params5.DL, m]
    rw [hScaleEq]
    have hExpNonneg : 0 ≤ (n : ℝ) := by positivity
    calc
      (n : ℝ) * f * Real.exp ((m : ℝ) ^ (15 / 100 : ℝ)) ≤
          (n : ℝ) * Real.exp (-(Real.log 2 / 2) * (m : ℝ)) *
            Real.exp ((m : ℝ) ^ (15 / 100 : ℝ)) :=
        mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hfrac hExpNonneg)
          (Real.exp_nonneg _)
      _ = (n : ℝ) * Real.exp ((m : ℝ) ^ (15 / 100 : ℝ) -
            (Real.log 2 / 2) * (m : ℝ)) := by
              calc
                _ = (n : ℝ) * (Real.exp (-(Real.log 2 / 2) * (m : ℝ)) *
                    Real.exp ((m : ℝ) ^ (15 / 100 : ℝ))) := by ring
                _ = (n : ℝ) * Real.exp (-(Real.log 2 / 2) * (m : ℝ) +
                    (m : ℝ) ^ (15 / 100 : ℝ)) := by rw [← Real.exp_add]
                _ = _ := by congr 1; ring
      _ ≤ (n : ℝ) * Real.exp ((p.m n : ℝ) ^ (15 / 100 : ℝ) -
            (Real.log 2 / 2) * (p.m n : ℝ)) := by
          have hmEq : m = p.m n := by simp [m, hXp]
          rw [hmEq]
      _ ≤ 1 := le_of_lt (by simpa [m, hXp.symm] using hNear)
  have hTailN : (N : ℝ) * (1 / 4 : ℝ) ^ n ≤ 1 / 100 := by
    calc
      (N : ℝ) * (1 / 4 : ℝ) ^ n ≤
          (n : ℝ) * (2 : ℝ) ^ n * (1 / 4 : ℝ) ^ n :=
        mul_le_mul_of_nonneg_right (by exact_mod_cast hN) (by positivity)
      _ = (n : ℝ) * (1 / 2 : ℝ) ^ n := by
        calc
          (n : ℝ) * (2 : ℝ) ^ n * (1 / 4 : ℝ) ^ n =
              (n : ℝ) * ((2 : ℝ) ^ n * (1 / 4 : ℝ) ^ n) := by ring
          _ = (n : ℝ) * ((2 : ℝ) * (1 / 4 : ℝ)) ^ n := by
            have hpow : (2 : ℝ) ^ n * (1 / 4 : ℝ) ^ n =
                ((2 : ℝ) * (1 / 4 : ℝ)) ^ n := by rw [← mul_pow]
            rw [hpow]
          _ = (n : ℝ) * (1 / 2 : ℝ) ^ n := by norm_num
      _ ≤ 1 / 100 := le_of_lt hTailn
  let avg (lo : X.LowHid) (y : Fin N) : ℝ :=
    (Fintype.card (OddRole5 n) : ℝ)⁻¹ * ∑ r, Z lo r y
  have hPerLabel (y : Fin N) :
      ν.pr (fun lo => C₂ < avg lo y) ≤ (1 / 4 : ℝ) ^ n := by
    have hAvgNonneg (lo : X.LowHid) : 0 ≤ avg lo y := by
      dsimp [avg]
      apply mul_nonneg (inv_nonneg.mpr (Nat.cast_nonneg _))
      exact Finset.sum_nonneg fun r _ => hZ.nonneg lo r y
    let wt (r : OddRole5 n) : ℝ :=
      if X.g.low (X.p.J n) r.1 then
        4 * (N : ℝ) * (X.prior b (X.g.roleKey (X.p.J n) r.1)).w y else 0
    have hwtNonneg : ∀ r, 0 ≤ wt r := by
      intro r
      by_cases hlow : X.g.low (X.p.J n) r.1
      · have hp : 0 ≤ (X.prior b (X.g.roleKey (X.p.J n) r.1)).w y :=
          (X.prior b (X.g.roleKey (X.p.J n) r.1)).nonneg y
        have hnonneg : 0 ≤ 4 * (N : ℝ) *
            (X.prior b (X.g.roleKey (X.p.J n) r.1)).w y :=
          mul_nonneg (mul_nonneg (by norm_num : (0 : ℝ) ≤ 4) (Nat.cast_nonneg N)) hp
        simpa [wt, hlow] using hnonneg
      · simp [wt, hlow]
    have hwtAvg : (Fintype.card (OddRole5 n) : ℝ)⁻¹ * ∑ r, wt r ≤ 4 * C₁ := by
      have hEq : (Fintype.card (OddRole5 n) : ℝ)⁻¹ * ∑ r, wt r = 4 * X.avgLowPrior b y := by
        unfold Setup5.avgLowPrior
        have hsum : ∑ r, wt r =
            4 * ∑ r : OddRole5 n,
              (if X.g.low (X.p.J n) r.1 then
                (N : ℝ) * (X.prior b (X.g.roleKey (X.p.J n) r.1)).w y else 0) := by
          calc
            ∑ r, wt r =
                ∑ r : OddRole5 n, 4 *
                  (if X.g.low (X.p.J n) r.1 then
                    (N : ℝ) * (X.prior b (X.g.roleKey (X.p.J n) r.1)).w y else 0) := by
                  apply Finset.sum_congr rfl
                  intro r hr
                  by_cases hlow : X.g.low (X.p.J n) r.1 <;> simp [wt, hlow] <;> ring
            _ = 4 * ∑ r : OddRole5 n,
                  (if X.g.low (X.p.J n) r.1 then
                    (N : ℝ) * (X.prior b (X.g.roleKey (X.p.J n) r.1)).w y else 0) := by
                  rw [Finset.mul_sum]
        rw [hsum]
        ring
      rw [hEq]
      exact mul_le_mul_of_nonneg_left (hAvg y) (by norm_num)
    let near : OddRole5 n → Finset (OddRole5 n) := fun r =>
      Finset.univ.filter fun r' =>
        hammingDist (X.g.sign r'.1) (X.g.sign r.1) ≤ rad
    have hSelf (r : OddRole5 n) : r ∈ near r := by
      simp only [near, Finset.mem_filter, Finset.mem_univ, true_and]
      simp [HypercubeRamsey.hammingDist]
    have hNearCard (r : OddRole5 n) : ((near r).card : ℝ) ≤ f * Fintype.card (OddRole5 n) := by
      have hc := Lane_q_s05_h5l.oddNearSign_entropy_card_le X.g hGeom
        (X.g.sign r.1) rad hm hradNat
      have hc' : ((near r).card : ℝ) ≤
          Real.exp (Real.binEntropy ((rad : ℝ) / (m : ℝ)) * (m : ℝ)) *
            (Fintype.card (OddRole5 n) : ℝ) / (2 : ℝ) ^ m := by
        simpa [near, m, HypercubeRamsey.hammingDist] using hc
      calc
        ((near r).card : ℝ) ≤
            Real.exp (Real.binEntropy ((rad : ℝ) / (m : ℝ)) * (m : ℝ)) *
              (Fintype.card (OddRole5 n) : ℝ) / (2 : ℝ) ^ m := hc'
        _ = f * Fintype.card (OddRole5 n) := by
          dsimp [f, t]
          ring
    have hdNonneg : 0 ≤ f := by positivity
    let L : ℝ := Real.exp (X.p.DL n)
    have hL : 0 ≤ L := by dsimp [L]; positivity
    have hZL : ∀ r lo, lo ∈ Finset.univ → Z lo r y ≤ L := by
      intro r lo hlo
      exact hZ.cap lo r y
    let d : OddRole5 n → ℝ := wt
    have hd : ∀ r, 0 ≤ d r := hwtNonneg
    have hMeanBound :
        (Fintype.card (OddRole5 n) : ℝ)⁻¹ * ∑ r, d r ≤ 4 * C₁ := hwtAvg
    have hJoint : ∀ (q : ℕ), q ≤ n → ∀ s : Fin q → OddRole5 n,
        (∀ i j : Fin q, j < i → s i ∉ near (s j)) →
          ∑ lo ∈ (Finset.univ : Finset X.LowHid), ν.w lo * ∏ i, Z lo (s i) y ≤
            (2 : ℝ) ^ q * ∏ i, d (s i) := by
      intro q hq s hsep
      by_cases hlow : ∀ i : Fin q, X.g.low (X.p.J n) (s i).1
      · let target : Fin q → X.LowIdx := fun i =>
          X.lowIdxOf (X.g.roleKey (X.p.J n) (s i).1)
        let Λ : Finset X.LowIdx := Finset.univ.image target
        have hmem (i : Fin q) : target i ∈ Λ :=
          Finset.mem_image.mpr ⟨i, Finset.mem_univ _, rfl⟩
        have hsign (i : Fin q) : (target i).2.1 = X.g.sign (s i).1 := by
          have hiLow : X.g.severity (s i).1 ≤ X.p.J n := hlow i
          simp [target, Setup5.lowIdxOf, ChunkGeometry5.roleKey, hiLow]
        have hNoNear (i j : Fin q) (hij : i ≠ j) : s j ∉ near (s i) := by
          by_cases hji : j < i
          · have hnot := hsep i j hji
            have hdistNot : ¬ hammingDist (X.g.sign (s i).1) (X.g.sign (s j).1) ≤ rad := by
              intro hdist
              apply hnot
              exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, by simpa [near] using hdist⟩
            intro hmemNear
            have hdist := (Finset.mem_filter.mp hmemNear).2
            apply hdistNot
            simpa [Lane_q_s05_h5l.hammingDist_symm5] using hdist
          · have hij' : i < j := by omega
            exact hsep j i hij'
        have htargetNoScope (i j : Fin q) (hij : i ≠ j) :
            target j ∉ Finset.univ.filter fun k : X.LowIdx =>
              hammingDist k.2.1 (X.g.sign (s i).1) ≤ rad := by
          intro hk
          have hk' := (Finset.mem_filter.mp hk).2
          have hmemNear : s j ∈ near (s i) := by
            apply Finset.mem_filter.mpr
            refine ⟨Finset.mem_univ _, ?_⟩
            simpa [near, hsign j] using hk'
          exact hNoNear i j hij hmemNear
        have htargetInj : Function.Injective target := by
          intro i j hij
          by_contra hne
          have hsignEq : X.g.sign (s i).1 = X.g.sign (s j).1 := by
            have hh := congrArg (fun k : X.LowIdx => k.2.1) hij
            rw [hsign i, hsign j] at hh
            exact hh
          have hdist : hammingDist (X.g.sign (s j).1) (X.g.sign (s i).1) ≤ rad := by
            rw [hsignEq]
            simp [HypercubeRamsey.hammingDist]
          have hmemNear : s j ∈ near (s i) :=
            Finset.mem_filter.mpr ⟨Finset.mem_univ _, hdist⟩
          exact hNoNear i j hne hmemNear
        let P : X.LowIdx → FinProb (Fin 1 → Fin N) := fun k =>
          FinProb.pi (fun _ : Fin 1 => tr k)
        let W : X.LowHid → ℝ := fun lo => ∏ i, Z lo (s i) y
        have hWNonneg : ∀ lo, 0 ≤ W lo := by
          intro lo
          dsimp [W]
          apply Finset.prod_nonneg
          intro i hi
          exact hZ.nonneg lo (s i) y
        let frow : X.LowHid → Fin q → (Fin 1 → Fin N) → ℝ := fun lo i u =>
          Z (Function.update lo (target i) (fun _ => u ⟨0, by omega⟩)) (s i) y
        have hOne : ∀ i lo,
          (P (target i)).expect (frow lo i) ≤ d (s i) := by
          intro i lo
          have hiLow := hlow i
          have hSingle : (P (target i)).expect (frow lo i) =
              (tr (target i)).expect (fun y' =>
                Z (Function.update lo (target i) (fun _ => y')) (s i) y) := by
            simpa [P, frow] using Lane_q_s05_h5l.pi_expect_singleton5
              (fun _ : Fin 1 => tr (target i)) (⟨0, by omega⟩ : Fin 1)
              (fun y' => Z (Function.update lo (target i) (fun _ => y')) (s i) y) X.y₀
          have hRoleKey : X.g.roleKey (X.p.J n) (s i).1 = .inl (target i) := by
            have hiLevel : X.g.severity (s i).1 ≤ X.p.J n := by
              simpa [ChunkGeometry5.low] using hiLow
            simp [target, Setup5.lowIdxOf, ChunkGeometry5.roleKey, hiLevel]
          have hTrBound :
              (tr (target i)).expect (fun y' =>
                Z (Function.update lo (target i) (fun _ => y')) (s i) y) ≤
                4 * (N : ℝ) * (X.prior b (X.g.roleKey (X.p.J n) (s i).1)).w y := by
            calc
              _ ≤ 2 * ∑ y', (X.prior b (X.g.roleKey (X.p.J n) (s i).1)).w y' *
                  Z (Function.update lo (target i) (fun _ => y')) (s i) y := by
                unfold FinProb.expect
                rw [Finset.mul_sum]
                apply Finset.sum_le_sum
                intro y' hy'
                have hZnonneg := hZ.nonneg
                  (Function.update lo (target i) (fun _ => y')) (s i) y
                have hdens : (tr (target i)).w y' ≤
                    2 * (X.prior b (X.g.roleKey (X.p.J n) (s i).1)).w y' := by
                  rw [hRoleKey]
                  exact hStage4.1 (target i) y'
                simpa [mul_assoc] using mul_le_mul_of_nonneg_right hdens hZnonneg
              _ ≤ 2 * (2 * (N : ℝ) *
                  (X.prior b (X.g.roleKey (X.p.J n) (s i).1)).w y) := by
                apply mul_le_mul_of_nonneg_left
                · exact hZ.one_target lo (s i) y hiLow
                · norm_num
              _ = 4 * (N : ℝ) *
                  (X.prior b (X.g.roleKey (X.p.J n) (s i).1)).w y := by ring
          have hD : d (s i) = 4 * (N : ℝ) *
              (X.prior b (X.g.roleKey (X.p.J n) (s i).1)).w y := by
            simp [d, wt, hiLow]
          rw [hD]
          calc
            (P (target i)).expect (frow lo i) =
                (tr (target i)).expect (fun y' =>
                  Z (Function.update lo (target i) (fun _ => y')) (s i) y) := hSingle
            _ ≤ 4 * (N : ℝ) * (X.prior b
                (X.g.roleKey (X.p.J n) (s i).1)).w y := hTrBound
        have hResample : ∀ lo,
            (X.resampleLow tr Λ lo).expect W ≤ ∏ i, d (s i) := by
          intro lo
          let loU : X.LowIdx → (Fin 1 → Fin N) := fun k => lo k
          have hPinned := Lane_q_s05_h5l.pi_expect_pinned5 P Λ loU W
          have hPinned' : (X.resampleLow tr Λ lo).expect W =
              (FinProb.pi (fun k : {k : X.LowIdx // k ∈ Λ} => P k.1)).expect
                (fun a => W (fun k => if hk : k ∈ Λ then a ⟨k, hk⟩ else loU k)) := by
            simpa [Setup5.resampleLow, P, FinProb.dirac5,
              Lane_q_s05_h5l.pinDirac5] using hPinned
          have hFactor (a : {k : X.LowIdx // k ∈ Λ} → (Fin 1 → Fin N)) :
              W (fun k => if hk : k ∈ Λ then a ⟨k, hk⟩ else loU k) =
                ∏ i, frow lo i (a ⟨target i, hmem i⟩) := by
            dsimp [W]
            apply Finset.prod_congr rfl
            intro i hi
            let loA : X.LowHid := fun k => if hk : k ∈ Λ then a ⟨k, hk⟩ else loU k
            let u : Fin 1 → Fin N := a ⟨target i, hmem i⟩
            let loB : X.LowHid := Function.update lo (target i) (fun _ => u ⟨0, by omega⟩)
            have hagree : ∀ k ∈ Finset.univ.filter (fun k : X.LowIdx =>
                hammingDist k.2.1 (X.g.sign (s i).1) ≤ rad), loA k = loB k := by
              intro k hk
              have hscope := (Finset.mem_filter.mp hk).2
              by_cases hkΛ : k ∈ Λ
              · obtain ⟨j, hj, hjk⟩ := Finset.mem_image.mp hkΛ
                have hji : j = i := by
                  by_contra hji
                  have hNo := htargetNoScope i j (Ne.symm hji)
                  exact hNo (by simpa [hjk] using hk)
                subst j
                have hkTarget : k = target i := hjk.symm
                subst k
                have hu : u = fun _ : Fin 1 => u ⟨0, by omega⟩ := by
                  funext z
                  have hz : z = (⟨0, by omega⟩ : Fin 1) := Subsingleton.elim _ _
                  rw [hz]
                have hA : loA (target i) = u := by simp [loA, u, hmem i]
                have hB : loB (target i) = (fun _ : Fin 1 => u ⟨0, by omega⟩) := by
                  simp [loB, Function.update_self]
                rw [hA, hB]
                exact hu
              · have hki : k ≠ target i := by
                  intro heq
                  exact hkΛ (heq ▸ hmem i)
                have hA : loA k = loU k := by simp [loA, hkΛ]
                have hB : loB k = lo k := by simp [loB, Function.update_of_ne hki]
                rw [hA, hB]
            have hrowFun : Z loA (s i) = Z loB (s i) :=
              hZ.locality (s i) loA loB hagree
            have hrowY : Z loA (s i) y = Z loB (s i) y :=
              congrArg (fun F : Fin N → ℝ => F y) hrowFun
            simpa [loA, loB, u, frow] using hrowY
          have hFunctionEq :
              (fun a : (∀ k : {k : X.LowIdx // k ∈ Λ}, Fin 1 → Fin N) =>
                W (fun k => if hk : k ∈ Λ then a ⟨k, hk⟩ else loU k)) =
              (fun a : (∀ k : {k : X.LowIdx // k ∈ Λ}, Fin 1 → Fin N) =>
                ∏ i, frow lo i (a ⟨target i, hmem i⟩)) := by
            funext a
            exact hFactor a
          have hProdExp := Lane_q_s05_h5l.pi_expect_prod_restrict5
            target htargetInj P (fun i u => frow lo i u)
          calc
            (X.resampleLow tr Λ lo).expect W =
                (FinProb.pi (fun k : {k : X.LowIdx // k ∈ Λ} => P k.1)).expect
                  (fun a => W (fun k => if hk : k ∈ Λ then a ⟨k, hk⟩ else loU k)) := hPinned'
            _ = ∏ i, (P (target i)).expect (frow lo i) := by
              rw [hFunctionEq]
              exact hProdExp
            _ ≤ ∏ i, d (s i) := by
              apply Finset.prod_le_prod₀
              · intro i hi
                unfold FinProb.expect
                apply Finset.sum_nonneg
                intro u hu
                exact mul_nonneg ((P (target i)).nonneg u)
                  (hZ.nonneg (Function.update lo (target i) (fun _ => u ⟨0, by omega⟩))
                    (s i) y)
              · intro i hi
                exact hOne i lo
        have hStageBound := hStage5.2.2.1 Λ W (∏ i, d (s i)) hWNonneg hResample
        have hcard : Λ.card = q := by
          dsimp [Λ]
          rw [Finset.card_image_of_injective _ htargetInj]
          simp
        have hleft :
            ν.expect (fun lo => ∏ i, Z lo (s i) y) ≤
              (2 : ℝ) ^ q * ∏ i, d (s i) := by
          calc
            ν.expect (fun lo => ∏ i, Z lo (s i) y) ≤
                (2 : ℝ) ^ Λ.card * ∏ i, d (s i) := by simpa [W] using hStageBound
            _ = (2 : ℝ) ^ q * ∏ i, d (s i) := by rw [hcard]
        simpa [FinProb.expect] using hleft
      · push_neg at hlow
        obtain ⟨i, hi⟩ := hlow
        have hprod (lo : X.LowHid) : ∏ i : Fin q, Z lo (s i) y = 0 := by
          apply Finset.prod_eq_zero (Finset.mem_univ i)
          exact hZ.high_zero lo (s i) y hi
        have hleft :
            ∑ lo ∈ (Finset.univ : Finset X.LowHid), ν.w lo * ∏ i, Z lo (s i) y = 0 := by
          apply Finset.sum_eq_zero
          intro lo hlo
          simp [hprod lo]
        rw [hleft]
        apply mul_nonneg (by positivity)
        apply Finset.prod_nonneg
        intro i hi
        exact hd (s i)
    have hOddNonempty : Nonempty (OddRole5 n) := by
      let even : CubeVertex n := fun _ => false
      have heven : IsEvenRole even := by simp [IsEvenRole, even]
      let i : Fin n := ⟨0, by omega⟩
      let odd := HypercubeRamsey.cubeFlip even i
      have hodd : ¬ IsEvenRole odd := by
        intro hodd
        exact ((HypercubeRamsey.cubeFlip_parity even i).mp hodd) heven
      exact ⟨⟨odd, hodd⟩⟩
    letI : Nonempty (OddRole5 n) := hOddNonempty
    let ZRole : OddRole5 n → X.LowHid → ℝ := fun r lo => Z lo r y
    have hMoment := HypercubeRamsey.scattered_moments
      (w := ν.w) (hw := fun lo => ν.nonneg lo)
      (succ := Finset.univ) (Z := fun r lo => ZRole r lo)
      (hZ0 := by intro r lo; exact hZ.nonneg lo r y)
      (L := L) hL (hZL := by intro r lo _; exact hZ.cap lo r y)
      (near := near) (hself := hSelf) (f := f) (hnear := hNearCard)
      (n := n) (K := 2) (by norm_num) (d := d) (hd := hd)
      (hjoint := hJoint)
    have hAvgMoment : ν.expect (fun lo => avg lo y ^ n) ≤
        (2 : ℝ) ^ n * ((Fintype.card (OddRole5 n) : ℝ)⁻¹ *
          ∑ r, d r + (n : ℝ) * f * L) ^ n := by
      simpa [avg, FinProb.expect] using hMoment
    have hMeanMoment :
        (Fintype.card (OddRole5 n) : ℝ)⁻¹ * ∑ r, d r + (n : ℝ) * f * L ≤
          4 * (C₁ + 1) := by
      have hprod : (n : ℝ) * f * L ≤ 1 := by
        simpa [L, mul_assoc] using hEventBound
      linarith [hMeanBound]
    have hMeanBaseNonneg :
        0 ≤ (Fintype.card (OddRole5 n) : ℝ)⁻¹ * ∑ r, d r := by
      apply mul_nonneg (inv_nonneg.mpr (Nat.cast_nonneg _))
      exact Finset.sum_nonneg fun r _ => hd r
    have hMeanMomentNonneg :
        0 ≤ (Fintype.card (OddRole5 n) : ℝ)⁻¹ * ∑ r, d r + (n : ℝ) * f * L :=
      add_nonneg hMeanBaseNonneg (by positivity)
    have hMomentBound : ν.expect (fun lo => avg lo y ^ n) ≤
        (8 * (C₁ + 1)) ^ n := by
      calc
        ν.expect (fun lo => avg lo y ^ n) ≤
            (2 : ℝ) ^ n * ((Fintype.card (OddRole5 n) : ℝ)⁻¹ *
              ∑ r, d r + (n : ℝ) * f * L) ^ n := hAvgMoment
        _ ≤ (2 : ℝ) ^ n * (4 * (C₁ + 1)) ^ n :=
          mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hMeanMomentNonneg
            hMeanMoment n) (by positivity)
        _ = (8 * (C₁ + 1)) ^ n := by rw [← mul_pow]; ring_nf
    have hPowEvent (lo : X.LowHid) (hbad : C₂ < avg lo y) :
        C₂ ^ n ≤ avg lo y ^ n := by
      exact pow_le_pow_left₀ (le_of_lt hC₂) hbad.le n
    have hMarkov : ν.pr (fun lo => C₂ ^ n ≤ avg lo y ^ n) ≤
        ν.expect (fun lo => avg lo y ^ n) / C₂ ^ n :=
      FinProb.markov ν (fun lo => avg lo y ^ n) (C₂ ^ n)
        (fun lo => pow_nonneg (hAvgNonneg lo) n) (by positivity)
    have hBadLe : ν.pr (fun lo => C₂ < avg lo y) ≤
        ν.pr (fun lo => C₂ ^ n ≤ avg lo y ^ n) :=
      FinProb.pr_mono ν _ _ (fun lo hbad => hPowEvent lo hbad)
    have hDenom :
        (8 * (C₁ + 1)) ^ n / C₂ ^ n ≤ (1 / 4 : ℝ) ^ n := by
      rw [← div_pow]
      have hRatio : (8 * (C₁ + 1)) / C₂ = 1 / 4 := by
        dsimp [C₂]
        field_simp [ne_of_gt (add_pos hC₁ (by norm_num : (0 : ℝ) < 1))]
        <;> ring
      rw [hRatio]
    calc
      ν.pr (fun lo => C₂ < avg lo y) ≤
          ν.expect (fun lo => avg lo y ^ n) / C₂ ^ n := hBadLe.trans hMarkov
      _ ≤ (8 * (C₁ + 1)) ^ n / C₂ ^ n :=
        div_le_div_of_nonneg_right hMomentBound (by positivity)
      _ ≤ (1 / 4 : ℝ) ^ n := hDenom
  have hUnion := FinProb.pr_exists_le_sum5 ν (fun y lo => C₂ < avg lo y)
  calc
    ν.pr (fun lo => ∃ y, C₂ < avg lo y) ≤
        ∑ y : Fin N, ν.pr (fun lo => C₂ < avg lo y) := by
      simpa using hUnion
    _ ≤ ∑ _y : Fin N, (1 / 4 : ℝ) ^ n := by
      apply Finset.sum_le_sum
      intro y hy
      exact hPerLabel y
    _ = (N : ℝ) * (1 / 4 : ℝ) ^ n := by simp
    _ ≤ 1 / 100 := hTailN


/-! ### The successful key history (05:742–744) -/

/-- A good key history (05:742–744): base and realized columns in raw support, parent in the support,
Steps 1 and 2 pass, and every occurring abstract record has its conditional Step 3 failure bound over fresh arrays. -/
structure KeyGood5 (H : X.KeyHist) (cL cH : ℝ) : Prop where
  parent_mem : H.1.1 ∈ X.P.lab0
  step1 : X.Step1Pass H.1
  step2 : X.Step2Pass H
  step3 : ∀ r : X.AbsRecord, X.RecOccurs r →
    X.step3Rate H r ≤ X.step3Scale (match r.1 with | .inl _ => cL / 4 | .inr _ => cH / 6) r.1
  base_support : X.baseLaw.w H.1 ≠ 0
  key_support : ∀ ℓ h, (X.prior H.1 ℓ).w (H.2 ℓ h) ≠ 0

/-- A successful key history: good, and the two history odd-load averages are bounded (the second for a given
proxy-mean functional) (05:1007–1041). -/
structure KeySuccess5 (H : X.KeyHist) (cL cH C : ℝ) (Zbar : X.KeyHist → OddRole5 n → Fin N → ℝ) : Prop where
  good : X.KeyGood5 H cL cH
  load_prior : ∀ y, X.avgLowPrior H.1 y ≤ C
  load_proxy : ∀ y, (Fintype.card (OddRole5 n) : ℝ)⁻¹ * ∑ r, Zbar H r y ≤ C

end Setup5

end

end HypercubeRamsey
