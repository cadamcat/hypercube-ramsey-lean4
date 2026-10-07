import HypercubeRamsey.S18.Endpoints

namespace HypercubeRamsey.Lane_q_s18_n6

open Classical Filter
open HypercubeRamsey.S18
open scoped BigOperators

lemma finLaw_E_nonneg {Ω : Type*} [Fintype Ω] (P : FinLaw Ω) (f : Ω → ℝ)
    (hf : ∀ ω, 0 ≤ f ω) : 0 ≤ P.E f := by
  unfold FinLaw.E
  apply Finset.sum_nonneg
  intro ω hω
  exact mul_nonneg (P.nonneg ω) (hf ω)

lemma finLaw_E_const {Ω : Type*} [Fintype Ω] (P : FinLaw Ω) (r : ℝ) :
    P.E (fun _ => r) = r := by
  unfold FinLaw.E
  rw [← Finset.sum_mul, P.sum_one, one_mul]

lemma finLaw_pr_nonneg {Ω : Type*} [Fintype Ω] (P : FinLaw Ω) (A : Ω → Prop) :
    0 ≤ P.pr A := by
  classical
  unfold FinLaw.pr
  apply Finset.sum_nonneg
  intro ω hω
  split_ifs
  · exact P.nonneg ω
  · exact le_rfl

noncomputable def endpointKernel {κ : CConsts} {T : Stage} {k : ℕ}
    {PT : ProfiledTiling κ T k} {hPT : PT.Valid}
    (D : LateData hPT) (A : InitialPairData D) :
    Pos T k → Fin (T.S.N k) → Fin (T.S.N k) → ℝ := fun v x z =>
  if v ∈ A.rows then
    if v ∈ D.nonisolates A.rows then
      if x ∈ D.palette v ∧ z ∈ D.palette v then
        (D.paletteScale A.paletteIndex)⁻¹ ^ 2
      else 0
    else isolatedWeight D v x z
  else 0

theorem endpointCertificate_of_comparisons {κ : CConsts} {T : Stage} {k : ℕ}
    {PT : ProfiledTiling κ T k} {hPT : PT.Valid} (hκ : κ.Admissible)
    (D : LateData hPT) (δ εterm εrun : ℝ)
    (C : TerminalCertificate D δ εterm) (H : CompletionCertificate D C εrun)
    (hε : εterm ≤ 1)
    (Kpair KL KI Cp Cs CQ : ℝ)
    (hKpair : 0 < Kpair) (hKL : 1 ≤ KL) (hKI : 1 ≤ KI)
    (hCp : 0 < Cp) (hCs : 0 < Cs) (hCQ : 0 < CQ)
    (hPair : PairInitialFacts D δ Kpair) (hIso : IsolateKernelFacts D KI)
    (hEndpoint : ∀ A : InitialPairData D, ∀ assignment,
      endpointProbability D C H A assignment ≤
        Real.exp (Cs * D.geom.r + Cp * A.rows.card * D.rank A.rows) * KL ^ A.rows.card *
          A.termTest C assignment)
    (hCompare : ∀ A : InitialPairData D, ∀ assignment,
      A.termTest C assignment ≤ (1 + εterm) * A.permTest assignment ∧
      A.permTest assignment ≤ 2 * A.permFreshTest assignment ∧
      A.permFreshTest assignment ≤ 2 * A.iidFreshTest assignment)
    (hQueries : ∀ A : InitialPairData D, ∃ Q : PairQueries D A,
      PairQueryBound D A Q ∧
      ∀ assignment, (∀ v ∈ A.rows, A.validPair v (assignment v).1 (assignment v).2) →
        A.iidFreshTest assignment ≤
          Real.exp (0.005 * (T.S.n k : ℝ) * (D.nonisolates A.rows).card +
            CQ * A.rows.card * D.rank A.rows) * (4 : ℝ) ^ Q.count * Q.integral assignment *
              (D.paletteScale A.paletteIndex)⁻¹ ^ (2 * (D.nonisolates A.rows).card) *
              ∏ v ∈ A.rows \ D.nonisolates A.rows,
                isolatedWeight D v (assignment v).1 (assignment v).2) :
    EndpointCertificate D C H (Kpair + KL + KI + 2) (Cp + CQ) (Cs + 10) := by
  classical
  let K : ℝ := Kpair + KL + KI + 2
  have hKpairK : Kpair ≤ K := by dsimp [K]; linarith
  have hKLK : KL ≤ K := by dsimp [K]; linarith
  have hKIK : KI ≤ K := by dsimp [K]; linarith
  have h2K : 2 ≤ K := by dsimp [K]; linarith
  have hKpos : 0 < K := by dsimp [K]; positivity
  have hScale (p : PaletteIndex D) : 0 < D.paletteScale p := by
    dsimp [LateData.paletteScale]
    have hMnat : 0 < (PT.tiling.P p.1).M := by
      rw [← (PT.tiling.P p.1).cardX]
      exact Finset.card_pos.mpr (hPT.tiling_valid.patch_nonempty p.1).1
    have hM : 0 < ((PT.tiling.P p.1).M : ℝ) := by exact_mod_cast hMnat
    have hχ : 0 < (D.chi p.1 : ℝ) := by exact_mod_cast D.chi_pos p.1
    exact div_pos hM hχ
  have hDensity : 0 < densityScale T k := by
    unfold densityScale
    have hN : 0 < (T.S.N k : ℝ) := by exact_mod_cast T.S.N_pos k
    positivity
  have hPair' : PairInitialFacts D δ K := by
    rcases hPair with ⟨hcard, hsize, hdegree, hnonisolates, hfull⟩
    refine ⟨?_, hsize, hdegree, hnonisolates, hfull⟩
    intro p
    have hs := hScale p
    calc
      (D.paletteRows p).card ≤ Kpair * D.paletteScale p / densityScale T k := hcard p
      _ ≤ K * D.paletteScale p / densityScale T k := by
        apply div_le_div_of_nonneg_right _ hDensity.le
        exact mul_le_mul_of_nonneg_right hKpairK hs.le
  refine ⟨hPair', ?_⟩
  intro A
  obtain ⟨Q, hQBound, hReduce⟩ := hQueries A
  let ker := endpointKernel D A
  have hEven (v : Pos T k) (hv : v ∈ A.rows) : IsEvenRole v := by
    have hm : v ∈ D.paletteRows A.paletteIndex := A.rows_subset hv
    exact (Finset.mem_filter.mp hm).2.1
  have hRole (v : Pos T k) (hv : v ∈ A.rows) :
      D.rolePalette v = A.paletteIndex := by
    have hm : v ∈ D.paletteRows A.paletteIndex := A.rows_subset hv
    exact (Finset.mem_filter.mp hm).2.2
  have hPaletteSize (v : Pos T k) (hv : v ∈ A.rows) :
      ((D.palette v).card : ℝ) ≤ 2 * D.paletteScale A.paletteIndex := by
    calc
      ((D.palette v).card : ℝ) =
          ((D.palettes (D.geom.patchOf v) (D.colourOf v)).card : ℝ) := rfl
      _ ≤ 2 * ((PT.tiling.P (D.geom.patchOf v)).M : ℝ) / D.chi (D.geom.patchOf v) :=
          D.palette_size (D.geom.patchOf v) (D.colourOf v)
      _ = 2 * D.paletteScale (D.rolePalette v) := by
          simp only [LateData.rolePalette, LateData.paletteScale]
          field_simp [ne_of_gt (by exact_mod_cast D.chi_pos (D.geom.patchOf v))]
          <;> ring
      _ = 2 * D.paletteScale A.paletteIndex := by rw [hRole v hv]
  have hKernelNonneg (v : Pos T k) (hv : v ∈ A.rows)
      (x z : Fin (T.S.N k)) : 0 ≤ ker v x z := by
    dsimp [ker, endpointKernel]
    simp only [if_pos hv]
    by_cases hn : v ∈ D.nonisolates A.rows
    · simp only [if_pos hn]
      by_cases hp : x ∈ D.palette v ∧ z ∈ D.palette v
      · simp only [if_pos hp]
        exact sq_nonneg ((D.paletteScale A.paletteIndex)⁻¹)
      · simp [hp]
    · simp only [if_neg hn]
      exact (hIso v (hEven v hv) x z).1
  refine ⟨ker, ?_, ?_, ?_, ?_, ?_⟩
  · intro v hv x z
    dsimp [ker, endpointKernel]
    simp only [if_pos hv]
    by_cases hn : v ∈ D.nonisolates A.rows
    · simp only [if_pos hn]
      by_cases hp : x ∈ D.palette v ∧ z ∈ D.palette v
      · simp only [if_pos hp]
        exact sq_nonneg ((D.paletteScale A.paletteIndex)⁻¹)
      · simp [hp]
    · simp only [if_neg hn]
      exact (hIso v (hEven v hv) x z).1
  · intro v hv x z
    dsimp [ker, endpointKernel]
    simp only [if_pos hv]
    by_cases hn : v ∈ D.nonisolates A.rows
    · simp only [if_pos hn]
      by_cases hx : x ∈ D.palette v <;> by_cases hz : z ∈ D.palette v <;>
        simp [hx, hz, and_comm]
    · simp only [if_neg hn]
      exact (hIso v (hEven v hv) x z).2.1
  · intro v hv x
    have hs : 0 < D.paletteScale A.paletteIndex := hScale A.paletteIndex
    dsimp [ker, endpointKernel]
    simp only [if_pos hv]
    by_cases hn : v ∈ D.nonisolates A.rows
    · simp only [if_pos hn]
      by_cases hx : x ∈ D.palette v
      · have hsumle :
            (∑ z, if x ∈ D.palette v ∧ z ∈ D.palette v then
              (D.paletteScale A.paletteIndex)⁻¹ ^ 2 else 0) ≤
              ∑ z, if z ∈ D.palette v then
                (D.paletteScale A.paletteIndex)⁻¹ ^ 2 else 0 := by
          apply Finset.sum_le_sum
          intro z hz
          by_cases hz' : z ∈ D.palette v <;> simp [hx, hz']
        have hsumEq :
            (∑ z, if z ∈ D.palette v then
              (D.paletteScale A.paletteIndex)⁻¹ ^ 2 else 0) =
              (D.palette v).card * (D.paletteScale A.paletteIndex)⁻¹ ^ 2 := by
          simp
        calc
          (∑ z, if x ∈ D.palette v ∧ z ∈ D.palette v then
              (D.paletteScale A.paletteIndex)⁻¹ ^ 2 else 0) ≤
              (D.palette v).card * (D.paletteScale A.paletteIndex)⁻¹ ^ 2 := by
                rw [← hsumEq]
                exact hsumle
          _ ≤ (2 * D.paletteScale A.paletteIndex) *
                (D.paletteScale A.paletteIndex)⁻¹ ^ 2 :=
                mul_le_mul_of_nonneg_right (hPaletteSize v hv) (by positivity)
          _ = 2 / D.paletteScale A.paletteIndex := by
                field_simp [ne_of_gt hs]
                <;> ring
          _ ≤ K / D.paletteScale A.paletteIndex :=
                div_le_div_of_nonneg_right h2K hs.le
      · have hzero :
            (∑ z, if x ∈ D.palette v ∧ z ∈ D.palette v then
              (D.paletteScale A.paletteIndex)⁻¹ ^ 2 else 0) = 0 := by
          apply Finset.sum_eq_zero
          intro z hz
          simp [hx]
        rw [hzero]
        positivity
    · simp only [if_neg hn]
      have hsum := (hIso v (hEven v hv) x x).2.2.1
      rw [hRole v hv] at hsum
      exact le_trans hsum (div_le_div_of_nonneg_right hKIK hs.le)
  · intro v hv x z
    have hs : 0 < D.paletteScale A.paletteIndex := hScale A.paletteIndex
    dsimp [ker, endpointKernel]
    simp only [if_pos hv]
    by_cases hn : v ∈ D.nonisolates A.rows
    · simp only [if_pos hn]
      by_cases hp : x ∈ D.palette v ∧ z ∈ D.palette v
      · simp only [if_pos hp]
        have hExp : 1 ≤ Real.exp (0.01 * (T.S.n k : ℝ)) := by
          apply Real.one_le_exp_iff.mpr
          positivity
        have hmul := mul_le_mul_of_nonneg_left hExp (by positivity :
          0 ≤ (D.paletteScale A.paletteIndex)⁻¹ ^ 2)
        simpa using hmul
      · simp only [if_neg hp]
        positivity
    · simp only [if_neg hn]
      have hbound := (hIso v (hEven v hv) x z).2.2.2
      rw [hRole v hv] at hbound
      exact hbound
  · intro assignment
    by_cases hvalid : ∀ v ∈ A.rows, A.validPair v (assignment v).1 (assignment v).2
    · have htermfactor : 0 ≤ 1 + εterm := by
        have hcmp := C.comparison (∅ : Finset D.geom.Cell)
          (by simp; positivity) (fun _ : D.encoding.InitInput => (1 : ℝ))
          (by norm_num) (by intro x y h; rfl)
        have hT := finLaw_E_const (D.encoding.terminalLaw (terminalSet D δ) C.positive) 1
        have hP := finLaw_E_const D.encoding.permLaw 1
        have hcmp' : 1 ≤ 1 + εterm := by simpa [hT, hP] using hcmp
        linarith
      rcases hCompare A assignment with ⟨h1, h2, h3⟩
      have hPhiNonneg : ∀ s : Config D.fresh, 0 ≤ A.phi assignment s := by
        intro s
        unfold InitialPairData.phi
        by_cases hi : ∀ v ∈ A.rows, D.initialValid v s
        · simp only [if_pos hi]
          apply mul_nonneg
          · positivity
          · apply Finset.prod_nonneg
            intro v hv
            by_cases htest : A.validPair v (assignment v).1 (assignment v).2 ∧
                (D.initialPrior v s).w (assignment v).1 ≠ 0 ∧
                (D.initialPrior v s).w (assignment v).2 ≠ 0
            · have hweight (y : Fin (T.S.N k)) : 0 ≤ D.initialWeight v s y := by
                unfold LateData.initialWeight
                have hσ : 0 ≤ D.sigma v s y := (hi v hv).1.1 y
                have hfactor (a : Fin (T.S.n k)) :
                    0 ≤ (if Hits (T.S.E k) PT.tiling.c y
                      (D.earlyLabel s (flipPos v a)) then (1 : ℝ) else 0) /
                      rowDeg (T.S.E k) PT.tiling.c y
                        (PT.π (D.geom.patchOf (flipPos v a))) := by
                  have hnum : 0 ≤ (if Hits (T.S.E k) PT.tiling.c y
                      (D.earlyLabel s (flipPos v a)) then (1 : ℝ) else 0) := by
                    split_ifs <;> norm_num
                  have hden : 0 ≤ rowDeg (T.S.E k) PT.tiling.c y
                      (PT.π (D.geom.patchOf (flipPos v a))) := by
                    unfold rowDeg
                    apply Finset.sum_nonneg
                    intro z hz
                    apply mul_nonneg
                    · exact (PT.π _).nonneg z
                    · split_ifs <;> norm_num [hit]
                  exact div_nonneg hnum hden
                apply mul_nonneg hσ
                apply Finset.prod_nonneg
                intro a ha
                exact hfactor a
              have hxy := mul_nonneg (hweight (assignment v).1)
                (hweight (assignment v).2)
              simpa only [if_pos htest] using hxy
            · simp [htest]
        · simp [hi]
      have hIidNonneg : 0 ≤ A.iidFreshTest assignment := by
        unfold InitialPairData.iidFreshTest
        apply finLaw_E_nonneg
        intro pools
        by_cases htyp : ∀ C ∈ A.scope, D.fresh.typical C (pools C)
        · simp only [if_pos htyp]
          apply finLaw_E_nonneg
          exact hPhiNonneg
        · simp [htyp]
      have htermBound : A.termTest C assignment ≤ 8 * A.iidFreshTest assignment := by
        calc
          A.termTest C assignment ≤ (1 + εterm) * A.permTest assignment := h1
          _ ≤ (1 + εterm) * (2 * A.permFreshTest assignment) :=
            mul_le_mul_of_nonneg_left h2 htermfactor
          _ ≤ (1 + εterm) * (2 * (2 * A.iidFreshTest assignment)) :=
            mul_le_mul_of_nonneg_left
              (mul_le_mul_of_nonneg_left h3 (by norm_num)) htermfactor
          _ = 4 * (1 + εterm) * A.iidFreshTest assignment := by ring
          _ ≤ 8 * A.iidFreshTest assignment := by
            exact mul_le_mul_of_nonneg_right (by nlinarith [hε]) hIidNonneg
      have hRowsSubset : D.nonisolates A.rows ⊆ A.rows := by
        intro v hv
        exact (Finset.mem_filter.mp hv).1
      have hRowsSplit : D.nonisolates A.rows ∪ (A.rows \ D.nonisolates A.rows) = A.rows := by
        exact Finset.union_sdiff_of_subset hRowsSubset
      have hKernelProd :
          (∏ v ∈ A.rows, ker v (assignment v).1 (assignment v).2) =
            (D.paletteScale A.paletteIndex)⁻¹ ^ (2 * (D.nonisolates A.rows).card) *
              ∏ v ∈ A.rows \ D.nonisolates A.rows,
                isolatedWeight D v (assignment v).1 (assignment v).2 := by
        have hfilterN : A.rows.filter (fun v => v ∈ D.nonisolates A.rows) =
            D.nonisolates A.rows := by
          ext v
          simp only [Finset.mem_filter]
          constructor
          · exact fun h => h.2
          · exact fun h => ⟨hRowsSubset h, h⟩
        have hfilterI : A.rows.filter (fun v => ¬ v ∈ D.nonisolates A.rows) =
            A.rows \ D.nonisolates A.rows := by
          ext v
          simp
        have hpoint (v : Pos T k) (hv : v ∈ A.rows) :
            ker v (assignment v).1 (assignment v).2 =
              if v ∈ D.nonisolates A.rows then
                (D.paletteScale A.paletteIndex)⁻¹ ^ 2
              else isolatedWeight D v (assignment v).1 (assignment v).2 := by
          have hrow := hv
          by_cases hn : v ∈ D.nonisolates A.rows
          · rcases hvalid v hv with ⟨hx, hz, henvx, henvz, hnc⟩
            simp [ker, endpointKernel, hv, hn, hx, hz]
          · simp [ker, endpointKernel, hv, hn]
        have hprodPiece :
            (∏ v ∈ A.rows, ker v (assignment v).1 (assignment v).2) =
              (∏ v ∈ A.rows with v ∈ D.nonisolates A.rows,
                (D.paletteScale A.paletteIndex)⁻¹ ^ 2) *
              (∏ v ∈ A.rows with ¬ v ∈ D.nonisolates A.rows,
                isolatedWeight D v (assignment v).1 (assignment v).2) := by
          calc
            (∏ v ∈ A.rows, ker v (assignment v).1 (assignment v).2) =
                ∏ v ∈ A.rows, if v ∈ D.nonisolates A.rows then
                  (D.paletteScale A.paletteIndex)⁻¹ ^ 2
                else isolatedWeight D v (assignment v).1 (assignment v).2 := by
                  apply Finset.prod_congr rfl
                  intro v hv
                  exact hpoint v hv
            _ = _ := by rw [Finset.prod_ite]
        calc
          _ = (∏ v ∈ D.nonisolates A.rows, (D.paletteScale A.paletteIndex)⁻¹ ^ 2) *
                (∏ v ∈ A.rows \ D.nonisolates A.rows,
                  isolatedWeight D v (assignment v).1 (assignment v).2) := by
                rw [hprodPiece, hfilterN, hfilterI]
          _ = (D.paletteScale A.paletteIndex)⁻¹ ^ (2 * (D.nonisolates A.rows).card) *
                ∏ v ∈ A.rows \ D.nonisolates A.rows,
                  isolatedWeight D v (assignment v).1 (assignment v).2 := by
                rw [Finset.prod_const, pow_mul]
      have hQNonneg : 0 ≤ Q.integral assignment := by
        unfold PairQueries.integral
        apply finLaw_E_nonneg
        intro pools
        by_cases htyp : ∀ q,
            D.fresh.typical (D.geom.cellOf (flipPos (Q.row q) (Q.coordinate q)))
              (pools (D.geom.cellOf (flipPos (Q.row q) (Q.coordinate q))))
        · simp only [if_pos htyp]
          apply finLaw_E_nonneg
          intro s
          apply Finset.prod_nonneg
          intro q hq
          split_ifs <;> norm_num
        · simp [htyp]
      have hQcancel :
          (4 : ℝ) ^ Q.count * Q.integral assignment ≤
            Real.exp (0.005 * (Q.count : ℝ)) := by
        have hpow : (4 : ℝ) ^ Q.count * (4 : ℝ) ^ (-(Q.count : ℤ)) = 1 := by
          rw [zpow_neg, zpow_natCast]
          exact mul_inv_cancel₀ (by positivity)
        calc
          (4 : ℝ) ^ Q.count * Q.integral assignment ≤
              (4 : ℝ) ^ Q.count * ((4 : ℝ) ^ (-(Q.count : ℤ)) *
                Real.exp (0.005 * (Q.count : ℝ))) :=
                mul_le_mul_of_nonneg_left (hQBound assignment hvalid) (by positivity)
          _ = Real.exp (0.005 * (Q.count : ℝ)) := by rw [← mul_assoc, hpow, one_mul]
      have hcount : (Q.count : ℝ) ≤
          (D.nonisolates A.rows).card * (T.S.n k : ℝ) := by
        exact_mod_cast Q.count_bound
      have hExpCount :
          Real.exp (0.005 * (Q.count : ℝ)) ≤
            Real.exp (0.005 * (T.S.n k : ℝ) * (D.nonisolates A.rows).card) := by
        apply Real.exp_le_exp.mpr
        nlinarith [hcount]
      have hIsoProdNonneg : 0 ≤
          (D.paletteScale A.paletteIndex)⁻¹ ^ (2 * (D.nonisolates A.rows).card) *
            ∏ v ∈ A.rows \ D.nonisolates A.rows,
              isolatedWeight D v (assignment v).1 (assignment v).2 := by
        apply mul_nonneg
        · exact pow_nonneg (inv_nonneg.mpr (hScale A.paletteIndex).le) _
        · apply Finset.prod_nonneg
          intro v hv
          have hrow := (Finset.mem_sdiff.mp hv).1
          exact (hIso v (hEven v hrow) (assignment v).1 (assignment v).2).1
      have hIidReduce :
          A.iidFreshTest assignment ≤
            Real.exp (0.01 * (T.S.n k : ℝ) * (D.nonisolates A.rows).card +
                CQ * A.rows.card * D.rank A.rows) *
              ((D.paletteScale A.paletteIndex)⁻¹ ^ (2 * (D.nonisolates A.rows).card) *
                ∏ v ∈ A.rows \ D.nonisolates A.rows,
                  isolatedWeight D v (assignment v).1 (assignment v).2) := by
        have hRed' := hReduce assignment hvalid
        calc
          A.iidFreshTest assignment ≤
              Real.exp (0.005 * (T.S.n k : ℝ) * (D.nonisolates A.rows).card +
                CQ * A.rows.card * D.rank A.rows) *
                ((4 : ℝ) ^ Q.count * Q.integral assignment) *
                ((D.paletteScale A.paletteIndex)⁻¹ ^ (2 * (D.nonisolates A.rows).card) *
                  ∏ v ∈ A.rows \ D.nonisolates A.rows,
                    isolatedWeight D v (assignment v).1 (assignment v).2) := by
              simpa [mul_assoc] using hRed'
          _ ≤ Real.exp (0.005 * (T.S.n k : ℝ) * (D.nonisolates A.rows).card +
                CQ * A.rows.card * D.rank A.rows) *
                Real.exp (0.005 * (Q.count : ℝ)) *
                ((D.paletteScale A.paletteIndex)⁻¹ ^ (2 * (D.nonisolates A.rows).card) *
                  ∏ v ∈ A.rows \ D.nonisolates A.rows,
                    isolatedWeight D v (assignment v).1 (assignment v).2) := by
              exact mul_le_mul_of_nonneg_right
                (mul_le_mul_of_nonneg_left hQcancel (Real.exp_pos _).le) hIsoProdNonneg
          _ ≤ Real.exp (0.005 * (T.S.n k : ℝ) * (D.nonisolates A.rows).card +
                CQ * A.rows.card * D.rank A.rows) *
                Real.exp (0.005 * (T.S.n k : ℝ) * (D.nonisolates A.rows).card) *
                ((D.paletteScale A.paletteIndex)⁻¹ ^ (2 * (D.nonisolates A.rows).card) *
                  ∏ v ∈ A.rows \ D.nonisolates A.rows,
                    isolatedWeight D v (assignment v).1 (assignment v).2) := by
              exact mul_le_mul_of_nonneg_right
                (mul_le_mul_of_nonneg_left hExpCount (Real.exp_pos _).le) hIsoProdNonneg
          _ = _ := by
                have hExpAdd :
                    Real.exp (0.005 * (T.S.n k : ℝ) * (D.nonisolates A.rows).card) *
                      Real.exp (0.005 * (T.S.n k : ℝ) * (D.nonisolates A.rows).card +
                        CQ * A.rows.card * D.rank A.rows) =
                    Real.exp (0.01 * (T.S.n k : ℝ) * (D.nonisolates A.rows).card +
                      CQ * A.rows.card * D.rank A.rows) :=
                  (Real.exp_add _ _).symm.trans (by congr 1 <;> ring)
                calc
                  _ = (Real.exp (0.005 * (T.S.n k : ℝ) * (D.nonisolates A.rows).card) *
                        Real.exp (0.005 * (T.S.n k : ℝ) * (D.nonisolates A.rows).card +
                          CQ * A.rows.card * D.rank A.rows)) *
                        ((D.paletteScale A.paletteIndex)⁻¹ ^ (2 * (D.nonisolates A.rows).card) *
                          ∏ v ∈ A.rows \ D.nonisolates A.rows,
                            isolatedWeight D v (assignment v).1 (assignment v).2) := by ring
                  _ = _ := by rw [hExpAdd]
      have hIidReduce' :
          A.iidFreshTest assignment ≤
            Real.exp (0.01 * (T.S.n k : ℝ) * (D.nonisolates A.rows).card +
              CQ * A.rows.card * D.rank A.rows) *
              ((D.paletteScale A.paletteIndex)⁻¹ ^ (2 * (D.nonisolates A.rows).card) *
                ∏ v ∈ A.rows \ D.nonisolates A.rows,
                  isolatedWeight D v (assignment v).1 (assignment v).2) := by
        simpa [mul_assoc] using hIidReduce
      have hstage : (1 + εterm) * 4 ≤ 8 := by nlinarith [hε]
      have hr : (1 : ℝ) ≤ (D.geom.r : ℝ) := by
        exact_mod_cast D.l16_valid.r_pos
      have hExpEight : 8 ≤ Real.exp (10 * (D.geom.r : ℝ)) := by
        have h := Real.add_one_le_exp (10 * (D.geom.r : ℝ))
        have hArg : (10 : ℝ) ≤ 10 * (D.geom.r : ℝ) := by nlinarith
        have hExp := Real.exp_le_exp.mpr hArg
        linarith
      have hKLpow : KL ^ A.rows.card ≤ K ^ A.rows.card :=
        pow_le_pow_left₀ (by positivity) hKLK _
      have hExponent :
          8 * Real.exp (Cs * (D.geom.r : ℝ) +
              Cp * A.rows.card * D.rank A.rows) *
              Real.exp (0.01 * (T.S.n k : ℝ) * (D.nonisolates A.rows).card +
                CQ * A.rows.card * D.rank A.rows) ≤
            Real.exp ((Cs + 10) * (D.geom.r : ℝ) +
              0.01 * (T.S.n k : ℝ) * (D.nonisolates A.rows).card +
              (Cp + CQ) * A.rows.card * D.rank A.rows) := by
        have hExpAB :
            Real.exp (Cs * (D.geom.r : ℝ) + Cp * A.rows.card * D.rank A.rows) *
              Real.exp (0.01 * (T.S.n k : ℝ) * (D.nonisolates A.rows).card +
                CQ * A.rows.card * D.rank A.rows) =
              Real.exp (Cs * (D.geom.r : ℝ) + Cp * A.rows.card * D.rank A.rows +
                (0.01 * (T.S.n k : ℝ) * (D.nonisolates A.rows).card +
                  CQ * A.rows.card * D.rank A.rows)) := (Real.exp_add _ _).symm
        calc
          8 * Real.exp (Cs * (D.geom.r : ℝ) + Cp * A.rows.card * D.rank A.rows) *
              Real.exp (0.01 * (T.S.n k : ℝ) * (D.nonisolates A.rows).card +
                CQ * A.rows.card * D.rank A.rows) =
            8 * (Real.exp (Cs * (D.geom.r : ℝ) + Cp * A.rows.card * D.rank A.rows) *
              Real.exp (0.01 * (T.S.n k : ℝ) * (D.nonisolates A.rows).card +
                CQ * A.rows.card * D.rank A.rows)) := by ring
          _ = 8 * Real.exp (Cs * (D.geom.r : ℝ) + Cp * A.rows.card * D.rank A.rows +
              (0.01 * (T.S.n k : ℝ) * (D.nonisolates A.rows).card +
                CQ * A.rows.card * D.rank A.rows)) := by rw [hExpAB]
          _ ≤
              Real.exp (10 * (D.geom.r : ℝ)) *
                Real.exp (Cs * (D.geom.r : ℝ) + Cp * A.rows.card * D.rank A.rows +
                  (0.01 * (T.S.n k : ℝ) * (D.nonisolates A.rows).card +
                    CQ * A.rows.card * D.rank A.rows)) :=
            mul_le_mul_of_nonneg_right hExpEight (Real.exp_pos _).le
          _ = Real.exp (10 * (D.geom.r : ℝ) +
                (Cs * (D.geom.r : ℝ) + Cp * A.rows.card * D.rank A.rows +
                  (0.01 * (T.S.n k : ℝ) * (D.nonisolates A.rows).card +
                    CQ * A.rows.card * D.rank A.rows))) := (Real.exp_add _ _).symm
          _ = Real.exp ((Cs + 10) * (D.geom.r : ℝ) +
                0.01 * (T.S.n k : ℝ) * (D.nonisolates A.rows).card +
                (Cp + CQ) * A.rows.card * D.rank A.rows) := by congr 1 <;> ring
      have hFinalExp :
          Real.exp ((Cs + 10) * (D.geom.r : ℝ)) *
            Real.exp (0.01 * (T.S.n k : ℝ) * (D.nonisolates A.rows).card +
              (Cp + CQ) * A.rows.card * D.rank A.rows) =
            Real.exp ((Cs + 10) * (D.geom.r : ℝ) +
              0.01 * (T.S.n k : ℝ) * (D.nonisolates A.rows).card +
              (Cp + CQ) * A.rows.card * D.rank A.rows) := by
        have hArg :
            (Cs + 10) * (D.geom.r : ℝ) +
                (0.01 * (T.S.n k : ℝ) * (D.nonisolates A.rows).card +
                  (Cp + CQ) * A.rows.card * D.rank A.rows) =
              (Cs + 10) * (D.geom.r : ℝ) +
                0.01 * (T.S.n k : ℝ) * (D.nonisolates A.rows).card +
                  (Cp + CQ) * A.rows.card * D.rank A.rows := by ring
        exact (Real.exp_add _ _).symm.trans (congrArg Real.exp hArg)
      calc
        endpointProbability D C H A assignment ≤
            Real.exp (Cs * (D.geom.r : ℝ) + Cp * A.rows.card * D.rank A.rows) *
              KL ^ A.rows.card * A.termTest C assignment := hEndpoint A assignment
        _ ≤ Real.exp (Cs * (D.geom.r : ℝ) + Cp * A.rows.card * D.rank A.rows) *
              KL ^ A.rows.card * (8 * A.iidFreshTest assignment) := by
                exact mul_le_mul_of_nonneg_left htermBound
                  (by positivity : 0 ≤ Real.exp (Cs * (D.geom.r : ℝ) +
                    Cp * A.rows.card * D.rank A.rows) * KL ^ A.rows.card)
        _ ≤ Real.exp (Cs * (D.geom.r : ℝ) + Cp * A.rows.card * D.rank A.rows) *
              K ^ A.rows.card * (8 * A.iidFreshTest assignment) := by
                exact mul_le_mul_of_nonneg_right
                  (mul_le_mul_of_nonneg_left hKLpow
                    (by positivity : 0 ≤ Real.exp (Cs * (D.geom.r : ℝ) +
                      Cp * A.rows.card * D.rank A.rows)))
                  (by positivity : 0 ≤ 8 * A.iidFreshTest assignment)
          _ ≤ Real.exp ((Cs + 10) * (D.geom.r : ℝ)) * K ^ A.rows.card *
                Real.exp (0.01 * (T.S.n k : ℝ) * (D.nonisolates A.rows).card +
                  (Cp + CQ) * A.rows.card * D.rank A.rows) *
                ∏ v ∈ A.rows, ker v (assignment v).1 (assignment v).2 := by
                calc
                  _ = Real.exp (Cs * (D.geom.r : ℝ) +
                        Cp * A.rows.card * D.rank A.rows) * K ^ A.rows.card *
                        (8 * A.iidFreshTest assignment) := by ring
                  _ ≤ Real.exp (Cs * (D.geom.r : ℝ) +
                        Cp * A.rows.card * D.rank A.rows) * K ^ A.rows.card *
                        (8 * (Real.exp (0.01 * (T.S.n k : ℝ) *
                          (D.nonisolates A.rows).card +
                          CQ * A.rows.card * D.rank A.rows) *
                          ((D.paletteScale A.paletteIndex)⁻¹ ^
                            (2 * (D.nonisolates A.rows).card) *
                            ∏ v ∈ A.rows \ D.nonisolates A.rows,
                              isolatedWeight D v (assignment v).1 (assignment v).2))) := by
                        exact mul_le_mul_of_nonneg_left
                          (mul_le_mul_of_nonneg_left hIidReduce' (by norm_num))
                          (by positivity)
                  _ = (8 * Real.exp (Cs * (D.geom.r : ℝ) +
                        Cp * A.rows.card * D.rank A.rows) *
                        Real.exp (0.01 * (T.S.n k : ℝ) *
                          (D.nonisolates A.rows).card +
                          CQ * A.rows.card * D.rank A.rows)) *
                        (K ^ A.rows.card *
                          ((D.paletteScale A.paletteIndex)⁻¹ ^
                            (2 * (D.nonisolates A.rows).card) *
                            ∏ v ∈ A.rows \ D.nonisolates A.rows,
                              isolatedWeight D v (assignment v).1 (assignment v).2)) := by ring
                  _ ≤ _ := by
                        rw [hKernelProd]
                        calc
                          _ ≤ Real.exp ((Cs + 10) * (D.geom.r : ℝ) +
                                0.01 * (T.S.n k : ℝ) * (D.nonisolates A.rows).card +
                                (Cp + CQ) * A.rows.card * D.rank A.rows) *
                                (K ^ A.rows.card *
                                  ((D.paletteScale A.paletteIndex)⁻¹ ^
                                    (2 * (D.nonisolates A.rows).card) *
                                    ∏ v ∈ A.rows \ D.nonisolates A.rows,
                                      isolatedWeight D v (assignment v).1 (assignment v).2)) :=
                                  mul_le_mul_of_nonneg_right hExponent (by positivity)
                          _ = _ := by
                                rw [← hFinalExp]
                                ring
    · have hTermZero : A.termTest C assignment = 0 := by
        push_neg at hvalid
        obtain ⟨v, hv, hnot⟩ := hvalid
        have hphi : ∀ s : Config D.fresh, A.phi assignment s = 0 := by
          intro s
          unfold InitialPairData.phi
          by_cases hi : ∀ v ∈ A.rows, D.initialValid v s
          · simp only [if_pos hi]
            have hfactor :
                (if A.validPair v (assignment v).1 (assignment v).2 ∧
                    (D.initialPrior v s).w (assignment v).1 ≠ 0 ∧
                    (D.initialPrior v s).w (assignment v).2 ≠ 0 then
                  D.initialWeight v s (assignment v).1 *
                    D.initialWeight v s (assignment v).2 else 0) = 0 := by
              simp [hnot]
            have hprod :
                (∏ v ∈ A.rows, if A.validPair v (assignment v).1 (assignment v).2 ∧
                    (D.initialPrior v s).w (assignment v).1 ≠ 0 ∧
                    (D.initialPrior v s).w (assignment v).2 ≠ 0 then
                  D.initialWeight v s (assignment v).1 *
                    D.initialWeight v s (assignment v).2 else 0) = 0 :=
              Finset.prod_eq_zero hv hfactor
            rw [hprod]
            simp
          · simp [hi]
        unfold InitialPairData.termTest
        simp [hphi, FinLaw.E]
      have hprobNonneg : 0 ≤ endpointProbability D C H A assignment := by
        unfold endpointProbability
        exact finLaw_pr_nonneg _ _
      have hprobZero : endpointProbability D C H A assignment = 0 := by
        have h := hEndpoint A assignment
        rw [hTermZero] at h
        linarith
      rw [hprobZero]
      have hkernelProduct : 0 ≤ ∏ v ∈ A.rows, ker v (assignment v).1 (assignment v).2 := by
        apply Finset.prod_nonneg
        intro v hv
        exact hKernelNonneg v hv (assignment v).1 (assignment v).2
      have hbaseNonneg : 0 ≤ Real.exp ((Cs + 10) * (D.geom.r : ℝ)) *
          K ^ A.rows.card *
          Real.exp (0.01 * (T.S.n k : ℝ) * (D.nonisolates A.rows).card +
            (Cp + CQ) * A.rows.card * D.rank A.rows) := by positivity
      exact mul_nonneg hbaseNonneg hkernelProduct

end HypercubeRamsey.Lane_q_s18_n6
