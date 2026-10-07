import HypercubeRamsey.S13.ResidualBounds_q_s13_resid

namespace HypercubeRamsey.Lane_q_s13_resid_cluster

open HypercubeRamsey
open Classical
open scoped BigOperators

theorem cleaned_clusterWitnessAt
    (κ : CConsts) (S : Stage) (k : ℕ)
    (RX RY : Finset (Fin (S.S.N k))) (b : ℕ) (ζ δ : ℝ)
    (hRX : RX ⊆ S.X k) (hRY : RY ⊆ S.Y k)
    (hClu : CluScaleWitness κ S k RX RY b false)
    (hClean : HypercubeRamsey.Lane_q_s13_resid.CleanClusterBinsAux
      κ S k RX RY b false)
    (hUwidth : (b : ℝ) ^ κ.aC ≤ (S.S.n k : ℝ) ^ δ)
    (hMixwidth : (b : ℝ) ^ κ.aC + Real.log 4 ≤ (S.S.n k : ℝ) ^ δ)
    (hBinAtom : Real.exp ((S.S.n k : ℝ) ^ ζ) ≤ Real.exp (b : ℝ) / 2)
    (hSmall : (S.S.n k : ℝ) ^ (-κ.η0) + (S.S.n k : ℝ) ^ (-δ) ≤
      min (κ.θ / 4) (1 / 4 : ℝ))
    (hCodegree : ∀ (N : ℕ) (E : Fin N → Fin N → Prop) (c : Colour)
      (μ : Law N) (y y' : Fin N),
      (∑ x : Fin N, μ.w x * hit E c x y * hit E c x y') =
        (1 + (if c then 1 else -1) * (2 * colDeg E true μ y - 1) +
          (if c then 1 else -1) * (2 * colDeg E true μ y' - 1) +
          pairCorr E false μ y y') / 4) :
    ClusterWitnessAt S k true ζ δ := by
  rcases hClu with ⟨U, hU, m, B, hUs, hBs, hDisj, hBins, hUmass, hVmass, hCorr⟩
  have hUs' : U ⊆ RX := by simpa using hUs
  have hBs' : ∀ j, B j ⊆ RY := by intro j; simpa using hBs j
  have hClean' := hClean U hU m B hUs hBs hDisj hBins hUmass hVmass hCorr
  rcases hClean' with ⟨B', hBsub, hBdisj, hBsize, hBmass, hBdeg⟩
  let V' : Finset (Fin (S.S.N k)) := Finset.univ.biUnion B'
  have hNpos : (0 : ℝ) < S.S.N k := by exact_mod_cast S.S.N_pos k
  have hV'pos : 0 < (V'.card : ℝ) := by
    apply lt_of_lt_of_le
      (div_pos (mul_pos hNpos (Real.exp_pos _)) (by norm_num : (0 : ℝ) < 4))
    simpa [V'] using hBmass
  have hV'nonempty : V'.Nonempty := by
    exact Finset.card_pos.mp (by exact_mod_cast hV'pos)
  obtain ⟨y₀, hy₀⟩ := hV'nonempty
  have hy₀' : y₀ ∈ Finset.univ.biUnion B' := by simpa [V'] using hy₀
  obtain ⟨j₀, hj₀, hy₀B'⟩ := Finset.mem_biUnion.mp hy₀'
  have hB'j₀ : (B' j₀).Nonempty := ⟨y₀, hy₀B'⟩
  have hB'disjFin :
      ((↑(Finset.univ : Finset (Fin m)) : Set (Fin m))).PairwiseDisjoint B' := by
    simpa using hBdisj
  have hV'card : V'.card = ∑ j : Fin m, (B' j).card := by
    simpa [V'] using Finset.card_biUnion (s := Finset.univ) hB'disjFin
  let C : Fin m → Finset (Fin (S.S.N k)) := fun j =>
    if h : (B' j).Nonempty then B' j else B' j₀
  have hCnonempty (j : Fin m) : (C j).Nonempty := by
    by_cases hj : (B' j).Nonempty
    · simpa [C, hj] using hj
    · simpa [C, hj] using hB'j₀
  have hCsubset (j : Fin m) : ∃ i : Fin m, C j ⊆ B i := by
    by_cases hj : (B' j).Nonempty
    · refine ⟨j, ?_⟩
      simpa [C, hj] using hBsub j
    · refine ⟨j₀, ?_⟩
      simpa [C, hj] using hBsub j₀
  have hCside (j : Fin m) : C j ⊆ RY := by
    rcases hCsubset j with ⟨i, hi⟩
    exact hi.trans (hBs' i)
  have hCsubsetRet (j : Fin m) : ∃ i : Fin m, C j ⊆ B' i := by
    by_cases hj : (B' j).Nonempty
    · refine ⟨j, ?_⟩
      simpa [C, hj]
    · refine ⟨j₀, ?_⟩
      simpa [C, hj]
  let μ : Law (S.S.N k) := Law.unifCore U hU
  let D : Fin m → Law (S.S.N k) := fun j => Law.unifCore (C j) (hCnonempty j)
  let lam : Fin m → ℝ := fun j => (B' j).card / (V'.card : ℝ)
  have hμwidthBase : μ.WidthLE ((b : ℝ) ^ κ.aC) := by
    have hApos : 0 < (U.card : ℝ) := by exact_mod_cast (Finset.card_pos.mpr hU)
    have hrecip : (U.card : ℝ)⁻¹ ≤
        Real.exp ((b : ℝ) ^ κ.aC) / (S.S.N k : ℝ) := by
      calc
        (U.card : ℝ)⁻¹ ≤
            ((S.S.N k : ℝ) * Real.exp (-((b : ℝ) ^ κ.aC)))⁻¹ := by
              simpa only [one_div] using
                (one_div_le_one_div_of_le (mul_pos hNpos (Real.exp_pos _)) hUmass)
        _ = Real.exp ((b : ℝ) ^ κ.aC) / (S.S.N k : ℝ) := by
          rw [Real.exp_neg]
          field_simp [ne_of_gt hNpos, ne_of_gt (Real.exp_pos ((b : ℝ) ^ κ.aC))]
    intro x
    by_cases hx : x ∈ U
    · simpa [μ, Law.unifCore, hx] using hrecip
    · simpa [μ, Law.unifCore, hx] using
        (div_nonneg (Real.exp_nonneg _) (Nat.cast_nonneg _))
  have hμwidth : μ.WidthLE ((S.S.n k : ℝ) ^ δ) :=
    Law.WidthLE.mono hμwidthBase (by linarith [hUwidth])
  have hμsupport : μ.SupportedIn (S.X k) := by
    intro x hx
    have hxU : x ∉ U := fun hx' => hx (hRX (hUs' hx'))
    simp [μ, Law.unifCore, hxU]
  have hDsupport : ∀ j, (D j).SupportedIn (S.Y k) := by
    intro j x hx
    have hxC : x ∉ C j := fun hx' => hx (hRY (hCside j hx'))
    simp [D, Law.unifCore, hxC]
  have hCsize (j : Fin m) : Real.exp ((S.S.n k : ℝ) ^ ζ) ≤ (C j).card := by
    by_cases hj : (B' j).Nonempty
    · have hjNotEmpty : B' j ≠ ∅ := Finset.nonempty_iff_ne_empty.mp hj
      have hhalf : ((B j).card : ℝ) / 2 ≤ (B' j).card := by
        rcases hBsize j with hempty | hhalf
        · exact False.elim (hjNotEmpty hempty)
        · exact hhalf
      have hbinHalf : Real.exp (b : ℝ) / 2 ≤ (B' j).card := by
        have hbin := hBins j
        have hbinReal : Real.exp (b : ℝ) ≤ (B j).card := hbin
        exact le_trans (div_le_div_of_nonneg_right hbinReal (by norm_num : (0 : ℝ) ≤ 2)) hhalf
      simpa [C, hj] using le_trans hBinAtom hbinHalf
    · have hCj0 : C j = B' j₀ := by simp [C, hj]
      have hhalf : ((B j₀).card : ℝ) / 2 ≤ (B' j₀).card := by
        rcases hBsize j₀ with hempty | hhalf
        · exact False.elim (Finset.nonempty_iff_ne_empty.mp hB'j₀ hempty)
        · exact hhalf
      have hbinHalf : Real.exp (b : ℝ) / 2 ≤ (B' j₀).card := by
        have hbinReal : Real.exp (b : ℝ) ≤ (B j₀).card := hBins j₀
        exact le_trans (div_le_div_of_nonneg_right hbinReal (by norm_num : (0 : ℝ) ≤ 2)) hhalf
      rw [hCj0]
      exact le_trans hBinAtom hbinHalf
  have hDatom : ∀ j y, (D j).w y ≤ Real.exp (-((S.S.n k : ℝ) ^ ζ)) := by
    intro j y
    by_cases hy : y ∈ C j
    · have hcardpos : 0 < ((C j).card : ℝ) := by
        exact_mod_cast (Finset.card_pos.mpr (hCnonempty j))
      have hrecip : ((C j).card : ℝ)⁻¹ ≤
          Real.exp (-((S.S.n k : ℝ) ^ ζ)) := by
        calc
          ((C j).card : ℝ)⁻¹ ≤ (Real.exp ((S.S.n k : ℝ) ^ ζ))⁻¹ :=
            by
              simpa only [one_div] using
                (one_div_le_one_div_of_le (Real.exp_pos _) (hCsize j))
          _ = Real.exp (-((S.S.n k : ℝ) ^ ζ)) := by rw [Real.exp_neg]
      simpa [D, Law.unifCore, hy] using hrecip
    · simp [D, Law.unifCore, hy]
      positivity
  have hlam_nonneg : ∀ j, 0 ≤ lam j := by
    intro j
    dsimp [lam]
    exact div_nonneg (Nat.cast_nonneg _) (le_of_lt hV'pos)
  have hlam_sum : ∑ j, lam j = 1 := by
    have hsum : (∑ j : Fin m, ((B' j).card : ℝ)) = (V'.card : ℝ) := by
      exact_mod_cast hV'card.symm
    dsimp [lam]
    rw [← Finset.sum_div, hsum]
    exact div_self (ne_of_gt hV'pos)
  have hterm (j : Fin m) (y : Fin (S.S.N k)) :
      lam j * (D j).w y = if y ∈ B' j then (V'.card : ℝ)⁻¹ else 0 := by
    classical
    by_cases hj : (B' j).Nonempty
    · have hcardpos : 0 < ((B' j).card : ℝ) := by
        exact_mod_cast (Finset.card_pos.mpr hj)
      have hDweight : (D j).w y =
          if y ∈ B' j then ((B' j).card : ℝ)⁻¹ else 0 := by
        change (if y ∈ C j then ((C j).card : ℝ)⁻¹ else 0) = _
        by_cases hy : y ∈ B' j <;> simp [C, hj, hy]
      rw [hDweight]
      dsimp [lam]
      by_cases hy : y ∈ B' j
      · simp only [hy, if_pos]
        calc
          ((B' j).card : ℝ) / (V'.card : ℝ) * ((B' j).card : ℝ)⁻¹ =
              ((B' j).card : ℝ) * (V'.card : ℝ)⁻¹ *
                ((B' j).card : ℝ)⁻¹ := by rw [div_eq_mul_inv]
          _ = ((B' j).card : ℝ) * ((B' j).card : ℝ)⁻¹ *
                (V'.card : ℝ)⁻¹ := by ring
          _ = (V'.card : ℝ)⁻¹ := by
                rw [mul_inv_cancel₀ (ne_of_gt hcardpos)]
                ring
      · simp [hy]
    · have hEmpty : B' j = ∅ := Finset.not_nonempty_iff_eq_empty.mp hj
      simp [lam, hEmpty]
  have hmixtureCap : ∀ y, (∑ j, lam j * (D j).w y) ≤ Real.exp ((S.S.n k : ℝ) ^ δ) / (S.S.N k : ℝ) := by
    intro y
    have htermSum :
        (∑ j : Fin m, lam j * (D j).w y) =
          ∑ j : Fin m, (if y ∈ B' j then (V'.card : ℝ)⁻¹ else 0) := by
      apply Finset.sum_congr rfl
      intro j hj
      exact hterm j y
    let I : Finset (Fin m) := Finset.univ.filter fun j => y ∈ B' j
    have hIcard : I.card ≤ 1 := by
      apply Finset.card_le_one.mpr
      intro i hi j hj
      by_contra hij
      have hyi := (Finset.mem_filter.mp hi).2
      have hyj := (Finset.mem_filter.mp hj).2
      have hdis : Disjoint (B' i) (B' j) := hBdisj (by simp) (by simp) hij
      exact (Finset.disjoint_left.mp hdis hyi) hyj
    have hsumIndicator :
        (∑ j : Fin m, (if y ∈ B' j then (V'.card : ℝ)⁻¹ else 0)) =
          (I.card : ℝ) * (V'.card : ℝ)⁻¹ := by
      simp [I, Finset.sum_ite, Finset.sum_const, nsmul_eq_mul]
    have hrecip : (V'.card : ℝ)⁻¹ ≤ Real.exp ((S.S.n k : ℝ) ^ δ) / (S.S.N k : ℝ) := by
      have hrecip' : (V'.card : ℝ)⁻¹ ≤
          ((S.S.N k : ℝ) * Real.exp (-((b : ℝ) ^ κ.aC)) / 4)⁻¹ := by
        simpa only [one_div] using
          (one_div_le_one_div_of_le
            (div_pos (mul_pos hNpos (Real.exp_pos _)) (by norm_num : (0 : ℝ) < 4))
            hBmass)
      have hexp4 : 4 * Real.exp ((b : ℝ) ^ κ.aC) ≤
          Real.exp ((S.S.n k : ℝ) ^ δ) := by
        calc
          4 * Real.exp ((b : ℝ) ^ κ.aC) =
              Real.exp (Real.log 4) * Real.exp ((b : ℝ) ^ κ.aC) := by
                rw [Real.exp_log (by norm_num : (0 : ℝ) < 4)]
          _ = Real.exp (Real.log 4 + (b : ℝ) ^ κ.aC) := by rw [← Real.exp_add]
          _ ≤ Real.exp ((S.S.n k : ℝ) ^ δ) :=
            Real.exp_le_exp.mpr (by linarith [hMixwidth])
      calc
        (V'.card : ℝ)⁻¹ ≤
            ((S.S.N k : ℝ) * Real.exp (-((b : ℝ) ^ κ.aC)) / 4)⁻¹ := hrecip'
        _ = 4 * Real.exp ((b : ℝ) ^ κ.aC) / (S.S.N k : ℝ) := by
          rw [Real.exp_neg]
          field_simp [ne_of_gt hNpos, ne_of_gt (Real.exp_pos ((b : ℝ) ^ κ.aC))]
        _ ≤ Real.exp ((S.S.n k : ℝ) ^ δ) / (S.S.N k : ℝ) :=
          div_le_div_of_nonneg_right hexp4 (by positivity)
    have hIle : (I.card : ℝ) * (V'.card : ℝ)⁻¹ ≤ (V'.card : ℝ)⁻¹ := by
      have hIcardReal : (I.card : ℝ) ≤ 1 := by exact_mod_cast hIcard
      have hInvNonneg : 0 ≤ (V'.card : ℝ)⁻¹ := inv_nonneg.mpr (le_of_lt hV'pos)
      simpa only [one_mul] using mul_le_mul_of_nonneg_right hIcardReal hInvNonneg
    rw [htermSum, hsumIndicator]
    exact le_trans hIle hrecip
  have hD_codeg : ∀ j y y', 0 < (D j).w y → 0 < (D j).w y' →
      1 / 4 + (S.S.n k : ℝ) ^ (-δ) ≤
        ∑ x, μ.w x * hit (S.S.E k) true x y * hit (S.S.E k) true x y' := by
    intro j y y' hy hy'
    have hyC : y ∈ C j := by
      by_contra hnot
      have := (D j).w y
      simp [D, Law.unifCore, hnot] at hy
    have hy'C : y' ∈ C j := by
      by_contra hnot
      have := (D j).w y'
      simp [D, Law.unifCore, hnot] at hy'
    rcases hCsubsetRet j with ⟨i, hi⟩
    have hyB' : y ∈ B' i := hi hyC
    have hy'B' : y' ∈ B' i := hi hy'C
    have hyB : y ∈ B i := hBsub i hyB'
    have hy'B : y' ∈ B i := hBsub i hy'B'
    have hdegY : |colDeg (S.S.E k) true μ y - 1 / 2| ≤
        (S.S.n k : ℝ) ^ (-κ.η0) := by
      simpa [μ] using hBdeg i y hyB'
    have hdegY' : |colDeg (S.S.E k) true μ y' - 1 / 2| ≤
        (S.S.n k : ℝ) ^ (-κ.η0) := by
      simpa [μ] using hBdeg i y' hy'B'
    by_cases hEq : y = y'
    · subst y'
      have hdiag :
          (∑ x, μ.w x * hit (S.S.E k) true x y * hit (S.S.E k) true x y) =
            colDeg (S.S.E k) true μ y := by
        unfold colDeg
        apply Finset.sum_congr rfl
        intro x hx
        by_cases hxHit : Hits (S.S.E k) true x y <;>
          simp [hit, hxHit] <;> ring
      have hdegLower : 1 / 2 - (S.S.n k : ℝ) ^ (-κ.η0) ≤
          colDeg (S.S.E k) true μ y := by
        have h := (abs_le.mp hdegY).1
        linarith
      rw [hdiag]
      have hsmallDiag : (S.S.n k : ℝ) ^ (-κ.η0) +
          (S.S.n k : ℝ) ^ (-δ) ≤ 1 / 4 := hSmall.trans (min_le_right _ _)
      linarith
    · have hcodegree := hCodegree (S.S.N k) (S.S.E k) true μ y y'
      have hcorr := hCorr i y hyB y' hy'B hEq
      have hmean1 : -2 * (S.S.n k : ℝ) ^ (-κ.η0) ≤
          2 * colDeg (S.S.E k) true μ y - 1 := by
        have h := (abs_le.mp hdegY).1
        linarith
      have hmean2 : -2 * (S.S.n k : ℝ) ^ (-κ.η0) ≤
          2 * colDeg (S.S.E k) true μ y' - 1 := by
        have h := (abs_le.mp hdegY').1
        linarith
      have hsmallTheta : (S.S.n k : ℝ) ^ (-κ.η0) +
          (S.S.n k : ℝ) ^ (-δ) ≤ κ.θ / 4 := hSmall.trans (min_le_left _ _)
      have hresult : 1 / 4 + (S.S.n k : ℝ) ^ (-δ) ≤
          (1 + (2 * colDeg (S.S.E k) true μ y - 1) +
            (2 * colDeg (S.S.E k) true μ y' - 1) +
            pairCorr (S.S.E k) false μ y y') / 4 := by
        linarith
      rw [hcodegree]
      simpa using hresult
  refine ⟨m, μ, lam, D, hμsupport, hDsupport, hlam_nonneg, hlam_sum,
    hμwidth, hmixtureCap, hDatom, hD_codeg⟩

end HypercubeRamsey.Lane_q_s13_resid_cluster
