import HypercubeRamsey.S12.Exceptional
import HypercubeRamsey.Framework.LawLemmas
import HypercubeRamsey.S13.ResidualScales

/-!
Lane-local helpers for the Section 13 residual scale bounds.
-/

namespace HypercubeRamsey.Lane_q_s13_resid

open HypercubeRamsey
open Filter
open Classical
open scoped BigOperators

/-- The clean-bin contract, duplicated here to keep helper definitions out of the
owned source declarations. It is definitionally equal to `S13.CleanClusterBins`. -/
def CleanClusterBinsAux (κ : CConsts) (T : Stage) (k : ℕ)
    (RX RY : Finset (Fin (T.S.N k))) (b : ℕ) (o : Bool) : Prop :=
  ∀ (U : Finset (Fin (T.S.N k))) (hU : U.Nonempty) (m : ℕ)
    (B : Fin m → Finset (Fin (T.S.N k))),
    U ⊆ (if o then RY else RX) →
    (∀ j, B j ⊆ (if o then RX else RY)) →
    Set.PairwiseDisjoint Set.univ B →
    (∀ j, Real.exp b ≤ (B j).card) →
    (T.S.N k : ℝ) * Real.exp (-(b : ℝ) ^ κ.aC) ≤ U.card →
    (T.S.N k : ℝ) * Real.exp (-(b : ℝ) ^ κ.aC) ≤ (Finset.univ.biUnion B).card →
    (∀ j, ∀ y ∈ B j, ∀ y' ∈ B j, y ≠ y' →
      κ.θ < pairCorr (T.S.E k) o (Law.unifCore U hU) y y') →
    ∃ B' : Fin m → Finset (Fin (T.S.N k)),
      (∀ j, B' j ⊆ B j) ∧ Set.PairwiseDisjoint Set.univ B' ∧
      (∀ j, B' j = ∅ ∨ ((B j).card : ℝ) / 2 ≤ (B' j).card) ∧
      (T.S.N k : ℝ) * Real.exp (-(b : ℝ) ^ κ.aC) / 4 ≤
        (Finset.univ.biUnion B').card ∧
      ∀ j y, y ∈ B' j →
        |(if o then rowDeg (T.S.E k) true y (Law.unifCore U hU)
          else colDeg (T.S.E k) true (Law.unifCore U hU) y) - 1 / 2| ≤
          (T.S.n k : ℝ) ^ (-κ.η0)

private theorem twoBudget_swap {T : Stage} {k : ℕ} {wS wL err : ℝ}
    (hD : TwoBudgetDisc T k wS wL err) :
    TwoBudgetDisc T.swap k wS wL err := by
  cases T with
  | mk S X Y hsmall =>
    dsimp [Stage.swap, BadSeq.swap] at *
    intro c μ ν hμ hν hpair
    have hpair' :
        (ν.WidthLE wL ∧ μ.WidthLE wS) ∨ (ν.WidthLE wS ∧ μ.WidthLE wL) := by
      rcases hpair with h | h
      · exact Or.inr ⟨h.2, h.1⟩
      · exact Or.inl ⟨h.2, h.1⟩
    have h := hD c ν μ hν hμ hpair'
    have hEq : dens (transposeRel (S.E k)) c μ ν = dens (S.E k) c ν μ :=
      dens_transpose (S.E k) c μ ν
    calc
      |dens (transposeRel (S.E k)) c μ ν - 1 / 2| =
          |dens (S.E k) c ν μ - 1 / 2| := by rw [hEq]
      _ ≤ err := h

private theorem colDeg_transpose_aux {N : ℕ} (E : Fin N → Fin N → Prop)
    (μ : Law N) (y : Fin N) :
    colDeg (transposeRel E) true μ y = rowDeg E true y μ := by
  unfold colDeg rowDeg
  apply Finset.sum_congr rfl
  intro x hx
  simp [hits_transpose]

theorem initDisc_swap {T : Stage} {η0 : ℝ}
    (hInit : InitDisc T η0) : InitDisc T.swap η0 := by
  change ∀ᶠ k in atTop,
    TwoBudgetDisc T k ((T.S.n k : ℝ) ^ η0) ((T.S.n k : ℝ) ^ η0)
      ((T.S.n k : ℝ) ^ (-η0)) at hInit
  change ∀ᶠ k in atTop,
    TwoBudgetDisc T.swap k ((T.S.n k : ℝ) ^ η0) ((T.S.n k : ℝ) ^ η0)
      ((T.S.n k : ℝ) ^ (-η0))
  filter_upwards [hInit] with k hk
  exact twoBudget_swap hk

theorem cluWitness_swap_aux (κ : CConsts) (T : Stage) (k : ℕ)
    (RX RY : Finset (Fin (T.S.N k))) (b : ℕ)
    (h : CluScaleWitness κ T k RX RY b true) :
    CluScaleWitness κ T.swap k RY RX b false := by
  dsimp [Stage.swap, BadSeq.swap]
  rcases h with ⟨U, hU, m, B, hUs, hBs, hdisj, hBins, hUcard, hBcard, hcorr⟩
  have hUs' : U ⊆ RY := by simpa using hUs
  have hBs' : ∀ j, B j ⊆ RX := by intro j; simpa using hBs j
  refine ⟨U, hU, m, B, hUs', hBs', hdisj, hBins, hUcard, hBcard, ?_⟩
  intro j y hy y' hy' hne
  have hcorr' := hcorr j y hy y' hy' hne
  have hswap : pairCorr (transposeRel (T.S.E k)) false
      (Law.unifCore U hU) y y' = pairCorr (T.S.E k) true
      (Law.unifCore U hU) y y' :=
    HypercubeRamsey.S13.pairCorr_transpose (T.S.E k) false
      (Law.unifCore U hU) y y'
  rw [hswap]
  exact hcorr'

theorem cleanBins_swap_aux (κ : CConsts) (T : Stage) (k : ℕ)
    (RX RY : Finset (Fin (T.S.N k))) (b : ℕ)
    (h : CleanClusterBinsAux κ T k RX RY b true) :
    CleanClusterBinsAux κ T.swap k RY RX b false := by
  dsimp [Stage.swap, BadSeq.swap]
  unfold CleanClusterBinsAux at h ⊢
  intro U hU m B hUs hBs hdisj hBins hUcard hVcard hcorr
  have hUs' : U ⊆ RY := by simpa using hUs
  have hBs' : ∀ j, B j ⊆ RX := by intro j; simpa using hBs j
  have hcorr' : ∀ j, ∀ y ∈ B j, ∀ y' ∈ B j, y ≠ y' →
      κ.θ < pairCorr (T.S.E k) true (Law.unifCore U hU) y y' := by
    intro j y hy y' hy' hne
    have h' := hcorr j y hy y' hy' hne
    have hswap : pairCorr (transposeRel (T.S.E k)) false
        (Law.unifCore U hU) y y' = pairCorr (T.S.E k) true
        (Law.unifCore U hU) y y' :=
      HypercubeRamsey.S13.pairCorr_transpose (T.S.E k) false
        (Law.unifCore U hU) y y'
    rw [hswap] at h'
    exact h'
  rcases h U hU m B hUs' hBs' hdisj hBins hUcard hVcard hcorr' with
    ⟨B', hsub, hdisj', hsize, hmass, hdeg⟩
  refine ⟨B', hsub, hdisj', hsize, hmass, ?_⟩
  intro j y hy
  simpa [Stage.swap, BadSeq.swap, colDeg_transpose_aux] using hdeg j y hy

private theorem clean_fixed_orientation_false
    (κ : CConsts) (hκ : CConsts.Admissible κ) (S : Stage)
    (hInit : InitDisc S κ.η0) :
    ∀ᶠ k in atTop, ∀ RX RY : Finset (Fin (S.S.N k)),
      RX ⊆ S.X k → RY ⊆ S.Y k → ∀ b, IsDyadic b →
        CluScaleWitness κ S k RX RY b false →
          CleanClusterBinsAux κ S k RX RY b false := by
  have hn2 : ∀ᶠ k in atTop, 2 ≤ (S.S.n k : ℝ) := by
    have htend : Tendsto (fun k : ℕ => (S.S.n k : ℝ)) atTop atTop :=
      (tendsto_natCast_atTop_atTop : Tendsto (fun n : ℕ => (n : ℝ)) atTop atTop).comp
        S.S.n_tendsto
    exact htend.eventually (eventually_ge_atTop (2 : ℝ))
  have hgapPos : 0 < κ.η0 - 2 * κ.aC := by
    have hmin : min κ.η0 1 ≤ κ.η0 := min_le_left _ _
    have haC : κ.aC < κ.η0 / 10 ^ 6 := by
      exact lt_of_lt_of_le hκ.aC_rng.2
        (div_le_div_of_nonneg_right hmin (by positivity))
    have hη0 := hκ.η0_pos
    nlinarith
  have hgap : ∀ᶠ k in atTop,
      2 ≤ (S.S.n k : ℝ) ^ (κ.η0 - 2 * κ.aC) := by
    have htend :=
      (tendsto_rpow_atTop hgapPos).comp
        (tendsto_natCast_atTop_atTop.comp S.S.n_tendsto)
    exact htend.eventually (eventually_ge_atTop (2 : ℝ))
  have hmassLarge : ∀ᶠ k in atTop,
      2 * Real.log 8 ≤ (S.S.n k : ℝ) ^ κ.η0 := by
    have htend :=
      (tendsto_rpow_atTop hκ.η0_pos).comp
        (tendsto_natCast_atTop_atTop.comp S.S.n_tendsto)
    exact htend.eventually (eventually_ge_atTop (2 * Real.log 8))
  change ∀ᶠ k in atTop,
    TwoBudgetDisc S k ((S.S.n k : ℝ) ^ κ.η0) ((S.S.n k : ℝ) ^ κ.η0)
      ((S.S.n k : ℝ) ^ (-κ.η0)) at hInit
  filter_upwards [hInit, hn2, hgap, hmassLarge] with k hDisc hn hgap hmass
  intro RX RY hRX hRY b hbdyadic hClu
  unfold CleanClusterBinsAux
  intro U hU m B hUs hBs hdisj hBins hUcard hVmass hcorr
  have hUs' : U ⊆ RX := by simpa using hUs
  have hBs' : ∀ j, B j ⊆ RY := by intro j; simpa using hBs j
  let V : Finset (Fin (S.S.N k)) := Finset.univ.biUnion B
  have hNpos : (0 : ℝ) < S.S.N k := by exact_mod_cast S.S.N_pos k
  have hVlowerPos : 0 < (S.S.N k : ℝ) * Real.exp (-((b : ℝ) ^ κ.aC)) :=
    mul_pos hNpos (Real.exp_pos _)
  have hVcardPos : 0 < (V.card : ℝ) := by
    exact lt_of_lt_of_le hVlowerPos (by simpa [V] using hVmass)
  have hVnonempty1 : V.Nonempty := by
    exact Finset.card_pos.mp (by exact_mod_cast hVcardPos)
  obtain ⟨y₀, hy₀⟩ := hVnonempty1
  have hVnonemptyLaw : V.Nonempty := by
    exact Finset.card_pos.mp (by exact_mod_cast hVcardPos)
  have hy₀' : y₀ ∈ Finset.univ.biUnion B := by simpa [V] using hy₀
  obtain ⟨j₀, hj₀, hy₀B⟩ := Finset.mem_biUnion.mp hy₀'
  have hBcardN : (B j₀).card ≤ S.S.N k := by
    simpa using Finset.card_le_card (Finset.subset_univ (B j₀))
  have hexpB : Real.exp (b : ℝ) ≤ (S.S.N k : ℝ) := by
    have h := hBins j₀
    exact le_trans h (by exact_mod_cast hBcardN)
  have hlogN : (b : ℝ) ≤ Real.log (S.S.N k : ℝ) := by
    calc
      (b : ℝ) = Real.log (Real.exp (b : ℝ)) := by rw [Real.log_exp]
      _ ≤ Real.log (S.S.N k : ℝ) :=
        Real.log_le_log (Real.exp_pos _) hexpB
  have hNupper : (S.S.N k : ℝ) ≤
      (S.S.n k : ℝ) * (2 : ℝ) ^ (S.S.n k) := by
    exact_mod_cast S.S.N_le k
  have hlogNupper : Real.log (S.S.N k : ℝ) ≤ 2 * (S.S.n k : ℝ) := by
    have hlogmul := Real.log_le_log hNpos hNupper
    rw [Real.log_mul (by positivity) (by positivity), Real.log_pow] at hlogmul
    have hlogn : Real.log (S.S.n k : ℝ) ≤ (S.S.n k : ℝ) - 1 :=
      Real.log_le_sub_one_of_pos (by positivity)
    have hlog2 : Real.log 2 ≤ 1 := by
      nlinarith [Real.log_two_lt_d9]
    nlinarith
  have hbLinear : (b : ℝ) ≤ 2 * (S.S.n k : ℝ) := hlogN.trans hlogNupper
  have hnpos : (0 : ℝ) < S.S.n k := by linarith
  have hpowBound : (b : ℝ) ^ κ.aC ≤ (S.S.n k : ℝ) ^ κ.η0 / 2 := by
    have hbase : 2 * (S.S.n k : ℝ) ≤ (S.S.n k : ℝ) ^ 2 := by nlinarith
    have hpow1 := Real.rpow_le_rpow (Nat.cast_nonneg b) hbLinear hκ.aC_rng.1.le
    have hpow2 := Real.rpow_le_rpow (by positivity) hbase hκ.aC_rng.1.le
    have hpowMul : ((S.S.n k : ℝ) ^ (2 : ℕ)) ^ κ.aC =
        (S.S.n k : ℝ) ^ (2 * κ.aC) :=
      calc
        ((S.S.n k : ℝ) ^ (2 : ℕ)) ^ κ.aC =
        ((S.S.n k : ℝ) ^ (2 : ℝ)) ^ κ.aC := by
              exact congrArg (fun x : ℝ => x ^ κ.aC)
                (Real.rpow_natCast (S.S.n k : ℝ) 2).symm
        _ = (S.S.n k : ℝ) ^ (2 * κ.aC) :=
          (Real.rpow_mul (x := (S.S.n k : ℝ)) (by positivity) 2 κ.aC).symm
    have hpowHalf : (S.S.n k : ℝ) ^ (2 * κ.aC) ≤
        (S.S.n k : ℝ) ^ κ.η0 / 2 := by
      have hidentity : (S.S.n k : ℝ) ^ κ.η0 =
          (S.S.n k : ℝ) ^ (2 * κ.aC) *
            (S.S.n k : ℝ) ^ (κ.η0 - 2 * κ.aC) := by
        rw [← Real.rpow_add hnpos]
        congr 1 <;> ring
      rw [hidentity]
      have hmul := mul_le_mul_of_nonneg_left hgap
        (Real.rpow_nonneg hnpos.le (2 * κ.aC))
      nlinarith [Real.rpow_nonneg hnpos.le (2 * κ.aC)]
    calc
      (b : ℝ) ^ κ.aC ≤ (2 * (S.S.n k : ℝ)) ^ κ.aC := hpow1
      _ ≤ ((S.S.n k : ℝ) ^ 2) ^ κ.aC := hpow2
      _ = (S.S.n k : ℝ) ^ (2 * κ.aC) := hpowMul
      _ ≤ (S.S.n k : ℝ) ^ κ.η0 / 2 := hpowHalf
  have uniformWidth {A : Finset (Fin (S.S.N k))} (hA : A.Nonempty)
      (hcard : (S.S.N k : ℝ) * Real.exp (-((b : ℝ) ^ κ.aC)) ≤ A.card) :
      (Law.unifCore A hA).WidthLE ((b : ℝ) ^ κ.aC) := by
    have hApos : 0 < (A.card : ℝ) := by exact_mod_cast (Finset.card_pos.mpr hA)
    have hrecip : (A.card : ℝ)⁻¹ ≤
        Real.exp ((b : ℝ) ^ κ.aC) / (S.S.N k : ℝ) := by
      calc
        (A.card : ℝ)⁻¹ ≤
            ((S.S.N k : ℝ) * Real.exp (-((b : ℝ) ^ κ.aC)))⁻¹ :=
          by
            simpa only [one_div] using
              (one_div_le_one_div_of_le
                (mul_pos hNpos (Real.exp_pos _)) hcard)
        _ = Real.exp ((b : ℝ) ^ κ.aC) / (S.S.N k : ℝ) := by
          rw [Real.exp_neg]
          field_simp [ne_of_gt hNpos, ne_of_gt (Real.exp_pos ((b : ℝ) ^ κ.aC))]
    intro x
    by_cases hx : x ∈ A
    · simpa [Law.unifCore, hx] using hrecip
    · simpa [Law.unifCore, hx] using
        (div_nonneg (Real.exp_nonneg _) (Nat.cast_nonneg _))
  let hτ : Law (S.S.N k) := Law.unifCore U hU
  let hν : Law (S.S.N k) := Law.unifCore V hVnonemptyLaw
  have hτwidth : hτ.WidthLE ((S.S.n k : ℝ) ^ κ.η0) := by
    exact Law.WidthLE.mono
      (uniformWidth hU hUcard) (by
        nlinarith [hpowBound, Real.rpow_nonneg hnpos.le κ.η0])
  have hνwidth : hν.WidthLE ((b : ℝ) ^ κ.aC) :=
    uniformWidth hVnonemptyLaw (by simpa [V] using hVmass)
  have hUsupport : hτ.SupportedIn (S.X k) := by
    intro x hx
    have hxU : x ∉ U := fun hx' => hx (hRX (hUs' hx'))
    simp [hτ, Law.unifCore, hxU]
  have hVsupport : hν.SupportedIn (S.Y k) := by
    intro x hx
    have hxV : x ∉ V := by
      intro hx'
      have hxV' : x ∈ Finset.univ.biUnion B := by simpa [V] using hx'
      rcases Finset.mem_biUnion.mp hxV' with ⟨j, hj, hxj⟩
      exact hx (hRY (hBs' j hxj))
    simp [hν, Law.unifCore, hxV]
  have hExc := HypercubeRamsey.S12.exceptional_second hDisc true
      (Or.inl ⟨le_rfl, le_rfl⟩) hτ hUsupport hτwidth hν hVsupport hνwidth
  let bad : Finset (Fin (S.S.N k)) := V.filter fun y =>
    (S.S.n k : ℝ) ^ (-κ.η0) <
      |colDeg (S.S.E k) true hτ y - 1 / 2|
  let Sbad : Finset (Fin (S.S.N k)) := Finset.univ.filter fun y =>
    (S.S.n k : ℝ) ^ (-κ.η0) <
      |(∑ x, hτ.w x * hit (S.S.E k) true x y) - 1 / 2|
  have hbadSubset : bad ⊆ Sbad := by
    intro y hy
    rcases Finset.mem_filter.mp hy with ⟨hyV, hbad⟩
    apply Finset.mem_filter.mpr
    refine ⟨Finset.mem_univ _, ?_⟩
    simpa only [colDeg, hit] using hbad
  have hsumBad : (∑ y ∈ bad, hν.w y) = (bad.card : ℝ) / (V.card : ℝ) := by
    calc
      (∑ y ∈ bad, hν.w y) = ∑ y ∈ bad, (V.card : ℝ)⁻¹ := by
        apply Finset.sum_congr rfl
        intro y hy
        have hyV := (Finset.mem_filter.mp hy).1
        simp [hν, Law.unifCore, hyV]
      _ = (bad.card : ℝ) / (V.card : ℝ) := by
        simp [div_eq_mul_inv, Finset.sum_const, nsmul_eq_mul]
  have hsumBound : (bad.card : ℝ) / (V.card : ℝ) ≤
      2 * Real.exp ((b : ℝ) ^ κ.aC - (S.S.n k : ℝ) ^ κ.η0) := by
    rw [← hsumBad]
    have hle : (∑ y ∈ bad, hν.w y) ≤ (∑ y ∈ Sbad, hν.w y) := by
      exact Finset.sum_le_sum_of_subset_of_nonneg hbadSubset
        (fun y hy _ => hν.nonneg y)
    have hExc' : (∑ y ∈ Sbad, hν.w y) ≤
        2 * Real.exp ((b : ℝ) ^ κ.aC - (S.S.n k : ℝ) ^ κ.η0) := by
      simpa [Sbad] using hExc
    exact hle.trans hExc'
  have hmassSmall :
      2 * Real.exp ((b : ℝ) ^ κ.aC - (S.S.n k : ℝ) ^ κ.η0) ≤ 1 / 4 := by
    have hexp : (b : ℝ) ^ κ.aC - (S.S.n k : ℝ) ^ κ.η0 ≤
        -((S.S.n k : ℝ) ^ κ.η0) / 2 := by linarith
    have hle := Real.exp_le_exp.mpr hexp
    have hmul := mul_le_mul_of_nonneg_left hle (by norm_num : (0 : ℝ) ≤ 2)
    have hmass' : Real.exp (-((S.S.n k : ℝ) ^ κ.η0) / 2) ≤ 1 / 8 := by
      have hlog8 : 0 < Real.log 8 := Real.log_pos (by norm_num)
      have htarget : Real.exp (-Real.log 8) = (1 / 8 : ℝ) := by
        rw [Real.exp_neg]
        rw [Real.exp_log (by norm_num : (0 : ℝ) < 8)]
        norm_num
      calc
        Real.exp (-((S.S.n k : ℝ) ^ κ.η0) / 2) ≤ Real.exp (-Real.log 8) :=
          Real.exp_le_exp.mpr (by linarith)
        _ = 1 / 8 := htarget
    calc
      2 * Real.exp ((b : ℝ) ^ κ.aC - (S.S.n k : ℝ) ^ κ.η0) ≤
          2 * Real.exp (-((S.S.n k : ℝ) ^ κ.η0) / 2) := hmul
      _ ≤ 2 * (1 / 8) := by exact mul_le_mul_of_nonneg_left hmass' (by norm_num)
      _ = 1 / 4 := by norm_num
  have hbadfrac : (bad.card : ℝ) / (V.card : ℝ) ≤ 1 / 4 :=
    hsumBound.trans hmassSmall
  let B' : Fin m → Finset (Fin (S.S.N k)) := fun j =>
    if (B j \ bad).card * 2 < (B j).card then ∅ else B j \ bad
  have hB'subdiff : ∀ j, B' j ⊆ B j \ bad := by
    intro j y hy
    by_cases hdrop : (B j \ bad).card * 2 < (B j).card
    · simp [B', hdrop] at hy
    · simpa [B', hdrop] using hy
  have hB'sub : ∀ j, B' j ⊆ B j := by
    intro j y hy
    have hsub : B j \ bad ⊆ B j := Finset.sdiff_subset
    exact hsub (hB'subdiff j hy)
  have hB'disj : Set.PairwiseDisjoint Set.univ B' := by
    intro i hi j hj hij
    change Disjoint (B' i) (B' j)
    rw [Finset.disjoint_left]
    intro y hyi hyj
    have hnot := (Finset.disjoint_left.mp (hdisj hi hj hij)) (hB'sub i hyi)
    exact hnot (hB'sub j hyj)
  have hB'size : ∀ j, B' j = ∅ ∨ ((B j).card : ℝ) / 2 ≤ (B' j).card := by
    intro j
    by_cases hdrop : (B j \ bad).card * 2 < (B j).card
    · exact Or.inl (by simp [B', hdrop])
    · right
      have hkeep : (B j).card ≤ 2 * (B j \ bad).card := by omega
      have hkeep' : (B j).card ≤ (B j \ bad).card * 2 := by omega
      have hkeepReal : ((B j).card : ℝ) / 2 ≤ ((B j \ bad).card : ℝ) := by
        apply (div_le_iff₀ (by norm_num : (0 : ℝ) < 2)).2
        exact_mod_cast hkeep'
      simpa [B', hdrop] using hkeepReal
  have hbadPart (j : Fin m) :
      (B j \ bad).card + (B j ∩ bad).card = (B j).card := by
    have heq : B j \ bad = B j \ (B j ∩ bad) := by
      ext y
      simp
    rw [heq]
    exact Finset.card_sdiff_add_card_eq_card Finset.inter_subset_left
  have hbadBinsDisj : Set.PairwiseDisjoint Set.univ (fun j : Fin m => B j ∩ bad) := by
    intro i hi j hj hij
    change Disjoint (B i ∩ bad) (B j ∩ bad)
    rw [Finset.disjoint_left]
    intro y hyi hyj
    exact (Finset.disjoint_left.mp (hdisj hi hj hij)
      (Finset.mem_inter.mp hyi).1) (Finset.mem_inter.mp hyj).1
  have hbadBinsUnion : Finset.univ.biUnion (fun j : Fin m => B j ∩ bad) = bad := by
    ext y
    constructor
    · intro hy
      rcases Finset.mem_biUnion.mp hy with ⟨j, hj, hyj⟩
      exact (Finset.mem_inter.mp hyj).2
    · intro hy
      have hyV := (Finset.mem_filter.mp hy).1
      have hyV' : y ∈ Finset.univ.biUnion B := by simpa [V] using hyV
      rcases Finset.mem_biUnion.mp hyV' with ⟨j, hj, hyj⟩
      apply Finset.mem_biUnion.mpr
      exact ⟨j, hj, Finset.mem_inter.mpr ⟨hyj, hy⟩⟩
  have hbadSum : (∑ j : Fin m, (B j ∩ bad).card) = bad.card := by
    have hbadBinsDisjFin :
        ((↑(Finset.univ : Finset (Fin m)) : Set (Fin m))).PairwiseDisjoint
          (fun j : Fin m => B j ∩ bad) := by
      simpa using hbadBinsDisj
    calc
      (∑ j : Fin m, (B j ∩ bad).card) =
          (Finset.univ.biUnion (fun j : Fin m => B j ∩ bad)).card := by
            symm
            simpa using Finset.card_biUnion (s := Finset.univ) hbadBinsDisjFin
      _ = bad.card := by rw [hbadBinsUnion]
  have hBdisj : Set.PairwiseDisjoint Set.univ B := hdisj
  have hBdisjFin :
      ((↑(Finset.univ : Finset (Fin m)) : Set (Fin m))).PairwiseDisjoint B := by
    simpa using hBdisj
  have hVcardExact : V.card = ∑ j : Fin m, (B j).card := by
    simpa [V] using Finset.card_biUnion (s := Finset.univ) hBdisjFin
  have hV' : Finset.univ.biUnion B' ⊆ V := by
    intro y hy
    rcases Finset.mem_biUnion.mp hy with ⟨j, hj, hyj⟩
    exact Finset.mem_biUnion.mpr ⟨j, hj, hB'sub j hyj⟩
  have hB'disjFin :
      ((↑(Finset.univ : Finset (Fin m)) : Set (Fin m))).PairwiseDisjoint B' := by
    simpa using hB'disj
  have hV'card : (Finset.univ.biUnion B').card = ∑ j : Fin m, (B' j).card := by
    simpa using Finset.card_biUnion (s := Finset.univ) hB'disjFin
  have hsumCard : (V.card : ℝ) ≤
      (Finset.univ.biUnion B').card + 3 * (bad.card : ℝ) := by
    have hpoint : ∀ j : Fin m,
        (B j).card ≤ (B' j).card + 3 * (B j ∩ bad).card := by
      intro j
      by_cases hdrop : (B j \ bad).card * 2 < (B j).card
      · have hparts := hbadPart j
        simp [B', hdrop]
        omega
      · have hparts := hbadPart j
        simp [B', hdrop]
        omega
    have hsum := Finset.sum_le_sum (s := Finset.univ) (fun j hj => hpoint j)
    have hsumNat :
        (∑ j : Fin m, (B j).card) ≤
          (∑ j : Fin m, (B' j).card) +
            3 * (∑ j : Fin m, (B j ∩ bad).card) := by
      simpa [Finset.sum_add_distrib, Finset.mul_sum] using hsum
    have hsumReal :
        (∑ j : Fin m, ((B j).card : ℝ)) ≤
          (∑ j : Fin m, ((B' j).card : ℝ)) +
            3 * (∑ j : Fin m, ((B j ∩ bad).card : ℝ)) := by
      exact_mod_cast hsumNat
    have hVcardReal : (V.card : ℝ) =
        ∑ j : Fin m, ((B j).card : ℝ) := by exact_mod_cast hVcardExact
    have hV'cardReal : ((Finset.univ.biUnion B').card : ℝ) =
        ∑ j : Fin m, ((B' j).card : ℝ) := by exact_mod_cast hV'card
    have hbadSumReal : (bad.card : ℝ) =
        ∑ j : Fin m, ((B j ∩ bad).card : ℝ) := by
      have hcast := congrArg (fun z : ℕ => (z : ℝ)) hbadSum
      simpa only [Nat.cast_sum] using hcast.symm
    calc
      (V.card : ℝ) = ∑ j : Fin m, ((B j).card : ℝ) := hVcardReal
      _ ≤ (∑ j : Fin m, ((B' j).card : ℝ)) +
          3 * (∑ j : Fin m, ((B j ∩ bad).card : ℝ)) := hsumReal
      _ = (Finset.univ.biUnion B').card + 3 * (bad.card : ℝ) := by
        rw [← hV'cardReal, ← hbadSumReal]
  have hbadle : (bad.card : ℝ) ≤ (V.card : ℝ) / 4 := by
    have hbadle' : (bad.card : ℝ) ≤ (1 / 4 : ℝ) * (V.card : ℝ) :=
      (div_le_iff₀ hVcardPos).mp hbadfrac
    nlinarith
  have hV'lower : (V.card : ℝ) / 4 ≤ (Finset.univ.biUnion B').card := by
    linarith [hsumCard]
  have hV'final :
      (S.S.N k : ℝ) * Real.exp (-((b : ℝ) ^ κ.aC)) / 4 ≤
        (Finset.univ.biUnion B').card := by
    have hcardlower :
        (S.S.N k : ℝ) * Real.exp (-((b : ℝ) ^ κ.aC)) ≤ (V.card : ℝ) := by
      simpa [V] using hVmass
    have hdiv := div_le_div_of_nonneg_right hcardlower (by norm_num : (0 : ℝ) ≤ 4)
    exact le_trans hdiv hV'lower
  have hB'good : ∀ j y, y ∈ B' j →
      |colDeg (S.S.E k) true hτ y - 1 / 2| ≤ (S.S.n k : ℝ) ^ (-κ.η0) := by
    intro j y hy
    have hyB := hB'sub j hy
    have hyV : y ∈ V := Finset.mem_biUnion.mpr ⟨j, Finset.mem_univ _, hyB⟩
    have hnotbad : y ∉ bad := (Finset.mem_sdiff.mp (hB'subdiff j hy)).2
    have hnotlt : ¬ (S.S.n k : ℝ) ^ (-κ.η0) <
        |colDeg (S.S.E k) true hτ y - 1 / 2| := by
      intro hlt
      exact hnotbad (Finset.mem_filter.mpr ⟨hyV, hlt⟩)
    exact le_of_not_gt hnotlt
  refine ⟨B', hB'sub, hB'disj, hB'size, hV'final, ?_⟩
  intro j y hy
  simpa using hB'good j y hy

theorem clean_cluster_scale_witness_aux
    (κ : CConsts) (hκ : CConsts.Admissible κ) (T : Stage)
    (hInit : InitDisc T κ.η0) :
    ∀ᶠ k in atTop, ∀ RX RY : Finset (Fin (T.S.N k)),
      RX ⊆ T.X k → RY ⊆ T.Y k → ∀ b o, IsDyadic b →
        CluScaleWitness κ T k RX RY b o →
          CleanClusterBinsAux κ T k RX RY b o := by
  have hInitSwap := initDisc_swap hInit
  filter_upwards [clean_fixed_orientation_false κ hκ T hInit,
    clean_fixed_orientation_false κ hκ T.swap hInitSwap] with k hT hSwap
  intro RX RY hRX hRY b o hb hClu
  cases o with
  | false =>
      exact hT RX RY hRX hRY b hb hClu
  | true =>
      have hCluSwap : CluScaleWitness κ T.swap k RY RX b false := by
        dsimp [Stage.swap, BadSeq.swap]
        rcases hClu with ⟨U, hU, m, B, hUs, hBs, hdisj, hBins, hUcard, hBcard, hcorr⟩
        refine ⟨U, hU, m, B, hUs, hBs, hdisj, hBins, hUcard, hBcard, ?_⟩
        intro j y hy y' hy' hne
        have hcorr' := hcorr j y hy y' hy' hne
        have hswap : pairCorr (transposeRel (T.S.E k)) false
            (Law.unifCore U hU) y y' = pairCorr (T.S.E k) true
            (Law.unifCore U hU) y y' :=
          HypercubeRamsey.S13.pairCorr_transpose
            (T.S.E k) false (Law.unifCore U hU) y y'
        rw [hswap]
        exact hcorr'
      have hCleanSwap := hSwap RY RX hRY hRX b hb hCluSwap
      dsimp [Stage.swap, BadSeq.swap] at hCleanSwap
      unfold CleanClusterBinsAux at hCleanSwap ⊢
      intro U hU m B hUs hBs hdisj hBins hUcard hVcard hcorr
      have hUs' : U ⊆ RY := by simpa using hUs
      have hBs' : ∀ j, B j ⊆ RX := by intro j; simpa using hBs j
      have hcorrSwap : ∀ j, ∀ y ∈ B j, ∀ y' ∈ B j, y ≠ y' →
          κ.θ < pairCorr (transposeRel (T.S.E k)) false
            (Law.unifCore U hU) y y' := by
        intro j y hy y' hy' hne
        have h := hcorr j y hy y' hy' hne
        have hEq : pairCorr (transposeRel (T.S.E k)) false
            (Law.unifCore U hU) y y' = pairCorr (T.S.E k) true
            (Law.unifCore U hU) y y' :=
          HypercubeRamsey.S13.pairCorr_transpose
            (T.S.E k) false (Law.unifCore U hU) y y'
        rw [hEq]
        exact h
      have hResult := hCleanSwap U hU m B hUs' hBs' hdisj hBins hUcard hVcard hcorrSwap
      rcases hResult with ⟨B', hsub, hdisj', hsize, hmass, hdeg⟩
      refine ⟨B', hsub, hdisj', hsize, hmass, ?_⟩
      intro j y hy
      simpa [colDeg_transpose_aux] using hdeg j y hy

end HypercubeRamsey.Lane_q_s13_resid
