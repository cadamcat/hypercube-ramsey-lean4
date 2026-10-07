import HypercubeRamsey.PartC.Tiling
import HypercubeRamsey.S13.ResidualScales_q_s13_scales

/-!
# Section 13.1: residual scale interfaces

The scales themselves are frozen in `PartC/Tiling.lean`. This file records the
specification facts used by the Section 13 proof nodes.
-/

namespace HypercubeRamsey.S13

open Filter

/-- D13.1 (sections/13, lines 15–32): each measured scale is a dyadic integer. -/
theorem gScale_isDyadic (κ : CConsts) (T : Stage) (k : ℕ)
    (RX RY : Finset (Fin (T.S.N k))) : IsDyadic (gScale κ T k RX RY) := by
  exact ⟨_, rfl⟩

theorem qScale_isDyadic (κ : CConsts) (T : Stage) (k : ℕ)
    (RX RY : Finset (Fin (T.S.N k))) : IsDyadic (qScale κ T k RX RY) := by
  exact ⟨_, rfl⟩

/-- D13.1 (sections/13, lines 15–32): an empty finite witness set gives scale `1`. -/
theorem gScale_eq_one_of_no_witness (κ : CConsts) (T : Stage) (k : ℕ)
    (RX RY : Finset (Fin (T.S.N k)))
    (h : ∀ j, 1 ≤ j → ¬ BiasWitness κ T k RX RY (2 ^ j)) :
    gScale κ T k RX RY = 1 := by
  classical
  let J := (Finset.range (2 * T.S.n k + 2)).filter
    (fun j => 1 ≤ j ∧ BiasWitness κ T k RX RY (2 ^ j))
  have hJ : J = ∅ := Finset.eq_empty_of_forall_notMem fun j hj => by
    rcases Finset.mem_filter.mp hj with ⟨_, hj, hw⟩
    exact (h j hj) hw
  change 2 ^ J.sup id = 1
  rw [hJ]
  simp

theorem qScale_eq_one_of_no_witness (κ : CConsts) (T : Stage) (k : ℕ)
    (RX RY : Finset (Fin (T.S.N k)))
    (h : ∀ j, 1 ≤ j → ¬ ∃ o, CluScaleWitness κ T k RX RY (2 ^ j) o) :
    qScale κ T k RX RY = 1 := by
  classical
  let J := (Finset.range (T.S.N k + 2)).filter
    (fun j => 1 ≤ j ∧ ∃ o, CluScaleWitness κ T k RX RY (2 ^ j) o)
  have hJ : J = ∅ := Finset.eq_empty_of_forall_notMem fun j hj => by
    rcases Finset.mem_filter.mp hj with ⟨_, hj, hw⟩
    exact (h j hj) hw
  change 2 ^ J.sup id = 1
  rw [hJ]
  simp

/-- D13.1(i) (sections/13, lines 15–32): a nontrivial measured bias scale is witnessed. -/
theorem gScale_witness (κ : CConsts) (T : Stage) (k : ℕ)
    (RX RY : Finset (Fin (T.S.N k)))
    (h : 2 ≤ gScale κ T k RX RY) :
    BiasWitness κ T k RX RY (gScale κ T k RX RY) := by
  classical
  let J := (Finset.range (2 * T.S.n k + 2)).filter
    (fun j => 1 ≤ j ∧ BiasWitness κ T k RX RY (2 ^ j))
  have hpow : 2 ≤ 2 ^ J.sup id := by simpa [gScale, J] using h
  have hsup_pos : 0 < J.sup id := by
    by_contra hz
    have hz' : J.sup id = 0 := Nat.eq_zero_of_not_pos hz
    simp [hz'] at hpow
  have hJne : J.Nonempty := by
    by_contra hn
    have hJempty : J = ∅ := Finset.not_nonempty_iff_eq_empty.mp hn
    simp [hJempty] at hsup_pos
  obtain ⟨j, hj, hsup⟩ := Finset.exists_mem_eq_sup J hJne id
  have hw : BiasWitness κ T k RX RY (2 ^ j) := (Finset.mem_filter.mp hj).2.2
  have hpowEq : 2 ^ J.sup id = 2 ^ j := congrArg (fun a : ℕ => 2 ^ a) hsup
  change BiasWitness κ T k RX RY (2 ^ J.sup id)
  rw [hpowEq]
  exact hw

/-- D13.1(i) (sections/13, lines 15–32): a nontrivial cluster scale is witnessed in some orientation. -/
theorem qScale_witness (κ : CConsts) (T : Stage) (k : ℕ)
    (RX RY : Finset (Fin (T.S.N k)))
    (h : 2 ≤ qScale κ T k RX RY) :
    ∃ o : Bool, CluScaleWitness κ T k RX RY (qScale κ T k RX RY) o := by
  classical
  let J := (Finset.range (T.S.N k + 2)).filter
    (fun j => 1 ≤ j ∧ ∃ o, CluScaleWitness κ T k RX RY (2 ^ j) o)
  have hpow : 2 ≤ 2 ^ J.sup id := by simpa [qScale, J] using h
  have hsup_pos : 0 < J.sup id := by
    by_contra hz
    have hz' : J.sup id = 0 := Nat.eq_zero_of_not_pos hz
    simp [hz'] at hpow
  have hJne : J.Nonempty := by
    by_contra hn
    have hJempty : J = ∅ := Finset.not_nonempty_iff_eq_empty.mp hn
    simp [hJempty] at hsup_pos
  obtain ⟨j, hj, hsup⟩ := Finset.exists_mem_eq_sup J hJne id
  obtain ⟨o, hw⟩ := (Finset.mem_filter.mp hj).2.2
  have hpowEq : 2 ^ J.sup id = 2 ^ j := congrArg (fun a : ℕ => 2 ^ a) hsup
  refine ⟨o, ?_⟩
  change CluScaleWitness κ T k RX RY (2 ^ J.sup id) o
  rw [hpowEq]
  exact hw

/-- D13.1(ii) (sections/13, lines 15–32): no larger in-range dyadic bias budget is witnessed. -/
theorem gScale_absent (κ : CConsts) (T : Stage) (k : ℕ)
    (RX RY : Finset (Fin (T.S.N k))) (b : ℕ)
    (hb : IsDyadic b) (hscale : gScale κ T k RX RY < b)
    (hrange : b ≤ 2 * T.S.n k + 1) :
    ¬ BiasWitness κ T k RX RY b := by
  classical
  let J := (Finset.range (2 * T.S.n k + 2)).filter
    (fun j => 1 ≤ j ∧ BiasWitness κ T k RX RY (2 ^ j))
  rintro hw
  rcases hb with ⟨j, rfl⟩
  have hpowlt : 2 ^ J.sup id < 2 ^ j := by simpa [gScale, J] using hscale
  have hsup_lt : J.sup id < j := (Nat.pow_lt_pow_iff_right Nat.one_lt_two).mp hpowlt
  have hjpos : 1 ≤ j := by omega
  have hjrange : j < 2 * T.S.n k + 2 := by
    have hjle : j ≤ 2 ^ j := nat_le_two_pow j
    omega
  have hjmem : j ∈ J := by
    change j ∈ (Finset.range (2 * T.S.n k + 2)).filter
      (fun i => 1 ≤ i ∧ BiasWitness κ T k RX RY (2 ^ i))
    apply Finset.mem_filter.mpr
    refine ⟨Finset.mem_range.mpr hjrange, ?_⟩
    exact ⟨hjpos, hw⟩
  have hle : j ≤ J.sup id := by simpa using (Finset.le_sup (f := id) hjmem)
  omega

/-- D13.1(ii) (sections/13, lines 15–32): no larger in-range cluster budget is witnessed. -/
theorem qScale_absent (κ : CConsts) (T : Stage) (k : ℕ)
    (RX RY : Finset (Fin (T.S.N k))) (b : ℕ)
    (hb : IsDyadic b) (hscale : qScale κ T k RX RY < b)
    (hrange : b ≤ T.S.N k + 1) :
    ¬ ∃ o : Bool, CluScaleWitness κ T k RX RY b o := by
  classical
  let J := (Finset.range (T.S.N k + 2)).filter
    (fun j => 1 ≤ j ∧ ∃ o, CluScaleWitness κ T k RX RY (2 ^ j) o)
  rintro hw
  rcases hb with ⟨j, rfl⟩
  have hpowlt : 2 ^ J.sup id < 2 ^ j := by simpa [qScale, J] using hscale
  have hsup_lt : J.sup id < j := (Nat.pow_lt_pow_iff_right Nat.one_lt_two).mp hpowlt
  have hjpos : 1 ≤ j := by omega
  have hjrange : j < T.S.N k + 2 := by
    have hjle : j ≤ 2 ^ j := nat_le_two_pow j
    omega
  have hjmem : j ∈ J := by
    change j ∈ (Finset.range (T.S.N k + 2)).filter
      (fun i => 1 ≤ i ∧ ∃ o, CluScaleWitness κ T k RX RY (2 ^ i) o)
    apply Finset.mem_filter.mpr
    refine ⟨Finset.mem_range.mpr hjrange, ?_⟩
    exact ⟨hjpos, hw⟩
  have hle : j ≤ J.sup id := by simpa using (Finset.le_sup (f := id) hjmem)
  omega

/-- D13.1(iii) (sections/13, lines 15–32): scales are monotone under enlarging residual sides. -/
theorem residual_scales_mono (κ : CConsts) (T : Stage) (k : ℕ)
    {RX RX' RY RY' : Finset (Fin (T.S.N k))}
    (hX : RX ⊆ RX') (hY : RY ⊆ RY') :
    gScale κ T k RX RY ≤ gScale κ T k RX' RY' ∧
      qScale κ T k RX RY ≤ qScale κ T k RX' RY' := by
  classical
  constructor
  · apply pow_le_pow_right' (a := 2) (by omega)
    apply Finset.sup_mono
    intro j hj
    rcases Finset.mem_filter.mp hj with ⟨hjrange, hjcond⟩
    apply Finset.mem_filter.mpr
    refine ⟨hjrange, ⟨hjcond.1, ?_⟩⟩
    exact biasWitness_mono hX hY hjcond.2
  · apply pow_le_pow_right' (a := 2) (by omega)
    apply Finset.sup_mono
    intro j hj
    rcases Finset.mem_filter.mp hj with ⟨hjrange, hjcond⟩
    apply Finset.mem_filter.mpr
    refine ⟨hjrange, ⟨hjcond.1, ?_⟩⟩
    rcases hjcond.2 with ⟨o, ho⟩
    exact ⟨o, cluScaleWitness_mono hX hY ho⟩

/-- D13.1(iv) (sections/13, lines 15–32): bias witnesses transfer under stage swap. -/
theorem biasWitness_swap_iff (κ : CConsts) (T : Stage) (k : ℕ)
    (RX RY : Finset (Fin (T.S.N k))) (b : ℕ) :
    BiasWitness κ T.swap k RY RX b ↔ BiasWitness κ T k RX RY b := by
  unfold BiasWitness
  constructor
  · rintro ⟨U, V, hU, hV, hUR, hVR, hcardU, hcardV, hden⟩
    refine ⟨V, U, hV, hU, hVR, hUR, hcardV, hcardU, ?_⟩
    change (b : ℝ) / T.S.n k ≤
      |dens (transposeRel (T.S.E k)) true (Law.unifCore U hU) (Law.unifCore V hV) - 1 / 2| at hden
    rw [dens_transpose] at hden
    exact hden
  · rintro ⟨U, V, hU, hV, hUR, hVR, hcardU, hcardV, hden⟩
    refine ⟨V, U, hV, hU, hVR, hUR, hcardV, hcardU, ?_⟩
    change (b : ℝ) / T.S.n k ≤
      |dens (transposeRel (T.S.E k)) true (Law.unifCore V hV) (Law.unifCore U hU) - 1 / 2|
    rw [dens_transpose]
    exact hden

/-- D13.1(iv) (sections/13, lines 15–32): cluster witnesses transfer under stage and orientation swap. -/
theorem clusterWitness_swap_iff (κ : CConsts) (T : Stage) (k : ℕ)
    (RX RY : Finset (Fin (T.S.N k))) (b : ℕ) :
    (∃ o, CluScaleWitness κ T.swap k RY RX b o) ↔
      (∃ o, CluScaleWitness κ T k RX RY b o) := by
  constructor
  · rintro ⟨o, hw⟩
    cases o with
    | false =>
        rcases hw with ⟨U, hU, m, B, hUs, hBs, hdisj, hsize, hUcard, hBcard, hcorr⟩
        refine ⟨true, U, hU, m, B, hUs, hBs, hdisj, hsize, hUcard, hBcard, ?_⟩
        intro j y hy y' hy' hne
        simpa [Stage.swap, BadSeq.swap] using hcorr j y hy y' hy' hne
    | true =>
        rcases hw with ⟨U, hU, m, B, hUs, hBs, hdisj, hsize, hUcard, hBcard, hcorr⟩
        refine ⟨false, U, hU, m, B, hUs, hBs, hdisj, hsize, hUcard, hBcard, ?_⟩
        intro j y hy y' hy' hne
        simpa [Stage.swap, BadSeq.swap] using hcorr j y hy y' hy' hne
  · rintro ⟨o, hw⟩
    cases o with
    | false =>
        rcases hw with ⟨U, hU, m, B, hUs, hBs, hdisj, hsize, hUcard, hBcard, hcorr⟩
        refine ⟨true, U, hU, m, B, hUs, hBs, hdisj, hsize, hUcard, hBcard, ?_⟩
        intro j y hy y' hy' hne
        have hcorr' := hcorr j y hy y' hy' hne
        have hswap : pairCorr (transposeRel (T.S.E k)) true (Law.unifCore U hU) y y' =
            pairCorr (T.S.E k) false (Law.unifCore U hU) y y' := by
          simpa using pairCorr_transpose (T.S.E k) true (Law.unifCore U hU) y y'
        rw [← hswap] at hcorr'
        simpa [Stage.swap, BadSeq.swap] using hcorr'
    | true =>
        rcases hw with ⟨U, hU, m, B, hUs, hBs, hdisj, hsize, hUcard, hBcard, hcorr⟩
        refine ⟨false, U, hU, m, B, hUs, hBs, hdisj, hsize, hUcard, hBcard, ?_⟩
        intro j y hy y' hy' hne
        have hcorr' := hcorr j y hy y' hy' hne
        have hswap : pairCorr (transposeRel (T.S.E k)) false (Law.unifCore U hU) y y' =
            pairCorr (T.S.E k) true (Law.unifCore U hU) y y' := by
          simpa using pairCorr_transpose (T.S.E k) false (Law.unifCore U hU) y y'
        rw [← hswap] at hcorr'
        simpa [Stage.swap, BadSeq.swap] using hcorr'

/-- D13.1 (sections/13, lines 15–32): specification interface consumed downstream. -/
/- D13.1's specification is kept as a named interface so downstream nodes can
consume all of its clauses together. -/
structure ResidualScaleSpec : Prop where
  g_dyadic : ∀ κ T k RX RY, IsDyadic (gScale κ T k RX RY)
  q_dyadic : ∀ κ T k RX RY, IsDyadic (qScale κ T k RX RY)
  g_empty : ∀ κ T k RX RY,
    (∀ j, 1 ≤ j → ¬ BiasWitness κ T k RX RY (2 ^ j)) →
      gScale κ T k RX RY = 1
  q_empty : ∀ κ T k RX RY,
    (∀ j, 1 ≤ j → ¬ ∃ o, CluScaleWitness κ T k RX RY (2 ^ j) o) →
      qScale κ T k RX RY = 1
  bias_witness : ∀ κ T k RX RY, 2 ≤ gScale κ T k RX RY →
    BiasWitness κ T k RX RY (gScale κ T k RX RY)
  cluster_witness : ∀ κ T k RX RY, 2 ≤ qScale κ T k RX RY →
    ∃ o, CluScaleWitness κ T k RX RY (qScale κ T k RX RY) o
  bias_absent : ∀ κ T k RX RY b, IsDyadic b → gScale κ T k RX RY < b →
    b ≤ 2 * T.S.n k + 1 → ¬ BiasWitness κ T k RX RY b
  cluster_absent : ∀ κ T k RX RY b, IsDyadic b → qScale κ T k RX RY < b →
    b ≤ T.S.N k + 1 → ¬ ∃ o, CluScaleWitness κ T k RX RY b o
  monotone : ∀ κ T k RX RX' RY RY', RX ⊆ RX' → RY ⊆ RY' →
    gScale κ T k RX RY ≤ gScale κ T k RX' RY' ∧
      qScale κ T k RX RY ≤ qScale κ T k RX' RY'
  bias_swap : ∀ κ T k RX RY b,
    BiasWitness κ T.swap k RY RX b ↔ BiasWitness κ T k RX RY b
  cluster_swap : ∀ κ T k RX RY b,
    (∃ o, CluScaleWitness κ T.swap k RY RX b o) ↔
      (∃ o, CluScaleWitness κ T k RX RY b o)

/-- D13.1: the specification assembly is proved from its six separate facts. -/
theorem d13_1_residual_scale_specification : ResidualScaleSpec := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact gScale_isDyadic
  · exact qScale_isDyadic
  · exact gScale_eq_one_of_no_witness
  · exact qScale_eq_one_of_no_witness
  · intro κ T k RX RY h
    exact gScale_witness κ T k RX RY h
  · intro κ T k RX RY h
    exact qScale_witness κ T k RX RY h
  · intro κ T k RX RY b hb hscale hrange
    exact gScale_absent κ T k RX RY b hb hscale hrange
  · intro κ T k RX RY b hb hscale hrange
    exact qScale_absent κ T k RX RY b hb hscale hrange
  · intro κ T k RX RX' RY RY' hX hY
    exact residual_scales_mono κ T k hX hY
  · exact biasWitness_swap_iff
  · exact clusterWitness_swap_iff

end HypercubeRamsey.S13
