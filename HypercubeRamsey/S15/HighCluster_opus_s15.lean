import HypercubeRamsey.S15.ClusterBinSampler_sol_s15_c2
import HypercubeRamsey.S15.ClusterBinCharges_sol_s15_c2
import HypercubeRamsey.S15.ClusterBinScales_sol_s15_c2
import HypercubeRamsey.S15.ClusterLabelStage_sol_s15_c2
import HypercubeRamsey.S15.ClusterLabelGeometry_sol_s15_c2
import HypercubeRamsey.S15.HighCluster_opus_s15_g_s15_cond

/-! Sub-lemmas for the conditioned bin and label stages of P15.3 (section 15, lines 119–156).

The bin stage is reduced to two charge-accounting estimates (`bin_star_charges`,
`bin_certificate_charges`); `bin_output_of_charges` applies the local lemma.  The label stage is
reduced to the exact singleton marginal of the independent label kernel, the clock sampler in
high-large-bin mode, and the per-bin injection sampler in high-small-bin mode. -/

namespace HypercubeRamsey.S15.Lane_opus_s15

open HypercubeRamsey HypercubeRamsey.S15 HypercubeRamsey.Lane_sol_s15_c2 Classical Filter
open scoped BigOperators
set_option backward.isDefEq.respectTransparency false

/-! ### Bin stage -/

/-- Local-lemma charges of the bin events: twice the raw probability for star events, and the
certificate weight `2^{|A|}` times the raw probability for capacity certificates. -/
noncomputable def binCharge {κ : CConsts} {T : Stage} {k : ℕ}
    (PT : ProfiledTiling κ T k) (hPT : PT.Valid)
    (hm : PT.tiling.mode = .highSmall ∨ PT.tiling.mode = .highLarge)
    (W : ClusterHistory PT hPT hm) : BinEvent PT → ℝ
  | .inl e => 2 * (clusterIndependentBinKernel PT hPT hm W).pr (binEventBad PT hPT hm W (.inl e))
  | .inr c => (2 : ℝ) ^ c.2.2.card *
      (clusterIndependentBinKernel PT hPT hm W).pr (binEventBad PT hPT hm W (.inr c))

theorem binCharge_nonneg {κ : CConsts} {T : Stage} {k : ℕ}
    (PT : ProfiledTiling κ T k) (hPT : PT.Valid)
    (hm : PT.tiling.mode = .highSmall ∨ PT.tiling.mode = .highLarge)
    (W : ClusterHistory PT hPT hm) (e : BinEvent PT) : 0 ≤ binCharge PT hPT hm W e := by
  have hpr (A : ClusterBinAssignment PT → Prop) : 0 ≤ (clusterIndependentBinKernel PT hPT hm W).pr A := by
    unfold FinLaw.pr
    exact Finset.sum_nonneg fun B _ => by
      split_ifs
      · exact (clusterIndependentBinKernel PT hPT hm W).nonneg B
      · exact le_rfl
  cases e with
  | inl e => exact mul_nonneg (by norm_num) (hpr _)
  | inr c => exact mul_nonneg (by positivity) (hpr _)

/-- The star mass-failure charge is at most `2 n^{-R/2}` by the Markov tail `hstar`. -/
theorem bin_star_failure_charge {κ : CConsts} {T : Stage} {k : ℕ}
    (PT : ProfiledTiling κ T k) (hPT : PT.Valid)
    (hm : PT.tiling.mode = .highSmall ∨ PT.tiling.mode = .highLarge)
    (W : ClusterHistory PT hPT hm) (a : EvenPosition T k)
    (hstar : (clusterIndependentBinKernel PT hPT hm W).pr
        (fun B => (T.S.n k : ℝ) ^ (-(κ.R : ℝ) / 2) < clusterBinStarFailure PT hPT hm W B a) ≤
        (T.S.n k : ℝ) ^ (-(κ.R : ℝ) / 2)) :
    binCharge PT hPT hm W (.inl (a, false)) ≤ 2 * (T.S.n k : ℝ) ^ (-(κ.R : ℝ) / 2) := by
  have hle : (clusterIndependentBinKernel PT hPT hm W).pr (binEventBad PT hPT hm W (.inl (a, false))) ≤
      (clusterIndependentBinKernel PT hPT hm W).pr
        (fun B => (T.S.n k : ℝ) ^ (-(κ.R : ℝ) / 2) < clusterBinStarFailure PT hPT hm W B a) := by
    unfold FinLaw.pr
    apply Finset.sum_le_sum
    intro B _
    by_cases hpos : 0 < (clusterIndependentBinKernel PT hPT hm W).w B
    · have heq := bin_star_failure_eq PT hPT hm W B a hpos
      have hiff : binEventBad PT hPT hm W (.inl (a, false)) B ↔
          (T.S.n k : ℝ) ^ (-(κ.R : ℝ) / 2) < clusterBinStarFailure PT hPT hm W B a := by
        show _ < _ ↔ _
        rw [heq]
      by_cases hb : binEventBad PT hPT hm W (.inl (a, false)) B
      · rw [if_pos hb, if_pos (hiff.mp hb)]
      · rw [if_neg hb]
        split_ifs
        · exact hpos.le
        · exact le_rfl
    · have hz : (clusterIndependentBinKernel PT hPT hm W).w B = 0 :=
        le_antisymm (le_of_not_gt hpos) ((clusterIndependentBinKernel PT hPT hm W).nonneg B)
      simp only [hz, ite_self, le_refl]
  show 2 * _ ≤ _
  linarith

/-- Monotonicity of event probabilities. -/
theorem finLaw_pr_mono {Ω : Type*} [Fintype Ω] (P : FinLaw Ω) {A B : Ω → Prop}
    (h : ∀ ω, A ω → B ω) : P.pr A ≤ P.pr B := by
  unfold FinLaw.pr
  apply Finset.sum_le_sum
  intro ω _
  by_cases hA : A ω
  · rw [if_pos hA, if_pos (h ω hA)]
  · rw [if_neg hA]
    split_ifs
    · exact P.nonneg ω
    · exact le_rfl

/-- The union bound for finite laws. -/
theorem finLaw_pr_exists_le {Ω ι : Type*} [Fintype Ω] (P : FinLaw Ω) (s : Finset ι)
    (A : ι → Ω → Prop) : P.pr (fun ω => ∃ i ∈ s, A i ω) ≤ ∑ i ∈ s, P.pr (A i) := by
  classical
  unfold FinLaw.pr
  rw [Finset.sum_comm]
  apply Finset.sum_le_sum
  intro ω _
  have hnn : ∀ i ∈ s, 0 ≤ (if A i ω then P.w ω else 0) := fun i _ => by
    split_ifs
    · exact P.nonneg ω
    · exact le_rfl
  by_cases h : ∃ i ∈ s, A i ω
  · rw [if_pos h]
    obtain ⟨i, hi, hA⟩ := h
    have hle := Finset.single_le_sum hnn hi
    rwa [if_pos hA] at hle
  · rw [if_neg h]
    exact Finset.sum_nonneg hnn

/-- A physical-bin probability is at most the largest atom of the group's bin law. -/
theorem binProbability_le_atom {κ : CConsts} {T : Stage} {k : ℕ}
    (PT : ProfiledTiling κ T k) (hPT : PT.Valid)
    (hm : PT.tiling.mode = .highSmall ∨ PT.tiling.mode = .highLarge)
    (W : ClusterHistory PT hPT hm) (g : ClusterGroupIndex PT) (D : Finset (Fin (T.S.N k)))
    (ε : ℝ) (hε : 0 ≤ ε)
    (hq : ∀ D' : clusterBinType g,
      (clusterSolver PT hPT hm g.1.1).q g.2 (historyOnSlice W g.1) D' ≤ ε) :
    clusterBinProbability PT hPT hm W g D ≤ ε := by
  classical
  unfold clusterBinProbability
  by_cases hex : ∃ D0 : clusterBinType g, D0.1 = D
  · obtain ⟨D0, hD0⟩ := hex
    rw [Finset.sum_eq_single D0]
    · rw [if_pos hD0]
      exact hq D0
    · intro D' _ hne
      rw [if_neg]
      intro h
      exact hne (Subtype.ext (h.trans hD0.symm))
    · intro h
      exact absurd (Finset.mem_univ D0) h
  · have hzero : ∀ D' : clusterBinType g,
        (if D'.1 = D then (clusterSolver PT hPT hm g.1.1).q g.2 (historyOnSlice W g.1) D' else 0) =
          0 := fun D' => if_neg (fun h => hex ⟨D', h⟩)
    rw [Finset.sum_congr rfl (fun D' _ => hzero D'), Finset.sum_const_zero]
    exact hε

/-- Two distinct groups choose the same physical bin with probability at most the largest atom. -/
theorem bin_pair_collision_le {κ : CConsts} {T : Stage} {k : ℕ}
    (PT : ProfiledTiling κ T k) (hPT : PT.Valid)
    (hm : PT.tiling.mode = .highSmall ∨ PT.tiling.mode = .highLarge)
    (W : ClusterHistory PT hPT hm) (g g' : ClusterGroupIndex PT) (hne : g ≠ g')
    (ε : ℝ) (hε : 0 ≤ ε)
    (hq : ∀ D' : clusterBinType g',
      (clusterSolver PT hPT hm g'.1.1).q g'.2 (historyOnSlice W g'.1) D' ≤ ε) :
    (clusterIndependentBinKernel PT hPT hm W).pr (fun B => (B g).1 = (B g').1) ≤ ε := by
  classical
  have hsub : ∀ B : ClusterBinAssignment PT, (B g).1 = (B g').1 →
      ∃ D ∈ (Finset.univ : Finset (PhysicalBin PT)),
        ∀ h ∈ ({g, g'} : Finset (ClusterGroupIndex PT)), (B h).1 = D.2.1 := by
    intro B hB
    refine ⟨⟨g.1.1, B g⟩, Finset.mem_univ _, ?_⟩
    intro h hh
    rcases Finset.mem_insert.mp hh with hh | hh
    · rw [hh]
    · rw [Finset.mem_singleton.mp hh]
      exact hB.symm
  calc
    _ ≤ _ := finLaw_pr_mono _ hsub
    _ ≤ ∑ D : PhysicalBin PT, (clusterIndependentBinKernel PT hPT hm W).pr
          (fun B => ∀ h ∈ ({g, g'} : Finset (ClusterGroupIndex PT)), (B h).1 = D.2.1) :=
      finLaw_pr_exists_le _ _ _
    _ = ∑ D : PhysicalBin PT, clusterBinProbability PT hPT hm W g D.2.1 *
          clusterBinProbability PT hPT hm W g' D.2.1 := by
      apply Finset.sum_congr rfl
      intro D _
      rw [fixed_physical_bins_probability, Finset.prod_pair hne]
    _ ≤ ∑ D : PhysicalBin PT, clusterBinProbability PT hPT hm W g D.2.1 * ε := by
      apply Finset.sum_le_sum
      intro D _
      exact mul_le_mul_of_nonneg_left (binProbability_le_atom PT hPT hm W g' D.2.1 ε hε hq)
        (bin_probability_nonneg PT hPT hm W g D.2.1)
    _ = ε := by rw [← Finset.sum_mul, physical_bin_probability_sum PT hPT hm W g, one_mul]

/-- Small-bin duplicates (15:126).  In high-large-bin mode `binDuplicate` is false.  In
high-small-bin mode a union bound over the `≤ n^2` ordered pairs of star groups and
`small_bin_atom_exponential` (every bin atom `≤ 4 e^{-c n}`) give `≤ 4 n^2 e^{-c n}`. -/
theorem bin_duplicate_charge (κ : CConsts) (hκ : κ.Admissible) (T : Stage) :
    ∃ c : ℝ, 0 < c ∧ ∀ᶠ k in atTop, ∀ PT : ProfiledTiling κ T k, ∀ hPT : PT.Valid,
    ∀ hm : PT.tiling.mode = .highSmall ∨ PT.tiling.mode = .highLarge,
    ∀ W : ClusterHistory PT hPT hm, ∀ a : EvenPosition T k,
      binCharge PT hPT hm W (.inl (a, true)) ≤
        8 * (T.S.n k : ℝ) ^ 2 * Real.exp (-c * (T.S.n k : ℝ)) := by
  classical
  obtain ⟨c, hc, hAtom⟩ := small_bin_atom_exponential κ hκ T
  refine ⟨c, hc, ?_⟩
  filter_upwards [hAtom] with k hAtom
  intro PT hPT hm W a
  have hRHS : 0 ≤ 8 * (T.S.n k : ℝ) ^ 2 * Real.exp (-c * (T.S.n k : ℝ)) := by positivity
  show 2 * (clusterIndependentBinKernel PT hPT hm W).pr (binDuplicate PT hPT hm a) ≤ _
  by_cases hs : PT.tiling.mode = .highSmall
  · obtain ⟨ε, hεdef⟩ : ∃ ε : ℝ, ε = 4 * Real.exp (-c * (T.S.n k : ℝ)) := ⟨_, rfl⟩
    have hε : 0 ≤ ε := by rw [hεdef]; positivity
    have hq : ∀ (g' : ClusterGroupIndex PT) (D' : clusterBinType g'),
        (clusterSolver PT hPT hm g'.1.1).q g'.2 (historyOnSlice W g'.1) D' ≤ ε := by
      intro g' D'
      rw [hεdef]
      exact hAtom PT hPT hs W g' D'
    obtain ⟨Q, hQdef⟩ : ∃ Q, Q = starGroupQueries PT hPT hm a := ⟨_, rfl⟩
    have hsub : ∀ B, binDuplicate PT hPT hm a B →
        ∃ p ∈ Q ×ˢ Q, p.1 ≠ p.2 ∧ (B p.1).1 = (B p.2).1 := by
      rintro B ⟨_, g, hg, g', hg', hne, heq⟩
      rw [hQdef]
      exact ⟨(g, g'), Finset.mem_product.mpr ⟨hg, hg'⟩, hne, heq⟩
    have hpair : ∀ p ∈ Q ×ˢ Q, (clusterIndependentBinKernel PT hPT hm W).pr
        (fun B => p.1 ≠ p.2 ∧ (B p.1).1 = (B p.2).1) ≤ ε := by
      intro p _
      by_cases hne : p.1 = p.2
      · have hz : (clusterIndependentBinKernel PT hPT hm W).pr
            (fun B => p.1 ≠ p.2 ∧ (B p.1).1 = (B p.2).1) = 0 := by
          unfold FinLaw.pr
          apply Finset.sum_eq_zero
          intro B _
          rw [if_neg]
          exact fun h => h.1 hne
        rw [hz]
        exact hε
      · exact (finLaw_pr_mono _ (fun B h => h.2)).trans
          (bin_pair_collision_le PT hPT hm W p.1 p.2 hne ε hε (hq p.2))
    have hQ' : (Q.card : ℝ) ≤ (T.S.n k : ℝ) := by
      rw [hQdef]
      exact_mod_cast starGroupQueries_card_le PT hPT hm a
    have hQ : ((Q ×ˢ Q).card : ℝ) ≤ (T.S.n k : ℝ) ^ 2 := by
      rw [Finset.card_product, Nat.cast_mul, sq]
      exact mul_le_mul hQ' hQ' (Nat.cast_nonneg _) (Nat.cast_nonneg _)
    calc
      2 * (clusterIndependentBinKernel PT hPT hm W).pr (binDuplicate PT hPT hm a) ≤
          2 * ∑ p ∈ Q ×ˢ Q, (clusterIndependentBinKernel PT hPT hm W).pr
            (fun B => p.1 ≠ p.2 ∧ (B p.1).1 = (B p.2).1) :=
        mul_le_mul_of_nonneg_left
          ((finLaw_pr_mono _ hsub).trans (finLaw_pr_exists_le _ _ _)) (by norm_num)
      _ ≤ 2 * ∑ _p ∈ Q ×ˢ Q, ε :=
        mul_le_mul_of_nonneg_left (Finset.sum_le_sum hpair) (by norm_num)
      _ = 2 * (((Q ×ˢ Q).card : ℝ) * ε) := by rw [Finset.sum_const, nsmul_eq_mul]
      _ ≤ 2 * ((T.S.n k : ℝ) ^ 2 * ε) :=
        mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right hQ hε) (by norm_num)
      _ = 8 * (T.S.n k : ℝ) ^ 2 * Real.exp (-c * (T.S.n k : ℝ)) := by rw [hεdef]; ring
  · have hzero : (clusterIndependentBinKernel PT hPT hm W).pr (binDuplicate PT hPT hm a) = 0 := by
      unfold FinLaw.pr
      apply Finset.sum_eq_zero
      intro B _
      rw [if_neg]
      exact fun h => hs h.1
    rw [hzero]
    linarith

/-- Sub-lemma (scales for the star charges): `R ≥ 28` from `hκ`, and `n^8 e^{-cn} → 0`. -/
theorem bin_star_scale (κ : CConsts) (hκ : κ.Admissible) (T : Stage) (c : ℝ) (hc : 0 < c) :
    ∀ᶠ k in atTop, 2 ≤ T.S.n k ∧
      16 * (T.S.n k : ℝ) ^ 6 * (2 * (T.S.n k : ℝ) ^ (-(κ.R : ℝ) / 2) +
        8 * (T.S.n k : ℝ) ^ 2 * Real.exp (-c * (T.S.n k : ℝ))) ≤ 1 := by
  have hP : 21000 ≤ κ.P := by
    have h := hκ.P_big.2
    rw [hκ.Ac_eq] at h
    omega
  have hRnat : 28 ≤ κ.R := by
    rw [hκ.R_eq]
    nlinarith
  have hR : (28 : ℝ) ≤ (κ.R : ℝ) := by exact_mod_cast hRnat
  have hnT : Tendsto (fun k => (T.S.n k : ℝ)) atTop atTop :=
    tendsto_natCast_atTop_atTop.comp T.S.n_tendsto
  have hev : ∀ᶠ x : ℝ in atTop, x ^ (8 : ℝ) * Real.exp (-c * x) < 1 / 256 :=
    (tendsto_rpow_mul_exp_neg_mul_atTop_nhds_zero 8 c hc).eventually (Iio_mem_nhds (by norm_num))
  filter_upwards [T.S.n_tendsto.eventually_ge_atTop 2, hnT.eventually hev] with k hk2 hkexp
  refine ⟨hk2, ?_⟩
  have hx : (2 : ℝ) ≤ (T.S.n k : ℝ) := by exact_mod_cast hk2
  have hx0 : (0 : ℝ) < (T.S.n k : ℝ) := by linarith
  have h8 : (T.S.n k : ℝ) ^ (8 : ℝ) = (T.S.n k : ℝ) ^ 8 := by
    rw [show (8 : ℝ) = ((8 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]
  have hkexp' : (T.S.n k : ℝ) ^ 8 * Real.exp (-c * (T.S.n k : ℝ)) < 1 / 256 := by
    rw [← h8]
    exact hkexp
  have hpow : (T.S.n k : ℝ) ^ (-(κ.R : ℝ) / 2) ≤ (T.S.n k : ℝ) ^ (-(14 : ℝ)) :=
    Real.rpow_le_rpow_of_exponent_le (by linarith) (by linarith)
  have h14 : (T.S.n k : ℝ) ^ (-(14 : ℝ)) = ((T.S.n k : ℝ) ^ 14)⁻¹ := by
    rw [Real.rpow_neg hx0.le, show (14 : ℝ) = ((14 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]
  have hx8 : (256 : ℝ) ≤ (T.S.n k : ℝ) ^ 8 := by
    calc (256 : ℝ) = 2 ^ 8 := by norm_num
      _ ≤ _ := pow_le_pow_left₀ (by norm_num) hx 8
  have hA : 16 * (T.S.n k : ℝ) ^ 6 * (2 * (T.S.n k : ℝ) ^ (-(κ.R : ℝ) / 2)) ≤ 1 / 8 := by
    have heq : 16 * (T.S.n k : ℝ) ^ 6 * (2 * ((T.S.n k : ℝ) ^ 14)⁻¹) =
        32 / (T.S.n k : ℝ) ^ 8 := by
      first | (field_simp; ring) | field_simp
    have hmono : 16 * (T.S.n k : ℝ) ^ 6 * (2 * (T.S.n k : ℝ) ^ (-(κ.R : ℝ) / 2)) ≤
        16 * (T.S.n k : ℝ) ^ 6 * (2 * ((T.S.n k : ℝ) ^ 14)⁻¹) := by
      rw [← h14]
      have h6 : 0 ≤ 16 * (T.S.n k : ℝ) ^ 6 := by positivity
      exact mul_le_mul_of_nonneg_left (by linarith) h6
    rw [heq] at hmono
    refine hmono.trans ?_
    rw [div_le_div_iff₀ (by positivity) (by norm_num)]
    linarith
  have hB : 16 * (T.S.n k : ℝ) ^ 6 * (8 * (T.S.n k : ℝ) ^ 2 * Real.exp (-c * (T.S.n k : ℝ))) ≤
      1 / 2 := by
    have heq : 16 * (T.S.n k : ℝ) ^ 6 * (8 * (T.S.n k : ℝ) ^ 2 * Real.exp (-c * (T.S.n k : ℝ))) =
        128 * ((T.S.n k : ℝ) ^ 8 * Real.exp (-c * (T.S.n k : ℝ))) := by ring
    rw [heq]
    have h128 : 128 * ((T.S.n k : ℝ) ^ 8 * Real.exp (-c * (T.S.n k : ℝ))) ≤ 128 * (1 / 256) :=
      mul_le_mul_of_nonneg_left hkexp'.le (by norm_num)
    calc
      _ ≤ 128 * (1 / 256 : ℝ) := h128
      _ = 1 / 2 := by norm_num
  calc
    _ = 16 * (T.S.n k : ℝ) ^ 6 * (2 * (T.S.n k : ℝ) ^ (-(κ.R : ℝ) / 2)) +
        16 * (T.S.n k : ℝ) ^ 6 * (8 * (T.S.n k : ℝ) ^ 2 * Real.exp (-c * (T.S.n k : ℝ))) := by ring
    _ ≤ 1 / 8 + 1 / 2 := add_le_add hA hB
    _ ≤ 1 := by norm_num

/-- Each group lies in at most `2hn ≤ 2n^2` stars, so at most `4n^2` star events touch it. -/
theorem star_event_touch_card {κ : CConsts} {T : Stage} {k : ℕ}
    (PT : ProfiledTiling κ T k) (hPT : PT.Valid)
    (hm : PT.tiling.mode = .highSmall ∨ PT.tiling.mode = .highLarge) (g : ClusterGroupIndex PT) :
    ((Finset.univ.filter
      (fun e : EvenPosition T k × Bool => g ∈ starGroupQueries PT hPT hm e.1)).card : ℝ) ≤
      4 * (T.S.n k : ℝ) ^ 2 := by
  classical
  have hprod : (Finset.univ.filter
      (fun e : EvenPosition T k × Bool => g ∈ starGroupQueries PT hPT hm e.1)) =
      (Finset.univ.filter fun a : EvenPosition T k => g ∈ starGroupQueries PT hPT hm a) ×ˢ
        (Finset.univ : Finset Bool) := by
    ext e
    simp
  have hinc := starGroupQueries_incidence_card_le PT hPT hm g
  have hh := clusterHeight_le PT hPT g.1.1
  rw [hprod, Finset.card_product, Finset.card_univ, Fintype.card_bool]
  have hnat : (Finset.univ.filter fun a : EvenPosition T k => g ∈ starGroupQueries PT hPT hm a).card *
      2 ≤ 4 * T.S.n k ^ 2 := by
    have h2 : 2 * (PT.tiling.P g.1.1).h * T.S.n k ≤ 2 * T.S.n k * T.S.n k :=
      Nat.mul_le_mul (Nat.mul_le_mul le_rfl hh) le_rfl
    nlinarith
  exact_mod_cast hnat

/-- Star and small-bin duplicate charges (15:126), touching `≤ 1/(4n^4)`. -/
theorem bin_star_charges (κ : CConsts) (hκ : κ.Admissible) (T : Stage) :
    ∀ᶠ k in atTop, ∀ PT : ProfiledTiling κ T k, ∀ hPT : PT.Valid,
    ∀ hm : PT.tiling.mode = .highSmall ∨ PT.tiling.mode = .highLarge,
    ∀ W : ClusterHistory PT hPT hm,
      (∀ a, (clusterIndependentBinKernel PT hPT hm W).pr
        (fun B => (T.S.n k : ℝ) ^ (-(κ.R : ℝ) / 2) < clusterBinStarFailure PT hPT hm W B a) ≤
        (T.S.n k : ℝ) ^ (-(κ.R : ℝ) / 2)) →
      (∀ e, binCharge PT hPT hm W (.inl e) ≤ 1 / 2) ∧
      ∀ g, (∑ e ∈ Finset.univ.filter
          (fun e : EvenPosition T k × Bool => g ∈ starGroupQueries PT hPT hm e.1),
          binCharge PT hPT hm W (.inl e)) ≤ 1 / (4 * (T.S.n k : ℝ) ^ 4) := by
  obtain ⟨c, hc, hDup⟩ := bin_duplicate_charge κ hκ T
  filter_upwards [hDup, bin_star_scale κ hκ T c hc] with k hDup hScale
  intro PT hPT hm W hstar
  obtain ⟨hn2, hsc⟩ := hScale
  have hnR : (2 : ℝ) ≤ (T.S.n k : ℝ) := by exact_mod_cast hn2
  have hnpos : (0 : ℝ) < (T.S.n k : ℝ) := by linarith
  have hrpow : 0 ≤ (T.S.n k : ℝ) ^ (-(κ.R : ℝ) / 2) := (Real.rpow_pos_of_pos hnpos _).le
  have hexp : 0 ≤ 8 * (T.S.n k : ℝ) ^ 2 * Real.exp (-c * (T.S.n k : ℝ)) := by positivity
  set M : ℝ := 2 * (T.S.n k : ℝ) ^ (-(κ.R : ℝ) / 2) +
    8 * (T.S.n k : ℝ) ^ 2 * Real.exp (-c * (T.S.n k : ℝ)) with hMdef
  have hM : ∀ e, binCharge PT hPT hm W (.inl e) ≤ M := by
    rintro ⟨a, f⟩
    cases f
    · have h := bin_star_failure_charge PT hPT hm W a (hstar a)
      linarith
    · have h := hDup PT hPT hm W a
      linarith
  have hn6 : 1 ≤ (T.S.n k : ℝ) ^ 6 := one_le_pow₀ (by linarith)
  have hM0 : 0 ≤ M := by rw [hMdef]; positivity
  have hMsmall : 16 * M ≤ 1 := by nlinarith
  refine ⟨fun e => (hM e).trans (by linarith), ?_⟩
  intro g
  have hcard := star_event_touch_card PT hPT hm g
  calc
    _ ≤ ∑ _e ∈ Finset.univ.filter
          (fun e : EvenPosition T k × Bool => g ∈ starGroupQueries PT hPT hm e.1), M :=
      Finset.sum_le_sum fun e _ => hM e
    _ = ((Finset.univ.filter
          (fun e : EvenPosition T k × Bool => g ∈ starGroupQueries PT hPT hm e.1)).card : ℝ) * M := by
      rw [Finset.sum_const, nsmul_eq_mul]
    _ ≤ 4 * (T.S.n k : ℝ) ^ 2 * M := mul_le_mul_of_nonneg_right hcard hM0
    _ ≤ 1 / (4 * (T.S.n k : ℝ) ^ 4) := by
      rw [le_div_iff₀ (by positivity)]
      have h6 : 4 * (T.S.n k : ℝ) ^ 2 * M * (4 * (T.S.n k : ℝ) ^ 4) =
          16 * (T.S.n k : ℝ) ^ 6 * M := by ring
      rw [h6]
      exact hsc

theorem binCharge_inr_eq {κ : CConsts} {T : Stage} {k : ℕ}
    (PT : ProfiledTiling κ T k) (hPT : PT.Valid)
    (hm : PT.tiling.mode = .highSmall ∨ PT.tiling.mode = .highLarge)
    (W : ClusterHistory PT hPT hm) (C : CapacityCertificate PT) :
    binCharge PT hPT hm W (.inr C) = certificateCharge PT hPT hm W C := by
  show (2 : ℝ) ^ C.2.2.card *
    (clusterIndependentBinKernel PT hPT hm W).pr (certificateEvent PT hPT hm W C) = _
  rw [certificate_probability]
  unfold certificateCharge
  split_ifs <;> simp

theorem certificateCharge_nonneg {κ : CConsts} {T : Stage} {k : ℕ}
    (PT : ProfiledTiling κ T k) (hPT : PT.Valid)
    (hm : PT.tiling.mode = .highSmall ∨ PT.tiling.mode = .highLarge)
    (W : ClusterHistory PT hPT hm) (C : CapacityCertificate PT) :
    0 ≤ certificateCharge PT hPT hm W C := by
  unfold certificateCharge
  split_ifs
  · exact mul_nonneg (by positivity)
      (Finset.prod_nonneg fun g _ => bin_probability_nonneg PT hPT hm W g _)
  · exact le_rfl

/-- Capacity certificate charges (P15.3b, 15:129–150): the touching sum at a group is
`∑_D q_g(D) · clusterPinnedCapacityCharge D g`, and pinned charges are `≤ n^{-5}`. -/
theorem bin_certificate_charges (κ : CConsts) (hκ : κ.Admissible) (T : Stage) (c : ℝ) (hc : 0 < c) :
    ∀ᶠ k in atTop, ∀ PT : ProfiledTiling κ T k, ∀ hPT : PT.Valid,
    ∀ hm : PT.tiling.mode = .highSmall ∨ PT.tiling.mode = .highLarge,
    ∀ W : ClusterHistory PT hPT hm,
      (∀ i (D : Bin PT.tiling i) g, 0 < clusterBinProbability PT hPT hm W g D.1 →
        clusterPinnedCapacityCharge PT hPT hm W D.1 g ≤
          Real.exp (-c * (D.1.card : ℝ) ^ (0.4 : ℝ))) →
      (∀ C, binCharge PT hPT hm W (.inr C) ≤ 1 / 2) ∧
      ∀ g, (∑ C ∈ Finset.univ.filter (fun C : CapacityCertificate PT => g ∈ C.2.2),
          binCharge PT hPT hm W (.inr C)) ≤ 1 / (4 * (T.S.n k : ℝ) ^ 4) := by
  classical
  have hn : ∀ᶠ k in atTop, 4 ≤ T.S.n k := T.S.n_tendsto.eventually_ge_atTop 4
  filter_upwards [high_capacity_charge_tail κ hκ T c 5 hc, hn] with k hTail hn
  intro PT hPT hm W hpin
  have hnR : (4 : ℝ) ≤ (T.S.n k : ℝ) := by exact_mod_cast hn
  have hnpos : (0 : ℝ) < (T.S.n k : ℝ) := by linarith
  have hε : (T.S.n k : ℝ) ^ (-(5 : ℝ)) ≤ 1 / (4 * (T.S.n k : ℝ) ^ 4) := by
    rw [Real.rpow_neg hnpos.le, show (5 : ℝ) = ((5 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]
    rw [inv_eq_one_div, div_le_div_iff₀ (by positivity) (by positivity)]
    have h4 : 0 < (T.S.n k : ℝ) ^ 4 := by positivity
    nlinarith
  have hhalf : 1 / (4 * (T.S.n k : ℝ) ^ 4) ≤ 1 / 2 := by
    rw [div_le_div_iff₀ (by positivity) (by norm_num)]
    have h4 : 1 ≤ (T.S.n k : ℝ) ^ 4 := one_le_pow₀ (by linarith)
    linarith
  have hsum (g : ClusterGroupIndex PT) :
      (∑ C : CapacityCertificate PT, if g ∈ C.2.2 then certificateCharge PT hPT hm W C else 0) ≤
        (T.S.n k : ℝ) ^ (-(5 : ℝ)) :=
    certificate_touching_sum_le PT hPT hm W g _
      (fun D hD => (hpin D.1 D.2 g hD).trans (hTail PT hPT hm D.1 D.2))
  refine ⟨?_, ?_⟩
  · intro C
    rw [binCharge_inr_eq]
    by_cases hact : certificateActive PT hPT hm W C
    · obtain ⟨g, hg⟩ := certificate_active_nonempty hact
      have h1 : certificateCharge PT hPT hm W C ≤
          ∑ C' : CapacityCertificate PT,
            if g ∈ C'.2.2 then certificateCharge PT hPT hm W C' else 0 := by
        have h := Finset.single_le_sum (s := Finset.univ)
          (f := fun C' : CapacityCertificate PT =>
            if g ∈ C'.2.2 then certificateCharge PT hPT hm W C' else 0)
          (fun C' _ => by
            split_ifs
            · exact certificateCharge_nonneg PT hPT hm W C'
            · exact le_rfl) (Finset.mem_univ C)
        simpa only [if_pos hg] using h
      exact h1.trans ((hsum g).trans (hε.trans hhalf))
    · unfold certificateCharge
      rw [if_neg hact]
      norm_num
  · intro g
    rw [Finset.sum_filter]
    simp_rw [binCharge_inr_eq]
    exact (hsum g).trans hε

private theorem half_le_exp_neg {t : ℝ} (ht : t ≤ 1 / 2) : 1 / 2 ≤ Real.exp (-t) := by
  have h := Real.add_one_le_exp (-t)
  linarith

/-- The local lemma applied to the bin events, given touching charges `≤ 1/(2n^4)`. -/
theorem bin_output_of_charges {κ : CConsts} {T : Stage} {k : ℕ}
    (PT : ProfiledTiling κ T k) (hPT : PT.Valid)
    (hm : PT.tiling.mode = .highSmall ∨ PT.tiling.mode = .highLarge)
    (W : ClusterHistory PT hPT hm) (hn : 2 ≤ T.S.n k)
    (hx1 : ∀ e, binCharge PT hPT hm W e ≤ 1 / 2)
    (htouch : ∀ g, (∑ e ∈ Finset.univ.filter (fun e => g ∈ binEventScope PT hPT hm e),
      binCharge PT hPT hm W e) ≤ 1 / (2 * (T.S.n k : ℝ) ^ 4))
    (hcapacity : ∀ B, (clusterIndependentBinKernel PT hPT hm W).w B ≠ 0 →
      clusterCapacityAvoided PT hPT hm W B → ∀ y, clusterGivenBinColumn PT hPT hm W B y ≤ κ.θ0) :
    Nonempty (BinLawOutput PT hPT hm W) := by
  classical
  have hnR : (2 : ℝ) ≤ (T.S.n k : ℝ) := by exact_mod_cast hn
  have hnpos : (0 : ℝ) < (T.S.n k : ℝ) := by linarith
  obtain ⟨δ, hδdef⟩ : ∃ δ : ℝ, δ = 1 / (2 * (T.S.n k : ℝ) ^ 4) := ⟨_, rfl⟩
  have htouchδ : ∀ g, (∑ e ∈ Finset.univ.filter (fun e => g ∈ binEventScope PT hPT hm e),
      binCharge PT hPT hm W e) ≤ δ := by
    rw [hδdef]
    exact htouch
  have hδ0 : 0 ≤ δ := by rw [hδdef]; positivity
  have hn4 : (16 : ℝ) ≤ (T.S.n k : ℝ) ^ 4 := by
    calc (16 : ℝ) = 2 ^ 4 := by norm_num
      _ ≤ _ := pow_le_pow_left₀ (by norm_num) hnR 4
  have hn3 : (8 : ℝ) ≤ (T.S.n k : ℝ) ^ 3 := by
    calc (8 : ℝ) = 2 ^ 3 := by norm_num
      _ ≤ _ := pow_le_pow_left₀ (by norm_num) hnR 3
  have hδsmall : δ ≤ 1 / 32 := by
    rw [hδdef, div_le_div_iff₀ (by positivity) (by norm_num)]
    linarith
  have hδn : 2 * δ * (T.S.n k : ℝ) ≤ 1 / 2 := by
    have heq : 2 * δ * (T.S.n k : ℝ) = 1 / (T.S.n k : ℝ) ^ 3 := by
      rw [hδdef]
      first | (field_simp; ring) | field_simp
    rw [heq, div_le_div_iff₀ (by positivity) (by norm_num)]
    linarith
  have hpr (A : ClusterBinAssignment PT → Prop) :
      0 ≤ (clusterIndependentBinKernel PT hPT hm W).pr A := by
    unfold FinLaw.pr
    exact Finset.sum_nonneg fun B _ => by
      split_ifs
      · exact (clusterIndependentBinKernel PT hPT hm W).nonneg B
      · exact le_rfl
  let P : ∀ g : ClusterGroupIndex PT, FinLaw (clusterBinType g) := fun g =>
    ⟨(clusterSolver PT hPT hm g.1.1).q g.2 (historyOnSlice W g.1),
      (clusterSolver PT hPT hm g.1.1).q_nonneg g.2 (historyOnSlice W g.1),
      (clusterSolver PT hPT hm g.1.1).q_sum g.2 (historyOnSlice W g.1)⟩
  have hPi : FinLaw.pi P = clusterIndependentBinKernel PT hPT hm W := rfl
  let x := binCharge PT hPT hm W
  have hx0 : ∀ e, 0 ≤ x e := binCharge_nonneg PT hPT hm W
  have hx1' : ∀ e, x e < 1 := fun e => lt_of_le_of_lt (hx1 e) (by norm_num)
  have hraw : ∀ e, (FinLaw.pi P).pr (binEventBad PT hPT hm W e) ≤
      x e * Real.exp (-2 * δ * (binEventScope PT hPT hm e).card) := by
    intro e
    rw [hPi]
    cases e with
    | inl e =>
      have hp := hpr (binEventBad PT hPT hm W (.inl e))
      have hcard : ((binEventScope PT hPT hm (.inl e)).card : ℝ) ≤ (T.S.n k : ℝ) := by
        show ((starGroupQueries PT hPT hm e.1).card : ℝ) ≤ (T.S.n k : ℝ)
        exact_mod_cast starGroupQueries_card_le PT hPT hm e.1
      have hexp : 1 / 2 ≤ Real.exp (-2 * δ * (binEventScope PT hPT hm (.inl e)).card) := by
        have h := half_le_exp_neg (t := 2 * δ * (binEventScope PT hPT hm (.inl e)).card)
          ((mul_le_mul_of_nonneg_left hcard (by positivity)).trans hδn)
        simpa only [neg_mul] using h
      change _ ≤ 2 * _ * _
      nlinarith
    | inr C =>
      have hp := hpr (binEventBad PT hPT hm W (.inr C))
      have hbase : 1 ≤ 2 * Real.exp (-2 * δ) := by
        have h := half_le_exp_neg (t := 2 * δ) (by linarith)
        rw [neg_mul]
        linarith
      have hpow : 1 ≤ (2 : ℝ) ^ C.2.2.card * Real.exp (-2 * δ * C.2.2.card) := by
        have hexp : Real.exp (-2 * δ * C.2.2.card) = Real.exp (-2 * δ) ^ C.2.2.card := by
          rw [← Real.exp_nat_mul]
          congr 1
          ring
        rw [hexp, ← mul_pow]
        exact one_le_pow₀ hbase
      change _ ≤ (2 : ℝ) ^ C.2.2.card * _ * Real.exp (-2 * δ * C.2.2.card)
      calc _ = 1 * (clusterIndependentBinKernel PT hPT hm W).pr (binEventBad PT hPT hm W (.inr C)) := by ring
        _ ≤ ((2 : ℝ) ^ C.2.2.card * Real.exp (-2 * δ * C.2.2.card)) *
            (clusterIndependentBinKernel PT hPT hm W).pr (binEventBad PT hPT hm W (.inr C)) :=
          mul_le_mul_of_nonneg_right hpow hp
        _ = _ := by ring
  have hLLL := charge_budget_LLL (binEventScope PT hPT hm) x
    (fun e => (FinLaw.pi P).pr (binEventBad PT hPT hm W e)) δ hx0 hx1 htouchδ hraw
  have hbudget : (T.S.n k : ℝ) ^ 3 * δ ≤ 1 / (2 * (T.S.n k : ℝ)) := by
    apply le_of_eq
    rw [hδdef]
    first | (field_simp; ring) | field_simp
  have hquery := charge_budget_query_comparison (binEventScope PT hPT hm) x δ (T.S.n k : ℝ)
    hx0 hx1' hδ0 (by linarith) htouchδ hbudget
  obtain ⟨L, hLraw, hLavoid, hLcomp⟩ := condition_product_events P (binEventBad PT hPT hm W)
    (binEventScope PT hPT hm) (binEvent_depends PT hPT hm W) x hx0 hx1' hLLL
    ((T.S.n k : ℝ) ^ 3) (1 + 1 / (T.S.n k : ℝ)) hquery
  apply bin_output_of_avoidance PT hPT hm W L
  · intro B hB
    rw [← hPi]
    exact hLraw B hB
  · exact hLavoid
  · exact hcapacity
  · intro F hF S hdep hcard
    rw [← hPi]
    exact hLcomp F hF S hdep hcard

/-- The two charge families sum to the full touching charge. -/
theorem bin_touch_split {κ : CConsts} {T : Stage} {k : ℕ}
    (PT : ProfiledTiling κ T k) (hPT : PT.Valid)
    (hm : PT.tiling.mode = .highSmall ∨ PT.tiling.mode = .highLarge)
    (W : ClusterHistory PT hPT hm) (g : ClusterGroupIndex PT) :
    (∑ e ∈ Finset.univ.filter (fun e => g ∈ binEventScope PT hPT hm e), binCharge PT hPT hm W e) =
      (∑ e ∈ Finset.univ.filter
          (fun e : EvenPosition T k × Bool => g ∈ starGroupQueries PT hPT hm e.1),
          binCharge PT hPT hm W (.inl e)) +
      ∑ C ∈ Finset.univ.filter (fun C : CapacityCertificate PT => g ∈ C.2.2),
          binCharge PT hPT hm W (.inr C) := by
  classical
  rw [Finset.sum_filter, Finset.sum_filter, Finset.sum_filter, Fintype.sum_sum_type]
  rfl

/-- The bin stage at a fixed loaded history, eventually in `k`. -/
theorem bin_local_output (κ : CConsts) (hκ : κ.Admissible) (T : Stage) (c : ℝ) (hc : 0 < c) :
    ∀ᶠ k in atTop, ∀ PT : ProfiledTiling κ T k, ∀ hPT : PT.Valid,
    ∀ hm : PT.tiling.mode = .highSmall ∨ PT.tiling.mode = .highLarge,
    ∀ W : ClusterHistory PT hPT hm,
      (∀ a, (clusterIndependentBinKernel PT hPT hm W).pr
        (fun B => (T.S.n k : ℝ) ^ (-(κ.R : ℝ) / 2) < clusterBinStarFailure PT hPT hm W B a) ≤
        (T.S.n k : ℝ) ^ (-(κ.R : ℝ) / 2)) →
      ((∀ i (D : Bin PT.tiling i) g, 0 < clusterBinProbability PT hPT hm W g D.1 →
        clusterPinnedCapacityCharge PT hPT hm W D.1 g ≤
          Real.exp (-c * (D.1.card : ℝ) ^ (0.4 : ℝ))) ∧
      (∀ B, (clusterIndependentBinKernel PT hPT hm W).w B ≠ 0 →
        clusterCapacityAvoided PT hPT hm W B →
          ∀ y, clusterGivenBinColumn PT hPT hm W B y ≤ κ.θ0)) →
      Nonempty (BinLawOutput PT hPT hm W) := by
  have hn : ∀ᶠ k in atTop, 2 ≤ T.S.n k := T.S.n_tendsto.eventually_ge_atTop 2
  filter_upwards [bin_star_charges κ hκ T, bin_certificate_charges κ hκ T c hc, hn] with
    k hStar hCert hn
  intro PT hPT hm W hstar hcert
  obtain ⟨hs1, hs2⟩ := hStar PT hPT hm W hstar
  obtain ⟨hc1, hc2⟩ := hCert PT hPT hm W hcert.1
  apply bin_output_of_charges PT hPT hm W hn
  · intro e
    cases e with
    | inl e => exact hs1 e
    | inr C => exact hc1 C
  · intro g
    rw [bin_touch_split]
    have h1 := hs2 g
    have h2 := hc2 g
    have hsum : 1 / (4 * (T.S.n k : ℝ) ^ 4) + 1 / (4 * (T.S.n k : ℝ) ^ 4) =
        1 / (2 * (T.S.n k : ℝ) ^ 4) := by
      first | (field_simp; ring) | field_simp
    linarith
  · exact hcert.2

/-! ### Label stage -/

/-- Exact singleton marginals of the independent label kernel: only coordinate `wordAtOdd b` of
the word product law matters. -/
theorem independent_label_singleton_U {κ : CConsts} {T : Stage} {k : ℕ}
    (PT : ProfiledTiling κ T k) (hPT : PT.Valid)
    (hm : PT.tiling.mode = .highSmall ∨ PT.tiling.mode = .highLarge)
    (W : ClusterHistory PT hPT hm) (B : ClusterBinAssignment PT) (b : OddPosition T k)
    (y : Fin (T.S.N k)) :
    (clusterIndependentLabelKernel PT hPT hm W B).pr
      (fun I => clusterLabelFromInternal (hPT := hPT) hm I b = y) =
    (clusterSolver PT hPT hm (patchAt PT hPT b.1)).U (clusterGroupIndexAt PT hPT hm b).2
      (historyOnSlice W (clusterSliceAt PT hPT b.1)) (B (clusterGroupIndexAt PT hPT hm b)) y := by
  classical
  rw [Lane_sol_s15_transfer.pr_eq_E_indicator, Lane_sol_s15_transfer.independent_label_E_eq_word_E]
  have h := Lane_sol_s15_transfer.E_pi_coord (Lane_sol_s15_transfer.wordLabelLaw PT hPT hm W B)
    (Lane_sol_s15_transfer.wordAtOdd PT hPT hm b)
    (fun z => @ite ℝ (z = y) (Classical.propDecidable _) 1 0)
  refine h.trans ?_
  unfold FinLaw.E
  dsimp only
  rw [Finset.sum_eq_single y (fun z _ hz => by rw [if_neg hz, mul_zero])
    (fun h => absurd (Finset.mem_univ y) h), if_pos rfl, mul_one]
  rfl

/-- Sub-lemma (high-large-bin mode, 15:155): the clock lemma with `B = 5`, applied to the
individual laws given successful bins (column sums `≤ θ0` by `hgood`, superpolynomially small
atoms), with the row mass failures (`hmass`) as predicates, gives an odd injection with all mass
gates and comparison factor `2` on `≤ n^2` queried roles. -/
theorem label_clock_large (κ : CConsts) (hκ : κ.Admissible) (T : Stage) :
    ∀ᶠ k in atTop, ∀ PT : ProfiledTiling κ T k, ∀ hPT : PT.Valid,
    ∀ hm : PT.tiling.mode = .highSmall ∨ PT.tiling.mode = .highLarge,
    PT.tiling.mode = .highLarge →
    ∀ W : ClusterHistory PT hPT hm, 0 < (clusterHistoryLaw PT hPT hm).w W →
      clusterAlarmsAvoided PT hPT hm W → clusterHistoryLoad PT hPT hm W →
    ∀ B : ClusterBinAssignment PT, 0 < (clusterIndependentBinKernel PT hPT hm W).w B →
      clusterBinGood PT hPT hm W B →
      (∀ a, (clusterIndependentLabelKernel PT hPT hm W B).pr
        (fun I => clusterRowMass PT hPT hm W I a < 1 / 2) ≤ (T.S.n k : ℝ) ^ (-(κ.R : ℝ) / 2)) →
      ∃ L : FinLaw (ClusterInternalData PT),
        (∀ I, L.w I ≠ 0 → clusterBinsOfInternal I = B) ∧
        (∀ I, L.w I ≠ 0 → ∀ b,
          clusterLabelFromInternal (hPT := hPT) hm I b ∈ (PT.tiling.P (patchAt PT hPT b.1)).Y) ∧
        (∀ I, L.w I ≠ 0 → Function.Injective (clusterLabelFromInternal (hPT := hPT) hm I)) ∧
        (∀ I, L.w I ≠ 0 → ∀ a, (1 / 2 : ℝ) ≤ clusterRowMass PT hPT hm W I a) ∧
        ∀ F : ClusterInternalData PT → ℝ, (∀ I, 0 ≤ F I) →
          ∀ S : Finset (OddPosition T k), ClusterLabelDependsOn hPT hm F S →
            (S.card : ℝ) ≤ (T.S.n k : ℝ) ^ 2 →
              L.E F ≤ 2 * (clusterIndependentLabelKernel PT hPT hm W B).E F := by
  sorry

/-- A product representation of a high-small-bin pre-label law: independent variables `V`
(for instance one calibrated injection per physical bin used by `B`, and one independent label
per word not read by an odd role), each odd role's label read from one variable `var b`. -/
structure LabelProductPreLaw {κ : CConsts} {T : Stage} {k : ℕ}
    (PT : ProfiledTiling κ T k) (hPT : PT.Valid)
    (hm : PT.tiling.mode = .highSmall ∨ PT.tiling.mode = .highLarge)
    (W : ClusterHistory PT hPT hm) (B : ClusterBinAssignment PT) where
  V : Type
  [vFin : Fintype V]
  [vDec : DecidableEq V]
  Ω : V → Type
  [ωFin : ∀ v, Fintype (Ω v)]
  Q : ∀ v, FinLaw (Ω v)
  φ : (∀ v, Ω v) → ClusterInternalData PT
  var : OddPosition T k → V
  pins : ∀ ω, clusterBinsOfInternal (φ ω) = B
  local_label : ∀ b ω ω', ω (var b) = ω' (var b) →
    clusterLabelFromInternal (hPT := hPT) hm (φ ω) b =
      clusterLabelFromInternal (hPT := hPT) hm (φ ω') b
  var_load : ∀ v, ((Finset.univ.filter fun b => var b = v).card : ℝ) ≤ (T.S.n k : ℝ) ^ 2
  singleton : ∀ b y, (FinLaw.map (FinLaw.pi Q) φ).pr
      (fun I => clusterLabelFromInternal (hPT := hPT) hm I b = y) =
    (clusterSolver PT hPT hm (patchAt PT hPT b.1)).U (clusterGroupIndexAt PT hPT hm b).2
      (historyOnSlice W (clusterSliceAt PT hPT b.1)) (B (clusterGroupIndexAt PT hPT hm b)) y
  preComparison : ∀ F : ClusterInternalData PT → ℝ, (∀ I, 0 ≤ F I) →
    ∀ S : Finset (OddPosition T k), ClusterLabelDependsOn hPT hm F S →
      (S.card : ℝ) ≤ (T.S.n k : ℝ) ^ 2 → ClusterLabelQueryOK PT hPT hm B S →
        (FinLaw.map (FinLaw.pi Q) φ).E F ≤
          clusterLabelError PT hPT hm B S * (clusterIndependentLabelKernel PT hPT hm W B).E F
  supported : ∀ ω, (FinLaw.pi Q).w ω ≠ 0 → ∀ b,
    clusterLabelFromInternal (hPT := hPT) hm (φ ω) b ∈ (PT.tiling.P (patchAt PT hPT b.1)).Y
  injective : ∀ ω, (FinLaw.pi Q).w ω ≠ 0 →
    Function.Injective (clusterLabelFromInternal (hPT := hPT) hm (φ ω))

attribute [instance] LabelProductPreLaw.vFin LabelProductPreLaw.vDec LabelProductPreLaw.ωFin

/-- Sub-lemma (high-small-bin pre-law, 15:155, L3.9): independently per physical bin used by `B`,
`near_product_injection` for the individual laws `U` of the roles assigned to it (maximum atom
`≤ d^{-.95}` by (15.13), column sums `≤ θ0 ≤ 0.4`), independent labels on the other words.
Exact singletons; joint upper error `exp(d^{-.04})` per multi-observed role (`clusterLabelError`). -/
theorem label_prelaw_small (κ : CConsts) (hκ : κ.Admissible) (T : Stage) :
    ∀ᶠ k in atTop, ∀ PT : ProfiledTiling κ T k, ∀ hPT : PT.Valid,
    ∀ hm : PT.tiling.mode = .highSmall ∨ PT.tiling.mode = .highLarge,
    PT.tiling.mode = .highSmall →
    ∀ W : ClusterHistory PT hPT hm, 0 < (clusterHistoryLaw PT hPT hm).w W →
      clusterAlarmsAvoided PT hPT hm W → clusterHistoryLoad PT hPT hm W →
    ∀ B : ClusterBinAssignment PT, 0 < (clusterIndependentBinKernel PT hPT hm W).w B →
      clusterBinGood PT hPT hm W B →
      Nonempty (LabelProductPreLaw PT hPT hm W B) := by
  sorry

/-- Sub-lemma (high-small-bin mass conditioning, 15:155): the local lemma on the variables of a
product pre-law against the star mass failures.  Under the pre-law each failure costs
`≤ 2 n^{-R/2}` (`preComparison` on the star, `ClusterLabelQueryOK` from the bin-stage distinctness
`hgood.2.2`, and `hmass`); each variable meets `≤ n^3` stars (`var_load`); queries of `≤ n^2`
roles meet `≤ n^2` variables, so the comparison factor is `1 + o(1) ≤ 2`. -/
theorem label_condition_small (κ : CConsts) (hκ : κ.Admissible) (T : Stage) :
    ∀ᶠ k in atTop, ∀ PT : ProfiledTiling κ T k, ∀ hPT : PT.Valid,
    ∀ hm : PT.tiling.mode = .highSmall ∨ PT.tiling.mode = .highLarge,
    PT.tiling.mode = .highSmall →
    ∀ W : ClusterHistory PT hPT hm, 0 < (clusterHistoryLaw PT hPT hm).w W →
      clusterAlarmsAvoided PT hPT hm W → clusterHistoryLoad PT hPT hm W →
    ∀ B : ClusterBinAssignment PT, 0 < (clusterIndependentBinKernel PT hPT hm W).w B →
      clusterBinGood PT hPT hm W B →
      (∀ a, (clusterIndependentLabelKernel PT hPT hm W B).pr
        (fun I => clusterRowMass PT hPT hm W I a < 1 / 2) ≤ (T.S.n k : ℝ) ^ (-(κ.R : ℝ) / 2)) →
    ∀ X : LabelProductPreLaw PT hPT hm W B,
      ∃ L : FinLaw (ClusterInternalData PT),
        (∀ I, L.w I ≠ 0 → ∃ ω, (FinLaw.pi X.Q).w ω ≠ 0 ∧ X.φ ω = I) ∧
        (∀ I, L.w I ≠ 0 → ∀ a, (1 / 2 : ℝ) ≤ clusterRowMass PT hPT hm W I a) ∧
        ∀ F : ClusterInternalData PT → ℝ, (∀ I, 0 ≤ F I) →
          ∀ S : Finset (OddPosition T k), ClusterLabelDependsOn hPT hm F S →
            (S.card : ℝ) ≤ (T.S.n k : ℝ) ^ 2 →
              L.E F ≤ 2 * (FinLaw.map (FinLaw.pi X.Q) X.φ).E F := by
  classical
  have hScaleEventually := Lane_q_s15_c2.clusterHighSmall_height_degree_scale hκ T
  have hDegreeEventually := Lane_sol_s15_c2.high_degree_ge_log_ten κ hκ T
  have hnEventually : ∀ᶠ k in atTop, 2 ≤ T.S.n k :=
    T.S.n_tendsto.eventually_ge_atTop 2
  let logN : ℕ → ℝ := fun k => Real.log (T.S.n k : ℝ)
  have hlogN : Tendsto logN atTop atTop := Real.tendsto_log_atTop.comp
    (tendsto_natCast_atTop_atTop.comp T.S.n_tendsto)
  have hlogPow : Tendsto (fun k => logN k ^ (-(0.35 : ℝ))) atTop (nhds 0) :=
    (tendsto_rpow_neg_atTop (by norm_num : (0 : ℝ) < 0.35)).comp hlogN
  have hlogTiny : ∀ᶠ k in atTop,
      logN k ^ (-(0.35 : ℝ)) ≤ Real.log (4 / 3) := by
    have hlogpos : 0 < Real.log (4 / 3) := Real.log_pos (by norm_num)
    filter_upwards [hlogPow.eventually (Iio_mem_nhds hlogpos)] with k hk
    exact hk.le
  filter_upwards [hScaleEventually, hDegreeEventually, hnEventually, hlogTiny,
      hlogN.eventually_ge_atTop 1] with k hScale hDegree hn hlogTiny hlogOne
  intro PT hPT hm hs W hW havoid hload B hB hgood hmass X
  let n : ℝ := T.S.n k
  have hnR : 2 ≤ n := by
    change (2 : ℝ) ≤ (T.S.n k : ℝ)
    exact_mod_cast hn
  have hn1 : 1 ≤ n := by linarith
  have hnPos : 0 < n := by linarith
  have hRnat : 28 ≤ κ.R := by
    have hP : 21000 ≤ κ.P := by
      have h := hκ.P_big.2
      rw [hκ.Ac_eq] at h
      omega
    rw [hκ.R_eq]
    nlinarith
  have hR : (28 : ℝ) ≤ (κ.R : ℝ) := by exact_mod_cast hRnat
  have hRpowExp : -(κ.R : ℝ) / 2 ≤ -14 := by linarith
  have hRpow : n ^ (-(κ.R : ℝ) / 2) ≤ n ^ (-14 : ℝ) :=
    Real.rpow_le_rpow_of_exponent_le hn1 hRpowExp
  have hnPow14 : (2 : ℝ) ^ 14 ≤ n ^ 14 :=
    pow_le_pow_left₀ (by norm_num) hnR 14
  have hnPow10 : (2 : ℝ) ^ 10 ≤ n ^ 10 :=
    pow_le_pow_left₀ (by norm_num) hnR 10
  have hNatPow14 : n ^ (14 : ℝ) = n ^ 14 := Real.rpow_natCast n 14
  have hNeg14 : n ^ (-14 : ℝ) = 1 / n ^ 14 := by
    rw [show (-14 : ℝ) = -(14 : ℝ) by norm_num,
      Real.rpow_neg hnPos.le (14 : ℝ), hNatPow14]
    exact (one_div (n ^ 14)).symm
  have hRpowRecip : n ^ (-(κ.R : ℝ) / 2) ≤ 1 / n ^ 14 := by
    rw [← hNeg14]
    exact hRpow
  have hRecip14 : 1 / n ^ 14 ≤ 1 / (2 : ℝ) ^ 14 :=
    one_div_le_one_div_of_le (by positivity) hnPow14
  let x0 : ℝ := 4 * n ^ (-(κ.R : ℝ) / 2)
  let δ : ℝ := n ^ 3 * x0
  have hx0pos : 0 < x0 := by
    dsimp [x0]
    positivity
  have hx0small : x0 ≤ 4 / (2 : ℝ) ^ 14 := by
    dsimp [x0]
    calc
      _ ≤ 4 * (1 / (2 : ℝ) ^ 14) :=
        mul_le_mul_of_nonneg_left (hRpowRecip.trans hRecip14) (by norm_num)
      _ = 4 / (2 : ℝ) ^ 14 := by ring
  have hx0lt : x0 < 1 := by
    have hnum : (4 : ℝ) / (2 : ℝ) ^ 14 < 1 := by norm_num
    exact lt_of_le_of_lt hx0small hnum
  have hx0half : x0 ≤ 1 / 2 := by
    have hnum : (4 : ℝ) / (2 : ℝ) ^ 14 ≤ 1 / 2 := by norm_num
    exact hx0small.trans hnum
  have hDeltaNonneg : 0 ≤ δ := by dsimp [δ]; positivity
  have hDeltaN : δ * n ≤ 4 / n ^ 10 := by
    dsimp [δ, x0]
    calc
      n ^ 3 * (4 * n ^ (-(κ.R : ℝ) / 2)) * n =
          4 * n ^ 4 * n ^ (-(κ.R : ℝ) / 2) := by ring
      _ ≤ 4 * n ^ 4 * (1 / n ^ 14) := by
        exact mul_le_mul_of_nonneg_left hRpowRecip (by positivity)
      _ = 4 / n ^ 10 := by field_simp
  have hDeltaNhalf : 2 * δ * n ≤ 1 / 2 := by
    calc
      2 * δ * n = 2 * (δ * n) := by ring
      _ ≤ 2 * (4 / n ^ 10) := by nlinarith [hDeltaN]
      _ ≤ 2 * (4 / (2 : ℝ) ^ 10) := by
        have hdiv : 4 / n ^ 10 ≤ 4 / (2 : ℝ) ^ 10 := by
          apply (div_le_div_iff₀ (by positivity) (by positivity)).2
          nlinarith [hnPow10]
        nlinarith [hdiv]
      _ ≤ 1 / 2 := by norm_num
  have hBudget : n ^ 3 * δ ≤ 1 / (2 * n) := by
    have hRemainder : 8 * n ≤ n ^ 8 := by
      have hpow : (8 : ℝ) ≤ n ^ 7 := by
        have h := pow_le_pow_left₀ (by norm_num) hnR 7
        norm_num at h ⊢
        exact le_trans (by norm_num) h
      calc
        8 * n ≤ n ^ 7 * n := mul_le_mul_of_nonneg_right hpow (by positivity)
        _ = n ^ 8 := by ring
    calc
      n ^ 3 * δ = 4 * n ^ 6 * n ^ (-(κ.R : ℝ) / 2) := by
        dsimp [δ, x0]
        ring
      _ ≤ 4 * n ^ 6 * (1 / n ^ 14) :=
        mul_le_mul_of_nonneg_left hRpowRecip (by positivity)
      _ = 4 / n ^ 8 := by field_simp
      _ ≤ 1 / (2 * n) := by
        apply (div_le_div_iff₀ (by positivity) (by positivity)).2
        nlinarith
  let scope : EvenPosition T k → Finset X.V := fun a =>
    (Lane_q_s15_direct.star a).image X.var
  let bad : EvenPosition T k → (∀ v, X.Ω v) → Prop := fun a ω =>
    clusterRowMass PT hPT hm W (X.φ ω) a < 1 / 2
  let Q : FinLaw (∀ v, X.Ω v) := FinLaw.pi X.Q
  have hstarCard (a : EvenPosition T k) :
      ((Lane_q_s15_direct.star a).card : ℝ) ≤ n ^ 2 := by
    have hnat : (Lane_q_s15_direct.star a).card ≤ (T.S.n k) ^ 2 := by
      calc
        _ ≤ T.S.n k := Lane_q_s15_direct.star_card_le a
        _ ≤ (T.S.n k) ^ 2 := by nlinarith [hn]
    change ((Lane_q_s15_direct.star a).card : ℝ) ≤ (T.S.n k : ℝ) ^ 2
    exact_mod_cast hnat
  have hscopeCard (a : EvenPosition T k) : (scope a).card ≤ T.S.n k := by
    calc
      _ ≤ (Lane_q_s15_direct.star a).card := Finset.card_image_le
      _ ≤ T.S.n k := Lane_q_s15_direct.star_card_le a
  have hscopeCardR (a : EvenPosition T k) : ((scope a).card : ℝ) ≤ n := by
    change ((scope a).card : ℝ) ≤ (T.S.n k : ℝ)
    exact_mod_cast hscopeCard a
  have hdepBad : ∀ a, FinProb.DependsOn (bad a) (scope a) := by
    intro a ω ω' hω
    have hlabels (b : OddPosition T k) (hb : b ∈ Lane_q_s15_direct.star a) :
        clusterLabelFromInternal (hPT := hPT) hm (X.φ ω) b =
          clusterLabelFromInternal (hPT := hPT) hm (X.φ ω') b := by
      exact X.local_label b ω ω'
        (hω (X.var b) (Finset.mem_image.mpr ⟨b, hb, rfl⟩))
    have hmassEq := Lane_sol_s15_c2.row_mass_label_depends PT hPT hm W a
      (X.φ ω) (X.φ ω') hlabels
    exact congrArg (fun z : ℝ => z < 1 / 2) hmassEq
  have hqueryStar (a : EvenPosition T k) :
      ClusterLabelQueryOK PT hPT hm B (Lane_q_s15_direct.star a) := by
    intro hsmall b hb
    let Qb : Finset (OddPosition T k) :=
      (Lane_q_s15_direct.star a).filter fun b' =>
        (B (clusterGroupIndexAt PT hPT hm b')).1 =
          (B (clusterGroupIndexAt PT hPT hm b)).1
    have hQsub : Qb ⊆ Finset.univ.filter fun b' : OddPosition T k =>
        clusterGroupIndexAt PT hPT hm b' = clusterGroupIndexAt PT hPT hm b := by
      intro b' hb'
      have hAdj : Adjacent a b := (Finset.mem_filter.mp hb).2
      have hAdj' : Adjacent a b' := (Finset.mem_filter.mp (Finset.mem_filter.mp hb').1).2
      have hbin : (B (clusterGroupIndexAt PT hPT hm b)).1 =
          (B (clusterGroupIndexAt PT hPT hm b')).1 := (Finset.mem_filter.mp hb').2.symm
      have hgroup := Lane_q_s15_c2.clusterBinGood_same_bin_implies_same_group
        W B hgood hsmall hAdj hAdj' hbin
      exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, hgroup.symm⟩
    have hcount : clusterBinQueryCount PT hPT hm B
        (Lane_q_s15_direct.star a) b ≤
          (PT.tiling.P (patchAt PT hPT b.1)).h := by
      change Qb.card ≤ _
      calc
        _ ≤ (Finset.univ.filter fun b' : OddPosition T k =>
          clusterGroupIndexAt PT hPT hm b' = clusterGroupIndexAt PT hPT hm b).card :=
            Finset.card_le_card hQsub
        _ ≤ (PT.tiling.P (clusterGroupIndexAt PT hPT hm b).1.1).h :=
          Lane_sol_s15_c2.group_role_count_le_height PT hPT hm
            (clusterGroupIndexAt PT hPT hm b)
        _ = (PT.tiling.P (patchAt PT hPT b.1)).h := rfl
    have hcountR : (clusterBinQueryCount PT hPT hm B
        (Lane_q_s15_direct.star a) b : ℝ) ≤
          ((PT.tiling.P (patchAt PT hPT b.1)).h : ℝ) := by exact_mod_cast hcount
    calc
      _ ≤ ((PT.tiling.P (patchAt PT hPT b.1)).h : ℝ) := hcountR
      _ ≤ 2 * ((PT.tiling.P (patchAt PT hPT b.1)).h : ℝ) := by nlinarith
      _ ≤ ((PT.tiling.P (patchAt PT hPT b.1)).d : ℝ) ^ (0.025 : ℝ) :=
        (hScale PT.tiling hPT.tiling_valid hsmall
          (patchAt PT hPT b.1)).2.1
  have hLabelError (a : EvenPosition T k) :
      clusterLabelError PT hPT hm B (Lane_q_s15_direct.star a) ≤ 4 / 3 := by
    let i := patchAt PT hPT a.1
    let intCoord (l : Fin (PT.tiling.P i).h) : Fin (T.S.n k) :=
      ⟨T.S.n k - (PT.tiling.P i).h + l.val, by
        have hh := clusterHeight_le PT hPT i
        have hl := l.isLt
        omega⟩
    let intRole (l : Fin (PT.tiling.P i).h) : OddPosition T k :=
      ⟨flipPos a.1 (intCoord l),
        fun hEven => (evenRole_flipPos a.1 (intCoord l)).mp hEven a.2⟩
    let intRoles : Finset (OddPosition T k) := Finset.univ.image intRole
    have hIntPatch (b : OddPosition T k) (hb : b ∈ intRoles) :
        patchAt PT hPT b.1 = i := by
      obtain ⟨l, hl, rfl⟩ := Finset.mem_image.mp hb
      simpa [intRole, intCoord, i] using
        Lane_q_s15_c2.patchAt_flip_internal PT hPT a.1 l
    have hFlipInv {v : OAI.HypercubeRamsey.CubeVertex (T.S.n k)} (j : Fin (T.S.n k)) :
        flipPos (flipPos v j) j = v := by
      funext t
      by_cases ht : t = j <;> simp [flipPos, ht]
    have heqFinApply {m n : ℕ} (hmn : m = n)
        {f : Fin m → Bool} {g : Fin n → Bool} (hfg : HEq f g) (j : Fin m) :
        f j = g (Fin.cast hmn j) := by
      cases hmn
      exact congrFun (eq_of_heq hfg) j
    have hsameSliceUnique {b b' : OddPosition T k}
        (hab : Adjacent a b) (hab' : Adjacent a b')
        (hslice : clusterSliceAt PT hPT b.1 = clusterSliceAt PT hPT b'.1)
        (hnot : clusterSliceAt PT hPT b.1 ≠ clusterSliceAt PT hPT a.1) : b = b' := by
      obtain ⟨j, hbj⟩ := Lane_sol_s15_transfer.adjacent_eq_flip hab
      obtain ⟨j', hbj'⟩ := Lane_sol_s15_transfer.adjacent_eq_flip hab'
      have hnot' : clusterSliceAt PT hPT b'.1 ≠ clusterSliceAt PT hPT a.1 := by
        intro h
        exact hnot (hslice.trans h)
      let ib := patchAt PT hPT b.1
      have hpatch : patchAt PT hPT b.1 = patchAt PT hPT b'.1 := congrArg Sigma.fst hslice
      have hdim : T.S.n k - (PT.tiling.P ib).h =
          T.S.n k - (PT.tiling.P (patchAt PT hPT b'.1)).h :=
        congrArg (fun p : Fin PT.tiling.m => T.S.n k - (PT.tiling.P p).h) hpatch
      have houtHEq : HEq (outsideWord PT hPT (patchAt PT hPT b.1) b.1)
          (outsideWord PT hPT (patchAt PT hPT b'.1) b'.1) := by
        exact Lane_q_s15_cond.heq_of_dependent_apply
          (fun s : ClusterSlice PT => s.2.1) hslice
      have hjExternal : j.val < T.S.n k - (PT.tiling.P ib).h := by
        by_contra hj
        let l : Fin (PT.tiling.P ib).h :=
          ⟨j.val - (T.S.n k - (PT.tiling.P ib).h), by
            have hh := clusterHeight_le PT hPT ib
            omega⟩
        let c : Fin (T.S.n k) := ⟨T.S.n k - (PT.tiling.P ib).h + l.val,
          by have hh := clusterHeight_le PT hPT ib; have hl := l.isLt; omega⟩
        have hc : c = j := by
          apply Fin.ext
          dsimp [c, l]
          omega
        have hback : flipPos b.1 c = a.1 := by
          rw [hbj, hc]
          exact hFlipInv j
        have hsliceBack := Lane_q_s15_c2.clusterSliceAt_flip_internal PT hPT b.1 l
        rw [hback] at hsliceBack
        exact hnot hsliceBack.symm
      let ib' := patchAt PT hPT b'.1
      have hjExternal' : j'.val < T.S.n k - (PT.tiling.P ib').h := by
        by_contra hj
        let l : Fin (PT.tiling.P ib').h :=
          ⟨j'.val - (T.S.n k - (PT.tiling.P ib').h), by
            have hh := clusterHeight_le PT hPT ib'
            omega⟩
        let c : Fin (T.S.n k) := ⟨T.S.n k - (PT.tiling.P ib').h + l.val,
            by have hh := clusterHeight_le PT hPT ib'; have hl := l.isLt; omega⟩
        have hc : c = j' := by
          apply Fin.ext
          dsimp [c, l]
          omega
        have hback : flipPos b'.1 c = a.1 := by
          rw [hbj', hc]
          exact hFlipInv j'
        have hsliceBack := Lane_q_s15_c2.clusterSliceAt_flip_internal PT hPT b'.1 l
        rw [hback] at hsliceBack
        exact hnot' hsliceBack.symm
      have hcoord : b.1 j = b'.1 j := by
        have he := heqFinApply hdim houtHEq ⟨j.val, hjExternal⟩
        simpa [outsideWord] using he
      have hjEq : j = j' := by
        by_contra hne
        rw [hbj, hbj'] at hcoord
        cases ha : a.1 j <;> simp [flipPos, ha, hne, Ne.symm hne] at hcoord
      apply Subtype.ext
      rw [hbj, hbj', hjEq]
    have hInternal (b : OddPosition T k) (hb : b ∈ Lane_q_s15_direct.star a)
        (hslice : clusterSliceAt PT hPT b.1 = clusterSliceAt PT hPT a.1) :
        b ∈ intRoles := by
      have hab : Adjacent a b := (Finset.mem_filter.mp hb).2
      obtain ⟨j, hbj⟩ := Lane_sol_s15_transfer.adjacent_eq_flip hab
      have hpatch : patchAt PT hPT b.1 = patchAt PT hPT a.1 := congrArg Sigma.fst hslice
      have hdim : T.S.n k - (PT.tiling.P (patchAt PT hPT b.1)).h =
          T.S.n k - (PT.tiling.P (patchAt PT hPT a.1)).h :=
        congrArg (fun p : Fin PT.tiling.m => T.S.n k - (PT.tiling.P p).h) hpatch
      have houtHEq : HEq (outsideWord PT hPT (patchAt PT hPT b.1) b.1)
          (outsideWord PT hPT (patchAt PT hPT a.1) a.1) := by
        exact Lane_q_s15_cond.heq_of_dependent_apply
          (fun s : ClusterSlice PT => s.2.1) hslice
      have hjInternal : T.S.n k - (PT.tiling.P (patchAt PT hPT a.1)).h ≤ j.val := by
        by_contra hj
        have hjext : j.val < T.S.n k - (PT.tiling.P (patchAt PT hPT a.1)).h := by omega
        let qA : Fin (T.S.n k - (PT.tiling.P (patchAt PT hPT a.1)).h) :=
          ⟨j.val, hjext⟩
        have he := heqFinApply hdim houtHEq (Fin.cast hdim.symm qA)
        have heq : b.1 j = a.1 j := by simpa [outsideWord] using he
        rw [hbj] at heq
        cases ha : a.1 j <;> simp [flipPos, ha] at heq
      let l : Fin (PT.tiling.P (patchAt PT hPT a.1)).h :=
        ⟨j.val - (T.S.n k - (PT.tiling.P (patchAt PT hPT a.1)).h), by
          have hh := clusterHeight_le PT hPT (patchAt PT hPT a.1)
          omega⟩
      have hc : intCoord l = j := by
        apply Fin.ext
        dsimp [intCoord, l, i]
        omega
      have hval : b.1 = (intRole l).1 := by
        rw [hbj]
        change flipPos a.1 j = flipPos a.1 (intCoord l)
        rw [← hc]
      exact Finset.mem_image.mpr ⟨l, Finset.mem_univ _, by
        apply Subtype.ext
        exact hval.symm⟩
    let S := Lane_q_s15_direct.star a
    let repeated := S.filter fun b => 2 ≤ clusterBinQueryCount PT hPT hm B S b
    have hRepeatedSub : repeated ⊆ intRoles := by
      intro b hb
      have hbS : b ∈ S := (Finset.mem_filter.mp hb).1
      have hrep : 2 ≤ clusterBinQueryCount PT hPT hm B S b := (Finset.mem_filter.mp hb).2
      let Qb : Finset (OddPosition T k) := S.filter fun b' =>
        (B (clusterGroupIndexAt PT hPT hm b')).1 =
          (B (clusterGroupIndexAt PT hPT hm b)).1
      have hbQ : b ∈ Qb := Finset.mem_filter.mpr ⟨hbS, rfl⟩
      have hQcard : 2 ≤ Qb.card := by simpa [clusterBinQueryCount, Qb] using hrep
      have hQerase : 0 < (Qb.erase b).card := by
        rw [Finset.card_erase_of_mem hbQ]
        omega
      obtain ⟨b', hb'erase⟩ := Finset.card_pos.mp hQerase
      have hb'Q : b' ∈ Qb := Finset.mem_of_mem_erase hb'erase
      have hne : b' ≠ b := (Finset.mem_erase.mp hb'erase).1
      have hbin : (B (clusterGroupIndexAt PT hPT hm b)).1 =
          (B (clusterGroupIndexAt PT hPT hm b')).1 := (Finset.mem_filter.mp hb'Q).2.symm
      have hab : Adjacent a b := (Finset.mem_filter.mp hbS).2
      have hab' : Adjacent a b' := (Finset.mem_filter.mp (Finset.mem_filter.mp hb'Q).1).2
      have hgroup := Lane_q_s15_c2.clusterBinGood_same_bin_implies_same_group
        W B hgood hs hab hab' hbin
      have hslice : clusterSliceAt PT hPT b.1 = clusterSliceAt PT hPT b'.1 :=
        congrArg Sigma.fst hgroup
      have hsliceCenter : clusterSliceAt PT hPT b.1 = clusterSliceAt PT hPT a.1 := by
        by_contra hnot
        have heq := hsameSliceUnique hab hab' hslice hnot
        exact hne heq.symm
      exact hInternal b hbS hsliceCenter
    have hIntRolesCard : (intRoles.card : ℝ) ≤ (PT.tiling.P i).h := by
      have hNat : intRoles.card ≤ (PT.tiling.P i).h := by
        unfold intRoles
        calc
          _ ≤ (Finset.univ : Finset (Fin (PT.tiling.P i).h)).card := Finset.card_image_le
          _ = (PT.tiling.P i).h := by simp
      exact_mod_cast hNat
    have hsumEq : (∑ b ∈ S, if 2 ≤ clusterBinQueryCount PT hPT hm B S b then
        ((PT.tiling.P (patchAt PT hPT b.1)).d : ℝ) ^ (-0.04 : ℝ) else 0) =
        ∑ b ∈ repeated, ((PT.tiling.P (patchAt PT hPT b.1)).d : ℝ) ^ (-0.04 : ℝ) := by
      simp [repeated, Finset.sum_filter]
    have hfNonneg (b : OddPosition T k) :
        0 ≤ ((PT.tiling.P (patchAt PT hPT b.1)).d : ℝ) ^ (-0.04 : ℝ) := by positivity
    have hsumSubset := Finset.sum_le_sum_of_subset_of_nonneg hRepeatedSub
      (fun b _ _ => hfNonneg b)
    have hsumConst : (∑ b ∈ intRoles,
        ((PT.tiling.P (patchAt PT hPT b.1)).d : ℝ) ^ (-0.04 : ℝ)) =
        (intRoles.card : ℝ) * ((PT.tiling.P i).d : ℝ) ^ (-0.04 : ℝ) := by
      calc
        _ = ∑ _b ∈ intRoles, ((PT.tiling.P i).d : ℝ) ^ (-0.04 : ℝ) := by
          apply Finset.sum_congr rfl
          intro b hb
          rw [hIntPatch b hb]
        _ = _ := by simp
    have hdLower : (logN k) ^ (10 : ℝ) ≤ (PT.tiling.P i).d := by
      exact_mod_cast hDegree PT hPT hm i
    have hlogPos : 0 < logN k := by linarith [hlogOne]
    have hdPos : 0 < ((PT.tiling.P i).d : ℝ) := by
      have hpow : 1 ≤ (logN k) ^ (10 : ℝ) := by
        calc
          1 = (logN k) ^ (0 : ℝ) := by simp [hlogPos.ne']
          _ ≤ _ := Real.rpow_le_rpow_of_exponent_le hlogOne (by norm_num)
      have hdge1 : (1 : ℝ) ≤ ((PT.tiling.P i).d : ℝ) := hpow.trans hdLower
      linarith
    have hraise : (logN k) ^ (0.35 : ℝ) ≤ ((PT.tiling.P i).d : ℝ) ^ (0.035 : ℝ) := by
      calc
        _ = ((logN k) ^ (10 : ℝ)) ^ (0.035 : ℝ) := by
          rw [← Real.rpow_mul (le_of_lt hlogPos)]
          norm_num
        _ ≤ _ := Real.rpow_le_rpow
          (Real.rpow_nonneg (le_of_lt hlogPos) _) hdLower (by norm_num)
    have hsmallD : ((PT.tiling.P i).d : ℝ) ^ (-0.035 : ℝ) ≤
        (logN k) ^ (-0.35 : ℝ) := by
      rw [show (-0.035 : ℝ) = -(0.035 : ℝ) by norm_num,
        show (-0.35 : ℝ) = -(0.35 : ℝ) by norm_num,
        Real.rpow_neg hdPos.le (0.035 : ℝ), Real.rpow_neg hlogPos.le (0.35 : ℝ)]
      simpa only [one_div] using
        one_div_le_one_div_of_le (Real.rpow_pos_of_pos hlogPos _) hraise
    have hsmallHD : ((PT.tiling.P i).h : ℝ) *
        ((PT.tiling.P i).d : ℝ) ^ (-0.04 : ℝ) ≤ Real.log (4 / 3) := by
      calc
        _ ≤ ((PT.tiling.P i).d : ℝ) ^ (0.005 : ℝ) *
            ((PT.tiling.P i).d : ℝ) ^ (-0.04 : ℝ) :=
          mul_le_mul_of_nonneg_right (hScale PT.tiling hPT.tiling_valid hs i).1
            (Real.rpow_nonneg (Nat.cast_nonneg _) _)
        _ = ((PT.tiling.P i).d : ℝ) ^ (-0.035 : ℝ) := by
          rw [← Real.rpow_add hdPos]
          norm_num
        _ ≤ (logN k) ^ (-0.35 : ℝ) := hsmallD
        _ ≤ Real.log (4 / 3) := hlogTiny
    have hExponent : (∑ b ∈ S, if 2 ≤ clusterBinQueryCount PT hPT hm B S b then
        ((PT.tiling.P (patchAt PT hPT b.1)).d : ℝ) ^ (-0.04 : ℝ) else 0) ≤
        Real.log (4 / 3) := by
      rw [hsumEq]
      calc
        _ ≤ ∑ b ∈ intRoles,
            ((PT.tiling.P (patchAt PT hPT b.1)).d : ℝ) ^ (-0.04 : ℝ) := hsumSubset
        _ = (intRoles.card : ℝ) * ((PT.tiling.P i).d : ℝ) ^ (-0.04 : ℝ) := hsumConst
        _ ≤ ((PT.tiling.P i).h : ℝ) * ((PT.tiling.P i).d : ℝ) ^ (-0.04 : ℝ) :=
          mul_le_mul_of_nonneg_right hIntRolesCard (Real.rpow_nonneg (Nat.cast_nonneg _) _)
        _ ≤ Real.log (4 / 3) := hsmallHD
    rw [clusterLabelError, if_pos hs]
    calc
      _ ≤ Real.exp (Real.log (4 / 3)) := Real.exp_le_exp.mpr hExponent
      _ = 4 / 3 := Real.exp_log (by norm_num)
  have hbadFdep (a : EvenPosition T k) : ClusterLabelDependsOn hPT hm
      (fun I => if clusterRowMass PT hPT hm W I a < 1 / 2 then (1 : ℝ) else 0)
      (Lane_q_s15_direct.star a) := by
    intro I I' hlabels
    have hmassEq := Lane_sol_s15_c2.row_mass_label_depends PT hPT hm W a I I' hlabels
    simp [hmassEq]
  have hprob (a : EvenPosition T k) : Q.pr (bad a) ≤ 2 * n ^ (-(κ.R : ℝ) / 2) := by
    let F : ClusterInternalData PT → ℝ := fun I =>
      if clusterRowMass PT hPT hm W I a < 1 / 2 then 1 else 0
    have hF : ∀ I, 0 ≤ F I := by intro I; dsimp [F]; split_ifs <;> norm_num
    have hpre := X.preComparison F hF (Lane_q_s15_direct.star a) (hbadFdep a)
      (hstarCard a) (hqueryStar a)
    have hmassE : (clusterIndependentLabelKernel PT hPT hm W B).E F ≤
        n ^ (-(κ.R : ℝ) / 2) := by
      have h := hmass a
      rw [Lane_sol_s15_transfer.pr_eq_E_indicator] at h
      exact h
    have hQprob : Q.pr (bad a) = (FinLaw.map Q X.φ).E F := by
      calc
        _ = Q.E (fun ω => if bad a ω then (1 : ℝ) else 0) :=
          Lane_sol_s15_transfer.pr_eq_E_indicator Q (bad a)
        _ = (FinLaw.map Q X.φ).E F := by
          rw [Lane_q_s15_c3.finLaw_map_E]
    rw [hQprob]
    calc
      _ ≤ clusterLabelError PT hPT hm B (Lane_q_s15_direct.star a) *
          (clusterIndependentLabelKernel PT hPT hm W B).E F := hpre
      _ ≤ (4 / 3) * n ^ (-(κ.R : ℝ) / 2) := by
        have hEpos : 0 ≤ (clusterIndependentLabelKernel PT hPT hm W B).E F := by
          unfold FinLaw.E
          exact Finset.sum_nonneg fun I _ => mul_nonneg
            ((clusterIndependentLabelKernel PT hPT hm W B).nonneg I) (hF I)
        calc
          _ ≤ (4 / 3) * (clusterIndependentLabelKernel PT hPT hm W B).E F :=
            mul_le_mul_of_nonneg_right (hLabelError a) hEpos
          _ ≤ _ := mul_le_mul_of_nonneg_left hmassE (by norm_num)
      _ ≤ 2 * n ^ (-(κ.R : ℝ) / 2) := by
        exact mul_le_mul_of_nonneg_right (by norm_num : (4 / 3 : ℝ) ≤ 2)
          (Real.rpow_nonneg (le_of_lt hnPos) _)
  have htouch : ∀ v : X.V,
      (∑ a ∈ Finset.univ.filter (fun a : EvenPosition T k => v ∈ scope a), x0) ≤ δ := by
    intro v
    let roles := Finset.univ.filter fun b : OddPosition T k => X.var b = v
    let incident := Finset.univ.filter fun a : EvenPosition T k => v ∈ scope a
    have hsub : incident ⊆ roles.biUnion Lane_q_s15_direct.starIncidence := by
      intro a ha
      obtain ⟨b, hb, hv⟩ := Finset.mem_image.mp (Finset.mem_filter.mp ha).2
      exact Finset.mem_biUnion.mpr ⟨b, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hv⟩,
        by simpa [Lane_q_s15_direct.starIncidence, Lane_q_s15_direct.star] using hb⟩
    have hincNat : incident.card ≤ roles.card * T.S.n k := by
      calc
        _ ≤ (roles.biUnion Lane_q_s15_direct.starIncidence).card := Finset.card_le_card hsub
        _ ≤ ∑ b ∈ roles, (Lane_q_s15_direct.starIncidence b).card := Finset.card_biUnion_le
        _ ≤ ∑ _b ∈ roles, T.S.n k := Finset.sum_le_sum fun b hb =>
          Lane_q_s15_direct.star_incidence_card_le b
        _ = roles.card * T.S.n k := by simp
    have hincR : (incident.card : ℝ) ≤ n ^ 3 := by
      calc
        _ ≤ (roles.card : ℝ) * (T.S.n k : ℝ) := by exact_mod_cast hincNat
        _ ≤ (T.S.n k : ℝ) ^ 2 * (T.S.n k : ℝ) :=
          mul_le_mul_of_nonneg_right (X.var_load v) (by positivity)
        _ = n ^ 3 := by dsimp [n]; ring
    calc
      _ = (incident.card : ℝ) * x0 := by simp [incident]
      _ ≤ n ^ 3 * x0 := mul_le_mul_of_nonneg_right hincR hx0pos.le
      _ = δ := rfl
  have hraw : ∀ a, Q.pr (bad a) ≤ x0 * Real.exp (-2 * δ * (scope a).card) := by
    intro a
    have ht : 2 * δ * (scope a).card ≤ 1 / 2 := by
      calc
        _ ≤ 2 * δ * n := mul_le_mul_of_nonneg_left (hscopeCardR a) (by positivity)
        _ ≤ 1 / 2 := hDeltaNhalf
    have hexp := half_le_exp_neg (t := 2 * δ * (scope a).card) ht
    calc
      _ ≤ 2 * n ^ (-(κ.R : ℝ) / 2) := hprob a
      _ ≤ x0 * (1 / 2) := by
        dsimp [x0]
        nlinarith [Real.rpow_pos_of_pos hnPos (-(κ.R : ℝ) / 2)]
      _ ≤ x0 * Real.exp (-(2 * δ * (scope a).card)) :=
        mul_le_mul_of_nonneg_left hexp hx0pos.le
      _ = x0 * Real.exp (-2 * δ * (scope a).card) := by ring_nf
  have hLLL := Lane_sol_s15_c2.charge_budget_LLL scope (fun _ => x0)
    (fun a => Q.pr (bad a)) δ (fun _ => hx0pos.le) (fun _ => hx0half)
    htouch hraw
  have hquery := Lane_sol_s15_c2.charge_budget_query_comparison scope (fun _ => x0) δ n
    (fun _ => hx0pos.le) (fun _ => hx0lt) hDeltaNonneg hn1 htouch hBudget
  obtain ⟨Lraw, hLraw, hLavoid, hLcomp⟩ :=
    Lane_sol_s15_c2.condition_product_events X.Q bad scope hdepBad (fun _ => x0)
      (fun _ => hx0pos.le) (fun _ => hx0lt) hLLL (n ^ 3) (1 + 1 / n) hquery
  let L := FinLaw.map Lraw X.φ
  have hMapSupport : ∀ I, L.w I ≠ 0 → ∃ ω, Lraw.w ω ≠ 0 ∧ X.φ ω = I := by
    intro I hI
    by_contra hnone
    have hzero : L.w I = 0 := by
      unfold L FinLaw.map
      apply Finset.sum_eq_zero
      intro ω hω
      by_cases hφ : X.φ ω = I
      · have hweight : Lraw.w ω = 0 := by
          by_contra hweight
          exact hnone ⟨ω, hweight, hφ⟩
        simp [hφ, hweight]
      · simp [hφ]
    exact hI hzero
  refine ⟨L, ?_, ?_, ?_⟩
  · intro I hI
    obtain ⟨ω, hω, hφ⟩ := hMapSupport I hI
    exact ⟨ω, hLraw ω hω, hφ⟩
  · intro I hI a
    obtain ⟨ω, hω, hφ⟩ := hMapSupport I hI
    have havoidω := hLavoid ω hω a
    rw [← hφ]
    exact le_of_not_gt havoidω
  · intro F hF S hdep hcard
    let U := S.image X.var
    let G : (∀ v, X.Ω v) → ℝ := fun ω => F (X.φ ω)
    have hG : ∀ ω, 0 ≤ G ω := fun ω => hF (X.φ ω)
    have hGdep : FinProb.DependsOn G U := by
      intro ω ω' hω
      apply hdep
      intro b hb
      exact X.local_label b ω ω'
        (hω (X.var b) (Finset.mem_image.mpr ⟨b, hb, rfl⟩))
    have hUcard : (U.card : ℝ) ≤ n ^ 2 := by
      calc
        _ ≤ (S.card : ℝ) := by exact_mod_cast Finset.card_image_le
        _ ≤ n ^ 2 := hcard
    have hUbudget : (U.card : ℝ) ≤ n ^ 3 := by
      calc
        _ ≤ n ^ 2 := hUcard
        _ ≤ n ^ 3 := by
          calc
            n ^ 2 = n ^ 2 * 1 := by ring
            _ ≤ n ^ 2 * n := mul_le_mul_of_nonneg_left hn1 (by positivity)
            _ = n ^ 3 := by ring
    have hcomp := hLcomp G hG U hGdep hUbudget
    have hfactor : 1 + 1 / n ≤ 2 := by
      have hrecip : 1 / n ≤ 1 := (div_le_iff₀ hnPos).2 (by linarith)
      linarith
    calc
      L.E F = Lraw.E G := by
        rw [Lane_q_s15_c3.finLaw_map_E]
      _ ≤ (1 + 1 / n) * Q.E G := hcomp
      _ = (1 + 1 / n) * (FinLaw.map Q X.φ).E F := by
        rw [Lane_q_s15_c3.finLaw_map_E]
      _ ≤ 2 * (FinLaw.map Q X.φ).E F := by
        have hnonneg : 0 ≤ (FinLaw.map Q X.φ).E F := by
          unfold FinLaw.E
          exact Finset.sum_nonneg fun I _ => mul_nonneg
            ((FinLaw.map Q X.φ).nonneg I) (hF I)
        exact mul_le_mul_of_nonneg_right hfactor hnonneg

/-- High-small-bin mode: the product pre-law followed by mass conditioning. -/
theorem label_output_small (κ : CConsts) (hκ : κ.Admissible) (T : Stage) :
    ∀ᶠ k in atTop, ∀ PT : ProfiledTiling κ T k, ∀ hPT : PT.Valid,
    ∀ hm : PT.tiling.mode = .highSmall ∨ PT.tiling.mode = .highLarge,
    PT.tiling.mode = .highSmall →
    ∀ W : ClusterHistory PT hPT hm, 0 < (clusterHistoryLaw PT hPT hm).w W →
      clusterAlarmsAvoided PT hPT hm W → clusterHistoryLoad PT hPT hm W →
    ∀ B : ClusterBinAssignment PT, 0 < (clusterIndependentBinKernel PT hPT hm W).w B →
      clusterBinGood PT hPT hm W B →
      (∀ a, (clusterIndependentLabelKernel PT hPT hm W B).pr
        (fun I => clusterRowMass PT hPT hm W I a < 1 / 2) ≤ (T.S.n k : ℝ) ^ (-(κ.R : ℝ) / 2)) →
      Nonempty (LabelLawOutput PT hPT hm W B) := by
  filter_upwards [label_prelaw_small κ hκ T, label_condition_small κ hκ T] with k hPre hCond
  intro PT hPT hm hs W hraw havoid hload B hB hgood hmass
  obtain ⟨X⟩ := hPre PT hPT hm hs W hraw havoid hload B hB hgood
  obtain ⟨L, hsupp, hmassL, hcomp⟩ := hCond PT hPT hm hs W hraw havoid hload B hB hgood hmass X
  refine ⟨{
    preLaw := FinLaw.map (FinLaw.pi X.Q) X.φ
    law := L
    pins := ?_
    singleton := X.singleton
    preComparison := X.preComparison
    comparison := hcomp
    supported := ?_
    injective := ?_
    mass := hmassL }⟩
  · intro I hI
    obtain ⟨ω, _, rfl⟩ := hsupp I hI
    exact X.pins ω
  · intro I hI b
    obtain ⟨ω, hω, rfl⟩ := hsupp I hI
    exact X.supported ω hω b
  · intro I hI
    obtain ⟨ω, hω, rfl⟩ := hsupp I hI
    exact X.injective ω hω

/-- In high-large-bin mode the pre-label law is the independent label kernel itself. -/
theorem label_output_large (κ : CConsts) (hκ : κ.Admissible) (T : Stage) :
    ∀ᶠ k in atTop, ∀ PT : ProfiledTiling κ T k, ∀ hPT : PT.Valid,
    ∀ hm : PT.tiling.mode = .highSmall ∨ PT.tiling.mode = .highLarge,
    PT.tiling.mode = .highLarge →
    ∀ W : ClusterHistory PT hPT hm, 0 < (clusterHistoryLaw PT hPT hm).w W →
      clusterAlarmsAvoided PT hPT hm W → clusterHistoryLoad PT hPT hm W →
    ∀ B : ClusterBinAssignment PT, 0 < (clusterIndependentBinKernel PT hPT hm W).w B →
      clusterBinGood PT hPT hm W B →
      (∀ a, (clusterIndependentLabelKernel PT hPT hm W B).pr
        (fun I => clusterRowMass PT hPT hm W I a < 1 / 2) ≤ (T.S.n k : ℝ) ^ (-(κ.R : ℝ) / 2)) →
      Nonempty (LabelLawOutput PT hPT hm W B) := by
  filter_upwards [label_clock_large κ hκ T] with k hClock
  intro PT hPT hm hl W hraw havoid hload B hB hgood hmass
  obtain ⟨L, hpins, hsupp, hinj, hmassL, hcomp⟩ :=
    hClock PT hPT hm hl W hraw havoid hload B hB hgood hmass
  have hns : PT.tiling.mode ≠ .highSmall := by rw [hl]; simp
  refine ⟨{
    preLaw := clusterIndependentLabelKernel PT hPT hm W B
    law := L
    pins := hpins
    singleton := independent_label_singleton_U PT hPT hm W B
    preComparison := ?_
    comparison := hcomp
    supported := hsupp
    injective := hinj
    mass := hmassL }⟩
  intro F hF S hdep hcard hquery
  have herr : clusterLabelError PT hPT hm B S = 1 := by
    unfold clusterLabelError
    rw [if_neg hns]
  rw [herr, one_mul]

/-- The label stage at a fixed loaded history and successful bin choice, eventually in `k`. -/
theorem label_local_output (κ : CConsts) (hκ : κ.Admissible) (T : Stage) :
    ∀ᶠ k in atTop, ∀ PT : ProfiledTiling κ T k, ∀ hPT : PT.Valid,
    ∀ hm : PT.tiling.mode = .highSmall ∨ PT.tiling.mode = .highLarge,
    ∀ W : ClusterHistory PT hPT hm, 0 < (clusterHistoryLaw PT hPT hm).w W →
      clusterAlarmsAvoided PT hPT hm W → clusterHistoryLoad PT hPT hm W →
    ∀ B : ClusterBinAssignment PT, 0 < (clusterIndependentBinKernel PT hPT hm W).w B →
      clusterBinGood PT hPT hm W B →
      (∀ a, (clusterIndependentLabelKernel PT hPT hm W B).pr
        (fun I => clusterRowMass PT hPT hm W I a < 1 / 2) ≤ (T.S.n k : ℝ) ^ (-(κ.R : ℝ) / 2)) →
      Nonempty (LabelLawOutput PT hPT hm W B) := by
  filter_upwards [label_output_small κ hκ T, label_output_large κ hκ T] with k hSmall hLarge
  intro PT hPT hm
  by_cases hs : PT.tiling.mode = .highSmall
  · exact hSmall PT hPT hm hs
  · exact hLarge PT hPT hm (hm.resolve_left hs)

end HypercubeRamsey.S15.Lane_opus_s15
