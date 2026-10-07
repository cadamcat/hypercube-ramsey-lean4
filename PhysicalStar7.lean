import HypercubeRamsey.S16.Producers
namespace HypercubeRamsey.S16.Lane_sol_fix2_s16
open Classical
open scoped BigOperators
private theorem cell_finLaw_ext7 {A : Type*} [Fintype A] (P Q : FinLaw A)
    (hw : ∀ a, P.w a = Q.w a) : P = Q := by
  cases P
  cases Q
  congr 1
  exact funext hw

private theorem flip_neighbors_injective7 {n : ℕ} (z : CubePos n) :
    Function.Injective (flipPos z) := by
  intro j l h
  by_contra hjl
  have he := congrFun h j
  simp [flipPos, hjl] at he

private theorem cluster_failure_dictionary7 {κ : CConsts} {T : Stage} {k : ℕ}
    {PT : ProfiledTiling κ T k} {G : LowGeom PT} (R : CellRawData G)
    (Perm : CellPermissions R) (K : CellRestrictedKernels R Perm)
    (hc : PT.tiling.mode.isCluster) (C : G.Cell) (W : R.Hist C)
    (S : SliceSolver κ PT.tiling (G.cellPatch C) PT.mesh) (Z : ∀ r, S.Val r)
    (groups : (R.Slice C × HypercubeRamsey.Group PT.tiling (G.cellPatch C)) ≃ R.Group C)
    (s : R.Slice C) (w : EvenRole PT.tiling (G.cellPatch C))
    (hGroup : ∀ z (hz : ¬ IsEvenRole (R.cellWords C (s, z)).1),
      R.groupOf C ⟨(R.cellWords C (s, z)).1, (R.cellWords C (s, z)).2, hz⟩ =
        groups (s, S.groupOf z))
    (hU : ∀ g D y, (R.U C W (groups (s, g)) D).w y = S.U g Z D y)
    (hPrior : ∀ ys fallback,
      R.rawPrior C W ys (R.cellWords C (s, w.1)).1 =
        S.σ w Z (nbrLabels w.1 (R.wordLabel C ys s fallback)))
    (a : R.Group C → Bin PT.tiling (G.cellPatch C)) :
    K.failure C W
      ⟨(R.cellWords C (s, w.1)).1, (R.cellWords C (s, w.1)).2,
        (R.word_parity hc C s w.1).mpr w.2⟩ a =
      Lane_sol_s16_prod1.solver_star_bin_failure S Z w (fun g => a (groups (s, g))) := by
  classical
  let fallback : Fin (T.S.N k) := ⟨0, T.S.N_pos k⟩
  have hodd : ∀ j : Fin (PT.tiling.P (G.cellPatch C)).h,
      ¬ IsEvenRole (R.cellWords C (s, flipPos w.1 j)).1 := by
    intro j
    rw [R.word_parity hc, Lane_sol_s16_prod1.flip_parity]
    exact not_not.mpr w.2
  let neighbor : Fin (PT.tiling.P (G.cellPatch C)).h → OddCellRole G C := fun j =>
    ⟨(R.cellWords C (s, flipPos w.1 j)).1, (R.cellWords C (s, flipPos w.1 j)).2, hodd j⟩
  have hi : Function.Injective neighbor := by
    intro j l heq
    have hw : R.cellWords C (s, flipPos w.1 j) = R.cellWords C (s, flipPos w.1 l) :=
      Subtype.ext (congrArg (fun r : OddCellRole G C => r.1) heq)
    exact flip_neighbors_injective7 w.1 (congrArg Prod.snd ((R.cellWords C).injective hw))
  have hlabels (ys : OddCellRole G C → Fin (T.S.N k)) :
      nbrLabels w.1 (R.wordLabel C ys s fallback) = fun j => ys (neighbor j) := by
    funext j
    simp only [nbrLabels, CellRawData.wordLabel, dif_pos (hodd j), neighbor]
  have hprior (ys : OddCellRole G C → Fin (T.S.N k)) :
      R.rawPrior C W ys (R.cellWords C (s, w.1)).1 = S.σ w Z (fun j => ys (neighbor j)) := by
    rw [hPrior ys fallback, hlabels]
  let P := fun r : OddCellRole G C => R.U C W (R.groupOf C r) (a (R.groupOf C r))
  let Q := fun z : IWord PT.tiling (G.cellPatch C) =>
    (⟨S.U (S.groupOf z) Z (a (groups (s, S.groupOf z))),
      S.U_nonneg _ _ _, S.U_sum _ _ _⟩ : FinLaw (Fin (T.S.N k)))
  have hrows : (fun j => P (neighbor j)) = (fun j => Q (flipPos w.1 j)) := by
    funext j
    dsimp only [P, neighbor]
    rw [hGroup (flipPos w.1 j) (hodd j)]
    apply cell_finLaw_ext7
    intro y
    exact hU _ _ y
  change (if PT.tiling.mode.isCluster then (FinLaw.pi P).pr
    (fun ys => R.rawPrior C W ys (R.cellWords C (s, w.1)).1 = 0) else 0) = _
  rw [if_pos hc]
  simp_rw [hprior]
  rw [Lane_sol_s16_prod1.pr_eq_indicator_E]
  let F : InternalLabels PT.tiling (G.cellPatch C) → ℝ :=
    fun zs => @ite ℝ (S.σ w Z zs = 0) (Classical.propDecidable _) 1 0
  have hleft := Lane_sol_s16_prod1.pi_injective_coordinate_E P neighbor hi
    F
  have hright := Lane_sol_s16_prod1.pi_injective_coordinate_E Q (flipPos w.1)
    (flip_neighbors_injective7 w.1) F
  rw [hrows] at hleft
  unfold Lane_sol_s16_prod1.solver_star_bin_failure
  rw [Lane_sol_s16_prod1.pr_eq_indicator_E]
  change (FinLaw.pi P).E (fun ys => F (fun j => ys (neighbor j))) =
    (FinLaw.pi Q).E (fun ys => F (fun j => ys (flipPos w.1 j)))
  exact hleft.trans hright.symm

private theorem physical_pretrim_mass7 {κ : CConsts} {T : Stage} {k : ℕ}
    {PT : ProfiledTiling κ T k} {G : LowGeom PT} (R : CellRawData G)
    (hR : R.SourceValid) (hc : PT.tiling.mode.isCluster)
    (C : G.Cell) (W : R.Hist C) (hW : (R.history C).w W ≠ 0) (g : R.Group C) :
    1 - ((PT.tiling.P (G.cellPatch C)).h : ℝ) ^ 2 *
      Real.sqrt (sliceEps κ (PT.tiling.P (G.cellPatch C)).h) ≤
      ∑ b ∈ R.pretrim C W g, (R.qraw C W g).w b := by
  classical
  rcases hR with ⟨hm, hu, hSource⟩ | ⟨hd, _⟩
  · obtain ⟨S, hS, records, groups, hLaw, hPass, hGroup, hQ, hTrim, hU, hPrior⟩ := hSource C
    obtain ⟨⟨s, g'⟩, hsg⟩ := groups.surjective g
    rw [← hsg, hTrim]
    simp_rw [hQ]
    have hp := Lane_sol_s16_prod1.cond_support _ _ _ _
      (Lane_sol_s16_prod1.pi_support _ W hW s)
    exact Lane_sol_s16_prod1.solver_pretrim_mass S _ ((hPass s _).mp hp.1) g' (Real.exp_pos _)
  · exact (hd hc).elim

private theorem physical_qbar_raw_domination7 {κ : CConsts} {T : Stage} {k : ℕ}
    {PT : ProfiledTiling κ T k} {G : LowGeom PT} (R : CellRawData G)
    (Perm : CellPermissions R) (K : CellRestrictedKernels R Perm)
    (C : G.Cell) (W : R.Hist C) (hW : (R.history C).w W ≠ 0)
    (u v : ℝ) (hu : u < 1) (hv : v < 1)
    (hPre : ∀ g, 1 - u ≤ ∑ b ∈ R.pretrim C W g, (R.qraw C W g).w b)
    (hPerm : ∀ g, 1 - v ≤ ∑ b ∈ (Perm.table C).permitted g, (R.qin C W g).w b)
    (g : R.Group C) (b : Bin PT.tiling (G.cellPatch C)) :
    (K.qbar C W g).w b ≤ ((1 - u) * (1 - v))⁻¹ * (R.qraw C W g).w b := by
  classical
  have hSlices : ∀ s, W s ∈ R.slicePass C s ∧ (R.sliceLaw C s).w (W s) ≠ 0 := by
    intro s
    exact Lane_sol_s16_prod1.cond_support _ _ _ _ (Lane_sol_s16_prod1.pi_support _ W hW s)
  have hp : 0 < 1 - u := by linarith
  have hvp : 0 < 1 - v := by linarith
  have hprePos := lt_of_lt_of_le hp (hPre g)
  have hpermPos := lt_of_lt_of_le hvp (hPerm g)
  have hqin : (R.qin C W g).w b ≤ (R.qraw C W g).w b / (1 - u) := by
    rw [R.qin_eq C W g b hSlices]
    calc
      _ ≤ (R.qraw C W g).w b / (∑ b ∈ R.pretrim C W g, (R.qraw C W g).w b) := by
        apply div_le_div_of_nonneg_right _ hprePos.le
        split_ifs
        · exact le_rfl
        · exact (R.qraw C W g).nonneg b
      _ ≤ _ := div_le_div_of_nonneg_left ((R.qraw C W g).nonneg b) hp (hPre g)
  rw [K.qbar_eq C W g b hW]
  calc
    _ ≤ (R.qin C W g).w b / (∑ b ∈ (Perm.table C).permitted g, (R.qin C W g).w b) := by
      apply div_le_div_of_nonneg_right _ hpermPos.le
      split_ifs
      · exact le_rfl
      · exact (R.qin C W g).nonneg b
    _ ≤ (R.qin C W g).w b / (1 - v) :=
      div_le_div_of_nonneg_left ((R.qin C W g).nonneg b) hvp (hPerm g)
    _ ≤ ((R.qraw C W g).w b / (1 - u)) / (1 - v) :=
      div_le_div_of_nonneg_right hqin hvp.le
    _ = _ := by simp only [mul_inv, div_eq_mul_inv]; ring

private theorem cluster_star_normalization_setup7 {κ : CConsts} (hκ : κ.Admissible) :
    ∃ n₀ : ℕ, ∀ {T : Stage} {k : ℕ} {PT : ProfiledTiling κ T k} {K16 : ℝ}
      (Q : LowModeQuantFacts hκ (PT := PT) K16) (i : Fin PT.tiling.m),
      PT.tiling.mode.isCluster → n₀ ≤ T.S.n k →
      let u := ((PT.tiling.P i).h : ℝ) ^ 2 * Real.sqrt (sliceEps κ (PT.tiling.P i).h)
      let v := Real.exp (-κ.cperm * T.S.n k / 2)
      u < 1 ∧ v < 1 ∧ 1 ≤ ((1 - u) * (1 - v))⁻¹ ∧
        ∀ m : ℕ, m ≤ (PT.tiling.P i).h → (((1 - u) * (1 - v))⁻¹) ^ m ≤ 2 := by
  obtain ⟨n₀, hroom⟩ := Lane_sol_s16_prod1.cluster_permission_cost_room hκ
  refine ⟨n₀, ?_⟩
  intro T k PT K16 Q i hc hn u v
  have hm : PT.tiling.mode = .lowCluster := by
    have hLow := Q.mode_low
    cases hm : PT.tiling.mode <;> simp_all [Mode.isCluster, Mode.isLow]
  have hhp : 0 < (PT.tiling.P i).h := by
    have hdy := (Q.profiled_valid.tiling_valid.cluster_data (Or.inl hm) i).2.2.2.2.2.2.1
    rw [hdy]
    positivity
  have hh1 : (1 : ℝ) ≤ (PT.tiling.P i).h := by exact_mod_cast hhp
  have hhN : (PT.tiling.P i).h ≤ T.S.n k := by
    have hle := Finset.le_sup (f := fun j : Fin PT.tiling.m => (PT.tiling.P j).h) (Finset.mem_univ i)
    have hh := Q.profiled_valid.tiling_valid.prefix_internal_length
    omega
  have hu : u < 1 := lt_of_le_of_lt
    (Lane_sol_s16_prod1.low_cluster_pretrim_small hκ Q hm i) (by norm_num)
  have hvRoom := hroom (T.S.n k) (PT.tiling.P i).h hn Q.n_large hhN
  have hv0 : 0 ≤ v := (Real.exp_pos _).le
  have hv : v < 1 := by
    have hx := le_mul_of_one_le_left hv0 hh1
    change v ≤ ((PT.tiling.P i).h : ℝ) * v at hx
    exact lt_of_le_of_lt (hx.trans hvRoom) (by norm_num)
  have huRoom := Lane_sol_s16_prod1.low_cluster_pretrim_power_small hκ Q hm i 3 (by norm_num)
  have huRoom' : ((PT.tiling.P i).h : ℝ) * u ≤ 1 / 1000 := by
    convert huRoom using 1 <;> norm_num [Real.rpow_neg, Real.rpow_natCast] <;> ring
  have hsmall : ((PT.tiling.P i).h : ℝ) * (u + v) ≤ 1 / 2 := by linarith only [huRoom', hvRoom]
  have hu0 : 0 ≤ u := by dsimp [u]; positivity
  refine ⟨hu, hv, ?_, ?_⟩
  · exact (Lane_sol_s16_prod1.normalization_product_room (PT.tiling.P i).h 0 u v hu0 hv0 hu hv
      (Nat.zero_le _) hsmall).1
  · intro m hm'
    exact (Lane_sol_s16_prod1.normalization_product_room (PT.tiling.P i).h m u v hu0 hv0 hu hv hm' hsmall).2

private theorem cluster_star_mean_setup7 {κ : CConsts} (hκ : κ.Admissible) :
    ∃ n₀ : ℕ, ∀ {T : Stage} {k : ℕ} {PT : ProfiledTiling κ T k} {K16 : ℝ}
      (Q : LowModeQuantFacts hκ (PT := PT) K16) {G : LowGeom PT}
      (R : CellRawData G) (Perm : CellPermissions R) (K : CellRestrictedKernels R Perm),
      R.SourceValid → PT.tiling.mode.isCluster → n₀ ≤ T.S.n k →
      ∀ C W, (R.history C).w W ≠ 0 →
      PermissionLossHypotheses (Perm.table C) (R.qin C W) →
      ∀ v : EvenCellRole G C,
        (FinLaw.pi (K.qbar C W)).E (K.failure C W v) ≤
          2 * sliceEps κ (PT.tiling.P (G.cellPatch C)).h ∧
        ∀ g b, (K.qbar C W g).w b ≠ 0 →
          (FinLaw.pi (Lane_sol_s16_prod1.coordinatePin (K.qbar C W) g b)).E (K.failure C W v) ≤
            2 * Real.sqrt (sliceEps κ (PT.tiling.P (G.cellPatch C)).h) := by
  classical
  obtain ⟨n₀, hRoom⟩ := cluster_star_normalization_setup7 hκ
  refine ⟨n₀, ?_⟩
  intro T k PT K16 Q G R Perm K hR hc hn C W hW hPerm v
  rcases hR with ⟨hMode, hUniform, hSource⟩ | ⟨hDirect, _⟩
  · obtain ⟨S, hS, records, groups, hLaw, hPass, hGroup, hQ, hTrim, hU, hPrior⟩ := hSource C
    let u := ((PT.tiling.P (G.cellPatch C)).h : ℝ) ^ 2 *
      Real.sqrt (sliceEps κ (PT.tiling.P (G.cellPatch C)).h)
    let δ := Real.exp (-κ.cperm * T.S.n k / 2)
    let c := ((1 - u) * (1 - δ))⁻¹
    obtain ⟨hu, hδ, hc1, hcost⟩ := hRoom Q (G.cellPatch C) hc hn
    have hPre : ∀ g, 1 - u ≤ ∑ b ∈ R.pretrim C W g, (R.qraw C W g).w b :=
      fun g => physical_pretrim_mass7 R (Or.inl ⟨hMode, hUniform, hSource⟩) hc C W hW g
    have hPermMass : ∀ g, 1 - δ ≤ ∑ b ∈ (Perm.table C).permitted g, (R.qin C W g).w b := by
      intro g
      have hh := Lane_sol_s16_prod1.permission_retained_sharp (Perm.table C) (R.qin C W) hPerm g
      simpa only [Perm.rate_eq, Perm.n_eq] using hh
    have hdom : ∀ g b, (K.qbar C W g).w b ≤ c * (R.qraw C W g).w b :=
      fun g b => physical_qbar_raw_domination7 R Perm K C W hW u δ hu hδ hPre hPermMass g b
    let sz := (R.cellWords C).symm ⟨v.1, v.2.1⟩
    have hv : (R.cellWords C (sz.1, sz.2)).1 = v.1 :=
      congrArg Subtype.val ((R.cellWords C).apply_symm_apply ⟨v.1, v.2.1⟩)
    have he : IsEvenRole sz.2 := (R.word_parity hc C sz.1 sz.2).mp (by rw [hv]; exact v.2.2)
    let w : EvenRole PT.tiling (G.cellPatch C) := ⟨sz.2, he⟩
    let v' : EvenCellRole G C := ⟨(R.cellWords C (sz.1, w.1)).1,
      (R.cellWords C (sz.1, w.1)).2, (R.word_parity hc C sz.1 w.1).mpr w.2⟩
    have hv' : v' = v := Subtype.ext hv
    let P := fun g => K.qbar C W (groups (sz.1, g))
    have hFailure : ∀ a, K.failure C W v a =
        Lane_sol_s16_prod1.solver_star_bin_failure S (records sz.1 (W sz.1)) w
          (fun g => a (groups (sz.1, g))) := by
      intro a
      have hh := cluster_failure_dictionary7 R Perm K hc C W S (records sz.1 (W sz.1)) groups sz.1 w
        (hGroup sz.1) (hU W sz.1) (hPrior W sz.1 w) a
      change K.failure C W v' a = _ at hh
      simpa only [hv'] using hh
    have hinj : Function.Injective (fun g => groups (sz.1, g)) := by
      intro g g' hh
      exact congrArg Prod.snd (groups.injective hh)
    have hMeanEq : (FinLaw.pi (K.qbar C W)).E (K.failure C W v) =
        (FinLaw.pi P).E (Lane_sol_s16_prod1.solver_star_bin_failure S (records sz.1 (W sz.1)) w) := by
      have hh := Lane_sol_s16_prod1.pi_injective_coordinate_E (K.qbar C W) (fun g => groups (sz.1, g)) hinj
        (Lane_sol_s16_prod1.solver_star_bin_failure S (records sz.1 (W sz.1)) w)
      simpa only [P, ← hFailure] using hh
    have hgood : S.AllGood (records sz.1 (W sz.1)) := by
      have hp := Lane_sol_s16_prod1.cond_support _ _ _ _
        (Lane_sol_s16_prod1.pi_support _ W hW sz.1)
      exact (hPass sz.1 _).mp hp.1
    have hRow : ∀ g ∈ Lane_sol_s16_prod1.solver_star_group_scope S w, ∀ b,
        (P g).w b ≤ c * S.q g (records sz.1 (W sz.1)) b := by
      intro g _ b
      simpa only [P, hQ] using hdom (groups (sz.1, g)) b
    have hmean := Lane_sol_s16_prod1.solver_star_trimmed_mean S (records sz.1 (W sz.1)) w
      (hgood w) P c (le_trans (by norm_num) hc1) hRow
    have hcost2 := hcost _ (Lane_sol_s16_prod1.solver_star_group_scope_count S w)
    have hOrdinary : (FinLaw.pi (K.qbar C W)).E (K.failure C W v) ≤
        2 * sliceEps κ (PT.tiling.P (G.cellPatch C)).h := by
      rw [hMeanEq]
      exact hmean.trans (mul_le_mul_of_nonneg_right hcost2 (Real.exp_pos _).le)
    refine ⟨hOrdinary, ?_⟩
    intro g b hb
    letI := hPerm.bins_nonempty
    have hEps : 0 < sliceEps κ (PT.tiling.P (G.cellPatch C)).h ∧
        sliceEps κ (PT.tiling.P (G.cellPatch C)).h ≤ 1 := by
      refine ⟨Real.exp_pos _, Real.exp_le_one_iff.mpr ?_⟩
      have ha : 0 < κ.a := by rw [hκ.a_eq]; exact div_pos hκ.θ_rng.1 (by norm_num)
      have hh : (0 : ℝ) ≤ (PT.tiling.P (G.cellPatch C)).h := Nat.cast_nonneg _
      have hk : (0 : ℝ) ≤ sliceK κ (PT.tiling.P (G.cellPatch C)).h := Nat.cast_nonneg _
      nlinarith [mul_nonneg (mul_nonneg ha.le hk) hh]
    have hRoot : sliceEps κ (PT.tiling.P (G.cellPatch C)).h ≤
        Real.sqrt (sliceEps κ (PT.tiling.P (G.cellPatch C)).h) := by
      apply (Real.le_sqrt hEps.1.le hEps.1.le).mpr
      nlinarith [sq_nonneg (sliceEps κ (PT.tiling.P (G.cellPatch C)).h)]
    obtain ⟨⟨s', g'⟩, hsg⟩ := groups.surjective g
    have hPinMeanEq :
        (FinLaw.pi (Lane_sol_s16_prod1.coordinatePin (K.qbar C W) g b)).E (K.failure C W v) =
        (FinLaw.pi (fun j => (Lane_sol_s16_prod1.coordinatePin (K.qbar C W) g b) (groups (sz.1, j)))).E
          (Lane_sol_s16_prod1.solver_star_bin_failure S (records sz.1 (W sz.1)) w) := by
      have hh := Lane_sol_s16_prod1.pi_injective_coordinate_E
        (Lane_sol_s16_prod1.coordinatePin (K.qbar C W) g b) (fun j => groups (sz.1, j)) hinj
        (Lane_sol_s16_prod1.solver_star_bin_failure S (records sz.1 (W sz.1)) w)
      simpa only [← hFailure] using hh
    rw [hPinMeanEq]
    by_cases hs : s' = sz.1
    · subst s'
      have hRows : (fun j => (Lane_sol_s16_prod1.coordinatePin (K.qbar C W) g b) (groups (sz.1, j))) =
          Lane_sol_s16_prod1.coordinatePin P g' b := by
        funext j
        by_cases hj : j = g'
        · subst j
          simp only [← hsg, Lane_sol_s16_prod1.coordinatePin, if_pos rfl]
        · have hneq : groups (sz.1, j) ≠ g := by
            intro heq
            have hh := groups.injective (heq.trans hsg.symm)
            exact hj (congrArg Prod.snd hh)
          simp only [Lane_sol_s16_prod1.coordinatePin, if_neg hneq, if_neg hj, P]
      rw [hRows]
      have hD : b ∈ S.pretrimBins (records sz.1 (W sz.1)) g' := by
        by_contra hNot
        have hSlices : ∀ t, W t ∈ R.slicePass C t ∧ (R.sliceLaw C t).w (W t) ≠ 0 := by
          intro t
          exact Lane_sol_s16_prod1.cond_support _ _ _ _ (Lane_sol_s16_prod1.pi_support _ W hW t)
        have hQinZero : (R.qin C W g).w b = 0 := by
          rw [← hsg, R.qin_eq C W _ b hSlices, hTrim W sz.1 g']
          simp only [if_neg hNot, zero_div]
        apply hb
        rw [K.qbar_eq C W g b hW, hQinZero]
        simp
      have hh := Lane_sol_s16_prod1.solver_star_trimmed_any_pin_mean S (records sz.1 (W sz.1)) w
        (hgood w) hEps P c hc1 hRow g' b hD
      exact hh.trans (mul_le_mul_of_nonneg_right hcost2 (Real.sqrt_nonneg _))
    · have hRows : (fun j => (Lane_sol_s16_prod1.coordinatePin (K.qbar C W) g b) (groups (sz.1, j))) = P := by
        funext j
        have hneq : groups (sz.1, j) ≠ g := by
          intro heq
          have hh := groups.injective (heq.trans hsg.symm)
          exact hs (congrArg Prod.fst hh).symm
        simp only [Lane_sol_s16_prod1.coordinatePin, if_neg hneq, P]
      rw [hRows]
      exact hmean.trans ((mul_le_mul_of_nonneg_right hcost2 hEps.1.le).trans
        (mul_le_mul_of_nonneg_left hRoot (by norm_num)))
  · exact (hDirect hc).elim

end HypercubeRamsey.S16.Lane_sol_fix2_s16


