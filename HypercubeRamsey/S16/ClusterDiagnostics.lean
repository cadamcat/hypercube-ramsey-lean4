import HypercubeRamsey.S16.ProducersDefs

/-! Cluster diagnostics proof nodes from the S16 pool diagnosis. -/

namespace HypercubeRamsey.S16.ClusterDiagnostics

open Classical
open scoped BigOperators
open Lane_sol_fix2_s16

/-- Fill the coordinates outside a finite scope from a fixed base point. -/
noncomputable def fillScope {J Bin : Type*} (I : Finset J) (base : J → Bin) (a : I → Bin) : J → Bin :=
  fun g => if h : g ∈ I then a ⟨g, h⟩ else base g

/-- Slot-expanded empirical integral of `f` over the scope `I`, with weights
`B * P j`; the coordinates outside `I` are frozen at `base`. -/
noncomputable def scopedEmpirical {J Slot Bin : Type*} [DecidableEq J]
    [Fintype Slot] [DecidableEq Slot] [Nonempty Slot] [Fintype Bin]
    (I : Finset J) (P : J → FinLaw Bin) (base : J → Bin) (f : (J → Bin) → ℝ)
    (pool : Slot → Bin) : ℝ :=
  Lane_sol_s16_prod1.empirical_statistic
    (Lane_sol_s16_prod1.empirical_weighted_kernel (fun j : I => P j.1) (Fintype.card Bin)
      (fun a => f (fillScope I base a))) pool

/-- C1. One-slot sensitivity (from `empirical_statistic_one_slot`).
TeX 16:235–249; estimated proof: 40 lines. -/
theorem scopedEmpirical_one_slot {J Slot Bin : Type*} [DecidableEq J]
    [Fintype Slot] [DecidableEq Slot] [Nonempty Slot] [Fintype Bin] [Nonempty Bin]
    (I : Finset J) (P : J → FinLaw Bin) (base : J → Bin) (f : (J → Bin) → ℝ)
    (hf : ∀ a, 0 ≤ f a ∧ f a ≤ 1) (A : ℝ) (hA : 1 ≤ A)
    (hcap : ∀ j b, (P j).w b ≤ A / Fintype.card Bin)
    (s : Slot) (x y : Slot → Bin) (hxy : ∀ t, t ≠ s → x t = y t) :
    |scopedEmpirical I P base f x - scopedEmpirical I P base f y| ≤
      (I.card : ℝ) * A ^ I.card / Fintype.card Slot := by
  sorry

/-- C2. Mean under iid uniform slots (from `empirical_statistic_mean`,
`empirical_weighted_kernel_range` and `empirical_weighted_kernel_integral`).
TeX 16:235–249; estimated proof: 50 lines. -/
theorem scopedEmpirical_mean {J Slot Bin : Type*} [DecidableEq J]
    [Fintype Slot] [DecidableEq Slot] [Nonempty Slot] [Fintype Bin] [DecidableEq Bin]
    [Nonempty Bin]
    (I : Finset J) (P : J → FinLaw Bin) (base : J → Bin) (f : (J → Bin) → ℝ)
    (hf : ∀ a, 0 ≤ f a ∧ f a ≤ 1) (A : ℝ) (hA : 1 ≤ A)
    (hcap : ∀ j b, (P j).w b ≤ A / Fintype.card Bin) :
    (FinLaw.pi (fun _ : Slot => FinLaw.uniform (Finset.univ : Finset Bin) Finset.univ_nonempty)).E
        (scopedEmpirical I P base f) ≤
      (FinLaw.pi (fun j : I => P j.1)).E (fun a => f (fillScope I base a)) +
        A ^ I.card * ((I.card : ℝ) ^ 2 / Fintype.card Slot) := by
  sorry

/-- C3. The pool-restricted integral is bounded by the slot expansion, on
every pool (repeated images only enlarge the right side).
TeX 16:235–249; estimated proof: 150 lines. -/
theorem scopedEmpirical_restricted {J Slot Bin : Type*} [DecidableEq J]
    [Fintype Slot] [DecidableEq Slot] [Nonempty Slot] [Fintype Bin] [DecidableEq Bin]
    (I : Finset J) (Q P : J → FinLaw Bin) (base : J → Bin) (f : (J → Bin) → ℝ)
    (hf : ∀ a, 0 ≤ f a) (pool : Slot → Bin)
    (hmass : ∀ j ∈ I, 0 < ∑ b ∈ Finset.univ.image pool, (Q j).w b)
    (hP : ∀ j ∈ I, ∀ b, (P j).w b =
      (if b ∈ Finset.univ.image pool then (Q j).w b else 0) /
        ∑ b' ∈ Finset.univ.image pool, (Q j).w b') :
    (FinLaw.pi (fun j : I => P j.1)).E (fun a => f (fillScope I base a)) *
        ∏ j ∈ I, ((Fintype.card Bin : ℝ) / Fintype.card Slot *
          ∑ b ∈ Finset.univ.image pool, (Q j).w b) ≤
      scopedEmpirical I Q base f pool := by
  sorry

/-- C4a. Marginalisation of a scope-local integrand.
TeX 16:235–245; estimated proof: 40 lines. -/
theorem pi_E_scope {J Bin : Type*} [Fintype J] [DecidableEq J] [Fintype Bin] [Nonempty Bin]
    (R : J → FinLaw Bin) (I : Finset J) (base : J → Bin) (f : (J → Bin) → ℝ)
    (hf : ∀ x y, (∀ g ∈ I, x g = y g) → f x = f y) :
    (FinLaw.pi R).E f = (FinLaw.pi (fun j : I => R j.1)).E (fun a => f (fillScope I base a)) := by
  sorry

/-- C4b. The same with one coordinate of the scope pinned.
TeX 16:228–245; estimated proof: 40 lines. -/
theorem pi_E_scope_pin {J Bin : Type*} [Fintype J] [DecidableEq J] [Fintype Bin]
    [DecidableEq Bin] [Nonempty Bin]
    (R : J → FinLaw Bin) (I : Finset J) (g : J) (hg : g ∈ I) (b : Bin)
    (base : J → Bin) (hbase : base g = b) (f : (J → Bin) → ℝ)
    (hf : ∀ x y, (∀ g ∈ I, x g = y g) → f x = f y) :
    (FinLaw.pi (Lane_sol_s16_prod1.coordinatePin R g b)).E f =
      (FinLaw.pi (fun j : (I.erase g) => R j.1)).E
        (fun a => f (fillScope (I.erase g) base a)) := by
  sorry

/-- C4c. A pin outside the scope is invisible.
TeX 16:228–245; estimated proof: 40 lines. -/
theorem pi_E_pin_outside {J Bin : Type*} [Fintype J] [DecidableEq J] [Fintype Bin]
    [DecidableEq Bin] [Nonempty Bin]
    (R : J → FinLaw Bin) (I : Finset J) (g : J) (hg : g ∉ I) (b : Bin)
    (f : (J → Bin) → ℝ) (hf : ∀ x y, (∀ g ∈ I, x g = y g) → f x = f y) :
    (FinLaw.pi (Lane_sol_s16_prod1.coordinatePin R g b)).E f = (FinLaw.pi R).E f := by
  sorry

/-- C4d. Injective reindexing commutes with a coordinate pin.
TeX 16:239–245; estimated proof: 40 lines. -/
theorem pi_coordinatePin_comp {I J O : Type*} [Fintype I] [DecidableEq I]
    [Fintype J] [DecidableEq J] [Fintype O] [DecidableEq O]
    (P : I → FinLaw O) (ι : J → I) (hι : Function.Injective ι) (j : J) (o : O)
    (F : (J → O) → ℝ) :
    (FinLaw.pi (Lane_sol_s16_prod1.coordinatePin P (ι j) o)).E (fun a => F (fun j' => a (ι j'))) =
      (FinLaw.pi (Lane_sol_s16_prod1.coordinatePin (fun j' => P (ι j')) j o)).E F := by
  sorry

/-- C4e. `GroupBinProblem.pinnedFailure` as a pinned product integral.
TeX 16:228–245; estimated proof: 40 lines. -/
theorem pinned_ratio_eq {I O : Type*} [Fintype I] [DecidableEq I] [Fintype O] [DecidableEq O]
    (P : I → FinLaw O) (i : I) (o : O) (f : (I → O) → ℝ) :
    (FinLaw.pi P).E (fun a => if a i = o then f a else 0) /
        (FinLaw.pi P).pr (fun a => a i = o) =
      if (P i).w o = 0 then 0 else (FinLaw.pi (Lane_sol_s16_prod1.coordinatePin P i o)).E f := by
  sorry

/-- C5. A slot pin moves an expectation by at most the one-slot sensitivity.
TeX 16:247–257; estimated proof: 80 lines. -/
theorem pinLaw_E_close {Slot Bin Hist Check : Type*}
    [Fintype Slot] [DecidableEq Slot] [Fintype Bin] [DecidableEq Bin]
    [Fintype Hist] [Fintype Check] {n : ℕ} {c0 : ℝ}
    (D : CellPoolDiagnostics Slot Bin Hist Check n c0) (Φ : (Slot → Bin) → ℝ)
    (s : Slot) (b : Bin) (δ : ℝ)
    (hΦ : ∀ x y, (∀ t, t ≠ s → x t = y t) → |Φ x - Φ y| ≤ δ) :
    |(D.pinLaw s b).E Φ - D.poolLaw.E Φ| ≤ δ := by
  sorry

/-- C6. Per-check facts assemble the concentration record (mixed families).
TeX 16:247–257; estimated proof: 80 lines. -/
theorem pool_concentration_of_checks {Slot Bin Hist Check : Type*}
    [Fintype Slot] [DecidableEq Slot] [Fintype Bin] [DecidableEq Bin]
    [Fintype Hist] [Fintype Check] {n : ℕ} {c0 : ℝ}
    (D : CellPoolDiagnostics Slot Bin Hist Check n c0)
    (hn : 2 ≤ n) (hc0 : 0 < c0) (hslots : 0 < Fintype.card Slot)
    (heps : 0 < D.ε ∧ D.ε ≤ 1) (htol : ∀ c, 0 < D.tolerance c)
    (sens : Check → ℝ) (hsens : ∀ c, 0 < sens c)
    (hone : ∀ c s x y, (∀ t, t ≠ s → x t = y t) →
      |D.normalizer x c - D.normalizer y c| ≤ sens c)
    (hmean : ∀ c, |D.poolLaw.E (D.normalizer · c) - D.center c| + sens c ≤ D.tolerance c / 2)
    (hvar : ∀ c, (n : ℝ) ^ c0 + Real.log (8 * max 1 (Fintype.card Check : ℝ)) ≤
      2 * (D.tolerance c / 2) ^ 2 / ((Fintype.card Slot : ℝ) * sens c ^ 2))
    (hcollision : (Fintype.card Slot : ℝ) ^ 2 / Fintype.card Bin ≤
      Real.exp (-(n : ℝ) ^ c0) / 4) :
    Nonempty (PoolConcentrationHypotheses D) := by
  sorry

/-- C7. Numerical room for star/pin checks: sensitivity, variance budget, cover.
TeX 16:247–257; estimated proof: 150 lines. -/
theorem cluster_star_budget_room : ∃ n₀ : ℕ, ∀ (n h : ℕ) (L ε Checks : ℝ),
    n₀ ≤ n → 2 ≤ n → h ≤ n → (n : ℝ) ^ (199 : ℕ) ≤ L →
    Real.rpow (n : ℝ) (-1) ≤ ε → ε ≤ 1 / 10 ^ 6 →
    Checks ≤ Real.exp (3 * (n : ℝ) ^ (1.01 : ℝ)) →
    ((h : ℝ) + 1) * n / L ≤ Real.rpow ε (1 / 4 : ℝ) / 8 / 2 ∧
    Real.rpow (n : ℝ) (1 / 2 : ℝ) + Real.log (8 * max 1 Checks) ≤
      2 * (Real.rpow ε (1 / 4 : ℝ) / 8 / 2) ^ 2 / (L * (((h : ℝ) + 1) * n / L) ^ 2) ∧
    2 * Real.sqrt ε + (n : ℝ) * (h : ℝ) ^ 2 / L + Real.rpow ε (1 / 4 : ℝ) / 8 ≤
      (1 - Real.rpow (n : ℝ) (-4)) ^ h * Real.rpow ε (1 / 4 : ℝ) := by
  sorry

/-- C8. `cluster_normalizer_budget_room` with the total check count.
TeX 16:206–219,247–257; estimated proof: 100 lines. -/
theorem cluster_normalizer_budget_room3 : ∃ n₀ : ℕ, ∀ (n : ℕ) (L B Checks : ℝ),
    n₀ ≤ n → 2 ≤ n → 0 < B → (n : ℝ) ^ (199 : ℕ) ≤ L →
    L ^ 2 / B ≤ Real.exp (-Real.rpow (n : ℝ) (1 / 2 : ℝ)) / 4 →
    Checks ≤ Real.exp (3 * (n : ℝ) ^ (1.01 : ℝ)) →
    ((n : ℝ) * L ^ 2 / B + ((n : ℝ) + 1) / L ≤ Real.rpow (n : ℝ) (-4) / 2) ∧
    (Real.rpow (n : ℝ) (1 / 2 : ℝ) + Real.log (8 * max 1 Checks) ≤
      L * Real.rpow (n : ℝ) (-4) ^ 2 / (8 * (n : ℝ) ^ (2 : ℕ))) := by
  sorry

/-! ## Lane B: star/pin physics (Producers.lean, private in the real file). -/

/-- B1 (= run 7's `cluster_failure_dictionary7`).
TeX 16:228–245; estimated proof: 250 lines. -/
theorem cluster_failure_dictionary {κ : CConsts} {T : Stage} {k : ℕ}
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
  sorry

/-- B2. Sharp domination of the restricted rows by the raw solver rows:
pretrim loss `h^2 sqrt eps` and permission loss `exp(-cperm n/2)`, with the
cost over at most `h` groups at most 2 (run 7: `permission_retained_sharp7`,
`normalization_product_room7`, `low_cluster_pretrim_power_small7`,
`cluster_permission_cost_room7`).
TeX 16:228–233; estimated proof: 150 lines. -/
theorem cluster_qbar_domination {κ : CConsts} (hκ : κ.Admissible) :
    ∃ n₀ : ℕ, ∀ {T : Stage} {k : ℕ} {PT : ProfiledTiling κ T k} {K16 : ℝ}
      (Q : LowModeQuantFacts hκ (PT := PT) K16) {G : LowGeom PT}
      (R : CellRawData G) (Perm : CellPermissions R) (K : CellRestrictedKernels R Perm),
      PT.tiling.mode = .lowCluster → n₀ ≤ T.S.n k → ∀ C : G.Cell,
      ∃ c : ℝ, 1 ≤ c ∧ c ^ (PT.tiling.P (G.cellPatch C)).h ≤ 2 ∧
        ∀ (S : SliceSolver κ PT.tiling (G.cellPatch C) PT.mesh)
          (records : ∀ s, R.Value C s ≃ (∀ r, S.Val r))
          (groups : (R.Slice C × HypercubeRamsey.Group PT.tiling (G.cellPatch C)) ≃ R.Group C),
          (∀ s V, V ∈ R.slicePass C s ↔ S.AllGood (records s V)) →
          (∀ W s g D, (R.qraw C W (groups (s, g))).w D = S.q g (records s (W s)) D) →
          (∀ W s g, R.pretrim C W (groups (s, g)) = S.pretrimBins (records s (W s)) g) →
          ∀ W, (R.history C).w W ≠ 0 → PermissionLossHypotheses (Perm.table C) (R.qin C W) →
          ∀ s g D, (K.qbar C W (groups (s, g))).w D ≤ c * S.q g (records s (W s)) D := by
  classical
  obtain ⟨n₁, hpermRoom⟩ := Lane_sol_s16_prod1.cluster_permission_cost_room hκ
  refine ⟨n₁, ?_⟩
  intro T k PT K16 Q G R Perm K hmode hn C
  let n := T.S.n k
  let h := (PT.tiling.P (G.cellPatch C)).h
  let ε := sliceEps κ h
  let u := Real.exp (-κ.cperm * (n : ℝ) / 2)
  let v := (h : ℝ) ^ 2 * Real.sqrt ε
  have hnlarge : 2 ≤ n := Q.n_large
  have hheight : h ≤ n := by
    simpa only [Fintype.card_fin] using
      Fintype.card_le_of_injective (R.axis C) (R.axis_injective C)
  have huNonneg : 0 ≤ u := le_of_lt (Real.exp_pos _)
  have hrate : 0 < κ.cperm * (n : ℝ) / 2 := by
    have hnpos : (0 : ℝ) < n := by exact_mod_cast lt_of_lt_of_le (by norm_num : (0 : ℕ) < 2) hnlarge
    exact div_pos (mul_pos hκ.cperm_rng.1 hnpos) (by norm_num)
  have huLt : u < 1 := by
    exact Real.exp_lt_one_iff.mpr (by nlinarith [hrate])
  have hvNonneg : 0 ≤ v := by
    dsimp [v]
    positivity
  have hsmall2 : v ≤ 1 / 1000 := by
    have hs := Lane_sol_s16_prod1.low_cluster_pretrim_power_small
      hκ Q hmode (G.cellPatch C) 2 (by norm_num)
    norm_num [Real.rpow_neg, Real.rpow_natCast] at hs
    simpa [v, h, ε] using hs
  have hsmall3 : (h : ℝ) ^ 3 * Real.sqrt ε ≤ 1 / 1000 := by
    have hs := Lane_sol_s16_prod1.low_cluster_pretrim_power_small
      hκ Q hmode (G.cellPatch C) 3 (by norm_num)
    norm_num [Real.rpow_neg, Real.rpow_natCast] at hs
    simpa [h, ε] using hs
  have hvLt : v < 1 := by linarith
  have hhu : (h : ℝ) * u ≤ 1 / 4 := by
    exact hpermRoom n h hn hnlarge hheight
  have hsmallSum : (h : ℝ) * (u + v) ≤ 1 / 2 := by
    have hhv : (h : ℝ) * v = (h : ℝ) ^ 3 * Real.sqrt ε := by
      dsimp [v]
      ring
    rw [mul_add, hhv]
    linarith
  have hnorm := Lane_sol_s16_prod1.normalization_product_room h h u v
    huNonneg hvNonneg huLt hvLt le_rfl hsmallSum
  let c : ℝ := ((1 - u) * (1 - v))⁻¹
  have hc : 1 ≤ c := by simpa [c] using hnorm.1
  have hcpow : c ^ h ≤ 2 := by simpa [c] using hnorm.2
  have huPos : 0 < 1 - u := sub_pos.mpr huLt
  have hvPos : 0 < 1 - v := sub_pos.mpr hvLt
  refine ⟨c, hc, hcpow, ?_⟩
  intro S records groups hPass hqraw hpretrim W hW hPerm s g D
  have hSlices : ∀ t, W t ∈ R.slicePass C t ∧ (R.sliceLaw C t).w (W t) ≠ 0 := by
    intro t
    exact Lane_sol_s16_prod1.cond_support _ _ _ _
      (Lane_sol_s16_prod1.pi_support _ W hW t)
  have hGood : S.AllGood (records s (W s)) :=
    (hPass s (W s)).mp (hSlices s).1
  let rawMass : ℝ :=
    ∑ D' ∈ S.pretrimBins (records s (W s)) g, S.q g (records s (W s)) D'
  have hsolverMass := Lane_sol_s16_prod1.solver_pretrim_mass
    S (records s (W s)) hGood g (Real.exp_pos _)
  have hpreMass : 1 - v ≤ rawMass := by
    simpa [rawMass, v, h, ε] using hsolverMass
  have hrawMass :
      (∑ D' ∈ R.pretrim C W (groups (s, g)),
        (R.qraw C W (groups (s, g))).w D') = rawMass := by
    rw [hpretrim]
    apply Finset.sum_congr rfl
    intro D' hD'
    exact hqraw W s g D'
  have hqinFormula : (R.qin C W (groups (s, g))).w D =
      (if D ∈ S.pretrimBins (records s (W s)) g then
        S.q g (records s (W s)) D else 0) / rawMass := by
    rw [R.qin_eq C W (groups (s, g)) D hSlices, ← hrawMass, hpretrim, hqraw]
  have hqinBound : (R.qin C W (groups (s, g))).w D ≤
      S.q g (records s (W s)) D / (1 - v) := by
    rw [hqinFormula]
    by_cases hD : D ∈ S.pretrimBins (records s (W s)) g
    · rw [if_pos hD]
      exact div_le_div_of_nonneg_left (S.q_nonneg g (records s (W s)) D)
        (sub_pos.mpr hvLt) hpreMass
    · simp [hD]
      exact div_nonneg (S.q_nonneg g (records s (W s)) D) (sub_nonneg.mpr hvLt.le)
  have hpermSharp := Lane_sol_s16_prod1.permission_retained_sharp
    (Perm.table C) (R.qin C W) hPerm (groups (s, g))
  have hpermMass : 1 - u ≤
      ∑ D' ∈ (Perm.table C).permitted (groups (s, g)),
        (R.qin C W (groups (s, g))).w D' := by
    simpa [u, n, Perm.rate_eq C, Perm.n_eq C] using hpermSharp
  have hpermPos : 0 <
      ∑ D' ∈ (Perm.table C).permitted (groups (s, g)),
        (R.qin C W (groups (s, g))).w D' :=
    lt_of_lt_of_le huPos hpermMass
  rw [K.qbar_eq C W (groups (s, g)) D hW]
  by_cases hD : D ∈ (Perm.table C).permitted (groups (s, g))
  · rw [if_pos hD]
    calc
      _ ≤ (S.q g (records s (W s)) D / (1 - v)) /
          (∑ D' ∈ (Perm.table C).permitted (groups (s, g)),
            (R.qin C W (groups (s, g))).w D') :=
        div_le_div_of_nonneg_right hqinBound hpermPos.le
      _ ≤ (S.q g (records s (W s)) D / (1 - v)) / (1 - u) :=
        div_le_div_of_nonneg_left
          (div_nonneg (S.q_nonneg g (records s (W s)) D) hvPos.le)
          huPos hpermMass
      _ = c * S.q g (records s (W s)) D := by
        dsimp [c, u, v]
        field_simp [ne_of_gt huPos, ne_of_gt hvPos]
        <;> ring
  · simp [hD]
    exact mul_nonneg (le_trans (by norm_num) hc)
      (S.q_nonneg g (records s (W s)) D)

/-- B3. Star and pinned-star integrals against the restricted (unpooled)
rows: `solver_star_trimmed_mean` / `solver_star_trimmed_pin_mean` with B2.
TeX 16:228–249; estimated proof: 100 lines. -/
theorem cluster_star_qbar_means {κ : CConsts} (hκ : κ.Admissible) :
    ∃ n₀ : ℕ, ∀ {T : Stage} {k : ℕ} {PT : ProfiledTiling κ T k} {K16 : ℝ}
      (Q : LowModeQuantFacts hκ (PT := PT) K16) {G : LowGeom PT}
      (R : CellRawData G) (Perm : CellPermissions R) (K : CellRestrictedKernels R Perm),
      PT.tiling.mode = .lowCluster → n₀ ≤ T.S.n k → ∀ (C : G.Cell)
      (S : SliceSolver κ PT.tiling (G.cellPatch C) PT.mesh)
      (records : ∀ s, R.Value C s ≃ (∀ r, S.Val r))
      (groups : (R.Slice C × HypercubeRamsey.Group PT.tiling (G.cellPatch C)) ≃ R.Group C),
      (∀ s V, V ∈ R.slicePass C s ↔ S.AllGood (records s V)) →
      (∀ W s g D, (R.qraw C W (groups (s, g))).w D = S.q g (records s (W s)) D) →
      (∀ W s g, R.pretrim C W (groups (s, g)) = S.pretrimBins (records s (W s)) g) →
      ∀ W, (R.history C).w W ≠ 0 → PermissionLossHypotheses (Perm.table C) (R.qin C W) →
      ∀ s (w : EvenRole PT.tiling (G.cellPatch C)),
        (FinLaw.pi fun g => K.qbar C W (groups (s, g))).E
            (Lane_sol_s16_prod1.solver_star_bin_failure S (records s (W s)) w) ≤
          2 * sliceEps κ (PT.tiling.P (G.cellPatch C)).h ∧
        ∀ g D, g ∈ Lane_sol_s16_prod1.solver_star_group_scope S w →
          D ∈ S.pretrimBins (records s (W s)) g →
          (FinLaw.pi (Lane_sol_s16_prod1.coordinatePin
              (fun g => K.qbar C W (groups (s, g))) g D)).E
              (Lane_sol_s16_prod1.solver_star_bin_failure S (records s (W s)) w) ≤
            2 * Real.sqrt (sliceEps κ (PT.tiling.P (G.cellPatch C)).h) := by
  classical
  obtain ⟨n₀, hdom⟩ := cluster_qbar_domination hκ
  refine ⟨n₀, ?_⟩
  intro T k PT K16 Q G R Perm K hmode hn C S records groups hPass hqraw hpretrim
    W hW hPerm s w
  obtain ⟨c, hc, hcpow, hrows⟩ := hdom Q R Perm K hmode hn C
  have hrows := hrows S records groups hPass hqraw hpretrim W hW hPerm
  have hSlices : ∀ t, W t ∈ R.slicePass C t ∧ (R.sliceLaw C t).w (W t) ≠ 0 := by
    intro t
    exact Lane_sol_s16_prod1.cond_support _ _ _ _
      (Lane_sol_s16_prod1.pi_support _ W hW t)
  have hGood : S.AllGood (records s (W s)) :=
    (hPass s (W s)).mp (hSlices s).1
  let P : HypercubeRamsey.Group PT.tiling (G.cellPatch C) →
      FinLaw (Bin PT.tiling (G.cellPatch C)) :=
    fun g => K.qbar C W (groups (s, g))
  have hP : ∀ g ∈ Lane_sol_s16_prod1.solver_star_group_scope S w, ∀ D,
      (P g).w D ≤ c * S.q g (records s (W s)) D := by
    intro g _ D
    exact hrows s g D
  have hc0 : 0 ≤ c := le_trans (by norm_num) hc
  have hcount := Lane_sol_s16_prod1.solver_star_group_scope_count S w
  have hpow : c ^ (Lane_sol_s16_prod1.solver_star_group_scope S w).card ≤ 2 := by
    exact (pow_le_pow_right₀ hc hcount).trans hcpow
  have hmean := Lane_sol_s16_prod1.solver_star_trimmed_mean
    S (records s (W s)) w (hGood w) P c hc0 hP
  have hεnonneg : 0 ≤ sliceEps κ (PT.tiling.P (G.cellPatch C)).h := by
    unfold sliceEps
    exact (Real.exp_pos _).le
  constructor
  · exact hmean.trans (mul_le_mul_of_nonneg_right hpow hεnonneg)
  · intro g D hg hD
    have hvg : SliceSolver.Incident w g := by
      obtain ⟨j, _, heq⟩ := Finset.mem_image.mp hg
      rw [← heq]
      refine ⟨j, S.groupOf_spec _ ?_⟩
      rw [Lane_sol_s16_prod1.flip_parity]
      exact not_not.mpr w.2
    have hpin := Lane_sol_s16_prod1.solver_star_trimmed_pin_mean
      S (records s (W s)) w P c hc hP g D hD hvg
    exact hpin.trans (mul_le_mul_of_nonneg_right hpow (Real.sqrt_nonneg _))

/-! ## Lane D: the cluster load gate, under the repair. -/

/-- D1. Generic: a product of conditioned laws is the image of a product of
laws on the positive passing values.
TeX 16:259–278; estimated proof: 120 lines. -/
theorem pi_cond_support_map {I : Type*} [Fintype I] [DecidableEq I]
    {V : I → Type*} [∀ i, Fintype (V i)] [∀ i, DecidableEq (V i)]
    (P : ∀ i, FinLaw (V i)) (A : ∀ i, Finset (V i))
    (hA : ∀ i, 0 < ∑ v ∈ A i, (P i).w v) :
    ∃ P' : ∀ i, FinLaw {v : V i // v ∈ A i ∧ (P i).w v ≠ 0},
      FinLaw.pi (fun i => FinLaw.cond (P i) (A i) (hA i)) =
        FinLaw.map (FinLaw.pi P') (fun z i => (z i).1) := by
  sorry

/-- D2. The load summand of one odd role depends on its own slice value.
TeX 16:259–278; estimated proof: 150 lines. -/
theorem cluster_role_term_local {κ : CConsts} {T : Stage} {k : ℕ}
    {PT : ProfiledTiling κ T k} {G : LowGeom PT} (R : CellRawData G)
    (Perm : CellPermissions R) (K : CellRestrictedKernels R Perm)
    (hFallback : ∀ C pool W g, (∑ D ∈ Finset.univ.image pool, (K.qbar C W g).w D) = 0 →
      K.qtilde C pool W g = K.qbar C W g)
    (hR : R.SourceValid) (hc : PT.tiling.mode.isCluster) (C : G.Cell) (pool : CellPool G C)
    (W W' : R.Hist C) (hW : (R.history C).w W ≠ 0) (hW' : (R.history C).w W' ≠ 0)
    (r : OddCellRole G C)
    (heq : W ((R.cellWords C).symm ⟨r.1, r.2.1⟩).1 = W' ((R.cellWords C).symm ⟨r.1, r.2.1⟩).1)
    (y : Fin (T.S.N k)) :
    ∑ b, (K.qtilde C pool W (R.groupOf C r)).w b * (R.U C W (R.groupOf C r) b).w y =
      ∑ b, (K.qtilde C pool W' (R.groupOf C r)).w b * (R.U C W' (R.groupOf C r) b).w y := by
  sorry

/-- D3. Per-role cap at pools whose normalizers pass (typical pools).
TeX 16:274–276; estimated proof: 150 lines. -/
theorem cluster_role_term_cap {κ : CConsts} (hκ : κ.Admissible)
    {T : Stage} {k : ℕ} {PT : ProfiledTiling κ T k} {K16 : ℝ}
    (Q : LowModeQuantFacts hκ (PT := PT) K16) (H : LowGeometryCertificate hκ Q)
    (R : CellRawData H.geom) (Perm : CellPermissions R) (K : CellRestrictedKernels R Perm)
    (hR : R.SourceValid) (hc : PT.tiling.mode.isCluster)
    (hPerm : ∀ C W, (R.history C).w W ≠ 0 → PermissionLossHypotheses (Perm.table C) (R.qin C W))
    (C : H.geom.Cell) (pool : CellPool H.geom C) (W : R.Hist C) (hW : (R.history C).w W ≠ 0)
    (hn4 : Real.rpow (T.S.n k : ℝ) (-4) ≤ 1 / 2)
    (hmass : ∀ g, (1 - Real.rpow (T.S.n k : ℝ) (-4)) *
      ((H.geom.nslot C : ℝ) / Fintype.card (Bin PT.tiling (H.geom.cellPatch C))) ≤
        ∑ b ∈ Finset.univ.image pool, (K.qbar C W g).w b)
    (r : OddCellRole H.geom C) (y : Fin (T.S.N k)) :
    ∑ b, (K.qtilde C pool W (R.groupOf C r)).w b * (R.U C W (R.groupOf C r) b).w y ≤
      64 * Real.exp (2 * (sliceK κ (PT.tiling.P (H.geom.cellPatch C)).h : ℝ) *
        sliceT κ (PT.tiling.P (H.geom.cellPatch C)).h) / (H.geom.nslot C : ℝ) := by
  sorry

/-- D4. Per-role history mean at typical pools, through `low_profile` and
`law_cap` (T16:268-273): `4 (B/L) * 11/M`.
TeX 16:268–273; estimated proof: 350 lines. -/
theorem cluster_role_term_mean {κ : CConsts} (hκ : κ.Admissible)
    {T : Stage} {k : ℕ} {PT : ProfiledTiling κ T k} {K16 : ℝ}
    (Q : LowModeQuantFacts hκ (PT := PT) K16) (H : LowGeometryCertificate hκ Q)
    (R : CellRawData H.geom) (Perm : CellPermissions R) (K : CellRestrictedKernels R Perm)
    (hR : R.SourceValid) (hc : PT.tiling.mode.isCluster)
    (hPerm : ∀ C W, (R.history C).w W ≠ 0 → PermissionLossHypotheses (Perm.table C) (R.qin C W))
    (C : H.geom.Cell) (pool : CellPool H.geom C)
    (hn4 : Real.rpow (T.S.n k : ℝ) (-4) ≤ 1 / 2)
    (hmass : ∀ W, (R.history C).w W ≠ 0 → ∀ g, (1 - Real.rpow (T.S.n k : ℝ) (-4)) *
      ((H.geom.nslot C : ℝ) / Fintype.card (Bin PT.tiling (H.geom.cellPatch C))) ≤
        ∑ b ∈ Finset.univ.image pool, (K.qbar C W g).w b)
    (r : OddCellRole H.geom C) (y : Fin (T.S.N k)) :
    (R.history C).E (fun W =>
      ∑ b, (K.qtilde C pool W (R.groupOf C r)).w b * (R.U C W (R.groupOf C r) b).w y) ≤
      44 / ((H.geom.nslot C : ℝ) * (PT.tiling.P (H.geom.cellPatch C)).d) := by
  sorry

/-- D5. Numerical room of the gate variance budget. Here `words = 2^h`,
`A = exp(2kT)` and `slices * words` is the cell size.
TeX 16:274–278; estimated proof: 120 lines. -/
theorem cluster_gate_budget_room {κ : CConsts} (hκ : κ.Admissible) :
    ∃ n₀ : ℕ, ∀ (n : ℕ) (L slices words A N : ℝ),
      n₀ ≤ n → 2 ≤ n → (n : ℝ) ^ (199 : ℕ) ≤ L → 0 ≤ slices → 1 ≤ words → words ≤ n →
      slices * words ≤ (n : ℝ) ^ (200 : ℕ) → 1 ≤ A → A ≤ n → 1 ≤ N → N ≤ n * 2 ^ n →
      (Real.rpow (n : ℝ) (1 / 2 : ℝ) + Real.log (max 1 N)) *
          (slices * (words * (64 * A / L)) ^ 2) ≤ 2 * (κ.θstar / 2) ^ 2 := by
  sorry

/-- D6. The cluster gate (assembled from D1-D5 plus Link/checks_cover).
TeX 16:259–278; estimated proof: 250 lines. -/
theorem cluster_load_gate {κ : CConsts} (hκ : κ.Admissible) :
    ∃ n₀ : ℕ, ∀ {T : Stage} {k : ℕ} {PT : ProfiledTiling κ T k} {K16 : ℝ}
      (Q : LowModeQuantFacts hκ (PT := PT) K16) (H : LowGeometryCertificate hκ Q)
      (R : CellRawData H.geom) (Perm : CellPermissions R) (K : CellRestrictedKernels R Perm),
      (∀ C pool W g, (∑ D ∈ Finset.univ.image pool, (K.qbar C W g).w D) = 0 →
        K.qtilde C pool W g = K.qbar C W g) →
      R.SourceValid → PT.tiling.mode.isCluster → n₀ ≤ T.S.n k →
      (∀ C W, (R.history C).w W ≠ 0 → PermissionLossHypotheses (Perm.table C) (R.qin C W)) →
      ∀ (C : H.geom.Cell) {Check : Type} [Fintype Check]
        (D : CellPoolDiagnostics (Fin (H.geom.nslot C)) (Bin PT.tiling (H.geom.cellPatch C))
          (R.Hist C) Check (T.S.n k) (1 / 2)),
        CellDiagnosticLink K C D → Nonempty (LoadGateHypotheses D) := by
  sorry

/-! ## Assembly. -/

/-- Star checks (`none`) and pinned-star checks (`some (g, b)`), indexed by a
positive passing slice value, never by a whole-cell history. -/
abbrev ClusterStarCheck {κ : CConsts} {T : Stage} {k : ℕ} {PT : ProfiledTiling κ T k}
    {G : LowGeom PT} (R : CellRawData G) (C : G.Cell) :=
  (s : R.Slice C) × ({z : R.Value C s // z ∈ R.slicePass C s ∧ (R.sliceLaw C s).w z ≠ 0} ×
    EvenRole PT.tiling (G.cellPatch C) ×
    Option (HypercubeRamsey.Group PT.tiling (G.cellPatch C) × Bin PT.tiling (G.cellPatch C)))

/-- E1. Total check count (normalizer rows from `cluster_normalizer_setup`,
`hrowCount`, plus star/pin checks): cell size, `low_support`, `2^h <= n`
from the amplitude room, and `#bins <= N <= n 2^n`.
TeX 16:249–257; estimated proof: 100 lines. -/
theorem cluster_check_count {κ : CConsts} (hκ : κ.Admissible) :
    ∃ n₀ : ℕ, ∀ {T : Stage} {k : ℕ} {PT : ProfiledTiling κ T k} {K16 : ℝ}
      (Q : LowModeQuantFacts hκ (PT := PT) K16) (H : LowGeometryCertificate hκ Q)
      (R : CellRawData H.geom), R.SourceValid → PT.tiling.mode.isCluster → n₀ ≤ T.S.n k →
      ∀ (C : H.geom.Cell) (NormalizerCheck : Type) [Fintype NormalizerCheck],
        (Fintype.card NormalizerCheck : ℝ) ≤
          (T.S.n k : ℝ) ^ (200 : ℕ) * Real.exp ((T.S.n k : ℝ) ^ (1.01 : ℝ)) →
        (Fintype.card (NormalizerCheck ⊕ ClusterStarCheck R C) : ℝ) ≤
          Real.exp (3 * (T.S.n k : ℝ) ^ (1.01 : ℝ)) := by
  sorry


end HypercubeRamsey.S16.ClusterDiagnostics
