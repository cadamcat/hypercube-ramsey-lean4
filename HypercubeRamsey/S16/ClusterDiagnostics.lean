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
  sorry

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
  sorry

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

set_option maxHeartbeats 800000 in
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
  classical
  let i := H.geom.cellPatch C
  let patch := PT.tiling.P i
  let B : ℝ := Fintype.card (Bin PT.tiling i)
  let L : ℝ := H.geom.nslot C
  have hMnat : 0 < patch.M := by
    rw [← patch.cardY]
    exact_mod_cast Finset.card_pos.mpr
      (Q.profiled_valid.tiling_valid.patch_nonempty i).2
  have hMpos : 0 < (patch.M : ℝ) := by exact_mod_cast hMnat
  have hbinSum := patch.bins.sum_card_parts
  have hparts : (∑ b ∈ patch.bins.parts, b.card) = patch.bins.parts.card * patch.d := by
    calc
      _ = ∑ b ∈ patch.bins.parts, patch.d := by
        apply Finset.sum_congr rfl
        intro b hb
        exact Q.profiled_valid.tiling_valid.bins_card i b hb
      _ = _ := by simp
  rw [hparts, patch.cardY] at hbinSum
  have hbinNat : Fintype.card (Bin PT.tiling i) * patch.d = patch.M := by
    change Fintype.card {b // b ∈ patch.bins.parts} * patch.d = patch.M
    rw [Fintype.card_of_subtype patch.bins.parts (fun _ => Iff.rfl)]
    exact hbinSum
  have hBnat : 0 < Fintype.card (Bin PT.tiling i) := by
    by_contra h
    have hz : Fintype.card (Bin PT.tiling i) = 0 := Nat.eq_zero_of_not_pos h
    rw [hz, zero_mul] at hbinNat
    omega
  have hdNat : 0 < patch.d := by
    by_contra h
    have hz : patch.d = 0 := Nat.eq_zero_of_not_pos h
    rw [hz, Nat.mul_zero] at hbinNat
    omega
  have hBpos : 0 < B := by
    dsimp [B]
    exact_mod_cast hBnat
  have hdpos : 0 < (patch.d : ℝ) := by exact_mod_cast hdNat
  have hθ : 0 < κ.θstar := hκ.bucket.2.2.2.2
  have hKcell : 0 < κ.Kcell :=
    lt_of_lt_of_le (div_pos (by norm_num) hθ) hκ.Kcell_big
  have hnpos : 0 < (T.S.n k : ℝ) := by
    exact_mod_cast lt_of_lt_of_le (by norm_num : (0 : ℕ) < 2) Q.n_large
  have hLnat : 0 < H.geom.nslot C := by
    change 0 < H.data.cells.nslot C
    rw [H.cell_partition.slot_count C]
    apply Nat.ceil_pos.mpr
    exact div_pos (mul_pos hKcell (Real.rpow_pos_of_pos hnpos _)) hdpos
  have hLpos : 0 < L := by
    dsimp [L]
    exact_mod_cast hLnat
  have hbinReal : B * (patch.d : ℝ) = patch.M := by
    dsimp [B]
    exact_mod_cast hbinNat
  rcases hR with ⟨hMode, _hUniform, hSource⟩ | ⟨hNotCluster, _hSource⟩
  · obtain ⟨S, hS, records, groups, hLaw, hPass, hGroup, hQ, hTrim, hU, _hPrior⟩ := hSource C
    let words := R.cellWords C
    let sz := words.symm ⟨r.1, r.2.1⟩
    let s : R.Slice C := sz.1
    let z := sz.2
    have hback : words sz = ⟨r.1, r.2.1⟩ := words.apply_symm_apply _
    have hval : (words (s, z)).1 = r.1 := by
      simpa [s, z] using congrArg Subtype.val hback
    have hodd : ¬ IsEvenRole (words (s, z)).1 := by
      rw [hval]
      exact r.2.2
    have hrole : (⟨(words (s, z)).1, (words (s, z)).2, hodd⟩ : OddCellRole H.geom C) = r := by
      apply Subtype.ext
      exact hval
    have hgroup : R.groupOf C r = groups (s, S.groupOf z) := by
      have hh := hGroup s z hodd
      rw [hrole] at hh
      exact hh
    let g := S.groupOf z
    let P : FinLaw (∀ t, S.Val t) := S.recLaw PT.parameter
    let good := Finset.univ.filter S.AllGood
    have hgood : 0 < P.pr S.AllGood :=
      Lane_sol_s16_prod1.solver_good_pos Q.profiled_valid hMode S hS
    let condLaw : ∀ t : R.Slice C, FinLaw (R.Value C t) := fun t =>
      FinLaw.cond (R.sliceLaw C t) (R.slicePass C t) (R.slice_pos C t)
    have hSupported : ∀ W : R.Hist C, (R.history C).w W ≠ 0 →
        ∀ t, W t ∈ R.slicePass C t ∧ (R.sliceLaw C t).w (W t) ≠ 0 := by
      intro W hW t
      have hw : (condLaw t).w (W t) ≠ 0 := by
        exact Lane_sol_s16_prod1.pi_support condLaw W
          (by simpa [CellRawData.history, condLaw] using hW) t
      exact Lane_sol_s16_prod1.cond_support _ _ _ (W t) hw
    have hqin (W : R.Hist C) (hW : (R.history C).w W ≠ 0) (b : Bin PT.tiling i) :
        (R.qin C W (groups (s, g))).w b = S.qin (records s (W s)) g b := by
      rw [R.qin_eq C W (groups (s, g)) b (hSupported W hW)]
      simp_rw [hTrim W s g, hQ W s g]
      by_cases hb : b ∈ S.pretrimBins (records s (W s)) g
      · simp [SliceSolver.qin, hb]
      · simp [SliceSolver.qin, hb]
    let fRole : R.Hist C → ℝ := fun W =>
      ∑ b, (K.qtilde C pool W (R.groupOf C r)).w b *
        (R.U C W (R.groupOf C r) b).w y
    let fQin : R.Hist C → ℝ := fun W =>
      ∑ b, (R.qin C W (R.groupOf C r)).w b *
        (R.U C W (R.groupOf C r) b).w y
    let fSlice : R.Value C s → ℝ := fun w =>
      ∑ b, S.qin (records s w) g b * S.U g (records s w) b y
    have hqinTerm (W : R.Hist C) (hW : (R.history C).w W ≠ 0) :
        fQin W = fSlice (W s) := by
      dsimp [fQin, fSlice]
      rw [hgroup]
      apply Finset.sum_congr rfl
      intro b _
      rw [hqin W hW b, hU W s g b y]
    have hnormalizer (W : R.Hist C) (hW : (R.history C).w W ≠ 0) :
        L / (2 * B) ≤
          ∑ b ∈ Finset.univ.image pool, (K.qbar C W (groups (s, g))).w b := by
      have hm := hmass W hW (groups (s, g))
      have hfactor : (1 / 2 : ℝ) ≤ 1 - Real.rpow (T.S.n k : ℝ) (-4) := by
        linarith [hn4]
      have hLB : 0 ≤ L / B := div_nonneg hLpos.le hBpos.le
      calc
        L / (2 * B) = (1 / 2 : ℝ) * (L / B) := by ring
        _ ≤ (1 - Real.rpow (T.S.n k : ℝ) (-4)) * (L / B) :=
          mul_le_mul_of_nonneg_right hfactor hLB
        _ ≤ _ := hm
    have hqbar (W : R.Hist C) (hW : (R.history C).w W ≠ 0)
        (b : Bin PT.tiling i) :
        (K.qbar C W (groups (s, g))).w b ≤
          2 * (R.qin C W (groups (s, g))).w b := by
      have hret := Lane_sol_s16_prod1.permission_retained_half
        (Perm.table C) (R.qin C W) (hPerm C W hW) (groups (s, g))
      have hden : 0 < ∑ b' ∈ (Perm.table C).permitted (groups (s, g)),
          (R.qin C W (groups (s, g))).w b' := by linarith
      rw [K.qbar_eq C W (groups (s, g)) b hW]
      by_cases hb : b ∈ (Perm.table C).permitted (groups (s, g))
      · rw [if_pos hb]
        calc
          _ ≤ (R.qin C W (groups (s, g))).w b / (1 / 2 : ℝ) :=
            div_le_div_of_nonneg_left ((R.qin C W (groups (s, g))).nonneg b)
              (by norm_num) hret
          _ = 2 * (R.qin C W (groups (s, g))).w b := by ring
      · simpa [hb] using (R.qin C W (groups (s, g))).nonneg b
    have hqtilde (W : R.Hist C) (hW : (R.history C).w W ≠ 0)
        (b : Bin PT.tiling i) :
        (K.qtilde C pool W (groups (s, g))).w b ≤
          (2 * B / L) * (K.qbar C W (groups (s, g))).w b := by
      have hZ := hnormalizer W hW
      have hZpos : 0 < ∑ b' ∈ Finset.univ.image pool,
          (K.qbar C W (groups (s, g))).w b' := by
        exact lt_of_lt_of_le (div_pos hLpos (by positivity)) hZ
      rw [K.qtilde_eq C pool W (groups (s, g)) b hW (ne_of_gt hZpos)]
      by_cases hb : b ∈ Finset.univ.image pool
      · rw [if_pos hb]
        calc
          _ ≤ (K.qbar C W (groups (s, g))).w b / (L / (2 * B)) :=
            div_le_div_of_nonneg_left
              ((K.qbar C W (groups (s, g))).nonneg b) (by positivity) hZ
          _ = (2 * B / L) * (K.qbar C W (groups (s, g))).w b := by
            field_simp [ne_of_gt hLpos] <;> ring
      · simp only [if_neg hb, zero_div]
        exact mul_nonneg (div_nonneg (mul_nonneg (by norm_num) hBpos.le) hLpos.le)
          ((K.qbar C W (groups (s, g))).nonneg b)
    have hpoint (W : R.Hist C) (hW : (R.history C).w W ≠ 0) :
        fRole W ≤ (4 * B / L) * fQin W := by
      dsimp [fRole, fQin]
      rw [hgroup]
      have hsum :
          (∑ b, (K.qbar C W (groups (s, g))).w b *
            (R.U C W (groups (s, g)) b).w y) ≤
          2 * ∑ b, (R.qin C W (groups (s, g))).w b *
            (R.U C W (groups (s, g)) b).w y := by
        calc
          _ ≤ ∑ b, 2 * ((R.qin C W (groups (s, g))).w b *
              (R.U C W (groups (s, g)) b).w y) := by
            apply Finset.sum_le_sum
            intro b _
            calc
              _ ≤ (2 * (R.qin C W (groups (s, g))).w b) *
                  (R.U C W (groups (s, g)) b).w y :=
                mul_le_mul_of_nonneg_right (hqbar W hW b)
                  ((R.U C W (groups (s, g)) b).nonneg y)
              _ = _ := by ring
          _ = _ := by rw [← Finset.mul_sum]
      calc
        _ ≤ (2 * B / L) *
            ∑ b, (K.qbar C W (groups (s, g))).w b *
              (R.U C W (groups (s, g)) b).w y := by
          calc
            _ ≤ ∑ b, ((2 * B / L) * (K.qbar C W (groups (s, g))).w b) *
                (R.U C W (groups (s, g)) b).w y := by
              apply Finset.sum_le_sum
              intro b _
              exact mul_le_mul_of_nonneg_right (hqtilde W hW b)
                ((R.U C W (groups (s, g)) b).nonneg y)
            _ = _ := by
              rw [Finset.mul_sum]
              apply Finset.sum_congr rfl
              intro b _
              ring
        _ ≤ (2 * B / L) *
            (2 * ∑ b, (R.qin C W (groups (s, g))).w b *
              (R.U C W (groups (s, g)) b).w y) :=
          mul_le_mul_of_nonneg_left hsum (by positivity)
        _ = (4 * B / L) *
            ∑ b, (R.qin C W (groups (s, g))).w b *
              (R.U C W (groups (s, g)) b).w y := by ring
    have hEbound : (R.history C).E fRole ≤ (4 * B / L) * (R.history C).E fQin := by
      unfold FinLaw.E
      calc
        _ ≤ ∑ W, (R.history C).w W * ((4 * B / L) * fQin W) := by
          apply Finset.sum_le_sum
          intro W _
          by_cases hW : (R.history C).w W = 0
          · simp [hW]
          · exact mul_le_mul_of_nonneg_left (hpoint W hW) ((R.history C).nonneg W)
        _ = _ := by
          calc
            _ = ∑ W, (4 * B / L) * ((R.history C).w W * fQin W) := by
              apply Finset.sum_congr rfl
              intro W _
              ring
            _ = _ := by rw [Finset.mul_sum]
    have hmeanQin : (R.history C).E fQin = (PT.π i).w y := by
      let law : ∀ t : R.Slice C, FinLaw (R.Value C t) := condLaw
      have hreplace : (FinLaw.pi law).E fQin =
          (FinLaw.pi law).E (fun W => fSlice (W s)) := by
        unfold FinLaw.E
        apply Finset.sum_congr rfl
        intro W _
        by_cases hW : (FinLaw.pi law).w W = 0
        · simp [hW]
        · have hW' : (R.history C).w W ≠ 0 := by
            simpa [CellRawData.history, law, condLaw] using hW
          rw [hqinTerm W hW']
      have hcoord : (FinLaw.pi law).E (fun W => fSlice (W s)) =
          (law s).E fSlice := by
        let S : Finset (R.Slice C) := {s}
        let st : {t : R.Slice C // t ∈ S} := ⟨s, by simp [S]⟩
        letI inst : Unique {t : R.Slice C // t ∈ S} := {
          default := st
          uniq := by
            intro t
            apply Subtype.ext
            exact Finset.mem_singleton.mp (by simpa [S] using t.2) }
        let Qfw : ∀ t : R.Slice C, FinProb (R.Value C t) := fun t =>
          HypercubeRamsey.S16.finLawToFramework (law t)
        have hm := FinProb.pi_marginal_expect Qfw S (fun a => fSlice (a default))
        let e : (∀ t : {t : R.Slice C // t ∈ S}, R.Value C t.1) ≃ R.Value C s :=
          Equiv.piUnique (fun t : {t : R.Slice C // t ∈ S} => R.Value C t.1)
        have hprod (a : ∀ t : {t : R.Slice C // t ∈ S}, R.Value C t.1) :
            (∏ t, (Qfw t.1).w (a t)) = (Qfw s).w (a default) := by
          rw [Fintype.prod_unique]
          simp [Qfw, inst, st, S]
        have hsingle :
            (FinProb.pi (fun t : {t : R.Slice C // t ∈ S} => Qfw t.1)).expect
                (fun a => fSlice (a default)) = (Qfw s).expect fSlice := by
          calc
            _ = ∑ a, (Qfw s).w (e a) * fSlice (e a) := by
              unfold FinProb.expect
              apply Finset.sum_congr rfl
              intro a _
              change (∏ t, (Qfw t.1).w (a t)) * fSlice (a default) = _
              rw [hprod a]
              change (Qfw s).w (e a) * fSlice (e a) = _
              have he : e a = a default := rfl
              rw [he]
            _ = ∑ w, (Qfw s).w w * fSlice w :=
              Equiv.sum_comp e (fun w => (Qfw s).w w * fSlice w)
            _ = _ := rfl
        rw [hsingle] at hm
        simpa [FinProb.expect, FinProb.pi, FinLaw.E, FinLaw.pi, Qfw, inst, st, S,
          HypercubeRamsey.S16.finLawToFramework] using hm
      have hweight (w : R.Value C s) : (R.sliceLaw C s).w w = P.w (records s w) := by
        rw [hLaw s]
        change (FinLaw.map (S.recLaw PT.parameter) (records s).symm).w w =
          (S.recLaw PT.parameter).w (records s w)
        simp [FinLaw.map, Equiv.symm_apply_eq, P]
      have hgoodDen : (∑ W ∈ good, P.w W) = P.pr S.AllGood := by
        simpa [good, FinLaw.pr] using (Finset.sum_ite_mem_eq good P.w).symm
      have hgoodMass : 0 < ∑ W ∈ good, P.w W := by
        rw [hgoodDen]
        exact hgood
      have hden : ∑ w ∈ R.slicePass C s, (R.sliceLaw C s).w w = P.pr S.AllGood := by
        calc
          _ = ∑ w ∈ R.slicePass C s, P.w (records s w) := by
            apply Finset.sum_congr rfl
            intro w _
            exact hweight w
          _ = ∑ w, if w ∈ R.slicePass C s then P.w (records s w) else 0 := by
            simp [Finset.sum_ite_mem, Finset.univ_inter]
          _ = ∑ W, if (records s).symm W ∈ R.slicePass C s then P.w W else 0 := by
            simpa [Equiv.apply_symm_apply] using
              (Equiv.sum_comp (records s) (fun W =>
                if (records s).symm W ∈ R.slicePass C s then P.w W else 0))
          _ = P.pr S.AllGood := by
            calc
              _ = ∑ W, if S.AllGood W then P.w W else 0 := by
                apply Finset.sum_congr rfl
                intro W _
                have hp : (records s).symm W ∈ R.slicePass C s ↔ S.AllGood W := by
                  simpa using hPass s ((records s).symm W)
                by_cases hg : S.AllGood W
                · simp [hp.mpr hg, hg]
                · have hn : (records s).symm W ∉ R.slicePass C s := by
                    intro h
                    exact hg (hp.mp h)
                  simp [hn, hg]
              _ = ∑ W ∈ good, P.w W := by
                simpa [good] using (Finset.sum_ite_mem_eq good P.w)
              _ = _ := hgoodDen
      have hcondE : (law s).E fSlice =
          (FinLaw.cond P good hgoodMass).E (fun W => fSlice ((records s).symm W)) := by
        have hcondWeight (w : R.Value C s) : (law s).w w =
            (FinLaw.cond P good hgoodMass).w (records s w) := by
          simp only [law, condLaw, FinLaw.cond]
          rw [hweight w, hden, hgoodDen]
          have hp := hPass s w
          simp only [good, Finset.mem_filter, Finset.mem_univ, true_and]
          by_cases hg : S.AllGood (records s w)
          · simp [hp.mpr hg, hg]
          · have hn : w ∉ R.slicePass C s := fun hw => hg (hp.mp hw)
            simp [hn, hg]
        calc
          _ = ∑ w, (FinLaw.cond P good hgoodMass).w (records s w) * fSlice w := by
            unfold FinLaw.E
            apply Finset.sum_congr rfl
            intro w _
            rw [hcondWeight w]
          _ = _ := by
            unfold FinLaw.E
            simpa [Equiv.apply_symm_apply] using
              (Equiv.sum_comp (records s) (fun W =>
                (FinLaw.cond P good hgoodMass).w W * fSlice ((records s).symm W)))
      have hlow : (FinLaw.cond P good hgoodMass).E
          (fun W => fSlice ((records s).symm W)) = S.lowOut PT.parameter g y := by
        have hnum :
            (∑ W, (if S.AllGood W then P.w W else 0) *
              fSlice ((records s).symm W)) =
            ∑ W, P.w W * (if S.AllGood W then
              ∑ b, S.qin W g b * S.U g W b y else 0) := by
          apply Finset.sum_congr rfl
          intro W _
          by_cases hg : S.AllGood W
          · simp [hg, fSlice, Equiv.apply_symm_apply]
          · simp [hg]
        have hnumS :
            (∑ W, (if S.AllGood W then (S.recLaw PT.parameter).w W else 0) *
              fSlice ((records s).symm W)) =
            ∑ W, (S.recLaw PT.parameter).w W * (if S.AllGood W then
              ∑ b, S.qin W g b * S.U g W b y else 0) := by
          simpa [P] using hnum
        have hgoodDenS : (∑ W ∈ good, (S.recLaw PT.parameter).w W) =
            (S.recLaw PT.parameter).pr S.AllGood := by
          simpa [P] using hgoodDen
        dsimp only [FinLaw.E, FinLaw.cond, SliceSolver.lowOut, P]
        simp only [good, Finset.mem_filter, Finset.mem_univ, true_and]
        calc
          _ = ∑ W, ((if S.AllGood W then (S.recLaw PT.parameter).w W else 0) *
              fSlice ((records s).symm W)) /
              (∑ W' ∈ good, (S.recLaw PT.parameter).w W') := by
            apply Finset.sum_congr rfl
            intro W _
            simp only [good, Finset.mem_filter, Finset.mem_univ, true_and]
            ring
          _ = (∑ W, (if S.AllGood W then (S.recLaw PT.parameter).w W else 0) *
              fSlice ((records s).symm W)) /
              (∑ W' ∈ good, (S.recLaw PT.parameter).w W') := by
            rw [← Finset.sum_div]
          _ = _ := by rw [hgoodDenS, hnumS]
      change (FinLaw.pi law).E fQin = (PT.π i).w y
      calc
        _ = (law s).E fSlice := hreplace.trans hcoord
        _ = S.lowOut PT.parameter g y := hcondE.trans hlow
        _ = (PT.π i).w y := (Q.profiled_valid.low_profile hMode i S hS g y).symm
    have hcap := Q.profiled_valid.law_cap i y
    calc
      _ ≤ (4 * B / L) * (R.history C).E fQin := hEbound
      _ = (4 * B / L) * (PT.π i).w y := by rw [hmeanQin]
      _ ≤ (4 * B / L) * (11 / (patch.M : ℝ)) :=
        mul_le_mul_of_nonneg_left hcap (by positivity)
      _ = 44 / (L * (patch.d : ℝ)) := by
        rw [← hbinReal]
        field_simp [ne_of_gt hLpos, ne_of_gt hBpos, ne_of_gt hdpos]
        ring
  · exact False.elim (hNotCluster hc)

/-- D5. Numerical room of the gate variance budget. Here `words = 2^h`,
`A = exp(2kT)` and `slices * words` is the cell size.
TeX 16:274–278; estimated proof: 120 lines. -/
theorem cluster_gate_budget_room {κ : CConsts} (hκ : κ.Admissible) :
    ∃ n₀ : ℕ, ∀ (n : ℕ) (L slices words A N : ℝ),
      n₀ ≤ n → 2 ≤ n → (n : ℝ) ^ (199 : ℕ) ≤ L → 0 ≤ slices → 1 ≤ words → words ≤ n →
      slices * words ≤ (n : ℝ) ^ (200 : ℕ) → 1 ≤ A → A ≤ n → 1 ≤ N → N ≤ n * 2 ^ n →
      (Real.rpow (n : ℝ) (1 / 2 : ℝ) + Real.log (max 1 N)) *
          (slices * (words * (64 * A / L)) ^ 2) ≤ 2 * (κ.θstar / 2) ^ 2 := by
  have hθ : 0 < κ.θstar := hκ.bucket.2.2.2.2
  let n₀ : ℕ := ⌈24576 / κ.θstar ^ 2⌉₊
  refine ⟨n₀, ?_⟩
  intro n L slices words A N hn₀ hn2 hL hslices hwords hwordsN hcell hA hAN hN hNbound
  let x : ℝ := n
  have hx2 : 2 ≤ x := by dsimp [x]; exact_mod_cast hn2
  have hx : 0 < x := by linarith
  have hx1 : 1 ≤ x := by linarith
  have hLp : 0 < L := lt_of_lt_of_le (pow_pos hx _) hL
  have hceil : 24576 / κ.θstar ^ 2 ≤ (n₀ : ℝ) := by
    change 24576 / κ.θstar ^ 2 ≤ (⌈24576 / κ.θstar ^ 2⌉₊ : ℝ)
    exact Nat.le_ceil _
  have hn₀' : (n₀ : ℝ) ≤ x := by
    dsimp [x]
    exact_mod_cast hn₀
  have hxpow : x ≤ x ^ (194 : ℕ) := by
    have hh := pow_le_pow_right₀ hx1 (by norm_num : 1 ≤ (194 : ℕ))
    simpa using hh
  have hthreshold : 24576 / κ.θstar ^ 2 ≤ x ^ (194 : ℕ) :=
    le_trans (le_trans hceil hn₀') hxpow
  have hbudget : 12288 / x ^ (194 : ℕ) ≤ κ.θstar ^ 2 / 2 := by
    apply (div_le_iff₀ (pow_pos hx 194)).2
    have hprod : 12288 ≤ (κ.θstar ^ 2 / 2) * x ^ (194 : ℕ) := by
      calc
        12288 = (κ.θstar ^ 2 / 2) * (24576 / κ.θstar ^ 2) := by
          field_simp [ne_of_gt hθ]
          norm_num
        _ ≤ (κ.θstar ^ 2 / 2) * x ^ (194 : ℕ) :=
          mul_le_mul_of_nonneg_left hthreshold (by positivity)
    nlinarith
  have hlogx : Real.log x ≤ x := by
    exact (Real.log_le_sub_one_of_pos hx).trans (by linarith)
  have hlog2 : Real.log (2 : ℝ) ≤ 1 := by
    exact (Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 2)).trans (by norm_num)
  have hmax : max 1 N ≤ x * 2 ^ n := by
    apply max_le
    · have hxreal : (1 : ℝ) ≤ x := hx1
      have hpow : (1 : ℝ) ≤ 2 ^ n := one_le_pow₀ (by norm_num : (1 : ℝ) ≤ 2)
      nlinarith
    · simpa [x] using hNbound
  have hlog : Real.log (max 1 N) ≤ 2 * x := by
    calc
      Real.log (max 1 N) ≤ Real.log (x * 2 ^ n) :=
        Real.log_le_log (by positivity) hmax
      _ = Real.log x + (n : ℝ) * Real.log 2 := by
        rw [Real.log_mul hx.ne' (by positivity), Real.log_pow]
      _ ≤ x + x := by
        have hnreal : (n : ℝ) = x := by rfl
        rw [hnreal]
        calc
          Real.log x + x * Real.log 2 ≤ x + x * 1 :=
            add_le_add hlogx (mul_le_mul_of_nonneg_left hlog2 hx.le)
          _ = x + x := by ring
      _ = 2 * x := by ring
  have hrpow : Real.rpow x (1 / 2 : ℝ) ≤ x := by
    simpa only [Real.rpow_eq_pow, Real.rpow_one] using
      Real.rpow_le_rpow_of_exponent_le hx1 (by norm_num : (1 / 2 : ℝ) ≤ 1)
  have hstat : Real.rpow x (1 / 2 : ℝ) + Real.log (max 1 N) ≤ 3 * x := by
    linarith
  have hratio : 0 ≤ 64 * A / L ∧ 64 * A / L ≤ 64 / x ^ (198 : ℕ) := by
    constructor
    · positivity
    · calc
        64 * A / L ≤ 64 * x / L :=
          div_le_div_of_nonneg_right (by nlinarith) hLp.le
        _ ≤ 64 * x / x ^ (199 : ℕ) :=
          div_le_div_of_nonneg_left (by positivity) (pow_pos hx 199) hL
        _ = 64 / x ^ (198 : ℕ) := by
          rw [show (199 : ℕ) = 198 + 1 by norm_num, pow_succ]
          field_simp [ne_of_gt hx] <;> ring
  have hratioSq : (64 * A / L) ^ 2 ≤ (64 / x ^ (198 : ℕ)) ^ 2 := by
    have hgap : 0 ≤ 64 / x ^ (198 : ℕ) - 64 * A / L := sub_nonneg.mpr hratio.2
    have hplus : 0 ≤ 64 * A / L + 64 / x ^ (198 : ℕ) := by positivity
    nlinarith [mul_nonneg hgap hplus]
  have hsw : slices * words ≤ x ^ (200 : ℕ) := by
    simpa [x] using hcell
  have hcoeff : slices * words ^ 2 ≤ x ^ (201 : ℕ) := by
    calc
      slices * words ^ 2 = (slices * words) * words := by ring
      _ ≤ x ^ (200 : ℕ) * x :=
        mul_le_mul hsw hwordsN (by positivity) (by positivity)
      _ = x ^ (201 : ℕ) := by rw [← pow_succ]
  have hwidth : slices * (words * (64 * A / L)) ^ 2 ≤ 4096 / x ^ (195 : ℕ) := by
    calc
      slices * (words * (64 * A / L)) ^ 2 =
          (slices * words ^ 2) * (64 * A / L) ^ 2 := by ring
      _ ≤ x ^ (201 : ℕ) * (64 / x ^ (198 : ℕ)) ^ 2 :=
        mul_le_mul hcoeff hratioSq (by positivity) (by positivity)
      _ = 4096 / x ^ (195 : ℕ) := by
        field_simp [ne_of_gt hx]
        ring
  have hstatNonneg : 0 ≤ Real.rpow x (1 / 2 : ℝ) + Real.log (max 1 N) := by
    exact add_nonneg (Real.rpow_nonneg hx.le _) (Real.log_nonneg (le_max_left 1 N))
  calc
    _ ≤ (3 * x) * (4096 / x ^ (195 : ℕ)) :=
      mul_le_mul hstat hwidth (by positivity) (by positivity)
    _ = 12288 / x ^ (194 : ℕ) := by
      field_simp [ne_of_gt hx]
      ring
    _ ≤ κ.θstar ^ 2 / 2 := hbudget
    _ = 2 * (κ.θstar / 2) ^ 2 := by ring

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
